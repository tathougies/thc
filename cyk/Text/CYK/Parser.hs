{-# OPTIONS_GHC -fplugin DumpCore #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module Text.CYK.Parser
  ( Splittable(..), SplitResult(..)

  , Parsed, Parser, getParseResult
  , parserFinal
  , printParsedTableau
  , parse, testParse, combineParses
  , ParserBuilder, RuleB, buildRule
  , compile, terminal

  , Sym, AST(..)
--  , simpleParser
  , simpleRuleParser
  , simpleRuleParserLR
  , showRules
  ) where

import           Control.Applicative
import           Control.Monad.ST
import           Control.Monad.State
import           Control.Parallel (par)
import           Control.Parallel.Strategies (Strategy, withStrategy, r0, rseq, runEval)

import           Data.Foldable (foldl', foldrM)
import qualified Data.IntMap as IM
import           Data.List (sortBy, intercalate)
import           Data.Ord (comparing)
import qualified Data.Sequence as Seq
import qualified Data.Vector as V
import qualified Data.Vector.Generic as GV
import qualified Data.Vector.Unboxed as UV
import qualified Data.Vector.Mutable as MV
import qualified Data.Dependent.Map as DM
import qualified Data.GADT.Compare as DM

import           Data.Bits ((.|.), (.&.), shiftL, shiftR)
import           Data.Foldable (toList)
import           Data.Int
import           Data.List (find)
import qualified Data.Map.Strict as M
import           Data.Maybe (fromMaybe, mapMaybe)
import           Data.Monoid (Last(..), Sum(..))
import qualified Data.Monoid as Monoid
import           Data.Semigroup (Max(..))
import qualified Data.Text as T
import           Data.Word

import           Data.FingerTree.Pinky (FingerTree, Measured(measure))
import qualified Data.FingerTree.Pinky as FingerTree

--import           Debug.Trace
import qualified Debug.Trace as Trace

import           GHC.Prim
import           GHC.Stack
import           GHC.Types (Any)

import           Unsafe.Coerce

trace :: String -> a -> a
--trace = Trace.trace
trace _ = id

class Splittable f where
  type SplitItem f :: *
  bisect :: f -> SplitResult f (SplitItem f)
  getAll :: f -> [ SplitItem f ]

data SplitResult f a
  = SplitResultNull
  | SplitResultOne !a
  | SplitResultSplit {-# UNPACK #-} !Word !f {-# UNPACK #-} !Word !f
    deriving Show

data Parser tok a where
  Parser :: Enum classification
         => { parserTokenClassifier   :: tok -> classification
            , parserSingleRules       :: V.Vector (Word32, (Word32, tok -> Maybe Any))
            , parserRules             :: UV.Vector (Word64, Word32)
            , parserCombinators       :: V.Vector (Any -> Any -> Any)
            , parserFinal             :: {-# UNPACK #-} !Word32 -- Final state
            , parserEmptyMatches      :: [ a ]
            }
         -> Parser tok a

type ParserTableau tok = Seq.Seq (ParsedTableauRow tok)
type ProductionRules = UV.Vector (Word64, Word32)

data Parsed tok a -- This is a phantom type paramater. We have to rely on unsafe casting to get the result, if any
  = Parsed
  { parsedTableau    :: !(ParserTableau tok)
  , parsedTokenCount :: {-# UNPACK #-} !Word
  }

getParseResult :: Parser tok a -> Parsed tok a -> [a]
getParseResult pp (Parsed tableau cnt) =
  case Seq.viewr tableau of
    Seq.EmptyR -> parserEmptyMatches pp
    _ Seq.:> ParsedTableauRow rowCount row
        | rowCount /= cnt -> parserEmptyMatches pp
        | otherwise ->
            case FingerTree.viewl row of
              TableauCell prods FingerTree.:< _ ->
                  parserEmptyMatches pp ++
                  mapMaybe (\(term, a) -> if term == parserFinal pp then Just (unsafeCoerce a) else Nothing ) (V.toList prods)
              _ -> parserEmptyMatches pp

instance Measured (Last Word) (ParsedTableauRow tok) where
  measure (ParsedTableauRow len _) = Last (Just len)

data TableauCell tok
  = TableauCell
  { tcProductions :: !(V.Vector (Word32, Any)) -- An array of productions and production outputs, ordered by key
  }
  | TableauRowSkip {-# UNPACK #-} !Word

instance Show (TableauCell tok) where
  show = showTableauCell

tableauCellProductionIndices :: TableauCell tok -> V.Vector Word32
tableauCellProductionIndices (TableauCell n) = fmap fst n
tableauCellProductionIndices _ = mempty

data ParsedTableauRow tok
  = ParsedTableauRow {-# UNPACK #-} !Word !(FingerTree TableauCellPosition (TableauCell tok))

data TableauCellPosition
    = TableauCellPosition
    { tcpIx :: {-# UNPACK #-} !Word
    , tcpNonSparse :: !Bool
    } deriving Show

instance Semigroup TableauCellPosition where
    a <> b = TableauCellPosition (tcpIx a + tcpIx b) (tcpNonSparse a || tcpNonSparse b)

instance Monoid TableauCellPosition where
    mempty = TableauCellPosition 0 False
    mappend = (<>)

instance Measured TableauCellPosition (TableauCell tok) where
  measure (TableauCell {}) = TableauCellPosition 1 True
  measure (TableauRowSkip x) = TableauCellPosition x False

instance Splittable T.Text where
  type SplitItem T.Text = Char

  bisect t
    | T.null t = SplitResultNull
    | T.length t == 1 = SplitResultOne (T.head t)
    | otherwise = let firstLength = T.length t `div` 2
                      (a, b) = T.splitAt firstLength t
                  in SplitResultSplit (fromIntegral firstLength) a (fromIntegral $ T.length t - firstLength) b

  getAll = T.unpack

-- | Parse the given grammar in parallel
parse :: Splittable f
      => Word -> Parser (SplitItem f) a -> f -> Parsed (SplitItem f) a
parse smallestSubproblem parser toks =
  case bisect toks of
    SplitResultNull  -> Parsed Seq.empty 0
    SplitResultOne a -> makeEntireTableau parser 1 [a]
    SplitResultSplit aSz a bSz b ->
      let ap | aSz <= smallestSubproblem = makeEntireTableau parser aSz (getAll a)
             | otherwise = parse smallestSubproblem parser a
          bp | bSz <= smallestSubproblem = makeEntireTableau parser bSz (getAll b)
             | otherwise = parse smallestSubproblem parser b
          combined = combineParses parser ap bp
      in runEval (rseq ap) `par` runEval (rseq bp) `par` combined `seq` combined

makeEntireTableau :: Parser tok a -> Word -> [tok] -> Parsed tok a
makeEntireTableau _ _ [] = Parsed mempty 0
makeEntireTableau pp@Parser { parserSingleRules = singles, parserTokenClassifier = classify } tokCnt toks =
  Parsed finalTableau tokCnt
  where
    finalTableau = parsedInitial `seq` foldl' buildNextRow (Seq.singleton parsedInitial) (map fst (zip [2..] (tail toks)))
    parsedInitial = ParsedTableauRow 1 (FingerTree.fromList (initialRow 0 toks))

    initialRow 0 [] = []
    initialRow n [] = [ TableauRowSkip n ]
    initialRow n (tok:toks) =
      let prod = fromIntegral (fromEnum (classify tok))
          prodStart = bsearch singles prod
          applicableProductions = V.takeWhile ((== prod) . fst) (V.drop prodStart singles)
          newProductions = V.mapMaybe (\(_, (next, mk)) -> (next,) <$> mk tok) applicableProductions

      in if V.null newProductions
         then initialRow (n + 1) toks
         else if n == 0
              then TableauCell newProductions:initialRow 0 toks
              else TableauRowSkip n:TableauCell newProductions:initialRow 0 toks

    buildNextRow tableau sz =
      trace ("buildNextRow: " ++ show sz) $
      let matchingRows = getMatchingPairs 0 sz tableau
          nextRow = computeCell (tokCnt - sz + 1) sz pp matchingRows mempty
      in trace ("MAtching pairs " ++ show (length matchingRows)) $
         trace ("Row nonsparse: " ++ show (tcpNonSparse (measure nextRow))) $
         if tcpNonSparse (measure nextRow)
         then tableau Seq.|> ParsedTableauRow sz nextRow
         else tableau


a |>* b | tcpIx (measure a) == 0 = FingerTree.singleton b
a |>* b@(TableauCell {}) = a FingerTree.|> b
a |>* b@(TableauRowSkip n) =
  case FingerTree.viewr a of
    a' FingerTree.:> TableauRowSkip m ->
      a' FingerTree.|> TableauRowSkip (m + n)
    _ -> a FingerTree.|> b

b *<| a | tcpIx (measure a) == 0 = FingerTree.singleton b
b@(TableauCell {}) *<| a = b FingerTree.<| a
b@(TableauRowSkip n) *<| a =
  case FingerTree.viewl a of
    TableauRowSkip m FingerTree.:< a' ->
      TableauRowSkip (m + n) FingerTree.<| a'
    _ -> b FingerTree.<| a

a >*< b | tcpIx (measure a) == 0 = b
        | tcpIx (measure b) == 0 = a
a >*< b = --a FingerTree.>< b
 case ( FingerTree.viewr a
      , FingerTree.viewl b) of
   ( FingerTree.EmptyR, _ ) -> b
   ( _, FingerTree.EmptyL ) -> a
   ( a' FingerTree.:> TableauRowSkip n,
     TableauRowSkip m FingerTree.:< b' ) ->
     let skip = TableauRowSkip (m + n)
     in {-# SCC fingerTreeMergeSkip #-} skip `seq` (a' FingerTree.|> skip) FingerTree.>< b'
   _ -> {-# SCC fingerTreeMergeNormal #-} a FingerTree.>< b


-- | Combine two parses using the parser given
combineParses :: Parser tok a -> Parsed tok a -> Parsed tok a -> Parsed tok a
combineParses pp@(Parser { parserRules = rules, parserCombinators = combinators }) a@(Parsed aTableauBegin atc) b@(Parsed bTableauBegin btc) =
    Parsed (go 1 aTableauBegin bTableauBegin mempty) finalTokenCount
  where
    finalTokenCount = atc + btc
    nextRowToGenerate = max atc btc + 1

    go n _ _ t
      | n > finalTokenCount = t
    go n at bt finalTableau =
      trace ("go " ++ show n) $
        case ( Seq.viewl at, Seq.viewl bt ) of
          ( Seq.EmptyL, Seq.EmptyL ) ->
              finalizeTableau n finalTableau

          ( (ParsedTableauRow aLen aRow) Seq.:< at',
            (ParsedTableauRow bLen bRow) Seq.:< bt' )
              | aLen == bLen && aLen == n ->
                  iterateRow at' bt' n aRow bRow finalTableau

          ( _,
            ParsedTableauRow bLen bRow Seq.:< bt' )
              | bLen == n ->
                trace ("Right biased case; " ++ show (n, atc - bLen + 1, atc, bLen)) $
                -- finalizeTableau nextRowToGenerate (finalTableau FingerTree.>< FingerTree.fmap' (padRowLeft atc) bt)
                iterateRow at bt' bLen mempty bRow finalTableau

          ( ParsedTableauRow aLen aRow Seq.:< at', _ )
              | aLen == n ->
                  trace ("Left biased case: " ++ show (btc - aLen + 1)) $
                  let b | aLen <= btc = FingerTree.singleton (TableauRowSkip (btc - aLen + 1))
                        | otherwise = mempty
                  in iterateRow at' bt aLen aRow b finalTableau

          _ -> let phantomA | n <= atc = FingerTree.singleton (TableauRowSkip (atc - n + 1))
                            | otherwise = FingerTree.empty
                   phantomB | n <= btc = FingerTree.singleton (TableauRowSkip (btc - n + 1))
                            | otherwise = FingerTree.empty
               in iterateRow at bt n phantomA phantomB finalTableau

    iterateRow at bt rowLen aRow bRow finalTableau =
        {-# SCC iterateRow #-}
        trace ("filling in row of length " ++ show rowLen) $
        let nextRow = ParsedTableauRow rowLen nextRowEntries

            matchingRows = getMatchingPairs (tcpIx (measure aRow)) rowLen finalTableau
            nextRowEntries = trace ("Wanting " ++ show (cellsNeeded, map (\(x, y) -> (map showTableauCell x, map showTableauCell y )) matchingRows)) (onlyLeft `seq` (onlyLeft >*< bRow))
              where onlyLeft =
                      computeCell cellsNeeded rowLen pp matchingRows aRow
                    cellsNeeded = min (atc - tcpIx (measure aRow)) (finalTokenCount - rowLen + 1 - tcpIx (measure aRow))

            nextTableau = addRow finalTableau nextRow
        in seq nextRow (seq nextRowEntries (seq nextTableau (go (rowLen + 1) at bt nextTableau)))

    addRow tableau nextRow@(ParsedTableauRow _ nextRowEntries)
        | tcpNonSparse (measure nextRowEntries) = tableau Seq.|> nextRow
        | otherwise = tableau

    finalizeTableau len tableau
        | len > finalTokenCount = tableau
        | otherwise =

            {-# SCC finalizeTableau #-}
            trace ("Computing row of length " ++ show (len, finalTokenCount) ++ ": should be of size " ++ show (finalTokenCount - len + 1)) $
            let matchingRows = getMatchingPairs 0 len tableau
                computed = trace ("Got " ++ show (length matchingRows) ++ " matching pairs") (computeCell (finalTokenCount - len + 1) len pp matchingRows mempty)

                nextRow = ParsedTableauRow len computed
                nextTableau = addRow tableau nextRow
            in trace ("Got comptued row " ++ show (measure computed)) $ seq nextRow (seq nextTableau (finalizeTableau (len + 1) nextTableau))

getRowColCount :: ParsedTableauRow tok -> Word
getRowColCount (ParsedTableauRow _ row) = tcpIx (measure row)

splitRow :: Word -> FingerTree TableauCellPosition (TableauCell tok)
         -> [ TableauCell tok ]
splitRow 0 row = toList row
splitRow i row =
--   case FingerTree.openZipper ((>=i).tcpIx) row of
--     FingerTree.FingerTreeZ TableauCellPosition { tcpIx = aLen } (TableauRowSkip m) z
--       | m > (i - aLen) ->
--           TableauRowSkip (m - (i - aLen)):FingerTree.zipperToList z
--     FingerTree.FingerTreeZ _ _ z -> FingerTree.zipperToList z
--     FingerTree.FingerTreeDone -> []


 let (a, b) = FingerTree.split ((>i) . tcpIx) row
     aLen = tcpIx (measure a)
 in if i == aLen
    then toList b
    else case FingerTree.viewl b of
           TableauRowSkip m FingerTree.:< b ->
             TableauRowSkip (m - (i - aLen)):toList b
           _ -> toList b

-- Return a list of all rows whose lengths together sum to the given
getMatchingPairs :: Word -> Word -> ParserTableau tok -> [ ( [ TableauCell tok],
                                                             [ TableauCell tok ] ) ]
getMatchingPairs start total tbl =
  {-# SCC getMatchingPairs #-}
  case Seq.viewl tbl of
    Seq.EmptyL -> []
    leftRow Seq.:< tbl' ->
      go leftRow tbl'
  where
    forward 0 xs = xs
    forward n (TableauRowSkip m:xs)
      | m <= n = forward (n - m) xs
      | otherwise = TableauRowSkip (m - n):xs
    forward n (x:xs) = forward (n - 1) xs

    go fullRow@(ParsedTableauRow leftLen leftRow) tbl'
      | rightLen == leftLen =
        let leftRow' = splitRow start leftRow
        in trace ("Splitting " ++ show (leftLen, rightLen)) $
           [ ( leftRow', forward leftLen leftRow' ) ]
      | otherwise =
          case Seq.viewr tbl' of
            Seq.EmptyR -> []
            tbl'' Seq.:> (ParsedTableauRow realRightLen rightRow)
              | realRightLen == rightLen ->
                  trace ("Splitting " ++ show (leftLen, rightLen, start + leftLen, rightRow)) $
                  let leftRow' = splitRow start leftRow
                      rightRow' = splitRow start rightRow
                  in (leftRow', forward leftLen rightRow'):
                     (rightRow', forward rightLen leftRow'):
                     getMatchingPairs start total tbl''
              | realRightLen > rightLen -> go fullRow tbl''
              | otherwise -> case Seq.viewl tbl' of
                               Seq.EmptyL -> []
                               row Seq.:< tbl''' -> go row tbl'''
      where rightLen = total - leftLen

-- getMatchingPairs :: Word -> ParserTableau tok -> [ ( [ TableauCell tok],
--                                                      [ TableauCell tok ] ) ]
-- getMatchingPairs total tbl =
--   case FingerTree.viewr tbl of
--     FingerTree.EmptyR -> []
--     tbl' FingerTree.:> ParsedTableauRow rightLen rightRow
--       | rightLen == leftLen -> [ ( toList rightRow, toList (splitRow rightLen rightRow) ) ]
--       | otherwise ->
--           case FingerTree.viewl tbl'' of
--             ParsedTableauRow realLeftLen leftRow FingerTree.:< tbl''' ->
--               let leftRight = ( toList leftRow, toList (splitRow leftLen rightRow) )
--                   rightLeft = ( toList rightRow, toList (splitRow rightLen leftRow) )
--               in leftRight:rightLeft:getMatchingPairs total tbl'''
--             _ -> getMatchingPairs total tbl''
--       where leftLen = total - rightLen
--
--             (_, tbl'') = FingerTree.split (\(Last leftSize) -> maybe False (>= leftLen) leftSize) tbl'

--  case FingerTree.viewl tbl of
--    FingerTree.EmptyL -> []
--    leftRow FingerTree.:< tbl' ->
--      go leftRow tbl'
--  where
--    go fullRow@(ParsedTableauRow leftLen leftRow) tbl'
--      | rightLen == leftLen = [ ( toList leftRow, toList (splitRow leftLen leftRow) ) ]
--      | otherwise =
--          case FingerTree.viewr tbl' of
--            FingerTree.EmptyR -> []
--            tbl'' FingerTree.:> (ParsedTableauRow realRightLen rightRow)
--              | realRightLen == rightLen -> (toList leftRow, toList (splitRow leftLen rightRow)):(toList rightRow, toList (splitRow rightLen leftRow)):getMatchingPairs total tbl''
--              | otherwise -> go fullRow tbl''
--      where rightLen = total - leftLen


newtype CellRun tok = CellRun { unCellRun :: [ TableauCell tok ] }

instance Monoid (CellRun tok) where
  mempty = CellRun []
  mappend = (<>)

instance Semigroup (CellRun tok) where
  CellRun a <> CellRun b = CellRun (go a b)
    where
      go (TableauRowSkip m:as) (TableauRowSkip n:bs)
        | m < n = TableauRowSkip m:go as (TableauRowSkip (n - m):bs)
        | m > n = TableauRowSkip n:go (TableauRowSkip (m - n):as) bs
        | otherwise = TableauRowSkip m:go as bs
      go (TableauRowSkip m:as) (cell:bs)
        | m == 1 = cell:go as bs
        | otherwise = cell:go (TableauRowSkip (m - 1):as) bs
      go (cell:as) (TableauRowSkip n:bs)
        | n == 1 = cell:go as bs
        | otherwise = cell:go as (TableauRowSkip (n - 1):bs)
      go (TableauCell l:as) (TableauCell r:bs) =
        TableauCell (l <> r):go as bs
      go [] bs = bs
      go as [] = as

computeCell :: Word -> Word -> Parser tok a
            -> [ ( [ TableauCell tok ],
                   [ TableauCell tok ] ) ]
            -> FingerTree TableauCellPosition (TableauCell tok)
            -> FingerTree TableauCellPosition (TableauCell tok)
computeCell tokCnt len
            Parser { parserRules = rules
                   , parserCombinators = combinators }
            matchingRows initialAccum =
  rest `seq` (initialAccum >*< rest)
--  go tokCnt 0 matchingRows initialAccum
  where
    rest = FingerTree.fromList cellList
    cellList = unCellRun (foldMap CellRun (map (takeOnly tokCnt . uncurry (mergeRow 0)) matchingRows))

    takeOnly tokCnt (TableauRowSkip n:xs)
      | n < tokCnt = TableauRowSkip n:takeOnly (tokCnt - n) xs
      | otherwise = [ TableauRowSkip tokCnt ]
    takeOnly 1 (cell@(TableauCell {}):xs) = [ cell ]
    takeOnly n (cell:xs) = cell:takeOnly (n - 1) xs
    takeOnly 0 [] = []
    takeOnly n [] = [ TableauRowSkip n ]

    spanLength n pred v
      | UV.null v = n
      | pred (UV.unsafeHead v) = spanLength (n + 1) pred (UV.unsafeTail v)
      | otherwise = n

    mergeRow !skip [] (TableauRowSkip n:xs) = TableauRowSkip (n + skip):xs
    mergeRow skip (TableauRowSkip n:xs)  []= TableauRowSkip (n + skip):xs
    mergeRow skip [] x | skip == 0 = x
                       | otherwise = TableauRowSkip skip:x
    mergeRow skip x [] | skip == 0 = x
                       | otherwise = TableauRowSkip skip:x
    mergeRow skip (TableauRowSkip n:as) (TableauRowSkip m:bs)
      | n < m = mergeRow (n + skip) as (TableauRowSkip (m - n):bs)
      | n > m = mergeRow (m + skip) (TableauRowSkip (n - m):as) bs
      | otherwise = mergeRow (m + skip) as bs
    mergeRow skip (TableauCell {}:as) (TableauRowSkip m:bs) =
      let bs' | m == 1 = bs
              | otherwise = TableauRowSkip (m - 1):bs
      in mergeRow (1 + skip)as bs'
    mergeRow skip (TableauRowSkip n:as) (TableauCell {}:bs) =
      let as' | n == 1 = as
              | otherwise = TableauRowSkip (n - 1):as
      in mergeRow (1 + skip) as' bs
    mergeRow skip (TableauCell leftProds:as) (TableauCell rightProds:bs) =
      let nextProds = do
            (l, la) <- leftProds
            (r, ra) <- rightProds
            case trace ("Lookup " ++ show (l, r)) $ lookupSequence rules l r of
              Nothing -> empty
              Just (i, nextProduction) -> do
                let pair = productionPair l r
                    rules' = UV.unsafeDrop i rules
                    ruleCnt = spanLength 0 ((== pair) . fst) rules'

                j <- V.enumFromN i ruleCnt
                let f = trace ("Got ruule index " ++ show j) (V.unsafeIndex combinators j)
                pure (snd (UV.unsafeIndex rules j), f la ra)
      in if V.null nextProds
         then mergeRow (skip + 1) as bs
         else if skip == 0
              then nextProds `seq` (TableauCell nextProds:mergeRow 0 as bs)
              else TableauRowSkip skip:TableauCell nextProds:mergeRow 0 as bs

--    go 0 skip _ !accum
--      | skip == 0 = accum
--      | otherwise = accum |>* TableauRowSkip skip
--    go !n !skip [] !accum
--      | skip == 0 = accum
--      | otherwise = accum |>* TableauRowSkip skip
--    go !n !skip rows !accum =
--      let (nextCell, rows') = compute rows [] []
--      in trace ("Got next cell with " ++ show (V.length nextCell) ++ " productions") $
--         if V.null nextCell
--         then go (n - 1) (skip + 1) rows' accum
--         else let accum' | skip == 0 = accum
--                         | otherwise = accum |>* TableauRowSkip skip
--              in trace ("Skip is " ++ show skip) $
--                 go (n - 1) 0 rows' (accum' |>* TableauCell nextCell)
--
--    compute [] rows' a = (V.concat a, rows')
--    compute ((leftRow, rightRow):rows) rows' a =
--      trace ("Compute rows " ++ show (fmap showTableauCell (toList leftRow), fmap showTableauCell (toList rightRow))) $
--      case ( leftRow, rightRow ) of
--        ( [], _ ) -> compute rows rows' a
--        ( _, [] ) -> compute rows rows' a
--        ( TableauRowSkip 1:leftRow',
--          TableauRowSkip 1:rightRow' ) ->
--          compute rows ((leftRow', rightRow'):rows') a
--        ( TableauRowSkip 1:leftRow',
--          TableauRowSkip n:rightRow' ) ->
--          compute rows ((leftRow', TableauRowSkip (n - 1):rightRow'):rows') a
--        ( TableauRowSkip n:leftRow',
--          TableauRowSkip 1:rightRow' ) ->
--          compute rows ((TableauRowSkip (n - 1): leftRow', rightRow'):rows') a
--        ( TableauRowSkip 1:leftRow',
--          TableauCell {}:rightRow' ) ->
--          compute rows ((leftRow', rightRow'):rows') a
--        ( TableauCell {}:leftRow',
--          TableauRowSkip 1:rightRow' ) ->
--          compute rows ((leftRow', rightRow'):rows') a
--        ( TableauCell {}:leftRow',
--          TableauRowSkip n:rightRow' ) ->
--          compute rows ((leftRow', TableauRowSkip (n - 1):rightRow'):rows') a
--        ( TableauRowSkip n:leftRow',
--          TableauCell {}:rightRow' ) ->
--          compute rows ((TableauRowSkip (n - 1):leftRow', rightRow'):rows') a
--        ( TableauRowSkip nl:leftRow',
--          TableauRowSkip nr:rightRow' ) ->
--          compute rows ((TableauRowSkip (nl - 1):leftRow', TableauRowSkip (nr - 1):rightRow'):rows') a
--        ( TableauCell leftProds:leftRow',
--          TableauCell rightProds:rightRow' ) ->
--          trace ("Got prods " ++ show (fmap fst leftProds, fmap fst rightProds)) $
--          let next = do
--                (l, la) <- leftProds
--                (r, ra) <- rightProds
--                case trace ("Lookup " ++ show (l, r)) $ lookupSequence rules l r of
--                  Nothing -> empty
--                  Just (i, nextProduction) ->
--                    trace ("FOund for " ++ show (l, r)) $
--                    let f = V.unsafeIndex combinators i
--                    in pure (nextProduction, f la ra)
--          in compute rows ((leftRow', rightRow'):rows') (next:a)

-- updateParser :: TokenPosition -> [ token ] -> Parsed tok a -> Parsed tok a

lookupNext :: UV.Vector (Word64, Word32) -> Word32 -> UV.Vector (Word64, Word32)
lookupNext v b =
  let p = productionPair b 0
      i = bsearch v p
  in UV.unsafeDrop i v

{-# INLINE lookupSequence #-}
lookupSequence :: ProductionRules -> Word32 -> Word32 -> Maybe (Int, Word32)
lookupSequence v a b =
  let p = productionPair a b
      i = bsearch v p

      (p', next) = UV.unsafeIndex v i
  in if p == p' then Just (i, next) else Nothing

{-# INLINE bsearch #-}
{-# SPECIALIZE bsearch :: UV.Vector (Word64, Word32) -> Word64 -> Int #-}
{-# SPECIALIZE bsearch :: forall v. V.Vector (Word32, v) -> Word32 -> Int #-}
bsearch :: (Ord k, GV.Vector vector (k, v)) => vector (k, v) -> k -> Int
bsearch vs k = loop 0 (GV.length vs)
  where
    loop !l !u
      | u <= l = l
      | otherwise = let i = midpoint l u
                        (k', _)  = GV.unsafeIndex vs i
                    in case compare k' k of
                         LT -> loop (i + 1) u
                         _ -> loop l i

    midpoint !l !u = fromIntegral (((fromIntegral l :: Word) + fromIntegral u) `div` 2)

productionPair :: Word32 -> Word32 -> Word64
productionPair a b = (fromIntegral a `shiftL` 32) .|. fromIntegral b

decomposePair :: Word64 -> (Word32, Word32)
decomposePair a = (fromIntegral (a `shiftR` 32), fromIntegral (a .&. 0xFFFFFFFF))

-- Parser building

data GenericRuleSpec = GenericRuleSpec {-# UNPACK #-} !Word64 {-# UNPACK #-} !Word32 (Any -> Any -> Any)
data SingleProductionSpec tok = SingleProductionSpec { spsCls, spsDest :: {-# UNPACK #-} !Word32
                                                     , spsMk :: tok -> Any }

instance Measured (Last Word64) GenericRuleSpec where
  measure (GenericRuleSpec a _ _) = Last (Just a)
instance Measured (Last Word32) (SingleProductionSpec tok) where
  measure sps = Last (Just (spsCls sps))

data ProdSpec tok cls a
  = ProdSpec
  { psRule :: RuleIx a
  , psBuild :: RuleB tok cls a
  , psDerivedFrom :: DM.DMap ProdIx (Const ())
  }

newtype ParserBuilder tok classification a
  = ParserBuilder { runParserBuilder ::
                      State (Word32, Word32,
                             DM.DMap ProdIx (ProdSpec tok classification)) a }
  deriving (Functor, Monad, MonadFix, Applicative)

--data Rule tok cls a
--  = Rule [a] (RuleB tok cls a) (RuleIx a)

data Keyed k v = Keyed k v deriving Show

instance Measured (Last k) (Keyed k v) where
    measure (Keyed k _) = Last (Just k)

addRuleSpec :: (Ord k, Measured (Last k) spec)
            => spec -> FingerTree (Last k) spec
            -> FingerTree (Last k) spec
addRuleSpec s ft =
  let Last lastS = measure s
      (a, b) = FingerTree.split (\(Last k) -> fromMaybe False $ do
                                                k' <- k
                                                lastS' <- lastS
                                                pure (lastS' <= k')) ft
  in (a FingerTree.|> s) FingerTree.>< b

simplifyParser :: HasCallStack => Parser tok a -> Parser tok a
simplifyParser p = runST $ do

  singleMarks <- MV.replicate (V.length (parserSingleRules p)) False
  seqMarks <- MV.replicate (UV.length (parserRules p)) False

  let Max maxRule = foldMap (Max . fst . snd) (parserSingleRules p) <>
                    foldMap (Max . snd) (UV.toList (parserRules p))
  seen <- MV.replicate (fromIntegral maxRule + 1) False
  MV.write seen (fromIntegral $ parserFinal p) True

  let cullRules = do
        validSingleIndices <- V.findIndices id <$> V.freeze singleMarks
        validSeqIndices <- V.findIndices id <$> V.freeze seqMarks

        pure ( V.backpermute (parserSingleRules p) validSingleIndices
             , UV.backpermute (parserRules p) (UV.fromList (V.toList validSeqIndices))
             , V.backpermute (parserCombinators p) validSeqIndices )

      mark [] = cullRules
      mark (nextRule:rules) = do
        forM_ (V.indexed (parserSingleRules p)) $ \(i, (_, (dst, _))) ->
          when (dst == nextRule) $
            markSingle i

        rules' <-
           foldrM (\(i, (seq, dst)) rules' ->
                     if dst == nextRule
                     then do
                       let (left, right) = decomposePair seq
                       rules'' <- visit left rules'
                       rules''' <- visit right rules''
                       markSeq i
                       pure rules'''
                     else pure rules')
                  rules (zip [0..] (UV.toList (parserRules p)))

        mark rules'

      markSingle i =
        MV.write singleMarks i True
      markSeq i =
        MV.write seqMarks i True

      visit n rules = do
        alreadySeen <- MV.read seen (fromIntegral n)
        if alreadySeen then pure rules
          else do
            MV.write seen (fromIntegral n) True
            pure (n:rules)

  (single', rules', combinators) <- mark [parserFinal p]

  pure p { parserSingleRules = single'
         , parserRules = rules'
         , parserCombinators = combinators }

compile :: forall tok classification a
         . (Enum classification, Bounded classification)
        => (tok -> classification) -> ParserBuilder tok classification (RuleB tok classification a) -> Parser tok a
compile classifier (ParserBuilder build) =
    let buildRules = do
          startRuleB <- build

          (nextRule, nextProd, rules) <- get
          let startAlts = map (\r -> ProdSpec startRule r DM.empty) (deAlt startRuleB)
              startRule = RuleIx nextRule
          put ( nextRule + 1, nextProd + fromIntegral (length startAlts)
              , foldr (uncurry DM.insert) rules (zip (map ProdIx [nextProd..]) startAlts) )

          runParserBuilder removeMany
          runParserBuilder liftTerminals
          runParserBuilder elimBin
          runParserBuilder inlineConstants -- DEL rlue
          runParserBuilder inlineSingletons -- UNIT rule

          pure startRule

        (RuleIx startRuleIx, (_, _, rules)) = runState buildRules (0, 0, DM.empty)

        ruleList = DM.toAscList rules

        singles = V.fromList . sortBy (comparing fst) $ do
          _ DM.:=> ProdSpec (RuleIx rule) (Ap (Pure fn) (Terminal cls mkTok)) _ <- ruleList
          pure ( fromIntegral (fromEnum cls), (rule, fmap (fmap (unsafeCoerce . fn)) mkTok) )

        (trans, combinators) = unzip .
                               sortBy (comparing (fst . fst)) $
                               [ ( (productionPair xIx yIx, ruleIx )
                                       , \x y -> unsafeCoerce (fn (unsafeCoerce x) (unsafeCoerce y)) )
                               | _ DM.:=> ProdSpec (RuleIx ruleIx)
                                            (Ap (Ap (Pure fn) (EmbedRule (RuleIx xIx)))
                                                (EmbedRule (RuleIx yIx))) _ <- ruleList ]

    in simplifyParser $
       Parser { parserTokenClassifier = classifier
              , parserSingleRules = singles
              , parserFinal = startRuleIx
              , parserCombinators = V.fromList combinators
              , parserRules = UV.fromList trans
              , parserEmptyMatches = [] {- TODO empty matches -} }

reallyReallyUnsafeOptimizationEquality :: a -> b -> Bool
reallyReallyUnsafeOptimizationEquality a b =
  case reallyUnsafePtrEquality# a (unsafeCoerce# b) of
    0# -> False
    _  -> True

data SomeMaker tok where
  SomeMaker :: (tok -> Maybe a) -> SomeMaker tok

liftTerminals :: Enum cls => ParserBuilder tok cls ()
liftTerminals = do
  (_, _, rules) <- ParserBuilder get

  (rules', _) <- flip runStateT M.empty $
                 DM.traverseWithKey (\x ps -> do
                                        prod' <- liftProdTerminal (psBuild ps)
                                        pure (ps { psBuild = prod' })) rules

  ParserBuilder (modify (\(nextRule, nextProd, rules'') -> (nextRule, nextProd, DM.union rules' rules'')))

  where
    liftProdTerminal :: Enum cls => RuleB tok cls a
                     -> StateT (M.Map Int [(SomeMaker tok, Word32)])
                               (ParserBuilder tok cls) (RuleB tok cls a)
    liftProdTerminal (Ap fn x) = Ap <$> liftProdTerminal fn <*> liftProdTerminal x
    liftProdTerminal (Many x)  = Many <$> liftProdTerminal x
    liftProdTerminal (Terminal cls mk) = do
      terms <- get
      case M.lookup (fromEnum cls) terms of
        Just makers
          | Just (_, rule) <- find (\(SomeMaker mkr, _) -> reallyReallyUnsafeOptimizationEquality mkr mk) makers -> pure (EmbedRule (RuleIx rule))
        found -> do
          (nextRule, nextProd, _) <- lift (ParserBuilder get)
          let makers = fromMaybe [] found
              makers' = (SomeMaker mk, nextRule):makers
          lift (ParserBuilder (modify (\(nextRule, _, rules) -> (nextRule + 1, nextProd + 1, DM.insert (ProdIx nextProd) (ProdSpec (RuleIx nextRule) (Terminal cls mk) DM.empty) rules))))
          modify (M.insert (fromEnum cls) makers')
          pure (EmbedRule (RuleIx nextRule))
    liftProdTerminal x = pure x

removeMany :: ParserBuilder tok cls ()
removeMany = do
  (_, _, rules) <- ParserBuilder get

  rules' <-
    DM.traverseWithKey (\_ prod -> do
                           prod' <- removeMany (psBuild prod)
                           pure (prod { psBuild = prod' })) rules

  ParserBuilder (modify (\(nextRule, nextProd, rules'') -> (nextRule, nextProd, DM.union rules' rules'')))
  where
    removeMany :: RuleB tok cls a -> ParserBuilder tok cls (RuleB tok cls a)
    removeMany (Ap f x) = Ap <$> removeMany f <*> removeMany x
    removeMany (Many f) = do
      (nextRule, nextProd, rules) <- ParserBuilder get
      ParserBuilder (put (nextRule + 2, nextProd + 3, rules))

      f' <- removeMany f

      ParserBuilder $ modify $ \(nextRule', nextProd', rules') ->
        let rules'' = DM.insert (ProdIx nextProd) (ProdSpec ruleIx (Pure []) DM.empty) $
                      DM.insert (ProdIx (nextProd + 1)) (ProdSpec ruleIx (Ap (Ap (Pure (:)) (EmbedRule elemRuleIx)) (EmbedRule ruleIx)) DM.empty)  $
                      DM.insert (ProdIx (nextProd + 2)) (ProdSpec elemRuleIx f' DM.empty) $
                      rules'

            elemRuleIx = RuleIx (nextRule + 1)
            ruleIx = RuleIx nextRule
        in (nextRule', nextProd', rules'')

      pure (EmbedRule (RuleIx nextRule))
    removeMany x = pure x

data SeparatedRule tok cls a where
  SeparatedRule :: (a -> b) -> RuleB tok cls a -> SeparatedRule tok cls b

elimBin :: ParserBuilder tok cls ()
elimBin = do
  (_, _, rules) <- ParserBuilder get

  rules' <-
    DM.traverseWithKey (\_ prod -> do
                           prod' <- elimBinProd id (psBuild prod)
                           pure (prod { psBuild = prod' })) rules

  ParserBuilder (modify (\(nextRule, nextProd, rules'') -> (nextRule, nextProd, DM.union rules' rules'')))
  where
    elimBinProd :: (b -> c) -> RuleB tok cls b -> ParserBuilder tok cls (RuleB tok cls c)
    elimBinProd f (Pure a) =
      pure (Pure (f a))
    elimBinProd f (EmbedRule ix) =
      pure (Ap (Pure f) (EmbedRule ix))
    elimBinProd f (Ap (Pure fn) x) =
      elimBinProd (f . fn) x
    elimBinProd f (Ap (Ap (Pure fn) x) y) = do
      SeparatedRule transformX xRule <- separateRule id x
      SeparatedRule transformY yRule <- separateRule id y
      case (xRule, yRule) of
        (Pure x', Pure y') ->
          pure (Pure (f (fn (transformX x') (transformY y'))))
        (Pure x', _) ->
          pure (Ap (Pure (\y' -> f (fn (transformX x') (transformY y')))) yRule)
        (_, Pure y') ->
          pure (Ap (Pure (\x' -> f (fn (transformX x') (transformY y')))) xRule)
        _ ->
          pure (Ap (Ap (Pure (\x' y' -> f (fn (transformX x') (transformY y')))) xRule) yRule)
    elimBinProd f (Ap fn x) = do
      SeparatedRule transformFn fnRule <- separateRule id fn
      SeparatedRule transformX  xRule  <- separateRule id x
      case (fnRule, xRule) of
        (Pure fn', Pure x') ->
          pure (Pure (f ((transformFn fn') (transformX x'))))
        (Pure fn', _) ->
          pure (Ap (Pure (\x' -> f ((transformFn fn') (transformX x')))) xRule)
        (_, Pure x') ->
          pure (Ap (Pure (\fn' -> f ((transformFn fn') (transformX x')))) fnRule)
        _ ->
          pure (Ap (Ap (Pure (\fn' x' -> f ((transformFn fn') (transformX x')))) fnRule) xRule)
    elimBinProd f x =
      pure (Ap (Pure f) x)

    separateRule :: (b -> c) -> RuleB tok cls b -> ParserBuilder tok cls (SeparatedRule tok cls c)
    separateRule f (Pure x) =
      pure (SeparatedRule f (Pure x))
    separateRule f (Ap (Pure fn) x) =
      separateRule (f . fn) x
    separateRule f (EmbedRule ruleIx) =
      pure (SeparatedRule f (EmbedRule ruleIx))
    separateRule f rule = do
      -- Allocate new rule
      rule' <- elimBinProd f rule
      case rule' of
        Pure x -> pure (SeparatedRule id rule')
        _ -> do
          (nextRule, _, _) <- ParserBuilder get
          let nextRuleIx = RuleIx nextRule
          ParserBuilder (modify (\(nextRule, nextProd, rules) ->
                                   (nextRule + 1, nextProd + 1,
                                    DM.insert (ProdIx nextProd) (ProdSpec nextRuleIx rule' DM.empty) rules)))
          pure (SeparatedRule id (EmbedRule nextRuleIx))

rewrite :: (forall a. Word32 -> DM.DMap ProdIx (ProdSpec tok cls) -> ProdIx a -> ProdSpec tok cls a -> ParserBuilder tok cls (ProdSpec tok cls a))
        -> ParserBuilder tok cls ()
rewrite doRewrite = go 0
  where
    go startProd =  do
      (_, lastProd, _) <- ParserBuilder get

      onePass startProd

      (_, lastProd', _) <- ParserBuilder get

      if lastProd' == lastProd
        then pure ()
        else go lastProd

    onePass startProd = do
      (_, _, rules) <- ParserBuilder get

      DM.traverseWithKey (doRewrite startProd rules) rules

inlineConstants :: ParserBuilder tok cls ()
inlineConstants = rewrite rewriteLit >> removeAllConstants
  where
    removeAllConstants :: ParserBuilder tok cls ()
    removeAllConstants =
      ParserBuilder $ do
        modify (\(rule, prod, rs) -> (rule, prod, DM.filterWithKey (\_ (ProdSpec _ rule _) -> case rule of { Pure {} -> False; _ -> True }) rs))

    rewriteLit :: Word32 -> DM.DMap ProdIx (ProdSpec tok cls)
               -> ProdIx a -> ProdSpec tok cls a -> ParserBuilder tok cls (ProdSpec tok cls a)
    rewriteLit startFrom rules prodIx rule =
      case psBuild rule of
        Ap (Pure fn) x -> do
          forM_ (lookupLits startFrom rules x) $ \(xSpec, xLit) ->
            addSpec rule xSpec (Pure (fn xLit))
          pure rule
        Ap (Ap (Pure fn) x) y -> do
          let xLits = lookupLits startFrom rules x
              yLits = lookupLits startFrom rules y
          forM_ xLits $ \(fromSpec, xLit) ->
            addSpec rule fromSpec (Ap (Pure (fn xLit)) y)
          forM_ yLits $ \(fromSpec, yLit) ->
            addSpec rule fromSpec (Ap (Pure (\x -> fn x yLit)) x)
          forM_ ((,) <$> xLits <*> yLits) $ \((xSpec, xLit), (ySpec, yLit)) ->
            addSpec rule (DM.union xSpec ySpec) (Pure (fn xLit yLit))
          pure rule
        _ -> pure rule

    addSpec :: ProdSpec tok cls a -> DM.DMap ProdIx (Const ()) -> RuleB tok cls a -> ParserBuilder tok cls ()
    addSpec origSpec newDeps newProd = do
      ParserBuilder $ do
        (_, lastProd, _) <- get
        modify (\(rule, prod, rs) -> (rule, prod + 1, DM.insert (ProdIx lastProd) (ProdSpec (psRule origSpec) newProd (DM.union (psDerivedFrom origSpec) newDeps)) rs))

    lookupLits :: Word32 -> DM.DMap ProdIx (ProdSpec tok cls) -> RuleB tok cls a -> [ (DM.DMap ProdIx (Const ()), a) ]
    lookupLits startFrom rules (EmbedRule ruleIx) =
      [ (newDeps, x)
      | ProdIx thisProdIx DM.:=> ProdSpec (DM.geq ruleIx -> Just DM.Refl) (Pure x) newDeps <- DM.toList rules
      , thisProdIx >= startFrom ]
    lookupLits startFrom rules _ = []

data UsefulProduction tok cls c where
  UsefulProduction :: (a -> b -> c) -> RuleB tok cls a -> RuleB tok cls b -> UsefulProduction tok cls c
  UsefulTerminal :: (a -> b) -> cls -> (tok -> Maybe a) -> UsefulProduction tok cls b

inlineSingletons :: ParserBuilder tok cls ()
inlineSingletons = rewrite rewriteUnit >> removeAllUnits
  where
    removeAllUnits :: ParserBuilder tok cls ()
    removeAllUnits =
      ParserBuilder $
      modify (\(rule, prod, rs) -> (rule, prod, DM.filterWithKey (\_ -> not . isUnit) rs))

    isUnit :: ProdSpec tok cls a -> Bool
    isUnit a = countRules (psBuild a) == 1

    countRules :: RuleB tok cls a -> Int
    countRules (Ap a b) = countRules a + countRules b
    countRules (Pure {}) = 0
    countRules (EmbedRule {}) = 1
    countRules (Alt a b) = countRules a + countRules b
    countRules (Many a) = countRules a
    countRules Empty = 0
    countRules (Terminal {}) = 0

    rewriteUnit :: Word32 -> DM.DMap ProdIx (ProdSpec tok cls)
                -> ProdIx a -> ProdSpec tok cls a -> ParserBuilder tok cls (ProdSpec tok cls a)
    rewriteUnit startFrom rules prodIx rule =
      case psBuild rule of
        Ap (Pure fn) (EmbedRule x) -> do
          let xProds = lookupUsefulProductions startFrom rules x
          forM_ xProds $ \prod ->
            case prod of
              UsefulProduction cmb a b ->
                addSpec rule (Ap (Ap (Pure (\x y -> fn (cmb x y))) a) b)
              UsefulTerminal fn' cls mk ->
                addSpec rule (Ap (Pure (fn . fn')) (Terminal cls mk))
          pure rule

        EmbedRule x -> do
          rewriteUnit startFrom rules prodIx (rule { psBuild = Ap (Pure id) (EmbedRule x) })

        _ -> pure rule

    addSpec :: ProdSpec tok cls a -> RuleB tok cls a -> ParserBuilder tok cls ()
    addSpec orig newRule =
      ParserBuilder $ do
      modify (\(rule, prod, rs) -> (rule, prod + 1, DM.insert (ProdIx prod) (ProdSpec (psRule orig) newRule (psDerivedFrom orig)) rs))

    lookupUsefulProductions :: Word32 -> DM.DMap ProdIx (ProdSpec tok cls)
                            -> RuleIx a -> [ UsefulProduction tok cls a ]
    lookupUsefulProductions startFrom rules whichRule =
      [ UsefulProduction fn x y
      | ProdIx thisProdIx DM.:=> ProdSpec (DM.geq whichRule -> Just DM.Refl) (Ap (Ap (Pure fn) x) y) _
           <- DM.toAscList rules
      , thisProdIx >= startFrom ] ++
      [ UsefulTerminal fn cls mk
      | ProdIx thisProdIx DM.:=> ProdSpec (DM.geq whichRule -> Just DM.Refl) (Ap (Pure fn) (Terminal cls mk)) _
           <- DM.toAscList rules
      , thisProdIx >= startFrom ]

newtype RuleIx a = RuleIx { unRuleIx :: Word32 } deriving Show
newtype ProdIx a = ProdIx Word32 deriving Show

instance DM.GEq ProdIx where
  geq (ProdIx a) (ProdIx b)
    | a == b = Just (unsafeCoerce DM.Refl)
    | otherwise = Nothing

instance DM.GEq RuleIx where
  geq (RuleIx a) (RuleIx b)
    | a == b = Just (unsafeCoerce DM.Refl)
    | otherwise = Nothing

instance DM.GCompare ProdIx where
  gcompare (ProdIx a) (ProdIx b) =
    case compare a b of
      LT -> DM.GLT
      GT -> DM.GGT
      EQ -> unsafeCoerce DM.GEQ

-- production :: Enum cls
--            => ParserBuilder tok cls (RuleIx a)
-- production = ParserBuilder $ do
--                (nextNm, rules) <- get
--                put (nextNm + 1, rules)
--                pure (RuleIx nextNm)

data Sym = A | B | C | Star | Error
  deriving (Show, Enum, Bounded)

charToSym :: Char -> Sym
charToSym 'a' = A
charToSym 'b' = B
charToSym 'c' = C
charToSym '*' = Star
charToSym _ = Error

data AST = A' | B' | C' | Mul AST AST
           deriving Show

-- simpleParser :: Parser Char AST
-- simpleParser = compile id $ mdo
-- 
--   varProd <- production
-- 
--   varProd <=. ('a', \_ -> A')
--   varProd <=. ('b', \_ -> B')
--   varProd <=. ('c', \_ -> C')
-- 
--   starProd <- production
--   starProd <=. ('*', \_ -> ())
-- 
--   mulProd <- production
--   mulProd <=* (\_ b -> trace ("Making b " ++ show b) (\a -> Mul a b), starProd, varProd)
-- 
--   varProd <=* (\a f -> f a, varProd, mulProd)
-- 
--   pure (Rule [] Empty varProd)

testParse :: Parser Char a -> String -> [a]
testParse pp s =
  let t = T.pack s
      res = parse 50 pp t
  in getParseResult pp res

getTestParsed :: Parser Char a -> String -> Parsed Char a
getTestParsed pp s = parse 50 pp (T.pack s)

getTestParsedText :: Parser Char a -> T.Text -> Parsed Char a
getTestParsedText pp = parse 50 pp

printParsedTableau :: Parsed tok a -> IO ()
printParsedTableau (Parsed tbl _) = go tbl
    where
      go cur =
          case Seq.viewl cur of
            Seq.EmptyL -> pure ()
            ParsedTableauRow len row Seq.:< cur' -> do
              putStr ("Length " ++ show len ++ ": ")
              forM_ row $ \cell ->
                  case cell of
                    TableauCell ps -> putStr (show (fmap fst ps) ++ " ")
                    TableauRowSkip w -> putStr ("<" ++ show w ++ "> ")
              putStr "\n"
              go cur'

-- Rule builder applicative

data RuleB tok cls a where
    Pure :: a -> RuleB tok cls a
    -- Embed :: (forall b. (a -> b) -> RuleIx b -> ParserBuilder tok cls ()) -> RuleB tok cls a
    Terminal :: cls -> (tok -> Maybe a) -> RuleB tok cls a
    EmbedRule :: RuleIx a -> RuleB tok cls a
    Ap :: RuleB tok cls (a -> b) -> RuleB tok cls a -> RuleB tok cls b

    Alt :: RuleB tok cls a -> RuleB tok cls a -> RuleB tok cls a

    Many :: RuleB tok cls a -> RuleB tok cls [a]
    Empty :: RuleB tok cls a

instance Functor (RuleB tok cls) where
    fmap fn (Pure x) = Pure (fn x)
    fmap fn (Ap fn' b) = Ap (fmap (fmap fn) fn') b
    fmap fn x = Ap (Pure fn) x

instance Applicative (RuleB tok cls) where
    pure = Pure
    Pure fn <*> Pure x = Pure (fn x)
    a <*> Pure x = fmap ($ x) a
    a <*> b = Ap a b

instance Alternative (RuleB tok cls) where
    Empty <|> x  = x
    x <|> Empty  = x
    a <|> b = Alt a b
    empty = Empty

    many = Many
    some x =
      (:) <$> x <*> many x

data MappedRule tok cls a where
  MappedRule :: (b -> a) -> [a] -> RuleIx b -> MappedRule tok cls a

showRuleB :: Enum cls => RuleB tok cls a -> String
showRuleB (Pure x) = "(Pure _)"
showRuleB (Terminal cls _) = "(Terminal " ++ show (fromEnum cls) ++ ")"
showRuleB (EmbedRule {}) = "EmbedRule"
showRuleB (Ap fn x) = "(Ap " ++ showRuleB fn ++ " " ++ showRuleB x ++ ")"
showRuleB (Alt a b) = "(Alt " ++ showRuleB a ++ " " ++ showRuleB b ++ ")"
showRuleB (Many x) = "(Many " ++ showRuleB x ++ ")"
showRuleB Empty = "Empty"

buildRule :: Enum cls => RuleB tok cls a -> ParserBuilder tok cls (RuleB tok cls a)
buildRule rule =
  ParserBuilder $ do
    (ruleIx, prodIx, prods) <- get
    let nextRuleIx = RuleIx ruleIx
        alts = deAlt rule

        prods' = foldr (\(prodIx', alt') -> DM.insert (ProdIx prodIx') (ProdSpec nextRuleIx alt' DM.empty)) prods (zip [prodIx..] alts)

    put (ruleIx + 1, prodIx + fromIntegral (length alts), prods')
    pure (EmbedRule nextRuleIx)

deAlt :: Enum cls => RuleB tok cls a -> [ RuleB tok cls a ]
deAlt Empty = []
deAlt (Alt a b) = deAlt a ++ deAlt b
deAlt (Ap fn a) = Ap <$> deAlt fn <*> deAlt a
deAlt (Many x) = Many <$> deAlt x
deAlt x = pure x

--     do n <- production
--        let alts = deAlt rule
--        empties <- mconcat <$> mapM (\r -> produceRule id r n) alts
--        return (Rule empties rule n)
-- 
--     where
--       deAlt :: Enum cls => RuleB tok cls a -> [ RuleB tok cls a ]
--       deAlt Empty = []
--       deAlt (Alt a b) =
--         deAlt a ++ deAlt b
--       deAlt (Pure a) = [ Pure a ]
--       deAlt (Ap fn a) = Ap <$> deAlt fn <*> deAlt a
--       deAlt (EmbedRule r) = [ EmbedRule r ]
--       deAlt (Embed mk) = [ Embed mk ]
-- 
--       getRule :: Enum cls => (a -> b) -> RuleB tok cls a -> ParserBuilder tok cls (MappedRule tok cls b)
--       getRule fmapped (EmbedRule ~(Rule xs _ w)) = pure (MappedRule fmapped (fmapped <$> xs) w)
--       getRule fmapped (Ap (Pure fn) a) =
--         getRule (fmapped . fn) a
--       getRule fmapped x = do
--         pr <- production
--         xs <- produceRule fmapped x pr
--         pure (MappedRule id xs pr)
-- 
--       produceRule :: Enum cls => (a -> b) -> RuleB tok cls a -> RuleIx b -> ParserBuilder tok cls [b]
--       produceRule fmapped (Pure a) _ = pure [ fmapped a ]
--       produceRule fmapped (Ap fn a) rule =
--           case fn of
--             Pure fn ->
--               produceRule (fmapped . fn) a rule
--             Ap (Pure fn) b ->
--                 do MappedRule xMap xs xRule <- getRule id b
--                    MappedRule yMap ys yRule <- getRule id a
-- 
--                    rule <=* (\x y -> fmapped (fn (xMap x) (yMap y)), xRule, yRule)
-- 
--                    yLits <- fmap mconcat . forM ys $ \y ->
--                      produceRule (fmapped . (\x -> fn x y)) b rule
--                    xLits <- fmap mconcat . forM xs $ \x ->
--                      produceRule (fmapped . fn x) a rule
-- 
--                    pure (xLits ++ (fmapped <$> (fn <$> xs <*> ys)))
--             fn ->
--                 do MappedRule fnMap fns fnRule <- getRule id fn
--                    MappedRule xMap xs xRule <- getRule id a
-- 
--                    forM fns $ \fn ->
--                      produceRule (fmapped . fn) a rule
--                    forM xs $ \x ->
--                      produceRule (fmapped . ($ x)) fn rule
-- 
--                    rule <=* (\f x -> fmapped ((fnMap f) (xMap x)), fnRule, xRule)
--                    pure (fmapped <$> (fns <*> xs))
-- 
--       produceRule fmapped (EmbedRule ~(Rule _ build _)) rule = do
--         let alts = deAlt build
--         empties <- mconcat <$> mapM (\r -> produceRule fmapped r rule) alts
--         return empties
-- 
--       produceRule fmapped (Embed mk) rule = do
--         mk fmapped rule
--         pure []
-- --      produceRule fmapped (Many x) rule = do
-- --        produceRule (fmapped (EmbedRule (Rule [[]] (do x <- (pure [] <|> (:) <$> x ) 0))) rule
--       produceRule _ (Alt {}) _ = fail "produceRule: Alt"

terminal :: Enum cls => cls -> (tok -> Maybe a) -> RuleB tok cls a
terminal = Terminal

--rule :: RuleIx a -> RuleB tok cls a
--rule = EmbedRule

simpleRuleParser :: Parser Char AST
simpleRuleParser = compile id $ mdo
  varProd <- buildRule (terminal 'a' (\_ -> Just A') <|>
                        terminal 'b' (\_ -> Just B') <|>
                        terminal 'c' (\_ -> Just C') <|>
                        (Mul <$> varProd <*> (terminal '*' (\_ -> Just ()) *> varProd)))
  pure varProd

simpleRuleParserLR :: Parser Char AST
simpleRuleParserLR = compile id $ mdo
  termProd <- buildRule (terminal 'a' (\_ -> Just A') <|>
                         terminal 'b' (\_ -> Just B') <|>
                         terminal 'c' (\_ -> Just C'))

  varProd <- buildRule (termProd <|>
                        (Mul <$> termProd <*> (terminal '*' (\_ -> Just ()) *> varProd)))
  pure varProd

data LC
  = Lam String LC
  | ApL LC LC
  | Var String
  deriving Show

data Exp
  = VarE String
  | Add Exp Exp
  deriving Show

simpleExprParser :: Parser Char Exp
simpleExprParser = compile id $ mdo
  let charP c = terminal c Just
--      strP = foldr (*>) (pure ()) . map charP
      oneOf s = foldr (<|>) empty (map charP s)

  char <- buildRule (oneOf "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQQRSTUVWXYZ0123456789_'")
  oneChar <- buildRule ( pure <$> char )
  nm <- buildRule ( oneChar <|> ( (:) <$> char <*> nm) )

  var <- buildRule (VarE <$> nm)
  plus <- buildRule (charP '+')

  expr <- buildRule ( var <|> (Add <$> var <*> (plus *>expr)))
  pure expr

simpleLCParser :: Parser Char LC
simpleLCParser = compile id $ mdo
  let charP c = terminal c Just
--      strP = foldr (*>) (pure ()) . map charP
      oneOf s = foldr (<|>) empty (map charP s)

  char <- buildRule (oneOf "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQQRSTUVWXYZ0123456789_'")
  nm <- buildRule ( (:) <$> char <*> (pure [] <|> nm))

  arrow <- buildRule (charP '-' *> charP '>' *> pure ())
  lam <- buildRule (charP '\\')

  ws <- buildRule ( oneOf " \t\r\n\v" *> maybeWs )
  maybeWs <- buildRule ( pure () <|> ws )

  lamRule <- buildRule (Lam <$> (lam *> maybeWs *> nm) <*> (maybeWs *> arrow *> maybeWs *> expr))

  bexpr <- buildRule ( (Var <$> nm <* ws) <|> (charP '(' *> expr <* charP ')'))
  expr <- buildRule ( lamRule <|> bexpr <|> (ApL <$> expr <*> bexpr) )

  pure expr

showTableauCell :: TableauCell tok -> String
showTableauCell (TableauRowSkip n) = "<" ++ show n ++ ">"
showTableauCell (TableauCell x) = show (fmap fst x)

showRules :: (Word32 -> String) -> Parser tok a -> IO ()
showRules showCls pp = do
  let rules = map (\(cls, (nxt, _)) -> (nxt, "`" ++ showCls cls ++ "`")) (toList (parserSingleRules pp)) ++
              map (\(seq, nxt) -> let left = seq `shiftR` 32
                                      right = seq .&. 0xFFFFFFFF
                                  in (nxt, show left ++ " " ++ show right)) (UV.toList (parserRules pp))

  forM_ (sortBy (comparing fst) rules) $ \(nxt, what) ->
    putStrLn (show nxt ++ " -> " ++ what)
