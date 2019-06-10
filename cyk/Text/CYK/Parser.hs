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

module Text.CYK.Parser where

import           Control.Applicative
import           Control.Monad.State
import           Control.Parallel.Strategies (Strategy, withStrategy, r0)

import qualified Data.Vector as V
import qualified Data.Vector.Generic as GV
import qualified Data.Vector.Unboxed as UV

import           Data.Bits ((.|.), shiftL)
import           Data.Foldable (toList)
import           Data.Int
import qualified Data.Map.Strict as M
import           Data.Maybe (fromMaybe)
import           Data.Monoid (Last(..), Sum(..))
import qualified Data.Text as T
import           Data.Word

import           Data.FingerTree (FingerTree, Measured(measure))
import qualified Data.FingerTree as FingerTree

--import           Debug.Trace

import           GHC.Types (Any)

import           Unsafe.Coerce

trace :: String -> a -> a
trace _ = id

class Splittable f where
  type SplitItem f :: *
  bisect :: f -> SplitResult f (SplitItem f)

data SplitResult f a
  = SplitResultNull
  | SplitResultOne a
  | SplitResultSplit f f

data Parser tok a where
  Parser :: Enum classification
         => { parserTokenClassifier   :: tok -> classification
            , parserSingleRules       :: V.Vector (Word32, (Word32, tok -> Any))
            , parserRules             :: UV.Vector (Word64, Word32)
            , parserCombinators       :: V.Vector (Any -> Any -> Any)
            , parserFinal             :: {-# UNPACK #-} !Word32 -- Final state
            }
         -> Parser tok a

type ParserTableau tok = FingerTree (Last Word) (ParsedTableauRow tok)
type ProductionRules = UV.Vector (Word64, Word32)

data Parsed tok a -- This is a phantom type paramater. We have to rely on unsafe casting to get the result, if any
  = Parsed
  { parsedTableau    :: ParserTableau tok
  , parsedTokenCount :: {-# UNPACK #-} !Word
  }

getParseResult :: Parser tok a -> Parsed tok a -> [a]
getParseResult pp (Parsed tableau cnt) =
  case FingerTree.viewr tableau of
    FingerTree.EmptyR -> []
    _ FingerTree.:> ParsedTableauRow rowCount row
        | rowCount /= cnt -> []
        | otherwise ->
            case FingerTree.viewl row of
              TableauCell prods FingerTree.:< _ ->
                  map (\(_, a) -> unsafeCoerce a) (V.toList prods)
              _ -> []

instance Measured (Last Word) (ParsedTableauRow tok) where
  measure (ParsedTableauRow len _) = Last (Just len)

data TableauCell tok
  = TableauCell
  { tcProductions :: V.Vector (Word32, Any) -- An array of productions and production outputs, ordered by key
  }
  | TableauRowSkip Word

data ParsedTableauRow tok
  = ParsedTableauRow Word (FingerTree TableauCellPosition (TableauCell tok))

data TableauCellPosition
    = TableauCellPosition
    { tcpIx :: {-# UNPACK #-} !Word
    , tcpNonSparse :: {-# UNPACK #-} !Bool
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
                  in SplitResultSplit a b

-- | Parse the given grammar in parallel
parse :: Splittable f
      => Strategy (Parsed (SplitItem f) a) -> Parser (SplitItem f) a -> f -> Parsed (SplitItem f) a
parse evalStrategy
      parser@(Parser { parserTokenClassifier = classify, parserRules = rules
                     , parserSingleRules = singles }) toks =
  case bisect toks of
    SplitResultNull  -> Parsed FingerTree.empty 0
    SplitResultOne a ->
      let prod = fromIntegral (fromEnum (classify a))
          prodStart = bsearch singles prod

          applicableProductions = V.takeWhile ((== prod) . fst) (V.drop prodStart singles)

          newProductions = V.map (\(_, (next, mk)) -> (next, mk a)) applicableProductions

          row = ParsedTableauRow 1 (FingerTree.singleton (if V.null newProductions then TableauRowSkip 1 else TableauCell newProductions))
      in trace ("Prod start is " ++ show (prodStart, fmap fst singles, fmap fst newProductions, fmap fst applicableProductions)) (Parsed (FingerTree.singleton row) 1)
    SplitResultSplit a b ->
      let ap = parse evalStrategy parser a
          bp = parse evalStrategy parser b
      in withStrategy evalStrategy ap `seq`
         withStrategy evalStrategy bp `seq`
         combineParses parser ap bp

padRowLeft, padRowRight :: Word -> ParsedTableauRow tok -> ParsedTableauRow tok
padRowLeft 0 row = row
padRowLeft w (ParsedTableauRow len cols) = ParsedTableauRow len (TableauRowSkip w FingerTree.<| cols)

padRowRight 0 row = row
padRowRight w (ParsedTableauRow len cols) = ParsedTableauRow len (cols FingerTree.|> TableauRowSkip w)

-- | Combine two parses using the parser given
combineParses :: Parser tok a -> Parsed tok a -> Parsed tok a -> Parsed tok a
combineParses pp@(Parser { parserRules = rules, parserCombinators = combinators }) a@(Parsed aTableauBegin atc) b@(Parsed bTableauBegin btc) =
    Parsed (go aTableauBegin bTableauBegin mempty ) finalTokenCount
  where
    finalTokenCount = atc + btc
    nextRowToGenerate = max atc btc + 1

    go at bt finalTableau =
        case ( FingerTree.viewl at, FingerTree.viewl bt ) of
          ( FingerTree.EmptyL, FingerTree.EmptyL ) ->
              finalizeTableau nextRowToGenerate finalTableau

          ( ParsedTableauRow aLen _ FingerTree.:< _, FingerTree.EmptyL ) ->
              finalizeTableau nextRowToGenerate (finalTableau FingerTree.>< FingerTree.fmap' (padRowRight (atc - aLen - 1)) at)

          ( FingerTree.EmptyL, _ ) ->
              finalizeTableau nextRowToGenerate (finalTableau FingerTree.>< FingerTree.fmap' (padRowLeft atc) bt)

          ( (ParsedTableauRow aLen aRow) FingerTree.:< at',
            (ParsedTableauRow bLen bRow) FingerTree.:< bt' )
              | trace ("Alen " ++ show (aLen, bLen)) (aLen < bLen) ->
                  iterateRow at' bt aLen aRow (FingerTree.singleton (TableauRowSkip (btc - aLen + 1))) finalTableau
              | aLen > bLen ->
                  iterateRow at bt' bLen (FingerTree.singleton (TableauRowSkip (atc - bLen + 1))) bRow finalTableau
              | otherwise ->
                  iterateRow at' bt' aLen aRow bRow finalTableau

    compressRow [] rest = rest
    compressRow (Just x:xs) rest = x FingerTree.<| compressRow xs rest
    compressRow (Nothing:xs) rest = emptyRun 1 xs rest

    emptyRun !n [] rest = TableauRowSkip n FingerTree.<| rest
    emptyRun !n (Nothing:xs) rest = emptyRun (n + 1) xs rest
    emptyRun !n (Just x:xs) rest = TableauRowSkip n FingerTree.<| x FingerTree.<| compressRow xs rest

    iterateRow at bt rowLen aRow bRow finalTableau =
        let nextRow = ParsedTableauRow rowLen nextRowEntries

            nextRowEntries = aRow FingerTree.>< remaining

            computed = map (\start -> computeCell pp finalTableau start rowLen) [ atc - rowLen + 1 .. atc - 1 ]
            remaining = compressRow computed bRow

            nextTableau = addRow finalTableau nextRow
        in go at bt nextTableau

    addRow tableau nextRow@(ParsedTableauRow _ nextRowEntries)
        | tcpNonSparse (measure nextRowEntries) = tableau FingerTree.|> nextRow
        | otherwise = tableau


    finalizeTableau len tableau
        | len > finalTokenCount = tableau
        | otherwise =
            trace ("Computing row of length " ++ show len) $
            let computed = map (\start -> computeCell pp tableau start len) [ 0 .. finalTokenCount - len ]
                remaining = trace ("Computed " ++ show (fmap (() <$) computed)) (compressRow computed mempty)

                nextRow = ParsedTableauRow len remaining
            in finalizeTableau (len + 1) (addRow tableau nextRow)

lookupRow :: Word -> ParserTableau tok -> Maybe (ParsedTableauRow tok)
lookupRow lenIx ft =
    let (a, b) = FingerTree.split (\(Last l) -> maybe False (>= lenIx) l) ft
    in case FingerTree.viewl b of
         row@(ParsedTableauRow realLen _) FingerTree.:< _
             | lenIx == realLen -> Just row
         _ -> Nothing

lookupColumn :: Word -> ParsedTableauRow tok -> Maybe (V.Vector (Word32, Any))
lookupColumn colIx (ParsedTableauRow _ row) =
    let (a, b) = FingerTree.split (\thisCol -> tcpIx thisCol > colIx) row

    in if tcpIx (measure a) == colIx
       then case FingerTree.viewl b of
              TableauCell p FingerTree.:< _ -> Just p
              _ -> Nothing
       else Nothing

getRowColCount :: ParsedTableauRow tok -> Word
getRowColCount (ParsedTableauRow _ row) = tcpIx (measure row)

computeCell :: Parser tok a -> ParserTableau tok
            -> Word -> Word -> Maybe (TableauCell tok)
computeCell Parser { parserRules = rules
                   , parserCombinators = combinators } tableau start len =
    trace ("Compute cell " ++ show (start, len)) $
    if V.null nextProds then Nothing else Just (TableauCell nextProds)
    where
      nextProds = V.generate (fromIntegral (len - 2 + 1)) (\i -> go (fromIntegral i + 1)) >>= id

      go :: Word -> V.Vector (Word32, Any)
      go leftLen =
        let rightLen = len - leftLen

            -- TODO no need to lookup row
        in trace ("Computing at " ++ show (start, len, leftLen)) $
           case ( lookupRow leftLen tableau
                , lookupRow rightLen tableau ) of
             ( Nothing, _ ) -> trace ("Could not find row of length " ++ show leftLen) V.empty
             ( _, Nothing ) -> trace ("Could not find row of length " ++ show rightLen) V.empty
             ( Just leftRow,
               Just rightRow ) ->
                trace ("Got row " ++ show (getRowColCount leftRow, getRowColCount rightRow)) $
                case ( lookupColumn start leftRow
                     , lookupColumn (start + leftLen) rightRow ) of
                  ( Nothing, _ ) -> trace ("Could not find left column " ++ show start) V.empty
                  ( _, Nothing ) -> trace ("Could not find right column " ++ show (start + leftLen)) V.empty
                  ( Just leftProductions,
                    Just rightProductions ) -> trace ("Got productions " ++ show (fmap fst leftProductions, fmap fst rightProductions)) $ do
                      ( l, la ) <- leftProductions
                      ( r, ra ) <- rightProductions
                      case trace ("Looking up " ++ show (l, r)) (lookupSequence rules l r) of
                        Nothing -> V.empty
                        Just (i, nextProduction) ->
                          let f = V.unsafeIndex combinators i
                          in trace ("Got next production " ++ show (l, r, i)) (pure (nextProduction, f la ra))

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
                         EQ -> i
                         GT -> loop l i

    midpoint !l !u = fromIntegral (((fromIntegral l :: Word) + fromIntegral u) `div` 2)

productionPair :: Word32 -> Word32 -> Word64
productionPair a b = (fromIntegral a `shiftL` 32) .|. fromIntegral b

-- Parser building

data GenericRuleSpec = GenericRuleSpec {-# UNPACK #-} !Word64 {-# UNPACK #-} !Word32 (Any -> Any -> Any)
data SingleProductionSpec tok = SingleProductionSpec {-# UNPACK #-} !Word32 {-# UNPACK #-} !Word32 (tok -> Any)

instance Measured (Last Word64) GenericRuleSpec where
  measure (GenericRuleSpec a _ _) = Last (Just a)
instance Measured (Last Word32) (SingleProductionSpec tok) where
  measure (SingleProductionSpec a _ _) = Last (Just a)

newtype ParserBuilder tok classification a
  = ParserBuilder (State (Word32,
                          FingerTree (Last Word64) GenericRuleSpec,
                          FingerTree (Last Word32) (SingleProductionSpec tok)) a)
  deriving (Functor, Monad, MonadFix, Applicative)

newtype Rule a
  = Rule Word32
  deriving Show

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
                                                pure (lastS' < k')) ft
  in (a FingerTree.|> s) FingerTree.>< b

compile :: forall tok classification a
         . (Enum classification, Bounded classification)
        => (tok -> classification) -> ParserBuilder tok classification (Rule a) -> Parser tok a
compile classifier (ParserBuilder build) =
  let (Rule final, (_, transitionMap, singles)) = runState build (0, mempty, mempty)

      (transitions, combinators) = unzip (map (\(GenericRuleSpec p n f) -> ((p, n), f)) (toList transitionMap))
      singlesRules = map (\(SingleProductionSpec cls dest fn) -> (cls, (dest, fn))) (toList singles)
  in Parser classifier (V.fromList singlesRules)
         (UV.fromList transitions)
         (V.fromList combinators) final

production :: Enum cls
           => ParserBuilder tok cls (Rule a)
production = ParserBuilder $ do
               (nextNm, trans, prods) <- get
               put (nextNm + 1, trans, prods)
               pure (Rule nextNm)

(<=.) :: Enum classification
      => Rule a -> (classification, token -> a) -> ParserBuilder token classification ()
Rule nm <=. (cls, mk) =
    ParserBuilder $ do
      (nextNm, trans, prods) <- get
      put (nextNm, trans, addRuleSpec (SingleProductionSpec (fromIntegral (fromEnum cls)) nm (\a -> unsafeCoerce (mk a))) prods)
      pure ()

(<=*) :: Rule c -> (a -> b -> c, Rule a, Rule b) -> ParserBuilder token classification ()
Rule nm <=* (cmb, Rule l, Rule r) =
    ParserBuilder $ do
      (nextNm, trans, prods) <- get
      put (nextNm,
           addRuleSpec (GenericRuleSpec (productionPair l r) nm (\a b -> unsafeCoerce (cmb (unsafeCoerce a) (unsafeCoerce b)))) trans,
           prods)
      pure ()

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

parseSingleUnsafe :: Parser Char AST -> Char -> V.Vector (Word32, AST)
parseSingleUnsafe Parser { parserTokenClassifier = classify
                         , parserSingleRules = singles } c =
    let prodStart = bsearch singles prod
        prod = (fromIntegral (fromEnum (classify c)))

        applicable = V.takeWhile ((==prod) .fst) (V.drop prodStart singles)

        prods = V.map (\(_, (next, mk)) -> (next, unsafeCoerce (mk c))) applicable
    in prods

simpleParser :: Parser Char AST
simpleParser = compile id $ mdo

  varProd <- production

  varProd <=. ('a', \_ -> A')
  varProd <=. ('b', \_ -> B')
  varProd <=. ('c', \_ -> C')

  starProd <- production
  starProd <=. ('*', \_ -> ())

  mulProd <- production
  mulProd <=* (\_ b -> trace ("Making b " ++ show b) (\a -> Mul a b), starProd, varProd)

  varProd <=* (\a f -> f a, varProd, mulProd)

  pure varProd

testParse :: Parser Char a -> String -> [a]
testParse pp s =
  let t = T.pack s
      res = parse r0 pp t
  in getParseResult pp res

getTestParsed :: Parser Char a -> String -> Parsed Char a
getTestParsed pp s = parse r0 pp (T.pack s)

printParsedTableau :: Parsed Char a -> IO ()
printParsedTableau (Parsed tbl _) = go tbl
    where
      go cur =
          case FingerTree.viewl cur of
            FingerTree.EmptyL -> pure ()
            ParsedTableauRow len row FingerTree.:< cur' -> do
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
    Embed :: (Rule a -> ParserBuilder tok cls ()) -> RuleB tok cls a
    EmbedRule :: Rule a -> RuleB tok cls a
    Ap :: RuleB tok cls (a -> b) -> RuleB tok cls a -> RuleB tok cls b

    Alt :: RuleB tok cls a -> RuleB tok cls a -> RuleB tok cls a
    Empty :: RuleB tok cls a

instance Functor (RuleB tok cls) where
    fmap fn x = Ap (Pure fn) x

instance Applicative (RuleB tok cls) where
    pure = Pure
    Pure fn <*> Pure x = Pure (fn x)
    a <*> b = Ap a b

instance Alternative (RuleB tok cls) where
    Empty <|> x  = x
    x <|> Empty  = x
    a <|> b = Alt a b
    empty = Empty

buildRule :: Enum cls => RuleB tok cls a -> ParserBuilder tok cls (Rule a)
buildRule rule = produceRule rule production
    where

      produceRule :: Enum cls => RuleB tok cls a -> ParserBuilder tok cls (Rule a) -> ParserBuilder tok cls (Rule a)
      produceRule (Pure a) _ = fail "Could not build parser -- terminal returned pure"
      produceRule (Ap fn a) mkRule =
          case fn of
            Pure fn ->
                -- Attempt to dig down into the rule
                fail "Unimplemented"
            Ap (Pure fn) b ->
                do rule <- mkRule
                   aRule <- produceRule b production
                   bRule <- produceRule a production
                   rule <=* (fn, aRule, bRule)
                   pure rule
            fn ->
                do rule <- mkRule
                   fnRule <- produceRule fn production
                   xRule <- produceRule a production
                   rule <=* (id, fnRule, xRule)
                   pure rule

      produceRule (EmbedRule a) _ = pure a
      produceRule (Embed mk) newRule = do
        rule <- newRule
        mk rule
        pure rule
      produceRule (Alt a b) mkRule = do
        rule <- mkRule
        produceRule a (pure rule)
        produceRule b (pure rule)
        pure rule

terminal :: Enum cls => cls -> (tok -> a) -> RuleB tok cls a
terminal cls mk =
    Embed $ \prod -> do
      prod <=. (cls, mk)

rule :: Rule a -> RuleB tok cls a
rule = EmbedRule

simpleRuleParser :: Parser Char AST
simpleRuleParser = compile id $ mdo
  varProd <- buildRule (terminal 'a' (\_ -> A') <|>
                        terminal 'b' (\_ -> B') <|>
                        terminal 'c' (\_ -> C') <|>
                        (Mul <$> rule varProd <*> (terminal '*' (\_ -> ()) *> rule varProd)))
  pure varProd

simpleLCParser :: Parser Char String
simpleLCParser = compile id $ mdo
  char <- buildRule (many (terminal 'a' id <|>
                           terminal 'b' id))
  pure char
