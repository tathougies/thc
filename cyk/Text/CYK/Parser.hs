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

import           Control.Monad.State
import           Control.Parallel.Strategies (Strategy, withStrategy, r0)

import qualified Data.Vector as V
import qualified Data.Vector.Generic as GV
import qualified Data.Vector.Unboxed as UV

import           Data.Bits ((.|.), shiftL)
import           Data.Foldable (toList)
import           Data.Int
import qualified Data.Map.Strict as M
import           Data.Monoid (Last(..))
import           Data.Semigroup (Max(..))
import qualified Data.Text as T
import           Data.Word

import           Data.FingerTree (FingerTree, Measured(measure))
import qualified Data.FingerTree as FingerTree

import           GHC.Types (Any)

import           Unsafe.Coerce

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

data Parsed tok a -- This is a phantom type paramater. We have to rely on unsafe casting to get the result, if any
  = Parsed
  { parsedTableau    :: FingerTree (Max Word) (ParsedTableauRow tok)
  , parsedTokenCount :: {-# UNPACK #-} !Word
  }

getParseResult :: Parser tok a -> Parsed tok a -> Maybe a
getParseResult pp (Parsed tableau cnt) =
  case FingerTree.viewl tableau of
    FingerTree.EmptyL -> Nothing
    ParsedTableauRow row FingerTree.:< _ ->
      case FingerTree.viewl row of
        FingerTree.EmptyL -> Nothing
        pt FingerTree.:< _
          | ptTokenLevel pt == cnt &&
            ptProduction pt == parserFinal pp -> Just (unsafeCoerce (ptToken pt))
          | otherwise -> Nothing

instance Measured (Max Word) (ParsedTableauRow tok) where
  measure (ParsedTableauRow t) = Max $ tcLevel (measure t)

data TableauColumn
  = TableauColumn
  { tcTokenCount :: {-# UNPACK #-} !Word
  , tcLevel      :: {-# UNPACK #-} !Word
  } deriving Show

instance Monoid TableauColumn where
  mempty = TableauColumn 0 0
  mappend (TableauColumn atc al) (TableauColumn btc bl) =
    TableauColumn (atc + btc) (max al bl)

instance Semigroup TableauColumn where
  (<>) = mappend

data ParsedToken tok
  = ParsedToken
  { ptTokenCount  :: {-# UNPACK #-} !Word
  , ptTokenLevel  :: {-# UNPACK #-} !Word
  , ptProductions :: V.Vector (Word32, Any) -- An array of productions and production outputs, ordered by key
  }

newtype ParsedTableauRow tok
  = ParsedTableauRow (FingerTree TableauColumn (ParsedToken tok))

instance Measured TableauColumn (ParsedToken tok) where
  measure = TableauColumn <$> ptTokenCount <*> ptTokenLevel

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
parse evalStrategy parser@(Parser { parserTokenClassifier = classify, parserRules = rules
                                  , parserSingleRules = singles }) toks =
  case bisect toks of
    SplitResultNull  -> Parsed FingerTree.empty 0
    SplitResultOne a ->
      let prod = fromIntegral (fromEnum (classify a))
          prodStart = bsearch singles prod

          applicableProductions = V.takeWhile ((== prod) . fst) (V.drop prodStart singles)

          newProductions = V.map (\(_, (next, mk)) -> (next, mk a)) applicableProductions

          row = ParsedTableauRow (FingerTree.singleton (ParsedToken 1 1 prod newProductions))
      in Parsed (FingerTree.singleton row) 1
    SplitResultSplit a b ->
      let ap = parse evalStrategy parser a
          bp = parse evalStrategy parser b
      in withStrategy evalStrategy ap `seq`
         withStrategy evalStrategy bp `seq`
         combineParses parser ap bp

-- | Combine two parses using the parser given
combineParses :: Parser tok a -> Parsed tok a -> Parsed tok a -> Parsed tok a
combineParses _ (Parsed _ 0) b = b
combineParses _ a (Parsed _ 0) = a
combineParses (Parser { parserRules = rules, parserCombinators = combinators }) a@(Parsed at atc) b@(Parsed bt btc) =
  let (at', bt', newTableau) = levelUp at bt
      nextLevel = atc + btc
  in case (FingerTree.viewr at', FingerTree.viewl bt') of
       (FingerTree.EmptyR, _) -> b
       (_, FingerTree.EmptyL) -> a
       ( at'' FingerTree.:> apt@(ParsedToken { ptProductions = aProds }),
         bpt@(ParsedToken { ptProductions = bProds }) FingerTree.:< bt'' ) ->

         -- Check if this token sequence can result in a new one
         case lookupSequence rules (ptProduction apt) (ptProduction bpt) of
           Nothing -> Parsed newTableau (atc + btc)
           Just (i, nextProduction) ->
             let combine :: Any -> Any -> Any
                 combine = V.unsafeIndex combinators i

                 newTok = combine aTok bTok -- OMG die all types!
                 newParsedToken = ParsedToken (ptTokenCount apt + ptTokenCount bpt) nextLevel nextProduction (lookupNext rules nextProduction) newTok
                 newRow = ParsedTableauRow ((at'' FingerTree.|> newParsedToken) FingerTree.>< bt'')
             in Parsed (newRow FingerTree.<| newTableau) (atc + btc)

-- updateParser :: TokenPosition -> [ token ] -> Parsed tok a -> Parsed tok a

lookupNext :: UV.Vector (Word64, Word32) -> Word32 -> UV.Vector (Word64, Word32)
lookupNext v b =
  let p = productionPair b 0
      i = bsearch v p
  in UV.unsafeDrop i v

{-# INLINE lookupSequence #-}
lookupSequence :: UV.Vector (Word64, Word32) -> Word32 -> Word32 -> Maybe (Int, Word32)
lookupSequence v a b =
  let p = productionPair a b
      i = bsearch v p

      (p', next) = UV.unsafeIndex v i
  in if p == p' then Just (i, next) else Nothing

{-# INLINE bsearch #-}
{-# SPECIALIZE bsearch :: UV.Vector (Word64, Word32) -> Word64 -> Int #-}
{-# SPECIALIZE bsearch :: forall v. V.Vector (Word32, v) -> Word32 -> Int #-}
bsearch :: (Ord k, GV.Vector v (k, v)) => v (k, v) -> k -> Int
bsearch vs k = loop 0 (UV.length vs)
  where
    loop !l !u
      | u <= l = l
      | otherwise = let i = midpoint l u
                        (k', _)  = UV.unsafeIndex vs i
                    in case compare k' k of
                         LT -> loop (i + 1) u
                         EQ -> i
                         GT -> loop l i

    midpoint !l !u = fromIntegral (((fromIntegral l :: Word) + fromIntegral u) `div` 2)

productionPair :: Word32 -> Word32 -> Word64
productionPair a b = (fromIntegral a `shiftL` 32) .|. fromIntegral b

levelUp :: FingerTree (Max Word) (ParsedTableauRow tok)
        -> FingerTree (Max Word) (ParsedTableauRow tok)
        -> ( FingerTree TableauColumn (ParsedToken tok) -- The highest row in a
           , FingerTree TableauColumn (ParsedToken tok) -- The highest row in b
           , FingerTree (Max Word) (ParsedTableauRow tok) )
levelUp a b =
  case ( FingerTree.viewr a, FingerTree.viewr b) of
    (FingerTree.EmptyR, _) -> error "levelUp: a is empty"
    (_, FingerTree.EmptyR) -> error "levelUp: b is empty"
    ( aRow FingerTree.:> ParsedTableauRow a',
      bRow FingerTree.:> ParsedTableauRow b' ) ->
      go a' b' aRow bRow (FingerTree.singleton (ParsedTableauRow (a' FingerTree.>< b')))

  where
    go lastA lastB aRow bRow accum =
      case ( FingerTree.viewr aRow, FingerTree.viewr bRow ) of
        ( FingerTree.EmptyR, FingerTree.EmptyR ) -> ( lastA, lastB, accum )
        ( FingerTree.EmptyR, _ ) ->
          let ParsedTableauRow lastB' FingerTree.:< _ = FingerTree.viewl bRow -- Irrefutable because it wasn't empty
              remaining = FingerTree.fmap' (\(ParsedTableauRow bRow') -> ParsedTableauRow (lastA FingerTree.>< bRow')) bRow
          in ( lastA, lastB', remaining FingerTree.>< accum )

        ( _, FingerTree.EmptyR ) ->
          let ParsedTableauRow lastA' FingerTree.:< _ = FingerTree.viewl aRow
              remaining = FingerTree.fmap' (\(ParsedTableauRow aRow') -> ParsedTableauRow (aRow' FingerTree.>< lastB)) aRow
          in ( lastA', lastB, remaining FingerTree.>< accum)

        ( aRow' FingerTree.:> ParsedTableauRow a' ,
          bRow' FingerTree.:> ParsedTableauRow b' )
          | aLvl == bLvl -> go a' b' aRow' bRow' (ParsedTableauRow (a' FingerTree.>< b') FingerTree.<| accum)
          | aLvl < bLvl  -> go lastA b' aRow bRow' (ParsedTableauRow (lastA FingerTree.>< b') FingerTree.<| accum)
          | otherwise    -> go a' lastB aRow' bRow (ParsedTableauRow (a' FingerTree.>< lastB) FingerTree.<| accum)
          where TableauColumn { tcLevel = aLvl } = measure a'
                TableauColumn { tcLevel = bLvl } = measure b'

-- Parser building

data RuleSpec c where
  RuleSpec :: (a -> b -> c) -> Rule a -> Rule b -> RuleSpec c

data GenericRuleSpec = GenericRuleSpec {-# UNPACK #-} !Word64 {-# UNPACK #-} !Word32 (Any -> Any -> Any)

instance Measured (Last Word64) GenericRuleSpec where
  measure (GenericRuleSpec a _ _) = Last (Just a)

newtype ParserBuilder tok classification a
  = ParserBuilder (State (Word32, FingerTree (Last Word64) GenericRuleSpec) a)
  deriving (Functor, Monad, MonadFix, Applicative)

newtype Rule a
  = Rule Word32
  deriving Show

addRuleSpec :: GenericRuleSpec -> FingerTree (Last Word64) GenericRuleSpec
            -> FingerTree (Last Word64) GenericRuleSpec
addRuleSpec grs@(GenericRuleSpec p _ _) ft =
  let (a, b) = FingerTree.split (\(Last k) -> maybe False (>p) k) ft
  in (a FingerTree.|> grs) FingerTree.>< b

compile :: forall tok classification a
         . (Enum classification, Bounded classification)
        => (tok -> classification) -> ParserBuilder tok classification (Rule a) -> Parser tok a
compile classifier (ParserBuilder build) =
  let firstNonTerminal :: Word32
      firstNonTerminal = fromIntegral (succ (fromEnum (maxBound::classification)))

      (Rule final, (_, transitionMap)) = runState build (firstNonTerminal, mempty)

      (transitions, combinators) = unzip (map (\(GenericRuleSpec p n f) -> ((p, n), f)) (toList transitionMap))
  in Parser classifier (UV.fromList (reverse transitions)) (V.fromList (reverse combinators)) final

terminal :: Enum classification
         => classification
         -> ParserBuilder tok classification (Rule tok)
terminal cls =
  pure (Rule (fromIntegral (fromEnum cls)))

toGenericRuleSpec :: Word32 -> RuleSpec c -> GenericRuleSpec
toGenericRuleSpec dest (RuleSpec f (Rule a1) (Rule a2)) =
  GenericRuleSpec (productionPair a1 a2) dest (unsafeCoerce f)

production :: [ RuleSpec c ] -> ParserBuilder tok classification (Rule c)
production rules =
  ParserBuilder $ do
    (nextNm, transitions) <- get
    let newTransitions = foldr (addRuleSpec . toGenericRuleSpec nextNm) transitions rules
    put (succ nextNm, newTransitions)
    pure (Rule nextNm)

rule :: (a -> b -> c) -> Rule a -> Rule b -> RuleSpec c
rule = RuleSpec

data Sym = A | B | C | Star | Error
  deriving (Show, Enum, Bounded)

charToSym :: Char -> Sym
charToSym 'a' = A
charToSym 'b' = B
charToSym 'c' = C
charToSym '*' = Star
charToSym _ = Error

simpleParser :: Parser Char Bool
simpleParser = compile charToSym $ mdo
  a    <- terminal A
  b    <- terminal B
  star <- terminal Star
  c <- production [ rule (\_ _ -> ()) a b ]
  production [ rule (\_ _ -> True) a star
             , rule (\_ _ -> False) a c ]

testParse :: Parser Char a -> String -> Maybe a
testParse pp s =
  let t = T.pack s
      res = parse r0 pp t
  in getParseResult pp res

