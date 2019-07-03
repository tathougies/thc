{-# OPTIONS_GHC -funbox-strict-fields #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
module Data.FingerTree.Pinky.Sequence
   ( Seq
   , empty, length, singleton
   , (<|), (|>), (><)
   , fromList
   , null
   , ViewL(..), viewl
   , ViewR(..), viewr
   , splitAt, take, drop
   , traverse', traverseWithIndex
   , index, (!!), (!?)
   , replicate
   ) where

import Prelude hiding ( null, length, splitAt
                      , take, drop, (!!)
                      , replicate )

import Data.Monoid
import Data.Foldable (toList)
import Data.Word (Word)
import Data.Semigroup hiding (Last)

import Control.DeepSeq

import Text.Show

import Unsafe.Coerce

infixr 5 ><
infixr 5 <|, <|*, :<
infixl 5 |>, |>*, :>

data Level = LZ | LSucc Level
  deriving Show

data RuntimeDepthInspection (l :: Level) where
    RuntimeZ :: RuntimeDepthInspection 'LZ
    RuntimeSucc :: RuntimeDepth l -> RuntimeDepthInspection ('LSucc l)

inspect :: RuntimeDepth l -> RuntimeDepthInspection l
prevDepth :: RuntimeDepth ('LSucc l) -> RuntimeDepth l
nextDepth :: RuntimeDepth l -> RuntimeDepth ('LSucc l)

#if TYPESAFE

data RuntimeDepth (l :: Level) where
  RuntimeZD :: RuntimeDepth ('LSucc 'LZ) -> RuntimeDepth 'LZ
  RuntimeSuccD :: RuntimeDepth l -> RuntimeDepth ('LSucc ('LSucc l)) -> RuntimeDepth ('LSucc l)

prevDepth (RuntimeSuccD a _) = a

nextDepth (RuntimeZD n) = n
nextDepth (RuntimeSuccD _ n) = n

inspect RuntimeZD = RuntimeZ
inspect (RuntimeSuccD prev _) = RuntimeSucc (inspect prev)

zeroDepth :: RuntimeDepth 'LZ
zeroDepth = let x = RuntimeZD (next x)

                next prev = let y = RuntimeSuccD prev (next y)
                            in y
            in x

#else
newtype RuntimeDepth (l :: Level) = RuntimeDepth Word
  deriving Show

{-# INLINE inspect #-}
inspect (RuntimeDepth 0) = unsafeCoerce RuntimeZ
inspect (RuntimeDepth n) = unsafeCoerce (RuntimeSucc (RuntimeDepth (n - 1)))

{-# INLINE prevDepth #-}
prevDepth (RuntimeDepth n) = RuntimeDepth (n - 1)

{-# INLINE nextDepth #-}
nextDepth (RuntimeDepth n) = RuntimeDepth (n + 1)
#endif

newtype Seq a = Seq (SeqN 'LZ a)

instance Monoid (Seq a) where
  mempty = empty
  mappend = (Data.Semigroup.<>)

instance Semigroup (Seq a) where
  (<>) = (><)

instance NFData a => NFData (Seq a) where
  rnf (Seq x) = rnfSeqN zeroDepth x `seq` ()

rnfSeqN :: NFData a => RuntimeDepth l -> SeqN l a -> ()
rnfSeqN _ Empty = ()
rnfSeqN l (Single x) = rnfTree l x
rnfSeqN l (Deep _ pr m sf) = rnfDigit l pr `seq` rnfSeqN (nextDepth l) m `seq` rnfDigit l sf

rnfDigit :: NFData a => RuntimeDepth l -> Digit l a -> ()
rnfDigit l (One a) = rnfTree l a
rnfDigit l (Two a b) = rnfTree l a `seq` rnfTree l b
rnfDigit l (Three a b c) = rnfTree l a `seq` rnfTree l b `seq` rnfTree l c
rnfDigit l (Four a b c d) = rnfTree l a `seq` rnfTree l b `seq` rnfTree l c `seq` rnfTree l d

rnfTree :: NFData a => RuntimeDepth l -> Tree l a -> ()
rnfTree (inspect -> RuntimeZ {}) (Tree a) = rnf a
rnfTree (inspect -> RuntimeSucc l) (Tree n) =
  case n of
    Node2 _ a b -> rnfTree l a `seq` rnfTree l b
    Node3 _ a b c -> rnfTree l a `seq` rnfTree l b `seq` rnfTree l c

instance Show a => Show (Seq a) where
  showsPrec d x =
    showParen (d > app_prec) $
    (showString "fromList " . showsPrec (app_prec + 1) (toList x))
    where app_prec = 10

instance Foldable Seq where
  foldMap f (Seq ft) = foldMapSeq zeroDepth f ft
  foldr f x (Seq ft) = foldrSeq zeroDepth f x ft
  toList (Seq ft) = toListSeq zeroDepth ft []

data SeqN (l :: Level) a where
  Empty :: SeqN l a
  Single :: Tree l a -> SeqN l a
  Deep :: !Int -> !(Digit l a)
       -> (SeqN ('LSucc l) a) -- TODO does this need to be strict?
       -> !(Digit l a) -> SeqN l a

foldMapSeq :: Monoid b => RuntimeDepth l -> (a -> b) -> SeqN l a -> b
foldMapSeq !l _ Empty {} = mempty
foldMapSeq !l f (Single x) = foldMapTree l f x
foldMapSeq !l f (Deep _ pr m sf) = foldMapDigit l f pr `mappend` foldMapSeq (nextDepth l) f m `mappend` foldMapDigit l f sf

foldrSeq :: RuntimeDepth l -> (a -> b -> b) -> b -> SeqN l a -> b
foldrSeq !l _ x Empty{} = x
foldrSeq !l f x (Single a) = foldrTree l f x a
foldrSeq !l f x (Deep _ pr m sf) = foldrDigit l f (foldrSeq (nextDepth l) f (foldrDigit l f x sf) m) pr

foldMapTree :: Monoid b => RuntimeDepth l -> (a -> b) -> Tree l a -> b
foldMapTree (inspect -> RuntimeZ {}) f (Tree a) = f a
foldMapTree (inspect -> RuntimeSucc l') f (Tree (Node2 _ a b)) = foldMapTree l' f a `mappend` foldMapTree l' f b
foldMapTree (inspect -> RuntimeSucc l') f (Tree (Node3 _ a b c)) = foldMapTree l' f a `mappend` foldMapTree l' f b `mappend` foldMapTree l' f c

foldrDigit :: RuntimeDepth l -> (a -> b -> b) -> b -> Digit l a -> b
foldrDigit !l f x (One a)        = {-# SCC foldrDigitOne #-} foldrTree l f x a
foldrDigit !l f x (Two a b)      = {-# SCC foldrDigitTwo #-} next (next x b) a
  where next = foldrTree l f
foldrDigit !l f x (Three a b c)  = {-# SCC foldrDigitThree #-} next (next (next x c) b) a
  where next = foldrTree l f
foldrDigit !l f x (Four a b c d) = {-# SCC foldrDigitFour #-} next (next (next (next x d) c) b) a
  where next = foldrTree l f

foldrTree :: RuntimeDepth l -> (a -> b -> b) -> b -> Tree l a -> b
foldrTree (inspect -> RuntimeZ {}) f x (Tree a) = {-# SCC foldrTreeOne #-} f a x
foldrTree (inspect -> RuntimeSucc l') f x (Tree (Node2 _ a b)) = {-# SCC foldrTreeNode2 #-} next (next x b) a
  where next = foldrTree l' f
foldrTree (inspect -> RuntimeSucc l') f x (Tree (Node3 _ a b c)) = {-# SCC foldrTreeNode3 #-} next (next (next x c) b) a
  where next = foldrTree l' f

foldMapDigit :: Monoid b => RuntimeDepth l -> (a -> b) -> Digit l a -> b
foldMapDigit !l f (One a) = foldMapTree l f a
foldMapDigit !l f (Two a b) = foldMapTree l f a `mappend` foldMapTree l f b
foldMapDigit !l f (Three a b c) = foldMapTree l f a `mappend` foldMapTree l f b `mappend` foldMapTree l f c
foldMapDigit !l f (Four a b c d) = foldMapTree l f a `mappend` foldMapTree l f b `mappend` foldMapTree l f c `mappend` foldMapTree l f d

measureSeq :: RuntimeDepth l -> SeqN l a -> Int
measureSeq !_ Empty {} = 0
measureSeq !l (Single a) = measureTree l a
measureSeq !_ (Deep v _ _ _) = v

data Digit (n :: Level) a
  = One   (Tree n a)
  | Two   (Tree n a) (Tree n a)
  | Three (Tree n a) (Tree n a) (Tree n a)
  | Four  (Tree n a) (Tree n a) (Tree n a) (Tree n a)

measureDigit :: RuntimeDepth l -> Digit l a -> Int
measureDigit !l (One a) = measureTree l a
measureDigit !l (Two a b) = measureTree l a + measureTree l b
measureDigit !l (Three a b c) = measureTree l a + measureTree l b + measureTree l c
measureDigit !l (Four a b c d) = measureTree l a + measureTree l b + measureTree l c + measureTree l d

newtype Tree n a = Tree (TreeF n a)

type family TreeF (n :: Level) a where
  TreeF LZ a = a
  TreeF (LSucc l) a = Node l a

treeDigit :: Node l a -> Tree ('LSucc l) a
treeDigit n = Tree n

measureTree :: RuntimeDepth l -> Tree l a -> Int
measureTree (inspect -> RuntimeZ {}) (Tree x) = 1
measureTree (inspect -> RuntimeSucc {}) (Tree n) =
  measureNode n

measureNode :: Node l a -> Int
measureNode (Node2 l _ _) = l
measureNode (Node3 l _ _ _) = l

data Node n a
  = Node2 !Int !(Tree n a) !(Tree n a)
  | Node3 !Int !(Tree n a) !(Tree n a) !(Tree n a)

node2 :: RuntimeDepth n -> Tree n a -> Tree n a -> Node n a
node2 !l a b = Node2 (measureTree l a + measureTree l b) a b

node3 :: RuntimeDepth n -> Tree n a -> Tree n a -> Tree n a -> Node n a
node3 !l a b c = Node3 (measureTree l a + measureTree l b + measureTree l c) a b c

zeroDepth :: RuntimeDepth 'LZ
zeroDepth = RuntimeDepth 0
--            let z = RuntimeZ (next z)
--            in z
--   where
--     next :: RuntimeDepth l -> RuntimeDepth ('LSucc l)
--     next s = let n = RuntimeSucc s (next n)
--              in n

nodeToDigit :: Node l a -> Digit l a
nodeToDigit (Node2 _ a b) = Two a b
nodeToDigit (Node3 _ a b c) = Three a b c

deep :: RuntimeDepth l -> Digit (l :: Level) a -> SeqN ('LSucc l) a -> Digit l a -> SeqN l a
deep !l pr m sf =
  Deep ((measureDigit l pr + measureSeq (nextDepth l) m) + measureDigit l sf) pr m sf

-- * Construuction, deconstruction, and concatenation

-- | /O(1)/. The empty sequence
empty :: Seq a
empty = Seq Empty

-- | /O(1)/. Get length of sequence
length :: Seq a -> Int
length (Seq Empty) = 0
length (Seq Single {}) = 1
length (Seq (Deep l _ _ _)) = l

-- | /O(1)/. The singleton sequence
singleton :: a -> Seq a
singleton a = Seq (Single (Tree a))

-- | /O(n)/. Create sequence from finite list of elements.
-- The opposite operation 'toList' is provided by the 'Foldable' instance.
fromList :: [a] -> Seq a
fromList = foldr (<|) empty

-- | /O(1)/. Add an element to the left end of a sequence
(<|) :: a -> Seq a -> Seq a
a <| Seq ft = Seq ((zeroDepth, Tree a) <|* ft)

(<|*) :: (RuntimeDepth l, Tree l a) -> SeqN l a -> SeqN l a
(!l, a) <|* Empty = Single a
(!l, a) <|* (Single b) = deep l (One a) Empty (One b)
(!l, a) <|* (Deep v (Four b c d e) m sf) =
  m `seq` Deep (measureTree l a + v) (Two a b) ((nextDepth l, treeDigit (node3 l c d e)) <|* m) sf
(!l, a) <|* Deep v pr m sf =
  Deep (measureTree l a + v) (consDigit a pr) m sf

consDigit :: Tree l a -> Digit l a -> Digit l a
consDigit a (One b) = Two a b
consDigit a (Two b c) = Three a b c
consDigit a (Three b c d) = Four a b c d
consDigit _ (Four {}) = error "consDigit: illegal argument"

-- | /O(1)/. Add an element to the right end of a sequence.
(|>) :: Seq a -> a -> Seq a
Seq ft |> a = Seq (ft |>* (zeroDepth, Tree a))

{-# INLINE (|>*) #-}
(|>*) :: SeqN l a -> (RuntimeDepth l, Tree l a) -> SeqN l a
Empty |>* (!_, a) = Single a
Single a |>* (!l, b) = deep l (One a) Empty (One b)
Deep v pr m (Four a b c d) |>* (!l, e) = m `seq`
  Deep (v + measureTree l e) pr (m |>* (nextDepth l, treeDigit (node3 l a b c))) (Two d e)
Deep v pr m sf |>* (!l, x) =
  Deep (v + measureTree l x) pr m (snocDigit sf x)

snocDigit :: Digit l a -> Tree l a -> Digit l a
snocDigit (One a) b = Two a b
snocDigit (Two a b) c = Three a b c
snocDigit (Three a b c) d = Four a b c d
snocDigit (Four {}) _ = error "snocDigit: illegal argument"

-- | /O(1)/. Is this the empty sequence?
null :: Seq a -> Bool
null (Seq Empty {}) = True
null _ = False

data ViewL s a
  = EmptyL
  | a :< s a

-- | /O(1)/. Analyse the left end of a sequence.
viewl :: Seq a -> ViewL Seq a
viewl (Seq ft) = case viewl' zeroDepth ft of
                   Nothing -> EmptyL
                   Just (Tree a, ft) -> a :< Seq ft

viewl' :: RuntimeDepth l -> SeqN l a -> Maybe (Tree l a, SeqN l a)
viewl' !_ Empty {} = Nothing
viewl' !_ (Single x) = Just (x, Empty)
viewl' !l (Deep _ (One x) m sf) = Just (x, rotL l m sf)
viewl' !l (Deep _ pr m sf) = Just (lheadDigit pr, deep l (ltailDigit pr) m sf)

rotL :: RuntimeDepth l -> SeqN ('LSucc l) a -> Digit l a -> SeqN l a
rotL !l m sf =
  case viewl' (nextDepth l) m of
    Nothing -> digitToTree l sf
    Just (Tree a, m') -> Deep (measureSeq (nextDepth l) m + measureDigit l sf) (nodeToDigit a) m' sf

lheadDigit :: Digit l a -> Tree l a
lheadDigit (One a) = a
lheadDigit (Two a _) = a
lheadDigit (Three a _ _) = a
lheadDigit (Four a _ _ _) = a

ltailDigit :: Digit l a -> Digit l a
ltailDigit (One _) = error "ltailDigit: illegal argument"
ltailDigit (Two _ b) = One b
ltailDigit (Three _ b c) = Two b c
ltailDigit (Four _ b c d) = Three b c d

data ViewR s a
  = EmptyR
  | s a :> a

-- | /O(1)/. Analyze the right end of a sequence
viewr :: Seq a -> ViewR Seq a
viewr (Seq ft) = case viewr' zeroDepth ft of
                   Nothing -> EmptyR
                   Just (ft, Tree a) -> Seq ft :> a

viewr' :: RuntimeDepth l -> SeqN l a -> Maybe (SeqN l a, Tree l a)
viewr' !_ Empty {} = Nothing
viewr' !_ (Single x) = Just (Empty, x)
viewr' !l (Deep _ pr m (One x)) = Just (rotR l pr m, x)
viewr' !l (Deep _ pr m sf) = Just (deep l pr m (rtailDigit sf), rheadDigit sf)

rotR :: RuntimeDepth l -> Digit l a -> SeqN ('LSucc l) a -> SeqN l a
rotR !l pr m =
  case viewr' (nextDepth l) m of
    Nothing -> digitToTree l pr
    Just (m', Tree a) -> Deep (measureDigit l pr + measureSeq (nextDepth l) m) pr m' (nodeToDigit a)

rheadDigit :: Digit l a -> Tree l a
rheadDigit (One a) = a
rheadDigit (Two _ b) = b
rheadDigit (Three _ _ c) = c
rheadDigit (Four _ _ _ d) = d

rtailDigit :: Digit l a -> Digit l a
rtailDigit (One _) = error "rtailDigit: illegal argument"
rtailDigit (Two a _) = One a
rtailDigit (Three b c _) = Two b c
rtailDigit (Four b c d _) = Three b c d

digitToTree :: RuntimeDepth l -> Digit l a -> SeqN l a
digitToTree !l (One a) = Single a
digitToTree !l (Two a b) = deep l (One a) Empty (One b)
digitToTree !l (Three a b c) = deep l (Two a b) Empty (One c)
digitToTree !l (Four a b c d) = deep l (Two a b) Empty (Two c d)

-- * Concatenation

-- | /O(log(min(n1, n2)))/. Concatenate two sequences
(><) :: Seq a -> Seq a -> Seq a
Seq a >< Seq b = Seq (appendTree0 zeroDepth a b)

appendTree0 :: RuntimeDepth l -> SeqN l a -> SeqN l a -> SeqN l a
appendTree0 !_ (Empty {}) xs = xs
appendTree0 !_ xs (Empty {}) = xs
appendTree0 !l (Single x) xs = (l, x) <|* xs
appendTree0 !l xs (Single x) = xs |>* (l, x)
appendTree0 !l (Deep a pr1 m1 sf1) (Deep b pr2 m2 sf2) =
  Deep (a + b) pr1 (addDigits0 l m1 sf1 pr2 m2) sf2

addDigits0 :: RuntimeDepth l
           -> SeqN ('LSucc l) a
           -> Digit l a -> Digit l a
           -> SeqN ('LSucc l) a -> SeqN ('LSucc l) a
addDigits0 !l m1 (One a) (One b) m2 =
  appendTree1 l m1 (node2 l a b) m2
addDigits0 !l m1 (One a) (Two b c) m2 =
  appendTree1 l m1 (node3 l a b c) m2
addDigits0 !l m1 (One a) (Three b c d) m2 =
  appendTree2 l m1 (node2 l a b) (node2 l c d) m2
addDigits0 !l m1 (One a) (Four b c d e) m2 =
  appendTree2 l m1 (node3 l a b c) (node2 l d e) m2
addDigits0 !l m1 (Two a b) (One c) m2 =
  appendTree1 l m1 (node3 l a b c) m2
addDigits0 !l m1 (Two a b) (Two c d) m2 =
  appendTree2 l m1 (node2 l a b) (node2 l c d) m2
addDigits0 !l m1 (Two a b) (Three c d e) m2 =
  appendTree2 l m1 (node3 l a b c) (node2 l d e) m2
addDigits0 !l m1 (Two a b) (Four c d e f) m2 =
  appendTree2 l m1 (node3 l a b c) (node3 l d e f) m2
addDigits0 !l m1 (Three a b c) (One d) m2 =
  appendTree2 l m1 (node2 l a b) (node2 l c d) m2
addDigits0 !l m1 (Three a b c) (Two d e) m2 =
  appendTree2 l m1 (node3 l a b c) (node2 l d e) m2
addDigits0 !l m1 (Three a b c) (Three d e f) m2 =
  appendTree2 l m1 (node3 l a b c) (node3 l d e f) m2
addDigits0 !l m1 (Three a b c) (Four d e f g) m2 =
  appendTree3 l m1 (node3 l a b c) (node2 l d e) (node2 l f g) m2
addDigits0 !l m1 (Four a b c d) (One e) m2 =
  appendTree2 l m1 (node3 l a b c) (node2 l d e) m2
addDigits0 !l m1 (Four a b c d) (Two e f) m2 =
  appendTree2 l m1 (node3 l a b c) (node3 l d e f) m2
addDigits0 !l m1 (Four a b c d) (Three e f g) m2 =
  appendTree3 l m1 (node3 l a b c) (node2 l d e) (node2 l f g) m2
addDigits0 !l m1 (Four a b c d) (Four e f g h) m2 =
  appendTree3 l m1 (node3 l a b c) (node3 l d e f) (node2 l g h) m2

appendTree1 :: RuntimeDepth l -> SeqN ('LSucc l) a -> Node l a -> SeqN ('LSucc l) a -> SeqN ('LSucc l) a
appendTree1 !l Empty {} a xs = (l', treeDigit a) <|* xs
  where l' = nextDepth l
appendTree1 !l xs a Empty {} = xs |>* (l', treeDigit a)
  where l' = nextDepth l
appendTree1 !l (Single x) a xs = (l', x) <|* (l', treeDigit a) <|* xs
  where l' = nextDepth l
appendTree1 !l xs a (Single x) = xs |>* (l', treeDigit a) |>* (l', x)
  where l' = nextDepth l
appendTree1 !l (Deep al pr1 m1 sf1) a (Deep bl pr2 m2 sf2) =
  Deep (al + measureNode a  + bl) pr1 (addDigits1 l' m1 sf1 (treeDigit a) pr2 m2) sf2
  where l' = nextDepth l

addDigits1 :: RuntimeDepth l -> SeqN ('LSucc l) a
           -> Digit l a -> Tree l a -> Digit l a
           -> SeqN ('LSucc l) a -> SeqN ('LSucc l) a
addDigits1 !l m1 (One a) b (One c) m2 =
  appendTree1 l m1 (node3 l a b c) m2
addDigits1 !l m1 (One a) b (Two c d) m2 =
  appendTree2 l m1 (node2 l a b) (node2 l c d) m2
addDigits1 !l m1 (One a) b (Three c d e) m2 =
  appendTree2 l m1 (node3 l a b c) (node2 l d e) m2
addDigits1 !l m1 (One a) b (Four c d e f) m2 =
  appendTree2 l m1 (node3 l a b c) (node3 l d e f) m2
addDigits1 !l m1 (Two a b) c (One d) m2 =
  appendTree2 l m1 (node2 l a b) (node2 l c d) m2
addDigits1 !l m1 (Two a b) c (Two d e) m2 =
  appendTree2 l m1 (node3 l a b c) (node2 l d e) m2
addDigits1 !l m1 (Two a b) c (Three d e f) m2 =
  appendTree2 l m1 (node3 l a b c) (node3 l d e f) m2
addDigits1 !l m1 (Two a b) c (Four d e f g) m2 =
  appendTree3 l m1 (node3 l a b c) (node2 l d e) (node2 l f g) m2
addDigits1 !l m1 (Three a b c) d (One e) m2 =
  appendTree2 l m1 (node3 l a b c) (node2 l d e) m2
addDigits1 !l m1 (Three a b c) d (Two e f) m2 =
  appendTree2 l m1 (node3 l a b c) (node3 l d e f) m2
addDigits1 !l m1 (Three a b c) d (Three e f g) m2 =
  appendTree3 l m1 (node3 l a b c) (node2 l d e) (node2 l f g) m2
addDigits1 !l m1 (Three a b c) d (Four e f g h) m2 =
  appendTree3 l m1 (node3 l a b c) (node3 l d e f) (node2 l g h) m2
addDigits1 !l m1 (Four a b c d) e (One f) m2 =
  appendTree2 l m1 (node3 l a b c) (node3 l d e f) m2
addDigits1 !l m1 (Four a b c d) e (Two f g) m2 =
  appendTree3 l m1 (node3 l a b c) (node2 l d e) (node2 l f g) m2
addDigits1 !l m1 (Four a b c d) e (Three f g h) m2 =
  appendTree3 l m1 (node3 l a b c) (node3 l d e f) (node2 l g h) m2
addDigits1 !l m1 (Four a b c d) e (Four f g h i) m2 =
  appendTree3 l m1 (node3 l a b c) (node3 l d e f) (node3 l g h i) m2

appendTree2 :: RuntimeDepth l
            -> SeqN ('LSucc l) a -> Node l a -> Node l a
            -> SeqN ('LSucc l) a -> SeqN ('LSucc l) a
appendTree2 !l Empty {} a b xs =
  (l', treeDigit a) <|* (l', treeDigit b) <|* xs
  where l' = nextDepth l
appendTree2 !l xs a b Empty {} =
  xs |>* (l', treeDigit a) |>* (l', treeDigit b)
  where l' = nextDepth l
appendTree2 !l (Single x) a b xs =
  (l', x) <|* (l', treeDigit a) <|* (l', treeDigit b) <|* xs
  where l' = nextDepth l
appendTree2 !l xs a b (Single x) =
  xs |>* (l', treeDigit a) |>* (l', treeDigit b) |>* (l', x)
  where l' = nextDepth l
appendTree2 !l (Deep al pr1 m1 sf1) a b (Deep bl pr2 m2 sf2) =
  Deep (al + measureNode a + measureNode b + bl) pr1 (addDigits2 l' m1 sf1 (treeDigit a) (treeDigit b) pr2 m2) sf2
  where l' = nextDepth l

addDigits2 :: RuntimeDepth l -> SeqN ('LSucc l) a
           -> Digit l a -> Tree l a -> Tree l a -> Digit l a
           -> SeqN ('LSucc l) a -> SeqN ('LSucc l) a
addDigits2 !l m1 (One a) b c (One d) m2 =
  appendTree2 l m1 (node2 l a b) (node2 l c d) m2
addDigits2 !l m1 (One a) b c (Two d e) m2 =
  appendTree2 l m1 (node3 l a b c) (node2 l d e) m2
addDigits2 !l m1 (One a) b c (Three d e f) m2 =
  appendTree2 l m1 (node3 l a b c) (node3 l d e f) m2
addDigits2 !l m1 (One a) b c (Four d e f g) m2 =
  appendTree3 l m1 (node3 l a b c) (node2 l d e) (node2 l f g) m2
addDigits2 !l m1 (Two a b) c d (One e) m2 =
  appendTree2 l m1 (node3 l a b c) (node2 l d e) m2
addDigits2 !l m1 (Two a b) c d (Two e f) m2 =
  appendTree2 l m1 (node3 l a b c) (node3 l d e f) m2
addDigits2 !l m1 (Two a b) c d (Three e f g) m2 =
  appendTree3 l m1 (node3 l a b c) (node2 l d e) (node2 l f g) m2
addDigits2 !l m1 (Two a b) c d (Four e f g h) m2 =
  appendTree3 l m1 (node3 l a b c) (node3 l d e f) (node2 l g h) m2
addDigits2 !l m1 (Three a b c) d e (One f) m2 =
  appendTree2 l m1 (node3 l a b c) (node3 l d e f) m2
addDigits2 !l m1 (Three a b c) d e (Two f g) m2 =
  appendTree3 l m1 (node3 l a b c) (node2 l d e) (node2 l f g) m2
addDigits2 !l m1 (Three a b c) d e (Three f g h) m2 =
  appendTree3 l m1 (node3 l a b c) (node3 l d e f) (node2 l g h) m2
addDigits2 !l m1 (Three a b c) d e (Four f g h i) m2 =
  appendTree3 l m1 (node3 l a b c) (node3 l d e f) (node3 l g h i) m2
addDigits2 !l m1 (Four a b c d) e f (One g) m2 =
  appendTree3 l m1 (node3 l a b c) (node2 l d e) (node2 l f g) m2
addDigits2 !l m1 (Four a b c d) e f (Two g h) m2 =
  appendTree3 l m1 (node3 l a b c) (node3 l d e f) (node2 l g h) m2
addDigits2 !l m1 (Four a b c d) e f (Three g h i) m2 =
  appendTree3 l m1 (node3 l a b c) (node3 l d e f) (node3 l g h i) m2
addDigits2 !l m1 (Four a b c d) e f (Four g h i j) m2 =
  appendTree4 l m1 (node3 l a b c) (node3 l d e f) (node2 l g h) (node2 l i j) m2

appendTree3 :: RuntimeDepth l
            -> SeqN ('LSucc l) a -> Node l a -> Node l a -> Node l a
            -> SeqN ('LSucc l) a -> SeqN ('LSucc l) a
appendTree3 !l Empty {} a b c xs =
  (l', treeDigit a) <|* (l', treeDigit b) <|* (l', treeDigit c) <|* xs
  where l' = nextDepth l
appendTree3 !l xs a b c Empty {} =
  xs |>* (l', treeDigit a) |>* (l', treeDigit b) |>* (l', treeDigit c)
  where l' = nextDepth l
appendTree3 !l (Single x) a b c xs =
  (l', x) <|* (l', treeDigit a) <|* (l', treeDigit b) <|* (l', treeDigit c) <|* xs
  where l' = nextDepth l
appendTree3 !l xs a b c (Single x) =
  xs |>* (l', treeDigit a) |>* (l', treeDigit b) |>* (l', treeDigit c) |>* (l', x)
  where l' = nextDepth l
appendTree3 !l (Deep al pr1 m1 sf1) a b c (Deep bl pr2 m2 sf2) =
  Deep (al + measureNode a + measureNode b + measureNode c + bl) pr1 (addDigits3 l' m1 sf1 (treeDigit a) (treeDigit b) (treeDigit c) pr2 m2) sf2
  where l' = nextDepth l

addDigits3 :: RuntimeDepth l -> SeqN ('LSucc l) a
           -> Digit l a -> Tree l a -> Tree l a -> Tree l a -> Digit l a
           -> SeqN ('LSucc l) a -> SeqN ('LSucc l) a
addDigits3 !l m1 (One a) b c d (One e) m2 =
  appendTree2 l m1 (node3 l a b c) (node2 l d e) m2
addDigits3 !l m1 (One a) b c d (Two e f) m2 =
  appendTree2 l m1 (node3 l a b c) (node3 l d e f) m2
addDigits3 !l m1 (One a) b c d (Three e f g) m2 =
  appendTree3 l m1 (node3 l a b c) (node2 l d e) (node2 l f g) m2
addDigits3 !l m1 (One a) b c d (Four e f g h) m2 =
  appendTree3 l m1 (node3 l a b c) (node3 l d e f) (node2 l g h) m2
addDigits3 !l m1 (Two a b) c d e (One f) m2 =
  appendTree2 l m1 (node3 l a b c) (node3 l d e f) m2
addDigits3 !l m1 (Two a b) c d e (Two f g) m2 =
  appendTree3 l m1 (node3 l a b c) (node2 l d e) (node2 l f g) m2
addDigits3 !l m1 (Two a b) c d e (Three f g h) m2 =
  appendTree3 l m1 (node3 l a b c) (node3 l d e f) (node2 l g h) m2
addDigits3 !l m1 (Two a b) c d e (Four f g h i) m2 =
  appendTree3 l m1 (node3 l a b c) (node3 l d e f) (node3 l g h i) m2
addDigits3 !l m1 (Three a b c) d e f (One g) m2 =
  appendTree3 l m1 (node3 l a b c) (node2 l d e) (node2 l f g) m2
addDigits3 !l m1 (Three a b c) d e f (Two g h) m2 =
  appendTree3 l m1 (node3 l a b c) (node3 l d e f) (node2 l g h) m2
addDigits3 !l m1 (Three a b c) d e f (Three g h i) m2 =
  appendTree3 l m1 (node3 l a b c) (node3 l d e f) (node3 l g h i) m2
addDigits3 !l m1 (Three a b c) d e f (Four g h i j) m2 =
  appendTree4 l m1 (node3 l a b c) (node3 l d e f) (node2 l g h) (node2 l i j) m2
addDigits3 !l m1 (Four a b c d) e f g (One h) m2 =
  appendTree3 l m1 (node3 l a b c) (node3 l d e f) (node2 l g h) m2
addDigits3 !l m1 (Four a b c d) e f g (Two h i) m2 =
  appendTree3 l m1 (node3 l a b c) (node3 l d e f) (node3 l g h i) m2
addDigits3 !l m1 (Four a b c d) e f g (Three h i j) m2 =
  appendTree4 l m1 (node3 l a b c) (node3 l d e f) (node2 l g h) (node2 l i j) m2
addDigits3 !l m1 (Four a b c d) e f g (Four h i j k) m2 =
  appendTree4 l m1 (node3 l a b c) (node3 l d e f) (node3 l g h i) (node2 l j k) m2

appendTree4 :: RuntimeDepth l -> SeqN ('LSucc l) a
            -> Node l a -> Node l a -> Node l a -> Node l a
            -> SeqN ('LSucc l) a -> SeqN ('LSucc l) a
appendTree4 !l Empty {} a b c d xs =
  (l', treeDigit a) <|* (l', treeDigit b) <|* (l', treeDigit c) <|* (l', treeDigit d) <|* xs
  where l' = nextDepth l
appendTree4 !l xs a b c d Empty {} =
  xs |>* (l', treeDigit a) |>* (l', treeDigit b) |>* (l', treeDigit c) |>* (l', treeDigit d)
  where l' = nextDepth l
appendTree4 !l (Single x) a b c d xs =
  (l', x) <|* (l', treeDigit a) <|* (l', treeDigit b) <|* (l', treeDigit c) <|* (l', treeDigit d) <|* xs
  where l' = nextDepth l
appendTree4 !l xs a b c d (Single x) =
  xs |>* (l', treeDigit a) |>* (l', treeDigit b) |>* (l', treeDigit c) |>* (l', treeDigit d) |>* (l', x)
  where l' = nextDepth l
appendTree4 !l (Deep al pr1 m1 sf1) a b c d (Deep bl pr2 m2 sf2) =
  Deep (al + measureNode a + measureNode b + measureNode c + measureNode d + bl)
       pr1 (addDigits4 l' m1 sf1 (treeDigit a) (treeDigit b) (treeDigit c) (treeDigit d) pr2 m2) sf2
  where l' = nextDepth l

addDigits4 :: RuntimeDepth l -> SeqN ('LSucc l) a -> Digit l a
           -> Tree l a -> Tree l a -> Tree l a -> Tree l a
           -> Digit l a -> SeqN ('LSucc l) a -> SeqN ('LSucc l) a
addDigits4 !l m1 (One a) b c d e (One f) m2 =
  appendTree2 l m1 (node3 l a b c) (node3 l d e f) m2
addDigits4 !l m1 (One a) b c d e (Two f g) m2 =
  appendTree3 l m1 (node3 l a b c) (node2 l d e) (node2 l f g) m2
addDigits4 !l m1 (One a) b c d e (Three f g h) m2 =
  appendTree3 l m1 (node3 l a b c) (node3 l d e f) (node2 l g h) m2
addDigits4 !l m1 (One a) b c d e (Four f g h i) m2 =
  appendTree3 l m1 (node3 l a b c) (node3 l d e f) (node3 l g h i) m2
addDigits4 !l m1 (Two a b) c d e f (One g) m2 =
  appendTree3 l m1 (node3 l a b c) (node2 l d e) (node2 l f g) m2
addDigits4 !l m1 (Two a b) c d e f (Two g h) m2 =
  appendTree3 l m1 (node3 l a b c) (node3 l d e f) (node2 l g h) m2
addDigits4 !l m1 (Two a b) c d e f (Three g h i) m2 =
  appendTree3 l m1 (node3 l a b c) (node3 l d e f) (node3 l g h i) m2
addDigits4 !l m1 (Two a b) c d e f (Four g h i j) m2 =
  appendTree4 l m1 (node3 l a b c) (node3 l d e f) (node2 l g h) (node2 l i j) m2
addDigits4 !l m1 (Three a b c) d e f g (One h) m2 =
  appendTree3 l m1 (node3 l a b c) (node3 l d e f) (node2 l g h) m2
addDigits4 !l m1 (Three a b c) d e f g (Two h i) m2 =
  appendTree3 l m1 (node3 l a b c) (node3 l d e f) (node3 l g h i) m2
addDigits4 !l m1 (Three a b c) d e f g (Three h i j) m2 =
  appendTree4 l m1 (node3 l a b c) (node3 l d e f) (node2 l g h) (node2 l i j) m2
addDigits4 !l m1 (Three a b c) d e f g (Four h i j k) m2 =
  appendTree4 l m1 (node3 l a b c) (node3 l d e f) (node3 l g h i) (node2 l j k) m2
addDigits4 !l m1 (Four a b c d) e f g h (One i) m2 =
  appendTree3 l m1 (node3 l a b c) (node3 l d e f) (node3 l g h i) m2
addDigits4 !l m1 (Four a b c d) e f g h (Two i j) m2 =
  appendTree4 l m1 (node3 l a b c) (node3 l d e f) (node2 l g h) (node2 l i j) m2
addDigits4 !l m1 (Four a b c d) e f g h (Three i j k) m2 =
  appendTree4 l m1 (node3 l a b c) (node3 l d e f) (node3 l g h i) (node2 l j k) m2
addDigits4 !lvl m1 (Four a b c d) e f g h (Four i j k l) m2 =
  appendTree4 lvl m1 (node3 lvl a b c) (node3 lvl d e f) (node3 lvl g h i) (node3 lvl j k l) m2

-- * Splits

data Split t a = Split t a t

-- | /O(log(min(i, n-i)))/. Split a sequence at a point where the predicate
-- on the accumulated measure of the prefix changes from 'False' to 'True'.
--
-- For predictable results, one should ensure that there is only one such
-- point, i.e. that the predicate is /monotonic/.
{-# INLINE splitAt #-}
splitAt :: Int -> Seq a -> (Seq a, Seq a)
splitAt i xs
  | i < length xs = ( Seq l, Seq ((zeroDepth, Tree x) <|* r) )
  | otherwise = ( xs, Seq Empty )
  where
    Split l (Tree x) r =
      case xs of
        Seq xs' -> splitTree zeroDepth (> i) 0 xs'

-- | /O(log(min(i,n-i)))/.
-- Given a monotonic predicate @p@, @'takeUntil' p t@ is the largest
-- prefix of @t@ whose measure does not satisfy @p@.
--
-- *  @'takeUntil' p t = 'fst' ('split' p t)@
take :: Int -> Seq a -> Seq a
take n = fst . splitAt n

-- | /O(log(min(i,n-i)))/.
-- Given a monotonic predicate @p@, @'dropUntil' p t@ is the rest of @t@
-- after removing the largest prefix whose measure does not satisfy @p@.
--
-- * @'dropUntil' p t = 'snd' ('split' p t)@
drop :: Int -> Seq a -> Seq a
drop n  =  snd . splitAt n

splitTree :: RuntimeDepth l -> (Int -> Bool) -> Int
          -> SeqN l a -> Split (SeqN l a) (Tree l a)
splitTree !_   _ _ Empty = error "splitTree: illegal argument"
splitTree !_   _ _ (Single x) = Split Empty x Empty
splitTree !lvl p i (Deep _ pr m sf)
  | p vpr     = let Split l x r     =  splitDigit lvl p i pr
                in  Split (maybe Empty (digitToTree lvl) l) x (deepL lvl r m sf)
  | p vm      = let Split ml xs mr = splitTree (nextDepth lvl) p vpr m
                    Split l  x  r  = splitNode lvl p (vpr + measureSeq (nextDepth lvl) ml) xs
                in  Split (deepR lvl pr ml l) x (deepL lvl r mr sf)
  | otherwise = let Split l x r    = splitDigit lvl p vm sf
                in Split (deepR lvl pr m l) x (maybe Empty (digitToTree lvl) r)
  where
    vpr     =  i    +  measureDigit lvl pr
    vm      =  vpr  +  measureSeq (nextDepth lvl) m

deepL :: RuntimeDepth l -> Maybe (Digit l a) -> SeqN ('LSucc l) a
      -> Digit l a -> SeqN l a
deepL !l Nothing   m sf = rotL l m sf
deepL !l (Just pr) m sf = deep l pr m sf

deepR :: RuntimeDepth l -> Digit l a -> SeqN ('LSucc l) a
      -> Maybe (Digit l a) -> SeqN l a
deepR !l pr m Nothing   = rotR l pr m
deepR !l pr m (Just sf) = deep l pr m sf

splitDigit :: RuntimeDepth l -> (Int -> Bool) -> Int -> Digit l a -> Split (Maybe (Digit l a)) (Tree l a)
splitDigit !l _ i (One a) = i `seq` Split Nothing a Nothing
splitDigit !l p i (Two a b)
  | p va      = Split Nothing a (Just (One b))
  | otherwise = Split (Just (One a)) b Nothing
  where
    va = i + measureTree l a
splitDigit !l p i (Three a b c)
  | p va      = Split Nothing a (Just (Two b c))
  | p vab     = Split (Just (One a)) b (Just (One c))
  | otherwise = Split (Just (Two a b)) c Nothing
  where
    va  = i  + measureTree l a
    vab = va + measureTree l b
splitDigit l p i (Four a b c d)
  | p va      = Split Nothing a (Just (Three b c d))
  | p vab     = Split (Just (One a)) b (Just (Two c d))
  | p vabc    = Split (Just (Two a b)) c (Just (One d))
  | otherwise = Split (Just (Three a b c)) d Nothing
  where
    va   = i   + measureTree l a
    vab  = va  + measureTree l b
    vabc = vab + measureTree l c

splitNode :: RuntimeDepth l -> (Int -> Bool)
          -> Int -> Tree ('LSucc l) a
          -> Split (Maybe (Digit l a)) (Tree l a)
splitNode !l p i  (Tree (Node2 _ a b))
  | p va      = Split Nothing a (Just (One b))
  | otherwise = Split (Just (One a)) b Nothing
  where
    va = i + measureTree l a
splitNode !l p i (Tree (Node3 _ a b c))
  | p va      = Split Nothing a (Just (Two b c))
  | p vab     = Split (Just (One a)) b (Just (One c))
  | otherwise = Split (Just (Two a b)) c Nothing
  where
    va  = i  + measureTree l a
    vab = va + measureTree l b


-- * Traversals

traverse' :: Applicative f
          => (a1 -> f a2) -> Seq a1 -> f (Seq a2)
traverse' f (Seq t) = Seq <$> traverse'' zeroDepth f t

traverse'' :: Applicative f
           => RuntimeDepth l -> (a1 -> f a2) -> SeqN l a1 -> f (SeqN l a2)
traverse'' !_ _ Empty = pure Empty
traverse'' !l f (Single x) = Single <$> traverseTree l f x
traverse'' !l f (Deep _ pr m sf) = deep l <$> traverseDigit l f pr <*> traverse'' (nextDepth l) f m <*> traverseDigit l f sf

traverseTree :: Applicative f
             => RuntimeDepth l -> (a1 -> f a2) -> Tree l a1 -> f (Tree l a2)
traverseTree (inspect -> RuntimeZ {}) f (Tree x) = Tree <$> f x
traverseTree (inspect -> RuntimeSucc l') f (Tree (Node2 _ a b)) = treeDigit <$> (node2 l' <$> traverseTree l' f a <*> traverseTree l' f b)
traverseTree (inspect -> RuntimeSucc l') f (Tree (Node3 _ a b c)) = treeDigit <$> (node3 l' <$> traverseTree l' f a <*> traverseTree l' f b <*> traverseTree l' f c)

traverseDigit :: Applicative f
              => RuntimeDepth l -> (a1 -> f a2) -> Digit l a1 -> f (Digit l a2)
traverseDigit !l f (One a) = One <$> traverseTree l f a
traverseDigit !l f (Two a b) = Two <$> traverseTree l f a <*> traverseTree l f b
traverseDigit !l f (Three a b c) = Three <$> traverseTree l f a <*> traverseTree l f b <*> traverseTree l f c
traverseDigit !l f (Four a b c d) = Four <$> traverseTree l f a <*> traverseTree l f b <*> traverseTree l f c <*> traverseTree l f d

traverseWithIndex :: Applicative f
                => (Int -> a1 -> f a2) -> Seq a1 -> f (Seq a2)
traverseWithIndex f (Seq t) = Seq <$> traverseWithIndex' zeroDepth f 0 t

traverseWithIndex' :: Applicative f
                 => RuntimeDepth l -> (Int -> a1 -> f a2) -> Int -> SeqN l a1 -> f (SeqN l a2)
traverseWithIndex' !_ _ _ Empty = pure Empty
traverseWithIndex' !l f v (Single x) = Single <$> traverseWITree l f v x
traverseWithIndex' !l f v (Deep _ pr m sf) =
  deep l <$> traverseWIDigit l f v pr <*> traverseWithIndex' (nextDepth l) f vpr m <*> traverseWIDigit l f vm sf
  where
    vpr = v   + measureDigit l pr
    vm  = vpr + measureSeq (nextDepth l) m

traverseWITree :: Applicative f
               => RuntimeDepth l -> (Int -> a1 -> f a2) -> Int -> Tree l a1 -> f (Tree l a2)
traverseWITree (inspect -> RuntimeZ {}) f v (Tree x) = Tree <$> f v x
traverseWITree (inspect -> RuntimeSucc l') f v (Tree (Node2 _ a b)) =
  treeDigit <$> (node2 l' <$> traverseWITree l' f v a <*> traverseWITree l' f va b)
  where
    va = v + measureTree l' a
traverseWITree (inspect -> RuntimeSucc l') f v (Tree (Node3 _ a b c)) =
  treeDigit <$> (node3 l' <$> traverseWITree l' f v a <*> traverseWITree l' f va b <*> traverseWITree l' f vb c)
  where
    va = v  + measureTree l' a
    vb = va + measureTree l' b

traverseWIDigit :: Applicative f
                => RuntimeDepth l -> (Int -> a1 -> f a2) -> Int -> Digit l a1 -> f (Digit l a2)
traverseWIDigit !l f v (One a) = One <$> traverseWITree l f v a
traverseWIDigit !l f v (Two a b) = Two <$> traverseWITree l f v a <*> traverseWITree l f va b
  where
    va = v + measureTree l a
traverseWIDigit !l f v (Three a b c) = Three <$> traverseWITree l f v a <*> traverseWITree l f va b
                                             <*> traverseWITree l f vb c
  where
    va = v  + measureTree l a
    vb = va + measureTree l b
traverseWIDigit !l f v (Four a b c d) = Four <$> traverseWITree l f v a  <*> traverseWITree l f va b
                                             <*> traverseWITree l f vb c <*> traverseWITree l f vc d
  where
    va = v  + measureTree l a
    vb = va + measureTree l b
    vc = vb + measureTree l c

toListSeq :: RuntimeDepth l -> SeqN l a -> [ a ] -> [ a ]
toListSeq !l Empty {} a = a
toListSeq !l (Single x) a = toListTree l x a
toListSeq !l (Deep _ pr m sf) a = toListDigit l pr (toListSeq (nextDepth l) m (toListDigit l sf a))

toListDigit :: RuntimeDepth l -> Digit l a -> [ a ] -> [ a ]
toListDigit !l (One a) next = toListTree l a next
toListDigit !l (Two a b) next = toListTree l a (toListTree l b next)
toListDigit !l (Three a b c) next = toListTree l a (toListTree l b (toListTree l c next))
toListDigit !l (Four a b c d) next = toListTree l a (toListTree l b (toListTree l c (toListTree l d next)))

toListTree :: RuntimeDepth l -> Tree l a -> [ a ] -> [ a ]
toListTree (inspect -> RuntimeZ {}) (Tree t) next = t:next
toListTree (inspect -> RuntimeSucc l') (Tree (Node2 _ a b)) next =
  toListTree l' a (toListTree l' b next)
toListTree (inspect -> RuntimeSucc l') (Tree (Node3 _ a b c)) next =
  toListTree l' a (toListTree l' b (toListTree l' c next))

(!?) :: Seq a -> Int -> Maybe a
Seq n !? i = go zeroDepth n i
  where
    go :: RuntimeDepth l -> SeqN l a -> Int -> Maybe a
    go _ Empty _ = Nothing
    go l (Single x) i
      | i < measureTree l x = goTree l x i
      | otherwise = Nothing
    go l (Deep vsf pr m sf) i
      | i < vpr = goDigit l pr i
      | i < vm  = go (nextDepth l) m (i - vpr)
      | i < vsf = goDigit l sf (i - vm)
      | otherwise = Nothing
      where
        vpr = measureDigit l pr
        vm  = vpr + measureSeq (nextDepth l) m

    goTree :: RuntimeDepth l -> Tree l a -> Int -> Maybe a
    goTree (inspect -> RuntimeZ {}) (Tree x) _ = Just x
    goTree (inspect -> RuntimeSucc l) (Tree n) i =
      case n of
        Node2 _ a b
          | i < va    -> goTree l a i
          | otherwise -> goTree l b (i - va)
          where va = measureTree l a
        Node3 _ a b c
          | i < va    -> goTree l a i
          | i < vb    -> goTree l b (i - va)
          | otherwise -> goTree l c (i - vb)
          where va = measureTree l a
                vb = va + measureTree l b

    goDigit :: RuntimeDepth l -> Digit l a -> Int -> Maybe a
    goDigit l (One a) i = goTree l a i
    goDigit l (Two a b) i
      | i < va    = goTree l a i
      | otherwise = goTree l b (i - va)
      where va = measureTree l a
    goDigit l (Three a b c) i
      | i < va    = goTree l a i
      | i < vb    = goTree l b (i - va)
      | otherwise = goTree l c (i - vb)
      where va = measureTree l a
            vb = va + measureTree l b
    goDigit l (Four a b c d) i
      | i < va    = goTree l a i
      | i < vb    = goTree l b (i - va)
      | i < vc    = goTree l c (i - vb)
      | otherwise = goTree l d (i - vc)
      where va = measureTree l a
            vb = va + measureTree l b
            vc = vb + measureTree l c

(!!) :: Seq a -> Int -> a
s !! i = case s !? i of
           Nothing -> error "(!!): out of bounds"
           Just x  -> x

index :: Seq a -> Int -> a
index = (!!)

replicate :: Int -> a -> Seq a
replicate 0 _ = empty
replicate 1 a = singleton a
replicate n a =
  let (n', r) = n `divMod` 2
      half = replicate n' a
      both = half >< half
  in if r == 0 then both else both |> a
