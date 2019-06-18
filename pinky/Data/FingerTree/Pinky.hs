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
module Data.FingerTree.Pinky
   ( FingerTree, Measured(..)
   , empty, singleton
   , (<|), (|>), (><)
   , fromList
   , null
   , ViewL(..), viewl
   , ViewR(..), viewr
   , split, takeUntil, dropUntil
   , traverse', traverseWithPos
   ) where

import Prelude hiding (null)

import Data.Monoid
import Data.Foldable (toList)
import Data.Word (Word)

import Text.Show

import Unsafe.Coerce

infixr 5 ><
infixr 5 <|, <|*, :<
infixl 5 |>, |>*, :>

class Monoid v => Measured v a | a -> v where
  measure :: a -> v

data Level = LZ | LSucc Level
  deriving Show

newtype RuntimeDepth (l :: Level) = RuntimeDepth Word

data RuntimeDepthInspection (l :: Level) where
    RuntimeZ :: RuntimeDepthInspection 'LZ
    RuntimeSucc :: RuntimeDepth l -> RuntimeDepthInspection ('LSucc l)

{-# INLINE inspect #-}
inspect :: RuntimeDepth l -> RuntimeDepthInspection l
inspect (RuntimeDepth 0) = unsafeCoerce RuntimeZ
inspect (RuntimeDepth n) = unsafeCoerce (RuntimeSucc (RuntimeDepth (n - 1)))

--  RuntimeZ :: RuntimeDepth ('LSucc 'LZ) -> RuntimeDepth 'LZ
--  RuntimeSucc :: RuntimeDepth l -> RuntimeDepth ('LSucc ('LSucc l)) -> RuntimeDepth ('LSucc l)

instance Show (RuntimeDepth l) where
  show _ = "_"

{-# INLINE prevDepth #-}
prevDepth :: RuntimeDepth ('LSucc l) -> RuntimeDepth l
prevDepth (RuntimeDepth n) = RuntimeDepth (n - 1)
--prevDepth (RuntimeSucc a _) = a

{-# INLINE nextDepth #-}
nextDepth :: RuntimeDepth l -> RuntimeDepth ('LSucc l)
nextDepth (RuntimeDepth n) = RuntimeDepth (n + 1)
-- nextDepth (RuntimeZ n) = n
-- nextDepth (RuntimeSucc _ n) = n

newtype FingerTree v a = FingerTree (FingerTreeN 'LZ v a)

instance Show a => Show (FingerTree v a) where
  showsPrec d x =
    showParen (d > app_prec) $
    (showString "fromList " . showsPrec (app_prec + 1) (toList x))
    where app_prec = 10

instance Foldable (FingerTree v) where
  foldMap f (FingerTree ft) = foldMapFingerTree zeroDepth f ft
  foldr f x (FingerTree ft) = foldrFingerTree zeroDepth f x ft
  toList (FingerTree ft) = toListFingerTree zeroDepth ft []

instance Measured v a => Measured v (FingerTree v a) where
  measure (FingerTree ft) = measureFingerTree zeroDepth ft

instance Measured v a => Monoid (FingerTree v a) where
  mempty = empty
  mappend = (><)

instance Measured v a => Semigroup (FingerTree v a) where
  (<>) = (><)

data FingerTreeN (l :: Level) v a where
  Empty :: FingerTreeN l v a
  Single :: Tree l v a -> FingerTreeN l v a
  Deep :: !v -> !(Digit l v a)
       -> !(FingerTreeN ('LSucc l) v a)
       -> !(Digit l v a) -> FingerTreeN l v a

foldMapFingerTree :: Monoid b => RuntimeDepth l -> (a -> b) -> FingerTreeN l v a -> b
foldMapFingerTree !l _ Empty {} = mempty
foldMapFingerTree !l f (Single x) = foldMapTree l f x
foldMapFingerTree !l f (Deep _ pr m sf) = foldMapDigit l f pr `mappend` foldMapFingerTree (nextDepth l) f m `mappend` foldMapDigit l f sf

foldrFingerTree :: RuntimeDepth l -> (a -> b -> b) -> b -> FingerTreeN l v a -> b
foldrFingerTree !l _ x Empty{} = x
foldrFingerTree !l f x (Single a) = foldrTree l f x a
foldrFingerTree !l f x (Deep _ pr m sf) = foldrDigit l f (foldrFingerTree (nextDepth l) f (foldrDigit l f x sf) m) pr

foldMapTree :: Monoid b => RuntimeDepth l -> (a -> b) -> Tree l v a -> b
foldMapTree (inspect -> RuntimeZ {}) f (Tree a) = f a
foldMapTree (inspect -> RuntimeSucc l') f (Tree (Node2 _ a b)) = foldMapTree l' f a `mappend` foldMapTree l' f b
foldMapTree (inspect -> RuntimeSucc l') f (Tree (Node3 _ a b c)) = foldMapTree l' f a `mappend` foldMapTree l' f b `mappend` foldMapTree l' f c

foldrDigit :: RuntimeDepth l -> (a -> b -> b) -> b -> Digit l v a -> b
foldrDigit !l f x (One a)        = {-# SCC foldrDigitOne #-} foldrTree l f x a
foldrDigit !l f x (Two a b)      = {-# SCC foldrDigitTwo #-} next (next x b) a
  where next = foldrTree l f
foldrDigit !l f x (Three a b c)  = {-# SCC foldrDigitThree #-} next (next (next x c) b) a
  where next = foldrTree l f
foldrDigit !l f x (Four a b c d) = {-# SCC foldrDigitFour #-} next (next (next (next x d) c) b) a
  where next = foldrTree l f

foldrTree :: RuntimeDepth l -> (a -> b -> b) -> b -> Tree l v a -> b
foldrTree (inspect -> RuntimeZ {}) f x (Tree a) = {-# SCC foldrTreeOne #-} f a x
foldrTree (inspect -> RuntimeSucc l') f x (Tree (Node2 _ a b)) = {-# SCC foldrTreeNode2 #-} next (next x b) a
  where next = foldrTree l' f
foldrTree (inspect -> RuntimeSucc l') f x (Tree (Node3 _ a b c)) = {-# SCC foldrTreeNode3 #-} next (next (next x c) b) a
  where next = foldrTree l' f

foldMapDigit :: Monoid b => RuntimeDepth l -> (a -> b) -> Digit l v a -> b
foldMapDigit !l f (One a) = foldMapTree l f a
foldMapDigit !l f (Two a b) = foldMapTree l f a `mappend` foldMapTree l f b
foldMapDigit !l f (Three a b c) = foldMapTree l f a `mappend` foldMapTree l f b `mappend` foldMapTree l f c
foldMapDigit !l f (Four a b c d) = foldMapTree l f a `mappend` foldMapTree l f b `mappend` foldMapTree l f c `mappend` foldMapTree l f d

measureFingerTree :: Measured v a => RuntimeDepth l -> FingerTreeN l v a -> v
measureFingerTree !_ Empty {} = mempty
measureFingerTree !l (Single a) = measureTree l a
measureFingerTree !_ (Deep v _ _ _) = v

data Digit (n :: Level) v a
  = One   (Tree n v a)
  | Two   (Tree n v a) (Tree n v a)
  | Three (Tree n v a) (Tree n v a) (Tree n v a)
  | Four  (Tree n v a) (Tree n v a) (Tree n v a) (Tree n v a)

measureDigit :: Measured v a => RuntimeDepth l -> Digit l v a -> v
measureDigit !l (One a) = measureTree l a
measureDigit !l (Two a b) = measureTree l a `mappend` measureTree l b
measureDigit !l (Three a b c) = measureTree l a `mappend` measureTree l b `mappend` measureTree l c
measureDigit !l (Four a b c d) = measureTree l a `mappend` measureTree l b `mappend` measureTree l c `mappend` measureTree l d

newtype Tree n v a = Tree (TreeF n v a)

type family TreeF (n :: Level) v a where
  TreeF LZ v a = a
  TreeF (LSucc l) v a = Node l v a

treeDigit :: Node l v a -> Tree ('LSucc l) v a
treeDigit n = Tree n

measureTree :: Measured v a => RuntimeDepth l -> Tree l v a -> v
measureTree (inspect -> RuntimeZ {}) (Tree x) = measure x
measureTree (inspect -> RuntimeSucc {}) (Tree n) = measure n

data Node n v a
  = Node2 !v !(Tree n v a) !(Tree n v a)
  | Node3 !v !(Tree n v a) !(Tree n v a) !(Tree n v a)

node2 :: Measured v a => RuntimeDepth n -> Tree n v a -> Tree n v a -> Node n v a
node2 !l a b = Node2 (measureTree l a `mappend` measureTree l b) a b

node3 :: Measured v a => RuntimeDepth n -> Tree n v a -> Tree n v a -> Tree n v a -> Node n v a
node3 !l a b c = Node3 (measureTree l a `mappend` measureTree l b `mappend` measureTree l c) a b c

instance Measured v a => Measured v (Node l v a) where
  measure (Node2 v _ _) = v
  measure (Node3 v _ _ _) = v

zeroDepth :: RuntimeDepth 'LZ
zeroDepth = RuntimeDepth 0
--            let z = RuntimeZ (next z)
--            in z
--   where
--     next :: RuntimeDepth l -> RuntimeDepth ('LSucc l)
--     next s = let n = RuntimeSucc s (next n)
--              in n

nodeToDigit :: Node l v a -> Digit l v a
nodeToDigit (Node2 _ a b) = Two a b
nodeToDigit (Node3 _ a b c) = Three a b c

deep :: Measured v a
     => RuntimeDepth l -> Digit (l :: Level) v a -> FingerTreeN ('LSucc l) v a -> Digit l v a -> FingerTreeN l v a
deep !l pr m sf =
  Deep ((measureDigit l pr `mappend` measureFingerTree (nextDepth l) m) `mappend` measureDigit l sf) pr m sf

-- * Construuction, deconstruction, and concatenation

-- | /O(1)/. The empty sequence
empty :: Measured v a => FingerTree v a
empty = FingerTree Empty

-- | /O(1)/. The singleton sequence
singleton :: Measured v a => a -> FingerTree v a
singleton a = FingerTree (Single (Tree a))

-- | /O(n)/. Create sequence from finite list of elements.
-- The opposite operation 'toList' is provided by the 'Foldable' instance.
fromList :: Measured v a => [a] -> FingerTree v a
fromList = foldr (<|) empty

-- | /O(1)/. Add an element to the left end of a sequence
(<|) :: Measured v a => a -> FingerTree v a -> FingerTree v a
a <| FingerTree ft = FingerTree ((zeroDepth, Tree a) <|* ft)

(<|*) :: Measured v a => (RuntimeDepth l, Tree l v a) -> FingerTreeN l v a -> FingerTreeN l v a
(!l, a) <|* Empty = Single a
(!l, a) <|* (Single b) = deep l (One a) Empty (One b)
(!l, a) <|* (Deep v (Four b c d e) m sf) =
  m `seq` Deep (measureTree l a `mappend` v) (Two a b) ((nextDepth l, treeDigit (node3 l c d e)) <|* m) sf
(!l, a) <|* Deep v pr m sf =
  Deep (measureTree l a `mappend` v) (consDigit a pr) m sf

consDigit :: Tree l v a -> Digit l v a -> Digit l v a
consDigit a (One b) = Two a b
consDigit a (Two b c) = Three a b c
consDigit a (Three b c d) = Four a b c d
consDigit _ (Four {}) = error "consDigit: illegal argument"

-- | /O(1)/. Add an element to the right end of a sequence.
(|>) :: Measured v a => FingerTree v a -> a -> FingerTree v a
FingerTree ft |> a = FingerTree (ft |>* (zeroDepth, Tree a))

{-# INLINE (|>*) #-}
(|>*) :: Measured v a => FingerTreeN l v a -> (RuntimeDepth l, Tree l v a) -> FingerTreeN l v a
Empty |>* (!_, a) = Single a
Single a |>* (!l, b) = deep l (One a) Empty (One b)
Deep v pr m (Four a b c d) |>* (!l, e) = m `seq`
  Deep (v `mappend` measureTree l e) pr (m |>* (nextDepth l, treeDigit (node3 l a b c))) (Two d e)
Deep v pr m sf |>* (!l, x) =
  Deep (v `mappend` measureTree l x) pr m (snocDigit sf x)

snocDigit :: Digit l v a -> Tree l v a -> Digit l v a
snocDigit (One a) b = Two a b
snocDigit (Two a b) c = Three a b c
snocDigit (Three a b c) d = Four a b c d
snocDigit (Four {}) _ = error "snocDigit: illegal argument"

-- | /O(1)/. Is this the empty sequence?
null :: FingerTree v a -> Bool
null (FingerTree Empty {}) = True
null _ = False

data ViewL s a
  = EmptyL
  | a :< s a

-- | /O(1)/. Analyse the left end of a sequence.
viewl :: Measured v a => FingerTree v a -> ViewL (FingerTree v) a
viewl (FingerTree ft) = case viewl' zeroDepth ft of
                          Nothing -> EmptyL
                          Just (Tree a, ft) -> a :< FingerTree ft

viewl' :: Measured v a => RuntimeDepth l -> FingerTreeN l v a -> Maybe (Tree l v a, FingerTreeN l v a)
viewl' !_ Empty {} = Nothing
viewl' !_ (Single x) = Just (x, Empty)
viewl' !l (Deep _ (One x) m sf) = Just (x, rotL l m sf)
viewl' !l (Deep _ pr m sf) = Just (lheadDigit pr, deep l (ltailDigit pr) m sf)

rotL :: Measured v a => RuntimeDepth l -> FingerTreeN ('LSucc l) v a -> Digit l v a -> FingerTreeN l v a
rotL !l m sf =
  case viewl' (nextDepth l) m of
    Nothing -> digitToTree l sf
    Just (Tree a, m') -> Deep (measureFingerTree (nextDepth l) m `mappend` measureDigit l sf) (nodeToDigit a) m' sf

lheadDigit :: Digit l v a -> Tree l v a
lheadDigit (One a) = a
lheadDigit (Two a _) = a
lheadDigit (Three a _ _) = a
lheadDigit (Four a _ _ _) = a

ltailDigit :: Digit l v a -> Digit l v a
ltailDigit (One _) = error "ltailDigit: illegal argument"
ltailDigit (Two _ b) = One b
ltailDigit (Three _ b c) = Two b c
ltailDigit (Four _ b c d) = Three b c d

data ViewR s a
  = EmptyR
  | s a :> a

-- | /O(1)/. Analyze the right end of a sequence
viewr :: Measured v a => FingerTree v a -> ViewR (FingerTree v) a
viewr (FingerTree ft) = case viewr' zeroDepth ft of
                          Nothing -> EmptyR
                          Just (ft, Tree a) -> FingerTree ft :> a

viewr' :: Measured v a => RuntimeDepth l -> FingerTreeN l v a -> Maybe (FingerTreeN l v a, Tree l v a)
viewr' !_ Empty {} = Nothing
viewr' !_ (Single x) = Just (Empty, x)
viewr' !l (Deep _ pr m (One x)) = Just (rotR l pr m, x)
viewr' !l (Deep _ pr m sf) = Just (deep l pr m (rtailDigit sf), rheadDigit sf)

rotR :: Measured v a => RuntimeDepth l -> Digit l v a -> FingerTreeN ('LSucc l) v a -> FingerTreeN l v a
rotR !l pr m =
  case viewr' (nextDepth l) m of
    Nothing -> digitToTree l pr
    Just (m', Tree a) -> Deep (measureDigit l pr `mappend` measureFingerTree (nextDepth l) m) pr m' (nodeToDigit a)

rheadDigit :: Digit l v a -> Tree l v a
rheadDigit (One a) = a
rheadDigit (Two _ b) = b
rheadDigit (Three _ _ c) = c
rheadDigit (Four _ _ _ d) = d

rtailDigit :: Digit l v a -> Digit l v a
rtailDigit (One _) = error "rtailDigit: illegal argument"
rtailDigit (Two _ b) = One b
rtailDigit (Three _ b c) = Two b c
rtailDigit (Four _ b c d) = Three b c d

digitToTree :: Measured v a => RuntimeDepth l -> Digit l v a -> FingerTreeN l v a
digitToTree !l (One a) = Single a
digitToTree !l (Two a b) = deep l (One a) Empty (One b)
digitToTree !l (Three a b c) = deep l (Two a b) Empty (One c)
digitToTree !l (Four a b c d) = deep l (Two a b) Empty (Two c d)

-- * Concatenation

-- | /O(log(min(n1, n2)))/. Concatenate two sequences
(><) :: Measured v a => FingerTree v a -> FingerTree v a -> FingerTree v a
FingerTree a >< FingerTree b = FingerTree (appendTree0 zeroDepth a b)

appendTree0 :: Measured v a => RuntimeDepth l -> FingerTreeN l v a -> FingerTreeN l v a -> FingerTreeN l v a
appendTree0 !_ (Empty {}) xs = xs
appendTree0 !_ xs (Empty {}) = xs
appendTree0 !l (Single x) xs = (l, x) <|* xs
appendTree0 !l xs (Single x) = xs |>* (l, x)
appendTree0 !l (Deep _ pr1 m1 sf1) (Deep _ pr2 m2 sf2) =
  deep l pr1 (addDigits0 l m1 sf1 pr2 m2) sf2

addDigits0 :: Measured v a
           => RuntimeDepth l
           -> FingerTreeN ('LSucc l) v a
           -> Digit l v a -> Digit l v a
           -> FingerTreeN ('LSucc l) v a -> FingerTreeN ('LSucc l) v a
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

appendTree1 :: Measured v a => RuntimeDepth l -> FingerTreeN ('LSucc l) v a -> Node l v a -> FingerTreeN ('LSucc l) v a -> FingerTreeN ('LSucc l) v a
appendTree1 !l Empty {} a xs = (l', treeDigit a) <|* xs
  where l' = nextDepth l
appendTree1 !l xs a Empty {} = xs |>* (l', treeDigit a)
  where l' = nextDepth l
appendTree1 !l (Single x) a xs = (l', x) <|* (l', treeDigit a) <|* xs
  where l' = nextDepth l
appendTree1 !l xs a (Single x) = xs |>* (l', treeDigit a) |>* (l', x)
  where l' = nextDepth l
appendTree1 !l (Deep _ pr1 m1 sf1) a (Deep _ pr2 m2 sf2) =
  deep l' pr1 (addDigits1 l' m1 sf1 (treeDigit a) pr2 m2) sf2
  where l' = nextDepth l

addDigits1 :: Measured v a
           => RuntimeDepth l -> FingerTreeN ('LSucc l) v a
           -> Digit l v a -> Tree l v a -> Digit l v a
           -> FingerTreeN ('LSucc l) v a -> FingerTreeN ('LSucc l) v a
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

appendTree2 :: Measured v a
            => RuntimeDepth l
            -> FingerTreeN ('LSucc l) v a -> Node l v a -> Node l v a
            -> FingerTreeN ('LSucc l) v a -> FingerTreeN ('LSucc l) v a
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
appendTree2 !l (Deep _ pr1 m1 sf1) a b (Deep _ pr2 m2 sf2) =
  deep l' pr1 (addDigits2 l' m1 sf1 (treeDigit a) (treeDigit b) pr2 m2) sf2
  where l' = nextDepth l

addDigits2 :: Measured v a
           => RuntimeDepth l -> FingerTreeN ('LSucc l) v a
           -> Digit l v a -> Tree l v a -> Tree l v a -> Digit l v a
           -> FingerTreeN ('LSucc l) v a -> FingerTreeN ('LSucc l) v a
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

appendTree3 :: Measured v a
            => RuntimeDepth l
            -> FingerTreeN ('LSucc l) v a -> Node l v a -> Node l v a -> Node l v a
            -> FingerTreeN ('LSucc l) v a -> FingerTreeN ('LSucc l) v a
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
appendTree3 !l (Deep _ pr1 m1 sf1) a b c (Deep _ pr2 m2 sf2) =
  deep l' pr1 (addDigits3 l' m1 sf1 (treeDigit a) (treeDigit b) (treeDigit c) pr2 m2) sf2
  where l' = nextDepth l

addDigits3 :: Measured v a
           => RuntimeDepth l -> FingerTreeN ('LSucc l) v a
           -> Digit l v a -> Tree l v a -> Tree l v a -> Tree l v a -> Digit l v a
           -> FingerTreeN ('LSucc l) v a -> FingerTreeN ('LSucc l) v a
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

appendTree4 :: Measured v a
            => RuntimeDepth l -> FingerTreeN ('LSucc l) v a
            -> Node l v a -> Node l v a -> Node l v a -> Node l v a
            -> FingerTreeN ('LSucc l) v a -> FingerTreeN ('LSucc l) v a
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
appendTree4 !l (Deep _ pr1 m1 sf1) a b c d (Deep _ pr2 m2 sf2) =
  deep l' pr1 (addDigits4 l' m1 sf1 (treeDigit a) (treeDigit b) (treeDigit c) (treeDigit d) pr2 m2) sf2
  where l' = nextDepth l

addDigits4 :: Measured v a
           => RuntimeDepth l -> FingerTreeN ('LSucc l) v a -> Digit l v a
           -> Tree l v a -> Tree l v a -> Tree l v a -> Tree l v a
           -> Digit l v a -> FingerTreeN ('LSucc l) v a -> FingerTreeN ('LSucc l) v a
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
{-# INLINE split #-}
split :: Measured v a
      => (v -> Bool) -> FingerTree v a -> (FingerTree v a, FingerTree v a)
split p xs
  | p (measure xs) = ( FingerTree l, FingerTree ((zeroDepth, Tree x) <|* r) )
  | otherwise      = ( xs, FingerTree Empty )
  where
    Split l (Tree x) r =
      case xs of
        FingerTree xs' -> splitTree zeroDepth p mempty xs'

-- | /O(log(min(i,n-i)))/.
-- Given a monotonic predicate @p@, @'takeUntil' p t@ is the largest
-- prefix of @t@ whose measure does not satisfy @p@.
--
-- *  @'takeUntil' p t = 'fst' ('split' p t)@
takeUntil :: Measured v a => (v -> Bool) -> FingerTree v a -> FingerTree v a
takeUntil p = fst . split p

-- | /O(log(min(i,n-i)))/.
-- Given a monotonic predicate @p@, @'dropUntil' p t@ is the rest of @t@
-- after removing the largest prefix whose measure does not satisfy @p@.
--
-- * @'dropUntil' p t = 'snd' ('split' p t)@
dropUntil :: (Measured v a) => (v -> Bool) -> FingerTree v a -> FingerTree v a
dropUntil p  =  snd . split p

splitTree :: Measured v a
          => RuntimeDepth l -> (v -> Bool) -> v
          -> FingerTreeN l v a -> Split (FingerTreeN l v a) (Tree l v a)
splitTree !_   _ _ Empty = error "splitTree: illegal argument"
splitTree !_   _ _ (Single x) = Split Empty x Empty
splitTree !lvl p i (Deep _ pr m sf)
  | p vpr     = let Split l x r     =  splitDigit lvl p i pr
                in  Split (maybe Empty (digitToTree lvl) l) x (deepL lvl r m sf)
  | p vm      = let Split ml xs mr = splitTree (nextDepth lvl) p vpr m
                    Split l  x  r  = splitNode lvl p (vpr `mappend` measureFingerTree (nextDepth lvl) ml) xs
                in  Split (deepR lvl pr ml l) x (deepL lvl r mr sf)
  | otherwise = let Split l x r    = splitDigit lvl p vm sf
                in Split (deepR lvl pr m l) x (maybe Empty (digitToTree lvl) r)
  where
    vpr     =  i    `mappend`  measureDigit lvl pr
    vm      =  vpr  `mappend`  measureFingerTree (nextDepth lvl) m

deepL :: Measured v a
      => RuntimeDepth l -> Maybe (Digit l v a) -> FingerTreeN ('LSucc l) v a
      -> Digit l v a -> FingerTreeN l v a
deepL !l Nothing   m sf = rotL l m sf
deepL !l (Just pr) m sf = deep l pr m sf

deepR :: Measured v a
      => RuntimeDepth l -> Digit l v a -> FingerTreeN ('LSucc l) v a
      -> Maybe (Digit l v a) -> FingerTreeN l v a
deepR !l pr m Nothing   = rotR l pr m
deepR !l pr m (Just sf) = deep l pr m sf

splitDigit :: Measured v a
           => RuntimeDepth l -> (v -> Bool) -> v -> Digit l v a -> Split (Maybe (Digit l v a)) (Tree l v a)
splitDigit !l _ i (One a) = i `seq` Split Nothing a Nothing
splitDigit !l p i (Two a b)
  | p va      = Split Nothing a (Just (One b))
  | otherwise = Split (Just (One a)) b Nothing
  where
    va = i `mappend` measureTree l a
splitDigit !l p i (Three a b c)
  | p va      = Split Nothing a (Just (Two b c))
  | p vab     = Split (Just (One a)) b (Just (One c))
  | otherwise = Split (Just (Two a b)) c Nothing
  where
    va  = i  `mappend` measureTree l a
    vab = va `mappend` measureTree l b
splitDigit l p i (Four a b c d)
  | p va      = Split Nothing a (Just (Three b c d))
  | p vab     = Split (Just (One a)) b (Just (Two c d))
  | p vabc    = Split (Just (Two a b)) c (Just (One d))
  | otherwise = Split (Just (Three a b c)) d Nothing
  where
    va   = i   `mappend` measureTree l a
    vab  = va  `mappend` measureTree l b
    vabc = vab `mappend` measureTree l c

splitNode :: Measured v a
          => RuntimeDepth l -> (v -> Bool)
          -> v -> Tree ('LSucc l) v a
          -> Split (Maybe (Digit l v a)) (Tree l v a)
splitNode !l p i  (Tree (Node2 _ a b))
  | p va      = Split Nothing a (Just (One b))
  | otherwise = Split (Just (One a)) b Nothing
  where
    va = i `mappend` measureTree l a
splitNode !l p i (Tree (Node3 _ a b c))
  | p va      = Split Nothing a (Just (Two b c))
  | p vab     = Split (Just (One a)) b (Just (One c))
  | otherwise = Split (Just (Two a b)) c Nothing
  where
    va  = i  `mappend` measureTree l a
    vab = va `mappend` measureTree l b


-- * Traversals

traverse' :: (Measured v1 a1, Measured v2 a2, Applicative f)
          => (a1 -> f a2) -> FingerTree v1 a1 -> f (FingerTree v2 a2)
traverse' f (FingerTree t) = FingerTree <$> traverse'' zeroDepth f t

traverse'' :: (Measured v1 a1, Measured v2 a2, Applicative f)
           => RuntimeDepth l -> (a1 -> f a2) -> FingerTreeN l v1 a1 -> f (FingerTreeN l v2 a2)
traverse'' !_ _ Empty = pure Empty
traverse'' !l f (Single x) = Single <$> traverseTree l f x
traverse'' !l f (Deep _ pr m sf) = deep l <$> traverseDigit l f pr <*> traverse'' (nextDepth l) f m <*> traverseDigit l f sf

traverseTree :: (Measured v1 a1, Measured v2 a2, Applicative f)
             => RuntimeDepth l -> (a1 -> f a2) -> Tree l v1 a1 -> f (Tree l v2 a2)
traverseTree (inspect -> RuntimeZ {}) f (Tree x) = Tree <$> f x
traverseTree (inspect -> RuntimeSucc l') f (Tree (Node2 _ a b)) = treeDigit <$> (node2 l' <$> traverseTree l' f a <*> traverseTree l' f b)
traverseTree (inspect -> RuntimeSucc l') f (Tree (Node3 _ a b c)) = treeDigit <$> (node3 l' <$> traverseTree l' f a <*> traverseTree l' f b <*> traverseTree l' f c)

traverseDigit :: (Measured v1 a1, Measured v2 a2, Applicative f)
              => RuntimeDepth l -> (a1 -> f a2) -> Digit l v1 a1 -> f (Digit l v2 a2)
traverseDigit !l f (One a) = One <$> traverseTree l f a
traverseDigit !l f (Two a b) = Two <$> traverseTree l f a <*> traverseTree l f b
traverseDigit !l f (Three a b c) = Three <$> traverseTree l f a <*> traverseTree l f b <*> traverseTree l f c
traverseDigit !l f (Four a b c d) = Four <$> traverseTree l f a <*> traverseTree l f b <*> traverseTree l f c <*> traverseTree l f d

traverseWithPos :: (Measured v1 a1, Measured v2 a2, Applicative f)
                => (v1 -> a1 -> f a2) -> FingerTree v1 a1 -> f (FingerTree v2 a2)
traverseWithPos f (FingerTree t) = FingerTree <$> traverseWithPos' zeroDepth f mempty t

traverseWithPos' :: (Measured v1 a1, Measured v2 a2, Applicative f)
                 => RuntimeDepth l -> (v1 -> a1 -> f a2) -> v1 -> FingerTreeN l v1 a1 -> f (FingerTreeN l v2 a2)
traverseWithPos' !_ _ _ Empty = pure Empty
traverseWithPos' !l f v (Single x) = Single <$> traverseWPTree l f v x
traverseWithPos' !l f v (Deep _ pr m sf) =
  deep l <$> traverseWPDigit l f v pr <*> traverseWithPos' (nextDepth l) f vpr m <*> traverseWPDigit l f vm sf
  where
    vpr = v   `mappend` measureDigit l pr
    vm  = vpr `mappend` measureFingerTree (nextDepth l) m

traverseWPTree :: (Measured v1 a1, Measured v2 a2, Applicative f)
               => RuntimeDepth l -> (v1 -> a1 -> f a2) -> v1 -> Tree l v1 a1 -> f (Tree l v2 a2)
traverseWPTree (inspect -> RuntimeZ {}) f v (Tree x) = Tree <$> f v x
traverseWPTree (inspect -> RuntimeSucc l') f v (Tree (Node2 _ a b)) =
  treeDigit <$> (node2 l' <$> traverseWPTree l' f v a <*> traverseWPTree l' f va b)
  where
    va = v `mappend` measureTree l' a
traverseWPTree (inspect -> RuntimeSucc l') f v (Tree (Node3 _ a b c)) =
  treeDigit <$> (node3 l' <$> traverseWPTree l' f v a <*> traverseWPTree l' f va b <*> traverseWPTree l' f vb c)
  where
    va = v  `mappend` measureTree l' a
    vb = va `mappend` measureTree l' b

traverseWPDigit :: (Measured v1 a1, Measured v2 a2, Applicative f)
                => RuntimeDepth l -> (v1 -> a1 -> f a2) -> v1 -> Digit l v1 a1 -> f (Digit l v2 a2)
traverseWPDigit !l f v (One a) = One <$> traverseWPTree l f v a
traverseWPDigit !l f v (Two a b) = Two <$> traverseWPTree l f v a <*> traverseWPTree l f va b
  where
    va = v `mappend` measureTree l a
traverseWPDigit !l f v (Three a b c) = Three <$> traverseWPTree l f v a <*> traverseWPTree l f va b
                                             <*> traverseWPTree l f vb c
  where
    va = v  `mappend` measureTree l a
    vb = va `mappend` measureTree l b
traverseWPDigit !l f v (Four a b c d) = Four <$> traverseWPTree l f v a  <*> traverseWPTree l f va b
                                             <*> traverseWPTree l f vb c <*> traverseWPTree l f vc d
  where
    va = v  `mappend` measureTree l a
    vb = va `mappend` measureTree l b
    vc = vb `mappend` measureTree l c

toListFingerTree :: RuntimeDepth l -> FingerTreeN l v a -> [ a ] -> [ a ]
toListFingerTree !l Empty {} a = a
toListFingerTree !l (Single x) a = toListTree l x a
toListFingerTree !l (Deep _ pr m sf) a = toListDigit l pr (toListFingerTree (nextDepth l) m (toListDigit l sf a))

toListDigit :: RuntimeDepth l -> Digit l v a -> [ a ] -> [ a ]
toListDigit !l (One a) next = toListTree l a next
toListDigit !l (Two a b) next = toListTree l a (toListTree l b next)
toListDigit !l (Three a b c) next = toListTree l a (toListTree l b (toListTree l c next))
toListDigit !l (Four a b c d) next = toListTree l a (toListTree l b (toListTree l c (toListTree l d next)))

toListTree :: RuntimeDepth l -> Tree l v a -> [ a ] -> [ a ]
toListTree (inspect -> RuntimeZ {}) (Tree t) next = t:next
toListTree (inspect -> RuntimeSucc l') (Tree (Node2 _ a b)) next =
  toListTree l' a (toListTree l' b next)
toListTree (inspect -> RuntimeSucc l') (Tree (Node3 _ a b c)) next =
  toListTree l' a (toListTree l' b (toListTree l' c next))
