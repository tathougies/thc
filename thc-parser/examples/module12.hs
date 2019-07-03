module Thc.Parse.Test where

infixl 9 +, /, *

a, b, c :: Test (a, b) => Hello a b

data Test = Test1 | Test2 Int Test !Int | Test3 { a, b :: Word, c :: Test, d :: !Strict }
  deriving (Show, Eq, Ord Test2)

newtype Blah = Blah Int deriving Show
newtype Blah = Blah Int
newtype Show a => Blah a = Blah a
newtype Blah = Blah { aField :: Int }
newtype Blah = Blah { aField2 :: Int } deriving Eq

type Test a = Blah a
