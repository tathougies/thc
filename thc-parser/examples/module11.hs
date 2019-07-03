module Thc.Parse.Test where

infixl 9 +, /, *

a, b, c :: Test (a, b) => Hello a b

data Test = Test1 | Test2 Int Test !Int | Test3 { a, b :: Word, c :: Test, d :: !Strict }
  deriving (Show, Eq, Ord Test2)
