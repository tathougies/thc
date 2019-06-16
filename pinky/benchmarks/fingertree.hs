module Main where

import Data.FingerTree
import Data.Monoid
import System.Environment

newtype SeqC a = SeqC a
  deriving Show

instance Measured (Sum Int) (SeqC a) where
  measure _ = Sum 1

makeSeq :: [a] -> FingerTree (Sum Int) (SeqC a)
makeSeq = fromList . map SeqC

main :: IO ()
main = do
  [n] <- getArgs
  let n' = read n
      xs = makeSeq [0..n']
  mapM_ (putStrLn . show) xs
