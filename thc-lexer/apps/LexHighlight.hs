module Main where

import Language.Haskell.THC.Syntax.SourceFile

import System.Environment

main :: IO ()
main = do
  [ fp ] <- getArgs
  showHighlightedFile fp
