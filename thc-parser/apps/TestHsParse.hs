module Main where

import Language.Haskell.THC.Syntax.Parser
import Language.Haskell.THC.Syntax.SourceFile

import Data.Foldable

import System.Environment

import Text.CYK.Parser

main :: IO ()
main = do
  [fp] <- getArgs
  fl <- readSourceFile fp

  let parsed = parse 50 hsModParser (ParsingSourceFile (sourceFileTokens fl))
      res = getParseResult hsModParser parsed

  putStrLn ("There were " ++ show (length res) ++ " parse(s)")
  forM_ res $ \res' ->
      putStrLn (show res')
