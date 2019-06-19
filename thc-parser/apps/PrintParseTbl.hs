{-# LANGUAGE TypeApplications #-}

module Main where

import Language.Haskell.THC.Syntax.Parser
import Text.CYK.Parser

main :: IO ()
main = do
  showRules (show . id @ThcLexemeCategory . toEnum . fromIntegral) hsModParser

  putStrLn ("Final rule is " ++ show (parserFinal hsModParser))
