module Main where

import           Text.CYK.Parser

import           Data.Char
import qualified Data.Text as T
import qualified Data.Text.IO as T

import           System.Environment

import           Control.Parallel.Strategies

main :: IO ()
main = do
  [fn] <- getArgs
  f <- T.readFile fn
  let f' = T.takeWhile (not . isSpace) (T.dropWhile isSpace f)
  putStrLn (show (getParseResult simpleRuleParserLR (parse 200 simpleRuleParserLR f')))
