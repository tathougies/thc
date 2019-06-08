{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module Language.Haskell.THC.Syntax.SourceFile where

import           Language.Haskell.THC.Syntax.Lexer

import           Control.Monad (forM_)

import           Data.FingerTree (FingerTree, Measured)
import qualified Data.FingerTree as FingerTree
import           Data.Monoid (Last(..), Sum(..))
import           Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as T
import           Data.Word

import qualified System.Console.ANSI as ANSI

data PlacedText
  = PlacedText
  { ptOriginal :: !Text
  , ptNow      :: !Text
  } deriving Show

instance Measured (Sum Word) PlacedText where
  measure = Sum . fromIntegral . T.length . ptNow

data PlacedToken a
  = PlacedToken
  { ptLength   :: !Word
  , ptToken    :: a
  } deriving Show

instance Measured (Sum Word) (PlacedToken a) where
  measure = Sum . ptLength

data SourceFile a
  = SourceFile
  { sourceFileSrc    :: FingerTree (Sum Word) PlacedText
  , sourceFileTokens :: FingerTree (Sum Word) (PlacedToken a) -- Tokens
  } deriving Show

data SourceRange = SourceRange { srStart, srEnd :: !Word }
  deriving Show

readSourceText :: Text -> SourceFile (ThcCommented ThcLexeme)
readSourceText src = do
  let source = FingerTree.fromList [ PlacedText src src ]
      -- Now, lex the source
      mkTokens !curLength lexSt t =
        case T.uncons t of
          Nothing ->
            case finalToken lexSt of
              (Nothing, _) -> []
              (Just t, _) -> [ PlacedToken curLength t ]
          Just (c, t') ->
            case lexHaskell lexSt c of
              ( Nothing, lexSt'  ) -> mkTokens (curLength + 1) lexSt' t'
              ( Just tok, lexSt' ) -> PlacedToken curLength  tok:mkTokens 1 lexSt' t'

      tokenTree = FingerTree.fromList (mkTokens 0 (ThcLexStateLexing T.empty lexer) src)

    in SourceFile source tokenTree

readSourceFile :: FilePath -> IO (SourceFile (ThcCommented ThcLexeme))
readSourceFile fp =
  readSourceText <$> T.readFile fp

data HighlightedText cls = HighlightedText cls Text
  deriving Show

tokenHighlighter :: ThcCommented ThcLexeme -> (ANSI.ColorIntensity, ANSI.Color)
tokenHighlighter ThcComment = (ANSI.Dull, ANSI.Red)
tokenHighlighter ThcSpecialComment = (ANSI.Dull, ANSI.Red)
tokenHighlighter (ThcLineIndent {}) = (ANSI.Dull, ANSI.Black)
tokenHighlighter (ThcCode c)
  | isKeywordToken c = (ANSI.Vivid, ANSI.Blue)
  | isConstructor c = (ANSI.Dull, ANSI.Green)
  | isLiteral c = (ANSI.Vivid, ANSI.Red)
tokenHighlighter (ThcCode (ThcLexemeIdentifier {})) = (ANSI.Vivid, ANSI.White)
tokenHighlighter (ThcCode (ThcLexemeOperator {})) = (ANSI.Dull, ANSI.Yellow)
tokenHighlighter _ = (ANSI.Dull, ANSI.White)

highlight :: (tok -> cls) -> SourceFile tok -> [ HighlightedText cls ]
highlight hiliter = go <$> sourceFileSrc <*> sourceFileTokens
  where
    go text toks =
      case FingerTree.viewl toks of
        FingerTree.EmptyL -> []
        PlacedToken l tok FingerTree.:< toks' ->
          case splitText l text of
            Nothing -> []
            Just (thisTok, text') ->
              HighlightedText (hiliter tok) thisTok:go text' toks'

    splitText l t =
      case FingerTree.viewl t of
        FingerTree.EmptyL -> Nothing
        PlacedText old chk FingerTree.:< t' ->
          let (thisTok, chk') = T.splitAt (fromIntegral l) chk
          in Just (thisTok, if T.null chk' then t' else PlacedText old chk' FingerTree.<| t')

showHighlighted :: SourceFile (ThcCommented ThcLexeme) -> IO ()
showHighlighted src = do
  let highlighted = highlight tokenHighlighter src
  forM_ highlighted $ \(HighlightedText (i, c) t) -> do
    ANSI.setSGR [ ANSI.SetColor ANSI.Foreground i c ]
    T.putStr t
  ANSI.setSGR [ ANSI.SetColor ANSI.Foreground ANSI.Dull ANSI.White ]

showHighlightedFile :: FilePath -> IO ()
showHighlightedFile fp = readSourceFile fp >>= showHighlighted

-- -- The third parameter is how we want to 'mark' new tokens, and the fourth function is how to mark old tokens
-- makeChange :: SourceRange -> Text -> a -> (a -> b) -> SourceFile a -> (Set b, SourceFile a)
-- makeChange = undefined
