{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module Language.Haskell.THC.Syntax.SourceFile where

import           Language.Haskell.THC.Syntax.Lexer

import           Control.Applicative
import           Control.Monad (forM_)
import           Control.Monad.State

import           Data.FingerTree.Pinky (FingerTree, Measured)
import qualified Data.FingerTree.Pinky as FingerTree
import           Data.Maybe (fromMaybe)
import           Data.Monoid (Last(..), Sum(..))
import           Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as T
import           Data.Word
import           Debug.Trace

import qualified System.Console.ANSI as ANSI

data PlacedText
  = PlacedText
  { ptOriginal :: !Text
  , ptNow      :: !Text
  , ptNewlines :: !Word
  } deriving Show

data PlacedTextPos
  = PlacedTextPos
  { ptpTextLength :: {-# UNPACK #-} !Word
  , ptpNewlines   :: {-# UNPACK #-} !Word
  } deriving Show

instance Measured PlacedTextPos PlacedText where
  measure = PlacedTextPos <$> fromIntegral . T.length . ptNow
                          <*> ptNewlines

instance Monoid PlacedTextPos where
  mempty = PlacedTextPos 0 0
  mappend = (<>)

instance Semigroup PlacedTextPos where
  a <> b = PlacedTextPos (ptpTextLength a + ptpTextLength b) (ptpNewlines a + ptpNewlines b)

data PlacedToken a
  = PlacedToken
  { ptLength   :: !Word
  , ptIsComment :: !Bool
  , ptBeginsBlock :: !Bool
  , ptTokenPhantomBefore :: [ a ]
  , ptToken    :: a
  , ptTokenPhantomAfter  :: [ a ]
  } deriving Show

data PlacedTokenPos a
  = PlacedTokenPos
  { ptpTokens :: {-# UNPACK #-} !Word
  , ptpComments :: {-# UNPACK #-} !Word
  , ptpPosition :: {-# UNPACK #-} !Word
  , ptpLastIsBlock :: Maybe Bool
  } deriving Show

instance Measured (PlacedTokenPos a) (PlacedToken a) where
  measure pt = PlacedTokenPos (fromIntegral (length (ptTokenPhantomBefore pt) + length (ptTokenPhantomAfter pt)) + if ptIsComment pt then 0 else 1)
                              (if ptIsComment pt then 1 else 0) (ptLength pt)
                              (if ptIsComment pt then Nothing else Just (ptBeginsBlock pt))

instance Monoid (PlacedTokenPos a) where
  mempty = PlacedTokenPos 0 0 0 Nothing
  mappend = (<>)

instance Semigroup (PlacedTokenPos a) where
  a <> b = PlacedTokenPos (ptpTokens a + ptpTokens b)
                          (ptpComments a + ptpComments b)
                          (ptpPosition a + ptpPosition b)
                          (ptpLastIsBlock b <|> ptpLastIsBlock a)

data SourceFile a
  = SourceFile
  { sourceFileIsComment, sourceFileDoesBeginBlock :: a -> Bool
  , sourceFileSrc    :: FingerTree PlacedTextPos PlacedText
  , sourceFileTokens :: FingerTree (PlacedTokenPos a) (PlacedToken a) -- Tokens
  }

data SourceRange = SourceRange { srStart, srEnd :: !Word }
  deriving Show

readSourceText :: Text -> SourceFile (ThcCommented ThcLexeme)
readSourceText src = do
  let isComment ThcComment {} = True
      isComment ThcSpecialComment {} = True
      isComment (ThcCode ThcLexemeWhitespace) = True
      isComment (ThcCode ThcLexemeIndent {}) = True
      isComment _ = False

      beginsBlock (ThcCode (ThcLexemeSimple ThcLexemeWhere)) = True
      beginsBlock (ThcCode (ThcLexemeSimple ThcLexemeOf)) = True
      beginsBlock (ThcCode (ThcLexemeSimple ThcLexemeLet)) = True
      beginsBlock (ThcCode (ThcLexemeSimple ThcLexemeIf)) = True
      beginsBlock (ThcCode (ThcLexemeSimple ThcLexemeDo)) = True
      beginsBlock _ = False

      source = FingerTree.fromList [ PlacedText src src (countNewlines src) ]
      -- Now, lex the source
      mkTokens !curLength lexSt t =
        case T.uncons t of
          Nothing ->
            case finalToken lexSt of
              (Nothing, _) -> []
              (Just t, _) -> [ PlacedToken curLength (isComment t) (beginsBlock t) [] t [] ]
          Just (c, t') ->
            case lexHaskell lexSt c of
              ( Nothing, lexSt'  ) -> mkTokens (curLength + 1) lexSt' t'
              ( Just tok, lexSt' ) -> PlacedToken curLength (isComment tok) (beginsBlock tok) [] tok []:mkTokens 1 lexSt' t'

      tokenTree = FingerTree.fromList (mkTokens 0 (ThcLexStateLexing T.empty lexer) src)

    in SourceFile isComment beginsBlock source (doIndent source tokenTree)

doIndent source toks =
  let (toks', (stk, _)) = runState (FingerTree.traverseWithPos calcIndent toks) ([], Nothing)
  in case FingerTree.viewr toks' of
       FingerTree.EmptyR -> error "doIndent: no tokens"
       toks'' FingerTree.:> lastTok
           | null stk || stk == [0] || all (/= 0) stk ->
               let lastBlock = if fromMaybe False (ptpLastIsBlock (FingerTree.measure toks'))
                               then [ ThcCode (ThcLexemeSimple ThcLexemeOpenIndent)
                                    , ThcCode (ThcLexemeSimple ThcLexemeCloseIndent) ]
                               else []
               in toks'' FingerTree.|> lastTok { ptTokenPhantomAfter = lastBlock ++ (ThcCode (ThcLexemeSimple ThcLexemeCloseIndent) <$ stk) }
           | otherwise -> error ("no closing indent: " ++ show stk)
  where
    getIndentStack = fmap fst get
    putIndentStack s = do
      (_, n) <- get
      put (s, n)

    setIndent n = do
      (s, _) <- get
      put (s, n)
    getIndent = fmap snd get

    calcIndent PlacedTokenPos { ptpLastIsBlock = Just True } tok@(PlacedToken { ptIsComment = True }) = pure tok

    calcIndent ptp tok@(PlacedToken { ptToken = ThcCode (ThcLexemeIndent n) }) = do
      setIndent (Just n)
      pure tok

    calcIndent _ tok@(PlacedToken { ptToken = ThcCode (ThcLexemeSimple ThcLexemeCloseIndent) }) = do
      stk <- getIndentStack
      case stk of
        0:ms -> do
          putIndentStack ms
          pure tok
        _ -> pure tok -- Error

    calcIndent _ tok@(PlacedToken { ptToken = ThcCode (ThcLexemeSimple ThcLexemeOpenIndent) }) = do
      stk <- getIndentStack
      putIndentStack (0:stk)
      pure tok

    calcIndent PlacedTokenPos { ptpLastIsBlock = Just True, ptpPosition = p } tok = do
      let (line, column) = resolveLineCol source p
      stk <- getIndentStack
      case stk of
        m:ms | column > m -> do
                 putIndentStack (column:stk)
                 pure tok { ptTokenPhantomBefore = [ ThcCode (ThcLexemeSimple ThcLexemeOpenIndent) ] }
        [] -> do
          putIndentStack (column:stk)
          pure tok { ptTokenPhantomBefore = [ ThcCode (ThcLexemeSimple ThcLexemeOpenIndent) ] }
        _ -> pure tok { ptTokenPhantomBefore = [ ThcCode (ThcLexemeSimple ThcLexemeOpenIndent)
                                               , ThcCode (ThcLexemeSimple ThcLexemeCloseIndent) ] }

    calcIndent _ tok = checkIndent tok

    checkIndent tok = do
      n <- getIndent
      case n of
        Nothing -> pure tok
        Just n -> do
             setIndent Nothing
             stk <- getIndentStack
             case stk of
               m:ms -> do let (closes, rest) = span (>n) stk
                              last = case rest of
                                       m':_ | m' == n -> [ ThcCode (ThcLexemeSimple ThcLexemeSemicolon) ]
                                       _ -> []
                              tok' = tok { ptTokenPhantomBefore = (ThcCode (ThcLexemeSimple ThcLexemeCloseIndent) <$ closes) ++ last }

                          putIndentStack rest
                          pure tok'
               _ -> pure tok

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
tokenHighlighter (ThcCode (ThcLexemeSimple ThcLexemeHasType)) = (ANSI.Vivid, ANSI.Green)
tokenHighlighter _ = (ANSI.Dull, ANSI.White)

highlight :: (tok -> (cls, Text)) -> (tok -> cls) -> SourceFile tok -> [ HighlightedText cls ]
highlight mkPhantom hiliter = go <$> sourceFileSrc <*> sourceFileTokens
  where
    go text toks =
      case FingerTree.viewl toks of
        FingerTree.EmptyL -> []
        PlacedToken l _ _ phBefore tok phAfter FingerTree.:< toks' ->
          case splitText l text of
            Nothing -> []
            Just (thisTok, text') ->
              let before x = foldr (\tok toks -> let (cls, txt) = mkPhantom tok
                                                 in HighlightedText cls txt:toks) x phBefore
                  after x = foldr (\tok toks -> let (cls, txt) = mkPhantom tok
                                                in HighlightedText cls txt:toks) x phAfter
              in before (HighlightedText (hiliter tok) thisTok:after (go text' toks'))

    splitText l t =
      case FingerTree.viewl t of
        FingerTree.EmptyL -> Nothing
        PlacedText old chk _ FingerTree.:< t' ->
          let (thisTok, chk') = T.splitAt (fromIntegral l) chk
          in Just (thisTok, if T.null chk' then t' else PlacedText old chk' (countNewlines chk') FingerTree.<| t')

showHighlighted :: SourceFile (ThcCommented ThcLexeme) -> IO ()
showHighlighted src = do
  let highlighted = highlight mkPhantom tokenHighlighter src
      mkPhantom (ThcCode (ThcLexemeSimple ThcLexemeOpenIndent)) = ((ANSI.Dull, ANSI.Magenta), T.singleton '{')
      mkPhantom (ThcCode (ThcLexemeSimple ThcLexemeCloseIndent)) = ((ANSI.Dull, ANSI.Magenta), T.singleton '}')
      mkPhantom (ThcCode (ThcLexemeSimple ThcLexemeSemicolon)) = ((ANSI.Dull, ANSI.Magenta), T.singleton ';')
      mkPhantom _ = ((ANSI.Dull, ANSI.Magenta), T.singleton '?')
  forM_ highlighted $ \(HighlightedText (i, c) t) -> do
    ANSI.setSGR [ ANSI.SetColor ANSI.Foreground i c ]
    T.putStr t
  ANSI.setSGR [ ANSI.SetColor ANSI.Foreground ANSI.Dull ANSI.White ]
  putStrLn ("Got " ++ show (length highlighted) ++ " tokens")

showHighlightedFile :: FilePath -> IO ()
showHighlightedFile fp = readSourceFile fp >>= showHighlighted

-- -- The third parameter is how we want to 'mark' new tokens, and the fourth function is how to mark old tokens
-- makeChange :: SourceRange -> Text -> a -> (a -> b) -> SourceFile a -> (Set b, SourceFile a)
-- makeChange = undefined

countNewlines :: Text -> Word
countNewlines = T.foldr (\c -> if c `elem` "\r\n\f" then succ else id) 0

resolveLineCol :: FingerTree PlacedTextPos PlacedText -> Word -> (Word, Word)
resolveLineCol src wh =
  let (l, r) = FingerTree.split ((>= wh) . ptpTextLength) src
  in case FingerTree.viewl r of
       PlacedText { ptNow = now } FingerTree.:< _ ->
         let l'Measure = FingerTree.measure l
             nowIndex = wh - ptpTextLength l'Measure
             upTilHere = T.take (fromIntegral nowIndex) now

             lastLine = T.dropWhileEnd (`notElem` "\r\n\f") upTilHere
         in (ptpNewlines l'Measure + countNewlines lastLine, fromIntegral (T.length upTilHere - T.length lastLine))
       FingerTree.EmptyL -> (0, 0)
