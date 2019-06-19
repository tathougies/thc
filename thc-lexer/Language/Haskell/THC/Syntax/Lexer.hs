{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveFunctor #-}

module Language.Haskell.THC.Syntax.Lexer where

import           Control.Arrow ( (&&&) )
import           Control.Monad.Trans

import           Data.Char (isSpace, isUpper, chr )
import           Data.FingerTree.Pinky (FingerTree)
import qualified Data.FingerTree.Pinky as FingerTree
import           Data.Maybe (maybe, catMaybes)
import           Data.Monoid
import           Data.String
import           Data.Text (Text)
import qualified Data.Text as T

import           Debug.Trace

newtype ThcModuleName
    = ThcModuleName Text
      deriving Show

data ThcName
    = ThcName !Text
    | ThcSymbol !Text
      deriving Show

data ThcIdentifier
    = ThcIdentifier [ ThcModuleName ] ThcName
      deriving Show

data ThcCommented a
    = ThcComment
    | ThcSpecialComment
    | ThcCode a
    | ThcLineIndent !Int
      deriving Show

data ThcLexemeC
    = ThcLexemeModule
    | ThcLexemeLet
    | ThcLexemeWhere
    | ThcLexemeIf
    | ThcLexemeIn
    | ThcLexemeThen
    | ThcLexemeElse
    | ThcLexemeData
    | ThcLexemeType
    | ThcLexemeNewtype
    | ThcLexemeDeriving
    | ThcLexemeLambda
    | ThcLexemeCase
    | ThcLexemeImport
    | ThcLexemeMinus
    | ThcLexemeEqual
    | ThcLexemeHasType
    | ThcLexemeComma
    | ThcLexemeOf
    | ThcLexemeDo
    | ThcLexemeForall
    | ThcLexemeInfixl
    | ThcLexemeInfixr
    | ThcLexemeInfix
    | ThcLexemeSemicolon

    | ThcLexemeOpenParen
    | ThcLexemeCloseParen
    | ThcLexemeOpenBracket
    | ThcLexemeCloseBracket
    | ThcLexemeBar

    | ThcLexemeOpenIndent
    | ThcLexemeCloseIndent

    | ThcLexemeContext
    | ThcLexemeArrow
      deriving (Show, Enum, Bounded)

data ThcLexeme
    = ThcLexemeSimple ThcLexemeC

    | ThcLexemeCommentStart
    | ThcLexemeMLCommentStart

    | ThcLexemeWhitespace
    | ThcLexemeIndent !Word

    | ThcLexemeIdentifier ThcIdentifier
    | ThcLexemeOperator ThcIdentifier

    | ThcLexemeRational Rational
    | ThcLexemeText     Text
    | ThcLexemeChar     Char

      deriving Show

data LexOneBranch a = LexOneBranch Char (Maybe (Lexer a))

instance FingerTree.Measured (Last Char) (LexOneBranch a) where
    measure (LexOneBranch a _) = Last (Just a)

newtype LexBranch a
    = LexBranch (FingerTree (Last Char) (LexOneBranch a))

data Lexer a
    = Lexer (Maybe (Text -> a)) (LexBranch a)

isKeywordToken, isConstructor, isLiteral, isWhitespace :: ThcLexeme -> Bool
isWhitespace (ThcLexemeIndent {}) = True
isWhitespace ThcLexemeWhitespace = True
isWhitespace ThcLexemeCommentStart = True
isWhitespace ThcLexemeMLCommentStart = True
isWhitespace _ = False

isKeywordToken (ThcLexemeSimple ThcLexemeModule) = True
isKeywordToken (ThcLexemeSimple ThcLexemeLet) = True
isKeywordToken (ThcLexemeSimple ThcLexemeWhere) = True
isKeywordToken (ThcLexemeSimple ThcLexemeIf) = True
isKeywordToken (ThcLexemeSimple ThcLexemeIn) = True
isKeywordToken (ThcLexemeSimple ThcLexemeThen) = True
isKeywordToken (ThcLexemeSimple ThcLexemeElse) = True
isKeywordToken (ThcLexemeSimple ThcLexemeData) = True
isKeywordToken (ThcLexemeSimple ThcLexemeType) = True
isKeywordToken (ThcLexemeSimple ThcLexemeNewtype) = True
isKeywordToken (ThcLexemeSimple ThcLexemeDeriving) = True
isKeywordToken (ThcLexemeSimple ThcLexemeCase) = True
isKeywordToken (ThcLexemeSimple ThcLexemeImport) = True
isKeywordToken (ThcLexemeSimple ThcLexemeDo) = True
isKeywordToken (ThcLexemeSimple ThcLexemeForall) = True
isKeywordToken (ThcLexemeSimple ThcLexemeOf) = True
isKeywordToken (ThcLexemeSimple ThcLexemeInfixl) = True
isKeywordToken (ThcLexemeSimple ThcLexemeInfixr) = True
isKeywordToken (ThcLexemeSimple ThcLexemeInfix) = True
isKeywordToken _ = False

isConstructor (ThcLexemeOperator i) = isConstructorIdentifier i
isConstructor (ThcLexemeIdentifier i) = isConstructorIdentifier i
isConstructor _ = False

isLiteral (ThcLexemeRational {}) = True
isLiteral (ThcLexemeText {}) = True
isLiteral (ThcLexemeChar {}) = True
isLiteral _ = False

isConstructorIdentifier :: ThcIdentifier -> Bool
isConstructorIdentifier (ThcIdentifier _ (ThcSymbol sym)) =
  T.isPrefixOf ":" sym
isConstructorIdentifier (ThcIdentifier _ (ThcName n)) =
  case T.uncons n of
    Nothing -> False
    Just (c, _) -> isUpper c

-- TODO LexBranch Monoid

only :: Char -> LexerBuilder
only c = LexerBuilder (\l -> Lexer Nothing (LexBranch (FingerTree.fromList [ LexOneBranch c (Just l), LexOneBranch (succ c) Nothing ])))

range :: Char -> Char -> LexerBuilder
range c c' = LexerBuilder (\l -> Lexer Nothing (LexBranch (FingerTree.fromList [ LexOneBranch c (Just l), LexOneBranch (succ c') Nothing ])))

newtype LexerBuilder where
    LexerBuilder :: (forall a. Lexer a -> Lexer a) -> LexerBuilder

instance IsString LexerBuilder where
    fromString = foldMap only

instance Monoid LexerBuilder where
    mempty = LexerBuilder id
    mappend = (<>)

instance Semigroup LexerBuilder where
    LexerBuilder a <> LexerBuilder b = LexerBuilder (a . b)

lexer :: Lexer ThcLexeme
lexer = "case"     $=> ThcLexemeSimple ThcLexemeCase
    ||| "module"   $=> ThcLexemeSimple ThcLexemeModule
    ||| "where"    $=> ThcLexemeSimple ThcLexemeWhere
    ||| "let"      $=> ThcLexemeSimple ThcLexemeLet
    ||| "if"       $=> ThcLexemeSimple ThcLexemeIf
    ||| "then"     $=> ThcLexemeSimple ThcLexemeThen
    ||| "else"     $=> ThcLexemeSimple ThcLexemeElse
    ||| "data"     $=> ThcLexemeSimple ThcLexemeData
    ||| "newtype"  $=> ThcLexemeSimple ThcLexemeNewtype
    ||| "type"     $=> ThcLexemeSimple ThcLexemeType
    ||| "deriving" $=> ThcLexemeSimple ThcLexemeDeriving
    ||| "\\"       $=> ThcLexemeSimple ThcLexemeLambda
    ||| "import"   $=> ThcLexemeSimple ThcLexemeImport
    ||| "in"       $=> ThcLexemeSimple ThcLexemeIn
    ||| "of"       $=> ThcLexemeSimple ThcLexemeOf
    ||| "do"       $=> ThcLexemeSimple ThcLexemeDo
    ||| "forall"   $=> ThcLexemeSimple ThcLexemeForall
    ||| "infixl"   $=> ThcLexemeSimple ThcLexemeInfixl
    ||| "infixr"   $=> ThcLexemeSimple ThcLexemeInfixr
    ||| "infix"    $=> ThcLexemeSimple ThcLexemeInfix
    ||| "--"       $=> ThcLexemeCommentStart
    ||| "{-"       $=> ThcLexemeMLCommentStart
    ||| "("        $=> ThcLexemeSimple ThcLexemeOpenParen
    ||| ")"        $=> ThcLexemeSimple ThcLexemeCloseParen
    ||| "|"        $=> ThcLexemeSimple ThcLexemeBar
    ||| "{"        $=> ThcLexemeSimple ThcLexemeOpenIndent
    ||| "}"        $=> ThcLexemeSimple ThcLexemeCloseIndent
    ||| "["        $=> ThcLexemeSimple ThcLexemeOpenBracket
    ||| "]"        $=> ThcLexemeSimple ThcLexemeCloseBracket
    ||| "-"        $=> ThcLexemeSimple ThcLexemeMinus
    ||| "->"       $=> ThcLexemeSimple ThcLexemeArrow
    ||| "=>"       $=> ThcLexemeSimple ThcLexemeContext
    ||| "="        $=> ThcLexemeSimple ThcLexemeEqual
    ||| "::"       $=> ThcLexemeSimple ThcLexemeHasType
    ||| ";"        $=> ThcLexemeSimple ThcLexemeSemicolon
    ||| ","        $=> ThcLexemeSimple ThcLexemeComma
    ||| space      $=> ThcLexemeWhitespace
    ||| (nl <> space) $=\> makeIndentation

    -- Sections have to be handled by the parser

    ||| (backtick <> name <> backtick) $=\> makeIdentifierOperator
    ||| name $=\> (ThcLexemeIdentifier . makeIdentifier ThcName)
    ||| operator   $=\> ThcLexemeOperator . makeIdentifier ThcSymbol

    ||| (dquote <> string <> dquote) $=\> ThcLexemeText -- TODO transform
    ||| (squote <> char <> squote) $=\> ThcLexemeChar . makeCharacter

    ||| integer $=\> ThcLexemeRational . makeInteger

($=\>) :: LexerBuilder -> (Text -> b) -> Lexer b
LexerBuilder mk $=\> go = mk (Lexer (Just go) (LexBranch mempty))

($=>) :: LexerBuilder -> b -> Lexer b
l $=> b = l $=\> const b

(|||) :: Lexer a -> Lexer a -> Lexer a
Lexer Nothing a ||| Lexer r b = Lexer r (combineBranch a b)
Lexer r a ||| Lexer _ b = Lexer r (combineBranch a b)

makeIndentation :: Text -> ThcLexeme
makeIndentation = ThcLexemeIndent . T.foldl (\i c -> if c == '\t'
                                                     then ((i + 8) `div` 8) * 8
                                                     else if c `elem` ("\r\n\f" :: [Char])
                                                          then 0 else i + 1) 0

combineBranch :: LexBranch a -> LexBranch a -> LexBranch a
combineBranch (LexBranch a') (LexBranch b') =
    LexBranch (merge Nothing Nothing a' b')
    where
      merge la lb a b =
        case (FingerTree.viewl a, FingerTree.viewl b) of
          (FingerTree.EmptyL, _) -> b
          (_, FingerTree.EmptyL) -> a
          ( LexOneBranch ac an FingerTree.:< ar,
            LexOneBranch bc bn FingerTree.:< br )
            | ac < bc -> case an of
                           Nothing -> LexOneBranch ac lb FingerTree.<| merge an lb ar b
                           Just an' -> case lb of
                                         Nothing -> LexOneBranch ac an FingerTree.<| merge an lb ar b
                                         Just lb' -> LexOneBranch ac (Just (an' ||| lb')) FingerTree.<| merge an lb ar b
            | bc < ac -> case bn of
                           Nothing  -> LexOneBranch bc la FingerTree.<| merge la bn a br
                           Just bn' -> case la of
                                         Nothing -> LexOneBranch bc bn FingerTree.<| merge la bn a br
                                         Just la' -> LexOneBranch bc (Just (la' ||| bn')) FingerTree.<| merge la bn a br
            | ac == bc -> let n = maybe bn (\an' -> Just (maybe an' (an' |||) bn) ) an
                          in LexOneBranch ac n FingerTree.<| merge an bn ar br -- Bias towards a

($||) :: LexerBuilder -> LexerBuilder -> LexerBuilder
LexerBuilder a $|| LexerBuilder b = LexerBuilder (\l -> a l ||| b l)

infixl 4 $=>, $=\>
infixl 3 |||, $||

-- Lexers

nl :: LexerBuilder
nl = anyOf "\r\n\f"

space :: LexerBuilder
space = zeroOrMore oneSpace

oneSpace :: LexerBuilder
oneSpace = anyOf " \xa0\x1680\x180E\x3000\xFEFF\x202F\x205F" $|| range '\x2000' '\x200B'

backtick :: LexerBuilder
backtick = only '`'

prime, squote :: LexerBuilder
prime = only '\''
squote = prime

dquote :: LexerBuilder
dquote = only '"'

char :: LexerBuilder
char = graphic $|| oneSpace $|| escape False
  where
    graphic = small $|| large $|| symbol $|| digit $|| anyOf ":(),;[]`{}\""

string :: LexerBuilder
string = zeroOrMore (graphic $|| oneSpace $|| escape True)
  where graphic = small $|| large $|| symbol $|| digit $|| anyOf ":(),;[]`{}'"

escape :: Bool -> LexerBuilder
escape allowAmp = only '\\' <> (escapeChar $|| decEscape $|| hexEscape $|| octEscape $|| ( oneOrMore oneSpace <> only '\\'))
  where
    escapeCharBasic = anyOf "abfnrtv\"'\\" -- TODO ascii escapes
    escapeChar | allowAmp = escapeCharBasic $|| only '&'
               | otherwise = escapeCharBasic
    decEscape = oneOrMore decDigits
    hexEscape = anyOf "xX" <> oneOrMore hexDigits
    octEscape = anyOf "oO" <> oneOrMore octDigits

integer :: LexerBuilder
integer = oneOrMore decDigits
      $|| ("0o" $|| "0O") <> oneOrMore octDigits
      $|| ("0x" $|| "0X") <> oneOrMore hexDigits

decDigits, octDigits, hexDigits :: LexerBuilder
decDigits = range '0' '9'
hexDigits = range '0' '9' $|| range 'a' 'f' $|| range 'A' 'F'
octDigits = range '0' '7'

dot :: LexerBuilder
dot = only '.'

operator :: LexerBuilder
operator = zeroOrMore moduleNamespace <> oneOrMore (symbol $|| anyOf "\\:")

anyOf :: String -> LexerBuilder
anyOf [] = LexerBuilder (\_ -> Lexer Nothing (LexBranch mempty))
anyOf (x:xs) = foldr ($||) (only x) (map only xs)

symbol :: LexerBuilder
symbol = anyOf "!#$%&*+./<=>?@^|-~"

name :: LexerBuilder
name = zeroOrMore moduleNamespace <> varOrConSym

varOrConSym :: LexerBuilder
varOrConSym = (small $|| large) <> symOrConRest

symOrConRest :: LexerBuilder
symOrConRest = zeroOrMore (small $|| large $|| digit $|| prime)

small :: LexerBuilder
small = range 'a' 'z' $|| only '_' -- TODO other small

large :: LexerBuilder
large = range 'A' 'Z' -- TODO other large

digit :: LexerBuilder
digit = range '0' '9' -- TODo other digits?

moduleNamespace :: LexerBuilder
moduleNamespace = moduleName <> dot

moduleName :: LexerBuilder
moduleName = varcon

varcon :: LexerBuilder
varcon = large <> symOrConRest

oneOrMore :: LexerBuilder -> LexerBuilder
oneOrMore a = a <> zeroOrMore a
zeroOrMore :: LexerBuilder -> LexerBuilder
zeroOrMore (LexerBuilder b) =
    LexerBuilder (\l -> let x = l ||| b x
                        in x)

makeInteger :: Text -> Rational
makeInteger t | Just oct <- T.stripPrefix "0o" t = readValue' octDigit oct
              | Just oct <- T.stripPrefix "0O" t = readValue' octDigit oct
              | Just hex <- T.stripPrefix "0x" t = readValue' hexDigit hex
              | Just hex <- T.stripPrefix "0X" t = readValue' hexDigit hex
              | otherwise = readValue' decDigit t
  where readValue' f t = fromIntegral (readValue f t)

makeCharacter :: Text -> Char
makeCharacter t =
  let t' = T.init (T.tail t)
  in if T.head t == '\\'
     then parseEscape (T.tail t)
     else T.head t

parseEscape :: Text -> Char
parseEscape "a" = '\a'
parseEscape "b" = '\b'
parseEscape "f" = '\f'
parseEscape "n" = '\n'
parseEscape "r" = '\r'
parseEscape "t" = '\t'
parseEscape "v" = '\v'
parseEscape t =
  case T.head t of
    'o' -> parseChar octDigit (T.tail t)
    'O' -> parseChar octDigit (T.tail t)
    'x' -> parseChar hexDigit (T.tail t)
    'X' -> parseChar hexDigit (T.tail t)
    c   -> c

parseChar :: (Char -> Word) -> Text -> Char
parseChar mkD = chr . fromIntegral . readValue mkD

readValue :: (Char -> Word) -> Text -> Word
readValue mkD = fst . T.foldr addValue (0, 1)
  where
    addValue c (a, place) =
      (a + mkD c * place, place * 10)

hexDigit, octDigit, decDigit :: Char -> Word
octDigit '1' = 1
octDigit '2' = 2
octDigit '3' = 3
octDigit '4' = 4
octDigit '5' = 5
octDigit '6' = 6
octDigit '7' = 7
octDigit x = 0

decDigit '8' = 8
decDigit '9' = 9
decDigit c = octDigit c

hexDigit 'a' = 10
hexDigit 'A' = 10
hexDigit 'b' = 11
hexDigit 'B' = 11
hexDigit 'c' = 12
hexDigit 'C' = 12
hexDigit 'd' = 13
hexDigit 'D' = 13
hexDigit 'e' = 14
hexDigit 'E' = 14
hexDigit 'f' = 15
hexDigit 'F' = 15
hexDigit c = decDigit c


makeIdentifierOperator :: Text -> ThcLexeme
makeIdentifierOperator op =
    ThcLexemeOperator (makeIdentifier ThcName (T.tail (T.init op)))

makeIdentifier :: (Text -> ThcName) -> Text -> ThcIdentifier
makeIdentifier mk t =
    let comps = T.split (== '.') t
        mod = init comps
    in ThcIdentifier (map ThcModuleName mod) (mk (last comps))

tryParse :: Lexer a -> Text -> Maybe (a, Text)
tryParse = go mempty
    where
      go r (Lexer finish next) t =
          case T.uncons t of
            Nothing -> (,t) <$> (finish <*> pure r)
            Just (c, t') ->
                case lookupBranch next c of
                  Nothing -> (,t) <$> (finish <*> pure r)
                  Just nextLexer ->
                      go (T.snoc r c) nextLexer t'

lookupBranch :: LexBranch a -> Char -> Maybe (Lexer a)
lookupBranch (LexBranch ft) k =
    let (before, after) = FingerTree.split (\(Last c) -> maybe False (> k) c) ft
    in case FingerTree.viewr before of
         FingerTree.EmptyR -> Nothing
         _ FingerTree.:> LexOneBranch c j
             | c <= k -> j
             | otherwise -> Nothing

data ThcLexState a
    = ThcLexStateMLComment ThcMLCommentState !Int {- Comment level -}
    | ThcLexStateComment {- Line comment -}
    | ThcLexStateLexing Text a
    | ThcLexStateError ThcLexError
      deriving (Functor, Show)

data ThcMLCommentState
  = ThcMLCommentStart
  | ThcMLCommentOpenBrace
  | ThcMLCommentDash
  deriving (Show, Eq)

data ThcLexError
  = ThcLexErrorUnknownToken
  | ThcLexErrorUnterminatedComment
  deriving Show

data ThcLexing a
    = ThcLexing (ThcLexState (Lexer ThcLexeme)) ThcLexeme ((ThcLexState (Lexer ThcLexeme), Char) -> a)

-- Partial equality of lexing states (TODO, true equality)
isCertainlySameLexState :: ThcLexState (Lexer ThcLexeme) -> ThcLexState (Lexer ThcLexeme) -> Bool
isCertainlySameLexState (ThcLexStateMLComment as a) (ThcLexStateMLComment bs b) =
    as == bs && a == b
isCertainlySameLexState ThcLexStateComment ThcLexStateComment = True
isCertainlySameLexState (ThcLexStateLexing {}) (ThcLexStateLexing {}) = False

lexHaskell :: ThcLexState (Lexer ThcLexeme) -> Char -> (Maybe (ThcCommented ThcLexeme), ThcLexState (Lexer ThcLexeme))
lexHaskell ThcLexStateComment c
    | c `elem` [ '\r', '\n', '\f' ] = (Just ThcComment, ThcLexStateLexing (T.singleton c) (advanceLexer lexer c))
    | otherwise = ( Nothing, ThcLexStateComment )
lexHaskell (ThcLexStateMLComment ThcMLCommentOpenBrace n) '-' = (Nothing, ThcLexStateMLComment ThcMLCommentStart (n + 1))
lexHaskell (ThcLexStateMLComment ThcMLCommentDash n) '}' =
  if n == 1
  then (Just ThcComment, ThcLexStateLexing T.empty lexer)
  else (Nothing, ThcLexStateMLComment ThcMLCommentStart (n - 1))
lexHaskell (ThcLexStateMLComment ThcMLCommentStart n) '{' = (Nothing, ThcLexStateMLComment ThcMLCommentOpenBrace (n + 1))
lexHaskell (ThcLexStateMLComment ThcMLCommentStart n) '-' = (Nothing, ThcLexStateMLComment ThcMLCommentDash n)
lexHaskell (ThcLexStateMLComment _ n) _ = (Nothing, ThcLexStateMLComment ThcMLCommentStart n)
lexHaskell (ThcLexStateLexing r (Lexer fn br)) c =
    case lookupBranch br c of
      Nothing -> case fn <*> pure r of
                   Nothing -> ( Nothing, ThcLexStateError ThcLexErrorUnknownToken)
                   Just ThcLexemeCommentStart -> ( Nothing, ThcLexStateComment )
                   Just ThcLexemeMLCommentStart -> ( Nothing, ThcLexStateMLComment ThcMLCommentStart 1 )
                   Just t -> ( Just (ThcCode t)
                             , ThcLexStateLexing (T.singleton c) (advanceLexer lexer c) )
      Just l' -> ( Nothing, ThcLexStateLexing (T.snoc r c) l' )
lexHaskell (ThcLexStateError e) c = ( Nothing, ThcLexStateError e)

finalToken :: ThcLexState (Lexer ThcLexeme) -> ( Maybe (ThcCommented ThcLexeme), ThcLexState a )
finalToken ThcLexStateComment = ( Just ThcComment, ThcLexStateComment )
finalToken ThcLexStateMLComment {} = ( Nothing, ThcLexStateError ThcLexErrorUnterminatedComment )
finalToken (ThcLexStateLexing r (Lexer fn _)) = ( fmap ThcCode (fn <*> pure r), ThcLexStateComment )
finalToken (ThcLexStateError e) = ( Nothing, ThcLexStateError e)

advanceLexer :: Lexer a -> Char -> Lexer a
advanceLexer (Lexer _ branch) c =
  case lookupBranch branch c of
    Nothing -> Lexer Nothing (LexBranch FingerTree.empty)
    Just l  -> l

lexHaskellTest :: [ Char ] -> ([ ThcCommented ThcLexeme ], ThcLexState ())
lexHaskellTest s =
  let tokens = scanl (lexHaskell . snd) (Nothing, ThcLexStateLexing T.empty lexer) s
      finalState = snd (last tokens)
      (lastToken, finalState') = finalToken finalState
      tokens' = catMaybes (map fst tokens ++ [ lastToken ])
  in (tokens', finalState')

lexHaskellFile :: FilePath -> IO ([ ThcCommented ThcLexeme ], ThcLexState ())
lexHaskellFile fp = lexHaskellTest <$> readFile fp
