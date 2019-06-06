{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}

module Language.Haskell.THC.Syntax.Lexer where

import           Control.Monad.Trans

import           Data.FingerTree (FingerTree)
import qualified Data.FingerTree as FingerTree
import           Data.Maybe (maybe)
import           Data.Monoid
import           Data.String
import           Data.Text (Text)
import qualified Data.Text as T

import           Streaming.Prelude (Stream, Of(..))
import qualified Streaming.Prelude as Stream

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
    = ThcWhitespace Bool {- At beginning of line -}
    | ThcComment
    | ThcSpecialComment
    | ThcCode a
    | ThcLineIndent !Int
      deriving Show

data ThcLexeme
    = ThcLexemeModule
    | ThcLexemeLet
    | ThcLexemeWhere
    | ThcLexemeIf
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
    | ThcLexemeOf
    | ThcLexemeDo

    | ThcLexemeOpenParen
    | ThcLexemeCloseParen
    | ThcLexemeOpenBracket
    | ThcLexemeCloseBracket
    | ThcLexemeBar

    | ThcLexemeOpenIndent
    | ThcLexemeCloseIndent

    | ThcLexemeIdentifier ThcIdentifier
    | ThcLexemeConstructor ThcIdentifier
    | ThcLexemeOperator ThcIdentifier

    | ThcLexemeContext
    | ThcLexemeArrow

    | ThcLexemeRational Rational
    | ThcLexemeText     Text
    | ThcLexemeChar     Char

    | ThcLexemeCommentStart
    | ThcLexemeMLCommentStart

      deriving Show

newtype ThcIndentStack = ThcIndentStack [Int]
    deriving Show

data LexOneBranch a = LexOneBranch Char (Maybe (Lexer a))

instance FingerTree.Measured (Last Char) (LexOneBranch a) where
    measure (LexOneBranch a _) = Last (Just a)

newtype LexBranch a
    = LexBranch (FingerTree (Last Char) (LexOneBranch a))

data Lexer a
    = Lexer (Maybe (Text -> a)) (LexBranch a)

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
lexer = "case"     $=> ThcLexemeCase
    ||| "module"   $=> ThcLexemeModule
    ||| "where"    $=> ThcLexemeWhere
    ||| "let"      $=> ThcLexemeLet
    ||| "if"       $=> ThcLexemeIf
    ||| "then"     $=> ThcLexemeThen
    ||| "else"     $=> ThcLexemeElse
    ||| "data"     $=> ThcLexemeData
    ||| "newtype"  $=> ThcLexemeNewtype
    ||| "deriving" $=> ThcLexemeDeriving
    ||| "\\"       $=> ThcLexemeLambda
    ||| "import"   $=> ThcLexemeImport
    ||| "of"       $=> ThcLexemeOf
    ||| "do"       $=> ThcLexemeDo
    ||| "--"       $=> ThcLexemeCommentStart
    ||| "{-"       $=> ThcLexemeMLCommentStart
    ||| "("        $=> ThcLexemeOpenParen
    ||| ")"        $=> ThcLexemeCloseParen
    ||| "|"        $=> ThcLexemeBar
    ||| "{"        $=> ThcLexemeOpenIndent
    ||| "}"        $=> ThcLexemeCloseIndent
    ||| "["        $=> ThcLexemeOpenBracket
    ||| "]"        $=> ThcLexemeCloseBracket
    ||| "-"        $=> ThcLexemeMinus
    ||| "->"       $=> ThcLexemeArrow
    ||| "=>"       $=> ThcLexemeContext
    ||| "="        $=> ThcLexemeEqual
    ||| "::"       $=> ThcLexemeHasType

    ||| ("(" <> operator <> ")") $=\> makeOperatorIdentifier
    ||| (backtick <> name <> backtick) $=\> makeIdentifierOperator
    ||| name $=\> (ThcLexemeIdentifier . makeIdentifier ThcName)
    ||| operator   $=\> (ThcLexemeOperator . ThcIdentifier [] . ThcSymbol)

($=\>) :: LexerBuilder -> (Text -> b) -> Lexer b
LexerBuilder mk $=\> go = mk (Lexer (Just go) (LexBranch mempty))

($=>) :: LexerBuilder -> b -> Lexer b
l $=> b = l $=\> const b

(|||) :: Lexer a -> Lexer a -> Lexer a
Lexer Nothing a ||| Lexer r b = Lexer r (combineBranch a b)
Lexer r a ||| Lexer _ b = Lexer r (combineBranch a b)

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

backtick :: LexerBuilder
backtick = only '`'

prime :: LexerBuilder
prime = only '\''

dot :: LexerBuilder
dot = only '.'

operator :: LexerBuilder
operator = oneOrMore symbol

anyOf :: String -> LexerBuilder
anyOf [] = LexerBuilder (\_ -> Lexer Nothing (LexBranch mempty))
anyOf (x:xs) = foldr ($||) (only x) (map only xs)

symbol :: LexerBuilder
symbol = anyOf "!#$%&*+./<=>?@\\^|-~"

name :: LexerBuilder
name = zeroOrMore moduleNamespace <> varsym

varsym :: LexerBuilder
varsym = small <> symOrConRest

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

makeIdentifierOperator, makeOperatorIdentifier :: Text -> ThcLexeme a
makeIdentifierOperator op =
    ThcLexemeOperator (makeIdentifier ThcName (T.tail (T.init op)))
makeOperatorIdentifier op =
    ThcLexemeIdentifier (makeIdentifier ThcSymbol (T.tail (T.init op)))

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

data ThcLexState
    = ThcLexStateStart
    | ThcLexStateMLComment !Int {- Comment level -}
    | ThcLexStateBeginningOfLine !Int {- Whitespace level -}
    | ThcLexStateComment {- Line comment -}
    | ThcLexStateLexing Text (Lexer ThcLexeme)
    | ThcLexStateWhitespace
    | ThcLexStateError
      deriving Show

data ThcLexing a
    = ThcLexing ThcLexState ThcLexemeIf ((ThcLexState, Char) -> a)

-- Partial equality of lexing states (TODO, true equality)
isCertainlySameLexState :: ThcLexState -> ThcLexState -> Bool
isCertainlySameLexState ThcLexStateStart ThcLexStateStart = True
isCertainlySameLexState (ThcLexStateMLComment a) (THCLexStateMLComment b) =
    a == b
isCertainlySameLexState (ThcLexStateBeginningOfLine a) (ThcLexStateBeginningOfLine b) =
    a == b
isCertainlySameLexState ThcLexStateComment ThcLexStateComment = True
isCertainlySameLexState ThcLexStateNone ThcLexStateNone = True
isCertainlySameLexState (ThcLexStateLexing {}) (ThcLexStateLexing {}) = False

lexHaskell :: ThcLexState -> Char -> (Maybe (ThcCommented ThcLexeme), ThcLexState)
lexHaskell ThcLexStateStart c = lexHaskell (ThcLexStateLexing T.empty lexer) c
lexHaskell ThcLexStateComment c
    | c `elem` "\r\n\f" = (Nothing, ThcLexStateBeginningOfLine 0)
lexHaskell (ThcLexStateBeginningOfLine indent) '\t' = (Nothing, ThcLexStateBeginningOfLine (((indent + 7) / 8) * 8))
lexHaskell (ThcLexStateBeginningOfLine indent) ' ' = (Nothing, ThcLexStateBeginningOfLine (indent + 1))
lexHaskell (ThcLexStateBeginningOfLine indent) c = ( Just (ThcLineIndent indent), ThcLexStateLexing (T.singleton c) (advanceLexer lexer c) )
lexHaskell (ThcLexStateLexing r (Lexer fn (LexBranch br))) c
    | FingerTree.null br = ( fn <*> pure r, ThcLexStateError )
lexHaskell (ThcLexStateLexing r (Lexer fn br)) c =
    case lookupBranch br c of
      Nothing -> case fn <*> pure r of
                   Nothing | isSpace c -> ( Nothing, ThcLexStateWhitespace )
                           | otherwise -> ( Nothing, ThcLexStateError ) -- A printable character causes a lexing error
                   Just ThcLexemeCommentStart -> ( Nothing, ThcLexStateComment )
                   Just ThcLexemeMLCommentStart -> ( Nothing, ThcLexStateMLComment 1 )
                   Just t  -> ( Just t, ThcLexStateLexing (advanceLexer lexer c) )
      Just l' -> ( Nothing, ThcLexStateLexing (T.snoc r c) l' )
lexHaskell ThcLexStateWhitespace c
    | isSpace c = (Nothing, ThcLexStateWhitespace)
    | otherwise = (Nothing, ThcLexStateLexing
