{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RecursiveDo #-}
module Language.Haskell.THC.Syntax.Parser where

import           Language.Haskell.THC.Syntax.Lexer
import           Language.Haskell.THC.Syntax.SourceFile
import           Language.Haskell.THC.Syntax.AST

import           Control.Applicative ((<|>))
import           Control.Monad

import qualified Data.FingerTree.Pinky as FingerTree
import           Data.Foldable (toList)

import           Text.CYK.Parser

data ParsingSourceFile
    = ParsingSourceFile (FingerTree.FingerTree (PlacedTokenPos (ThcCommented ThcLexeme)) (PlacedToken (ThcCommented ThcLexeme)))
    | BisectingToken [ ThcLexeme ]
    deriving Show

getAllFromToken :: PlacedToken (ThcCommented ThcLexeme) -> [ThcLexeme]
getAllFromToken pt =
    do let before = do
             ThcCode a <- ptTokenPhantomBefore pt
             pure a
           after = do
             ThcCode a <- ptTokenPhantomAfter pt
             pure a

       tok <- case ptToken pt of
                ThcCode a -> before ++ pure a ++ after
                _ -> before ++ after
       guard (not (isWhitespace tok))
       pure tok

instance Splittable ParsingSourceFile where
    type SplitItem ParsingSourceFile = ThcLexeme
    bisect (ParsingSourceFile sf) =
        let total = ptpTokens (FingerTree.measure sf)
            firstSize = total `div` 2

            (left, right) = FingerTree.split ((>=firstSize).ptpTokens) sf
        in if total == 0
           then SplitResultNull
           else if total == 1
                then case FingerTree.viewl sf of
                       FingerTree.EmptyL -> SplitResultNull
                       pt FingerTree.:< _ ->
                           case getAllFromToken pt of
                             [t] -> SplitResultOne t
                             _ -> SplitResultNull
                else let leftCount = ptpTokens (FingerTree.measure left)
                         rightCount = ptpTokens (FingerTree.measure right)
                     in  if leftCount == 0 || rightCount ==0
                         then bisect (BisectingToken (toList sf >>= getAllFromToken))
                         else SplitResultSplit leftCount (ParsingSourceFile left)
                                               rightCount (ParsingSourceFile right)

    bisect (BisectingToken []) = SplitResultNull
    bisect (BisectingToken [t]) = SplitResultOne t
    bisect (BisectingToken ts) =
        let total = fromIntegral (length ts)
            leftSize = total `div` 2

            (left, right) = splitAt (fromIntegral leftSize) ts
        in  SplitResultSplit leftSize (BisectingToken left) (total - leftSize) (BisectingToken right)

    getAll (ParsingSourceFile sf) =
        do pt <- toList sf
           getAllFromToken pt

data ThcLexemeCategory
    = ThcLexemeCategorySimple ThcLexemeC
    | ThcLexemeCategorySpace
    | ThcLexemeCategoryIdentifier
    | ThcLexemeCategoryConstructor
    | ThcLexemeCategoryOperator
    | ThcLexemeCategoryRational
    | ThcLexemeCategoryText
    | ThcLexemeCategoryChar
      deriving Show

instance Bounded ThcLexemeCategory where
    minBound = ThcLexemeCategorySimple minBound
    maxBound = ThcLexemeCategoryChar

instance Enum ThcLexemeCategory where
    fromEnum (ThcLexemeCategorySimple x) = fromEnum x
    fromEnum ThcLexemeCategorySpace = fromEnum (maxBound :: ThcLexemeC) + 1
    fromEnum ThcLexemeCategoryIdentifier = fromEnum (maxBound :: ThcLexemeC) + 2
    fromEnum ThcLexemeCategoryConstructor = fromEnum (maxBound :: ThcLexemeC) + 3
    fromEnum ThcLexemeCategoryOperator = fromEnum (maxBound :: ThcLexemeC) + 4
    fromEnum ThcLexemeCategoryRational = fromEnum (maxBound :: ThcLexemeC) + 5
    fromEnum ThcLexemeCategoryText = fromEnum (maxBound :: ThcLexemeC) + 6
    fromEnum ThcLexemeCategoryChar = fromEnum (maxBound :: ThcLexemeC) + 7

    toEnum x
        | x <= fromEnum (maxBound :: ThcLexemeC) = ThcLexemeCategorySimple (toEnum x)
        | otherwise =
            case x - fromEnum (maxBound :: ThcLexemeC) of
              1 -> ThcLexemeCategorySpace
              2 -> ThcLexemeCategoryIdentifier
              3 -> ThcLexemeCategoryConstructor
              4 -> ThcLexemeCategoryOperator
              5 -> ThcLexemeCategoryRational
              6 -> ThcLexemeCategoryText
              7 -> ThcLexemeCategoryChar
              _ -> error "toEnum{ThcLexemeCategory}: invalid value"

match x = terminal x (\_ -> ())

mkModuleName :: ThcIdentifier -> [ ThcModuleName ]
mkModuleName (ThcIdentifier mods (ThcName t)) = mods ++ [ ThcModuleName t ]
mkModuleName _ = error "mkModuleName"

hsLexemeCategory :: ThcLexeme -> ThcLexemeCategory
hsLexemeCategory (ThcLexemeSimple c) = ThcLexemeCategorySimple c
hsLexemeCategory ThcLexemeCommentStart = ThcLexemeCategorySpace
hsLexemeCategory ThcLexemeMLCommentStart = ThcLexemeCategorySpace
hsLexemeCategory ThcLexemeWhitespace = ThcLexemeCategorySpace
hsLexemeCategory (ThcLexemeIndent _) = ThcLexemeCategorySpace
hsLexemeCategory (ThcLexemeIdentifier i)
    | isConstructorIdentifier i = ThcLexemeCategoryConstructor
    | otherwise = ThcLexemeCategoryIdentifier
hsLexemeCategory (ThcLexemeRational _) = ThcLexemeCategoryRational
hsLexemeCategory (ThcLexemeText _) = ThcLexemeCategoryText
hsLexemeCategory (ThcLexemeChar _) = ThcLexemeCategoryChar

hsModParser :: Parser ThcLexeme ThcModule
hsModParser =
    compile hsLexemeCategory $ mdo
      consT <- buildRule (terminal ThcLexemeCategoryConstructor (\(ThcLexemeIdentifier id) -> id))
      idT <- buildRule (terminal ThcLexemeCategoryIdentifier (\(ThcLexemeIdentifier id) -> id))

      identifierT <- buildRule (rule idT <|> rule consT)

      let oParen = match (ThcLexemeCategorySimple ThcLexemeOpenParen)
          cParen = match (ThcLexemeCategorySimple ThcLexemeCloseParen)
          oBrace = match (ThcLexemeCategorySimple ThcLexemeOpenIndent)
          cBrace = match (ThcLexemeCategorySimple ThcLexemeCloseIndent)
          comma = match (ThcLexemeCategorySimple ThcLexemeComma)
          semicolon = match (ThcLexemeCategorySimple ThcLexemeSemicolon)

          moduleT = match (ThcLexemeCategorySimple ThcLexemeModule)
          whereT = match (ThcLexemeCategorySimple ThcLexemeWhere)
          importT = match (ThcLexemeCategorySimple ThcLexemeImport)

          parens a = oParen *> a <* cParen
          indented a = oBrace *> pure [] <* cBrace

          sepBy what item = mdo
            list <- buildRule (pure [] <|> (:) <$> item <*> (pure [] <|> (what *> rule list)))
            pure list

      namespaceP <- buildRule ((ThcModuleNamespaceModule <$ match (ThcLexemeCategorySimple ThcLexemeModule)) <|>
                               (ThcModuleNamespaceType <$ match (ThcLexemeCategorySimple ThcLexemeType)) <|>
                               pure ThcModuleNamespaceValue)

      consListSomeP <- buildRule (pure [] <|>
                                  (:) <$> rule identifierT <*> (pure [] <|> (comma *> rule consListSomeP)))

      consListP <-  buildRule (pure ThcNoConstructors <|>
                               parens (ThcSomeConstructors <$> rule consListSomeP))

      let mkExport ns id cons =
              ThcModuleExport { thcModExpName = id
                              , thcModExpNamespace = ns
                              , thcModExpConstructors = cons }

      oneExportP <- buildRule (mkExport <$> rule namespaceP
                                        <*> rule identifierT
                                        <*> rule consListP)

      exportListInsideP <- buildRule (pure [] <|> (:) <$> rule oneExportP <*> (pure [] <|> (comma *> rule exportListInsideP)))
      exportListP <- buildRule (fmap Just (parens (rule exportListInsideP)) <|> pure Nothing)


      let mkModule modName exports imports = ThcModule modName exports imports

      importP <- buildRule (importT *> ((\n -> ThcImport (mkModuleName n) False Nothing ThcImportAll) <$> rule consT))
      importsP <- sepBy semicolon (rule importP)

      moduleP <- buildRule (moduleT *> (mkModule <$> (mkModuleName <$> rule consT) <*> rule exportListP <*> (whereT *> indented (rule importsP))))

      pure moduleP

