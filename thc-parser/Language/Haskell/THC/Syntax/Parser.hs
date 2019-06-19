{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RecursiveDo #-}
module Language.Haskell.THC.Syntax.Parser where

import           Language.Haskell.THC.Syntax.Lexer
import           Language.Haskell.THC.Syntax.SourceFile
import           Language.Haskell.THC.Syntax.AST

import           Control.Applicative ((<|>), optional)
import           Control.Monad

import qualified Data.FingerTree.Pinky as FingerTree
import           Data.Foldable (toList)

import           Debug.Trace

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
    getAll (BisectingToken ts) = ts

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
simple = match . ThcLexemeCategorySimple

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
hsLexemeCategory (ThcLexemeOperator _) = ThcLexemeCategoryOperator
hsLexemeCategory (ThcLexemeRational _) = ThcLexemeCategoryRational
hsLexemeCategory (ThcLexemeText _) = ThcLexemeCategoryText
hsLexemeCategory (ThcLexemeChar _) = ThcLexemeCategoryChar

hsModParser :: Parser ThcLexeme ThcModule
hsModParser =
    compile hsLexemeCategory $ mdo
      consT <- buildRule (terminal ThcLexemeCategoryConstructor (\(ThcLexemeIdentifier id) -> id))
      idT <- buildRule (terminal ThcLexemeCategoryIdentifier (\(ThcLexemeIdentifier id) -> id))

      identifierT <- buildRule (rule idT <|> rule consT)

      operatorT <- buildRule (terminal ThcLexemeCategoryOperator (\(ThcLexemeOperator id) -> id))

      let nameT = fmap (\(ThcIdentifier _ nm) -> nm) (rule identifierT) -- TODO

          oParen = match (ThcLexemeCategorySimple ThcLexemeOpenParen)
          cParen = match (ThcLexemeCategorySimple ThcLexemeCloseParen)
          oBracket = match (ThcLexemeCategorySimple ThcLexemeOpenBracket)
          cBracket = match (ThcLexemeCategorySimple ThcLexemeCloseBracket)
          oBrace = match (ThcLexemeCategorySimple ThcLexemeOpenIndent)
          cBrace = match (ThcLexemeCategorySimple ThcLexemeCloseIndent)
          comma = match (ThcLexemeCategorySimple ThcLexemeComma)
          semicolon = match (ThcLexemeCategorySimple ThcLexemeSemicolon)

          hasTypeT = simple ThcLexemeHasType
          contextT = simple ThcLexemeContext
          funArrowT = simple ThcLexemeArrow

          moduleT = match (ThcLexemeCategorySimple ThcLexemeModule)
          whereT = match (ThcLexemeCategorySimple ThcLexemeWhere)
          importT = match (ThcLexemeCategorySimple ThcLexemeImport)

          intT = terminal ThcLexemeCategoryRational (\(ThcLexemeRational r) -> round r) -- TODO only allow integers

          parens a = oParen *> a <* cParen
          brackets a = oBracket *> a <* cBracket
          indented a = oBrace *> a <* cBrace

          sepBy what item = mdo
            list <- buildRule (pure [] <|> (:) <$> item <*> (pure [] <|> (what *> rule list)))
            pure list

          sepBy1 what item = mdo
            list <- buildRule ((:) <$> item <*> (pure [] <|> (what *> rule list)))
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


      let mkModule modName exports (imports, decls) = ThcModule modName exports imports decls
          addImport newImport (imports, decls) = (newImport:imports, decls)
          addDecl newDecl (imports, decls) = (imports, newDecl:decls)

      -- | imports
      importP <- buildRule (importT *> ((\n -> ThcImport (mkModuleName n) False Nothing ThcImportAll) <$> rule consT))
      importsAndDeclsP <- buildRule (rule modDeclsP <|> addImport <$> rule importP <*> (pure ([], []) <|> semicolon *> rule importsAndDeclsP))

      -- | Fixities

      fixityP <- buildRule ((ThcFixityDecl ThcAssociativityLeft  <$ match (ThcLexemeCategorySimple ThcLexemeInfixl)) <|>
                            (ThcFixityDecl ThcAssociativityRight <$ match (ThcLexemeCategorySimple ThcLexemeInfixr)) <|>
                            (ThcFixityDecl ThcAssociativityNone  <$ match (ThcLexemeCategorySimple ThcLexemeInfix)))
      fixitySymbolsP <- sepBy1 comma (rule operatorT)
      fixityDeclP <- buildRule (rule fixityP <*> (pure 9 <|> intT) <*> (map (\(ThcIdentifier _ nm) -> nm) <$> rule fixitySymbolsP))

      -- | Types
      typeP <- buildRule (rule btypeP <|> ThcTypeFun <$> rule btypeP <*> (funArrowT *> rule typeP))
      btypeP <- buildRule (rule atypeP <|> ThcTypeAp <$> rule btypeP <*> rule atypeP)
--      atypeP <- buildRule (--ThcTypeTuple <$> parens (rule tupleInsideP) <|>
--                           ThcTypeList <$> brackets (rule typeP) <|>
--                           parens (rule typeP) -- <|>
--                           ThcTypeVar <$> nameT <|>
--                           rule qtyconP)
      let atypeP = qtyconP
      qtyconP <- buildRule (ThcTypeCon <$> rule consT <|>
                            ThcTypeListCon <$ brackets (rule typeP)) -- <|>
--                            ThcTypeFunTypeCon <$ parens funArrowT)
--                            ThcTypeTupleCon <$> parens (rule tupleConInsideP))
      --tupleConInsideP <- buildRule (pure (0 :: Word) <|> (+1) <$> (comma *> rule tupleConInsideP))
--      tupleInsideP <- sepBy1 comma (rule typeP)


      -- | Contexts
      contextP <- buildRule (ThcContext <$> parens (rule manyClassesP) <|>
                             ThcContext . pure <$> rule classPredP)
      manyClassesP <- sepBy comma (rule classPredP <|> parens (rule contextP))
      classArgsP <- buildRule (pure [] <|> (:) <$> rule typeP <*> rule classArgsP)
      classPredP <- buildRule (ThcContextClass <$> rule consT <*> rule classArgsP)

      -- | type decls
      varsListP <- sepBy1 comma nameT
      typeSigDeclP <- buildRule (ThcTypeSig <$> (rule varsListP <* hasTypeT) <*> optional (rule contextP) <*> rule typeP)

      declP <- buildRule (ThcModDeclFixity <$> rule fixityDeclP <|>
                          ThcModDeclTypeSig <$> rule typeSigDeclP)
      modDeclsP <- buildRule (pure ([], []) <|> addDecl <$> rule declP <*> (pure ([], []) <|> semicolon *> rule modDeclsP))

      moduleP <- buildRule (moduleT *> (mkModule <$> (mkModuleName <$> rule consT) <*> rule exportListP <*> (whereT *> indented (rule importsAndDeclsP))))

      pure (trace "Building module" moduleP)

