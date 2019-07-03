{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RecursiveDo #-}
module Language.Haskell.THC.Syntax.Parser where

import           Language.Haskell.THC.Syntax.Lexer
import           Language.Haskell.THC.Syntax.SourceFile
import           Language.Haskell.THC.Syntax.AST

import           Control.Applicative ((<|>), optional, some, many)
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

match x = terminal x (\_ -> Just ())
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
      consT <- buildRule (terminal ThcLexemeCategoryConstructor (\(ThcLexemeIdentifier id) -> Just id))
      idT <- buildRule (terminal ThcLexemeCategoryIdentifier (\(ThcLexemeIdentifier id) -> Just id))

      identifierT <- buildRule (idT <|> consT)
      unqualifiedIdentifierT <- buildRule (terminal ThcLexemeCategoryIdentifier (\(ThcLexemeIdentifier (ThcIdentifier q nm)) ->
                                                                                    case q of { [] -> Just nm; _ -> Nothing }))
      unqualifiedConsT <- buildRule (terminal ThcLexemeCategoryConstructor (\(ThcLexemeIdentifier (ThcIdentifier q nm)) ->
                                                                               case q of { [] -> Just nm; _ -> Nothing }))

      operatorT <- buildRule (terminal ThcLexemeCategoryOperator (\(ThcLexemeOperator id) -> Just id))

      let nameT = fmap (\(ThcIdentifier _ nm) -> nm) identifierT -- TODO

          oParen = match (ThcLexemeCategorySimple ThcLexemeOpenParen)
          cParen = match (ThcLexemeCategorySimple ThcLexemeCloseParen)
          oBracket = match (ThcLexemeCategorySimple ThcLexemeOpenBracket)
          cBracket = match (ThcLexemeCategorySimple ThcLexemeCloseBracket)
          oBrace = match (ThcLexemeCategorySimple ThcLexemeOpenIndent)
          cBrace = match (ThcLexemeCategorySimple ThcLexemeCloseIndent)
          comma = match (ThcLexemeCategorySimple ThcLexemeComma)
          semicolon = match (ThcLexemeCategorySimple ThcLexemeSemicolon)
          equals = simple ThcLexemeEqual

          newtypeT = simple ThcLexemeNewtype
          typeT = simple ThcLexemeType
          dataT = simple ThcLexemeData
          bang = simple ThcLexemeBang
          derivingT = simple ThcLexemeDeriving
          bar = simple ThcLexemeBar

          hasTypeT = simple ThcLexemeHasType
          contextT = simple ThcLexemeContext
          funArrowT = simple ThcLexemeArrow

          moduleT = match (ThcLexemeCategorySimple ThcLexemeModule)
          whereT = match (ThcLexemeCategorySimple ThcLexemeWhere)
          importT = match (ThcLexemeCategorySimple ThcLexemeImport)

          intT = terminal ThcLexemeCategoryRational (\(ThcLexemeRational r) -> Just (round r)) -- TODO only allow integers

          parens a = oParen *> a <* cParen
          brackets a = oBracket *> a <* cBracket
          indented a = oBrace *> a <* cBrace

          sepBy what item = pure [] <|> sepBy1 what item

          sepBy1 what item = (:) <$> item <*> many (what *> item)

      namespaceP <- buildRule ((ThcModuleNamespaceModule <$ match (ThcLexemeCategorySimple ThcLexemeModule)) <|>
                               (ThcModuleNamespaceType <$ match (ThcLexemeCategorySimple ThcLexemeType)) <|>
                               pure ThcModuleNamespaceValue)

      consListSomeP <- buildRule (pure [] <|>
                                  (:) <$> identifierT <*> (pure [] <|> (comma *> consListSomeP)))

      consListP <-  buildRule (pure ThcNoConstructors <|>
                               parens (ThcSomeConstructors <$> consListSomeP))

      let mkExport ns id cons =
              ThcModuleExport { thcModExpName = id
                              , thcModExpNamespace = ns
                              , thcModExpConstructors = cons }

      oneExportP <- buildRule (mkExport <$> namespaceP
                                        <*> identifierT
                                        <*> consListP)

      exportListInsideP <- buildRule (pure [] <|> (:) <$> oneExportP <*> (pure [] <|> (comma *> exportListInsideP)))
      exportListP <- buildRule (fmap Just (parens exportListInsideP) <|> pure Nothing)


      let mkModule modName exports (imports, decls) = ThcModule modName exports imports decls
          addImport newImport (imports, decls) = (newImport:imports, decls)
          addDecl newDecl (imports, decls) = (imports, newDecl:decls)

      -- | imports
      importP <- buildRule (importT *> ((\n -> ThcImport (mkModuleName n) False Nothing ThcImportAll) <$> consT))
      importsAndDeclsP <- buildRule (modDeclsP <|> addImport <$> importP <*> (pure ([], []) <|> semicolon *> importsAndDeclsP))

      -- | Fixities

      fixityP <- buildRule ((ThcFixityDecl ThcAssociativityLeft  <$ match (ThcLexemeCategorySimple ThcLexemeInfixl)) <|>
                            (ThcFixityDecl ThcAssociativityRight <$ match (ThcLexemeCategorySimple ThcLexemeInfixr)) <|>
                            (ThcFixityDecl ThcAssociativityNone  <$ match (ThcLexemeCategorySimple ThcLexemeInfix)))
      fixityDeclP <- buildRule (fixityP <*> (pure 9 <|> intT) <*> (map (\(ThcIdentifier _ nm) -> nm) <$> sepBy1 comma operatorT))

      -- | Types
      typeP <- buildRule (btypeP <|> ThcTypeFun <$> btypeP <*> (funArrowT *> typeP))
      btypeP <- buildRule (atypeP <|> ThcTypeAp <$> btypeP <*> atypeP)
      atypeP <- buildRule (ThcTypeTuple <$> parens tupleInsideP <|>
                           ThcTypeList <$> brackets typeP <|>
                           parens typeP <|>
                           ThcTypeVar <$> unqualifiedIdentifierT <|>
                           qtyconP)

      qtyconP <- buildRule (ThcTypeCon <$> consT <|>
                            ThcTypeListCon <$ brackets typeP <|>
                            ThcTypeFunTypeCon <$ parens funArrowT <|>
                            ThcTypeTupleCon <$> parens tupleConInsideP)
      tupleConInsideP <- buildRule (pure (0 :: Word) <|> (+1) <$> (comma *> tupleConInsideP))
      tupleInsideP <- buildRule ((:) <$> typeP <*> some (comma *> typeP))


      -- | Contexts
      contextP <- buildRule (ThcContext <$> parens (sepBy comma (classPredP <|> parens contextP)) <|>
                             ThcContext . pure <$> classPredP)
      classArgsP <- buildRule (pure [] <|> (:) <$> atypeP <*> classArgsP)
      classPredP <- buildRule (ThcContextClass <$> consT <*> classArgsP)

      -- | type decls
      typeSigDeclP <- buildRule (ThcTypeSig <$> (sepBy1 comma nameT <* hasTypeT) <*> optional (contextP <* contextT) <*> typeP)
      simpleTypeP <- buildRule (ThcSimpleType <$> unqualifiedConsT <*> many unqualifiedIdentifierT)

      -- | deriving clause
      derivingClauseP <- buildRule (ThcDeriving <$> (derivingT *> fmap (pure  . ( ThcDerivingStock, )) contextP))

      -- | data decl
      dataDeclP <- buildRule (ThcDataDecl <$> (dataT *> optional (contextP <* contextT)) <*> (simpleTypeP <* equals)
                                          <*> sepBy1 bar dataConstrP <*> optional derivingClauseP)
      dataConstrP <- buildRule (fmap ThcDataConstrAnon anonConstrP <|> fmap ThcDataConstrRecord recordConstrP)
      anonConstrP <- buildRule (ThcAnonDataConstr <$> unqualifiedConsT <*> many aFieldTypeP)
      recordConstrP <- buildRule (ThcRecordDataConstr <$> unqualifiedConsT <*> indented (sepBy comma ((,) <$> sepBy1 comma unqualifiedIdentifierT <*> (hasTypeT *> fieldTypeP))))

      fieldTypeP <- buildRule (ThcFieldType ThcLazy <$> typeP <|>
                               ThcFieldType ThcStrict <$> (bang *> atypeP))
      aFieldTypeP <- buildRule (ThcFieldType ThcLazy <$> atypeP <|>
                                ThcFieldType ThcStrict <$> (bang *> atypeP))

      -- | type decl
      typeDeclP <- buildRule (ThcTypeDecl <$> (typeT *> simpleTypeP <* equals) <*> typeP)

      -- | newtype decl
      newtypeDeclP <- buildRule (ThcNewtypeDecl <$> (newtypeT *> optional (contextP <* contextT))
                                                <*> (simpleTypeP <* equals)
                                                <*> unqualifiedConsT <*> (oBrace *> fmap Just unqualifiedIdentifierT <* hasTypeT)
                                                <*> (typeP <* cBrace)
                                                <*> optional derivingClauseP <|>
                                 ThcNewtypeDecl <$> (newtypeT *> optional (contextP <* contextT))
                                                <*> (simpleTypeP <* equals)
                                                <*> unqualifiedConsT <*> pure Nothing
                                                <*> atypeP <*> optional derivingClauseP)

      declP <- buildRule (ThcModDeclFixity  <$> fixityDeclP <|>
                          ThcModDeclTypeSig <$> typeSigDeclP <|>
                          ThcModDeclData    <$> dataDeclP <|>
                          ThcModDeclNewtype <$> newtypeDeclP <|>
                          ThcModDeclType    <$> typeDeclP)
      modDeclsP <- buildRule (pure ([], []) <|> addDecl <$> declP <*> (pure ([], []) <|> semicolon *> modDeclsP))

      moduleP <- buildRule (moduleT *> (mkModule <$> (mkModuleName <$> consT) <*> exportListP <*> (whereT *> indented importsAndDeclsP)))

      pure (trace "Building module" moduleP)

