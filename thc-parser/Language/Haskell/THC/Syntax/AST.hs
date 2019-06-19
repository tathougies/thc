module Language.Haskell.THC.Syntax.AST where

import Language.Haskell.THC.Syntax.Lexer

import Data.Text
import Data.Word

data ThcModuleNamespace
    = ThcModuleNamespaceType
    | ThcModuleNamespacePattern
    | ThcModuleNamespaceValue
    | ThcModuleNamespaceModule
      deriving Show

data ThcConstructors
    = ThcNoConstructors
    | ThcAllConstructors
    | ThcSomeConstructors [ ThcIdentifier ]
      deriving Show

data ThcModuleExport
    = ThcModuleExport
    { thcModExpName         :: ThcIdentifier
    , thcModExpNamespace    :: ThcModuleNamespace
    , thcModExpConstructors :: ThcConstructors
    } deriving Show

data ThcNameImport
    = ThcNameImport
    { thcImportName :: ThcIdentifier
    , thcImportNamespace :: ThcModuleNamespace
    , thcImportConstructors :: ThcConstructors
    } deriving Show

data ThcImports
    = ThcImportAll
    | ThcImportHiding [ ThcNameImport ]
    | ThcImportExposing [ ThcNameImport ]
      deriving Show

data ThcImport
    = ThcImport
    { thcImportModule :: [ ThcModuleName ]
    , thcQualified    :: Bool
    , thcAlias        :: Maybe [ ThcModuleName ]
    , thcImports      :: ThcImports
    } deriving Show

data ThcModule
    = ThcModule
    { thcModName       :: [ ThcModuleName ]
    , thcModExportList :: Maybe [ ThcModuleExport ]
    , thcModImports    :: [ ThcImport ]
    , thcModDecls      :: [ ThcModDecl ]
    } deriving Show

data ThcAssociativity
  = ThcAssociativityLeft
  | ThcAssociativityRight
  | ThcAssociativityNone
  deriving Show

data ThcFixityDecl
  = ThcFixityDecl
  { thcFixityAssoc :: ThcAssociativity
  , thcFixityLvl   :: Int
  , thcFixityOf    :: [ ThcName ]
  } deriving Show

data ThcModDecl
  = ThcModDeclFixity ThcFixityDecl
  | ThcModDeclTypeSig ThcTypeSig
  deriving Show

data ThcType
  = ThcTypeFun ThcType ThcType
  | ThcTypeAp ThcType ThcType
  | ThcTypeTuple [ ThcType ]
  | ThcTypeList ThcType
  | ThcTypeVar ThcName
  | ThcTypeCon ThcIdentifier
  | ThcTypeListCon
  | ThcTypeFunTypeCon
  | ThcTypeTupleCon Word
  deriving Show

data ThcTypeSig
  = ThcTypeSig
  { thcTypeSigVars :: [ ThcName ]
  , thcTypeSigCtx  :: Maybe ThcContext
  , thcTypeSigTy   :: ThcType
  } deriving Show

data ThcContext
  = ThcContext [ ThcContext ]
  | ThcContextClass ThcIdentifier [ ThcType ]
  deriving Show
