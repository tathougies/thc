module Language.Haskell.THC.Syntax.AST where

import Language.Haskell.THC.Syntax.Lexer

import Data.Text

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
    } deriving Show
