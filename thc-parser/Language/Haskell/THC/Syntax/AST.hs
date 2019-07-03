module Language.Haskell.THC.Syntax.AST where

import Language.Haskell.THC.Syntax.Lexer

import qualified Data.Text as T
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
  | ThcModDeclData ThcDataDecl
  | ThcModDeclNewtype ThcNewtypeDecl
  | ThcModDeclType ThcTypeDecl
  | ThcModDeclBinding ThcBindingDecl
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

data ThcDataDecl
  = ThcDataDecl
  { thcDataDeclContext :: Maybe ThcContext
  , thcDataDeclType    :: ThcSimpleType
  , thcDataDeclConstrs :: [ ThcDataConstr ]
  , thcDataDeclDeriving :: Maybe ThcDeriving
  } deriving Show

data ThcNewtypeDecl
  = ThcNewtypeDecl
  { thcNewtypeDeclContext :: Maybe ThcContext
  , thcNewtypeDeclType    :: ThcSimpleType
  , thcNewtypeDeclConstrName :: ThcName
  , thcNewtypeDeclConstrFieldName :: Maybe ThcName
  , thcNewtypeDeclWrapped :: ThcType
  , thcNewtypeDeclDeriving :: Maybe ThcDeriving
  } deriving Show

newtype ThcDeriving
  = ThcDeriving [ (ThcDerivingMethod, ThcContext) ]
  deriving Show

data ThcDerivingMethod
  = ThcDerivingStock | ThcDerivingAny | ThcDerivingNewtype
  deriving Show

data ThcSimpleType
  = ThcSimpleType
  { thcSimpleTyCon :: ThcName
  , thcSimpleTyVars :: [ ThcName ]
  } deriving Show

data ThcDataConstr
  = ThcDataConstrAnon ThcAnonDataConstr
  | ThcDataConstrRecord ThcRecordDataConstr
  deriving Show

data ThcAnonDataConstr
  = ThcAnonDataConstr
  { thcAnonDataConstrName :: ThcName
  , thcAnonDataConstrArgs :: [ ThcFieldType ]
  } deriving Show

data ThcRecordDataConstr
  = ThcRecordDataConstr
  { thcRecordDataConstrName :: ThcName
  , thcRecordDataConstrFields :: [ ( [ThcName], ThcFieldType ) ]
  } deriving Show

data ThcStrictness = ThcLazy | ThcStrict
  deriving Show

data ThcFieldType
  = ThcFieldType
  { thcFieldStrictness :: ThcStrictness
  , thcFieldType       :: ThcType
  } deriving Show

data ThcTypeDecl
  = ThcTypeDecl
  { thcTypeDeclHead :: ThcSimpleType
  , thcTypeDeclAlias :: ThcType
  } deriving Show

data ThcBindingDecl
  = ThcBindingDecl
  { thcBindingDeclLhs :: ThcBindingLhs
  , thcBindingDeclRhs :: ThcBindingRhs
  , thcBindingDeclWhere :: [ ThcLetDecl ]}
  deriving Show

data ThcBindingLhs
  = ThcBindingLhsFun ThcFunBinding
  | ThcBindingLhsPat ThcPat
  deriving Show

data ThcFunBinding
  = ThcFunBinding
  { thcFunBindingName :: ThcName
  , thcFunBindingArgs :: [ ThcPat ]
  } deriving Show

data ThcBindingRhs
  = ThcBindingUnguardedRhs ThcExp
  | ThcBindingGuardedRhs [ (ThcGuard, ThcExp) ]
  deriving Show

type ThcGuard = ThcExp

data ThcPat
  = ThcPatCon ThcName [ThcPat]
  | ThcPatVar ThcName
  | ThcPatAlias ThcName ThcPat
  | ThcPatRecord [ (ThcName, ThcPat) ]
  | ThcPatLit ThcLit
  | ThcPatWildCard
  | ThcPatTuple [ ThcPat ]
  | ThcPatList [ ThcPat ]
  | ThcPatIrrefutable ThcPat
  deriving Show

data ThcLit
  = ThcLitText !T.Text
  | ThcLitNumber !Rational
  deriving Show

data ThcLet
  = ThcLetDeclFixity ThcFixityDecl
  | ThcLetDeclTypeSig ThcTypeSig
  | ThcLetDeclBinding ThcBindingDecl
  deriving Show

data ThcListComprehensionProdcuer
  = ThcListComprehensionIntro ThcPat ThcExp
  | ThcListComprehensionGuard ThcExp

data ThcLambda
  = ThcLambda { thcLambdaArgs :: [ ThcLet ]
              , thcLambdaExp  :: ThcExp }
  deriving Show

data ThcLetDecl
  = ThcLetDecl
  { thcLetDeclBindings :: [ ThcLetDecl ] }
  deriving Show

data ThcListComprehensionProvider
  = ThcProvideItems ThcPat ThcExp
  | ThcSchoolSearchesItems
  deriving Show

data ThcCaseChoice
  = ThcCaseChoice ThcPat ThcBindingRhs
  deriving Show

data ThcExp
  = ThcExpTyped ThcExp (Maybe ThcContext) ThcType
  | ThcExpAp ThcExp ThcExp
  | ThcExpLit ThcLit
  | ThcExpLambda ThcLambda
  | ThcIfThenElse ThcExp ThcExp ThcExp
  | ThcLet [ ThcLetDecl ] ThcExp
  | ThcCase ThcExp [ ThcCaseChoice ]
  | ThcExpVar ThcName
  | ThcExpTuple [ ThcExp ]
  | ThcExpList [ ThcExp ]

  | ThcExpArithSeq ThcExp (Maybe ThcExp) (Maybe ThcExp)
  | ThcExpListComprehension ThcExp [ ThcListComprehensionProvider ]
  | ThcExpSectionLeft ThcIdentifier ThcExp
  | ThcExpSectionRight ThcExp ThcIdentifier
  | ThcExpConstruct ThcIdentifier [ (ThcName, ThcExp) ]
  | ThcExpUpdate ThcIdentifier [ (ThcName, ThcExp) ]
  deriving Show
