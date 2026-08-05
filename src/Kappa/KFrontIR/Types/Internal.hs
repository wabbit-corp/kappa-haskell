{-# LANGUAGE DataKinds #-}

module Kappa.KFrontIR.Types.Internal
  ( KFrontIRPhase (..)
  , Resolution (..)
  , FrontNode (..)
  , FrontFieldSyntax (..)
  , FrontImportSyntax (..)
  , ExprFacts (..)
  , ArgFacts (..)
  , emptyExprFacts
  , emptyArgFacts
  , KFrontIR (..)
  , emptyKFrontIR
  ) where

import Data.IntMap.Strict (IntMap)
import Data.IntMap.Strict qualified as IntMap
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text qualified as T
import Kappa.Core (Q, RuntimeErasure, Term)
import Kappa.KFrontIR.Identity.Internal
import Kappa.KFrontIR.Origin
import Kappa.SemanticHash (sha256Hex)
import Kappa.Syntax

data KFrontIRPhase
  = Raw
  | Imports
  | DeclarationShapes
  | HeaderTypes
  | Status
  | ImplicitSignatures
  | BodyResolve
  | ModalSolve
  | Checkers
  | CoreLowering
  deriving stock (Eq, Ord, Enum, Bounded, Show)

data Resolution a
  = Pending
  | Resolved !a
  | Failed !FrontErrorId
  | Blocked !ObligationId
  deriving stock (Eq, Ord, Show)

data FrontNode kind payload facts = FrontNode
  { fnId :: !(FrontNodeId kind)
  , fnOrigin :: !OriginId
  , fnHighestPhase :: !KFrontIRPhase
  , fnSyntax :: !payload
  , fnFacts :: !facts
  }
  deriving stock (Show)

data FrontFieldSyntax
  = FrontRecordValueField !RecItem
  | FrontRecordTypeField !RecTypeField
  | FrontPatchField !PatchItem
  deriving stock (Show)

data FrontImportSyntax
  = FrontImportSpec !ImportSpec
  | FrontImportItem !ImportItem
  | FrontExceptItem !ExceptItem
  deriving stock (Show)

data ExprFacts = ExprFacts
  { efResolvedType :: !(Resolution Term)
  , efExpectedType :: !(Resolution Term)
  , efExpectedQuantity :: !(Resolution Q)
  , efExpressionErasure :: !(Resolution (RuntimeErasure Term))
  , efExpansion :: !(Maybe ExpansionId)
  }
  deriving stock (Eq, Show)

data ArgFacts = ArgFacts
  { afSelectedBinder :: !(Resolution SelectedBinderId)
  , afExpectedType :: !(Resolution Term)
  , afExpectedClassifier :: !(Resolution Term)
  , afDemand :: !(Resolution Q)
  , afBorrowDemand :: !(Resolution (Maybe Q))
  , afErasure :: !(Resolution (RuntimeErasure Term))
  }
  deriving stock (Eq, Show)

emptyExprFacts :: ExprFacts
emptyExprFacts = ExprFacts Pending Pending Pending Pending Nothing

emptyArgFacts :: ArgFacts
emptyArgFacts = ArgFacts Pending Pending Pending Pending Pending Pending

data KFrontIR = KFrontIR
  { kfArena :: !FrontArenaId
  , kfHighestPhase :: !KFrontIRPhase
  , kfOpenPhase :: !(Maybe KFrontIRPhase)
  , kfModule :: !(Maybe (FrontNodeId 'ModuleNode))
  , kfSyntax :: !Module
  , kfModules :: !(IntMap (FrontNode 'ModuleNode Module ()))
  , kfDecls :: !(IntMap (FrontNode 'DeclNode Decl (Resolution DeclarationSymbolId)))
  , kfExprs :: !(IntMap (FrontNode 'ExprNode Expr ExprFacts))
  , kfArgs :: !(IntMap (FrontNode 'ArgNode Arg ArgFacts))
  , kfBinders :: !(IntMap (FrontNode 'BinderNode Binder ()))
  , kfPatterns :: !(IntMap (FrontNode 'PatternNode Pattern ()))
  , kfFields :: !(IntMap (FrontNode 'FieldNode FrontFieldSyntax ()))
  , kfImports :: !(IntMap (FrontNode 'ImportNode FrontImportSyntax ()))
  , kfExports :: !(IntMap (FrontNode 'ExportNode FrontImportSyntax ()))
  , kfOrigins :: !(IntMap Origin)
  , kfExpansions :: !(IntMap ExpansionRecord)
  , kfChildren :: !(Map SomeFrontNodeId [SomeFrontNodeId])
  , kfParent :: !(Map SomeFrontNodeId SomeFrontNodeId)
  , kfNextNodeId :: !Int
  , kfNextOriginId :: !Int
  , kfNextExpansionId :: !Int
  }
  deriving stock (Show)

emptyKFrontIR :: Module -> KFrontIR
emptyKFrontIR syntax =
  KFrontIR
    { kfArena =
        FrontArenaId
          (sha256Hex ("KAPPA:v1:KFrontIR-arena\0" <> T.pack (show syntax)))
    , kfHighestPhase = Raw
    , kfOpenPhase = Nothing
    , kfModule = Nothing
    , kfSyntax = syntax
    , kfModules = IntMap.empty
    , kfDecls = IntMap.empty
    , kfExprs = IntMap.empty
    , kfArgs = IntMap.empty
    , kfBinders = IntMap.empty
    , kfPatterns = IntMap.empty
    , kfFields = IntMap.empty
    , kfImports = IntMap.empty
    , kfExports = IntMap.empty
    , kfOrigins = IntMap.empty
    , kfExpansions = IntMap.empty
    , kfChildren = Map.empty
    , kfParent = Map.empty
    , kfNextNodeId = 0
    , kfNextOriginId = 0
    , kfNextExpansionId = 0
    }
