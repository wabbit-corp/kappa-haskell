{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}

module Kappa.KFrontIR.Identity.Internal
  ( FrontArenaId (..)
  , FrontNodeKind (..)
  , FrontNodeId (..)
  , SomeFrontNodeId (..)
  , frontNodeArena
  , frontNodeIdValue
  , OriginId (..)
  , originArena
  , originIdValue
  , ExpansionId (..)
  , expansionArena
  , expansionIdValue
  , DeclarationSymbolId (..)
  , SelectedBinderId (..)
  , SemanticObjectId (..)
  , ObligationId (..)
  , FrontErrorId (..)
  , CoreNodeId (..)
  ) where

import Data.Text (Text)

-- | Identity of one immutable frontend arena. Node-local integer ordinals are
-- meaningful only together with this identity; an ID from another source
-- arena therefore cannot accidentally resolve to an unrelated occurrence.
newtype FrontArenaId = FrontArenaId Text
  deriving stock (Eq, Ord, Show)

data FrontNodeKind
  = ModuleNode
  | DeclNode
  | ExprNode
  | ArgNode
  | BinderNode
  | PatternNode
  | FieldNode
  | ImportNode
  | ExportNode

data FrontNodeId (kind :: FrontNodeKind) = FrontNodeId !FrontArenaId !Int
  deriving stock (Eq, Ord, Show)

data SomeFrontNodeId
  = SomeModuleNode !(FrontNodeId 'ModuleNode)
  | SomeDeclNode !(FrontNodeId 'DeclNode)
  | SomeExprNode !(FrontNodeId 'ExprNode)
  | SomeArgNode !(FrontNodeId 'ArgNode)
  | SomeBinderNode !(FrontNodeId 'BinderNode)
  | SomePatternNode !(FrontNodeId 'PatternNode)
  | SomeFieldNode !(FrontNodeId 'FieldNode)
  | SomeImportNode !(FrontNodeId 'ImportNode)
  | SomeExportNode !(FrontNodeId 'ExportNode)
  deriving stock (Eq, Ord, Show)

frontNodeArena :: SomeFrontNodeId -> FrontArenaId
frontNodeArena = \case
  SomeModuleNode (FrontNodeId arena _) -> arena
  SomeDeclNode (FrontNodeId arena _) -> arena
  SomeExprNode (FrontNodeId arena _) -> arena
  SomeArgNode (FrontNodeId arena _) -> arena
  SomeBinderNode (FrontNodeId arena _) -> arena
  SomePatternNode (FrontNodeId arena _) -> arena
  SomeFieldNode (FrontNodeId arena _) -> arena
  SomeImportNode (FrontNodeId arena _) -> arena
  SomeExportNode (FrontNodeId arena _) -> arena

frontNodeIdValue :: SomeFrontNodeId -> Int
frontNodeIdValue = \case
  SomeModuleNode (FrontNodeId _ value) -> value
  SomeDeclNode (FrontNodeId _ value) -> value
  SomeExprNode (FrontNodeId _ value) -> value
  SomeArgNode (FrontNodeId _ value) -> value
  SomeBinderNode (FrontNodeId _ value) -> value
  SomePatternNode (FrontNodeId _ value) -> value
  SomeFieldNode (FrontNodeId _ value) -> value
  SomeImportNode (FrontNodeId _ value) -> value
  SomeExportNode (FrontNodeId _ value) -> value

data OriginId = OriginId !FrontArenaId !Int
  deriving stock (Eq, Ord, Show)

originArena :: OriginId -> FrontArenaId
originArena (OriginId arena _) = arena

originIdValue :: OriginId -> Int
originIdValue (OriginId _ value) = value

data ExpansionId = ExpansionId !FrontArenaId !Int
  deriving stock (Eq, Ord, Show)

expansionArena :: ExpansionId -> FrontArenaId
expansionArena (ExpansionId arena _) = arena

expansionIdValue :: ExpansionId -> Int
expansionIdValue (ExpansionId _ value) = value

data DeclarationSymbolId = DeclarationSymbolId !FrontArenaId !Int
  deriving stock (Eq, Ord, Show)

-- | Identity of the exact Pi binder selected for one application argument.
-- Source binders retain their occurrence identity; declaration binders use
-- the declaration symbol plus their telescope ordinal. Selecting a callable
-- semantic object does not identify one of its binders.
data SelectedBinderId
  = SelectedSourceBinder !(FrontNodeId 'BinderNode)
  | SelectedDeclarationBinder !DeclarationSymbolId !Int
  deriving stock (Eq, Ord, Show)

data SemanticObjectId = SemanticObjectId !Text
  deriving stock (Eq, Ord, Show)

data ObligationId = ObligationId !FrontArenaId !Int
  deriving stock (Eq, Ord, Show)

data FrontErrorId = FrontErrorId !FrontArenaId !Int
  deriving stock (Eq, Ord, Show)

data CoreNodeId = CoreNodeId !Text
  deriving stock (Eq, Ord, Show)
