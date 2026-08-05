{-# LANGUAGE DataKinds #-}

module Kappa.KFrontIR.Query
  ( lookupFrontModule
  , lookupFrontDecl
  , lookupFrontExpr
  , lookupFrontArg
  , lookupFrontBinder
  , lookupFrontPattern
  , lookupFrontField
  , lookupFrontImport
  , lookupFrontExport
  , allFrontExpressions
  , allFrontArguments
  , frontExpansionCount
  , frontPublishedPhase
  , frontChildren
  , frontParent
  , frontDescendants
  , asModuleNode
  , asDeclNode
  , asExprNode
  , asArgNode
  , asBinderNode
  , asPatternNode
  , asFieldNode
  , asImportNode
  , asExportNode
  ) where

import Data.IntMap.Strict qualified as IntMap
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Kappa.KFrontIR.Identity.Internal
import Kappa.KFrontIR.Types.Internal
import Kappa.Syntax

lookupFrontModule :: FrontNodeId 'ModuleNode -> KFrontIR -> Maybe (FrontNode 'ModuleNode Module ())
lookupFrontModule (FrontNodeId arena key) front = inArena arena front (IntMap.lookup key (kfModules front))

lookupFrontDecl :: FrontNodeId 'DeclNode -> KFrontIR -> Maybe (FrontNode 'DeclNode Decl (Resolution DeclarationSymbolId))
lookupFrontDecl (FrontNodeId arena key) front = inArena arena front (IntMap.lookup key (kfDecls front))

lookupFrontExpr :: FrontNodeId 'ExprNode -> KFrontIR -> Maybe (FrontNode 'ExprNode Expr ExprFacts)
lookupFrontExpr (FrontNodeId arena key) front = inArena arena front (IntMap.lookup key (kfExprs front))

lookupFrontArg :: FrontNodeId 'ArgNode -> KFrontIR -> Maybe (FrontNode 'ArgNode Arg ArgFacts)
lookupFrontArg (FrontNodeId arena key) front = inArena arena front (IntMap.lookup key (kfArgs front))

lookupFrontBinder :: FrontNodeId 'BinderNode -> KFrontIR -> Maybe (FrontNode 'BinderNode Binder ())
lookupFrontBinder (FrontNodeId arena key) front = inArena arena front (IntMap.lookup key (kfBinders front))

lookupFrontPattern :: FrontNodeId 'PatternNode -> KFrontIR -> Maybe (FrontNode 'PatternNode Pattern ())
lookupFrontPattern (FrontNodeId arena key) front = inArena arena front (IntMap.lookup key (kfPatterns front))

lookupFrontField :: FrontNodeId 'FieldNode -> KFrontIR -> Maybe (FrontNode 'FieldNode FrontFieldSyntax ())
lookupFrontField (FrontNodeId arena key) front = inArena arena front (IntMap.lookup key (kfFields front))

lookupFrontImport :: FrontNodeId 'ImportNode -> KFrontIR -> Maybe (FrontNode 'ImportNode FrontImportSyntax ())
lookupFrontImport (FrontNodeId arena key) front = inArena arena front (IntMap.lookup key (kfImports front))

lookupFrontExport :: FrontNodeId 'ExportNode -> KFrontIR -> Maybe (FrontNode 'ExportNode FrontImportSyntax ())
lookupFrontExport (FrontNodeId arena key) front = inArena arena front (IntMap.lookup key (kfExports front))

allFrontExpressions :: KFrontIR -> [FrontNode 'ExprNode Expr ExprFacts]
allFrontExpressions = IntMap.elems . kfExprs

allFrontArguments :: KFrontIR -> [FrontNode 'ArgNode Arg ArgFacts]
allFrontArguments = IntMap.elems . kfArgs

frontExpansionCount :: KFrontIR -> Int
frontExpansionCount = IntMap.size . kfExpansions

frontPublishedPhase :: KFrontIR -> KFrontIRPhase
frontPublishedPhase = kfHighestPhase

inArena :: FrontArenaId -> KFrontIR -> Maybe a -> Maybe a
inArena arena front value
  | arena == kfArena front = value
  | otherwise = Nothing

frontChildren :: SomeFrontNodeId -> KFrontIR -> [SomeFrontNodeId]
frontChildren identity front = Map.findWithDefault [] identity (kfChildren front)

frontParent :: SomeFrontNodeId -> KFrontIR -> Maybe SomeFrontNodeId
frontParent identity front = Map.lookup identity (kfParent front)

-- | Pre-order identity traversal. A malformed cycle cannot make tooling hang:
-- the visited set bounds traversal even before the verifier reports it.
frontDescendants :: SomeFrontNodeId -> KFrontIR -> [SomeFrontNodeId]
frontDescendants root front = go (Set.singleton root) (frontChildren root front)
  where
    go _ [] = []
    go seen (identity : rest)
      | identity `Set.member` seen = go seen rest
      | otherwise =
          identity
            : go
                (Set.insert identity seen)
                (frontChildren identity front ++ rest)

asModuleNode :: SomeFrontNodeId -> Maybe (FrontNodeId 'ModuleNode)
asModuleNode (SomeModuleNode identity) = Just identity
asModuleNode _ = Nothing

asDeclNode :: SomeFrontNodeId -> Maybe (FrontNodeId 'DeclNode)
asDeclNode (SomeDeclNode identity) = Just identity
asDeclNode _ = Nothing

asExprNode :: SomeFrontNodeId -> Maybe (FrontNodeId 'ExprNode)
asExprNode (SomeExprNode identity) = Just identity
asExprNode _ = Nothing

asArgNode :: SomeFrontNodeId -> Maybe (FrontNodeId 'ArgNode)
asArgNode (SomeArgNode identity) = Just identity
asArgNode _ = Nothing

asBinderNode :: SomeFrontNodeId -> Maybe (FrontNodeId 'BinderNode)
asBinderNode (SomeBinderNode identity) = Just identity
asBinderNode _ = Nothing

asPatternNode :: SomeFrontNodeId -> Maybe (FrontNodeId 'PatternNode)
asPatternNode (SomePatternNode identity) = Just identity
asPatternNode _ = Nothing

asFieldNode :: SomeFrontNodeId -> Maybe (FrontNodeId 'FieldNode)
asFieldNode (SomeFieldNode identity) = Just identity
asFieldNode _ = Nothing

asImportNode :: SomeFrontNodeId -> Maybe (FrontNodeId 'ImportNode)
asImportNode (SomeImportNode identity) = Just identity
asImportNode _ = Nothing

asExportNode :: SomeFrontNodeId -> Maybe (FrontNodeId 'ExportNode)
asExportNode (SomeExportNode identity) = Just identity
asExportNode _ = Nothing
