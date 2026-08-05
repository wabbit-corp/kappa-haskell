{-# LANGUAGE DataKinds #-}

module Kappa.KFrontIR.Facts
  ( FrontFactError (..)
  , resolveDeclarationSymbol
  , resolveExpressionType
  , resolveExpressionExpectedType
  , resolveExpressionExpectedQuantity
  , resolveExpressionErasure
  , resolveArgumentSelection
  , resolveArgumentExpectedType
  , resolveArgumentExpectedClassifier
  , resolveArgumentDemand
  , resolveArgumentBorrowDemand
  , resolveArgumentErasure
  , blockArgumentErasure
  , failArgumentErasure
  ) where

import Data.IntMap.Strict qualified as IntMap
import Kappa.Core (Q, RuntimeErasure, Term)
import Kappa.KFrontIR.Identity.Internal
import Kappa.KFrontIR.Phase
import Kappa.KFrontIR.Types.Internal

data FrontFactError
  = FrontFactPhaseError !FrontPhaseError
  | FrontFactMissingNode !SomeFrontNodeId
  | FrontFactConflict !SomeFrontNodeId !String
  deriving stock (Eq, Show)

resolveDeclarationSymbol
  :: FrontNodeId 'DeclNode
  -> DeclarationSymbolId
  -> KFrontIR
  -> Either FrontFactError KFrontIR
resolveDeclarationSymbol identity symbol front = do
  requirePhase DeclarationShapes front
  updateDecl identity (setResolution "declaration symbol" symbol) DeclarationShapes front

resolveExpressionType
  :: FrontNodeId 'ExprNode
  -> Term
  -> KFrontIR
  -> Either FrontFactError KFrontIR
resolveExpressionType identity typ front = do
  requirePhase BodyResolve front
  updateExpr identity (updateExprFacts "resolved type" efResolvedType (\value facts -> facts {efResolvedType = value}) typ) BodyResolve front

resolveExpressionExpectedType
  :: FrontNodeId 'ExprNode
  -> Term
  -> KFrontIR
  -> Either FrontFactError KFrontIR
resolveExpressionExpectedType identity typ front = do
  requirePhase BodyResolve front
  updateExpr identity (updateExprFacts "expected type" efExpectedType (\value facts -> facts {efExpectedType = value}) typ) BodyResolve front

resolveExpressionExpectedQuantity
  :: FrontNodeId 'ExprNode
  -> Q
  -> KFrontIR
  -> Either FrontFactError KFrontIR
resolveExpressionExpectedQuantity identity quantity front = do
  requirePhase BodyResolve front
  updateExpr identity (updateExprFacts "expected quantity" efExpectedQuantity (\value facts -> facts {efExpectedQuantity = value}) quantity) BodyResolve front

resolveExpressionErasure
  :: FrontNodeId 'ExprNode
  -> RuntimeErasure Term
  -> KFrontIR
  -> Either FrontFactError KFrontIR
resolveExpressionErasure identity erasure front = do
  requirePhase BodyResolve front
  updateExpr identity (updateExprFacts "expression erasure" efExpressionErasure (\value facts -> facts {efExpressionErasure = value}) erasure) BodyResolve front

resolveArgumentSelection
  :: FrontNodeId 'ArgNode
  -> SelectedBinderId
  -> KFrontIR
  -> Either FrontFactError KFrontIR
resolveArgumentSelection identity binder front = do
  requirePhase BodyResolve front
  updateArg identity (updateArgFacts "selected binder" afSelectedBinder (\value facts -> facts {afSelectedBinder = value}) binder) BodyResolve front

resolveArgumentExpectedType
  :: FrontNodeId 'ArgNode
  -> Term
  -> KFrontIR
  -> Either FrontFactError KFrontIR
resolveArgumentExpectedType identity typ front = do
  requirePhase BodyResolve front
  updateArg identity (updateArgFacts "expected type" afExpectedType (\value facts -> facts {afExpectedType = value}) typ) BodyResolve front

resolveArgumentExpectedClassifier
  :: FrontNodeId 'ArgNode
  -> Term
  -> KFrontIR
  -> Either FrontFactError KFrontIR
resolveArgumentExpectedClassifier identity classifier front = do
  requirePhase BodyResolve front
  updateArg identity (updateArgFacts "expected classifier" afExpectedClassifier (\value facts -> facts {afExpectedClassifier = value}) classifier) BodyResolve front

resolveArgumentDemand
  :: FrontNodeId 'ArgNode
  -> Q
  -> KFrontIR
  -> Either FrontFactError KFrontIR
resolveArgumentDemand identity demand front = do
  requirePhase BodyResolve front
  updateArg identity (updateArgFacts "demand" afDemand (\value facts -> facts {afDemand = value}) demand) BodyResolve front

resolveArgumentBorrowDemand
  :: FrontNodeId 'ArgNode
  -> Maybe Q
  -> KFrontIR
  -> Either FrontFactError KFrontIR
resolveArgumentBorrowDemand identity demand front = do
  requirePhase BodyResolve front
  updateArg identity (updateArgFacts "borrow demand" afBorrowDemand (\value facts -> facts {afBorrowDemand = value}) demand) BodyResolve front

resolveArgumentErasure
  :: FrontNodeId 'ArgNode
  -> RuntimeErasure Term
  -> KFrontIR
  -> Either FrontFactError KFrontIR
resolveArgumentErasure identity erasure front = do
  requirePhase BodyResolve front
  updateArg identity (updateArgFacts "argument erasure" afErasure (\value facts -> facts {afErasure = value}) erasure) BodyResolve front

blockArgumentErasure
  :: FrontNodeId 'ArgNode
  -> ObligationId
  -> KFrontIR
  -> Either FrontFactError KFrontIR
blockArgumentErasure identity obligation front = do
  requirePhase BodyResolve front
  updateArg identity (transitionArgErasure "argument erasure" (Blocked obligation)) BodyResolve front

failArgumentErasure
  :: FrontNodeId 'ArgNode
  -> FrontErrorId
  -> KFrontIR
  -> Either FrontFactError KFrontIR
failArgumentErasure identity failure front = do
  requirePhase BodyResolve front
  updateArg identity (transitionArgErasure "argument erasure" (Failed failure)) BodyResolve front

requirePhase :: KFrontIRPhase -> KFrontIR -> Either FrontFactError ()
requirePhase phase front = either (Left . FrontFactPhaseError) Right (requireFrontIRWritePhase phase front)

setResolution :: Eq a => String -> a -> Resolution a -> Either String (Resolution a)
setResolution label value = transitionResolution label (Resolved value)

transitionResolution :: Eq a => String -> Resolution a -> Resolution a -> Either String (Resolution a)
transitionResolution _ requested Pending = Right requested
transitionResolution _ requested (Blocked _)
  | isTerminal requested = Right requested
transitionResolution _ requested current
  | requested == current = Right current
transitionResolution label _ _ = Left label

isTerminal :: Resolution a -> Bool
isTerminal Resolved {} = True
isTerminal Failed {} = True
isTerminal _ = False

updateExprFacts
  :: Eq a
  => String
  -> (ExprFacts -> Resolution a)
  -> (Resolution a -> ExprFacts -> ExprFacts)
  -> a
  -> ExprFacts
  -> Either String ExprFacts
updateExprFacts label project inject value facts = do
  resolution <- setResolution label value (project facts)
  pure (inject resolution facts)

updateArgFacts
  :: Eq a
  => String
  -> (ArgFacts -> Resolution a)
  -> (Resolution a -> ArgFacts -> ArgFacts)
  -> a
  -> ArgFacts
  -> Either String ArgFacts
updateArgFacts label project inject value facts = do
  resolution <- setResolution label value (project facts)
  pure (inject resolution facts)

transitionArgErasure :: String -> Resolution (RuntimeErasure Term) -> ArgFacts -> Either String ArgFacts
transitionArgErasure label requested facts = do
  resolution <- transitionResolution label requested (afErasure facts)
  pure facts {afErasure = resolution}

updateDecl
  :: FrontNodeId 'DeclNode
  -> (Resolution DeclarationSymbolId -> Either String (Resolution DeclarationSymbolId))
  -> KFrontIRPhase
  -> KFrontIR
  -> Either FrontFactError KFrontIR
updateDecl identity@(FrontNodeId arena key) update _required front =
  case if arena == kfArena front then IntMap.lookup key (kfDecls front) else Nothing of
    Nothing -> Left (FrontFactMissingNode (SomeDeclNode identity))
    Just node ->
      case update (fnFacts node) of
        Left label -> Left (FrontFactConflict (SomeDeclNode identity) label)
        Right facts ->
          Right front {kfDecls = IntMap.insert key (node {fnFacts = facts}) (kfDecls front)}

updateExpr
  :: FrontNodeId 'ExprNode
  -> (ExprFacts -> Either String ExprFacts)
  -> KFrontIRPhase
  -> KFrontIR
  -> Either FrontFactError KFrontIR
updateExpr identity@(FrontNodeId arena key) update _required front =
  case if arena == kfArena front then IntMap.lookup key (kfExprs front) else Nothing of
    Nothing -> Left (FrontFactMissingNode (SomeExprNode identity))
    Just node ->
      case update (fnFacts node) of
        Left label -> Left (FrontFactConflict (SomeExprNode identity) label)
        Right facts ->
          Right front {kfExprs = IntMap.insert key (node {fnFacts = facts}) (kfExprs front)}

updateArg
  :: FrontNodeId 'ArgNode
  -> (ArgFacts -> Either String ArgFacts)
  -> KFrontIRPhase
  -> KFrontIR
  -> Either FrontFactError KFrontIR
updateArg identity@(FrontNodeId arena key) update _required front =
  case if arena == kfArena front then IntMap.lookup key (kfArgs front) else Nothing of
    Nothing -> Left (FrontFactMissingNode (SomeArgNode identity))
    Just node ->
      case update (fnFacts node) of
        Left label -> Left (FrontFactConflict (SomeArgNode identity) label)
        Right facts ->
          Right front {kfArgs = IntMap.insert key (node {fnFacts = facts}) (kfArgs front)}
