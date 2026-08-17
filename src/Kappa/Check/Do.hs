-- | @do@ blocks, @try@, and effectful sequencing.
--
-- Helpers for the do-kernel: recognizing reference operations, tracking
-- which mutable cells a block reads or writes, and the analyses that decide
-- whether a current-value read may be lifted out of a statement.
--
-- Carved out of "Kappa.Check" as part of splitting that module; see
-- "Kappa.Check.Types" for the shared data dictionary and docs\/CONCEPTS.md
-- for the vocabulary these assume.
module Kappa.Check.Do
  ( abruptSuite
  , annotateExplicitArgs
  , applyVarCurrentEffects
  , builtinIOMonadRefLowering
  , escapedRefFacetsExpr
  , inoutEmptyBindPattern
  , inoutPlaceTarget
  , ioCarrierErrorType
  , isFlexHead
  , isKernelDoCarrierM
  , markImplicitLocal
  , monadActionView
  , monadRefDiagnosticRefType
  , monadRefNewAction
  , monadRefRefType
  , monadRefWriteAction
  , multishotOpExecutedExpr
  , ordinaryRefReadArgs
  , ordinaryRefWriteArgs
  , refFacetReadArgs
  , refFacetWriteArgsWithHead
  , refOpOfTerm
  , refReadWitnessFromInfo
  , refWriteWitnessFromInfo
  , resolvedEtaTermHead
  , statementInferable
  , traitMemberObservationMode
  , unsupportedRefFacet
  ) where

import Control.Applicative ((<|>))
import Control.Monad (filterM, foldM, forM, forM_, guard, replicateM, unless, void, when, zipWithM)
import Control.Monad.State.Strict
import Data.Char (isLower)
import Data.Data (Data, cast, gmapQ)
import Data.Graph (SCC (..), stronglyConnComp)
import Data.List (elemIndex, find, intersect, nub, nubBy, sort, sortOn, zip4, (\\))
import qualified Data.List as List
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes, fromMaybe, isJust, isNothing, listToMaybe, mapMaybe, maybeToList)
import Data.Monoid (Any (..))
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import GHC.Stack (HasCallStack, callStack, prettyCallStack)
import Numeric.Natural (Natural)
import Kappa.Builtins
import Kappa.Cardinality
  ( CardConstraint (..)
  , CardExpr (..)
  , cardAdd
  , cardGuardedSub
  , cardIf
  , cardIndex
  , cardLiteral
  , cardMul
  , normalizeCardExpr
  )
import Kappa.Arithmetic
  ( AFormula (..)
  , ArithmeticSemantics (..)
  , PrimitiveComparisonDomain (..)
  , decodePrimitiveComparisonOperandM
  , deriveArithmeticFormulaReplayWithAssumptions
  , derivePrincipalAffineSubstitution
  , formulaAssumptionFacts
  )
import Kappa.Check.Patch
import Kappa.Check.Pending
  ( captureDependencySnapshot
  , dependencySnapshotIsCurrent
  )
import Kappa.Check.Arith
import Kappa.Check.Totality
import Kappa.Check.Types
import Kappa.Check.UniverseConstraints
  ( constraintIdsForOwnersAndOccurrences
  , rewriteSelectedConstraints
  )
import Kappa.Check.Support
import Kappa.Core
import Kappa.CoreOps
  ( declarationUniverseConstraintBinder
  , declarationUniverseConstraints
  , dedupeUniverseConstraints
  , equivalentUniverseConstraint
  , foldTerm
  , foldTermWithDepth
  , coreToNeutralLevelTerm
  , mentionsGlobal
  , globalsOfTerm
  , mapSchemaRoleEvidence
  , mapPatternConstructorUniverses
  , mapTermWithDepth
  , plainPatternBinder
  , eraseObserveOnlyAnnotations
  , levelMetasOfTerm
  , levelParamsOfTerm
  , roleLevelParamsOfTerm
  , maxFreeIndexTerm
  , metaIdsOf
  , metaOccursInTermShallow
  , metaOccursInTermShallowFuel
  , patBindersC
  , CorePatternDecision (..)
  , instantiateEtaConstructor
  , instantiateCorePatternBody
  , matchCorePattern
  , projectionDepsOf
  , shiftTerm
  , weakenTermUnderBinderAt
  , specializeTraitMemberProjectionType
  , spineOfTerm
  , substGlobal
  , substTopTermAt
  , termClosed
  , termScopedAt
  , zonkTermWith
  )
import qualified Kappa.Backend.Repr as Repr
import Kappa.DependencyFrontier
  ( emptyDependencyFrontier
  , recordDependencyCompletions
  )
import qualified Kappa.DirectedGraph as DirectedGraph
import Kappa.Diagnostic
import Kappa.Eval
import Kappa.Inhabitance
  ( InhabEnv (..)
  , InhabitanceSummary (Empty, Contractible, Finite, Unknown)
  , InhabitancePurpose (..)
  , HeadClass (..)
  , CtorFiber (..)
  , inhabitanceSummary
  , isEmpty
  , multiplySummaries
  , symbolicCardinality
  )
import Kappa.Level
  ( Assumptions
  , ConstraintOrigin (..)
  , LevelMeta
  , LevelConstraint (..)
  , LevelAssignmentGraphError (..)
  , LevelSolveError (..)
  , LevelSolution (..)
  , PrincipalInferenceOutcome (..)
  , PrincipalNonLeastWitness (..)
  , SolveResult (..)
  , assumptionsConsistent
  , assumptionsList
  , classifyAssumptions
  , abstractLocalLevelParams
  , compareClosedLevel
  , emptyLevelAssignmentGraphBudget
  , emptyAssumptions
  , insertAssumption
  , instantiateLocalLevelParams
  , levelVars
  , levelFields
  , levelParams
  , normalizeLevel
  , proveLevelEq
  , proveLevelLeq
  , renderLevel
  , inferPrincipalLevelsFor
  , extendLevelAssignmentGraphWithBudget
  , solveLevelConstraints
  , solveLevelConstraintsFor
  , uniquelyDeterminedLevelAssignmentsFor
  , substituteLevelConstraintMetas
  , substituteLevelMetas
  , substituteLevelParams
  , levelMetas
  , neutralLevelTermLevels
  )
import Kappa.LevelEvidence (validateUniverseEvidenceRelationUnder)
import Kappa.Observation (observationModeSubsumes)
import Kappa.MonotoneWorklist
  ( WorklistResult (..)
  , stabilizeWorklist
  )
import Kappa.UniverseProjection
  ( UniverseReferenceProjection (..)
  , UniverseReferenceProjections (..)
  , deriveUniverseReferenceProjection
  , deriveUniverseReferenceProjectionToLevels
  , rewriteProvisionalUniverseReferences
  , uniqueUniverseReferenceProjections
  )
import Kappa.NominalVariance
import Kappa.ObservationDeps
  ( DependencySet
  , ObservationBinding (..)
  , ObservationOracle (..)
  , ParametricOrigin (..)
  , classifierRelativeDependencies
  , constructorPatternObservationSites
  , dependencyIsAnalysisFailure
  , dependenciesMode
  , evidenceRelativeCallableDependencies
  , isParametricKindValue
  , observationDependencies
  )
import Kappa.Pretty (renderTerm)
import Kappa.Parser (parseExprText)
import Kappa.Representation
import Kappa.Source
import Kappa.Syntax hiding (CompClause (..), Quantity (..))
import qualified Kappa.Syntax as S
import Kappa.Termination hiding (expandedGlobalsOfTerm)
import qualified Kappa.Termination as Termination
import Kappa.TypeTag (semanticTypeTag)
import Kappa.SyntaxOps
  ( boundNamesIn
  , collectSplices
  , freeVarOccurrences
  , freeVarOccurrencesScoped
  , renameFreeVarOccurrences
  , renameVarOccurrences
  , renderExprSrc
  , replaceSplices
  , substQuoteHoles
  )
import Kappa.SurfaceValidation (quantityBorrowMarkerSpans)
import Kappa.Token (QuotedLit (..), StrFragment (..), StringLit (..))
import Kappa.Unicode (isSingleGrapheme)
import Kappa.Usage (tailResumptiveClause)

monadActionView :: Value -> CheckM (Maybe (Value, Value))
monadActionView ty0 = do
  ty <- forceM ty0
  pure (monadActionViewValue ty)

monadRefRefType :: Ctx -> Term -> Term -> CheckM Value
monadRefRefType ctx dictTm aTm = do
  mode <- traitMemberObservationMode prelMonadRef "Ref"
  evalIn ctx (CApp Expl (CProjM mode dictTm "Ref") aTm)

-- | Source-facing associated-cell type for mutable-binding diagnostics.
-- Type checking retains the exact selected dictionary projection above;
-- diagnostics name the authenticated public MonadRef associated member so
-- payloads remain stable across evidence-local projection binders.
monadRefDiagnosticRefType :: Value -> Value
monadRefDiagnosticRefType storedType =
  VGlobN prelRef [(Expl, storedType)]

-- | Read a selected trait member's checked observation mode from the trait
-- declaration. Generated dictionary projections must use the same structural
-- fact as source projections; defaulting a kind-valued member to 'Ordinary'
-- would manufacture a promotion error at the finalized-Core checkpoint.
traitMemberObservationMode :: GName -> Text -> CheckM ObservationMode
traitMemberObservationMode trait member = do
  traits <- gets csTraits
  pure $ fromMaybe Ordinary $ do
    info <- Map.lookup trait traits
    Map.lookup member (tiMemberModes info)

monadRefNewAction :: Term -> Term -> Term -> Term
monadRefNewAction dictTm aTm initTm =
  CApp Expl (CApp Impl (CProjM Ordinary dictTm "newRef") aTm) initTm

monadRefWriteAction :: Term -> Term -> Term -> Term -> Term
monadRefWriteAction dictTm aTm refTm rhsTm =
  CApp Expl (CApp Expl (CApp Impl (CProjM Ordinary dictTm "writeRef") aTm) refTm) rhsTm

freshRefCellId :: CheckM RefCellId
freshRefCellId = do
  n <- gets csNextRefCellId
  modify' $ \st -> st {csNextRefCellId = n + 1}
  pure (RefCellId n)

-- | Recover a resolved declaration identity through the eta-expanded Core
-- representation used for constructors and generated accessors. This is
-- intentionally distinct from 'termHeadGlob': expected-type planning needs
-- the semantic owner even after binders or checked arguments have been
-- recorded around the global head.
resolvedEtaTermHead :: Term -> Maybe GName
resolvedEtaTermHead = \case
  CLamM _ _ _ _ body -> resolvedEtaTermHead body
  CApp _ function _ -> resolvedEtaTermHead function
  CUniverseLift _ _ _ term -> resolvedEtaTermHead term
  CGlob global -> Just global
  CGlobal global _ -> Just global
  CCtor constructor _ _ -> Just constructor
  CCtorI constructor _ _ _ -> Just constructor
  _ -> Nothing

isIOCarrierValue :: Value -> CheckM Bool
isIOCarrierValue mTy0 = do
  mTy <- forceM mTy0
  pure $ case mTy of
    VGlobI g _ [(Expl, _)] -> g == prelIO
    _ -> False

isIOMonadRefInstance :: InstanceEntry -> Bool
isIOMonadRefInstance ie =
  ieTrait ie == prelMonadRef
    && case ieDict ie of
      GName mn _ | mn == preludeModule -> case ieHead ie of
        [carrier] -> termHeadGlob carrier == Just prelIO
        _ -> False
      _ -> False

builtinIOMonadRefLowering :: Ctx -> Value -> Term -> CheckM (Maybe RefLoweringWitness)
builtinIOMonadRefLowering _ctx mTy dictTm = do
  isIO <- isIOCarrierValue mTy
  insts <- gets csInstances
  case termHeadGlob dictTm of
    Just dictG
      | isIO
      , any (\ie -> ieDict ie == dictG && isIOMonadRefInstance ie) insts -> do
          Just . BuiltinIORefWitness <$> freshRefCellId
    _ -> pure Nothing

refReadWitnessFromInfo :: VarRefInfo -> Maybe RefActionWitness
refReadWitnessFromInfo info = BuiltinIORefRead <$> vriLoweringWitness info

refWriteWitnessFromInfo :: VarRefInfo -> Maybe RefActionWitness
refWriteWitnessFromInfo info = BuiltinIORefWrite <$> vriLoweringWitness info

refOpOfTerm :: Ctx -> Term -> CheckM (Maybe (ExplicitRefOp, RefOpEvidence))
refOpOfTerm ctx term =
  case spineOfTerm (stripIdentityWrappers term) of
    (CGlobal global _, arguments)
      | Just operation <- refOperationGlobal global -> do
          definitions <- gets csGlobals
          ec <- ec_
          pure $ do
            definition <- Map.lookup global definitions
            let memberType = globalCoreType ec definition
            let evidence =
                  case selectedMonadRefDictionary memberType arguments of
                    Just dictionary -> RefOpDict dictionary
                    Nothing ->
                      case sourceArgumentsOf memberType arguments of
                        Just [] -> RefOpBare
                        Just [carrier] -> RefOpCarrier carrier
                        _ -> RefOpBare
            pure (operation, evidence)
    (CProjM _ dictionary member, _arguments)
      | Just operation <- refOperationMember member -> do
          dictionaryType <- knownRefEvidenceType ctx dictionary
          case dictionaryType of
            Nothing -> pure Nothing
            Just ty -> do
              ty' <- forceM ty
              pure $ case ty' of
                VGlobI trait _ _ | trait == prelMonadRef ->
                  Just (operation, RefOpDict dictionary)
                _ -> Nothing
    _ -> pure Nothing
  where
    -- Recognition is by the exact selected declaration identity. A record or
    -- unrelated trait field that merely happens to be named readRef/writeRef
    -- is not a MonadRef operation.
    refOperationGlobal global
      | global == prelReadRef
          || global == memberGlobal prelMonadRef "readRef" =
          Just ExplicitRefRead
      | global == prelWriteRef
          || global == memberGlobal prelMonadRef "writeRef" =
          Just ExplicitRefWrite
      | otherwise = Nothing

    refOperationMember = \case
      "readRef" -> Just ExplicitRefRead
      "writeRef" -> Just ExplicitRefWrite
      _ -> Nothing

    -- A projected method is recognized only from a receiver whose checked
    -- type is the canonical MonadRef trait application. The source field
    -- spelling alone is never semantic authority: an unrelated record or
    -- trait member named readRef/writeRef therefore remains ordinary code.
    knownRefEvidenceType current = \case
      CVar index ->
        pure (ceType <$> indexMaybe index (ctxEntries current))
      CGlobal global universes -> do
        definitions <- gets csGlobals
        case Map.lookup global definitions of
          Nothing -> pure Nothing
          Just definition -> do
            (_, ty) <- specializeGlobalAt current global definition universes
            pure (Just ty)
      CUniverseLift _ _ _ inner -> knownRefEvidenceType current inner
      CSchemaLift _ _ _ _ _ _ _ _ inner -> knownRefEvidenceType current inner
      _ -> pure Nothing

    indexMaybe index entries =
      case drop index entries of
        entry : _ -> Just entry
        [] -> Nothing

    -- Align the checked application with its typed declaration telescope.
    -- Generated declaration-universe proof binders are authenticated by
    -- BinderGenerated and do not occupy semantic member-prefix positions.
    -- The remaining source binders begin with MonadRef's carrier and selected
    -- dictionary, followed by the member's own parameters.
    sourceArgumentsOf typeTerm = go typeTerm []
      where
        go _ collected [] = Just (reverse collected)
        go (CPiEvidenceM _ _ expectedIcit _ _ _ _ origin _ codomain)
            collected ((actualIcit, argument) : rest)
          | expectedIcit == actualIcit =
              go codomain
                (if origin == BinderGenerated then collected else argument : collected)
                rest
        go _ _ _ = Nothing

    -- Select evidence by the checked member telescope, never by a positional
    -- guess. MonadRef members may carry other evidence (notably Monad m)
    -- before the selected MonadRef m dictionary. Each supplied argument is
    -- substituted through the dependent codomain so the next binder domain is
    -- inspected at the exact occurrence instantiation.
    selectedMonadRefDictionary = go
      where
        go _ [] = Nothing
        go
          (CPiEvidenceM _ _ expectedIcit _ _ _ _ _ domain codomain)
          ((actualIcit, argument) : rest)
          | expectedIcit == actualIcit =
              if termHeadGlob (stripIdentityWrappers domain) == Just prelMonadRef
                then Just argument
                else go (substTopTermAt 0 argument codomain) rest
        go _ _ = Nothing

ordinaryRefReadArgs :: [Arg] -> Maybe ([Arg], Expr)
ordinaryRefReadArgs = go []
  where
    go prefix = \case
      ArgImplicit e : rest -> go (prefix ++ [ArgImplicit e]) rest
      [ArgExplicit e]
        | Nothing <- refFacetExpr e -> Just (prefix, e)
      _ -> Nothing

ordinaryRefWriteArgs :: [Arg] -> Maybe ([Arg], Expr, Expr)
ordinaryRefWriteArgs = go []
  where
    go prefix = \case
      ArgImplicit e : rest -> go (prefix ++ [ArgImplicit e]) rest
      [ArgExplicit refE, ArgExplicit rhsE]
        | Nothing <- refFacetExpr refE -> Just (prefix, refE, rhsE)
      _ -> Nothing

refFacetExpr :: Expr -> Maybe (Name, Span)
refFacetExpr = \case
  ERefFacet n sp -> Just (n, sp)
  EAscription e _ _ -> refFacetExpr e
  _ -> Nothing

refFacetReadArgs :: [Arg] -> Maybe ([Arg], Name, Span)
refFacetReadArgs = go []
  where
    go prefix = \case
      ArgImplicit e : rest -> go (prefix ++ [ArgImplicit e]) rest
      [ArgExplicit e]
        | Just (n, sp) <- refFacetExpr e -> Just (prefix, n, sp)
      _ -> Nothing

refFacetWriteArgsWithHead :: [Arg] -> Maybe ([Arg], Name, Expr, Span)
refFacetWriteArgsWithHead = go []
  where
    go prefix = \case
      ArgImplicit e : rest -> go (prefix ++ [ArgImplicit e]) rest
      [ArgExplicit refE, ArgExplicit rhs]
        | Just (n, sp) <- refFacetExpr refE -> Just (prefix, n, rhs, sp)
      _ -> Nothing

applyVarCurrentEffects :: Set Text -> Set Text -> Ctx -> Ctx
applyVarCurrentEffects writes escapes ctx =
  foldr escapeVarCurrent
    (foldr invalidateVarCurrent ctx (Set.toList writes))
    (Set.toList escapes)

-- | §18.6.2 current-value facts do not survive an operation site whose
-- declared resumption quantity permits multi-shot reuse. Recognition consumes
-- checker-recorded spans produced by resolved effect-label identity and
-- operation metadata, not by rediscovering @label.op@ source spelling.
multishotOpExecutedExpr :: Ctx -> Expr -> CheckM Bool
multishotOpExecutedExpr _ctx expr = do
  ops <- gets csRecognizedMultishotOps
  pure (recognizedMultishotInExpr ops expr)

recognizedMultishotInExpr :: Map Span (GName, Text) -> Expr -> Bool
recognizedMultishotInExpr ops = go
  where
    hit sp = Map.member sp ops
    hitMember = \case
      DotName op -> hit (nameSpan op)
      DotOperator op -> hit (nameSpan op)
    anyMap p = any p
    goArg = \case
      ArgExplicit e -> go e
      ArgImplicit e -> go e
      ArgInout e _ -> go e
      ArgNamedBlock fields _ -> any (maybe False go . snd) fields
    goLet (LetBind _ _ _ _ rhs _) = go rhs
    goCase = \case
      MatchCase _ mg body _ -> maybe False go mg || go body
      MatchImpossible {} -> False
    goExcept (ExceptCase _ mg body _) = maybe False go mg || go body
    goHandler = \case
      HandlerReturn _ body _ -> go body
      HandlerOp _ _ _ body _ -> go body
    goDecl = \case
      DLet _ ld _ -> go (ldBody ld)
      DTopSplice e _ -> go e
      DUnsafeAssert _ inner _ -> goDecl inner
      _ -> False
    goDo = \case
      DoBind lb -> go (lbExpr lb)
      DoLet lb -> go (lbExpr lb)
      DoLetQ _ rhs mElse _ -> go rhs || maybe False (go . snd) mElse
      DoVar _ mty rhs _ -> maybe False go mty || go rhs
      DoAssign _ _ rhs _ -> go rhs
      DoExpr e -> go e
      DoUsing _ _ rhs _ -> go rhs
      DoDefer {} -> False
      DoReturn _ me _ -> maybe False go me
      DoBreak {} -> False
      DoContinue {} -> False
      DoWhile _ cond body mels _ -> go cond || any goDo body || maybe False (any goDo) mels
      DoFor _ _ src body mels _ -> go src || any goDo body || maybe False (any goDo) mels
      DoIf alts mels _ ->
        any (\(cond, body) -> go cond || any goDo body) alts || maybe False (any goDo) mels
      DoDecl d -> goDecl d
    goCompClause = \case
      S.CFor _ _ _ src _ -> go src
      S.CLet _ _ mty rhs _ -> maybe False go mty || go rhs
      S.CIf e -> go e
      S.COrderBy keys _ -> any (go . snd) keys
      S.CSkip e _ -> go e
      S.CTake e _ -> go e
      S.CDistinct me _ -> maybe False go me
      S.CGroupBy key aggs _ _ -> go key || any (\(_, e, mu) -> go e || maybe False go mu) aggs
      S.CJoin _ _ src on _ _ -> go src || go on
    goYield = \case
      YieldExpr e -> go e
      YieldPair k v -> go k || go v
    goPatch = \case
      PatchUpdate _ (PatchValue e) -> go e
      PatchExtend _ e -> go e
      PatchSection a b -> go a || go b
      PatchPun {} -> False
    goOpElem = \case
      ChainOperand e -> go e
      ChainOp {} -> False
    go = \case
      EVar {} -> False
      EContextualImpossible {} -> False
      ERefFacet {} -> False
      EVarRead {} -> False
      EHole {} -> False
      EIntLit {} -> False
      EFloatLit {} -> False
      EStringLit _ parts _ -> any (go . ipExpr) parts
      EQuotedLit {} -> False
      EUnit {} -> False
      ETuple es _ -> any go es
      ERecordLit items _ -> any (\(RecItem _ _ mv) -> maybe False go mv) items
      ERecordType {} -> False
      EUniverseInstantiation base levels _ -> go base || any go levels
      eApp@(EApp f args) -> hit (exprSpan eApp) || go f || any goArg args
      EDot recv member -> hitMember member || go recv
      EQDot recv member -> hitMember member || go recv
      ERecordPatch recv items _ -> go recv || any goPatch items
      EReceiverSection _ args _ -> any goArg args
      ESectionLeft e _ _ -> go e
      ESectionRight _ e _ -> go e
      EOpRef {} -> False
      EOpChain elems -> any goOpElem elems
      EElvis a b _ -> go a || go b
      ELambda {} -> False
      ELet binds body _ -> any goLet binds || go body
      EBlock decls mres _ -> any goDecl decls || maybe False go mres
      EDo _ items _ -> any goDo items
      EIf alts mels _ ->
        anyMap (\(cond, body) -> go cond || go body) alts || maybe False go mels
      EMatch scrut cases _ -> go scrut || any goCase cases
      ETry scrut excepts mfin _ -> go scrut || any goExcept excepts || maybe False go mfin
      ETryMatch scrut cases excepts mfin _ ->
        go scrut || any goCase cases || any goExcept excepts || maybe False go mfin
      EHandle _ lbl scrut cases _ -> go lbl || go scrut || any goHandler cases
      EIs e _ -> go e
      EThunk {} -> False
      ELazy {} -> False
      EForce e _ -> go e
      ESeal a b _ -> go a || go b
      EOpenExists e _ _ body _ -> go e || go body
      ESealExists bs a b _ -> any (go . snd) bs || go a || go b
      EListLit es _ -> any go es
      ESetLit es _ -> any go es
      EMapLit kvs _ -> any (\(k, v) -> go k || go v) kvs
      EComprehension _ clauses yield _ -> any goCompClause clauses || goYield yield
      EArrow {} -> False
      EForall {} -> False
      EExists {} -> False
      ETraitArrow {} -> False
      EEffRow {} -> False
      EVariant arms mtail _ ->
        any (\(VariantArm e mty) -> go e || maybe False go mty) arms || maybe False go mtail
      EOptionSugar {} -> False
      EAscription e _ _ -> go e
      ECaptures e _ _ -> go e
      EBang _ e _ -> go e
      EQuote {} -> False
      ECodeQuote {} -> False
      ECodeEscape e _ -> go e
      ESplice e _ -> go e
      ESpliceInQuote {} -> False
      EQuoteHole {} -> False
      EImpossible {} -> False
      EKindQualified {} -> False
      EModuleSig {} -> False

unsupportedRefFacet :: Ctx -> Name -> Span -> CheckM (Maybe (Term, Value))
unsupportedRefFacet ctx n sp = do
  errAt sp "E_UNSUPPORTED" (Just "kappa.unsupported.deterministic")
    ("mutable variable '" <> nameText n <> "' uses a higher-order monad shape this implementation cannot apply for explicit ref-facet operations (§18.6.1)")
  Just <$> anyHole ctx

escapedRefFacetsExpr :: Ctx -> Expr -> CheckM (Set Text)
escapedRefFacetsExpr _ e =
  pure (collectRefFacets e)

ioCarrierErrorType :: Value -> Maybe Value
ioCarrierErrorType carrier = do
  guard (nominalFamilyValueHead carrier == Just prelIO)
  snd <$> monadActionViewValue carrier

isKernelDoCarrierM :: Value -> CheckM Bool
isKernelDoCarrierM carrier = do
  forced <- forceM carrier
  pure (maybe False (`elem` doKernelCarriers) (nominalFamilyValueHead forced))

-- | Does this do-suite have no normal completion that can reach a following
-- item? This is deliberately conservative: only source forms whose every
-- branch is structurally abrupt are accepted.
abruptSuite :: [DoItem] -> Bool
abruptSuite items = case reverse items of
  (DoReturn {} : _) -> True
  (DoBreak {} : _) -> True
  (DoContinue {} : _) -> True
  (DoExpr e : _) -> abruptExpr e
  (DoIf alts (Just els) _ : _) ->
    all (abruptSuite . snd) alts && abruptSuite els
  _ -> False

-- | Expression counterpart of 'abruptSuite'. Match failure and
-- 'impossible' are non-normal completions too, so exhaustiveness is not a
-- prerequisite here; every explicit arm must nevertheless be abrupt.
abruptExpr :: Expr -> Bool
abruptExpr = \case
  EDo _ inner _ -> abruptSuite inner
  EImpossible {} -> True
  EMatch _ cases _ -> all abruptMatchCase cases
  EIf alts (Just els) _ ->
    all (abruptExpr . snd) alts && abruptExpr els
  EAscription e _ _ -> abruptExpr e
  ECaptures e _ _ -> abruptExpr e
  _ -> False
  where
    abruptMatchCase = \case
      MatchCase _ _ body _ -> abruptExpr body
      MatchImpossible {} -> True

-- | Is the (forced) value headed by an unsolved metavariable?
isFlexHead :: Value -> Bool
isFlexHead = \case
  VFlex {} -> True
  _ -> False

-- | Statement shapes that elaborate soundly by inference, allowing the
-- pure-statement accommodation in 'elabDo' (variants, literals and other
-- expected-type-directed forms keep the plain IO checking path).
statementInferable :: Expr -> Bool
statementInferable = \case
  EApp f _ -> statementInferable f
  EVar {} -> True
  EOpRef {} -> True
  EDot {} -> True
  EQDot {} -> True
  EOpChain {} -> True
  EIf {} -> True
  EMatch {} -> True
  EUnit {} -> True
  ETuple {} -> True
  EIntLit {} -> True
  EFloatLit {} -> True
  EStringLit {} -> True
  _ -> False

annotateExplicitArgs :: [Maybe InoutParamInfo] -> [Arg] -> [(Arg, Maybe InoutParamInfo)]
annotateExplicitArgs infos = go infos
  where
    go _ [] = []
    go ps (arg : rest) = case arg of
      ArgImplicit _ -> (arg, Nothing) : go ps rest
      ArgNamedBlock {} -> (arg, Nothing) : go ps rest
      ArgExplicit {} -> case ps of
        p : ps' -> (arg, p) : go ps' rest
        [] -> (arg, Nothing) : go [] rest
      ArgInout {} -> case ps of
        p : ps' -> (arg, p) : go ps' rest
        [] -> (arg, Nothing) : go [] rest

inoutPlaceTarget :: Ctx -> Expr -> Maybe (Name, [Name], Bool, VarInoutWriteBack)
inoutPlaceTarget ctx = go []
  where
    go acc = \case
      EVar n
        | Just (_, entry) <- lookupCtx (nameText n) ctx ->
            Just (n, acc, isJust (ceVarInfo entry), VarInoutPath)
      EDot e (DotName fld) -> go (fld : acc) e
      EAscription e _ _ -> go acc e
      _ -> Nothing

inoutEmptyBindPattern :: Pattern -> Bool
inoutEmptyBindPattern = \case
  PWild _ -> True
  PUnit _ -> True
  _ -> False

-- | §16.3.3: an implicit do-binding @let (\@x : T) = e@ joins the local
-- implicit context for the remaining items. @before@ is the context the
-- pattern was elaborated in; the entries added on top of it are marked.
-- @binderSp@ is the do-binding's source span; for a @\@&@-borrowed
-- implicit local it is recorded as the §3.1.1A introduction origin so a
-- later borrow-escape diagnostic can cite where the candidate was
-- borrowed.
markImplicitLocal :: Span -> Bool -> BinderPrefix -> Ctx -> Ctx -> Ctx
markImplicitLocal _ False _ _ after = after
markImplicitLocal binderSp True (BinderPrefix _ mq mb) before after =
  let es = ctxEntries after
      (new, old) = splitAt (length es - ctxLen before) es
      mark e =
        e
          { ceImplicitLocal = True
          , ceQ = mq
          , ceBorrow = isJust mb
          , ceOrigin = if isJust mb then binderSp else ceOrigin e
          }
   in after {ctxEntries = map mark new ++ old}

-- | Spec §18.3.1 monadic splice (`!`).  The normative elaboration of `!e` is
-- the translation @Splice_m[-]@: a `!e` occurring in a do-item is LIFTED to a
-- monadic bind @tmp <- e@ in the nearest enclosing do-block, and the occurrence
-- is replaced by @tmp@ (`Splice_m[!e] = e`).  Because the lift is a real bind,
-- the spliced result stays MONADIC-typed and left-to-right effect order is
-- preserved.
--
-- This is NOT a pure IO-result extraction.  Extracting `!e` purely was
-- unsound: composed with @throwIO : forall e a. e -> IO e a@ it forges a pure
-- inhabitant of the free @a@.  The bind-lift dissolves this: a bind keeps the
-- item monadic, so @do { !(throwIO Unit) }@ has type @IO _ _@ which is not
-- @Void@ — a plain type error.  It also removes the old synthesized splice-head
-- entirely, so there is no sentinel name a user could spell (via backticks) to
-- route around 'gateUnsafeIntrinsic'.
--
-- 'liftBangsExpr' realizes @Splice_m[-]@ for a single expression: it returns the
-- ordered list of @tmp <- operand@ binds that must be sequenced BEFORE the
-- expression, together with the bang-free residual.  The do-kernels splice those
-- binds in via 'liftDoItems' (the per-do-scope pre-pass).
--
-- Branch-locality (§18.3.1): @Splice_m[if c then t else f] = Splice_m[c] >>= \\c'
-- -> if c' then Splice_m[t] else Splice_m[f]@ — bangs in an /untaken/ branch must
-- NOT run.  So a bang inside an @if@/@match@ branch is NOT hoisted above the
-- conditional; instead the whole conditional is rebuilt with each branch wrapped
-- as a nested @do@ (its own monadic scope) and the conditional itself is bound to
-- a fresh temp.  Only the scrutinee/condition bangs (evaluated unconditionally)
-- are hoisted ahead.
