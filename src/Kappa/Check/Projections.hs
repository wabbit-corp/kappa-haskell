-- | Projection applications (Spec §16.1.5, §16.1.6).
--
-- Recognizing the standard operations behind their dictionary encodings, by
-- resolved semantic identity rather than by source spelling.
--
-- Carved out of "Kappa.Check" as part of splitting that module; see
-- "Kappa.Check.Types" for the shared data dictionary and docs\/CONCEPTS.md
-- for the vocabulary these assume.
module Kappa.Check.Projections
  ( bundleCapsM
  , canonicalizeEqualityGoalUnderCheckedBranchFacts
  , canonicalizeEqualityGoalUnderCheckedBranchFactsOnly
  , canonicalizeSelectedNatOperation
  , canonicalizeTermsUnderCheckedBranchFactsOnly
  , flexApplicationBinderOrigin
  , isUnsafeAssertProofHead
  , mutableVarPlaceRoot
  , pendingEntryHasRigidSemanticArgument
  , pendingEntryIsNumericLiteral
  , pendingEntryUsesAssociatedEvidenceProjection
  , pendingEvidenceComponentsFromRoots
  , projFullApp
  , projectionHead
  , projectionInfoOfExpr
  , runtimeSafeApplicationArgumentPosition
  , stablePlaceExpr
  , withApplicationEvidenceScope
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

-- | Resolve an application head to a projection facet, if any.
projectionHead :: Ctx -> Expr -> CheckM (Maybe (GName, ProjInfo))
projectionHead ctx e = do
  mg <- staticGlobalExpr ctx e
  st <- get
  pure $ do
    g <- mg
    pj <- Map.lookup g (csProjections st)
    pure (g, pj)

projectionInfoOfExpr :: Ctx -> Expr -> CheckM (Maybe ProjInfo)
projectionInfoOfExpr ctx = \case
  EVar hn ->
    case lookupCtx (nameText hn) ctx of
      Just (_, e) -> pure (ceProjInfo e)
      Nothing -> do
        mg <- lookupGlobalName (nameText hn)
        st <- get
        pure $ mg >>= (`Map.lookup` csProjections st)
  e@EDot {} -> do
    mg <- staticGlobalExpr ctx e
    st <- get
    pure $ mg >>= (`Map.lookup` csProjections st)
  EAscription e _ _ -> projectionInfoOfExpr ctx e
  _ -> pure Nothing

-- | Does a projection-head application supply every declared binder?
projFullApp :: ProjInfo -> [Arg] -> Bool
projFullApp pj args =
  all isExpl args && length args == length (pjIsPlace pj) && or (pjIsPlace pj)
  where
    isExpl = \case
      ArgExplicit _ -> True
      _ -> False

-- | The accessor capabilities of a structural bundle record type
-- (§16.1.6): @Just [(field, roots, focus)]@ when every field is an
-- accessor descriptor.
bundleCapsM :: [(Text, Value)] -> CheckM (Maybe [(Text, Value, Value)])
bundleCapsM fs
  | null fs = pure Nothing
  | otherwise = do
      caps <- forM fs $ \(nm, tv) -> do
        t <- forceM tv
        pure $ case t of
          VGlobN (GName pm former) [(_, roots), (_, focus)]
            | pm == preludeModule
            , lookup nm capFormers == Just former ->
                Just (nm, roots, focus)
          _ -> Nothing
      pure (sequence caps)
  where
    capFormers = [("get", "Getter"), ("open", "Opener"), ("set", "Setter"), ("sink", "Sinker")]

-- | Syntactic stable-place check (§12.4.1 subset: variables and
-- record\/constructor field paths).
stablePlaceExpr :: Expr -> Bool
stablePlaceExpr = \case
  EVar _ -> True
  EDot e (DotName _) -> stablePlaceExpr e
  EAscription e _ _ -> stablePlaceExpr e
  _ -> False

mutableVarPlaceRoot :: Ctx -> Expr -> Maybe Name
mutableVarPlaceRoot ctx = \case
  EVar n ->
    if maybe False (isJust . ceVarInfo . snd) (lookupCtx (nameText n) ctx)
      then Just n
      else Nothing
  EDot e (DotName _) -> mutableVarPlaceRoot ctx e
  EAscription e _ _ -> mutableVarPlaceRoot ctx e
  _ -> Nothing

-- | Evidence synthesized while elaborating one application belongs to that
-- application's recovered Core. If the application is structurally invalid,
-- the recovery hole contains no use of newly synthesized dictionaries, so
-- retain only obligations that existed before both callee elaboration and
-- spine checking. Callers that infer the head themselves wrap the complete
-- operation in this scope; 'elabSpine' supplies the same invariant when given
-- an already checked head.
withApplicationEvidenceScope :: CheckM a -> CheckM a
withApplicationEvidenceScope action = do
  pending0 <- gets csPending
  diagCount0 <- gets (length . csDiags)
  result <- action
  diags <- gets csDiags
  let freshCount = max 0 (length diags - diagCount0)
      structurallyInvalid = any applicationShapeFailure (take freshCount diags)
  when structurallyInvalid $ do
    let preexisting = Set.fromList [mid | (mid, _, _, _, _) <- pending0]
    modify' $ \st ->
      let retainedPending =
            filter
              (\(mid, _, _, _, _) -> Set.member mid preexisting)
              (csPending st)
          retainedIds =
            Set.fromList [mid | (mid, _, _, _, _) <- retainedPending]
       in st
            { csPending = retainedPending
            , csPendingLevelEvidence =
                Map.restrictKeys (csPendingLevelEvidence st) retainedIds
            }
  pure result

-- | Compute connected pending-evidence components for a set of roots in one
-- indexed graph pass. Re-running 'pendingEvidenceComponentFromSeed' once per
-- numeric literal made declaration finalization quadratic on large generated
-- declarations. The graph here is the same semantic graph: an evidence node
-- is connected through unsolved metas in its checked goal and transitively
-- through those metas' creation-site classifiers.
pendingEvidenceComponentsFromRoots :: Set MetaId -> CheckM [Set MetaId]
pendingEvidenceComponentsFromRoots roots = do
  graph <- buildPendingEvidenceGraph
  let componentFrom root =
        pendingEvidenceComponentIn graph (Set.singleton root)
      collect remaining
        | Set.null remaining = []
        | otherwise =
            let root = Set.findMin remaining
                component = componentFrom root
             in component : collect (Set.difference remaining component)
  pure (collect (Set.intersection roots (pegPendingIds graph)))

pendingEntryIsNumericLiteral :: PendingEvidenceEntry -> CheckM Bool
pendingEntryIsNumericLiteral entry =
  refreshPendingEntry entry >>= \case
    VGlobN trait _
      | trait == gPrel traitFromInteger
          || trait == gPrel traitFromFloat ->
          pure True
    VGlobI trait _ _
      | trait == gPrel traitFromInteger
          || trait == gPrel traitFromFloat ->
          pure True
    _ -> pure False

-- | A rigid semantic trait argument is an ordinary instance-search input, not
-- a guess from the ambient instance set.  It may therefore anchor bounded
-- complete-component improvement.  For example,
-- @Contains (NumericRange ?a) Nat@ has a rigid second argument that rules out
-- the Integer instance and yields one principal assignment for @?a@.  Goals
-- such as @FromInteger ?a@ or @Sized ?a@ have no such anchor and remain
-- subject to the normal defaulting/ambiguity boundary.
pendingEntryHasRigidSemanticArgument
  :: PendingEvidenceEntry
  -> CheckM Bool
pendingEntryHasRigidSemanticArgument entry =
  refreshPendingEntry entry >>= \case
    VGlobI trait _ arguments -> do
      state <- get
      pure $ case traitSemanticSpineIn state trait arguments of
        Nothing -> False
        Just semanticArguments ->
          any
            ( \(_, argument) ->
                null
                  ( unsolvedMetasOf
                      state
                      ( quote
                          (ecOf state)
                          (ctxLen (pendingEntryCtx entry))
                          argument
                      )
                  )
            )
            semanticArguments
    _ -> pure False

-- | Does a pending goal depend on an authenticated associated static member
-- of another evidence placeholder? This is the typed dependency that permits
-- complete-component improvement before numeric defaulting. A mere pair of
-- ordinary goals such as @FromInteger ?a@ and @Sized ?a@ has no such edge and
-- must not let the currently imported instance set choose @?a@.
pendingEntryUsesAssociatedEvidenceProjection
  :: PendingEvidenceEntry
  -> CheckM Bool
pendingEntryUsesAssociatedEvidenceProjection (_, goal, _, pendingCtx, _) = do
  goalTerm <-
    quoteIn pendingCtx goal >>= zonkTermM (ctxLen pendingCtx)
  state <- get
  pure
    ( getAny
        (foldTerm (projectionNode state) (const mempty) goalTerm)
    )
  where
    projectionNode state = \case
      CProjM _ receiver field ->
        Any (authenticatedAssociatedMember state receiver field)
      CProjAtM _ receiver field _ ->
        Any (authenticatedAssociatedMember state receiver field)
      _ -> mempty

    authenticatedAssociatedMember state receiver field =
      isJust $ do
        evidenceMeta <- case stripIdentityWrappers receiver of
          CMeta meta -> Just meta
          _ -> Nothing
        classifier <- Map.lookup evidenceMeta (csMetaClassifiers state)
        trait <- termHeadGlob (stripIdentityWrappers (micType classifier))
        traitInfo <- Map.lookup trait (csTraits state)
        guard (field `Set.member` tiAssociatedStaticMembers traitInfo)

applicationShapeFailure :: Diagnostic -> Bool
applicationShapeFailure diagnostic =
  dCode diagnostic
    `elem`
      [ "E_APPLICATION_NONCALLABLE"
      , "E_APPLICATION_ARGUMENT_MISMATCH"
      , "E_CONSTRUCTOR_ARITY_MISMATCH"
      , "E_NAMED_ARG_MISSING"
      , "E_NAMED_ARG_DUPLICATE"
      , "E_NAMED_ARG_UNKNOWN"
      ]

-- | Reify the canonical semantic identity of the standard Nat operation at
-- the point where its selected evidence is still explicit in Core. This is
-- not arithmetic conversion: it only replaces a fully applied method call
-- whose exact Add-Nat dictionary is the authenticated prelude instance with
-- the source definition that instance delegates to. User dictionaries,
-- partial calls, and every other carrier are preserved verbatim.
canonicalizeSelectedNatOperation :: Ctx -> Term -> CheckM Term
canonicalizeSelectedNatOperation ctx application = do
  finalized <- zonkTermM (ctxLen ctx) application
  instances <- gets csInstances
  pure (fromMaybe application (canonicalStandardBinaryOperation instances finalized))

-- | Canonicalize only the two explicit endpoints of a checked equality goal.
-- The bounded transparent reducer deliberately does not descend through
-- arbitrary application operands: doing so would force unrelated user calls.
-- Equality endpoints are different because their complete standard-equality
-- spine has already authenticated both positions as proof-relevant terms.
-- Rebuilding preserves every implicit carrier/evidence argument verbatim.
canonicalizeEqualityGoalUnderCheckedBranchFacts
  :: Ctx
  -> Term
  -> CheckM Term
canonicalizeEqualityGoalUnderCheckedBranchFacts ctx goal =
  canonicalizeEqualityGoalWith
    (canonicalizeTermsUnderCheckedBranchFacts ctx)
    goal

canonicalizeEqualityGoalUnderCheckedBranchFactsOnly
  :: Ctx
  -> Term
  -> CheckM Term
canonicalizeEqualityGoalUnderCheckedBranchFactsOnly ctx goal =
  canonicalizeEqualityGoalWith
    (canonicalizeTermsUnderCheckedBranchFactsOnly ctx)
    goal

canonicalizeEqualityGoalWith
  :: ([Term] -> CheckM [Term])
  -> Term
  -> CheckM Term
canonicalizeEqualityGoalWith canonicalize goal =
  case equalityExplicitEndpoints goal of
    Nothing -> pure goal
    Just (left, right) ->
      canonicalize [left, right] >>= \case
        [left', right'] ->
          pure (replaceLastTwoExplicitArguments left' right' goal)
        _ -> pure goal

replaceLastTwoExplicitArguments :: Term -> Term -> Term -> Term
replaceLastTwoExplicitArguments left right goal =
  let (headTerm, arguments) = spineOfTerm goal
      explicitCount = length [() | (Expl, _) <- arguments]
      replace index = \case
        (Expl, _)
          | index == explicitCount - 2 -> (Expl, left)
          | index == explicitCount - 1 -> (Expl, right)
        argument -> argument
      (_, arguments') =
        List.mapAccumL
          (\index argument ->
             (index + if fst argument == Expl then 1 else 0, replace index argument))
          0
          arguments
   in List.foldl'
        (\function (icit, argument) -> CApp icit function argument)
        headTerm
        arguments'

canonicalizeTermsUnderCheckedBranchFactsOnly
  :: Ctx
  -> [Term]
  -> CheckM [Term]
canonicalizeTermsUnderCheckedBranchFactsOnly =
  canonicalizeTermsUnderBranchFactsWith 24 normalizeBoolFacts id

-- | Whether a (possibly applied) callee term is headed by the §28.2
-- 'unsafeAssertProof' escape or its '__unsafeAssertProof' primitive.  Used to
-- provenance-gate the special handling of its erased 'reason : String' binder.
isUnsafeAssertProofHead :: Term -> Bool
isUnsafeAssertProofHead = go
  where
    go = \case
      CApp _ f _ -> go f
      CGlob g ->
        g == GName preludeModule "unsafeAssertProof"
          || g == GName preludeModule "__unsafeAssertProof"
      _ -> False

-- | The primitive equality eliminators are the only ordinary functions whose
-- checked operational contract permits an occurrence-local proof-erasure
-- decision without changing their calling convention. Authenticate both the
-- resolved global and its source-telescope position. The proof classifier is
-- handled separately after application planning has specialized it.
runtimeSafeApplicationArgumentPosition :: Term -> [Icit] -> Bool
runtimeSafeApplicationArgumentPosition function argumentIcities =
  case termHeadGlob function of
    Just global
      | global == prelSubst ->
          length argumentIcities >= 4
            && all (== Impl) argumentIcities
      | global == prelPathInd ->
          length argumentIcities >= 5
            && let (generatedPrefix, sourcePrefix) =
                     splitAt (length argumentIcities - 5) argumentIcities
                in all (== Impl) generatedPrefix
                     && sourcePrefix == [Impl, Impl, Impl, Expl, Impl]
    _ -> False

-- | A flexible application headed by a provisional declaration binder creates
-- a transient generated Pi. Its domain mode cannot be selected until the
-- argument's own classifier has been solved by the complete declaration.
-- Finalization rewrites this origin to the ordinary source-interface origin;
-- non-provisional inference retains the historical source-written contract.
flexApplicationBinderOrigin :: Ctx -> Term -> BinderOrigin
flexApplicationBinderOrigin ctx function =
  case fst (spineOfTerm function) of
    CVar index
      | Just entry <- listToMaybe (drop index (ctxEntries ctx))
      , ceModeProvisional entry || ceImplicitLocal entry && isDirectFlex (ceType entry) -> BinderGenerated
    _ -> BinderSourceWritten
  where
    isDirectFlex = \case
      VFlex _ [] -> True
      _ -> False
