-- | Implicit arguments and trait-evidence resolution (Spec §16.3.3).
--
-- Support for the resolution ladder: local implicit context first, then
-- global instance search, then boolean-proposition normalization for
-- @(lhs = rhs)@ goals decided by conversion.
--
-- Carved out of "Kappa.Check" as part of splitting that module; see
-- "Kappa.Check.Types" for the shared data dictionary and docs\/CONCEPTS.md
-- for the vocabulary these assume.
module Kappa.Check.Implicits
  ( aliasRhsObservation
  , arithmeticAssumptionFactsForDomain
  , arithmeticAssumptionFormulasForDomain
  , arithmeticFactForDomain
  , arithmeticFormulaForDomain
  , arithmeticFormulaReplayTerm
  , arithmeticFormulaVariables
  , arithmeticRigidFactsForDomain
  , arithmeticSemanticsForDomain
  , arithmeticVariableBelongsToDomain
  , branchFactTruthAt
  , checkDeclaredOrdinaryResultObservation
  , conversionDependsOnDiagnosedEvidence
  , ctxArithmeticVariables
  , currentPrincipalLevelAssignmentsFor
  , dictValuePending
  , emitUnsolvedGoal
  , equalityFromCheckedBranchFacts
  , evidenceUniquenessDependencyBlocked
  , exactBoolFacts
  , goalHasFlex
  , goalHasUniverseFlex
  , instanceDeclSite
  , instanceRelateds
  , isAssociatedStaticMemberType
  , isEqGoal
  , isFlexV
  , isLocalEvidenceCandidate
  , isRowGoal
  , localProjectionLevel
  , localProjectionLevelAt
  , localProjectionValueLevel
  , lookupClosedEvidence
  , naturalCoreOfArithmeticExpression
  , nonImprovingFlexibleCandidate
  , normalizeArithmeticCertificateGoal
  , normalizeArithmeticCertificateTerm
  , normalizeArithmeticPredicateTerm
  , normalizeBranchConditionTerm
  , pendingEvidenceComponent
  , pendingEvidenceComponentTerms
  , pendingEvidenceRetryIds
  , pendingProofRelevantMetas
  , propDecisionKey
  , proveBoolTermFromBranchFacts
  , proveBoolValueFromBranchFacts
  , providerLawArguments
  , prunePendingEvidenceAttempts
  , recordPendingEvidenceAttempt
  , registerDiscardedResult
  , rememberClosedEvidence
  , reopenSolvedPendingMeta
  , resolveDeclaredResultObservation
  , resolveLetObservation
  , retirePendingLevelEvidence
  , rowProof
  , selectedEqConditionEndpoints
  , selectedEqOperation
  , standardProofNormalizationProviders
  , typeLevelCertificateProviders
  , valueArithmeticCertificateProviders
  , withCapturedBoolFacts
  , withCapturedBranchFacts
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

maxEvidenceCacheEntries :: Int
maxEvidenceCacheEntries = 4096

-- | Exact semantic-identity guard for the forbidden self-coherence edge in an
-- independent evidence-uniqueness certificate.  This is intentionally not a
-- spelling test: the fully checked trait head is compared with the active
-- declaration identities.
evidenceUniquenessDependencyBlocked :: Value -> CheckM Bool
evidenceUniquenessDependencyBlocked evidenceType = do
  active <- gets csEvidenceUniquenessStack
  forceM evidenceType >>= \case
    VGlobI trait _ _ -> pure (trait `elem` active)
    _ -> pure False

-- | §11.1.6/§14.2.1 compile-time member classification. This is deliberately
-- broader than 'isParametricKind': a predicate such as
-- @(n : Nat) -> Type@ is not a v1 parametric kind, but its fully applied
-- result is compile-time and therefore it is a valid associated static
-- member. Exact checked global identities classify the intrinsic static
-- carriers; function spaces inherit the classification from their eventual
-- result.
isAssociatedStaticMemberType :: Int -> Value -> CheckM Bool
isAssociatedStaticMemberType lvl value =
  forceM value >>= \case
    VSort {} -> pure True
    VPi _ _ _ _ _ codomain -> do
      result <- clApp codomain (VRigid lvl [])
      isAssociatedStaticMemberType (lvl + 1) result
    VUniverseLift _ _ _ inner ->
      isAssociatedStaticMemberType lvl inner
    VGlobN global _ ->
      pure (global `Set.member` associatedStaticCarrierIdentities)
    _ -> pure False
  where
    associatedStaticCarrierIdentities =
      Set.fromList associatedStaticCarrierGlobals

aliasRhsObservation :: Ctx -> Text -> Term -> Value -> CheckM ObservationJudgment
aliasRhsObservation ctx aliasOrigin term classifier = do
  observation <- go ctx term classifier
  pure observation {ojOrigin = if ojMode observation == Parametric then aliasOrigin else ojOrigin observation}
  where
    -- A type alias exports the observation facet of its result, not the
    -- closed dependency set of the eta-expanded function value used to
    -- implement its source parameters.  Keep those parameters in scope while
    -- checking the terminal body so a transparent alias such as
    -- @type Keep (0 T : Type) = T@ retains T's parametric origin in the
    -- interface summary.  Ordinary application still uses the shared
    -- dependency calculus at each call site.
    go current (CLamM actualMode actualIcit quantity name body) ty =
      forceM ty >>= \case
        VPiM expectedMode expectedIcit _ borrowed _ domain closure
          | actualMode == expectedMode
          , actualIcit == expectedIcit -> do
              let rigid = VRigid (ctxLen current) []
                  current' =
                    bindCtxMQB actualMode quantity name (actualIcit == Impl) borrowed domain current
              result <- clApp closure rigid
              go current' body result
        _ -> observationJudgmentForTerm current (CLamM actualMode actualIcit quantity name body) ty
    go current body ty = observationJudgmentForTerm current body ty

-- | Resolve an independently source-prefixed let binding. The RHS judgment is
-- structural; an explicit ordinary prefix is an ordinary sink, while an
-- explicit parametric prefix is legal only for a parametric-kind classifier.
-- Quantity is intentionally absent from this decision (§12.1.1).
resolveLetObservation :: Ctx -> Span -> BinderPrefix -> Value -> ObservationJudgment -> CheckM ObservationJudgment
resolveLetObservation ctx sp prefix classifier inferred =
  case bpObservation prefix of
    Nothing -> pure inferred
    Just Ordinary -> do
      when (ojMode inferred == Parametric) $
        reportParametricPromotion sp "ordinary let binding" inferred
      observationForBinding Ordinary (ojOrigin inferred) classifier
    Just Parametric -> observationForBinding Parametric (ojOrigin inferred) classifier

-- | A declared universe-valued result also determines the exported global
-- facet. Runtime-result contracts are checked after traversing the leading
-- lambda telescope by the finalized-Core observation validator; they must not
-- overwrite the mode of the whole function value here. This is distinct from
-- an unannotated local alias, which infers and preserves its RHS facet.
resolveDeclaredResultObservation
  :: Ctx
  -> Span
  -> BinderPrefix
  -> Bool
  -> Value
  -> ObservationJudgment
  -> CheckM ObservationJudgment
resolveDeclaredResultObservation ctx sp prefix hasDeclaredResult classifier inferred = do
  typeProducing <- finalIsSort ctx classifier
  if hasDeclaredResult && typeProducing && isNothing (bpObservation prefix)
    then observationForBinding Ordinary "declared-ordinary-type-code-result" classifier
    else resolveLetObservation ctx sp prefix classifier inferred

-- | Check the terminal result of a source-declared function telescope at the
-- elaboration boundary.  The mode of the function value itself is not the
-- mode of its result: after pairing each Core lambda with its checked Pi, a
-- terminal @Type@ result is an ordinary observation sink.  Performing this
-- check here gives the source diagnostic once and prevents later level-scope
-- recovery from obscuring a genuine parametric-promotion error.
checkDeclaredOrdinaryResultObservation :: Span -> Term -> Value -> CheckM ()
checkDeclaredOrdinaryResultObservation site = go emptyCtx
  where
    go ctx term expected = case term of
      CLamM actualMode actualIcit quantity name body ->
        forceM expected >>= \case
          VPiBoundM expectedMode expectedIcit _ borrowed expectedName assumption domain closure
            | actualMode == expectedMode
            , actualIcit == expectedIcit -> do
                withAssumption <- extendLevelAssumption site ctx assumption
                let rigid = VRigid (ctxLen ctx) []
                    ctx' =
                      bindCtxMQB
                        actualMode quantity
                        (if name == "_" then expectedName else name)
                        (actualIcit == Impl) borrowed domain withAssumption
                codomain <- clApp closure rigid
                go ctx' body codomain
          _ -> pure ()
      _ -> do
        typeProducing <- finalIsSort ctx expected
        when typeProducing $ do
          observation <- observationJudgmentForTerm ctx term expected
          when (ojMode observation == Parametric) $
            reportParametricPromotion site "declared ordinary type-code result" observation

-- | Whether a local context entry participates in §16.3.3's first search
-- tier. Besides source implicit binders, an explicit local root is eligible
-- exactly when its elaborated type is authenticated trait evidence. Global
-- bindings never enter 'Ctx', so this does not turn imported declarations
-- into ambient instances.
isLocalEvidenceCandidate :: CtxEntry -> CheckM Bool
isLocalEvidenceCandidate entry
  | ceImplicitLocal entry = pure True
  | otherwise = isTraitGoal (ceType entry)

goalHasFlex :: Value -> CheckM Bool
goalHasFlex value = not . null <$> unsolvedMetaIdsIn value

-- | A checked evidence goal with a residual universe occurrence is no more
-- rigid than one with a residual term meta.  In particular, searching for
-- @Trait.{?u} a@ before the enclosing application has contributed and
-- principalized @a : Type ?u@ can reject the unique declaration instance at
-- the wrong occurrence level.  Keep the two notions separate because term
-- metas and level metas have distinct solvers, but feed either kind of
-- flexibility into the one generic postponed-evidence queue.
goalHasUniverseFlex :: Ctx -> Value -> CheckM Bool
goalHasUniverseFlex ctx value = do
  state <- get
  let assignments = csLevelAssignments state
      term =
        zonkLevels assignments
          (quote (ecOf state) (ctxLen ctx) value)
  pure (not (null (levelMetasOfTerm term)))

pendingEvidenceRetryIds :: Bool -> CheckM (Set MetaId)
pendingEvidenceRetryIds forceAll = do
  state <- get
  pure $
    Set.fromList
      [ peeMeta entry
      | entry <- csPending state
      , forceAll
          || maybe
               True
               (not . dependencySnapshotIsCurrent (pendingEvidenceDependencyVersion state))
               (Map.lookup (peeMeta entry) (csPendingEvidenceAttempts state))
      ]

recordPendingEvidenceAttempt
  :: MetaId
  -> Term
  -> [ScopedBoolFact]
  -> CheckM ()
recordPendingEvidenceAttempt evidence goal facts = do
  state <- get
  let factTerms = [term | ScopedBoolFact _ term _ <- facts]
      dependencies =
        Set.delete (PendingTermMeta evidence)
          (pendingEvidenceDependencies state (goal : factTerms))
      snapshot =
        captureDependencySnapshot
          (pendingEvidenceDependencyVersion state)
          dependencies
  modify' $ \next ->
    next
      { csPendingEvidenceAttempts =
          Map.insert evidence snapshot (csPendingEvidenceAttempts next)
      }

pendingEvidenceDependencies
  :: CheckState
  -> [Term]
  -> Set PendingEvidenceDependency
pendingEvidenceDependencies state roots =
  Set.unions
    [ Set.map PendingTermMeta termMetas
    , Set.map PendingLevelMeta levelMetas'
    , Set.map PendingGlobal globals
    ]
  where
    rootMetas = Set.fromList (concatMap metaIdsOf roots)
    termMetas = closeClassifierMetas rootMetas rootMetas
    classifierTerms =
      [ micType classifier
      | meta <- Set.toList termMetas
      , Just classifier <- [Map.lookup meta (csMetaClassifiers state)]
      ]
    allTerms = roots ++ classifierTerms
    levelMetas' = Set.fromList (concatMap levelMetasOfTerm allTerms)
    globals = Set.unions (map globalsOfTerm allTerms)

    closeClassifierMetas reached frontier
      | Set.null frontier = reached
      | otherwise =
          let discovered =
                Set.fromList
                  [ dependency
                  | meta <- Set.toList frontier
                  , Just classifier <- [Map.lookup meta (csMetaClassifiers state)]
                  , dependency <- metaIdsOf (micType classifier)
                  ]
              fresh = Set.difference discovered reached
           in closeClassifierMetas (Set.union reached fresh) fresh

pendingEvidenceDependencyVersion
  :: CheckState
  -> PendingEvidenceDependency
  -> PendingEvidenceDependencyVersion
pendingEvidenceDependencyVersion state = \case
  PendingTermMeta meta ->
    PendingTermMetaVersion
      (Map.findWithDefault 0 meta (csMetaAssignmentGenerations state))
  PendingLevelMeta meta ->
    PendingLevelMetaVersion (Map.lookup meta (csLevelAssignments state))
  PendingGlobal global ->
    PendingGlobalVersion
      ( fmap
          (\definition ->
             ( gdUniverses definition
             , gdCoreType definition
             , gdCoreBody definition
             , gdReducible definition
             ))
          (Map.lookup global (csGlobals state))
      )
      ( fmap
          (\constructor -> (ciUniverses constructor, ciType constructor))
          (Map.lookup global (csCtors state))
      )

prunePendingEvidenceAttempts :: CheckM ()
prunePendingEvidenceAttempts =
  modify' $ \state ->
    let live =
          Set.fromList (map peeMeta (csPending state))
     in state
          { csPendingEvidenceAttempts =
              Map.restrictKeys (csPendingEvidenceAttempts state) live
          }

-- | A pending evidence meta may be filled indirectly while a later dependent
-- argument is unified (for example through @?d.Ref@).  That structural
-- equation is useful for constraining the surrounding application, but it is
-- not evidence selection and does not authenticate the candidate's type.
-- Reopen the placeholder at the pending boundary and run the ordinary ladder
-- from its captured checked goal.  Any values that already refer to the meta
-- retain its stable identity and observe the newly checked solution.
reopenSolvedPendingMeta :: MetaId -> CheckM ()
reopenSolvedPendingMeta meta =
  modify' $ \state ->
    state
      { csMetas =
          Map.adjust (const Nothing) meta (csMetas state)
      , csSolvedMetas = Set.delete meta (csSolvedMetas state)
      }

-- | Keep the generated-level-evidence side table aligned with 'csPending'.
-- Once the corresponding term meta is solved or diagnosed, its authenticated
-- relation has either become ordinary evidence or ceased to be actionable;
-- retaining it would make a completed module look inference-incomplete and
-- keep the entire level-assignment history alive downstream.
retirePendingLevelEvidence :: MetaId -> CheckM ()
retirePendingLevelEvidence meta =
  modify' $ \st ->
    st
      { csPendingLevelEvidence =
          Map.delete meta (csPendingLevelEvidence st)
      , csPendingEvidenceAttempts =
          Map.delete meta (csPendingEvidenceAttempts st)
      }

-- | Find the connected component of postponed evidence that can block a
-- conversion involving the supplied values. Associated static members are
-- the motivating case: before its dictionary is selected,
-- @(?dictionary).Member@ cannot reduce far enough for conversion to inspect
-- the member result.
--
-- Connectivity is semantic, not source-name based. An evidence metavariable
-- is connected to every unsolved metavariable in its checked goal, and each
-- metavariable is connected to the unsolved metas in its creation-site
-- classifier. Taking the transitive closure also brings in numeric-literal
-- evidence sharing the carrier with a blocked trait goal. The caller can then
-- close exactly this component without committing unrelated declaration-wide
-- inference choices.
pendingEvidenceComponent :: Ctx -> [Value] -> CheckM (Set MetaId)
pendingEvidenceComponent ctx values = do
  st <- get
  ec <- ec_
  pendingEvidenceComponentFromSeed
    ctx
    ( Set.unions
        [ Set.fromList
            (unsolvedMetasOf st (quote ec (ctxLen ctx) value))
        | value <- values
        ]
    )

-- | A failed evidence search already owns the diagnostic for its exact
-- placeholder. Any conversion that still mentions that unsolved meta is
-- indeterminate recovery, not an independently established type mismatch.
-- This relation is structural and identity-based; unrelated errors and metas
-- solved after the root diagnostic are not suppressed.
conversionDependsOnDiagnosedEvidence :: Ctx -> [Value] -> CheckM Bool
conversionDependsOnDiagnosedEvidence ctx values = do
  state <- get
  evaluator <- ec_
  let dependencies =
        Set.unions
          [ Set.fromList
              ( unsolvedMetasOf
                  state
                  (quote evaluator (ctxLen ctx) value)
              )
          | value <- values
          ]
  pure
    ( not
        ( Set.disjoint
            dependencies
            (csDiagnosedPendingEvidence state)
        )
    )

-- | Term-preserving counterpart of 'pendingEvidenceComponent'. This is used
-- at proof-producing transport boundaries where NbE intentionally erases
-- proof arguments from semantic values, but the checked Core index still
-- contains the exact postponed evidence metavariable.
pendingEvidenceComponentTerms :: Ctx -> [Term] -> CheckM (Set MetaId)
pendingEvidenceComponentTerms ctx terms = do
  st <- get
  pendingEvidenceComponentFromSeed
    ctx
    ( Set.unions
        [Set.fromList (unsolvedMetasOf st term) | term <- terms]
    )

pendingEvidenceComponentFromSeed
  :: Ctx
  -> Set MetaId
  -> CheckM (Set MetaId)
pendingEvidenceComponentFromSeed _ rawSeed = do
  graph <- buildPendingEvidenceGraph
  pure (pendingEvidenceComponentIn graph rawSeed)

nonImprovingFlexibleCandidate
  :: Value
  -> CheckM (Maybe Term)
  -> CheckM (Maybe Term)
nonImprovingFlexibleCandidate goal search = do
  goalMetas <- unsolvedMetaIdsIn goal
  saved <- get
  found <- search
  after <- get
  let remainsUnsolved meta = case Map.lookup meta (csMetas after) of
        Just Nothing -> True
        _ -> False
  if isJust found && all remainsUnsolved goalMetas
    then pure found
    else put saved >> pure Nothing

-- | Replay the exact Boolean facts captured when a postponed obligation was
-- raised. The facts are lexical proof authority, so they are prepended only for
-- the duration of the proof-side action and never leak into later obligations.
withCapturedBoolFacts :: [ScopedBoolFact] -> CheckM a -> CheckM a
withCapturedBoolFacts captured action = do
  surrounding <- gets csBoolFacts
  modify' $ \state ->
    state {csBoolFacts = captured ++ surrounding}
  result <- action
  modify' $ \state ->
    state {csBoolFacts = surrounding}
  pure result

-- | Replay all exact branch-local proof authority captured by a postponed
-- obligation. Rigid constructor refinements and Boolean facts have the same
-- lexical lifetime, so retry must install and restore them as one scope.
withCapturedBranchFacts
  :: [ScopedBoolFact]
  -> Map RefinementSubject RigidFact
  -> CheckM a
  -> CheckM a
withCapturedBranchFacts capturedBool capturedRigid action = do
  surroundingBool <- gets csBoolFacts
  surroundingRigid <- gets csFacts
  modify' $ \state ->
    state
      { csBoolFacts = capturedBool ++ surroundingBool
      , csFacts = Map.union capturedRigid surroundingRigid
      }
  result <- action
  modify' $ \state ->
    state
      { csBoolFacts = surroundingBool
      , csFacts = surroundingRigid
      }
  pure result

-- | Compute the observable meta dependencies used only by the pending-goal
-- flexibility guard. Equality itself is opaque, so normalize its two checked
-- endpoints under the captured facts and retain every dependency outside those
-- endpoints unchanged. A selected projection may thereby discard erased proof
-- payloads containing unrelated evidence metas without hiding a flexible
-- carrier or operation head. Evidence is still synthesized against the
-- original checked goal by 'resolvePendingGoal'.
pendingProofRelevantMetas
  :: Ctx
  -> [ScopedBoolFact]
  -> Map RefinementSubject RigidFact
  -> Term
  -> CheckM ([MetaId], [LevelMeta])
pendingProofRelevantMetas ctx capturedBool capturedRigid goal = do
  stateBefore <- get
  let allOrdinary =
        Set.fromList (unsolvedMetasOf stateBefore goal)
      allLevels =
        Set.fromList (levelMetasOfTerm goal)
  case equalityExplicitEndpoints goal of
    Nothing -> pure (Set.toAscList allOrdinary, Set.toAscList allLevels)
    Just (left, right) -> do
      normalized <-
        withCapturedBranchFacts capturedBool capturedRigid $
          canonicalizeTermsUnderCheckedBranchFacts ctx [left, right]
      case normalized of
        [left', right'] -> do
          stateAfter <- get
          let originalEndpointOrdinary =
                Set.fromList
                  ( unsolvedMetasOf stateBefore left
                      ++ unsolvedMetasOf stateBefore right
                  )
              normalizedEndpointOrdinary =
                Set.fromList
                  ( unsolvedMetasOf stateAfter left'
                      ++ unsolvedMetasOf stateAfter right'
                  )
              originalEndpointLevels =
                Set.fromList
                  (levelMetasOfTerm left ++ levelMetasOfTerm right)
              normalizedEndpointLevels =
                Set.fromList
                  (levelMetasOfTerm left' ++ levelMetasOfTerm right')
              relevantOrdinary =
                Set.union
                  (Set.difference allOrdinary originalEndpointOrdinary)
                  normalizedEndpointOrdinary
              relevantLevels =
                Set.union
                  (Set.difference allLevels originalEndpointLevels)
                  normalizedEndpointLevels
          pure
            ( Set.toAscList relevantOrdinary
            , Set.toAscList relevantLevels
            )
        _ -> pure (Set.toAscList allOrdinary, Set.toAscList allLevels)

-- | Emit an unsolved-implicit goal failure, applying §3.1.11 single-cause
-- cascade suppression so one ill-typed expression yields one diagnostic.
--
-- Two cascade shapes collapse to a single root cause:
--
--   * The goal's carrier still mentions an unsolved metavariable that an
--     earlier same-span type-equality mismatch reported against (the
--     mismatch could not be decided precisely because this carrier was
--     never solved). The mismatch is the downstream consequence: drop it
--     and keep the more informative unsolved-goal diagnostic. (e.g. an
--     overloaded value-position member whose result carrier `?m a` fails
--     against the declared result type while its trait goal is unsolved.)
--
--   * The goal's carrier is fully concrete and is exactly the type that an
--     earlier mismatch already rejected at the same site (e.g. a numeric
--     trait goal `Mul T` raised for an operand whose type `T` already
--     failed to unify with the numeric domain). Here the goal is the
--     downstream consequence: suppress it and keep the mismatch.
emitUnsolvedGoal :: Ctx -> Span -> Value -> CheckM ()
emitUnsolvedGoal ctx sp g = do
  ec <- ec_
  let gT = quote ec (ctxLen ctx) g
      gRendered = renderTerm gT
  ms <- unsolvedMetaIdsIn g
  let -- §3.1.11: unsolved metavariables now render as the stable hole
      -- `_` (never a raw `?mN` solver id). A same-span type-equality
      -- mismatch whose rendered expected/actual carries that hole is the
      -- downstream consequence of this goal's unsolved carrier (the
      -- unification was blocked precisely because a metavariable here was
      -- never solved). The structural condition is the goal still has
      -- unsolved metas ('not (null ms)') and the mismatch shows a hole.
      mentionsMeta d = any noteHasHole (dNotes d)
      -- a standalone `_` token (the rendered unsolved hole) inside an
      -- expected:/actual: note, as opposed to `_` embedded in an
      -- identifier or a `(x : _)`-style binder
      noteHasHole note = "_" `elem` T.words (T.map spaceP note)
      spaceP c = if c `elem` ("():," :: String) then ' ' else c
      isMismatch d = dCode d == "E_TYPE_EQUALITY_MISMATCH"
      -- the goal's trait arguments, rendered (e.g. the carrier `T` of
      -- `Mul T`): a concrete carrier already named in a mismatch note
      carrierTexts = case gT of
        CApp _ _ _ -> [renderTerm a | a <- spineArgs gT]
        _ -> []
      spineArgs = reverse . go
        where
          go (CApp _ f a) = a : go f
          go _ = []
  ds <- gets csDiags
  let sameStart d = spanStart (dPrimary d) == spanStart sp
      isDownstreamMismatch d = isMismatch d && sameStart d && mentionsMeta d
      hasDownstreamMismatch = not (null ms) && any isDownstreamMismatch ds
      concreteCarrierAlreadyRejected =
        null ms
          && not (null carrierTexts)
          && any
            ( \d ->
                isMismatch d
                  && posLine (spanStart (dPrimary d)) == posLine (spanStart sp)
                  && any (\ct -> any (ct `T.isInfixOf`) (dNotes d)) carrierTexts
            )
            ds
      goalMsg = "could not resolve implicit argument of type " <> gRendered
      emit = errAt sp "E_UNSOLVED_IMPLICIT" (Just "kappa.implicit.unsolved") goalMsg
      summarize d =
        Suppressed (dCode d) (dFamily d) (dPrimary d) (dMessage d)
  if hasDownstreamMismatch
    then do
      -- §3.1.10/§3.1.11: drop the downstream same-span mismatch and keep
      -- the unsolved goal, recording the dropped mismatch in the survivor's
      -- 'suppressed' summary so tooling can still show it.
      let dropped = [summarize d | d <- ds, isDownstreamMismatch d]
      modify' $ \st -> st {csDiags = filter (not . isDownstreamMismatch) (csDiags st)}
      report $
        withSuppressed dropped $
          diag SevError StageElaborate "E_UNSOLVED_IMPLICIT" (Just "kappa.implicit.unsolved") sp goalMsg
    else
      if concreteCarrierAlreadyRejected
        then
          -- the goal is the cascade of an already-reported mismatch:
          -- record its summary on that surviving root mismatch (§3.1.11).
          modify' $ \st ->
            let supp = Suppressed "E_UNSOLVED_IMPLICIT" (Just "kappa.implicit.unsolved") sp goalMsg
                onLine d = isMismatch d && posLine (spanStart (dPrimary d)) == posLine (spanStart sp)
                -- attach to the first matching root mismatch only
                attachOnce [] = []
                attachOnce (d : rest)
                  | onLine d = withSuppressed [supp] d : rest
                  | otherwise = d : attachOnce rest
             in st {csDiags = attachOnce (csDiags st)}
        else emit

-- | Cache key for globally reusable implicit evidence.  The key is the exact
-- de-Bruijn Core shape, not pretty-printed prose.  A key is produced only for
-- closed goals, because local rigids make evidence context-sensitive.  The
-- semantic epoch is part of the key, so global/trait/instance changes cannot
-- reuse stale evidence even if a future state mutation forgets to clear the
-- map eagerly.
closedEvidenceKey :: Ctx -> Value -> CheckM (Maybe EvidenceCacheKey)
closedEvidenceKey ctx goal = do
  branchLocal <- gets (not . null . csBoolFacts)
  if branchLocal || any ceImplicitLocal (ctxEntries ctx)
    then pure Nothing
    else do
      ec <- ec_
      st <- get
      let gT = quote ec (ctxLen ctx) goal
      pure $
        if termClosed gT
            && null (levelMetasOfTerm gT)
            && termCacheUniverseScoped st gT
          then
            Just
              ( EvidenceCacheKey
                  (csActiveUniverseDefinition st)
                  (T.pack (show (csNormEpoch st)) <> "\x1e" <> renderStructuralTermKey gT)
              )
          else Nothing

lookupClosedEvidence :: Ctx -> Value -> CheckM (Maybe Term)
lookupClosedEvidence ctx goal = do
  mk <- closedEvidenceKey ctx goal
  case mk of
    Nothing -> pure Nothing
    Just k -> gets (Map.lookup k . csEvidenceCache)

rememberClosedEvidence :: Ctx -> Value -> Term -> CheckM ()
rememberClosedEvidence ctx goal tm = do
  -- Branch facts are proof sources (§3.2.3), not global theorems.  Reusing a
  -- proof found under `if c then ...` outside that branch would be unsound even
  -- when the goal term itself is closed.  Positive closed-evidence caching is
  -- therefore restricted to the empty branch-fact environment.
  branchLocal <- gets (not . null . csBoolFacts)
  unless branchLocal $ do
    mk <- closedEvidenceKey ctx goal
    forM_ mk $ \k ->
      do
        st <- get
        when
          ( termClosed tm
              && null (levelMetasOfTerm tm)
              && termCacheUniverseScoped st tm
          ) $
          modify' $ \state ->
            state
              { csEvidenceCache =
                  boundedInsert maxEvidenceCacheEntries k tm (csEvidenceCache state)
              }

registerDiscardedResult :: Ctx -> Span -> Value -> CheckM ()
registerDiscardedResult ctx sp ty =
  modify' $ \st ->
    st
      { csPendingDiscardedResults =
          PendingDiscardedResult sp ctx ty : csPendingDiscardedResults st
      }

isEqGoal :: Value -> CheckM Bool
isEqGoal v =
  forceM v >>= \case
    VGlobN g _ | g == prelEqType -> pure True
    VCtor g _ | g == prelEqType -> pure True
    _ -> pure False

-- | Is the goal one of the §11.3.1A intrinsic row traits (solved by
-- compiler-owned introduction rules, postponed while its row is flex)?
isRowGoal :: Value -> CheckM Bool
isRowGoal v =
  forceM v >>= \case
    VGlobN (GName pm "LacksRec") _ | pm == preludeModule -> pure True
    _ -> pure False

-- | §11.3.1A compiler-owned introduction rules: @LacksRec r l@ is
-- solvable iff the normalized row tail @r@ contains no label @l@ —
-- for a closed residual row, decided structurally on its fields.
rowProof :: Value -> CheckM (Maybe Term)
rowProof goal = do
  g <- forceM goal
  case g of
    VGlobI lacksRec [] [(_, rowV), (_, lblV)]
      | lacksRec == prelLacksRec -> do
          row <- forceM rowV
          lbl <- forceM lblV
          case (row, lbl) of
            (VGlobI closedRow [_] [(_, fieldsV)], VLit (LitStr l))
              | closedRow == prelClosedRow
              -> do
                  fsF <- forceM fieldsV
                  case fsF of
                    VRecordT fs
                      | l `notElem` map fst fs ->
                          pure (Just (CGlobal prelRowEvidence []))
                    _ -> pure Nothing
            _ -> pure Nothing
    _ -> pure Nothing

-- | Whether a forced value is an unsolved metavariable (a flexible head).
isFlexV :: Value -> Bool
isFlexV (VFlex _ _) = True
isFlexV _ = False

-- | Whether an instance dictionary's value is still pending (its
-- declaration's members have not been checked yet — the §14.3
-- pre-pass registers heads ahead of the body pass).
dictValuePending :: GName -> CheckM Bool
dictValuePending g = gets (maybe True (isNothing . gdValue) . Map.lookup g . csGlobals)

-- | §3.1.1A: the declaration site of an instance, recovered from the
-- §14.3 pre-pass table ('csPreInstances' is keyed by declaration span)
-- by its dictionary global. Returns Nothing for instances with no
-- pre-pass entry (built-in/imported).
instanceDeclSite :: GName -> CheckM (Maybe Span)
instanceDeclSite dictG = do
  pre <- gets csPreInstances
  pure $ listToMaybe [sp | (sp, Just pii) <- Map.toList pre, piDictG pii == dictG]

-- | §3.1.1A trait-coherence related origins: every surviving incoherent
-- instance's declaration site (those with a known pre-pass span).
instanceRelateds :: [InstanceEntry] -> CheckM [RelatedOrigin]
instanceRelateds ies = do
  sites <- mapM (instanceDeclSite . ieDict) ies
  pure
    [ related RoleInstanceDeclarationSite s "a matching instance is declared here"
    | Just s <- sites
    ]

-- | Decide an ordinary equality after reducing both endpoints under the exact
-- checked facts of the current branch. This is proof synthesis, not a new
-- definitional-equality rule: the caller emits an explicit equality
-- introduction only after this local judgment succeeds.
equalityFromCheckedBranchFacts
  :: Ctx
  -> Maybe Term
  -> Value
  -> Value
  -> CheckM Bool
equalityFromCheckedBranchFacts ctx sourceGoal lhs rhs = do
  booleanFacts <- gets csBoolFacts
  rigidFacts <- gets csFacts
  if null booleanFacts && Map.null rigidFacts
    then pure False
    else do
      let depth = ctxLen ctx
      sourceEndpoints <-
        case sourceGoal of
          Nothing -> pure Nothing
          Just goalTerm ->
            equalityExplicitEndpoints <$> zonkTermM depth goalTerm
      (lhsTerm, rhsTerm) <-
        case sourceEndpoints of
          Just endpoints -> pure endpoints
          Nothing ->
            (,) <$> (quoteIn ctx lhs >>= zonkTermM depth)
                <*> (quoteIn ctx rhs >>= zonkTermM depth)
      normalized <-
        canonicalizeTermsUnderExactCheckedBranchFacts
          ctx
          [lhsTerm, rhsTerm]
      case normalized of
        [lhsNormalized, rhsNormalized] -> do
          evaluation <- ec_
          lhsValue <- evalIn ctx lhsNormalized
          rhsValue <- evalIn ctx rhsNormalized
          let solved =
                convertible
                  evaluation
                  depth
                  (force evaluation lhsValue)
                  (force evaluation rhsValue)
          pure solved
        _ -> pure False

-- | Decode one checked application of the standard @Eq.==@ member. Source
-- spelling only narrows candidates: callers must authenticate each returned
-- dictionary against @Eq carrier@ with 'knownTraitMemberProjection' before
-- using a law. The direct accessor ABI carries the carrier explicitly;
-- projected forms retain no independently recoverable carrier here and are
-- therefore returned only to callers that already know it.
selectedEqOperation
  :: Term
  -> Maybe (Term, Term, [(Maybe Term, Term)])
selectedEqOperation condition = do
  let (headTerm, arguments) =
        spineOfTerm (stripIdentityWrappers condition)
      explicitArguments =
        [ argument
        | (Expl, argument) <- arguments
        ]
  (leftTerm, rightTerm) <- last2 explicitArguments
  dictionaries <-
    case stripIdentityWrappers headTerm of
      CProjM _ dictionary member
        | member == "==" ->
            Just [(Nothing, dictionary)]
      CProjAtM _ dictionary member _
        | member == "==" ->
            Just [(Nothing, dictionary)]
      globalHead
        | termHeadGlob globalHead
            `elem`
              [ Just (gPrel "==")
              , Just (memberGlobal (gPrel "Eq") "==")
              ]
        , sourceCarrier : dictionary : _ <-
            [argument | (Impl, argument) <- arguments] ->
            Just [(Just sourceCarrier, dictionary)]
      _ -> Nothing
  guard (not (null dictionaries))
  pure (leftTerm, rightTerm, dictionaries)

-- | Reconstruct the total affine Nat fragment admitted by
-- 'derivePrincipalAffineSubstitution'. Variable identities are de Bruijn
-- levels, so this inverse is exact at the current context depth.
naturalCoreOfArithmeticExpression :: Int -> AExpr -> Maybe Term
naturalCoreOfArithmeticExpression depth = \case
  AConst value
    | value >= 0 -> Just (CLit (LitInt value))
  AVar level
    | level >= 0
    , level < depth ->
        Just (CVar (depth - 1 - level))
  AScale coefficient expression
    | coefficient >= 0 -> do
        expression' <- naturalCoreOfArithmeticExpression depth expression
        pure
          ( case coefficient of
              0 -> CLit (LitInt 0)
              1 -> expression'
              _ ->
                CApp Expl
                  (CApp Expl (CGlob prelNatMultiply) (CLit (LitInt coefficient)))
                  expression'
          )
  AAdd lhs rhs ->
    CApp Expl . CApp Expl (CGlob prelNatAdd)
      <$> naturalCoreOfArithmeticExpression depth lhs
      <*> naturalCoreOfArithmeticExpression depth rhs
  _ -> Nothing

-- | Reify branch-local dependent-match equalities into the same arithmetic
-- fact language used by checked certificates.  A rigid fact is admitted only
-- when the lexical binder has the selected arithmetic classifier and the
-- replacement itself is recognized through the exact operation identities for
-- that domain.  Negative constructor facts and unrelated refinements remain
-- conversion-only information.
arithmeticRigidFactsForDomain
  :: Ctx
  -> ArithmeticDomain
  -> [(Int, ArithmeticVariableKind)]
  -> CheckM [AFact]
arithmeticRigidFactsForDomain ctx domain variables = do
  let depth = ctxLen ctx
  facts <- gets csFacts
  fmap catMaybes . forM variables $ \(level, kind) ->
    if arithmeticVariableBelongsToDomain domain kind
      then
        case Map.lookup (RefinementRigid level) facts of
          Just (FactIs replacement) -> do
            replacementTerm <- quoteIn ctx replacement >>= zonkTermM depth
            normalized <-
              normalizeArithmeticCertificateTerm depth replacementTerm
            expression <-
              selectedArithmeticExpression domain depth normalized
            pure (AFact ACmpEq (AVar level) <$> expression)
          _ -> pure Nothing
      else pure Nothing

-- | Standard-library provider interface.  Every identity is the resolved
-- object identity installed by the authenticated embedded prelude.  More
-- theory kinds extend this table without adding source-name recognition to
-- the generic provider engine.
standardProofNormalizationProviders :: [ProofNormalizationProvider]
standardProofNormalizationProviders =
  [ additiveMonoidProvider
      "std.prelude.provider.additive-monoid.left-identity"
      ProviderLeftIdentity
      "addLeftIdentity"
  , additiveMonoidProvider
      "std.prelude.provider.additive-monoid.right-identity"
      ProviderRightIdentity
      "addRightIdentity"
  , ProofNormalizationProvider
      { pnpIdentity = "std.prelude.provider.commutative-additive-monoid"
      , pnpTheory = ArithmeticCommutativeMonoid
      , pnpLawRole = ProviderCommutative
      , pnpOperationIdentities =
          [ prelAddOp
          , prelAddMethod
          , prelNatAdd
          , memberGlobal prelAdd "add"
          ]
      , pnpEvidenceTrait = gPrel "CommutativeAdditiveMonoid"
      , pnpLawOwner = gPrel "CommutativeAdditiveMonoid"
      , pnpLawField = "addCommutative"
      , pnpLawIdentity =
          memberGlobal
            (gPrel "CommutativeAdditiveMonoid")
            "addCommutative"
      , pnpNormalFormVersion = 1
      , pnpProviderVersion = 1
      , pnpCheckerVersion = 1
      }
  ]
  where
    additiveMonoidProvider identity role field =
      ProofNormalizationProvider
        { pnpIdentity = identity
        , pnpTheory = ArithmeticMonoid
        , pnpLawRole = role
        , pnpOperationIdentities =
            [ prelAddOp
            , prelAddMethod
            , prelNatAdd
            , memberGlobal prelAdd "add"
            ]
        , pnpEvidenceTrait = gPrel "AdditiveMonoid"
        , pnpLawOwner = gPrel "AdditiveMonoid"
        , pnpLawField = field
        , pnpLawIdentity = memberGlobal (gPrel "AdditiveMonoid") field
        , pnpNormalFormVersion = 1
        , pnpProviderVersion = 1
        , pnpCheckerVersion = 1
        }

-- | Match the operation application named by the authenticated provider and
-- extract exactly the arguments demanded by its law role. The instantiated
-- member type is still checked against the complete equality goal, so merely
-- resembling an identity or commutativity law grants no authority.
providerLawArguments
  :: ProofNormalizationProvider
  -> Term
  -> Maybe [Term]
providerLawArguments provider application =
  case spineOfTerm (stripIdentityWrappers application) of
    (headTerm, arguments)
      | Just operation <- termHeadGlob (stripIdentityWrappers headTerm)
      , operation `elem` pnpOperationIdentities provider
      , Just (left, right) <-
          last2 [argument | (Expl, argument) <- arguments] ->
          Just $ case pnpLawRole provider of
            ProviderLeftIdentity -> [right]
            ProviderRightIdentity -> [left]
            ProviderCommutative -> [left, right]
    _ -> Nothing

typeLevelCertificateProviders
  :: [Term]
  -> CheckM [ArithmeticProviderEvidence Term]
typeLevelCertificateProviders roots = do
  let candidates =
        nub
          [ (trait, dictionary)
          | root <- roots
          , (trait, dictionary) <-
              foldTerm providerCandidate (const []) root
          ]
  fmap catMaybes . forM candidates $ \(trait, dictionary) -> do
    standard <- standardTypeLevelDictionary trait dictionary
    pure
      ( if standard
          then Just (ArithmeticProviderEvidence Nothing trait dictionary)
          else Nothing
      )
  where
    providerCandidate term =
      case spineOfTerm (stripIdentityWrappers term) of
        (headTerm, arguments)
          | Just operation <- termHeadGlob (stripIdentityWrappers headTerm)
          , Just trait <- Map.lookup operation providerTraits
          , _carrier : dictionary : _ <-
              [argument | (Impl, argument) <- arguments] ->
              [(trait, dictionary)]
        _ -> []

    providerTraits =
      Map.fromList
        [ (gPrel "<", gPrel "Ord")
        , (gPrel "<=", gPrel "Ord")
        , (gPrel "add", gPrel "Add")
        , (gPrel "max", gPrel "Max")
        , (gPrel "succ", gPrel "Successor")
        , (gPrel "fromInteger", gPrel "FromInteger")
        ]

normalizeArithmeticCertificateTerm :: Int -> Term -> CheckM Term
normalizeArithmeticCertificateTerm depth term = do
  -- Certificate payloads cross the independent KCore boundary. Normalize the
  -- already checked source term all the way to canonical Core operations so
  -- replay does not depend on a source-level trait wrapper or dictionary
  -- spelling. Partial-operation domains are rechecked from the recorded
  -- assumptions by the arithmetic kernel; normalization grants no authority.
  finalized <- zonkTermM depth term
  instances <- gets csInstances
  pure
    ( simplifyDecisionTermAt depth
        (canonicalizeStandardArithmeticOperations instances finalized)
    )

-- | Put the arithmetic endpoints of a certificate goal into a definitionally
-- equal, bounded transparent normal form before they cross the KCore trust
-- boundary. This exposes ordinary transparent predicates and helpers to the
-- small portable arithmetic language without teaching KCore about generated
-- dictionaries or local definitions. Authenticated arithmetic heads remain
-- opaque and only their operands are normalized.
normalizeArithmeticCertificateGoal :: Int -> Term -> CheckM Term
normalizeArithmeticCertificateGoal depth rawGoal = do
  goal <- normalizeArithmeticCertificateTerm depth rawGoal
  case certificateGoalEndpoints goal of
    Nothing -> pure goal
    Just (GoalBooleanPredicate predicate) -> do
      reduced <- normalizeArithmeticPredicateTerm depth 24 predicate
      normalizeArithmeticCertificateTerm
        depth
        (replaceExplicitSubterm predicate reduced goal)
    Just (GoalArithmeticEquality lhs rhs) -> do
      lhs' <- normalizeArithmeticOperandTerm depth 24 lhs
      rhs' <- normalizeArithmeticOperandTerm depth 24 rhs
      normalizeArithmeticCertificateTerm
        depth
        ( replaceExplicitSubterm
            rhs
            rhs'
            (replaceExplicitSubterm lhs lhs' goal)
        )
  where
    certificateGoalEndpoints candidate =
      case spineOfTerm (stripIdentityWrappers candidate) of
        (headTerm, arguments)
          | termHeadGlob (stripIdentityWrappers headTerm) == Just prelEqType
          , carrier : _ <- [argument | (Impl, argument) <- arguments]
          , Just (lhs, rhs) <-
              last2 [argument | (Expl, argument) <- arguments] ->
              if isBoolType carrier
                then case (isTrueTerm lhs, isTrueTerm rhs) of
                  (False, True) -> Just (GoalBooleanPredicate lhs)
                  (True, False) -> Just (GoalBooleanPredicate rhs)
                  _ -> Nothing
                else case arithmeticDomainForCarrier carrier of
                  Just ArithmeticNatural ->
                    Just (GoalArithmeticEquality lhs rhs)
                  Just ArithmeticInteger ->
                    Just (GoalArithmeticEquality lhs rhs)
                  _ -> Nothing
        _ -> Nothing

    replaceExplicitSubterm target replacement = \case
      CUniverseLift lower upper evidence inner ->
        CUniverseLift
          lower
          upper
          evidence
          (replaceExplicitSubterm target replacement inner)
      CSchemaLift family source targetLevel roles roleEvidence certificate sourceArguments targetArguments inner ->
        CSchemaLift
          family
          source
          targetLevel
          roles
          roleEvidence
          certificate
          sourceArguments
          targetArguments
          (replaceExplicitSubterm target replacement inner)
      candidate ->
        let (headTerm, arguments) = spineOfTerm candidate
         in List.foldl'
              (\function (icit, argument) ->
                CApp
                  icit
                  function
                  ( if icit == Expl && argument == target
                      then replacement
                      else argument
                  ))
              headTerm
              arguments

    isBoolType candidate =
      termHeadGlob (stripIdentityWrappers candidate) == Just prelBool

    isTrueTerm = \case
      CCtor constructor _ [] -> constructor == prelTrue
      CCtorI constructor _ _ [] -> constructor == prelTrue
      _ -> False

-- | Canonicalize the value operands of an already-authenticated arithmetic
-- predicate before it crosses the KCore boundary.  The independent verifier
-- has stable primitive identities but deliberately does not have permission
-- to unfold arbitrary source definitions.  Bounded delta/beta reduction here
-- therefore exposes transparent helpers such as @natMin@/@natClamp@ while
-- retaining the selected comparison head and its dictionary arguments.
normalizeArithmeticPredicateTerm :: Int -> Int -> Term -> CheckM Term
normalizeArithmeticPredicateTerm depth fuel term
  | fuel <= 0 = pure term
  | otherwise =
      case simplifyDecisionTerm term of
        candidate@CApp {}
          | authenticatedComparisonApplication candidate ->
              normalizeComparisonArguments candidate
        _ -> do
          reduced <- transparentProofReduce depth 48 term
          case simplifyDecisionTerm reduced of
            CIf condition thenTerm elseTerm ->
              CIf
                <$> normalizeArithmeticPredicateTerm depth (fuel - 1) condition
                <*> normalizeArithmeticPredicateTerm depth (fuel - 1) thenTerm
                <*> normalizeArithmeticPredicateTerm depth (fuel - 1) elseTerm
            candidate@CApp {}
              | authenticatedComparisonApplication candidate ->
                  normalizeComparisonArguments candidate
            candidate -> pure candidate
  where
    authenticatedComparisonApplication candidate =
      let (headTerm, _) = spineOfTerm (stripIdentityWrappers candidate)
       in authenticatedComparisonHead headTerm

    normalizeComparisonArguments candidate = do
      let (headTerm, arguments) =
            spineOfTerm (stripIdentityWrappers candidate)
      arguments' <-
        traverse
          (\case
            (Expl, argument) ->
              (Expl,)
                <$> normalizeArithmeticOperandTerm
                  depth
                  (fuel - 1)
                  argument
            implicit -> pure implicit)
          arguments
      pure
        ( List.foldl'
            (\function (icit, argument) -> CApp icit function argument)
            headTerm
            arguments'
        )

    authenticatedComparisonHead headTerm =
      termHeadGlob (stripIdentityWrappers headTerm)
        `elem`
          [ Just (gPrel "<")
          , Just (gPrel "<=")
          , Just (gPrel "==")
          , Just (gPrel "ltInt")
          , Just (gPrel "leInt")
          , Just (gPrel "eqInt")
          ]

normalizeArithmeticOperandTerm :: Int -> Int -> Term -> CheckM Term
normalizeArithmeticOperandTerm depth fuel term
  | fuel <= 0 = pure term
  | otherwise =
      case simplifyDecisionTerm term of
        candidate@CApp {}
          | authenticatedArithmeticApplication candidate ->
              normalizeApplicationArguments candidate
        _ -> do
          reduced <- transparentProofReduce depth 48 term
          case simplifyDecisionTerm reduced of
            CIf condition thenTerm elseTerm ->
              CIf
                <$> normalizeArithmeticPredicateTerm depth (fuel - 1) condition
                <*> normalizeArithmeticOperandTerm depth (fuel - 1) thenTerm
                <*> normalizeArithmeticOperandTerm depth (fuel - 1) elseTerm
            candidate@CApp {} ->
              normalizeApplicationArguments candidate
            candidate -> pure candidate
  where
    authenticatedArithmeticApplication candidate =
      case spineOfTerm (stripIdentityWrappers candidate) of
        (headTerm, _) ->
          case termHeadGlob (stripIdentityWrappers headTerm) of
            Just global ->
              global == prelNatAdd
                || global == prelNatMultiply
                || isJust (intArithPrim global)
            Nothing -> False

    normalizeApplicationArguments candidate = do
      let (headTerm, arguments) = spineOfTerm candidate
      arguments' <-
        traverse
          (\case
            (Expl, argument) ->
              (Expl,)
                <$> normalizeArithmeticOperandTerm
                  depth
                  (fuel - 1)
                  argument
            implicit -> pure implicit)
          arguments
      pure
        ( List.foldl'
            (\function (icit, argument) -> CApp icit function argument)
            headTerm
            arguments'
        )

valueArithmeticCertificateProviders
  :: Ctx
  -> ArithmeticDomain
  -> [Term]
  -> CheckM [ArithmeticProviderEvidence Term]
valueArithmeticCertificateProviders ctx domain roots = do
  providerRoots <- transparentArithmeticProviderRoots roots
  normalizedCandidates <-
    forM (rawCandidates providerRoots) $ \(trait, dictionary) ->
      (trait,) <$> zonkTermM (ctxLen ctx) dictionary
  let candidates =
        nubBy
          (\(leftTrait, leftEvidence) (rightTrait, rightEvidence) ->
            leftTrait == rightTrait
              && renderStructuralTermKey leftEvidence
                == renderStructuralTermKey rightEvidence)
          normalizedCandidates
  fmap catMaybes . forM candidates $ \(trait, dictionary) -> do
    standard <-
      standardPreludeDictionary
        trait
        (\case
          [headType] -> arithmeticDomainForCarrier headType == Just domain
          _ -> False)
        dictionary
    pure
      ( if standard
          then Just (ArithmeticProviderEvidence Nothing trait dictionary)
          else Nothing
      )
  where
    rawCandidates candidateRoots =
      [ (trait, dictionary)
      | root <- candidateRoots
      , (trait, carrier, dictionary) <-
          foldTerm providerCandidate (const []) root
      , arithmeticDomainForCarrier carrier == Just domain
      ]

    -- Selected operations hidden in an ordinary transparent helper or a
    -- generated dictionary factory still need to be authenticated by the
    -- artifact. Follow only applied checked reducible definitions, stop at
    -- arithmetic operations themselves, and bound/cycle-check the closure.
    -- A dictionary factory may be saturated entirely by erased evidence, so
    -- requiring an explicit runtime argument would skip its selected methods.
    transparentArithmeticProviderRoots initial = do
      state <- get
      pure (go state 12 Set.empty initial initial)

    go _ 0 _ _ accumulated = accumulated
    go state fuel seen frontier accumulated =
      let callees =
            Set.fromList
              [ global
              | root <- frontier
              , global <-
                  foldTerm transparentCallee (const []) root
              , global `Set.notMember` seen
              ]
          bodies =
            [ body
            | global <- Set.toAscList callees
            , Just definition <- [Map.lookup global (csGlobals state)]
            , gdReducible definition
            , Just body <-
                [ Map.lookup global (csCoreBodies state)
                    <|> gdCoreBody definition
                ]
            ]
       in if null bodies
            then accumulated
            else
              go
                state
                (fuel - 1)
                (Set.union seen callees)
                bodies
                (accumulated ++ bodies)

    transparentCallee term =
      case spineOfTerm (stripIdentityWrappers term) of
        (headTerm, arguments)
          | not (null arguments)
          , Just global <- termHeadGlob (stripIdentityWrappers headTerm)
          , isNothing (standardArithmeticOperationTrait global)
          , isNothing (intArithPrim global)
          , isNothing (intCmpPrim global) ->
              [global]
        _ -> []

    providerCandidate term =
      case spineOfTerm (stripIdentityWrappers term) of
        (headTerm, arguments) ->
          case standardArithmeticDirectProvider term of
            Just provider -> [provider]
            Nothing -> maybeToList (projectedProvider headTerm arguments)

    projectedProvider headTerm _arguments = do
      (dictionary, member) <- case stripIdentityWrappers headTerm of
        CProjM _ dictionary' member' -> Just (dictionary', member')
        CProjAtM _ dictionary' member' _ -> Just (dictionary', member')
        _ -> Nothing
      trait <- standardArithmeticMemberTrait member
      carrier <-
        case domain of
          ArithmeticNatural -> Just (CGlob prelNat)
          ArithmeticInteger -> Just (CGlob prelInteger)
          ArithmeticTypeLevel -> Nothing
          ArithmeticProviderLaw -> Nothing
      pure (trait, carrier, dictionary)

standardArithmeticMemberTrait :: Text -> Maybe GName
standardArithmeticMemberTrait = \case
  "==" -> Just (gPrel "Eq")
  "<" -> Just prelOrd
  "<=" -> Just prelOrd
  "add" -> Just prelAdd
  "multiply" -> Just (gPrel "Mul")
  "subtract" -> Just (gPrel "CheckedSub")
  "divide" -> Just (gPrel "CheckedDiv")
  "modulo" -> Just (gPrel "CheckedMod")
  _ -> Nothing

arithmeticSemanticsForDomain :: ArithmeticDomain -> Maybe ArithmeticSemantics
arithmeticSemanticsForDomain = \case
  ArithmeticNatural -> Just ArithmeticNaturalSemantics
  ArithmeticInteger -> Just ArithmeticIntegerSemantics
  ArithmeticTypeLevel -> Nothing
  ArithmeticProviderLaw -> Nothing

arithmeticVariableBelongsToDomain
  :: ArithmeticDomain
  -> ArithmeticVariableKind
  -> Bool
arithmeticVariableBelongsToDomain domain kind =
  case (domain, kind) of
    (ArithmeticNatural, ArithmeticVariableNatural) -> True
    (ArithmeticInteger, ArithmeticVariableInteger) -> True
    _ -> False

ctxArithmeticVariables :: Ctx -> CheckM [(Int, ArithmeticVariableKind)]
ctxArithmeticVariables ctx =
  fmap catMaybes . forM (zip [0 :: Int ..] (ctxEntries ctx)) $ \(index, entry) -> do
    ty <- forceM (ceType entry)
    let level = ctxLen ctx - 1 - index
    pure $ case ty of
      VGlobN global []
        | global == prelNat ->
            Just (level, ArithmeticVariableNatural)
        | global == prelInteger || global == prelInt ->
            Just (level, ArithmeticVariableInteger)
      _ -> Nothing

-- | Reconstruct the portable, domain-indexed Boolean term corresponding to
-- an already authenticated arithmetic formula.  Nat and Integer share the
-- exact integer primitive substrate, so replay must retain an explicit
-- @natToInt@ boundary around every open Nat comparison operand.  Reifying
-- from 'AFormula' is safe here because the formula was obtained through the
-- selected-evidence decoder above; this function grants no authority to a
-- source spelling and returns 'Nothing' for forms it cannot type faithfully.
arithmeticFormulaReplayTerm
  :: Int
  -> ArithmeticDomain
  -> AFormula
  -> Maybe Term
arithmeticFormulaReplayTerm depth domain = goFormula
  where
    goFormula = \case
      ATruth truth -> Just (boolTerm truth)
      AAtom (AFact comparison lhs rhs) -> do
        lhs' <- goExpression lhs
        rhs' <- goExpression rhs
        let comparisonTerm operation =
              binary
                operation
                (comparisonOperand lhs')
                (comparisonOperand rhs')
        pure $ case comparison of
          ACmpEq -> comparisonTerm (gPrel "eqInt")
          ACmpLt -> comparisonTerm (gPrel "ltInt")
          ACmpLe -> comparisonTerm (gPrel "leInt")
          ACmpNe ->
            CIf
              (comparisonTerm (gPrel "eqInt"))
              (boolTerm False)
              (boolTerm True)
      AAnd lhs rhs ->
        CIf
          <$> goFormula lhs
          <*> goFormula rhs
          <*> pure (boolTerm False)
      AOr lhs rhs ->
        CIf
          <$> goFormula lhs
          <*> pure (boolTerm True)
          <*> goFormula rhs
      ANot formula ->
        CIf
          <$> goFormula formula
          <*> pure (boolTerm False)
          <*> pure (boolTerm True)

    goExpression = \case
      AConst value
        | domain == ArithmeticInteger || value >= 0 ->
            Just (CLit (LitInt value))
      AVar level
        | level >= 0
        , level < depth ->
            Just (CVar (depth - 1 - level))
      AScale coefficient expression
        | domain == ArithmeticInteger || coefficient >= 0 ->
            binary (arithmeticGlobal "multiply")
              (CLit (LitInt coefficient))
              <$> goExpression expression
      AAdd lhs rhs ->
        binaryResult "add"
          <$> goExpression lhs
          <*> goExpression rhs
      ASub lhs rhs ->
        binaryResult "subtract"
          <$> goExpression lhs
          <*> goExpression rhs
      AMul lhs rhs ->
        binaryResult "multiply"
          <$> goExpression lhs
          <*> goExpression rhs
      ADiv lhs rhs ->
        binaryResult "divide"
          <$> goExpression lhs
          <*> goExpression rhs
      AMod lhs rhs ->
        binaryResult "modulo"
          <$> goExpression lhs
          <*> goExpression rhs
      ANeg expression
        | domain == ArithmeticInteger ->
            unary (gPrel "negInt") <$> goExpression expression
      AMax lhs rhs -> do
        lhs' <- goExpression lhs
        rhs' <- goExpression rhs
        pure
          ( CIf
              (binary (gPrel "leInt") (comparisonOperand lhs') (comparisonOperand rhs'))
              rhs'
              lhs'
          )
      AMin lhs rhs -> do
        lhs' <- goExpression lhs
        rhs' <- goExpression rhs
        pure
          ( CIf
              (binary (gPrel "leInt") (comparisonOperand lhs') (comparisonOperand rhs'))
              lhs'
              rhs'
          )
      AIf condition thenExpression elseExpression ->
        CIf
          <$> goFormula condition
          <*> goExpression thenExpression
          <*> goExpression elseExpression
      _ -> Nothing

    comparisonOperand = case domain of
      ArithmeticNatural -> unary prelNatToInt
      ArithmeticInteger -> id
      ArithmeticTypeLevel -> id
      ArithmeticProviderLaw -> id

    arithmeticGlobal operation = case (domain, operation) of
      (ArithmeticNatural, "add") -> prelNatAdd
      (ArithmeticNatural, "multiply") -> prelNatMultiply
      (_, "add") -> gPrel "addInt"
      (_, "subtract") -> gPrel "subInt"
      (_, "multiply") -> gPrel "mulInt"
      (_, "divide") -> gPrel "divInt"
      (_, "modulo") -> gPrel "modInt"
      _ -> gPrel operation

    binaryResult operation lhs rhs = case domain of
      ArithmeticNatural
        | operation == "add" || operation == "multiply" ->
            binary (arithmeticGlobal operation) lhs rhs
        | otherwise ->
            unary
              (gPrel "natOfInt")
              ( binary
                  (arithmeticGlobal operation)
                  (comparisonOperand lhs)
                  (comparisonOperand rhs)
              )
      _ -> binary (arithmeticGlobal operation) lhs rhs

    boolTerm truth =
      CCtorI (if truth then prelTrue else prelFalse) [] Nothing []
    unary function argument = CApp Expl (CGlob function) argument
    binary function lhs rhs =
      CApp Expl (CApp Expl (CGlob function) lhs) rhs

-- | Recover only a candidate endpoint pair for equality reflection. A
-- projected member spelling is intentionally insufficient by itself; callers
-- must reconstruct and typecheck the exact prelude @Eq@ member through the
-- candidate dictionary before using the result.
selectedEqConditionEndpoints :: Term -> Maybe (Term, Term)
selectedEqConditionEndpoints condition = do
  let (headTerm, arguments) =
        spineOfTerm (stripIdentityWrappers condition)
      endpoints = last2 [argument | (Expl, argument) <- arguments]
  case stripIdentityWrappers headTerm of
    CProjM _ _ member
      | member == "==" -> endpoints
    CProjAtM _ _ member _
      | member == "==" -> endpoints
    globalHead
      | termHeadGlob globalHead
          `elem`
            [ Just (gPrel "==")
            , Just (memberGlobal (gPrel "Eq") "==")
            ] ->
          endpoints
    _ -> Nothing

-- | Reify the polarity-safe arithmetic consequences of already-authenticated
-- certificate assumptions. Proof replay and principal assignment share this
-- exact projection so neither solver gains ambient facts unavailable to the
-- other.
arithmeticAssumptionFactsForDomain
  :: Int
  -> ArithmeticDomain
  -> [ArithmeticAssumption Term]
  -> CheckM [AFact]
arithmeticAssumptionFactsForDomain depth domain assumptions =
  fmap (concat . catMaybes) . forM assumptions $
    \(ArithmeticAssumption truth _ replayProposition _) ->
      arithmeticFormulaForDomain depth domain replayProposition >>= \case
        Nothing -> pure Nothing
        Just formula ->
          pure (formulaAssumptionFacts truth formula)

-- | Preserve complete authenticated assumption formulas for the portable
-- Boolean arithmetic solver. The atomic projection above remains appropriate
-- for principal assignment, but implication may require case analysis over a
-- true disjunction or false conjunction.
arithmeticAssumptionFormulasForDomain
  :: Int
  -> ArithmeticDomain
  -> [ArithmeticAssumption Term]
  -> CheckM [(Bool, AFormula)]
arithmeticAssumptionFormulasForDomain depth domain assumptions =
  fmap catMaybes . forM assumptions $
    \(ArithmeticAssumption truth _ replayProposition _) ->
      arithmeticFormulaForDomain depth domain replayProposition >>= \case
        Nothing -> pure Nothing
        Just formula -> pure (Just (truth, formula))

arithmeticFactForDomain
  :: Int
  -> ArithmeticDomain
  -> Term
  -> CheckM (Maybe AFact)
arithmeticFactForDomain depth domain term =
  case spineOfTerm (stripIdentityWrappers term) of
    (headTerm, arguments)
      | termHeadGlob (stripIdentityWrappers headTerm) == Just prelEqType -> do
          let implicit = [argument | (Impl, argument) <- arguments]
              explicit = [argument | (Expl, argument) <- arguments]
          case (listToMaybe implicit, last2 explicit) of
            (Just carrier, Just (left, right))
              | arithmeticCarrierForDomain domain carrier -> do
                  leftExpression <- selectedArithmeticExpression domain depth left
                  rightExpression <- selectedArithmeticExpression domain depth right
                  pure (AFact ACmpEq <$> leftExpression <*> rightExpression)
              | isBoolType carrier ->
                  case (stripIdentityWrappers left, stripIdentityWrappers right) of
                    (predicate, truth) | isTrueTerm truth ->
                      selectedArithmeticPredicateFactForDomain domain depth predicate
                    (truth, predicate) | isTrueTerm truth ->
                      selectedArithmeticPredicateFactForDomain domain depth predicate
                    _ -> pure Nothing
            _ -> pure Nothing
    _ -> pure Nothing
  where
    isTrueTerm = \case
      CCtor constructor _ [] -> constructor == prelTrue
      CCtorI constructor _ _ [] -> constructor == prelTrue
      _ -> False
    isBoolType candidate =
      termHeadGlob (stripIdentityWrappers candidate) == Just prelBool

-- | Reify the required quantifier-free Boolean arithmetic fragment while
-- preserving the authenticated atom decoder above. Connectives are accepted
-- only by resolved prelude identity or by their checked short-circuit Core
-- shape.
arithmeticFormulaForDomain
  :: Int
  -> ArithmeticDomain
  -> Term
  -> CheckM (Maybe AFormula)
arithmeticFormulaForDomain depth domain proposition =
  arithmeticFactForDomain depth domain proposition >>= \case
    Just fact -> pure (Just (AAtom fact))
    Nothing ->
      case booleanLiteralEqualityPayload proposition of
        Nothing -> pure Nothing
        Just (wanted, condition) -> do
          formula <- arithmeticBooleanFormula depth domain condition
          pure (if wanted then formula else ANot <$> formula)

arithmeticCarrierForDomain :: ArithmeticDomain -> Term -> Bool
arithmeticCarrierForDomain domain carrier =
  case (domain, termHeadGlob (stripIdentityWrappers carrier)) of
    (ArithmeticNatural, Just global) -> global == prelNat
    (ArithmeticInteger, Just global) ->
      global == prelInteger || global == prelInt
    (ArithmeticTypeLevel, _) -> False
    _ -> False

arithmeticFactVariables :: AFact -> Set Int
arithmeticFactVariables (AFact _ lhs rhs) =
  arithmeticExpressionVariables lhs `Set.union` arithmeticExpressionVariables rhs

arithmeticFormulaVariables :: AFormula -> Set Int
arithmeticFormulaVariables = \case
  ATruth _ -> Set.empty
  AAtom fact -> arithmeticFactVariables fact
  AAnd lhs rhs -> binary lhs rhs
  AOr lhs rhs -> binary lhs rhs
  ANot formula -> arithmeticFormulaVariables formula
  where
    binary lhs rhs =
      arithmeticFormulaVariables lhs `Set.union` arithmeticFormulaVariables rhs

arithmeticExpressionVariables :: AExpr -> Set Int
arithmeticExpressionVariables = \case
  AConst _ -> Set.empty
  AVar variable -> Set.singleton variable
  AScale _ expression -> arithmeticExpressionVariables expression
  AAdd lhs rhs -> binary lhs rhs
  ASub lhs rhs -> binary lhs rhs
  AMul lhs rhs -> binary lhs rhs
  ADiv lhs rhs -> binary lhs rhs
  AMod lhs rhs -> binary lhs rhs
  ANeg expression -> arithmeticExpressionVariables expression
  AMax lhs rhs -> binary lhs rhs
  AMin lhs rhs -> binary lhs rhs
  AIf condition thenExpression elseExpression ->
    arithmeticFormulaVariables condition
      `Set.union` arithmeticExpressionVariables thenExpression
      `Set.union` arithmeticExpressionVariables elseExpression
  where
    binary lhs rhs =
      arithmeticExpressionVariables lhs `Set.union` arithmeticExpressionVariables rhs

-- | Preserve a TypeLevel-valued projection as a dependency on the resolved
-- local binder identity and field path. The caller has already checked the
-- complete term against the canonical TypeLevel carrier, so this recognizes
-- structural Core identity only; field spelling alone is never authority.
localProjectionLevel :: Ctx -> Term -> Maybe Level
localProjectionLevel ctx = localProjectionLevelAt (ctxLen ctx) ctx

localProjectionLevelAt :: Int -> Ctx -> Term -> Maybe Level
localProjectionLevelAt depth _ctx = go [] . stripIdentityWrappers
  where
    go path = \case
      CProjM _ receiver field -> go (field : path) receiver
      CProjAtM _ receiver field _ -> go (field : path) receiver
      CVar index
        | let root = depth - 1 - index
        , root >= 0 -> Just (LProjection root path)
      _ -> Nothing

localProjectionValueLevel :: Value -> Maybe Level
localProjectionValueLevel = go []
  where
    go path = \case
      VProjN _ receiver field -> go (field : path) receiver
      VRigid root [] | not (null path) -> Just (LProjection root path)
      _ -> Nothing

-- | Query a principal assignment only for the connected component of the
-- requested metas. Proof search and postponed-goal classification must not be
-- made order-dependent by an unrelated declaration's pending or already
-- diagnosed universe constraint. Constraint solving itself couples
-- metavariables only through identities occurring in the same judgment, so
-- this transitive slice is exact rather than heuristic. An empty target set
-- requests the complete module snapshot for legacy callers.
currentPrincipalLevelAssignmentsFor
  :: Set LevelMeta
  -> CheckM (Maybe (Map LevelMeta Level))
currentPrincipalLevelAssignmentsFor requested = do
  st <- get
  let prior = csLevelAssignments st
      constraints0 = zonkedPendingLevelConstraints prior st
  pure (principalLevelAssignmentsWithin prior requested constraints0)

-- | Put a checked branch condition into the local-definition normal form that
-- its enclosing context denotes.  This unfolds immutable local lets through
-- 'ctxEnv' but deliberately excludes branch/pattern facts: those facts are the
-- authority being recorded, not additional equations available while choosing
-- its identity.  Global applications and selected dictionaries remain headed
-- by their resolved symbols.
normalizeBranchConditionTerm :: Ctx -> Term -> CheckM Term
normalizeBranchConditionTerm ctx term = do
  state <- get
  let ec = (ecOf state) {ecFacts = Map.empty}
      normalized = quote ec (ctxLen ctx) (eval ec (ctxEnv ctx) term)
  zonkTermM (ctxLen ctx) normalized

propDecisionKey :: Ctx -> Value -> CheckM (Maybe PropCacheKey)
propDecisionKey ctx goal = do
  let d = ctxLen ctx
  case neutralValueTerm d goal of
    Nothing -> pure Nothing
    Just goalTm -> do
      facts <- boolFactsDecisionKey d
      st <- get
      if not (null (unsolvedMetasOf st goalTm))
          || not (null (levelMetasOfTerm goalTm))
          || not (termCacheUniverseScoped st goalTm)
          || any (not . null . unsolvedMetasOf st . fst) facts
          || any (not . null . levelMetasOfTerm . fst) facts
          || any (not . termCacheUniverseScoped st . fst) facts
        then pure Nothing
        else do
          stableCtx <- ctxTypesMetaStable ctx
          if not stableCtx
            then pure Nothing
            else do
              natKey <- natLevelsDecisionKey ctx
              epoch <- gets csNormEpoch
              let factsKey = T.intercalate "\x1e" [prefix <> renderStructuralTermKey tm | (tm, prefix) <- facts]
              owner <- gets csActiveUniverseDefinition
              pure
                (Just (PropCacheKey epoch owner d (renderStructuralTermKey goalTm) factsKey natKey))

boolFactsDecisionKey :: Int -> CheckM [(Term, Text)]
boolFactsDecisionKey d = do
  facts <- scopedBoolFactsAt d =<< gets csBoolFacts
  let one (tm, truth) =
        (simplifyDecisionTerm tm, if truth then "T:" else "F:")
  pure (map one facts)

ctxTypesMetaStable :: Ctx -> CheckM Bool
ctxTypesMetaStable ctx = do
  ec <- ec_
  st <- get
  let d = ctxLen ctx
      tyStable e =
        let term = quote ec d (ceType e)
         in null (unsolvedMetasOf st term)
              && null (levelMetasOfTerm term)
              && termCacheUniverseScoped st term
  pure (all tyStable (ctxEntries ctx))

natLevelsDecisionKey :: Ctx -> CheckM Text
natLevelsDecisionKey ctx = do
  natLvls <- ctxNatLevels ctx
  pure (T.pack (show (Set.toAscList natLvls)))

proveBoolValueFromBranchFacts :: Ctx -> Bool -> Value -> CheckM Bool
proveBoolValueFromBranchFacts ctx want v = do
  let d = ctxLen ctx
  case neutralValueTerm d v of
    Nothing -> pure False
    Just term -> proveBoolTermFromBranchFacts ctx want term

proveBoolTermFromBranchFacts :: Ctx -> Bool -> Term -> CheckM Bool
proveBoolTermFromBranchFacts ctx want term = do
  let depth = ctxLen ctx
  -- Resolve solved metavariables in the goal: a deferred proof obligation
  -- captures fresh evidence/argument metas that are only solved later.
  -- Zonking retains the original selected dictionary applications while
  -- exposing those solutions to the term-based decision procedures.
  normalized <- zonkTermM depth term
  boolFacts <- normalizeBoolFacts depth =<< gets csBoolFacts
  arithmeticFacts <- arithmeticBranchFacts ctx
  naturalLevels <- ctxNatLevels ctx
  proveBoolValue
    naturalLevels
    boolFacts
    arithmeticFacts
    depth
    want
    normalized

arithmeticBranchFacts :: Ctx -> CheckM [AFact]
arithmeticBranchFacts ctx = do
  let d = ctxLen ctx
  natLvls <- ctxNatLevels ctx
  bfs <- normalizeBoolFacts d =<< gets csBoolFacts
  fmap concat $ forM bfs $ \(tm, truth) -> do
    rangeFacts <-
      if truth
        then selectedNatRangeMembershipFacts d tm
        else pure Nothing
    case rangeFacts of
      Just facts -> pure facts
      Nothing -> do
        mf <-
          selectedStandardOrderFact d tm >>= \case
            Just (_, fact) -> pure (Just fact)
            Nothing -> selectedArithmeticPredicateFact d tm
        pure $ case mf >>= if truth then Just else negateFactForNat natLvls of
          Just fact -> [fact]
          Nothing -> []

-- The complement of equality is not generally a single arithmetic fact.
-- For a variable whose type is known to be Nat, however, @n /= 0@ entails
-- @0 < n@. Keep this refinement local to authenticated Nat binders; applying
-- it to Int or to an arbitrary arithmetic expression would be unsound.
negateFactForNat :: Set Int -> AFact -> Maybe AFact
negateFactForNat natLvls = \case
  AFact ACmpEq (AVar lvl) (AConst 0)
    | lvl `Set.member` natLvls -> Just (AFact ACmpLt (AConst 0) (AVar lvl))
  AFact ACmpEq (AConst 0) (AVar lvl)
    | lvl `Set.member` natLvls -> Just (AFact ACmpLt (AConst 0) (AVar lvl))
  fact -> negateFact fact

-- | Facts eligible to justify an ordinary branch-local @refl@. This path is
-- intentionally limited to the checked condition and the polarity-safe
-- consequences of its Boolean structure. Delta-normalized or arithmetic
-- consequences must use an explicit arithmetic certificate so KCore can
-- replay the derivation rather than accepting source-checker normalization as
-- conversion.
exactBoolFacts :: Int -> [ScopedBoolFact] -> CheckM [(Term, Bool)]
exactBoolFacts d facts =
  concatMap
    (\(term, truth) ->
       decomposeBoolFact 16 (simplifyDecisionTerm term) truth)
    <$> zonkedBoolFacts d facts

proveBoolValue :: Set Int -> [(Term, Bool)] -> [AFact] -> Int -> Bool -> Term -> CheckM Bool
proveBoolValue natLvls boolFacts facts d want t = do
  exactBranchFact <- branchFactTruthAt d boolFacts t
  case exactBranchFact of
    Just truth -> pure (truth == want)
    Nothing -> do
      mRaw <- proveBoolValueAttempt natLvls boolFacts facts d want t
      case mRaw of
        Just ok -> pure ok
        Nothing -> do
          mNorm <- transparentProofNormalize d t
          case mNorm of
            Just t' -> do
              normalizedBranchFact <- branchFactTruthAt d boolFacts t'
              case normalizedBranchFact of
                Just truth -> pure (truth == want)
                Nothing ->
                  fromMaybe False
                    <$> proveBoolValueAttempt natLvls boolFacts facts d want t'
            Nothing -> pure False

-- | Match an exact checked branch fact modulo Core definitional equality.
-- Structural keys remain the fast path in 'evalBoolTermWithFacts', but
-- cumulative lifts, selected reducible wrappers, and checked literal
-- elaboration can give definitionally equal conditions different retained
-- syntax.  The evaluator comparison is bounded and uses the same rigid local
-- environment as ordinary conversion; it does not derive a new Boolean fact
-- or inspect names.
branchFactTruthAt :: Int -> [(Term, Bool)] -> Term -> CheckM (Maybe Bool)
branchFactTruthAt depth facts target = do
  ec <- ec_
  let environment =
        [VRigid level [] | level <- reverse [0 .. depth - 1]]
      targetValue = eval ec environment target
      matches (condition, _) =
        convertible ec depth (eval ec environment condition) targetValue
  pure (snd <$> find matches facts)

proveBoolValueAttempt :: Set Int -> [(Term, Bool)] -> [AFact] -> Int -> Bool -> Term -> CheckM (Maybe Bool)
proveBoolValueAttempt natLvls boolFacts facts d want t = do
  case simplifyDecisionTerm t of
    CCtor g _ [] | g == prelTrue -> pure (Just want)
    CCtor g _ [] | g == prelFalse -> pure (Just (not want))
    _ -> do
      case evalBoolTermWithFacts d boolFacts (6 :: Int) t of
        Just got -> pure (Just (got == want))
        Nothing -> do
          mRangeFacts <- selectedNatRangeMembershipFacts d t
          rangeResult <- case mRangeFacts of
            Just rangeFacts -> do
              proved <- mapM (proveFact natLvls facts) rangeFacts
              pure (if and proved == want then Just True else Nothing)
            Nothing -> pure Nothing
          case rangeResult of
            Just result -> pure (Just result)
            Nothing -> do
          -- Branch-refined equality proofs first consume only the visible
          -- boolean/arithmetic shape of the target proposition plus active
          -- branch facts. The caller may then try one bounded transparent
          -- normalization pass through definitions already marked reducible
          -- by the ordinary totality/opacity machinery.
              mf <- selectedArithmeticPredicateFact d t
              case mf >>= if want then Just else negateFact of
                Just fact -> do
                  ok <- proveFact natLvls facts fact
                  pure (if ok then Just True else Nothing)
                Nothing -> pure Nothing

evalBoolTermWithFacts :: Int -> [(Term, Bool)] -> Int -> Term -> Maybe Bool
evalBoolTermWithFacts _ _ 0 _ = Nothing
evalBoolTermWithFacts d facts depth t0 =
  let factMap =
        Map.fromListWith
          (\new _old -> new)
          [(branchFactKey tm, truth) | (tm, truth) <- facts]
      go = evalBoolTermWithFacts d facts (depth - 1)
      t = simplifyDecisionTerm t0
   in case t of
        CCtor g _ [] | g == prelTrue -> Just True
        CCtor g _ [] | g == prelFalse -> Just False
        _ | Just truth <- Map.lookup (branchFactKey t) factMap -> Just truth
        CIf c th el -> do
          truth <- go c
          go (if truth then th else el)
        _ | Just p <- boolNotArg t -> not <$> go p
        _ -> Nothing

-- ── Quantities (surface → core) ──────────────────────────────────────

-- | Substitute only branch propositions that are already present in the
-- checked condition (including polarity-safe Boolean decomposition). This is
-- the §16.3.3 step-3 boundary that may justify ordinary @refl@: it neither
-- unfolds a different predicate to expose arithmetic subgoals nor derives a
-- Presburger consequence. Those cases must proceed to the proof-producing
-- §15.8 solver and carry an independently checked certificate.
canonicalizeTermsUnderExactCheckedBranchFacts
  :: Ctx
  -> [Term]
  -> CheckM [Term]
canonicalizeTermsUnderExactCheckedBranchFacts ctx terms = do
  instances <- gets csInstances
  canonicalizeTermsUnderBranchFactsWith
    0
    exactBoolFacts
    (canonicalizeStandardArithmeticOperations instances)
    ctx
    terms
