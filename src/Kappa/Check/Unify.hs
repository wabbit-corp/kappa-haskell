-- | Unification support: metavariables, zonking, level constraints.
--
-- Helpers behind 'unify' — reading solved metavariables back out ('zonk'),
-- reindexing deferred level constraints, and the occurs-check machinery that
-- stops a metavariable being solved with a term containing itself.
--
-- Carved out of "Kappa.Check" as part of splitting that module; see
-- "Kappa.Check.Types" for the shared data dictionary and docs\/CONCEPTS.md
-- for the vocabulary these assume.
module Kappa.Check.Unify
  ( applyGeneratedConstraintArguments
  , authenticatedStandardLevelOperator
  , captureAnnotationView
  , corePiIcities
  , finalizeLevelArtifacts
  , generatedConstraintInterfacesAffectedBy
  , insertLevelConstraint
  , insertLevelConstraintOwned
  , lambdaCaptureRequirements
  , levelConstraintFailureAlreadyReported
  , levelOperatorResultCarrier
  , mismatchPayload
  , opaqueSealHead
  , peelCapturesM
  , peelCapturesWithRegionsM
  , principalizeBodyUniverseInstantiations
  , principalizeGeneratedInterfaceOccurrences
  , qSubsumes
  , recordActiveLocalUniverseRequirement
  , registerLevelConstraint
  , rememberLevelOperatorAlias
  , repairFinalizedGeneratedConstraintEvidence
  , replayPublishedGeneratedConstraintCallSpines
  , reportBorrowViewRegionMismatch
  , reportCaptureSetMismatch
  , reportRigidLevelConversionFailure
  , rowEntriesV
  , sameLabelV
  , solveFinalLevelConstraints
  , solverEstablishedLevelWitness
  , withUniverseConstraintOwner
  , withUniverseDiagnosticSpan
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
  , equivalentLevelMetaAssignments
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

-- | Pi binder-quantity subsumption (§12.2.1): a function whose demand
-- interval is contained in the expected binder's demand may stand at
-- that type — every argument capability satisfying the expected demand
-- also satisfies the actual one (e.g. a @(1 x : A) -> B@ value may be
-- used where @(x : A) -> B@ is expected, but not vice versa).
qSubsumes :: Q -> Q -> Bool
qSubsumes qa qe = qa == qe || qInterval qa `contained` qInterval qe
  where
    qInterval :: Q -> (Int, Maybe Int)
    qInterval = \case
      Q0 -> (0, Just 0)
      Q1 -> (1, Just 1)
      QLe1 -> (0, Just 1)
      QGe1 -> (1, Nothing)
      QW -> (0, Nothing)
    contained (lo1, hi1) (lo2, hi2) =
      lo1 >= lo2 && case (hi1, hi2) of
        (_, Nothing) -> True
        (Nothing, Just _) -> False
        (Just h1, Just h2) -> h1 <= h2

-- | Run constructor checking with the enclosing nominal family as the owner
-- of any retained universe obligation.  Constructors do not have an
-- independent declaration schema: a bound such as @succ u <= 3@ is part of
-- the family interface and every constructor result must pass its proof to
-- that family application.  Unlike 'withActiveUniverseDefinition', this
-- scope deliberately does not materialize the proof immediately; the data
-- header installs the family and all constructor interfaces atomically.
withUniverseConstraintOwner :: GName -> CheckM a -> CheckM a
withUniverseConstraintOwner owner action = do
  previous <- gets csActiveUniverseDefinition
  modify' $ \st -> st {csActiveUniverseDefinition = Just owner}
  result <- action
  modify' $ \st -> st {csActiveUniverseDefinition = previous}
  pure result

-- | Add the generated proof arguments required by uses of a nominal family
-- before wrapping the containing declaration in the corresponding proof
-- binders.  At local depth @d@, the newly prepended binders live at indices
-- @d + n - 1 .. d@.  Rewriting the resolved global identity rather than a
-- source spelling keeps constructor result applications and nested GADT
-- results aligned with the family's physical Core telescope.
applyGeneratedConstraintArguments :: GName -> Int -> Term -> Term
applyGeneratedConstraintArguments _ 0 term = term
applyGeneratedConstraintArguments owner count term =
  mapTermWithDepth rewrite 0 term
  where
    rewrite depth = \case
      CGlobal target universes | target == owner ->
        Just $
          foldl'
            (CApp Impl)
            (CGlobal target universes)
            [CVar (depth + count - index - 1) | index <- [0 .. count - 1]]
      _ -> Nothing

generatedProofEnvironment
  :: GeneratedProofScope
  -> Term
  -> [(Text, UniverseConstraint)]
  -> Maybe Term
  -> GeneratedProofEnvironment
generatedProofEnvironment proofScope body callerConstraintBinders rigidWitness =
  GeneratedProofEnvironment
    { gpeAvailableCallerConstraints = availableCallerConstraints
    , gpeCallerAssumptions =
        foldl'
          (\assumptions (_, constraint) ->
             insertAssumption (ucLower constraint) (ucUpper constraint) assumptions)
          emptyAssumptions
          availableCallerConstraints
    , gpeRigidWitness = rigidWitness
    }
  where
    bodyProofNames = case proofScope of
      GeneratedProofLambdas -> generatedProofPrefix body
      GeneratedProofTelescope -> map fst callerConstraintBinders
    availableCallerConstraints =
      [ (index, constraint)
      | (index, name) <- zip [0 ..] bodyProofNames
      , Just constraint <- [lookup name callerConstraintBinders]
      ]

generatedProofFor
  :: GeneratedProofEnvironment
  -> Int
  -> UniverseConstraint
  -> Maybe Term
generatedProofFor environment depth constraint =
  case
      List.find
        (equivalentUniverseConstraint constraint . snd)
        (gpeAvailableCallerConstraints environment) of
    Just (index, _)
      | depth > index -> Just (CVar (depth - index - 1))
    _
      | Just witness <- gpeRigidWitness environment
      , proveLevelLeq
          (gpeCallerAssumptions environment)
          (ucLower constraint)
          (ucUpper constraint)
            == Proved ->
          Just witness
      | otherwise -> Nothing

generatedProofPrefix :: Term -> [Text]
generatedProofPrefix = \case
  CLamM Ordinary Impl Q0 name inner ->
    name : generatedProofPrefix inner
  _ -> []

-- | Replay a previously published generated-proof prefix into an artifact
-- rebuilt from an older interface snapshot. Unlike a fresh publication delta,
-- the artifact may already contain the prefix. The finalized target telescope
-- therefore authenticates the only two rewrites allowed here:
--
-- * a saturated occurrence short by exactly the published prefix receives it;
-- * a partial occurrence whose icities align only after removing that prefix
--   receives it;
-- * an occurrence already aligned with the finalized telescope is preserved.
--
-- Partial or otherwise malformed applications are left untouched. Their
-- provenance is ambiguous without a typed occurrence annotation, so guessing
-- would risk treating an ordinary implicit as generated evidence; finalized
-- Core validation remains the fail-closed authority for those cases.
replayPublishedGeneratedConstraintCallSpines
  :: GeneratedProofScope
  -> Map GName ([UniverseConstraint], [Icit])
  -> Map GName ([UniverseConstraint], [Icit])
  -> [(Text, UniverseConstraint)]
  -> Maybe Term
  -> Term
  -> Term
replayPublishedGeneratedConstraintCallSpines proofScope targets constructors callerConstraintBinders rigidWitness body =
  walk 0 body
  where
    proofEnvironment =
      generatedProofEnvironment
        proofScope
        body
        callerConstraintBinders
        rigidWitness

    walk depth = mapTermWithDepth rewrite depth

    rewrite depth term =
      replayGlobal depth term <|> replayConstructor depth term

    replayGlobal depth term =
      case spineOfTerm term of
        (CGlobal target universes, arguments)
          | Just (constraints, finalizedIcities) <- Map.lookup target targets
          , not (null constraints) ->
              let walkedArguments =
                    [(icit, walk depth argument) | (icit, argument) <- arguments]
                  actualIcities = map fst walkedArguments
                  prefixCount = length constraints
                  finalizedArity = length finalizedIcities
                  saturatedMissing =
                    length walkedArguments + prefixCount == finalizedArity
                  saturatedComplete = length walkedArguments == finalizedArity
                  aligns expected = actualIcities == take (length actualIcities) expected
                  alignsComplete = aligns finalizedIcities
                  alignsMissing = aligns (drop prefixCount finalizedIcities)
                  missing =
                    saturatedMissing
                      || (not saturatedComplete && alignsMissing && not alignsComplete)
                      || null walkedArguments
                  complete =
                    saturatedComplete
                      || (alignsComplete && not alignsMissing)
               in if missing
                    then do
                      proofs <-
                        traverse
                          (generatedProofFor proofEnvironment depth . instantiate universes)
                          constraints
                      pure $
                        foldl'
                          (\function (icit, argument) -> CApp icit function argument)
                          (foldl' (CApp Impl) (CGlobal target universes) proofs)
                          walkedArguments
                    else if complete
                      then
                        Just $
                          foldl'
                            (\function (icit, argument) -> CApp icit function argument)
                            (CGlobal target universes)
                            walkedArguments
                      else
                        -- Suppress descent into the application head: a
                        -- shorter nested spine is not a distinct occurrence.
                        Just $
                          foldl'
                            (\function (icit, argument) -> CApp icit function argument)
                            (CGlobal target universes)
                            walkedArguments
        _ -> Nothing

    replayConstructor depth = \case
      CCtorI target universes annotation arguments
        | Just (constraints, finalizedIcities) <- Map.lookup target constructors
        , not (null constraints) ->
            let walkedAnnotation = fmap (walk depth) annotation
                walkedArguments =
                  [argument {caTerm = walk depth (caTerm argument)} | argument <- arguments]
                actualIcities = map caIcit walkedArguments
                prefixCount = length constraints
                finalizedArity = length finalizedIcities
                saturatedMissing =
                  length walkedArguments + prefixCount == finalizedArity
                saturatedComplete = length walkedArguments == finalizedArity
                aligns expected = actualIcities == take (length actualIcities) expected
                alignsComplete = aligns finalizedIcities
                alignsMissing = aligns (drop prefixCount finalizedIcities)
                missing =
                  saturatedMissing
                    || (not saturatedComplete && alignsMissing && not alignsComplete)
                    || null walkedArguments
             in if missing
                  then do
                    proofs <-
                      traverse
                        (generatedProofFor proofEnvironment depth . instantiate universes)
                        constraints
                    pure
                      ( CCtorI target universes walkedAnnotation
                          ( [ConstructorArg Impl False Nothing proof | proof <- proofs]
                              ++ walkedArguments
                          )
                      )
                  else Just (CCtorI target universes walkedAnnotation walkedArguments)
      _ -> Nothing

    instantiate universes (UniverseConstraint lower upper) =
      UniverseConstraint
        (normalizeLevel (substituteLevelParams universes lower))
        (normalizeLevel (substituteLevelParams universes upper))

corePiIcities :: Term -> [Icit]
corePiIcities = \case
  CPiBoundM _ icit _ _ _ _ _ codomain -> icit : corePiIcities codomain
  _ -> []

-- | Revalidate proof arguments that were selected while a declaration still
-- had a provisional universe spine. The target's finalized checked telescope
-- determines exactly which leading erased arguments are generated level
-- evidence. Only those slots are replaced, and only from an exact caller
-- binder or a rigid solver proof; ordinary implicits and unproved obligations
-- are preserved for typed-Core validation to judge.
repairGeneratedConstraintEvidenceArguments
  :: GeneratedProofScope
  -> Map GName [UniverseConstraint]
  -> Map GName [UniverseConstraint]
  -> [(Text, UniverseConstraint)]
  -> Maybe Term
  -> Term
  -> Term
repairGeneratedConstraintEvidenceArguments proofScope targetConstraints constructorConstraints callerConstraintBinders rigidWitness body =
  walk 0 body
  where
    proofEnvironment =
      generatedProofEnvironment
        proofScope
        body
        callerConstraintBinders
        rigidWitness

    walk depth = mapTermWithDepth rewrite depth

    rewrite depth term =
      repairGlobal depth term <|> repairConstructor depth term

    repairGlobal depth term =
      case spineOfTerm term of
        (CGlobal target universes, arguments)
          | Just constraints <- Map.lookup target targetConstraints
          , not (null constraints)
          , let (proofArguments, ordinaryArguments) =
                  splitAt (length constraints) arguments
          , length proofArguments == length constraints
          , all ((== Impl) . fst) proofArguments
          , Just proofs <-
              traverse
                (generatedProofFor proofEnvironment depth . instantiate universes)
                constraints ->
              Just $
                foldl'
                  (\function (icit, argument) -> CApp icit function argument)
                  (CGlobal target universes)
                  ( zip (map fst proofArguments) proofs
                      ++ [(icit, walk depth argument) | (icit, argument) <- ordinaryArguments]
                  )
        _ -> Nothing

    repairConstructor depth = \case
      CCtorI target universes annotation arguments
        | Just constraints <- Map.lookup target constructorConstraints
        , not (null constraints)
        , let (proofArguments, ordinaryArguments) =
                splitAt (length constraints) arguments
        , length proofArguments == length constraints
        , all ((== Impl) . caIcit) proofArguments
        , Just proofs <-
            traverse
              (generatedProofFor proofEnvironment depth . instantiate universes)
              constraints ->
            Just
              ( CCtorI target universes
                  (fmap (walk depth) annotation)
                  ( zipWith
                      (\argument proof -> argument {caTerm = proof})
                      proofArguments
                      proofs
                      ++ [argument {caTerm = walk depth (caTerm argument)} | argument <- ordinaryArguments]
                  )
              )
      _ -> Nothing

    instantiate universes (UniverseConstraint lower upper) =
      UniverseConstraint
        (normalizeLevel (substituteLevelParams universes lower))
        (normalizeLevel (substituteLevelParams universes upper))

-- | Enforce the finalized generated-proof ABI after all declaration SCCs,
-- interface-publication waves, and pending evidence have settled. Earlier
-- phases may retain a certificate selected against a provisional occurrence
-- assignment; this pass uses only checked final telescopes and rewrites only
-- their authenticated generated-evidence prefix.
repairFinalizedGeneratedConstraintEvidence :: CheckM ()
repairFinalizedGeneratedConstraintEvidence = do
  state <- get
  let currentModule = csModule state
      context = ecOf state
      rigidWitness =
        if Map.member prelRefl (csCtors state)
          then Just solverEstablishedLevelWitness
          else Nothing
      globalConstraints =
        Map.map
          (map snd . generatedConstraintBinders . globalCoreType context)
          (csGlobals state)
      constructorConstraints =
        Map.map
          (map snd . generatedConstraintBinders . ciType)
          (csCtors state)
      repairType global definition
        | not (gnameInModule global currentModule) = definition
        | otherwise =
            let coreType = globalCoreType context definition
                repaired =
                  repairGeneratedConstraintEvidenceArguments
                    GeneratedProofTelescope
                    globalConstraints
                    constructorConstraints
                    (generatedConstraintBinders coreType)
                    rigidWitness
                    coreType
             in definition {gdCoreType = Just repaired}
      globalsWithCoreTypes = Map.mapWithKey repairType (csGlobals state)
      repairedContext = context {ecGlobals = Globals globalsWithCoreTypes}
      globalsWithTypes =
        Map.mapWithKey
          (\global definition ->
             if gnameInModule global currentModule
               then
                 definition
                   { gdType =
                       eval repairedContext [] (globalCoreType repairedContext definition)
                   }
               else definition)
          globalsWithCoreTypes
      repairConstructor constructor info
        | not (gnameInModule constructor currentModule) = info
        | otherwise =
            info
              { ciType =
                  repairGeneratedConstraintEvidenceArguments
                    GeneratedProofTelescope
                    globalConstraints
                    constructorConstraints
                    (generatedConstraintBinders (ciType info))
                    rigidWitness
                    (ciType info)
              }
      constructors' = Map.mapWithKey repairConstructor (csCtors state)
      repairBody global body
        | not (gnameInModule global currentModule) = body
        | otherwise =
            let callerConstraints =
                  maybe
                    []
                    (generatedConstraintBinders . globalCoreType repairedContext)
                    (Map.lookup global globalsWithTypes)
             in repairGeneratedConstraintEvidenceArguments
                  GeneratedProofLambdas
                  globalConstraints
                  constructorConstraints
                  callerConstraints
                  rigidWitness
                  body
      bodies' = Map.mapWithKey repairBody (csCoreBodies state)
      stateWithArtifacts =
        state
          { csGlobals = globalsWithTypes
          , csCtors = constructors'
          , csCoreBodies = bodies'
          }
      globals' =
        Map.mapWithKey
          (\global definition ->
             maybe
               definition
               (\body ->
                  globalDefWithCanonicalCoreBody
                    stateWithArtifacts
                    body
                    definition)
               (Map.lookup global bodies'))
          globalsWithTypes
  put
    ( invalidateSemanticCaches
        stateWithArtifacts {csGlobals = globals'}
    )

-- | Closed proof-irrelevant representative used only after the level solver
-- has established a generated comparison.  The authenticated relation lives
-- on the Pi/application slot; the witness identity is intentionally not part
-- of interface semantics (§11.1.2.3A).  Building this term directly avoids
-- running ordinary constructor elaboration while the embedded prelude itself
-- is still being assembled.
solverEstablishedLevelWitness :: Term
solverEstablishedLevelWitness =
  CCtorI prelRefl [LZero] Nothing
    [ ConstructorArg Impl False Nothing (CGlobal prelBool [])
    , ConstructorArg Impl False Nothing truth
    , ConstructorArg Impl False Nothing truth
    ]
  where
    truth = CCtorI prelTrue [] Nothing []

-- | Retain a rigid relation discovered while checking one explicit local
-- declaration schema. Local declarations do not have a global owner in
-- 'csActiveUniverseDefinition'; their generalization boundary instead owns
-- every constraint allocated since its saved constraint identity. Admit only
-- a relation closed over that local telescope and only when the extended
-- assumptions remain consistent. This gives local SCC generalization the
-- same proof-binder input as a top-level declaration without allowing an
-- unrelated lexical rigid mismatch to become a declaration contract.
recordActiveLocalUniverseRequirement
  :: Assumptions
  -> Level
  -> Level
  -> CheckM Bool
recordActiveLocalUniverseRequirement assumptions lhs rhs = do
  state <- get
  let localParameterCount =
        csActiveLocalUniverseSchemaCount state
          <|> ( length . lrssCurrentInstance
                  <$> csActiveLocalRecursiveSchemaScope state
              )
      levels = [lhs, rhs]
      closed count =
        null (concatMap levelMetas levels)
          && null (concatMap levelVars levels)
          && null (concatMap levelFields levels)
          && all
            (\parameter -> parameter >= 0 && parameter < count)
            (concatMap levelParams levels)
      extended = insertAssumption lhs rhs assumptions
  case localParameterCount of
    Just count
      | closed count
      , assumptionsConsistent extended -> do
          insertLevelConstraintOwned
            Nothing
            assumptions
            (ConstraintOrigin "local declaration universe" "type conversion")
            lhs
            rhs
          pure True
    _ -> pure False

generatedConstraintInterfacesAffectedBy
  :: GName
  -> CheckState
  -> CheckState
  -> Set GeneratedConstraintInterface
generatedConstraintInterfacesAffectedBy owner before after =
  let newGlobals = Map.keysSet (Map.difference (csGlobals after) (csGlobals before))
      newConstructors = Map.keysSet (Map.difference (csCtors after) (csCtors before))
      ownerConstructors =
        Set.fromList (maybe [] diCtors (Map.lookup owner (csDatas after)))
   in Set.unions
        [ Set.singleton (GeneratedGlobalInterface owner)
        , Set.map GeneratedGlobalInterface newGlobals
        , Set.map GeneratedConstructorInterface
            (Set.union ownerConstructors newConstructors)
        ]

registerLevelConstraint :: Ctx -> Text -> Text -> Level -> Level -> CheckM ()
registerLevelConstraint ctx description construct lhs rhs = do
  assumptions <- effectiveLevelAssumptions ctx
  insertLevelConstraint assumptions (ConstraintOrigin description construct) lhs rhs

insertLevelConstraint :: Assumptions -> ConstraintOrigin -> Level -> Level -> CheckM ()
insertLevelConstraint assumptions origin lhs rhs = do
  owner <- gets csActiveUniverseDefinition
  insertLevelConstraintOwned owner assumptions origin lhs rhs

insertLevelConstraintOwned
  :: Maybe GName
  -> Assumptions
  -> ConstraintOrigin
  -> Level
  -> Level
  -> CheckM ()
insertLevelConstraintOwned owner assumptions origin lhs rhs =
  void
    ( insertLevelConstraintOwnedWithProvenance
        Nothing
        owner
        assumptions
        origin
        lhs
        rhs
    )

solveFinalLevelConstraints :: CheckState -> [LevelConstraint] -> CheckM Bool
solveFinalLevelConstraints initialState constraints = do
  let rigidFailure constraint =
        null
          ( levelMetas (lcLhs constraint)
              ++ levelMetas (lcRhs constraint)
              ++ concat
                   [ levelMetas lower ++ levelMetas upper
                   | (lower, upper) <- assumptionsList (lcAssumptions constraint)
                   ]
          )
          && proveLevelLeq
               (lcAssumptions constraint)
               (lcLhs constraint)
               (lcRhs constraint)
               == Disproved
      (rigidFailures, inferableConstraints) = List.partition rigidFailure constraints
  if not (null rigidFailures)
    then do
      mapM_ (reportLevelSolveError . LevelConstraintDisproved) rigidFailures
      -- Independent declaration failures must not mask one another. Continue
      -- through the remaining connected inference problem to expose any
      -- additional non-rigid failure, but retain the failed result even when
      -- that remainder solves.
      unless (null inferableConstraints) $
        void (solveFinalLevelConstraints initialState inferableConstraints)
      pure False
    else solveInferable
  where
    solveInferable = do
      let assignments = csLevelAssignments initialState
          constraintMetas constraint =
            Set.fromList
              ( levelMetas (lcLhs constraint)
                  ++ levelMetas (lcRhs constraint)
                  ++ concat
                       [ levelMetas lower ++ levelMetas upper
                       | (lower, upper) <- assumptionsList (lcAssumptions constraint)
                       ]
              )
          constrainedMetas = Set.unions (map constraintMetas constraints)
          -- Final evidence commitment can replace an ordinary term meta by a
          -- proof term carrying fresh universe occurrences. Materialize each
          -- body before collecting the complete final selected set.
          bodyMetas =
            Map.foldl'
              (\metas body ->
                 let materialized = evalState (zonkTermM 0 body) initialState
                  in Set.union metas
                       (Set.fromList (levelMetasOfTerm (zonkLevels assignments materialized))))
              Set.empty
              (csCoreBodies initialState)
          firstClassMetas =
            Set.fromList
              [ projected
              | origin <- Set.toList (csFirstClassLevelMetas initialState)
              , projected <-
                  levelMetas
                    (normalizeLevel (substituteLevelMetas assignments (LMeta origin)))
              ]
          remainingMetas = Set.unions [constrainedMetas, bodyMetas, firstClassMetas]
          -- Declaration generalization has already replaced every legal
          -- user-observable polymorphic identity by a rigid 'LParam'. Any
          -- level meta still present at module closeout is therefore an
          -- occurrence, result, or other minimizable inference choice.
          targets = remainingMetas
          owners =
            Set.toAscList . Set.fromList $
              [ owner
              | constraint <- constraints
              , Just owner <-
                  [Map.lookup (lcIdentity constraint) (csLevelConstraintOwners initialState)]
              ]
          declarations = case owners of
            [] -> [moduleNameText (csModule initialState)]
            _ -> map gKey owners
          explicitSchema =
            any
              (\owner -> maybe False (dutExplicit . gdUniverses)
                (Map.lookup owner (csGlobals initialState)))
              owners
          diagnosticSpan =
            fromMaybe
              (Span "<universe-inference>" (Pos 1 1) (Pos 1 1))
              (listToMaybe constraints >>= \constraint ->
                 Map.lookup (lcIdentity constraint) (csLevelConstraintSpans initialState))
      inferred <-
        inferPrincipalAtDeclarationBoundary
          diagnosticSpan declarations explicitSchema targets constraints
      case inferred of
        PrincipalBoundarySolved principal -> do
          installLevelAssignments principal
          finalState <- get
          let combined = csLevelAssignments finalState
              finalizedConstraints =
                map (substituteLevelConstraintMetas combined) constraints
          case solveLevelConstraints finalizedConstraints of
            Left solveError -> reportLevelSolveError solveError >> pure False
            Right solution
              | null (lsResidual solution) -> do
                  finalizeLevelArtifacts
                  modify' $ \state ->
                    if Map.null (csPendingLevelEvidence state)
                      then
                        reindexLevelConstraints $
                          state
                            { csLevelConstraints = []
                            , csLevelConstraintOwners = Map.empty
                            , csLevelConstraintSpans = Map.empty
                            }
                      else
                        -- Pending authenticated LevelLe terms may be the only
                        -- remaining roots that mention occurrence metas. Keep
                        -- the solved graph until those proofs replay against
                        -- its principal component; the next closeout
                        -- iteration clears it after the side table is retired.
                        reindexLevelConstraints
                          state {csLevelConstraints = finalizedConstraints}
                  pure True
              | otherwise -> do
                  modify' $ \state ->
                    reindexLevelConstraints $
                      state
                      { csLevelConstraints = lsResidual solution
                      , csLevelConstraintOwners =
                          Map.restrictKeys
                            (csLevelConstraintOwners state)
                            (Set.fromList (map lcIdentity (lsResidual solution)))
                      , csLevelConstraintSpans =
                          Map.restrictKeys
                            (csLevelConstraintSpans state)
                            (Set.fromList (map lcIdentity (lsResidual solution)))
                      }
                  pure False
        PrincipalBoundaryDeferred -> pure False
        PrincipalBoundaryRejected failure -> do
          reportPrincipalBoundaryFailure
            diagnosticSpan declarations explicitSchema targets constraints failure
          pure False

-- | Close checker-created universe instantiations before a reducible body is
-- installed. Module-final solving is too late for these metas: a following
-- declaration may unfold the body during conversion, and an unsolved
-- occurrence would then look like an independent universe choice. Source
-- interface metas are deliberately excluded; only fresh instantiations made
-- while specializing declaration telescopes are principalized here.
principalizeBodyUniverseInstantiations :: GName -> Value -> Term -> CheckM Term
principalizeBodyUniverseInstantiations owner interfaceType body0 = do
  -- Solved term metavariables can contain fresh universe instantiations. The
  -- declaration boundary must inspect their reified Core, otherwise those
  -- levels appear only in the caller's later zonk and escape principalization.
  body <- zonkTermM 0 body0
  interface <- quoteIn emptyCtx interfaceType >>= zonkTermM 0
  st <- get
  let assignments = csLevelAssignments st
      bodyMetas = Set.fromList (levelMetasOfTerm (zonkLevels assignments body))
      interfaceMetas =
        Set.fromList
          (levelMetasOfTerm (zonkLevels assignments interface))
      provisionalInstantiationMetas =
        unmaterializedProvisionalUniverseMetas st
          ( Map.findWithDefault
              Set.empty
              owner
              (csProvisionalUniverseInstantiationsByConsumer st)
          )
      recursiveCandidateInstantiationMetas =
        Set.fromList
          [ meta
          | occurrence <- Map.findWithDefault
              []
              owner
              (csRecursiveSchemaOccurrencesByCaller st)
          , not (rsoExplicit occurrence)
          , rsoCallee occurrence `Set.member` csTerminationNames st
          , level <- rsoLevels occurrence
          , meta <- levelMetas
              (normalizeLevel (substituteLevelMetas assignments level))
          ]
      targets =
        Set.filter (`Map.notMember` assignments)
          ( Set.difference
              (Set.difference bodyMetas interfaceMetas)
              (Set.union provisionalInstantiationMetas recursiveCandidateInstantiationMetas)
          )
      ownerSymbols =
        Set.insert owner
          (maybe Set.empty (Set.fromList . diCtors) (Map.lookup owner (csDatas st)))
      constraints =
        map
          (substituteLevelConstraintMetas assignments)
          (levelConstraintsOwnedBy st ownerSymbols ++ bodyLiftConstraints body)
      preferredAliases =
        Map.restrictKeys
          ( equivalentLevelMetaAssignments
              interfaceMetas
              interfaceMetas
              targets
              constraints
          )
          targets
      -- Materialized cumulative coercions are typed Core obligations.  Their
      -- original side-table constraints may already have been discharged
      -- into evidence, but occurrence-level principalization still needs the
      -- certified lower/upper relation to choose metas appearing in the
      -- body.  Reconstruct only those semantic judgments, preserving the
      -- certificate's recorded dependencies as assumptions.
      bodyLiftConstraints term =
        zipWith toConstraint [-1, -2 ..]
          ( foldTermWithDepth
              (\_ node -> case node of
                  CUniverseLift _ _ (UniverseEvidence steps) _ -> steps
                  _ -> [])
              0
              term
          )
      toConstraint identity (UniverseEvidenceStep lower upper dependencies) =
        LevelConstraint
          { lcIdentity = identity
          , lcLhs = lower
          , lcRhs = upper
          , lcOrigin = ConstraintOrigin "typed cumulative coercion" "declaration-body principalization"
          , lcAssumptions =
              foldr (uncurry insertAssumption) emptyAssumptions dependencies
          }
  if not (Map.null preferredAliases)
    then do
      -- A body occurrence exactly equal to a published interface identity is
      -- that identity, not an independent least-level choice. Re-enter after
      -- installing the alias so the selected set and residual constraints are
      -- recomputed from the authoritative representative.
      installLevelAssignments preferredAliases
      principalizeBodyUniverseInstantiations owner interfaceType body
    else if Set.null targets
    then normalizeProvisionalBodyReferences body
    else do
      let diagnosticSpan = Span "<universe-inference>" (Pos 1 1) (Pos 1 1)
      inferred <-
        inferPrincipalAtDeclarationBoundary
          diagnosticSpan [gKey owner] False targets constraints
      case inferred of
        PrincipalBoundarySolved candidate -> do
          installLevelAssignments candidate
          zonkTermM 0 body >>= normalizeProvisionalBodyReferences
        PrincipalBoundaryDeferred -> pure body
        PrincipalBoundaryRejected _ -> pure body

-- | Close compiler-created declaration occurrences before deciding which
-- interface levels belong to a generated declaration's own schema.  An
-- instance head such as @Eq TypeLevel@ specializes @Eq@ at a fresh level and
-- constrains that occurrence to its least admissible value.  Treating the
-- fresh level as part of the dictionary's source schema would instead publish
-- a spurious polymorphic instance.
--
-- Source-owned levels are excluded by provenance.  If an occurrence depends
-- on one of those levels and cannot yet be solved independently, the portable
-- solver returns 'PrincipalBoundaryDeferred' and the complete declaration SCC
-- remains the authority.
principalizeGeneratedInterfaceOccurrences
  :: GName
  -> Set LevelMeta
  -> Term
  -> CheckM Term
principalizeGeneratedInterfaceOccurrences owner protectedOrigins interface = do
  st <- get
  let assignments = csLevelAssignments st
      zonked = zonkLevels assignments interface
      interfaceMetas = Set.fromList (levelMetasOfTerm zonked)
      projected =
        Set.fromList
          . concatMap
              ( levelMetas
                  . normalizeLevel
                  . substituteLevelMetas assignments
                  . LMeta
              )
          . Set.toList
      sourceOwned =
        projected
          ( Set.union protectedOrigins
              ( Set.difference
                  ( Map.findWithDefault
                      Set.empty
                      owner
                      (csLevelGeneralizableMetasByOwner st)
                  )
                  (Map.findWithDefault
                    Set.empty
                    owner
                    (csLevelInstantiationMetasByOwner st))
              )
          )
      provisionalOccurrenceIds =
        Map.findWithDefault
          Set.empty
          owner
          (csProvisionalUniverseInstantiationsByConsumer st)
      deferredDependencyMetas =
        unmaterializedProvisionalUniverseMetas st provisionalOccurrenceIds
      targets =
        Set.difference
          (Set.difference interfaceMetas sourceOwned)
          deferredDependencyMetas
      constraints =
        map
          (substituteLevelConstraintMetas assignments)
          (levelConstraintsOwnedBy st (Set.singleton owner))
      groups = selectedConstraintGroups targets constraints
      diagnosticSpan = Span "<universe-inference>" (Pos 1 1) (Pos 1 1)
  forM_ groups $ \(componentTargets, componentConstraints) -> do
    inferred <-
      inferPrincipalAtDeclarationBoundary
        diagnosticSpan
        [gKey owner]
        False
        componentTargets
        componentConstraints
    case inferred of
      PrincipalBoundarySolved candidate -> installLevelAssignments candidate
      PrincipalBoundaryDeferred -> pure ()
      PrincipalBoundaryRejected _ -> pure ()
  zonkTermM 0 interface

-- | Late declaration bodies (notably instance dictionaries) are elaborated
-- after the module SCC pass.  Their global references may therefore still use
-- a dependency's provisional all-meta universe spine.  Once body-local metas
-- have been principalized, apply the same source-to-retained projection used
-- by the SCC finalizer before the body is recorded.
normalizeProvisionalBodyReferences :: Term -> CheckM Term
normalizeProvisionalBodyReferences body = do
  st <- get
  let targets = Set.toList (globalsOfTerm body)
      globalProjections =
        Map.unions [provisionalUniverseProjections st target | target <- targets]
      constructorProjections =
        Map.unions
          [ provisionalConstructorUniverseProjections st target
          | target <- targets
          ]
  pure
    ( rewriteProvisionalUniverseReferences
        ( UniverseReferenceProjections
            globalProjections
            constructorProjections
            Map.empty
            Map.empty
        )
        body
    )

provisionalConstructorUniverseProjections
  :: CheckState
  -> GName
  -> Map (GName, Int) UniverseReferenceProjection
provisionalConstructorUniverseProjections st constructor = fromMaybe Map.empty $ do
  info <- Map.lookup constructor (csCtors st)
  guard (not (dutExplicit (ciUniverses info)))
  let assignments =
        Map.union
          ( Map.findWithDefault
              Map.empty
              constructor
              (csFinalizedGlobalUniverseMetaMaps st)
          )
          (csLevelAssignments st)
      fallbackSource = nub (levelMetasOfTerm (ciType info))
      sourceSpines =
        Map.findWithDefault
          [fallbackSource]
          constructor
          (csProvisionalConstructorUniverseMetas st)
      retainedLevels =
        map LParam [0 .. dutParameterCount (ciUniverses info) - 1]
  pure $
    uniqueUniverseReferenceProjections
      [ ( (constructor, length sourceMetas)
        , deriveUniverseReferenceProjectionToLevels
            assignments
            sourceMetas
            retainedLevels
        )
      | sourceMetas <- sourceSpines
      ]

-- | Reconcile constructor-pattern checkpoint metadata with the finalized
-- typed scrutinee carried by each 'CMatch'. Constructor patterns and their
-- enclosing data family share one declaration-universe schema; provisional
-- body occurrences can nevertheless be minimized before the family SCC
-- acquires its final telescope. The typed match annotation is the checked
-- authority for that occurrence. Unknown heads, arity mismatches, and failed
-- field alignment are left untouched for the final KBackendIR validator.
repairConstructorPatternUniverseSpines
  :: EvalCtx
  -> Map GName CtorInfo
  -> Term
  -> Term
repairConstructorPatternUniverseSpines evaluation constructors = goTerm 0
  where
    rigidEnvironment depth =
      [VRigid level [] | level <- reverse [0 .. depth - 1]]

    goTerm depth =
      mapTermWithDepth (rewriteTerm depth) depth

    rewriteTerm _ currentDepth (CMatch scrutinee annotation resultAnnotation alternatives) =
      let scrutinee' = goTerm currentDepth scrutinee
          annotation' = goTerm currentDepth <$> annotation
          resultAnnotation' = goTerm currentDepth <$> resultAnnotation
          expected =
            eval evaluation (rigidEnvironment currentDepth) <$> annotation'
          alternatives' = map (repairAlternative currentDepth expected) alternatives
       in Just (CMatch scrutinee' annotation' resultAnnotation' alternatives')
    rewriteTerm _ _ _ = Nothing

    repairAlternative depth expected (CaseAlt pattern' guard body) =
      let pattern'' = repairPattern depth expected pattern'
          bodyDepth = depth + patBindersC pattern''
       in CaseAlt
            pattern''
            (goTerm bodyDepth <$> guard)
            (goTerm bodyDepth body)

    repairPattern depth expected = \case
      CPCtorM existentialModes bridges hidden constructor universes patterns ->
        let selected = do
              expectedType <- expected
              info <- Map.lookup constructor constructors
              (family, familyUniverses) <- nominalInstance expectedType
              guard (family == ciData info)
              guard
                (length familyUniverses
                  == dutParameterCount (ciUniverses info))
              pure (info, familyUniverses, expectedType)
            universes' = maybe universes (\(_, levels, _) -> levels) selected
            fieldTypes = do
              (info, levels, expectedType) <- selected
              constructorType <- specializeConstructorType evaluation (Just levels) info
              map snd
                <$> constructorPatternObservationSites
                      evaluation
                      False
                      depth
                      (length (ciFields info))
                      constructorType
                      expectedType
            bridgeDepth = depth + length existentialModes
            (bridges', fieldDepth) = repairBridges bridgeDepth bridges
            expectedTypes =
              fromMaybe
                (replicate (length patterns) Nothing)
                (map Just <$> fieldTypes)
            patterns' =
              repairConstructorPatterns
                fieldDepth
                expectedTypes
                hidden
                patterns
         in CPCtorM existentialModes bridges' hidden constructor universes' patterns'
      CPTuple patterns ->
        let fieldTypes = case expected of
              Just value -> case force evaluation value of
                VRecordTQ fields -> map (Just . rfType) fields
                _ -> replicate (length patterns) Nothing
              Nothing -> replicate (length patterns) Nothing
         in CPTuple (repairPatternList depth fieldTypes patterns)
      CPRecordM fields rest ->
        let recordFields = case expected of
              Just value -> case force evaluation value of
                VRecordTQ available -> available
                _ -> []
              Nothing -> []
            expectedFor name = rfType <$> find ((== name) . rfName) recordFields
            patterns = map snd fields
            repaired =
              repairPatternList
                depth
                [expectedFor name | (name, _) <- fields]
                patterns
         in CPRecordM (zip (map fst fields) repaired) rest
      CPInject tag pattern' ->
        CPInject tag (repairPattern depth Nothing pattern')
      CPOr patterns permutations ->
        CPOr (map (repairPattern depth expected) patterns) permutations
      CPAsM mode name pattern' ->
        CPAsM mode name (repairPattern (depth + 1) expected pattern')
      pattern' -> pattern'

    repairPatternList _ _ [] = []
    repairPatternList depth expectedTypes (pattern' : rest) =
      let expected = listToMaybe expectedTypes >>= id
          pattern'' = repairPattern depth expected pattern'
       in pattern''
            : repairPatternList
                (depth + patBindersC pattern'')
                (drop 1 expectedTypes)
                rest

    repairConstructorPatterns depth expectedTypes hidden patterns =
      case interleaveConstructorSourceBinders hidden (zip expectedTypes patterns) of
        Nothing -> patterns
        Just slots -> go depth slots
      where
        go _ [] = []
        go currentDepth (Left _ : rest) =
          go (currentDepth + 1) rest
        go currentDepth (Right (expected, pattern') : rest) =
          let repaired = repairPattern currentDepth expected pattern'
           in repaired
                : go
                    (currentDepth + patBindersC repaired)
                    rest

    repairBridges depth [] = ([], depth)
    repairBridges depth (bridge : rest) =
      case bridge of
        ConstructorForcedEquality left right ->
          let bridge' =
                ConstructorForcedEquality
                  (goTerm depth left)
                  (goTerm depth right)
              (rest', finalDepth) = repairBridges depth rest
           in (bridge' : rest', finalDepth)
        ConstructorPropositionalBridge proposition proof ->
          let bridge' =
                ConstructorPropositionalBridge
                  (goTerm depth proposition)
                  (goTerm depth proof)
              (rest', finalDepth) = repairBridges (depth + 1) rest
           in (bridge' : rest', finalDepth)

    nominalInstance value =
      case force evaluation value of
        VGlobI family universes _ -> Just (family, universes)
        _ -> Nothing

-- | Materialize the solved universe substitution in every semantic artifact
-- that survives the module boundary. The assignment map is elaborator state;
-- finalized Core and imported interfaces must be closed on their own.
finalizeLevelArtifacts :: CheckM ()
finalizeLevelArtifacts = do
  st <- get
  let assignments = csLevelAssignments st
      ec = ecOf st
      currentModule = csModule st
      zonkCurrentMap transform =
        Map.mapWithKey
          (\global value ->
             if gnameInModule global currentModule
               then transform global value
               else value)
      zonkCurrentOwner transform owner value =
        if gnameInModule owner currentModule
          then transform value
          else value
      finalUniverseArity global =
        (dutParameterCount . gdUniverses <$> Map.lookup global (csGlobals st))
          <|> (dutParameterCount . ciUniverses <$> Map.lookup global (csCtors st))
      -- A final arity of zero is itself a complete projection proof: none of
      -- the provisional dependency metas survived in the referenced schema.
      -- Remove only that obsolete all-meta spine here. Nonzero mismatches stay
      -- intact so the finalized-Core validator rejects rather than guessing a
      -- retained-position mapping.
      canonicalizeMonomorphicReferences =
        mapPatternConstructorUniverses
          (\constructor universes ->
             if not (null universes) && finalUniverseArity constructor == Just 0
               then []
               else universes)
          . mapTermWithDepth
              (\_ -> \case
                 CGlobal global universes
                   | not (null universes)
                   , finalUniverseArity global == Just 0 -> Just (CGlobal global [])
                 CCtorI constructor universes annotation arguments
                   | not (null universes)
                   , finalUniverseArity constructor == Just 0 ->
                       Just (CCtorI constructor [] annotation arguments)
                 _ -> Nothing)
              0
      resolveTermMeta = resolvedMetaCore st ec
      zonkTermWithLevels resolveLevel =
        -- Finalization is a substitution over already checked dependent Core,
        -- not a second elaboration pass. Rewriting evidence-selected
        -- operations independently in types and terms can invalidate
        -- eliminator telescopes and proof arguments. Operations whose
        -- evidence was established during elaboration are already canonical;
        -- late cases retain their checked generic lowering.
        canonicalizeMonomorphicReferences
          . zonkTermWith resolveTermMeta resolveLevel 0
      zonkTerm = zonkTermWithLevels (substituteLevelMetas assignments)
      ownerLevelResolver = resolveFinalizedOwnerLevel st
      zonkOwnedTerm owner = zonkTermWithLevels (ownerLevelResolver owner)
      zonkValue value =
        let term = zonkTerm (quote ec 0 value)
         in if termScopedAt 0 term then eval ec [] term else value
      zonkOwnedValue owner value =
        let term = zonkOwnedTerm owner (quote ec 0 value)
         in if termScopedAt 0 term then eval ec [] term else value
      zonkGlobal global def =
        let coreType = zonkOwnedTerm global <$> gdCoreType def
            coreBody = zonkOwnedTerm global <$> (Map.lookup global (csCoreBodies st) <|> gdCoreBody def)
         in def
              { gdType = case coreType of
                  Just ty | termScopedAt 0 ty -> eval ec [] ty
                  _ -> zonkValue (gdType def)
              , gdCoreType = coreType
              , gdValue = case coreBody of
                  Just body -> Just (eval ec [] body)
                  Nothing ->
                    if Map.member global (csTraits st)
                         || globalValueIsUniverseInterface
                              (csUniverseInterfaceValues st) global def
                      then zonkOwnedValue global <$> gdValue def
                      else gdValue def
              , gdCoreBody = coreBody
              }
      zonkData owner info =
        info {diLevel = ownerLevelResolver owner (diLevel info)}
      zonkCtor owner info = info {ciType = zonkOwnedTerm owner (ciType info)}
      zonkTrait owner info =
        info {tiSupers = [(name, zonkOwnedTerm owner term) | (name, term) <- tiSupers info]}
      zonkInstance entry =
        entry
          { ieTraitUniverses = map (ownerLevelResolver (ieDict entry)) (ieTraitUniverses entry)
          , ieUniverses = zonkUniverseTelescope (ieUniverses entry)
          , iePremises = map (zonkOwnedTerm (ieDict entry)) (iePremises entry)
          , ieHead = map (zonkOwnedTerm (ieDict entry)) (ieHead entry)
          }
      zonkUniverseTelescope telescope = telescope
      zonkPreInstance entry =
        entry
          { piFvTele = [te {teDomain = zonkOwnedTerm (piDictG entry) (teDomain te)} | te <- piFvTele entry]
          , piPremTms = map (zonkOwnedTerm (piDictG entry)) (piPremTms entry)
          , piArgTms = map (zonkOwnedTerm (piDictG entry)) (piArgTms entry)
          }
      zonkEffLabel info =
        let zonkEffectTerm = zonkOwnedTerm (eliIface info)
            zonkEffectValue = zonkOwnedValue (eliIface info)
            zonkEffectLevel = ownerLevelResolver (eliIface info)
         in
        info
          { eliParams = [entry {teDomain = zonkEffectTerm (teDomain entry)} | entry <- eliParams info]
          , eliFixedArgs = fmap (map zonkEffectValue) (eliFixedArgs info)
          , eliFixedUniverses = fmap (map zonkEffectLevel) (eliFixedUniverses info)
          , eliOps = map (zonkEffOp zonkEffectTerm) (eliOps info)
          }
      zonkEffOp zonkEffectTerm info =
        info
          { eoiImplicits = [entry {teDomain = zonkEffectTerm (teDomain entry)} | entry <- eoiImplicits info]
          , eoiArgs = [entry {teDomain = zonkEffectTerm (teDomain entry)} | entry <- eoiArgs info]
          , eoiResT = zonkEffectTerm (eoiResT info)
          }
      zonkTermination decl =
        decl
          { tdSigType = zonkOwnedValue (tdName decl) (tdSigType decl)
          , tdCoreBody = zonkOwnedTerm (tdName decl) (tdCoreBody decl)
          }
      globalsZonked = zonkCurrentMap zonkGlobal (csGlobals st)
      constructorsFinal = zonkCurrentMap zonkCtor (csCtors st)
      finalizedContext = ec {ecGlobals = Globals globalsZonked}
      repairPatterns =
        repairConstructorPatternUniverseSpines
          finalizedContext
          constructorsFinal
      coreBodiesFinal =
        Map.map repairPatterns
          (zonkCurrentMap zonkOwnedTerm (csCoreBodies st))
      globalsFinal =
        Map.map
          (\definition ->
             definition
               { gdCoreBody = repairPatterns <$> gdCoreBody definition
               })
          globalsZonked
      finalized =
        setCheckInstances
          [ zonkCurrentOwner zonkInstance (ieDict entry) entry
          | entry <- csInstances st
          ] $
        st
          { csGlobals = globalsFinal
          , csDatas = zonkCurrentMap zonkData (csDatas st)
          , csCtors = constructorsFinal
          , csTraits = zonkCurrentMap zonkTrait (csTraits st)
          , csBareTypeLevels = Map.map (substituteLevelMetas assignments) (csBareTypeLevels st)
          , csPreInstances =
              Map.map
                (fmap (\entry -> zonkCurrentOwner zonkPreInstance (piDictG entry) entry))
                (csPreInstances st)
          , csModEffLabels = Map.map zonkEffLabel (csModEffLabels st)
          , csEffectInterfaces =
              Map.map
                (\info -> zonkCurrentOwner zonkEffLabel (eliIface info) info)
                (csEffectInterfaces st)
          , csCoreBodies = coreBodiesFinal
          , csCoreSignatures =
              Map.filterWithKey
                (\global _ -> not (gnameInModule global currentModule))
                (csCoreSignatures st)
          , csBackendIntrinsics = Map.map zonkTerm (csBackendIntrinsics st)
          , csFoundationProviders = Map.map zonkTerm (csFoundationProviders st)
          , csTerminationDecls =
              Map.map
                (\declaration ->
                   zonkCurrentOwner zonkTermination (tdName declaration) declaration)
                (csTerminationDecls st)
          }
  put (invalidateSemanticCaches finalized)

-- | Final module solving can revisit an inconsistency already diagnosed while
-- checking a declaration body. 'reportLevelSolveError' deduplicates that
-- report, so closeout must distinguish "already explained" from "solver
-- failed silently" before adding the generic residual diagnostic.
levelConstraintFailureAlreadyReported :: CheckState -> LevelConstraint -> Bool
levelConstraintFailureAlreadyReported state constraint =
  any matches (csDiags state)
  where
    assignments = csLevelAssignments state
    normalized =
      renderLevel (substituteLevelMetas assignments (lcLhs constraint))
        <> " <= "
        <> renderLevel (substituteLevelMetas assignments (lcRhs constraint))
    ownerKey =
      gKey <$> Map.lookup (lcIdentity constraint) (csLevelConstraintOwners state)
    sourceSpan =
      Map.lookup (lcIdentity constraint) (csLevelConstraintSpans state)
    matches diagnostic =
      dCode diagnostic
        `elem` [ "E_UNIVERSE_CONSTRAINT_UNSATISFIABLE"
               , "E_UNIVERSE_SELF_CONTAINMENT"
               ]
        && lookup "normalizedFailedConstraint" (pFields (dPayload diagnostic))
             == Just normalized
        && lookup "declaration" (pFields (dPayload diagnostic)) == ownerKey
        && maybe True (== dPrimary diagnostic) sourceSpan

-- | A semantic level operation must ultimately produce either a TypeLevel
-- value or the Bool result of a level comparison. This cheap typed filter runs
-- before re-elaborating a captured source equation, so unrelated transparent
-- definitions (especially proof terms) are never inspected as alias
-- candidates. Exact operation identity is still established structurally by
-- 'classifyLevelOperatorTerm'.
levelOperatorResultCarrier :: Value -> CheckM Bool
levelOperatorResultCarrier = go False 0
  where
    go consumedTypeLevel level value = forceM value >>= \case
      VPiM _ _ _ _ _ domain closure -> do
        domain' <- forceM domain
        let consumesTypeLevel =
              consumedTypeLevel
                || case domain' of
                     VGlobN g [] -> g == prelTypeLevel
                     _ -> False
        clApp closure (VRigid level []) >>= go consumesTypeLevel (level + 1)
      VGlobN g [] ->
        pure
          ( g == prelTypeLevel
              || (g == prelBool && consumedTypeLevel)
          )
      _ -> pure False

rememberLevelOperatorAlias :: GName -> LevelOperatorIdentity -> CheckM ()
rememberLevelOperatorAlias g identity =
  modify' $ \st ->
    st {csLevelOperatorAliases = Map.insert g identity (csLevelOperatorAliases st)}

-- | Authenticate one overloaded TypeLevel operation by exact member identity,
-- carrier, and selected dictionary. Both the user-facing operator aliases and
-- the underlying trait members can appear in finalized Core, so spelling is
-- never the authorization boundary.
authenticatedStandardLevelOperator :: GName -> [(Icit, Term)] -> CheckM (Maybe LevelOperatorIdentity)
authenticatedStandardLevelOperator operation arguments =
  case Map.lookup operation standardOperators of
    Nothing -> pure Nothing
    Just (identity, trait) ->
      case [argument | (Impl, argument) <- arguments] of
        carrier : dictionary : _
          | termHeadGlob (stripIdentityWrappers carrier) == Just prelTypeLevel -> do
              standard <- standardTypeLevelDictionary trait dictionary
              pure (if standard then Just identity else Nothing)
        _ -> pure Nothing
  where
    standardOperators = Map.fromList
      [ (gPrel "zero", (LevelOperatorZero, gPrel "Zero"))
      , (gPrel "one", (LevelOperatorOne, gPrel "One"))
      , (gPrel "fromInteger", (LevelOperatorFromInteger, gPrel "FromInteger"))
      , (prelSucc, (LevelOperatorSucc, prelSuccessor))
      , (gPrel "+", (LevelOperatorAdd, gPrel "Add"))
      , (gPrel "add", (LevelOperatorAdd, gPrel "Add"))
      , (prelMaxOp, (LevelOperatorMax, prelMax))
      , (gPrel "<", (LevelOperatorLt, prelOrd))
      , (gPrel "<=", (LevelOperatorLe, prelOrd))
      ]

-- | §3.1.9 expected/actual mismatch payload (the @kappa.type.mismatch@
-- family MUST expose it when both sides are available). The compact
-- rendered fragments are the user-facing renderings (already zonked and
-- metavar-hygienic, §3.1.11). The mismatch kind defaults to
-- @expression-type@ — the bare type-equality check shape (§3.1.9
-- ExpectedActualMismatchKind).
mismatchPayload :: Text -> Text -> Payload
mismatchPayload expectedR actualR =
  withPayloadField "expected" expectedR $
    withPayloadField "actual" actualR $
      withPayloadField "mismatchKind" "expression-type" $
        payloadKind "expected-actual"

-- | The (label, interface) entries of a fully-concrete effect row (ending
-- in @__effRowNil@); Nothing if the row has a non-cons tail (e.g. a
-- metavariable), where this subsumption does not apply.
rowEntriesV :: Value -> CheckM (Maybe [(Value, Value)])
rowEntriesV row0 = do
  row <- forceM row0
  case row of
    VGlobN (GName _ "__effRowNil") [] -> pure (Just [])
    VGlobN (GName _ "__effRowCons") [(_, l), (_, e), (_, rest)] -> do
      mrest <- rowEntriesV rest
      pure (fmap ((l, e) :) mrest)
    _ -> pure Nothing

sameLabelV :: Value -> Value -> CheckM Bool
sameLabelV a b = do
  aF <- forceM a
  bF <- forceM b
  pure $ case (aF, bF) of
    (VGlobN g1 [], VGlobN g2 []) -> g1 == g2
    (VCtor g1 [], VCtor g2 []) -> g1 == g2
    _ -> False

withUniverseDiagnosticSpan :: Span -> CheckM a -> CheckM a
withUniverseDiagnosticSpan source action = do
  previous <- gets csUniverseDiagnosticSpan
  modify' $ \state -> state {csUniverseDiagnosticSpan = Just source}
  result <- action
  modify' $ \state -> state {csUniverseDiagnosticSpan = previous}
  pure result

reportRigidLevelConversionFailure
  :: Ctx
  -> Span
  -> Level
  -> Level
  -> CheckM ()
reportRigidLevelConversionFailure ctx sp lhs rhs = do
  assumptions <- effectiveLevelAssumptions ctx
  let origin = ConstraintOrigin "sort conversion" "type conversion"
      constraint = LevelConstraint (-1) lhs rhs origin assumptions
  owner <- gets csActiveUniverseDefinition
  reportLevelSolveErrorWithProvenance
    owner
    (Just sp)
    (LevelConstraintDisproved constraint)

reportBorrowViewRegionMismatch
  :: Ctx
  -> Span
  -> Value
  -> Value
  -> CheckM ()
reportBorrowViewRegionMismatch ctx site actualRegion expectedRegion = do
  actualTerm <- quoteIn ctx actualRegion >>= zonkTermM (ctxLen ctx)
  expectedTerm <- quoteIn ctx expectedRegion >>= zonkTermM (ctxLen ctx)
  let actualText = renderTerm actualTerm
      expectedText = renderTerm expectedTerm
      origin = rigidOrigin actualRegion
      withOrigin diagnostic =
        case origin of
          Just source | source /= noSpan ->
            withRelated
              (related RoleBorrowStart source "borrow region introduced here")
              diagnostic
          _ -> diagnostic
  report $
    withPayload
      ( withPayloadField "actualRegion" actualText $
          withPayloadField "expectedRegion" expectedText $
            payloadKind "borrow-escape"
      ) $
      withOrigin $
        withRelated
          (related RoleBorrowEscapeSite site "borrowed view would escape under a different region")
          ( diag SevError StageElaborate "E_QTT_BORROW_ESCAPE"
              (Just "kappa.borrow.escape") site
              "a first-class borrowed view cannot be retagged to an unrelated rigid region (§12.3, §12.4.3)"
          )
  where
    rigidOrigin region =
      case region of
        VRigid level [] ->
          ceOrigin
            <$> listToMaybe
              (drop (ctxLen ctx - level - 1) (ctxEntries ctx))
        _ -> Nothing

-- | Strip §12.3.1 capture-annotation layers (elimination positions use
-- the underlying type; the annotation itself is part of type identity).
peelCapturesM :: Value -> CheckM Value
peelCapturesM v = fst <$> peelCapturesWithRegionsM v

-- | Capture annotations do not add a callable binder, but their exact region
-- witnesses remain useful while elaborating a borrowed Pi application. Keep
-- them alongside the elimination view instead of discarding the only typed
-- constraint that can solve an omitted anonymous-region argument.
peelCapturesWithRegionsM :: Value -> CheckM (Value, [Value])
peelCapturesWithRegionsM v = do
  v' <- forceM v
  case v' of
    VGlobI global _ ((_, inner) : (_, region) : _)
      | global == prelCaptures -> do
          (underlying, regions) <- peelCapturesWithRegionsM inner
          pure (underlying, regions ++ [region])
    _ -> pure (v', [])

-- | View an outer §12.3.1 capture annotation without confusing absence with
-- the explicit empty set.  Nested wrappers are the canonical Core encoding
-- of one finite set.
captureAnnotationView :: Value -> CheckM (Value, [Value], Bool)
captureAnnotationView value = do
  forced <- forceM value
  case forced of
    VGlobI global _ ((_, inner) : (_, region) : _)
      | global == prelCaptures -> do
          (underlying, regions, _) <- captureAnnotationView inner
          pure (underlying, regions ++ [region], True)
    _ -> pure (forced, [], False)

renderCaptureRegions :: Ctx -> [Value] -> CheckM Text
renderCaptureRegions ctx regions = do
  rendered <- mapM (fmap renderTerm . quoteIn ctx) regions
  pure ("{" <> T.intercalate ", " rendered <> "}")

reportCaptureSetMismatch :: Ctx -> Span -> [Value] -> [Value] -> [Value] -> CheckM ()
reportCaptureSetMismatch ctx site inferred demanded missing = do
  inferredText <- renderCaptureRegions ctx inferred
  demandedText <- renderCaptureRegions ctx demanded
  missingText <- renderCaptureRegions ctx missing
  report $
    withPayload
      ( withPayloadField "valueExpression" (T.pack (show site)) $
          withPayloadField "inferredCaptureSet" inferredText $
            withPayloadField "demandedCaptureSet" demandedText $
              withPayloadField "missingRegions" missingText $
                withPayloadField "regionOrigins" (T.pack (show site)) $
                  withPayloadField "enclosingInterface" (T.pack (show site)) $
                    payloadKind "capture-set-mismatch"
      ) $
      diag SevError StageElaborate "E_CAPTURE_SET_MISMATCH" (Just "kappa.capture.mismatch") site
        "the value's hidden region environment is not contained in the demanded capture annotation (§12.3.1)"

-- | Minimal explicit capture environment of a closure literal.  Free locals
-- inherit capture annotations from their checked types; borrowed locals add
-- the resolved region installed by 'recordBinderCaptureRegion'.  Anonymous
-- borrows are returned separately because no surface annotation can name
-- their rigid region.
lambdaCaptureRequirements :: Ctx -> Expr -> CheckM ([(Value, Span)], [Span])
lambdaCaptureRequirements ctx expression = do
  requirements <- fmap concat $ forM (freeVarOccurrences expression) $ \occurrence ->
    case lookupCtx (nameText occurrence) ctx of
      Nothing -> pure []
      Just (_, entry) ->
        case Map.lookup (nameText occurrence) (ctxBorrowCaptureRegions ctx) of
          Just (Just region) -> pure [Left (region, nameSpan occurrence)]
          Just Nothing -> pure [Right (nameSpan occurrence)]
          Nothing -> do
            (_, regions, annotated) <- captureAnnotationView (ceType entry)
            pure [Left (region, nameSpan occurrence) | annotated, region <- regions]
  pure
    ( [entry | Left entry <- requirements]
    , [site | Right site <- requirements]
    )

-- | Is the value (in whnf) headed by a projection of an opaque member
-- of a sealed package (§13.2.10)?
opaqueSealHead :: Value -> CheckM Bool
opaqueSealHead v = do
  v' <- forceM v
  case v' of
    VProjN _ r f -> do
      r' <- forceM r
      case r' of
        VSealV ls _ -> pure (f `elem` ls)
        _ -> pure False
    VAppN _ h _ -> opaqueSealHead h
    _ -> pure False

-- ── Names ────────────────────────────────────────────────────────────
