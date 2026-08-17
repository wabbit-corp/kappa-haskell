-- | Declaration processing: registering and checking top-level forms.
--
-- Helpers behind the declaration passes — publishing a declaration's
-- interface, aligning constructor telescopes, and the universe bookkeeping
-- that has to happen once an SCC's principal telescope is known.
--
-- Carved out of "Kappa.Check" as part of splitting that module; see
-- "Kappa.Check.Types" for the shared data dictionary and docs\/CONCEPTS.md
-- for the vocabulary these assume.
module Kappa.Check.Decls
  ( allNamesIn
  , closeCompletedProvisionalBodyUniverses
  , compactCompletedModuleUniverseState
  , constructorInterfaceTermsByOwner
  , constructorUniverseRoles
  , dataNominalRequirements
  , dataNominalSignatureClosure
  , declarationBodyUniverseOwners
  , declarationUniverseDeferralClosure
  , declarationUniverseScopeContains
  , deferSignatureHoles
  , extendUniversePublicationConsumers
  , installDataNominalSummary
  , mapSelectedKeysWithKey
  , monotoneCandidatesOfTerm
  , neutralLevelTermToCore
  , nominalClosureClause
  , nominalPhysicalSaturationArity
  , opaqueSealPass
  , predeclarePassRaw
  , previewOwnedInterfaceUniverseAssignments
  , principalizeDeclarationUniverses
  , principalizeFinalizedOccurrenceUniversesInScope
  , projectGeneralizableLevelMetas
  , recordSelectedMonotoneEvidence
  , renderSelectedLevel
  , reportConstructorSize
  , restrictDeclarationUniverseScope
  , rewriteConstructorResultHead
  , rewriteConstructorTypeResultHead
  , sigSatisfactionPass
  , signatureDeclarationName
  , signedLetNames
  , sourceDeclarationSymbols
  , traitNominalRequirements
  , traitNominalSignatureClosure
  , universePublicationConsumers
  , validateModuleConstructorBindings
  , certifyClosedBuiltinData
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

constructorSchemaGeneralizableMetas :: Term -> Set LevelMeta
constructorSchemaGeneralizableMetas term =
  Set.intersection
    (durGeneralizable (constructorUniverseRoles term))
    (schemaBearingLevelMetas term)

levelMetasByOwner
  :: Map LevelMeta (Set GName)
  -> Map GName (Set LevelMeta)
levelMetasByOwner =
  Map.foldlWithKey'
    (\byOwner meta owners ->
       Set.foldl'
         (\current owner ->
            Map.alter
              (Just . Set.insert meta . fromMaybe Set.empty)
              owner
              current)
         byOwner
         owners)
    Map.empty

constructorsByData
  :: Map GName CtorInfo
  -> Map GName (Map GName CtorInfo)
constructorsByData =
  Map.fromListWith Map.union
    . map
        (\(ctor, info) ->
           (ciData info, Map.singleton ctor info))
    . Map.toList

-- | Before signed term bodies have been checked, every declaration whose
-- semantic interface depends (transitively) on one of those terms must remain
-- provisional as well. Finalizing only the signed term itself freezes caller
-- lifts and result classifiers against an incomplete callee schema. Constructor
-- facets participate independently but follow a deferred parent data facet.
declarationUniverseDeferralClosure :: CheckState -> Set GName -> Set GName
declarationUniverseDeferralClosure st roots =
  DirectedGraph.reachableFrom reverseDependencies roots
  where
    globals =
      Map.filterWithKey
        (\(GName owner _) _ -> owner == csModule st)
        (csGlobals st)
    constructors =
      Map.filterWithKey
        (\(GName owner _) _ -> owner == csModule st)
        (csCtors st)
    traitTerms global =
      maybe [] (map snd . tiSupers) (Map.lookup global (csTraits st))
    globalDependencies global definition =
      Set.unions . map globalsOfTerm $
        globalUniverseInterfaceTerms st global definition
          ++ traitTerms global
          ++ maybe [] pure (Map.lookup global (csCoreBodies st))
    constructorDependencies info = globalsOfTerm (ciType info)
    reverseDependencies =
      DirectedGraph.fromEdges
        ( [ (dependency, global)
          | (global, definition) <- Map.toAscList globals
          , dependency <- Set.toAscList (globalDependencies global definition)
          ]
            ++ [ (dependency, constructor)
               | (constructor, info) <- Map.toAscList constructors
               , dependency <-
                   Set.toAscList
                     (Set.insert (ciData info) (constructorDependencies info))
               ]
        )

constraintMetaClosure :: Set LevelMeta -> [LevelConstraint] -> Set LevelMeta
constraintMetaClosure roots constraints =
  reachableLevelMetas (levelMetaAdjacency (map constraintLevelMetas constraints)) roots

-- | Project source-generalizable identities through the current level
-- substitution without transferring their inference role to elaboration-only
-- metas occurring inside the resulting expression. Generalizability is
-- provenance, not a property inherited by the arms of a solved @max@. A
-- substitution may eliminate a source meta or identify it with another source
-- meta in the same declaration SCC; it must never turn a dependency occurrence
-- into a declaration parameter.
projectGeneralizableLevelMetas
  :: Map LevelMeta Level
  -> Set LevelMeta
  -> Set LevelMeta
projectGeneralizableLevelMetas assignments origins =
  Set.intersection origins . Set.fromList $
    [ projected
    | origin <- Set.toList origins
    , projected <-
        levelMetas
          (normalizeLevel (substituteLevelMetas assignments (LMeta origin)))
    ]

-- | Materialize only occurrences retained by the selected declaration bodies.
-- This is the body-completion counterpart of the callee-oriented SCC helper
-- above: it closes a completed consumer without touching uses retained by
-- still-open declarations.
materializeProvisionalUniverseConstraintsConsumedBy :: Set GName -> CheckM ()
materializeProvisionalUniverseConstraintsConsumedBy consumers = do
  occurrenceIds <- gets $ \state ->
    Set.unions
      [ Map.findWithDefault
          Set.empty
          consumer
          (csProvisionalUniverseInstantiationsByConsumer state)
      | consumer <- Set.toList consumers
      ]
  materializeProvisionalUniverseConstraints occurrenceIds

declarationUniverseScopeContains :: DeclarationUniverseScope -> GName -> Bool
declarationUniverseScopeContains scope owner =
  case scope of
    GeneralizeAllExcept deferred -> owner `Set.notMember` deferred
    GeneralizeOnly selected -> owner `Set.member` selected

restrictDeclarationUniverseScope
  :: DeclarationUniverseScope
  -> Map GName value
  -> Map GName value
restrictDeclarationUniverseScope scope values =
  case scope of
    GeneralizeAllExcept deferred -> Map.withoutKeys values deferred
    GeneralizeOnly selected -> Map.restrictKeys values selected

mapSelectedKeysWithKey
  :: Ord key
  => Set key
  -> (key -> value -> value)
  -> Map key value
  -> Map key value
mapSelectedKeysWithKey selected transform values =
  Set.foldl'
    (\updated key -> Map.adjust (transform key) key updated)
    values
    selected

universePublicationOwnerTerms :: CheckState -> Map GName [Term]
universePublicationOwnerTerms state =
  let ec = ecOf state
   in Map.unionsWith
        (++)
        [ Map.mapWithKey
            (\owner definition ->
               globalCoreType ec definition
                 : maybe [] pure (Map.lookup owner (csCoreBodies state)))
            (csGlobals state)
        , Map.map (map snd . tiSupers) (csTraits state)
        , constructorInterfaceTermsByOwner (csCtors state)
        , Map.fromListWith
            (++)
            [ ( ieDict entry
              , map CSort (ieTraitUniverses entry)
                  ++ iePremises entry
                  ++ ieHead entry
              )
            | entry <- csInstances state
            ]
        , Map.fromListWith
            (++)
            [ ( piDictG entry
              , map teDomain (piFvTele entry)
                  ++ piPremTms entry
                  ++ piArgTms entry
              )
            | Just entry <- Map.elems (csPreInstances state)
            ]
        , Map.mapWithKey
            (\owner _ -> effectUniverseInterfaceTerms state owner)
            (csEffectInterfaces state)
        , Map.map
            (\case
               PendingTraitNominalSummary _ _ clauses _ -> clauses
               PendingDataNominalSummary {} -> [])
            (csNominalSummaryRequests state)
        ]

extendUniversePublicationConsumers
  :: Map GName [Term]
  -> UniversePublicationConsumers
  -> UniversePublicationConsumers
extendUniversePublicationConsumers ownerTerms consumers0 =
  Map.foldlWithKey'
    (\consumers owner terms ->
       Set.foldl'
         (\index target -> Map.insertWith Set.union target (Set.singleton owner) index)
         consumers
         (Set.unions (map globalsOfTerm terms)))
    consumers0
    ownerTerms

universePublicationConsumers :: CheckState -> UniversePublicationConsumers
universePublicationConsumers state =
  extendUniversePublicationConsumers
    (universePublicationOwnerTerms state)
    Map.empty

-- | Minimize each declaration SCC's own result-classifier metas before
-- provisional dependency occurrences are materialized. A callee such as
-- @List : (A : Type u) -> Type r@ owns the principal choice @r = 0@;
-- allowing caller constraints to participate first can incorrectly identify
-- @r@ with the caller's reusable @u@ and make a Type0 carrier monomorphic.
-- Parameter-position metas and fresh dependency instantiations are left for
-- the complete SCC generalizer below.
minimizeOwnedDeclarationClassifiers
  :: DeferredExplicitUniverseTreatment
  -> DeclarationUniverseScope
  -> Set GName
  -> Set GName
  -> Set GName
  -> Set GName
  -> CheckM ()
minimizeOwnedDeclarationClassifiers
    deferredExplicitTreatment
    scope
    preexisting
    preexistingCtors
    sourceGlobals
    sourceCtors =
  do
  st0 <- get
  let currentModule = csModule st0
      globals =
        Map.filterWithKey
          (\g@(GName owner _) definition ->
             owner == currentModule
               && g `Set.notMember` csFinalizedUniverseInterfaces st0
               -- A signed body may remain deferred, but a source-written
               -- universe schema is already a complete public interface.
               -- Close its checker-created occurrence levels before another
               -- declaration can observe the signature.
               && ( declarationUniverseScopeContains scope g
                      || ( deferredExplicitTreatment == MinimizeDeferredExplicitUniverses
                             && dutExplicit (gdUniverses definition)
                         )
                  )
               && (g `Set.notMember` preexisting || g `Set.member` sourceGlobals))
          ( case deferredExplicitTreatment of
              MinimizeDeferredExplicitUniverses -> csGlobals st0
              PreserveDeferredExplicitUniverses ->
                restrictDeclarationUniverseScope scope (csGlobals st0)
          )
      candidateNames = Map.keysSet globals
      ec0 = ecOf st0
      constructorTerms =
        constructorInterfaceTermsByOwner
          ( Map.filter
              (\info -> ciData info `Set.member` candidateNames)
              (csCtors st0)
          )
      termsOf g gd =
        globalUniverseInterfaceTerms st0 g gd
          ++ Map.findWithDefault [] g constructorTerms
          ++ maybe [] pure (Map.lookup g (csCoreBodies st0))
      dependencies terms =
        Set.toList
          (Set.intersection candidateNames (Set.unions (map globalsOfTerm terms)))
      graph =
        [ (g, g, dependencies (termsOf g gd))
        | (g, gd) <- Map.toList globals
        ]
      components =
        [ case component of
            AcyclicSCC g -> [g]
            CyclicSCC gs -> sort gs
        | component <- stronglyConnComp graph
        ]
      eligibleConstructors =
        Map.filterWithKey
          (\ctor info ->
             let ownerExplicit =
                   maybe False (dutExplicit . gdUniverses)
                     (Map.lookup (ciData info) (csGlobals st0))
              in ciData info `Set.member` candidateNames
                   && ctor `Set.notMember` csFinalizedUniverseInterfaces st0
                   && ciData info `Set.notMember` csFinalizedUniverseInterfaces st0
                   && ( declarationUniverseScopeContains scope ctor
                          || ( deferredExplicitTreatment == MinimizeDeferredExplicitUniverses
                                 && ownerExplicit
                             )
                      )
                   && ( declarationUniverseScopeContains scope (ciData info)
                          || ( deferredExplicitTreatment == MinimizeDeferredExplicitUniverses
                                 && ownerExplicit
                             )
                      )
                   && (ctor `Set.notMember` preexistingCtors || ctor `Set.member` sourceCtors))
          ( case deferredExplicitTreatment of
              MinimizeDeferredExplicitUniverses -> csCtors st0
              PreserveDeferredExplicitUniverses ->
                restrictDeclarationUniverseScope scope (csCtors st0)
          )
      eligibleConstructorsByData = constructorsByData eligibleConstructors
      generalizableByOwner =
        csLevelGeneralizableMetasByOwner st0
  forM_ components $ \component -> do
    st <- get
    let ec = ecOf st
        assignments = csLevelAssignments st
        zonk = zonkLevels assignments
        terms =
          [ zonk term
          | g <- component
          , Just gd <- [Map.lookup g (csGlobals st)]
          , term <- globalUniverseInterfaceTerms st g gd
          ]
        componentSet = Set.fromList component
        ownedSymbols =
          Set.union componentSet . Set.unions $
            [ Map.keysSet
                (Map.findWithDefault Map.empty owner eligibleConstructorsByData)
            | owner <- component
            ]
        roles = mconcat (map declarationUniverseRoles terms)
        explicitInterfaceMetas =
          Set.fromList
            [ meta
            | g <- component
            , Just gd <- [Map.lookup g (csGlobals st)]
            , dutExplicit (gdUniverses gd)
            , term <- globalUniverseInterfaceTerms st g gd
            , meta <- levelMetasOfTerm (zonk term)
            ]
        ownedGeneralizableMetas =
          levelMetasOwnedBy generalizableByOwner ownedSymbols
        ordinaryClassifierTargets =
          Set.difference
            ( Set.difference
                (Set.difference (durMinimizable roles) (durGeneralizable roles))
                (csLevelGeneralizableMetas st)
            )
            (csLevelInstantiationMetas st)
        -- An explicit schema has no inferred public level parameters. Any
        -- residual interface meta not introduced by source syntax is a
        -- dependency-occurrence choice and must receive its principal value
        -- under this declaration's own constraints. In particular this
        -- closes @UIO A@ to the written rigid @u@ before callers instantiate
        -- the signature. Source-generalizable metas remain errors for the
        -- complete explicit-schema check; never minimize them as recovery.
        explicitOccurrenceTargets =
          Set.difference explicitInterfaceMetas ownedGeneralizableMetas
        targets = Set.union ordinaryClassifierTargets explicitOccurrenceTargets
        constraints =
          map
            (substituteLevelConstraintMetas assignments)
            (levelConstraintsOwnedBy st ownedSymbols)
    unless (Set.null targets) $
      do
        let diagnosticSpan = Span "<universe-inference>" (Pos 1 1) (Pos 1 1)
            explicitSchema =
              any
                (\g -> maybe False (dutExplicit . gdUniverses) (Map.lookup g (csGlobals st)))
                component
        inferred <-
          inferPrincipalAtDeclarationBoundary
            diagnosticSpan (map gKey component) explicitSchema targets constraints
        case inferred of
          PrincipalBoundarySolved candidate -> installLevelAssignments candidate
          PrincipalBoundaryDeferred -> pure ()
          PrincipalBoundaryRejected _ -> pure ()
    -- A dependency's principal source-meta image is now fixed. Materialize its
    -- recorded fresh specializations before the next (dependent) SCC is
    -- minimized, so caller result classifiers see the callee's equalities and
    -- lower bounds instead of defaulting independently.
    materializeProvisionalUniverseConstraintsFor ownedSymbols

-- | A source-generalizable level remains a schema parameter unless the
-- completed declaration constraints determine it uniquely (§11.1.2.4A).
-- Compute the ordinary least candidate, then require the unconditional
-- constraint closure to prove equality in both directions. This discharges
-- pinned levels such as @0 <= u, u <= 0@ without turning a one-sided lower
-- bound into accidental monomorphism.
uniquelyDeterminedLevelMetaAssignments
  :: Set LevelMeta
  -> Set LevelMeta
  -> [LevelConstraint]
  -> Map LevelMeta Level
uniquelyDeterminedLevelMetaAssignments = uniquelyDeterminedLevelAssignmentsFor

-- | A constructor's terminal data-family application repeats the owning
-- declaration's universe spine; it is not a second source of generalized
-- parameters. Constructor telescope domains may introduce genuine local
-- universe choices, so only those domains contribute roles here.
constructorUniverseRoles :: Term -> DeclarationUniverseRoles
constructorUniverseRoles = go
  where
    go = \case
      CPiM _ _ _ _ _ domain codomain ->
        DeclarationUniverseRoles
          (Set.fromList (levelMetasOfTerm domain))
          Set.empty
          <> go codomain
      CUniverseLift _ _ _ term -> go term
      _ -> mempty

-- | Constructor telescopes are part of their owning data declaration's
-- observable interface.  In particular, references from one constructor
-- field to a sibling data family are semantic declaration dependencies even
-- though they do not occur in the family's result kind.  Every universe SCC
-- pass must therefore include these terms, or mutually recursive data schemas
-- become source-order dependent (§§11.1.2.3A and 15.16).
constructorInterfaceTermsByOwner :: Map GName CtorInfo -> Map GName [Term]
constructorInterfaceTermsByOwner =
  Map.fromListWith (++)
    . map (\info -> (ciData info, [ciType info]))
    . Map.elems

-- | Solve result-classifier metas before the SCC is generalized. The ordinary
-- solver cannot be run over every interface meta here: doing so would choose a
-- least monomorphic level for parameter-position metas which the spec requires
-- us to generalize. Explicit schemas are complete, so every residual interface
-- meta in an explicit declaration is instead a minimization obligation and is
-- never appended to the written telescope.
principalizeDeclarationUniverses
  :: DeferredExplicitUniverseTreatment
  -> DeclarationUniverseScope
  -> Set GName
  -> Set GName
  -> Set GName
  -> Set GName
  -> CheckM ()
principalizeDeclarationUniverses
    deferredExplicitTreatment
    scope
    preexisting
    preexistingCtors
    sourceGlobals
    sourceCtors =
  do
  minimizeOwnedDeclarationClassifiers
    deferredExplicitTreatment
    scope
    preexisting
    preexistingCtors
    sourceGlobals
    sourceCtors
  st0 <- get
  let currentModule0 = csModule st0
      globals0 =
        Map.filterWithKey
          (\g@(GName owner _) _ ->
             owner == currentModule0
               && g `Set.notMember` csFinalizedUniverseInterfaces st0
               && declarationUniverseScopeContains scope g
               && (g `Set.notMember` preexisting || g `Set.member` sourceGlobals))
          (restrictDeclarationUniverseScope scope (csGlobals st0))
      ctors0 =
        Map.filterWithKey
          (\g@(GName owner _) info ->
             owner == currentModule0
               && g `Set.notMember` csFinalizedUniverseInterfaces st0
               && ciData info `Set.notMember` csFinalizedUniverseInterfaces st0
               && declarationUniverseScopeContains scope g
               && declarationUniverseScopeContains scope (ciData info)
               && (g `Set.notMember` preexistingCtors || g `Set.member` sourceCtors))
          (restrictDeclarationUniverseScope scope (csCtors st0))
      ec0 = ecOf st0
      universeInterfaceValues0 = csUniverseInterfaceValues st0
      existingAssignments = csLevelAssignments st0
      zonk0 = zonkLevels existingAssignments
      traitInterfaceTerms0 =
        Map.fromListWith (++)
          [ (g, valueTerms ++ superTerms)
          | (g, info) <- Map.toList (Map.restrictKeys (csTraits st0) (Map.keysSet globals0))
          , let valueTerms =
                  maybe [] (maybe [] (pure . zonk0 . quote ec0 0) . gdValue) (Map.lookup g globals0)
                superTerms = map (zonk0 . snd) (tiSupers info)
          ]
      universeValueTerms0 =
        Map.mapMaybeWithKey
          (\global definition ->
             if globalValueIsUniverseInterface universeInterfaceValues0 global definition
               then zonk0 . quote ec0 0 <$> gdValue definition
               else Nothing)
          globals0
      globalInterfaceTerms0 =
        [ zonk0 term
        | (global, definition) <- Map.toList globals0
        , term <- globalUniverseInterfaceTerms st0 global definition
        ]
      roles0 =
        mconcat
          ( map declarationUniverseRoles globalInterfaceTerms0
              ++ map (constructorUniverseRoles . zonk0 . ciType) (Map.elems ctors0)
              ++ map declarationUniverseRoles (concat (Map.elems traitInterfaceTerms0))
              ++ map declarationUniverseRoles (Map.elems universeValueTerms0)
          )
      schemaGeneralizable0 =
        Set.unions
          ( map declarationSchemaGeneralizableMetas globalInterfaceTerms0
              ++ map (constructorSchemaGeneralizableMetas . zonk0 . ciType) (Map.elems ctors0)
              ++ map declarationSchemaGeneralizableMetas (concat (Map.elems traitInterfaceTerms0))
              ++ map declarationSchemaGeneralizableMetas (Map.elems universeValueTerms0)
          )
      generalizableOrigins0 =
        Set.intersection
          (csLevelGeneralizableMetas st0)
          schemaGeneralizable0
      instantiationOrigins0 =
        Set.difference
          (csLevelInstantiationMetas st0)
          generalizableOrigins0
      minimizableOrigins0 =
        Set.difference
          (Set.union (durMinimizable roles0) instantiationOrigins0)
          generalizableOrigins0
  componentState <- get
  let currentModule = csModule componentState
      globals =
        Map.filterWithKey
          (\g@(GName owner _) _ ->
             owner == currentModule
               && g `Set.notMember` csFinalizedUniverseInterfaces componentState
               && declarationUniverseScopeContains scope g
               && (g `Set.notMember` preexisting || g `Set.member` sourceGlobals))
          (restrictDeclarationUniverseScope scope (csGlobals componentState))
      candidateNames = Map.keysSet globals
      ec = ecOf componentState
      universeInterfaceValues = csUniverseInterfaceValues componentState
      rawGlobalTerms = Map.map (globalCoreType ec) globals
      rawBodyTerms = Map.restrictKeys (csCoreBodies componentState) candidateNames
      rawTraitInterfaceTerms =
        Map.fromListWith (++)
          [ (g, valueTerms ++ map snd (tiSupers info))
          | (g, info) <- Map.toList (Map.restrictKeys (csTraits componentState) candidateNames)
          , let valueTerms =
                  maybe [] (maybe [] (pure . quote ec 0) . gdValue) (Map.lookup g globals)
          ]
      rawInstanceInterfaceTerms =
        Map.fromList
          [ (g, instanceUniverseInterfaceTerms componentState g)
          | g <- Map.keys globals
          ]
      rawUniverseValueTerms =
        Map.mapMaybeWithKey
          (\global definition ->
             if globalValueIsUniverseInterface universeInterfaceValues global definition
               then quote ec 0 <$> gdValue definition
               else Nothing)
          globals
      rawConstructorTerms =
        constructorInterfaceTermsByOwner
          ( Map.filter
              (\info -> ciData info `Set.member` candidateNames)
              (csCtors componentState)
          )
      ctors0ByData = constructorsByData ctors0
      artifactTermsByOwner =
        Map.unionsWith
          (++)
          [ Map.map pure rawGlobalTerms
          , Map.map pure rawBodyTerms
          , rawTraitInterfaceTerms
          , rawInstanceInterfaceTerms
          , rawConstructorTerms
          , Map.map pure rawUniverseValueTerms
          ]
      artifactInstantiationOwners =
        Map.fromListWith
          Set.union
          [ (meta, Set.singleton owner)
          | (owner, terms) <- Map.toList artifactTermsByOwner
          , meta <- Set.toList (Set.fromList (concatMap levelMetasOfTerm terms))
          , meta `Set.member` csLevelInstantiationMetas componentState
          ]
      generalizableByOwner =
        csLevelGeneralizableMetasByOwner componentState
      instantiationByOwner =
        Map.unionWith
          Set.union
          (csLevelInstantiationMetasByOwner componentState)
          (levelMetasByOwner artifactInstantiationOwners)
      dependencies g =
        Set.toList . Set.intersection candidateNames . Set.unions . map globalsOfTerm $
          Map.findWithDefault [] g rawTraitInterfaceTerms
            ++ Map.findWithDefault [] g rawInstanceInterfaceTerms
            ++ Map.findWithDefault [] g rawConstructorTerms
            ++ maybe [] pure (Map.lookup g rawUniverseValueTerms)
            ++ maybe [] pure (Map.lookup g rawBodyTerms)
            ++ maybe [] pure (Map.lookup g rawGlobalTerms)
      graph = [(g, g, dependencies g) | g <- Map.keys globals]
      components =
        [ case component of
            AcyclicSCC g -> [g]
            CyclicSCC gs -> sort gs
        | component <- stronglyConnComp graph
        ]
      principalizationComponents =
        [ Set.union
            componentSet
            ( Set.unions
                [ Map.keysSet
                    (Map.findWithDefault Map.empty owner ctors0ByData)
                | owner <- component
                ]
            )
        | component <- components
        , let componentSet = Set.fromList component
        ]
  unless (Map.null artifactInstantiationOwners) $
    modify' $ \state ->
      state
        { csLevelInstantiationOwners =
            Map.unionWith
              Set.union
              (csLevelInstantiationOwners state)
              artifactInstantiationOwners
        , csLevelInstantiationMetasByOwner =
            Map.unionWith
              Set.union
              (csLevelInstantiationMetasByOwner state)
              (levelMetasByOwner artifactInstantiationOwners)
        }
  forM_ components $ \component -> do
      st <- get
      let
        componentSet = Set.fromList component
        componentCtors =
          Map.unions
            [ Map.findWithDefault Map.empty owner ctors0ByData
            | owner <- component
            ]
        ownedSymbols = Set.union componentSet (Map.keysSet componentCtors)
        assignments = csLevelAssignments st
        zonk = zonkLevels assignments
        currentGlobals = Map.restrictKeys (csGlobals st) componentSet
        globalTerms = Map.map (zonk . globalCoreType (ecOf st)) currentGlobals
        ctorTerms = Map.map (zonk . ciType) componentCtors
        traitInterfaceTerms =
          Map.fromListWith (++)
            [ (g, valueTerms ++ superTerms)
            | (g, info) <- Map.toList (Map.restrictKeys (csTraits st) componentSet)
            , let valueTerms =
                    maybe [] (maybe [] (pure . zonk . quote (ecOf st) 0) . gdValue)
                      (Map.lookup g currentGlobals)
                  superTerms = map (zonk . snd) (tiSupers info)
            ]
        instanceInterfaceTerms =
          Map.map (map zonk) (Map.restrictKeys rawInstanceInterfaceTerms componentSet)
        universeValueTerms = Map.map zonk (Map.restrictKeys rawUniverseValueTerms componentSet)
        interfaceTerms =
          Map.elems globalTerms
            ++ Map.elems ctorTerms
            ++ concat (Map.elems traitInterfaceTerms)
            ++ concat (Map.elems instanceInterfaceTerms)
            ++ Map.elems universeValueTerms
        inferredRoles =
          mconcat
            ( map declarationUniverseRoles (Map.elems globalTerms)
                ++ map constructorUniverseRoles (Map.elems ctorTerms)
                ++ map declarationUniverseRoles (concat (Map.elems traitInterfaceTerms))
                ++ map declarationUniverseRoles (concat (Map.elems instanceInterfaceTerms))
                ++ map declarationUniverseRoles (Map.elems universeValueTerms)
            )
        schemaGeneralizable =
          Set.unions
            ( map declarationSchemaGeneralizableMetas (Map.elems globalTerms)
                ++ map constructorSchemaGeneralizableMetas (Map.elems ctorTerms)
                ++ map declarationSchemaGeneralizableMetas (concat (Map.elems traitInterfaceTerms))
                ++ map declarationSchemaGeneralizableMetas (concat (Map.elems instanceInterfaceTerms))
                ++ map declarationSchemaGeneralizableMetas (Map.elems universeValueTerms)
            )
        explicitGlobals = Map.filter (dutExplicit . gdUniverses) currentGlobals
        -- A constructor spelling @C.{u}@ restates only the enclosing data
        -- family's explicit schema. Constructor-local binder classifiers may
        -- still contribute an inferred hidden suffix. The inherited
        -- 'dutExplicit' bit therefore cannot classify every meta in the
        -- constructor interface as covered by the source-written schema.
        explicitTerms =
          Map.elems (Map.restrictKeys globalTerms (Map.keysSet explicitGlobals))
            ++ concat
                 (Map.elems (Map.restrictKeys traitInterfaceTerms (Map.keysSet explicitGlobals)))
            ++ concat
                 (Map.elems (Map.restrictKeys instanceInterfaceTerms (Map.keysSet explicitGlobals)))
            ++ Map.elems (Map.restrictKeys universeValueTerms (Map.keysSet explicitGlobals))
        explicitMetas = Set.fromList (concatMap levelMetasOfTerm explicitTerms)
        interfaceMetas = Set.fromList (concatMap levelMetasOfTerm interfaceTerms)
        constraints =
          map
            (substituteLevelConstraintMetas assignments)
            (levelConstraintsOwnedBy st ownedSymbols)
        relevantMetas = constraintMetaClosure interfaceMetas constraints
        projectOrigins origins =
          Set.fromList
            [ projected
            | origin <- Set.toList origins
            , projected <-
                levelMetas
                  (normalizeLevel (substituteLevelMetas assignments (LMeta origin)))
            ]
        ownedGeneralizableOrigins =
          levelMetasOwnedBy generalizableByOwner ownedSymbols
        projectedGeneralizableOrigins =
          projectGeneralizableLevelMetas assignments ownedGeneralizableOrigins
        generalizableOrigins =
          Set.intersection projectedGeneralizableOrigins schemaGeneralizable
        ownedInstantiationOrigins =
          levelMetasOwnedBy instantiationByOwner ownedSymbols
        instantiationOrigins = projectOrigins ownedInstantiationOrigins
        instantiationMetas =
          Set.intersection relevantMetas
            (Set.difference instantiationOrigins generalizableOrigins)
        -- Explicit schema parameters are already rigid LParams. Any remaining
        -- source-generalizable meta retains that role: declaration explicitness
        -- cannot turn a polymorphic source position into a minimizable one.
        generalizable = generalizableOrigins
        explicitGeneralizable = Set.intersection explicitMetas generalizable
        -- Source provenance, not the incidental shape of elaborated Core, is
        -- the authority for generalization. Every other meta connected to the
        -- completed interface is an occurrence/result choice and must receive
        -- the SCC's principal least solution. In particular, constructor
        -- telescope domains contain freshly instantiated schemas whose Core
        -- shape is indistinguishable from a source binder after elaboration.
        minimizable =
          Set.unions
            [ durMinimizable inferredRoles
            , instantiationMetas
            , Set.difference relevantMetas generalizable
            ]
        -- A source-role identity is rigid outside the declaration component
        -- that owns it. Dependency terms can expose that identity while their
        -- fresh occurrence is still being principalized, but this component
        -- must solve the occurrence toward the source meta, never the source
        -- meta toward the occurrence. Otherwise one caller can erase another
        -- declaration's universe parameter and make schema inference depend on
        -- SCC traversal order.
        allProjectedGeneralizable =
          projectGeneralizableLevelMetas
            assignments
            (csLevelGeneralizableMetas st)
        foreignGeneralizable =
          Set.difference allProjectedGeneralizable projectedGeneralizableOrigins
        targets =
          Set.difference
            (Set.difference minimizable generalizable)
            foreignGeneralizable
      unless (Set.null explicitGeneralizable) $ do
        reportNoPrincipalUniverse component constraints True explicitGeneralizable
        -- Recovery is intentionally local and follows the diagnostic. It keeps
        -- later passes well scoped without making zero a successful schema
        -- specialization.
        installLevelAssignments (Map.fromSet (const LZero) explicitGeneralizable)
      unless (Set.null targets) $
        do
          let diagnosticSpan = Span "<universe-inference>" (Pos 1 1) (Pos 1 1)
          inferred <-
            inferPrincipalAtDeclarationBoundary
              diagnosticSpan
              (map gKey component)
              (not (Map.null explicitGlobals))
              targets
              constraints
          case inferred of
            PrincipalBoundarySolved candidate -> installLevelAssignments candidate
            PrincipalBoundaryDeferred -> pure ()
            PrincipalBoundaryRejected _ -> pure ()
  -- Source-generalizable identities are quotient-ed and uniquely solved only
  -- after every minimizable classifier/occurrence choice in the semantic SCC
  -- has reached its principal value. Reversing these phases can project a
  -- source role onto an unsolved dependency occurrence and freeze that
  -- internal choice into the public schema.
  principalizeOwnedGeneralizableMetas
    principalizationComponents
    minimizableOrigins0
  where
    reportNoPrincipalUniverse component constraints explicitSchema metas =
      reportNoPrincipalUniverseDiagnostic
        (Span "<universe-inference>" (Pos 1 1) (Pos 1 1))
        (map gKey component)
        explicitSchema
        metas
        constraints
        Nothing
        "declaration universe constraints have no unique principal solution (§11.1.3)"

-- | Complete steps 4 and 5 of §11.1.2.4A for one set of declaration owners,
-- after their minimizable metas have been solved. Constraint ownership is a
-- hard boundary: deferred declarations must not be influenced by an earlier
-- header pass that happens to share the same module state.
principalizeOwnedGeneralizableMetas
  :: [Set GName]
  -> Set LevelMeta
  -> CheckM ()
principalizeOwnedGeneralizableMetas semanticComponents minimizableOrigins =
  do
  initialState <- get
  let initialAssignments = csLevelAssignments initialState
      eligibleOwners = Set.unions semanticComponents
      componentOwners = Map.fromList (zip [0 :: Int ..] semanticComponents)
      ownerComponents =
        Map.fromList
          [ (owner, component)
          | (component, owners) <- Map.toList componentOwners
          , owner <- Set.toList owners
          ]
      generalizableByComponent =
        Map.map
          ( levelMetasOwnedBy
              (csLevelGeneralizableMetasByOwner initialState)
          )
          componentOwners
      constraints =
        map
          (substituteLevelConstraintMetas initialAssignments)
          (levelConstraintsOwnedBy initialState eligibleOwners)
      constraintGroups =
        Map.fromListWith (++)
          [ ( owner >>= (`Map.lookup` ownerComponents)
            , [constraint]
            )
          | constraint <- constraints
          , let owner =
                  Map.lookup (lcIdentity constraint) (csLevelConstraintOwners initialState)
          ]
      generalizableFor = \case
        Nothing -> Set.empty
        Just component ->
          projectGeneralizableLevelMetas initialAssignments
            (Map.findWithDefault Set.empty component generalizableByComponent)
      equivalentCandidates =
        Map.fromListWith (++)
          [ (meta, [level])
          | (owner, ownerConstraints) <- Map.toList constraintGroups
          , (meta, level) <-
              Map.toList
                ( equivalentLevelMetaAssignments
                    (projectGeneralizableLevelMetas initialAssignments (csLevelGeneralizableMetas initialState))
                    (generalizableFor owner)
                    minimizableOrigins
                    ownerConstraints
                )
          ]
      equivalentAssignments =
        Map.map head
          (Map.filter ((== 1) . length . nub) equivalentCandidates)
  unless (Map.null equivalentAssignments) $
    installLevelAssignments equivalentAssignments

  determinedState <- get
  let determinedAssignments = csLevelAssignments determinedState
      zonkConstraint = substituteLevelConstraintMetas determinedAssignments
      determinedGeneralizableByComponent =
        Map.map
          ( levelMetasOwnedBy
              (csLevelGeneralizableMetasByOwner determinedState)
          )
          componentOwners
      determinedConstraintGroups =
        Map.fromListWith (++)
          [ ( owner >>= (`Map.lookup` ownerComponents)
            , [zonkConstraint constraint]
            )
          | constraint <- levelConstraintsOwnedBy determinedState eligibleOwners
          , let owner =
                  Map.lookup (lcIdentity constraint) (csLevelConstraintOwners determinedState)
          ]
      projectedGeneralizableFor = \case
        Nothing -> Set.empty
        Just component ->
          projectGeneralizableLevelMetas determinedAssignments
            (Map.findWithDefault Set.empty component determinedGeneralizableByComponent)
      determinedCandidates =
        Map.fromListWith (++)
          [ (meta, [level])
          | (owner, ownerConstraints) <- Map.toList determinedConstraintGroups
          , (meta, level) <-
              Map.toList
                ( uniquelyDeterminedLevelMetaAssignments
                    (projectGeneralizableLevelMetas determinedAssignments (csLevelGeneralizableMetas determinedState))
                    (projectedGeneralizableFor owner)
                    ownerConstraints
                )
          ]
      uniquelyDeterminedAssignments =
        Map.map head
          (Map.filter ((== 1) . length . nub) determinedCandidates)
  unless (Map.null uniquelyDeterminedAssignments) $
    installLevelAssignments uniquelyDeterminedAssignments

-- | Principalize hidden-universe occurrences introduced after a declaration
-- interface has already been generalized. Bodies are checked after the
-- header boundary and may instantiate schemas in Core that never re-enters
-- interface generalization. Such metas are occurrence choices, never new
-- declaration parameters: solve their connected constraints and choose the
-- least level for an otherwise unconstrained occurrence.
principalizeFinalizedOccurrenceUniverses :: Set GName -> Set GName -> Set GName -> CheckM ()
principalizeFinalizedOccurrenceUniverses preexisting sourceGlobals deferredGlobals = do
  principalizeFinalizedOccurrenceUniversesInScope
    preexisting
    sourceGlobals
    (GeneralizeAllExcept deferredGlobals)

principalizeFinalizedOccurrenceUniversesInScope
  :: Set GName
  -> Set GName
  -> DeclarationUniverseScope
  -> CheckM ()
principalizeFinalizedOccurrenceUniversesInScope preexisting sourceGlobals scope = do
  st <- get
  let currentModule = csModule st
      eligible owner@(GName moduleName _) =
        moduleName == currentModule
          && declarationUniverseScopeContains scope owner
          && (owner `Set.notMember` preexisting || owner `Set.member` sourceGlobals)
      eligibleOwners =
        Set.filter eligible
          (Map.keysSet (restrictDeclarationUniverseScope scope (csGlobals st)))
      includeUnowned = case scope of
        GeneralizeAllExcept _ -> True
        GeneralizeOnly _ -> False
  principalizeFinalizedOccurrenceUniversesFor includeUnowned eligibleOwners

-- | The owner-indexed form of 'principalizeFinalizedOccurrenceUniverses'.
-- Incremental body closeout already knows the completed declaration component;
-- retaining that positive set avoids rebuilding its whole-module complement on
-- every body while running the identical selected-meta solver.
principalizeFinalizedOccurrenceUniversesFor :: Bool -> Set GName -> CheckM ()
principalizeFinalizedOccurrenceUniversesFor includeUnowned eligibleOwners = do
  st <- get
  let currentModule = csModule st
      assignments = csLevelAssignments st
      zonk = zonkLevels assignments
      unresolved origin =
        not . null . levelMetas $
          normalizeLevel (substituteLevelMetas assignments (LMeta origin))
      unresolvedOwnedOwners =
        Set.filter
          (\owner ->
             any unresolved
               (Set.toList
                 (Map.findWithDefault
                   Set.empty
                   owner
                   (csLevelInstantiationMetasByOwner st))))
          eligibleOwners
      unresolvedUnownedInstantiationOrigins
        | includeUnowned =
            Set.difference
              (Set.filter unresolved (csLevelInstantiationMetas st))
              (Map.keysSet (csLevelInstantiationOwners st))
        | otherwise = Set.empty
      eligibleGlobals =
        Map.filterWithKey
          (\global@(GName owner _) _ ->
             owner == currentModule && global `Set.member` eligibleOwners)
          (Map.restrictKeys (csGlobals st) eligibleOwners)
      projectedUnownedInstantiationMetas =
        Set.fromList
          [ projected
          | origin <- Set.toList unresolvedUnownedInstantiationOrigins
          , projected <-
              levelMetas
                (normalizeLevel (substituteLevelMetas assignments (LMeta origin)))
          ]
      artifactTerms global definition =
        map zonk (globalUniverseInterfaceTerms st global definition)
          ++ maybe [] (pure . zonk) (Map.lookup global (csCoreBodies st))
      observableUnownedOwners
        | Set.null projectedUnownedInstantiationMetas = Set.empty
        | otherwise =
            Set.fromList
              [ global
              | (global, definition) <- Map.toList eligibleGlobals
              , let artifactMetas =
                      Set.fromList
                        (concatMap levelMetasOfTerm (artifactTerms global definition))
              , not
                  ( Set.null
                      (Set.intersection artifactMetas projectedUnownedInstantiationMetas)
                  )
              ]
      currentSymbols =
        Set.union
          observableUnownedOwners
          (Set.intersection (Map.keysSet eligibleGlobals) unresolvedOwnedOwners)
      belongsToCurrent global = global `Set.member` currentSymbols
      interfaceTerms =
        [ zonk term
        | (g, definition) <- Map.toList (csGlobals st)
        , belongsToCurrent g
        , term <- globalUniverseInterfaceTerms st g definition
        ]
      bodyTerms =
        [ zonk body
        | (g, body) <- Map.toList (csCoreBodies st)
        , belongsToCurrent g
        ]
      observableMetas =
        Set.fromList (concatMap levelMetasOfTerm (interfaceTerms ++ bodyTerms))
      ownedInstantiationOrigins =
        Set.unions
          [ Map.findWithDefault
              Set.empty
              owner
              (csLevelInstantiationMetasByOwner st)
          | owner <- Set.toList currentSymbols
          ]
      candidateInstantiationOrigins =
        Set.union ownedInstantiationOrigins unresolvedUnownedInstantiationOrigins
      relevantInstantiationOrigins =
        Set.filter
          (\origin ->
             let owners =
                   Map.findWithDefault Set.empty origin (csLevelInstantiationOwners st)
                 projected =
                   Set.fromList
                     ( levelMetas
                         (normalizeLevel (substituteLevelMetas assignments (LMeta origin)))
                     )
              in not (Set.null (Set.intersection currentSymbols owners))
                   || ( origin `Set.member` unresolvedUnownedInstantiationOrigins
                          && not (Set.null (Set.intersection observableMetas projected))
                      ))
          candidateInstantiationOrigins
      instantiationMetas =
        Set.fromList
          [ projected
          | origin <- Set.toList relevantInstantiationOrigins
          , projected <-
              levelMetas
                (normalizeLevel (substituteLevelMetas assignments (LMeta origin)))
          ]
      generalizableMetas =
        Set.union
          ( projectGeneralizableLevelMetas assignments
              ( Set.unions
                  [ Map.findWithDefault
                      Set.empty
                      owner
                      (csLevelGeneralizableMetasByOwner st)
                  | owner <- Set.toList currentSymbols
                  ]
              )
          )
          ( durGeneralizable
              (mconcat (map declarationUniverseRoles interfaceTerms))
          )
      provisionalInstantiationMetas =
        unmaterializedProvisionalUniverseMetas st provisionalOccurrenceIds
      provisionalOccurrenceIds =
        Set.unions
          [ Map.findWithDefault
              Set.empty
              owner
              (csProvisionalUniverseInstantiationsByOwner st)
              `Set.union`
            Map.findWithDefault
              Set.empty
              owner
              (csProvisionalUniverseInstantiationsByConsumer st)
          | owner <- Set.toList currentSymbols
          ]
      ownedConstraints =
        concat
          [ Map.findWithDefault [] owner (csLevelConstraintsByOwner st)
          | owner <- Set.toAscList currentSymbols
          ]
      -- Unowned constraints arise at occurrence boundaries such as generated
      -- member accessors and transactional evidence search. When this closeout
      -- explicitly includes unowned occurrence metas, their constraints are
      -- part of the same solver region. Selecting the observable metas while
      -- omitting these equations lets the least-level solver minimize an
      -- occurrence before its exact rigid identity is considered.
      unownedConstraints
        | includeUnowned =
            [ constraint
            | constraint <- csLevelConstraints st
            , Map.notMember
                (lcIdentity constraint)
                (csLevelConstraintOwners st)
            ]
        | otherwise = []
      currentConstraints = ownedConstraints ++ unownedConstraints
      ownedConstraintMetas =
        Set.fromList
          [ meta
          | constraint <- currentConstraints
          , meta <- levelMetas (lcLhs constraint) ++ levelMetas (lcRhs constraint)
          ]
      -- A level can first enter through a polymorphic dependency occurrence
      -- and later become the inferred kind of a source declaration binder.
      -- The source role is authoritative: minimizing such a meta here would
      -- monomorphize the declaration before its SCC can generalize it.
      -- Likewise, occurrences of an unfinalized same-module declaration are
      -- not body-local choices yet. Their callee constraints are materialized
      -- by 'materializeProvisionalUniverseConstraints' in the complete SCC
      -- pass below; defaulting them here can select zero before a kind
      -- argument contributes its lower bound and desynchronize the rewritten
      -- Core spine from the retained constraint graph.
      seedInstantiationMetas =
        Set.difference
          (Set.difference instantiationMetas generalizableMetas)
          provisionalInstantiationMetas
      seedTargets =
        Set.intersection
          (Set.union observableMetas ownedConstraintMetas)
          seedInstantiationMetas
      constraints =
        [ substituteLevelConstraintMetas assignments constraint
        | constraint <- currentConstraints
        ]
      bodyMap = Map.restrictKeys (csCoreBodies st) currentSymbols
      bodyDependencies body =
        Set.toList (Set.intersection currentSymbols (globalsOfTerm body))
      bodyGraph =
        [ (owner, owner, bodyDependencies body)
        | (owner, body) <- Map.toList bodyMap
        ]
      recursiveComponentMembers =
        [ members
        | component <- stronglyConnComp bodyGraph
        , members <- case component of
            CyclicSCC owners -> [Set.fromList owners]
            AcyclicSCC owner
              | maybe False (Set.member owner . globalsOfTerm) (Map.lookup owner bodyMap) ->
                  [Set.singleton owner]
            _ -> []
        ]
      sameRecursiveComponent caller callee =
        any
          (\members -> caller `Set.member` members && callee `Set.member` members)
          recursiveComponentMembers
      declarationIdentityLevels global =
        case Map.lookup global (csGlobals st) of
          Nothing -> []
          Just definition
            | arity <- dutParameterCount (gdUniverses definition)
            , arity > 0 -> map LParam [0 .. arity - 1]
            | otherwise ->
                let terms =
                      map
                        (zonkLevels assignments)
                        (globalUniverseInterfaceTerms st global definition)
                    retained =
                      durGeneralizable
                        (mconcat (map declarationUniverseRoles terms))
                 in map LMeta . nub $
                      [ meta
                      | term <- terms
                      , meta <- levelMetasOfTerm term
                      , meta `Set.member` retained
                      ]
      identityCandidate occurrence = do
        guard (not (rsoExplicit occurrence))
        guard (sameRecursiveComponent (rsoCaller occurrence) (rsoCallee occurrence))
        let sourceLevels = declarationIdentityLevels (rsoCaller occurrence)
            calleeLevels = declarationIdentityLevels (rsoCallee occurrence)
            callerArity = length sourceLevels
            calleeArity = length calleeLevels
            targetLevels =
              map (normalizeLevel . substituteLevelMetas assignments) (rsoLevels occurrence)
        guard (callerArity > 0 && callerArity == calleeArity)
        guard (length targetLevels == callerArity)
        targetMetas <- traverse (\case LMeta meta -> Just meta; _ -> Nothing) targetLevels
        guard (all (`Set.member` csLevelInstantiationMetas st) targetMetas)
        let alternatives = zip targetMetas sourceLevels
            localChoices =
              Map.fromListWith (++) [(meta, [level]) | (meta, level) <- alternatives]
        guard
          ( all
              (\(meta, level) -> LMeta meta /= normalizeLevel level)
              alternatives
          )
        guard (all ((== 1) . length . nub) (Map.elems localChoices))
        let substitution = Map.map head localChoices
            affected constraint =
              any
                (`Map.member` substitution)
                (levelMetas (lcLhs constraint) ++ levelMetas (lcRhs constraint))
            preserves constraint =
              let assumptions =
                    substituteLevelAssumptions substitution (lcAssumptions constraint)
                  lower = substituteLevelMetas substitution (lcLhs constraint)
                  upper = substituteLevelMetas substitution (lcRhs constraint)
               in proveLevelLeq assumptions lower upper == Proved
        guard (all preserves (filter affected constraints))
        pure alternatives
      identityAlternatives =
        Map.fromListWith (++)
          [ (meta, [level])
          | caller <- Set.toList currentSymbols
          , occurrence <- Map.findWithDefault
              []
              caller
              (csRecursiveSchemaOccurrencesByCaller st)
          , alternatives <- maybeToList (identityCandidate occurrence)
          , (meta, level) <- alternatives
          ]
      identityDefaults =
        Map.map head
          (Map.filter ((== 1) . length . nub) identityAlternatives)
      connectedMetas = constraintMetaClosure seedTargets constraints
      -- §11.1.2.4B solves selected-meta SCCs together. The closure was
      -- previously used only to retain relevant constraints, leaving hidden
      -- occurrence metas unselected and turning ordinary occurrence chains
      -- into a spurious OutsidePortableInferenceFragment result. Select every
      -- connected occurrence-owned meta while continuing to exclude source
      -- schema identities and not-yet-materialized provisional occurrences.
      targets =
        Set.difference
          (Set.difference connectedMetas generalizableMetas)
          provisionalInstantiationMetas
      relevantConstraints =
        [ constraint
        | constraint <- constraints
        , let metas =
                Set.fromList
                  (levelMetas (lcLhs constraint) ++ levelMetas (lcRhs constraint))
        , not (Set.null (Set.intersection connectedMetas metas))
        ]
      -- A completed body may introduce fresh occurrence metas only after its
      -- public schema has been generalized.  Quotient exact equality cycles
      -- before asking the least-solution solver to minimize those
      -- occurrences.  Otherwise an occurrence equal to a protected source
      -- parameter can be selected independently as zero, destroying the
      -- already-published schema identity.  Restricting the assignments to
      -- selected occurrence targets keeps source and foreign identities rigid.
      equivalentDefaults =
        Map.restrictKeys
          ( equivalentLevelMetaAssignments
              ( projectGeneralizableLevelMetas
                  assignments
                  (csLevelGeneralizableMetas st)
              )
              generalizableMetas
              targets
              relevantConstraints
          )
          targets
      targetGroups = selectedConstraintGroups targets relevantConstraints
  if not (Map.null equivalentDefaults)
    then do
      -- Recompute the selected closure after quotienting.  Every installed
      -- assignment removes a target meta, so this recursion strictly
      -- decreases just like the recursive-schema identity path below.
      installLevelAssignments equivalentDefaults
      principalizeFinalizedOccurrenceUniversesFor includeUnowned eligibleOwners
    else if Map.null identityDefaults
      then
      forM_ targetGroups $ \(componentTargets, componentConstraints) -> do
        let componentOwners =
              Set.fromList
                [ owner
                | constraint <- componentConstraints
                , Just owner <- [Map.lookup (lcIdentity constraint) (csLevelConstraintOwners st)]
                , owner `Set.member` currentSymbols
                ]
            diagnosticSpan = Span "<universe-inference>" (Pos 1 1) (Pos 1 1)
        inferred <-
          inferPrincipalAtDeclarationBoundary
            diagnosticSpan
            (map gKey (Set.toAscList componentOwners))
            False
            componentTargets
            componentConstraints
        case inferred of
          PrincipalBoundarySolved candidate -> installLevelAssignments candidate
          PrincipalBoundaryDeferred -> pure ()
          PrincipalBoundaryRejected _ -> pure ()
      else do
        -- Re-enter with the identity defaults materialized so target components
        -- and constraints are recomputed from the new substitution. Each chosen
        -- meta disappears from 'identityCandidate', so recursion decreases.
        installLevelAssignments identityDefaults
        principalizeFinalizedOccurrenceUniversesFor includeUnowned eligibleOwners

-- | Close solver-local universe occurrences in body-complete declarations
-- without publishing their declaration telescope early. Source metas remain
-- abstract; only fresh dependency/body occurrences are solved and reflected
-- into retained Core. This makes transparent delta reduction replayable for
-- following declarations while preserving one public generalization at the
-- complete semantic SCC boundary.
closeCompletedProvisionalBodyUniverses
  :: Set GName
  -> CheckM ()
closeCompletedProvisionalBodyUniverses owners
  | Set.null owners = pure ()
  | otherwise = do
      rewriteCompletedBodyUniverses owners
      beforeClose <- get
      let unresolvedOwners =
            Set.filter
              (\owner ->
                 maybe
                   False
                   (not . globalDefinitionBodyUniversesReplayable)
                   (Map.lookup owner (csGlobals beforeClose)))
              owners
      unless (Set.null unresolvedOwners) $ do
        materializeProvisionalUniverseConstraintsConsumedBy unresolvedOwners
        principalizeFinalizedOccurrenceUniversesFor False unresolvedOwners
        rewriteCompletedBodyUniverses unresolvedOwners

-- | Reflect already-solved body-local universe occurrences into retained Core
-- while preserving each declaration's source-generalizable metas. This fast
-- path is allocation and rewriting only; callers invoke the principal solver
-- afterwards only for bodies that remain unreplayable.
rewriteCompletedBodyUniverses :: Set GName -> CheckM ()
rewriteCompletedBodyUniverses owners = do
  st <- get
  let sourceMetas owner =
        Set.fromList . concat $
          Map.findWithDefault
            []
            owner
            (csProvisionalGlobalUniverseMetas st)
      rewriteBody owner body =
        evalState
          (zonkTermM 0 body)
          st
            { csLevelAssignments =
                Map.withoutKeys
                  (csLevelAssignments st)
                  (sourceMetas owner)
            }
      bodies' =
        Set.foldl'
          (\bodies owner -> Map.adjust (rewriteBody owner) owner bodies)
          (csCoreBodies st)
          owners
      stateWithBodies = st {csCoreBodies = bodies'}
      globals' =
        Set.foldl'
          (\globals owner ->
             case Map.lookup owner bodies' of
               Nothing -> globals
               Just body ->
                 Map.adjust
                   ( globalDefWithCanonicalCoreBody
                       stateWithBodies
                       body
                   )
                   owner
                   globals)
          (csGlobals st)
          owners
  put
    ( invalidateSemanticCaches
        stateWithBodies {csGlobals = globals'}
    )

-- | §7.1 binding groups admit at most one ordinary constructor declaration
-- with a given spelling in one lexical scope. The per-data check in
-- 'finishDataHeaderIn' catches repetition inside a declaration; this check
-- covers collisions between distinct data declarations before either header
-- can overwrite the other's semantic entry.
validateModuleConstructorBindings :: [Decl] -> CheckM ()
validateModuleConstructorBindings declarations =
  forM_ (Map.toList constructorsBySpelling) $ \(constructor, declarations') ->
    case declarations' of
      (_ : (_, duplicateSite) : _)
        | Set.size (Set.fromList (map fst declarations')) > 1 ->
            errAt duplicateSite
              "E_DUPLICATE_DECLARATION"
              (Just "kappa-hs.name.duplicate")
              ("duplicate constructor declaration '" <> constructor <> "' in the same lexical scope (§7.1)")
      _ -> pure ()
  where
    constructorsBySpelling =
      foldl'
        (\table (constructor, owner, site) ->
           Map.insertWith (flip (++)) constructor [(owner, site)] table)
        Map.empty
        [ (nameText constructor, nameText owner, site)
        | DData _ (DataDecl owner _ _ constructors) site <- declarations
        , CtorDecl constructor _ _ _ _ <- constructors
        ]

-- | Drop declaration-local universe inference history only after the complete
-- module boundary has consumed it. 'finalizeLevelArtifacts' has already
-- materialized the solved substitution in every exported Core/interface
-- artifact, but evidence selection, discarded-result checking, and
-- termination still need that substitution before 'checkModule' returns.
--
-- A failed or incomplete universe closeout retains its full diagnostic state:
-- clearing assignments in the presence of a residual constraint, pending
-- generated proof, or provisional occurrence would turn a later failure into
-- an accidental fresh inference problem. Stable declaration telescopes,
-- finalized owner projections, nominal summaries, selected evidence, and
-- inference records are semantic interface state and deliberately survive.
compactCompletedModuleUniverseState :: CheckState -> CheckState
compactCompletedModuleUniverseState st
  | not (null (csLevelConstraints st)) = st
  | not (Map.null (csLevelConstraintIndex st)) = st
  | not (Map.null (csPendingLevelEvidence st)) = st
  | not (Map.null (csPendingUniverseProofs st)) = st
  | not (Map.null (csProvisionalUniverseInstantiations st)) = st
  | isJust (csActiveUniverseDefinition st) = st
  | otherwise =
      invalidateSemanticCaches
        st
          { csFirstClassLevelMetas = Set.empty
          , csLevelAssignments = Map.empty
          , csLevelAssignmentDependents = Map.empty
          , csLevelAssignmentBudget = emptyLevelAssignmentGraphBudget
          , csLevelGeneralizableMetas = Set.empty
          , csLevelGeneralizableOwners = Map.empty
          , csLevelGeneralizableMetasByOwner = Map.empty
          , csLevelInstantiationMetas = Set.empty
          , csLevelInstantiationOwners = Map.empty
          , csLevelInstantiationMetasByOwner = Map.empty
          , csProvisionalUniverseInstantiations = Map.empty
          , csProvisionalUniverseInstantiationsByOwner = Map.empty
          , csProvisionalUniverseInstantiationsByConsumer = Map.empty
          , csProvisionalGlobalUniverseMetas = Map.empty
          , csProvisionalConstructorUniverseMetas = Map.empty
          , csRecursiveSchemaOccurrences = []
          , csRecursiveSchemaOccurrencesByCaller = Map.empty
          , csBareTypeLevels = Map.empty
          }

-- | Names of signature-governed term definitions in this module.  The SCC
-- termination pass is concerned with definitions, not standalone signatures,
-- so an unsatisfied signature is still reported by 'sigSatisfactionPass'.
signedLetNames :: Set Text -> [Decl] -> [Text]
signedLetNames sigNames = concatMap go
  where
    go = \case
      DLet _ (LetDef (Just n) _ Nothing _ _ _ _ _ _) _
        | nameText n `Set.member` sigNames -> [nameText n]
      DPattern _ (LetDef (Just n) _ Nothing _ _ _ _ _ _) _
        | nameText n `Set.member` sigNames -> [nameText n]
      DUnsafeAssert _ inner _ -> go inner
      _ -> []

-- | Resolved identities completed by one body-pass declaration.  The caller
-- intersects this with the signed-definition set: only those declarations
-- already have a complete provisional interface that can soundly be closed
-- before the module body boundary.  Inferred lets and instance dictionaries
-- retain their existing shared completion boundary.
declarationBodyUniverseOwners :: CheckState -> Decl -> Set GName
declarationBodyUniverseOwners state = \case
  DLet _ definition _ -> maybe Set.empty (Set.singleton . own) (ldName definition)
  DPattern _ definition _ -> maybe Set.empty (Set.singleton . own) (ldName definition)
  DProjection _ name _ _ _ _ -> Set.singleton (own name)
  DInstance _ span' ->
    maybe Set.empty (maybe Set.empty (Set.singleton . piDictG))
      (Map.lookup span' (csPreInstances state))
  DUnsafeAssert _ inner _ -> declarationBodyUniverseOwners state inner
  _ -> Set.empty
  where
    own name = GName (csModule state) (nameText name)

-- | Preview the principal declaration-SCC classification for one completed
-- signed interface without mutating checker state.  This is the arity
-- authority for 'materializeOwnedInterfaceUniverseProofs': minimizable
-- occurrence/result metas and equivalent or uniquely determined source metas
-- are first eliminated exactly as the final solver will eliminate them.  Only
-- a relation that remains after that preview is eligible to become an early
-- proof Pi.  Any solver failure returns an invalid preview and leaves the
-- ordinary final diagnostic path authoritative.
previewOwnedInterfaceUniverseAssignments
  :: GName
  -> GlobalDef
  -> CheckState
  -> (Bool, Map LevelMeta Level)
previewOwnedInterfaceUniverseAssignments owner definition st =
  let initialAssignments = csLevelAssignments st
      initialResolve = substituteLevelMetas initialAssignments
      rawType = globalCoreType (ecOf st) definition
      interfaceType = zonkTermWith (\_ _ -> Nothing) initialResolve 0 rawType
      interfaceMetas = Set.fromList (levelMetasOfTerm interfaceType)
      ownedConstraints =
        [ constraint
            { lcLhs = initialResolve (lcLhs constraint)
            , lcRhs = initialResolve (lcRhs constraint)
            }
        | constraint <- Map.findWithDefault [] owner (csLevelConstraintsByOwner st)
        ]
      relevantMetas = constraintMetaClosure interfaceMetas ownedConstraints
      ownedGeneralizableOrigins =
        Set.fromList
          [ meta
          | (meta, owners) <- Map.toList (csLevelGeneralizableOwners st)
          , owner `Set.member` owners
          ]
      generalizable =
        projectGeneralizableLevelMetas
          initialAssignments
          ownedGeneralizableOrigins
      projectedOrigins origins =
        Set.fromList
          [ projected
          | origin <- Set.toList origins
          , projected <-
              levelMetas
                (normalizeLevel (initialResolve (LMeta origin)))
          ]
      instantiationMetas =
        Set.intersection relevantMetas . Set.difference
          (projectedOrigins (csLevelInstantiationMetas st)) $
          generalizable
      roles = declarationUniverseRoles interfaceType
      minimizable =
        Set.unions
          [ durMinimizable roles
          , instantiationMetas
          , Set.difference relevantMetas generalizable
          ]
      targets =
        Set.difference
          (Set.difference minimizable generalizable)
          (csLevelGeneralizableMetas st)
      solveMinimizable
        | Set.null targets = Just (Map.empty, ownedConstraints)
        | otherwise = case solveLevelConstraintsFor targets ownedConstraints of
            Left _ -> Nothing
            Right solution ->
              let solved = lsAssignments solution
                  unresolved = Set.filter (`Map.notMember` solved) targets
                  candidate = Map.union solved (Map.fromSet (const LZero) unresolved)
                  residual =
                    map (substituteLevelConstraintMetas candidate) (lsResidual solution)
                  residualTargets =
                    Set.intersection targets . Set.fromList $
                      concat
                        [ levelMetas (lcLhs constraint)
                            ++ levelMetas (lcRhs constraint)
                        | constraint <- residual
                        ]
               in if Set.null residualTargets
                    then Just (candidate, residual)
                    else Nothing
   in case solveMinimizable of
        Nothing -> (False, initialAssignments)
        Just (minimizableAssignments, residual0) ->
          let afterMinimizable = Map.union minimizableAssignments initialAssignments
              zonkMinimizable = substituteLevelConstraintMetas afterMinimizable
              residual1 = map zonkMinimizable residual0
              generalized1 =
                projectGeneralizableLevelMetas
                  afterMinimizable
                  ownedGeneralizableOrigins
              equivalent =
                equivalentLevelMetaAssignments
                  (projectGeneralizableLevelMetas afterMinimizable (csLevelGeneralizableMetas st))
                  generalized1
                  minimizable
                  residual1
              afterEquivalent = Map.unions [equivalent, afterMinimizable]
              zonkEquivalent = substituteLevelConstraintMetas afterEquivalent
              residual2 = map zonkEquivalent residual1
              generalized2 =
                projectGeneralizableLevelMetas
                  afterEquivalent
                  ownedGeneralizableOrigins
              determined =
                uniquelyDeterminedLevelMetaAssignments
                  (projectGeneralizableLevelMetas afterEquivalent (csLevelGeneralizableMetas st))
                  generalized2
                  residual2
           in (True, Map.unions [determined, equivalent, afterMinimizable])

-- | Source-owned declaration identities. Compiler seeding may install a
-- placeholder global or constructor before its prelude source declaration is
-- checked, so map membership cannot distinguish a current declaration from an
-- untouched import. The surface declaration tree is the authoritative
-- ownership boundary; declarations introduced by top-level splices remain
-- covered by the ordinary "not preexisting" case above.
sourceDeclarationSymbols :: ModuleName -> [Decl] -> (Set GName, Set GName)
sourceDeclarationSymbols owner decls =
  ( Set.fromList [GName owner name | name <- concatMap globalNames decls]
  , Set.fromList [GName owner name | name <- concatMap ctorNames decls]
  )
  where
    namedLet def = maybe [] (pure . nameText) (ldName def)
    globalNames = \case
      DSig _ name _ _ -> [nameText name]
      DLet _ def _ -> namedLet def
      DData _ dd _ -> [nameText (ddName dd)]
      DTypeAlias _ name _ _ _ _ -> [nameText name]
      DTrait _ td _ ->
        let traitName = nameText (trName td)
            members = concatMap traitMemberName (trMembers td)
         in traitName
              : members
              ++ [traitName <> "." <> member | member <- members]
      DEffect _ eff _ -> nameText (effName eff) : map (nameText . eoName) (effOps eff)
      DExpect _ form _ -> [expectName form]
      DPattern _ def _ -> namedLet def
      DProjection _ name _ _ _ _ -> [nameText name]
      DUnsafeAssert _ inner _ -> globalNames inner
      _ -> []
    ctorNames = \case
      DData _ dd _ -> map (nameText . cdName) (ddCtors dd)
      DUnsafeAssert _ inner _ -> ctorNames inner
      _ -> []
    traitMemberName = \case
      TraitSig name _ _ -> [nameText name]
      TraitDefault def _ -> namedLet def
      TraitDerived name _ _ -> [nameText name]
      TraitEvidenceUniqueness {} -> []
    expectName = \case
      ExpectTerm name _ -> nameText name
      ExpectType name _ _ -> nameText name
      ExpectData name _ _ -> nameText name
      ExpectTrait name _ _ -> nameText name

-- §8.5.2: seal this module's 'opaque' term/type-alias definitions. Their
-- defining equations were available for definitional equality while this
-- module was checked (transparent within the defining module); now clear
-- 'gdReducible' so no downstream module can δ-unfold them during
-- conversion. Runtime evaluation is unaffected — 'ecRuntime' unfolds every
-- valued global regardless of 'gdReducible'.
opaqueSealPass :: CheckM ()
opaqueSealPass = modify' $ \st ->
  let mn = csModule st
      ours = [g | g@(GName m _) <- Map.keys (csOpaqueDefs st), m == mn]
   in st {csGlobals = foldr (Map.adjust (\gd -> gd {gdReducible = False})) (csGlobals st) ours}

-- §9.1: a non-expect top-level term signature must be satisfied by
-- exactly one matching definition in the same source file.
sigSatisfactionPass :: CheckM ()
sigSatisfactionPass = do
  st <- get
  unless (csModule st == preludeModule) $
    forM_ (Map.toList (csSigPending st)) $ \(g, sp) ->
      errAt sp "E_SIGNATURE_UNSATISFIED" (Just "kappa-hs.signature.unsatisfied")
        ("top-level signature '" <> gnameText g
           <> "' has no definition in this source file (Spec §9.1); use 'expect term' for external requirements (§9.4)")

predeclarePassRaw :: Decl -> CheckM ()
predeclarePassRaw = \case
  DLet mods (LetDef (Just n) _ Nothing _ _ [] _ Nothing rhs) _
    | not (dmOpaque mods) -> do
        g <- ownName n
        modify' $ \st ->
          st {csTransparentValueAliases = Map.insert g rhs (csTransparentValueAliases st)}
  DData _ declaration@(DataDecl n params _ _) sp -> do
    g <- ownName n
    resultLevel <- freshLevelMeta
    predeclareNominalHeader g params resultLevel
    modify' $ \st ->
      st
        { csTopLevelDataHeaders =
            Map.insertWith
              (\_ existing -> existing)
              g
              (PendingTopLevelDataHeader declaration sp)
              (csTopLevelDataHeaders st)
        }
  DTrait _ trait _ -> do
    g <- ownName (trName trait)
    predeclareNominalHeader g (trParams trait) LZero
  _ -> pure ()

-- | Publish a provisional nominal head before any header body is elaborated.
-- Module declaration groups have no semantic source order (§9.5), so data and
-- trait headers must both be able to refer to later nominal heads. The real
-- header pass replaces every meta domain with the checked source telescope.
predeclareNominalHeader :: GName -> [Binder] -> Level -> CheckM ()
predeclareNominalHeader global parameters resultLevel = do
  exists <- gets (Map.member global . csGlobals)
  unless exists $ do
    telescope <- forM parameters $ \binder -> do
      domain <- freshMeta
      let mode = fromMaybe Parametric (bpObservation (bPrefix binder))
          quantity =
            maybe
              (if mode == Parametric then Q0 else headerBinderQ binder)
              (qOf . Just)
              (bpQuantity (bPrefix binder))
      pure
        TelescopeEntry
          { teIcit = if bImplicit binder then Impl else Expl
          , teMode = mode
          , teFormation =
              if mode == Parametric then FormationParametric else FormationOrdinary
          , teQ = quantity
          , teBorrow = isJust (bpBorrow (bPrefix binder))
          , teName = maybe "_" nameText (bName binder)
          , teDomain = domain
          , teLevelAssumption = Nothing
          }
    ty <- evalIn emptyCtx (foldr telePi (CSort resultLevel) telescope)
    addGlobal global
      (globalDefWithObservationMode Ordinary (GlobalDef ty Nothing False))

signatureDeclarationName :: Decl -> Maybe Name
signatureDeclarationName = \case
  DSig _ name _ _ -> Just name
  DUnsafeAssert _ inner _ -> signatureDeclarationName inner
  _ -> Nothing

deferSignatureHoles :: Name -> CheckM ()
deferSignatureHoles name = do
  owner <- ownName name
  holes <- gets csHoles
  modify' $ \st ->
    st
      { csSignatureHoles =
          Map.insert owner holes (csSignatureHoles st)
      }

-- | Every identifier spelled anywhere inside a piece of surface syntax
-- (generic over-approximation; binder shadowing is ignored). Used for
-- the recursive-type-alias check.
allNamesIn :: Expr -> [Text]
allNamesIn = go
  where
    go :: Data a => a -> [Text]
    go x = case cast x :: Maybe Name of
      Just n -> [nameText n]
      Nothing -> concat (gmapQ go x)

-- | Replace the nominal head of a constructor result while preserving its
-- checked family arguments and any explicit classifier lift. Constructor
-- declarations share the enclosing data schema, so this is the one place
-- where the result occurrence must use the constructor's complete schema
-- identity rather than a separately minimized occurrence spine.
rewriteConstructorResultHead :: GName -> [Level] -> Term -> Term
rewriteConstructorResultHead owner universes = go
  where
    go (CUniverseLift lower upper evidence term) =
      CUniverseLift lower upper evidence (go term)
    go term =
      let (headTerm, arguments) = spineOfTerm term
       in case headTerm of
            CGlobal target _ | target == owner ->
              foldl'
                (\function (icit, argument) -> CApp icit function argument)
                (CGlobI owner universes)
                arguments
            _ -> term

-- | Apply 'rewriteConstructorResultHead' to the terminal result of a complete
-- constructor telescope. Domains are left untouched: nested family uses in
-- fields are ordinary independently selected schema instances.
rewriteConstructorTypeResultHead :: GName -> [Level] -> Term -> Term
rewriteConstructorTypeResultHead owner universes = \case
  CPiRuntimeM mode formation icit quantity borrowed name assumption origin runtimeErasure domain codomain ->
    CPiRuntimeM
      mode
      formation
      icit
      quantity
      borrowed
      name
      assumption
      origin
      runtimeErasure
      domain
      (rewriteConstructorTypeResultHead owner universes codomain)
  result -> rewriteConstructorResultHead owner universes result

-- | Extract the opaque one-hole applications whose variance needs ordinary
-- evidence. Constructor algebra (succ/add/max) is handled structurally; an
-- arbitrary neutral application is never assumed monotone from its spelling.
monotoneCandidatesOfTerm :: Term -> [(Int, NeutralLevelTerm)]
monotoneCandidatesOfTerm = concatMap monotoneCandidatesOfLevel . levelsOfTerm
  where
    levelsOfTerm = \case
      CSort level -> [level]
      CLevel level -> [level]
      term ->
        concatMap levelsOfTerm (childrenOfTerm term)

    childrenOfTerm = \case
      CPiEvidenceM _ _ _ _ _ _ _ _ domain codomain -> [domain, codomain]
      CApp _ function argument -> [function, argument]
      CUniverseLift _ _ _ inner -> [inner]
      CSchemaLift _ _ _ _ _ _ sourceArguments targetArguments inner ->
        sourceArguments ++ targetArguments ++ [inner]
      CRecordTQ fields -> map rfType fields
      CRecordV fields -> map snd fields
      CProjM _ receiver _ -> [receiver]
      CProjAtM _ receiver _ _ -> [receiver]
      CVariantT members -> members
      CInject _ value -> [value]
      CSealE _ value -> [value]
      CSigT _ value -> [value]
      CThunkE value suspensionType -> value : maybeToList suspensionType
      CLazyE value suspensionType -> value : maybeToList suspensionType
      CForceE value resultType -> value : maybeToList resultType
      CIf condition yes no -> [condition, yes, no]
      _ -> []

monotoneCandidatesOfLevel :: Level -> [(Int, NeutralLevelTerm)]
monotoneCandidatesOfLevel = \case
  LSucc level -> monotoneCandidatesOfLevel level
  LAdd left right -> monotoneCandidatesOfLevel left ++ monotoneCandidatesOfLevel right
  LMax left right -> monotoneCandidatesOfLevel left ++ monotoneCandidatesOfLevel right
  LNeutral (NeutralLevelTermAtom _ term) -> case term of
    NLTApply True operator (NLTLevel (LParam parameter))
      | parameter `notElem` concatMap levelParams (neutralLevelTermLevels operator) ->
          [(parameter, operator)]
    _ -> []
  _ -> []

neutralLevelTermToCore :: Int -> NeutralLevelTerm -> Maybe Term
neutralLevelTermToCore depth = \case
  NLTLocal level
    | level >= 0 && level < depth -> Just (CVar (depth - level - 1))
    | otherwise -> Nothing
  NLTLocalDeclaration level universes
    | level >= 0 && level < depth -> Just (CLocal (depth - level - 1) universes)
    | otherwise -> Nothing
  NLTGlobal owner name universes -> Just (CGlobI (GName (ModuleName owner) name) universes)
  NLTConstruct owner name universes arguments ->
    CCtorI (GName (ModuleName owner) name) universes Nothing
      <$> mapM (\(explicit, argument) -> ConstructorArg (if explicit then Expl else Impl) True Nothing <$> neutralLevelTermToCore depth argument) arguments
  NLTApply explicit function argument ->
    CApp (if explicit then Expl else Impl)
      <$> neutralLevelTermToCore depth function
      <*> neutralLevelTermToCore depth argument
  NLTProject field receiver -> CProjM Ordinary <$> neutralLevelTermToCore depth receiver <*> pure field
  NLTLevel level -> Just (CLevel level)
  NLTLiteral literal -> CLit <$> case literal of
    NLLInt value -> Just (LitInt value)
    NLLDouble value -> Just (LitDouble value)
    NLLString value -> Just (LitStr value)
    NLLScalar value -> Just (LitScalar value)
    NLLByte value -> Just (LitByte value)
    -- Byte arrays are represented by a packed host ByteString in Core; this
    -- role-evidence path has no need to reconstruct literal byte payloads.
    NLLBytes _ -> Nothing
    NLLGrapheme value -> Just (LitGrapheme value)
  NLTRecord fields -> CRecordV <$> mapM (\(field, value) -> (field,) <$> neutralLevelTermToCore depth value) fields
  NLTIf condition yes no -> CIf
    <$> neutralLevelTermToCore depth condition
    <*> neutralLevelTermToCore depth yes
    <*> neutralLevelTermToCore depth no
  NLTUnsupported _ -> Nothing

recordSelectedMonotoneEvidence :: Ctx -> Term -> Text -> Term -> CheckM ()
recordSelectedMonotoneEvidence ctx _operator renderedGoal dictionary = do
  evidenceIdentity <- selectedMonotoneMemberIdentity ctx dictionary
  forM_ evidenceIdentity $ \identity ->
    modify' $ \state ->
      state
        { csSelectedUniverseEvidence =
            Set.insert
              (SelectedUniverseEvidence renderedGoal identity)
              (csSelectedUniverseEvidence state)
        }

renderSelectedLevel :: Int -> Level -> Text
renderSelectedLevel binderLevel = go . normalizeLevel
  where
    go = \case
      LZero -> "typeLevelZero"
      LFinite 1 -> "typeLevelOne"
      LFinite n -> "typeLevelFinite " <> T.pack (show n)
      LOmega -> "typeLevelOmega"
      LSucc level -> "succ " <> atom level
      LAdd left right -> atom left <> " + " <> atom right
      LMax left right -> "max " <> atom left <> " " <> atom right
      LVar level | level == binderLevel -> "x"
      LVar level -> "u" <> T.pack (show level)
      LField _ field -> "this." <> field
      LProjection root path ->
        "u" <> T.pack (show root) <> "." <> T.intercalate "." path
      LNeutral (NeutralLevelTermAtom _ term) ->
        maybe "<opaque-level>" renderTerm (neutralLevelTermToCore (binderLevel + 1) term)
      LNeutral (NeutralLevelSymbol identity arguments) ->
        identity
          <> if null arguments
               then ""
               else "[" <> T.intercalate ", " (map go arguments) <> "]"
      LMeta meta -> "?u" <> T.pack (show meta)
      LParam parameter -> "^u#" <> T.pack (show parameter)
    atom level@LAdd {} = "(" <> go level <> ")"
    atom level@LMax {} = "(" <> go level <> ")"
    atom level = go level

selectedMonotoneMemberIdentity :: Ctx -> Term -> CheckM (Maybe GName)
selectedMonotoneMemberIdentity ctx dictionary = do
  mode <- gets $ \state ->
    fromMaybe Parametric $ do
      trait <- Map.lookup prelMonotone (csTraits state)
      Map.lookup "monotone" (tiMemberModes trait)
  member <- forceM =<< evalIn ctx (CProjM mode dictionary "monotone")
  let projected = do
        term <- neutralValueTerm (ctxLen ctx) member
        globalHead term
  case projected of
    Just identity -> pure (Just identity)
    Nothing -> do
      -- Generated instance dictionaries may be deliberately non-reducible at
      -- this phase.  Their checked Core body is still the authoritative
      -- selected artifact, so inspect the exact selected dictionary global
      -- rather than scanning declarations for a theorem-shaped type.
      state <- get
      pure $ do
        dictionaryIdentity <- globalHead dictionary
        body <- Map.lookup dictionaryIdentity (csCoreBodies state)
          <|> (Map.lookup dictionaryIdentity (csGlobals state) >>= gdCoreBody)
        memberTerm <- case peelDictionaryTelescope body of
          CRecordV fields -> lookup "monotone" fields
          _ -> Nothing
        globalHead memberTerm
  where
    peelDictionaryTelescope = \case
      CLamM _ _ _ _ body -> peelDictionaryTelescope body
      body -> body
    globalHead term = case fst (spineOfTerm term) of
      CGlobal identity _ -> Just identity
      _ -> Nothing

-- | The saturation authority is the finalized physical family telescope.
-- Source parameter counts deliberately exclude compiler-generated proof
-- binders, while §11.1.2.3A.2 includes every implicit/erased binder in full
-- saturation. Falling back to the source count is only for the diagnostic
-- recovery path where the family global is unavailable.
nominalPhysicalSaturationArity :: GName -> Int -> CheckM Int
nominalPhysicalSaturationArity family fallback = do
  state <- get
  pure $
    maybe fallback (piArity . globalCoreType (ecOf state))
      (Map.lookup family (csGlobals state))
  where
    piArity (CPiM _ _ _ _ _ _ codomain) = 1 + piArity codomain
    piArity _ = 0

dataNominalRequirements
  :: FrozenMonotoneEvidence
  -> GName
  -> Map GName [UniverseVariance]
  -> Int
  -> [GName]
  -> CheckM [RoleRequirement]
dataNominalRequirements frozenMonotone family tentativeRoles dataParameterCount constructors = do
  constructorTable <- gets csCtors
  fmap (nub . sort . concat) $
    forM constructors $ \constructor ->
      case Map.lookup constructor constructorTable of
        Nothing -> pure []
        Just info ->
          nominalRequirementsFromConstructor
            frozenMonotone family tentativeRoles dataParameterCount (ciType info)

-- | Materialize the current ordinary-data signature closure once. Role
-- inference, certificate replay, semantic hashing, and interface export all
-- consume this same typed record; none rebuild a source-shaped clause list.
dataNominalSignatureClosure
  :: FrozenMonotoneEvidence
  -> Map GName [UniverseVariance]
  -> GName
  -> Int
  -> [GName]
  -> Span
  -> CheckM NominalSignatureClosure
dataNominalSignatureClosure frozenMonotone tentativeRoles family dataParameterCount constructors site = do
  definitions <- gets csGlobals
  constructorTable <- gets csCtors
  ec <- ec_
  case Map.lookup family definitions of
    Nothing -> do
      errAt site "E_KCORE_SCHEMA_CERTIFICATE_INVALID"
        (Just "kappa.kcore.schema-certificate-invalid")
        "nominal signature closure has no finalized family interface"
      pure $
        makeNominalSignatureClosure 0 [] dataParameterCount
          [ NominalClosureClause ClauseExtension ("invalid-family:" <> gKey family) [] "missing"
              [] NominalTransformRepresentation
          ]
    Just definition -> do
      let familyUniverseArity = dutParameterCount (gdUniverses definition)
      pointClauses <- fmap concat . forM constructors $ \constructor ->
        case Map.lookup constructor constructorTable of
          Nothing -> do
            errAt site "E_KCORE_SCHEMA_CERTIFICATE_INVALID"
              (Just "kappa.kcore.schema-certificate-invalid")
              ("nominal signature closure is missing constructor " <> gKey constructor)
            pure []
          Just info -> do
            requirements <-
              nominalRequirementsFromConstructor
                frozenMonotone family tentativeRoles dataParameterCount (ciType info)
            pure
              [ nominalClosureClause familyUniverseArity ClausePointConstructor
                  ("constructor:" <> gKey constructor) requirements (ciType info)
              ]
      let familyType = globalCoreType ec definition
          sortClause =
            nominalClosureClause familyUniverseArity ClauseSortDeclaration
              ("family:" <> gKey family) [] familyType
          generated kind label point =
            point
              { nccKind = kind
              , nccIdentity = label <> ":" <> nccIdentity point
              }
          clauses =
            sortClause : pointClauses
              ++ concat
                   [ [ generated ClauseEliminator "eliminator" point
                     , generated ClauseComputationRule "computation" point
                     ]
                   | point <- pointClauses
                   ]
      physicalSaturationArity <- nominalPhysicalSaturationArity family dataParameterCount
      pure $
        withNominalMonotoneWitnesses
          [ witness
          | ((owner, _, _), witness) <- Map.toAscList frozenMonotone
          , owner == family
          ]
          ( makeNominalSignatureClosure
              familyUniverseArity
              (declarationConstraintSummary (dutParameterCount (gdUniverses definition)) familyType)
              physicalSaturationArity
              clauses
          )

traitNominalSignatureClosure
  :: Map GName [UniverseVariance]
  -> GName
  -> Int
  -> [Term]
  -> Span
  -> CheckM NominalSignatureClosure
traitNominalSignatureClosure tentativeRoles family saturationArity clauses site = do
  definitions <- gets csGlobals
  ec <- ec_
  case Map.lookup family definitions of
    Nothing -> do
      errAt site "E_KCORE_SCHEMA_CERTIFICATE_INVALID"
        (Just "kappa.kcore.schema-certificate-invalid")
        "trait nominal signature closure has no finalized family interface"
      pure $
        makeNominalSignatureClosure 0 [] saturationArity
          [ NominalClosureClause ClauseExtension ("invalid-trait:" <> gKey family) [] "missing"
              [] NominalTransformRepresentation
          ]
    Just definition -> do
      let familyUniverseArity = dutParameterCount (gdUniverses definition)
      memberClauses <- forM (zip [0 :: Int ..] clauses) $ \(index, term) -> do
        requirements <- traitNominalRequirements tentativeRoles family [term]
        pure
          ( nominalClosureClause familyUniverseArity ClauseGeneratedProjection
              ("projection:" <> gKey family <> ":" <> T.pack (show index)) requirements term
          )
      let familyType = globalCoreType ec definition
          sortClause =
            nominalClosureClause familyUniverseArity ClauseSortDeclaration
              ("family:" <> gKey family) [] familyType
          dictionaryClause =
            NominalClosureClause ClausePointConstructor ("dictionary:" <> gKey family)
              (concatMap nccBinders memberClauses)
              (nominalTypeFingerprint familyType)
              (concatMap nccRoleActions memberClauses)
              NominalPreserveRepresentation
          derivedDictionaryClause kind label =
            dictionaryClause
              { nccKind = kind
              , nccIdentity = label <> ":" <> nccIdentity dictionaryClause
              }
      physicalSaturationArity <- nominalPhysicalSaturationArity family saturationArity
      pure $
        makeNominalSignatureClosure
          familyUniverseArity
          (declarationConstraintSummary (dutParameterCount (gdUniverses definition)) familyType)
          physicalSaturationArity
          ( sortClause
              : dictionaryClause
              : derivedDictionaryClause ClauseEliminator "eliminator"
              : derivedDictionaryClause ClauseComputationRule "computation"
              : memberClauses
          )

nominalClosureClause
  :: Int
  -> NominalClauseKind
  -> Text
  -> [RoleRequirement]
  -> Term
  -> NominalClosureClause
nominalClosureClause familyUniverseArity kind identity requirements = go []
  where
    go binders (CPiEvidenceM mode formation ic quantity borrowed _ assumption _ domain codomain) =
      go
        ( binders
            ++ [ NominalBinderContract
                   mode
                   formation
                   (case ic of Expl -> NominalExplicit; Impl -> NominalImplicit)
                   (case quantity of
                      Q0 -> NominalZero
                      Q1 -> NominalOne
                      QW -> NominalOmega
                      QLe1 -> NominalAtMostOne
                      QGe1 -> NominalAtLeastOne)
                   borrowed
                   (fmap (\(lower, upper) -> (renderLevel (normalizeLevel lower), renderLevel (normalizeLevel upper))) assumption)
                   (nominalTypeFingerprint domain)
               ]
        )
        codomain
    go binders result =
      NominalClosureClause kind identity binders (nominalTypeFingerprint result)
        (mapMaybe requirementAction requirements)
        NominalPreserveRepresentation

    requirementAction = \case
      RequireCovariant index _
        | familyUniverseParameter index -> Just (NominalCovariantUse index)
      RequireInvariant index _
        | familyUniverseParameter index -> Just (NominalInvariantUse index)
      _ -> Nothing

    -- Constructor schemas begin with the enclosing family's universe
    -- telescope and may append constructor-local universes. Only the prefix
    -- participates in the family's role action; the suffix remains in the
    -- clause fingerprint and is independently scoped at each constructor use.
    -- KCore replay enforces the same boundary by stable universe identity.
    familyUniverseParameter index =
      index >= 0 && index < familyUniverseArity

-- | Certify a compiler-seeded, universe-closed data family through the same
-- normalized nominal closure consumed by source declarations. Seeded logical
-- families such as Nat exist before the ordinary declaration pipeline runs,
-- so they cannot use 'PendingDataNominalSummary'; accepting them without a
-- summary would make independently verified KCore depend on an in-process
-- checker exception. Keep this entry point deliberately narrow: a seeded
-- family with universe parameters or constraints must go through the full
-- declaration fixed point instead of guessing roles here.
certifyClosedBuiltinData :: GName -> CheckState -> Either Text CheckState
certifyClosedBuiltinData family state = do
  definition <-
    maybe
      (Left ("seeded nominal family is missing its global interface: " <> gKey family))
      Right
      (Map.lookup family (csGlobals state))
  dataInfo <-
    maybe
      (Left ("seeded nominal family is missing its data interface: " <> gKey family))
      Right
      (Map.lookup family (csDatas state))
  unless (dutParameterCount (gdUniverses definition) == 0) $
    Left ("seeded closed nominal family unexpectedly has declaration universes: " <> gKey family)
  constructorInfos <-
    forM (diCtors dataInfo) $ \constructor ->
      maybe
        (Left ("seeded nominal family is missing constructor " <> gKey constructor))
        Right
        (Map.lookup constructor (csCtors state))
  unless (all ((== family) . ciData) constructorInfos) $
    Left ("seeded nominal family includes a constructor owned by another family: " <> gKey family)
  let ec = EvalCtx (Globals (csGlobals state)) (csMetas state) False mempty
      familyType = globalCoreType ec definition
      constructorTypes = map ciType constructorInfos
      constraints = declarationConstraintSummary 0 familyType
  unless
    ( null constraints
        && null (levelParamsOfTerm familyType)
        && all (null . levelParamsOfTerm) constructorTypes
    ) $
      Left ("seeded closed nominal family contains an open universe obligation: " <> gKey family)
  let sortClause =
        nominalClosureClause
          0
          ClauseSortDeclaration
          ("family:" <> gKey family)
          []
          familyType
      pointClauses =
        zipWith
          (\constructor info ->
             nominalClosureClause
               0
               ClausePointConstructor
               ("constructor:" <> gKey constructor)
               []
               (ciType info))
          (diCtors dataInfo)
          constructorInfos
      generated kind label point =
        point
          { nccKind = kind
          , nccIdentity = label <> ":" <> nccIdentity point
          }
      closure =
        makeNominalSignatureClosure
          0
          []
          (diParamCount dataInfo)
          ( sortClause
              : pointClauses
              ++ concat
                   [ [ generated ClauseEliminator "eliminator" point
                     , generated ClauseComputationRule "computation" point
                     ]
                   | point <- pointClauses
                   ]
          )
      summary =
        makeNominalCumulativitySummary
          (gKey family)
          []
          []
          closure
          Nothing
  unless (verifyNominalCumulativitySummary summary) $
    Left ("seeded nominal family certificate failed independent replay: " <> gKey family)
  pure
    state
      { csGlobals =
          Map.adjust
            (globalDefWithNominalSummary summary)
            family
            (csGlobals state)
      }

-- Resolved globals, de Bruijn indices, levels, and field identities are
-- semantic. Binder names are presentation only, so erase them recursively
-- from the type grammar before hashing the closure.
nominalTypeFingerprint :: Term -> Text
nominalTypeFingerprint = stableNominalHash . renderStructuralTermKey . alphaType
  where
    alphaType = \case
      CLamM mode ic quantity _ body -> CLamM mode ic quantity "_" (alphaType body)
      CPiRuntimeM mode formation ic quantity borrowed _ assumption origin runtimeErasure domain codomain ->
        CPiRuntimeM mode formation ic quantity borrowed "_" assumption origin
          (fmap alphaType runtimeErasure)
          (alphaType domain)
          (alphaType codomain)
      CAppM ic runtimeErasure function argument ->
        CAppRuntime ic
          (fmap alphaType runtimeErasure)
          (alphaType function)
          (alphaType argument)
      CUniverseLift from to evidence term -> CUniverseLift from to evidence (alphaType term)
      CSchemaLift owner source target roles evidence certificate sourceArguments targetArguments term ->
        CSchemaLift owner source target roles evidence certificate
          (map alphaType sourceArguments) (map alphaType targetArguments) (alphaType term)
      CRecordTQ fields -> CRecordTQ (map (fmap alphaType) fields)
      CVariantT members -> CVariantT (map alphaType members)
      CSigT labels term -> CSigT labels (alphaType term)
      CSealE labels term -> CSealE labels (alphaType term)
      CProjM mode term field -> CProjM mode (alphaType term) field
      CProjAtM mode term field index -> CProjAtM mode (alphaType term) field index
      CThunkE term suspensionType ->
        CThunkE (alphaType term) (alphaType <$> suspensionType)
      CLazyE term suspensionType ->
        CLazyE (alphaType term) (alphaType <$> suspensionType)
      CForceE term resultType ->
        CForceE (alphaType term) (alphaType <$> resultType)
      term -> term

-- Trait dictionaries are nominal records. Their supplied trait parameters do
-- not constrain declaration-universe roles, but member and supertrait field
-- types do. Analyse those elaborated Core types in the same SCC fixed point as
-- data constructors; an unrecognized type operation is invariant.
traitNominalRequirements
  :: Map GName [UniverseVariance]
  -> GName
  -> [Term]
  -> CheckM [RoleRequirement]
traitNominalRequirements tentativeRoles family terms = do
  (trusted, initialDepth, universeArity) <- nominalRoleEvidenceContext family
  fmap (nub . sort . concat) (mapM (go trusted initialDepth universeArity) terms)
  where
    go trusted depth universeArity = \case
      liftTerm@(CUniverseLift from to proof inner)
        | validateUniverseEvidenceRelationUnder trusted depth universeArity (from, to) proof -> do
            innerRequirements <- go trusted depth universeArity inner
            pure
              ( requirementsForUniverseRole
                  "trait dictionary field uses a classifier-only universe lift"
                  Covariant
                  (concatMap levelParams [from, to])
                  ++ innerRequirements
              )
        | otherwise ->
            pure
              [ RequireInvariant parameter
                  "trait dictionary field has unauthenticated universe-lift evidence"
              | parameter <- levelParamsOfTerm liftTerm
              ]
      CSchemaLift owner source target roles evidence certificate sourceArguments targetArguments inner -> do
        (_, wrapperRequirements) <-
          sourceSchemaLiftRoleRequirements
            trusted depth universeArity
            "trait dictionary field uses a certified nominal schema lift"
            owner source target roles evidence certificate sourceArguments targetArguments
        innerRequirements <- go trusted depth universeArity inner
        pure
          ( wrapperRequirements
              ++ innerRequirements
          )
      CSort level ->
        pure [RequireCovariant parameter "trait dictionary field stores a type code or witness" | parameter <- levelParams level]
      CPiEvidenceM _ _ _ _ _ _ assumption _ domain codomain -> do
        let domainRequirements =
              [ RequireInvariant parameter "trait dictionary function domain uses a declaration universe"
              | parameter <- roleLevelParamsOfTerm domain
              ]
            trusted' = maybe trusted (\(lower, upper) -> insertAssumption lower upper trusted) assumption
        codomainRequirements <- go trusted' (depth + 1) universeArity codomain
        pure (domainRequirements ++ codomainRequirements)
      nominal -> do
        certified <- requirementsFromCertifiedNominal nominal
        pure $ fromMaybe
          [ RequireInvariant parameter "trait dictionary field uses a universe under an unverified operation"
          | parameter <- roleLevelParamsOfTerm nominal
          ]
          certified

    requirementsFromCertifiedNominal term = do
      let (headTerm, arguments) = spineOfTerm term
      case headTerm of
        CGlobal nested levels -> do
          externalSummary <- gets (Map.lookup nested . csGlobals) >>= pure . (>>= gdNominalSummary)
          localAuthority <- case Map.lookup nested tentativeRoles of
            Nothing -> pure Nothing
            Just localRoles -> do
              saturation <- nominalPhysicalSaturationArity nested 0
              pure (Just (localRoles, saturation))
          let externalAuthority = do
                summary <- externalSummary
                guard
                  ( verifyNominalCumulativitySummary summary
                      && ncsFamilyIdentity summary == gKey nested
                  )
                pure (ncsRoles summary, ncsSaturationArity summary)
              certifiedAuthority = localAuthority <|> externalAuthority
          pure $ do
            (roles, saturation) <- certifiedAuthority
            guard (length levels == length roles)
            guard (length arguments == saturation)
            pure
              ( concat
                  [ case role of
                      Invariant -> [RequireInvariant parameter "trait dictionary field uses an invariant certified family" | parameter <- levelParams level]
                      Covariant -> [RequireCovariant parameter "trait dictionary field uses a covariant certified family" | parameter <- levelParams level]
                      Irrelevant -> []
                  | (role, level) <- zip roles levels
                  ]
              )
        _ -> pure Nothing

-- | Trusted universe context for nominal role replay. The finalized typed
-- family interface, not evidence embedded in an occurrence, supplies proof
-- authority and the physical binder depth.
nominalRoleEvidenceContext :: GName -> CheckM (Assumptions, Int, Int)
nominalRoleEvidenceContext family = do
  state <- get
  pure $ case Map.lookup family (csGlobals state) of
    Nothing -> (emptyAssumptions, 0, 0)
    Just definition ->
      let universeArity = dutParameterCount (gdUniverses definition)
          familyType = globalCoreType (ecOf state) definition
          trusted =
            foldl'
              (\assumptions constraint ->
                 insertAssumption (ucLower constraint) (ucUpper constraint) assumptions)
              emptyAssumptions
              (declarationUniverseConstraints universeArity familyType)
       in (trusted, piArity familyType, universeArity)
  where
    piArity (CPiEvidenceM _ _ _ _ _ _ _ _ _ codomain) = 1 + piArity codomain
    piArity _ = 0

installDataNominalSummary
  :: GName -> Maybe UniverseSchema -> NominalSignatureClosure -> Span -> CheckM ()
installDataNominalSummary family sourceSchema closure site = do
  globals <- gets csGlobals
  case Map.lookup family globals of
    Nothing -> pure ()
    Just definition -> do
      let parameterCount = dutParameterCount (gdUniverses definition)
      let requirements = nominalClosureRequirements closure
      let inferred = inferUniverseRoles parameterCount requirements
          written = maybe [] usRoles sourceSchema ++ repeat Nothing
          -- A rejected annotation is a diagnostic, never input to the
          -- certificate.  Retain the independently inferred role so one bad
          -- source annotation cannot manufacture a second, misleading
          -- certificate-replay failure.
          effective =
            zipWith
              (\annotation inferredRole ->
                case annotation of
                  Just writtenRole | rolePermitsAnnotation writtenRole inferredRole -> writtenRole
                  _ -> inferredRole
              )
              written
              inferred
          explicitFlags = map isJust (take parameterCount written)
      forM_ (zip4 [0 :: Int ..] (take parameterCount written) inferred effective) $
        \(index, annotation, inferredRole, effectiveRole) ->
          case annotation of
            Just writtenRole | not (rolePermitsAnnotation writtenRole inferredRole) ->
              report $
                withPayload
                  ( withPayloadField "nominalDeclaration" (gKey family) $
                      withPayloadField "nominalDeclarationIdentity" (gKey family) $
                      withPayloadField "signatureBlock" (gKey family) $
                        withPayloadField "parameterIndex" (T.pack (show index)) $
                          withPayloadField "universeParameterIndex" (T.pack (show index)) $
                          withPayloadField "sourceName" (schemaParameterName index) $
                            withPayloadField "explicitRole" (varianceText writtenRole) $
                              withPayloadField "inferredRole" (varianceText inferredRole) $
                                withPayloadField "effectiveRole" (varianceText effectiveRole) $
                                  withPayloadField "roleCheckerVersion" "1" $
                                    withPayloadField "forcingObligation" (forcingRequirement index requirements) $
                                      withPayloadField "declarationKind" "ordinary-data" $
                                        withPayloadField "nearestAcceptedRole" (varianceText inferredRole) $
                                          payloadKind "universe-variance"
                  ) $
                    diag SevError StageElaborate "E_UNIVERSE_VARIANCE_TOO_PERMISSIVE"
                      (Just "kappa.universe.variance") site
                      ( "universe role " <> varianceText writtenRole <> " for parameter "
                          <> schemaParameterName index <> " is more permissive than inferred role "
                          <> varianceText inferredRole <> " (§11.1.2.3A.2)"
                      )
            _ -> pure ()
      let summary =
            makeNominalCumulativitySummary (gKey family) effective explicitFlags closure Nothing
      if verifyNominalCumulativitySummary summary
        then modify' $ \st -> st {csGlobals = Map.adjust (globalDefWithNominalSummary summary) family (csGlobals st)}
        else
          errAt site "E_KCORE_SCHEMA_CERTIFICATE_INVALID"
            (Just "kappa.kcore.schema-certificate-invalid")
            ( "the generated nominal action certificate for " <> gKey family
                <> " failed independent replay (universe arity "
                <> T.pack (show (nscUniverseArity closure))
                <> "; clause actions "
                <> T.pack
                     ( show
                         [ (nccIdentity clause, nccRoleActions clause)
                         | clause <- nscClauses closure
                         , not (null (nccRoleActions clause))
                         ]
                     )
                <> ")"
            )
  where
    schemaParameterName index =
      fromMaybe ("^u#" <> T.pack (show index)) $ do
        schema <- sourceSchema
        parameter <- usParameters schema List.!? index
        pure (nameText parameter)

    forcingRequirement index requirements =
      fromMaybe "no clause requires a tighter role" $
        listToMaybe
          [ reason
          | requirement <- requirements
          , let (parameter, reason) = case requirement of
                  RequireCovariant i why -> (i, why)
                  RequireInvariant i why -> (i, why)
          , parameter == index
          ]

    varianceText = \case
      Invariant -> "invariant"
      Covariant -> "covariant"
      Irrelevant -> "irrelevant"

-- | Requirements contributed by constructor-local fields. Leading family
-- parameters are fixed aligned arguments, so their classifiers do not impose
-- schema variance. A direct type-code/witness field is covariant; occurrence
-- below a function or an unverified nominal operation is invariant.
nominalRequirementsFromConstructor
  :: FrozenMonotoneEvidence
  -> GName
  -> Map GName [UniverseVariance]
  -> Int
  -> Term
  -> CheckM [RoleRequirement]
nominalRequirementsFromConstructor frozenMonotone family tentativeRoles dataParameterCount term = do
  (trusted, initialDepth, schemaArity) <- nominalRoleEvidenceContext family
  goFields trusted initialDepth schemaArity
    (dropPis dataParameterCount (dropDeclarationConstraints schemaArity term))
  where
    dropDeclarationConstraints arity candidate =
      case declarationUniverseConstraintBinder arity candidate of
        Just _ -> case candidate of
          CPiEvidenceM _ _ _ _ _ _ _ _ _ codomain ->
            dropDeclarationConstraints arity codomain
          _ -> candidate
        Nothing -> candidate

    dropPis 0 term = term
    dropPis count (CPiEvidenceM _ _ _ _ _ _ _ _ _ codomain) = dropPis (count - 1) codomain
    dropPis _ term = term

    goFields trusted depth schemaArity (CPiEvidenceM _ _ _ _ _ name assumption _ domain codomain) = do
      domainRequirements <- case assumption of
        -- Declaration constraints have already been removed by exact
        -- declaration-telescope identity above. A remaining checked
        -- assumption belongs to this constructor telescope. Reconstructing
        -- @lower <= upper@ at a larger schema instance is covariant in a
        -- monotone upper endpoint and invariant in a lower endpoint: raising
        -- the lower bound can invalidate the source proof.
        Just (lower, upper) ->
          pure
            ( [ RequireInvariant parameter
                  ("constructor proof field " <> name <> " uses a declaration universe in its lower bound")
              | parameter <- levelParams lower
              ]
                ++ requirementsForLevel name upper
            )
        Nothing -> requirementsForDomain trusted depth schemaArity name domain
      let trusted' =
            maybe trusted (\(lower, upper) -> insertAssumption lower upper trusted) assumption
      rest <- goFields trusted' (depth + 1) schemaArity codomain
      pure (domainRequirements ++ rest)
    goFields _ _ _ _ = pure []

    requirementsForDomain trusted depth schemaArity field term =
      case term of
        liftTerm@(CUniverseLift from to proof inner)
          | validateUniverseEvidenceRelationUnder trusted depth schemaArity (from, to) proof -> do
              innerRequirements <- requirementsForDomain trusted depth schemaArity field inner
              pure
                ( requirementsForUniverseRole
                    ("constructor field " <> field <> " uses a classifier-only universe lift")
                    Covariant
                    (concatMap levelParams [from, to])
                    ++ innerRequirements
                )
          | otherwise ->
              pure
                [ RequireInvariant parameter
                    ("constructor field " <> field <> " has unauthenticated universe-lift evidence")
                | parameter <- levelParamsOfTerm liftTerm
                ]
        CSchemaLift owner source target roles evidence certificate sourceArguments targetArguments inner -> do
          let reason = "constructor field " <> field <> " uses a certified nominal schema lift"
          (_, wrapperRequirements) <-
            sourceSchemaLiftRoleRequirements
              trusted depth schemaArity
              reason owner source target roles evidence certificate sourceArguments targetArguments
          innerRequirements <- requirementsForDomain trusted depth schemaArity field inner
          pure (wrapperRequirements ++ innerRequirements)
        CSort level ->
          pure (requirementsForLevel field level)
        nominal -> do
          certified <- requirementsFromCertifiedNominal field nominal
          pure $ fromMaybe
            [RequireInvariant parameter ("constructor field " <> field <> " uses the universe under a runtime type operation") | parameter <- roleLevelParamsOfTerm nominal]
            certified

    requirementsForLevel field = go
      where
        covariant parameter =
          RequireCovariant parameter ("constructor field " <> field <> " stores a type code/witness")
        invariant parameter =
          RequireInvariant parameter ("constructor field " <> field <> " uses an opaque TypeLevel operation without selected Monotone evidence")
        go = \case
          LZero -> []
          LFinite _ -> []
          LOmega -> []
          LSucc level -> go level
          LAdd left right -> go left ++ go right
          LMax left right -> go left ++ go right
          LVar _ -> []
          LParam parameter -> [covariant parameter]
          LField _ _ -> []
          LProjection _ _ -> []
          LMeta _ -> []
          neutral@(LNeutral _) ->
            let candidates = monotoneCandidatesOfLevel neutral
                selected parameter operator = Map.member (family, parameter, operator) frozenMonotone
                candidateFor parameter = [operator | (candidate, operator) <- candidates, candidate == parameter]
             in [ if any (selected parameter) (candidateFor parameter)
                    then covariant parameter
                    else invariant parameter
                | parameter <- levelParams neutral
                ]

    requirementsFromCertifiedNominal field term = do
      let (headTerm, arguments) = spineOfTerm term
      case headTerm of
        CGlobal nested levels -> do
          externalSummary <- gets (Map.lookup nested . csGlobals) >>= pure . (>>= gdNominalSummary)
          localAuthority <- case Map.lookup nested tentativeRoles of
            Nothing -> pure Nothing
            Just localRoles -> do
              saturation <- nominalPhysicalSaturationArity nested 0
              pure (Just (localRoles, saturation))
          let externalAuthority = do
                summary <- externalSummary
                guard
                  ( verifyNominalCumulativitySummary summary
                      && ncsFamilyIdentity summary == gKey nested
                  )
                pure (ncsRoles summary, ncsSaturationArity summary)
              certifiedAuthority = localAuthority <|> externalAuthority
          pure $ do
            (roles, saturation) <- certifiedAuthority
            guard (length levels == length roles)
            guard (length arguments == saturation)
            pure . concat $
              [ case role of
                  Invariant -> [RequireInvariant parameter ("constructor field " <> field <> " uses invariant nominal family " <> gKey nested) | parameter <- levelParams level]
                  Covariant -> [RequireCovariant parameter ("constructor field " <> field <> " uses covariant nominal family " <> gKey nested) | parameter <- levelParams level]
                  Irrelevant -> []
              | (role, level) <- zip roles levels
              ]
        _ -> pure Nothing

-- | Validate the complete source-side shape of a nominal schema lift before
-- using its role vector. KCore independently checks the same evidence and
-- saturation facts. Source role publication must not infer a more permissive
-- certificate from malformed Core merely because an endpoint vector happened
-- to have the expected length.
--
-- For a valid lift, ordinary source arguments and proof evidence are not part
-- of the represented target type; callers recurse through target arguments.
-- For a malformed lift, every universe visible in either endpoint or argument
-- is conservatively invariant. The inner represented term is still analysed
-- by the caller.
sourceSchemaLiftRoleRequirements
  :: Assumptions
  -> Int
  -> Int
  -> Text
  -> GName
  -> [Level]
  -> [Level]
  -> [UniverseVariance]
  -> [SchemaRoleEvidence]
  -> SchemaActionCertificateId
  -> [Term]
  -> [Term]
  -> CheckM (Bool, [RoleRequirement])
sourceSchemaLiftRoleRequirements trusted depth universeArity reason owner source target roles evidence certificate sourceArguments targetArguments = do
  summary <- gets (Map.lookup owner . csGlobals) >>= pure . (>>= gdNominalSummary)
  alignments <- zipWithM sourceSchemaArgumentAligns sourceArguments targetArguments
  let argumentsAligned = all fst alignments
      alignmentRequirements = concatMap snd alignments
  let authorityValid = case summary of
        Just checkedSummary ->
          verifyNominalCumulativitySummary checkedSummary
            && ncsFamilyIdentity checkedSummary == gKey owner
            && ncsRoles checkedSummary == roles
            && ncsCertificateId checkedSummary == certificate
            && ncsSaturationArity checkedSummary == length sourceArguments
        Nothing -> False
      metadataValid =
        authorityValid
          && length roles == length source
          && length roles == length target
          && length roles == length evidence
          && length sourceArguments == length targetArguments
          && argumentsAligned
          && and
            [ schemaRoleEvidenceMatches role roleEvidence from to
            | (role, roleEvidence, from, to) <- zip4 roles evidence source target
            ]
      validRequirements =
        concat
          [ requirementsForUniverseRole reason role (levelParams from ++ levelParams to)
          | (role, from, to) <- zip3 roles source target
          ]
          ++ alignmentRequirements
      malformedRequirements =
        requirementsForUniverseRole
          "malformed source nominal schema lift fails closed during role publication"
          Invariant
          ( levelParamsOfTerm
              ( CSchemaLift
                  owner source target roles evidence certificate
                  sourceArguments targetArguments (CRecordV [])
              )
          )
  pure
    ( metadataValid
    , if metadataValid then validRequirements else malformedRequirements
    )
  where
    schemaRoleEvidenceMatches Invariant SchemaInvariantEvidence from to =
      normalizeLevel from == normalizeLevel to
    schemaRoleEvidenceMatches Covariant (SchemaCovariantEvidence proof) from to =
      validateUniverseEvidenceRelationUnder trusted depth universeArity (from, to) proof
    schemaRoleEvidenceMatches Irrelevant SchemaIrrelevantEvidence _ _ = True
    schemaRoleEvidenceMatches _ _ _ _ = False

    sourceSchemaArgumentAligns sourceArgument targetArgument
      | sourceArgument == targetArgument = pure (True, [])
    sourceSchemaArgumentAligns sourceArgument (CUniverseLift from to proof inner) =
      if validateUniverseEvidenceRelationUnder trusted depth universeArity (from, to) proof
        then do
          (aligned, innerRequirements) <- sourceSchemaArgumentAligns sourceArgument inner
          pure
            ( aligned
            , requirementsForUniverseRole
                "aligned nominal argument uses an authenticated universe lift"
                Covariant
                (levelParams from ++ levelParams to)
                ++ innerRequirements
            )
        else pure (False, [])
    sourceSchemaArgumentAligns sourceArgument
      (CSchemaLift nested nestedSource nestedTarget nestedRoles nestedEvidence nestedCertificate nestedSourceArguments nestedTargetArguments inner) = do
        (nestedValid, nestedRequirements) <-
          sourceSchemaLiftRoleRequirements
            trusted depth universeArity
            "nested source argument uses a certified nominal schema lift"
            nested nestedSource nestedTarget nestedRoles nestedEvidence nestedCertificate
            nestedSourceArguments nestedTargetArguments
        if nestedValid
          then do
            (aligned, innerRequirements) <- sourceSchemaArgumentAligns sourceArgument inner
            pure (aligned, nestedRequirements ++ innerRequirements)
          else pure (False, nestedRequirements)
    sourceSchemaArgumentAligns _ _ = pure (False, [])

reportConstructorSize :: Text -> Text -> Level -> Ctx -> Binder -> Text -> Icit -> Q -> Expr -> Level -> CheckM ()
reportConstructorSize dataName ctorName rho ctx binder binderName ic q annotation alpha = do
  let constraint = renderLevel alpha <> " <= " <> renderLevel rho
  report $
    withPayload
      ( withPayloadField "dataDeclaration" dataName $
          withPayloadField "dataResultUniverse" (renderLevel rho) $
            withPayloadField "constructor" ctorName $
              withPayloadField "constructorLocalBinder" binderName $
                withPayloadField "binderExplicitness" (if ic == Impl then "implicit" else "explicit") $
                  withPayloadField "binderQuantity" (renderCoreQ q) $
                    withPayloadField "binderOriginKind" "source-written" $
                      withPayloadField "binderAnnotation" (renderExprSrc annotation) $
                        withPayloadField "binderAnnotationUniverse" (renderLevel alpha) $
                          withPayloadField "requiredUniverseConstraint" constraint $
                            withPayloadField "normalizedFailedConstraint" constraint $
                              withPayloadField "levelAssumptions" (renderLevelAssumptions (ctxLevelAssumptions ctx)) $
                                withPayloadField "localRepairAvailable" "raise-data-result-universe" $
                                  payloadKind "universe-constructor-size"
      ) $
      diag SevError StageElaborate "E_DATA_CONSTRUCTOR_FIELD_UNIVERSE"
        (Just "kappa.universe.constructor-size") (bSpan binder)
        ( "constructor binder '" <> binderName <> "' has classifier Type " <> renderLevel alpha
            <> ", which does not fit the declared data universe Type " <> renderLevel rho
            <> " (§10.4.1)"
        )
