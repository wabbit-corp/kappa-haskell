-- | Helpers shared across several elaboration topics.
--
-- This is the common base of the modules carved out of "Kappa.Check": every
-- definition here is reachable from more than one of them, so it belongs to
-- no single topic. Everything else in the @Kappa.Check.*@ family imports this
-- and nothing here imports them back.
--
-- Carved out of "Kappa.Check" as part of splitting that module; see
-- "Kappa.Check.Types" for the shared data dictionary and docs\/CONCEPTS.md
-- for the vocabulary these assume.
module Kappa.Check.Support
  ( addGlobal
  , anyHole
  , bindCtx
  , bindCtxLet
  , bindCtxLetProjOp
  , bindCtxLetProjOpMode
  , bindCtxMQ
  , bindCtxMQB
  , bindCtxMQBProvisional
  , bindCtxQ
  , bindEntry
  , binderQ
  , binderTypeExpr
  , booleanLiteralEqualityPayload
  , branchFactKey
  , buildPendingEvidenceGraph
  , canonicalCoreBodyForDefinition
  , canonicalizeTermsUnderBranchFactsWith
  , canonicalizeTermsUnderCheckedBranchFacts
  , clApp
  , collectRefFacets
  , constraintLevelMetas
  , constraintOwnedAfterRetiringOccurrences
  , constructorInScope
  , ctxLen
  , ctxNatLevels
  , declarationConstraintSummary
  , declarationSchemaGeneralizableMetas
  , declarationUniverseRoles
  , decomposeBoolFact
  , delaborateType
  , delaborateTypeWithEnv
  , deleteProvisionalUniverseInstantiations
  , duplicatesOf
  , ecRT_
  , effectOperationInterfaceTerm
  , effectUniverseInterfaceTerms
  , effectiveLevelAssumptions
  , emptyBinderPrefix
  , emptyCtx
  , ensureGeneratedConstraintLambdas
  , equalityExplicitEndpoints
  , errAt
  , errMutableBinding
  , errOnce
  , errOncePerSpan
  , escapeVarCurrent
  , etaCtor
  , evalIn
  , expandedGlobalsOfTerm
  , expandedGlobalsOfTermM
  , exprHasBang
  , exprHasCurrentRead
  , extendLevelAssumption
  , finalIsSort
  , forceM
  , forceRT
  , freshLevelInstantiationMeta
  , freshLevelMeta
  , freshMeta
  , freshMetaForWithId
  , freshMetaId
  , freshMetaV
  , freshNameM
  , generatedConstraintBinderNames
  , generatedConstraintBinders
  , generatedConstraintsNotIn
  , globalCoreType
  , globalDefWithCanonicalCoreBody
  , globalUniverseInterfaceTerms
  , globalValueIsUniverseInterface
  , headerBinderQ
  , inferPrincipalAtDeclarationBoundary
  , insertLevelConstraintOwnedWithProvenance
  , insertRecursiveSchemaOccurrence
  , insertScopeName
  , installLevelAssignments
  , instanceUniverseInterfaceTerms
  , instantiateProvisionalUniversesWith
  , invalidateSemanticCaches
  , invalidateVarCurrent
  , isKindLike
  , isParametricKind
  , isTraitGoal
  , isTypeLevelValue
  , levelConstraintsOwnedBy
  , levelFieldDepsOf
  , levelMetaAdjacency
  , levelMetasOwnedBy
  , lookupCtx
  , lookupGlobalName
  , manifestValue
  , markGeneralizableLevelTerm
  , markGeneralizableLevelTermFor
  , materializePendingUniverseProofsRaw
  , materializeProvisionalUniverseConstraints
  , materializeProvisionalUniverseConstraintsFor
  , memberVisible
  , mentionsVar
  , metaOccursInValue
  , monadActionViewValue
  , monadRefReadAction
  , monadResultType
  , mutableBindingLookupFields
  , neutralValueTerm
  , nominalDataHead
  , nominalFamilyValueHead
  , normalizeBinderDomain
  , normalizeBinderDomainWithRecovery
  , normalizeBoolFacts
  , observationDependenciesForTerm
  , observationForBinding
  , observationJudgmentForTerm
  , observationTermTypeAt
  , orderLevelConstraintsBySignatureOccurrence
  , ownName
  , pendingEntryCtx
  , pendingEntryMeta
  , pendingEvidenceComponentIn
  , prependGeneratedConstraintBinders
  , principalLevelAssignmentsWithin
  , principalizeLevelOccurrence
  , provisionalUniverseProjections
  , qOf
  , quoteIn
  , quoteRawIn
  , reachableLevelMetas
  , recordDeclSite
  , recordRecognizedMultishotOp
  , recordRecursiveSchemaOccurrence
  , refreshPendingEntry
  , registerProvisionalGlobalUniverseMetas
  , reindexLevelConstraints
  , renderCoreQ
  , renderLevelAssumptions
  , renderPayloadTerm
  , renderPayloadValue
  , report
  , reportLevelSolveError
  , reportLevelSolveErrorWithProvenance
  , reportNoPrincipalUniverseDiagnostic
  , reportParametricPromotion
  , reportPrincipalBoundaryFailure
  , reportUnsolvedHoleAt
  , reportUnsupported
  , resolveCtor
  , resolveCtorWithoutDiagnostic
  , resolveFinalizedOwnerLevel
  , resolveModuleObjectName
  , resolvedMetaCore
  , rewriteGeneratedConstraintEvidence
  , schemaBearingLevelMetas
  , scopedBoolFactsAt
  , selectFormationMode
  , selectedConstraintGroups
  , setCheckInstances
  , shapeModule
  , solveMeta
  , sortName
  , specializeConstructorType
  , specializeDeclarationUniverses
  , specializeGlobalAt
  , stableGeneratedNameAt
  , standardArithmeticDirectProvider
  , standardArithmeticOperationTrait
  , standardTypeLevelDictionary
  , staticGlobalExpr
  , surfPatVars
  , surfaceQuantityPositive
  , surfaceQuantityZero
  , telePi
  , thisDepsOf
  , thisG
  , traitMemberOwnerUniverseMetas
  , traitSemanticSpineIn
  , transparentProofNormalize
  , typeLevelRelationSpine
  , unmaterializedProvisionalUniverseMetas
  , unqualifiedConstructorCandidates
  , unsolvedMetaIdsIn
  , unsupported
  , unsupportedAt
  , withNamedHoleScope
  , zonkLevels
  , zonkTermM
  , zonkedBoolFacts
  , zonkedPendingLevelConstraints
  , expectUnsatisfiedDiags
  , linkedCoreBodies
  , metaObservationMode
  , nominalHiddenProjectionInfo
  , recursiveSchemaEdgeRecorded
  , scriptUnsafeConfig
  , selectedUniverseEvidenceRecorded
  , universeInferenceRecord
  , unresolvedBuiltins
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

-- | Runtime implementations visible to a backend invocation. The mutable
-- 'csCoreBodies' map is deliberately current-unit only: imported checked
-- modules retain their implementation bodies on immutable 'GlobalDef'
-- entries. Keeping the linked view derived prevents imported artifacts from
-- being re-zonked, ownership-analysed, or linted as though they belonged to
-- the module currently being checked.
linkedCoreBodies :: CheckState -> Map GName Term
linkedCoreBodies state =
  Map.union
    (csCoreBodies state)
    ( Map.union
        (csImportedCoreBodies state)
        (Map.mapMaybe gdCoreBody (csGlobals state))
    )

-- | §4.2: in script mode implementations MAY default the unsafe/debug
-- settings to @true@ for experimentation. This implementation does so,
-- so scripts can use the escapes without per-build flags.
scriptUnsafeConfig :: UnsafeConfig
scriptUnsafeConfig = UnsafeConfig True True True True True True True

insertRecursiveSchemaOccurrence
  :: RecursiveSchemaOccurrence
  -> CheckState
  -> CheckState
insertRecursiveSchemaOccurrence occurrence state =
  state
    { csRecursiveSchemaOccurrences =
        occurrence : csRecursiveSchemaOccurrences state
    , csRecursiveSchemaOccurrencesByCaller =
        Map.insertWith
          (++)
          (rsoCaller occurrence)
          [occurrence]
          (csRecursiveSchemaOccurrencesByCaller state)
    }

recursiveSchemaEdgeRecorded :: CheckState -> Text -> Text -> Text -> Bool
recursiveSchemaEdgeRecorded state caller callee relation =
  any matches (Set.toList (csRecursiveSchemaEdges state))
  where
    matches edge =
      nameMatches caller (rseCaller edge)
        && nameMatches callee (rseCallee edge)
        && relation == relationName (rseRelation edge)
    nameMatches requested name = requested == gnameText name || requested == gKey name
    relationName = \case
      RecursiveSchemaIdentity -> "identity"
      RecursiveSchemaLowerOrEqual -> "lower-or-equal"
      RecursiveSchemaStrictLower -> "strict-lower"

selectedUniverseEvidenceRecorded :: CheckState -> Text -> Text -> Bool
selectedUniverseEvidenceRecorded state goal evidence =
  any matches (Set.toList (csSelectedUniverseEvidence state))
  where
    matches selected =
      normalizeGoal goal == normalizeGoal (sueGoal selected)
        && (evidence == gnameText (sueEvidence selected) || evidence == gKey (sueEvidence selected))
    normalizeGoal = T.unwords . T.words

universeInferenceRecord :: CheckState -> Text -> Maybe UniverseInferenceRecord
universeInferenceRecord state requested =
  case [record | (name, record) <- Map.toAscList (csUniverseInferenceRecords state), matches name] of
    [record] -> Just record
    _ -> Nothing
  where
    matches name =
      requested == name
        || ("." <> requested) `T.isSuffixOf` name

-- | The §22 derivation-shape reflection module.
shapeModule :: ModuleName
shapeModule = modDerivingShape

-- | The wired-in prelude names (see "Kappa.Builtins") that fail to resolve
-- in a checked state — i.e. names the compiler assumes the prelude defines
-- but which are absent from its globals and constructors. An empty result
-- means the compiler↔prelude name contract holds. Used by the pipeline's
-- post-prelude validation to turn silent drift into a reported error.
unresolvedBuiltins :: CheckState -> [WiredIn]
unresolvedBuiltins st =
  [ w
  | w <- wiredInPreludeNames
  , not (wiName w `Map.member` csGlobals st)
  , not (wiName w `Map.member` csCtors st)
  ]

-- | Reconstruct one operation header as a closed term under the owning
-- effect interface's parameter telescope. Operation signatures are part of
-- the effect declaration's observable interface (§11.1.2.3A, §18.1.15):
-- levels that occur only in an operation domain must therefore contribute to
-- the effect's declaration-universe schema just like levels in the effect's
-- own parameter telescope.
effectOperationInterfaceTerm :: EffLabelInfo -> EffOpInfo -> Term
effectOperationInterfaceTerm effectInfo operation =
  foldr telePi operationBody (eliParams effectInfo)
  where
    operationBody =
      foldr telePi
        (foldr telePi (eoiResT operation) (eoiArgs operation))
        (eoiImplicits operation)

-- | Canonical operation-header terms owned by one effect interface. Alias
-- labels reuse this metadata but do not own another copy of its universe
-- schema, so only the canonical (unfixed) interface entry contributes.
effectUniverseInterfaceTerms :: CheckState -> GName -> [Term]
effectUniverseInterfaceTerms st interface =
  [ effectOperationInterfaceTerm effectInfo operation
  | effectInfo <- maybeToList (Map.lookup interface (csEffectInterfaces st))
  , operation <- eliOps effectInfo
  ]

emptyCtx :: Ctx
emptyCtx = Ctx [] [] Map.empty Map.empty Map.empty Set.empty [] Map.empty False Nothing Map.empty Map.empty 0 Nothing emptyAssumptions Map.empty Map.empty

ctxLen :: Ctx -> Int
ctxLen = length . ctxEntries

-- | Shared binder scaffold: prepend @entry@, push @v@ onto the
-- environment, and drop any prior flow-refinement/alias facts about the
-- binder's name (a fresh binder shadows them). All three @bindCtx*@
-- helpers differ only in the entry's flags and the environment value.
bindEntry :: CtxEntry -> Value -> Ctx -> Ctx
bindEntry entry v ctx =
  ctx
    { ctxEntries = entry : ctxEntries ctx
    , ctxEnv = v : ctxEnv ctx
    , ctxRefines = Map.delete (ceName entry) (ctxRefines ctx)
    , ctxAliases = Map.delete (ceName entry) (ctxAliases ctx)
    , ctxVarCurrentVersions = Map.delete (ceName entry) (ctxVarCurrentVersions ctx)
    , ctxVarCurrentEscaped = Set.delete (ceName entry) (ctxVarCurrentEscaped ctx)
    , ctxBorrowCaptureRegions = Map.delete (ceName entry) (ctxBorrowCaptureRegions ctx)
    }

bindCtx :: Text -> Bool -> Value -> Ctx -> Ctx
bindCtx n implocal ty ctx =
  bindCtxMQ Ordinary QW n implocal ty ctx

bindCtxQ :: Q -> Text -> Bool -> Value -> Ctx -> Ctx
bindCtxQ q n implocal ty ctx =
  bindCtxMQ Ordinary q n implocal ty ctx

bindCtxMQ :: ObservationMode -> Q -> Text -> Bool -> Value -> Ctx -> Ctx
bindCtxMQ mode q n implocal ty ctx =
  bindCtxMQB mode q n implocal False ty ctx

-- | Borrow-aware form of 'bindCtxMQProvisional'. Declaration-header and
-- explicit-forall inference must retain the complete source access contract
-- while postponing only observation-mode selection.
bindCtxMQBProvisional :: ObservationMode -> Q -> Text -> Bool -> Bool -> Value -> Ctx -> Ctx
bindCtxMQBProvisional mode q n implocal borrowed ty ctx =
  case ctxEntries bound of
    entry : rest -> bound {ctxEntries = entry {ceModeProvisional = True} : rest}
    [] -> bound
  where
    bound = bindCtxMQB mode q n implocal borrowed ty ctx

-- | Bind a local with its complete telescope contract. Implicit-candidate
-- status and borrowed access are independent properties; conflating them made
-- borrowed explicit binders participate in implicit search while silently
-- dropping their access restriction.
bindCtxMQB :: ObservationMode -> Q -> Text -> Bool -> Bool -> Value -> Ctx -> Ctx
bindCtxMQB mode q n implocal borrowed ty ctx =
  bindEntry
    (CtxEntry n ty Nothing mode False implocal Nothing Nothing Nothing q Nothing Nothing borrowed noSpan)
    (VRigid (length (ctxEnv ctx)) [])
    ctx

-- | Bind a local definition: the environment carries the definiens, so
-- conversion sees through local lets (delta for locals, §15.1).
bindCtxLet :: Text -> Bool -> Value -> Value -> Ctx -> Ctx
bindCtxLet n implocal ty v ctx =
  bindCtxLetProj n implocal ty v Nothing ctx

bindCtxLetProj :: Text -> Bool -> Value -> Value -> Maybe ProjInfo -> Ctx -> Ctx
bindCtxLetProj n implocal ty v mpj ctx =
  bindCtxLetProjOp n implocal ty v mpj Nothing ctx

bindCtxLetProjOp :: Text -> Bool -> Value -> Value -> Maybe ProjInfo -> Maybe EffectOpValueInfo -> Ctx -> Ctx
bindCtxLetProjOp n implocal ty v mpj mop ctx =
  bindCtxLetProjOpMode n implocal ty v mpj mop Ordinary Nothing ctx

bindCtxLetProjOpMode :: Text -> Bool -> Value -> Value -> Maybe ProjInfo -> Maybe EffectOpValueInfo -> ObservationMode -> Maybe Text -> Ctx -> Ctx
bindCtxLetProjOpMode n implocal ty v mpj mop mode observationOrigin ctx =
  bindEntry (CtxEntry n ty Nothing mode False implocal Nothing mpj mop QW observationOrigin Nothing False noSpan) v ctx

invalidateVarCurrent :: Text -> Ctx -> Ctx
invalidateVarCurrent n ctx =
  ctx {ctxVarCurrentVersions = Map.adjust (+ 1) n (ctxVarCurrentVersions ctx)}

escapeVarCurrent :: Text -> Ctx -> Ctx
escapeVarCurrent n ctx =
  let ctx' = invalidateVarCurrent n ctx
   in ctx' {ctxVarCurrentEscaped = Set.insert n (ctxVarCurrentEscaped ctx')}

lookupCtx :: Text -> Ctx -> Maybe (Int, CtxEntry)
lookupCtx n ctx = go 0 (ctxEntries ctx)
  where
    go _ [] = Nothing
    go i (e : rest)
      | ceName e == n = Just (i, e)
      | otherwise = go (i + 1) rest

evalIn :: HasCallStack => Ctx -> Term -> CheckM Value
evalIn ctx t = do
  unless (termScopedAt (ctxLen ctx) t) $
    error
      ( "Kappa.Check.evalIn: internal error: term is not scoped at context depth "
          <> show (ctxLen ctx)
          <> ": "
          <> T.unpack (renderTerm t)
          <> "\nraw term: "
          <> show t
          <> "\n"
          <> prettyCallStack callStack
      )
  ec <- ec_
  pure (eval ec (ctxEnv ctx) t)

quoteIn :: HasCallStack => Ctx -> Value -> CheckM Term
quoteIn ctx v = do
  quoted <- quoteRawIn ctx v
  unless (termScopedAt (ctxLen ctx) quoted) $
    error
      ( "Kappa.Check.quoteIn: internal error: value quotes outside context depth "
          <> show (ctxLen ctx)
          <> ": "
          <> T.unpack (renderTerm quoted)
          <> "\nraw term: "
          <> show quoted
          <> "\n"
          <> prettyCallStack callStack
      )
  pure quoted

quoteRawIn :: Ctx -> Value -> CheckM Term
quoteRawIn ctx v = do
  ec <- ec_
  pure (quote ec (ctxLen ctx) v)

forceM :: Value -> CheckM Value
forceM v = do
  ec <- ec_
  pure (force ec v)

clApp :: Closure -> Value -> CheckM Value
clApp (Closure env body) v = do
  ec <- ec_
  pure (eval ec (v : env) body)

-- | Record a diagnostic. Diagnostics accumulate in reverse (prepend)
-- order; 'checkModule' restores source order once at the end.
report :: Diagnostic -> CheckM ()
report d = modify' $ \st -> st {csDiags = d : csDiags st}

-- | The neutral standing for the record under §13.2.1 elaboration.
thisG :: GName
thisG = prelThis

-- | The sibling field labels a §13.2.1 field type depends on.
thisDepsOf :: Term -> [Text]
thisDepsOf = projectionDepsOf thisG

-- | Sibling dependencies represented in the universe solver language rather
-- than as ordinary Core projections.  Dependent record telescopes use both
-- forms, and their introduction/update order must respect both.
levelFieldDepsOf :: Term -> [Text]
levelFieldDepsOf =
  foldTerm
    (\case
      CSort level -> names level
      CLevel level -> names level
      CGlobal _ universes -> concatMap names universes
      CUniverseLift from to evidence _ ->
        names from
          ++ names to
          ++ concatMap
            (\step -> names (uesLower step) ++ names (uesUpper step)
              ++ concatMap (\(lhs, rhs) -> names lhs ++ names rhs) (uesAssumptions step))
            (ueSteps evidence)
      _ -> [])
    (const [])
  where
    names level = [field | LField _ field <- universeLevelNodes level]

    universeLevelNodes level = level : case level of
      LSucc inner -> universeLevelNodes inner
      LAdd lhs rhs -> universeLevelNodes lhs ++ universeLevelNodes rhs
      LMax lhs rhs -> universeLevelNodes lhs ++ universeLevelNodes rhs
      _ -> []

-- | Report a diagnostic unless an identical (code, message) one was
-- already reported — for judgements re-checked once per occurrence of
-- the same source type (e.g. a signature and its definition binders).
errOnce :: Span -> DiagnosticCode -> Maybe DiagnosticFamily -> Text -> CheckM ()
errOnce sp code fam msg = do
  ds <- gets csDiags
  unless (any (\d -> dCode d == code && dMessage d == msg) ds) $
    errAt sp code fam msg

-- | Like 'errOnce', but distinct origins each report (one diagnostic
-- per malformed source construct, not per judgement).
errOncePerSpan :: Span -> DiagnosticCode -> Maybe DiagnosticFamily -> Text -> CheckM ()
errOncePerSpan sp code fam msg = do
  ds <- gets csDiags
  unless (any (\d -> dCode d == code && dMessage d == msg && dPrimary d == sp) ds) $
    errAt sp code fam msg

errAt :: Span -> DiagnosticCode -> Maybe DiagnosticFamily -> Text -> CheckM ()
errAt sp code fam msg = report (diag SevError StageElaborate code fam sp msg)

mutableBindingPayload :: Text -> Text -> [(Text, Text)] -> Payload
mutableBindingPayload binding selectedFacet fields =
  foldl
    (\p (k, v) -> withPayloadField k v p)
    ( withPayloadField "selectedFacet" selectedFacet $
        withPayloadField "binding" binding $
          payloadKind "mutable-binding"
    )
    fields

errMutableBinding :: Span -> DiagnosticCode -> Text -> Text -> [(Text, Text)] -> Text -> CheckM ()
errMutableBinding sp code binding selectedFacet fields msg =
  report $
    withPayload (mutableBindingPayload binding selectedFacet fields) $
      diag SevError StageElaborate code (Just "kappa.var.mutable-binding") sp msg

mutableBindingInfoFields :: Ctx -> Int -> CtxEntry -> VarRefInfo -> Text -> CheckM [(Text, Text)]
mutableBindingInfoFields ctx i _entry info occurrence = do
  hiddenRef <- renderPayloadValue ctx (vriDiagnosticRefType info)
  stored <- renderPayloadValue ctx (vriStoredType info)
  monadTy <- renderPayloadValue ctx (vriMonadType info)
  evidenceTy <- renderPayloadValue ctx (VGlobN prelMonadRef [(Expl, vriMonadType info)])
  evidence <- renderPayloadTerm ctx (shiftTerm (i + 1) 0 (vriMonadRefDict info))
  pure
    [ ("hiddenReferenceType", hiddenRef)
    , ("storedValueType", stored)
    , ("enclosingMonad", monadTy)
    , ("enclosingDoBlock", "nearest")
    , ("monadRefEvidence", evidence)
    , ("monadRefEvidenceType", evidenceTy)
    , ("occurrence", occurrence)
    ]

mutableBindingLookupFields :: Ctx -> Name -> Text -> CheckM [(Text, Text)]
mutableBindingLookupFields ctx n occurrence =
  case lookupCtx (nameText n) ctx of
    Just (i, entry)
      | Just info <- ceVarInfo entry -> mutableBindingInfoFields ctx i entry info occurrence
    _ -> pure []

recordRecognizedMultishotOp :: Span -> EffectOpValueInfo -> CheckM ()
recordRecognizedMultishotOp sp info =
  modify' $ \st ->
    st {csRecognizedMultishotOps = Map.insert sp (eoviLabel info, eoviName info) (csRecognizedMultishotOps st)}

renderPayloadValue :: Ctx -> Value -> CheckM Text
renderPayloadValue ctx v = do
  tm <- quoteIn ctx v
  tm' <- principalizePayloadLevels (ctxLen ctx) tm >>= normalizeTermAt (ctxLen ctx)
  pure (renderTerm tm')

renderPayloadTerm :: Ctx -> Term -> CheckM Text
renderPayloadTerm ctx tm = do
  tm' <- principalizePayloadLevels (ctxLen ctx) tm
  pure (renderTerm tm')

-- | Diagnostic payloads are emitted before the enclosing declaration's final
-- universe solve, but portable payloads must never expose compiler level-meta
-- ids. Compute the same least solution non-destructively for the metas visible
-- in the rendered term. If the constraint set is not yet principal, retain the
-- ordinary zonked term rather than guessing.
principalizePayloadLevels :: Int -> Term -> CheckM Term
principalizePayloadLevels depth term = do
  zonked <- zonkTermM depth term
  st <- get
  let assignments = csLevelAssignments st
      base = zonkLevels assignments zonked
      targets = Set.fromList (levelMetasOfTerm base)
      constraints =
        [ substituteLevelConstraintMetas assignments constraint
        | constraint <- csLevelConstraints st
        ]
  if Set.null targets
    then pure base
    else case solveLevelConstraintsFor targets constraints of
      Left _ -> pure base
      Right solution -> do
        let solved = lsAssignments solution
            unresolved = Set.filter (`Map.notMember` solved) targets
            candidate = Map.union solved (Map.fromSet (const LZero) unresolved)
            residualTargets =
              Set.intersection targets . Set.fromList $
                concat
                  [ levelMetas (substituteLevelMetas candidate (lcLhs constraint))
                      ++ levelMetas (substituteLevelMetas candidate (lcRhs constraint))
                  | constraint <- lsResidual solution
                  ]
        pure $
          if Set.null residualTargets
            then zonkLevels candidate base
            else base

-- | §3 @kappa.unsupported.deterministic@ payload: the family REQUIRES the
-- diagnostic to carry the unsupported action, the selected language profile,
-- and whether source analysis continued (plus a backend profile / required
-- capability when those are relevant — these v1 restrictions are
-- elaboration-level with no owning capability gate, so those fields are
-- recorded as not-applicable). Source analysis continues: the error is
-- collected and the rest of the unit is still checked.
unsupportedPayload :: Text -> Payload
unsupportedPayload action =
  withPayloadField "unsupportedAction" action
    $ withPayloadField "languageProfile" "default"
    $ withPayloadField "backendProfile" "n/a"
    $ withPayloadField "requiredCapability" "none"
    $ withPayloadField "sourceAnalysisContinued" "true"
    $ payloadKind "unsupported-deterministic"

-- | Emit a deterministic-unsupported diagnostic (§3.x family
-- @kappa.unsupported.deterministic@) carrying the mandated payload.
unsupportedAt :: Span -> Text -> CheckM ()
unsupportedAt sp msg =
  report
    ( withPayload (unsupportedPayload msg)
        (diag SevError StageElaborate "E_UNSUPPORTED" (Just "kappa.unsupported.deterministic") sp msg)
    )

-- | Allocate a fresh, unsolved metavariable and return its raw id.
freshMetaId :: CheckM MetaId
freshMetaId = do
  st <- get
  let m = csNextMeta st
  put st {csNextMeta = m + 1, csMetas = Map.insert m Nothing (csMetas st)}
  pure m

freshMeta :: CheckM Term
freshMeta = CMeta <$> freshMetaId

freshMetaV :: Ctx -> CheckM Value
freshMetaV ctx = freshMeta >>= evalIn ctx

-- | Allocate a classifier-authenticated inference meta while retaining its
-- stable identity for analyses that must track the variable independently of
-- its current solution.
freshMetaForWithId :: Ctx -> Value -> CheckM (MetaId, Term)
freshMetaForWithId ctx classifier = do
  firstClassLevel <- isTypeLevelValue classifier
  meta <- freshMetaId
  classifierTerm <- quoteIn ctx classifier
  modify' $ \st ->
    st
      { csMetaClassifiers =
          Map.insert
            meta
            (MetaClassifier (ctxLen ctx) classifierTerm Nothing)
            (csMetaClassifiers st)
      , csFirstClassLevelMetas =
          if firstClassLevel
            then Set.insert meta (csFirstClassLevelMetas st)
            else csFirstClassLevelMetas st
      }
  pure (meta, CMeta meta)

freshLevelMeta :: CheckM Level
freshLevelMeta = LMeta <$> freshMetaId

markGeneralizableLevelTermFor :: GName -> Term -> CheckM ()
markGeneralizableLevelTermFor owner term =
  modify' $ \st ->
    let metas = Set.fromList (levelMetasOfTerm term)
     in st
          { csLevelGeneralizableMetas =
              Set.union metas (csLevelGeneralizableMetas st)
          , csLevelGeneralizableOwners =
              Set.foldl'
                (\owners meta -> Map.insertWith Set.union meta (Set.singleton owner) owners)
                (csLevelGeneralizableOwners st)
                metas
          , csLevelGeneralizableMetasByOwner =
              Map.insertWith
                Set.union
                owner
                metas
                (csLevelGeneralizableMetasByOwner st)
          }

markGeneralizableLevelTerm :: Term -> CheckM ()
markGeneralizableLevelTerm term = do
  owner <- gets csActiveUniverseDefinition
  forM_ owner $ \declaration ->
    markGeneralizableLevelTermFor declaration term

declarationSchemaGeneralizableMetas :: Term -> Set LevelMeta
declarationSchemaGeneralizableMetas term =
  Set.intersection
    (durGeneralizable (declarationUniverseRoles term))
    (schemaBearingLevelMetas term)

-- | Levels visible only in cumulative annotations or generated level-proof
-- binders are occurrence/checking facts, not evidence that an inferred value
-- abstracts over that level. Ordinary nominal spines and source binders remain
-- schema-bearing. This distinction is made only while promoting inferred
-- occurrence metas; finalized interface role analysis still sees its complete
-- proof telescope.
schemaBearingLevelMetas :: Term -> Set LevelMeta
schemaBearingLevelMetas =
  Set.fromList . levelMetasOfTerm . eraseCheckingAnnotations
  where
    eraseCheckingAnnotations =
      mapTermWithDepth
        ( \_ -> \case
            CUniverseLift _ _ _ payload ->
              Just (eraseCheckingAnnotations payload)
            CPiEvidenceM _ _ _ _ _ _ (Just _) _ _ codomain ->
              Just (eraseCheckingAnnotations codomain)
            _ -> Nothing
        )
        0

-- | Allocate a universe metavariable for one omitted declaration-universe
-- instantiation. Such a meta may occur in a user-observable interface, but it
-- does not itself denote a new source universe parameter. Its least admissible
-- value is selected during SCC principalization (§11.1.2.4A).
freshLevelInstantiationMeta :: CheckM Level
freshLevelInstantiationMeta = do
  level <- freshLevelMeta
  owner <- gets csActiveUniverseDefinition
  case level of
    LMeta meta ->
      modify' $ \st ->
        st
          { csLevelInstantiationMetas =
              Set.insert meta (csLevelInstantiationMetas st)
          , csLevelInstantiationOwners =
              case owner of
                Nothing -> csLevelInstantiationOwners st
                Just declaration ->
                  Map.insertWith
                    Set.union
                    meta
                    (Set.singleton declaration)
                    (csLevelInstantiationOwners st)
          , csLevelInstantiationMetasByOwner =
              case owner of
                Nothing -> csLevelInstantiationMetasByOwner st
                Just declaration ->
                  Map.insertWith
                    Set.union
                    declaration
                    (Set.singleton meta)
                    (csLevelInstantiationMetasByOwner st)
          }
    _ -> pure ()
  pure level

-- | Semantic caches are keyed by a small epoch rather than by the whole
-- evaluator state.  Advancing the epoch is required when global lookup,
-- trait/instance lookup, or conversion-time reducibility changes.
-- Metavariable-sensitive normalization/proposition entries are kept out of the
-- caches until their quoted keys contain no unsolved metas; otherwise every
-- solved evidence hole would invalidate the very cache meant to tame evidence
-- storms.  Clearing the maps at the same time keeps memory use bounded on
-- proof-heavy files and prevents stale trait evidence after a new instance
-- enters scope.
invalidateSemanticCaches :: CheckState -> CheckState
invalidateSemanticCaches st =
  st
    { csEvidenceCache = Map.empty
    , csNormEpoch = csNormEpoch st + 1
    , csNormCache = Map.empty
    , csPropCache = Map.empty
    }

solveMeta :: HasCallStack => MetaId -> Value -> CheckM ()
solveMeta m v = do
  state <- get
  case Map.lookup m (csMetaClassifiers state) of
    Just classifier
      | let depth = micDepth classifier
            candidate = quote (ecOf state) depth v
      , not (termScopedAt depth candidate) ->
          error
            ( "Kappa.Check.solveMeta: internal error: candidate for meta "
                <> show m
                <> " escapes its creation depth "
                <> show depth
                <> "\nclassifier: "
                <> show (micType classifier)
                <> "\ncandidate: "
                <> show candidate
                <> "\neffective level: "
                <> show
                  ( substituteLevelMetas
                      (csLevelAssignments state)
                      (LMeta m)
                  )
                <> "\n"
                <> prettyCallStack callStack
            )
    _ -> pure ()
  modify' $ \next ->
    next
      { csMetas = Map.insert m (Just v) (csMetas next)
      , csSolvedMetas = Set.insert m (csSolvedMetas next)
      , csMetaAssignmentGenerations =
          Map.insertWith (+) m 1 (csMetaAssignmentGenerations next)
      }

freshNameM :: Text -> CheckM Text
freshNameM base = do
  st <- get
  put st {csFresh = csFresh st + 1}
  pure (base <> T.pack (show (csFresh st)))

-- | Semantic generated globals must not inherit the allocation order of
-- unrelated checker temporaries. The declaration origin is the authoritative
-- identity source until the frontend carries first-class declaration IDs.
stableGeneratedNameAt :: Text -> Text -> Span -> CheckM Text
stableGeneratedNameAt category written site = do
  owner <- gets (moduleNameText . csModule)
  pure
    ( "#generated."
        <> category
        <> "."
        <> owner
        <> "."
        <> written
        <> "@"
        <> T.pack (spanFile site)
        <> ":"
        <> T.pack (show (posLine (spanStart site)))
        <> ":"
        <> T.pack (show (posCol (spanStart site)))
    )

-- | Install a checked Core body as the single authority for both lowering and
-- NbE. Declaration-universe generalization rewrites the Core term; retaining a
-- semantic value evaluated from the pre-generalized term leaves solved metas
-- whose 'LParam's belong to the old declaration telescope. Re-evaluating the
-- closed body is structural (functions remain closures and global references
-- remain neutral) and keeps every later lookup on the same generalized term.
canonicalCoreBodyForDefinition :: GlobalDef -> Term -> Term
canonicalCoreBodyForDefinition definition =
  zonkTermWith
    (\_ _ -> Nothing)
    ( substituteLevelMetas
        ( Map.fromList
            [ (meta, LParam parameter)
            | (meta, parameter) <-
                gdProvisionalUniverseProjection definition
            , parameter >= 0
            , parameter < dutParameterCount (gdUniverses definition)
            ]
        )
    )
    0

globalDefWithCanonicalCoreBody :: CheckState -> Term -> GlobalDef -> GlobalDef
globalDefWithCanonicalCoreBody st body definition =
  let canonicalBody = canonicalCoreBodyForDefinition definition body
   in
  definition
    { gdValue = Just (eval (ecOf st) [] canonicalBody)
    , gdCoreBody = Just canonicalBody
    }

addGlobal :: GName -> GlobalDef -> CheckM ()
addGlobal g@(GName m nm) gd = modify' $ \st ->
  let gdWithBody =
        maybe gd (\body -> globalDefWithCanonicalCoreBody st body gd)
          (Map.lookup g (csCoreBodies st))
      gd' =
        if Map.null (csActiveUniverseSchema st)
          then gdWithBody
          else
            globalDefWithUniverses
              ( DeclarationUniverseTelescope
                  (Map.size (csActiveUniverseSchema st))
                  True
              )
              gdWithBody
   in invalidateSemanticCaches
    ( st
        { csGlobals = Map.insert g gd' (csGlobals st)
        , -- Keep the §3.2.2 typo-suggestion index (if already built) in step
          -- with the module's own globals, so it never needs a full rebuild
          -- (see 'moduleScopeNameIndex'). Names from other modules are not
          -- unqualified-in-scope here, so only this module's globals extend it.
          csScopeNameCache =
            if m == csModule st
              then fmap (insertScopeName nm) (csScopeNameCache st)
              else csScopeNameCache st
        }
    )

-- | Add one spelling to the length-bucketed §3.2.2 candidate index.
insertScopeName :: Text -> Map Int (Set Text) -> Map Int (Set Text)
insertScopeName nm = Map.insertWith Set.union (T.length nm) (Set.singleton nm)

-- | §3.1.1A: record the first declaration site of a module-scope name
-- (later occurrences keep the earliest span). Consulted by the
-- duplicate-declaration diagnostic to cite the original site.
recordDeclSite :: GName -> Span -> CheckM ()
recordDeclSite g sp =
  modify' $ \st -> st {csDeclSites = Map.insertWith (\_ old -> old) g sp (csDeclSites st)}

-- | Hidden declaration-universe constraints are assumptions while checking
-- the declaration that owns them. They are not ambient assumptions at an
-- ordinary reference: 'instantiateUniverseTelescope' turns them into fresh
-- level constraints for that use instead.
effectiveLevelAssumptions :: Ctx -> CheckM Assumptions
effectiveLevelAssumptions ctx = do
  active <- gets csActiveUniverseDefinition
  globals <- gets csGlobals
  pending <- gets csPendingUniverseProofs
  assignments <- gets csLevelAssignments
  ec <- ec_
  let scoped = case active >>= (`Map.lookup` globals) of
        Nothing -> ctxLevelAssumptions ctx
        Just gd ->
          foldl'
            (\assumptions constraint -> insertAssumption (ucLower constraint) (ucUpper constraint) assumptions)
            (ctxLevelAssumptions ctx)
            ( declarationConstraintSummary (dutParameterCount (gdUniverses gd)) (globalCoreType ec gd)
                ++ maybe [] id (active >>= (`Map.lookup` pending))
            )
  pure (substituteLevelAssumptions assignments scoped)

-- | The declaration type is the sole authority for schema constraints.  A
-- summary is admissible only when an authenticated Pi assumption is closed
-- over this declaration's hidden universe parameters; term-local level
-- variables, fields, and metas are ordinary lexical assumptions instead.
declarationConstraintSummary :: Int -> Term -> [UniverseConstraint]
declarationConstraintSummary = declarationUniverseConstraints

constraintProofType :: UniverseConstraint -> Term
constraintProofType (UniverseConstraint lower upper) =
  CApp Expl
    (CApp Expl (CGlobal prelLevelLe []) (CLevel lower))
    (CLevel upper)

generatedConstraintName :: Int -> Text
generatedConstraintName index = "__universeConstraint" <> T.pack (show index)

prependGeneratedConstraintBinders
  :: Int
  -> [UniverseConstraint]
  -> Term
  -> Term
  -> (Term, Term)
prependGeneratedConstraintBinders parameterCount requested ty body =
  let generated = generatedConstraintsNotIn parameterCount requested ty
      existing = declarationConstraintSummary parameterCount ty
      indexed = zip [length existing ..] generated
      wrapType (index, constraint@(UniverseConstraint lower upper)) codomain =
        CPiEvidenceM Ordinary FormationOrdinary Impl Q0 False
          (generatedConstraintName index)
          (Just (lower, upper))
          BinderGenerated
          (constraintProofType constraint)
          codomain
      wrapBody (index, _) term =
        CLamM Ordinary Impl Q0 (generatedConstraintName index) term
   in (foldr wrapType ty indexed, foldr wrapBody body indexed)

generatedConstraintsNotIn :: Int -> [UniverseConstraint] -> Term -> [UniverseConstraint]
generatedConstraintsNotIn parameterCount requested ty =
  let existing = declarationConstraintSummary parameterCount ty
      existingAssumptions =
        foldl'
          (\assumptions constraint ->
             insertAssumption (ucLower constraint) (ucUpper constraint) assumptions)
          emptyAssumptions
          existing
   in [ constraint
      | constraint <- dedupeUniverseConstraints requested
      , not (any (equivalentUniverseConstraint constraint) existing)
      , proveLevelLeq existingAssumptions (ucLower constraint) (ucUpper constraint) /= Proved
      ]

-- | §11.1.2.3A.3 orders generated proof binders by the first occurrence of
-- their normalized proposition in the completed declaration signature.
-- Constraint allocation order is an implementation detail: speculative
-- elaboration and candidate rollback may allocate equivalent obligations in
-- a different order.  The diagnostic span is the retained signature
-- occurrence identity; normalized endpoints provide a deterministic order
-- for multiple obligations originating at the same syntax node.  Constraints
-- without a source occurrence sort after source-backed obligations and by
-- their semantic proposition only.
orderLevelConstraintsBySignatureOccurrence
  :: CheckState
  -> [LevelConstraint]
  -> [LevelConstraint]
orderLevelConstraintsBySignatureOccurrence state =
  sortOn lcIdentity

-- | Repair a body at the exact boundary where declaration constraints become
-- new outer proof binders. Pending evidence metas are replaced only by a
-- semantically equal caller constraint. A global receives the newly-prepended
-- target arguments only when every target constraint, after specializing its
-- declaration universe spine, matches an available caller binder. Any other
-- call remains ill-typed for the finalized interface and is rejected by the
-- ordinary Core verifier rather than receiving guessed evidence.
rewriteGeneratedConstraintEvidence
  :: Map GName [UniverseConstraint]
  -> [UniverseConstraint]
  -> Map MetaId UniverseConstraint
  -> Term
  -> (Term, Set MetaId)
rewriteGeneratedConstraintEvidence targetConstraints callerConstraints pendingEvidence body =
  (mapTermWithDepth rewrite 0 body, resolvedPending)
  where
    callerCount = length callerConstraints
    bodyMetas = Set.fromList (metaIdsOf body)
    pendingIndices =
      Map.mapMaybe
        (\constraint -> List.findIndex (equivalentUniverseConstraint constraint) callerConstraints)
        pendingEvidence
    resolvedPending = Set.intersection bodyMetas (Map.keysSet pendingIndices)

    proofVariable depth index = CVar (depth + callerCount - index - 1)

    rewrite depth = \case
      CMeta meta
        | Just index <- Map.lookup meta pendingIndices ->
            Just (proofVariable depth index)
      CGlobal target universes
        | Just constraints <- Map.lookup target targetConstraints
        , not (null constraints)
        , Just indices <- traverse callerIndex (map instantiate constraints) ->
            Just $
              foldl'
                (CApp Impl)
                (CGlobal target universes)
                [proofVariable depth index | index <- indices]
        where
          instantiate (UniverseConstraint lower upper) =
            UniverseConstraint
              (normalizeLevel (substituteLevelParams universes lower))
              (normalizeLevel (substituteLevelParams universes upper))
      _ -> Nothing

    callerIndex constraint =
      List.findIndex (equivalentUniverseConstraint constraint) callerConstraints

generatedConstraintBinderNames :: Term -> [Text]
generatedConstraintBinderNames = map fst . generatedConstraintBinders

generatedConstraintBinders :: Term -> [(Text, UniverseConstraint)]
generatedConstraintBinders = go
  where
    go (CPiEvidenceM Ordinary FormationOrdinary Impl Q0 _ name (Just (lower, upper)) _ _ codomain)
      | schemaLevel lower
      , schemaLevel upper =
          (name, UniverseConstraint (normalizeLevel lower) (normalizeLevel upper)) : go codomain
    go _ = []

    schemaLevel level =
      null (levelMetas level)
        && null (levelVars level)
        && null (levelFields level)
        && all (>= 0) (levelParams level)

ensureGeneratedConstraintLambdas :: [Text] -> Term -> Term
ensureGeneratedConstraintLambdas names body
  | missingCount >= 0
  , existing == drop missingCount names =
      foldr (CLamM Ordinary Impl Q0) body (take missingCount names)
  | otherwise = go names body
  where
    existing = take (length names) (implicitErasedLambdaPrefix body)
    missingCount = length names - length existing

    -- The finalized Pi telescope supplies the exact generated binder identities.
    -- A source binder with a reserved-looking name has no semantic authority;
    -- only an exact suffix of that authenticated sequence can be an already
    -- materialized proof-lambda prefix.
    implicitErasedLambdaPrefix = \case
      CLamM Ordinary Impl Q0 name inner ->
        name : implicitErasedLambdaPrefix inner
      _ -> []

    go [] term = term
    go remaining@(name : rest) term = case term of
      CLamM _ Impl Q0 actual inner | actual == name ->
        CLamM Ordinary Impl Q0 actual (go rest inner)
      _ -> foldr (CLamM Ordinary Impl Q0) term remaining

-- | Make one declaration's pending generated proof telescope physical without
-- publishing that interface change.  The public wrapper above is the ordinary
-- entry point.  The publication transaction uses this raw operation for the
-- callers in its next worklist wave, then publishes that complete wave exactly
-- once after repairing artifacts for the current one.
materializePendingUniverseProofsRaw :: GName -> CheckM ()
materializePendingUniverseProofsRaw g = do
  st <- get
  case (Map.lookup g (csPendingUniverseProofs st), Map.lookup g (csGlobals st)) of
    (Just pending@(_ : _), Just definition) -> do
      let parameterCount = dutParameterCount (gdUniverses definition)
          coreType = globalCoreType (ecOf st) definition
          body = gdCoreBody definition <|> Map.lookup g (csCoreBodies st)
          generated = generatedConstraintsNotIn parameterCount pending coreType
          generatedByTarget =
            Map.mapMaybeWithKey
              (\target requested -> do
                 targetDefinition <- Map.lookup target (csGlobals st)
                 let targetType = globalCoreType (ecOf st) targetDefinition
                     targetParameterCount = dutParameterCount (gdUniverses targetDefinition)
                     targetGenerated =
                       generatedConstraintsNotIn targetParameterCount requested targetType
                 if null targetGenerated then Nothing else Just targetGenerated)
              (csPendingUniverseProofs st)
          pendingForOwner =
            Map.map pleConstraint
              (Map.filter ((== g) . pleOwner) (csPendingLevelEvidence st))
          generalizedEvidence =
            Map.keysSet $
              Map.filter
                (\constraint -> any (equivalentUniverseConstraint constraint) generated)
                pendingForOwner
          (repairedType, resolvedTypeEvidence) =
            rewriteGeneratedConstraintEvidence
              generatedByTarget
              generated
              pendingForOwner
              coreType
          (coreType', body', rewrittenEvidence) =
            case body of
              Just coreBody ->
                let (repairedBody, resolvedBodyEvidence) =
                      rewriteGeneratedConstraintEvidence
                        generatedByTarget
                        generated
                        pendingForOwner
                        coreBody
                    (ty, wrapped) =
                      prependGeneratedConstraintBinders parameterCount pending repairedType repairedBody
                 in (ty, Just wrapped, Set.union resolvedTypeEvidence resolvedBodyEvidence)
              Nothing ->
                let (ty, _) = prependGeneratedConstraintBinders parameterCount pending repairedType (CRecordV [])
                 in (ty, Nothing, resolvedTypeEvidence)
          ownerMetadataTerms =
            concat
              [ concat
                  [ iePremises entry ++ ieHead entry
                  | entry <- csInstances st
                  , ieDict entry == g
                  ]
              , concat
                  [ map teDomain (piFvTele entry) ++ piPremTms entry ++ piArgTms entry
                  | Just entry <- Map.elems (csPreInstances st)
                  , piDictG entry == g
                  ]
              ]
          survivingMetadataEvidence =
            Set.intersection generalizedEvidence
              (Set.fromList (concatMap metaIdsOf ownerMetadataTerms))
          resolvedEvidence =
            Set.union rewrittenEvidence
              (Set.difference generalizedEvidence survivingMetadataEvidence)
          definition' =
            definition
              { gdType = eval (ecOf st) [] coreType'
              , gdCoreType = Just coreType'
              , gdValue = eval (ecOf st) [] <$> body'
              , gdCoreBody = body'
              }
          globalsWithTarget = Map.insert g definition' (csGlobals st)
          -- A nominal family's generated proof telescope is shared by every
          -- constructor facet. Extend the constructor telescope in the same
          -- raw transaction as the family global. Retained family call spines
          -- are deliberately left to the publication repair below: editing
          -- them here as well would supply this same authenticated delta twice.
          extendFamilyConstructor info
            | ciData info /= g = info
            | otherwise =
                let constructorParameterCount =
                      dutParameterCount (ciUniverses info)
                    constructorGenerated =
                      generatedConstraintsNotIn
                        constructorParameterCount generated (ciType info)
                    (typeWithProofTelescope, _) =
                      prependGeneratedConstraintBinders
                        constructorParameterCount
                        constructorGenerated
                        (ciType info)
                        (CRecordV [])
                 in info {ciType = typeWithProofTelescope}
          constructorsWithTarget = Map.map extendFamilyConstructor (csCtors st)
          dirtyNominalSummaries
            | null generated = csDirtyNominalSummaries st
            | Map.member g (csNominalSummaryRequests st) =
                Set.insert g (csDirtyNominalSummaries st)
            | otherwise = csDirtyNominalSummaries st
          coreBodiesWithTarget =
            maybe (csCoreBodies st) (\term -> Map.insert g term (csCoreBodies st)) body'
      put
        st
          { csGlobals = globalsWithTarget
          , csCtors = constructorsWithTarget
          , csDirtyNominalSummaries = dirtyNominalSummaries
          , csCoreBodies = coreBodiesWithTarget
          , csPendingUniverseProofs = Map.delete g (csPendingUniverseProofs st)
          , csPending =
              filter (\(meta, _, _, _, _) -> meta `Set.notMember` resolvedEvidence) (csPending st)
          , csPendingLevelEvidence =
              Map.withoutKeys (csPendingLevelEvidence st) resolvedEvidence
          }
    _ -> pure ()

levelConstraintKey
  :: Maybe GName
  -> Maybe Span
  -> LevelConstraint
  -> LevelConstraintKey
levelConstraintKey owner sourceSpan constraint =
  LevelConstraintKey
    owner
    sourceSpan
    (lcLhs constraint)
    (lcRhs constraint)
    (lcOrigin constraint)
    (assumptionsList (lcAssumptions constraint))

reindexLevelConstraints :: CheckState -> CheckState
reindexLevelConstraints st =
  let constraints = csLevelConstraints st
      retainedIds = Set.fromList (map lcIdentity constraints)
      constraintIndex =
        Map.fromList
          [ ( levelConstraintKey
                (Map.lookup (lcIdentity constraint) (csLevelConstraintOwners st))
                (Map.lookup (lcIdentity constraint) (csLevelConstraintSpans st))
                constraint
            , lcIdentity constraint
            )
          | constraint <- constraints
          ]
      -- Prepend in constant time, then restore the authoritative constraint
      -- order once per owner. Appending each singleton made this rebuild
      -- quadratic for declarations with many universe constraints.
      constraintsByOwner =
        Map.map reverse $
          List.foldl'
            (\byOwner constraint ->
               case Map.lookup (lcIdentity constraint) (csLevelConstraintOwners st) of
                 Nothing -> byOwner
                 Just owner -> Map.insertWith (++) owner [constraint] byOwner)
            Map.empty
            constraints
   in st
    { csLevelConstraintIndex = constraintIndex
    , csLevelConstraintsByOwner = constraintsByOwner
    , csLevelConstraintOwners =
        Map.restrictKeys (csLevelConstraintOwners st) retainedIds
    , csLevelConstraintSpans =
        Map.restrictKeys (csLevelConstraintSpans st) retainedIds
    , csLevelConstraintProvenance =
        Map.restrictKeys (csLevelConstraintProvenance st) retainedIds
    }

constraintOwnedAfterRetiringOccurrences
  :: CheckState
  -> Set Int
  -> LevelConstraint
  -> Bool
constraintOwnedAfterRetiringOccurrences st retired constraint =
  case Map.lookup (lcIdentity constraint) (csLevelConstraintProvenance st) of
    Nothing -> True
    Just provenance ->
      lcpOrdinary provenance
        || not
             ( Set.null
                 ( Set.difference
                     (lcpProvisionalOccurrences provenance)
                     retired
                 )
             )

deleteProvisionalUniverseInstantiations
  :: Set Int
  -> CheckState
  -> CheckState
deleteProvisionalUniverseInstantiations retired state
  | Set.null retired = state
  | otherwise =
      let retiredMetas =
            Set.fromList
              [ meta
              | identity <- Set.toList retired
              , Just occurrence <-
                  [Map.lookup identity (csProvisionalUniverseInstantiations state)]
              , level <- puiFreshLevels occurrence
              , meta <- levelMetas level
              ]
          deleteIndex identity owner =
            Map.update
              (\identities ->
                 let retained = Set.delete identity identities
                  in if Set.null retained then Nothing else Just retained)
              owner
          removeIdentity (byOwner, byConsumer) identity =
            case Map.lookup identity (csProvisionalUniverseInstantiations state) of
              Nothing -> (byOwner, byConsumer)
              Just occurrence ->
                ( deleteIndex identity (puiOwner occurrence) byOwner
                , maybe
                    byConsumer
                    (\consumer -> deleteIndex identity consumer byConsumer)
                    (puiConsumer occurrence)
                )
          (owners', consumers') =
            Set.foldl'
              removeIdentity
              ( csProvisionalUniverseInstantiationsByOwner state
              , csProvisionalUniverseInstantiationsByConsumer state
              )
              retired
          trimMetasByOwner =
            Map.mapMaybe
              (\metas ->
                 let retainedMetas = Set.difference metas retiredMetas
                  in if Set.null retainedMetas then Nothing else Just retainedMetas)
       in state
            { csProvisionalUniverseInstantiations =
                Map.withoutKeys
                  (csProvisionalUniverseInstantiations state)
                  retired
            , csProvisionalUniverseInstantiationsByOwner = owners'
            , csProvisionalUniverseInstantiationsByConsumer = consumers'
            , csLevelInstantiationMetas =
                Set.difference (csLevelInstantiationMetas state) retiredMetas
            , csLevelInstantiationOwners =
                Map.withoutKeys (csLevelInstantiationOwners state) retiredMetas
            , csLevelInstantiationMetasByOwner =
                trimMetasByOwner (csLevelInstantiationMetasByOwner state)
            }

levelConstraintsOwnedBy :: CheckState -> Set GName -> [LevelConstraint]
levelConstraintsOwnedBy st owners =
  concatMap
    (\owner -> Map.findWithDefault [] owner (csLevelConstraintsByOwner st))
    (Set.toAscList owners)

levelMetasOwnedBy
  :: Map GName (Set LevelMeta)
  -> Set GName
  -> Set LevelMeta
levelMetasOwnedBy byOwner owners =
  Set.unions
    [ Map.findWithDefault Set.empty owner byOwner
    | owner <- Set.toList owners
    ]

insertProvisionalLevelConstraintOwned
  :: Int
  -> Maybe GName
  -> Assumptions
  -> ConstraintOrigin
  -> Level
  -> Level
  -> CheckM Int
insertProvisionalLevelConstraintOwned occurrence =
  insertLevelConstraintOwnedWithProvenance (Just occurrence)

insertLevelConstraintOwnedWithProvenance
  :: Maybe Int
  -> Maybe GName
  -> Assumptions
  -> ConstraintOrigin
  -> Level
  -> Level
  -> CheckM Int
insertLevelConstraintOwnedWithProvenance provisionalOccurrence owner assumptions origin lhs rhs = do
  st <- get
  let sourceSpan = csUniverseDiagnosticSpan st
      identity = csNextLevelConstraint st
      constraint =
        LevelConstraint
          { lcIdentity = identity
          , lcLhs = lhs
          , lcRhs = rhs
          , lcOrigin = origin
          , lcAssumptions = assumptions
          }
      key = levelConstraintKey owner sourceSpan constraint
      addProvenance =
        Map.alter
          ( Just
              . maybe
                  ( LevelConstraintProvenance
                      (isNothing provisionalOccurrence)
                      (maybe Set.empty Set.singleton provisionalOccurrence)
                  )
                  (\provenance ->
                     provenance
                       { lcpOrdinary =
                           lcpOrdinary provenance
                             || isNothing provisionalOccurrence
                       , lcpProvisionalOccurrences =
                           maybe
                             (lcpProvisionalOccurrences provenance)
                             (`Set.insert` lcpProvisionalOccurrences provenance)
                             provisionalOccurrence
                       })
          )
  case Map.lookup key (csLevelConstraintIndex st) of
    Just existing -> do
      modify' $ \current ->
        current
          { csLevelConstraintProvenance =
              addProvenance existing (csLevelConstraintProvenance current)
          }
      pure existing
    Nothing -> do
      put
        st
          { csLevelConstraints = constraint : csLevelConstraints st
          , csLevelConstraintOwners =
              maybe
                (csLevelConstraintOwners st)
                (\definition -> Map.insert identity definition (csLevelConstraintOwners st))
                owner
          , csLevelConstraintsByOwner =
              maybe
                (csLevelConstraintsByOwner st)
                (\definition ->
                   Map.insertWith
                     (++)
                     definition
                     [constraint]
                     (csLevelConstraintsByOwner st))
                owner
          , csLevelConstraintSpans =
              maybe
                (csLevelConstraintSpans st)
                (\source -> Map.insert identity source (csLevelConstraintSpans st))
                sourceSpan
          , csLevelConstraintIndex =
              Map.insert key identity (csLevelConstraintIndex st)
          , csLevelConstraintProvenance =
              addProvenance identity (csLevelConstraintProvenance st)
          , csNextLevelConstraint = identity + 1
          }
      pure identity

-- | Fresh levels of still-unmaterialized provisional declaration occurrences.
-- Their callee SCC has not yet published the constraints that relate source
-- and result positions, so selecting a principal value from the incomplete
-- graph can only be premature. Callers defer these metas until
-- 'materializeProvisionalUniverseConstraints' installs the complete callee
-- interface; finalized and imported declarations are never included.
unmaterializedProvisionalUniverseMetas
  :: CheckState
  -> Set Int
  -> Set LevelMeta
unmaterializedProvisionalUniverseMetas state occurrenceIds =
  Set.fromList
    [ meta
    | identity <- Set.toList occurrenceIds
    , Just occurrence <-
        [Map.lookup identity (csProvisionalUniverseInstantiations state)]
    , not (puiConstraintsMaterialized occurrence)
    , let GName occurrenceModule _ = puiOwner occurrence
    , occurrenceModule == csModule state
    , puiOwner occurrence `Set.notMember` csFinalizedUniverseInterfaces state
    , level <- puiFreshLevels occurrence
    , meta <-
        levelMetas
          ( normalizeLevel
              (substituteLevelMetas (csLevelAssignments state) level)
          )
    ]

-- | Resolve unsolved universe metas for one finalized owner without rewriting
-- its published rigid parameters. 'csFinalizedGlobalUniverseMetaMaps' is the
-- authenticated bridge from retained source identities to the declaration
-- telescope. Apply that bridge before the residual assignment graph: a source
-- meta selected for the final telescope denotes its 'LParam' even if an older
-- principalization attempt also recorded a concrete assignment. A genuinely
-- narrowed schema is rebuilt with a new (possibly empty) owner map, so it does
-- not need to reinterpret a still-published parameter after the fact.
resolveFinalizedOwnerLevel :: CheckState -> GName -> Level -> Level
resolveFinalizedOwnerLevel state owner =
  substituteLevelMetas assignments
    . substituteLevelMetas ownerMetas
  where
    assignments = csLevelAssignments state
    ownerMetas =
      Map.findWithDefault
        Map.empty
        owner
        (csFinalizedGlobalUniverseMetaMaps state)

provisionalUniverseProjections
  :: CheckState
  -> GName
  -> Map (GName, Int) UniverseReferenceProjection
provisionalUniverseProjections st global = fromMaybe Map.empty $ do
  definition <- Map.lookup global (csGlobals st)
  guard (not (dutExplicit (gdUniverses definition)))
  let assignments =
        Map.union
          (Map.findWithDefault Map.empty global (csFinalizedGlobalUniverseMetaMaps st))
          (csLevelAssignments st)
      originalTerms = globalUniverseInterfaceTerms st global definition
      fallbackSource = nub (concatMap levelMetasOfTerm originalTerms)
      sourceSpines =
        Map.findWithDefault [fallbackSource] global
          (csProvisionalGlobalUniverseMetas st)
      normalizedTerms = map (zonkLevels assignments) originalTerms
      retainedSet =
        durGeneralizable (mconcat (map declarationUniverseRoles normalizedTerms))
      retainedMetas =
        filter (`Set.member` retainedSet)
          (concatMap levelMetasOfTerm normalizedTerms)
      retainedLevels =
        if dutParameterCount (gdUniverses definition) > 0
          then map LParam [0 .. dutParameterCount (gdUniverses definition) - 1]
          else map LMeta retainedMetas
  pure $
    uniqueUniverseReferenceProjections
      [ ( (global, length sourceMetas)
        , deriveUniverseReferenceProjectionToLevels assignments sourceMetas retainedLevels
        )
      | sourceMetas <- sourceSpines
      ]

zonkLevels :: Map LevelMeta Level -> Term -> Term
zonkLevels assignments =
  zonkTermWith
    (\_ _ -> Nothing)
    (substituteLevelMetas assignments)
    0

reportLevelSolveError :: LevelSolveError -> CheckM ()
reportLevelSolveError solveError = do
  let constraint = levelSolveErrorConstraint solveError
  owner <- gets (Map.lookup (lcIdentity constraint) . csLevelConstraintOwners)
  sourceSpan <- gets (Map.lookup (lcIdentity constraint) . csLevelConstraintSpans)
  reportLevelSolveErrorWithProvenance owner sourceSpan solveError

levelSolveErrorConstraint :: LevelSolveError -> LevelConstraint
levelSolveErrorConstraint = \case
  LevelConstraintDisproved constraint -> constraint
  LevelContradictoryAssumptions constraint -> constraint
  LevelMetaOccurs _ _ constraint -> constraint
  LevelResourceLimit constraint _ -> constraint

-- | Render one solver failure with explicit source provenance. Deferred
-- constraints obtain this data from the checker side tables above; immediate
-- rigid conversion failures use the same constructor directly and therefore
-- do not poison the persistent inference graph with a known-unsatisfiable
-- edge merely to attach a span.
reportLevelSolveErrorWithProvenance
  :: Maybe GName
  -> Maybe Span
  -> LevelSolveError
  -> CheckM ()
reportLevelSolveErrorWithProvenance owner sourceSpan solveError = do
  let (code, constraint, detail) = case solveError of
        LevelConstraintDisproved c
          | constraintIsSelfContaining c ->
              ("E_UNIVERSE_SELF_CONTAINMENT", c, "the universe inequality requires strict self-containment")
          | otherwise ->
              ("E_UNIVERSE_CONSTRAINT_UNSATISFIABLE", c, "the universe inequality is inconsistent")
        LevelContradictoryAssumptions c ->
          ( "E_UNIVERSE_CONSTRAINT_UNSATISFIABLE"
          , c
          , "the scoped universe assumptions are contradictory"
          )
        LevelMetaOccurs meta lower c ->
          ( "E_UNIVERSE_SELF_CONTAINMENT"
          , c
          , "universe metavariable ?u" <> T.pack (show meta)
              <> " occurs recursively in " <> renderLevel lower
          )
        LevelResourceLimit c limit ->
          ( "E_UNIVERSE_INFERENCE_REQUIRES_ANNOTATION"
          , c
          , "the exact universe solver exceeded its "
              <> T.pack (show limit)
              <> "-node materialization budget; add an explicit universe schema or simplify the level relation"
          )
      normalized = renderLevel (lcLhs constraint) <> " <= " <> renderLevel (lcRhs constraint)
      ConstraintOrigin description construct = lcOrigin constraint
  let primary = fromMaybe (Span "<universe-inference>" (Pos 1 1) (Pos 1 1)) sourceSpan
      withOwner = case owner of
        Just declaration -> withPayloadField "declaration" (gKey declaration)
        Nothing -> id
      ownerKey = fmap gKey owner
      diagnostic =
        withPayload
          ( withPayloadField "normalizedFailedConstraint" normalized
              $ withPayloadField "levelAssumptions" (renderLevelAssumptions (lcAssumptions constraint))
              $ withPayloadField "constraintOrigin" description
              $ withPayloadField "construct" construct
              $ withOwner
              $ payloadKind "universe-constraint"
          )
          $ diag SevError StageElaborate code (Just "kappa.universe.constraint")
            primary
            (detail <> ": " <> normalized <> " (§11.1.3)")
      sameFailure existing =
        dCode existing == code
          && lookup "normalizedFailedConstraint" (pFields (dPayload existing)) == Just normalized
          && lookup "declaration" (pFields (dPayload existing)) == ownerKey
          && dPrimary existing == primary
  alreadyReported <- gets (any sameFailure . csDiags)
  unless alreadyReported (report diagnostic)
  where
    -- A failed @lhs <= rhs@ closes a strict cycle exactly when @lhs@ is
    -- equivalent to @succ rhs@ under the active assumptions. A merely closed
    -- contradiction such as @1 <= 0@ is unsatisfiable, but is not itself a
    -- self-containment cycle.
    constraintIsSelfContaining constraint =
      let assumptions = lcAssumptions constraint
          successor = levelSucc (lcRhs constraint)
       in proveLevelLeq assumptions successor (lcLhs constraint) == Proved
            && proveLevelLeq assumptions (lcLhs constraint) successor == Proved

-- | Emit the complete §3.1.4/§11.1.2.4A no-principal-solution record.  Every
-- inference boundary uses this constructor so local declarations, bodies, and
-- top-level SCCs expose the same machine-readable evidence rather than a
-- message-only approximation.
reportNoPrincipalUniverseDiagnostic
  :: Span
  -> [Text]
  -> Bool
  -> Set LevelMeta
  -> [LevelConstraint]
  -> Maybe PrincipalNonLeastWitness
  -> Text
  -> CheckM ()
reportNoPrincipalUniverseDiagnostic diagnosticSpan declarations explicitSchema metas constraints witness message =
  report $
    withPayload
      ( withPayloadField "declarationIdentity" declarationIdentity
          $ withPayloadField "declarationSccIdentity" sccIdentity
          $ withPayloadField "unresolvedUniverseMetavariables" renderedMetas
          $ withPayloadField "normalizedBounds" renderedBounds
          $ withPayloadField "candidateIncomparableMinimalSolutions" candidateMinima
          $ withPayloadField "sourceOrigins" renderedOrigins
          $ withPayloadField "explicitUniverseSchema" (if explicitSchema then "true" else "false")
          $ withPayloadField "suggestedRepair" suggestedRepair
          $ payloadKind "universe-no-principal-solution"
      )
      $ diag SevError StageElaborate "E_UNIVERSE_NO_PRINCIPAL_SOLUTION"
        (Just "kappa.universe.no-principal-solution") diagnosticSpan message
  where
    normalizedDeclarations = sort (nub declarations)
    declarationIdentity = case normalizedDeclarations of
      [] -> "<local-declaration>"
      [declaration] -> declaration
      many -> T.intercalate ", " many
    -- The ordered member identities are the canonical identity of a semantic
    -- SCC. Source spelling order and allocation counters do not participate.
    sccIdentity = T.intercalate "|" normalizedDeclarations
    renderedMetas =
      T.intercalate ", " ["?u" <> T.pack (show meta) | meta <- Set.toAscList metas]
    mentions meta level = meta `elem` levelMetas level
    boundsFor meta =
      [ renderLevel (normalizeLevel lower)
          <> " <= " <> renderLevel (normalizeLevel upper)
      | constraint <- constraints
      , (lower, upper) <-
          (lcLhs constraint, lcRhs constraint) : assumptionsList (lcAssumptions constraint)
      , mentions meta lower || mentions meta upper
      ]
    renderedBounds =
      T.intercalate "; "
        [ "?u" <> T.pack (show meta) <> ": ["
            <> T.intercalate ", " (nub (boundsFor meta)) <> "]"
        | meta <- Set.toAscList metas
        ]
    renderedOrigins =
      T.intercalate "; " . nub $
        [ coDescription origin <> " (" <> coConstruct origin <> ")"
        | constraint <- constraints
        , let origin = lcOrigin constraint
        , any
            (\meta -> any (\(lower, upper) -> mentions meta lower || mentions meta upper)
              ((lcLhs constraint, lcRhs constraint) : assumptionsList (lcAssumptions constraint)))
            (Set.toList metas)
        ]
    candidateMinima = case witness of
      Just checked ->
        "left=" <> renderAssignment (pnlwLeft checked)
          <> "; right=" <> renderAssignment (pnlwRight checked)
      Nothing -> "not-applicable"
    renderAssignment assignment =
      "{" <> T.intercalate ", "
        [ "?u" <> T.pack (show meta) <> "=" <> renderLevel level
        | (meta, level) <- Map.toAscList assignment
        ] <> "}"
    suggestedRepair =
      "add the unresolved levels to an explicit .{u...} declaration schema or constrain the result universe so the least solution is unique"

-- | Report the distinct §11.1.3 outcome in which a semantic principal value
-- may exist but is not derivable by the versioned portable assignment rules.
-- This is deliberately not the no-principal family: tools and users need to
-- know that an annotation can make the same program portable without claiming
-- a mathematical non-principality result.
reportUniverseInferenceRequiresAnnotation
  :: Span
  -> [Text]
  -> Bool
  -> Set LevelMeta
  -> [LevelConstraint]
  -> Text
  -> CheckM ()
reportUniverseInferenceRequiresAnnotation diagnosticSpan declarations explicitSchema metas constraints semanticStatus =
  forM_ (Set.toAscList metas) $ \meta -> do
    let normalizedDeclarations = sort (nub declarations)
        declarationIdentity = case normalizedDeclarations of
          [] -> "<local-declaration>"
          [declaration] -> declaration
          many -> T.intercalate ", " many
        sccIdentity = T.intercalate "|" normalizedDeclarations
        mentions level = meta `elem` levelMetas level
        relevant =
          [ constraint
          | constraint <- constraints
          , mentions (lcLhs constraint) || mentions (lcRhs constraint)
          ]
        renderedConstraints =
          T.intercalate "; "
            [ renderLevel (normalizeLevel (lcLhs constraint))
                <> " <= "
                <> renderLevel (normalizeLevel (lcRhs constraint))
            | constraint <- relevant
            ]
        renderedAssumptions =
          T.intercalate "; " . nub $
            [ renderLevelAssumptions (lcAssumptions constraint)
            | constraint <- relevant
            , not (null (assumptionsList (lcAssumptions constraint)))
            ]
        repair =
          if explicitSchema
            then "add an explicit result-universe annotation that determines this schema occurrence"
            else "add an explicit .{u...} declaration schema or result-universe annotation for this occurrence"
    report $
      withPayload
        ( withPayloadField "declarationIdentity" declarationIdentity
            $ withPayloadField "declarationSccIdentity" sccIdentity
            $ withPayloadField "selectedMetavariableIdentity" ("?u" <> T.pack (show meta))
            $ withPayloadField "normalizedConstraints" renderedConstraints
            $ withPayloadField "rigidAssumptions" renderedAssumptions
            $ withPayloadField "portableAssignmentRulesAttempted"
                "direct lower-bound join; natural-add/successor cancellation; closed residuation; selected max contexts; substitution and rigid recheck"
            $ withPayloadField "semanticLeastSolutionStatus" semanticStatus
            $ withPayloadField "smallestKnownRepair" repair
            $ payloadKind "universe-inference-requires-annotation"
        )
        $ diag SevError StageElaborate "E_UNIVERSE_INFERENCE_REQUIRES_ANNOTATION"
          (Just "kappa.universe.inference-requires-annotation") diagnosticSpan
          "portable universe inference cannot determine this minimizable level; add an explicit annotation (§11.1.3)"

classifyPrincipalAtDeclarationBoundary
  :: Set LevelMeta
  -> [LevelConstraint]
  -> (UniverseInferenceClass, PrincipalBoundaryResult)
classifyPrincipalAtDeclarationBoundary targets constraints =
  case solveLevelConstraintsFor targets constraints of
    Left solveError ->
      ( case solveError of
          LevelResourceLimit {} -> InferenceOutsidePortableInferenceFragment
          _ -> InferenceUnsatisfiable
      , PrincipalBoundaryRejected (PrincipalBoundarySolveFailure solveError)
      )
    Right _ ->
      case inferPrincipalLevelsFor targets constraints of
        SolvedPrincipal assignments ->
          (InferenceSolvedPrincipal, PrincipalBoundarySolved assignments)
        Unsatisfiable ->
          (InferenceUnsatisfiable, PrincipalBoundaryRejected PrincipalBoundaryClassifierUnsatisfiable)
        NoPointwiseLeastSolution witness ->
          ( InferenceNoPointwiseLeastSolution
          , PrincipalBoundaryRejected (PrincipalBoundaryNoPointwiseLeast witness)
          )
        OutsidePortableInferenceFragment ->
          ( InferenceOutsidePortableInferenceFragment
          , PrincipalBoundaryRejected PrincipalBoundaryOutsidePortableFragment
          )
        BlockedByUnselectedMetas ->
          (InferenceBlockedByUnselectedMetas, PrincipalBoundaryDeferred)

inferPrincipalAtDeclarationBoundary
  :: Span
  -> [Text]
  -> Bool
  -> Set LevelMeta
  -> [LevelConstraint]
  -> CheckM PrincipalBoundaryResult
inferPrincipalAtDeclarationBoundary _diagnosticSpan declarations _explicitSchema targets constraints = do
  let (inferenceClass, result) =
        classifyPrincipalAtDeclarationBoundary targets constraints
      assignments = case result of
        PrincipalBoundarySolved solved -> solved
        _ -> Map.empty
  -- Classification is deliberately diagnostic-free. Intermediate body and
  -- publication passes may revisit the same still-open component; only the
  -- complete semantic boundary commits a failure diagnostic.
  recordOutcome inferenceClass assignments
  pure result
  where
    recordOutcome inferenceClass assignments =
      modify' $ \state ->
        state
          { csUniverseInferenceRecords =
              foldr
                (\declaration ->
                  Map.insert declaration (UniverseInferenceRecord inferenceClass assignments))
                (csUniverseInferenceRecords state)
                declarations
          }

reportPrincipalBoundaryFailure
  :: Span
  -> [Text]
  -> Bool
  -> Set LevelMeta
  -> [LevelConstraint]
  -> PrincipalBoundaryFailure
  -> CheckM ()
reportPrincipalBoundaryFailure diagnosticSpan declarations explicitSchema targets constraints = \case
  PrincipalBoundarySolveFailure LevelResourceLimit {} ->
    reportUniverseInferenceRequiresAnnotation diagnosticSpan declarations explicitSchema targets constraints
      "unknown: the exact solver crossed its resource boundary before a principal solution could be established"
  PrincipalBoundarySolveFailure solveError ->
    reportLevelSolveError solveError
  PrincipalBoundaryClassifierUnsatisfiable ->
    report $
      diag SevError StageElaborate "E_UNIVERSE_CONSTRAINT_UNSATISFIABLE"
        (Just "kappa.universe.constraint") diagnosticSpan
        "the selected universe constraint system is unsatisfiable (§11.1.3)"
  PrincipalBoundaryNoPointwiseLeast witness ->
    reportNoPrincipalUniverseDiagnostic diagnosticSpan declarations explicitSchema targets constraints (Just witness)
      "declaration universe constraints have valid solutions but no pointwise least solution (§11.1.3)"
  PrincipalBoundaryOutsidePortableFragment ->
    reportUniverseInferenceRequiresAnnotation diagnosticSpan declarations explicitSchema targets constraints
      "unknown: a semantic least solution may exist, but the constraint is outside the portable inference fragment"

installLevelAssignments :: HasCallStack => Map LevelMeta Level -> CheckM ()
installLevelAssignments new = do
  old <- gets csLevelAssignments
  oldDependents <- gets csLevelAssignmentDependents
  oldBudget <- gets csLevelAssignmentBudget
  case extendLevelAssignmentGraphWithBudget old oldDependents oldBudget new of
    Left (LevelAssignmentGraphConflict meta installed requested) ->
      report $
        withPayload
          ( withPayloadField "metavariable" ("?u" <> T.pack (show meta)) $
              withPayloadField "installedAssignment" (renderLevel installed) $
                withPayloadField "requestedAssignment" (renderLevel requested) $
                  payloadKind "universe-assignment-conflict"
          ) $
          diag SevError StageElaborate "E_UNIVERSE_CONSTRAINT_UNSATISFIABLE"
            (Just "kappa.universe.constraint")
            (Span "<universe-inference>" (Pos 1 1) (Pos 1 1))
            ( "a principal universe assignment was revised after installation: ?u"
                <> T.pack (show meta)
                <> " was " <> renderLevel installed
                <> ", requested " <> renderLevel requested
            )
    Left (LevelAssignmentGraphResourceLimit budget) ->
      report $
        withPayload
          ( withPayloadField "nodeBudget" (T.pack (show budget)) $
              payloadKind "universe-resource-limit"
          ) $
          diag SevError StageElaborate "E_UNIVERSE_INFERENCE_REQUIRES_ANNOTATION"
            (Just "kappa.universe.inference-requires-annotation")
            (Span "<universe-inference>" (Pos 1 1) (Pos 1 1))
            "incremental universe assignments exceed the portable solver resource boundary"
    Right (combined, dependents, budget, affected) -> do
      modify' $ \st ->
        st
          { csLevelAssignments = combined
          , csLevelAssignmentDependents = dependents
          , csLevelAssignmentBudget = budget
          }
      -- A new solution can make an older symbolic assignment concrete.
      -- Follow the reverse dependency closure and compare effective values;
      -- unrelated assignments have already been reflected into 'csMetas'.
      forM_ (Set.toAscList affected) $ \meta -> do
        let before = substituteLevelMetas old (LMeta meta)
            after = substituteLevelMetas combined (LMeta meta)
        when (before /= after) $
          forM_ (levelValueMaybe after) (solveMeta meta)

-- Hidden declaration-universe parameters are compiler-only telescope entries,
-- not term binders. Only levels with an actual term representation may be
-- reflected into the ordinary elaboration metavariable store.
levelValueMaybe :: Level -> Maybe Value
levelValueMaybe = \case
  LZero -> Just (VPrim "__typeLevelZero" [])
  LFinite n -> Just (VPrim "__typeLevelFinite" [VLit (LitInt n)])
  LOmega -> Just (VPrim "__typeLevelOmega" [])
  LSucc a -> VPrim "__typeLevelSucc" . pure <$> levelValueMaybe a
  LAdd a b -> do
    a' <- levelValueMaybe a
    b' <- levelValueMaybe b
    pure (VPrim "__typeLevelAdd" [a', b'])
  LMax a b -> do
    a' <- levelValueMaybe a
    b' <- levelValueMaybe b
    pure (VPrim "__typeLevelMax" [a', b'])
  LVar v -> Just (VRigid v [])
  LField _ field -> Just (VProjN Ordinary (VGlobN thisG []) field)
  LProjection root path ->
    Just (foldl (\receiver field -> VProjN Ordinary receiver field) (VRigid root []) path)
  LNeutral _ -> Nothing
  LParam _ -> Nothing
  LMeta _ -> Nothing

levelOperatorValue :: LevelOperatorIdentity -> Value
levelOperatorValue = \case
  LevelOperatorZero -> VPrim "__typeLevelZero" []
  LevelOperatorOne -> VPrim "__typeLevelFinite" [VLit (LitInt 1)]
  LevelOperatorSucc -> VPrim "__typeLevelSucc" []
  LevelOperatorAdd -> VPrim "__typeLevelAdd" []
  LevelOperatorMax -> VPrim "__typeLevelMax" []
  LevelOperatorFromInteger -> VPrim "__typeLevelFromNat" []
  LevelOperatorLt -> VGlobN (gPrel "<") []
  LevelOperatorLe -> VGlobN (gPrel "<=") []

metaOccursInValue :: Map MetaId (Maybe Value) -> MetaId -> Value -> Bool
metaOccursInValue metas = metaOccursInValueSeen metas metaOccursFuel Set.empty

metaOccursFuel :: Int
metaOccursFuel = 4096

metaOccursInValueSeen :: Map MetaId (Maybe Value) -> Int -> Set MetaId -> MetaId -> Value -> Bool
metaOccursInValueSeen metas fuel0 seen0 target = goV fuel0 seen0
  where
    next n = n - 1

    exhausted n = n <= 0

    -- Direct meta solving is a shortcut.  If the finite occurs-check budget is
    -- exhausted, fail closed by reporting "may occur"; callers then use the
    -- ordinary unifier instead of installing a possibly cyclic solution.  This
    -- keeps the occurs check from recursively chasing large closure graphs or
    -- recursive standard-library values while preserving soundness.
    goSp n seen
      | exhausted n = const True
      | otherwise = any (goV (next n) seen . snd)

    goClosure boundCount n seen (Closure env body)
      | exhausted n = True
      | otherwise =
          metaOccursInTerm metas (next n) seen target body
            || goReachableEnvironment n seen env [(boundCount, body)]

    -- A semantic closure captures the complete evaluator environment, not
    -- merely the values its body references.  An occurs check must follow
    -- only reachable de Bruijn slots: scanning every captured value rejects
    -- acyclic solutions whenever an unrelated environment cell happens to
    -- contain the meta being solved.  Suspended do kernels are opaque to the
    -- depth-aware fold, so retain the conservative all-environment answer for
    -- those bodies rather than risking a missed cycle.
    goReachableEnvironment n seen env scopedTerms
      | any (termContainsDo . snd) scopedTerms = any (goV (next n) seen) env
      | otherwise = any reachable (nub (concatMap scopedEnvironmentIndices scopedTerms))
      where
        reachable index =
          case drop index env of
            value : _ -> goV (next n) seen value
            [] -> True

    scopedEnvironmentIndices (boundCount, term) =
      foldTermWithDepth occurrence boundCount term
      where
        occurrence depth = \case
          CVar index | index >= depth -> [index - depth]
          CLocal index _ | index >= depth -> [index - depth]
          _ -> []

    termContainsDo = getAny . foldTerm termNode (const mempty)
      where
        termNode = \case
          CDo {} -> Any True
          _ -> mempty

    goV n seen v
      | exhausted n = True
      | otherwise = case v of
      VRigid _ sp -> goSp n seen sp
      VFlex m sp ->
        m == target
          || goSp n seen sp
          || ( not (Set.member m seen)
                 && case Map.lookup m metas of
                   Just (Just sol) -> goV (next n) (Set.insert m seen) sol
                   _ -> False
             )
      VGlobN _ sp -> goSp n seen sp
      VLam _ _ _ clo -> goClosure 1 n seen clo
      VPi _ _ _ _ dom clo -> goV (next n) seen dom || goClosure 1 (next n) seen clo
      VSort _ -> False
      VLevel _ -> False
      VUniverseLift _ _ _ inner -> goV (next n) seen inner
      VLit _ -> False
      VCtor _ args -> any (goV (next n) seen) args
      VRecordT fs -> any (goV (next n) seen . snd) fs
      VRecordV fs -> any (goV (next n) seen . snd) fs
      VVariantT ms -> any (goV (next n) seen) ms
      VInject _ v' -> goV (next n) seen v'
      VMatchN scrut scrutineeAnnotation resultAnnotation alts env ->
        goV (next n) seen scrut
          || maybe False (goV (next n) seen) scrutineeAnnotation
          || maybe False (goV (next n) seen) resultAnnotation
          || any (goAlt (next n) seen) alts
          || goReachableEnvironment
               (next n)
               seen
               env
               [ (patBindersC pattern', term)
               | CaseAlt pattern' guardTerm body <- alts
               , term <- maybeToList guardTerm ++ [body]
               ]
      VProjN _ v' _ -> goV (next n) seen v'
      VAppN _ f a -> goV (next n) seen f || goV (next n) seen a
      VSealV _ v' -> goV (next n) seen v'
      VSigT _ v' -> goV (next n) seen v'
      VDoV _ items env -> any (goK (next n) seen) items || any (goV (next n) seen) env
      VThunkV clo -> goClosure 0 n seen clo
      VLazyV clo -> goClosure 0 n seen clo
      VIfN c t f ->
        goV (next n) seen c
          || goClosure 0 (next n) seen t
          || goClosure 0 (next n) seen f
      VArithmeticProof certificate ->
        any (goV (next n) seen) (foldMapArithmeticCertificate (: []) certificate)
      VPrim _ args -> any (goV (next n) seen) args
      VRef _ -> False
      VArr _ _ -> False
      VMVar _ -> False
      VFiber _ _ -> False
      VScope _ -> False
      VFiberRef _ -> False
      VTVar _ -> False
      VIOAction _ args -> any (goV (next n) seen) args
      VQuote _ slots -> any (goV (next n) seen) slots

    goAlt n seen (CaseAlt _ gd body)
      | exhausted n = True
      | otherwise =
          maybe False (metaOccursInTerm metas (next n) seen target) gd
            || metaOccursInTerm metas (next n) seen target body

    goK n seen
      | exhausted n = const True
      | otherwise = \case
      KBind _ _ t _ -> metaOccursInTerm metas (next n) seen target t
      KLet _ _ t -> metaOccursInTerm metas (next n) seen target t
      KLetQ _ t m -> metaOccursInTerm metas (next n) seen target t || maybe False (metaOccursInTerm metas (next n) seen target . snd) m
      KExpr t -> metaOccursInTerm metas (next n) seen target t
      KVarItem _ initT actT _ -> metaOccursInTerm metas (next n) seen target initT || metaOccursInTerm metas (next n) seen target actT
      KAssign lhs _ rhs actT _ ->
        metaOccursInTerm metas (next n) seen target lhs
          || metaOccursInTerm metas (next n) seen target rhs
          || metaOccursInTerm metas (next n) seen target actT
      KReturn t -> metaOccursInTerm metas (next n) seen target t
      KBreak _ -> False
      KContinue _ -> False
      KWhile _ c b e ->
        metaOccursInTerm metas (next n) seen target (kCondTerm c)
          || any (goK (next n) seen) b
          || maybe False (any (goK (next n) seen)) e
      KFor _ _ src b e ->
        metaOccursInTerm metas (next n) seen target src
          || any (goK (next n) seen) b
          || maybe False (any (goK (next n) seen)) e
      KIf alts e ->
        any
          (\(c, b) ->
             metaOccursInTerm metas (next n) seen target c
               || any (goK (next n) seen) b)
          alts
          || maybe False (any (goK (next n) seen)) e
      KDefer _ t -> metaOccursInTerm metas (next n) seen target t
      KUsing _ acquire release ->
        metaOccursInTerm metas (next n) seen target acquire
          || metaOccursInTerm metas (next n) seen target release
      KSubDo _ items -> any (goK (next n) seen) items

metaOccursInTerm :: Map MetaId (Maybe Value) -> Int -> Set MetaId -> MetaId -> Term -> Bool
metaOccursInTerm metas fuel0 seen target = go fuel0
  where
    next n = n - 1
    exhausted n = n <= 0

    goK n
      | exhausted n = const True
      | otherwise = \case
      KBind _ _ t _ -> go (next n) t
      KLet _ _ t -> go (next n) t
      KLetQ _ t m -> go (next n) t || maybe False (go (next n) . snd) m
      KExpr t -> go (next n) t
      KVarItem _ initT actT _ -> go (next n) initT || go (next n) actT
      KAssign lhs _ rhs actT _ -> go (next n) lhs || go (next n) rhs || go (next n) actT
      KReturn t -> go (next n) t
      KBreak _ -> False
      KContinue _ -> False
      KWhile _ c b e -> go (next n) (kCondTerm c) || any (goK (next n)) b || maybe False (any (goK (next n))) e
      KFor _ _ src b e -> go (next n) src || any (goK (next n)) b || maybe False (any (goK (next n))) e
      KIf alts e ->
        any (\(c, b) -> go (next n) c || any (goK (next n)) b) alts
          || maybe False (any (goK (next n))) e
      KDefer _ t -> go (next n) t
      KUsing _ acquire release -> go (next n) acquire || go (next n) release
      KSubDo _ items -> any (goK (next n)) items

    go n t
      | exhausted n = True
      | otherwise = case t of
      CMeta m ->
        m == target
          || ( not (Set.member m seen)
                 && case Map.lookup m metas of
                   Just (Just sol) -> metaOccursInValueSeen metas (next n) (Set.insert m seen) target sol
                   _ -> False
             )
      CApp _ f a -> go (next n) f || go (next n) a
      CLam _ _ _ b -> go (next n) b
      CPi _ _ _ _ a b -> go (next n) a || go (next n) b
      CCtor _ _ as -> any (go (next n)) as
      CMatch s _ _ alts -> go (next n) s || any (\(CaseAlt _ gd b) -> maybe False (go (next n)) gd || go (next n) b) alts
      CRecordT fs -> any (go (next n) . snd) fs
      CRecordV fs -> any (go (next n) . snd) fs
      CProj e _ -> go (next n) e
      CProjAt e _ _ -> go (next n) e
      CVariantT ms -> any (go (next n)) ms
      CInject _ e -> go (next n) e
      CLet _ _ a b c -> go (next n) a || go (next n) b || go (next n) c
      CLetRec _ _ a b c -> go (next n) a || go (next n) b || go (next n) c
      CIf a b c -> go (next n) a || go (next n) b || go (next n) c
      CThunkE e suspensionType ->
        go (next n) e || maybe False (go (next n)) suspensionType
      CLazyE e suspensionType ->
        go (next n) e || maybe False (go (next n)) suspensionType
      CForceE e resultType ->
        go (next n) e || maybe False (go (next n)) resultType
      CSealE _ e -> go (next n) e
      CSigT _ e -> go (next n) e
      CQuote _ slots -> any (go (next n)) slots
      CDo _ items -> any (goK (next n)) items
      _ -> False

-- | Is the value a §16.1.7.1 suspension type (Thunk/Need)?
isSuspV :: Value -> Bool
isSuspV = \case
  VGlobN global _ | global == prelThunk || global == prelNeed -> True
  _ -> False

lookupGlobalName :: Text -> CheckM (Maybe GName)
lookupGlobalName n = do
  st <- get
  let own = GName (csModule st) n
  case Map.lookup n (csLocalDeclScope st) of
    Just local -> pure (Just local)
    Nothing
      | Map.member own (csGlobals st) || Map.member own (csCtors st) ->
          pure (Just own)
      | otherwise -> pure (Map.lookup n (csScope st))

-- | Whether a constructor identity may be named unqualified at the current
-- source location. Expected-type-directed constructor selection must use the
-- same import authority as ordinary name resolution: knowing the result data
-- family does not make an opaque or non-imported constructor visible.
constructorInScope :: CheckState -> GName -> Bool
constructorInScope st constructor@(GName moduleName _) =
  constructor `elem` Map.elems (csLocalDeclScope st)
    || moduleName == csModule st
    || Map.lookup (gnameText constructor) (csScope st) == Just constructor

registerProvisionalGlobalUniverseMetas
  :: GName
  -> [LevelMeta]
  -> CheckM ()
registerProvisionalGlobalUniverseMetas global provisionalMetas = do
  let provisionalProjection =
        [ (meta, index)
        | (index, meta) <- zip [0 ..] provisionalMetas
        ]
  modify' $ \current ->
    current
      { csGlobals =
          Map.adjust
            (\definition ->
               definition
                 { gdProvisionalUniverseProjection = provisionalProjection
                 })
            global
            (csGlobals current)
      , csProvisionalGlobalUniverseMetas =
          Map.insertWith
            (\new existing -> nub (existing ++ new))
            global
            [provisionalMetas]
            (csProvisionalGlobalUniverseMetas current)
      }

-- | Instantiate a provisional declaration while fixing selected source-meta
-- positions to levels authenticated by an enclosing semantic occurrence.
-- The complete source spine is retained so SCC finalization can apply the
-- ordinary provisional-to-principal projection.
instantiateProvisionalUniversesWith
  :: ProvisionalUniverseFacet
  -> GName
  -> [LevelMeta]
  -> Map LevelMeta Level
  -> Term
  -> CheckM ([Level], Term)
instantiateProvisionalUniversesWith facet owner sourceMetas pinned term = do
  freshLevels <-
    forM sourceMetas $ \meta ->
      maybe freshLevelInstantiationMeta pure (Map.lookup meta pinned)
  consumer <- gets csActiveUniverseDefinition
  let substitution = Map.fromList (zip sourceMetas freshLevels)
      substitute = substituteLevelMetas substitution
  unless (null sourceMetas) $
    modify' $ \st ->
      let identity = csNextProvisionalUniverseInstantiation st
          occurrence =
            ProvisionalUniverseInstantiation
              identity
              facet
              owner
              consumer
              sourceMetas
              freshLevels
              False
              Set.empty
       in st
            { csProvisionalUniverseInstantiations =
                Map.insert
                  identity
                  occurrence
                  (csProvisionalUniverseInstantiations st)
            , csProvisionalUniverseInstantiationsByOwner =
                Map.insertWith
                  Set.union
                  owner
                  (Set.singleton identity)
                  (csProvisionalUniverseInstantiationsByOwner st)
            , csProvisionalUniverseInstantiationsByConsumer =
                maybe
                  (csProvisionalUniverseInstantiationsByConsumer st)
                  (\consumerOwner ->
                     Map.insertWith
                       Set.union
                       consumerOwner
                       (Set.singleton identity)
                       (csProvisionalUniverseInstantiationsByConsumer st))
                  consumer
            , csNextProvisionalUniverseInstantiation = identity + 1
            }
  pure
    ( freshLevels
    , zonkTermWith (\_ _ -> Nothing) substitute 0 term
    )

specializeGlobalAt :: Ctx -> GName -> GlobalDef -> [Level] -> CheckM (Term, Value)
specializeGlobalAt ctx g gd universes = do
  assignments <- gets csLevelAssignments
  ec <- ec_
  let rawType = zonkLevels assignments (globalCoreType ec gd)
      specialized = specializeDeclarationUniverses (gdUniverses gd) universes rawType
  -- Explicit schema arguments are ordinary first-class TypeLevel terms and
  -- may therefore denote caller-local values.  Evaluate the specialized
  -- interface in the occurrence context so LVar identities remain rigid;
  -- evaluating in emptyCtx turns them into unrelated metas and loses proof
  -- obligations such as the reflexive bound in f.{v} v.
  ty <- evalIn ctx specialized
  pure (CGlobI g universes, ty)

recordRecursiveSchemaOccurrence :: Maybe Ctx -> Bool -> Span -> GName -> [Level] -> CheckM ()
recordRecursiveSchemaOccurrence occurrenceCtx explicit site callee levels = do
  st <- get
  case csActiveUniverseDefinition st of
    Just caller
      | csRecordRecursiveSchemaOccurrences st
      , Map.member caller (csGlobals st)
      , Map.member callee (csGlobals st) -> do
          assumptions <- effectiveLevelAssumptions (fromMaybe emptyCtx occurrenceCtx)
          modify' $ \current ->
            insertRecursiveSchemaOccurrence
              (RecursiveSchemaOccurrence caller callee levels explicit assumptions site)
              current
    _ -> pure ()

-- | Specialize either a finalized declaration telescope ('LParam') or the
-- exact provisional meta spine carried by a same-SCC occurrence. The latter
-- is essential during header elaboration: re-reading the raw declaration type
-- without substituting its occurrence spine reconnects a use to the callee's
-- source metas and destroys independent instantiation (§11.1.2.3A).
specializeDeclarationUniverses
  :: DeclarationUniverseTelescope
  -> [Level]
  -> Term
  -> Term
specializeDeclarationUniverses telescope universes rawType
  | dutParameterCount telescope > 0 =
      zonkTermWith (\_ _ -> Nothing) (substituteLevelParams universes) 0 rawType
  | length universes == length provisionalMetas =
      zonkTermWith
        (\_ _ -> Nothing)
        (substituteLevelMetas (Map.fromList (zip provisionalMetas universes)))
        0
        rawType
  | otherwise = rawType
  where
    provisionalMetas = nub (levelMetasOfTerm rawType)

-- Constructors as values: λ-wrap to a saturated source-shaped 'CCtor'. KCore
-- keeps explicit fields, including explicit erased fields, so the interpreter
-- and conversion continue to see source pattern arity. Only the KCore →
-- KBackendIR lowering physically drops runtime-erased fields.
--
-- The native backend recognises a saturated application of this shape and
-- beta-reduces it back to a direct 'CCtor' ('Kappa.Backend.IR.coreEtaCtorApp');
-- that recognizer depends on the exact shape produced here (nested 'CLam's
-- whose body is a 'CCtor' selecting the Core constructor payload binders by bare
-- 'CVar'), so keep the two in sync.
etaCtor :: EvalCtx -> GName -> [Level] -> Term -> Term
etaCtor ec g universes cty = build 0 [] (eval ec [] cty)
  where
    build n acc fty = case force ec fty of
      VPiRuntimeM mode _ ic q _ name _ _ runtimeErasure dom clo ->
        CLamM mode ic q ("x" <> T.pack (show n)) $
          build (n + 1) ((n, ic, coreCtorPayloadField ec n runtimeErasure ic q dom, name) : acc) (evalClosure clo (VRigid n []))
      _ ->
        -- KBackendIR Stage 0 / Perceus S1.3: annotate the saturated 'CCtor'
        -- with the constructor's TYPE telescope ('cty', a closed top-level term)
        -- so KBackendIR lowering can recover the field count/layout via
        -- 'Repr.ctorLayoutOf' (the runtime fields are this telescope's
        -- non-erased explicit payloads plus non-erased implicit evidence).
        -- Observe-only metadata for KCore equality/conversion; KBackendIR reads it
        -- when attaching layout facts, but it cannot change tag ids or evaluation.
        CCtorI g universes (Just cty)
          [ ConstructorArg ic payload (Just name) (CVar (n - 1 - i))
          | (i, ic, payload, name) <- reverse acc
          ]
    evalClosure (Closure env body) v = eval ec (v : env) body
    coreCtorPayloadField ctx lvl runtimeErasure ic q dom =
      ic == Expl || Repr.runtimeConstructorPiField ctx lvl runtimeErasure ic q dom

-- universe spellings: Type, Type0, Type1, ..., and '*' (§11.1)
sortName :: Text -> Maybe Level
sortName t
  | t == "Type" || t == "*" = Just LZero
  | t == "Typeω" = Just LOmega
  | Just rest <- T.stripPrefix "Type" t
  , not (T.null rest)
  , T.all (\c -> c >= '0' && c <= '9') rest
  , -- bounds check: a suffix this long would overflow 'Int'; treat the
    -- spelling as an ordinary (unresolved) identifier instead
    T.length rest <= 9 =
      Just (finiteLevel (read (T.unpack rest) :: Integer))
  | otherwise = Nothing

isTypeLevelValue :: Value -> CheckM Bool
isTypeLevelValue v = forceM v >>= \case
  VGlobN g [] -> pure (g == prelTypeLevel)
  _ -> pure False

-- | Select and retain the formation judgment while the domain and source
-- annotation are available. Later phases consume this fact; they must not
-- reconstruct it from observation mode, quantity, or erasure.
selectFormationMode :: Ctx -> ObservationMode -> Value -> CheckM FormationMode
selectFormationMode ctx mode domain = do
  parametricKind <- isParametricKind (ctxLen ctx) domain
  pure $
    if mode == Parametric && parametricKind
      then FormationParametric
      else FormationOrdinary

extendLevelAssumption :: Span -> Ctx -> Maybe (Level, Level) -> CheckM Ctx
extendLevelAssumption _ ctx Nothing = pure ctx
extendLevelAssumption sp ctx (Just (lhs, rhs)) = do
  let extended = insertAssumption lhs rhs (ctxLevelAssumptions ctx)
  case classifyAssumptions extended of
    Proved -> pure ctx {ctxLevelAssumptions = extended}
    Blocked _ -> pure ctx {ctxLevelAssumptions = extended}
    IndeterminateResourceLimit -> do
      report $
        withPayload
          ( withPayloadField "rejectedConstraint" (renderLevel lhs <> " <= " <> renderLevel rhs) $
              payloadKind "universe-inference-requires-annotation"
          ) $
          diag SevError StageElaborate "E_UNIVERSE_INFERENCE_REQUIRES_ANNOTATION"
            (Just "kappa.universe.inference-requires-annotation") sp
            "the scoped universe assumptions exceed the portable solver resource boundary"
      pure ctx {ctxLevelAssumptions = extended}
    Disproved -> rejectContradiction extended
    ContradictoryAssumptions -> rejectContradiction extended
  where
    rejectContradiction extended = do
      let rejected = renderLevel lhs <> " <= " <> renderLevel rhs
          -- A prior path may establish @succ rhs <= lhs@ transitively.  The
          -- rejected edge @lhs <= rhs@ then closes a strict cycle even when
          -- the two source expressions have different head identities.
          selfContainment =
            isNothing (compareClosedLevel lhs rhs)
              && proveLevelLeq (ctxLevelAssumptions ctx) (levelSucc rhs) lhs == Proved
          code =
            if selfContainment
              then "E_UNIVERSE_SELF_CONTAINMENT"
              else "E_UNIVERSE_CONSTRAINT_UNSATISFIABLE"
      report $
        withPayload
          ( withPayloadField "rejectedConstraint" rejected $
              withPayloadField "normalizedRejectedConstraint" rejected $
                withPayloadField "constraintOrigin" "erased level-comparison proof binder" $
                  withPayloadField "enclosingConstructKind" "telescope" $
                    withPayloadField "universeVariablesInScope" (T.pack (show (levelVars lhs ++ levelVars rhs))) $
                      withPayloadField "levelAssumptions" (renderLevelAssumptions extended) $
                        withPayloadField "selfContainment" (if selfContainment then "true" else "false") $
                          withPayloadField "failureKind" "explicit-level-evidence" $
                            withPayloadField "sourceOrigin" (T.pack (show sp)) $
                              payloadKind "universe-constraint"
          ) $
          diag SevError StageElaborate code
            (Just "kappa.universe.constraint") sp
            ( "the erased level bound " <> rejected
                <> " makes the scoped universe assumptions inconsistent (§11.1.2.2)"
            )
      -- Keep the rejected assumption in the recovery context. The exact
      -- solver treats an inconsistent context as proving nothing, while the
      -- marker lets later formation checks suppress cascaded diagnostics.
      pure ctx {ctxLevelAssumptions = extended}

renderLevelAssumptions :: Assumptions -> Text
renderLevelAssumptions assumptions =
  T.intercalate ", "
    [renderLevel lhs <> " <= " <> renderLevel rhs | (lhs, rhs) <- assumptionsList assumptions]

anyHole :: Ctx -> CheckM (Term, Value)
anyHole ctx = do
  m <- freshMeta
  ty <- freshMetaV ctx
  pure (m, ty)

reportUnsolvedHoleAt :: Int -> Text -> Span -> Term -> CheckM ()
reportUnsolvedHoleAt depth holeName sp tyT = do
  tyTz <- zonkTermM depth tyT
  let
      expectedR = renderTerm tyTz
  report $
    -- §3.2.4 kappa.hole.unsolved payload: hole identifier + expected type.
    withPayload
      ( withPayloadField "hole" holeName $
          withPayloadField "expected" expectedR $
            payloadKind "hole-unsolved"
      )
      $ diag SevError StageElaborate "E_HOLE_UNSOLVED" (Just "kappa.hole.unsolved") sp
          ("hole " <> holeName <> " : " <> expectedR)

pendingEntryMeta :: PendingEvidenceEntry -> MetaId
pendingEntryMeta (meta, _, _, _, _) = meta

pendingEntryCtx :: PendingEvidenceEntry -> Ctx
pendingEntryCtx (_, _, _, pendingCtx, _) = pendingCtx

refreshPendingEntry :: PendingEvidenceEntry -> CheckM Value
refreshPendingEntry (_, goal, _, pendingCtx, _) =
  quoteIn pendingCtx goal
    >>= zonkTermM (ctxLen pendingCtx)
    >>= evalIn pendingCtx
    >>= forceM

reportUnsupported :: Span -> Text -> CheckM ()
reportUnsupported sp what =
  let msg = what <> " is not supported by this implementation"
   in report $
        withNote "see SPEC_COMPLIANCE.md for the implemented subset" $
          withPayload (unsupportedPayload msg) $
            diag SevError StageElaborate "E_UNSUPPORTED" (Just "kappa.unsupported.deterministic") sp msg

unsupported :: Ctx -> Span -> Text -> CheckM (Term, Value)
unsupported ctx sp what = reportUnsupported sp what >> anyHole ctx

-- | Kind-like goals — @Type@, @Type -> Type@, … — are inferred from
-- use sites (metavariables), never searched as evidence (§16.3.3).
-- LOCKSTEP: @Kappa.Backend.Repr.runtimeErasedParam@ is the pure shared
-- backend-side classifier for quantity-0, kind-domain, and proof-only binders.
-- If the notion of kind-like changes here (e.g. a new sort-former), update that
-- shared classifier in lockstep or KBackendIR erasure can desync from the
-- elaborator.
isKindLike :: Int -> Value -> CheckM Bool
isKindLike lvl v = do
  t <- forceM v
  case t of
    VSort _ -> pure True
    VPi _ _ _ _ _ clo -> do
      cod <- clApp clo (VRigid lvl [])
      isKindLike (lvl + 1) cod
    _ -> pure False

observationForBinding :: ObservationMode -> Text -> Value -> CheckM ObservationJudgment
observationForBinding mode origin classifier = do
  classifier' <- case mode of
    Ordinary -> pure Nothing
    Parametric ->
      forceM classifier >>= \case
        VSort level -> pure (Just (ObservationType level))
        _ -> pure (Just ObservationTypeFormer)
  pure (ObservationJudgment mode origin classifier')

ordinaryObservation :: Text -> ObservationJudgment
ordinaryObservation origin = ObservationJudgment Ordinary origin Nothing

joinObservation :: ObservationJudgment -> ObservationJudgment -> ObservationJudgment
joinObservation left right = case (ojMode left, ojMode right) of
  (Parametric, _) -> left
  (_, Parametric) -> right
  _ -> left

-- | Derive an occurrence's KCore observation judgment from the exact finite
-- origin calculus of SS30.2.0.  This is the elaboration-side invocation of the
-- same pure analyzer used by the finalized KCore checkpoint.
observationJudgmentForTerm :: Ctx -> Term -> Value -> CheckM ObservationJudgment
observationJudgmentForTerm ctx term classifier = do
  establishedDependencies <- observationDependenciesForTerm ctx term classifier
  let mode = dependenciesMode establishedDependencies
      origin = case Set.lookupMin establishedDependencies of
        Nothing -> "ordinary-expression"
        Just dependency -> T.pack (show dependency)
  observationForBinding mode origin classifier

-- | The dependency set underlying 'observationJudgmentForTerm'. Declaration
-- generalization consumes the identities directly so it can distinguish a
-- newly-rigid candidate binder from unrelated outer parametric dependencies.
observationDependenciesForTerm :: Ctx -> Term -> Value -> CheckM DependencySet
observationDependenciesForTerm ctx term classifier = do
  st <- get
  ec <- ec_
  bindings <- forM (zip [0 ..] (ctxEntries ctx)) $ \(index, entry) -> do
    mode <-
      if ceModeProvisional entry
        then do
          parametricKind <- isParametricKind (ctxLen ctx) (ceType entry)
          pure (if parametricKind then Parametric else Ordinary)
        else pure (ceMode entry)
    pure
      ObservationBinding
        { obMode = mode
        , obOrigin =
            if mode == Parametric
              then Just (ParametricExternal index (fromMaybe (ceName entry) (ceObservationOrigin entry)))
              else Nothing
        , obType = Just (ceType entry)
        , obUniverses = luiTelescope <$> ceLocalUniverses entry
        , obDefinition = Nothing
        }
  let oracle = observationOracle st ec
      -- Observation is a finite structural analysis.  Whole-term NBE here
      -- would unfold recursive definitions before the dependency equations
      -- can use their already-finalized global summaries.
      rawDependencies = observationDependencies oracle bindings (Just classifier) term
      classifierRelative =
        classifierRelativeDependencies oracle bindings (ctxLen ctx) classifier rawDependencies
      dependencies =
        evidenceRelativeCallableDependencies ec (ctxLen ctx) classifier classifierRelative
      -- Term metas are not stable observation origins.  During application
      -- elaboration they can be solved by later operands in the same spine,
      -- so defer only these origins until the declaration is zonked and the
      -- finalized Core checkpoint reruns the same calculus.  In particular,
      -- do not discard 'ParametricAnalysisFailure': that is a real fail-closed
      -- source diagnostic rather than a deferred inference fact.
      establishedDependencies = Set.filter (\case ParametricMeta {} -> False; _ -> True) dependencies
  pure establishedDependencies

observationOracle :: CheckState -> EvalCtx -> ObservationOracle
observationOracle st ec =
  ObservationOracle
    { ooEvalCtx = ec
    , ooThisType = thisObservationType (csThis st)
    , ooGlobalMode = \global@(GName moduleName _) ->
        -- The active declaration's recursive self edge is an equation
        -- variable, not a fresh observation origin.  Taking it as ordinary
        -- here computes the least fixed point: every independent dependency
        -- in the body is still retained and determines the final summary.
        if Just global == csActiveUniverseDefinition st
          then Just Ordinary
          else
            (gdObservationMode <$> Map.lookup global (csGlobals st))
              <|> (Ordinary <$ guard (moduleName == primModule))
    , ooGlobalBody = \global -> do
        definition <- Map.lookup global (csGlobals st)
        if gdReducible definition then gdCoreBody definition else Nothing
    , ooGlobalPrimitive = \global ->
        maybe False (maybe False primitiveValue . gdValue)
          (Map.lookup global (csGlobals st))
    , ooMetaMode = metaObservationMode st ec
    , ooInferType = observationTermTypeAt st ec
    , ooProjectionMode = \receiverType field ->
        case force ec receiverType of
          VGlobN trait _ ->
            (Map.lookup trait (csTraits st) >>= Map.lookup field . tiMemberModes)
              <|> nominalHiddenProjectionMode st ec receiverType field
          _ ->
            nominalHiddenProjectionMode st ec receiverType field
    , ooProjectionType = \depth _receiver receiverType field ->
        observationTermTypeAt st ec (depth + 1)
          [ ObservationBinding
              { obMode = Ordinary
              , obOrigin = Nothing
              , obType = Just receiverType
              , obUniverses = Nothing
              , obDefinition = Nothing
              }
          ]
          (CProjM Ordinary (CVar 0) field)
    , ooProjectionTrait = \receiverType field ->
        case force ec receiverType of
          VGlobN trait _ -> do
            info <- Map.lookup trait (csTraits st)
            guard (Map.member field (tiMemberModes info))
            pure trait
          _ -> Nothing
    , ooConstructorType = \constructor universes ->
        case Map.lookup constructor (csCtors st) of
          Nothing -> Nothing
          Just info -> specializeConstructorType ec universes info
    , ooProvisionalUniverseMetadata = True
    , ooExpandingGlobals = Set.empty
    }
  where
    thisObservationType = \case
      Just (ThisType fields) -> Just (VRecordTQ (sortOn rfName fields))
      Just (ThisTraitSibs fields) -> Just (VRecordTQ (sortOn rfName fields))
      Just (ThisValue _ fields) -> Just (VRecordTQ (sortOn rfName fields))
      Nothing -> Nothing

    primitiveValue value = case force ec value of
      VPrim {} -> True
      VIOAction {} -> True
      _ -> False

metaObservationMode :: CheckState -> EvalCtx -> MetaId -> Maybe ObservationMode
metaObservationMode st ec meta = do
  classifier <- Map.lookup meta (csMetaClassifiers st)
  let depth = micDepth classifier
      environment = [VRigid level [] | level <- reverse [0 .. depth - 1]]
      classifierValue = eval ec environment (micType classifier)
  pure
    ( if isParametricKindValue ec depth classifierValue
        then Parametric
        else Ordinary
    )

observationTermTypeAt :: CheckState -> EvalCtx -> Int -> [ObservationBinding] -> Term -> Maybe Value
observationTermTypeAt st ec depth localBindings = go
  where
    globals = csGlobals st

    go = \case
      CGlobal global universes -> specializeGlobalType universes . gdType <$> Map.lookup global globals
      CVar index -> listToMaybe (drop index localBindings) >>= obType
      CLocal index universes -> do
        binding <- listToMaybe (drop index localBindings)
        telescope <- obUniverses binding
        ty <- obType binding
        if length universes == dutParameterCount telescope
          then Just (specializeLocalType telescope universes ty)
          else Nothing
      CProjM _ receiver field -> go receiver >>= projectionType receiver field
      CProjAtM _ receiver field _ -> go receiver >>= projectionType receiver field
      CSealE _ value -> go value
      CIf _ yes no -> sameType (go yes) (go no)
      CMatch _ _ resultAnnotation _ -> evalAt <$> resultAnnotation
      application@CApp {} ->
        let (headTerm, arguments) = spineOfTerm application
         in go headTerm >>= \headType -> applyArguments headType arguments
      _ -> Nothing

    applyArguments ty [] = Just ty
    applyArguments ty ((actualIcit, argument) : rest) =
      case force ec ty of
        VPiM _ expectedIcit _ _ _ _ (Closure closureEnv codomain)
          | actualIcit == expectedIcit ->
              applyArguments (eval ec (evalAt argument : closureEnv) codomain) rest
        _ -> Nothing

    projectionType receiver field receiverType =
      case force ec receiverType of
        VRecordTQ fields -> rfType <$> find ((== field) . rfName) fields
        VSigT _ inner -> projectionType receiver field inner
        VGlobI trait universes arguments ->
          case Map.lookup trait (csTraits st) of
            Just info
              | Just semanticArguments <- traitSemanticSpineIn st trait arguments
              , field `elem` tiMembers info -> do
                  member <- Map.lookup (memberGlobal trait field) globals
                  memberType <- specializeGlobalDefinitionTypePrefix ec universes member
                  let specializedMemberType = quote ec depth memberType
                      argumentTerms = map (quote ec depth . snd) semanticArguments
                  projectedType <-
                    specializeTraitMemberProjectionType depth (tiParamCount info)
                      argumentTerms receiver specializedMemberType
                  pure (evalAt projectedType)
              | Just semanticArguments <- traitSemanticSpineIn st trait arguments
              , Just super <- Map.lookup field (Map.fromList (tiSupers info)) ->
                  applySuper (eval ec [] super) (map snd semanticArguments)
            _ ->
              snd <$> nominalHiddenProjectionInfo st ec depth receiver receiverType field
        _ ->
          snd <$> nominalHiddenProjectionInfo st ec depth receiver receiverType field

    applySuper value [] = Just (force ec value)
    applySuper value (argument : arguments) =
      case force ec value of
        VLamM _ Expl _ _ (Closure closureEnv body) ->
          applySuper (eval ec (argument : closureEnv) body) arguments
        _ -> Nothing

    sameType (Just left) (Just right)
      | convertible ec depth (force ec left) (force ec right) = Just left
    sameType _ _ = Nothing

    specializeGlobalType universes value
      | null universes = value
      | otherwise =
          eval ec []
            (zonkTermWith (\_ _ -> Nothing) (substituteLevelParams universes) 0 (quote ec 0 value))

    -- Local declaration schemas are interpreted in the lexical term scope in
    -- which their type was recorded. Quoting at depth zero turns references to
    -- enclosing binders into malformed/out-of-scope terms and makes typed
    -- observation replay reject valid mutually recursive local declarations.
    -- Keep this identical to Backend.IR's finalized-Core type recovery.
    specializeLocalType telescope universes generalizedType =
      let raw = quote (ec {ecFacts = Map.empty}) depth generalizedType
          specialized =
            zonkTermWith
              (\_ _ -> Nothing)
              (instantiateLocalLevelParams (dutParameterCount telescope) universes)
              0
              raw
       in eval ec [VRigid level [] | level <- reverse [0 .. depth - 1]] specialized

    evalAt = eval ec [VRigid level [] | level <- reverse [0 .. depth - 1]]

-- | Recover a named erased constructor field from a nominal receiver using
-- the same checked constructor interfaces that authorized source projection.
-- Every constructor of the family must expose the same final hidden binder;
-- otherwise the typed analysis fails closed instead of inferring a field from
-- its spelling. Prior named source fields are instantiated as projections of
-- the receiver so dependent proof-field types retain their exact identity.
nominalHiddenProjectionInfo
  :: CheckState
  -> EvalCtx
  -> Int
  -> Term
  -> Value
  -> Text
  -> Maybe (ObservationMode, Value)
nominalHiddenProjectionInfo st ec depth receiverTerm receiverType field = do
  family <- case force ec receiverType of
    VGlobI global _ _ ->
      Just global
    _ -> Nothing
  dataInfo <- Map.lookup family (csDatas st)
  guard (not (null (diCtors dataInfo)))
  nominalHiddenProjectionInfoForConstructors
    st
    ec
    depth
    receiverTerm
    receiverType
    (diCtors dataInfo)
    field

-- | Recover a named erased constructor field over an authenticated subset of
-- a nominal family's constructors. Every preceding source binder is
-- instantiated by projecting that binder from the same receiver, so a
-- dependent field such as @proof : predicate value@ retains the exact
-- receiver-indexed type. Fresh constructor metas are deliberately not used:
-- they describe an arbitrary constructor occurrence rather than this value.
nominalHiddenProjectionInfoForConstructors
  :: CheckState
  -> EvalCtx
  -> Int
  -> Term
  -> Value
  -> [GName]
  -> Text
  -> Maybe (ObservationMode, Value)
nominalHiddenProjectionInfoForConstructors
  st ec depth receiverTerm receiverType constructors field = do
  (universes, familyArguments) <- case force ec receiverType of
    VGlobI _ selectedUniverses arguments ->
      Just (selectedUniverses, map snd arguments)
    _ -> Nothing
  guard (not (null constructors))
  results <-
    traverse
      (constructorField universes familyArguments)
      constructors
  case results of
    firstResult@(_, firstType) : rest -> do
      guard
        ( all
            (\(mode, fieldType) ->
               mode == fst firstResult
                 && convertible ec depth firstType fieldType)
            rest
        )
      pure firstResult
    [] -> Nothing
  where
    receiverValue =
      eval ec
        [VRigid level [] | level <- reverse [0 .. depth - 1]]
        receiverTerm

    constructorField universes familyArguments constructor = do
      info <- Map.lookup constructor (csCtors st)
      targetIndex <- case
        [ index
        | (index, sourceField) <- zip [0 :: Int ..] (ciSourceFields info)
        , sourceField == (Impl, Just field)
        ] of
          [] -> Nothing
          indices -> Just (last indices)
      constructorType <- specializeConstructorType ec (Just universes) info
      let sourceCount = length (ciSourceFields info)
          prefixCount = constructorPiCount constructorType - sourceCount
      guard (prefixCount >= 0 && prefixCount == length familyArguments)
      sourceType <- applyPrefix constructorType familyArguments
      selectSourceField targetIndex receiverValue sourceType (ciSourceFields info)

    constructorPiCount value = case force ec value of
      VPiM _ _ _ _ _ _ closure ->
        1 + constructorPiCount (clAppRigid closure)
      _ -> 0

    clAppRigid (Closure environment codomain) =
      eval ec (VRigid (length environment) [] : environment) codomain

    applyPrefix value [] = Just value
    applyPrefix value (argument : arguments) =
      case force ec value of
        VPiM _ _ _ _ _ _ (Closure environment codomain) ->
          applyPrefix (eval ec (argument : environment) codomain) arguments
        _ -> Nothing

    selectSourceField targetIndex root = go 0
      where
        go _ _ [] = Nothing
        go index value ((expectedIcit, expectedName) : rest) =
          case force ec value of
            VPiM mode actualIcit quantity _ actualName domain (Closure environment codomain) -> do
              guard (actualIcit == expectedIcit)
              guard (expectedName == Just actualName)
              if index == targetIndex
                then do
                  guard (actualIcit == Impl && quantity == Q0 && actualName == field)
                  pure (mode, domain)
                else do
                  name <- expectedName
                  let argument = VProjN mode root name
                  go (index + 1) (eval ec (argument : environment) codomain) rest
            _ -> Nothing

-- | Authenticate the observation mode of a named erased constructor field
-- without fabricating a receiver value.  Unlike the dependent field type,
-- the mode is fixed by the constructor telescope itself.  Looking it up
-- directly also keeps the observation oracle valid at arbitrary lexical
-- depths: a synthetic @CVar 0@ cannot instantiate a field whose type depends
-- on the actual nominal receiver and its preceding fields.
nominalHiddenProjectionMode
  :: CheckState
  -> EvalCtx
  -> Value
  -> Text
  -> Maybe ObservationMode
nominalHiddenProjectionMode st ec receiverType field = do
  family <- case force ec receiverType of
    VGlobI global _ _ -> Just global
    _ -> Nothing
  dataInfo <- Map.lookup family (csDatas st)
  guard (not (null (diCtors dataInfo)))
  modes <- traverse constructorMode (diCtors dataInfo)
  case modes of
    firstMode : rest
      | all (== firstMode) rest -> Just firstMode
    _ -> Nothing
  where
    constructorMode constructor = do
      info <- Map.lookup constructor (csCtors st)
      targetIndex <- case
        [ index
        | (index, sourceField) <- zip [0 :: Int ..] (ciSourceFields info)
        , sourceField == (Impl, Just field)
        ] of
          [] -> Nothing
          indices -> Just (last indices)
      -- Observation mode is invariant under declaration-universe
      -- specialization.  Inspecting the raw checked telescope avoids making a
      -- mode query depend on whether a provisional universe occurrence has
      -- already been finalized.
      let constructorType = eval ec [] (ciType info)
          sourceCount = length (ciSourceFields info)
          prefixCount = constructorPiCount constructorType - sourceCount
      guard (prefixCount >= 0)
      sourceType <- dropPrefix prefixCount constructorType
      selectMode targetIndex sourceType (ciSourceFields info)

    constructorPiCount value = case force ec value of
      VPiM _ _ _ _ _ _ closure ->
        1 + constructorPiCount (applyRigid closure)
      _ -> 0

    applyRigid (Closure environment codomain) =
      eval ec (VRigid (length environment) [] : environment) codomain

    dropPrefix 0 value = Just value
    dropPrefix count value = case force ec value of
      VPiM _ _ _ _ _ _ closure ->
        dropPrefix (count - 1) (applyRigid closure)
      _ -> Nothing

    selectMode _ _ [] = Nothing
    selectMode targetIndex value ((expectedIcit, expectedName) : rest) =
      case force ec value of
        VPiM mode actualIcit quantity _ actualName _ closure -> do
          guard (actualIcit == expectedIcit)
          guard (expectedName == Just actualName)
          if targetIndex == 0
            then do
              guard (actualIcit == Impl && quantity == Q0 && actualName == field)
              pure mode
            else
              selectMode (targetIndex - 1) (applyRigid closure) rest
        _ -> Nothing

constructorObservationSites :: EvalCtx -> Value -> [(ObservationMode, Value)]
constructorObservationSites ec = collect 0
  where
    collect level value = case force ec value of
      VPiM mode _ _ _ _ domain (Closure closureEnv codomain) ->
        (mode, domain) : collect (level + 1) (eval ec (VRigid level [] : closureEnv) codomain)
      _ -> []

specializeConstructorType :: EvalCtx -> Maybe [Level] -> CtorInfo -> Maybe Value
specializeConstructorType ec selectedUniverses info =
  case selectedUniverses of
    Nothing -> Just (eval ec [] (ciType info))
    Just universes ->
      let telescope = ciUniverses info
          rawType = ciType info
          provisionalMetas = nub (levelMetasOfTerm rawType)
          provisionalParameterArity = case levelParamsOfTerm rawType of
            [] -> 0
            parameters -> 1 + maximum parameters
          specialize substitution =
            Just (eval ec [] (zonkTermWith (\_ _ -> Nothing) substitution 0 rawType))
       in if dutParameterCount telescope > 0
            then
              if length universes == dutParameterCount telescope
                then specialize (substituteLevelParams universes)
                else Nothing
            else
              -- During header/SCC elaboration an inferred constructor has a
              -- provisional ordered raw-meta telescope while occurrences
              -- already carry its freshly instantiated spine.
              if not (null provisionalMetas) && length universes == length provisionalMetas
                then specialize
                  (substituteLevelMetas (Map.fromList (zip provisionalMetas universes)))
                else if null provisionalMetas && length universes == provisionalParameterArity
                  then specialize (substituteLevelParams universes)
                  else Nothing

buildPendingEvidenceGraph :: CheckM PendingEvidenceGraph
buildPendingEvidenceGraph = do
  state <- get
  ec <- ec_
  let classifierDependencies =
        Map.map
          (Set.fromList . unsolvedMetasOf state . micType)
          (csMetaClassifiers state)
      closeClassifiers = closeClassifierDependencies classifierDependencies
      entries = csPending state
      dependencies =
        Map.fromList
          [ ( pendingEntryMeta entry
            , closeClassifiers
                ( Set.insert
                    (pendingEntryMeta entry)
                    ( Set.fromList
                        ( unsolvedMetasOf
                            state
                            (quote ec (ctxLen pendingCtx) goal)
                        )
                    )
                )
            )
          | entry@(_, goal, _, pendingCtx, _) <- entries
          ]
      reverseIndex =
        Map.fromListWith Set.union
          [ (meta, Set.singleton evidence)
          | (evidence, metas) <- Map.toList dependencies
          , meta <- Set.toList metas
          ]
  pure
    PendingEvidenceGraph
      { pegPendingIds =
          Set.fromList [pendingEntryMeta entry | entry <- entries]
      , pegDependencies = dependencies
      , pegReverseIndex = reverseIndex
      , pegClassifierDependencies = classifierDependencies
      }

closeClassifierDependencies
  :: Map MetaId (Set MetaId)
  -> Set MetaId
  -> Set MetaId
closeClassifierDependencies dependencies initial = close initial initial
  where
    close reached frontier
      | Set.null frontier = reached
      | otherwise =
          let discovered =
                Set.unions
                  [ Map.findWithDefault Set.empty meta dependencies
                  | meta <- Set.toList frontier
                  ]
              fresh = Set.difference discovered reached
           in close (Set.union reached fresh) fresh

pendingEvidenceComponentIn
  :: PendingEvidenceGraph
  -> Set MetaId
  -> Set MetaId
pendingEvidenceComponentIn graph rawSeed = close seed Set.empty
  where
    closeClassifiers =
      closeClassifierDependencies (pegClassifierDependencies graph)
    seed = closeClassifiers rawSeed
    close reachable evidence =
      let connected =
            Set.unions
              [ Map.findWithDefault Set.empty meta (pegReverseIndex graph)
              | meta <- Set.toList reachable
              ]
          evidence' = Set.union evidence connected
          reachable' =
            closeClassifiers
              ( Set.unions
                  ( reachable
                      : [ Map.findWithDefault Set.empty meta (pegDependencies graph)
                        | meta <- Set.toList evidence'
                        ]
                  )
              )
       in if reachable' == reachable && evidence' == evidence
            then evidence
            else close reachable' evidence'

-- | Expose the equality proposition behind a standard level-relation alias.
-- Ordinary forcing is preferred.  During an early declaration checkpoint an
-- imported reducible alias can still be represented by its neutral global;
-- in that case unfold only the authenticated standard identity and only from
-- its checked monomorphic semantic body.
levelConstraintEqualityGoal :: Ctx -> Value -> CheckM (Maybe Value)
levelConstraintEqualityGoal ctx goal = do
  forced <- forceM goal
  case forced of
    VGlobN equality _ | equality == prelEqType -> pure (Just forced)
    VCtor equality _ | equality == prelEqType -> pure (Just forced)
    _ -> do
      ec <- ec_
      goalTerm <- zonkTermM (ctxLen ctx) (quote ec (ctxLen ctx) goal)
      case spineOfTerm goalTerm of
        (CGlobal alias universes, arguments)
          | alias == prelLevelLe || alias == prelLevelLt
          , null universes -> do
              definition <- gets (Map.lookup alias . csGlobals)
              case definition >>= gdValue of
                Just body
                  | maybe False gdReducible definition -> do
                      argumentValues <-
                        mapM
                          (\(icit, argument) -> (,) icit <$> evalIn ctx argument)
                          arguments
                      pure (Just (force ec (evalApp ec body argumentValues)))
                _ -> pure Nothing
        _ -> pure Nothing

-- | Unsolved metavariable identifiers occurring in a value's quotation.
unsolvedMetaIdsIn :: Value -> CheckM [MetaId]
unsolvedMetaIdsIn v = do
  ec <- ec_
  let t = quote ec 0 v
  st <- get
  pure (unsolvedMetasOf st t)

-- | Replace solved metavariables by their solutions, quoted at the
-- correct binder depth. Run after 'flushPending' so terms stored as
-- globals (and instance dictionaries) contain no live 'CMeta' whose
-- solution mentions local rigids (premise dictionaries, §14.3.2).
zonkTermM :: Int -> Term -> CheckM Term
zonkTermM depth0 t0 = do
  ec <- ec_
  st <- get
  assignments <- gets csLevelAssignments
  let resolve = resolvedMetaCore st ec
      resolveLevel = substituteLevelMetas assignments
  pure (zonkTermWith resolve resolveLevel depth0 t0)

-- | Reify one solved typed metavariable back to Core. Evaluation is
-- intentionally transparent through 'CUniverseLift', so the meta store can
-- retain only the semantic value. The creation-site classifier and the
-- solver-selected proof are the authority for restoring that erased
-- cumulative use; callers must not infer it from the solved value's shape.
resolvedMetaCore :: CheckState -> EvalCtx -> Int -> MetaId -> Maybe Term
resolvedMetaCore st ec depth meta = do
  solution <- Map.lookup meta (ecMetas ec) >>= id
  let term0 = quote ec depth solution
      term =
        case Map.lookup meta (csMetaClassifiers st) of
          Just MetaClassifier {micDepth, micType}
            | depth >= micDepth ->
                etaLongAtClassifier
                  term0
                  (shiftTerm (depth - micDepth) 0 micType)
          _ -> term0
  pure $
    case Map.lookup meta (csMetaClassifiers st) >>= micUniverseCoercion of
      Just evidence -> universeLift evidence term
      Nothing -> term
  where
    -- NbE stores higher-order meta solutions extensionally. For a Miller
    -- equation such as @?P x = F x@ the semantic solution may therefore be
    -- the head @F@ even when @?P@'s authenticated Pi classifier has a
    -- different quantity or observation mode. Reifying that head verbatim
    -- produces ill-typed Core (notably for quantity-0 equality motives).
    --
    -- Eta-long reification is the standard typed boundary: every generated
    -- lambda takes its contract from the creation-site classifier and applies
    -- the semantic solution to the same binder. KCore independently checks
    -- the result, so this cannot turn an invalid semantic solution into an
    -- accepted artifact. Borrowed Pi binders have no lambda representation
    -- and therefore remain fail-closed.
    etaLongAtClassifier solutionTerm = \case
      CPiEvidenceM mode _ ic quantity False name _ _ _ codomain ->
        CLamM
          mode
          ic
          quantity
          name
          ( etaLongAtClassifier
              (CApp ic (shiftTerm 1 0 solutionTerm) (CVar 0))
              codomain
          )
      _ -> solutionTerm

isTraitGoal :: Value -> CheckM Bool
isTraitGoal v =
  forceM v >>= \case
    VGlobN g arguments -> do
      state <- get
      pure $
        if g == gPrel "IsTrait"
          then length arguments == 1
          else case Map.lookup g (csTraits state) of
            Just info ->
              maybe
                False
                ((== tiParamCount info) . length)
                (traitSemanticSpineIn state g arguments)
            Nothing -> False
    _ -> pure False

-- | Remove the physically present declaration-universe proof prefix from a
-- resolved trait application.  Instance heads, supertrait closures, and
-- member telescopes are defined over the trait's semantic source parameters;
-- generated/user level proofs are ordinary implicit Core arguments but are
-- not additional trait parameters.  The exact resolved global type is the
-- authority, so an ordinary implicit parameter can never be dropped merely
-- because its source shape resembles evidence.
traitSemanticSpineIn
  :: CheckState
  -> GName
  -> [(Icit, argument)]
  -> Maybe [(Icit, argument)]
traitSemanticSpineIn st trait arguments = do
  definition <- Map.lookup trait (csGlobals st)
  info <- Map.lookup trait (csTraits st)
  let semanticCount = tiParamCount info
      parameterCount = dutParameterCount (gdUniverses definition)
      proofCount =
        length
          ( declarationUniverseConstraints
              parameterCount
              (globalCoreType (ecOf st) definition)
          )
      (proofArguments, semanticArguments) = splitAt proofCount arguments
  if length arguments == semanticCount
    then
      -- Checker-owned semantic goals are built by 'globalValueM': the hidden
      -- universe instance is explicit in 'VGlobal', while generated
      -- declaration-constraint proofs are not materialized in the value spine.
      -- Exact source arity authenticates this representation.
      pure arguments
    else do
      -- Values evaluated from finalized Core carry the physical erased proof
      -- prefix. Validate that complete prefix before exposing source arguments.
      guard (length proofArguments == proofCount)
      guard (all ((== Impl) . fst) proofArguments)
      guard (length semanticArguments == semanticCount)
      pure semanticArguments

equalityExplicitEndpoints :: Term -> Maybe (Term, Term)
equalityExplicitEndpoints term =
  case spineOfTerm (stripIdentityWrappers term) of
    (headTerm, arguments)
      | termHeadGlob (stripIdentityWrappers headTerm) == Just prelEqType ->
          last2 [argument | (Expl, argument) <- arguments]
    _ -> Nothing

-- | Decode an equality between a checked Bool term and a resolved prelude Bool
-- literal. The literal may occur on either side; source spelling and arbitrary
-- same-named constructors carry no authority.
booleanLiteralEqualityPayload :: Term -> Maybe (Bool, Term)
booleanLiteralEqualityPayload term =
  case spineOfTerm (stripIdentityWrappers term) of
    (headTerm, arguments)
      | termHeadGlob (stripIdentityWrappers headTerm) == Just prelEqType
      , carrier : _ <- [argument | (Impl, argument) <- arguments]
      , termHeadGlob (stripIdentityWrappers carrier) == Just prelBool
      , Just (lhs, rhs) <-
          last2 [argument | (Expl, argument) <- arguments] ->
          case (boolLiteral lhs, boolLiteral rhs) of
            (_, Just truth) -> Just (truth, lhs)
            (Just truth, _) -> Just (truth, rhs)
            _ -> Nothing
    _ -> Nothing
  where
    boolLiteral candidate =
      case stripIdentityWrappers candidate of
        CCtor constructor _ []
          | constructor == prelTrue -> Just True
          | constructor == prelFalse -> Just False
        CCtorI constructor _ _ []
          | constructor == prelTrue -> Just True
          | constructor == prelFalse -> Just False
        _ -> Nothing

-- | Retain the exact standard evidence whose overloaded operations occur in
-- a value-arithmetic certificate's checked propositions. Replay uses
-- canonical primitives, but the independent checker must still authenticate
-- the source-side operation/evidence pair instead of inferring standard
-- semantics from a member spelling.
standardArithmeticDirectProvider
  :: Term
  -> Maybe (GName, Term, Term)
standardArithmeticDirectProvider term = do
  let (headTerm, arguments) =
        spineOfTerm (stripIdentityWrappers term)
  operation <- termHeadGlob (stripIdentityWrappers headTerm)
  trait <- standardArithmeticOperationTrait operation
  carrier : dictionary : _ <-
    pure [argument | (Impl, argument) <- arguments]
  pure (trait, carrier, dictionary)

standardArithmeticOperationTrait :: GName -> Maybe GName
standardArithmeticOperationTrait operation
  | operation
      `elem`
        [ gPrel "=="
        , memberGlobal (gPrel "Eq") "=="
        ] =
      Just (gPrel "Eq")
  | operation `elem` [gPrel "<", gPrel "<="] = Just prelOrd
  | operation `elem` [prelAddOp, prelAddMethod, memberGlobal prelAdd "add"] =
      Just prelAdd
  | operation
      `elem`
        [ gPrel "*"
        , gPrel "multiply"
        , memberGlobal (gPrel "Mul") "multiply"
        ] =
      Just (gPrel "Mul")
  | operation
      `elem`
        [ gPrel "-"
        , gPrel "subtract"
        , memberGlobal (gPrel "CheckedSub") "subtract"
        ] =
      Just (gPrel "CheckedSub")
  | operation
      `elem`
        [ gPrel "/"
        , gPrel "divide"
        , memberGlobal (gPrel "CheckedDiv") "divide"
        ] =
      Just (gPrel "CheckedDiv")
  | operation
      `elem`
        [ gPrel "%"
        , gPrel "modulo"
        , memberGlobal (gPrel "CheckedMod") "modulo"
        ] =
      Just (gPrel "CheckedMod")
  | otherwise = Nothing

-- | Authenticate the operation/carrier/dictionary portion of a TypeLevel
-- comparison while retaining its operand spine for the caller. Operand
-- normalization is a separate concern: source level binders use the ordinary
-- TypeLevel bridge, while proof search consumes already-finalized Core.
typeLevelRelationSpine :: Term -> CheckM (Maybe (LevelOperatorIdentity, [(Icit, Term)]))
typeLevelRelationSpine relation = do
  aliases <- gets csLevelOperatorAliases
  case spineOfTerm (stripIdentityWrappers relation) of
    (headTerm, args)
      | Just opG <- termHeadGlob (stripIdentityWrappers headTerm)
      , Just op <- comparisonIdentity aliases opG
      , let implicitArgs = [arg | (Impl, arg) <- args]
      , typeArg : dictArg : _ <- implicitArgs
      , termHeadGlob (stripIdentityWrappers typeArg) == Just prelTypeLevel -> do
          standard <- standardTypeLevelDictionary prelOrd dictArg
          pure $ if standard then Just (op, args) else Nothing
    _ -> pure Nothing
  where
    comparisonIdentity aliases g
      | g == gPrel "<" = Just LevelOperatorLt
      | g == gPrel "<=" = Just LevelOperatorLe
      | otherwise = case Map.lookup g aliases of
          Just LevelOperatorLt -> Just LevelOperatorLt
          Just LevelOperatorLe -> Just LevelOperatorLe
          _ -> Nothing

-- | Authenticate a selected compiler-owned TypeLevel dictionary. This is the
-- common trust boundary for both solver-level operations and erased ordering
-- proofs: neither rendered member names nor a matching result type suffice.
standardTypeLevelDictionary :: GName -> Term -> CheckM Bool
standardTypeLevelDictionary trait dictionary = do
  instances <- gets csInstances
  pure $ case termHeadGlob (stripIdentityWrappers dictionary) of
    Just dictG ->
      dictG `gnameInModule` modTypeLevel
        && any
          ( \entry ->
              ieDict entry == dictG
                && ieTrait entry == trait
                && null (iePremises entry)
                && case ieHead entry of
                     [headType] -> termHeadGlob (stripIdentityWrappers headType) == Just prelTypeLevel
                     _ -> False
          )
          instances
    Nothing -> False

-- | Query the principal solution of the pending constraint set without
-- installing it.  Proof search must be order-independent, so it may observe
-- the joined solution but cannot commit a provisional lower bound before the
-- owning declaration/module boundary.
currentPrincipalLevelAssignments :: CheckM (Maybe (Map LevelMeta Level))
currentPrincipalLevelAssignments = do
  st <- get
  let prior = csLevelAssignments st
      constraints = zonkedPendingLevelConstraints prior st
  pure $ case solveLevelConstraints constraints of
    Left _ -> Nothing
    Right solution -> Just (Map.union (lsAssignments solution) prior)

-- | Infer selected metas from an explicit constraint region. This is the
-- reusable transaction-local form of 'currentPrincipalLevelAssignmentsFor':
-- ambient metas may occur as rigid parameters in the resulting assignment,
-- but constraints outside the supplied region cannot influence it.
principalLevelAssignmentsWithin
  :: Map LevelMeta Level
  -> Set LevelMeta
  -> [LevelConstraint]
  -> Maybe (Map LevelMeta Level)
principalLevelAssignmentsWithin prior requested constraints0 =
  let
      targets =
        Set.unions
          [ Set.fromList (levelMetas (substituteLevelMetas prior (LMeta meta)))
          | meta <- Set.toList requested
          ]
      constraints
        | Set.null targets = []
        | otherwise = relevantConstraintClosure targets constraints0
   in if Set.null targets
        then Just prior
        else case inferPrincipalLevelsFor targets constraints of
          SolvedPrincipal solution -> Just (Map.union solution prior)
          Unsatisfiable -> Nothing
          BlockedByUnselectedMetas -> Nothing
          NoPointwiseLeastSolution _ -> Nothing
          OutsidePortableInferenceFragment -> Nothing
  where
    relevantConstraintClosure seeds constraints =
      let go known =
            let selected =
                  [ constraint
                  | constraint <- constraints
                  , not . Set.null $
                      Set.intersection known (constraintMetas constraint)
                  ]
                known' =
                  Set.unions (known : map constraintMetas selected)
             in if known' == known then selected else go known'
       in go seeds

    constraintMetas constraint =
      Set.fromList $
        levelMetas (lcLhs constraint)
          ++ levelMetas (lcRhs constraint)
          ++ concatMap
               (\(lower, upper) -> levelMetas lower ++ levelMetas upper)
               (assumptionsList (lcAssumptions constraint))

-- | Close one compiler-created universe occurrence against the exact
-- connected constraint component established while checking it. The caller
-- decides whether to install the returned assignments; this keeps the same
-- portable principalization authority reusable by transactional proof
-- searches and by successful instance trials.
principalizeLevelOccurrence
  :: Int
  -> CheckState
  -> Set LevelMeta
  -> Term
  -> CheckM (Maybe (Map LevelMeta Level, Term))
principalizeLevelOccurrence depth baseline selected candidate = do
  zonked <- zonkTermM depth candidate
  if Set.null selected
    then pure (Just (Map.empty, zonked))
    else do
      current <- get
      let baselineIdentities =
            Set.fromList (map lcIdentity (csLevelConstraints baseline))
          localConstraints =
            [ constraint
            | constraint <- zonkedPendingLevelConstraints (csLevelAssignments current) current
            , lcIdentity constraint `Set.notMember` baselineIdentities
            ]
          principal =
            principalLevelAssignmentsWithin
              (csLevelAssignments current)
              selected
              localConstraints
      case principal of
        Nothing -> pure Nothing
        Just assignments -> do
          let localAssignments = Map.restrictKeys assignments selected
              specialized =
                zonkTermWith
                  (\_ _ -> Nothing)
                  (substituteLevelMetas localAssignments)
                  depth
                  zonked
          closed <- zonkTermM depth specialized
          pure
            ( if
                Set.null
                  ( Set.intersection
                      selected
                      (Set.fromList (levelMetasOfTerm closed))
                  )
                then Just (localAssignments, closed)
                else Nothing
            )

zonkedPendingLevelConstraints
  :: Map LevelMeta Level
  -> CheckState
  -> [LevelConstraint]
zonkedPendingLevelConstraints prior st =
  [ substituteLevelConstraintMetas prior constraint
  | constraint <- reverse (csLevelConstraints st)
  ]

-- | Canonical observation form for a checked branch condition.
--
-- Match annotations are explicitly observe-only in Core. Constructor-pattern
-- universe spines are required checkpoint evidence, but once a match has been
-- checked they cannot affect which constructor branch is selected. Fresh
-- elaboration instances of either must therefore not split one semantic
-- branch fact into distinct identities. Constructor globals, payloads,
-- binders, guards, and term arguments remain exact.
branchDecisionObservationTerm :: Term -> Term
branchDecisionObservationTerm =
  eraseObserveOnlyAnnotations
    . mapPatternConstructorUniverses (\_ _ -> [])
    . simplifyDecisionTerm

branchFactKey :: Term -> Text
branchFactKey =
  renderStructuralTermKey . branchDecisionObservationTerm

-- | Reconstruct only already-neutral values as Core syntax.  This deliberately
-- does not call 'force' or 'quote': boolean branch facts may mention recursive
-- predicates, and using them as assumptions must not evaluate those predicates.
neutralValueTerm :: Int -> Value -> Maybe Term
neutralValueTerm lvl = \case
  VRigid l sp -> neutralSpine (CVar (lvl - 1 - l)) sp
  VFlex m sp -> neutralSpine (CMeta m) sp
  VGlobI g universes sp -> neutralSpine (CGlobI g universes) sp
  VSort level -> Just (CSort level)
  VLevel level -> Just (CLevel level)
  VUniverseLift _ _ evidence inner ->
    universeLift evidence <$> neutralValueTerm lvl inner
  VLit lit -> Just (CLit lit)
  VCtorI g universes arguments ->
    CCtorI g universes Nothing
      <$> traverse
        (\argument ->
          ConstructorArg (cvaIcit argument) (cvaPayload argument) (cvaName argument)
            <$> neutralValueTerm lvl (cvaValue argument))
        arguments
  VPrim p args ->
    foldM
      (\acc a -> CApp Expl acc <$> neutralValueTerm lvl a)
      (CGlob (GName primModule p))
      args
  VAppN ic f a -> CApp ic <$> neutralValueTerm lvl f <*> neutralValueTerm lvl a
  VProjN mode e f -> CProjM mode <$> neutralValueTerm lvl e <*> pure f
  _ -> Nothing
  where
    neutralSpine hd =
      foldM
        (\acc (ic, a) -> CApp ic acc <$> neutralValueTerm lvl a)
        hd

normalizeBoolFacts :: Int -> [ScopedBoolFact] -> CheckM [(Term, Bool)]
normalizeBoolFacts d facts = do
  zonked <- zonkedBoolFacts d facts
  concat <$> forM zonked (\(tm, truth) -> do
    mtm <- transparentProofNormalize d tm
    let raw = simplifyDecisionTerm tm
        candidates = case mtm of
          Just norm | norm /= raw -> [(raw, truth), (norm, truth)]
          _ -> [(raw, truth)]
        decomposed = concatMap (uncurry (decomposeBoolFact 16)) candidates
    pure decomposed
    )

zonkedBoolFacts :: Int -> [ScopedBoolFact] -> CheckM [(Term, Bool)]
zonkedBoolFacts d facts = do
  rebased <- scopedBoolFactsAt d facts
  forM rebased $ \(term, truth) -> do
    -- Conditions are recorded before all selected evidence is necessarily
    -- settled. Zonking preserves the checked expression while making exact
    -- occurrences comparable at the later proof site.
    zonked <- zonkTermM d term
    pure (zonked, truth)

-- | Extract exactly the polarity-safe propositional consequences of the
-- standard boolean connectives (§16.4.2). A true conjunction proves both
-- conjuncts; a false disjunction refutes both disjuncts; negation flips
-- polarity. False conjunctions and true disjunctions remain atomic because
-- choosing one side would invent a fact. Resolved global identity, rather
-- than an operator spelling, is the authority for every decomposition.
decomposeBoolFact :: Int -> Term -> Bool -> [(Term, Bool)]
decomposeBoolFact fuel term truth
  | fuel <= 0 = [(term, truth)]
  | otherwise =
      case stripIdentityWrappers term of
        CThunkE body _ ->
          decomposeBoolFact (fuel - 1) body truth
        CForceE (CThunkE body _) _ ->
          decomposeBoolFact (fuel - 1) body truth
        CIf condition thenTerm elseTerm
          | truth
          , isFalseTerm elseTerm ->
              decomposeBoolFact (fuel - 1) condition True
                ++ decomposeBoolFact (fuel - 1) thenTerm True
          | not truth
          , isTrueTerm thenTerm ->
              decomposeBoolFact (fuel - 1) condition False
                ++ decomposeBoolFact (fuel - 1) elseTerm False
          | isFalseTerm thenTerm
          , isTrueTerm elseTerm ->
              decomposeBoolFact (fuel - 1) condition (not truth)
        _ -> decomposeSpine
  where
    decomposeSpine =
      case spineOfTerm (stripIdentityWrappers term) of
        (headTerm, arguments)
          | termHeadGlob (stripIdentityWrappers headTerm) == Just prelAnd
          , truth
          , Just (left, right) <- last2 [argument | (Expl, argument) <- arguments] ->
              decomposeBoolFact (fuel - 1) left True
                ++ decomposeBoolFact (fuel - 1) right True
          | termHeadGlob (stripIdentityWrappers headTerm) == Just prelOr
          , not truth
          , Just (left, right) <- last2 [argument | (Expl, argument) <- arguments] ->
              decomposeBoolFact (fuel - 1) left False
                ++ decomposeBoolFact (fuel - 1) right False
          | termHeadGlob (stripIdentityWrappers headTerm) == Just prelNot
          , [argument] <- [candidate | (Expl, candidate) <- arguments] ->
              decomposeBoolFact (fuel - 1) argument (not truth)
        _ -> [(term, truth)]

    isTrueTerm = \case
      CCtor constructor _ [] -> constructor == prelTrue
      _ -> False

    isFalseTerm = \case
      CCtor constructor _ [] -> constructor == prelFalse
      _ -> False

-- | Weaken branch facts into a descendant lexical context. A fact can only be
-- consumed at its original depth or below it; seeing it from a shallower
-- context would mean it escaped the branch/binder scope that established it,
-- so such a fact is rejected rather than guessed at.
scopedBoolFactsAt :: Int -> [ScopedBoolFact] -> CheckM [(Term, Bool)]
scopedBoolFactsAt targetDepth = fmap catMaybes . mapM rebase
  where
    rebase (ScopedBoolFact sourceDepth term truth)
      | targetDepth >= sourceDepth =
          pure (Just (shiftTerm (targetDepth - sourceDepth) 0 term, truth))
      | otherwise = pure Nothing

transparentProofNormalize :: Int -> Term -> CheckM (Maybe Term)
transparentProofNormalize d t = do
  st <- get
  if not (null (unsolvedMetasOf st t))
    then pure Nothing
    else do
      t' <- transparentProofReduce d (96 :: Int) t
      let raw = simplifyDecisionTerm t
          norm = simplifyDecisionTerm t'
      pure (if norm /= raw then Just norm else Nothing)

emptyBinderPrefix :: BinderPrefix -> Bool
emptyBinderPrefix (BinderPrefix observation quantity borrow) =
  isNothing observation && isNothing quantity && isNothing borrow

surfaceQuantityZero :: Maybe S.Quantity -> Bool
surfaceQuantityZero = \case
  Just S.QZero -> True
  _ -> False

surfaceQuantityPositive :: Maybe S.Quantity -> Bool
surfaceQuantityPositive = \case
  Just S.QOne -> True
  Just S.QAtLeastOne -> True
  _ -> False

qOf :: Maybe S.Quantity -> Q
qOf = \case
  Nothing -> QW
  Just S.QZero -> Q0
  Just S.QOne -> Q1
  Just S.QOmega -> QW
  Just S.QAtMostOne -> QLe1
  Just S.QAtLeastOne -> QGe1
  Just (S.QTerm _) -> QW -- symbolic quantities: approximated as ω

renderCoreQ :: Q -> Text
renderCoreQ = \case
  Q0 -> "0"
  Q1 -> "1"
  QW -> "ω"
  QLe1 -> "<=1"
  QGe1 -> ">=1"

renderObservationMode :: ObservationMode -> Text
renderObservationMode = \case
  Ordinary -> "ordinary"
  Parametric -> "parametric"

binderQ :: Binder -> Q
binderQ b = case bpQuantity (bPrefix b) of
  Just q -> qOf (Just q)
  Nothing
    | isJust (bpBorrow (bPrefix b)) -> QW -- borrowed reads (approximation)
    | bImplicit b -> QW
    | otherwise -> QW

-- | The recursive §11.1.2.3B parametric-kind grammar.  This is a judgment
-- over elaborated KCore values, not a source-name or quantity heuristic.
isParametricKind :: Int -> Value -> CheckM Bool
isParametricKind lvl value =
  forceM value >>= \case
    VSort _ -> pure True
    -- Formation is a derived representation fact, not part of the
    -- §11.1.2.3B parametric-kind grammar. In particular, a higher-kinded
    -- classifier inferred through a provisional application can carry an
    -- ordinary formation tag while still having the required parametric,
    -- erased binder contract.
    VPiEvidenceM Parametric _ _ Q0 False _ Nothing _ dom clo -> do
      domainOk <- isParametricKind lvl dom
      if not domainOk
        then pure False
        else clApp clo (VRigid lvl []) >>= isParametricKind (lvl + 1)
    _ -> pure False

-- | The binder's annotation with suspension sugar applied: a
-- @(thunk x : T)@ binder has type @Thunk T@ (§16.2.4).
binderTypeExpr :: Binder -> Maybe Expr
binderTypeExpr b = case (bSusp b, bType b) of
  (Just SuspThunk, Just t) ->
    Just (EApp (EVar (Name "Thunk" (bSpan b))) [ArgExplicit t])
  (Just SuspLazy, Just t) ->
    Just (EApp (EVar (Name "Need" (bSpan b))) [ArgExplicit t])
  (_, mt) -> mt

-- | Reject the superseded bounded-binder dialect @(u : TypeLevel < k)@ at
-- the shared binder boundary and recover as @(u : TypeLevel)@. Recognition
-- is gated by resolved declaration identity: a shadowed/user-defined
-- @TypeLevel@ or @<@ is an ordinary expression and receives its ordinary
-- diagnostics. Bounds in portable v1 are separate erased proof binders.
normalizeBinderDomain :: Ctx -> Binder -> Expr -> CheckM Expr
normalizeBinderDomain ctx binder domain = fst <$> normalizeBinderDomainWithRecovery ctx binder domain

normalizeBinderDomainWithRecovery :: Ctx -> Binder -> Expr -> CheckM (Expr, Bool)
normalizeBinderDomainWithRecovery ctx binder domain =
  case domain of
    EApp opHead [ArgExplicit levelTy@(EVar levelName), ArgExplicit _]
      | Just op <- operatorHeadName opHead
      , nameText op == "<"
      , nameText levelName == "TypeLevel"
      , isNothing (lookupCtx "<" ctx)
      , isNothing (lookupCtx "TypeLevel" ctx) -> do
          opIdentity <- lookupGlobalName "<"
          levelIdentity <- lookupGlobalName "TypeLevel"
          if opIdentity == Just (gPrel "<") && levelIdentity == Just prelTypeLevel
            then do
              errAt (bSpan binder) "E_UNIVERSE_LEVEL_EXPRESSION" (Just "kappa.universe.level-expression")
                "bounded level-binder syntax is not supported; bind TypeLevel and add a separate erased proof such as (@0 p : u < k) (§11.1.2.6)"
              pure (levelTy, True)
            else pure (domain, False)
    _ -> pure (domain, False)
  where
    operatorHeadName = \case
      EVar op -> Just op
      EOpRef _ op _ -> Just op
      _ -> Nothing

-- ── Elaboration ──────────────────────────────────────────────────────

-- | Verify @expr@ against an @expected0@ type and elaborate it to a core
-- 'Term'. Used wherever the context already knows the type (a typed @let@
-- body, a lambda checked against a function type). Knowing the expectation
-- lets 'check' handle forms 'infer' cannot, so it matches on the /pair/
-- @(expr, expected)@ to catch those (e.g. a lambda against a 'VPi'). Any
-- form with no rule for the @(expr, expected)@ pair falls through to
-- 'infer', inserts any still-missing implicit arguments, then 'unify's the
-- result against the expectation — the generic "switch direction" step.
-- | Recover the nominal family identity from a checked semantic value while
-- preserving explicit universe applications and proof-carrying lifts. This is
-- shared by expected-constructor selection and branch-evidence classification;
-- neither caller may infer nominal identity from source spelling.
nominalFamilyValueHead :: Value -> Maybe GName
nominalFamilyValueHead = \case
  VGlobI family _ _ -> Just family
  VGlobN family _ -> Just family
  VUniverseLift _ _ _ value -> nominalFamilyValueHead value
  VAppN _ function _ -> nominalFamilyValueHead function
  _ -> Nothing

reportParametricPromotion :: Span -> Text -> ObservationJudgment -> CheckM ()
reportParametricPromotion sp demandedConstruct judgment =
  report $
    withPayload
      ( withPayloadField "witnessOrigin" origin $
          maybe id (withPayloadField "witnessLevel" . renderLevel) level $
            withPayloadField "witnessExpression" origin $
              withPayloadField "useSite" (T.pack (show sp)) $
                withPayloadField "demandedConstructKind" demandedConstruct $
                  withPayloadField "witnessSourceKind" "binder-or-projection" $
                    withPayloadField "generatedUse" "false" $
                      withPayloadField "nearestAnnotation" origin $
                        withPayloadField "expectedCapability" "ordinary-type-code" $
                          withPayloadField "actualCapability" "parametric-type-witness" $
                            payloadKind "parametric-type-promotion"
      ) $
      diag SevError StageElaborate "E_PARAMETRIC_TYPE_PROMOTION"
        (Just "kappa.type.parametric-promotion") sp
        "a parametric observation cannot be used where ordinary observation is required (§11.1.2.3B)"
  where
    origin = ojOrigin judgment
    level = case ojClassifier judgment of
      Just (ObservationType rho) -> Just rho
      _ -> Nothing

-- | Is the value a (possibly parameterized) type former — i.e. is its
-- final codomain a universe?
finalIsSort :: Ctx -> Value -> CheckM Bool
finalIsSort ctx v0 = go (ctxLen ctx) (8 :: Int) v0
  where
    go _ 0 _ = pure False
    go lvl fuel v = do
      vf <- forceM v
      case vf of
        VSort _ -> pure True
        VPi _ _ _ _ _ clo -> clApp clo (VRigid lvl []) >>= go (lvl + 1) (fuel - 1)
        _ -> pure False

-- | Resolve a source expression only when it is a static global path:
-- an unshadowed name, an import alias member, or a fully-qualified module path.
-- This is used by semantic recognizers such as projection facets; ordinary
-- field selection remains in 'elabDot'.
staticGlobalExpr :: Ctx -> Expr -> CheckM (Maybe GName)
staticGlobalExpr ctx = \case
  EVar hn
    | Nothing <- lookupCtx (nameText hn) ctx ->
        lookupGlobalName (nameText hn)
  -- Parenthesized operator references are ordinary static declaration
  -- references.  Keeping this case here (rather than recognizing a spelling
  -- in universe-instantiation code) makes @(=).{u}@ and any user-defined
  -- operator declaration follow the same resolved-identity path as @Box.{u}@.
  EOpRef _ hn _
    | Nothing <- lookupCtx (nameText hn) ctx ->
        lookupGlobalName (nameText hn)
  EDot base (DotName member) -> do
    st <- get
    case base of
      EVar (Name alias _)
        | Nothing <- lookupCtx alias ctx
        , Just mn <- Map.lookup alias (csModuleAliases st) ->
            pure (visibleMember st mn member)
      _ -> case modulePathOf base of
        Just segs@(firstSeg : _)
          | Nothing <- lookupCtx firstSeg ctx ->
              pure (visibleMember st (ModuleName segs) member)
        _ -> pure Nothing
  EAscription e _ _ -> staticGlobalExpr ctx e
  _ -> pure Nothing
  where
    visibleMember st mn member =
      let g = GName mn (nameText member)
       in if memberVisible st mn (nameText member)
            && (Map.member g (csGlobals st) || Map.member g (csCtors st) || Map.member g (csProjections st))
            then Just g
            else Nothing
    modulePathOf = \case
      EVar (Name s _) -> Just [s]
      EDot inner (DotName (Name s _)) -> (++ [s]) <$> modulePathOf inner
      _ -> Nothing

-- | Canonicalize checked terms under the current scoped branch facts.
-- Authentication of arithmetic and Boolean heads happens before contextual
-- rewriting, so both type compatibility and proof synthesis consume exactly
-- the same local semantic authority.
canonicalizeTermsUnderCheckedBranchFacts
  :: Ctx
  -> [Term]
  -> CheckM [Term]
canonicalizeTermsUnderCheckedBranchFacts ctx terms = do
  instances <- gets csInstances
  canonicalizeTermsUnderBranchFactsWith
    24
    normalizeBoolFacts
    (canonicalizeStandardArithmeticOperations instances)
    ctx
    terms

canonicalizeTermsUnderBranchFactsWith
  :: Int
  -> (Int -> [ScopedBoolFact] -> CheckM [(Term, Bool)])
  -> (Term -> Term)
  -> Ctx
  -> [Term]
  -> CheckM [Term]
canonicalizeTermsUnderBranchFactsWith
  reductionFuel
  selectFacts
  canonicalizeStandard
  ctx
  terms = do
  let depth = ctxLen ctx
  rigidFacts <- checkedRigidFactTerms ctx
  branchFacts0 <- selectFacts depth =<< gets csBoolFacts
  let branchFacts =
        [ (canonicalizeStandard proposition, truth)
        | (proposition, truth) <- branchFacts0
        ]
      normalizeOne fuel current
        | fuel <= 0 =
            normalizeCheckedBranchFacts
              depth
              canonicalizeStandard
              branchFacts
              (canonicalizeStandard (substituteCheckedRigidFacts depth rigidFacts current))
        | otherwise = do
            let underRigidFacts =
                  substituteCheckedRigidFacts depth rigidFacts current
            underFacts <-
              normalizeCheckedBranchFacts
                depth
                canonicalizeStandard
                branchFacts
                (canonicalizeStandard underRigidFacts)
            reduced <- transparentProofReduce depth 48 underFacts
            let next =
                  canonicalizeStandard
                    (simplifyDecisionTermAt depth reduced)
            if next == current
              then pure next
              else normalizeOne (fuel - 1) next
  mapM (normalizeOne reductionFuel) terms

-- | Quote the positive constructor/index refinements established by the
-- current checked patterns.  The map key is a rigid level, not a source name;
-- negative constructor exclusions are intentionally not substitutions.
checkedRigidFactTerms :: Ctx -> CheckM (Map Int Term)
checkedRigidFactTerms ctx = do
  facts <- gets csFacts
  fmap Map.fromList . fmap catMaybes . forM (Map.toList facts) $ \case
    (level, FactIs replacement)
      | level >= 0
      , level < ctxLen ctx -> do
          term <- quoteIn ctx replacement >>= zonkTermM (ctxLen ctx)
          pure (Just (level, term))
    _ -> pure Nothing

-- | Replay positive rigid facts in Core while preserving de Bruijn scope.
-- At a node depth @d@, @CVar i@ denotes rigid level @d - 1 - i@. A quoted
-- replacement lives at the enclosing depth and is weakened only across the
-- binders traversed by this rewrite. This is the syntactic replay of the same
-- certified facts already consumed by conversion-time evaluation.
substituteCheckedRigidFacts :: Int -> Map Int Term -> Term -> Term
substituteCheckedRigidFacts enclosingDepth facts =
  mapTermWithDepth rewrite enclosingDepth
  where
    rewrite nodeDepth = \case
      CVar index
        | let level = nodeDepth - 1 - index
        , Just replacement <- Map.lookup level facts ->
            Just (shiftTerm (nodeDepth - enclosingDepth) 0 replacement)
      _ -> Nothing

-- | Normalize a term under the exact Boolean facts in the current branch.
-- Facts are already scoped, zonked, and decomposed by 'normalizeBoolFacts'.
-- Structural keys are the same collision-free Core keys used by the Boolean
-- decision procedure; no source spelling or operation name participates.
--
-- This is contextual conversion only. It does not add a global reduction
-- rule, and callers must discard every meta assignment when the enclosing
-- compatibility attempt fails.
normalizeCheckedBranchFacts
  :: Int
  -> (Term -> Term)
  -> [(Term, Bool)]
  -> Term
  -> CheckM Term
normalizeCheckedBranchFacts depth canonicalizeStandard facts term = do
  evalContext <- ec_
  pure (fixedPoint evalContext term)
  where
    fixedPoint evalContext current =
      let nodes =
            foldTermWithDepth
              (\nodeDepth node -> [(nodeDepth, node)])
              depth
              current
          agreedTruth nodeDepth node =
            case nub
              [ truth
              | (proposition, truth) <- facts
              , let delta = nodeDepth - depth
              , delta >= 0
              , let propositionAtNode =
                      shiftTerm delta 0 proposition
                    sameCheckedObservation =
                      branchDecisionObservationTerm propositionAtNode
                        == branchDecisionObservationTerm node
                    environment =
                      [ VRigid level []
                      | level <- reverse [0 .. nodeDepth - 1]
                      ]
                    propositionValue =
                      eval
                        evalContext
                        environment
                        ( branchDecisionObservationTerm
                            propositionAtNode
                        )
                    nodeValue =
                      eval
                        evalContext
                        environment
                        (branchDecisionObservationTerm node)
              , sameCheckedObservation
                  || convertible evalContext nodeDepth propositionValue nodeValue
              ] of
              [truth] -> Just truth
              _ -> Nothing
          truthByNode =
            Map.fromList
              [ ((nodeDepth, branchFactKey node), truth)
              | (nodeDepth, node) <- nodes
              , Just truth <- [agreedTruth nodeDepth node]
              ]
          rewrite nodeDepth node =
            case Map.lookup
              (nodeDepth, branchFactKey node)
              truthByNode of
              Just True -> Just (CCtorI prelTrue [] Nothing [])
              Just False -> Just (CCtorI prelFalse [] Nothing [])
              Nothing -> Nothing
          next =
            canonicalizeStandard
              ( simplifyDecisionTermAt depth
                  (mapTermWithDepth rewrite depth current)
              )
       in if next == current
            then current
            else fixedPoint evalContext next

-- | Names that occur more than once (each reported once).
duplicatesOf :: [Text] -> [Text]
duplicatesOf ns = nub [n | n <- ns, length (filter (== n) ns) > 1]

-- visibility of a member of another module (§8.5): only exported names
-- are accessible from outside the defining module
memberVisible :: CheckState -> ModuleName -> Text -> Bool
memberVisible st mn nm =
  mn == csModule st
    || case Map.lookup mn (csModuleExports st) of
      Just ex -> nm `elem` ex
      Nothing -> True -- prelude and unknown modules: unrestricted

-- | §2.8.4: the manifest value of a receiver term — resolved through
-- local definientia, module-level lets without widening signatures,
-- record projections of such, and direct (immediately-used) results.
-- A binding under a widening signature forgets static-object identity.
manifestValue :: Ctx -> Term -> CheckM (Maybe Value)
manifestValue ctx tm = case tm of
  CGlob g -> do
    st <- get
    if Map.member g (csManifest st) || Map.member g (csDatas st)
      then case Map.lookup g (csGlobals st) >>= gdValue of
        Just v -> Just <$> forceM v
        Nothing -> pure (Just (VGlobN g []))
      else pure Nothing
  CProj t f -> do
    mv <- manifestValue ctx t
    -- §13.2.10: transparent members of a sealed package stay manifest;
    -- opaque members forget static-object identity
    let unwrap v =
          forceM v >>= \case
            VSealV ls r | f `notElem` ls -> unwrap r
            v' -> pure v'
    mv' <- traverse unwrap mv
    case mv' of
      Just (VRecordV fs) | Just v <- lookup f fs -> Just <$> forceM v
      _ -> pure Nothing
  -- P0.4: a fixed-offset projection manifests by NAME exactly like CProj (the
  -- catch-all's eager evalIn would wrongly manifest a non-manifest projection).
  CProjAt t f _ -> do
    mv <- manifestValue ctx t
    let unwrap v =
          forceM v >>= \case
            VSealV ls r | f `notElem` ls -> unwrap r
            v' -> pure v'
    mv' <- traverse unwrap mv
    case mv' of
      Just (VRecordV fs) | Just v <- lookup f fs -> Just <$> forceM v
      _ -> pure Nothing
  CVar i -> case drop i (ctxEnv ctx) of
    (v : _) -> do
      v' <- forceM v
      pure $ case v' of
        VRigid {} -> Nothing -- an opaque binder, not a let definiens
        _ -> Just v'
    [] -> pure Nothing
  _ -> Just <$> (evalIn ctx tm >>= forceM)

-- | Resolve the contextual module declaration used by both @module M@ and
-- @moduleSig M@. Module aliases are lexical declarations; an unaliased
-- one-component module name is accepted only when its interface is present.
resolveModuleObjectName :: CheckState -> Text -> Maybe ModuleName
resolveModuleObjectName st name =
  Map.lookup name (csModuleAliases st)
    <|> let direct = ModuleName [name]
         in if direct == csModule st || Map.member direct (csModuleExports st)
              then Just direct
              else Nothing

resolveCtor :: Ctx -> CtorRef -> CheckM (Maybe (GName, CtorInfo))
resolveCtor ctx reference@(CtorRef _ n) = do
  resolved <- resolveCtorWithoutDiagnostic ctx reference
  when (isNothing resolved) $
    errAt (nameSpan n) "E_NAME_UNRESOLVED" (Just "kappa.name.unresolved")
      ("unresolved constructor '" <> nameText n <> "'")
  pure resolved

-- | Resolve a constructor from checked lexical/module identity without
-- committing to a constructor-only diagnostic. Ambiguous @let C p... = rhs@
-- syntax uses this at the checker boundary: absence means the ordinary named
-- function reading, while a result selects the constructor-pattern reading.
resolveCtorWithoutDiagnostic
  :: Ctx
  -> CtorRef
  -> CheckM (Maybe (GName, CtorInfo))
resolveCtorWithoutDiagnostic ctx (CtorRef mqual n) = do
  st <- get
  let candidates = case mqual of
        Nothing ->
          map fst (unqualifiedConstructorCandidates st n)
        Just q ->
          [ ctorG
          | (dg, di) <- Map.toList (csDatas st)
          , sourceNameResolvesTo st dg (nameText q)
          , inScope st dg
          , ctorG <- diCtors di
          , sourceNameResolvesTo st ctorG (nameText n)
          ]
  case candidates of
    (g : _) -> do
      pure ((,) g <$> Map.lookup g (csCtors st))
    [] -> do
      -- §2.8.4/§7.6: a rebound type object preserves its identity for
      -- dotted lookup — the qualifier may be a local or module binding
      -- whose manifest value is a data type constructor
      mDataG <- case mqual of
        Just q -> do
          mv <- case lookupCtx (nameText q) ctx of
            Just (i, _) -> manifestValue ctx (CVar i)
            Nothing -> do
              mg <- lookupGlobalName (nameText q)
              case mg of
                Just g -> manifestValue ctx (CGlob g)
                Nothing -> pure Nothing
          case mv of
            Just (VGlobN dg []) | Map.member dg (csDatas st) -> pure (Just dg)
            _ -> pure Nothing
        Nothing -> pure Nothing
      case mDataG of
        Just dg
          | Just di <- Map.lookup dg (csDatas st)
          , (ctorG : _) <- [c | c <- diCtors di, gnameText c == nameText n] ->
              pure ((,) ctorG <$> Map.lookup ctorG (csCtors st))
        _ -> pure Nothing
  where
    inScope = constructorInScope

-- | Resolve an unqualified constructor spelling to checked constructor
-- identities without emitting a diagnostic. Pattern parsing deliberately
-- leaves a bare lowercase atom as 'PVar'; this lookup is the semantic
-- disambiguation boundary that lets ordinary lowercase constructors (notably
-- the standard @refl@) enter the same constructor-pattern path as uppercase
-- constructors. Callers must make decisions from the returned 'GName' and
-- 'CtorInfo', never from the spelling alone.
unqualifiedConstructorCandidates
  :: CheckState
  -> Name
  -> [(GName, CtorInfo)]
unqualifiedConstructorCandidates state name =
  case resolvedIdentity >>= \identity -> (identity,) <$> Map.lookup identity (csCtors state) of
    Just candidate -> [candidate]
    Nothing -> []
  where
    source = nameText name
    own = GName (csModule state) source
    resolvedIdentity =
      Map.lookup source (csLocalDeclScope state)
        <|> (own <$ guard (Map.member own (csGlobals state) || Map.member own (csCtors state)))
        <|> Map.lookup source (csScope state)

sourceNameResolvesTo :: CheckState -> GName -> Text -> Bool
sourceNameResolvesTo state identity source =
  gnameText identity == source
    || Map.lookup source (csLocalDeclScope state) == Just identity

monadResultType :: Value -> Value -> Maybe Value
monadResultType mTy a = case mTy of
  VGlobI g universes args ->
    Just (VGlobI g universes (args ++ [(Expl, a)]))
  VFlex m args -> Just (VFlex m (args ++ [(Expl, a)]))
  VRigid l args -> Just (VRigid l (args ++ [(Expl, a)]))
  _ -> Nothing

-- | Decompose one already-forced application of a first-order monad carrier.
-- The carrier retains its complete checked prefix (including generated
-- universe and evidence arguments); only the final explicit result argument
-- is removed. This is the inverse of 'monadResultType'.
monadActionViewValue :: Value -> Maybe (Value, Value)
monadActionViewValue = \case
  VGlobI g universes args
    | Just (pre, (Expl, a)) <- unsnoc args ->
        Just (VGlobI g universes pre, a)
  VFlex m args
    | Just (pre, (Expl, a)) <- unsnoc args ->
        Just (VFlex m pre, a)
  VRigid l args
    | Just (pre, (Expl, a)) <- unsnoc args ->
        Just (VRigid l pre, a)
  _ -> Nothing
  where
    unsnoc [] = Nothing
    unsnoc [x] = Just ([], x)
    unsnoc (x : xs) = do
      (pre, lastArg) <- unsnoc xs
      Just (x : pre, lastArg)

monadRefReadAction :: Term -> Term -> Term -> Term
monadRefReadAction dictTm aTm refTm =
  CApp Expl (CApp Impl (CProjM Ordinary dictTm "readRef") aTm) refTm

collectRefFacets :: Data a => a -> Set Text
collectRefFacets x =
  case (cast x :: Maybe Expr) of
    Just (ERefFacet n _) -> Set.singleton (nameText n)
    _ -> Set.unions (gmapQ collectRefFacets x)

-- | Does an expression contain a monadic splice `!` that 'liftBangsExpr' would
-- lift in the CURRENT do-scope?  Used to decide whether an @if@/@match@ branch
-- must be hoisted (branch-local sequencing).  It does NOT descend into nested
-- `do`-blocks or lambdas: a `!` there belongs to that inner monadic scope, not
-- this one (§18.3.1: `!` does not cross lambda/do/quote/type boundaries).
exprHasBang :: Expr -> Bool
exprHasBang = go
  where
    go = \case
      EBang {} -> True
      EApp f as -> go f || any goA as
      EStringLit _ parts _ -> any (go . ipExpr) parts
      ERecordLit items _ -> any goRecItem items
      ERecordPatch base items _ -> go base || any goPatchItem items
      EQDot e _ -> go e
      EOpChain elems -> any goOpElem elems
      EElvis l r _ -> go l || go r
      EIf alts mels _ -> any (\(c, t) -> go c || go t) alts || maybe False go mels
      EMatch s cs _ -> go s || any goMatchCase cs
      EAscription e _ _ -> go e
      ETuple es _ -> any go es
      EListLit es _ -> any go es
      ESetLit es _ -> any go es
      EMapLit kvs _ -> any (\(k, v) -> go k || go v) kvs
      EDot e _ -> go e
      EIs e _ -> go e
      EThunk {} -> False
      ELazy {} -> False
      EForce e _ -> go e
      ESeal e _ _ -> go e
      ESealExists ws e _ _ -> any (go . snd) ws || go e
      ETry e excepts mfin _ ->
        go e || any goExcept excepts || maybe False go mfin
      ETryMatch e cases excepts mfin _ ->
        go e || any goMatchCase cases || any goExcept excepts || maybe False go mfin
      -- a `!` under a lambda / nested do / quote belongs to that inner scope.
      _ -> False
    goA = \case
      ArgExplicit e -> go e
      ArgImplicit e -> go e
      ArgInout e _ -> go e
      ArgNamedBlock fields _ -> any (maybe False go . snd) fields
    goRecItem (RecItem _ _ me) = maybe False go me
    goPatchItem = \case
      PatchUpdate _ (PatchValue e) -> go e
      PatchExtend _ e -> go e
      PatchSection recv e -> go recv || go e
      PatchPun _ -> False
    goOpElem = \case
      ChainOperand e -> go e
      ChainOp _ -> False
    goMatchCase = \case
      MatchCase _ mg b _ -> maybe False go mg || go b
      MatchImpossible _ -> False
    goExcept (ExceptCase _ mg b _) = maybe False go mg || go b

-- | Does an expression contain a mutable-variable current-value occurrence for
-- the supplied do-elaboration context?  The shadow set records binders whose
-- source names override outer mutable bindings.
exprHasCurrentRead :: Ctx -> Expr -> Bool
exprHasCurrentRead ctx = go Set.empty
  where
    current shadow n =
      nameText n `Set.notMember` shadow
        && maybe False (isJust . ceVarInfo . snd) (lookupCtx (nameText n) ctx)
    go shadow = \case
      EVar n -> current shadow n
      ERefFacet {} -> False
      EVarRead {} -> False
      EApp f as -> go shadow f || any (goArg shadow) as
      EStringLit _ parts _ -> any (go shadow . ipExpr) parts
      ERecordLit items _ -> any (goRecItem shadow) items
      ERecordPatch base items _ -> go shadow base || any (goPatchItem shadow) items
      EReceiverSection {} -> False
      ESectionLeft {} -> False
      ESectionRight {} -> False
      EQDot e _ -> go shadow e
      EOpChain elems -> any (goOpElem shadow) elems
      EElvis l r _ -> go shadow l || go shadow r
      ELet binds body _ -> goLetBinds shadow binds body
      EBlock decls mres _ -> goBlock shadow decls mres
      EIf alts mels _ -> any (\(c, t) -> go shadow c || go shadow t) alts || maybe False (go shadow) mels
      EMatch s cs _ -> go shadow s || any (goCase shadow) cs
      EHandle _ label scrut cases _ -> go shadow label || go shadow scrut || any (goHandler shadow) cases
      EAscription e _ _ -> go shadow e
      ETuple es _ -> any (go shadow) es
      EListLit es _ -> any (go shadow) es
      ESetLit es _ -> any (go shadow) es
      EMapLit kvs _ -> any (\(k, v) -> go shadow k || go shadow v) kvs
      EDot e _ -> go shadow e
      EIs e _ -> go shadow e
      EThunk {} -> False
      ELazy {} -> False
      EForce e _ -> go shadow e
      ESeal e _ _ -> go shadow e
      EOpenExists pkg ws pat body _ ->
        let shadow' = Set.unions [shadow, Set.fromList (map nameText ws), Set.fromList (map nameText (surfPatVars pat))]
         in go shadow pkg || go shadow' body
      ESealExists ws e _ _ -> any (go shadow . snd) ws || go shadow e
      EComprehension _ clauses yield _ -> goComp shadow clauses yield
      ETry e excepts mfin _ ->
        go shadow e || any (goExcept shadow) excepts || maybe False (go shadow) mfin
      ETryMatch e cases excepts mfin _ ->
        go shadow e || any (goCase shadow) cases || any (goExcept shadow) excepts || maybe False (go shadow) mfin
      EVariant arms mtail _ ->
        any (go shadow . vaExpr) arms || maybe False (go shadow) mtail
      EBang {} -> True
      -- Nested do/lambda/quote/type-like forms own their own lifting context or
      -- are no-read positions (§18.3.1).
      _ -> False
    goArg shadow = \case
      ArgExplicit e -> go shadow e
      ArgImplicit e -> go shadow e
      ArgInout _ _ -> False
      ArgNamedBlock fields _ -> any (maybe False (go shadow) . snd) fields
    goLetBinds shadow [] body = go shadow body
    goLetBinds shadow (LetBind _ _ pat _ rhs _ : rest) body =
      go shadow rhs || goLetBinds (Set.union shadow (Set.fromList (map nameText (surfPatVars pat)))) rest body
    goBlock shadow [] mres = maybe False (go shadow) mres
    goBlock shadow (d : ds) mres = case d of
      DLet _ ld _ ->
        let hasBody
              | null (ldBinders ld) = go shadow (ldBody ld)
              | otherwise = False
            shadow' = Set.union shadow (Set.fromList (map nameText (letDefVars ld)))
         in hasBody || goBlock shadow' ds mres
      _ -> goBlock shadow ds mres
    letDefVars ld =
      maybeToList (ldName ld)
        ++ maybe [] surfPatVars (ldPattern ld)
    goRecItem shadow (RecItem _ _ me) = maybe False (go shadow) me
    goPatchItem shadow = \case
      PatchUpdate _ (PatchValue e) -> go shadow e
      PatchExtend _ e -> go shadow e
      PatchSection recv e -> go shadow recv || go shadow e
      PatchPun _ -> False
    goOpElem shadow = \case
      ChainOperand e -> go shadow e
      ChainOp _ -> False
    goCase shadow = \case
      MatchCase p g b _ ->
        let shadow' = Set.union shadow (Set.fromList (map nameText (surfPatVars p)))
         in maybe False (go shadow') g || go shadow' b
      MatchImpossible _ -> False
    goHandler shadow = \case
      HandlerReturn p b _ ->
        let shadow' = Set.union shadow (Set.fromList (map nameText (surfPatVars p)))
         in go shadow' b
      HandlerOp _ ps k b _ ->
        let shadow' = Set.unions (shadow : Set.singleton (nameText k) : map (Set.fromList . map nameText . surfPatVars) ps)
         in go shadow' b
    goExcept shadow (ExceptCase p g b _) =
      let shadow' = Set.union shadow (Set.fromList (map nameText (surfPatVars p)))
       in maybe False (go shadow') g || go shadow' b
    goComp shadow clauses yield =
      let (hit, shadow') = foldl goClause (False, shadow) clauses
       in hit || goYield shadow' yield
    goClause (hit, shadow) = \case
      S.CFor _ _ pat src _ ->
        (hit || go shadow src, Set.union shadow (Set.fromList (map nameText (surfPatVars pat))))
      S.CLet _ pat _ rhs _ ->
        (hit || go shadow rhs, Set.union shadow (Set.fromList (map nameText (surfPatVars pat))))
      S.CIf e -> (hit || go shadow e, shadow)
      S.COrderBy keys _ -> (hit || any (go shadow . snd) keys, shadow)
      S.CSkip e _ -> (hit || go shadow e, shadow)
      S.CTake e _ -> (hit || go shadow e, shadow)
      S.CDistinct me _ -> (hit || maybe False (go shadow) me, shadow)
      S.CGroupBy key aggs into _ ->
        ( hit || go shadow key || any (\(_, e, mu) -> go shadow e || maybe False (go shadow) mu) aggs
        , Set.insert (nameText into) shadow
        )
      S.CJoin _ pat src on into _ ->
        ( hit || go shadow src || go shadow on
        , Set.unions [shadow, Set.fromList (map nameText (surfPatVars pat)), maybe Set.empty (Set.singleton . nameText) into]
        )
    goYield shadow = \case
      YieldExpr e -> go shadow e
      YieldPair k v -> go shadow k || go shadow v

-- | The runtime-mode evaluation context for elaboration-time
-- execution (§21.8, §30.2.4): every global unfolds.
ecRT_ :: CheckM EvalCtx
ecRT_ = gets (\st -> EvalCtx (Globals (csGlobals st)) (csMetas st) True (csFacts st))

forceRT :: Value -> CheckM Value
forceRT v = do
  ec <- ecRT_
  pure (force ec v)

-- | §21.6: delaborate a first-order TYPE term back to surface syntax (for
-- 'typeOfSyntax'). Covers the type-expression forms — universes, type
-- constructors/names, type application (implicit args inferred away),
-- saturated type-level constructors, and de Bruijn variables (resolved
-- through the binder stack, then the context). A form that is not a
-- first-order type expression yields Nothing, so the query fails gracefully
-- rather than fabricating syntax.
delaborateType :: Ctx -> Span -> Term -> Maybe Expr
delaborateType ctx dsp = delaborateTypeWithEnv ctx dsp []

-- | Delaborate a checked type under an explicitly named synthetic binder
-- environment. Compiler-owned declaration generators use this to abstract a
-- selected semantic field while still sending the resulting ordinary syntax
-- back through the normal checker. The environment is de Bruijn order
-- (nearest binder first), matching 'ctxEntries'.
delaborateTypeWithEnv :: Ctx -> Span -> [Text] -> Term -> Maybe Expr
delaborateTypeWithEnv ctx dsp initialEnv = go initialEnv
  where
    nm t = Name t dsp
    go env tm = case tm of
      CSort _ -> Just (EVar (nm "Type"))
      CGlob g -> Just (EVar (nm (gnameText g)))
      CGlobal g _ -> Just (EVar (nm (gnameText g)))
      CUniverseLift _ _ _ inner -> go env inner
      CSchemaLift _ _ _ _ _ _ _ _ inner -> go env inner
      CVar i
        | i < length env -> Just (EVar (nm (env !! i)))
        | otherwise -> case drop (i - length env) (ctxEntries ctx) of
            (e : _) -> Just (EVar (nm (ceName e)))
            [] -> Nothing
      CLit (LitInt value) -> Just (EIntLit value Nothing dsp)
      CLit (LitDouble value) -> Just (EFloatLit value Nothing dsp)
      CApp Impl f _ -> go env f
      CApp Expl f a -> do
        fE <- go env f
        aE <- go env a
        pure (EApp fE [ArgExplicit aE])
      CPiEvidenceM mode _ ic q borrowed binderName _ _ domain codomain -> do
        domainE <- go env domain
        let surfaceName
              | binderName == "_" = "__discarded" <> T.pack (show (length env))
              | otherwise = binderName
            binder =
              Binder
                { bImplicit = ic == Impl
                , bPrefix =
                    BinderPrefix
                      (case mode of
                         Ordinary -> Nothing
                         Parametric -> Just Parametric)
                      (Just (surfaceQuantity q))
                      (if borrowed then Just (BorrowMark Nothing) else Nothing)
                , bSusp = Nothing
                , bReceiver = NoReceiver
                , bInout = False
                , bName = Just (nm surfaceName)
                , bUnitBinder = False
                , bType = Just domainE
                , bDefault = Nothing
                , bSpan = dsp
                }
        EArrow binder <$> go (surfaceName : env) codomain
      CCtor g _ args -> do
        argEs <- mapM (go env) args
        pure (foldl (\acc e -> EApp acc [ArgExplicit e]) (EVar (nm (gnameText g))) argEs)
      CRecordTQ fields -> ERecordType <$> recordFields env fields <*> pure Nothing <*> pure dsp
      _ -> Nothing

    recordFields _ [] = Just []
    recordFields env (field : rest) = do
      fieldType <- go env (rfType field)
      later <- recordFields (rfName field : env) rest
      let mode =
            case rfMode field of
              Ordinary -> Nothing
              Parametric -> Just Parametric
          prefix =
            BinderPrefix
              mode
              (Just (surfaceQuantity (rfQ field)))
              Nothing
      pure
        ( RecTypeField
            False
            False
            prefix
            Nothing
            (nm (rfName field))
            fieldType
            : later
        )

    surfaceQuantity = \case
      Q0 -> S.QZero
      Q1 -> S.QOne
      QW -> S.QOmega
      QLe1 -> S.QAtMostOne
      QGe1 -> S.QAtLeastOne

-- | Surface pattern variables, in binding order.
surfPatVars :: Pattern -> [Name]
surfPatVars = \case
  PWild _ -> []
  PVar n -> [n]
  PLit _ _ -> []
  PAs n p -> n : surfPatVars p
  PCtor _ ps _ -> concatMap surfPatVars ps
  PCtorNamed _ fs _ -> concatMap surfPatVars [p | (_, Just p) <- fs]
  PActive _ _ p _ -> surfPatVars p
  PTuple ps _ -> concatMap surfPatVars ps
  PUnit _ -> []
  PRecord fs mrest _ ->
    concatMap (\(_, n, mp) -> maybe [n] surfPatVars mp) fs
      ++ [n | Just (PatRestBind n) <- [mrest]]
  PTyped p _ _ -> surfPatVars p
  POr ps _ -> case ps of
    (p : _) -> surfPatVars p
    [] -> []
  POpChain p chain _ -> surfPatVars p ++ concatMap (surfPatVars . snd) chain
  PVariant mb _ _ mrest _ -> maybe [] pure mb ++ maybe [] pure mrest

-- | The source declaration interface used while a global's universe schema is
-- still provisional. A type alias exposes its manifest type value in addition
-- to the classifier stored in 'gdType'. Generated trait dictionaries and
-- member declarations own separate schemas and are deliberately excluded.
-- Deriving an early spine from 'gdType' alone makes aliases whose universes
-- occur only in their definiens appear monomorphic until it is too late to
-- repair retained uses.
globalUniverseInterfaceTerms :: CheckState -> GName -> GlobalDef -> [Term]
globalUniverseInterfaceTerms st global definition =
  globalCoreType ec definition
    : manifestTerms ++ effectTerms ++ instanceTerms
  where
    ec = ecOf st
    manifestTerms
      | global `Set.member` csUniverseInterfaceValues st =
          maybe [] (pure . quote ec 0) (gdValue definition)
      | otherwise = []
    effectTerms = effectUniverseInterfaceTerms st global
    -- The normalized instance head and premises are part of the dictionary's
    -- public declaration identity (§14.3.2). NbE-quoting 'gdType' preserves
    -- their ordinary type shape but deliberately erases 'CUniverseLift'
    -- evidence. The instance table is therefore the authority for classifier
    -- metas introduced by cumulative head arguments; omitting it lets those
    -- occurrence choices escape principalization and later be mistaken for
    -- declaration-local parameters.
    instanceTerms = instanceUniverseInterfaceTerms st global

globalCoreType :: EvalCtx -> GlobalDef -> Term
globalCoreType ec definition =
  fromMaybe (quote ec 0 (gdType definition)) (gdCoreType definition)

instanceUniverseInterfaceTerms :: CheckState -> GName -> [Term]
instanceUniverseInterfaceTerms st global =
  Map.findWithDefault [] global (csInstanceUniverseInterfaces st)

setCheckInstances :: [InstanceEntry] -> CheckState -> CheckState
setCheckInstances entries st =
  st
    { csInstances = entries
    , csInstancesByTrait =
        Map.map (sortOn ieDict) $
          Map.fromListWith (++)
            [ (ieTrait entry, [entry])
            | entry <- entries
            ]
    , csInstanceUniverseInterfaces =
        Map.fromListWith
          (flip (++))
          [ ( ieDict entry
            , map CSort (ieTraitUniverses entry)
                ++ iePremises entry
                ++ ieHead entry
            )
          | entry <- entries
          ]
    }

-- | A source type alias exposes its defining value as part of the static
-- declaration interface. Levels occurring only in that value still need a
-- declaration schema even when the outer classifier itself is @Type0@.
-- Identity is recorded during alias elaboration, so type-producing ordinary
-- functions cannot be mistaken for interface equations.
globalValueIsUniverseInterface :: Set GName -> GName -> GlobalDef -> Bool
globalValueIsUniverseInterface aliases global definition =
  global `Set.member` aliases && isJust (gdValue definition)

constraintLevelMetas :: LevelConstraint -> Set LevelMeta
constraintLevelMetas constraint =
  Set.fromList (levelMetas (lcLhs constraint) ++ levelMetas (lcRhs constraint))

-- | Treat each constraint's metavariables as one hyperedge. A star is enough
-- to preserve hypergraph connectivity and avoids materializing a quadratic
-- clique for constraints with several metas.
levelMetaAdjacency :: [Set LevelMeta] -> Map LevelMeta (Set LevelMeta)
levelMetaAdjacency =
  Map.fromListWith Set.union . concatMap connect
  where
    connect metas =
      case Set.minView metas of
        Nothing -> []
        Just (pivot, rest) ->
          (pivot, rest)
            : [ (meta, Set.singleton pivot)
              | meta <- Set.toList rest
              ]

reachableLevelMetas
  :: Map LevelMeta (Set LevelMeta)
  -> Set LevelMeta
  -> Set LevelMeta
reachableLevelMetas adjacency roots = go roots roots
  where
    go visited frontier
      | Set.null frontier = visited
      | otherwise =
          let neighbours =
                Set.unions
                  [ Map.findWithDefault Set.empty meta adjacency
                  | meta <- Set.toList frontier
                  ]
              fresh = Set.difference neighbours visited
           in go (Set.union visited fresh) fresh

-- | Connected components of the selected-meta constraint graph. Unselected
-- metas remain available as rigid dependencies inside each component, but do
-- not connect otherwise independent occurrence choices merely because those
-- occurrences specialize the same declaration parameter.
selectedConstraintGroups
  :: Set LevelMeta
  -> [LevelConstraint]
  -> [(Set LevelMeta, [LevelConstraint])]
selectedConstraintGroups selected constraints =
  [ (component, reverse (Map.findWithDefault [] componentId groupedReversed))
  | (componentId, component) <- zip [0 :: Int ..] components
  ]
  where
    entries =
      [ (constraint, Set.intersection selected (constraintLevelMetas constraint))
      | constraint <- constraints
      ]
    adjacency = levelMetaAdjacency (map snd entries)
    components = go selected
    componentOf =
      Map.fromList
        [ (meta, componentId)
        | (componentId, component) <- zip [0 :: Int ..] components
        , meta <- Set.toList component
        ]
    groupedReversed =
      List.foldl'
        (\grouped (constraint, metas) ->
           case Set.lookupMin metas >>= (`Map.lookup` componentOf) of
             Nothing -> grouped
             Just componentId ->
               Map.insertWith (++) componentId [constraint] grouped)
        Map.empty
        entries
    go remaining
      | Set.null remaining = []
      | otherwise =
          let component =
                reachableLevelMetas adjacency (Set.singleton (Set.findMin remaining))
           in component : go (Set.difference remaining component)

-- | Instantiate every constraint of a still-provisional declaration at each
-- recorded reference. This is the constraint half of fresh telescope
-- specialization: substituting only the callee type loses relationships such
-- as the payload lower bound in @List A : Type u@ and lets a caller invent an
-- unrelated schema parameter for the result classifier.
materializeProvisionalUniverseConstraintsFor :: Set GName -> CheckM ()
materializeProvisionalUniverseConstraintsFor owners = do
  occurrenceIds <- gets $ \state ->
    Set.unions
      [ Map.findWithDefault
          Set.empty
          owner
          (csProvisionalUniverseInstantiationsByOwner state)
      | owner <- Set.toList owners
      ]
  materializeProvisionalUniverseConstraints occurrenceIds

materializeProvisionalUniverseConstraints
  :: Set Int
  -> CheckM ()
materializeProvisionalUniverseConstraints occurrenceIds = do
  st <- get
  let occurrences =
        [ occurrence
        | identity <- Set.toAscList occurrenceIds
        , Just occurrence <- [Map.lookup identity (csProvisionalUniverseInstantiations st)]
        , not (puiConstraintsMaterialized occurrence)
        ]
  forM_ occurrences $ \occurrence -> do
    current <- get
    let assignments = csLevelAssignments current
    let sourceSet = Set.fromList (puiSourceMetas occurrence)
        owner = puiOwner occurrence
        ownerSet =
          Set.insert owner
            ( maybe
                Set.empty
                (Set.fromList . diCtors)
                (Map.lookup owner (csDatas current))
            )
        -- The dependency SCC has already selected its principal assignment.
        -- Instantiate that solved judgment, not the stale pre-solve metas
        -- retained in the module-wide constraint log. Otherwise a minimized
        -- callee position is freshened as a new caller choice and can survive
        -- projection as an unrelated residual.
        ownedConstraints =
          map
            (substituteLevelConstraintMetas assignments)
            (levelConstraintsOwnedBy current ownerSet)
        internalMetas =
          Set.toAscList . Set.difference
            ( Set.fromList
                [ meta
                | constraint <- ownedConstraints
                , meta <- levelMetas (lcLhs constraint) ++ levelMetas (lcRhs constraint)
                ]
            ) $
            sourceSet
    freshInternal <- replicateM (length internalMetas) freshLevelInstantiationMeta
    let substitution =
          Map.fromList
            ( zip (puiSourceMetas occurrence) (puiFreshLevels occurrence)
                ++ zip internalMetas freshInternal
            )
        substitute = substituteLevelMetas substitution
        substituteAssumptions =
          foldr
            (\(lower, upper) -> insertAssumption (substitute lower) (substitute upper))
            emptyAssumptions
            . assumptionsList
        instantiatedSourceImage sourceMeta =
          substitute
            (normalizeLevel (substituteLevelMetas assignments (LMeta sourceMeta)))
    specializationIds <-
      fmap concat . forM (zip (puiSourceMetas occurrence) (puiFreshLevels occurrence)) $
      \(sourceMeta, freshLevel) -> do
        let image = instantiatedSourceImage sourceMeta
        if normalizeLevel freshLevel == normalizeLevel image
          then pure []
          else do
            -- The source image belongs to a still-provisional declaration
            -- SCC. Record specialization as an equality judgment; assigning
            -- the fresh occurrence meta here would install a choice before
            -- the callee's principal telescope is known and could later
            -- require revision.
            let origin =
                  ConstraintOrigin
                    ("principal universe specialization of " <> gnameText owner)
                    "global reference"
                insert =
                  insertProvisionalLevelConstraintOwned
                    (puiIdentity occurrence)
                    (puiConsumer occurrence)
                    emptyAssumptions
                    origin
            sequence [insert freshLevel image, insert image freshLevel]
    copiedIds <-
      forM ownedConstraints $ \constraint ->
        insertProvisionalLevelConstraintOwned
          (puiIdentity occurrence)
          (puiConsumer occurrence)
          (substituteAssumptions (lcAssumptions constraint))
          (lcOrigin constraint)
          (substitute (lcLhs constraint))
          (substitute (lcRhs constraint))
    let materializedIds = Set.fromList (specializationIds ++ copiedIds)
    modify' $ \state ->
      state
        { csProvisionalUniverseInstantiations =
            Map.adjust
              (\candidate ->
                 candidate
                   { puiConstraintsMaterialized = True
                   , puiMaterializedConstraintIds =
                       Set.union
                         materializedIds
                         (puiMaterializedConstraintIds candidate)
                   })
              (puiIdentity occurrence)
              (csProvisionalUniverseInstantiations state)
        }

-- | Classify the universe occurrences in one declaration interface as required
-- by §11.1.3. Parameter domains expose reusable universe choices and therefore
-- generalize. The terminal sort is the declaration/result classifier and is
-- minimized. A meta occurring in both sets remains generalizable unless the
-- constraint solver has already determined it uniquely.
declarationUniverseRoles :: Term -> DeclarationUniverseRoles
declarationUniverseRoles = go
  where
    go = \case
      CPiM _ _ _ _ _ domain codomain ->
        DeclarationUniverseRoles
          (Set.fromList (levelMetasOfTerm domain))
          Set.empty
          <> go codomain
      CUniverseLift _ _ _ term -> go term
      CSort level ->
        DeclarationUniverseRoles Set.empty (Set.fromList (levelMetas level))
      term ->
        DeclarationUniverseRoles
          (Set.fromList (levelMetasOfTerm term))
          Set.empty

-- | Recover the owning trait's universe occurrence from a generated member
-- accessor type. The accessor ABI is structural: after any generated
-- constraint binders and the owning trait's ordinary parameter telescope, the
-- next domain is the evidence dictionary. Its exact global identity, not a
-- source spelling, authenticates the prefix.
traitMemberOwnerUniverseMetas :: CheckState -> GName -> Term -> [LevelMeta]
traitMemberOwnerUniverseMetas state accessor accessorType =
  case Map.lookup accessor (csTraitMemberOwners state) of
    Nothing -> []
    Just owner ->
      case
          Map.lookup owner (csTraits state)
            >>= \info -> dictionaryDomain (tiParamCount info) accessorType
        of
        Nothing -> []
        Just domain ->
          case spineOfTerm domain of
            (CGlobal actualOwner universes, _)
              | actualOwner == owner -> nub (concatMap levelMetas universes)
            _ -> []
  where
    dictionaryDomain remaining = \case
      CPiEvidenceM _ _ _ _ _ _ assumption _ _ codomain
        | isJust assumption -> dictionaryDomain remaining codomain
      CPiEvidenceM _ _ _ _ _ _ _ _ domain codomain
        | remaining > 0 -> dictionaryDomain (remaining - 1) codomain
        | otherwise -> Just domain
      _ -> Nothing

-- | Run one header/body phase with an isolated named-hole map. The close
-- action runs before restoring the caller's map, so it can either diagnose a
-- completed declaration or retain a signature's obligations for its matching
-- body.
withNamedHoleScope
  :: Map Text NamedHole
  -> CheckM ()
  -> CheckM a
  -> CheckM a
withNamedHoleScope initial close action = do
  saved <- gets csHoles
  modify' $ \st -> st {csHoles = initial}
  result <- action
  close
  modify' $ \st -> st {csHoles = saved}
  pure result

ownName :: Name -> CheckM GName
ownName n = do
  st <- get
  pure (GName (csModule st) (nameText n))

-- | Does the de Bruijn variable @v@ occur anywhere in a term (accounting
-- for binders that shift it)?
mentionsVar :: Int -> Term -> Bool
mentionsVar = go
  where
    go v = \case
      CVar i -> i == v
      CUniverseLift _ _ _ inner -> go v inner
      CSchemaLift _ _ _ _ _ _ sourceArguments targetArguments inner ->
        any (go v) sourceArguments || any (go v) targetArguments || go v inner
      CArithmeticProof certificate ->
        any (go v) (foldMapArithmeticCertificate (: []) certificate)
      CGlob _ -> False
      CLam _ _ _ b -> go (v + 1) b
      CPi _ _ _ _ a b -> go v a || go (v + 1) b
      CApp _ f a -> go v f || go v a
      CSort _ -> False
      CLevel _ -> False
      CLit _ -> False
      CCtor _ _ as -> any (go v) as
      CMatch s _ _ alts -> go v s || any (\(CaseAlt p gd b) -> let n = patBindersC p in maybe False (go (v + n)) gd || go (v + n) b) alts
      CRecordT fs -> any (go v . snd) fs
      CRecordV fs -> any (go v . snd) fs
      CProj e _ -> go v e
      CProjAt e _ _ -> go v e
      CVariantT ms -> any (go v) ms
      CInject _ e -> go v e
      CLet _ _ a b c -> go v a || go v b || go (v + 1) c
      CLetRec _ _ a b c -> go v a || go (v + 1) b || go (v + 1) c
      CLetPolyM _ _ _ _ a b c -> go v a || go v b || go (v + 1) c
      CLetRecPolyM _ _ _ _ a b c -> go v a || go (v + 1) b || go (v + 1) c
      CLetRecGroupM _ definitions body ->
        let count = length definitions
         in any (\definition -> go v (clrdType definition) || go (v + count) (clrdRhs definition)) definitions
              || go (v + count) body
      CMeta _ -> False
      CDo _ _ -> False
      CSealE _ e -> go v e
      CSigT _ e -> go v e
      CThunkE e suspensionType -> go v e || maybe False (go v) suspensionType
      CLazyE e suspensionType -> go v e || maybe False (go v) suspensionType
      CForceE e resultType -> go v e || maybe False (go v) resultType
      CIf a b c -> go v a || go v b || go v c
      CQuote _ slots -> any (go v) slots
      CLocal i _ -> i == v

-- bind each telescope entry at its elaborated domain type (the domain
-- term is closed over the preceding entries)
telePi :: TelescopeEntry -> Term -> Term
telePi entry =
  CPiBoundFormedM
    (teMode entry)
    (teFormation entry)
    (teIcit entry)
    (teQ entry)
    (teBorrow entry)
    (teName entry)
    (teLevelAssumption entry)
    (teDomain entry)

-- | §11.3.3 declaration-header default: a genuinely unannotated parameter is
-- an erased parametric type variable. An explicit annotation or quantity keeps
-- the ordinary binder rules and is never rewritten after elaboration.
headerBinderQ :: Binder -> Q
headerBinderQ b
  | isNothing (bType b)
  , isNothing (bpQuantity (bPrefix b)) = Q0
  | otherwise = binderQ b

-- | §9.4: expects with no satisfier at the end of the compilation unit.
expectUnsatisfiedDiags :: CheckState -> Diagnostics
expectUnsatisfiedDiags st =
  [ diag SevError StageElaborate "E_EXPECT_UNSATISFIED" (Just "kappa-hs.expect.unsatisfied") sp
      ("expected declaration '" <> gnameText g
         <> "' is not satisfied by any definition, backend intrinsic, or imported artifact in this compilation unit (Spec §9.4)")
  | (g, (sp, n)) <- Map.toList (csExpects st)
  , n == 0
  ]

expandedGlobalsOfTermM :: Term -> CheckM (Set GName)
expandedGlobalsOfTermM tm = do
  st <- get
  pure (expandedGlobalsOfTerm st tm)

expandedGlobalsOfTerm :: CheckState -> Term -> Set GName
expandedGlobalsOfTerm st =
  Termination.expandedGlobalsOfTerm $ \global -> do
    definition <- Map.lookup global (csGlobals st)
    pure (gdReducible definition, Map.lookup global (csCoreBodies st))

ctxNatLevels :: Ctx -> CheckM (Set Int)
ctxNatLevels ctx =
  Set.fromList . catMaybes <$>
    forM (zip [0 :: Int ..] (ctxEntries ctx)) (\(i, e) -> do
      ty <- forceM (ceType e)
      let lvl = ctxLen ctx - 1 - i
      pure $ case ty of
        VGlobN g [] | g == prelNat -> Just lvl
        _ -> Nothing)

nominalDataHead :: Term -> Maybe GName
nominalDataHead term =
  termHeadGlob (stripIdentityWrappers (fst (spineOfTerm (stripIdentityWrappers term))))
