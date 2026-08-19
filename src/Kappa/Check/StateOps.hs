-- | Small accessors and updates over 'CheckState'.
--
-- Plumbing on the elaboration state: registering facts, invalidating derived
-- caches, and the derived-index maintenance that keeps lookup tables
-- synchronized with the authoritative ones.
--
-- Carved out of "Kappa.Check" as part of splitting that module; see
-- "Kappa.Check.Types" for the shared data dictionary and docs\/CONCEPTS.md
-- for the vocabulary these assume.
module Kappa.Check.StateOps
  ( addCtxAlias
  , addVarCurrentAlias
  , bareTypeLevel
  , bindCtxLetUniverseMode
  , bindCtxMQProvisional
  , bindCtxVar
  , ceVarBind
  , ctxRefinementOf
  , demandOfQ
  , duplicateRelated
  , existsPayloadLabel
  , existsWitLabel
  , freshGeneralizableLevelMeta
  , freshMetaFor
  , inheritGeneralizableLevelRoles
  , initCheckState
  , isExistsInternalLabel
  , isVarCurrentKey
  , markInferredDeclarationLevelCandidates
  , maxPropCacheEntries
  , mentionsThis
  , pushCtxBarrier
  , recordCoreBody
  , recordEffectOpValueGlobal
  , recordHandlerOpQuantity
  , recordMutableBindingFields
  , recordPatternBinderBorrow
  , recordPatternBinderFacts
  , recordUsageTypeAtSpan
  , recordRecognizedRefOp
  , recordTerminationDecl
  , recordTypeIsDependent
  , refineCtx
  , refineRoot
  , setRecursiveSchemaOccurrences
  , setTopCoreQ
  , setTopPrefix
  , singletonTerminationDependenciesReady
  , solveMetaAcyclic
  , substThisTm
  , topoFields
  , tryQuoteIn
  , varCurrentRootOf
  , withDemand
  , withGeneralizableBareTypeLevels
  , withIncompleteSelfEvidenceForbidden
  , withTraitSupers
  , withThis
  , withVarReadBlock
  , withoutGeneralizableBareTypeLevels
  , defaultUnsafeConfig
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

-- | The default build configuration: every unsafe/debug facility is
-- disabled (§4.2 package-mode defaults).
defaultUnsafeConfig :: UnsafeConfig
defaultUnsafeConfig = UnsafeConfig False False False False False False True

initCheckState :: CheckState
initCheckState =
  CheckState
    { csGlobals = Map.empty
    , csDatas = Map.empty
    , csCtors = Map.empty
    , csTopLevelDataHeaders = Map.empty
    , csTraits = Map.empty
    , csBareTraitMembers = Map.empty
    , csTraitMemberOwners = Map.empty
    , csInstances = []
    , csInstancesByTrait = Map.empty
    , csInstanceUniverseInterfaces = Map.empty
    , csMetas = emptyMetas
    , csSolvedMetas = Set.empty
    , csMetaAssignmentGenerations = Map.empty
    , csNextMeta = 0
    , csMetaClassifiers = Map.empty
    , csApplicationPlanningMetas = Set.empty
    , csFirstClassLevelMetas = Set.empty
    , csLevelConstraints = []
    , csLevelConstraintOwners = Map.empty
    , csLevelConstraintsByOwner = Map.empty
    , csLevelConstraintSpans = Map.empty
    , csLevelConstraintIndex = Map.empty
    , csLevelConstraintProvenance = Map.empty
    , csUniverseDiagnosticSpan = Nothing
    , csNextLevelConstraint = 0
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
    , csNextProvisionalUniverseInstantiation = 0
    , csProvisionalGlobalUniverseMetas = Map.empty
    , csProvisionalConstructorUniverseMetas = Map.empty
    , csFinalizedGlobalUniverseMetaMaps = Map.empty
    , csUniverseInterfaceValues = Set.empty
    , csFinalizedUniverseInterfaces = Set.empty
    , csNominalSummaryRequests = Map.empty
    , csDirtyNominalSummaries = Set.empty
    , csRecursiveSchemaEdges = Set.empty
    , csRecursiveSchemaOccurrences = []
    , csRecursiveSchemaOccurrencesByCaller = Map.empty
    , csSelectedUniverseEvidence = Set.empty
    , csUniverseInferenceRecords = Map.empty
    , csPendingUniverseProofs = Map.empty
    , csPublishedGeneratedConstraintCounts = Map.empty
    , csActiveUniverseDefinition = Nothing
    , csRecordRecursiveSchemaOccurrences = False
    , csActiveLocalRecursiveSchemaScope = Nothing
    , csLocalRecursiveSchemaOccurrences = []
    , csActiveUniverseSchema = Map.empty
    , csDeclaredUniverseSchemaNames = Map.empty
    , csActiveLocalUniverseSchemaCount = Nothing
    , csAllowSchemaLevelTerms = False
    , csGeneralizeBareTypeLevels = False
    , csBareTypeLevels = Map.empty
    , csDiags = []
    , csModule = ModuleName ["main"]
    , csScope = Map.empty
    , csLocalDeclScope = Map.empty
    , csLocalNominalCaptures = Map.empty
    , csScopedLocalNominals = Map.empty
    , csModuleAliases = Map.empty
    , csModuleExports = Map.empty
    , csFresh = 0
    , csPending = []
    , csPendingEvidenceAttempts = Map.empty
    , csDeferredTypeEqualities = []
    , csDiagnosedPendingEvidence = Set.empty
    , csPendingLevelEvidence = Map.empty
    , csEvidenceCache = Map.empty
    , csNormEpoch = 0
    , csNormCache = Map.empty
    , csPropCache = Map.empty
    , csScopeAmbig = Map.empty
    , csExpects = Map.empty
    , csSigPending = Map.empty
    , csManifest = Map.empty
    , csActive = Map.empty
    , csFacts = Map.empty
    , csProjections = Map.empty
    , csInoutParams = Map.empty
    , csAllowInoutBinderContext = False
    , csMutableBindingFields = Map.empty
    , csPendingDiscardedResults = []
    , csDiscardedResultTypes = Map.empty
    , csRecognizedRefOps = Map.empty
    , csRecognizedMultishotOps = Map.empty
    , csEffectOpValueGlobals = Map.empty
    , csHandlerOpQuantities = Map.empty
    , csPatternBinderQuantities = Map.empty
    , csPatternBinderBorrows = Set.empty
    , csConstructorPatternLetSpans = Set.empty
    , csStaticKindBinders = Set.empty
    , csErasedArgumentSpans = Set.empty
    , csBorrowedArgumentDemands = Map.empty
    , csErasedExpressionSpans = Set.empty
    , csImplicitExpressionDemands = Map.empty
    , csNextRefCellId = 0
    , csNextLevelFieldId = 0
    , csDemand = DemandRead
    , csThis = Nothing
    , csTraitSupers = []
    , csEvidenceUniquenessStack = []
    , csBlockedSupertraitProjections = Set.empty
    , csForbidIncompleteSelfEvidence = False
    , csArgIndexRetag = False
    , csDefinitionalEqualityOnly = False
    , csReceivers = Map.empty
    , csExpansions = Map.empty
    , csUsageExpressionTypes = Map.empty
    , csOpaqueDatas = Map.empty
    , csOpaqueDefs = Map.empty
    , csRecordOrders = Map.empty
    , csReExports = Map.empty
    , csBoolFacts = []
    , csArgFlatOk = False
    , csPreInstances = Map.empty
    , csDerivedDecls = Map.empty
    , csPositivity = Map.empty
    , csDeclSites = Map.empty
    , csMultiFixOps = Set.empty
    , csUnsafe = defaultUnsafeConfig
    , csPreludeDisabled = False
    , csAllowUnsafeIntrinsics = False
    , csEmbeddedLoad = False
    , csAuditLedger = []
    , csScopeNameCache = Nothing
    , csBackendIntrinsics = Map.empty
    , csFoundationProviders = Map.empty
    , csCoreBodies = Map.empty
    , csImportedCoreBodies = Map.empty
    , csCoreSignatures = Map.empty
    , csTransparentValueAliases = Map.empty
    , csLevelOperatorAliases = Map.empty
    , csOwnership = Map.empty
    , csTerminationNames = Set.empty
    , csTerminationDecls = Map.empty
    , csAssertTerminates = Set.empty
    , csModEffLabels = Map.empty
    , csEffectInterfaces = Map.empty
    , csMultishotOps = Set.empty
    , csAssertReducible = Set.empty
    , csImpossibleScrut = Nothing
    , csHoles = Map.empty
    , csSignatureHoles = Map.empty
    }

setRecursiveSchemaOccurrences
  :: [RecursiveSchemaOccurrence]
  -> CheckState
  -> CheckState
setRecursiveSchemaOccurrences occurrences state =
  state
    { csRecursiveSchemaOccurrences = occurrences
    , csRecursiveSchemaOccurrencesByCaller =
        Map.fromListWith
          (++)
          [(rsoCaller occurrence, [occurrence]) | occurrence <- occurrences]
    }

ceVarBind :: CtxEntry -> Bool
ceVarBind = isJust . ceVarInfo

-- | Mark a closure boundary: entries below it are captured (§16.2.1).
pushCtxBarrier :: Ctx -> Ctx
pushCtxBarrier ctx = ctx {ctxBarriers = ctxLen ctx : ctxBarriers ctx}

withVarReadBlock :: VarReadBlock -> Ctx -> Ctx
withVarReadBlock block ctx = ctx {ctxVarReadBlock = Just block}

-- | Bind a compiler-generated variable whose observation mode is only a
-- placeholder until uses have solved its domain. The provisional mode keeps
-- kind variables usable while elaborating the surrounding declaration;
-- source-time observation checks and the final telescope both classify the
-- solved domain instead of treating that placeholder as authoritative.
bindCtxMQProvisional :: ObservationMode -> Q -> Text -> Bool -> Value -> Ctx -> Ctx
bindCtxMQProvisional mode q n implocal ty ctx =
  case ctxEntries bound of
    entry : rest -> bound {ctxEntries = entry {ceModeProvisional = True} : rest}
    [] -> bound
  where
    bound = bindCtxMQ mode q n implocal ty ctx

bindCtxLetUniverseMode
  :: Text
  -> Bool
  -> Value
  -> Value
  -> DeclarationUniverseTelescope
  -> Maybe ProjInfo
  -> Maybe EffectOpValueInfo
  -> ObservationMode
  -> Maybe Text
  -> Ctx
  -> Ctx
bindCtxLetUniverseMode n implocal ty v telescope mpj mop mode observationOrigin ctx =
  bindEntry
    (CtxEntry n ty (Just (LocalUniverseInfo telescope)) mode False implocal Nothing mpj mop QW observationOrigin Nothing False noSpan)
    v
    ctx

-- | Bind a @var@ cell; the name denotes the cell itself (§18.6.1).
bindCtxVar :: Text -> Value -> VarRefInfo -> Ctx -> Ctx
bindCtxVar n ty info ctx =
  let ctx' = bindEntry (CtxEntry n ty Nothing Ordinary False False (Just info) Nothing Nothing QW Nothing Nothing False noSpan) (VRigid (length (ctxEnv ctx)) []) ctx
   in ctx' {ctxVarCurrentVersions = Map.insert n 0 (ctxVarCurrentVersions ctx')}

-- | Record the implicit binder prefix on the most recent entry
-- (quantity and borrow marker, §16.3.3). @binderSp@ is the binder's
-- source span; when the prefix marks a borrow (@\@&@) it is recorded as
-- the entry's §3.1.1A introduction origin so a later borrow-escape
-- diagnostic about this candidate can cite where it was borrowed.
setTopPrefix :: Span -> BinderPrefix -> Ctx -> Ctx
setTopPrefix binderSp (BinderPrefix _ mq mb) ctx = case ctxEntries ctx of
  (e : rest) ->
    ctx
      { ctxEntries =
          e
            { ceQ = mq
            , ceCoreQ = qOf mq
            , ceBorrow = isJust mb
            , ceOrigin = if isJust mb then binderSp else ceOrigin e
            }
            : rest
      }
  [] -> ctx

setTopCoreQ :: Q -> Ctx -> Ctx
setTopCoreQ q ctx = case ctxEntries ctx of
  e : rest -> ctx {ctxEntries = e {ceCoreQ = q} : rest}
  [] -> ctx

-- | The §7.4.3 stable-alias root of a variable.
refineRoot :: Ctx -> Text -> Text
refineRoot ctx = go (16 :: Int)
  where
    go 0 n = n
    go fuel n = case Map.lookup n (ctxAliases ctx) of
      Just n' -> go (fuel - 1) n'
      Nothing -> n

-- | Record §7.4.1 refinements (through alias roots).
refineCtx :: [(Text, [GName])] -> Ctx -> Ctx
refineCtx refs ctx =
  ctx {ctxRefines = foldr add (ctxRefines ctx) refs}
  where
    add (n, gs) = Map.insert (refinementRoot ctx n) gs

-- | Record a stable alias @q = p@ (§7.4.3).
addCtxAlias :: Text -> Text -> Ctx -> Ctx
addCtxAlias q p ctx = ctx {ctxAliases = Map.insert q p (ctxAliases ctx)}

-- | Current refinement of a variable, through its alias root.
ctxRefinementOf :: Ctx -> Text -> Maybe [GName]
ctxRefinementOf ctx n = Map.lookup (refinementRoot ctx n) (ctxRefines ctx)

-- | Flow facts for a mutable current value are versioned just like snapshot
-- aliases. A direct occurrence of the mutable binding denotes its current
-- version; an immutable alias already resolves to the version it captured.
refinementRoot :: Ctx -> Text -> Text
refinementRoot ctx n =
  fromMaybe (refineRoot ctx n) (varCurrentRootOf ctx n)

varCurrentKey :: Text -> Int -> Text
varCurrentKey n v = "$var-current:" <> n <> ":" <> T.pack (show v)

varCurrentKeyPrefix :: Text
varCurrentKeyPrefix = "$var-current:"

isVarCurrentKey :: Text -> Bool
isVarCurrentKey = T.isPrefixOf varCurrentKeyPrefix

varCurrentRootOf :: Ctx -> Text -> Maybe Text
varCurrentRootOf ctx n = do
  (_, entry) <- lookupCtx n ctx
  _ <- ceVarInfo entry
  version <- Map.lookup n (ctxVarCurrentVersions ctx)
  if n `Set.member` ctxVarCurrentEscaped ctx
    then Nothing
    else Just (varCurrentKey n version)

addVarCurrentAlias :: Text -> Text -> Ctx -> Ctx
addVarCurrentAlias alias root ctx =
  ctx {ctxAliases = Map.insert alias root (ctxAliases ctx)}

-- | Read-only normalization probes may encounter values originating in a
-- deeper pattern/closure context. Such a probe is simply inapplicable at the
-- caller depth; only committed Core construction uses 'quoteIn' and its fatal
-- scoping invariant.
tryQuoteIn :: Ctx -> Value -> CheckM (Maybe Term)
tryQuoteIn ctx value = do
  quoted <- quoteRawIn ctx value
  pure (quoted <$ guard (termScopedAt (ctxLen ctx) quoted))

-- | Run an action under a given §16.1.5 place demand, restoring the
-- ambient demand afterwards.
withDemand :: PlaceDemand -> CheckM a -> CheckM a
withDemand d act = do
  old <- gets csDemand
  modify' $ \st -> st {csDemand = d}
  r <- act
  modify' $ \st -> st {csDemand = old}
  pure r

demandOfQ :: Q -> PlaceDemand
demandOfQ q
  | q `elem` [Q1, QGe1] = DemandConsume
  | otherwise = DemandRead

-- | Run an action with @this@ denoting the given §13.2.1 sibling scope.
withThis :: Maybe ThisMode -> CheckM a -> CheckM a
withThis tm act = do
  old <- gets csThis
  modify' $ \st -> st {csThis = tm}
  r <- act
  modify' $ \st -> st {csThis = old}
  pure r

-- | Run one trait-member action with the owning trait's checked supertrait
-- premises available to implicit resolution. Both signatures and ordinary
-- defaults use this scope so a supertrait operation selects the same
-- @this.__superN@ evidence path in types and bodies.
withTraitSupers :: [(Text, Value)] -> CheckM a -> CheckM a
withTraitSupers supers action = do
  previous <- gets csTraitSupers
  modify' $ \state -> state {csTraitSupers = supers}
  result <- action
  modify' $ \state -> state {csTraitSupers = previous}
  pure result

-- | Reject reification of the dictionary currently being completed only at
-- an explicit fresh-evidence request. Method calls may still dispatch through
-- that dictionary while their member body is checked.
withIncompleteSelfEvidenceForbidden :: CheckM a -> CheckM a
withIncompleteSelfEvidenceForbidden action = do
  previous <- gets csForbidIncompleteSelfEvidence
  modify' $ \state -> state {csForbidIncompleteSelfEvidence = True}
  result <- action
  modify' $ \state -> state {csForbidIncompleteSelfEvidence = previous}
  pure result

-- | §13.2.11 internal existential member labels. The angle-bracket
-- sigil cannot occur in a source identifier (the lexer admits only
-- @[A-Za-z0-9_]@ and non-ASCII letters), so these labels are never
-- source-addressable through @EProj@/@elabDot@ — exactly the spec's
-- requirement that witness members and a non-record payload "are not
-- source-addressable and not rendered as a public field" (Spec.md
-- 13314, 13316-13317). The labels are position-based so that
-- alpha-equivalent existential types elaborate to the same internal
-- shape and remain convertible (Spec.md 13322).
existsWitLabel :: Int -> Text
existsWitLabel i = "⟨wit" <> T.pack (show i) <> "⟩"

-- | The single anonymous non-record payload label of an existential
-- (Spec.md 13316-13317: @⟨payload⟩ : T@, not a field named @value@).
existsPayloadLabel :: Text
existsPayloadLabel = "⟨payload⟩"

-- | Whether a member label is a §13.2.11 internal existential label
-- (witness or anonymous payload). Such labels are not source-visible
-- projection fields.
isExistsInternalLabel :: Text -> Bool
isExistsInternalLabel l = "⟨" `T.isPrefixOf` l

-- | Does a term mention the §13.2.1 @this@ neutral?
mentionsThis :: Term -> Bool
mentionsThis = mentionsGlobal thisG

-- | Substitute a receiver term (well-scoped at the substitution site)
-- for the §13.2.1 @this@ neutral, shifting under binders.
substThisTm :: Term -> Term -> Term
substThisTm = substGlobal thisG

-- | Does any field type of the record mention @this@?
recordTypeIsDependent :: Ctx -> [(Text, Value)] -> CheckM Bool
recordTypeIsDependent ctx fs =
  or <$> mapM (fmap mentionsThis . quoteIn ctx . snd) fs

-- | Topologically sort labelled items by their dependency labels;
-- 'Nothing' on a cycle.
topoFields :: [(Text, [Text], a)] -> Maybe [a]
topoFields = goT []
  where
    goT _ [] = Just []
    goT doneLs pending =
      case sortOn (\(label, _, _) -> label) [x | x@(_, ds, _) <- pending, all (`elem` doneLs) ds] of
        [] -> Nothing
        ready -> do
          let readyLs = [l | (l, _, _) <- ready]
              rest = [x | x@(l, _, _) <- pending, l `notElem` readyLs]
          ((map (\(_, _, a) -> a) ready) ++) <$> goT (doneLs ++ readyLs) rest

recordMutableBindingFields :: Ctx -> Span -> Value -> VarRefInfo -> CheckM ()
recordMutableBindingFields ctx sp _hiddenRefTy info = do
  hiddenRef <- renderPayloadValue ctx (vriDiagnosticRefType info)
  stored <- renderPayloadValue ctx (vriStoredType info)
  monadTy <- renderPayloadValue ctx (vriMonadType info)
  evidenceTy <- renderPayloadValue ctx (VGlobN prelMonadRef [(Expl, vriMonadType info)])
  evidence <- renderPayloadTerm ctx (vriMonadRefDict info)
  let fields =
        [ ("hiddenReferenceType", hiddenRef)
        , ("storedValueType", stored)
        , ("enclosingMonad", monadTy)
        , ("enclosingDoBlock", "nearest")
        , ("monadRefEvidence", evidence)
        , ("monadRefEvidenceType", evidenceTy)
        ]
  modify' $ \st -> st {csMutableBindingFields = Map.insert sp fields (csMutableBindingFields st)}

recordRecognizedRefOp :: Span -> Text -> CheckM ()
recordRecognizedRefOp sp op =
  modify' $ \st -> st {csRecognizedRefOps = Map.insert sp op (csRecognizedRefOps st)}

recordEffectOpValueGlobal :: GName -> EffectOpValueInfo -> CheckM ()
recordEffectOpValueGlobal g info =
  modify' $ \st -> st {csEffectOpValueGlobals = Map.insert g info (csEffectOpValueGlobals st)}

recordHandlerOpQuantity :: Span -> Q -> CheckM ()
recordHandlerOpQuantity sp q =
  modify' $ \st -> st {csHandlerOpQuantities = Map.insert sp q (csHandlerOpQuantities st)}

recordPatternBinderQuantity :: Span -> Q -> CheckM ()
recordPatternBinderQuantity sp q =
  modify' $ \st ->
    st {csPatternBinderQuantities = Map.insert sp q (csPatternBinderQuantities st)}

-- | Publish a finalized checker type under the stable source identity consumed
-- by Usage. Unsolved classifiers remain absent so later analysis fails closed
-- instead of treating a provisional delaboration as storage authority.
recordUsageTypeAtSpan :: Ctx -> Span -> Value -> CheckM ()
recordUsageTypeAtSpan ctx sp ty = do
  typeTerm0 <- quoteIn ctx ty
  typeTerm <- zonkTermM (ctxLen ctx) typeTerm0
  state <- get
  when (null (unsolvedMetasOf state typeTerm)) $
    case delaborateType ctx sp typeTerm of
      Nothing -> pure ()
      Just sourceType ->
        modify' $ \current ->
          current
            { csUsageExpressionTypes =
                Map.insert sp sourceType (csUsageExpressionTypes current)
            }

-- | Publish the checked quantity and static-kind status of a pattern binder
-- to the syntax-level usage pass. Observation mode and quantity are
-- independent: an @ordinary 0 A : Type@ field remains statically observable
-- in a pattern even though it contributes no runtime demand.
recordPatternBinderFacts :: Ctx -> Span -> Q -> Value -> CheckM ()
recordPatternBinderFacts ctx sp q ty = do
  recordPatternBinderQuantity sp q
  recordUsageTypeAtSpan ctx sp ty
  when (q == Q0) $ do
    staticClassifier <- isIntrinsicallyCompileTimeClassifier (ctxLen ctx) ty
    when staticClassifier $
      modify' $ \st ->
        st {csStaticKindBinders = Set.insert sp (csStaticKindBinders st)}

recordPatternBinderBorrow :: Span -> CheckM ()
recordPatternBinderBorrow sp =
  modify' $ \st -> st {csPatternBinderBorrows = Set.insert sp (csPatternBinderBorrows st)}

-- | Allocate an inference meta whose classifier is already known by the
-- bidirectional checker. This provenance is the authority used by local
-- declaration generalization; reconstructing a classifier later from source
-- shape would make holes and evidence arguments indistinguishable.
freshMetaFor :: Ctx -> Value -> CheckM Term
freshMetaFor ctx classifier = snd <$> freshMetaForWithId ctx classifier

-- | Allocate a level that is itself introduced by a source declaration
-- binder or annotation.  This is deliberately different from scanning the
-- elaborated binder domain after the fact: such a domain can contain freshly
-- instantiated universe arguments of referenced declarations, and those are
-- occurrences rather than parameters of the declaration being checked.
freshGeneralizableLevelMeta :: CheckM Level
freshGeneralizableLevelMeta = do
  level <- freshLevelMeta
  markGeneralizableLevelTerm (CSort level)
  pure level

-- | At an inferred declaration boundary the completed semantic classifier,
-- not the provenance of the metavariable that happened to reach it, decides
-- which universe positions admit declaration generalization (§11.3.3). This
-- is what preserves an existing polymorphic value in @let boo = foo@: lookup
-- freshens @foo@'s schema as an occurrence, but the fresh level occurs in a
-- parameter position of @boo@'s inferred classifier and is therefore a
-- declaration candidate. Result-only occurrence choices remain minimizable.
markInferredDeclarationLevelCandidates :: GName -> Value -> CheckM ()
markInferredDeclarationLevelCandidates owner classifier = do
  classifierTerm <- quoteIn emptyCtx classifier >>= zonkTermM 0
  markDeclarationSchemaLevelCandidates owner classifierTerm

-- | Mark exactly the levels contributed by a declaration's semantic schema.
-- Generated comparison binders and the source endpoint of a cumulative lift
-- are checking evidence, while the lifted payload and the surrounding
-- nominal/application spine remain part of the declaration interface.
markDeclarationSchemaLevelCandidates :: GName -> Term -> CheckM ()
markDeclarationSchemaLevelCandidates owner term =
  forM_ (Set.toAscList candidates) $ \meta ->
    markGeneralizableLevelTermFor owner (CSort (LMeta meta))
  where
    candidates = declarationSchemaGeneralizableMetas term

inheritGeneralizableLevelRoles :: GName -> GName -> Term -> CheckM ()
inheritGeneralizableLevelRoles source target term = do
  owners <- gets csLevelGeneralizableOwners
  let inherited =
        [ meta
        | meta <- levelMetasOfTerm term
        , source `Set.member` Map.findWithDefault Set.empty meta owners
        ]
  forM_ inherited $ \meta ->
    markGeneralizableLevelTermFor target (CSort (LMeta meta))

-- | §11.1.2.3: bare @Type@ is floating.  The source span is the annotation
-- identity used by grouped declarations, whose parser expansion intentionally
-- reuses one annotation node; separate annotations have distinct spans and
-- therefore receive independent metas.
bareTypeLevel :: Span -> CheckM Level
bareTypeLevel sp = do
  known <- gets (Map.lookup sp . csBareTypeLevels)
  level <- case known of
    Just existing -> pure existing
    Nothing -> do
      fresh <- freshLevelMeta
      modify' $ \st -> st {csBareTypeLevels = Map.insert sp fresh (csBareTypeLevels st)}
      pure fresh
  generalizable <- gets csGeneralizeBareTypeLevels
  when generalizable (markGeneralizableLevelTerm (CSort level))
  pure level

-- | Give bare @Type@ nodes their parameter-position provenance while a
-- syntactic binder domain is elaborated. This is intentionally not inferred
-- from the resulting Core term: that term can contain freshly specialized
-- universes belonging to referenced declarations.
withGeneralizableBareTypeLevels :: CheckM a -> CheckM a
withGeneralizableBareTypeLevels action = do
  previous <- gets csGeneralizeBareTypeLevels
  modify' $ \st -> st {csGeneralizeBareTypeLevels = True}
  result <- action
  modify' $ \st -> st {csGeneralizeBareTypeLevels = previous}
  pure result

-- | A lazily forced declaration header may be reached while elaborating a
-- caller's binder domain. The caller's source-role marker is lexical and must
-- not leak into the callee's result classifier; the callee's own binder
-- domains re-enter 'withGeneralizableBareTypeLevels' explicitly.
withoutGeneralizableBareTypeLevels :: CheckM a -> CheckM a
withoutGeneralizableBareTypeLevels action = do
  previous <- gets csGeneralizeBareTypeLevels
  modify' $ \st -> st {csGeneralizeBareTypeLevels = False}
  result <- action
  modify' $ \st -> st {csGeneralizeBareTypeLevels = previous}
  pure result

maxPropCacheEntries :: Int
maxPropCacheEntries = 8192

-- | Solve a metavariable only when the candidate value is acyclic through the
-- current solved-meta graph.  The ordinary occurs check used to quote the
-- candidate first; that is unsafe when another solved meta already points back
-- to the target, because quotation/forcing can chase the cycle indefinitely.
-- Walking the value graph directly rejects exactly those cyclic solutions
-- without normalizing user code.
solveMetaAcyclic :: MetaId -> Value -> CheckM Bool
solveMetaAcyclic m v = do
  state <- get
  let metas = csMetas state
      scoped =
        case Map.lookup m (csMetaClassifiers state) of
          Nothing -> True
          Just classifier ->
            termScopedAt
              (micDepth classifier)
              (quote (ecOf state) (micDepth classifier) v)
  if not scoped || metaOccursInValue metas m v
      then pure False
      else solveMeta m v >> pure True

-- | Record the elaborated KCore body of a top-level term definition for
-- the native backend (see 'csCoreBodies'). Called from 'elabLetDecl'
-- after zonking, with the body the interpreter would evaluate.
recordCoreBody :: GName -> Term -> CheckM ()
recordCoreBody g tm = do
  definition <- gets (Map.lookup g . csGlobals)
  ec <- ec_
  let proofBinders = maybe [] (generatedConstraintBinderNames . globalCoreType ec) definition
      canonical0 =
        canonicalizeSchemaLiftComposition
          (ensureGeneratedConstraintLambdas proofBinders tm)
      canonical =
        maybe canonical0
          (`canonicalCoreBodyForDefinition` canonical0)
          definition
  modify' $ \st ->
    st
      { csCoreBodies = Map.insert g canonical (csCoreBodies st)
      , csGlobals =
          Map.adjust
            (globalDefWithCanonicalCoreBody st canonical)
            g
            (csGlobals st)
      }

-- Certified schema actions are representation identities, so a linear chain
-- of let-bound actions is one action from the first source to the final
-- target. Canonicalizing this exact, single-use shape preserves evaluation
-- order while retaining every covariance proof step.
canonicalizeSchemaLiftComposition :: Term -> Term
canonicalizeSchemaLiftComposition = mapTermWithDepth rewrite 0
  where
    rewrite _ (CLetM _ _ _ _ first body) = do
      (family, source, middle, roles, firstEvidence, certificate, sourceArguments, middleArguments, payload) <- schemaLift first
      second <- case body of
        direct@CSchemaLift {} -> Just direct
        CLetM _ _ _ _ direct (CVar 0) -> Just direct
        _ -> Nothing
      (family', middle', target, roles', secondEvidence, certificate', middleArguments', targetArguments, CVar 0) <- schemaLift second
      guard
        ( family == family'
            && map normalizeLevel middle == map normalizeLevel middle'
            && roles == roles'
            && certificate == certificate'
            && middleArguments == middleArguments'
        )
      evidence <- composeEvidence roles firstEvidence secondEvidence
      pure (CSchemaLift family source target roles evidence certificate sourceArguments targetArguments payload)
    rewrite _ _ = Nothing
    schemaLift = \case
      CSchemaLift family source target roles evidence certificate sourceArguments targetArguments payload ->
        Just (family, source, target, roles, evidence, certificate, sourceArguments, targetArguments, payload)
      _ -> Nothing
    composeEvidence roles first second
      | length roles /= length first || length roles /= length second = Nothing
      | otherwise = zipWith3M compose roles first second
    compose role left right = case (role, left, right) of
      (Invariant, SchemaInvariantEvidence, SchemaInvariantEvidence) -> Just SchemaInvariantEvidence
      (Irrelevant, SchemaIrrelevantEvidence, SchemaIrrelevantEvidence) -> Just SchemaIrrelevantEvidence
      (Covariant, SchemaCovariantEvidence (UniverseEvidence lhs), SchemaCovariantEvidence (UniverseEvidence rhs)) ->
        Just (SchemaCovariantEvidence (UniverseEvidence (lhs ++ rhs)))
      _ -> Nothing
    zipWith3M _ [] [] [] = Just []
    zipWith3M f (a : as) (b : bs) (c : cs) = (:) <$> f a b c <*> zipWith3M f as bs cs
    zipWith3M _ _ _ _ = Nothing

recordTerminationDecl :: TerminationDecl -> CheckM ()
recordTerminationDecl td =
  modify' $ \st -> st {csTerminationDecls = Map.insert (tdName td) td (csTerminationDecls st)}

-- | A direct self-recursive declaration may be certified as soon as every
-- other termination-relevant dependency is already conversion-reducible.
-- Requiring the complete dependency set to be exactly @{self}@ incorrectly
-- keeps ordinary recursion opaque when it calls an earlier total helper. A
-- pending signature or an earlier opaque declaration may still close a larger
-- SCC, so those dependencies continue to defer certification.
singletonTerminationDependenciesReady :: GName -> Set GName -> CheckM Bool
singletonTerminationDependenciesReady self dependencies = do
  state <- get
  let termDependencies =
        Set.delete self
          (Set.intersection dependencies (csTerminationNames state))
      ready dependency =
        dependency `Set.notMember` Map.keysSet (csSigPending state)
          && maybe False gdReducible (Map.lookup dependency (csGlobals state))
  pure (all ready (Set.toList termDependencies))

-- | §3.1.1A duplicate-declaration related origins: the new (rejected)
-- declaration site as @declaration-site@, plus the original declaration
-- site (when recorded) as a second @declaration-site@. Both sites MUST
-- appear (§3.1.1A: "duplicate-declaration diagnostics MUST include both
-- sites"). Also attaches the §3.2.2 name payload.
duplicateRelated :: Text -> GName -> Span -> CheckM (Diagnostic -> Diagnostic)
duplicateRelated nm g sp = do
  mPrior <- gets (Map.lookup g . csDeclSites)
  let payload =
        withPayloadField "name" nm $
          payloadKind "name-duplicate"
      newSite = related RoleDeclarationSite sp ("redeclaration of '" <> nm <> "'")
      priorSite = case mPrior of
        Just psp | psp /= sp -> [related RoleDeclarationSite psp ("'" <> nm <> "' first declared here")]
        _ -> []
  pure (withPayload payload . withRelateds (newSite : priorSite))

-- ── Unification ──────────────────────────────────────────────────────
