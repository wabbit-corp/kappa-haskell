-- | The declaration and module driver: what the compiler does with a whole
-- module once the elaboration kernel can check individual expressions.
--
-- This is the public face of the checker, and the place to start reading it.
-- 'checkModule' is the entry point; the rest of the file is the per-declaration
-- work it dispatches to — publishing a data or trait header, elaborating an
-- instance and its members, checking a top-level definition against its
-- signature, and the derivation obligations those raise.
--
-- The expression-level machinery it calls sits in "Kappa.Check.Kernel", and
-- the supporting layers below that in the other @Kappa.Check.*@ modules.
module Kappa.Check
  ( CheckState (..)
  , initCheckState
  , DataInfo (..)
  , CtorInfo (..)
  , EvidenceConstructionMode (..)
  , EffLabelInfo (..)
  , EffOpInfo (..)
  , TraitInfo (..)
  , InstanceEntry (..)
  , LevelOperatorIdentity (..)
  , ProjInfo (..)
  , InoutParamInfo (..)
  , APResult (..)
  , APInfo (..)
  , EffectOpValueInfo (..)
  , TerminationDecl (..)
  , GlobalDef (..)
  , UnsafeConfig (..)
  , defaultUnsafeConfig
  , scriptUnsafeConfig
  , AuditRecord (..)
  , checkModule
  , linkedCoreBodies
  , unresolvedBuiltins
  , expectUnsatisfiedDiags
  , recursiveSchemaEdgeRecorded
  , selectedUniverseEvidenceRecorded
  , sourceRoleMetadataInvarianceChecks
  , UniverseInferenceClass (..)
  , UniverseInferenceRecord (..)
  , universeInferenceRecord
  , declarationTypesConvertibleAtUse
  , inhabitanceSummaryForState
  , symbolicCardinalityForState
  , ordinalRepresentationForState
  , exactNaturalRepresentationForState
  , refinementRepresentationForState
  , certifyClosedBuiltinData
  , invalidateSemanticCaches
  , metaObservationMode
  , nominalHiddenProjectionInfo
  , zonkTermM
  , preludeModule
  , shapeModule
  ) where

import Control.Applicative ((<|>))
import Control.Monad (filterM, foldM, forM, forM_, guard, replicateM, unless, when)
import Control.Monad.State.Strict
import Data.Data (Data, cast, gmapQ)
import Data.Graph (SCC (..), stronglyConnComp)
import Data.List (nub, nubBy, sort, sortOn)
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes, fromMaybe, isJust, isNothing, listToMaybe)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import Kappa.Builtins
import Kappa.Cardinality
  ( CardExpr (..)
  , cardAdd
  , cardIndex
  , cardLiteral
  , cardMul
  , normalizeCardExpr
  )
import Kappa.Check.Arith
import Kappa.Check.Totality
import Kappa.Check.Types
import Kappa.Check.Support
import Kappa.Check.Decls
import Kappa.Check.Implicits
import Kappa.Check.Positivity
import Kappa.Check.Unify
import Kappa.Check.Names
import Kappa.Check.CallGraph
import Kappa.Check.Match
import Kappa.Check.Blocks
import Kappa.Check.StateOps
import Kappa.Check.Elab
import Kappa.Check.Do
import Kappa.Check.Records
import Kappa.Check.Effects
import Kappa.Core
import Kappa.CoreOps
  ( declarationUniverseConstraints
  , equivalentUniverseConstraint
  , foldTermWithDepth
  , mapTermWithDepth
  , levelMetasOfTerm
  , metaIdsOf
  , shiftTerm
  , weakenTermUnderBinderAt
  , substTopTermAt
  , termScopedAt
  , zonkTermWith
  )
import qualified Kappa.Backend.Repr as Repr
import Kappa.DependencyFrontier
  ( emptyDependencyFrontier
  , recordDependencyCompletions
  )
import Kappa.Diagnostic
import Kappa.Eval
import Kappa.Inhabitance
  ( InhabitanceSummary (Contractible)
  , InhabitancePurpose (..)
  , CtorFiber (..)
  , inhabitanceSummary
  , symbolicCardinality
  )
import Kappa.Level
  ( LevelMeta
  , LevelConstraint (..)
  , normalizeLevel
  , renderLevel
  , substituteLevelParams
  , substituteLevelMetas
  , levelMetas
  )
import Kappa.NominalVariance
import Kappa.Pretty (renderTerm)
import Kappa.Representation
import Kappa.Source
import Kappa.Syntax hiding (CompClause (..), Quantity (..))
import Kappa.Termination hiding (expandedGlobalsOfTerm)
import Kappa.SyntaxOps
  ( freeVarOccurrences
  )
import Kappa.SurfaceValidation (quantityBorrowMarkerSpans)
import Kappa.Check.Kernel

-- | Compare two declaration interfaces as ordinary source occurrences.
-- Hidden declaration-universe telescopes are occurrence-polymorphic, so
-- comparing their stored @LParam@s directly is ill-scoped and rejects valid
-- specializations such as @Option.{0} Int@.  The Appendix-T harness uses this
-- entry point to freshen both interfaces exactly as name resolution does,
-- then asks the checker and principal level solver for definitional equality.
declarationTypesConvertibleAtUse :: CheckState -> GName -> GName -> Bool
declarationTypesConvertibleAtUse initial actual expected =
  evalState compareOccurrences initial
  where
    compareOccurrences = do
      diagnosticCount <- gets (length . csDiags)
      actualOccurrence <- globalTypeIn emptyCtx noSpan actual
      expectedOccurrence <- globalTypeIn emptyCtx noSpan expected
      case (actualOccurrence, expectedOccurrence) of
        (Just (_, actualType), Just (_, expectedType)) -> do
          equal <- unify emptyCtx actualType expectedType
          levelsSolved <- solveDeferredLevelConstraints True
          diagnostics <- gets csDiags
          let newDiagnostics = take (length diagnostics - diagnosticCount) diagnostics
          pure (equal && levelsSolved && not (any isError newDiagnostics))
        _ -> pure False

-- | Publish proof binders that became physical across a checker boundary to
-- every retained Core artifact.  Generated declaration constraints are always
-- prepended, so the increase in the authenticated physical prefix is the exact
-- call-spine delta; endpoint rewriting alone does not count as publication.
-- This deliberately compares Core interfaces rather than pending queues or
-- source names, either of which can lag the actual declaration artifact.
synchronizeGeneratedConstraintInterfaces :: CheckState -> CheckM ()
synchronizeGeneratedConstraintInterfaces =
  synchronizeGeneratedConstraintInterfacesFor Nothing

recordLevelOperatorAlias :: GName -> Term -> CheckM ()
recordLevelOperatorAlias g term = do
  classifyLevelOperatorTerm Set.empty term >>= mapM_ (rememberLevelOperatorAlias g)

-- | Make a signed transparent alias available to later declaration headers.
-- The module checker processes every signature before any ordinary body, but
-- universe annotations in a later header may depend on the alias's semantic
-- identity. Certification is speculative: keep only a clean identity proof
-- and roll back diagnostics, metas, goals, and every other elaboration effect.
-- The body pass still performs the authoritative definition check.
precertifyLevelOperatorAlias :: GName -> CheckM ()
precertifyLevelOperatorAlias g = do
  baseline <- get
  identity <- resolveLevelOperatorAliasIdentity Set.empty g
  after <- get
  put $ case identity of
    Just proven
      | length (csDiags after) == length (csDiags baseline) ->
          baseline
            { csLevelOperatorAliases =
                Map.insert g proven (csLevelOperatorAliases baseline)
            }
    _ -> baseline

-- | Compare two types now when possible, otherwise retain the comparison
-- behind the evidence metas that actually block it.  This is deliberately
-- narrower than expression coercion: binder annotations admit no transport or
-- representation-changing conversion.
expectTypeAfterPendingEvidence :: Ctx -> Span -> Value -> Value -> CheckM ()
expectTypeAfterPendingEvidence ctx sp actual expected = do
  compatible <- tryTypeCompatibility ctx sp actual expected
  unless compatible $ do
    dependencies <- pendingEvidenceComponent ctx [actual, expected]
    deferred <-
      if Set.null dependencies
        then pure False
        else deferTypeEqualityOnPendingEvidence ctx sp actual expected dependencies
    unless deferred (expectType ctx sp actual expected)

-- | A refinement obligation is not an inferable erased parameter: §16.1.9
-- requires an actual evidence value at this boundary. Ordinary implicit
-- resolution may return a fresh inference meta for an erased non-trait goal,
-- so make that speculative attempt transactional and retain it only when the
-- resulting evidence is already fully determined.
resolveRequiredImplicit
  :: Ctx
  -> Span
  -> Value
  -> CheckM (Maybe Term)
resolveRequiredImplicit ctx site =
  resolveRequiredImplicitWithTerm ctx site Nothing

-- | Close the dependency layers introduced by final evidence selection.
-- Selecting a polymorphic dictionary can instantiate a declaration-universe
-- schema and enqueue the dictionary's generated erased constraint proofs.
-- The first module-boundary solve necessarily precedes that selection, while
-- those nested proofs necessarily follow the resulting level assignments.
-- Iterate the two ordinary authorities until both queues are empty; every
-- pass consumes the current finite pending snapshot, and final-mode evidence
-- never defers an unsolved goal back onto that snapshot.
closeFinalEvidenceUniverses :: CheckM Bool
closeFinalEvidenceUniverses = do
  stateBefore <- get
  let pending = csPending stateBefore
      constraints = csLevelConstraints stateBefore
      pendingIds =
        Set.fromList [meta | (meta, _, _, _, _) <- pending]
      orphanedLevelEvidence =
        Set.difference
          (Map.keysSet (csPendingLevelEvidence stateBefore))
          pendingIds
  if not (Set.null orphanedLevelEvidence)
    then do
      errAt noSpan "E_INTERNAL" (Just "kappa.internal.compiler")
        ( "final evidence closure found authenticated level evidence without "
            <> "its pending goal"
        )
      pure False
    else
      if null pending && null constraints
        then finalizeLevelArtifacts >> pure True
        else do
          let beforeProgress = finalEvidenceProgressKey stateBefore
          solved <- solveDeferredLevelConstraints True
          if not solved
            then pure False
            else do
              flushPendingFinal
              stateAfter <- get
              let queuesRemain =
                    not (null (csPending stateAfter))
                      || not (null (csLevelConstraints stateAfter))
              if queuesRemain
                  && finalEvidenceProgressKey stateAfter == beforeProgress
                then do
                  errAt noSpan "E_INTERNAL" (Just "kappa.internal.compiler")
                    "final evidence and universe closure made no semantic progress"
                  pure False
                else closeFinalEvidenceUniverses
  where
    finalEvidenceProgressKey state =
      ( Set.fromList [meta | (meta, _, _, _, _) <- csPending state]
      , Map.keysSet (csPendingLevelEvidence state)
      , csLevelConstraintIndex state
      , csLevelAssignments state
      , Map.size (csMetas state)
      , Map.size (Map.filter isJust (csMetas state))
      )

-- | Commit every non-universe evidence choice after the complete header pass,
-- but retain flexible authenticated level propositions until declaration SCC
-- principalization has installed its final assignments. Calling the ordinary
-- final flush here used to either fabricate proof metas or diagnose valid
-- generated declaration constraints before their solver inputs existed.
flushPendingBeforeUniverseFinalization :: CheckM ()
flushPendingBeforeUniverseFinalization = do
  flushPendingWith True True True
  flushDeferredTypeEqualities False

-- | Commit §18.2 discard obligations after ordinary inference and postponed
-- evidence have reached their declaration boundary. A wholly unconstrained
-- payload specializes to Unit; solved payload types are handed to Usage, which
-- owns the structural QTT decision and diagnostics.
finalizeDiscardedResults :: CheckM ()
finalizeDiscardedResults = do
  st <- get
  let pending = reverse (csPendingDiscardedResults st)
  modify' $ \state -> state {csPendingDiscardedResults = []}
  unless (any ((== SevError) . dSeverity) (csDiags st)) $ do
    forM_ pending $ \PendingDiscardedResult {..} -> do
      -- A non-final expression supplies no observable payload context. When
      -- its entire payload type is still an unconstrained meta, choose Unit as
      -- the principal droppable specialization. This is the same contextual
      -- choice the desugaring's ignored lambda binder permits, and is required
      -- for polymorphic non-returning actions such as raise/reraise. Do not
      -- default metas nested inside an otherwise known payload type: those are
      -- real ambiguities in the value being discarded.
      finalizedType <- forceM pdrType >>= \case
        VFlex meta [] -> do
          unitType <- globalValueM prelUnit []
          solveMeta meta unitType
          pure unitType
        other -> pure other
      tyTm0 <- quoteIn pdrCtx finalizedType
      tyTm <- zonkTermM (ctxLen pdrCtx) tyTm0
      state <- get
      let unresolved = Set.fromList (unsolvedMetasOf state tyTm)
      if not (Set.null unresolved)
        then
          report $
            withPayload
              ( withPayloadField "metavariableKind" "discarded-result-type"
                  $ withPayloadField "sourceOrigin" (T.pack (show pdrSpan))
                  $ withPayloadField "constraints" "no remaining constraint determines the discarded result type"
                  $ withPayloadField "blockedObligations" "droppability"
                  $ withPayloadField "defaultingAttempted" "true"
                  $ withPayloadField "defaultingFailureReason" "no explicit defaulting rule applies"
                  $ withPayloadField "metavariables" (T.pack (show (Set.toAscList unresolved)))
                  $ payloadKind "unsolved-metavariable"
              )
              $ diag SevError StageElaborate "E_UNSOLVED_METAVARIABLE"
                (Just "kappa.type.unsolved-metavariable")
                pdrSpan
                "the discarded result type remains ambiguous, so its §12.2.6 droppability cannot be proved; bind it with an explicit type or constrain the action result (§18.2)"
        else
          case delaborateType pdrCtx pdrSpan tyTm of
            Just sourceType ->
              modify' $ \state ->
                state
                  { csDiscardedResultTypes =
                      Map.insert pdrSpan sourceType (csDiscardedResultTypes state)
                  }
            Nothing ->
              report $
                diag SevError StageElaborate "E_QTT_LINEAR_DROP"
                  (Just "kappa.quantity.positive-lower-bound")
                  pdrSpan
                  "the compiler cannot establish that this discarded result type is droppable (§12.2.6, §18.2)"

-- | §14.3/§33.2.1 program-level coherence: when two instances of one
-- trait have unifiable heads, the overlap is harmless only if the
-- instantiated dictionary artifacts are definitionally equivalent
-- (structural coherence mode); otherwise the program is rejected at
-- the later declaration, whether or not any use site resolves
-- through the overlapping pair.
instanceOverlapIsIncoherent :: InstanceEntry -> InstanceEntry -> CheckM Bool
instanceOverlapIsIncoherent new prior
  | length (ieHead new) /= length (ieHead prior) = pure False
  | otherwise = do
      saved <- get
      (_, _, specializeLevel, specializeTerm) <- instantiateInstanceOccurrence emptyCtx new
      metas <- forM [1 .. ieTeleLen new] (const freshMeta)
      metaVs <- mapM (evalIn emptyCtx) metas
      ec <- ec_
      let goalUniverses = map specializeLevel (ieTraitUniverses new)
          goalArgs = [eval ec (reverse metaVs) (specializeTerm t) | t <- ieHead new]
      -- §33.2.1 step 1: the comparison set holds only candidates that
      -- survive §14.3.1 resolution — an instance whose premises are
      -- unsolvable at the shared instantiation is discarded before
      -- coherence is judged
      mOld <- tryInstance 0 emptyCtx goalUniverses goalArgs prior
      mNew <- tryInstance 0 emptyCtx goalUniverses goalArgs new
      equivalent <- case (mNew, mOld) of
        (Just tmN, Just tmO) -> do
          vN <- evalIn emptyCtx tmN
          vO <- evalIn emptyCtx tmO
          ecu <- ec_
          pure (convertible ecu 0 vN vO)
        _ -> pure True -- disjoint heads or a discarded candidate
      put saved
      pure (not equivalent)

-- | Instance-head higher-kinded arguments need both an exact check and the
-- classifier that the argument actually synthesized.  Retaining only the
-- expected trait-parameter classifier makes occurrence-local result ceilings
-- look source-owned and can publish a spuriously polymorphic dictionary.
--
-- Inference is transactional because an expected-directed form may not
-- synthesize on its own.  Such a form falls back to the established exact
-- checker; an inferred form contributes only source-owned classifier levels
-- that predate the probe.
inferExactExplicitArg
  :: Ctx
  -> ObservationMode
  -> Q
  -> Bool
  -> RuntimeErasure Value
  -> Expr
  -> Value
  -> CheckM (Term, Set LevelMeta)
inferExactExplicitArg ctx mode q borrowed runtimeErasure expression expected = do
  before <- get
  let preexistingMetaLimit = csNextMeta before
  diagnosticsBefore <- gets (length . csDiags)
  let ctx' =
        if q == Q0
          then withVarReadBlock VarReadStaticPosition ctx
          else ctx
      inferArgument =
        withArgIndexRetag
          (withDemand (demandOfQ q) (infer ctx' expression))
  (_term, actual) <- inferArgument
  compatible <- unifyDefinitional ctx actual expected
  diagnosticsAfter <- gets (length . csDiags)
  if compatible && diagnosticsAfter == diagnosticsBefore
    then do
      actualTerm <- quoteIn ctx actual >>= zonkTermM (ctxLen ctx)
      let sourceClassifierLevels =
            Set.filter (< preexistingMetaLimit)
              (Set.fromList (levelMetasOfTerm actualTerm))
      -- Classifier discovery is observational. Fresh global-occurrence metas
      -- and constraints created by this probe are implementation choices,
      -- never generated-dictionary schema parameters.
      put before
      checked <-
        withDefinitionalEqualityOnly
          (checkExplicitArg ctx mode q borrowed runtimeErasure expression expected)
      expectedClassifierLevels <- unresolvedExpectedClassifierLevels ctx expected
      pure (checked, Set.union sourceClassifierLevels expectedClassifierLevels)
    else do
      put before
      term' <-
        withDefinitionalEqualityOnly
          (checkExplicitArg ctx mode q borrowed runtimeErasure expression expected)
      expectedClassifierLevels <- unresolvedExpectedClassifierLevels ctx expected
      pure (term', expectedClassifierLevels)

traitMemberSiblingTypesAt
  :: Span
  -> GName
  -> [Level]
  -> TraitInfo
  -> [Term]
  -> Ctx
  -> [(Text, Term)]
  -> [(Text, Term)]
  -> CheckM [RecordField Value]
traitMemberSiblingTypesAt site trait traitUniverses info argumentTerms ctx supers = go []
  where
    go _ [] = pure []
    go preceding ((member, memberTerm) : rest) = do
      arguments <- mapM (evalIn ctx) argumentTerms
      memberType <-
        instantiateTraitMemberType
          ctx
          site
          trait
          traitUniverses
          member
          arguments
          (supers ++ preceding)
      let field =
            RecordField
              member
              (Map.findWithDefault Ordinary member (tiMemberModes info))
              FormationOrdinary
              (Map.findWithDefault QW member (tiMemberQs info))
              Nothing
              RuntimeRelevant
              memberType
      (field :) <$> go (preceding ++ [(member, memberTerm)]) rest

checkTraitMemberExpressionAgainst
  :: ObservationMode
  -> Ctx
  -> Value
  -> [Binder]
  -> Maybe Expr
  -> Expr
  -> Span
  -> CheckM Term
checkTraitMemberExpressionAgainst memberMode ctx memberType binders resultType body site =
  case binders of
    [] ->
      checkObservedExpr
        ctx
        "ordinary trait member"
        memberMode
        (maybe body (\ty -> EAscription body ty site) resultType)
        memberType
    _ -> checkTraitMemberLambdaAgainst ctx memberType binders body site

checkTraitMemberLambdaAgainst
  :: Ctx
  -> Value
  -> [Binder]
  -> Expr
  -> Span
  -> CheckM Term
checkTraitMemberLambdaAgainst ctx ty binders body site = do
  forced <- case binders of
    [] -> forceM ty
    _ -> peelCapturesM ty
  case (binders, forced) of
    ([], _) -> check ctx body forced
    (binder : rest, VPiBoundM mode Impl quantity _ name assumption domain closure)
      | not (bImplicit binder)
      , mode == Parametric || (nameText <$> bName binder) /= Just name -> do
          withBound <- extendLevelAssumption site ctx assumption
          let nextCtx = bindCtxMQ mode quantity name True domain withBound
          codomain <- clApp closure (VRigid (ctxLen ctx) [])
          CLamM mode Impl quantity name
            <$> checkTraitMemberLambdaAgainst nextCtx codomain (binder : rest) body site
    (binder : rest, VPiBoundM mode icit quantity _ name assumption domain closure) -> do
      withBound <- extendLevelAssumption site ctx assumption
      let binderName = fromMaybe name (nameText <$> bName binder)
          nextCtx = bindCtxMQ mode quantity binderName (icit == Impl) domain withBound
      codomain <- clApp closure (VRigid (ctxLen ctx) [])
      CLamM mode icit quantity binderName
        <$> checkTraitMemberLambdaAgainst nextCtx codomain rest body site
    (_ : _, _) -> do
      errAt site "E_SIGNATURE_ARITY" (Just "kappa-hs.type.signature-arity")
        "trait member has more parameters than its checked member type"
      check ctx body forced

-- | Specialize a source-free checked ordinary-default template.  The hidden
-- declaration has exactly the member accessor's universe/type telescope, so
-- the owning trait occurrence fixes the leading universe prefix and only a
-- member-local suffix is freshened.  The abstract dictionary is supplied as
-- an ordinary checked argument; no source body is re-elaborated here.
instantiateCheckedTraitDefault
  :: Ctx
  -> Span
  -> GName
  -> [Level]
  -> Text
  -> [Term]
  -> [(Text, Term)]
  -> GName
  -> CheckM (Term, Value, Value)
instantiateCheckedTraitDefault ctx site trait traitUniverses member argumentTerms dictionaryFields defaultGlobal = do
  definitions <- gets csGlobals
  let memberName = memberGlobal trait member
  case (Map.lookup defaultGlobal definitions, Map.lookup memberName definitions) of
    (Nothing, _) -> do
      errAt site "E_TRAIT_MEMBER_TELESCOPE_MISMATCH" (Just "kappa.internal.compiler")
        "checked trait default template is missing from the semantic environment"
      recover
    (_, Nothing) -> do
      errAt site "E_TRAIT_MEMBER_TELESCOPE_MISMATCH" (Just "kappa.internal.compiler")
        "checked trait-member interface is missing from the semantic environment"
      recover
    (Just definition, Just memberDefinition) -> do
      let totalUniverses = dutParameterCount (gdUniverses definition)
          memberUniverses = dutParameterCount (gdUniverses memberDefinition)
      if length traitUniverses > totalUniverses || memberUniverses /= totalUniverses
        then do
          errAt site "E_TRAIT_MEMBER_TELESCOPE_MISMATCH" (Just "kappa.internal.compiler")
            "checked trait default template and member accessor have mismatched universe schemas"
          recover
        else do
          suffix <- replicateM (totalUniverses - length traitUniverses) freshLevelInstantiationMeta
          let universes = traitUniverses ++ suffix
          recordRecursiveSchemaOccurrence (Just ctx) False site defaultGlobal universes
          (template, templateType) <- specializeGlobalAt ctx defaultGlobal definition universes
          argumentValues <- mapM (evalIn ctx) argumentTerms
          memberType <-
            instantiateTraitMemberTypeAtUniverses
              ctx
              site
              trait
              member
              universes
              argumentValues
              dictionaryFields
          traitParameterClassifiers
            ctx
            site
            trait
            traitUniverses
            [(Expl, value) | value <- argumentValues] >>= \case
              Nothing -> do
                errAt site "E_TRAIT_MEMBER_TELESCOPE_MISMATCH" (Just "kappa.internal.compiler")
                  "checked trait default has an argument without a checked classifier"
                recover
              Just classifiers -> do
                let dictionaryTerm = CRecordV (sortOn fst dictionaryFields)
                    dictionaryTypeTerm =
                      foldl
                        (CApp Expl)
                        (CGlobal trait traitUniverses)
                        argumentTerms
                dictionaryType <- evalIn ctx dictionaryTypeTerm
                (term, instantiatedType) <-
                  applyGeneratedCoreSpine
                    ctx
                    site
                    template
                    templateType
                    ( [ (Impl, term, classifier)
                      | (term, classifier) <- zip argumentTerms classifiers
                      ]
                        ++ [(Impl, dictionaryTerm, dictionaryType)]
                    )
                let (appliedHead, appliedArguments) = spineOfTerm term
                    specializedBody =
                      zonkTermWith
                        (\_ _ -> Nothing)
                        (substituteLevelParams universes)
                        0
                        <$> gdCoreBody definition
                    specialized = do
                      body <- specializedBody
                      case appliedHead of
                        CGlobal global levels
                          | global == defaultGlobal
                          , levels == universes ->
                              Just
                                ( simplifyDecisionTermAt
                                    (ctxLen ctx)
                                    (foldl (\function (icit, argument) -> CApp icit function argument) body appliedArguments)
                                )
                        _ -> Nothing
                case specialized of
                  Just checkedBody
                    | termScopedAt (ctxLen ctx) checkedBody ->
                        pure (checkedBody, instantiatedType, memberType)
                  _ -> do
                    errAt site "E_TRAIT_MEMBER_TELESCOPE_MISMATCH" (Just "kappa.internal.compiler")
                      "checked trait default could not be specialized to closed instance Core"
                    recover
  where
    recover = do
      (term, ty) <- anyHole ctx
      pure (term, ty, ty)

elabNamedDeclLambda :: Ctx -> [Binder] -> Expr -> Span -> Maybe Value -> CheckM (Term, Value)
elabNamedDeclLambda = elabLambdaWith True False

-- | §18.1: elaborate a TOP-LEVEL @effect@ declaration. Like a scoped effect
-- it mints an opaque interface type + label value and computes the operation
-- signatures, but it registers them as module globals and records the
-- interface in 'csModEffLabels' (visible module-wide) and the type name in
-- the import scope, rather than as a lexically scoped local.
elabTopEffect :: EffectDecl -> Span -> CheckM ()
elabTopEffect eff _dsp = do
  let nm = nameText (effName eff)
  already <- gets (Map.member nm . csModEffLabels)
  unless already $ do
    st0 <- get
    let ifaceG = GName (csModule st0) nm
        labelG = GName (csModule st0) (nm <> ".label")
    (params, ifaceKindTm, ops) <- elabEffInterface emptyCtx eff
    recordMultishotOps ops
    ifaceKindV <- evalIn emptyCtx ifaceKindTm
    addGlobal ifaceG (GlobalDef ifaceKindV Nothing False)
    labelT <- globalValueM prelEffLabel []
    addGlobal labelG (GlobalDef labelT Nothing False)
    -- §18.1.18: the label's runtime identity is its (unique) global name.
    -- The interpreter uses the neutral global; the native backend has no
    -- neutral globals, so record a string-token core body for it (label
    -- equality in the native effect runtime is string equality).
    recordCoreBody labelG (CLit (LitStr (effLabelKey labelG)))
    -- the effect type name resolves module-wide as its interface (type
    -- constructor when parameterized, §18.1.15)
    modify' $ \st -> st {csScope = Map.insert nm ifaceG (csScope st)}
    let info =
          EffLabelInfo
            { eliLabel = labelG
            , eliIface = ifaceG
            , eliParams = params
            , eliFixedArgs = Nothing
            , eliFixedUniverses = Nothing
            , eliOps = ops
            }
    modify' $ \st ->
      st
        { csModEffLabels = Map.insert nm info (csModEffLabels st)
        , csEffectInterfaces = Map.insert ifaceG info (csEffectInterfaces st)
        }

-- | §18.1.15: a top-level @effect label l : E@ mints a fresh effect label
-- @l@ that shares the operations and interface of an existing effect @E@
-- (so several labels can name distinct instances of one effect). The new
-- label gets its own identity; its operations and interface are E's.
elabTopEffectLabel :: EffectDecl -> Span -> CheckM ()
elabTopEffectLabel eff sp = do
  let lblName = nameText (effName eff)
  unless (null (effParams eff)) $
    reportUnsupported sp "effect-label declaration parameters"
  case effLabelType eff of
    Just ifaceE -> do
      visible <- gets csModEffLabels
      mresolved <- resolveEffectLabelInterface emptyCtx sp ifaceE visible
      case mresolved of
        Just (base, universes, args) -> do
          already <- gets (Map.member lblName . csModEffLabels)
          unless already $ do
            st0 <- get
            let labelG = GName (csModule st0) (lblName <> ".label")
            labelT <- globalValueM prelEffLabel []
            addGlobal labelG (GlobalDef labelT Nothing False)
            recordCoreBody labelG (CLit (LitStr (effLabelKey labelG)))
            -- same interface + operations as E, but a fresh label identity
            modify' $ \st ->
              let alias =
                    base
                      { eliLabel = labelG
                      , eliFixedArgs = Just args
                      , eliFixedUniverses = Just universes
                      }
               in st {csModEffLabels = Map.insert lblName alias (csModEffLabels st)}
        Nothing -> pure ()
    Nothing ->
      errAt sp "E_EFFECT_LABEL_FORM" (Just "kappa-hs.effect.label")
        ("'effect label " <> lblName <> " : E' requires a concrete application of a named top-level effect (§18.1.15)")

-- | Run the purpose-keyed inhabitance query against a completed checker state.
-- This is the public analysis boundary used by completion tooling, artifact
-- verification, and the standard harness. The query runs transactionally:
-- speculative evidence search and GADT refinement cannot alter the supplied
-- compilation state.
inhabitanceSummaryForState
  :: CheckState
  -> InhabitancePurpose
  -> Value
  -> InhabitanceSummary
inhabitanceSummaryForState state purpose ty =
  evalState
    (mkInhabEnv emptyCtx >>= \environment -> inhabitanceSummary environment purpose ty)
    state

-- | Scope-indexed exact symbolic-cardinality query (§30.2.7A). The depth is
-- the lexical KCore depth of the supplied type value.
symbolicCardinalityForState
  :: CheckState
  -> Int
  -> Value
  -> Maybe CardExpr
symbolicCardinalityForState state depth ty =
  evalState
    (mkInhabEnv emptyCtx >>= \environment -> symbolicCardinality environment depth ty)
    state

-- | Derive and independently replay a compiler-owned ordinal-representation
-- certificate. Source 'OrdinalRepresentation' evidence is deliberately not a
-- prerequisite for the required structural fragment and cannot create a
-- certificate by itself.
ordinalRepresentationForState
  :: CheckState
  -> RepresentationContext
  -> Int
  -> Value
  -> Maybe OrdinalRepresentationCertificate
ordinalRepresentationForState state context depth ty =
  evalState deriveAndReplay state
  where
    deriveAndReplay = do
      initial <- get
      candidate <- deriveOrdinalRepresentationCertificate context depth ty
      put initial
      replay <- deriveOrdinalEncoding depth Set.empty ty
      put initial
      pure $ do
        certificate <- candidate
        (encoding, erasedFields) <- replay
        guard (encoding == orcEncoding certificate)
        guard (sort erasedFields == sort (orcErasedFields certificate))
        guard (verifyOrdinalRepresentationCertificate certificate == Right ())
        pure certificate

exactNaturalRepresentationForState
  :: CheckState
  -> RepresentationContext
  -> Int
  -> Value
  -> Maybe ExactNaturalRepresentationCertificate
exactNaturalRepresentationForState state context depth ty =
  evalState deriveAndReplay state
  where
    deriveAndReplay = do
      initial <- get
      candidate <-
        deriveExactNaturalRepresentationCertificate context depth ty
      put initial
      replay <- deriveExactNaturalRepresentationCertificate context depth ty
      put initial
      pure $ do
        certificate <- candidate
        replayed <- replay
        guard (replayed == certificate)
        guard (verifyExactNaturalRepresentationCertificate certificate == Right ())
        pure certificate

refinementRepresentationForState
  :: CheckState
  -> RepresentationContext
  -> Int
  -> Value
  -> Maybe RefinementRepresentationCertificate
refinementRepresentationForState state context depth ty =
  evalState deriveAndReplay state
  where
    deriveAndReplay = do
      initial <- get
      candidate <-
        deriveRefinementRepresentationCertificate context depth ty
      put initial
      replay <- deriveRefinementRepresentationCertificate context depth ty
      put initial
      pure $ do
        certificate <- candidate
        replayed <- replay
        guard (replayed == certificate)
        guard (verifyRefinementRepresentationCertificate certificate == Right ())
        pure certificate

deriveOrdinalRepresentationCertificate
  :: RepresentationContext
  -> Int
  -> Value
  -> CheckM (Maybe OrdinalRepresentationCertificate)
deriveOrdinalRepresentationCertificate context depth ty = do
  evaluation <- ec_
  normalized <- forceM ty
  representedType <- pure (quote evaluation depth normalized)
  cardinality <- symbolicCardinalityForCurrentState depth normalized
  derived <- deriveOrdinalEncoding depth Set.empty normalized
  pure $ do
    exactCardinality <- cardinality
    (encoding, erasedFields) <- derived
    guard
      ( ordinalEncodingCardinality encoding
          == Just (normalizeCardExpr exactCardinality)
      )
    pure
      OrdinalRepresentationCertificate
        { orcContext = context
        , orcRepresentedType = representedType
        , orcTypeIdentity =
            representationTypeIdentity context representedType
        , orcSourceEvidenceIdentity = Nothing
        , orcCardinalityExpression = normalizeCardExpr exactCardinality
        , orcEncoding = encoding
        , orcErasedFields = sort (nub erasedFields)
        , orcProfileRestrictions = commonRepresentationRestrictions
        , orcCertificateVersion = 1
        , orcCheckerVersion = 1
        }

symbolicCardinalityForCurrentState :: Int -> Value -> CheckM (Maybe CardExpr)
symbolicCardinalityForCurrentState depth ty = do
  environment <- mkInhabEnv emptyCtx
  symbolicCardinality environment depth ty

deriveOrdinalEncoding
  :: Int
  -> Set GName
  -> Value
  -> CheckM (Maybe (OrdinalEncoding, [ConstructorFieldPath]))
deriveOrdinalEncoding depth seen ty = do
  normalized <- forceM ty
  case normalized of
    VGlobal family _ [(_, index)]
      | family == prelFin -> do
          evaluation <- ec_
          let cardinality = case force evaluation index of
                VLit (LitInt value)
                  | value >= 0 -> cardLiteral (fromInteger value)
                value -> cardIndex (quote evaluation depth value)
          erased <- directErasedFields depth normalized
          pure (Just (OrdinalFin cardinality, erased))
    VGlobal family _ [(_, base), (_, predicate)]
      | family == prelRefined ->
          deriveRefinedOrdinalEncoding depth seen normalized base predicate
    VRecordT fields -> do
      children <- mapM (deriveOrdinalEncoding depth seen . snd) fields
      pure $ do
        derived <- sequence children
        pure
          ( OrdinalRecord (map fst derived)
          , concatMap snd derived
          )
    VVariantT members -> do
      children <- mapM (deriveOrdinalEncoding depth seen) members
      pure $ do
        derived <- sequence children
        pure
          ( OrdinalVariant (map fst derived)
          , concatMap snd derived
          )
    VGlobal family _ _
      | family `Set.member` seen -> pure Nothing
      | otherwise -> deriveNominalOrdinalEncoding depth seen family normalized
    _ -> do
      environment <- mkInhabEnv emptyCtx
      summary <-
        inhabitanceSummary environment SourceReachability normalized
      pure $
        if summary == Contractible
          then Just (OrdinalContractible, [])
          else Nothing

deriveRefinedOrdinalEncoding
  :: Int
  -> Set GName
  -> Value
  -> Value
  -> Value
  -> CheckM (Maybe (OrdinalEncoding, [ConstructorFieldPath]))
deriveRefinedOrdinalEncoding depth seen represented base predicate = do
  range <- canonicalNatRangeBounds depth base predicate
  case range of
    Just (lower, upper) -> do
      erased <- directErasedFields depth represented
      pure (Just (OrdinalInclusiveRange lower upper, erased))
    Nothing -> do
      accepted <- finiteRefinementOrdinals base predicate
      baseEncoding <- deriveOrdinalEncoding depth seen base
      erased <- directErasedFields depth represented
      pure $ do
        ordinals <- accepted
        (encoding, baseErased) <- baseEncoding
        pure
          ( OrdinalFiltered encoding ordinals
          , erased ++ baseErased
          )

deriveNominalOrdinalEncoding
  :: Int
  -> Set GName
  -> GName
  -> Value
  -> CheckM (Maybe (OrdinalEncoding, [ConstructorFieldPath]))
deriveNominalOrdinalEncoding depth seen family represented = do
  state <- get
  case Map.lookup family (csDatas state) of
    Nothing -> pure Nothing
    Just info -> do
      let seen' = Set.insert family seen
      arms <- mapM (deriveArm seen') (diCtors info)
      pure $ do
        derivedArms <- sequence arms
        let reachable = catMaybes derivedArms
        (constructors, erased, _) <-
          foldM appendArm ([], [], cardLiteral 0) reachable
        pure (OrdinalData constructors, erased)
  where
    deriveArm seen' constructor =
      inhabCtorFiber emptyCtx represented constructor >>= \case
        CtorContradiction -> pure (Just Nothing)
        CtorIndexUnknown -> pure Nothing
        CtorRefined fieldTypes -> do
          fields <- mapM (deriveOrdinalEncoding depth seen') fieldTypes
          directErased <- erasedFieldsForConstructor depth constructor fieldTypes
          pure $ do
            derived <- sequence fields
            pure
              ( Just
                  ( constructor
                  , map fst derived
                  , directErased ++ concatMap snd derived
                  )
              )

    appendArm (constructors, erased, offset) (constructor, fields, armErased) = do
      armCardinality <-
        foldM
          (\productSoFar field ->
            cardMul productSoFar
              <$> ordinalEncodingCardinality field)
          (cardLiteral 1)
          fields
      pure
        ( constructors
            ++ [ConstructorOrdinalEncoding constructor offset fields]
        , erased ++ armErased
        , cardAdd offset armCardinality
        )

directErasedFields
  :: Int
  -> Value
  -> CheckM [ConstructorFieldPath]
directErasedFields depth represented = do
  normalized <- forceM represented
  state <- get
  case normalized of
    VGlobal family _ _
      | Just info <- Map.lookup family (csDatas state) ->
          concat
            <$> mapM
              (\constructor ->
                inhabCtorFiber emptyCtx normalized constructor >>= \case
                  CtorRefined fields ->
                    erasedFieldsForConstructor depth constructor fields
                  _ -> pure [])
              (diCtors info)
    _ -> pure []

deriveExactNaturalRepresentationCertificate
  :: RepresentationContext
  -> Int
  -> Value
  -> CheckM (Maybe ExactNaturalRepresentationCertificate)
deriveExactNaturalRepresentationCertificate context depth ty = do
  evaluation <- ec_
  normalized <- forceM ty
  state <- get
  case normalized of
    VGlobal family _ _
      | Just info <- Map.lookup family (csDatas state) -> do
          shapes <- mapM (constructorRuntimeShape depth normalized) (diCtors info)
          evidence <-
            selectedRepresentationEvidenceIdentity
              context
              depth
              (gPrel "ExactNaturalRepresentation")
              normalized
          let zeros =
                [ (constructor, erased)
                | (constructor, [], erased) <- catMaybes shapes
                ]
              successors =
                [ (constructor, fieldIndex, erased)
                | (constructor, [(fieldIndex, fieldType)], erased) <- catMaybes shapes
                , convertible evaluation depth fieldType normalized
                ]
          pure $ do
            (zeroConstructor, zeroErased) <- single zeros
            (successorConstructor, recursiveIndex, successorErased) <-
              single successors
            evidenceIdentity <- evidence
            let representedType = quote evaluation depth normalized
                recursiveField =
                  ConstructorFieldPath successorConstructor recursiveIndex
                certificate =
                  ExactNaturalRepresentationCertificate
                    { enrcContext = context
                    , enrcRepresentedType = representedType
                    , enrcTypeIdentity =
                        representationTypeIdentity context representedType
                    , enrcEvidenceIdentity = evidenceIdentity
                    , enrcZeroConstructor = zeroConstructor
                    , enrcSuccessorConstructor = successorConstructor
                    , enrcRecursiveField = recursiveField
                    , enrcErasedFields =
                        sort (nub (zeroErased ++ successorErased))
                    , enrcProfileRestrictions =
                        commonRepresentationRestrictions
                    , enrcCertificateVersion = 1
                    , enrcCheckerVersion = 1
                    }
            guard
              (verifyExactNaturalRepresentationCertificate certificate
                == Right ())
            pure certificate
    _ -> pure Nothing

constructorRuntimeShape
  :: Int
  -> Value
  -> GName
  -> CheckM
      (Maybe
        ( GName
        , [(Int, Value)]
        , [ConstructorFieldPath]
        ))
constructorRuntimeShape depth represented constructor =
  inhabCtorFiber emptyCtx represented constructor >>= \case
    CtorRefined fieldTypes -> do
      evaluation <- ec_
      constructorInfo <- gets (Map.lookup constructor . csCtors)
      pure $ do
        info <- constructorInfo
        let contracts = constructorSourceContracts info
        guard (length contracts == length fieldTypes)
        let runtime =
              [ (sourceIndex, fieldType)
              | (sourceIndex, ((icit, quantity, runtimeErasure), fieldType)) <-
                  zip [0 :: Int ..] (zip contracts fieldTypes)
              , Repr.runtimeConstructorPiField
                  evaluation
                  depth
                  runtimeErasure
                  icit
                  quantity
                  fieldType
              ]
            erased =
              [ ConstructorFieldPath constructor sourceIndex
              | (sourceIndex, ((icit, quantity, runtimeErasure), fieldType)) <-
                  zip [0 :: Int ..] (zip contracts fieldTypes)
              , not
                  (Repr.runtimeConstructorPiField
                    evaluation
                    depth
                    runtimeErasure
                    icit
                    quantity
                    fieldType)
              ]
        pure (constructor, runtime, erased)
    _ -> pure Nothing

deriveRefinementRepresentationCertificate
  :: RepresentationContext
  -> Int
  -> Value
  -> CheckM (Maybe RefinementRepresentationCertificate)
deriveRefinementRepresentationCertificate context depth ty = do
  evaluation <- ec_
  normalized <- forceM ty
  case normalized of
    VGlobal family _ [(_, base), (_, _predicate)]
      | family == prelRefined -> do
          state <- get
          saved <- get
          goal <-
            globalValueM
              (gPrel "RefinementView")
              [(Expl, normalized)]
          selectedDictionary <- traitEvidence emptyCtx noSpan goal
          selectedEvidence <- case selectedDictionary of
            Just dictionary -> do
              baseMode <-
                traitMemberObservationMode
                  (gPrel "RefinementView")
                  "Base"
              selectedBase <-
                evalIn emptyCtx (CProjM baseMode dictionary "Base")
                  >>= forceM
              baseMatches <- unify emptyCtx selectedBase base
              if baseMatches
                then do
                  zonkedDictionary <- zonkTermM depth dictionary
                  pure
                    (Just
                      (Kappa.Representation.representationEvidenceIdentity
                        context
                        zonkedDictionary))
                else pure Nothing
            _ -> pure Nothing
          put saved
          case Map.lookup family (csDatas state) >>= single . diCtors of
            Nothing -> pure Nothing
            Just constructor -> do
              shape <- constructorRuntimeShape depth normalized constructor
              case shape of
                Just (_, [(baseIndex, baseFieldType)], erased) -> do
                  baseFieldMatches <-
                    unify emptyCtx baseFieldType base
                  pure $ do
                    guard baseFieldMatches
                    evidenceIdentity <- selectedEvidence
                    let representedType = quote evaluation depth normalized
                        baseType = quote evaluation depth (force evaluation base)
                        certificate =
                          RefinementRepresentationCertificate
                            { rrcContext = context
                            , rrcRepresentedType = representedType
                            , rrcTypeIdentity =
                                representationTypeIdentity context representedType
                            , rrcRefinementEvidenceIdentity = evidenceIdentity
                            , rrcBaseType = baseType
                            , rrcBaseTypeIdentity =
                                representationTypeIdentity context baseType
                            , rrcConstructor = constructor
                            , rrcRetainedBaseField =
                                ConstructorFieldPath constructor baseIndex
                            , rrcErasedEvidenceFields = sort (nub erased)
                            , rrcProfileRestrictions =
                                sort
                                  (RequireUnboxedRefinement
                                    : commonRepresentationRestrictions)
                            , rrcCertificateVersion = 1
                            , rrcCheckerVersion = 1
                            }
                    guard
                      (verifyRefinementRepresentationCertificate certificate
                        == Right ())
                    pure certificate
                _ -> pure Nothing
    _ -> pure Nothing

selectedRepresentationEvidenceIdentity
  :: RepresentationContext
  -> Int
  -> GName
  -> Value
  -> CheckM (Maybe Text)
selectedRepresentationEvidenceIdentity context depth trait represented = do
  saved <- get
  goal <- globalValueM trait [(Expl, represented)]
  selected <- traitEvidence emptyCtx noSpan goal
  identity <- case selected of
    Nothing -> pure Nothing
    Just evidence -> do
      zonkedEvidence <- zonkTermM depth evidence
      pure
        (Just
          (Kappa.Representation.representationEvidenceIdentity
            context
            zonkedEvidence))
  put saved
  pure identity

-- | Generalize exactly one completed declaration component.  Incremental body
-- closeout carries the positive SCC identity directly; it never constructs the
-- complement of the current module.
-- Rebuild propagation inside 'generalizeDeclarationUniverses' is deliberately
-- unchanged, so every consumer of a newly published call spine is still
-- rewritten regardless of whether that consumer is itself a candidate.
generalizeDeclarationUniverseOwners
  :: Set GName
  -> Set GName
  -> Set GName
  -> Set GName
  -> UniversePublicationConsumers
  -> Set GName
  -> CheckM ()
generalizeDeclarationUniverseOwners
    preexisting
    preexistingCtors
    sourceGlobals
    sourceCtors
    publicationConsumers
    owners
  | Set.null owners = pure ()
  | otherwise =
      generalizeDeclarationUniversesWith
        PreserveDeferredExplicitUniverses
        (GeneralizeOnly owners)
        (Just publicationConsumers)
        preexisting
        preexistingCtors
        sourceGlobals
        sourceCtors

-- | Check a resolved module: two passes (headers then bodies), per the
-- preceding-signature recursion rule (§15.16, §9.2).
checkModule :: CheckState -> Module -> (CheckState, Diagnostics)
checkModule st0 m =
  -- Sets, not lists: every let consults sigNames and every signature
  -- consults siglessLets, so list membership made large modules
  -- quadratic (measured ~4x time per size doubling at 16k+ decls)
  let sigNames = Set.fromList [nameText n | DSig _ n _ _ <- modDecls m]
      siglessLets =
        Set.fromList
          [ nameText n
          | DLet _ (LetDef (Just n) _ _ _ _ _ _ _ _) _ <- modDecls m
          , not (nameText n `Set.member` sigNames)
          ]
      termNames = Set.fromList [GName (csModule st0) nm | nm <- signedLetNames sigNames (modDecls m)]
      preexisting = Map.keysSet (csGlobals st0)
      preexistingCtors = Map.keysSet (csCtors st0)
      (sourceGlobals, sourceCtors) = sourceDeclarationSymbols (csModule st0) (modDecls m)
      expectDecls = [declaration | declaration@DExpect {} <- modDecls m]
      ordinaryDecls = [declaration | declaration <- modDecls m, not (isExpectDecl declaration)]
      expectNames =
        Set.fromList
          [ nameText name
          | DExpect _ form _ <- expectDecls
          , name <- case form of
              ExpectTerm n _ -> [n]
              ExpectType n _ _ -> [n]
              ExpectData n _ _ -> [n]
              ExpectTrait n _ _ -> [n]
          ]
      declarationInfos =
        [ (declaration, provided, declarationDependencies declaration)
        | declaration <- ordinaryDecls
        , let (providedGlobals, providedConstructors) =
                sourceDeclarationSymbols (csModule st0) [declaration]
              provided =
                Set.map gnameText
                  (Set.union providedGlobals providedConstructors)
        ]
      expectDependentNames =
        closeDeclarationDependencies declarationInfos $
          Set.unions
            [ Set.union
                (Set.intersection provided expectNames)
                ( if Set.null (Set.intersection expectNames dependencies)
                    then Set.empty
                    else provided
                )
            | (_, provided, dependencies) <- declarationInfos
            , not (Set.null (Set.intersection expectNames dependencies))
                || not (Set.null (Set.intersection provided expectNames))
            ]
      expectationProvider declaration =
        maybe False ((`Set.member` expectNames) . nameText)
          (declarationUniverseName declaration)
      preExpectOrdinary declaration =
        not (expectationProvider declaration)
          && let (providedGlobals, providedConstructors) =
                   sourceDeclarationSymbols (csModule st0) [declaration]
                 provided =
                   Set.map gnameText
                     (Set.union providedGlobals providedConstructors)
              in Set.null (Set.intersection provided expectDependentNames)
      preExpectOrdinaryDecls = filter preExpectOrdinary ordinaryDecls
      remainingOrdinaryDecls =
        [ declaration
        | declaration <- ordinaryDecls
        , not (preExpectOrdinary declaration)
        ]
      passes = do
        validateModuleConstructorBindings (modDecls m)
        mapM_ predeclarePass (modDecls m)
        -- An expectation may mention ordinary same-module declarations from
        -- another selected fragment. Elaborate every header whose identity is
        -- independent of the expectation first, preserving the established
        -- source order between data constructors, traits, signatures, and
        -- transparent aliases. Matching implementations and aliases that
        -- transitively depend on an expectation-provided identity remain in
        -- the post-expect phase, so they cannot overwrite their own contract.
        mapM_ (headerPassIn siglessLets) preExpectOrdinaryDecls
        -- §9.4 module fragments have no semantic declaration order. Register
        -- their contracts before elaborating any selected implementation
        -- header, even when a fragment suffix sorts before the common source
        -- file. The preceding shape pass still makes mutually referenced data
        -- family names available while these signatures are elaborated.
        mapM_
          (\declaration ->
             withDeclarationUniverseSchema declaration $
               case declaration of
                 DExpect _ form site -> headerExpect preexisting form site
                 _ -> pure ())
          expectDecls
        mapM_ (headerPassIn siglessLets) remainingOrdinaryDecls
        -- §10.4: once every data type's constructor types are
        -- elaborated, check strict positivity over the whole module's
        -- data group by fixed-point iteration and record each accepted
        -- type's parameter-positivity signature
        positivityPass (modDecls m)
        -- §14.3: register every top-level instance head before any
        -- body is checked, so instance visibility within the module
        -- does not depend on declaration order
        mapM_ instanceHeadPass (modDecls m)
        planDerivedDeclarations (modDecls m)
        -- Header/signature evidence now sees the complete instance set. Keep
        -- declaration universe interfaces provisional while bodies are
        -- elaborated: body edges are part of the semantic declaration SCC,
        -- and §11.1.2.4A permits exactly one principal solve after the
        -- complete SCC has been checked.
        beforeHeaderEvidencePublication <- get
        do
          flushPendingBeforeUniverseFinalization
          synchronizeGeneratedConstraintInterfaces beforeHeaderEvidencePublication
        headerState <- get
        let deferredInstanceDictionaries =
              Set.fromList
                [ piDictG preInstance
                | Just preInstance <- Map.elems (csPreInstances headerState)
                , let GName owner _ = piDictG preInstance
                , owner == csModule headerState
                ]
            -- An instance dictionary's semantic declaration includes every
            -- member body. Generalizing its normalized head after the
            -- instance-head pass alone would freeze occurrence ceilings before
            -- those bodies contribute their constraints, exactly like
            -- finalizing a signed let before checking its definition.
            deferredInterfaces =
              declarationUniverseDeferralClosure
                headerState
                (Set.union termNames deferredInstanceDictionaries)
        do
          generalizeDeclarationUniverses
            preexisting preexistingCtors sourceGlobals sourceCtors deferredInterfaces
          synchronizeGeneratedConstraintInterfaces headerState
        -- Static declarations such as type aliases have no body-pass event.
        -- If initial SCC generalization made one of their pending universe
        -- obligations physical, publish that call-spine delta now so every
        -- signature retained during the header pass is repaired before its
        -- definition is checked. Deferred semantic interfaces remain open and
        -- are published by the completed-component sweep below.
        initialUniverseState <- get
        let finalizedPendingOwners =
              Set.difference
                (Map.keysSet (csPendingUniverseProofs initialUniverseState))
                deferredInterfaces
        mapM_ materializePendingUniverseProofs
          (Set.toAscList finalizedPendingOwners)
        -- Runtime dictionary layout is representation metadata, not a source
        -- ordering effect. Header checking can already prove fields erased
        -- from local/supertrait evidence, while the remaining fields may need
        -- module-global instance heads and the principalized header-universe
        -- interfaces above. Finalize exactly here: both authorities are now
        -- complete, but no instance dictionary body or backend IR has yet been
        -- built from the member quantities.
        finalizeTraitMemberRepresentations
        finalizeDerivedRefinementDeclarations (modDecls m)
        initialPublicationState <- get
        let initialPublicationConsumers =
              universePublicationConsumers initialPublicationState
            elaborateBodies _ _ _ [] = pure ()
            elaborateBodies remaining closeIndex publicationConsumers0 (declaration : rest) = do
              bodyPassIn siglessLets declaration
              current <- get
              let completedBodies =
                    Set.intersection remaining
                      (declarationBodyUniverseOwners current declaration)
                  completedBodiesWithCore =
                    Set.filter (`Map.member` csCoreBodies current) completedBodies
                  -- A body diagnostic can leave an owner without retained
                  -- Core.  Keep that identity open so callers cannot publish
                  -- through a body that was never available for dependency
                  -- analysis.
                  remaining' = Set.difference remaining completedBodiesWithCore
                  completedBodyTerms =
                    Map.map pure
                      (Map.restrictKeys
                        (csCoreBodies current)
                        completedBodiesWithCore)
                  publicationConsumers =
                    extendUniversePublicationConsumers
                      completedBodyTerms
                      publicationConsumers0
                  openDependencies owner =
                    fmap
                      (Set.intersection remaining . expandedGlobalsOfTerm current)
                      (Map.lookup owner (csCoreBodies current))
                  (completedComponents, closeIndex') =
                    recordDependencyCompletions
                      completedBodiesWithCore
                      openDependencies
                      closeIndex
                  newlyClosedTermOwners =
                    Set.intersection termNames completedComponents
                  needsUniverseClose owner =
                    owner `Set.notMember` csFinalizedUniverseInterfaces current
                      && maybe
                           False
                           (not . globalDefinitionBodyUniversesReplayable)
                           (Map.lookup owner (csGlobals current))
                  ownersNeedingProvisionalClose =
                    Set.filter needsUniverseClose newlyClosedTermOwners
              -- Body checking can add further interface-closed obligations.
              -- Publish those proof binders only for a completed dependency
              -- component, so following declarations elaborate the complete
              -- call spine.  A body that still references an open declaration
              -- remains part of that declaration SCC and is left untouched.
              -- Do not run the global universe solver here: declarations still
              -- in 'remaining'' must see one order-independent solve.
              mapM_ materializeOwnedInterfaceUniverseProofs
                (Set.toAscList completedComponents)
              unless (Set.null ownersNeedingProvisionalClose) $ do
                -- Replayability is an owner-local solver fact, not an SCC
                -- membership test.  Rewrite the complete closed component so
                -- any subsequent publication remains atomic across mutual
                -- callers even when only one body introduced occurrence metas.
                closeCompletedProvisionalBodyUniverses newlyClosedTermOwners
                afterClose <- get
                let unresolvedOwners =
                      Set.filter
                        (\owner ->
                           maybe
                             False
                             (not . globalDefinitionBodyUniversesReplayable)
                             (Map.lookup owner (csGlobals afterClose)))
                        newlyClosedTermOwners
                unless (Set.null unresolvedOwners) $ do
                  beforeIncrementalGeneralization <- get
                  generalizeDeclarationUniverseOwners
                    preexisting
                    preexistingCtors
                    sourceGlobals
                    sourceCtors
                    publicationConsumers
                    newlyClosedTermOwners
                  afterIncrementalGeneralization <- get
                  let changedInterfaces =
                        Set.unions
                          [ generatedConstraintInterfacesAffectedBy
                              owner
                              beforeIncrementalGeneralization
                              afterIncrementalGeneralization
                          | owner <- Set.toAscList newlyClosedTermOwners
                          ]
                  synchronizeGeneratedConstraintInterfacesFor
                    (Just changedInterfaces)
                    beforeIncrementalGeneralization
              elaborateBodies
                remaining'
                closeIndex'
                publicationConsumers
                rest
        elaborateBodies
          (Set.union termNames deferredInstanceDictionaries)
          emptyDependencyFrontier
          initialPublicationConsumers
          (modDecls m)
        -- Finalize body-owned occurrence choices before committing deferred
        -- evidence. Generated level propositions may mention those occurrence
        -- metas, so final evidence search must observe the principal SCC
        -- solution rather than diagnosing the provisional variables. The
        -- resulting proof terms are still available before termination.
        beforeFinalUniverseGeneralization <- get
        do
          generalizeDeclarationUniverses
            preexisting preexistingCtors sourceGlobals sourceCtors Set.empty
          synchronizeGeneratedConstraintInterfaces beforeFinalUniverseGeneralization
        -- The final generalization pass can turn occurrence-meta relations
        -- into rigid owner-parameter obligations. They did not exist during
        -- the per-body sweep above, so give every remaining current-module
        -- owner the same interface-closed proof-binder materialization before
        -- the final solver judges residual constraints.
        finalUniverseState <- get
        let finalConstraintOwners =
              Set.fromList
                [ owner
                | constraint <- csLevelConstraints finalUniverseState
                , Just owner@(GName ownerModule _) <-
                    [Map.lookup (lcIdentity constraint) (csLevelConstraintOwners finalUniverseState)]
                , ownerModule == csModule finalUniverseState
                ]
        mapM_ materializeOwnedInterfaceUniverseProofs
          (Set.toAscList finalConstraintOwners)
        levelDiagCount <- gets (length . csDiags)
        levelOk <- solveDeferredLevelConstraints True
        levelDiagCount' <- gets (length . csDiags)
        levelFailureExplained <- gets $ \state ->
          any (levelConstraintFailureAlreadyReported state)
            (csLevelConstraints state)
        unless (levelOk || levelDiagCount' > levelDiagCount || levelFailureExplained) $ do
          residualState <- get
          let pending = csLevelConstraints residualState
              assignments = csLevelAssignments residualState
          let renderConstraint constraint =
                renderLevel (substituteLevelMetas assignments (lcLhs constraint))
                  <> " <= "
                  <> renderLevel (substituteLevelMetas assignments (lcRhs constraint))
              summary = T.intercalate ", " (map renderConstraint (take 6 pending))
              renderOwner constraint =
                case Map.lookup (lcIdentity constraint) (csLevelConstraintOwners residualState) of
                  Nothing -> "<unowned>#" <> T.pack (show (lcIdentity constraint))
                  Just owner ->
                    let arity =
                          (dutParameterCount . gdUniverses <$> Map.lookup owner (csGlobals residualState))
                            <|> (dutParameterCount . ciUniverses <$> Map.lookup owner (csCtors residualState))
                        relation =
                          UniverseConstraint
                            (normalizeLevel (substituteLevelMetas assignments (lcLhs constraint)))
                            (normalizeLevel (substituteLevelMetas assignments (lcRhs constraint)))
                        binderPresent =
                          case (arity, Map.lookup owner (csGlobals residualState)) of
                            (Just parameterCount, Just definition) ->
                              any (equivalentUniverseConstraint relation)
                                (declarationConstraintSummary parameterCount (globalCoreType (ecOf residualState) definition))
                            _ -> False
                     in gKey owner
                          <> "#"
                          <> T.pack (show (lcIdentity constraint))
                          <> "[arity="
                          <> maybe "missing" (T.pack . show) arity
                          <> ",binder="
                          <> (if binderPresent then "yes" else "no")
                          <> ",assumptions="
                          <> renderLevelAssumptions (lcAssumptions constraint)
                          <> "]"
              ownerSummary = T.intercalate ", " (map renderOwner (take 6 pending))
          unless (null pending) $
            report $
              withPayload
                ( withPayloadField "residualConstraintOwners" ownerSummary
                    $ withPayloadField "residualConstraints" summary
                    $ payloadKind "universe-constraint-residual"
                ) $
                diag SevError StageElaborate "E_UNSOLVED_METAVARIABLE"
                  (Just "kappa.type.unsolved-metavariable")
                  (Span "<universe-inference>" (Pos 1 1) (Pos 1 1))
                  ( "universe constraints have no principal order-independent solution: "
                      <> summary
                      <> " (§11.1.3)"
                  )
        flushPendingFinal
        when levelOk $ do
          evidenceClosed <- closeFinalEvidenceUniverses
          when evidenceClosed $ do
            finalizeDiscardedResults
            repairFinalizedGeneratedConstraintEvidence
        -- Termination consumes both the finalized level assignments and the
        -- erased relation evidence they determine. Running SCT earlier would
        -- observe provisional occurrence metas or unresolved proof terms.
        terminationSccPass
        finalizeDeferredSignatureHoles
        sigSatisfactionPass
        -- §8.5.2: now that this module's bodies (and any in-module proofs
        -- that rely on an opaque definition unfolding) are checked, seal
        -- the module's 'opaque' definitions against δ-unfolding downstream.
        opaqueSealPass
        finalizeTraitDictionaryInterfaces
      (_, st1) =
        runState
          passes
          ( st0
              { csSigPending = Map.empty
              , csPreInstances = Map.empty
              , csDerivedDecls = Map.empty
              , csTerminationNames = termNames
              , csTerminationDecls = Map.empty
              , csAssertTerminates = Set.empty
              , csAssertReducible = Set.empty
              }
          )
      st2 = compactCompletedModuleUniverseState st1
   in -- 'report' prepends; restore emission (source) order here
      (st2 {csDiags = []}, reverse (csDiags st1))
  where
    isExpectDecl DExpect {} = True
    isExpectDecl _ = False

    declarationDependencies :: Data a => a -> Set Text
    declarationDependencies value =
      case cast value of
        Just expression ->
          Set.fromList (map (nameText) (freeVarOccurrences expression))
        Nothing -> Set.unions (gmapQ declarationDependencies value)

    closeDeclarationDependencies infos = go
      where
        go dependent =
          let newlyDependent =
                Set.unions
                  [ provided
                  | (_, provided, dependencies) <- infos
                  , not (Set.null (Set.intersection dependent dependencies))
                  ]
              dependent' = Set.union dependent newlyDependent
           in if dependent' == dependent then dependent else go dependent'

-- Pre-register only the shape of data type-constructor names so declarations
-- in one file may refer to data types declared later (§10.1: declaration
-- order within a module is immaterial for type references).  This pass must
-- not elaborate source annotations: those may mention term interfaces (for
-- example a TypeLevel operator declared by an earlier @expect term@), and the
-- real header pass is the authority that checks them.
predeclarePass :: Decl -> CheckM ()
predeclarePass declaration =
  withDeclarationUniverseSchema declaration (predeclarePassRaw declaration)

-- | Header pass, knowing which module-level lets have no signature: a
-- signature whose type mentions such a name (a reified static object,
-- §2.8.3) is deferred to the body pass, where the binding's value is
-- available in declaration order.
headerPassIn :: Set Text -> Decl -> CheckM ()
headerPassIn siglessLets declaration =
  case signatureDeclarationName declaration of
    Just signatureName ->
      withNamedHoleScope Map.empty (deferSignatureHoles signatureName) action
    Nothing ->
      withNamedHoleScope Map.empty finalizeNamedHoles action
  where
    action =
      withDeclarationUniverseSchema declaration
        (headerPassInRaw siglessLets declaration)

headerPassInRaw :: Set Text -> Decl -> CheckM ()
headerPassInRaw siglessLets = \case
  DSig _ _ tyE _
    | any (`Set.member` siglessLets) (sigHeadNames tyE) ->
        -- deferred to 'bodyPassIn' (the let's value is needed first)
        pure ()
  DSig _ n tyE sp -> do
    -- §11.3.3 (approximation): free ASCII-lowercase heads in the
    -- signature that resolve to no global are implicitly universalized
    -- as erased implicit binders; the kind is inferred from use (a
    -- fresh meta, defaulted to Type when unconstrained).
    fvs <-
      filterM
        (\name -> do
          global <- lookupGlobalName name
          schemaLevel <- gets (Map.lookup name . csActiveUniverseSchema)
          pure (isNothing global && isNothing schemaLevel)
        )
        (nub (freeLower tyE))
    (ctx0, inferredBindersReversed) <-
      foldM
        ( \(prefixCtx, accumulated) variable -> do
            kind <- freshMetaV prefixCtx
            let extended =
                  bindCtxMQProvisional
                    Parametric
                    Q0
                    variable
                    False
                    kind
                    prefixCtx
            pure (extended, (variable, kind, prefixCtx) : accumulated)
        )
        (emptyCtx, [])
        fvs
    let inferredBinders = reverse inferredBindersReversed
    diagCount0 <- gets (length . csDiags)
    (tyTm0, _) <- withNamedCallableInoutSignature tyE (inferType ctx0 tyE)
    universalBinders <- forM inferredBinders $ \(v, kv, prefixCtx) -> do
      kv' <- forceM kv
      kind <- case kv' of
        VFlex m [] -> do
          level <- freshLevelMeta
          solveMeta m (VSort level)
          pure (VSort level)
        _ -> pure kv'
      kindTm <- quoteIn prefixCtx kind
      markGeneralizableLevelTerm kindTm
      paramKind <- isParametricKind (ctxLen prefixCtx) kind
      pure (v, if paramKind then Parametric else Ordinary, if paramKind then FormationParametric else FormationOrdinary, if paramKind then Q0 else QW, kindTm)
    let tyTm = foldr (\(v, mode, formation, q, kT) acc -> CPiFormedM mode formation Impl q False v kT acc) tyTm0 universalBinders
    tyV <- evalIn emptyCtx tyTm
    g <- ownName n
    exists <- gets (Map.member g . csGlobals)
    isExpected <- gets (Map.member g . csExpects)
    when (exists && not isExpected) $ do
      enrich <- duplicateRelated (nameText n) g sp
      report $ enrich $
        diag SevError StageElaborate "E_DUPLICATE_DECLARATION" (Just "kappa-hs.name.duplicate") sp
          ("duplicate declaration of '" <> nameText n <> "'")
    recordDeclSite g sp
    addGlobal g (GlobalDef tyV Nothing False)
    -- The semantic value intentionally makes cumulative lifts transparent.
    -- Retain the checked signature until its complete declaration SCC is
    -- generalized; installing it in 'gdCoreType' here would change the
    -- semantic interface used to check the body.
    modify' $ \state ->
      state
        { csCoreSignatures =
            Map.insert g tyTm (csCoreSignatures state)
        }
    precertifyLevelOperatorAlias g
    recordSignatureInoutParams g tyE
    -- §9.1: the signature awaits its same-file definition (an expected
    -- name is governed by §9.4 satisfaction instead)
    diagCount1 <- gets (length . csDiags)
    unless (isExpected || diagCount1 > diagCount0) $
      modify' $ \st -> st {csSigPending = Map.insert g sp (csSigPending st)}
  DData mods dd sp -> do
    -- §22.1: an 'opaque data' representation is inspectable only in
    -- its defining module
    when (dmOpaque mods) $ do
      g <- ownName (ddName dd)
      modify' $ \st -> st {csOpaqueDatas = Map.insert g () (csOpaqueDatas st)}
    headerData dd sp
  DTypeAlias _ n params _ (Just rhs) sp
    | nameText n `elem` allNamesIn rhs -> do
        -- §15.16 admits recursive type-alias groups only "when
        -- admitted"; this implementation does not admit them (aliases
        -- are transparent definitions, §11.3) — recursion needs a data
        -- declaration. The alias is salvaged as a fresh metavariable
        -- so downstream uses do not cascade.
        errAt sp "E_RECURSIVE_TYPE_ALIAS" (Just "kappa-hs.type.recursive-alias")
          ("type alias '" <> nameText n
             <> "' refers to itself; recursive type aliases are not admitted (§15.16) — use a data declaration")
        g <- ownName n
        noteDefinition g sp
        modify' $ \st ->
          st {csUniverseInterfaceValues = Set.insert g (csUniverseInterfaceValues st)}
        tyV <- aliasKind params
        mv <- freshMetaV emptyCtx
        addGlobal g (GlobalDef tyV (Just mv) True)
  DTypeAlias mods n params mkind (Just rhs) sp -> do
    -- alias: a definition at a universe type
    (tm, ty) <- elabAliasBody params mkind rhs
    g <- ownName n
    noteDefinition g sp
    modify' $ \st ->
      st {csUniverseInterfaceValues = Set.insert g (csUniverseInterfaceValues st)}
    -- §8.5.2: an 'opaque' type alias is transparent only within its
    -- defining module; sealed at module end ('opaqueSealPass').
    when (dmOpaque mods) $
      modify' $ \st -> st {csOpaqueDefs = Map.insert g () (csOpaqueDefs st)}
    -- §22.2: remember the written field order of a record alias for
    -- derivation-shape reflection (core records are canonicalized)
    case rhs of
      ERecordType rfs Nothing _ ->
        modify' $ \st ->
          st {csRecordOrders = Map.insert g [nameText (rtfName f) | f <- rfs] (csRecordOrders st)}
      _ -> pure ()
    -- Evaluation is transparent through CUniverseLift, so re-quoting the
    -- alias value later cannot recover cumulative-lift evidence. Retain the
    -- elaborated alias body exactly as for term definitions; KCoreText and
    -- interface artifacts serialize this proof-carrying form.
    recordCoreBody g tm
    tmV <- evalIn emptyCtx tm
    observation <- aliasRhsObservation emptyCtx (gnameText g) tm ty
    addGlobal g (globalDefWithObservationMode (ojMode observation) (GlobalDef ty (Just tmV) True))
  DTypeAlias _ n params _ Nothing _ -> do
    g <- ownName n
    tyV <- aliasKind params
    addGlobal g (GlobalDef tyV Nothing False)
  DTrait _ td sp -> headerTrait td sp
  -- §18.1: a top-level (non-scoped) effect declaration registers a
  -- module-wide effect interface; a `scoped effect` is handled lexically by
  -- hoistScopedEffects in the block where it appears (so it is skipped here).
  DEffect mods eff sp
    | dmScoped mods -> pure ()
    | effIsLabelDecl eff -> elabTopEffectLabel eff sp
    | otherwise -> elabTopEffect eff sp
  -- Expectations are one dedicated module-header phase in 'checkModule'.
  -- Re-entering them here after an implementation header would make hidden
  -- universe generalization depend on fragment filename order.
  DExpect {} -> pure ()
  DInstance inst sp -> do
    bootstrap <- compilerOwnedTypeLevelInstance inst
    when bootstrap (instanceHeadPass (DInstance inst sp))
  -- §4.4: register the wrapped definition's header like any other; the
  -- assertion prefix only affects termination checking and gating, which
  -- happen in the body pass.
  DUnsafeAssert _ inner _ -> headerPassInRaw siglessLets inner
  _ -> pure ()

aliasKind :: [Binder] -> CheckM Value
aliasKind params = do
  tele <- elabTele emptyCtx params
  evalIn emptyCtx (foldr telePi (CSort LZero) tele)

elabAliasBody :: [Binder] -> Maybe Expr -> Expr -> CheckM (Term, Value)
elabAliasBody params mkind rhs = do
  (tm0, kindTm0) <- go emptyCtx params
  tm <- zonkTermM 0 tm0
  kindTm <- zonkTermM 0 kindTm0
  tyV <- evalIn emptyCtx kindTm
  pure (tm, tyV)
  where
    go ctx [] = do
      -- an eta-reduced alias body may itself be a (partially applied)
      -- type former of higher kind ('type Equal (@0 a) = (=) a', §3.5.1)
      case mkind of
        Just kindE -> do
          (kindTm, _) <- inferType ctx kindE
          kindV <- evalIn ctx kindTm
          tm <- check ctx rhs kindV
          pure (tm, kindTm)
        -- A type alias declaration is a static, capability-preserving
        -- definition site. Parametric inputs may shape its RHS; ordinary
        -- observation is checked when the alias value reaches an ordinary
        -- sink, not while constructing the alias itself.
        Nothing -> do
          (tm, kindTm) <- inferAliasRhsKind ctx
          pure (tm, kindTm)
    go ctx (b : rest) = do
      (domTm, ownKindMeta, coerced, mSource) <- case bType b of
        Just t -> do
          domE <- normalizeBinderDomain ctx b t
          (term, _, wasCoerced) <-
            withGeneralizableBareTypeLevels $
              if bImplicit b
                then inferTypeBoolProp' ctx domE
                else (\(term', level) -> (term', level, False)) <$> inferType ctx domE
          pure (term, Nothing, wasCoerced, Just domE)
        Nothing -> do
          meta <- freshMetaId
          pure (CMeta meta, Just meta, False, Nothing)
      domV <- evalIn ctx domTm
      let nm = maybe "_" nameText (bName b)
          ic = if bImplicit b then Impl else Expl
          prefix = bPrefix b
          ordinaryDefault = if coerced then Q0 else headerBinderQ b
          provisionalMode = fromMaybe Parametric (bpObservation prefix)
          provisionalQ =
            maybe
              (if provisionalMode == Parametric then Q0 else ordinaryDefault)
              (qOf . Just)
              (bpQuantity prefix)
      (initialMode, initialQ) <- case ownKindMeta of
        Nothing -> resolveBinderModeQ ctx b domV ordinaryDefault
        Just _ -> pure (provisionalMode, provisionalQ)
      mBound <- case mSource of
        Just source -> levelAssumptionFromExpr ctx (Just domTm) source
        Nothing -> pure Nothing
      ctxWithBound <- extendLevelAssumption (bSpan b) ctx mBound
      let ctx' = bindCtxMQ initialMode initialQ nm False domV ctxWithBound
      (tm, innerK) <- go ctx' rest
      -- §11.3.3: only the kind metavariable introduced for this genuinely
      -- unannotated declaration parameter may take the floating-Type default.
      -- Commit that default after the RHS has had a chance to infer a more
      -- specific domain, then resolve observation mode from the final domain.
      forM_ ownKindMeta $ \meta -> do
        solution <- gets (Map.lookup meta . csMetas)
        case solution of
          Just Nothing -> do
            level <- freshLevelMeta
            solveMeta meta (VSort level)
            markGeneralizableLevelTerm (CSort level)
          _ -> pure ()
      (mode, q) <- case ownKindMeta of
        Nothing -> pure (initialMode, initialQ)
        Just _ -> do
          finalDomain <- forceM domV
          resolveBinderModeQ ctx b finalDomain ordinaryDefault
      finalDomain <- forceM domV
      formation <- selectFormationMode ctx mode finalDomain
      pure
        ( CLamM mode ic q nm tm
        , CPiBoundFormedM mode formation ic q False nm mBound domTm innerK
        )
    inferAliasRhsKind ctx = do
      (tm0, ty0) <- inferT ctx rhs
      tyF <- forceM ty0
      former <- finalIsSort ctx tyF
      case tyF of
        VSort lvl -> pure (tm0, CSort lvl)
        VFlex m [] -> do
          level <- freshLevelMeta
          solveMeta m (VSort level)
          pure (tm0, CSort level)
        VPi {} | former -> do
          kTm <- quoteIn ctx tyF
          pure (tm0, kTm)
        other -> do
          oT <- quoteIn ctx other
          errAt (exprSpan rhs) "E_NOT_A_TYPE" (Just "kappa.type.mismatch")
            ("expected a type; this expression has type " <> renderTerm oT)
          pure (tm0, CSort LZero)

headerData :: DataDecl -> Span -> CheckM ()
headerData declaration sp = do
  g <- ownName (ddName declaration)
  ensureTopLevelDataFamilyHeader g
  prepared <- gets (Map.lookup g . csTopLevelDataHeaders)
  case prepared of
    Just (PreparedTopLevelDataHeader paramTele sortT dataLevel) -> do
      finishDataHeaderIn emptyCtx [] declaration sp paramTele sortT dataLevel
      modify' $ \st ->
        st
          { csTopLevelDataHeaders =
              Map.delete g (csTopLevelDataHeaders st)
          }
    _ ->
      -- A declaration may reach this path without the module shape pass only
      -- in checker-internal/local construction. Preserve the same semantic
      -- split rather than reconstructing a source-shaped approximation.
      headerDataIn emptyCtx [] declaration sp

-- | Focused producer-side invariant for proof-only metadata. This invokes the
-- same role requirement function used by trait publication, rather than the
-- lower-level occurrence collector tested independently in CoreOps.
sourceRoleMetadataInvarianceChecks :: Bool
sourceRoleMetadataInvarianceChecks =
  directRoles == expectedRoles
    && fixedPointRoles family == Just expectedRoles
    && fixedPointRoles malformedFamily == Just [Invariant, Invariant, Invariant]
    && fixedPointRoles missingEvidenceFamily == Just [Invariant, Invariant, Irrelevant]
    && fixedPointRoles contradictoryEvidenceFamily == Just [Invariant, Invariant, Irrelevant]
    && fixedPointRoles argumentArityFamily == Just [Invariant, Invariant, Invariant]
    && fixedPointRoles forgedRoleFamily == Just [Invariant, Invariant, Irrelevant]
    && fixedPointRoles forgedCertificateFamily == Just [Invariant, Invariant, Irrelevant]
    && fixedPointRoles forgedEvidenceFamily == Just [Invariant, Invariant, Invariant]
    && fixedPointRoles nestedMalformedFamily == Just [Invariant, Invariant, Invariant]
    && fixedPointRoles partialFamily == Just [Invariant]
    && nccRoleActions constructorLocalUniverseClause == [NominalCovariantUse 0]
    && installedSummaryRoles family == Just expectedRoles
    && installedSummaryRoles dataFamily == Just expectedRoles
  where
    family = GName (ModuleName ["test", "role-metadata"]) "Family"
    malformedFamily = GName (ModuleName ["test", "role-metadata"]) "Malformed"
    missingEvidenceFamily = GName (ModuleName ["test", "role-metadata"]) "MissingEvidence"
    contradictoryEvidenceFamily = GName (ModuleName ["test", "role-metadata"]) "ContradictoryEvidence"
    argumentArityFamily = GName (ModuleName ["test", "role-metadata"]) "ArgumentArity"
    forgedRoleFamily = GName (ModuleName ["test", "role-metadata"]) "ForgedRole"
    forgedCertificateFamily = GName (ModuleName ["test", "role-metadata"]) "ForgedCertificate"
    forgedEvidenceFamily = GName (ModuleName ["test", "role-metadata"]) "ForgedEvidence"
    nestedMalformedFamily = GName (ModuleName ["test", "role-metadata"]) "NestedMalformed"
    partialFamily = GName (ModuleName ["test", "role-metadata"]) "Partial"
    dataFamily = GName (ModuleName ["test", "role-metadata"]) "DataFamily"
    dataConstructor = GName (ModuleName ["test", "role-metadata"]) "MkDataFamily"
    liftFamily = GName (ModuleName ["test", "role-metadata"]) "LiftFamily"
    expectedRoles = [Covariant, Covariant, Irrelevant, Irrelevant, Irrelevant]
    constructorLocalUniverseClause =
      nominalClosureClause
        1
        ClausePointConstructor
        "test.role-metadata.constructor-local-universe"
        [ RequireCovariant 0 "family prefix"
        , RequireInvariant 1 "constructor-local suffix"
        ]
        (CSort (LParam 1))
    proofAt index = CSort (LParam index)
    erasedAt index =
      RuntimeErased
        (RuntimeErasedEvidence (proofAt index) (proofAt index) (proofAt index))
    evidence =
      UniverseEvidence
        [UniverseEvidenceStep (LParam 0) (LParam 1) [(LParam 0, LParam 1)]]
    liftClosure =
      makeNominalSignatureClosure
        1
        []
        1
        [ NominalClosureClause
            ClauseSortDeclaration
            "test.role-metadata.LiftFamily"
            []
            "Type"
            [NominalCovariantUse 0]
            NominalPreserveRepresentation
        ]
    liftSummary =
      makeNominalCumulativitySummary
        (gKey liftFamily)
        [Covariant]
        [False]
        liftClosure
        Nothing
    lifted = CUniverseLift (LParam 0) (LParam 1) evidence (CSort LZero)
    schemaLifted =
      CSchemaLift
        liftFamily
        [LParam 0]
        [LParam 1]
        [Covariant]
        [SchemaCovariantEvidence evidence]
        (ncsCertificateId liftSummary)
        [proofAt 3]
        [proofAt 3]
        (CSort LZero)
    erasedArgument = CAppM Expl (erasedAt 4) (CGlob prelUnit) (CGlob prelUnit)
    clauses = [lifted, schemaLifted, erasedArgument]
    requirements =
      evalState
        (traitNominalRequirements Map.empty family clauses)
        directState
    directRoles = inferUniverseRoles 5 requirements
    malformedClause =
      CSchemaLift
        prelList
        [LParam 0, LParam 1]
        [LParam 2]
        [Covariant]
        [SchemaCovariantEvidence evidence]
        (SchemaActionCertificateId "test.source-role-metadata.malformed")
        []
        []
        (CSort LZero)
    missingEvidenceClause =
      CSchemaLift
        prelList
        [LParam 0]
        [LParam 1]
        [Covariant]
        []
        (SchemaActionCertificateId "test.source-role-metadata.missing-evidence")
        []
        []
        (CSort LZero)
    contradictoryEvidenceClause =
      CSchemaLift
        prelList
        [LParam 0]
        [LParam 1]
        [Covariant]
        [SchemaInvariantEvidence]
        (SchemaActionCertificateId "test.source-role-metadata.contradictory-evidence")
        []
        []
        (CSort LZero)
    argumentArityClause =
      CSchemaLift
        prelList
        [LParam 0]
        [LParam 1]
        [Covariant]
        [SchemaCovariantEvidence evidence]
        (SchemaActionCertificateId "test.source-role-metadata.argument-arity")
        [proofAt 2]
        []
        (CSort LZero)
    forgedRoleClause =
      CSchemaLift
        liftFamily
        [LParam 0]
        [LParam 1]
        [Irrelevant]
        [SchemaIrrelevantEvidence]
        (ncsCertificateId liftSummary)
        [CSort LZero]
        [CSort LZero]
        (CSort LZero)
    forgedCertificateClause =
      CSchemaLift
        liftFamily
        [LParam 0]
        [LParam 1]
        [Covariant]
        [SchemaCovariantEvidence evidence]
        (SchemaActionCertificateId "test.source-role-metadata.forged")
        [CSort LZero]
        [CSort LZero]
        (CSort LZero)
    forgedEvidenceClause =
      CSchemaLift
        liftFamily
        [LParam 0]
        [LParam 1]
        [Covariant]
        [SchemaCovariantEvidence (UniverseEvidence [UniverseEvidenceStep (LParam 2) (LParam 2) []])]
        (ncsCertificateId liftSummary)
        [CSort LZero]
        [CSort LZero]
        (CSort LZero)
    nestedMalformedArgument =
      CSchemaLift
        liftFamily
        [LParam 0]
        [LParam 1]
        [Covariant]
        []
        (ncsCertificateId liftSummary)
        [proofAt 2]
        [CSort LZero]
        (CSort LZero)
    nestedMalformedClause =
      CSchemaLift
        liftFamily
        [LParam 0]
        [LParam 1]
        [Covariant]
        [SchemaCovariantEvidence evidence]
        (ncsCertificateId liftSummary)
        [CSort LZero]
        [nestedMalformedArgument]
        (CSort LZero)
    partialClause = CGlobal liftFamily [LParam 0]
    definition arity =
      globalDefWithUniverses
        (DeclarationUniverseTelescope arity True)
        (GlobalDef (VSort LZero) Nothing False)
    definitionWithConstraint arity =
      globalDefWithCoreType
        ( CPiEvidenceM
            Ordinary FormationOrdinary Impl Q0 False "uLe"
            (Just (LParam 0, LParam 1)) BinderGenerated
            (CSort LZero) (CSort LZero)
        )
        (definition arity)
    directState =
      initCheckState
        { csGlobals =
            Map.fromList
              [ (family, definitionWithConstraint 5)
              , (liftFamily, globalDefWithNominalSummary liftSummary (definition 1))
              ]
        }
    fixedPointState =
      initCheckState
        { csGlobals =
            Map.fromList
              [ (family, definitionWithConstraint 5)
              , (malformedFamily, definition 3)
              , (missingEvidenceFamily, definition 3)
              , (contradictoryEvidenceFamily, definition 3)
              , (argumentArityFamily, definition 3)
              , (forgedRoleFamily, definition 3)
              , (forgedCertificateFamily, definition 3)
              , (forgedEvidenceFamily, definition 3)
              , (nestedMalformedFamily, definition 3)
              , (partialFamily, definition 1)
              , (dataFamily, definitionWithConstraint 5)
              , (liftFamily, globalDefWithNominalSummary liftSummary (definition 1))
              ]
        , csCtors =
            Map.singleton
              dataConstructor
              CtorInfo
                { ciData = dataFamily
                , ciUniverses = DeclarationUniverseTelescope 5 True
                , ciType =
                    CPiFormedM
                      Ordinary FormationOrdinary Expl QW False "field"
                      schemaLifted
                      (CGlobal dataFamily (map LParam [0 .. 4]))
                , ciFields = []
                , ciSourceFields = []
                }
        }
    pending =
      Map.fromList
        [ (family, PendingTraitNominalSummary Nothing 0 clauses noSpan)
        , (malformedFamily, PendingTraitNominalSummary Nothing 0 [malformedClause] noSpan)
        , (missingEvidenceFamily, PendingTraitNominalSummary Nothing 0 [missingEvidenceClause] noSpan)
        , (contradictoryEvidenceFamily, PendingTraitNominalSummary Nothing 0 [contradictoryEvidenceClause] noSpan)
        , (argumentArityFamily, PendingTraitNominalSummary Nothing 0 [argumentArityClause] noSpan)
        , (forgedRoleFamily, PendingTraitNominalSummary Nothing 0 [forgedRoleClause] noSpan)
        , (forgedCertificateFamily, PendingTraitNominalSummary Nothing 0 [forgedCertificateClause] noSpan)
        , (forgedEvidenceFamily, PendingTraitNominalSummary Nothing 0 [forgedEvidenceClause] noSpan)
        , (nestedMalformedFamily, PendingTraitNominalSummary Nothing 0 [nestedMalformedClause] noSpan)
        , (partialFamily, PendingTraitNominalSummary Nothing 0 [partialClause] noSpan)
        , (dataFamily, PendingDataNominalSummary Nothing 0 [dataConstructor] noSpan)
        ]
    fixedPoint =
      evalState
        (do
          (roles, _, _) <- inferPendingNominalRoles pending
          pure roles
        )
        fixedPointState
    fixedPointRoles owner = Map.lookup owner fixedPoint
    publishable = Map.restrictKeys pending (Set.fromList [family, dataFamily])
    publicationState =
      fixedPointState
        { csNominalSummaryRequests = publishable
        , csDirtyNominalSummaries = Map.keysSet publishable
        , csFinalizedUniverseInterfaces = Map.keysSet publishable
        }
    installedSummaries =
      evalState
        (do
          finalizePendingNominalSummaries
          gets (Map.mapMaybe (fmap ncsRoles . gdNominalSummary) . csGlobals)
        )
        publicationState
    installedSummaryRoles owner = Map.lookup owner installedSummaries

elabTele' :: Telescope -> [Binder] -> CheckM Telescope
elabTele' tele bs = do
  ctx <- teleCtx tele
  elabTele ctx bs

elabUnderParams :: Telescope -> Expr -> CheckM (Term, Value)
elabUnderParams tele e = do
  ctx <- teleCtx tele
  (tm, _) <- inferType ctx e
  -- Data-family parameters are supplied implicitly to constructors even when
  -- the family header itself uses explicit application syntax. They are
  -- compile-time constructor indices, not constructor payload fields.
  let closed = foldr (\entry acc -> telePi (entry {teIcit = Impl, teQ = Q0}) acc) tm tele
  pure (closed, VSort LZero)

-- | Prove that a trait member's eventual result is runtime-erased in the
-- member's checked telescope. This is a representation query over semantic
-- evidence: descend through the complete Pi telescope, then ask the ordinary
-- h-level solver for @IsProp result@. In particular, while elaborating
-- @Eq a@, the current trait's authenticated @IsSet a@ supertrait proves that
-- the equality results of @eqSound@ and @eqComplete@ are erased. A failed
-- probe is transactional and conservatively leaves the member runtime
-- relevant.
traitMemberResultRuntimeErased :: Ctx -> Span -> Value -> CheckM Bool
traitMemberResultRuntimeErased ctx site memberType = do
  before <- get
  erased <- go ctx memberType
  put before
  pure erased
  where
    go activeCtx ty =
      forceM ty >>= \case
        VPiBoundM mode icit quantity borrowed name assumption domain closure -> do
          withAssumption <- extendLevelAssumption site activeCtx assumption
          let level = ctxLen activeCtx
              nextCtx =
                bindCtxMQB
                  mode
                  quantity
                  name
                  (icit == Impl)
                  borrowed
                  domain
                  withAssumption
          result <- clApp closure (VRigid level [])
          go nextCtx result
        result -> do
          resultF <- forceM result
          isJust <$> runtimeErasureEvidenceAvailable activeCtx site resultF

-- | Complete the runtime-erasure classification of current-module trait
-- members after all instance heads have been registered and header universe
-- interfaces have been principalized. This is a monotone refinement: fields
-- already classified quantity-zero by declaration syntax or header-local
-- evidence stay zero, and an ordinary field is promoted only when its fully
-- checked global projection type is now semantically proven RuntimeErased.
-- Imported trait layouts are never rewritten.
finalizeTraitMemberRepresentations :: CheckM ()
finalizeTraitMemberRepresentations = do
  state <- get
  let currentModule = csModule state
      localTraits =
        [ (traitName, traitInfo)
        | (traitName@(GName owner _), traitInfo) <- Map.toList (csTraits state)
        , owner == currentModule
        ]
  refinements <- forM localTraits $ \(traitName, traitInfo) -> do
    quantities <- foldM (refineMember state traitName) (tiMemberQs traitInfo) (tiMembers traitInfo)
    pure (traitName, traitInfo {tiMemberQs = quantities})
  modify' $ \current ->
    current
      { csTraits =
          foldl'
            (\traits (traitName, traitInfo) -> Map.insert traitName traitInfo traits)
            (csTraits current)
            refinements
      }
  where
    refineMember state traitName quantities memberName
      | Map.lookup memberName quantities == Just Q0 = pure quantities
      | otherwise =
          case Map.lookup (memberGlobal traitName memberName) (csGlobals state) of
            Nothing -> pure quantities
            Just definition -> do
              erased <- traitMemberResultRuntimeErased emptyCtx noSpan (gdType definition)
              pure
                ( if erased
                    then Map.insert memberName Q0 quantities
                    else quantities
                )

headerTrait :: TraitDecl -> Span -> CheckM ()
headerTrait (TraitDecl supers n params members) sp = do
  g <- ownName n
  noteDefinition g sp
  rawParamTele <- elabTele emptyCtx params
  let provisionalParamTele = zipWith provisionalSourceDeclarationParam params rawParamTele
  pctx <- extendSourceDeclarationTeleCtx emptyCtx (zip params provisionalParamTele)
  -- supertrait premises (§14.1.4): their evidence is carried as
  -- dictionary fields, projected by the compiler as ordinary evidence
  -- projections (§14.2.1); a parenthesized premise list (C1 a, C2 a)
  -- is several premises
  let superList =
        concatMap
          ( \item ->
              case stiType item of
                ETuple expressions _ ->
                  [(stiDerived item, expression) | expression <- expressions]
                expression -> [(stiDerived item, expression)]
          )
          supers
  supEntries <- forM (zip [(0 :: Int) ..] superList) $ \(i, (derived, s)) -> do
    (sTm, _) <- inferType pctx s
    pure (superFieldName i, sTm, derived)
  let supPairs = [(field, term) | (field, term, _) <- supEntries]
      derivedSuperFields =
        Set.fromList [field | (field, _, True) <- supEntries]
  -- member declarations in source order; earlier members are in scope
  -- for later member signatures as §13.2.1 siblings of the evidence
  -- record ("Inside the trait body, Item refers to the associated
  -- static member of the current trait evidence", §14.2.1), and free
  -- lowercase identifiers are implicitly universalized (§14.2/§11.3.3)
  let paramNames = map teName provisionalParamTele
      memberNames =
        nub $
          [nameText mn | Just mn <- map Kappa.Syntax.traitMemberName members]
      derivedMemberNames =
        Set.fromList [nameText mn | TraitDerived mn _ _ <- members]
  provisionalMemberFields <- forM memberNames $ \member ->
    RecordField member Ordinary FormationOrdinary QW Nothing RuntimeRelevant <$> freshMetaV pctx
  let derivedMemberDeclarations =
        [ (nameText member, memberType, memberSpan)
        | TraitDerived member memberType memberSpan <- members
        ]
      derivedMemberGraph =
        [ ( (member, memberSpan)
          , member
          , nub
              [ dependency
              | dependency <- freeLower memberType
              , dependency `Set.member` derivedMemberNames
              ]
          )
        | (member, memberType, memberSpan) <- derivedMemberDeclarations
        ]
      derivedMemberCycles =
        [ cycleMembers
        | CyclicSCC cycleMembers <- stronglyConnComp derivedMemberGraph
        ]
  forM_ derivedMemberCycles $ \cycleMembers ->
    case cycleMembers of
      [] -> pure ()
      ((_, cycleSpan) : _) ->
        report $
          withPayload
            ( withPayloadField "cycle"
                (T.intercalate " -> " (map fst cycleMembers)) $
                payloadKind "derive-cycle"
            ) $
            diag SevError StageElaborate "E_DERIVE_CYCLE" (Just "kappa.derive") cycleSpan
              "the synthesized-member dependency graph contains an unproductive cycle (§14.3.4A)"
  let
      -- §14.1.4: a member signature may name a SUPERTRAIT operation (e.g.
      -- a member of a 'C => D' subtrait mentions an operation from the
      -- supertrait 'C'). Such an operation's implicit dictionary argument is the
      -- current trait evidence's supertrait field. During member-type
      -- elaboration we stash the supertrait premises in 'csTraitSupers'; the
      -- implicit solver ('superThisCandidate') then resolves that dictionary
      -- to a 'this.__superN' projection — a closed term that, after the
      -- 'substThisTm' in the member-projection construction, reads correctly
      -- both as a sibling field of the dictionary record type and as a
      -- projection from the member projection's '__d' binder. Because the
      -- dictionary is a closed projection (not a context binder), the
      -- operation's OTHER implicits — notably its carrier — keep their
      -- ordinary inference, so the member type is sound. Inert when the
      -- member names no supertrait operation.
      elabMemberTy acc mtyE = do
        fvs <-
          filterM
            (\v ->
              if v `elem` (paramNames ++ memberNames)
                then pure False
                else do
                  global <- lookupGlobalName v
                  schemaLevel <- gets (Map.lookup v . csActiveUniverseSchema)
                  pure (isNothing global && isNothing schemaLevel)
            )
            (nub (freeLower mtyE))
        kvs <- mapM (const (freshMetaV pctx)) fvs
        let mctx = foldl (\c (v, k) -> bindCtxMQProvisional Parametric Q0 v False k c) pctx (zip fvs kvs)
        superVals <- forM supPairs $ \(fld, sTm) -> (,) fld <$> evalIn pctx sTm
        oldSupers <- gets csTraitSupers
        modify' $ \st -> st {csTraitSupers = superVals}
        let availableMembers =
              acc
                ++ [ field
                   | field <- provisionalMemberFields
                   , rfName field `notElem` map rfName acc
                   ]
        (mtyTm0raw, _) <-
          withNamedCallableInoutSignature mtyE $
            withThis (Just (ThisTraitSibs (sortOn rfName availableMembers))) (inferType mctx mtyE)
        -- Resolve any POSTPONED supertrait-operation dictionaries now, while
        -- 'csTraitSupers' is still in scope and the operations' explicit args
        -- have pinned their carriers, so each commits to its 'this.__superN'
        -- projection (see 'flushPendingWith'/'superThisCandidate').
        unless (null supPairs) flushPending
        -- Zonk from the member context's depth: a dictionary implicit solved
        -- to a trait-parameter rigid (the supertrait-operation case) must be
        -- requoted at 'ctxLen mctx', not 0, or its de Bruijn index lands one
        -- binder short for every enclosing forall — yielding a member type
        -- whose carrier points at a forall value binder instead of the trait
        -- parameter (§14.1.4).
        mtyTm0 <- zonkTermM (ctxLen mctx) mtyTm0raw
        mtyV0 <- evalIn mctx mtyTm0
        runtimeErased <- traitMemberResultRuntimeErased mctx sp mtyV0
        modify' $ \st -> st {csTraitSupers = oldSupers}
        universalBinders <- forM (zip fvs kvs) $ \(v, kv) -> do
          kv' <- forceM kv
          kind <- case kv' of
            VFlex m [] -> do
              level <- freshLevelMeta
              solveMeta m (VSort level)
              markGeneralizableLevelTerm (CSort level)
              pure (VSort level)
            _ -> pure kv'
          kindTm <- quoteIn pctx kind
          paramKind <- isParametricKind (ctxLen pctx) kind
          pure (v, if paramKind then Parametric else Ordinary, if paramKind then FormationParametric else FormationOrdinary, if paramKind then Q0 else QW, kindTm)
        let mtyTm = foldr (\(v, mode, formation, q, kT) b -> CPiFormedM mode formation Impl q False v kT b) mtyTm0 universalBinders
        mtyV <- evalIn pctx mtyTm
        pure (mtyTm, mtyV, runtimeErased)
      -- A signature-less default still declares a function member when it
      -- has source binders (§14.2).  Its header therefore carries a
      -- classifier-authenticated provisional result beneath the complete
      -- binder telescope; the body pass constrains that interface and the
      -- ordinary declaration finalizers reject anything left unresolved.
      elabInferredDefaultMemberTy binders = do
        telescope <- elabTele pctx binders
        memberCtx <- extendTeleCtx pctx telescope
        resultLevel <- freshGeneralizableLevelMeta
        resultType <- freshMetaFor memberCtx (VSort resultLevel)
        let memberTypeTerm = foldr telePi resultType telescope
        memberType <- evalIn pctx memberTypeTerm
        pure (memberTypeTerm, memberType, False)
      memberName (mn, _, _, _, _, _, _, _, _) = mn
      memberTerm (mn, tm, _, mode, formation, q, _, _, _) = RecordField mn mode formation q Nothing RuntimeRelevant tm
      memberQ mn = case T.uncons mn of
        Just (c, _) | c >= 'A' && c <= 'Z' -> Q0
        _ -> QW
      goMembers _acc done [] = pure (reverse done)
      goMembers acc done (m : rest) = case m of
        TraitSig mn mtyE _ -> do
          let memberSchema = nameUniverseSchema mn
              memberOwner = memberGlobal g (nameText mn)
          (mtyTm, mtyV, runtimeErased) <- case memberSchema of
            Nothing -> elabMemberTy acc mtyE
            Just _ ->
              withActiveUniverseDefinition memberOwner $
                withNestedUniverseSchemaParameters memberSchema $
                  elabMemberTy acc mtyE
          let inouts = inoutParamsFromBinders (signatureBinders mtyE)
          associatedStatic <-
            isAssociatedStaticMemberType (ctxLen pctx) mtyV
          let
              q =
                if runtimeErased || associatedStatic
                  then Q0
                  else memberQ (nameText mn)
          mode <- (\isKind -> if isKind then Parametric else Ordinary) <$> isParametricKind (ctxLen pctx) mtyV
          formation <- selectFormationMode pctx mode mtyV
          let field = RecordField (nameText mn) mode formation q Nothing RuntimeRelevant mtyV
          goMembers
            (acc ++ [field])
            ( ( nameText mn
              , mtyTm
              , inouts
              , mode
              , formation
              , q
              , memberSchema
              , runtimeErased
              , associatedStatic
              )
                : done
            )
            rest
        TraitDerived mn mtyE memberSpan ->
          goMembers acc done (TraitSig mn mtyE memberSpan : rest)
        TraitDefault definition@(LetDef (Just mn) _ _ _ _ _ mty _ _) _
          -- a default for an already-declared member supplies its
          -- definition only; the declaration owns the dictionary
          -- field (§14.2: declaration vs definition forms)
          | nameText mn `elem` map memberName done -> goMembers acc done rest
          | otherwise -> do
              let memberSchema = nameUniverseSchema mn
                  memberOwner = memberGlobal g (nameText mn)
                  elaborateMember = case mty of
                    Just resultType ->
                      elabMemberTy acc (foldr EArrow resultType (ldBinders definition))
                    Nothing -> elabInferredDefaultMemberTy (ldBinders definition)
              (mtyTm, mtyV, runtimeErased) <- case memberSchema of
                Nothing -> elaborateMember
                Just _ ->
                  withActiveUniverseDefinition memberOwner $
                    withNestedUniverseSchemaParameters memberSchema elaborateMember
              let inouts = maybe [] (inoutParamsFromBinders . signatureBinders) mty
              associatedStatic <-
                isAssociatedStaticMemberType (ctxLen pctx) mtyV
              let
                  q =
                    if runtimeErased || associatedStatic
                      then Q0
                      else memberQ (nameText mn)
              mode <- (\isKind -> if isKind then Parametric else Ordinary) <$> isParametricKind (ctxLen pctx) mtyV
              formation <- selectFormationMode pctx mode mtyV
              let field = RecordField (nameText mn) mode formation q Nothing RuntimeRelevant mtyV
              goMembers
                (acc ++ [field])
                ( ( nameText mn
                  , mtyTm
                  , inouts
                  , mode
                  , formation
                  , q
                  , memberSchema
                  , runtimeErased
                  , associatedStatic
                  )
                    : done
                )
                rest
        TraitDefault {} -> goMembers acc done rest
        TraitEvidenceUniqueness {} -> goMembers acc done rest
  ms <- goMembers [] [] members
  paramTele <- finalizeSourceDeclarationTelescope emptyCtx (zip params provisionalParamTele)
  -- The member/supertrait uses above have now constrained every generated
  -- parameter domain. Build the public trait constructor from that finalized
  -- telescope so its mode and kind are one coherent interface contract.
  let tyTm = foldr telePi (CSort LZero) paramTele
  let memberTerms = map memberTerm ms
      dictBody =
        CRecordTQ . sortOn rfName $
          [RecordField fn Ordinary FormationOrdinary QW Nothing RuntimeRelevant tm | (fn, tm) <- supPairs] ++ memberTerms
      dictTm = foldr (\entry acc -> CLamM (teMode entry) (teIcit entry) (teQ entry) (teName entry) acc) dictBody paramTele
  traitUniverses <- provisionalDeclarationUniverses [tyTm]
  tyV <- evalIn emptyCtx tyTm
  dictV <- evalIn emptyCtx dictTm
  -- the trait constructor is abstract (§14.1.1): not conversion-reducible
  addGlobal g
    ( ( globalDefWithObservationMode
          Ordinary
          (GlobalDef tyV (Just dictV) False)
      )
        { gdRecordInterface = Just dictTm
        }
    )
  modify' $ \st ->
    st
      { csNominalSummaryRequests =
          Map.insert g
            ( PendingTraitNominalSummary
                (nameUniverseSchema n)
                (length paramTele)
                (map snd supPairs ++ [memberType | (_, memberType, _, _, _, _, _, _, _) <- ms])
                sp
            )
            (csNominalSummaryRequests st)
      , csDirtyNominalSummaries = Set.insert g (csDirtyNominalSummaries st)
      }
  let supTms = [(fn, foldr (\entry acc -> CLamM (teMode entry) (teIcit entry) (teQ entry) (teName entry) acc) sTm paramTele) | (fn, sTm) <- supPairs]
  modify' $ \st ->
    invalidateSemanticCaches
      ( st
          { csTraits =
              Map.insert
                g
                ( TraitInfo
                    (length paramTele)
                    (map memberName ms)
                    (Map.fromList [(mn, mode) | (mn, _, _, mode, _, _, _, _, _) <- ms])
                    ( Set.fromList
                        [ mn
                        | (mn, _, _, _, _, _, _, _, associatedStatic) <- ms
                        , associatedStatic
                        ]
                    )
                    (Map.fromList [(mn, q) | (mn, _, _, _, _, q, _, _, _) <- ms])
                    Map.empty
                    supTms
                    derivedMemberNames
                    derivedSuperFields
                    SealedCoherent
                )
                (csTraits st)
          }
      )
  -- member projection globals: m : forall params. (@d : Tr params) -> τ
  -- (occurrences of sibling members in τ become projections from the
  -- dict binder)
  forM_ ms $ \(mn, mtyTm, inouts, modeMember, _formationMember, _qMember, memberSchema, _runtimeErased, _associatedStatic) ->
    withNestedUniverseSchemaParameters memberSchema $ do
      let dictTy =
            foldl
              (\f (entry, i) -> CApp (teIcit entry) f (CVar i))
              (CGlobI g traitUniverses)
              (zip paramTele (reverse [0 .. length paramTele - 1]))
          projTy =
            foldr
              (\entry acc -> telePi (entry {teIcit = Impl, teBorrow = False}) acc)
              ( CPiFormedM Ordinary FormationOrdinary Impl QW False "__d" dictTy
                  (substThisTm (CVar 0) (weakenTermUnderBinderAt (length paramTele) mtyTm))
              )
              paramTele
          projTm =
            foldr
              (\entry acc -> CLamM (teMode entry) Impl (teQ entry) (teName entry) acc)
              (CLamM Ordinary Impl QW "__d" (CProjM modeMember (CVar 0) mn))
              paramTele
      projTyV <- evalIn emptyCtx projTy
      projV <- evalIn emptyCtx projTm
      mg <- ownName (Name mn sp)
      let qualifiedMember = memberGlobal g mn
      -- Install the bare member name only when it does not already denote a
      -- wired-in declaration. Public MonadRef operations are trait-member
      -- projections; concrete IO ref primitives live under the internal
      -- __io* names so ref-facet recognition is evidence-backed.
      bareExists <- gets (Map.member mg . csGlobals)
      when bareExists $ do
        previous <- gets (Map.lookup mg . csBareTraitMembers)
        forM_ previous $ \(previousTrait, previousMember) ->
          modify' $ \state ->
            state
              { csScopeAmbig =
                  Map.insertWith
                    (\new old -> sort (nub (new ++ old)))
                    mn
                    [memberGlobal previousTrait previousMember, qualifiedMember]
                    (csScopeAmbig state)
              }
      unless bareExists $ do
        inheritGeneralizableLevelRoles g mg projTy
        addGlobal mg (globalDefWithObservationMode modeMember (GlobalDef projTyV (Just projV) True))
        recordCoreBody mg projTm
        recordInoutParams mg inouts
        modify' $ \state ->
          state
            { csBareTraitMembers =
                Map.insert mg (g, mn) (csBareTraitMembers state)
            , csTraitMemberOwners =
                Map.insert mg g (csTraitMemberOwners state)
            }
      -- Always install the qualified projection global. Capture the KCore body for
      -- the native backend (§14.2.1 member projection): a CLam chain projecting the
      -- member field from the dict.
      inheritGeneralizableLevelRoles g qualifiedMember projTy
      addGlobal qualifiedMember (globalDefWithObservationMode modeMember (GlobalDef projTyV (Just projV) True))
      recordCoreBody qualifiedMember projTm
      recordInoutParams qualifiedMember inouts
      modify' $ \state ->
        state
          { csTraitMemberOwners =
              Map.insert qualifiedMember g (csTraitMemberOwners state)
          }

  let uniquenessClauses =
        [ (proof, clauseSpan)
        | TraitEvidenceUniqueness proof clauseSpan <- members
        ]
      independentlySubsingletonFields =
        all
          (\(_, _, _, _, _, _, _, runtimeErased, associatedStatic) -> runtimeErased || associatedStatic)
          ms
  constructionMode <-
    validateTraitEvidenceUniqueness
      g
      traitUniverses
      pctx
      paramTele
      supPairs
      independentlySubsingletonFields
      uniquenessClauses
  modify' $ \state ->
    state
      { csTraits =
          Map.adjust
            (\info -> info {tiEvidenceConstructionMode = constructionMode})
            g
            (csTraits state)
      }

-- | Validate the declaration-owned authority for fresh trait-evidence
-- construction (§14.1.1A).  Conventional certificates use a compact checked
-- structural proof: each field must already be independently subsingleton and
-- each supertrait must itself carry an independent certificate.  The embedded
-- standard foundation has additional identity-authenticated providers for
-- law-constrained fields such as @Eq.(==)@ and @IsContr.center@.  An explicit
-- proof is checked against the generated extensional theorem while the exact
-- trait is on 'csEvidenceUniquenessStack', disabling the forbidden
-- @IsTrait G -> IsSubsingleton G@ cycle.
validateTraitEvidenceUniqueness
  :: GName
  -> [Level]
  -> Ctx
  -> [TelescopeEntry]
  -> [(Text, Term)]
  -> Bool
  -> [(Expr, Span)]
  -> CheckM EvidenceConstructionMode
validateTraitEvidenceUniqueness trait traitUniverses parameterCtx parameterTele supers fieldsIndependent clauses =
  case clauses of
    [] -> pure SealedCoherent
    [(EDerive Nothing _, clauseSpan)] -> do
      supersIndependent <- and <$> mapM superIsIndependent supers
      foundation <- authenticatedFoundationProvider
      if (fieldsIndependent && supersIndependent) || foundation
        then pure IndependentlyUnique
        else do
          errAt clauseSpan "E_EVIDENCE_UNIQUENESS_INVALID"
            (Just "kappa.evidence.uniqueness")
            "the conventional evidence-uniqueness proof cannot establish independent equality of every evidence field (§14.1.1A)"
          pure SealedCoherent
    [(proofExpression, clauseSpan)] -> do
      expected <- evidenceUniquenessTheorem
      before <- gets (length . csDiags)
      modify' $ \state ->
        state
          { csEvidenceUniquenessStack =
              trait : csEvidenceUniquenessStack state
          }
      checkedProof <- check parameterCtx proofExpression expected
      -- Implicit evidence in the certificate body is often postponed until
      -- its endpoints are fixed.  Resolve it while the self-coherence guard
      -- is still active; popping the guard first would let the forbidden
      -- @IsTrait G@ edge enter through declaration closeout.
      flushPending
      modify' $ \state ->
        state
          { csEvidenceUniquenessStack =
              dropOne trait (csEvidenceUniquenessStack state)
          }
      diagnostics <- gets csDiags
      let added = take (length diagnostics - before) diagnostics
          dependencies = globalsOfTerm checkedProof
          coherenceCycle = prelTraitSubsingletonWitness `Set.member` dependencies
          cycleReported =
            coherenceCycle
              || any ((== "E_EVIDENCE_UNIQUENESS_CYCLE") . dCode) added
      when (coherenceCycle && not (any ((== "E_EVIDENCE_UNIQUENESS_CYCLE") . dCode) added)) $
        errAt clauseSpan "E_EVIDENCE_UNIQUENESS_CYCLE"
          (Just "kappa.evidence.uniqueness")
          "an evidence-uniqueness certificate depends on compiler-generated coherence for the same trait (§14.1.1A)"
      if null added && not coherenceCycle
        then pure IndependentlyUnique
        else do
          unless cycleReported $
            errAt clauseSpan "E_EVIDENCE_UNIQUENESS_INVALID"
              (Just "kappa.evidence.uniqueness")
              "the evidence-uniqueness expression does not prove the generated independent extensionality theorem (§14.1.1A)"
          pure SealedCoherent
    (_ : (_, duplicateSpan) : _) -> do
      errAt duplicateSpan "E_EVIDENCE_UNIQUENESS_INVALID"
        (Just "kappa.evidence.uniqueness")
        "a trait may declare at most one evidence-uniqueness certificate (§14.1.1A)"
      pure SealedCoherent
  where
    dropOne _ [] = []
    dropOne target (candidate : rest)
      | target == candidate = rest
      | otherwise = candidate : dropOne target rest

    superIsIndependent (_, closedSuper) = do
      superFunction <- evalIn parameterCtx closedSuper
      forceM superFunction >>= \case
        VGlobI superTrait _ _ -> do
          state <- get
          pure $
            maybe
              False
              ((== IndependentlyUnique) . tiEvidenceConstructionMode)
              (Map.lookup superTrait (csTraits state))
        _ -> pure False

    authenticatedFoundationProvider = do
      embedded <- gets csEmbeddedLoad
      pure
        ( embedded
            && trait
              `Set.member` Set.fromList
                [ gPrel "IsEmpty"
                , gPrel "IsContr"
                , gPrel "IsSubsingleton"
                , gPrel "IsProp"
                , gPrel "IsSet"
                , gPrel "IsGroupoid"
                , gPrel "Eq"
                ]
        )

    evidenceUniquenessTheorem = do
      let parameterIndices = reverse [0 .. length parameterTele - 1]
          evidenceTypeTerm =
            foldl
              (\function (entry, index) ->
                CApp (teIcit entry) function (CVar index))
              (CGlobI trait traitUniverses)
              (zip parameterTele parameterIndices)
      evidenceType <- evalIn parameterCtx evidenceTypeTerm
      let leftLevel = ctxLen parameterCtx
          leftCtx =
            bindCtxMQ Ordinary QW "left" False evidenceType parameterCtx
          rightLevel = ctxLen leftCtx
          rightCtx =
            bindCtxMQ Ordinary QW "right" False evidenceType leftCtx
      equality <-
        globalValueM
          prelEqType
          [ (Impl, evidenceType)
          , (Expl, VRigid leftLevel [])
          , (Expl, VRigid rightLevel [])
          ]
      equalityTerm <- quoteIn rightCtx equality
      let theoremTerm =
            CPiFormedM
              Ordinary
              FormationOrdinary
              Expl
              QW
              False
              "left"
              evidenceTypeTerm
              ( CPiFormedM
                  Ordinary
                  FormationOrdinary
                  Expl
                  QW
                  False
                  "right"
                  (shiftTerm 1 0 evidenceTypeTerm)
                  equalityTerm
              )
      evalIn parameterCtx theoremTerm

headerExpect :: Set GName -> ExpectForm -> Span -> CheckM ()
headerExpect preexisting form sp = case form of
  ExpectTerm n tyE -> do
    g <- ownName n
    st0 <- get
    let alreadyDef = case Map.lookup g (csGlobals st0) of
          Just gd -> Set.member g preexisting && isJust (gdValue gd)
          Nothing -> False
        definedInCompanion =
          alreadyDef
            && maybe False ((/= spanFile sp) . spanFile)
                 (Map.lookup g (csDeclSites st0))
    -- Elaborate the declared signature up front: it is needed both to
    -- register the abstract global (name resolution) and to check a
    -- backend-intrinsic satisfier against it up to definitional equality.
    (tyTm, _) <- withNamedCallableInoutSignature tyE (inferType emptyCtx tyE)
    tyV <- evalIn emptyCtx tyTm
    unless alreadyDef $ addGlobal g (GlobalDef tyV Nothing False)
    recordSignatureInoutParams g tyE
    -- Portable foundation constants are authenticated by resolved identity
    -- and an independently seeded Core schema.  They are neither ordinary
    -- source companions nor spelling-based backend intrinsics.
    byFoundation <- foundationProviderSatisfies g tyV sp
    -- §34.5/§9.4: a matching backend intrinsic of the selected profile
    -- satisfies this expectation when its signature matches.
    byIntrinsic <- backendIntrinsicSatisfies g tyV sp
    let count = if definedInCompanion || byFoundation || byIntrinsic then 1 else 0
    modify' $ \st -> st {csExpects = Map.insert g (sp, count) (csExpects st)}
  ExpectType n params _ -> abstractType n params
  ExpectData n params _ -> do
    abstractType n params
    g <- ownName n
    modify' $ \st -> st {csDatas = Map.insertWith (\_ old -> old) g (DataInfo [] (length params) LZero) (csDatas st)}
  ExpectTrait n params _ -> abstractType n params
  where
    abstractType n params = do
      g <- ownName n
      fresh <- registerExpect g
      when fresh $ do
        tyV <- aliasKind params
        addGlobal g (GlobalDef tyV Nothing False)
    -- Record the §9.4 expectation. An existing ordinary declaration is a
    -- satisfier only when it came from another selected source fragment;
    -- §9.4 explicitly excludes a definition in the expect's own source file.
    -- Returns True only when the expect must introduce the declaration into
    -- the global table itself.
    registerExpect g = do
      st <- get
      let exists =
            Set.member g preexisting
              && ( Map.member g (csGlobals st)
                     || Map.member g (csDatas st)
                     || Map.member g (csTraits st)
                 )
          satisfied =
            exists
              && maybe False ((/= spanFile sp) . spanFile)
                   (Map.lookup g (csDeclSites st))
          count = if satisfied then 1 else 0
      put st {csExpects = Map.insert g (sp, count) (csExpects st)}
      pure (not exists)

-- | Check one mandatory portable-foundation provider.  A provider claim with
-- the right identity but the wrong ABI is a precise signature error and does
-- not also degrade into an unsatisfied-expectation cascade.
foundationProviderSatisfies :: GName -> Value -> Span -> CheckM Bool
foundationProviderSatisfies g tyV sp = do
  providers <- gets csFoundationProviders
  case Map.lookup g providers of
    Nothing -> pure False
    Just expectedTm -> do
      expectedV <- evalIn emptyCtx expectedTm
      matches <- withUniverseDiagnosticSpan sp (unify emptyCtx tyV expectedV)
      if matches
        then pure True
        else do
          ec <- ec_
          let declared = renderTerm (quote ec 0 tyV)
              required = renderTerm (quote ec 0 expectedV)
          errAt sp "E_FOUNDATION_PROVIDER_SIGNATURE_MISMATCH"
            (Just "kappa.internal.compiler")
            ( "portable foundation provider '" <> gnameText g
                <> "' does not match its required Core signature; declared: "
                <> declared <> "; required: " <> required
            )
          pure True

-- | Body pass: elaborates definitions, plus any signatures the header
-- pass deferred because they mention signature-less module lets.
bodyPassIn :: Set Text -> Decl -> CheckM ()
bodyPassIn siglessLets d = case d of
  DSig _ _ tyE _
    | any (`Set.member` siglessLets) (sigHeadNames tyE) -> headerPassIn Set.empty d
  _ -> bodyPass d

bodyPass :: Decl -> CheckM ()
bodyPass d =
  case d of
    -- Signatures are retained until their matching definition completes.
    -- Re-entering an empty body-pass scope here would diagnose them before
    -- that definition can constrain their metas.
    DSig {} -> action
    -- The wrapped declaration owns the semantic hole scope; 'elabUnsafeAssert'
    -- delegates to 'bodyPass' for that declaration after auditing the wrapper.
    DUnsafeAssert {} -> action
    _ -> do
      owner <- traverse ownName (declarationUniverseName d)
      pending <- case owner of
        Nothing -> pure Map.empty
        Just global ->
          gets (Map.findWithDefault Map.empty global . csSignatureHoles)
      withNamedHoleScope pending (close owner) action
  where
    action = withDeclarationUniverseSchema d (bodyPass' d)
    close owner = do
      finalizeNamedHoles
      forM_ owner $ \global ->
        modify' $ \st ->
          st
            { csSignatureHoles =
                Map.delete global (csSignatureHoles st)
            }

    bodyPass' = \case
      DLet mods ld sp -> elabLetDecl mods ld sp
      DTrait _ trait traitSpan -> do
        forM_ (trMembers trait) $ \case
          TraitDefault definition _ ->
            mapM_ reportQuantityBorrowMarker
              (quantityBorrowMarkerSpans (ldBody definition))
          _ -> pure ()
        elaborateTraitDefaults trait traitSpan
      DInstance inst sp -> elabInstance inst sp
      DPattern mods ld sp -> elabActivePatternDecl mods ld sp
      DProjection mods n bs ty body sp -> elabProjectionDecl mods n bs ty body sp
      DDerive _ sp -> do
        generated <- gets (Map.findWithDefault [] sp . csDerivedDecls)
        valid <- validateDerivedDeclarations sp generated
        when valid $
          forM_ generated $ \case
            DInstance inst generatedSpan -> elabInstance inst generatedSpan
            _ -> pure ()
      DTopSplice _ sp ->
        unsupportedAt sp "top-level splices are not supported by this implementation"
      DUnsafeAssert akind inner sp -> elabUnsafeAssert akind inner sp
      _ -> pure ()

-- | Elaborate every ordinary trait default once in the abstract trait
-- context (§14.2).  The resulting hidden declaration has the exact checked
-- telescope of the public member accessor: generated universe evidence,
-- trait parameters, an abstract dictionary, and then the member's own
-- binders.  Instances subsequently specialize this Core template; they never
-- retain or re-check the source 'LetDef'.
elaborateTraitDefaults :: TraitDecl -> Span -> CheckM ()
elaborateTraitDefaults trait declarationSite = do
  traitGlobal <- ownName (trName trait)
  traitDefinition <- gets (Map.lookup traitGlobal . csGlobals)
  traitInfo <- gets (Map.lookup traitGlobal . csTraits)
  case (traitDefinition, traitInfo) of
    (Just ownerDefinition, Just info) -> do
      let traitUniverseCount = dutParameterCount (gdUniverses ownerDefinition)
          traitUniverses = map LParam [0 .. traitUniverseCount - 1]
          parameterCount = tiParamCount info
      forM_ (trMembers trait) $ \case
        TraitDefault definition defaultSite ->
          case ldName definition of
            Nothing ->
              errAt defaultSite "E_TRAIT_MEMBER_TELESCOPE_MISMATCH" (Just "kappa.internal.compiler")
                "an ordinary trait default is missing its declared member identity"
            Just memberName -> do
              let member = nameText memberName
                  accessor = memberGlobal traitGlobal member
                  defaultGlobal = traitDefaultGlobal traitGlobal member
              memberDefinition <- gets (Map.lookup accessor . csGlobals)
              case memberDefinition of
                Nothing ->
                  errAt defaultSite "E_TRAIT_MEMBER_TELESCOPE_MISMATCH" (Just "kappa.internal.compiler")
                    ("ordinary default member '" <> member <> "' has no checked member interface")
                Just checkedInterface -> do
                  state <- get
                  let interfaceType = globalCoreType (ecOf state) checkedInterface
                      proofCount =
                        length
                          ( declarationUniverseConstraints
                              (dutParameterCount (gdUniverses checkedInterface))
                              interfaceType
                          )
                      prefixCount = proofCount + parameterCount + 1
                  peelTraitMemberPrefix
                    defaultSite
                    prefixCount
                    emptyCtx
                    (gdType checkedInterface) >>= \case
                      Nothing -> pure ()
                      Just (memberCtx, memberType, prefixBinders) -> do
                        let argumentTerms =
                              [ CVar (parameterCount - index)
                              | index <- [0 .. parameterCount - 1]
                              ]
                            dictionary = CVar 0
                            superterms =
                              [ (field, CProjM Ordinary dictionary field)
                              | (field, _) <- tiSupers info
                              ]
                            memberTerms =
                              [ ( field
                                , CProjM
                                    (Map.findWithDefault Ordinary field (tiMemberModes info))
                                    dictionary
                                    field
                                )
                              | field <- tiMembers info
                              ]
                        siblingTypes <-
                          traitMemberSiblingTypesAt
                            defaultSite
                            traitGlobal
                            traitUniverses
                            info
                            argumentTerms
                            memberCtx
                            superterms
                            memberTerms
                        superValues <-
                          forM superterms $ \(field, term) ->
                            (field,) <$> evalIn memberCtx term
                        checked <-
                          withTraitSupers superValues $ do
                            pendingBefore <-
                              gets (Set.fromList . map pendingEntryMeta . csPending)
                            result <-
                              withThis (Just (ThisTraitSibs siblingTypes)) $
                                checkTraitMemberExpressionAgainst
                                  (Map.findWithDefault Ordinary member (tiMemberModes info))
                                  memberCtx
                                  memberType
                                  (ldBinders definition)
                                  Nothing
                                  (ldBody definition)
                                  defaultSite
                            pendingAfter <-
                              gets (Set.fromList . map pendingEntryMeta . csPending)
                            flushPendingSelected
                              (Set.difference pendingAfter pendingBefore)
                            flushDeferredTypeEqualities False
                            pure result
                        let closed =
                              wrapTraitMemberPrefix
                                prefixBinders
                                (substThisTm dictionary checked)
                        principalized <-
                          principalizeBodyUniverseInstantiations
                            accessor
                            (gdType checkedInterface)
                            closed
                        zonked <- zonkTermM 0 principalized
                        current <- get
                        let finalizedTemplate =
                              zonkTermWith
                                (\_ _ -> Nothing)
                                (resolveFinalizedOwnerLevel current accessor)
                                0
                                zonked
                            finalized =
                              termScopedAt 0 finalizedTemplate
                                && null (unsolvedMetasOf current finalizedTemplate)
                                && null (levelMetasOfTerm finalizedTemplate)
                        if not finalized
                          then
                            errAt defaultSite "E_UNSOLVED_METAVARIABLE"
                              (Just "kappa.type.unsolved-metavariable")
                              ( "ordinary default member '" <> member
                                  <> "' did not close to source-free checked Core"
                              )
                          else
                            modify' $ \current ->
                              let prototype =
                                    checkedInterface
                                      { gdNominalSummary = Nothing
                                      , gdRecordInterface = Nothing
                                      , gdReducible = True
                                      }
                                  installed =
                                    globalDefWithCanonicalCoreBody current finalizedTemplate prototype
                                  traits' =
                                    Map.adjust
                                      (\traitInfo' ->
                                         traitInfo'
                                           { tiDefaults =
                                               Map.insert member defaultGlobal (tiDefaults traitInfo')
                                           })
                                      traitGlobal
                                      (csTraits current)
                               in invalidateSemanticCaches
                                    current
                                      { csGlobals =
                                          Map.insert defaultGlobal installed (csGlobals current)
                                      , csCoreBodies =
                                          Map.insert defaultGlobal finalizedTemplate (csCoreBodies current)
                                      , csFinalizedUniverseInterfaces =
                                          Set.insert defaultGlobal (csFinalizedUniverseInterfaces current)
                                      , csTraits = traits'
                                      }
        _ -> pure ()
    _ ->
      errAt declarationSite "E_TRAIT_MEMBER_TELESCOPE_MISMATCH" (Just "kappa.internal.compiler")
        "trait defaults cannot be elaborated before the checked trait interface exists"

-- | §4.4 termination-assertion escape. The assertion is gated by the
-- §4.2 build configuration: rejected by default (kappa.feature.gated)
-- with a diagnostic naming both the offending form and the build setting
-- that disallows it. When permitted, the use is recorded in the §4.7
-- audit ledger and the wrapped definition is elaborated normally. Only
-- `assertReducible` records a conversion-reducibility override for the SCC
-- termination pass; `assertTerminates` remains an audited acceptance escape.
elabUnsafeAssert :: UnsafeAssertKind -> Decl -> Span -> CheckM ()
elabUnsafeAssert akind inner sp = do
  cfg <- gets csUnsafe
  let (facility, setting, allowed) = case akind of
        AssertTerminates -> ("assertTerminates", "allow_assert_terminates", allowAssertTerminates cfg)
        AssertTotal -> ("assertTotal", "allow_assert_terminates", allowAssertTerminates cfg)
        AssertReducible -> ("assertReducible", "allow_assert_reducible", allowAssertReducible cfg)
      affected = case inner of
        DLet _ ld _ -> maybe "<anonymous>" nameText (ldName ld)
        _ -> "<definition>"
  if allowed
    then do
      recordAudit facility affected setting sp Nothing
      case (akind, inner) of
        (AssertTerminates, DLet _ ld _) | Just n <- ldName ld -> do
          g <- ownName n
          modify' $ \st ->
            st {csAssertTerminates = Set.insert g (csAssertTerminates st)}
        (AssertTotal, DLet _ ld _) | Just n <- ldName ld -> do
          g <- ownName n
          modify' $ \st ->
            st {csAssertTerminates = Set.insert g (csAssertTerminates st)}
        (AssertReducible, DLet _ ld _) | Just n <- ldName ld -> do
          g <- ownName n
          modify' $ \st -> st {csAssertReducible = Set.insert g (csAssertReducible st)}
        _ -> pure ()
    else do
      gateUnsafe facility setting sp affected
      -- Keep elaborating the wrapped body for name recovery, but exclude it
      -- from totality checking: the disabled acceptance assertion is the root
      -- error and an additional termination failure would be a cascade.
      case inner of
        DLet _ definition _ | Just name <- ldName definition -> do
          global <- ownName name
          modify' $ \state ->
            state
              { csTerminationNames =
                  Set.delete global (csTerminationNames state)
              }
        _ -> pure ()
  -- Elaborate the wrapped definition regardless of gating: these forms
  -- never change runtime semantics (§4.4) and registering the binding avoids
  -- a spurious §9.1 signature-unsatisfied cascade on top of the gate error.
  bodyPass inner

-- | An active-pattern declaration (§17.3.1) elaborates as an ordinary
-- function definition (the pattern name is also a first-class value)
-- and registers pattern metadata: its result classification and the
-- number of pattern arguments before the scrutinee.
elabActivePatternDecl :: DeclMods -> LetDef -> Span -> CheckM ()
elabActivePatternDecl mods ld sp = do
  elabLetDecl mods ld sp
  case ldName ld of
    Nothing -> pure ()
    Just n -> do
      g <- ownName n
      mgd <- gets (Map.lookup g . csGlobals)
      forM_ mgd $ \gd -> do
        (_argc, res) <- unrollExplicit 0 (gdType gd)
        resF <- forceM res
        let kind = case resF of
              VGlobN g _ | g == prelOption -> Right APOption
              VGlobN g _ | g == prelMatch -> Right APMatch
              VGlobN g _ | g `elem` kernelMonadCarriers -> Left (gKey g)
              _ -> Right APTotal
        case kind of
          Left h ->
            errAt sp "E_ACTIVE_PATTERN_MONADIC_RESULT" (Just "kappa-hs.pattern.active")
              ("an active pattern's result type may not be the monadic type '" <> h
                 <> "'; return Option, Match, or a total view type (§17.3.1)")
          Right k -> do
            -- an Option/total-view pattern cannot return a residue, so
            -- a linear scrutinee would be lost on the miss path
            let explBinders = [b | b <- ldBinders ld, not (bImplicit b)]
                scrutLinear = case reverse explBinders of
                  (b : _) ->
                    surfaceQuantityPositive (bpQuantity (bPrefix b))
                      && isNothing (bpBorrow (bPrefix b))
                  [] -> False
            when (scrutLinear && k /= APMatch) $
              errAt sp "E_ACTIVE_PATTERN_LINEARITY_VIOLATION" (Just "kappa-hs.pattern.active")
                "this active pattern consumes a linear scrutinee but cannot thread a residue back on a miss; return 'Match item residue' instead (§17.3)"
            modify' $ \st -> st {csActive = Map.insert g (APInfo k) (csActive st)}
  where
    unrollExplicit :: Int -> Value -> CheckM (Int, Value)
    unrollExplicit = goU 0
      where
        goU expl lvl v = do
          vf <- forceM v
          case vf of
            VPi ic _ _ _ _ clo -> do
              inner <- clApp clo (VRigid lvl [])
              goU (if ic == Expl then expl + 1 else expl) (lvl + 1) inner
            _ -> pure (expl, vf)

-- | A projection definition (§9.1.1). Both forms register a term facet
-- global (a first-class descriptor) plus 'csProjections' metadata used
-- by the application-site elaborators of §16.1.5/§16.1.6.
--
--   * selector form: term facet @Δ -> Projector Roots T@; the runtime
--     value is @λΔ. λplaces. body@ with each @yield p@ reading @p@.
--   * expanded form: term facet @Δ -> Bundle@, a structural record of
--     @Getter/Opener/Setter/Sinker@ accessor closures with the §9.1.1
--     descriptor-field synthesis (get+set ⇒ open, inout ⇒ set).
--
-- Place lambdas/applications use the canonical (lexicographic) order of
-- the @Roots@ record so descriptor applications can be elaborated from
-- the roots record type alone.
elabProjectionDecl :: DeclMods -> Name -> [Binder] -> Expr -> ProjBody -> Span -> CheckM ()
elabProjectionDecl _mods n binders resTyE body sp = do
  flushPending
  g <- ownName n
  let groups = projBinderGroups binders
      placeBs = [b | (True, b) <- groups]
      ordBs = [b | (False, b) <- groups]
  when (null placeBs) $
    errAt sp "E_PROJECTION_MISSING_PLACE_BINDER" (Just "kappa-hs.projection.place-binder")
      "a projection definition must contain at least one 'place' binder (§9.1.1)"
  -- Δ context: ordinary binders, declaration order
  (ctxD, ordTele) <- elabOrdBinders emptyCtx ordBs
  -- place binder types and the focus, under the full Δ
  places0 <- forM placeBs $ \b -> do
    tyTm <- case binderTypeExpr b of
      Just tyE -> withGeneralizableBareTypeLevels $
        normalizeBinderDomain ctxD b tyE >>= fmap fst . inferType ctxD
      Nothing -> freshMeta
    tyV <- evalIn ctxD tyTm
    pure (maybe "_" nameText (bName b), tyTm, tyV)
  let placesLex = sortOn (\(nm, _, _) -> nm) places0
      ctxPl = foldl (\c (nm, _, tv) -> bindCtx nm False tv c) ctxD placesLex
      nPl = length placesLex
  -- the declared focus may depend on the place binders (e.g.
  -- 'Array this.len Byte'); in the descriptor type a unique root is
  -- represented by the §13.2.1 'this' neutral
  (focusTmP, _) <- inferType ctxPl resTyE
  focusV <- evalIn ctxPl focusTmP
  let focusTm = placesToThis nPl focusTmP
      rootsTm = CRecordT [(nm, t) | (nm, t, _) <- placesLex]
      placeNames = [nm | (nm, _, _) <- places0]
      lamsOrd t = foldr (\(q, nm, _) acc -> CLamM Ordinary Expl q nm acc) t ordTele
      pisOrd t = foldr (\(q, nm, ty) acc -> CPiFormedM Ordinary FormationOrdinary Expl q False nm ty acc) t ordTele
      app2 h a b = CApp Expl (CApp Expl h a) b
  case body of
    ProjSelector bodyE0 -> do
      projectorHead <- globalHeadM (gPrel "Projector")
      let yields0 = projYieldPlaces bodyE0
      yields <- fmap catMaybes . forM yields0 $ \case
        Right (root, path)
          -- with no place binders at all the declaration-level
          -- diagnostic already covers every yield
          | root `elem` placeNames || null placeNames -> pure (Just (root, path))
        Right (_, _) -> do
          errAt sp "E_PROJECTION_YIELD_INVALID" (Just "kappa-hs.projection.yield")
            "each 'yield' operand must be a stable place rooted in a 'place' binder of this projection (§9.1.1)"
          pure Nothing
        Left ysp -> do
          errAt ysp "E_PROJECTION_YIELD_INVALID" (Just "kappa-hs.projection.yield")
            "each 'yield' operand must be a stable place rooted in a 'place' binder of this projection (§9.1.1)"
          pure Nothing
      let bodyE = stripYields bodyE0
      bodyTm <- check ctxPl bodyE focusV
      let coreTy = pisOrd (app2 projectorHead rootsTm focusTm)
          defTm = lamsOrd (foldr (\(nm, _, _) acc -> CLamM Ordinary Expl QW nm acc) bodyTm placesLex)
      registerProjection g coreTy defTm $
        ProjInfo [isP | (isP, _) <- groups] placeNames True yields
    ProjAccessors clauses -> do
      forM_ (duplicatesOf [k | (k, _, _) <- clauses]) $ \k ->
        errAt sp "E_PROJECTION_ACCESSOR_CLAUSE_DUPLICATE" (Just "kappa-hs.projection.accessor")
          ("the accessor clause '" <> k <> "' appears more than once (§9.1.1)")
      when (length placeBs /= 1) $
        errAt sp "E_PROJECTION_EXPANDED_ACCESSOR_PLACE_BINDER_MISMATCH" (Just "kappa-hs.projection.accessor")
          "an expanded-form projection must have exactly one 'place' binder (§9.1.1)"
      case places0 of
        [] -> pure ()
        ((pName, pTyTm, pTyV) : _) -> do
          zipperHead <- globalHeadM prelZipper
          getterHead <- globalHeadM (gPrel "Getter")
          openerHead <- globalHeadM (gPrel "Opener")
          setterHead <- globalHeadM (gPrel "Setter")
          sinkerHead <- globalHeadM (gPrel "Sinker")
          let ctxP = bindCtx pName False pTyV ctxD
              zipperTm = CApp Expl (CApp Expl (CApp Expl zipperHead pTyTm) focusTm) focusTm
          zipperV <- evalIn ctxD zipperTm
          let clauseOf k = [(mb, e) | (k', mb, e) <- clauses, k' == k]
              getC = clauseOf "get"
              setC = clauseOf "set"
              inoutC = clauseOf "inout"
              sinkC = clauseOf "sink"
          -- direct clause bodies
          getTm <- forM (take 1 getC) $ \(_, e) -> check ctxP e focusV
          sinkTm <- forM (take 1 sinkC) $ \(_, e) -> check ctxP e focusV
          inoutTm <- forM (take 1 inoutC) $ \(_, e) -> check ctxP e zipperV
          setTm <- forM (take 1 setC) $ \(mb, e) -> do
            let nv = fromMaybe "new_value" (mb >>= fmap nameText . bName)
            nvV <- case mb >>= bType of
              Just tyE -> do
                (t, _) <- inferType ctxD tyE
                evalIn ctxD t
              Nothing -> pure focusV
            tm <- check (bindCtx nv False nvV ctxP) e pTyV
            pure (nv, tm)
          -- synthesized descriptors (§9.1.1)
          synthOpen <-
            case (inoutTm, getC, setC) of
              ([], ((_, getE) : _), ((mb, setE) : _)) -> do
                let nvB = fromMaybe (simpleBinder (Name "new_value" sp)) mb
                    openE =
                      EApp (EVar (Name "Zipper" sp))
                        [ ArgExplicit getE
                        , ArgExplicit (ELambda Nothing [nvB] setE sp)
                        ]
                tm <- check ctxP openE zipperV
                pure [tm]
              _ -> pure []
          synthSet <-
            case (setTm, inoutC) of
              ([], ((_, inoutE) : _)) -> do
                let newE = EVar (Name "__new" sp)
                    fillE = EApp (EDot inoutE (DotName (Name "fill" sp))) [ArgExplicit newE]
                tm <- check (bindCtx "__new" False focusV ctxP) fillE pTyV
                pure [("__new", tm)]
              _ -> pure []
          let lamP t = CLamM Ordinary Expl QW pName t
              caps =
                [ ("get", app2 getterHead rootsTm focusTm, lamP t) | t <- take 1 getTm ]
                  ++ [ ("open", app2 openerHead rootsTm focusTm, lamP t)
                     | t <- take 1 (inoutTm ++ synthOpen)
                     ]
                  ++ [ ("set", app2 setterHead rootsTm focusTm, lamP (CLamM Ordinary Expl Q1 nv t))
                     | (nv, t) <- take 1 (setTm ++ synthSet)
                     ]
                  ++ [ ("sink", app2 sinkerHead rootsTm focusTm, lamP t) | t <- take 1 sinkTm ]
              capsSorted = sortOn (\(nm, _, _) -> nm) caps
              coreTy = pisOrd (CRecordT [(nm, t) | (nm, t, _) <- capsSorted])
              defTm = lamsOrd (CRecordV [(nm, t) | (nm, _, t) <- capsSorted])
          registerProjection g coreTy defTm $
            ProjInfo [isP | (isP, _) <- groups] placeNames False []
  where
    stripYields e0 = case e0 of
      EApp (EVar y) [ArgExplicit e] | nameText y == "yield" -> e
      EIf alts mels isp ->
        EIf [(c, stripYields b) | (c, b) <- alts] (stripYields <$> mels) isp
      EMatch scrut cases msp ->
        EMatch scrut
          [ case c of
              MatchCase p mg b csp -> MatchCase p mg (stripYields b) csp
              other -> other
          | c <- cases
          ]
          msp
      EBlock ds (Just fin) bsp -> EBlock ds (Just (stripYields fin)) bsp
      EAscription e tyE asp -> EAscription (stripYields e) tyE asp
      e -> e

-- | Elaborate the ordinary (non-place) binders of a projection in
-- declaration order, returning the extended context and the telescope.
elabOrdBinders :: Ctx -> [Binder] -> CheckM (Ctx, [(Q, Text, Term)])
elabOrdBinders ctx0 [] = pure (ctx0, [])
elabOrdBinders ctx0 (b : bs) = do
  tyTm <- case binderTypeExpr b of
    Just tyE -> withGeneralizableBareTypeLevels $
      normalizeBinderDomain ctx0 b tyE >>= fmap fst . inferType ctx0
    Nothing -> freshMeta
  tyV <- evalIn ctx0 tyTm
  let nm = maybe "_" nameText (bName b)
      ctx1 = bindCtx nm (bImplicit b) tyV ctx0
  (ctx2, rest) <- elabOrdBinders ctx1 bs
  pure (ctx2, (binderQ b, nm, tyTm) : rest)

-- | Register a projection's term facet and projection-facet metadata.
registerProjection :: GName -> Term -> Term -> ProjInfo -> CheckM ()
registerProjection g coreTy defTm pj = do
  flushPending
  coreTy' <- zonkTermM 0 coreTy
  defTm' <- zonkTermM 0 defTm
  tyV <- evalIn emptyCtx coreTy'
  tmV <- evalIn emptyCtx defTm'
  addGlobal g (GlobalDef tyV (Just tmV) False)
  -- Record the projection's core definition so the native backend lowers the
  -- real selector (a CLam chain); without it the global has no recorded body
  -- and would be erased to the unit placeholder — a silent miscompile.
  recordCoreBody g defTm'
  modify' $ \st -> st {csProjections = Map.insert g pj (csProjections st)}

elabLetDecl :: DeclMods -> LetDef -> Span -> CheckM ()
elabLetDecl mods definition sp
  | Just _ <- ldConstructorPatternCandidate definition = do
      governed <- case ldName definition of
        Nothing -> pure False
        Just name -> do
          global <- ownName name
          gets (Map.member global . csCoreSignatures)
      if governed
        then
          elabLetDecl
            mods
            definition {ldConstructorPatternCandidate = Nothing}
            sp
        else do
          selected <- selectConstructorPatternLet emptyCtx sp definition
          case selected of
            Just (ConstructorPatternCandidate pattern' rhs) ->
              elabLetDecl
                mods
                definition
                  { ldName = Nothing
                  , ldPattern = Just pattern'
                  , ldConstructorPatternCandidate = Nothing
                  , ldBinders = []
                  , ldDecreases = Nothing
                  , ldBody = rhs
                  }
                sp
            Nothing ->
              elabLetDecl
                mods
                definition {ldConstructorPatternCandidate = Nothing}
                sp
-- Signature-governed functions are recorded for the SCC termination pass;
-- non-recursive values still become reducible immediately.
elabLetDecl mods (LetDef (Just n) _ Nothing _ prefix binders mResTy mdec body) sp = do
  declarationErrorsBefore <- gets (length . filter isError . csDiags)
  g <- ownName n
  noteDefinition g sp
  recordDefinitionInoutParams g binders
  mOpAlias <- if null binders then operationValueInfoOfExpr emptyCtx body else pure Nothing
  -- §8.5.2: an 'opaque' term definition keeps its equation available for
  -- definitional equality inside this module, but it is sealed
  -- (gdReducible cleared) at module end so other modules treat it as an
  -- opaque constant at its declared type.
  when (dmOpaque mods) $
    modify' $ \stM -> stM {csOpaqueDefs = Map.insert g () (csOpaqueDefs stM)}
  -- §7.4: record receiver-marked explicit binder positions (method
  -- sugar inserts the receiver at the unique such binder)
  let recvIdxs =
        [ i
        | (i, rb) <- zip [(0 :: Int) ..] [rb | rb <- binders, not (bImplicit rb)]
        , bReceiver rb /= NoReceiver
        ]
  unless (null recvIdxs) $
    modify' $ \stM -> stM {csReceivers = Map.insert g recvIdxs (csReceivers stM)}
  st <- get
  let msig = Map.lookup g (csGlobals st)
      definitionSchemaArity = maybe 0 (length . usParameters) (nameUniverseSchema n)
  case msig of
    Just gd
      | Nothing <- gdValue gd
      , let signatureSchema = gdUniverses gd
      , Just _ <- nameUniverseSchema n
      , not (dutExplicit signatureSchema)
          || dutParameterCount signatureSchema /= definitionSchemaArity ->
          errAt sp "E_UNIVERSE_SCHEMA_ARITY_MISMATCH" (Just "kappa.universe.schema-arity")
            ( "the signature and definition of top-level declaration '" <> nameText n
                <> "' must expose alpha-equivalent universe schemas; signature has "
                <> T.pack (show (dutParameterCount signatureSchema)) <> " parameters and definition has "
                <> T.pack (show definitionSchemaArity)
            )
    _ -> pure ()
  case msig of
    Just gd | Nothing <- gdValue gd -> pure ()
    _ ->
      -- no governing signature: the binding is manifest (§2.8.4)
      modify' $ \stM -> stM {csManifest = Map.insert g () (csManifest stM)}
  -- §13.2.10/§2.8: a signature-governed binding whose definiens is an
  -- identity-preserving form (record/seal/projection chain, not a
  -- function result) still preserves static-object identity
  let { manifestShaped = \case
          CGlob _ -> True
          CRecordV _ -> True
          CSealE _ x -> manifestShaped x
          CProj x _ -> manifestShaped x
          CProjAt x _ _ -> manifestShaped x
          _ -> False
      }
  let duplicateOrInfer = do
        -- a previous definition with a value: duplicate declaration (§9.2)
        case msig of
          Just gd' | isJust (gdValue gd') -> do
            enrich <- duplicateRelated (nameText n) g sp
            report $ enrich $
              diag SevError StageElaborate "E_DUPLICATE_DECLARATION" (Just "kappa-hs.name.duplicate") sp
                ("duplicate declaration of '" <> nameText n <> "'")
          _ -> pure ()
        -- no preceding signature: pre-register the name so self-references
        -- resolve and are reported as recursion-without-signature (§9.2)
        placeholderTy <- freshMetaV emptyCtx
        addGlobal g (GlobalDef placeholderTy Nothing False)
        firstMeta <- gets csNextMeta
        (tmRaw, tyRaw) <-
          elabFunction (Just (nameText n)) binders mResTy body sp
        flushPendingDeclaration
        let inferredBinders = binders ++ case body of
              ELambda _ lambdaBinders _ _ -> lambdaBinders
              _ -> []
        (tm0, ty) <-
          if null inferredBinders
            then pure (tmRaw, tyRaw)
            else do
              tyRawTerm <- quoteIn emptyCtx tyRaw
              (tmFinal, tyFinalTerm) <-
                finalizeLocalLambdaContracts True emptyCtx inferredBinders tmRaw tyRawTerm
              validateInferredLambdaGeneralization
                sp [nameText n] emptyCtx inferredBinders tmFinal tyFinalTerm
              (tyGeneralized, tmGeneralized) <-
                generalizeLocalDeclarationMetas
                  firstMeta emptyCtx sp [nameText n] tyFinalTerm tmFinal
              (tmGeneralized,) <$> evalIn emptyCtx tyGeneralized
        markInferredDeclarationLevelCandidates g ty
        tm1 <- principalizeBodyUniverseInstantiations g ty tm0
        tm <- zonkTermM 0 tm1
        when (occursGlobal g tm) $
          errAt sp "E_RECURSION_REQUIRES_SIGNATURE" (Just "kappa.type.missing-signature")
            "recursive definitions require a preceding signature declaration (§15, §9.2)"
        when (isJust mResTy) $
          checkDeclaredOrdinaryResultObservation sp tm ty
        tmV <- evalIn emptyCtx tm
        inferredObservation <- observationJudgmentForTerm emptyCtx tm ty
        observation <-
          resolveDeclaredResultObservation
            emptyCtx sp prefix (isJust mResTy) ty inferredObservation
        recordCoreBody g tm
        addGlobal g (globalDefWithObservationMode (ojMode observation) (GlobalDef ty (Just tmV) True))
        recordLevelOperatorAlias g tm
        forM_ mOpAlias (recordEffectOpValueGlobal g)
  case msig of
    Just gd | Nothing <- gdValue gd -> withActiveUniverseDefinition g $ do
      -- Pending goals raised inside the signature may have been solved
      -- to the signature's own binder rigids; re-quote the type so the
      -- solutions are baked in as proper de Bruijn variables.
      sigTy <- do
        ec <- ec_
        evalIn emptyCtx (globalCoreType ec gd)
      addGlobal g gd {gdType = sigTy}
      -- signature first: check the definition against it (recursion OK)
      -- §7.1/§7.2: a definition body is a term-expression position, so
      -- the same-spelling constructor facet wins there even under a
      -- sort-typed signature (reaching the reified type facet requires
      -- the explicit `type T` selector, §7.1.1)
      ctorFacetWins <- case body of
        EVar bn | null binders -> do
          sigF <- forceM sigTy
          case sigF of
            VSort _ -> do
              mg <- lookupGlobalName (nameText bn)
              case mg of
                Just bg -> gets (Map.member bg . csCtors)
                Nothing -> pure False
            _ -> pure False
        _ -> pure False
      tm0 <- withRecursiveSchemaOccurrenceRecording $
        if ctorFacetWins
          then case body of
            EVar bn -> do
              (tm', ty') <- infer emptyCtx (EVar bn)
              expectType emptyCtx (nameSpan bn) ty' sigTy
              pure tm'
            _ -> checkAgainstSig (Just (nameText n)) sigTy binders body sp
          else checkAgainstSig (Just (nameText n)) sigTy binders body sp
      flushPendingDeclaration
      settleActiveUniverseRequirements
      tm1 <- principalizeBodyUniverseInstantiations g sigTy tm0
      settleActiveUniverseRequirements
      tm <- zonkTermM 0 tm1
      checkDeclaredOrdinaryResultObservation sp tm sigTy
      tmV <- evalIn emptyCtx tm
      -- The observation summary is an equation over finalized Core bodies.
      -- Register this body's identity before solving that equation so direct
      -- and mutual recursive edges are recognized structurally instead of
      -- being approximated from an incomplete global table.
      recordCoreBody g tm
      inferredObservation <- observationJudgmentForTerm emptyCtx tm sigTy
      observation <-
        resolveDeclaredResultObservation
          emptyCtx sp prefix True sigTy inferredObservation
      deps <- expandedGlobalsOfTermM tm
      let recursive = Set.member g deps
          isFunction = case tm of
            CLam {} -> True
            _ -> not (null binders)
      declarationErrorsAfter <- gets (length . filter isError . csDiags)
      participates0 <- gets (Set.member g . csTerminationNames)
      let participates =
            participates0
              && declarationErrorsAfter == declarationErrorsBefore
      let termDecl = TerminationDecl g sigTy binders mdec tm sp
      when (participates && isFunction) $
        recordTerminationDecl termDecl
      earlyTerminationResult <-
        if participates && isFunction && recursive
          then do
            singletonReady <- singletonTerminationDependenciesReady g deps
            if singletonReady
              then withSccOpaque [g] (verifyTerminationScc [termDecl])
              else pure TerminationUnverified
          else pure TerminationUnverified
      reducible <-
        if recursive && not isFunction
          then do
            -- a self-referential value (no intervening function
            -- abstraction) is a definitional cycle (§15.3, §16.4)
            errAt sp "E_RECURSIVE_VALUE_CYCLE" (Just "kappa.termination.failure")
              ("recursive value cycle: '" <> nameText n
                 <> "' refers to itself without an intervening function abstraction, so its evaluation cannot terminate (§15)")
            pure False
          else if participates && isFunction
            then
              case earlyTerminationResult of
                TerminationConversionSafe -> pure True
                TerminationTotalOnly -> pure False
                TerminationUnverified -> not <$> shouldDeferTermination g deps
            else pure True
      when (manifestShaped tm) $
        modify' $ \stM -> stM {csManifest = Map.insert g () (csManifest stM)}
      currentUniverses <-
        gets
          ( maybe (gdUniverses gd) gdUniverses
              . Map.lookup g
              . csGlobals
          )
      addGlobal g gd
        { gdType = sigTy
        , gdObservationMode = ojMode observation
        , gdValue = Just tmV
        , gdReducible = reducible
        , gdUniverses = currentUniverses
        }
      recordLevelOperatorAlias g tm
      forM_ mOpAlias (recordEffectOpValueGlobal g)
      settleActiveUniverseRequirements
    _ -> duplicateOrInfer

elabLetDecl _ (LetDef Nothing _ (Just pat) _ prefix [] mty Nothing body) sp = do
  -- top-level pattern binding: bind each variable to a projection
  (bodyTm, bodyTy) <- case mty of
    Just tyE -> do
      (tyTm, _) <- inferType emptyCtx tyE
      tyV <- evalIn emptyCtx tyTm
      tm <- check emptyCtx body tyV
      pure (tm, tyV)
    Nothing -> infer emptyCtx body
  checkIrrefutable emptyCtx pat bodyTy sp
  case pat of
    PVar n -> do
      g <- ownName n
      when (isJust mty) $
        checkDeclaredOrdinaryResultObservation sp bodyTm bodyTy
      mOpAlias <- operationValueInfoOfExpr emptyCtx body
      tmV <- evalIn emptyCtx bodyTm
      inferredObservation <- observationJudgmentForTerm emptyCtx bodyTm bodyTy
      observation <-
        resolveDeclaredResultObservation
          emptyCtx sp prefix (isJust mty) bodyTy inferredObservation
      addGlobal g (globalDefWithObservationMode (ojMode observation) (GlobalDef bodyTy (Just tmV) True))
      recordLevelOperatorAlias g bodyTm
      forM_ mOpAlias (recordEffectOpValueGlobal g)
      -- Record the elaborated core body so the native backend lowers the
      -- real value (a top-level prefixed binding `let 1 x = e` / `let &x = e`
      -- reaches here as a PVar pattern); without this it has no recorded body
      -- and would be erased to the unit placeholder — a silent miscompile.
      recordCoreBody g bodyTm
    _ -> do
      (patC, ctxP, patternRefinements) <-
        elabPattern emptyCtx pat bodyTy
      bodyTyTm <- quoteIn emptyCtx bodyTy
      let names = ctxEntries ctxP
      withPatternRefinements patternRefinements $
        forM_ (zip [0 ..] names) $ \(i, entry) -> do
          let proj =
                CMatch
                  bodyTm
                  (Just bodyTyTm)
                  Nothing
                  [CaseAlt patC Nothing (CVar i)]
          g <- ownName (Name (ceName entry) sp)
          projV <- evalIn emptyCtx proj
          addGlobal
            g
            ( globalDefWithObservationMode
                (ceMode entry)
                (GlobalDef (ceType entry) (Just projV) True)
            )
          recordCoreBody g proj
elabLetDecl _ _ sp =
  unsupportedAt sp "this let-definition form is not supported at top level"

-- Termination verification (§15.3/§15.11, SCC-level).
--
-- A recursive definition is conversion-reducible only after this pass proves
-- that its whole strongly-connected component terminates.  The checker uses
-- two independent certificates:
--
--   * explicit ranking functions from `decreases`, checked on every call edge
--     f -> g by comparing g's measure at the call with f's measure at entry;
--   * size-change graphs for structural recursion, including mutual SCCs.
--
-- Surface helper names are not trusted by spelling.  Terms are normalized
-- through already-reducible globals, beta/iota/projection reduction, and then
-- classified only when primitive arithmetic semantics remain inspectable.
-- External solver results are not used to make definitions
-- conversion-reducible until there is an explicit trusted-boundary artifact
-- that records the replay data required by §15.9.
terminationSccPass :: CheckM ()
terminationSccPass = do
  st <- get
  let decls = Map.filterWithKey (\g _ -> Set.member g (csTerminationNames st)) (csTerminationDecls st)
      declKeys = Map.keysSet decls
  dependencyPairs <-
    forM (Map.elems decls) $ \td -> do
      let dependencies =
            Set.intersection declKeys (expandedGlobalsOfTerm st (tdCoreBody td))
      pure (td, dependencies)
  let dependencyMap =
        Map.fromList [(tdName td, dependencies) | (td, dependencies) <- dependencyPairs]
      depsOf td = Set.toList (Map.findWithDefault Set.empty (tdName td) dependencyMap)
      nodes = [(td, tdName td, depsOf td) | (td, _) <- dependencyPairs]
      sccs = stronglyConnComp nodes
      selfCycle td =
        tdName td
          `Set.member` Map.findWithDefault Set.empty (tdName td) dependencyMap
      recursiveGroups =
        [ group
        | scc <- sccs
        , group <- case scc of
            AcyclicSCC td | selfCycle td -> [[td]]
            CyclicSCC tds -> [tds]
            _ -> []
        ]
  classifyRecursiveSchemaOccurrences recursiveGroups
  -- Acyclic definitions may be unfolded while checking recursive SCCs.  This
  -- is safe even when such a helper mentions an unverified recursive function:
  -- unfolding the helper exposes that opaque function but cannot create a new
  -- conversion cycle through the helper itself.
  forM_ sccs $ \case
    AcyclicSCC td | not (selfCycle td) -> setGlobalReducible (tdName td) True
    _ -> pure ()
  verifyRecursiveGroups recursiveGroups
  where
    verifyRecursiveGroups [] = pure ()
    verifyRecursiveGroups groups = go groups
      where
        go pending = do
          results <- forM pending $ \tds -> do
            overrides <- gets csAssertReducible
            admissions <- gets csAssertTerminates
            let forced = all (`Set.member` overrides) (map tdName tds)
                admitted = all (`Set.member` admissions) (map tdName tds)
            result <-
              if forced then pure TerminationConversionSafe else withSccOpaque (map tdName tds) (verifyTerminationScc tds)
            case result of
              TerminationConversionSafe -> forM_ tds (\td -> setGlobalReducible (tdName td) True)
              TerminationTotalOnly -> forM_ tds (\td -> setGlobalReducible (tdName td) False)
              TerminationUnverified
                | admitted ->
                    forM_ tds (\td -> setGlobalReducible (tdName td) False)
              TerminationUnverified -> pure ()
            pure
              ( tds
              , if result == TerminationUnverified && admitted
                  then TerminationTotalOnly
                  else result
              )
          let failed = [tds | (tds, TerminationUnverified) <- results]
              madeProgress = any ((/= TerminationUnverified) . snd) results
          if null failed
            then pure ()
            else if madeProgress
              then go failed
              else forM_ failed rejectUnverified

    rejectUnverified tds = do
      overrides <- gets csAssertReducible
      occurrences <- gets csRecursiveSchemaOccurrences
      let names = Set.fromList (map tdName tds)
          forced = all (`Set.member` overrides) (map tdName tds)
      if forced
        then forM_ tds $ \td -> setGlobalReducible (tdName td) True
        else do
          forM_ tds $ \td -> setGlobalReducible (tdName td) False
          forM_ tds $ \td -> do
            let sites =
                  nub
                    [ rsoSpan occurrence
                    | occurrence <- occurrences
                    , rsoCaller occurrence == tdName td
                    , rsoCallee occurrence `Set.member` names
                    , rsoSpan occurrence /= noSpan
                    ]
            reportUnverifiedTermination
              (tdSpan td)
              sites
              ("could not verify termination of '" <> gnameText (tdName td) <> "' (§15)")
              "the recursive SCC has no checked well-founded decrease and is rejected because Kappa is total by default (§15.1–§15.2)"

verifyTerminationScc :: [TerminationDecl] -> CheckM TerminationResult
verifyTerminationScc = verifyTerminationSccIn emptyCtx

-- | Check a recursive SCC whose functions close over an already-checked
-- lexical context. Top-level declarations use 'emptyCtx'; instance members
-- use their instance-parameter and premise context. Keeping the ambient depth
-- explicit lets the same symbol- and Core-based solver reason about captured
-- values without re-encoding them as synthetic runtime arguments.
verifyTerminationSccIn :: Ctx -> [TerminationDecl] -> CheckM TerminationResult
verifyTerminationSccIn ambient tds = do
  funs <- mapM (prepareTermFunIn ambient) tds
  let funMap = Map.fromList [(tfName f, f) | f <- funs]
      explicit = [tdDecreases (tfDecl f) | f <- funs]
  case explicit of
    _ | all isNothing explicit -> do
          edges <- collectSccEdges funMap
          structural <- structuralSccOKWithEdges funMap Nothing edges
          if structural
            then pure TerminationConversionSafe
            else boolCert TerminationTotalOnly <$> inferredMeasureSccOKWithEdges edges funMap
      | any isNothing explicit -> pure TerminationUnverified
      | all isStructuralDec explicit -> do
          valid <- validateStructuralSelections funs
          if valid
            then do
              edges <- collectSccEdges funMap
              boolCert TerminationConversionSafe
                <$> structuralSccOKWithEdges funMap (Just (structuralSelections funs)) edges
            else pure TerminationUnverified
      | all isMeasureDec explicit -> do
          -- A `decreases <measure>` annotation states intent, but if the
          -- recursion is in fact STRUCTURAL — the recursive call passes a
          -- constructor sub-term of an argument (e.g. `decreases listLength
          -- xs` recursing on the tail of `xs`) — accept it by structural
          -- descent. Structural descent is the stronger, conversion-safe
          -- guarantee and subsumes any size-like measure: the recursion
          -- demonstrably terminates regardless of the (possibly
          -- non-arithmetic) measure the author named. Fall back to the
          -- arithmetic measure proof for genuinely non-structural measures
          -- (e.g. `decreases fuel` / `decreases max 0 n` on an Int counter).
          --
          -- Certify TOTALITY only (TerminationTotalOnly), NOT conversion
          -- safety: an explicit `decreases` measure signals the author
          -- intends a *total* (not necessarily δ-reducible) definition, and
          -- granting conversion-reducibility here would change how the body
          -- unfolds during conversion — perturbing downstream analyses such
          -- as match exhaustiveness. Clearing the termination warning must
          -- not silently alter reduction behavior.
          edges <- collectSccEdges funMap
          struct <- structuralSccOKWithEdges funMap Nothing edges
          if struct
            then pure TerminationTotalOnly
            else boolCert TerminationTotalOnly <$> measureSccOKWithEdges funMap edges
      | otherwise -> pure TerminationUnverified
  where
    boolCert yes ok = if ok then yes else TerminationUnverified
    isStructuralDec = \case
      Just DecStructural {} -> True
      _ -> False
    isMeasureDec = \case
      Just DecMeasure {} -> True
      _ -> False
    structuralSelections funs =
      Map.fromList
        [ (tfName f, ns)
        | f <- funs
        , Just (DecStructural xs) <- [tdDecreases (tfDecl f)]
        , let ns = map nameText xs
        ]
    validateStructuralSelections funs = and <$> mapM validateOne funs
    validateOne f =
      case tdDecreases (tfDecl f) of
        Just (DecStructural xs) -> do
          oks <- forM xs $ \x -> do
            let nm = nameText x
            if nm `elem` tfParamNames f
              then pure True
              else do
                report $
                  diag SevError StageElaborate "E_TERMINATION_INVALID_STRUCTURAL_TARGET" (Just "kappa.termination.invalid_structural_target") (nameSpan x)
                    ( "decreases structural target '" <> nm <> "' is not an explicit parameter of '"
                        <> gnameText (tfName f)
                        <> "' (§15.3)"
                    )
                pure False
          pure (and oks)
        _ -> pure True

-- Compatibility wrapper used by a few older call sites and useful in ghci.
-- The real implementation above works over SCCs; a singleton self-SCC is the
-- direct-recursion special case, not a separate algorithm.
terminationOK :: GName -> Value -> [Binder] -> Maybe Decreases -> Term -> CheckM Bool
terminationOK g sigTy binders mdec tm =
  (/= TerminationUnverified) <$> verifyTerminationScc [TerminationDecl g sigTy binders mdec tm noSpan]

prepareTermFun :: TerminationDecl -> CheckM TermFun
prepareTermFun = prepareTermFunIn emptyCtx

prepareTermFunIn :: Ctx -> TerminationDecl -> CheckM TermFun
prepareTermFunIn ambient td = do
  ctx <- measureCtxFromSigIn ambient (tdSigType td) (tdBinders td)
  natLvls <- ctxNatLevels ctx
  let (params, body, depth0) =
        peelTermParamsAt (ctxLen ambient) (tdCoreBody td)
      explParams = [lvl | (Expl, lvl) <- params]
      explNames = [nameText n | b <- tdBinders td, not (bImplicit b), Just n <- [bName b]]
  mSpec <- case tdDecreases td of
    Just (DecMeasure measure byRel usingProof) -> do
      (m0, mTy0) <- infer ctx measure
      (mTm0, mTy) <- insertAllImplicits ctx (exprSpan measure) m0 mTy0
      mTyKey <- quoteIn ctx mTy >>= normalizeTermAt (ctxLen ctx)
      relSpec <- traverse (prepareRelationSpec ctx (ctxLen ctx) mTy) byRel
      -- Store the elaborated measure itself.  Recursive-call checking
      -- normalizes it after the SCC pass has marked acyclic helpers
      -- reducible, so transparent helper arithmetic is exposed without
      -- trusting helper names during initial declaration checking.
      pure (Just (MeasureSpec mTm0 mTyKey relSpec usingProof (ctxLen ctx)))
    _ -> pure Nothing
  pure
    TermFun
      { tfDecl = td
      , tfName = tdName td
      , tfCtx = ctx
      , tfNatLvls = natLvls
      , tfParams = params
      , tfExplParams = explParams
      , tfParamNames = explNames
      , tfBody = body
      , tfDepth = depth0
      , tfMeasure = mSpec
      }

prepareRelationSpec :: Ctx -> Int -> Value -> Expr -> CheckM RelationSpec
prepareRelationSpec ctx d measureTy relE = do
  checkedType <- tryRelationCheck ctx measureTy relE RelationReturnsType
  checked <- case checkedType of
    Just ok -> pure (Just ok)
    Nothing -> tryRelationCheck ctx measureTy relE RelationReturnsBool
  case checked of
    Just (rTm0, rTy, flavor) -> do
      rTm <- normalizeTermAt d rTm0
      rTyKey <- quoteIn ctx rTy >>= normalizeTermAt d
      rKey <- relationCanonicalKey d flavor rTm
      wf <- relationWellFoundedEvidence ctx d measureTy rTm flavor
      pure (RelationSpec rTm rTyKey flavor rKey d wf)
    Nothing -> do
      -- Keep the relation syntactically available for diagnostics and keys,
      -- but classify it as unusable for termination.  This path is reached
      -- only after the expression failed to check as either
      -- m -> m -> Type or m -> m -> Bool.
      (r0, rTy0) <- infer ctx relE
      (rTm0, rTy) <- insertAllImplicits ctx (exprSpan relE) r0 rTy0
      rTm <- normalizeTermAt d rTm0
      rTyKey <- quoteIn ctx rTy >>= normalizeTermAt d
      rKey <- relationCanonicalKey d RelationUnknown rTm
      pure (RelationSpec rTm rTyKey RelationUnknown rKey d False)

tryRelationCheck :: Ctx -> Value -> Expr -> RelationFlavor -> CheckM (Maybe (Term, Value, RelationFlavor))
tryRelationCheck ctx measureTy relE flavor = do
  expected <- relationExpectedType ctx measureTy flavor
  saved <- get
  let diagCount0 = length (csDiags saved)
  r0 <- withDemand DemandRead (check ctx relE expected)
  diagCount1 <- gets (length . csDiags)
  if diagCount1 == diagCount0
    then do
      rTm <- zonkTermM (ctxLen ctx) r0
      pure (Just (rTm, expected, flavor))
    else put saved >> pure Nothing

checkAgainstSig :: Maybe Text -> Value -> [Binder] -> Expr -> Span -> CheckM Term
checkAgainstSig retName sigTy binders body sp = do
  -- consume binders against the signature's Pi telescope. §18.5: the body
  -- is the named function's body, so a `return@<name>` inside it resolves.
  go (emptyCtx {ctxReturnTarget = retName}) sigTy binders
  where
    -- §9.1: `let name = \binders -> body` is a named function `name`; the
    -- RHS lambda inherits the name as its return target. Inject it as the
    -- lambda's label so `return@name` inside the body resolves (an explicit
    -- label on the lambda is kept).
    body' = case (binders, body, retName) of
      ([], ELambda Nothing lbs lbody lsp, Just nm) -> ELambda (Just (Name nm lsp)) lbs lbody lsp
      _ -> body
    -- The function body do IS the return target's completion boundary, so
    -- elaborate it directly with ctxReturnTarget preserved (the generic
    -- EDo path would reset it, treating it as a nested do). §18.5.
    go ctx ty0 [] = do
      callableType <- peelCapturesM ty0
      case callableType of
        VPiBoundM mode Impl q _ nm assumption dom clo
          | not bodyStartsWithLambda ->
              -- Preserve an already-polymorphic body before introducing an
              -- omitted signature binder, but only when synthesis confirms
              -- that the body itself starts with an implicit callable
              -- telescope.  A speculative direct check alone is not enough:
              -- it may postpone an incompatible carrier/evidence obligation
              -- and appear diagnostic-free until the declaration boundary.
              -- Monomorphic bodies (notably @do@ blocks) must instead see the
              -- signature binders while they are elaborated.
              bodySynthesizesImplicit ctx >>= \case
                True ->
                  tryExpectedReading (checkBody ctx ty0) >>= \case
                    Just direct -> pure direct
                    Nothing ->
                      tryExpectedReading (skipImplicit ctx mode q nm assumption dom clo []) >>= \case
                        Just etaExpanded -> pure etaExpanded
                        -- Both readings failed.  Re-run the original direct
                        -- comparison so diagnostics describe the two
                        -- higher-rank types, not incidental implicit search
                        -- performed by the discarded eta alternative.
                        Nothing -> checkBody ctx ty0
                False -> skipImplicit ctx mode q nm assumption dom clo []
        -- No definition binder remains: an outer capture annotation is now
        -- the demanded result environment, not a transparent callable
        -- wrapper. Preserve it for closure inference and containment.
        _ -> checkBody ctx ty0
    go ctx ty0 (b : rest) = do
      -- §12.3.1 capture environments refine function identity without adding
      -- a source parameter. Peel them only while consuming a definition
      -- binder; the result type (the zero-binder case above) remains wrapped.
      (ty, captureRegions) <- peelCapturesWithRegionsM ty0
      case ty of
        VPiBoundM mode Impl q borrowed nm assumption dom clo
          | not (bImplicit b)
          , (nameText <$> bName b) /= Just nm -> do
              -- An unnamed trait-arrow binder may be named explicitly by a
              -- definition when the source supplies one more explicit binder
              -- than the remaining explicit Pi telescope. This is ordinary
              -- explicit dictionary passing (`let f A ev x = ...`) and is
              -- unambiguous with the elided form (`let f A x = ...`).
              cod <- clApp clo (VRigid (ctxLen ctx) [])
              traitBinder <- isTraitGoal dom
              remaining <- explicitPiArity (ctxLen ctx + 1) cod
              let supplied = length [() | sb <- b : rest, not (bImplicit sb)]
              if traitBinder && supplied > remaining
                then claim ctx mode Impl q borrowed captureRegions nm assumption dom clo b rest
                else skipImplicit ctx mode q nm assumption dom clo (b : rest)
        VPiBoundM mode Impl q borrowed nm assumption dom clo
          | bImplicit b
          , nm /= "_"
          , Just suppliedName <- nameText <$> bName b
          , suppliedName /= nm -> do
              codomain <- clApp clo (VRigid (ctxLen ctx) [])
              namedLater <-
                implicitBinderNamed
                  (ctxLen ctx + 1)
                  suppliedName
                  codomain
              if namedLater
                then
                  -- All forall binders are omittable implicits. Stable source
                  -- binder identity disambiguates omission from alpha-renaming:
                  -- when this name belongs to a later implicit slot, introduce
                  -- the intervening signature binder and retry unchanged.
                  skipImplicit ctx mode q nm assumption dom clo (b : rest)
                else case binderTypeExpr b of
                  Just tyE -> do
                    -- A differently named annotated binder claims the current
                    -- Pi only when its annotation matches. Otherwise it may be
                    -- targeting a later anonymous/generated implicit.
                    st0 <- get
                    nBefore <- gets (length . csDiags)
                    ok <- do
                      (tyTm, _) <- inferBinderDomainType ctx b tyE
                      tyV <- evalIn ctx tyTm
                      unify ctx dom tyV
                    nAfter <- gets (length . csDiags)
                    put st0
                    if ok && nAfter == nBefore
                      then claim ctx mode Impl q borrowed captureRegions nm assumption dom clo b rest
                      else skipImplicit ctx mode q nm assumption dom clo (b : rest)
                  Nothing ->
                    -- No later slot owns the supplied name and no annotation
                    -- says otherwise, so this is ordinary alpha-renaming of
                    -- the current implicit binder.
                    claim ctx mode Impl q borrowed captureRegions nm assumption dom clo b rest
        VPiBoundM mode ic q borrowed nm assumption dom clo ->
          claim ctx mode ic q borrowed captureRegions nm assumption dom clo b rest
        _ -> do
          errAt sp "E_SIGNATURE_ARITY" (Just "kappa-hs.type.signature-arity")
            "definition has more parameters than its signature type"
          check ctx body ty
    skipImplicit ctx mode q nm assumption dom clo bs = do
      withBound <- extendLevelAssumption sp ctx assumption
      let ctx' = bindCtxMQ mode q nm True dom withBound
      cod <- clApp clo (VRigid (ctxLen ctx) [])
      CLamM mode Impl q nm <$> go ctx' cod bs

    bodyStartsWithLambda = case body' of
      ELambda {} -> True
      _ -> False

    -- This is a read-only classification probe.  Inference can allocate metas,
    -- enqueue evidence, and record usage even when it reports no diagnostic,
    -- so every state component is restored before returning the answer.
    bodySynthesizesImplicit _ | EDo {} <- body' = pure False
    bodySynthesizesImplicit ctx = do
      st0 <- get
      n0 <- gets (length . csDiags)
      (_, actual0) <- infer ctx body'
      actual <- peelCapturesM actual0
      n1 <- gets (length . csDiags)
      let hasImplicit = case actual of
            VPiBoundM _ Impl _ _ _ _ _ _ -> True
            _ -> False
      put st0
      pure (n0 == n1 && hasImplicit)

    -- Choosing between the direct higher-rank reading and eta-expanding an
    -- omitted signature forall is structural recovery, not a demand that the
    -- chosen body be error-free. A reading whose only failure is its selected
    -- evidence obligation is the right reading and must retain that single
    -- cause; discarding it would replace E_UNSOLVED_IMPLICIT with a misleading
    -- whole-function type mismatch. Every other speculative failure restores
    -- the complete checker state.
    tryExpectedReading action = do
      initial <- get
      diagnosticCount <- gets (length . csDiags)
      result <- action
      diagnostics <- gets csDiags
      let added = take (length diagnostics - diagnosticCount) diagnostics
          evidenceOnly =
            not (null added)
              && all ((== "E_UNSOLVED_IMPLICIT") . dCode) added
      if null added || evidenceOnly
        then pure (Just result)
        else put initial >> pure Nothing

    checkBody ctx ty = case body' of
      EDo mlbl items isp -> do
        (tm, ty') <- elabDo ctx mlbl items isp (Just ty)
        expectType ctx isp ty' ty
        pure tm
      _ -> check ctx body' ty
    claim ctx mode ic q borrowed captureRegions nm assumption dom clo b rest = do
      let bn = fromMaybe nm (nameText <$> bName b)
      forM_ (binderTypeExpr b) $ \tyE -> do
        (tyTm, _) <- inferBinderDomainType ctx b tyE
        tyV <- evalIn ctx tyTm
        expectTypeAfterPendingEvidence ctx (bSpan b) dom tyV
      unless (ic == (if bImplicit b then Impl else Expl) || ic == Impl) $
        errAt (bSpan b) "E_BINDER_MISMATCH" (Just "kappa-hs.type.binder")
          "binder implicitness does not match the signature"
      withBound <- extendLevelAssumption (bSpan b) ctx assumption
      -- A source binder may explicitly name an implicit signature slot (most
      -- notably a trait-arrow dictionary).  Candidate status follows the
      -- checked Pi binder, not the surface spelling used to claim it; the
      -- resulting Core lambda is implicit and the dictionary must remain
      -- available to ordinary implicit resolution in the body.
      let ctx'0 = bindCtxMQ mode q bn (ic == Impl) dom withBound
      ctx' <- recordBinderCaptureRegion ctx b borrowed captureRegions ctx'0
      cod <- clApp clo (VRigid (ctxLen ctx) [])
      CLamM mode ic q bn <$> go ctx' cod rest

    explicitPiArity lvl ty0 = do
      ty <- peelCapturesM ty0
      case ty of
        VPi ic _ _ _ _ clo -> do
          cod <- clApp clo (VRigid lvl [])
          rest <- explicitPiArity (lvl + 1) cod
          pure (if ic == Expl then rest + 1 else rest)
        _ -> pure (0 :: Int)

    implicitBinderNamed lvl target ty0 = do
      ty <- peelCapturesM ty0
      case ty of
        VPiBoundM _ Impl _ _ name _ _ closure
          | name == target -> pure True
          | otherwise -> do
              codomain <- clApp closure (VRigid lvl [])
              implicitBinderNamed (lvl + 1) target codomain
        _ -> pure False

elabFunction :: Maybe Text -> [Binder] -> Maybe Expr -> Expr -> Span -> CheckM (Term, Value)
elabFunction retName [] mResTy body _ =
  let ctx = emptyCtx {ctxReturnTarget = retName}
   in case mResTy of
        Just tyE -> do
          (tyTm, _) <- inferType ctx tyE
          tyV <- evalIn ctx tyTm
          tm <- check ctx body tyV
          pure (tm, tyV)
        Nothing -> do
          -- A declaration boundary preserves an already-polymorphic value.
          -- Implicit insertion belongs to a use/application site; performing
          -- it here silently specializes @let boo = foo@ and destroys foo's
          -- existing forall telescope (§11.3.3).
          infer ctx body
elabFunction retName binders mResTy body sp = do
  let ctx = emptyCtx {ctxReturnTarget = retName}
  case mResTy of
    -- A fully annotated named definition is definitionally the same
    -- declaration contract as a separate signature followed by a body.
    -- Elaborating only an ascription on the body loses the source-level
    -- identity of transparent type aliases when the inferred Pi is quoted.
    -- Build and check against the complete annotated telescope instead.
    Just resultType
      | all (isJust . binderTypeExpr) binders -> do
          let declarationType = foldr EArrow resultType binders
          (typeTerm, _) <-
            withNamedCallableInoutSignature declarationType
              (inferType ctx declarationType)
          typeValue <- evalIn ctx typeTerm
          elabNamedDeclLambda ctx binders body sp (Just typeValue)
    Just resultType ->
      elabNamedDeclLambda ctx binders (EAscription body resultType sp) sp Nothing
    Nothing ->
      elabNamedDeclLambda ctx binders body sp Nothing

-- | §14.3 instance pre-pass: elaborate and register the head of every
-- top-level instance declaration (instance-set entry plus the
-- dictionary global's type) before any declaration body is checked,
-- so instance visibility within the module does not depend on
-- declaration order. Instance heads depend only on header-pass
-- artifacts (traits, data types, aliases; lowercase head names are
-- implicitly universalized per §11.3.3), so this is sound ahead of
-- the body pass. Member bodies are still checked in source order by
-- 'elabInstance'.
planDerivedDeclarations :: [Decl] -> CheckM ()
planDerivedDeclarations declarations = do
  requests <- fmap catMaybes . forM declarations $ \case
    DDerive headExpression sourceSpan -> do
      (traitIdentity, _, arguments) <- instSplitHead headExpression
      case (traitIdentity, arguments) of
        (Just trait, [target]) -> do
          targetTerm <- fst <$> inferType emptyCtx target
          targetTerm' <- zonkTermM 0 targetTerm
          pure
            ( Just
                ( sourceSpan
                , trait
                , target
                , targetTerm'
                )
            )
        _ -> do
          errAt sourceSpan "E_DERIVE_HEAD" (Just "kappa.derive")
            "derive expects one supported trait applied to one target type (§14.5)"
          pure Nothing
    _ -> pure Nothing
  let isSetTrait = gPrel "IsSet"
      eqTrait = gPrel "Eq"
  forM_ requests $ \(sourceSpan, trait, target, targetTerm) -> do
    generated <-
      if trait == isSetTrait
        then pure [derivedEmptyInstance sourceSpan 1 "IsSet" target]
        else
          if trait == eqTrait
            then do
              eqDeclaration <- derivedEqDecl sourceSpan 2 target targetTerm
              explicitIsSet <-
                anyM
                  (\(_, requestTrait, _, requestTarget) ->
                     if requestTrait == isSetTrait
                       then termsMatchTransactionally targetTerm requestTarget
                       else pure False)
                  requests
              registeredIsSet <- matchingEvidenceExists isSetTrait targetTerm
              pure $
                ( if explicitIsSet || registeredIsSet
                    then []
                    else [derivedEmptyInstance sourceSpan 1 "IsSet" target]
                )
                  ++ [eqDeclaration]
            else
              if trait == gPrel "RefinementView"
                then pure [derivedEmptyInstance sourceSpan 1 "RefinementView" target]
                else
                  if trait == gPrel "ExactNaturalRepresentation"
                    then pure [derivedEmptyInstance sourceSpan 1 "ExactNaturalRepresentation" target]
                    else pure [derivedWholeInstance sourceSpan trait target]
    modify' $ \state ->
      state {csDerivedDecls = Map.insert sourceSpan generated (csDerivedDecls state)}
    mapM_ instanceHeadPass generated
  where
    -- Paired derive requests are compared by checked Core under an isolated
    -- solver state. Independently fresh universe occurrence metas therefore
    -- do not manufacture duplicate evidence, while failed comparison cannot
    -- constrain either declaration (§14.5.1, §33.2.1).
    termsMatchTransactionally left right = do
      saved <- get
      matches <- termMatchesTerm emptyCtx left right
      put saved
      pure matches

    -- Reuse ordinary, identity-backed instance selection to detect an IsSet
    -- artifact already declared outside the derive request list. This keeps
    -- target equivalence, universe specialization, and head normalization in
    -- the same authority as every later evidence lookup.
    matchingEvidenceExists trait target = do
      saved <- get
      targetValue <- evalIn emptyCtx target
      goal <- globalValueM trait [(Expl, targetValue)]
      found <- isJust <$> traitEvidence emptyCtx noSpan goal
      put saved
      pure found

    anyM predicate = go
      where
        go [] = pure False
        go (value : rest) = do
          found <- predicate value
          if found then pure True else go rest

-- | Dependent refinement fibers can contain ordinary type/evidence metas that
-- are finalized only after the complete module header and instance set has
-- been checked. The derive head is registered by 'planDerivedDeclarations';
-- after header evidence finalization this pass replaces its head-only
-- placeholder with the checked generated members. This mirrors the ordinary
-- instance header/body split and avoids order-dependent retries.
finalizeDerivedRefinementDeclarations :: [Decl] -> CheckM ()
finalizeDerivedRefinementDeclarations declarations =
  forM_ declarations $ \case
    DDerive headExpression sourceSpan -> do
      (traitIdentity, _, arguments) <- instSplitHead headExpression
      case (traitIdentity, arguments) of
        (Just trait, [target])
          | trait == gPrel "RefinementView" -> do
              targetTerm0 <- fst <$> inferType emptyCtx target
              targetTerm <- zonkTermM 0 targetTerm0
              shape <- deriveRefinementViewShape sourceSpan target targetTerm
              let generated =
                    [ maybe
                        (derivedEmptyInstance sourceSpan 1 "RefinementView" target)
                        (derivedRefinementViewDecl sourceSpan target)
                        shape
                    ]
              modify' $ \state ->
                state
                  { csDerivedDecls =
                      Map.insert sourceSpan generated (csDerivedDecls state)
                  }
        _ -> pure ()
    _ -> pure ()

-- | §14.5.2 eligibility and predicate recovery. This deliberately works from
-- the checked constructor telescope:
--
-- * one ordinary runtime-kept field is the base;
-- * every other source field is erased quantity-0 evidence;
-- * one field has checked type @IsProp P@ and one has checked type @P@;
-- * the two fibers are definitionally equal; and
-- * the predicate contains no unresolved meta except the selected base-field
--   meta, which is abstracted into the generated associated predicate.
--
-- Requiring exactly the base/IsProp/proof triple is the v1 deterministic
-- filler fragment. Shapes with additional erased fields fail closed until
-- those fields have a checked synthesis rule.
deriveRefinementViewShape
  :: Span
  -> Expr
  -> Term
  -> CheckM (Maybe DerivedRefinementViewShape)
deriveRefinementViewShape sourceSpan target _requestTargetTerm = do
  -- Re-specialize the target under the checked derived-head occurrence.
  -- Eligibility itself performs no evidence search and cannot be justified by
  -- the instance being generated.
  settledTargetTerm0 <- fst <$> inferType emptyCtx target
  settledTargetTerm <- zonkTermM 0 settledTargetTerm0
  deriveRefinementViewShapeSettled sourceSpan settledTargetTerm

deriveRefinementViewShapeSettled
  :: Span
  -> Term
  -> CheckM (Maybe DerivedRefinementViewShape)
deriveRefinementViewShapeSettled sourceSpan targetTerm = do
  state <- get
  case nominalDataHead targetTerm >>= \dataName -> (dataName,) <$> Map.lookup dataName (csDatas state) of
    Just (_dataName, dataInfo)
      | [constructor] <- diCtors dataInfo
      , Just constructorInfo <- Map.lookup constructor (csCtors state) -> do
          targetValue <- evalIn emptyCtx targetTerm
          (_universes, _constructorType, arguments, namedBinders, _explicitFields) <-
            instantiateConstructorForFields
              emptyCtx
              constructor
              constructorInfo
              targetValue
              sourceSpan
          let sourceFieldCount = length (ciSourceFields constructorInfo)
              sourceBinders =
                drop (length namedBinders - sourceFieldCount) namedBinders
              sourceContracts = constructorSourceContracts constructorInfo
              instantiatedFields0 =
                [ InstantiatedRefinementField
                    sourceIndex
                    argumentIndex
                    mode
                    quantity
                    runtimeErasure
                    fieldType
                    argument
                | (sourceIndex, ((argumentIndex, _fieldName, mode, quantity, fieldType), (_icit, _sourceQuantity, runtimeErasure))) <-
                    zip [0 :: Int ..] (zip sourceBinders sourceContracts)
                , Just argument <- [arguments `atMay` argumentIndex]
                ]
          connectedEvidence <-
            pendingEvidenceComponent emptyCtx (map irfType instantiatedFields0)
          flushPendingSelected connectedEvidence
          instantiatedFields <-
            forM instantiatedFields0 $ \field -> do
              fieldTypeTerm <-
                quoteIn emptyCtx (irfType field) >>= zonkTermM 0
              fieldType <- evalIn emptyCtx fieldTypeTerm
              pure field {irfType = fieldType}
          ec <- ec_
          let retainedFields =
                [ field
                | field <- instantiatedFields
                , Repr.runtimeConstructorPiField
                    ec
                    (irfArgumentIndex field)
                    (irfRuntimeErasure field)
                    (caIcit (irfArgument field))
                    (irfQuantity field)
                    (irfType field)
                ]
              erasedFields =
                [ field
                | field <- instantiatedFields
                , field `notElemByIndex` retainedFields
                ]
              exactSourceShape =
                length instantiatedFields == sourceFieldCount
                  && and
                    [ caIcit (irfArgument field) == sourceIcit
                    | (field, (sourceIcit, _sourceName)) <-
                        zip instantiatedFields (ciSourceFields constructorInfo)
                    ]
          case retainedFields of
            [baseField]
              | exactSourceShape
              , irfMode baseField == Ordinary
              , length instantiatedFields == 3
              , all ((== Q0) . irfQuantity) erasedFields -> do
                  baseArgument <- zonkTermM 0 (caTerm (irfArgument baseField))
                  case stripIdentityWrappers baseArgument of
                    CMeta baseMeta -> do
                      classified <-
                        forM erasedFields $ \field ->
                          (field,) <$> refinementIsPropFiber (irfType field)
                      let isPropFields =
                            [ (field, fiber)
                            | (field, Just fiber) <- classified
                            ]
                          proofFields =
                            [ field
                            | (field, Nothing) <- classified
                            ]
                          matchingPairs =
                            [ (isPropField, proofField, fiber)
                            | (isPropField, fiber) <- isPropFields
                            , proofField <- proofFields
                            , convertible ec 0 fiber (irfType proofField)
                            ]
                      case matchingPairs of
                        [(isPropField, proofField, fiber)] -> do
                          baseTypeTerm <-
                            quoteIn emptyCtx (irfType baseField) >>= zonkTermM 0
                          predicateTerm0 <-
                            quoteIn emptyCtx fiber >>= zonkTermM 0
                          let predicateTerm =
                                mapTermWithDepth
                                  ( \depth -> \case
                                      CMeta meta
                                        | meta == baseMeta -> Just (CVar depth)
                                      _ -> Nothing
                                  )
                                  0
                                  predicateTerm0
                              noResidualMetas =
                                null (metaIdsOf baseTypeTerm)
                                  && null (metaIdsOf predicateTerm)
                              baseName = "__derive_refinement_base"
                              sourceNames = map snd (ciSourceFields constructorInfo)
                              baseFieldName =
                                sourceNames `atMay` irfSourceIndex baseField >>= id
                              isPropFieldName =
                                sourceNames `atMay` irfSourceIndex isPropField >>= id
                              proofFieldName =
                                sourceNames `atMay` irfSourceIndex proofField >>= id
                              checkedSourceModes =
                                ( caIcit (irfArgument baseField)
                                , caIcit (irfArgument isPropField)
                                , caIcit (irfArgument proofField)
                                )
                          pure $ do
                            guard noResidualMetas
                            guard (checkedSourceModes == (Expl, Impl, Impl))
                            isPropName <- isPropFieldName
                            proofName <- proofFieldName
                            baseType <-
                              delaborateTypeWithEnv emptyCtx sourceSpan [] baseTypeTerm
                            predicateBody <-
                              delaborateTypeWithEnv
                                emptyCtx
                                sourceSpan
                                [baseName]
                                predicateTerm
                            pure
                              DerivedRefinementViewShape
                                { drvsConstructor = constructor
                                , drvsFieldCount = length instantiatedFields
                                , drvsFieldIcit = map (caIcit . irfArgument) instantiatedFields
                                , drvsBaseIndex = irfSourceIndex baseField
                                , drvsIsPropIndex = irfSourceIndex isPropField
                                , drvsProofIndex = irfSourceIndex proofField
                                , drvsBaseFieldName = baseFieldName
                                , drvsIsPropFieldName = isPropName
                                , drvsProofFieldName = proofName
                                , drvsBaseType = baseType
                                , drvsPredicateBody = predicateBody
                                }
                        _ -> pure Nothing
                    _ -> pure Nothing
            _ -> pure Nothing
    _ -> pure Nothing
  where
    atMay values index
      | index < 0 = Nothing
      | otherwise = listToMaybe (drop index values)
    field `notElemByIndex` others =
      all ((/= irfSourceIndex field) . irfSourceIndex) others

derivedEqDecl :: Span -> Int -> Expr -> Term -> CheckM Decl
derivedEqDecl sourceSpan discriminator target targetTerm = do
  (shape, premises) <- deriveNominalShape emptyCtx sourceSpan targetTerm
  let span' = derivedGeneratedSpan sourceSpan discriminator
      xName = Name "__derive_x" span'
      yName = Name "__derive_y" span'
      member name binders body =
        DLet noMods
          ( LetDef
              (Just (Name name span'))
              False
              Nothing
              Nothing
              emptyPrefix
              binders
              Nothing
              Nothing
              body
          )
          span'
      equalityBody =
        derivedEqualityBody span' target shape xName yName
  pure $
    DInstance
      ( InstanceDecl
          Nothing
          premises
          (derivedTraitHead span' "Eq" target)
          ( InstanceMembers
              [ member "==" [simpleBinder xName, simpleBinder yName] equalityBody
              ]
          )
      )
      span'

-- | Stable, identity-backed source shape used only to generate ordinary
-- pattern syntax. Constructor and target identities come from the checked
-- header tables; textual names are emitted and then resolved by the ordinary
-- pattern checker. The checked field term is retained so later law synthesis
-- can authenticate the exact evidence selected by the checked comparator.
deriveNominalShape
  :: Ctx
  -> Span
  -> Term
  -> CheckM (DerivedNominalShape, [Expr])
deriveNominalShape ctx sourceSpan target = do
  state <- get
  case nominalDataHead target >>= (`Map.lookup` csDatas state) of
    Nothing -> pure ([], [])
    Just info -> do
      targetValue <- evalIn ctx target
      constructors <-
        forM
        [ (constructor, constructorInfo)
        | constructor <- diCtors info
        , Just constructorInfo <- [Map.lookup constructor (csCtors state)]
        ] $ \(constructor, constructorInfo) -> do
          instantiated <-
            ctorFieldTypesWithQ
              ctx
              constructor
              constructorInfo
              targetValue
              sourceSpan
          let explicitSourceCount =
                length
                  [ ()
                  | (icit, _) <- ciSourceFields constructorInfo
                  , icit == Expl
                  ]
              sourceFields =
                drop (length instantiated - explicitSourceCount) instantiated
          fields <-
            forM sourceFields $ \(_, quantity, fieldValue) -> do
              fieldType <- quoteIn ctx fieldValue >>= zonkTermM (ctxLen ctx)
              case delaborateType ctx sourceSpan fieldType of
                Just fieldExpression ->
                  pure
                    ( DerivedNominalField
                        quantity
                        fieldType
                        fieldExpression
                    )
                Nothing -> do
                  errAt sourceSpan "E_DERIVE_UNSUPPORTED" (Just "kappa.derive")
                    "derive Eq could not reify one checked field type as ordinary source syntax (§14.5.1)"
                  pure
                    ( DerivedNominalField
                        quantity
                        fieldType
                        (EHole Nothing sourceSpan)
                    )
          pure (constructor, fields)
      let self = nominalDataHead target
          premiseCandidates =
            [ (trait, fieldType, fieldExpression)
            | (_, fields) <- constructors
            , DerivedNominalField quantity fieldType fieldExpression <- fields
            , let trait =
                    if quantity == Q0
                      then gPrel "IsProp"
                      else gPrel "Eq"
            , quantity == Q0 || nominalDataHead fieldType /= self
            ]
          uniquePremises =
            nubBy
              (\(leftTrait, leftType, _) (rightTrait, rightType, _) ->
                 leftTrait == rightTrait && leftType == rightType)
              premiseCandidates
          premises =
            [ derivedTraitHead sourceSpan (gnameText trait) fieldExpression
            | (trait, _, fieldExpression) <- uniquePremises
            ]
          shape =
            [ (constructor, fields)
            | (constructor, fields) <- constructors
            ]
      pure (shape, premises)

-- | Align each runtime-relevant nominal field with the exact @Eq@ dictionary
-- selected by the already checked comparator. The comparator Core, dictionary
-- classifier, trait identity, and carrier conversion all participate in the
-- check; source spellings do not. A comparator with a different control-flow
-- shape (including a call to a recursive helper) returns 'Nothing' for the
-- functional-induction provider rather than guessing an alignment.
derivedEqEvidenceForComparator
  :: Ctx
  -> Span
  -> DerivedNominalShape
  -> Term
  -> CheckM (Maybe ([DerivedEqEvidenceBinding], DerivedEqEvidenceNames))
derivedEqEvidenceForComparator ctx site shape comparator = do
  runtimeFields <-
    forM runtimeFieldTerms $ \(constructor, fieldIndex, fieldType) ->
      (constructor, fieldIndex,) <$> evalIn ctx fieldType
  evidenceComponent <-
    pendingEvidenceComponentTerms ctx (map snd rawCandidates)
  flushPendingSelected evidenceComponent
  checkedCandidates <-
    forM rawCandidates $ \(depth, dictionary) -> do
      checked <- zonkTermM (ctxLen ctx + depth) dictionary
      pure (shiftTerm (-depth) 0 checked)
  candidates <- mapM authenticate checkedCandidates
  case sequence candidates of
    Nothing -> pure Nothing
    Just exact
      | length exact /= length runtimeFields -> pure Nothing
      | otherwise -> do
          let aligned = zip runtimeFields exact
          beforeAlignment <- get
          carrierMatches <-
            forM aligned $ \((_, _, fieldType), (_, _, carrier)) ->
              unify ctx fieldType carrier
          let carriersMatch = and carrierMatches
          if not carriersMatch
            then put beforeAlignment >> pure Nothing
            else do
              let bindings =
                    [ DerivedEqEvidenceBinding
                        (evidenceName constructor fieldIndex ordinal)
                        dictionary
                        dictionaryType
                    | ( ordinal
                      , ( (constructor, fieldIndex, _)
                        , (dictionary, dictionaryType, _)
                        )
                      ) <- zip [0 :: Int ..] aligned
                    ]
                  namesByField =
                    Map.fromList
                      [ ( constructor
                        , [ if dnfQuantity field == Q0
                              then Nothing
                              else
                                Just
                                  ( evidenceName
                                      constructor
                                      fieldIndex
                                      (runtimeOrdinal constructor fieldIndex)
                                  )
                          | (fieldIndex, field) <- zip [0 :: Int ..] fields
                          ]
                        )
                      | (constructor, fields) <- shape
                      ]
              pure (Just (bindings, namesByField))
  where
    rawCandidates =
      foldTermWithDepth collect 0 comparator

    collect depth node =
      case selectedEqOperation node of
        Nothing -> []
        Just (_, _, dictionaries) ->
          [ (depth, dictionary)
          | (_, dictionary) <- dictionaries
          ]

    runtimeFieldTerms =
      [ (constructor, fieldIndex, dnfTypeTerm field)
      | (constructor, fields) <- shape
      , (fieldIndex, field) <- zip [0 :: Int ..] fields
      , dnfQuantity field /= Q0
      ]

    authenticate dictionary
      | not (termScopedAt (ctxLen ctx) dictionary) = pure Nothing
      | otherwise =
          coreTermClassifierInCtx ctx dictionary >>= \case
            Nothing -> pure Nothing
            Just dictionaryType -> do
              state <- get
              forceM dictionaryType >>= \case
                VGlobI trait _ arguments
                  | trait == gPrel "Eq"
                  , Just [(_, carrier)] <-
                      traitSemanticSpineIn state trait arguments ->
                      pure (Just (dictionary, dictionaryType, carrier))
                _ -> pure Nothing

    evidenceName constructor fieldIndex ordinal =
      Name
        ( "__derive_eq_evidence_"
            <> gnameText constructor
            <> "_"
            <> T.pack (show fieldIndex)
            <> "_"
            <> T.pack (show ordinal)
        )
        site

    runtimeOrdinal targetConstructor targetFieldIndex =
      fromMaybe 0
        ( List.findIndex
            (\(constructor, fieldIndex, _) ->
               constructor == targetConstructor
                 && fieldIndex == targetFieldIndex)
            runtimeFieldTerms
        )

-- | Find the checked equation providers reached directly or transitively by
-- a custom equality comparator, and independently certify their ordinary
-- termination before a derivation may inspect those equations.  The result
-- is keyed entirely by resolved globals and Core dependencies.  A missing
-- body, an incomplete SCC, or an unverified decrease rejects the provider.
checkedFunctionalEqualityHelpers :: Term -> CheckM [GName]
checkedFunctionalEqualityHelpers comparator = do
  baseline <- get
  let declarations = csTerminationDecls baseline
      declarationNames = Map.keysSet declarations
      roots = Set.intersection declarationNames (globalsOfTerm comparator)
      reachable = closeReachable declarations roots
      selected = Map.restrictKeys declarations reachable
      dependencies declaration =
        Set.toList
          ( Set.intersection
              reachable
              (globalsOfTerm (tdCoreBody declaration))
          )
      components =
        stronglyConnComp
          [ (declaration, identity, dependencies declaration)
          | (identity, declaration) <- Map.toAscList selected
          ]
      members = \case
        AcyclicSCC declaration -> [declaration]
        CyclicSCC group -> group
  result <- certify [] (map members components)
  put baseline
  pure result
  where
    closeReachable declarations = go Set.empty . Set.toAscList
      where
        go reached [] = reached
        go reached (identity : pending)
          | Set.member identity reached = go reached pending
          | otherwise =
              let discovered =
                    maybe
                      []
                      ( Set.toAscList
                          . Set.intersection (Map.keysSet declarations)
                          . globalsOfTerm
                          . tdCoreBody
                      )
                      (Map.lookup identity declarations)
               in go (Set.insert identity reached) (discovered ++ pending)

    certify accepted [] = pure (reverse accepted)
    certify accepted (group : groups)
      | null group = certify accepted groups
      | otherwise = do
          let identities = map tdName group
          outcome <-
            withTemporaryReducibleGlobals accepted $
              withSccOpaque identities $
                verifyTerminationSccIn emptyCtx group
          if outcome == TerminationConversionSafe
            then certify (reverse identities ++ accepted) groups
            else pure []

checkedFunctionalEqualityPlan
  :: Ctx
  -> Span
  -> Term
  -> [GName]
  -> CheckM (Maybe DerivedFunctionalEquality)
checkedFunctionalEqualityPlan ctx site comparator certified = do
  plans <- catMaybes <$> mapM planFor occurrences
  pure $ case plans of
    [plan] -> Just plan
    _ -> Nothing
  where
    certifiedSet = Set.fromList certified
    occurrences =
      nub
        [ (identity, universes)
        | (_, CGlobal identity universes) <- foldTermWithDepth (\depth term -> [(depth, term)]) 0 comparator
        , Set.member identity certifiedSet
        ]

    planFor (identity, universes) = do
      let helperTerm = CGlobal identity universes
      coreTermClassifierInCtx ctx helperTerm >>= \case
        Nothing -> pure Nothing
        Just helperType ->
          binaryBooleanDomain helperType >>= \case
            Nothing -> pure Nothing
            Just domain -> do
              domainTerm <- quoteIn ctx domain
              case delaborateType ctx site domainTerm of
                Nothing -> pure Nothing
                Just domainExpr -> do
                  (shape, _) <- deriveNominalShape ctx site domainTerm
                  methods <- derivedRecursiveFieldMethods ctx domain shape
                  let hasRecursive =
                        any
                          (any (== DerivedEqFieldRecursive))
                          (Map.elems methods)
                  if null shape || not hasRecursive
                    then pure Nothing
                    else
                      pure
                        ( Just
                            DerivedFunctionalEquality
                              { dfeIdentity = identity
                              , dfeBindingName = Name "__derive_functional_comparator" site
                              , dfeTerm = helperTerm
                              , dfeType = helperType
                              , dfeDomain = domain
                              , dfeDomainExpr = domainExpr
                              , dfeShape = shape
                              , dfeMethods = methods
                              }
                        )

    binaryBooleanDomain helperType =
      forceM helperType >>= \case
        VPiM _ Expl _ _ _ firstDomain firstClosure -> do
          secondType <- clApp firstClosure (VRigid (ctxLen ctx) [])
          forceM secondType >>= \case
            VPiM _ Expl _ _ _ _ secondClosure -> do
              resultType <- clApp secondClosure (VRigid (ctxLen ctx + 1) [])
              forceM resultType >>= \case
                VGlobI boolean _ arguments
                  | boolean == prelBool
                  , null arguments -> pure (Just firstDomain)
                _ -> pure Nothing
            _ -> pure Nothing
        _ -> pure Nothing

derivedRecursiveFieldMethods
  :: Ctx
  -> Value
  -> DerivedNominalShape
  -> CheckM DerivedEqFieldMethods
derivedRecursiveFieldMethods ctx recursiveDomain shape =
  Map.fromList <$> mapM constructorMethods shape
  where
    constructorMethods (constructor, fields) =
      (constructor,) <$> mapM fieldMethod fields

    fieldMethod field
      | dnfQuantity field == Q0 =
          pure (DerivedEqFieldEvidence Nothing)
      | otherwise = do
          fieldType <- evalIn ctx (dnfTypeTerm field)
          baseline <- get
          recursive <- unify ctx fieldType recursiveDomain
          put baseline
          pure
            ( if recursive
                then DerivedEqFieldRecursive
                else DerivedEqFieldEvidence Nothing
            )

validateDerivedDeclarations :: Span -> [Decl] -> CheckM Bool
validateDerivedDeclarations _ [] = pure False
validateDerivedDeclarations sourceSpan generated = do
  results <- forM generated $ \case
    -- Generic declaration-level derive is validated by the same typed facet
    -- planner as source @instance G = derive@. The structural checks below
    -- apply only to specialized generators that emit an explicit body.
    DInstance (InstanceDecl _ _ _ InstanceDerive) _ -> pure True
    DInstance (InstanceDecl _ _ headExpression (InstanceMembers _)) _ ->
      validateHead headExpression
    _ -> pure False
  let valid = and results
  unless valid $
    errAt sourceSpan "E_DERIVE_UNSUPPORTED" (Just "kappa.derive")
      "the requested derivation is outside the checked conservative structural fragment (§14.5.1-§14.5.2)"
  pure valid
  where
    validateHead headExpression = do
      (traitIdentity, _, arguments) <- instSplitHead headExpression
      case (traitIdentity, arguments) of
        (Just trait, [target])
          | trait == gPrel "IsSet" -> validateStructuralDerive (gPrel "IsSet") target
          | trait == gPrel "Eq" -> validateStructuralDerive (gPrel "Eq") target
          | trait == gPrel "ExactNaturalRepresentation" -> validateExactNaturalDerive target
          | trait == gPrel "RefinementView" -> validateRefinementViewDerive target
        _ -> pure False

validateStructuralDerive :: GName -> Expr -> CheckM Bool
validateStructuralDerive fieldTrait target = do
  targetTerm <- fst <$> inferType emptyCtx target
  targetTerm' <- zonkTermM 0 targetTerm
  state <- get
  case nominalDataHead targetTerm' >>= \dataName -> (dataName,) <$> Map.lookup dataName (csDatas state) of
    Nothing -> pure False
    Just (dataName, info) ->
      and <$> mapM (constructorEligible dataName) (diCtors info)
  where
    constructorEligible dataName constructor = do
      state <- get
      case Map.lookup constructor (csCtors state) of
        Nothing -> pure False
        Just info ->
          and <$> mapM (fieldEligible dataName) (constructorFieldBinders info)
    fieldEligible dataName (quantity, fieldType)
      | nominalDataHead fieldType == Just dataName = pure True
      | maxFreeIndexTerm fieldType >= 0 = pure False
      | otherwise = do
          fieldValue <- evalIn emptyCtx fieldType
          let requiredTrait = if quantity == Q0 then gPrel "IsProp" else fieldTrait
          goal <- globalValueM requiredTrait [(Expl, fieldValue)]
          derivationProbe emptyCtx (exprSpan target) goal

-- | Ask the unified derivation engine whether a closed structural obligation
-- is solvable without committing speculative metas, caches, expansions, or
-- diagnostics.  Declaration eligibility and expression-level @derive@ must
-- share one proof authority; otherwise a field can be accepted by one path
-- and rejected by the other.  A failed or diagnostic-producing search is an
-- ordinary conservative rejection.
derivationProbe :: Ctx -> Span -> Value -> CheckM Bool
derivationProbe ctx site goal = do
  baseline <- get
  diagnosticCount <- gets (length . csDiags)
  _ <- synthesizeDerivationWithFuel 24 ctx site goal
  diagnostics <- gets csDiags
  let solved = length diagnostics == diagnosticCount
  put baseline
  pure solved

validateExactNaturalDerive :: Expr -> CheckM Bool
validateExactNaturalDerive target = do
  targetTerm <- fst <$> inferType emptyCtx target
  state <- get
  case nominalDataHead targetTerm >>= \dataName -> (dataName,) <$> Map.lookup dataName (csDatas state) of
    Nothing -> pure False
    Just (dataName, info) -> do
      let runtimeFields constructor =
            [ fieldType
            | (quantity, fieldType) <-
                maybe [] constructorFieldBinders (Map.lookup constructor (csCtors state))
            , quantity /= Q0
            ]
          fields = map runtimeFields (diCtors info)
          zeroCount = length [() | [] <- fields]
          successorCount =
            length
              [ ()
              | [fieldType] <- fields
              , nominalDataHead fieldType == Just dataName
              ]
      pure (length fields == 2 && zeroCount == 1 && successorCount == 1)

validateRefinementViewDerive :: Expr -> CheckM Bool
validateRefinementViewDerive target = do
  targetTerm0 <- fst <$> inferType emptyCtx target
  targetTerm <- zonkTermM 0 targetTerm0
  isJust <$> deriveRefinementViewShape (exprSpan target) target targetTerm

compilerOwnedTypeLevelInstance :: InstanceDecl -> CheckM Bool
compilerOwnedTypeLevelInstance (InstanceDecl _ premises hd _) = do
  currentModule <- gets csModule
  (traitG, _, args) <- instSplitHead hd
  if currentModule /= modTypeLevel
      || not (null premises)
      || traitG `notElem` map Just compilerOwnedTypeLevelTraits
    then pure False
    else case args of
      [arg] -> do
        (argTm, _) <- inferType emptyCtx arg
        pure (argTm == CGlob prelTypeLevel)
      _ -> pure False

instanceHeadPass :: Decl -> CheckM ()
instanceHeadPass declaration =
  withDeclarationUniverseSchema declaration (instanceHeadPassRaw declaration)

instanceHeadPassRaw :: Decl -> CheckM ()
instanceHeadPassRaw = \case
  DInstance (InstanceDecl _ premises hd _) sp -> do
    already <- gets (Map.member sp . csPreInstances)
    unless already $ do
      mpi <- registerInstanceHead premises hd sp
      modify' $ \st -> st {csPreInstances = Map.insert sp mpi (csPreInstances st)}
  _ -> pure ()

-- | Elaborate an instance head and register the dictionary global
-- (type only — 'elabInstance' fills the value) and the instance-set
-- entry consulted by §14.3.1 search.
registerInstanceHead :: [Expr] -> Expr -> Span -> CheckM (Maybe PreInstance)
registerInstanceHead premises hd sp = do
  (traitIdentity, _, _) <- instSplitHead hd
  dictName <-
    stableGeneratedNameAt
      "instance-dictionary"
      (maybe "invalid" gnameText traitIdentity)
      sp
  dictG <- gets (\state -> GName (csModule state) dictName)
  withActiveUniverseDefinition dictG (registerInstanceHeadAs dictG premises hd sp)

registerInstanceHeadAs :: GName -> [Expr] -> Expr -> Span -> CheckM (Maybe PreInstance)
registerInstanceHeadAs dictG premises hd sp = do
  -- head must be Trait args...
  (traitG, explicitUniverseArguments, argEs) <- instSplitHead hd
  st <- get
  case traitG >>= \g -> g <$ Map.lookup g (csTraits st) of
    Nothing -> do
      errAt sp "E_INSTANCE_HEAD" (Just "kappa-hs.trait.bad-instance-head")
        "instance head must be a trait applied to type arguments"
      pure Nothing
    Just g
      | csModule st /= preludeModule
      , g `Set.member` intrinsicUniverseTraits -> do
          errAt sp "E_UNIVERSE_LEVEL_EXPRESSION"
            (Just "kappa.universe.level-expression")
            ( "instances for intrinsic trait '" <> gnameText g
                <> "' are compiler-owned and cannot be declared in source (§11.1.4)"
            )
          pure Nothing
    Just g -> do
      -- Instance-head variables are the unresolved identifier leaves of the
      -- normalized head/premises. This includes the spec's conventional
      -- uppercase parametric names (`instance BadReflect A`) while resolved
      -- constructors and trait heads remain globals, never binders.
      fvs <- instanceFreeVars (hd : premises)
      compilerGeneratedDerive <-
        gets
          ( any
              (any (generatedInstanceAt sp))
              . Map.elems
              . csDerivedDecls
          )
      -- §14.3.5 instance-search termination (Paterson-style): every premise
      -- must be structurally smaller than the head, so resolution cannot
      -- loop. A premise is rejected if its constructor-and-variable size is
      -- not strictly smaller than the head's, or if it uses some type
      -- variable more often than the head does. Rejecting at declaration
      -- time keeps a circular instance (e.g. `Container f => Container f`,
      -- or `(C f, C f, C f) => C f`) out of the search set entirely — the
      -- depth backstop alone does not stop the exponential breadth.
      let headOccs = constraintIdOccs hd
          headSize = length headOccs
          headName = constraintHead hd
          occCount xs v = length (filter (== v) xs)
          patersonViolation p =
            let pOccs = constraintIdOccs p
                -- the strict-size condition (§14.3.5) bites only for a
                -- premise on the SAME trait as the head — that is the
                -- self-recursive case that can loop. A cross-trait bridge
                -- (e.g. the prelude's `Eq a => Equiv a`) is well-founded
                -- even at equal size, so only the variable-occurrence
                -- condition applies there.
                sameTrait = constraintHead p == headName
             in ( sameTrait
                    && not compilerGeneratedDerive
                    && length pOccs >= headSize
                )
                  || any (\v -> occCount pOccs v > occCount headOccs v) fvs
      if any patersonViolation premises
        then do
          errAt sp "E_INSTANCE_SEARCH_NONTERMINATING" (Just "kappa.termination.failure")
            ( "instance for trait '" <> gnameText g
                <> "' has a premise that is not structurally smaller than the head, "
                <> "so instance search may not terminate; every premise must be strictly "
                <> "smaller than the head and use no type variable more often than the head (§14.3.5)"
            )
          pure Nothing
        else patersonOk explicitUniverseArguments g argEs
  where
    generatedInstanceAt wanted = \case
      DInstance _ generatedSpan -> generatedSpan == wanted
      _ -> False

    patersonOk explicitUniverseArguments g argEs = do
      fvs <- instanceFreeVars (hd : premises)
      -- Infer each implicitly-universalized head variable's domain from the
      -- whole premise/head use, rather than fixing it to Type0. The
      -- provisional parametric contract is finalized below once the trait
      -- head has constrained these metas.
      fvTele0 <- forM fvs $ \v -> do
        kind <- freshMeta
        -- The domain meta has not yet established whether this is a kind
        -- parameter or an ordinary first-class value (for example the fixed
        -- TypeLevel in a parameterized Monotone instance).  Header checking is
        -- type-position-only, so start with ordinary observation and let
        -- 'finalizeGeneratedTelescope' install the erased parametric contract
        -- exactly when the inferred domain is a parametric kind.  Starting at
        -- Parametric here rejects an ordinary value while its own head is
        -- constraining the domain, before finalization can correct the mode.
        pure (TelescopeEntry Impl Ordinary FormationOrdinary QW False v kind Nothing)
      -- Implicitly-universalized head variables are not evidence premises.
      -- Keeping them out of local candidate search while their domain metas
      -- are being constrained prevents a value variable from solving itself
      -- to a trait dictionary (for example @k@ in @Monotone (add k)@).
      -- The finalized telescope remains implicit; only explicit instance
      -- premises become candidates through 'instBindPremises'.
      ctx0 <- foldM bindHeadVariable emptyCtx fvTele0
      premTms <- forM premises $ \p -> fst <$> inferType ctx0 p
      ctxP' <- instBindPremises ctx0 premTms
      -- head arguments check against the trait constructor's parameter
      -- types (so type constructors are valid arguments of
      -- higher-kinded traits, §14.1.2)
      traitDefinition <- gets (Map.lookup g . csGlobals)
      (traitHead, traitUniverses, checkedArguments) <- case traitDefinition of
        Just definition -> do
          (headTerm, traitTy, universes) <- case explicitUniverseArguments of
            Nothing -> instantiateGlobal g definition
            Just levelExpressions -> do
              supplied <- mapM (fmap snd . elabLevelExpr emptyCtx) levelExpressions
              let expected = dutParameterCount (gdUniverses definition)
                  found = length supplied
              when (expected /= found) $
                errAt sp "E_UNIVERSE_SCHEMA_ARITY_MISMATCH" (Just "kappa.universe.schema-arity")
                  ( "declaration '" <> gnameText g <> "' expects " <> T.pack (show expected)
                      <> " universe arguments, but this instantiation supplies " <> T.pack (show found)
                  )
              let actual = take expected (supplied ++ repeat LZero)
              (term, ty) <- specializeGlobalAt emptyCtx g definition actual
              pure (term, ty, actual)
          checkedArguments <- instCheckHeadArgs ctxP' traitTy argEs
          pure (headTerm, universes, checkedArguments)
        Nothing -> do
          checkedArguments <-
            forM argEs $ \argument -> do
              (term, _level) <- inferType ctxP' argument
              pure (term, Set.empty)
          pure (CGlob g, [], checkedArguments)
      fvTele <- finalizeGeneratedTelescope emptyCtx fvTele0
      let headClassifierLevels = Set.unions (map snd checkedArguments)
      let teleLen = length fvTele + length premises
          argTms = map fst checkedArguments
      register
        g
        traitHead
        traitUniverses
        fvTele
        premTms
        argTms
        headClassifierLevels
        teleLen
      where
        bindHeadVariable context entry = do
          domain <- evalIn context (teDomain entry)
          withBound <- extendLevelAssumption noSpan context (teLevelAssumption entry)
          pure
            ( bindCtxMQB
                (teMode entry)
                (teQ entry)
                (teName entry)
                False
                (teBorrow entry)
                domain
                withBound
            )
    register g traitHead traitUniverses fvTele premTms argTms headClassifierLevels teleLen = do
      -- register the instance before checking members so member bodies
      -- can use the instance being defined (recursive instances, §14.3)
      (dictTyTerm0, _) <- instDictTy fvTele premTms traitHead argTms
      instantiationLevels <- gets csLevelInstantiationMetas
      let binderSourceLevels =
            Set.fromList
              [ meta
              | entry <- fvTele
              , meta <-
                  levelMetasOfTerm (teDomain entry)
                    ++ maybe [] (\(lower, upper) -> levelMetas lower ++ levelMetas upper)
                         (teLevelAssumption entry)
              ]
          sourceLevels =
            binderSourceLevels
              `Set.union` Set.unions
                (map schemaBearingLevelMetas (premTms ++ argTms))
          -- An ordinary declaration occurrence is minimized before the
          -- generated dictionary is published. A trait parameter instantiated
          -- by a generated head binder is different: its checked classifier
          -- is part of the instance head's public contract. This covers both
          -- @instance C a@ and higher-kinded heads such as
          -- @Applicative (IO e)@.
          -- A generated free-variable binder is itself declaration syntax:
          -- every level in its inferred domain belongs to the dictionary
          -- schema even when unification also records that identity as an
          -- occurrence meta.  Provenance sets cease to be disjoint after
          -- unification, so subtracting all occurrence identities here made
          -- @instance C a@ spuriously monomorphic at Type0.  Occurrence-only
          -- levels in the premise/head remain minimizable.  A first-order
          -- head such as @Eq TypeLevel@ has no generated binder level and
          -- therefore still retains its principal Type0 specialization.
          protectedSourceLevels =
            Set.unions
              [ binderSourceLevels
              , Set.difference sourceLevels instantiationLevels
              , headClassifierLevels
              ]
      dictTyTerm <-
        principalizeGeneratedInterfaceOccurrences
          dictG
          protectedSourceLevels
          dictTyTerm0
      dictTy <- evalIn emptyCtx dictTyTerm
      -- §11.1.2.3A/§14.3: principal occurrence choices have been removed
      -- above.  The remaining normalized head and premises are the generated
      -- declaration's user-observable schema boundary. Generated declarations
      -- do not acquire source provenance merely because an omitted global
      -- occurrence appears in a Pi domain: only the binder/interface levels
      -- authenticated above are schema parameters. The ordinary structural
      -- marker would promote the trait occurrence itself and publish
      -- @u <= v@ instead of selecting its principal least value @v = u@.
      forM_ (Set.toAscList protectedSourceLevels) $ \meta ->
        markGeneralizableLevelTermFor dictG (CSort (LMeta meta))
      schemaCount <- gets (Map.size . csActiveUniverseSchema)
      let schema = DeclarationUniverseTelescope schemaCount (schemaCount > 0)
      addGlobal dictG
        ( globalDefWithCoreType dictTyTerm
            (globalDefWithUniverses schema (GlobalDef dictTy Nothing False))
        )
      modify' $ \s ->
        invalidateSemanticCaches
          ( setCheckInstances
              ( InstanceEntry
                  g
                  traitUniverses
                  schema
                  teleLen
                  (map (shiftTerm (length premises) 0) premTms)
                  argTms
                  dictG
                  : csInstances s
              )
              s
          )
      pure (Just (PreInstance g fvTele premTms argTms dictG))

-- | Check an instance head against its owning trait telescope and retain only
-- authenticated source-owned classifier levels. Generated dictionary
-- principalization may preserve those identities, but never fresh occurrence
-- metas allocated by the observational inference probe.
instCheckHeadArgs :: Ctx -> Value -> [Expr] -> CheckM [(Term, Set LevelMeta)]
instCheckHeadArgs _ _ [] = pure []
instCheckHeadArgs ctx ty (e : es) = do
  t <- forceM ty
  case t of
    VPiRuntimeM mode _ Expl q borrowed _ _ _ runtimeErasure dom clo -> do
      -- Trait heads are type-position syntax (§14.3.1A). A parametric type
      -- witness may therefore instantiate a universe-classified trait
      -- parameter even when the dictionary's parameter quantity is not Q0;
      -- this does not expose the witness as an ordinary term value.
      domF <- forceM dom
      (tm, classifierLevels) <- case domF of
        VPiEvidenceM {} -> inferExactExplicitArg ctx mode q borrowed runtimeErasure e dom
        _ -> do
          checked <- checkExplicitArg ctx mode q borrowed runtimeErasure e dom
          pure (checked, Set.empty)
      v <- evalIn ctx tm
      rest <- clApp clo v >>= \cod -> instCheckHeadArgs ctx cod es
      pure ((tm, classifierLevels) : rest)
    _ -> do
      (tm, _classifierLevel) <- inferType ctx e
      rest <- instCheckHeadArgs ctx t es
      pure ((tm, Set.empty) : rest)

elabInstance :: InstanceDecl -> Span -> CheckM ()
elabInstance (InstanceDecl _ premises hd completion) sp = do
  let (wholeDerived, members) = case completion of
        InstanceMembers explicitMembers -> (False, explicitMembers)
        InstanceDerive -> (True, [])
  flushPending
  stash <- gets (Map.lookup sp . csPreInstances)
  mpi <- case stash of
    -- head already elaborated (or already rejected) by the pre-pass
    Just mpi -> pure mpi
    Nothing -> registerInstanceHead premises hd sp
  mpti <- case mpi of
    Nothing -> pure Nothing
    Just pinst -> gets (fmap ((,) pinst) . Map.lookup (piTrait pinst) . csTraits)
  forM_ mpti $ \(pinst, ti) -> do
    let g = piTrait pinst
        fvTele = piFvTele pinst
        premTms = piPremTms pinst
        argTms = piArgTms pinst
        dictG = piDictG pinst
    traitUniverses <-
      instanceDictionaryTraitUniverses sp dictG g
    diagnosticsBeforeBody <- gets (length . csDiags)
    withActiveUniverseDefinition dictG $ do
      ctx0 <- teleCtx fvTele
      ctxP' <- instBindPremises ctx0 premTms
      -- §14.1.4/§14.3.3: every supertrait premise of the trait must be
      -- satisfiable at the instance head (from the instance's own
      -- premises — including their transitive supertrait conformance
      -- paths — or the global instance set); the evidence found is
      -- stored in the dictionary's supertrait field
      superFields <- forM (tiSupers ti) $ \(fn, supClosed) -> do
        ec <- ec_
        argVs <- mapM (evalIn ctxP') argTms
        specializedSuper <- specializeDeclarationComponent g traitUniverses supClosed
        supF <- evalIn ctxP' specializedSuper
        supGoal <- forceM (evalApp ec supF [(Expl, a) | a <- argVs])
        mEv <- traitEvidence ctxP' sp supGoal
        case mEv of
          Just tm -> pure (Just (fn, tm))
          Nothing
            | wholeDerived || fn `Set.member` tiDerivedSupers ti -> pure Nothing
            | otherwise -> do
                gT <- quoteIn ctxP' supGoal
                errAt sp "E_DERIVE_SUPERTRAIT_UNSOLVED" (Just "kappa.derive")
                  ("instance does not satisfy the supertrait premise '" <> renderTerm gT <> "' of trait '" <> gnameText g <> "' (§14.1.4)")
                pure Nothing
      -- member definitions checked against member types, in declaration
      -- order; already-checked members (associated static members in
      -- particular) instantiate the dict binder of later member types
      -- (§14.3.4)
      let goFields done terminations [] =
            pure (reverse done, reverse terminations)
          goFields done terminations (mn : rest) = do
            let memberMode = Map.findWithDefault Ordinary mn (tiMemberModes ti)
            mfield <- case findMember mn members of
              Just (LetDef _ _ _ _ _ mbinders mResTy mdec mbody, msp) -> do
                memberTyV <-
                  memberSigInstance
                    g
                    traitUniverses
                    mn
                    argTms
                    ctxP'
                    (catMaybes superFields ++ reverse done)
                checked <-
                  checkInstanceMember
                    g
                    traitUniverses
                    ti
                    argTms
                    ctxP'
                    (catMaybes superFields)
                    (reverse done)
                    memberMode
                    memberTyV
                    mbinders
                    mResTy
                    mbody
                    msp
                let (tm, terminationBody) = checked
                pure
                  ( Just
                      ( (mn, tm)
                      , InstanceMemberTermination
                          mn
                          memberTyV
                          mbinders
                          mdec
                          terminationBody
                          msp
                      )
                  )
              Nothing -> case Map.lookup mn (tiDefaults ti) of
                -- The trait's source-free checked template fills the member
                -- (§14.2).  Its interface is the member accessor interface, so
                -- specialization uses the selected trait universes and the
                -- partial dictionary assembled at this exact completion point.
                Just defaultGlobal -> do
                  (tm, instantiatedType, memberTyV) <-
                    instantiateCheckedTraitDefault
                      ctxP'
                      sp
                      g
                      traitUniverses
                      mn
                      argTms
                      (catMaybes superFields ++ reverse done)
                      defaultGlobal
                  -- The checked default and accessor share one declaration-
                  -- universe occurrence. The accessor is the authoritative
                  -- member interface, so a second independently freshened
                  -- member occurrence would only introduce a spurious equality
                  -- component at dictionary completion.
                  expectType ctxP' sp instantiatedType memberTyV
                  pure
                    ( Just
                        ( (mn, tm)
                        , InstanceMemberTermination
                            mn
                            memberTyV
                            []
                            Nothing
                            tm
                            sp
                        )
                    )
                Nothing -> do
                  memberTyV <-
                    memberSigInstance
                      g
                      traitUniverses
                      mn
                      argTms
                      ctxP'
                      (catMaybes superFields ++ reverse done)
                  let declaredDerived =
                        wholeDerived || mn `Set.member` tiDerivedMembers ti
                  structural <-
                    if declaredDerived
                      then
                        deriveStructuralInstanceMember
                          g
                          dictG
                          traitUniverses
                          ti
                          argTms
                          ctxP'
                          (catMaybes superFields)
                          (reverse done)
                          memberMode
                          mn
                          memberTyV
                          sp
                      else pure Nothing
                  completed <- case structural of
                    Just result -> pure (Just result)
                    Nothing ->
                      completeOmittedMember
                        declaredDerived
                        mn
                        g
                        traitUniverses
                        ti
                        argTms
                        ctxP'
                        (catMaybes superFields)
                        (reverse done)
                        memberTyV
                        sp
                        >>= \case
                          Just proof -> pure (Just (proof, proof))
                          Nothing -> pure Nothing
                  case completed of
                      Just (proof, terminationBody) ->
                        pure
                          ( Just
                              ( (mn, proof)
                              , InstanceMemberTermination
                                  mn
                                  memberTyV
                                  []
                                  Nothing
                                  terminationBody
                                  sp
                              )
                          )
                      Nothing -> do
                        unless declaredDerived $
                          errAt sp "E_DERIVE_MEMBER_MISSING" (Just "kappa.derive")
                            ("instance does not define member '" <> mn <> "'")
                        pure Nothing
            case mfield of
              Nothing -> goFields done terminations rest
              Just (field, termination) ->
                goFields (field : done) (termination : terminations) rest
      (dictFields, memberTerminations) <- goFields [] [] (tiMembers ti)
      -- Derived supertraits are facets of the completed dictionary, not
      -- prerequisites for checking unrelated explicit/derived members. Retry
      -- unresolved derived slots with the completed member dictionary exposed
      -- as an ordinary implicit candidate. The resulting proof is then
      -- substituted with the checked record value; no incomplete evidence
      -- escapes this local derivation scope (§14.3.4A).
      completedDerivedSupers <-
        fmap catMaybes . forM (tiSupers ti) $ \(fn, supClosed) ->
          if not wholeDerived && fn `Set.notMember` tiDerivedSupers ti
              || isJust (lookup fn (catMaybes superFields))
            then pure Nothing
            else do
              ec <- ec_
              argVs <- mapM (evalIn ctxP') argTms
              specializedSuper <- specializeDeclarationComponent g traitUniverses supClosed
              supFunction <- evalIn ctxP' specializedSuper
              supGoal <- forceM (evalApp ec supFunction [(Expl, argument) | argument <- argVs])
              let selfTerm = foldl (CApp Expl) (CGlobal g traitUniverses) argTms
              selfGoal <- evalIn ctxP' selfTerm
              let selfCtx = bindCtxMQ Ordinary QW "__derived_self" True selfGoal ctxP'
                  partialDictionary =
                    CRecordV
                      ( sortOn fst
                          (catMaybes superFields ++ dictFields)
                      )
              baseline <- get
              modify' $ \state ->
                state
                  { csBlockedSupertraitProjections =
                      Set.insert (g, fn) (csBlockedSupertraitProjections state)
                  }
              proof <- synthesizeDerivation selfCtx sp supGoal
              modify' $ \state ->
                state
                  { csBlockedSupertraitProjections =
                      Set.delete (g, fn) (csBlockedSupertraitProjections state)
                  }
              diagnostics <- gets csDiags
              if length diagnostics == length (csDiags baseline)
                then
                  pure
                    ( Just
                        ( fn
                        , substTopTermAt 0 partialDictionary proof
                        )
                    )
                else pure Nothing
      let allSuperFields = catMaybes superFields ++ completedDerivedSupers
      -- §14.3.4: an instance member the trait does not declare is
      -- undeclared — an associated static member must be declared in the
      -- trait body before an instance may define it.
      forM_ [(nameText dn, dsp) | DLet _ (LetDef (Just dn) _ _ _ _ _ _ _ _) dsp <- members] $ \(inm, dsp) ->
        unless (inm `elem` tiMembers ti) $
          errAt dsp "E_ASSOCIATED_MEMBER_UNDECLARED" (Just "kappa.associated.member-undeclared")
            ( "instance defines '" <> inm <> "', which trait '" <> gnameText g
                <> "' does not declare; an associated static member must first be declared in the trait body (§14.3.4)"
            )
      flushPending
      settleActiveUniverseRequirements
      checkInstanceMemberTerminationSccs ctxP' g dictG memberTerminations
      let fields = sortOn fst (allSuperFields ++ dictFields)
          dictBody = CRecordV fields
          -- order: fvs outermost, then premises
          wrapped =
            foldr
              (\entry acc -> CLamM (teMode entry) (teIcit entry) (teQ entry) (teName entry) acc)
              (foldr (\_ acc -> CLamM Ordinary Impl QW "__p" acc) dictBody premises)
              fvTele
      dictType <- gets (maybe (VSort LZero) gdType . Map.lookup dictG . csGlobals)
      wrapped0 <- principalizeBodyUniverseInstantiations dictG dictType wrapped
      settleActiveUniverseRequirements
      wrapped' <- zonkTermM 0 wrapped0
      dictV <- evalIn emptyCtx wrapped'
      dictDef <- gets (Map.lookup dictG . csGlobals)
      addGlobal dictG $
        case dictDef of
          Just definition -> definition {gdValue = Just dictV, gdReducible = True}
          Nothing -> GlobalDef (VSort LZero) (Just dictV) True
      -- §14.1.1: trait evidence lowers to a runtime record of the member
      -- implementations; capture its KCore body for the native backend.
      recordCoreBody dictG wrapped'
      -- §14.3/§33.2.1: program-level coherence is a declaration-level
      -- validity condition. Member checking must run first because structural
      -- coherence compares completed evidence artifacts. A body-invalid,
      -- non-overlapping artifact is unpublished so recovery cannot poison
      -- later instance bodies. An overlapping artifact is still judged:
      -- generated-law recovery errors are replaced by the coherence root, and
      -- a body-valid incoherent artifact remains visible to resolution so an
      -- attempted selection also reports the non-deferrable use-site error
      -- required by §3.1.15.
      stPost <- get
      let diagnosticsAfterBody = length (csDiags stPost)
          bodyDiagnosticCount =
            max 0 (diagnosticsAfterBody - diagnosticsBeforeBody)
          bodyHasErrors =
            any isError (take bodyDiagnosticCount (csDiags stPost))
          unpublishInvalid state =
            invalidateSemanticCaches
              ( setCheckInstances
                  (filter ((/= dictG) . ieDict) (csInstances state))
                  state
              )
      case dropWhile ((/= dictG) . ieDict) (csInstances stPost) of
        (newIe : priors) -> do
          let sameTraitPriors = [ie | ie <- priors, ieTrait ie == g]
          incoherentPriors <-
            filterM (instanceOverlapIsIncoherent newIe) sameTraitPriors
          case incoherentPriors of
            [] -> when bodyHasErrors (modify' unpublishInvalid)
            _ -> do
              priorSites <- mapM (instanceDeclSite . ieDict) incoherentPriors
              modify' $ \state ->
                let withoutRecoveryDiagnostics =
                      state {csDiags = drop bodyDiagnosticCount (csDiags state)}
                 in if bodyHasErrors
                      then unpublishInvalid withoutRecoveryDiagnostics
                      else withoutRecoveryDiagnostics
              let relateds =
                    related RoleInstanceDeclarationSite sp "this overlapping instance"
                      : [ related RoleInstanceDeclarationSite priorSite
                            "conflicts with this instance"
                        | Just priorSite <- priorSites
                        ]
              report $
                withRelateds relateds $
                  diag SevError StageElaborate "E_INSTANCE_INCOHERENT"
                    (Just "kappa-hs.trait.incoherent") sp
                    ( "overlapping instances of trait '" <> gnameText g
                        <> "' are not equivalent implementations (§14.3, §33.2.1 coherence)"
                    )
        [] -> pure ()
      settleActiveUniverseRequirements
  where
    findMember mn ms =
      case [ (ld, dsp) | DLet _ ld@(LetDef (Just dn) _ _ _ _ _ _ _ _) dsp <- ms, nameText dn == mn
           ] of
        (x : _) -> Just x
        [] -> Nothing

    checkInstanceMemberTerminationSccs ambient trait dictionary terminations = do
      state <- get
      let identities =
            Map.fromList
              [ (imtName termination, memberIdentity (imtName termination))
              | termination <- terminations
              ]
          shapeValidatedAccessors =
            Map.fromList
              [ (global, accessor)
              | (global, definition) <- Map.toList (csGlobals state)
              , Just body <- [gdCoreBody definition]
              , Just accessor@(member, _, _) <- [projectionAccessor body]
              , Map.member member identities
              ]
          authenticatedAccessors =
            Map.fromList
              ( [ (global, member)
                | (global, (owner, member)) <-
                    Map.toList (csBareTraitMembers state)
                , owner == trait
                , Map.member member identities
                ]
                  ++ [ (global, member)
                     | member <- Map.keys identities
                     , let global = memberGlobal trait member
                     , Map.lookup global (csTraitMemberOwners state) == Just trait
                     ]
              )
          memberIdentity member =
            case dictionary of
              GName owner dictionaryName ->
                GName owner (dictionaryName <> "#termination-member#" <> member)
          rewriteMemberReference _ term = case term of
            CProjM _ receiver member
              | Just identity <- Map.lookup member identities
              , receiverIsCurrentDictionary receiver ->
                  Just (CGlob identity)
            _ ->
              case spineOfTerm term of
                (CGlob accessor, arguments)
                  | Just member <- Map.lookup accessor authenticatedAccessors
                  , Just receiverPosition <-
                      List.findIndex
                        (receiverIsCurrentDictionary . snd)
                        arguments
                  , accessorReceiverPositionIsValid
                      accessor
                      receiverPosition
                      arguments
                  , Just identity <- Map.lookup member identities ->
                      Just
                        ( List.foldl'
                            (\function (icit, argument) ->
                               CApp icit function argument)
                            (CGlob identity)
                            (drop (receiverPosition + 1) arguments)
                        )
                _ -> Nothing
          accessorReceiverPositionIsValid accessor receiverPosition arguments =
            case Map.lookup accessor shapeValidatedAccessors of
              Just (_, binderCount, expectedReceiverPosition) ->
                length arguments >= binderCount
                  && receiverPosition == expectedReceiverPosition
              Nothing -> True
          projectionAccessor = go 0
            where
              go binderCount = \case
                CLamM _ _ _ _ body -> go (binderCount + 1) body
                CProjM _ (CVar index) member
                  | let receiverPosition = binderCount - index - 1
                  , receiverPosition >= 0
                  , receiverPosition < binderCount ->
                      Just (member, binderCount, receiverPosition)
                _ -> Nothing
          receiverIsCurrentDictionary receiver =
            receiver == CGlob thisG
              || case fst (spineOfTerm receiver) of
                   CGlob resolved -> resolved == dictionary
                   _ -> False
      prepared <-
        fmap catMaybes . forM terminations $ \termination ->
          case Map.lookup (imtName termination) identities of
            Nothing -> pure Nothing
            Just identity -> do
              zonked <-
                zonkTermM (ctxLen ambient) (imtBody termination)
              let exposed =
                    mapTermWithDepth
                      rewriteMemberReference
                      0
                      zonked
              normalized <-
                normalizeTermAt (ctxLen ambient) exposed
              pure
                ( Just
                    ( termination
                    , identity
                    , mapTermWithDepth rewriteMemberReference 0 normalized
                    )
                )
      let
          memberNames = Set.fromList [identity | (_, identity, _) <- prepared]
          dependencies body =
            Set.toList (Set.intersection memberNames (globalsOfTerm body))
          graphNodes =
            [ ((termination, identity, body), identity, dependencies body)
            | (termination, identity, body) <- prepared
            ]
          selfRecursive (_, identity, body) =
            identity `Set.member` globalsOfTerm body
          recursiveGroups =
            [ group
            | component <- stronglyConnComp graphNodes
            , group <- case component of
                AcyclicSCC entry
                  | selfRecursive entry -> [[entry]]
                CyclicSCC entries -> [entries]
                _ -> []
            ]
      forM_ recursiveGroups $ \group -> do
        let declarations =
              [ TerminationDecl
                  identity
                  (imtType termination)
                  (imtBinders termination)
                  (imtDecreases termination)
                  body
                  (imtSpan termination)
              | (termination, identity, body) <- group
              ]
        result <- verifyTerminationSccIn ambient declarations
        when (result == TerminationUnverified) $
          forM_ group $ \(termination, _, _) ->
            reportUnverifiedTermination
              (imtSpan termination)
              []
              ( "could not verify termination of instance member '"
                  <> imtName termination
                  <> "' (§15)"
              )
              "this instance-member SCC has no checked well-founded decrease and is rejected because Kappa is total by default (§15.1–§15.2)"

    memberSigInstance traitG traitUniverses mn argTms ctx doneFields = do
      arguments <- mapM (evalIn ctx) argTms
      instantiateTraitMemberType
        ctx
        sp
        traitG
        traitUniverses
        mn
        arguments
        doneFields

    checkMemberAgainst memberMode ctx memberTy mbinders mResTy mbody msp =
      checkTraitMemberExpressionAgainst
        memberMode
        ctx
        memberTy
        mbinders
        mResTy
        mbody
        msp

    checkInstanceMember trait traitUniverses info argTms ctx supers done memberMode memberTy mbinders mResTy mbody msp = do
      siblingTypes <-
        traitMemberSiblingTypesAt
          msp
          trait
          traitUniverses
          info
          argTms
          ctx
          supers
          done
      let partialDictionary = CRecordV (sortOn fst (supers ++ done))
      checked <-
        withThis (Just (ThisTraitSibs siblingTypes)) $
          checkMemberAgainst memberMode ctx memberTy mbinders mResTy mbody msp
      pure (substThisTm partialDictionary checked, checked)

    deriveStructuralInstanceMember trait _dictionary traitUniverses info argTms ctx supers done memberMode member memberTy site
      | trait /= gPrel "Eq" = pure Nothing
      | memberIdentity /= memberGlobal (gPrel "Eq") "eqSound"
          && memberIdentity /= memberGlobal (gPrel "Eq") "eqComplete" = pure Nothing
      | [targetTerm] <- argTms
      , Just target <- delaborateType ctx site targetTerm = do
          (shape, _) <- deriveNominalShape ctx site targetTerm
          case (shape, lookup "==" done) of
            ([], _) -> pure Nothing
            (_, Nothing) -> pure Nothing
            (_, Just comparator) ->
              derivedEqEvidenceForComparator
                ctx
                site
                shape
                comparator >>= \case
                Just exact -> Just <$> checkGenerated target shape exact
                Nothing ->
                  checkedFunctionalEqualityHelpers comparator >>= \case
                    [] -> pure Nothing
                    helpers -> attemptFunctional comparator target shape helpers
      | otherwise = pure Nothing
      where
        memberIdentity = memberGlobal trait member

        checkGenerated target shape (evidenceBindings, evidenceNames) = do
          let generatedSpan = derivedGeneratedSpan site 43
              xName = Name "__derive_member_x" generatedSpan
              yName = Name "__derive_member_y" generatedSpan
              proofName = Name "__derive_member_proof" generatedSpan
              body
                | memberIdentity == memberGlobal (gPrel "Eq") "eqSound" =
                    derivedEqualitySoundBody
                      generatedSpan
                      target
                      shape
                      evidenceNames
                      xName
                      yName
                      proofName
                | otherwise =
                    derivedEqualityCompleteBody
                      generatedSpan
                      target
                      shape
                      evidenceNames
                      xName
                      yName
                      proofName
          evidenceCtx <- bindDerivedEqEvidence ctx evidenceBindings
          checked <- checkGeneratedBody evidenceCtx body
          pure
            ( closeDerivedEqEvidence evidenceBindings (fst checked)
            , closeDerivedEqEvidence evidenceBindings (snd checked)
            )

        checkGeneratedBody activeCtx body = do
          let generatedSpan = derivedGeneratedSpan site 43
              xName = Name "__derive_member_x" generatedSpan
              yName = Name "__derive_member_y" generatedSpan
              proofName = Name "__derive_member_proof" generatedSpan
          siblingTypes <-
            traitMemberSiblingTypesAt
              generatedSpan
              trait
              traitUniverses
              info
              argTms
              ctx
              supers
              done
          let partialDictionary = CRecordV (sortOn fst (supers ++ done))
          checked <-
            withThis (Just (ThisTraitSibs siblingTypes)) $
              checkMemberAgainst
                memberMode
                activeCtx
                memberTy
                [simpleBinder xName, simpleBinder yName, simpleBinder proofName]
                Nothing
                body
                generatedSpan
          pure
            ( substThisTm partialDictionary checked
            , checked
            )

        -- A custom comparator may delegate to a transparent recursive helper
        -- instead of projecting the selected field dictionaries directly.
        -- In that case propose the ordinary structural proof under the
        -- helper's checked equations.  This is deliberately speculative: the
        -- normal checker must establish that the helper is definitionally the
        -- same decision procedure, and a failed proposal leaves no metas or
        -- diagnostics behind.
        attemptFunctional comparator target shape helpers = do
          baseline <- get
          let errors state =
                length
                  [ ()
                  | diagnostic <- csDiags state
                  , dSeverity diagnostic == SevError
                  ]
          checkedFunctionalEqualityPlan ctx site comparator helpers >>= \case
            Nothing -> put baseline >> pure Nothing
            Just functional -> do
              rootMethods <-
                derivedRecursiveFieldMethods ctx (dfeDomain functional) shape
              helperValue <- evalIn ctx (dfeTerm functional)
              let helperCtx =
                    bindCtxLet
                      (nameText (dfeBindingName functional))
                      False
                      (dfeType functional)
                      helperValue
                      ctx
                  generatedSpan = derivedGeneratedSpan site 43
                  xName = Name "__derive_member_x" generatedSpan
                  yName = Name "__derive_member_y" generatedSpan
                  proofName = Name "__derive_member_proof" generatedSpan
                  sound =
                    memberIdentity == memberGlobal (gPrel "Eq") "eqSound"
                  body =
                    derivedFunctionalEqualityMemberBody
                      sound
                      generatedSpan
                      target
                      shape
                      rootMethods
                      functional
                      xName
                      yName
                      proofName
                  close = substTopTermAt 0 (dfeTerm functional)
              generated <-
                withTemporaryReducibleGlobals helpers $
                  checkGeneratedBody helperCtx body
              current <- get
              if errors current == errors baseline
                then
                  pure
                    ( Just
                        (close (fst generated), close (snd generated))
                    )
                else put baseline >> pure Nothing

    completeOmittedMember declaredDerived member trait traitUniverses info argTms ctx supers done memberTy site = do
      admissible <-
        if declaredDerived
          then pure True
          else do
            propositionGoal <- globalValueM prelIsProp [(Expl, memberTy)]
            isJust <$> isPropClosure ctx site propositionGoal
      if not admissible
        then pure Nothing
        else do
          baseline <- get
          siblingTypes <-
            traitMemberSiblingTypesAt
              site
              trait
              traitUniverses
              info
              argTms
              ctx
              supers
              done
          let partialDictionary = CRecordV (sortOn fst (supers ++ done))
          proof <-
            withThis (Just (ThisTraitSibs siblingTypes)) $
              synthesizeDerivation ctx site memberTy
          diagnostics <- gets csDiags
          let added = length diagnostics - length (csDiags baseline)
          if added == 0
            then pure (Just (substThisTm partialDictionary proof))
            else do
              when declaredDerived $
                retagNew (length (csDiags baseline)) $ \diagnostic ->
                  if dCode diagnostic == "E_DERIVE_AMBIGUOUS"
                    then
                      diagnostic
                        { dMessage =
                            dMessage diagnostic
                              <> " while completing member '"
                              <> member
                              <> "'"
                        }
                    else diagnostic
              unless declaredDerived (put baseline)
              pure Nothing
