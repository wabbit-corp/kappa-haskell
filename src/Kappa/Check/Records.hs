-- | Records, projections, and patches.
--
-- Helpers for record types and values — field ordering, dependent sibling
-- references via @this@, and the §13.2.5 patch rules.
--
-- Carved out of "Kappa.Check" as part of splitting that module; see
-- "Kappa.Check.Types" for the shared data dictionary and docs\/CONCEPTS.md
-- for the vocabulary these assume.
module Kappa.Check.Records
  ( associatedStaticMemberArgs
  , carrierSourceArgument
  , elabModuleMember
  , globalTermWithUniversePrefix
  , metaClassifierTermInContext
  , moduleObjectFor
  , moduleSignatureType
  , peelTraitMemberPrefix
  , recordErasedProjection
  , recordUsageExpressionType
  , selectConstructorPatternLet
  , traitDefaultGlobal
  , validatePatchSourceItems
  , varUsedAt
  , wrapTraitMemberPrefix
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

-- | Commit a successfully principalized provisional occurrence. Its checked
-- result no longer contains occurrence metas, so retaining the occurrence or
-- constraints owned solely by it would leak transaction-local inference state
-- into module closeout. Constraints also registered by source elaboration, or
-- shared with another live occurrence, remain owned.
retireProvisionalUniverseOccurrences :: Set Int -> CheckM ()
retireProvisionalUniverseOccurrences retired
  | Set.null retired = pure ()
  | otherwise =
      modify' $ \st ->
        let retainedConstraints =
              filter
                (constraintOwnedAfterRetiringOccurrences st retired)
                (csLevelConstraints st)
            retainedIds =
              Set.fromList (map lcIdentity retainedConstraints)
            trimProvenance provenance =
              provenance
                { lcpProvisionalOccurrences =
                    Set.difference
                      (lcpProvisionalOccurrences provenance)
                      retired
                }
         in reindexLevelConstraints
              (deleteProvisionalUniverseInstantiations retired st)
                { csLevelConstraints = retainedConstraints
                , csLevelConstraintOwners =
                    Map.restrictKeys
                      (csLevelConstraintOwners st)
                      retainedIds
                , csLevelConstraintSpans =
                    Map.restrictKeys
                      (csLevelConstraintSpans st)
                      retainedIds
                , csLevelConstraintProvenance =
                    Map.map trimProvenance
                      ( Map.restrictKeys
                          (csLevelConstraintProvenance st)
                          retainedIds
                      )
                }

recordUsageExpressionType :: Ctx -> Expr -> Value -> CheckM ()
recordUsageExpressionType ctx expression ty = do
  typeTerm0 <- quoteIn ctx ty
  typeTerm <- zonkTermM (ctxLen ctx) typeTerm0
  state <- get
  when (null (unsolvedMetasOf state typeTerm)) $
    case delaborateType ctx (exprSpan expression) typeTerm of
      Nothing -> pure ()
      Just sourceType ->
        modify' $ \current ->
          current
            { csUsageExpressionTypes =
                Map.insert
                  (exprSpan expression)
                  sourceType
                  (csUsageExpressionTypes current)
            }

recordErasedProjection :: Expr -> DotMember -> CheckM ()
recordErasedProjection receiver member =
  modify' $ \state ->
    state
      { csErasedExpressionSpans =
          Set.insert (exprSpan (EDot receiver member)) (csErasedExpressionSpans state)
      }

-- a member completion of a reified module path: either a deeper module
-- object or nothing nameable (§2.8.6)
elabModuleMember :: Ctx -> [Text] -> Span -> CheckM (Term, Value)
elabModuleMember ctx segs sp = do
  st <- get
  if Map.member (ModuleName segs) (csModuleExports st) || ModuleName segs == csModule st
    then pure (moduleObjectFor (ModuleName segs))
    else do
      errAt sp "E_STATIC_OBJECT_UNRESOLVED" (Just "kappa.name.unresolved")
        ("no module named '" <> T.intercalate "." segs <> "' is in this compilation unit (Spec §2.8.6)")
      anyHole ctx

-- a reified module object (§2.8.6): a record carrying the module
-- identity in a tag field, so member access through rebindings works
moduleObjectFor :: ModuleName -> (Term, Value)
moduleObjectFor (ModuleName segs) =
  let moduleName = ModuleName segs
      tag = moduleObjectTag moduleName
   in (CRecordV [(tag, CRecordV [])], evalModuleSignatureType moduleName)

-- | The current Core representation of a module signature is deliberately
-- nominal and contextual. The hidden field records the resolved module
-- identity; it is not a structural approximation of the exported facets.
-- Member projection recognizes this checked type and delegates to
-- 'moduleMember', which consults the canonical interface tables and freshly
-- instantiates the selected declaration's universe schema.
moduleSignatureType :: ModuleName -> Term
moduleSignatureType moduleName =
  CRecordT [(moduleObjectTag moduleName, CRecordT [])]

evalModuleSignatureType :: ModuleName -> Value
evalModuleSignatureType moduleName =
  VRecordT [(moduleObjectTag moduleName, VRecordT [])]

moduleObjectTag :: ModuleName -> Text
moduleObjectTag (ModuleName segments) =
  "__module:" <> T.intercalate "." segments

-- | Open the checked prefix shared by a trait-member accessor and its hidden
-- default template.  The count is structural: generated universe evidence,
-- owning-trait parameters, and the abstract dictionary binder.  Source
-- binders belonging to the member itself remain in the returned member type.
peelTraitMemberPrefix
  :: Span
  -> Int
  -> Ctx
  -> Value
  -> CheckM (Maybe (Ctx, Value, [(ObservationMode, Icit, Q, Text)]))
peelTraitMemberPrefix site = go []
  where
    go binders 0 activeCtx ty = pure (Just (activeCtx, ty, reverse binders))
    go binders remaining activeCtx ty = do
      forced <- forceM ty
      case forced of
        VPiBoundM mode icit quantity _ name assumption domain closure -> do
          withBound <- extendLevelAssumption site activeCtx assumption
          let nextCtx = bindCtxMQ mode quantity name (icit == Impl) domain withBound
          codomain <- clApp closure (VRigid (ctxLen activeCtx) [])
          go ((mode, icit, quantity, name) : binders) (remaining - 1) nextCtx codomain
        _ -> do
          errAt site "E_TRAIT_MEMBER_TELESCOPE_MISMATCH" (Just "kappa.internal.compiler")
            "checked trait-member interface ended before its abstract trait prefix"
          pure Nothing

wrapTraitMemberPrefix
  :: [(ObservationMode, Icit, Q, Text)]
  -> Term
  -> Term
wrapTraitMemberPrefix binders body =
  foldr
    (\(mode, icit, quantity, name) -> CLamM mode icit quantity name)
    body
    binders

-- | Specialize a declaration at an authenticated leading universe prefix.
-- Trait-member accessors are the primary user: their owning trait occurrence
-- fixes the prefix, while levels introduced by the member signature remain
-- independently polymorphic at each projection.
globalTermWithUniversePrefix
  :: Ctx
  -> Span
  -> GName
  -> [Level]
  -> CheckM (Maybe (Term, Value))
globalTermWithUniversePrefix ctx site global prefix = do
  definition <- gets (Map.lookup global . csGlobals)
  case definition of
    Nothing -> pure Nothing
    Just gd -> do
      let total = dutParameterCount (gdUniverses gd)
      state <- get
      let finalized =
            global `Set.member` csFinalizedUniverseInterfaces state
          hasProvisionalLevels =
            not . null . levelMetasOfTerm $
              zonkLevels
                (csLevelAssignments state)
                (globalCoreType (ecOf state) gd)
      if not finalized || hasProvisionalLevels
        then instantiateProvisionalMember gd
        else if length prefix > total
        then do
          errAt site "E_TRAIT_MEMBER_TELESCOPE_MISMATCH" (Just "kappa.internal.compiler")
            ( "trait-member declaration '" <> gnameText global
                <> "' has " <> T.pack (show total)
                <> " universe parameters, fewer than its owning trait occurrence's "
                <> T.pack (show (length prefix))
                <> "-parameter prefix"
            )
          pure Nothing
        else do
          suffix <- replicateM (total - length prefix) freshLevelInstantiationMeta
          let universes = prefix ++ suffix
          recordRecursiveSchemaOccurrence (Just ctx) False site global universes
          Just <$> specializeGlobalAt ctx global gd universes
  where
    instantiateProvisionalMember definition = do
      state <- get
      let assignments = csLevelAssignments state
          unspecializedType =
            zonkLevels assignments (globalCoreType (ecOf state) definition)
          unspecializedInterfaceTerms =
            map
              (zonkLevels assignments)
              (globalUniverseInterfaceTerms state global definition)
          publishedCount = dutParameterCount (gdUniverses definition)
      if publishedCount > 0
        then
          if length prefix > publishedCount
            then malformed publishedCount
            else do
              publishedSuffix <-
                replicateM (publishedCount - length prefix) freshLevelInstantiationMeta
              let publishedUniverses = prefix ++ publishedSuffix
                  specializePublished =
                    zonkTermWith
                      (\_ _ -> Nothing)
                      (substituteLevelParams publishedUniverses)
                      0
                  rawType = specializePublished unspecializedType
                  rawInterfaceTerms =
                    map specializePublished unspecializedInterfaceTerms
                  sourceMetas =
                    nub (concatMap levelMetasOfTerm rawInterfaceTerms)
              closeProvisionalOccurrence
                sourceMetas
                Map.empty
                publishedUniverses
                rawType
        else do
          let rawType = unspecializedType
              rawInterfaceTerms = unspecializedInterfaceTerms
              sourceMetas =
                nub (concatMap levelMetasOfTerm rawInterfaceTerms)
              ownerMetas =
                traitMemberOwnerUniverseMetas state global rawType
          if length ownerMetas /= length prefix
            then malformed (length ownerMetas)
            else
              closeProvisionalOccurrence
                sourceMetas
                (Map.fromList (zip ownerMetas prefix))
                prefix
                rawType
      where
        malformed found = do
          errAt site "E_TRAIT_MEMBER_TELESCOPE_MISMATCH" (Just "kappa.internal.compiler")
            ( "provisional trait-member declaration '" <> gnameText global
                <> "' exposes " <> T.pack (show found)
                <> " owning-trait universe positions, but the checked receiver has "
                <> T.pack (show (length prefix))
            )
          pure Nothing

        closeProvisionalOccurrence sourceMetas pinned headUniverses rawType = do
          registerProvisionalGlobalUniverseMetas global sourceMetas
          active <- gets csActiveUniverseDefinition
          baseline <- get
          (_, specializedType0) <-
            if active == Just global
              then do
                let selected =
                      [ Map.findWithDefault (LMeta meta) meta pinned
                      | meta <- sourceMetas
                      ]
                    substitution =
                      Map.fromList (zip sourceMetas selected)
                pure
                  ( selected
                  , zonkTermWith
                      (\_ _ -> Nothing)
                      (substituteLevelMetas substitution)
                      0
                      rawType
                  )
              else
                instantiateProvisionalUniversesWith
                  ProvisionalGlobalFacet
                  global
                  sourceMetas
                  pinned
                  rawType
          specializedType <-
            if active == Just global
              then pure (Just specializedType0)
              else do
                materializeProvisionalUniverseConstraintsFor (Set.singleton global)
                current <- get
                let newlyFresh =
                      Set.difference
                        (csLevelInstantiationMetas current)
                        (csLevelInstantiationMetas baseline)
                    baselineOccurrences =
                      Map.keysSet (csProvisionalUniverseInstantiations baseline)
                    localOccurrences =
                      Set.difference
                        (Map.keysSet (csProvisionalUniverseInstantiations current))
                        baselineOccurrences
                principalizeLevelOccurrence
                  0
                  baseline
                  newlyFresh
                  specializedType0 >>= \case
                    Just (principal, closedType) -> do
                      installLevelAssignments principal
                      retireProvisionalUniverseOccurrences localOccurrences
                      pure (Just closedType)
                    Nothing -> do
                      errAt
                        site
                        "E_UNIVERSE_NO_PRINCIPAL_SOLUTION"
                        (Just "kappa.universe.no-principal-solution")
                        ( "the provisional universe occurrence of trait member '"
                            <> gnameText global
                            <> "' has no principal specialization"
                        )
                      pure Nothing
          case specializedType of
            Nothing -> pure Nothing
            Just closedType -> do
              recordRecursiveSchemaOccurrence
                (Just ctx)
                False
                site
                global
                headUniverses
              ty <- evalIn emptyCtx closedType
              pure (Just (CGlobI global headUniverses, ty))

-- | Transport a metavariable's checked creation-site classifier through a
-- lexical context extension. Context entries are de Bruijn binders prepended
-- after the metavariable was created, so weakening by the exact depth delta
-- preserves every reference to the original context. A shallower or
-- unrelated context has no such transport and fails closed.
metaClassifierTermInContext :: Ctx -> MetaClassifier -> Maybe Term
metaClassifierTermInContext ctx classifier = do
  let creationDepth = micDepth classifier
      currentDepth = ctxLen ctx
  guard (creationDepth <= currentDepth)
  pure (shiftTerm (currentDepth - creationDepth) 0 (micType classifier))

-- | Recover the source type argument whose cumulative image inhabits a
-- carrier's input universe. Generalized Applicative/Monad members quantify
-- over that source type and insert the lift themselves; passing the already
-- lifted carrier argument would apply the modality twice and leave malformed
-- Core once the member's universe telescope is principalized.
--
-- The inverse is used only for an explicit proof-carrying 'VUniverseLift' at
-- this typed carrier-argument boundary. The reconstructed member application
-- is subsequently checked against the exact expected action type, which is
-- the authoritative target-domain validation even while level metas remain
-- unsolved here. All other values are already source arguments and remain
-- unchanged.
carrierSourceArgument :: Ctx -> Span -> Value -> Value -> CheckM Value
carrierSourceArgument _ctx _site _carrier argument = do
  exposed <- exposeSolvedMetas 64 Set.empty argument
  case exposed of
    VUniverseLift _ _ _ source -> pure source
    _ -> pure exposed
  where
    -- Ordinary forcing deliberately erases cumulative lifts for conversion.
    -- Here the lift is the information being inverted, so dereference solved
    -- term metas without crossing any other semantic constructor.
    exposeSolvedMetas fuel seen value
      | fuel <= (0 :: Int) = pure value
      | otherwise =
          case value of
            VFlex meta spine
              | meta `Set.notMember` seen -> do
                  solution <- gets (Map.lookup meta . csMetas)
                  case solution of
                    Just (Just solved) -> do
                      context <- ec_
                      exposeSolvedMetas
                        (fuel - 1)
                        (Set.insert meta seen)
                        (evalApp context solved spine)
                    _ -> pure value
            _ -> pure value

traitDefaultGlobal :: GName -> Text -> GName
traitDefaultGlobal (GName m trait) member =
  GName m (trait <> ".#default." <> member)

-- | @Trait.Member p1 ... pn rest@ is the source-level associated-family
-- spelling used by the standard range/refinement interfaces. The generated
-- accessor ABI keeps the trait parameters implicit so ordinary evidence
-- projections remain ergonomic. Reclassify exactly that checked trait prefix;
-- the normal spine then resolves the dictionary and applies any residual
-- arguments to the projected compile-time member. This is keyed by resolved
-- trait/member metadata, never by a member spelling.
associatedStaticMemberArgs :: Int -> [Arg] -> [Arg]
associatedStaticMemberArgs traitArity =
  zipWith reclassify [0 :: Int ..]
  where
    reclassify index argument
      | index < traitArity =
          case argument of
            ArgExplicit expression -> ArgImplicit expression
            _ -> argument
      | otherwise = argument

selectConstructorPatternLet
  :: Ctx
  -> Span
  -> LetDef
  -> CheckM (Maybe ConstructorPatternCandidate)
selectConstructorPatternLet ctx declarationSpan definition =
  case ldConstructorPatternCandidate definition of
    Just candidate@(ConstructorPatternCandidate pattern' _) ->
      case pattern' of
        PCtor reference _ _ ->
          resolveCtorWithoutDiagnostic ctx reference >>= \case
            Just _ -> do
              modify' $ \state ->
                state
                  { csConstructorPatternLetSpans =
                      Set.insert
                        declarationSpan
                        (csConstructorPatternLetSpans state)
                  }
              pure (Just candidate)
            Nothing -> pure Nothing
        _ -> pure Nothing
    Nothing -> pure Nothing

-- | Validate the source-level patch identity contract before the receiver's
-- runtime representation is known.  §13.2.5 makes these properties of one
-- patch expression, so closed records, open rows, dependent records, and
-- constructor-backed records must not acquire different answers.
validatePatchSourceItems :: [PatchItem] -> Span -> CheckM Bool
validatePatchSourceItems items fallbackSpan = do
  let violations = patchSourceViolations fallbackSpan items
  forM_ violations $ \case
    DuplicateUpdatePath site path ->
      errAt site "E_RECORD_PATCH_DUPLICATE_PATH" (Just "kappa-hs.record.patch-duplicate")
        ("record patch updates path '" <> path <> "' more than once (§13.2.5)")
    DuplicateExtensionLabel site label ->
      errAt site "E_ROW_EXTENSION_DUPLICATE_LABEL" (Just "kappa-hs.row.extension-duplicate")
        ("row extension introduces label '" <> label <> "' more than once (§13.2.6)")
    UpdatePrefixConflict site path ->
      errAt site "E_RECORD_PATCH_PREFIX_CONFLICT" (Just "kappa-hs.record.patch-prefix-conflict")
        ("record patch updates both '" <> path <> "' and a path beneath it (§13.2.5)")
    MixedPatchLabelConflict site label ->
      errAt site "E_RECORD_PATCH_PREFIX_CONFLICT" (Just "kappa-hs.record.patch-prefix-conflict")
        ("record patch uses label '" <> label <> "' for both update and extension (§13.2.5)")
  pure (null violations)

-- | Whether the de Bruijn /index/ @ix@ (relative to the term's top
-- scope) is referenced by any @CVar@ in the term, incrementing the
-- target under each binder. Used by 'elabOpenExists' to detect witness
-- escape in the inferred result type.
varUsedAt :: Int -> Term -> Bool
varUsedAt = go
  where
    go ix = \case
      CVar i -> i == ix
      CLevel _ -> False
      CUniverseLift _ _ _ inner -> go ix inner
      CSchemaLift _ _ _ _ _ _ sourceArguments targetArguments inner ->
        any (go ix) sourceArguments || any (go ix) targetArguments || go ix inner
      CLam _ _ _ b -> go (ix + 1) b
      CPi _ _ _ _ a b -> go ix a || go (ix + 1) b
      CApp _ f a -> go ix f || go ix a
      CCtor _ _ as -> any (go ix) as
      CMatch s _ _ alts -> go ix s || or [maybe False (go (ix + patBindersC p)) g || go (ix + patBindersC p) b | CaseAlt p g b <- alts]
      CRecordT fs -> any (go ix . snd) fs
      CRecordV fs -> any (go ix . snd) fs
      CProj x _ -> go ix x
      CProjAt x _ _ -> go ix x
      CVariantT ms -> any (go ix) ms
      CInject _ x -> go ix x
      CLet _ _ a b c -> go ix a || go ix b || go (ix + 1) c
      CLetRec _ _ a b c -> go ix a || go (ix + 1) b || go (ix + 1) c
      CLetPolyM _ _ _ _ a b c -> go ix a || go ix b || go (ix + 1) c
      CLetRecPolyM _ _ _ _ a b c -> go ix a || go (ix + 1) b || go (ix + 1) c
      CLetRecGroupM _ definitions body ->
        let count = length definitions
         in any (\definition -> go ix (clrdType definition) || go (ix + count) (clrdRhs definition)) definitions
              || go (ix + count) body
      CSealE _ x -> go ix x
      CSigT _ x -> go ix x
      CThunkE x suspensionType -> go ix x || maybe False (go ix) suspensionType
      CLazyE x suspensionType -> go ix x || maybe False (go ix) suspensionType
      CForceE x resultType -> go ix x || maybe False (go ix) resultType
      CIf a b c -> go ix a || go ix b || go ix c
      CQuote _ slots -> any (go ix) slots
      CGlob _ -> False
      CLocal i _ -> i == ix
      CSort _ -> False
      CLit _ -> False
      CMeta _ -> False
      CDo _ _ -> False
