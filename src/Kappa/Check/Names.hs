-- | Name resolution and scoping.
--
-- Turning a source spelling into a resolved identity: looking through the
-- local context, the module scope, and the import environment, and
-- instantiating a constructor or global at a fresh universe occurrence.
--
-- Carved out of "Kappa.Check" as part of splitting that module; see
-- "Kappa.Check.Types" for the shared data dictionary and docs\/CONCEPTS.md
-- for the vocabulary these assume.
module Kappa.Check.Names
  ( alignNominalOccurrenceUniverses
  , applyLocalNominalCaptures
  , badLiteralSuffix
  , canonicalEqualityCorePayload
  , closeSpellings
  , coherentTraitEvidenceTerms
  , coreTermClassifierInCtx
  , declaredNominalApplication
  , extendLevelAssumptionFromSynthesized
  , formationCeiling
  , formationCeilingTerm
  , formationContribution
  , generatedEffPureAtM
  , generatedEffPureCore
  , holeMetas
  , inferRefFacet
  , inferVarRead
  , instantiateCtor
  , instantiateCtorType
  , instantiateLocalDeclaration
  , instantiateLocalDeclarationAt
  , instantiateProvisionalUniverses
  , instantiateUniverseTelescope
  , nameHasOrdinaryBinding
  , nominalArgumentDomain
  , normalizeProvisionalUniverseOccurrence
  , pendingComponentTypeKey
  , pendingEntryFacts
  , pendingEntryIsTrait
  , pendingEntryIsUnsolved
  , pendingEntrySite
  , pendingTraitArgumentsRigid
  , prefixResolves
  , provisionalDeclarationUniverses
  , recordExpectedImplicitRecursiveSchema
  , recordHoleClassifier
  , recordImplicitExpressionDemand
  , recordLocalRecursiveSchemaOccurrence
  , refinementViewMayResolve
  , registerLevelField
  , replaceTermRoot
  , replayCheckedLevelAssumption
  , reportInconsistentHole
  , reportInvalidLevelTerm
  , reportUnboundedTelescope
  , reportUnsolvedHole
  , scopeNamesNear
  , shadowedDeclKind
  , specializeCtorAt
  , specializeDeclarationComponent
  , specializeEffectOperationMetadata
  , suggestionThreshold
  , termContainsRoot
  , varReadBlocked
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

-- | §3.1.4/§8.3.1A: if the spelling @n@ names a live type, constructor,
-- or other top-level declaration (the kind of declaration a module alias
-- with the same spelling shadows), return a short human label for that
-- kind. Returns 'Nothing' when @n@ denotes no such declaration, so the
-- caller falls back to the ordinary unresolved-member diagnostic. The
-- test is keyed on "the alias spelling also has a declaration", not on
-- any particular name.
shadowedDeclKind :: Text -> CheckM (Maybe Text)
shadowedDeclKind n = do
  mg <- lookupGlobalName n
  st <- get
  pure $ do
    g <- mg
    if
      | Map.member g (csDatas st) -> Just "type"
      | Map.member g (csCtors st) -> Just "constructor"
      | Map.member g (csGlobals st) -> Just "declaration"
      | otherwise -> Nothing

applyLocalNominalCaptures
  :: Ctx
  -> Span
  -> GName
  -> (Term, Value)
  -> CheckM (Term, Value)
applyLocalNominalCaptures ctx site global initial = do
  captures <- gets (Map.findWithDefault [] global . csLocalNominalCaptures)
  foldM applyOne initial captures
  where
    applyOne (function, functionType) capture = do
      let index = ctxLen ctx - lncLevel capture - 1
      if index < 0 || index >= ctxLen ctx
        then do
          report $
            withPayload
              ( withPayloadField "localDeclaration" (gnameText global) $
                  withPayloadField "capture" (lncName capture) $
                    payloadKind "local-declaration-capture-scope"
              ) $
              diag SevError StageElaborate "E_LOCAL_DECLARATION_CAPTURE_SCOPE"
                (Just "kappa.name.unresolved") site
                ( "local declaration '" <> gnameText global
                    <> "' requires captured binder '" <> lncName capture
                    <> "', but that declaration-site binder is no longer in lexical scope (§30.1.1)"
                )
          pure (function, functionType)
        else do
          let argument = CVar index
              argumentValue = ctxEnv ctx !! index
          forceM functionType >>= \case
            VPiM _ Impl _ _ _ _ codomain -> do
              resultType <- clApp codomain argumentValue
              pure (CApp Impl function argument, resultType)
            actual -> do
              actualTerm <- quoteIn ctx actual
              report $
                withPayload
                  ( withPayloadField "localDeclaration" (gnameText global) $
                      withPayloadField "capture" (lncName capture) $
                        withPayloadField "actualHeadType" (renderTerm actualTerm) $
                          payloadKind "local-declaration-capture-interface"
                  ) $
                  diag SevError StageElaborate "E_LOCAL_DECLARATION_CAPTURE_INTERFACE"
                    (Just "kappa.internal.compiler") site
                    ( "local declaration '" <> gnameText global
                        <> "' has no implicit capture binder for '" <> lncName capture
                        <> "' in its finalized interface"
                    )
              pure (function, functionType)

-- | Build the compiler-owned effect-tree pure node with its exact intrinsic
-- telescope.  It is not a declared constructor and therefore cannot use
-- 'generatedCtorApplyAtM'.
generatedEffPureCore :: Term -> Term -> Term -> Term
generatedEffPureCore payloadType resultType payload =
  CCtorI prelEffPure []
    (Just (CPiBoundFormedM Ordinary FormationOrdinary Expl Q1 False "__value" Nothing payloadType (shiftTerm 1 0 resultType)))
    [ConstructorArg Expl True Nothing payload]

generatedEffPureAtM :: Ctx -> Value -> Term -> CheckM Term
generatedEffPureAtM ctx expected payload = do
  forced <- forceM expected
  case monadActionViewValue forced of
    Just (carrier, payloadType)
      | nominalFamilyValueHead carrier == Just prelEff -> do
          payloadTypeTerm <- quoteIn ctx payloadType
          resultTypeTerm <- quoteIn ctx expected
          pure (generatedEffPureCore payloadTypeTerm resultTypeTerm payload)
    _ -> do
      errAt noSpan "E_INTERNAL_EFFECT_PURE_TYPE" Nothing
        "compiler-generated __EffPure requires an Eff row result type"
      fst <$> anyHole ctx

canonicalEqualityCorePayload :: Term -> Maybe ([Level], Term, Term, Term)
canonicalEqualityCorePayload proposition = do
  let (headTerm, arguments) =
        spineOfTerm (stripIdentityWrappers proposition)
      implicit = [argument | (Impl, argument) <- arguments]
      explicit = [argument | (Expl, argument) <- arguments]
  universes <- case stripIdentityWrappers headTerm of
    CGlobal equality levels
      | equality == prelEqType -> Just levels
    CGlob equality
      | equality == prelEqType -> Just []
    _ -> Nothing
  carrier <- listToMaybe implicit
  (lhs, rhs) <- last2 explicit
  pure (universes, carrier, lhs, rhs)

instantiateCtorType :: GName -> CtorInfo -> CheckM Term
instantiateCtorType g ci = snd <$> instantiateCtor g ci

instantiateCtor :: GName -> CtorInfo -> CheckM ([Level], Term)
instantiateCtor g ci = do
  assignments <- gets csLevelAssignments
  let rawType = zonkLevels assignments (ciType ci)
      telescope = ciUniverses ci
  if dutParameterCount telescope > 0
    then do
      universes <- instantiateUniverseTelescope g telescope
      pure
        ( universes
        , zonkTermWith
            (\_ _ -> Nothing)
            (substituteLevelParams universes)
            0
            rawType
        )
    else do
      let provisionalMetas = nub (levelMetasOfTerm rawType)
      modify' $ \state ->
        state
          { csProvisionalConstructorUniverseMetas =
              Map.insertWith
                (\new existing -> nub (existing ++ new))
                g
                [provisionalMetas]
                (csProvisionalConstructorUniverseMetas state)
          }
      instantiateProvisionalUniverses
        ProvisionalConstructorFacet g provisionalMetas rawType

-- | Freshen a declaration interface before the module SCC generalization
-- boundary has replaced its observable level metas by stable 'LParam's. This
-- is the provisional form of the same hidden telescope, not let-bound
-- monomorphism: every external occurrence receives fresh levels and the
-- constraints are installed once the declaration SCC materializes its stable
-- telescope. This temporary phase must stay bounded: scanning/copying the
-- module constraint graph at every use makes header elaboration quadratic.
-- Terms retained past the header pass are rewritten to the final telescope by
-- 'generalizeDeclarationUniverses'.
instantiateProvisionalUniverses
  :: ProvisionalUniverseFacet
  -> GName
  -> [LevelMeta]
  -> Term
  -> CheckM ([Level], Term)
instantiateProvisionalUniverses facet owner sourceMetas =
  instantiateProvisionalUniversesWith facet owner sourceMetas Map.empty

-- | Universe spine for a declaration reference emitted while that
-- declaration's header is still being elaborated. An explicit schema is
-- already rigid and uses its ordered parameters; an inferred declaration
-- forwards the observable provisional metas until SCC generalization replaces
-- them with stable parameters. Emitting an empty spine here creates a distinct
-- global identity and cannot be repaired later when no meta occurs in the
-- stale reference.
provisionalDeclarationUniverses :: [Term] -> CheckM [Level]
provisionalDeclarationUniverses interfaceTerms = do
  explicitCount <- gets (Map.size . csActiveUniverseSchema)
  finalizedTerms <- mapM (zonkTermM 0) interfaceTerms
  pure $
    if explicitCount > 0
      then map LParam [0 .. explicitCount - 1]
      else map LMeta (nub (concatMap levelMetasOfTerm finalizedTerms))

instantiateUniverseTelescope :: GName -> DeclarationUniverseTelescope -> CheckM [Level]
instantiateUniverseTelescope _ telescope =
  replicateM (dutParameterCount telescope) freshLevelInstantiationMeta

-- | Freshen a local declaration schema at one lexical occurrence. The
-- generalized semantic value remains in 'ctxEnv'; 'CLocal' carries the static
-- specialization needed by NbE and KCoreText without introducing a term
-- argument or runtime closure field (§11.1.2.3A.1).
instantiateLocalDeclaration
  :: Ctx
  -> Span
  -> Int
  -> CtxEntry
  -> LocalUniverseInfo
  -> CheckM (Term, Value)
instantiateLocalDeclaration ctx site index entry LocalUniverseInfo {luiTelescope = telescope} = do
  recursiveScope <- gets csActiveLocalRecursiveSchemaScope
  let calleeLevel = ctxLen ctx - 1 - index
      currentRecursiveInstance = do
        scope <- recursiveScope
        guard (calleeLevel `Map.member` lrssMembers scope)
        guard
          ( length (lrssCurrentInstance scope)
              == dutParameterCount telescope
          )
        pure (lrssCurrentInstance scope)
  universes <-
    maybe
      (replicateM (dutParameterCount telescope) freshLevelInstantiationMeta)
      pure
      currentRecursiveInstance
  recordLocalRecursiveSchemaOccurrence ctx False site index universes
  instantiateLocalDeclarationAt ctx index entry telescope universes

instantiateLocalDeclarationAt
  :: Ctx
  -> Int
  -> CtxEntry
  -> DeclarationUniverseTelescope
  -> [Level]
  -> CheckM (Term, Value)
instantiateLocalDeclarationAt ctx index entry telescope universes = do
  generalizedType <- quoteIn ctx (ceType entry)
  let specializedType =
        zonkTermWith
          (\_ _ -> Nothing)
          (instantiateLocalLevelParams (length universes) universes)
          0
          generalizedType
  ty <- evalIn ctx specializedType
  pure (CLocal index universes, ty)

recordLocalRecursiveSchemaOccurrence
  :: Ctx
  -> Bool
  -> Span
  -> Int
  -> [Level]
  -> CheckM ()
recordLocalRecursiveSchemaOccurrence ctx explicit site calleeIndex levels = do
  scope <- gets csActiveLocalRecursiveSchemaScope
  forM_ scope $ \LocalRecursiveSchemaScope {..} -> do
    let calleeLevel = ctxLen ctx - 1 - calleeIndex
    when (calleeLevel `Map.member` lrssMembers) $ do
      assumptions <- effectiveLevelAssumptions ctx
      modify' $ \state ->
        state
          { csLocalRecursiveSchemaOccurrences =
              LocalRecursiveSchemaOccurrence
                lrssCaller
                calleeLevel
                levels
                explicit
                assumptions
                site
                : csLocalRecursiveSchemaOccurrences state
          }

-- | Normalize a same-module reference while its declaration still has the
-- provisional all-meta telescope used during header elaboration. Seeded and
-- already-finalized references may carry the principal spine at the same
-- time. Conversion compares the two only after applying the declaration's
-- current provisional-to-principal morphism; the SCC finalizer later performs
-- the identical rewrite in retained Core.
normalizeProvisionalUniverseOccurrence :: GName -> [Level] -> CheckM [Level]
normalizeProvisionalUniverseOccurrence g universes = do
  definition <- gets (Map.lookup g . csGlobals)
  case definition of
    Just gd | not (dutExplicit (gdUniverses gd)) -> do
      st <- get
      let assignments = csLevelAssignments st
          rawInterfaceTerms = globalUniverseInterfaceTerms st g gd
          normalizedInterfaceTerms = map (zonkLevels assignments) rawInterfaceTerms
          sourceMetas = nub (concatMap levelMetasOfTerm rawInterfaceTerms)
          roles = mconcat (map declarationUniverseRoles normalizedInterfaceTerms)
          retainedSet = durGeneralizable roles
          retainedMetas =
            filter (`Set.member` retainedSet)
              (concatMap levelMetasOfTerm normalizedInterfaceTerms)
      pure $ case deriveUniverseReferenceProjection assignments sourceMetas retainedMetas of
        Just projection
          | length universes == urpSourceArity projection ->
              [universes !! position | position <- urpRetainedPositions projection]
        _ -> universes
    _ -> pure universes

-- | Specialize a semantic component stored under a declaration's universe
-- telescope (for example a trait's supertrait closures) at one occurrence of
-- that declaration. Components do not own an independent schema: the
-- declaration interface is authoritative. The provisional path uses the
-- interface's source-meta order so a component mentioning only a subset cannot
-- accidentally renumber the occurrence.
specializeDeclarationComponent :: GName -> [Level] -> Term -> CheckM Term
specializeDeclarationComponent owner universes component = do
  definition <- gets (Map.lookup owner . csGlobals)
  assignments <- gets csLevelAssignments
  st <- get
  let zonk = zonkLevels assignments
      rawComponent = zonk component
  pure $ case definition of
    Nothing -> rawComponent
    Just gd
      | dutParameterCount (gdUniverses gd) > 0 ->
          zonkTermWith
            (\_ _ -> Nothing)
            (substituteLevelParams universes)
            0
            rawComponent
      | otherwise ->
          let rawInterfaces = map zonk (globalUniverseInterfaceTerms st owner gd)
              sourceMetas = nub (concatMap levelMetasOfTerm rawInterfaces)
              substitution = substituteLevelMetas (Map.fromList (zip sourceMetas universes))
           in zonkTermWith (\_ _ -> Nothing) substitution 0 rawComponent

-- | Specialize the complete operation telescope with the same hidden or
-- provisional universe occurrence selected for its owning effect interface.
-- The metadata is not an independent declaration: freshening it separately,
-- or leaving its raw metas connected to the declaration header, makes two
-- operation selections spuriously monomorphic.
specializeEffectOperationMetadata
  :: GName
  -> [Level]
  -> EffLabelInfo
  -> EffOpInfo
  -> CheckM (EffLabelInfo, EffOpInfo)
specializeEffectOperationMetadata owner universes effectInfo operation = do
  let specializeTerm = specializeDeclarationComponent owner universes
      specializeLevel level = do
        specialized <- specializeTerm (CSort level)
        pure $ case specialized of
          CSort result -> result
          _ -> level
      specializeAssumption = traverse $ \(lower, upper) ->
        (,) <$> specializeLevel lower <*> specializeLevel upper
      specializeEntry entry = do
        domain <- specializeTerm (teDomain entry)
        assumption <- specializeAssumption (teLevelAssumption entry)
        pure entry {teDomain = domain, teLevelAssumption = assumption}
      specializeOperation op = do
        implicits <- traverse specializeEntry (eoiImplicits op)
        arguments <- traverse specializeEntry (eoiArgs op)
        result <- specializeTerm (eoiResT op)
        pure op {eoiImplicits = implicits, eoiArgs = arguments, eoiResT = result}
  parameters <- traverse specializeEntry (eliParams effectInfo)
  operation' <- specializeOperation operation
  pure (effectInfo {eliParams = parameters}, operation')

specializeCtorAt :: Ctx -> GName -> CtorInfo -> [Level] -> CheckM (Term, Value)
specializeCtorAt ctx g ci universes = do
  assignments <- gets csLevelAssignments
  ec <- ec_
  let rawType = zonkLevels assignments (ciType ci)
      specialized = specializeDeclarationUniverses (ciUniverses ci) universes rawType
  ty <- evalIn ctx specialized
  pure (etaCtor ec g universes specialized, ty)

-- | §3.2.2 suggestion edit-distance threshold for a spelling of this
-- length. Scales with the length so a one-character name does not match
-- every other one-character name. Used both to bound the candidate
-- buckets ('scopeNamesNear') and to filter by edit distance below.
suggestionThreshold :: Int -> Int
suggestionThreshold tlen = max 1 (min 2 (tlen `div` 3))

-- | §3.2.2 typo suggestions: in-scope names within a small edit distance
-- of the unresolved spelling, nearest first (ties broken alphabetically
-- for determinism, §3.1.10). The threshold scales with the length so a
-- one-character name does not match every other one-character name.
-- @cands@ is expected to already be length-compatible (see
-- 'scopeNamesNear'); the length pre-filter is kept so the function is
-- correct on any candidate list.
closeSpellings :: Text -> [Text] -> [Text]
closeSpellings target cands =
  map snd $
    sort
      [ (d, c)
      | c <- cands
      , c /= target
      -- Levenshtein distance is at least the length difference, so a
      -- candidate whose length differs from the target by more than the
      -- threshold can never be within threshold. Skipping it before the
      -- O(len^2) edit-distance keeps the per-error cost proportional to
      -- the (small) set of length-compatible candidates rather than the
      -- whole scope (avoids an O(Nnames * Nscope * len^2) blowup when a
      -- dropped import breaks many references in a large module).
      , abs (T.length c - tlen) <= threshold
      , let d = editDistance tchars (T.unpack c)
      , d <= threshold
      ]
  where
    tchars = T.unpack target
    tlen = T.length target
    threshold = suggestionThreshold tlen

-- | Standard Levenshtein edit distance.
editDistance :: String -> String -> Int
editDistance a b = last (foldl transform [0 .. length a] b)
  where
    transform prevRow@(p0 : _) c =
      scanl compute (p0 + 1) (zip3 a prevRow (tail prevRow))
      where
        compute z (ca, dDiag, dLeft) =
          minimum [dLeft + 1, z + 1, dDiag + if ca == c then 0 else 1]
    transform [] _ = []

-- | Primitive universe spellings are selected only after ordinary name
-- resolution proves that no lexical, static-schema, imported, module-object,
-- or global binding owns the same namespace key. Backtick spelling has the
-- same key as an unquoted identifier, so no token-form exception is needed.
nameHasOrdinaryBinding :: Ctx -> Name -> CheckM Bool
nameHasOrdinaryBinding ctx name =
  case lookupCtx text ctx of
    Just _ -> pure True
    Nothing -> do
      state <- get
      if Map.member text (csActiveUniverseSchema state)
          || Map.member text (csScopeAmbig state)
          || isJust (resolveModuleObjectName state text)
        then pure True
        else isJust <$> lookupGlobalName text
  where
    text = nameText name

inferRefFacet :: Ctx -> Name -> Span -> CheckM (Term, Value)
inferRefFacet ctx n sp =
  case lookupCtx (nameText n) ctx of
    Just (i, e)
      | Just _ <- ceVarInfo e ->
          pure (CVar i, ceType e)
      | otherwise -> do
          errMutableBinding sp "E_VAR_REF_REQUIRED" (nameText n) "reference" [("sourceOperation", "ref")]
            ("'ref " <> nameText n <> "' requires '" <> nameText n <> "' to be a mutable var binding introduced by 'var' (§18.6.1)")
          anyHole ctx
    Nothing -> do
      errAt (nameSpan n) "E_NAME_UNRESOLVED" (Just "kappa.name.unresolved")
        ("unresolved mutable var binding '" <> nameText n <> "' in 'ref " <> nameText n <> "'")
      anyHole ctx

inferVarRead :: Ctx -> Name -> Span -> CheckM (Term, Value)
inferVarRead ctx n sp =
  case lookupCtx (nameText n) ctx of
    Just (i, e)
      | Just info <- ceVarInfo e -> do
          let evidenceShift = i + 1
              refDict = shiftTerm evidenceShift 0 (vriMonadRefDict info)
              aTm = shiftTerm evidenceShift 0 (vriStoredTypeTerm info)
              refTm = CVar i
          case monadResultType (vriMonadType info) (vriStoredType info) of
            Just actionTy ->
              pure
                ( monadRefReadAction refDict aTm refTm
                , actionTy
                )
            Nothing -> do
              errAt sp "E_UNSUPPORTED" (Just "kappa.unsupported.deterministic")
                ("mutable variable '" <> nameText n <> "' uses a higher-order monad shape this implementation cannot apply for generated reads (§18.6.1)")
              anyHole ctx
      | otherwise -> do
          errMutableBinding sp "E_VAR_READ_OUTSIDE_DO" (nameText n) "current-value" [("sourceOperation", "generated read")]
            ("internal current-value read for '" <> nameText n <> "' does not refer to a mutable var binding (§18.6.1)")
          anyHole ctx
    Nothing -> do
      errAt (nameSpan n) "E_NAME_UNRESOLVED" (Just "kappa.name.unresolved")
        ("unresolved mutable var binding '" <> nameText n <> "' in generated current-value read")
      anyHole ctx

varReadBlocked :: Ctx -> Name -> Span -> CheckM (Term, Value)
varReadBlocked ctx n sp = do
  let (code, blockedBy, msg) = case ctxVarReadBlock ctx of
        Just VarReadCrossesBoundary ->
          ( "E_VAR_READ_CROSSES_BOUNDARY"
          , "expression-lifting-boundary"
          , "mutable variable '" <> nameText n
              <> "' is a current-value occurrence here, but elaborating the generated read would cross a user-written lambda, local function, quote, type, or delayed-evaluation boundary; bind a snapshot before the boundary, use an inner do block, or write 'ref "
              <> nameText n <> "' to select the reference cell (§18.3.1, §18.6.1)"
          )
        Just VarReadStaticPosition ->
          ( "E_VAR_IN_STATIC_POSITION"
          , "static-position"
          , "mutable variable '" <> nameText n
              <> "' is a current-value occurrence in a type, static, erased, implicit-search, or elaboration-time position that cannot perform object-phase reads; bind a snapshot first or write 'ref "
              <> nameText n <> "' where a reference cell is required (§18.3.1, §18.6.1)"
          )
        _ ->
          ( "E_VAR_READ_OUTSIDE_DO"
          , "outside-do"
          , "mutable variable '" <> nameText n
              <> "' is a current-value occurrence here, but this expression is not in a do-item lifting position; use 'ref "
              <> nameText n <> "' to select the reference cell, or bind a snapshot inside an explicit do (§18.3.1, §18.6.1)"
          )
  infoFields <- mutableBindingLookupFields ctx n "user-written"
  errMutableBinding sp code (nameText n) "current-value"
    (infoFields ++ [("sourceOperation", "current read"), ("repair", "ref " <> nameText n), ("blockedBy", blockedBy)])
    msg
  case lookupCtx (nameText n) ctx of
    Just (_, entry)
      | Just info <- ceVarInfo entry -> do
          -- Blocking the object-phase read invalidates the term, not the
          -- mutable binding's authenticated stored type. Preserve that type
          -- in recovery so an expected static classifier can still constrain
          -- the declaration that introduced the cell; returning 'anyHole'
          -- here loses the relation and causes derivative literal ambiguity.
          recovery <- freshMeta
          pure (recovery, vriStoredType info)
    _ -> anyHole ctx

-- | §3.2.2 typo-suggestion candidate index, bucketed by spelling length:
-- the import scope plus this module's own globals. A single dropped
-- import can leave thousands of references unresolved, each raising a
-- suggestion diagnostic; rebuilding and rescanning the whole scope per
-- diagnostic is O(Nerrors * Nscope). The index is built once here (on the
-- first unresolved name) and thereafter extended incrementally in
-- 'addGlobal' as the module's own globals appear, so the build is paid
-- once. Bucketing by length lets each diagnostic consult only the
-- length-compatible candidates (Levenshtein distance is at least the
-- length difference), bounding the per-error scan. Entering a new module
-- clears the index (Pipeline / TestHarness), since scope and module change.
moduleScopeNameIndex :: CheckM (Map Int (Set Text))
moduleScopeNameIndex = do
  st <- get
  case csScopeNameCache st of
    Just idx -> pure idx
    Nothing -> do
      let scope = Map.keys (csScope st)
          own = [nm | GName m nm <- Map.keys (csGlobals st), m == csModule st]
          idx = foldr insertScopeName Map.empty (scope ++ own)
      modify' $ \s -> s {csScopeNameCache = Just idx}
      pure idx

-- | The length-compatible §3.2.2 candidates for a target spelling: only
-- names whose length is within @threshold@ of the target can be within
-- edit distance @threshold@, so only those buckets are gathered.
scopeNamesNear :: Text -> Int -> CheckM [Text]
scopeNamesNear target threshold = do
  idx <- moduleScopeNameIndex
  let tlen = T.length target
      buckets =
        [ s
        | len <- [tlen - threshold .. tlen + threshold]
        , Just s <- [Map.lookup len idx]
        ]
  pure (Set.toList (Set.unions buckets))

-- | Does a name resolve at all (locals or globals)? Used for §6.3.4
-- literal-prefix resolution, which is ordinary term name resolution.
prefixResolves :: Ctx -> Text -> CheckM Bool
prefixResolves ctx n =
  case lookupCtx n ctx of
    Just _ -> pure True
    Nothing -> do
      mg <- lookupGlobalName n
      pure (maybe False (const True) mg)

reportInvalidLevelTerm :: Span -> Text -> Term -> Text -> CheckM ()
reportInvalidLevelTerm sp source normalized reason =
  report $
    withPayload
      ( withPayloadField "sourceExpression" source $
          withPayloadField "expectedClassifier" "TypeLevel" $
            withPayloadField "normalizedExpression" (renderTerm normalized) $
              withPayloadField "reason" reason $
                withPayloadField "transparentReductionAttempted" "true" $
                  withPayloadField "normalizationBlockedBy" reason $
                    payloadKind "universe-level-expression"
      ) $
      diag SevError StageElaborate "E_UNIVERSE_LEVEL_EXPRESSION"
        (Just "kappa.universe.level-expression") sp
        "a Type index must be a stable, total, serializable TypeLevel term (§11.1.1)"

-- | Select the least available explicit ceiling that proves an upper bound
-- for a component classifier. This deliberately consults only scoped proof
-- assumptions; ω is never inserted as an automatic ceiling.
ceilingLevel :: Ctx -> Level -> Level
ceilingLevel ctx lvl
  | null (levelVars normalized) && null (levelFields normalized) = normalized
  | otherwise = case candidates of
      [] -> normalized
      first : rest -> foldl choose first rest
  where
    normalized = normalizeLevel lvl
    edges = [(normalizeLevel lhs, normalizeLevel rhs) | (lhs, rhs) <- assumptionsList (ctxLevelAssumptions ctx)]
    -- Every level constructor is monotone. Closing a bounded number of rounds
    -- under contextual substitution derives, for example, `succ u <= succ ω`
    -- from `u <= ω` without inventing a global omega ceiling. The round bound
    -- prevents a cyclic/growing assumption from creating an infinite term
    -- sequence; the exact solver still validates every selected candidate.
    closure = take (length edges + 2) (iterate step [normalized])
    step prior = nub (prior ++ [replaceLevel lhs rhs term | term <- prior, (lhs, rhs) <- edges])
    candidates =
      nub
        [ candidate
        | candidate <- concat closure ++ map snd edges
        , candidate /= normalized
        , proveLevelLeq (ctxLevelAssumptions ctx) normalized candidate == Proved
        ]
    choose best candidate
      | proveLevelLeq (ctxLevelAssumptions ctx) candidate best == Proved = candidate
      | otherwise = best

    replaceLevel lhs rhs term
      | normalizeLevel term == lhs = rhs
      | otherwise = normalizeLevel $ case term of
          LSucc a -> LSucc (replaceLevel lhs rhs a)
          LAdd a b -> LAdd (replaceLevel lhs rhs a) (replaceLevel lhs rhs b)
          LMax a b -> LMax (replaceLevel lhs rhs a) (replaceLevel lhs rhs b)
          other -> other

registerLevelField :: Ctx -> Text -> Value -> CheckM Ctx
registerLevelField ctx field ty = do
  isLevel <- isTypeLevelValue ty
  if not isLevel
    then pure ctx
    else do
      fieldId <- gets csNextLevelFieldId
      modify' $ \st -> st {csNextLevelFieldId = fieldId + 1}
      pure ctx {ctxLevelFieldIds = Map.insert field fieldId (ctxLevelFieldIds ctx)}

formationContribution :: FormationMode -> Level -> Level
formationContribution formation classifier = case formation of
  FormationParametric -> LZero
  FormationOrdinary -> classifier

-- | Replace an internally-bound classifier by the least explicit ceiling
-- justified by assumptions in scope. The caller still verifies that no local
-- level identity escaped; this helper never invents an omega ceiling.
formationCeiling :: Ctx -> Level -> Level
formationCeiling ctx classifier
  | assumptionsConsistent (ctxLevelAssumptions ctx) = ceilingLevel ctx classifier
  | otherwise = LZero

-- | Raise a component type to the least scoped formation ceiling and retain
-- the exact solver derivation in KCore. Parametric components do not call this
-- helper: their classifier contributes zero by the modal formation rule and
-- no cumulative use of the component term occurred.
formationCeilingTerm :: Ctx -> Level -> Term -> (Term, Level)
formationCeilingTerm ctx classifier term =
  let target = formationCeiling ctx classifier
      evidence = solverUniverseEvidence (ctxLevelAssumptions ctx) classifier target
   in (universeLift evidence term, target)

reportUnboundedTelescope :: Ctx -> Span -> Text -> Text -> Level -> CheckM ()
reportUnboundedTelescope ctx sp kind0 component classifier = do
  -- An inconsistent scoped proof context has already received its primary
  -- universe-constraint diagnostic. It proves no ceiling (the pure solver
  -- fails closed on inconsistent assumptions), and reporting an additional
  -- unbounded telescope here would only be recovery noise.
  when (assumptionsConsistent (ctxLevelAssumptions ctx)) $ do
    let assumptions = renderLevelAssumptions (ctxLevelAssumptions ctx)
    let kind = case kind0 of
          "record telescope" -> "record"
          "existential telescope" -> "exists"
          "forall telescope" -> "pi"
          "dependent function" -> "pi"
          other -> other
        escaping = case levelVars classifier of
          v : _ -> "level#" <> T.pack (show v)
          [] -> case levelFields classifier of
            (_, field) : _ -> "this." <> field
            [] -> "unknown"
        repair = "add an earlier erased bound such as (@0 p : i < κ)"
    report $
      withPayload
        ( withPayloadField "telescopeKind" kind $
            withPayloadField "escapingVariable" escaping $
              withPayloadField "componentType" component $
                withPayloadField "componentClassifier" ("Type " <> renderLevel classifier) $
                  withPayloadField "levelAssumptions" assumptions $
                    withPayloadField "attemptedCeiling" "none" $
                      withPayloadField "reason" "no ceiling independent of the telescope variable exists" $
                        withPayloadField "binderOrigin" (T.pack (show sp)) $
                          withPayloadField "componentOrigin" (T.pack (show sp)) $
                            withPayloadField "suggestedRepair" repair $
                              payloadKind "universe-unbounded-telescope"
        ) $
        diag SevError StageElaborate "E_UNIVERSE_UNBOUNDED_TELESCOPE"
          (Just "kappa.universe.unbounded-telescope") sp
          ( kind0 <> " component '" <> component <> "' has classifier Type "
              <> renderLevel classifier
              <> " mentioning a level bound inside the telescope, with no outer-scope ceiling; "
              <> repair <> " (§11.1.2.8)"
          )

-- | Replay an assumption that has already crossed a source validation
-- boundary. Post-check annotation passes need the scoped solver context, but
-- must not diagnose the same source binder a second time.
replayCheckedLevelAssumption :: Ctx -> Maybe (Level, Level) -> Ctx
replayCheckedLevelAssumption ctx = \case
  Nothing -> ctx
  Just (lhs, rhs) ->
    ctx
      { ctxLevelAssumptions =
          insertAssumption lhs rhs (ctxLevelAssumptions ctx)
      }

-- | A synthesized erased proof metavariable is an obligation, not yet an
-- authority.  Its proposition may scope the dependent remainder of the
-- application, but an inconsistent proposition must not be diagnosed as
-- though the user had supplied established evidence.  The owning occurrence
-- or schema-lift check remains responsible for the dedicated failure.  Once
-- the proof term is solved, use the ordinary checked-assumption path.
extendLevelAssumptionFromSynthesized
  :: Span -> Ctx -> Maybe (Level, Level) -> Term -> CheckM Ctx
extendLevelAssumptionFromSynthesized sp ctx assumption proof = do
  st <- get
  if null (unsolvedMetasOf st proof)
    then extendLevelAssumption sp ctx assumption
    else pure $ case assumption of
      Nothing -> ctx
      Just (lhs, rhs) ->
        ctx {ctxLevelAssumptions = insertAssumption lhs rhs (ctxLevelAssumptions ctx)}

-- | §16.3.2 resolve an expression hole to its shared term metavariable and
-- type metavariable, recording this occurrence's span.
--
-- For an anonymous hole (@_@, 'Nothing') this is just 'anyHole': @_@ always
-- introduces a fresh hole, so anonymous holes are never tracked and never
-- shared. For a named hole (@?name@) all occurrences within one enclosing
-- declaration refer to the SAME metavariable (one @HoleId@): the first
-- occurrence creates the shared metas and later occurrences reuse them, so
-- the occurrences denote the same unknown and must elaborate at
-- definitionally equal expected types. Reset per declaration in
-- 'elabLetDecl'. Returns the shared metas plus the 'NamedHole' record (when
-- named) so a check-direction inconsistency can cite every occurrence.
holeMetas :: Ctx -> Maybe Name -> Span -> CheckM (Term, Value, Maybe NamedHole)
holeMetas ctx Nothing _ = do
  (m, ty) <- anyHole ctx
  pure (m, ty, Nothing)
holeMetas ctx (Just n) sp = do
  let nm = nameText n
  existing <- gets (Map.lookup nm . csHoles)
  case existing of
    Just nh -> do
      let nh' = nh {nhOccs = sp : nhOccs nh}
      modify' $ \st -> st {csHoles = Map.insert nm nh' (csHoles st)}
      pure (nhTerm nh', nhType nh', Just nh')
    Nothing -> do
      m <- freshMeta
      tyTerm <- freshMeta
      ty <- evalIn ctx tyTerm
      let nh =
            NamedHole
              { nhTerm = m
              , nhType = ty
              , nhTypeTerm = tyTerm
              , nhDepth = ctxLen ctx
              , nhOccs = [sp]
              }
      modify' $ \st -> st {csHoles = Map.insert nm nh (csHoles st)}
      pure (m, ty, Just nh)

-- | The display spelling of a hole (§16.3.2): @?name@ for a named hole,
-- @_@ for the anonymous hole.
holeSpelling :: Maybe Name -> Text
holeSpelling = maybe "_" (("?" <>) . nameText)

-- | §3.2.4 @E_HOLE_UNSOLVED@: report that an expression hole remains
-- unsolved, stating its expected type. Shared by both elaboration
-- directions so a hole reports the same payload whether it was inferred
-- (expected type = a fresh meta, rendered @_@ until solved) or checked
-- (expected type = the known checking type). The type term is zonked so a
-- solved expected type is shown concretely and an unsolved one renders as
-- the stable hole @_@ (§3.1.11).
reportUnsolvedHole :: Ctx -> Maybe Name -> Span -> Term -> CheckM ()
reportUnsolvedHole ctx mn =
  reportUnsolvedHoleAt (ctxLen ctx) (holeSpelling mn)

-- | Record the checked classifier of a named hole's shared term meta.
-- Arithmetic principalization and declaration-local generalization may assign
-- only metas whose creation-site classifier is known exactly; the fact that a
-- source token happened to be written as @?name@ is not type authority.
recordHoleClassifier :: Ctx -> Term -> Value -> CheckM ()
recordHoleClassifier ctx term classifier =
  case term of
    CMeta meta -> do
      classifierTerm <- quoteIn ctx classifier
      modify' $ \st ->
        st
          { csMetaClassifiers =
              Map.insertWith
                (\_ existing -> existing)
                meta
                (MetaClassifier (ctxLen ctx) classifierTerm Nothing)
                (csMetaClassifiers st)
          }
    _ -> pure ()

-- | §3.2.4 @E_HOLE_INCONSISTENT_EXPECTED_TYPE@ / family
-- @kappa.hole.inconsistent@: emitted when two occurrences of one named
-- hole receive expected types that are not definitionally equal
-- (unifying the shared type metavariable with the second occurrence's
-- expected type failed). The diagnostic cites every occurrence of the
-- hole (§16.3.2 MUST) and both distinct expected types.
reportInconsistentHole :: Ctx -> Name -> Span -> NamedHole -> Value -> CheckM ()
reportInconsistentHole ctx n sp nh expected = do
  -- the type the earlier occurrences agreed on (the shared meta, now
  -- solved to the first occurrence's expected type) versus this one.
  priorT <- quoteIn ctx (nhType nh) >>= zonkTermM (ctxLen ctx)
  thisT <- quoteIn ctx expected >>= zonkTermM (ctxLen ctx)
  let holeName = "?" <> nameText n
      priorR = renderTerm priorT
      thisR = renderTerm thisT
      -- every occurrence (nhOccs holds them most-recent first, including
      -- this one); cite each as a use-site related origin (§3.1.1A).
      rels = [related RoleUseSite osp ("occurrence of " <> holeName) | osp <- reverse (nhOccs nh)]
  report $
    withRelateds rels $
      withPayload
        ( withPayloadField "hole" holeName $
            withPayloadField "expected" priorR $
              withPayloadField "expected2" thisR $
                payloadKind "hole-inconsistent"
        )

        $ diag SevError StageElaborate "E_HOLE_INCONSISTENT_EXPECTED_TYPE"
            (Just "kappa.hole.inconsistent") sp
            ( "named hole " <> holeName <> " is used at inconsistent expected types: "
                <> priorR <> " and " <> thisR <> " (§16.3.2)"
            )

-- | Exact implicit locals and projection chains rooted in them whose inferred
-- classifiers are authenticated trait goals. Coherent evidence is not
-- restricted to a whole implicit local: a supertrait projection is itself an
-- evidence value and may be the exact dictionary captured by an overloaded
-- operation. The generic typed projection oracle is supplemented by the
-- standard-operation decoder, whose resolved operation identity and checked
-- telescope independently recover the exact evidence slot even when a nested
-- supertrait projection cannot be reconstructed in isolation. Restricting
-- candidates to those two typed evidence shapes avoids turning arbitrary
-- endpoint subterms into new instance-search triggers. Nested-binder nodes and
-- terms whose classifier cannot be reconstructed fail closed.
coherentTraitEvidenceTerms
  :: Ctx
  -> [Term]
  -> CheckM [(Term, Value)]
coherentTraitEvidenceTerms ctx endpoints = do
  let depth = ctxLen ctx
      candidates =
        nub
          [ node
          | endpoint <- endpoints
          , (nodeDepth, node) <-
              foldTermWithDepth
                (\nodeDepth node -> [(nodeDepth, node)])
                depth
                endpoint
          , nodeDepth == depth
          , implicitEvidenceProjection node
          ]
  projected <-
    fmap catMaybes . forM candidates $ \candidate ->
      coreTermClassifierInCtx ctx candidate >>= \case
        Nothing -> pure Nothing
        Just evidenceType -> do
          authenticated <- isTraitGoal evidenceType
          pure
            ( if authenticated
                then Just (candidate, evidenceType)
                else Nothing
            )
  operationEvidence <-
    concat <$> mapM (coherentArithmeticEvidenceOccurrences ctx) endpoints
  pure
    ( nubBy
        (\(left, _) (right, _) -> left == right)
        (projected ++ operationEvidence)
    )
  where
    implicitEvidenceProjection = \case
      CVar index ->
        maybe
          False
          ceImplicitLocal
          (listToMaybe (drop index (ctxEntries ctx)))
      CProjM _ receiver _ -> implicitEvidenceProjection receiver
      CProjAtM _ receiver _ _ -> implicitEvidenceProjection receiver
      CSealE _ receiver -> implicitEvidenceProjection receiver
      _ -> False

-- | Recover the classifier of an already checked Core term without freshening
-- any declaration occurrence. This is an observational query over the current
-- lexical context; unsupported terms return 'Nothing' and cannot influence
-- elaboration state.
coreTermClassifierInCtx :: Ctx -> Term -> CheckM (Maybe Value)
coreTermClassifierInCtx ctx term = do
  state <- get
  evaluator <- ec_
  pure
    ( observationTermTypeAt
        state
        evaluator
        (ctxLen ctx)
        (map observationBinding (ctxEntries ctx))
        term
    )
  where
    observationBinding entry =
      ObservationBinding
        { obMode = ceMode entry
        , obOrigin = Nothing
        , obType = Just (ceType entry)
        , obUniverses = luiTelescope <$> ceLocalUniverses entry
        , obDefinition = Nothing
        }

termContainsRoot :: Term -> Term -> Bool
termContainsRoot root =
  getAny
    . foldTermWithDepth
      (\depth node -> Any (node == shiftTerm depth 0 root))
      0

replaceTermRoot :: Term -> Term -> Term -> Term
replaceTermRoot fromTerm toTerm =
  mapTermWithDepth
    (\depth node ->
      if node == shiftTerm depth 0 fromTerm
        then Just (shiftTerm depth 0 toTerm)
        else Nothing)
    0

nominalArgumentDomain
  :: Ctx
  -> Map GName GlobalDef
  -> GName
  -> [Level]
  -> [(Icit, Term)]
  -> Int
  -> CheckM (Maybe Value)
nominalArgumentDomain ctx definitions global universes arguments target =
  case Map.lookup global definitions of
    Nothing -> pure Nothing
    Just definition -> do
      (_, familyType) <- specializeGlobalAt ctx global definition universes
      go 0 familyType arguments
  where
    go _ _ [] = pure Nothing
    go index familyType ((argumentIcit, argumentTerm) : rest) = do
      forced <- forceM familyType
      case forced of
        VPiEvidenceM
          _
          _
          binderIcit
          _
          _
          _
          _
          _
          domain
          closure
            | binderIcit == argumentIcit ->
                if index == target
                  then pure (Just domain)
                  else do
                    argument <- evalIn ctx argumentTerm
                    result <- clApp closure argument
                    go (index + 1) result rest
        _ -> pure Nothing

-- | Reconcile only hidden-universe metas authenticated as fresh declaration
-- occurrence specializations.  These metas are elaboration choices rather
-- than source universe parameters, so aliasing a bare occurrence meta to the
-- corresponding level of the same nominal family is principal.  Complex
-- equations and every source/generalizable meta remain rigid here; the
-- ordinary universe solver owns those cases.
alignNominalOccurrenceUniverses :: [Level] -> [Level] -> CheckM Bool
alignNominalOccurrenceUniverses actual expected = do
  state <- get
  let installed = csLevelAssignments state
      occurrenceMetas = csLevelInstantiationMetas state
      normalizeWith aliases =
        normalizeLevel
          . substituteLevelMetas (Map.union aliases installed)
      derive aliases [] = Just aliases
      derive aliases ((actualLevel0, expectedLevel0) : rest) =
        let actualLevel = normalizeWith aliases actualLevel0
            expectedLevel = normalizeWith aliases expectedLevel0
         in if actualLevel == expectedLevel
              then derive aliases rest
              else
                assign aliases actualLevel expectedLevel >>= \aliases' ->
                  derive aliases' rest
      assign aliases (LMeta actualMeta) expectedLevel
        | actualMeta `Set.member` occurrenceMetas
        , actualMeta `notElem` levelMetas expectedLevel =
            Just (Map.insert actualMeta expectedLevel aliases)
      assign aliases actualLevel (LMeta expectedMeta)
        | expectedMeta `Set.member` occurrenceMetas
        , expectedMeta `notElem` levelMetas actualLevel =
            Just (Map.insert expectedMeta actualLevel aliases)
      assign _ _ _ = Nothing
  case derive Map.empty (zip actual expected) of
    Nothing -> pure False
    Just aliases -> do
      unless (Map.null aliases) (installLevelAssignments aliases)
      pure True

-- | Decompose only a checked declaration with nominal identity. This shared
-- recognizer is intentionally exact: a source spelling, constructor name, or
-- structurally similar application cannot enter nominal result planning or
-- proof transport.
declaredNominalApplication
  :: Map GName GlobalDef
  -> Map GName DataInfo
  -> Term
  -> Maybe (GName, [Level], [(Icit, Term)])
declaredNominalApplication definitions dataFamilies term =
  let (headTerm, arguments) = spineOfTerm (stripIdentityWrappers term)
   in case stripIdentityWrappers headTerm of
        CGlobal global universes
          | Map.member global dataFamilies
              || maybe False (isJust . gdNominalSummary)
                   (Map.lookup global definitions) ->
              Just (global, universes, arguments)
        _ -> Nothing

-- | Cheap semantic candidate filter for the implicit refinement conversion.
-- Ordinary conversion failure is a hot path, so it must not launch full
-- instance/universe search when no 'RefinementView' dictionary can possibly
-- exist. Checked instance heads provide the nominal discriminator; a
-- variable-headed instance remains a conservative wildcard. Local evidence is
-- admitted only when its checked trait identity is 'RefinementView' or reaches
-- it through the declared supertrait graph.
refinementViewMayResolve :: Ctx -> Value -> CheckM Bool
refinementViewMayResolve ctx target = do
  state <- get
  targetTerm <- quoteIn ctx target
  let refinementTrait = gPrel "RefinementView"
      targetHead = nominalDataHead targetTerm
      instanceCandidate entry
        | ieTrait entry /= refinementTrait = False
        | otherwise =
            case ieHead entry of
              [headTerm] ->
                case nominalDataHead headTerm of
                  Nothing -> True
                  Just candidateHead -> Just candidateHead == targetHead
              _ -> False
      reachesRefinement seen trait
        | trait == refinementTrait = True
        | trait `Set.member` seen = False
        | otherwise =
            case Map.lookup trait (csTraits state) of
              Nothing -> False
              Just info ->
                any
                  ( maybe False
                      (reachesRefinement (Set.insert trait seen))
                      . traitClosureHead
                      . snd
                  )
                  (tiSupers info)
  localCandidates <-
    forM
      [entry | entry <- ctxEntries ctx, ceImplicitLocal entry]
      $ \entry ->
        forceM (ceType entry) >>= \case
          VGlobI trait _ _ ->
            pure
              ( Map.member trait (csTraits state)
                  && reachesRefinement Set.empty trait
              )
          _ -> pure False
  pure (any instanceCandidate (csInstances state) || or localCandidates)
  where
    traitClosureHead = \case
      CLamM _ _ _ _ body -> traitClosureHead body
      CApp _ function _ -> traitClosureHead function
      CUniverseLift _ _ _ term -> traitClosureHead term
      CSchemaLift _ _ _ _ _ _ _ _ term -> traitClosureHead term
      CGlobal global _ -> Just global
      CGlob global -> Just global
      _ -> Nothing

recordImplicitExpressionDemand :: Span -> Q -> CheckM ()
recordImplicitExpressionDemand site quantity =
  modify' $ \state ->
    state
      { csImplicitExpressionDemands =
          Map.insert site quantity (csImplicitExpressionDemands state)
      }

pendingComponentTypeKey :: Int -> [MetaId] -> CheckState -> Text
pendingComponentTypeKey depth metas state =
  T.intercalate
    "\x1f"
    [ maybe "?" renderStructuralTermKey
        (resolvedMetaCore state (ecOf state) depth meta)
    | meta <- metas
    ]

pendingEntrySite :: PendingEvidenceEntry -> Span
pendingEntrySite (_, _, site, _, _) = site

pendingEntryFacts :: PendingEvidenceEntry -> [ScopedBoolFact]
pendingEntryFacts (_, _, _, _, facts) = facts

pendingEntryIsUnsolved :: PendingEvidenceEntry -> CheckM Bool
pendingEntryIsUnsolved entry =
  gets $ \state ->
    case Map.lookup (pendingEntryMeta entry) (csMetas state) of
      Just Nothing -> True
      _ -> False

pendingEntryIsTrait :: PendingEvidenceEntry -> CheckM Bool
pendingEntryIsTrait entry =
  refreshPendingEntry entry >>= isTraitGoal

pendingTraitArgumentsRigid :: Ctx -> Value -> CheckM Bool
pendingTraitArgumentsRigid ctx goal =
  forceM goal >>= \case
    VGlobI trait _ arguments -> do
      state <- get
      case traitSemanticSpineIn state trait arguments of
        Nothing -> pure False
        Just semanticArguments ->
          pure $
            all
              ( \(_, argument) ->
                  null
                    ( unsolvedMetasOf
                        state
                        (quote (ecOf state) (ctxLen ctx) argument)
                    )
              )
              semanticArguments
    _ -> pure False

-- Expected types must not silently choose a non-identity declaration schema
-- for a recursive call (§11.1.2.3A).  Recognize only the structurally direct
-- case: the recursive declaration's finalized result is the same nominal
-- family at its own declaration parameters, and the omitted occurrence was
-- recorded at that identity spine.  The SCC classifier remains the sole site
-- that emits the portable recursive-schema diagnostic.
recordExpectedImplicitRecursiveSchema :: Ctx -> Span -> Term -> Value -> Value -> CheckM Bool
recordExpectedImplicitRecursiveSchema ctx site term actual0 expected0 = do
  actual <- forceM actual0
  expected <- forceM expected0
  st <- get
  ec <- ec_
  let occurrenceHead = termGlobalHeadWithUniverses term
      sameArguments left right =
        length left == length right
          && and
            [ leftIcit == rightIcit && convertible ec (ctxLen ctx) leftValue rightValue
            | ((leftIcit, leftValue), (rightIcit, rightValue)) <- zip left right
            ]
      resultSchema definition = do
        let result = piResult (globalCoreType ec definition)
            (headTerm, _) = spineOfTerm result
        case headTerm of
          CGlobal family levels -> Just (family, map normalizeLevel levels)
          _ -> Nothing
      piResult = \case
        CPiBoundM _ _ _ _ _ _ _ body -> piResult body
        result -> result
  case (occurrenceHead, actual, expected) of
    ( Just (callee, occurrenceLevels)
      , VGlobI sourceFamily sourceLevels sourceArguments
      , VGlobI targetFamily targetLevels targetArguments
      )
        | sourceFamily == targetFamily
        , map normalizeLevel sourceLevels /= map normalizeLevel targetLevels
        , sameArguments sourceArguments targetArguments
        , Just calleeDefinition <- Map.lookup callee (csGlobals st)
        , let arity = dutParameterCount (gdUniverses calleeDefinition)
        , arity > 0
        , resultSchema calleeDefinition
            == Just (sourceFamily, map LParam [0 .. arity - 1])
        , map normalizeLevel occurrenceLevels == map normalizeLevel sourceLevels
        , Just caller <- csActiveUniverseDefinition st
        , Just sourceOccurrence <- listToMaybe
            [ occurrence
            | occurrence <- Map.findWithDefault
                []
                caller
                (csRecursiveSchemaOccurrencesByCaller st)
            , rsoCallee occurrence == callee
            , not (rsoExplicit occurrence)
            , map normalizeLevel (rsoLevels occurrence) == map normalizeLevel occurrenceLevels
            ] -> do
              assumptions <- effectiveLevelAssumptions ctx
              modify' $ \current ->
                insertRecursiveSchemaOccurrence
                  ( RecursiveSchemaOccurrence
                      (rsoCaller sourceOccurrence)
                      callee
                      targetLevels
                      False
                      assumptions
                      site
                  )
                  current
              pure True
    _ -> pure False

termGlobalHeadWithUniverses :: Term -> Maybe (GName, [Level])
termGlobalHeadWithUniverses = \case
  CApp _ function _ -> termGlobalHeadWithUniverses function
  CUniverseLift _ _ _ inner -> termGlobalHeadWithUniverses inner
  CSchemaLift _ _ _ _ _ _ _ _ inner -> termGlobalHeadWithUniverses inner
  CGlobal global universes -> Just (global, universes)
  _ -> Nothing

-- §6.1.6: an out-of-scope numeric-literal suffix is a compile-time
-- name-resolution error identifying the missing suffix name.
badLiteralSuffix :: Ctx -> Name -> CheckM (Term, Value)
badLiteralSuffix ctx name = do
  let n = nameText name
      sp = nameSpan name
  errAt sp "E_NAME_UNRESOLVED" (Just "kappa.name.unresolved")
    ("the numeric-literal suffix '" <> n <> "' does not resolve to a term in scope (Spec §6.1.6)")
  anyHole ctx

-- ── Implicit resolution (§16.3.3) ────────────────────────────────────

-- | Exact arithmetic-operation dictionary occurrences in one checked Core
-- proposition. The global operation identity and its checked implicit
-- telescope authenticate the trait/carrier/evidence slots; no source spelling
-- or projected field name is used as authority here.
coherentArithmeticEvidenceOccurrences
  :: Ctx
  -> Term
  -> CheckM [(Term, Value)]
coherentArithmeticEvidenceOccurrences ctx root =
  fmap catMaybes . forM candidates $ \(trait, carrierTerm, dictionary) -> do
    let depth = ctxLen ctx
    if not (termScopedAt depth carrierTerm && termScopedAt depth dictionary)
      then pure Nothing
      else
        coreTermClassifierInCtx ctx dictionary >>= \case
          Nothing -> pure Nothing
          Just evidenceType -> do
            authenticated <- isTraitGoal evidenceType
            exactTrait <-
              forceM evidenceType >>= \case
                VGlobN evidenceTrait _ -> pure (evidenceTrait == trait)
                _ -> pure False
            pure
              ( if authenticated && exactTrait
                  then Just (dictionary, evidenceType)
                  else Nothing
              )
  where
    candidates =
      nubBy
        (\(leftTrait, leftCarrier, leftDictionary)
           (rightTrait, rightCarrier, rightDictionary) ->
            leftTrait == rightTrait
              && leftCarrier == rightCarrier
              && leftDictionary == rightDictionary)
        ( foldTerm
            (maybeToList . standardArithmeticDirectProvider)
            (const [])
            root
        )
