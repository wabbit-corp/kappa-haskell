-- | Strict positivity for data declarations (Spec §10.4).
--
-- A data type may not refer to itself in a negative position (left of an
-- arrow); allowing it would let non-termination in through the back door and
-- break soundness. These are the helpers that decide the question.
--
-- Carved out of "Kappa.Check" as part of splitting that module; see
-- "Kappa.Check.Types" for the shared data dictionary and docs\/CONCEPTS.md
-- for the vocabulary these assume.
module Kappa.Check.Positivity
  ( backendIntrinsicSatisfies
  , classifyRecursiveSchemaOccurrences
  , declarationUniverseName
  , extendSourceDeclarationTeleCtx
  , extendTeleCtx
  , finalizeDeferredSignatureHoles
  , finalizeGeneratedTelescope
  , finalizeInferredClassifier
  , finalizeNamedHoles
  , finalizeSourceDeclarationTelescope
  , gateUnsafe
  , gateUnsafeResolved
  , inferredMeasureSccOKWithEdges
  , inoutParamsFromBinders
  , installTraitNominalSummary
  , internalizeUniverseSchema
  , measureCtxFromSigIn
  , noteDefinition
  , occursGlobal
  , peelTermParamsAt
  , placesToThis
  , positivityPass
  , provisionalSourceDeclarationParam
  , recordAudit
  , recordDefinitionInoutParams
  , recordDefinitionReceiverParams
  , recordInoutParams
  , recordSignatureInoutParams
  , recordSignatureReceiverParams
  , rejectAllInoutBinders
  , rejectInoutBinderContext
  , relationCanonicalKey
  , relationExpectedType
  , relationWellFoundedEvidence
  , reportUnverifiedTermination
  , setGlobalReducible
  , sigHeadNames
  , signatureBinders
  , superFieldName
  , teleCtx
  , validateUniverseVarianceApplicability
  , withActiveUniverseDefinitionRaw
  , withLocalDeclarationUniverseSchema
  , withNamedCallableInoutSignature
  , withNestedUniverseSchemaParameters
  , withRecursiveSchemaOccurrenceRecording
  , withSccOpaque
  , withUniverseSchemaParameters
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

positivityPass :: [Decl] -> CheckM ()
positivityPass decls = do
  st <- get
  let dataDecls = [(dd, sp) | DData _ dd sp <- decls]
  group <- catMaybes <$> mapM (gatherPosData st) dataDecls
  unless (null group) $ do
    let groupNames = Set.fromList (map pdName group)
        dependencySccs =
          stronglyConnComp
            [ (d, pdName d, Set.toList (Set.intersection groupNames (Set.unions (map (globalsOfTerm . pfType) (pdFields d)))))
            | d <- group
            ]
        recursiveGroupOf =
          Map.fromList
            [ (pdName d, names)
            | scc <- dependencySccs
            , let members = case scc of
                    AcyclicSCC d -> [d]
                    CyclicSCC ds -> ds
                  names = Set.fromList (map pdName members)
            , d <- members
            ]
        -- prior (non-group) signatures: accepted data types and the
        -- strictly-positive built-in/imported carriers
        priorSig = csPositivity st
        -- fixed-point over the group for the parameter-positivity
        -- signatures (§10.4). The recompute operator is monotone in the
        -- "more positive" direction (a parameter known positive lets a
        -- recursive index recurse strictly-positively instead of
        -- demanding the parameter be absent), so the signature we want is
        -- its GREATEST fixed point: start every parameter positive and
        -- iterate downward until stable. (A least fixed point from
        -- all-non-positive degenerates — e.g. it would mark 'a' in
        -- 'data Tree a = ... Branch (Tree a) a (Tree a)' as non-positive,
        -- wrongly. The rejection judgement below is computed afterwards
        -- against the converged signatures, per §10.4.)
        sig0 = Map.fromList [(pdName d, replicate (pdParamCount d) True) | d <- group]
        converged = fixpoint groupNames priorSig group sig0
        fullSig = Map.union converged priorSig
    -- record the converged group signatures for later declarations
    modify' $ \s -> s {csPositivity = Map.union converged (csPositivity s)}
    -- reject any group member with a non-strictly-positive occurrence
    forM_ group $ \d ->
      forM_ (pdFields d) $ \fld ->
        let recursiveNames = Map.findWithDefault (Set.singleton (pdName d)) (pdName d) recursiveGroupOf
         in unless (spPositive recursiveNames fullSig (pfType fld)) $
          errOncePerSpan (pdSpan d) "E_DATA_NOT_STRICTLY_POSITIVE" (Just "kappa.termination.failure")
            ( "data type '" <> gnameText (pdName d)
                <> "' is not strictly positive: it occurs in a negative or non-admissible position"
                <> " in a constructor argument type (Spec §10.4)"
            )

-- | Collect the field types of one data declaration from the elaborated
-- 'CtorInfo' types. Returns 'Nothing' for a type with no recorded data
-- info (should not happen for a 'DData' that elaborated).
gatherPosData :: CheckState -> (DataDecl, Span) -> CheckM (Maybe PosData)
gatherPosData st (DataDecl n _ _ _, sp) = do
  g <- ownName n
  case Map.lookup g (csDatas st) of
    Nothing -> pure Nothing
    Just di -> do
      let pc = diParamCount di
          ctorTys = [ciType ci | cg <- diCtors di, Just ci <- [Map.lookup cg (csCtors st)]]
          rawFlds = concatMap (posCtorFieldTypes pc) ctorTys
      flds <- forM rawFlds $ \fld ->
        PosField (pfDepth fld) <$> normalizeTermAt (pfDepth fld) (pfType fld)
      pure (Just (PosData g pc flds sp))

-- | Peel 'pc' leading parameter binders, then collect each remaining
-- 'CPi' domain (a constructor field type) together with the binder depth
-- in scope at that domain.
posCtorFieldTypes :: Int -> Term -> [PosField]
posCtorFieldTypes pc = peelParams pc
  where
    peelParams 0 t = peelFields pc t
    peelParams k (CPi _ _ _ _ _ b) = peelParams (k - 1) b
    peelParams _ _ = [] -- malformed; nothing to check
    peelFields depth = \case
      CPi _ _ _ _ a b -> PosField depth a : peelFields (depth + 1) b
      _ -> [] -- the result head 'T params' carries no fields

-- | Fixed-point iteration of the group's parameter-positivity signatures
-- (§10.4): recompute every member's signature from the current
-- signatures until nothing changes.
fixpoint :: Set GName -> Map GName [Bool] -> [PosData] -> Map GName [Bool] -> Map GName [Bool]
fixpoint groupNames priorSig group = go
  where
    go sig =
      let sig' = Map.fromList [(pdName d, recomputeSig groupNames (Map.union sig priorSig) d) | d <- group]
       in if sig' == sig then sig else go sig'

-- | Recompute one data type's parameter-positivity signature: parameter
-- @j@ is positive iff every occurrence of the corresponding de Bruijn
-- variable in every field type is in a strictly positive position
-- (§10.4).
recomputeSig :: Set GName -> Map GName [Bool] -> PosData -> [Bool]
recomputeSig groupNames sig d =
  [ all (\fld -> varPositive groupNames sig (pfDepth fld - 1 - j) (pfType fld)) (pdFields d)
  | j <- [0 .. pdParamCount d - 1]
  ]

-- | Is the parameter-positivity signature of an applied head 'F' known
-- and is 'F' admissible in a strictly positive position? Returns the
-- per-argument positivity flags when admissible (§10.4 admissibility).
admissibleSig :: Set GName -> Map GName [Bool] -> Term -> Maybe [Bool]
admissibleSig groupNames sig = \case
  CGlob g
    | g `Set.member` groupNames -> Map.lookup g sig -- a group member (its evolving signature)
    | otherwise -> Map.lookup g sig -- a prior data type / built-in carrier with a recorded signature
  _ -> Nothing

-- | Split a term into its head and argument spine.
posSpine :: Term -> (Term, [Term])
posSpine = go []
  where
    go acc (CApp _ f a) = go (a : acc) f
    go acc t = (t, acc)

-- | §10.4 strict positivity of a constructor field type with respect to
-- a /target/ supplied as the predicate @hits@ (does this exact subterm
-- mention the target as its head?) plus @occurs@ (does the target occur
-- anywhere in this subterm?). The walk implements: the argument type
-- itself; @X -> U@ / @(x : X) -> U@ with the target absent from @X@ and
-- strictly positive in @U@; and an admissible application @F A1 .. An@
-- in which the target occurs strictly positively only in the @Ai@ whose
-- parameter is marked positive (and not at all in the others).
posWalk
  :: Set GName
  -> Map GName [Bool]
  -> (Int -> Term -> Bool) -- ^ @occurs shift t@: does the target occur in @t@ (shift = extra binders since the top)?
  -> (Int -> Term -> Bool) -- ^ @isBareTarget shift t@: is @t@ exactly a bare occurrence of the target (the "argument type itself")?
  -> Int -- ^ binders entered since the top (de Bruijn shift)
  -> Term
  -> Bool
posWalk groupNames sig occurs isBareTarget = go
  where
    go shift (CUniverseLift _ _ _ inner) = go shift inner
    go shift (CSchemaLift _ _ _ _ _ _ _ _ inner) = go shift inner
    go shift t
      -- the argument type itself (possibly with family arguments):
      -- a bare occurrence of the target is a strictly positive position
      | isBareTarget shift t = True
      -- the target does not occur at all: trivially strictly positive
      | not (occurs shift t) = True
      | otherwise = case posSpine t of
          -- function/dependent-function type 'X -> U' / '(x : X) -> U':
          -- target absent from the domain and strictly positive in 'U'
          (CPi _ _ _ _ a b, []) ->
            not (occurs shift a) && go (shift + 1) b
          -- application 'F A1 .. An'
          (hd, args@(_ : _)) ->
            case admissibleSig groupNames sig hd of
              Just flags ->
                -- 'F' is admissible (a prior/built-in carrier, or the
                -- defined type applied to family arguments, which is
                -- itself a strictly positive position): the target may
                -- occur strictly positively only in those 'Ai' whose
                -- parameter is marked positive in F's signature, and not
                -- at all in the others
                and
                  [ if positiveFlag
                      then go shift arg
                      else not (occurs shift arg)
                  | (arg, positiveFlag) <- zip args (flags ++ repeat False)
                  ]
              Nothing ->
                -- 'F' is not admissible (a bare variable, an opaque type
                -- without a positivity signature, …): the target must
                -- not occur anywhere in the application
                False
          -- covariant suspension wrappers: the target stays strictly
          -- positive under Thunk/Memo/Force in type position
          (CThunkE e _, []) -> go shift e
          (CLazyE e _, []) -> go shift e
          (CForceE e _, []) -> go shift e
          -- record / variant type formers: every component is covariant
          (CRecordT fs, []) -> all (go shift . snd) fs
          (CVariantT ms, []) -> all (go shift) ms
          -- any other shape carrying an occurrence is not a strictly
          -- positive position
          _ -> False

-- | §10.4 strict positivity of a field type with respect to the group
-- types (the reject condition target). A group type may occur, but only
-- in strictly positive positions.
spPositive :: Set GName -> Map GName [Bool] -> Term -> Bool
spPositive groupNames sig =
  posWalk groupNames sig (\_shift t -> mentionsGroup groupNames t) bareGroup 0
  where
    bareGroup _shift = \case
      CGlob g -> g `Set.member` groupNames
      _ -> False

-- | §10.4 strict positivity of a field type with respect to one data
-- parameter (the de Bruijn variable @v@ at the field-domain depth). Used
-- to compute the parameter-positivity signature.
varPositive :: Set GName -> Map GName [Bool] -> Int -> Term -> Bool
varPositive groupNames sig v0 =
  posWalk groupNames sig (\shift t -> mentionsVar (v0 + shift) t) bareVar 0
  where
    bareVar shift = \case
      CVar i -> i == v0 + shift
      _ -> False

-- | Does any group type constructor occur anywhere in a term?
mentionsGroup :: Set GName -> Term -> Bool
mentionsGroup groupNames = go
  where
    go = \case
      CGlob g -> g `Set.member` groupNames
      CUniverseLift _ _ _ inner -> go inner
      CSchemaLift _ _ _ _ _ _ sourceArguments targetArguments inner ->
        any go sourceArguments || any go targetArguments || go inner
      CArithmeticProof certificate ->
        any go (foldMapArithmeticCertificate (: []) certificate)
      CVar _ -> False
      CLam _ _ _ b -> go b
      CPi _ _ _ _ a b -> go a || go b
      CApp _ f a -> go f || go a
      CSort _ -> False
      CLevel _ -> False
      CLit _ -> False
      CCtor _ _ as -> any go as
      CMatch s _ _ alts -> go s || any (\(CaseAlt _ gd b) -> maybe False go gd || go b) alts
      CRecordT fs -> any (go . snd) fs
      CRecordV fs -> any (go . snd) fs
      CProj e _ -> go e
      CProjAt e _ _ -> go e
      CVariantT ms -> any go ms
      CInject _ e -> go e
      CLet _ _ a b c -> go a || go b || go c
      CLetRec _ _ a b c -> go a || go b || go c
      CLetPolyM _ _ _ _ a b c -> go a || go b || go c
      CLetRecPolyM _ _ _ _ a b c -> go a || go b || go c
      CLetRecGroupM _ definitions body ->
        any (\definition -> go (clrdType definition) || go (clrdRhs definition)) definitions || go body
      CMeta _ -> False
      CDo _ _ -> False
      CSealE _ e -> go e
      CSigT _ e -> go e
      CThunkE e suspensionType -> go e || maybe False go suspensionType
      CLazyE e suspensionType -> go e || maybe False go suspensionType
      CForceE e resultType -> go e || maybe False go resultType
      CIf a b c -> go a || go b || go c
      CQuote _ slots -> any go slots
      CLocal _ _ -> False

teleCtx :: Telescope -> CheckM Ctx
teleCtx = extendTeleCtx emptyCtx

extendTeleCtx :: Ctx -> Telescope -> CheckM Ctx
extendTeleCtx = foldM step
  where
    step c (TelescopeEntry ic mode _formation q borrowed nm domTm mBound) = do
      domV <- evalIn c domTm
      c' <- extendLevelAssumption noSpan c mBound
      pure (bindCtxMQB mode q nm (ic == Impl) borrowed domV c')

-- | Extend a declaration context with source parameters whose omitted
-- classifiers are still being inferred from the declaration body. The
-- telescope stores the current provisional contract; the context flag tells
-- observation analysis and flexible application inference to recompute that
-- contract from the classifier solved by later uses.
extendSourceDeclarationTeleCtx :: Ctx -> [(Binder, TelescopeEntry)] -> CheckM Ctx
extendSourceDeclarationTeleCtx = foldM step
  where
    step c (binder, TelescopeEntry ic storedMode _formation storedQ borrowed nm domTm mBound) = do
      domV <- evalIn c domTm
      c' <- extendLevelAssumption noSpan c mBound
      if isNothing (bType binder)
        then do
          let prefix = bPrefix binder
              mode = fromMaybe Parametric (bpObservation prefix)
              quantity =
                maybe
                  (if mode == Parametric then Q0 else headerBinderQ binder)
                  (qOf . Just)
                  (bpQuantity prefix)
          pure (bindCtxMQBProvisional mode quantity nm (ic == Impl) borrowed domV c')
        else
          pure (bindCtxMQB storedMode storedQ nm (ic == Impl) borrowed domV c')

-- | Finalize a classifier inferred through applications of provisional
-- binders. Flexible application records only those synthesized Pi nodes as
-- transient 'BinderGenerated' binders. Once the surrounding declaration has
-- supplied every constraint, recursively choose each generated domain's
-- observation/quantity contract and publish it as an ordinary interface Pi.
-- A still-unconstrained classifier receives the §11.3/§11.3.3 Type default.
finalizeInferredClassifier :: Ctx -> Term -> CheckM (Term, Value)
finalizeInferredClassifier ctx classifierTerm = do
  classifier0 <- evalIn ctx classifierTerm >>= forceM
  classifier <- defaultFlexible classifier0
  quoted <- quoteIn ctx classifier
  finalizeQuoted ctx quoted
  where
    defaultFlexible = \case
      VFlex meta [] -> do
        level <- freshLevelMeta
        solveMeta meta (VSort level)
        markGeneralizableLevelTerm (CSort level)
        pure (VSort level)
      value -> pure value

    finalizeQuoted activeCtx raw = do
      term <- zonkTermM (ctxLen activeCtx) raw
      case term of
        CPiRuntimeM oldMode oldFormation icit oldQuantity borrowed name assumption origin runtimeErasure domain codomain -> do
          (domain', domainValue) <- finalizeInferredClassifier activeCtx domain
          let transient = origin == BinderGenerated && isNothing assumption
          domainIsParametricKind <- isParametricKind (ctxLen activeCtx) domainValue
          let mode
                | transient && domainIsParametricKind = Parametric
                | transient = Ordinary
                | otherwise = oldMode
              quantity
                | transient && domainIsParametricKind = Q0
                | transient && icit == Impl = Q0
                | transient = QW
                | otherwise = oldQuantity
              formation
                | transient && domainIsParametricKind = FormationParametric
                | transient = FormationOrdinary
                | otherwise = oldFormation
              publishedOrigin = if transient then BinderSourceWritten else origin
          withAssumption <- extendLevelAssumption noSpan activeCtx assumption
          let codomainCtx =
                bindCtxMQB
                  mode
                  quantity
                  name
                  (icit == Impl)
                  borrowed
                  domainValue
                  withAssumption
          (codomain', _) <- finalizeInferredClassifier codomainCtx codomain
          let finalized =
                CPiRuntimeM
                  mode
                  formation
                  icit
                  quantity
                  borrowed
                  name
                  assumption
                  publishedOrigin
                  runtimeErasure
                  domain'
                  codomain'
          value <- evalIn activeCtx finalized >>= forceM
          pure (finalized, value)
        _ -> do
          value <- evalIn activeCtx term >>= forceM
          pure (term, value)

-- | Finalize a generated telescope after its use sites have constrained the
-- provisional domain metas. This is shared by GADT locals and instance-head
-- variables so higher-kinded and row variables retain their inferred domains
-- and receive the least-permissive legal observation contract.
finalizeGeneratedTelescope :: Ctx -> Telescope -> CheckM Telescope
finalizeGeneratedTelescope _ [] = pure []
finalizeGeneratedTelescope ctx (entry : rest) = do
  (domainTm, domain) <- finalizeInferredClassifier ctx (teDomain entry)
  markGeneralizableLevelTerm domainTm
  paramKind <- isParametricKind (ctxLen ctx) domain
  let mode = if paramKind then Parametric else Ordinary
      q = if paramKind then Q0 else QW
      formation = if paramKind && mode == Parametric then FormationParametric else FormationOrdinary
      entry' = entry {teMode = mode, teFormation = formation, teQ = q, teDomain = domainTm}
      ctx' = bindCtxMQB mode q (teName entry) (teIcit entry == Impl) (teBorrow entry) domain ctx
  rest' <- finalizeGeneratedTelescope ctx' rest
  pure (entry' : rest')

-- | Finalize source declaration parameters after the whole declaration header
-- has constrained their provisional kinds. Unannotated parameters acquire the
-- least kind-compatible observation contract and own every level appearing in
-- that inferred kind. Source-written annotations, modes, and quantities remain
-- authoritative; this pass only zonks their domains.
finalizeSourceDeclarationTelescope :: Ctx -> [(Binder, TelescopeEntry)] -> CheckM Telescope
finalizeSourceDeclarationTelescope _ [] = pure []
finalizeSourceDeclarationTelescope ctx ((binder, entry) : rest) = do
  (domainTm, domain) <-
    if isNothing (bType binder)
      then finalizeInferredClassifier ctx (teDomain entry)
      else do
        value <- evalIn ctx (teDomain entry) >>= forceM
        term <- quoteIn ctx value
        pure (term, value)
  when (isNothing (bType binder)) $
    markGeneralizableLevelTerm domainTm
  (mode, quantity) <-
    if isNothing (bType binder)
      then do
        paramKind <- isParametricKind (ctxLen ctx) domain
        let prefix = bPrefix binder
            inferredMode = if paramKind then Parametric else Ordinary
            selectedMode = fromMaybe inferredMode (bpObservation prefix)
            selectedQuantity =
              maybe
                (if selectedMode == Parametric then Q0 else headerBinderQ binder)
                (qOf . Just)
                (bpQuantity prefix)
        pure (selectedMode, selectedQuantity)
      else pure (teMode entry, teQ entry)
  formation <- selectFormationMode ctx mode domain
  let entry' = entry {teMode = mode, teFormation = formation, teQ = quantity, teDomain = domainTm}
      ctx' =
        bindCtxMQB
          mode
          quantity
          (teName entry)
          (teIcit entry == Impl)
          (teBorrow entry)
          domain
          ctx
  later <- finalizeSourceDeclarationTelescope ctx' rest
  pure (entry' : later)

-- | The published placeholder for a declaration with source-unannotated
-- parameters must carry the same deferred observation contract as its local
-- elaboration context. Otherwise the first recursive use can solve the kind
-- meta while a later use is rejected against a stale ordinary Pi. The final
-- declaration telescope replaces this provisional mode and quantity from the
-- completely solved classifier.
provisionalSourceDeclarationParam :: Binder -> TelescopeEntry -> TelescopeEntry
provisionalSourceDeclarationParam binder entry
  | isNothing (bType binder) =
      let prefix = bPrefix binder
          mode = fromMaybe Parametric (bpObservation prefix)
          quantity =
            maybe
              (if mode == Parametric then Q0 else headerBinderQ binder)
              (qOf . Just)
              (bpQuantity prefix)
       in entry {teMode = mode, teQ = quantity}
  | otherwise = entry

installTraitNominalSummary :: GName -> Maybe UniverseSchema -> NominalSignatureClosure -> Span -> CheckM ()
installTraitNominalSummary family sourceSchema closure site = do
  definitions <- gets csGlobals
  case Map.lookup family definitions of
    Nothing -> pure ()
    Just definition -> do
      let parameterCount = dutParameterCount (gdUniverses definition)
          requirements = nominalClosureRequirements closure
          inferred = inferUniverseRoles parameterCount requirements
          written = maybe [] usRoles sourceSchema ++ repeat Nothing
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
          summary =
            makeNominalCumulativitySummary (gKey family) effective explicitFlags closure Nothing
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
                          withPayloadField "explicitRole" (varianceText writtenRole) $
                            withPayloadField "inferredRole" (varianceText inferredRole) $
                              withPayloadField "effectiveRole" (varianceText effectiveRole) $
                                withPayloadField "roleCheckerVersion" "1" $
                                  withPayloadField "declarationKind" "trait" $
                                    withPayloadField "nearestAcceptedRole" (varianceText inferredRole) $
                                      payloadKind "universe-variance"
                  ) $
                    diag SevError StageElaborate "E_UNIVERSE_VARIANCE_TOO_PERMISSIVE"
                      (Just "kappa.universe.variance") site
                      ( "universe role " <> varianceText writtenRole <> " for trait parameter "
                          <> T.pack (show index) <> " is more permissive than inferred role "
                          <> varianceText inferredRole <> " (§11.1.2.3A.2)"
                      )
            _ -> pure ()
      if verifyNominalCumulativitySummary summary
        then modify' $ \st -> st {csGlobals = Map.adjust (globalDefWithNominalSummary summary) family (csGlobals st)}
        else
          errAt site "E_KCORE_SCHEMA_CERTIFICATE_INVALID"
            (Just "kappa.kcore.schema-certificate-invalid")
            "the generated trait-evidence nominal certificate failed independent replay"
  where
    varianceText = \case
      Invariant -> "invariant"
      Covariant -> "covariant"
      Irrelevant -> "irrelevant"

-- | The dictionary field carrying the i-th supertrait premise's
-- evidence (§14.1.4/§14.3.3).
superFieldName :: Int -> Text
superFieldName i = "__super" <> T.pack (show i)

-- | §34.5/§9.4: decide whether a backend intrinsic of the selected profile
-- satisfies the expectation @g@ with declared type @tyV@. An intrinsic is
-- keyed by its Kappa spelling ('csBackendIntrinsics', empty unless a native
-- profile is selected); its expected signature MUST match @tyV@ up to
-- definitional equality. A name match with a type mismatch is reported as
-- 'E_BACKEND_INTRINSIC_SIGNATURE_MISMATCH' and still counts as "claimed by
-- the backend" so the precise mismatch is the sole diagnostic (not also a
-- spurious unsatisfied-expectation error).
backendIntrinsicSatisfies :: GName -> Value -> Span -> CheckM Bool
backendIntrinsicSatisfies g tyV sp = do
  st <- get
  case Map.lookup (gnameText g) (csBackendIntrinsics st) of
    Nothing -> pure False
    Just expectedTm -> do
      expectedV <- evalIn emptyCtx expectedTm
      ec <- ec_
      if convertible ec 0 tyV expectedV
        then pure True
        else do
          errAt sp "E_BACKEND_INTRINSIC_SIGNATURE_MISMATCH" (Just "kappa-hs.backend.intrinsic")
            ( "the declared type of '" <> gnameText g
                <> "' does not match the signature of the backend intrinsic that satisfies it (Spec §9.4, §34.5)"
            )
          pure True

-- | Note a top-level definition of @g@: it satisfies a pending same-file
-- signature (§9.1) and, when it belongs to another selected fragment, counts
-- toward §9.4 expect satisfaction (a second satisfier is ambiguous).
noteDefinition :: GName -> Span -> CheckM ()
noteDefinition g sp = do
  recordDeclSite g sp
  st <- get
  put st {csSigPending = Map.delete g (csSigPending st)}
  case Map.lookup g (csExpects st) of
    Nothing -> pure ()
    Just (esp, cnt)
      -- An expect requires an implementation outside its own source file.
      -- Same-module companion fragments retain distinct 'spanFile' identities
      -- after composition, so this check is independent of fragment order.
      | spanFile esp == spanFile sp -> pure ()
      | otherwise -> do
          modify' $ \st' -> st' {csExpects = Map.insert g (esp, cnt + 1) (csExpects st')}
          when (cnt + 1 == 2) $
            errAt sp "E_EXPECT_AMBIGUOUS" (Just "kappa-hs.expect.ambiguous")
              ("more than one definition satisfies expected declaration '" <> gnameText g <> "' (Spec §9.4)")

-- names a signature's type may resolve through (heads of applications,
-- dotted bases, binder domains)
sigHeadNames :: Expr -> [Text]
sigHeadNames = go
  where
    go = \case
      EVar (Name t _) -> [t]
      EApp f args -> go f ++ concatMap goArg args
      EDot e _ -> go e
      EQDot e _ -> go e
      EArrow b e -> maybe [] go (bType b) ++ go e
      EForall bs e _ -> concatMap (maybe [] go . bType) bs ++ go e
      EExists bs e _ -> concatMap (maybe [] go . bType) bs ++ go e
      ETuple es _ -> concatMap go es
      EOptionSugar e _ -> go e
      ETraitArrow a b -> go a ++ go b
      EOpChain els -> concat [go x | ChainOperand x <- els]
      _ -> []
    goArg = \case
      ArgExplicit e -> go e
      ArgImplicit e -> go e
      _ -> []

-- | Commit declaration-scoped named-hole obligations after every inference
-- mechanism for that declaration has run. A solved shared meta is ordinary
-- inferred Core and produces no diagnostic; an unsolved one reports once at
-- its first source occurrence. This ordering is required by §15.8.6:
-- arithmetic proof search may uniquely determine a named Nat hole while
-- checking a later erased proof argument.
finalizeNamedHoles :: CheckM ()
finalizeNamedHoles = do
  holes <- gets csHoles
  state <- get
  forM_ (Map.toAscList holes) $ \(name, hole) ->
    unless (null (unsolvedMetasOf state (nhTerm hole))) $ do
      let (depth, expected) =
            case nhTerm hole of
              CMeta meta
                | Just classifier <- Map.lookup meta (csMetaClassifiers state) ->
                    (micDepth classifier, micType classifier)
              _ -> (nhDepth hole, nhTypeTerm hole)
          occurrence = fromMaybe noSpan (lastMaybe (nhOccs hole))
      reportUnsolvedHoleAt depth ("?" <> name) occurrence expected

-- | Diagnose signatures that never reached a matching body (the ordinary
-- signature-satisfaction diagnostic is emitted separately). This also keeps
-- malformed declarations from leaking named-hole scopes across a module
-- boundary.
finalizeDeferredSignatureHoles :: CheckM ()
finalizeDeferredSignatureHoles = do
  pending <- gets csSignatureHoles
  forM_ (Map.toAscList pending) $ \(_, holes) ->
    withNamedHoleScope holes finalizeNamedHoles (pure ())
  modify' $ \st -> st {csSignatureHoles = Map.empty}

-- | Canonical alpha-bound names used while checking one declaration or SCC.
-- '$' is not a source identifier spelling, so an ordinary source binder
-- cannot capture a schema occurrence renamed to one of these names.
internalizeUniverseSchema :: UniverseSchema -> UniverseSchema
internalizeUniverseSchema schema =
  schema
    { usParameters =
        [ Name ("$schema" <> T.pack (show index)) (nameSpan parameter)
        | (index, parameter) <- zip [0 :: Int ..] (usParameters schema)
        ]
    }

validateUniverseVarianceApplicability :: Decl -> CheckM ()
validateUniverseVarianceApplicability declaration =
  case declarationUniverseName declaration >>= nameUniverseSchema of
    Just schema
      | any isJust (usRoles schema)
      , not (nominalDeclaration declaration) ->
          errOnce (usSpan schema) "E_UNIVERSE_VARIANCE_NOT_APPLICABLE"
            (Just "kappa.universe.variance")
            "declaration-universe roles are valid only on nominal data or trait signature blocks (§11.1.2.3A.2)"
    _ -> pure ()
  where
    nominalDeclaration = \case
      DData {} -> True
      DTrait {} -> True
      _ -> False

-- | Enter only the rigid schema-parameter scope. Anonymous declarations such
-- as instances acquire their semantic owner after head elaboration begins;
-- 'registerInstanceHead' establishes that owner around the complete typed
-- head while reusing this static mapping.
withUniverseSchemaParameters :: Maybe UniverseSchema -> CheckM a -> CheckM a
withUniverseSchemaParameters Nothing action = action
withUniverseSchemaParameters (Just (UniverseSchema parameters _ schemaSpan)) action = do
  let names = map nameText parameters
  forM_ (duplicatesOf names) $ \duplicate ->
    errAt schemaSpan "E_UNIVERSE_SCHEMA_SCOPE" (Just "kappa.universe.schema-scope")
      ("duplicate declaration-universe parameter '" <> duplicate <> "' in one schema")
  previous <- gets csActiveUniverseSchema
  let active = Map.fromList (zip names (map LParam [0 ..]))
  modify' $ \st -> st {csActiveUniverseSchema = active}
  result <- action
  modify' $ \st -> st {csActiveUniverseSchema = previous}
  pure result

-- | Enter a nested local semantic declaration's universe boundary. Inferred
-- local declarations receive a fresh boundary while retaining outer schema
-- names; explicit local schemas prepend their own parameters and shift outer
-- parameters out of the way. The restoration action lets a local declaration
-- finish its header under the schema and check the following lexical body
-- after that schema has gone out of scope.
withLocalDeclarationUniverseSchema
  :: Bool
  -- ^ Whether the local declaration elaborates to a nominal signature block.
  -> Maybe UniverseSchema
  -> (CheckM () -> CheckM a)
  -> CheckM a
withLocalDeclarationUniverseSchema rolesApplicable schema action = do
  case schema of
    Just localSchema
      | any isJust (usRoles localSchema)
      , not rolesApplicable ->
          errOnce (usSpan localSchema) "E_UNIVERSE_VARIANCE_NOT_APPLICABLE"
            (Just "kappa.universe.variance")
            "declaration-universe roles are valid only on nominal data or trait signature blocks (§11.1.2.3A.2)"
    _ -> pure ()
  previousNames <- gets csActiveUniverseSchema
  previousCount <- gets csActiveLocalUniverseSchemaCount
  activeNames <- case schema of
    Nothing -> pure previousNames
    Just (UniverseSchema parameters _ schemaSpan) -> do
      let names = map nameText parameters
          count = length names
      forM_ (duplicatesOf names) $ \duplicate ->
        errAt schemaSpan "E_UNIVERSE_SCHEMA_SCOPE" (Just "kappa.universe.schema-scope")
          ("duplicate local declaration-universe parameter '" <> duplicate <> "' in one schema")
      let localNames = Map.fromList (zip names (map LParam [0 ..]))
          shiftedOuter = Map.map (abstractLocalLevelParams count) previousNames
      pure (Map.union localNames shiftedOuter)
  let localCount = length . maybe [] usParameters $ schema
      restore = modify' $ \st ->
        st
          { csActiveUniverseSchema = previousNames
          , csActiveLocalUniverseSchemaCount = previousCount
          }
  modify' $ \st ->
    st
      { csActiveUniverseSchema = activeNames
      , csActiveLocalUniverseSchemaCount =
          case schema of
            Nothing -> Nothing
            Just _ -> Just localCount
      }
  result <- action restore
  restore
  pure result

-- | Extend an enclosing declaration schema for a nested semantic declaration
-- such as a data constructor or associated member. Enclosing parameters keep
-- their indices; the nested declaration appends its own rigid parameters.
-- Consequently the nested declaration's complete telescope contains every
-- static identity that can occur in its interface, while no parameter becomes
-- a term binder or runtime field.
withNestedUniverseSchemaParameters :: Maybe UniverseSchema -> CheckM a -> CheckM a
withNestedUniverseSchemaParameters Nothing action = action
withNestedUniverseSchemaParameters (Just (UniverseSchema parameters _ schemaSpan)) action = do
  previous <- gets csActiveUniverseSchema
  let names = map nameText parameters
      duplicates = duplicatesOf names
      shadows = filter (`Map.member` previous) names
      offset = Map.size previous
  forM_ duplicates $ \duplicate ->
    errAt schemaSpan "E_UNIVERSE_SCHEMA_SCOPE" (Just "kappa.universe.schema-scope")
      ("duplicate declaration-universe parameter '" <> duplicate <> "' in one schema")
  forM_ shadows $ \shadow ->
    errAt schemaSpan "E_UNIVERSE_SCHEMA_SCOPE" (Just "kappa.universe.schema-scope")
      ( "nested declaration-universe parameter '" <> shadow
          <> "' would shadow an enclosing schema parameter"
      )
  let appended = Map.fromList (zip names (map LParam [offset ..]))
      active = Map.union previous appended
  modify' $ \st -> st {csActiveUniverseSchema = active}
  result <- action
  modify' $ \st -> st {csActiveUniverseSchema = previous}
  pure result

declarationUniverseName :: Decl -> Maybe Name
declarationUniverseName = \case
  DSig _ name _ _ -> Just name
  DLet _ def _ -> ldName def
  DData _ decl _ -> Just (ddName decl)
  DTypeAlias _ name _ _ _ _ -> Just name
  DTrait _ decl _ -> Just (trName decl)
  DEffect _ decl _ -> Just (effName decl)
  DPattern _ def _ -> ldName def
  DProjection _ name _ _ _ _ -> Just name
  DExpect _ form _ -> case form of
    ExpectTerm name _ -> Just name
    ExpectType name _ _ -> Just name
    ExpectData name _ _ -> Just name
    ExpectTrait name _ _ -> Just name
  DUnsafeAssert _ inner _ -> declarationUniverseName inner
  _ -> Nothing

-- | §4.2: reject an unsafe/debug facility that the build configuration
-- disallows, citing both the offending form and the disabling setting.
gateUnsafe :: Text -> Text -> Span -> Text -> CheckM ()
gateUnsafe facility setting sp affected =
  report $
    withPayload (featureGatedPayload ("unsafe-debug-facility:" <> facility) setting) $
    withRelated (related RoleFeatureGateSite sp ("build setting '" <> setting <> "' is disabled")) $
      diag SevError StageElaborate "E_FEATURE_INACTIVE" (Just "kappa.feature.gated") sp
        ( "use of unsafe/debug facility '" <> facility <> "'"
            <> (if T.null affected || affected == "<definition>" then "" else " (on '" <> affected <> "')")
            <> " requires the build setting '" <> setting
            <> "', which is disabled (Spec §4.2)"
        )

-- | §4.7: append one audit-ledger entry for an accepted unsafe/debug use.
recordAudit :: Text -> Text -> Text -> Span -> Maybe Text -> CheckM ()
recordAudit facility affected setting sp reason = do
  mn <- gets csModule
  let rec' = AuditRecord facility mn sp affected setting reason
  modify' $ \st -> st {csAuditLedger = csAuditLedger st ++ [rec']}

-- | §4.5: gate a reference to the unchecked-proof escape
-- @unsafeAssertProof@ (and its primitive @__unsafeAssertProof@, whose type
-- @forall (@0 p : Type). p@ is a raw admit — it inhabits ANY proposition from
-- a @Type@ alone, so naming it from ordinary user code forges false proofs).
--
-- There are exactly two doors, neither of them name-based:
--
--   * the 'csAllowUnsafeIntrinsics' flag — set by the prelude loader for the
--     genuine embedded prelude/std-lib (so the prelude can define and use
--     these admits), and by the pipeline for any user module that carries the
--     @AllowUnsafeIntrinsics attribute; and
--   * the @allow_unsafe_assert_proof@ build setting — the explicit, audited
--     per-build opt-in used by the lawful-trait escape (§11.4/§14.4).
--
-- The exemption is deliberately NOT name-based on @cur == preludeModule@. The
-- previous gate skipped its whole body whenever @cur == preludeModule@, so a
-- user file literally named @module std.prelude@ — which never goes through
-- the embedded-prelude loader and so never gets the flag — could forge
-- @let bogus : (=) True False = __unsafeAssertProof@ and inhabit Void. The
-- flag, not the module name, now decides the embedded exemption, exactly as
-- 'gateUnsafeIntrinsic' does, so the spoof module is rejected like any other.
-- Each accepted use is recorded in the §4.7 ledger (except the genuine
-- embedded prelude's own internal admits, which would otherwise pollute every
-- downstream module's carried-forward ledger).
gateUnsafeAssertProof :: GName -> Span -> CheckM ()
gateUnsafeAssertProof (GName gm nm) sp
  | gm == preludeModule, nm `elem` ["unsafeAssertProof", "__unsafeAssertProof"] = do
      allowed <- gets csAllowUnsafeIntrinsics
      embedded <- gets csEmbeddedLoad
      cfg <- gets csUnsafe
      if allowed
        then when (not embedded) $
          recordAudit "unsafeAssertProof" nm "allow_unsafe_intrinsics" sp Nothing
        else
          if allowUnsafeAssertProof cfg
            then recordAudit "unsafeAssertProof" nm "allow_unsafe_assert_proof" sp Nothing
            else gateUnsafe "unsafeAssertProof" "allow_unsafe_assert_proof" sp ""
  | otherwise = pure ()

-- | §4.5 soundness gate: the raw-admit proof intrinsics. Each of these
-- prelude primitives inhabits an ARBITRARY proposition from nothing but a
-- @Type@ (or transmutes one value to any type), so naming one from ordinary
-- user code is a total-unsoundness hole — e.g.
-- @let bogus : (=) True False = __eqProof@ type-checks, and @subst@ over a
-- discriminator family then inhabits @Void@. They exist only so the prelude
-- can admit the proof helpers (cong/sym/trans/subst/pathInd/isPropEq/… and
-- the §11.4 List-monoid laws) and so the elaborator can build @__handleEff@
-- applications. The exemption is the 'csAllowUnsafeIntrinsics' flag ALONE:
-- it is set by the prelude loader when elaborating the genuine embedded
-- prelude/std-lib (so those admit the proof helpers), and by the pipeline
-- for any user module that carries the @AllowUnsafeIntrinsics attribute
-- (for tests/bootstrapping). The exemption is deliberately NOT name-based
-- on @cur == preludeModule@ — a user file literally named @module std.prelude@
-- never goes through the embedded-prelude load and so never gets the flag,
-- and is rejected like any other module. Every gated name is rejected when
-- the flag is off, before any term is built, on every resolution path
-- (unqualified, module-aliased, fully-qualified, and reified-module-member),
-- so there is no path by which ordinary user code reaches the raw admit.
-- Each accepted opt-in use is recorded in the §4.7 audit ledger.
-- The complete set of user-nameable prelude prims that inhabit an arbitrary
-- proposition or can liberate a free result variable:
--
--   (a) RESULT type a free, unpinned variable — bound by the prim's telescope
--       but appearing in no argument, so it unifies with any target type. A
--       full prelude scan (§4.5) found these six: the four proof intrinsics
--       plus the two @std.debug@ introspection prims @__debugInspect@/
--       @__debugCompare@, whose result @r@ is pinned only by the std.debug
--       wrappers one module up but is free at the bare-prim level —
--       @let bogus : (=) True False = __debugInspect 0@ type-checks.
--
--   (b) Pure eliminators whose result is pinned to a FREE argument variable
--       that a sound producer can supply unconstrained — a composition hole.
--       The remaining prelude case is @__arrayIndexUnsafe@ via an empty
--       @__arrayFromList []@ producer.
--
-- @__debugRender@ is deliberately NOT gated: its result is pinned to @String@
-- (no free variable, no producer can liberate it), so it is not exploitable,
-- and a §11.4 positive test names it from a plain module to exercise carrier
-- recovery through a primitive equand (isprop-eq-string-prim-carrier-positive.kp)
-- — gating it would break that legitimate use for no soundness gain. The
-- §28.5 STEP-3 composition survey checked every remaining pinned-result
-- eliminator for a free-variable producer: @__codeEscape : Code t -> t@ has no
-- way to build a @Code (free t)@ (the only code producer, @.<e>.@, requires a
-- well-typed @e : t@); @runPure : Eff __effRowNil a -> a@ has no @Eff (free a)@
-- producer (@throwIO@/@stmAbort@ produce @IO@, not @Eff@, and a fully-handled
-- @__effRowNil@ row cannot be reached with a free result); and @atomically :
-- STM a -> IO Void a@ / @runCode : ClosedCode t -> IO Void t@ wrap (not extract)
-- the result. The remaining eliminator that does have a sound free-variable
-- producer is @__arrayIndexUnsafe@ (via @__arrayFromList []@), gated below.
-- @__bytesIndexUnsafe@/@__rowExtend@ have concrete results (@Byte@ / a row),
-- no free variable to liberate.
-- @__unsafeAssertProof@ is gated separately by 'gateUnsafeAssertProof'.
--
-- @std.testing.failNow@ (type @forall (@0 a : Type). String -> a@) has the same
-- raw-admit shape — its result @a@ is free — and, unlike the six prelude prims,
-- it lives in @std.testing@ and is reachable from a plain user module via
-- @import std.testing as T; T.failNow@ or a bare @std.testing.failNow@. A guard
-- keyed on @gm == preludeModule@ would never fire for it, so the gate is keyed
-- on the full @(module, name)@ pair below. @std.testing@ itself is loaded with
-- the 'csAllowUnsafeIntrinsics' flag (it is part of the embedded std-lib), so
-- its own definitions are exempt; only a NON-exempt module naming @failNow@ is
-- gated.
gatedUnsafeIntrinsics :: Set.Set GName
gatedUnsafeIntrinsics =
  Set.fromList $
    prelRawProof
      : [ GName preludeModule n
    | n <-
        [ "__transport"
        , "__absurd"
        , "__handleEff"
        , "__debugInspect"
        , "__debugCompare"
        , -- §4.5 composition class: @__arrayIndexUnsafe :
          -- forall a. Array a -> Int -> a@ extracts an element PURELY, and its
          -- result @a@ is pinned to the @Array a@ argument, so the original
          -- free-RESULT survey passed it over. But @__arrayFromList : forall a.
          -- List a -> Array a@ applied to the empty list @[]@ builds an @Array
          -- (free a)@ with NO element (a genuinely empty array — the producer is
          -- sound), and indexing it liberates the free @a@:
          -- @let bad : (=) True False = __arrayIndexUnsafe (__arrayFromList []) 0@
          -- type-checks. Users have the safe @arrayIndex@/@Array.get@ wrappers
          -- (which return @Option@/trap), and the embedded prelude's own
          -- @arrayIndex@ definition uses this prim under the
          -- 'csAllowUnsafeIntrinsics' exemption, so gating the bare prim costs
          -- ordinary code nothing. (@__bytesIndexUnsafe : Bytes -> Nat -> Byte@
          -- is NOT gated: its result @Byte@ is concrete — no free variable to
          -- liberate.)
          "__arrayIndexUnsafe"
        ]
    ]
      ++ [GName modTesting "failNow"]

gateUnsafeIntrinsic :: GName -> Span -> CheckM ()
gateUnsafeIntrinsic g@(GName _ nm) sp
  | g `Set.member` gatedUnsafeIntrinsics = do
      -- §4.5: exemption is the 'csAllowUnsafeIntrinsics' flag ALONE (set
      -- for the embedded prelude/std-lib by the loader, and for a user
      -- module carrying @AllowUnsafeIntrinsics). A user file merely named
      -- 'module std.prelude' does NOT get the flag and is rejected.
      allowed <- gets csAllowUnsafeIntrinsics
      embedded <- gets csEmbeddedLoad
      if allowed
        then -- §4.7: record each accepted opt-in use in the audit ledger so the
             -- soundness escape shows in the audit trail (mirrors how
             -- 'gateUnsafeAssertProof' records 'unsafeAssertProof'). The genuine
             -- embedded prelude/std-lib admits the proof helpers and wraps the
             -- debug prims internally — implementation machinery, not a user
             -- opt-in — so those uses are NOT ledgered (they would otherwise
             -- pollute every downstream module's ledger, since the base ledger
             -- carries forward). Every NON-embedded module reaching here did so
             -- via the @AllowUnsafeIntrinsics flag, so the use is recorded.
          when (not embedded) $
            recordAudit "unsafeIntrinsic" nm "allow_unsafe_intrinsics" sp Nothing
        else
          report $
            withPayload
              ( withPayloadField "name" nm $
                  payloadKind "unsafe-intrinsic-gated"
              ) $
              withRelated (related RoleUseSite sp ("'" <> nm <> "' named here")) $
                diag SevError StageElaborate "E_UNSAFE_INTRINSIC_GATED" (Just "kappa.feature.gated") sp
                  ( "the raw-admit proof intrinsic '" <> nm
                      <> "' inhabits an arbitrary proposition and is not nameable from ordinary"
                      <> " user code; it would forge false proofs and break soundness."
                      <> " Use the checked proof helpers (refl/cong/subst/…) instead, or mark the"
                      <> " module '@AllowUnsafeIntrinsics' to opt in for testing (Spec §4.5)"
                  )
  | otherwise = pure ()

-- | §4.5 soundness gate at every name/member resolution path. The two
-- escapes ('gateUnsafeAssertProof' and 'gateUnsafeIntrinsic') were
-- originally invoked only from the unqualified 'resolveName' path, which
-- a QUALIFIED reference bypasses: @import std.prelude as P@ then
-- @P.__eqProof@ (the module-alias branch of 'elabDotUnqualified'), a bare
-- fully-qualified @std.prelude.__eqProof@ ('elabDotOrdinary'), or a reified
-- module-object member ('moduleMember') each resolve straight to the
-- prelude 'globalTerm' with no gate. This helper runs BOTH gates and is
-- threaded through every such path, so a qualified reference is gated
-- identically to a bare one and the @AllowUnsafeIntrinsics flag is the only
-- way user code can name a gated intrinsic.
gateUnsafeResolved :: GName -> Span -> CheckM ()
gateUnsafeResolved g sp = do
  gateUnsafeAssertProof g sp
  gateUnsafeIntrinsic g sp

-- | Rewrite references to the innermost @n@ binders (a projection's
-- place binders) into the §13.2.1 @this@ neutral, dropping the binders.
-- Used to express a root-dependent focus type under Δ alone.
placesToThis :: Int -> Term -> Term
placesToThis n = go 0
  where
    go d t = case t of
      CVar i
        | i >= d ->
            if i - d < n then CGlob thisG else CVar (i - n)
        | otherwise -> t
      CGlobal _ _ -> t
      CLamM mode ic q nm b -> CLamM mode ic q nm (go (d + 1) b)
      CPiRuntimeM mode formation ic q brw nm assumption origin runtimeErasure a b ->
        CPiRuntimeM mode formation ic q brw nm assumption origin
          (fmap (go d) runtimeErasure)
          (go d a)
          (go (d + 1) b)
      CAppM ic runtimeErasure f a ->
        CAppRuntime ic (fmap (go d) runtimeErasure) (go d f) (go d a)
      CUniverseLift from to evidence inner ->
        CUniverseLift from to evidence (go d inner)
      CSchemaLift family source target roles evidence certificate sourceArguments targetArguments inner ->
        CSchemaLift family source target roles evidence certificate
          (map (go d) sourceArguments) (map (go d) targetArguments) (go d inner)
      CArithmeticProof certificate ->
        CArithmeticProof (mapArithmeticCertificate (go d) certificate)
      CSort _ -> t
      CLevel _ -> t
      CLit _ -> t
      CCtorI g universes ann arguments ->
        CCtorI g universes (fmap (go d) ann)
          [argument {caTerm = go d (caTerm argument)} | argument <- arguments]
      CMatch s ann resultAnn alts ->
        CMatch (go d s) (fmap (go d) ann) (fmap (go d) resultAnn)
          [CaseAlt p (fmap (go (d + patBindersC p)) g) (go (d + patBindersC p) b) | CaseAlt p g b <- alts]
      CRecordTQ fs -> CRecordTQ (map (fmap (go d)) fs)
      CRecordV fs -> CRecordV [(nm, go d x) | (nm, x) <- fs]
      CProjM mode e f -> CProjM mode (go d e) f
      CProjAtM mode e f i -> CProjAtM mode (go d e) f i
      CVariantT ms -> CVariantT (map (go d) ms)
      CInject tag e -> CInject tag (go d e)
      CLetRuntimeM mode q nm runtimeErasure a b c ->
        CLetRuntimeM mode q nm (fmap (go d) runtimeErasure) (go d a) (go d b) (go (d + 1) c)
      CLetRecRuntimeM mode q nm runtimeErasure a b c ->
        CLetRecRuntimeM mode q nm (fmap (go d) runtimeErasure) (go d a) (go (d + 1) b) (go (d + 1) c)
      CLetPolyRuntimeM mode q nm telescope runtimeErasure a b c ->
        CLetPolyRuntimeM mode q nm telescope (fmap (go d) runtimeErasure) (go d a) (go d b) (go (d + 1) c)
      CLetRecPolyRuntimeM mode q nm telescope runtimeErasure a b c ->
        CLetRecPolyRuntimeM mode q nm telescope (fmap (go d) runtimeErasure) (go d a) (go (d + 1) b) (go (d + 1) c)
      CLetRecGroupM telescope definitions body ->
        let d' = d + length definitions
         in CLetRecGroupM telescope
              [ definition
                  { clrdRuntimeErasure = fmap (go d) (clrdRuntimeErasure definition)
                  , clrdType = go d (clrdType definition)
                  , clrdRhs = go d' (clrdRhs definition)
                  }
              | definition <- definitions
              ]
              (go d' body)
      CMeta _ -> t
      CDo _ _ -> t
      CSealE ls e -> CSealE ls (go d e)
      CSigT ls e -> CSigT ls (go d e)
      CThunkE e suspensionType -> CThunkE (go d e) (go d <$> suspensionType)
      CLazyE e suspensionType -> CLazyE (go d e) (go d <$> suspensionType)
      CForceE e resultType -> CForceE (go d e) (go d <$> resultType)
      CIf a b c -> CIf (go d a) (go d b) (go d c)
      CQuote qs slots -> CQuote qs (map (go d) slots)
      CLocal i universes
        | i >= d ->
            if i - d < n then CGlob thisG else CLocal (i - n) universes
        | otherwise -> t

rejectInoutBinderContext :: Text -> Binder -> CheckM ()
rejectInoutBinderContext context b =
  when (bInout b) $
    errAt (bSpan b) "E_QTT_INOUT_BINDER_CONTEXT" (Just "kappa-hs.qtt.inout-marker")
      ( "'inout' is permitted only on explicit parameters of named functions, "
          <> "methods, and trait-member signatures; it is not permitted in a "
          <> context
          <> " (§18.9.2)"
      )

rejectAllInoutBinders :: Data a => Text -> a -> CheckM ()
rejectAllInoutBinders context x =
  forM_ (collectInoutBinders x) (rejectInoutBinderContext context)

collectInoutBinders :: Data a => a -> [Binder]
collectInoutBinders x =
  maybeToList (cast x >>= \b -> if bInout b then Just b else Nothing)
    ++ concat (gmapQ collectInoutBinders x)

withNamedCallableInoutSignature :: Expr -> CheckM a -> CheckM a
withNamedCallableInoutSignature tyE action = do
  validateNamedCallableInoutSignature tyE
  old <- gets csAllowInoutBinderContext
  modify' $ \st -> st {csAllowInoutBinderContext = True}
  r <- action
  modify' $ \st -> st {csAllowInoutBinderContext = old}
  pure r

validateNamedCallableInoutSignature :: Expr -> CheckM ()
validateNamedCallableInoutSignature = goHead
  where
    goHead = \case
      EArrow b body -> do
        forM_ (bType b) (rejectAllInoutBinders "parameter type")
        forM_ (bDefault b) (rejectAllInoutBinders "parameter default")
        goHead body
      EForall bs body _ -> do
        forM_ bs $ \b -> do
          rejectInoutBinderContext "forall binder" b
          forM_ (bType b) (rejectAllInoutBinders "forall binder type")
          forM_ (bDefault b) (rejectAllInoutBinders "forall binder default")
        goHead body
      ETraitArrow premise body -> do
        rejectAllInoutBinders "trait premise" premise
        goHead body
      EAscription e ty _ -> do
        goHead e
        rejectAllInoutBinders "signature ascription type" ty
      ECaptures e _ _ -> goHead e
      other ->
        rejectAllInoutBinders "nested anonymous function type" other

recordInoutParams :: GName -> [Maybe InoutParamInfo] -> CheckM ()
recordInoutParams g infos =
  when (any isJust infos) $
    modify' $ \st -> st {csInoutParams = Map.insert g infos (csInoutParams st)}

inoutParamsFromBinders :: [Binder] -> [Maybe InoutParamInfo]
inoutParamsFromBinders =
  mapMaybe explicitInfo
  where
    explicitInfo b
      | bImplicit b = Nothing
      | otherwise =
          Just $
            if bInout b
              then do
                nm <- bName b
                let t = nameText nm
                Just (InoutParamInfo t t)
              else Nothing

signatureBinders :: Expr -> [Binder]
signatureBinders = \case
  EForall bs body _ -> bs ++ signatureBinders body
  ETraitArrow _ body -> signatureBinders body
  EArrow b body -> b : signatureBinders body
  ECaptures e _ _ -> signatureBinders e
  EAscription e _ _ -> signatureBinders e
  _ -> []

recordSignatureInoutParams :: GName -> Expr -> CheckM ()
recordSignatureInoutParams g tyE =
  recordInoutParams g (inoutParamsFromBinders (signatureBinders tyE))

recordDefinitionInoutParams :: GName -> [Binder] -> CheckM ()
recordDefinitionInoutParams g binders =
  recordInoutParams g (inoutParamsFromBinders binders)

receiverParamsFromBinders :: [Binder] -> [Int]
receiverParamsFromBinders binders =
  [ index
  | (index, binder) <- zip [0 ..] (filter (not . bImplicit) binders)
  , bReceiver binder /= NoReceiver
  ]

recordReceiverParams :: GName -> [Int] -> CheckM ()
recordReceiverParams global positions =
  unless (null positions) $
    modify' $ \state ->
      state {csReceivers = Map.insert global positions (csReceivers state)}

-- A governing signature defines the callable receiver ABI (§7.4, §9.1).
-- Recording only non-empty metadata lets an unmarked definition preserve that
-- ABI while still allowing a signature-less marked definition to provide it.
recordSignatureReceiverParams :: GName -> Expr -> CheckM ()
recordSignatureReceiverParams global signature =
  recordReceiverParams global (receiverParamsFromBinders (signatureBinders signature))

recordDefinitionReceiverParams :: GName -> [Binder] -> CheckM ()
recordDefinitionReceiverParams global binders =
  recordReceiverParams global (receiverParamsFromBinders binders)

withRecursiveSchemaOccurrenceRecording :: CheckM a -> CheckM a
withRecursiveSchemaOccurrenceRecording action = do
  previous <- gets csRecordRecursiveSchemaOccurrences
  modify' $ \state -> state {csRecordRecursiveSchemaOccurrences = True}
  result <- action
  modify' $ \state -> state {csRecordRecursiveSchemaOccurrences = previous}
  pure result

-- | Run one owner-scoped solver action and make its pending proof telescope
-- physical, but leave publication to the enclosing transaction.  Keeping this
-- operation separate prevents a publication worklist from recursively
-- re-entering itself while the current delta wave is only half repaired.
withActiveUniverseDefinitionRaw :: GName -> CheckM a -> CheckM a
withActiveUniverseDefinitionRaw g action = do
  previous <- gets csActiveUniverseDefinition
  modify' $ \st -> st {csActiveUniverseDefinition = Just g}
  result <- action
  materializePendingUniverseProofsRaw g
  modify' $ \st -> st {csActiveUniverseDefinition = previous}
  pure result

occursGlobal :: GName -> Term -> Bool
occursGlobal g = Set.member g . globalsOfTerm

reportUnverifiedTermination :: Span -> [Span] -> Text -> Text -> CheckM ()
reportUnverifiedTermination declarationSite callSites message note =
  forM_ primarySites $ \primarySite ->
    report $
      withNote note $
        addOrigins primarySite $
          diag
            SevError
            StageElaborate
            "E_TERMINATION_UNVERIFIED"
            (Just "kappa.termination.failure")
            primarySite
            message
  where
    sites = nub (filter (/= noSpan) callSites)
    primarySites = if null sites then [declarationSite] else sites
    addOrigins primarySite diagnostic =
      let withDeclaration
            | declarationSite == noSpan || declarationSite == primarySite = diagnostic
            | otherwise =
                withRelated
                  (related RoleDeclarationSite declarationSite "recursive declaration")
                  diagnostic
       in foldl'
            (\current site ->
               if site == primarySite
                 then current
                 else
                   withRelated
                     (related RoleCallSite site "other recursive call considered in this unverified SCC")
                     current)
            withDeclaration
            sites

classifyRecursiveSchemaOccurrences :: [[TerminationDecl]] -> CheckM ()
classifyRecursiveSchemaOccurrences groups = do
  st <- get
  let assignments = csLevelAssignments st
      groupSets = map (Set.fromList . map tdName) groups
      recursive occurrence =
        any
          (\members -> rsoCaller occurrence `Set.member` members && rsoCallee occurrence `Set.member` members)
          groupSets
          && ( declarationUniverseArity (rsoCaller occurrence) > 0
                 || declarationUniverseArity (rsoCallee occurrence) > 0
             )
      declarationUniverseArity global =
        maybe 0 (dutParameterCount . gdUniverses) (Map.lookup global (csGlobals st))
      occurrences = filter recursive (reverse (csRecursiveSchemaOccurrences st))
  forM_ occurrences $ \occurrence -> do
    current <- get
    let recursiveMembers =
          fromMaybe Set.empty . listToMaybe $
            [ members
            | members <- groupSets
            , rsoCaller occurrence `Set.member` members
            , rsoCallee occurrence `Set.member` members
            ]
        completeExplicitScc =
          all
            (\member ->
              member `Set.member` csTerminationNames current
                && maybe False (dutExplicit . gdUniverses)
                     (Map.lookup member (csGlobals current)))
            (Set.toList recursiveMembers)
        callerArity =
          maybe 0 (dutParameterCount . gdUniverses)
            (Map.lookup (rsoCaller occurrence) (csGlobals current))
        sourceLevels = map LParam [0 .. callerArity - 1]
        ownerAssignments =
          Map.union
            (Map.findWithDefault Map.empty (rsoCaller occurrence)
              (csFinalizedGlobalUniverseMetaMaps current))
            assignments
        rawOccurrenceLevels = rsoLevels occurrence
        occurrenceLevels =
          case Map.lookup
                 (rsoCallee occurrence, length rawOccurrenceLevels)
                 (provisionalUniverseProjections current (rsoCallee occurrence)) of
            Just projection
              | urpSourceArity projection == length rawOccurrenceLevels ->
                  [rawOccurrenceLevels !! position | position <- urpRetainedPositions projection]
            _ -> rawOccurrenceLevels
        targetLevels = map (normalizeLevel . substituteLevelMetas ownerAssignments) occurrenceLevels
        occurrenceAssumptions = substituteLevelAssumptions ownerAssignments (rsoAssumptions occurrence)
        identity =
          length sourceLevels == length targetLevels
            && and (zipWith (==) (map normalizeLevel sourceLevels) targetLevels)
        pointwise =
          length sourceLevels == length targetLevels
            && and
              [ proveLevelLeq occurrenceAssumptions target source == Proved
              | (target, source) <- zip targetLevels sourceLevels
              ]
        strict =
          pointwise
            && or
              [ proveLevelLeq occurrenceAssumptions (levelSucc target) source == Proved
              | (target, source) <- zip targetLevels sourceLevels
              ]
        site
          | rsoSpan occurrence == noSpan =
              Map.findWithDefault noSpan (rsoCaller occurrence) (csDeclSites current)
          | otherwise = rsoSpan occurrence
        edge relation =
          modify' $ \state ->
            state
              { csRecursiveSchemaEdges =
                  Set.insert
                    (RecursiveSchemaEdge (rsoCaller occurrence) (rsoCallee occurrence) relation)
                    (csRecursiveSchemaEdges state)
              }
    if identity
      then edge RecursiveSchemaIdentity
      else if not (rsoExplicit occurrence) || not completeExplicitScc
        then
          report $
            withPayload
              ( withPayloadField "caller" (gKey (rsoCaller occurrence)) $
                  withPayloadField "callee" (gKey (rsoCallee occurrence)) $
                    withPayloadField "completeExplicitRecursiveScc" (if completeExplicitScc then "true" else "false") $
                      withPayloadField "sourceInstance" (T.intercalate ", " (map renderLevel sourceLevels)) $
                        withPayloadField "targetInstance" (T.intercalate ", " (map renderLevel targetLevels)) $
                          payloadKind "universe-recursive-schema-implicit"
              ) $
              diag SevError StageElaborate "E_UNIVERSE_RECURSIVE_SCHEMA_IMPLICIT"
                (Just "kappa.universe.recursive-schema") site
                "a non-identity recursive declaration-schema call requires an explicit .{...} instance and complete explicit signatures and schemas for the whole SCC (§11.1.2.3A)"
        else if pointwise
          then edge (if strict then RecursiveSchemaStrictLower else RecursiveSchemaLowerOrEqual)
          else
            report $
              withPayload
                ( withPayloadField "caller" (gKey (rsoCaller occurrence)) $
                    withPayloadField "callee" (gKey (rsoCallee occurrence)) $
                      withPayloadField "sourceInstance" (T.intercalate ", " (map renderLevel sourceLevels)) $
                        withPayloadField "targetInstance" (T.intercalate ", " (map renderLevel targetLevels)) $
                          payloadKind "universe-recursive-schema-increase"
                ) $
                diag SevError StageElaborate "E_UNIVERSE_RECURSIVE_SCHEMA_INCREASE"
                  (Just "kappa.universe.recursive-schema") site
                  "a recursive declaration-schema instance must be pointwise same-or-lower than the current SCC instance (§11.1.2.3A)"

withSccOpaque :: [GName] -> CheckM a -> CheckM a
withSccOpaque gs act = do
  saved <- gets csGlobals
  let restore acc g = case Map.lookup g saved of
        Just gd -> Map.insert g gd acc
        Nothing -> acc
  modify' $ \st ->
    invalidateSemanticCaches
      (st {csGlobals = foldr (Map.adjust (\gd -> gd {gdReducible = False})) (csGlobals st) gs})
  r <- act
  modify' $ \st ->
    invalidateSemanticCaches (st {csGlobals = List.foldl' restore (csGlobals st) gs})
  pure r

setGlobalReducible :: GName -> Bool -> CheckM ()
setGlobalReducible g ok =
  modify' $ \st ->
    invalidateSemanticCaches
      (st {csGlobals = Map.adjust (\gd -> gd {gdReducible = ok}) g (csGlobals st)})

-- | Try the bounded, deterministic ranking-function fragment required by
-- §§15.5-15.8 when no explicit @decreases@ clause is present. Candidates are
-- formed from typed explicit parameters only: each arithmetic parameter, then
-- each ordered difference of two integer parameters. Every candidate is
-- handed to the same proof-producing call-edge checker used for explicit
-- measures; no source spelling or unchecked heuristic can certify an SCC.
inferredMeasureSccOKWithEdges :: Maybe [CallEdge] -> Map GName TermFun -> CheckM Bool
inferredMeasureSccOKWithEdges edges funMap
  | Map.null funMap = pure False
  | otherwise = tryShapes candidateShapes
  where
    functions = Map.elems funMap
    sharedArity = minimum (map (length . tfExplParams) functions)
    candidateShapes =
      [InferredParameter index | index <- [0 .. sharedArity - 1]]
        ++ [ InferredDifference left right
           | left <- [0 .. sharedArity - 1]
           , right <- [0 .. sharedArity - 1]
           , left /= right
           ]
        ++ [ InferredDifferencePlusOne left right
           | left <- [0 .. sharedArity - 1]
           , right <- [0 .. sharedArity - 1]
           , left /= right
           ]
        ++ [ InferredSuccessorDifference left right
           | left <- [0 .. sharedArity - 1]
           , right <- [0 .. sharedArity - 1]
           , left /= right
           ]

    tryShapes [] = pure False
    tryShapes (shape : rest) = do
      measured <- traverse (withInferredMeasure shape) funMap
      case sequence measured of
        Nothing -> tryShapes rest
        Just candidateMap -> do
          accepted <- measureSccOKWithEdges candidateMap edges
          if accepted then pure True else tryShapes rest

withInferredMeasure :: InferredMeasureShape -> TermFun -> CheckM (Maybe TermFun)
withInferredMeasure shape function = do
  candidate <- case shape of
    InferredParameter index -> do
      parameter <- arithmeticParameter function index
      pure $ do
        (term, _, domain) <- parameter
        typeKey <- arithmeticMeasureTypeKey domain
        pure (term, typeKey)
    InferredDifference leftIndex rightIndex ->
      integerPairCandidate leftIndex rightIndex intSub
    InferredDifferencePlusOne leftIndex rightIndex ->
      integerPairCandidate leftIndex rightIndex $ \left right ->
        intAdd (intSub left right) (CLit (LitInt 1))
    InferredSuccessorDifference leftIndex rightIndex ->
      integerPairCandidate leftIndex rightIndex $ \left right ->
        intSub (intAdd left (CLit (LitInt 1))) right
  pure $ do
    (measure, typeKey) <- candidate
    pure
      function
        { tfMeasure =
            Just
              MeasureSpec
                { msMeasureTerm = measure
                , msMeasureTypeKey = typeKey
                , msRelation = Nothing
                , msProof = Nothing
                , msDepth = tfDepth function
                }
        }
  where
    integerPairCandidate leftIndex rightIndex build = do
      left <- arithmeticParameter function leftIndex
      right <- arithmeticParameter function rightIndex
      pure $ do
        (leftTerm, _, leftDomain) <- left
        (rightTerm, _, rightDomain) <- right
        guard (leftDomain == ArithmeticInteger)
        guard (rightDomain == ArithmeticInteger)
        typeKey <- arithmeticMeasureTypeKey leftDomain
        pure (build leftTerm rightTerm, typeKey)

    intAdd = integerBinary "addInt"
    intSub = integerBinary "subInt"
    integerBinary operation left right =
      CApp Expl (CApp Expl (CGlob (gPrel operation)) left) right

arithmeticParameter
  :: TermFun
  -> Int
  -> CheckM (Maybe (Term, Term, ArithmeticDomain))
arithmeticParameter function parameterIndex =
  case nthMaybe parameterIndex (tfExplParams function) of
    Nothing -> pure Nothing
    Just level ->
      case nthMaybe (tfDepth function - level - 1) (ctxEntries (tfCtx function)) of
        Nothing -> pure Nothing
        Just entry -> do
          typeKey <-
            quoteIn (tfCtx function) (ceType entry)
              >>= normalizeTermAt (tfDepth function)
          pure $ do
            domain <- arithmeticDomainForCarrier typeKey
            pure
              ( CVar (tfDepth function - level - 1)
              , typeKey
              , domain
              )

arithmeticMeasureTypeKey :: ArithmeticDomain -> Maybe Term
arithmeticMeasureTypeKey = \case
  ArithmeticNatural -> Just (CGlob prelNat)
  ArithmeticInteger -> Just (CGlob prelInteger)
  ArithmeticTypeLevel -> Nothing
  ArithmeticProviderLaw -> Nothing

-- | Reconstruct the source telescope used when elaborating a decreases
-- expression.  This mirrors the signature-driven lambda elaborator: implicit
-- binders present in the signature but absent from the source are still placed
-- in the context, while explicit source binders keep their written names.
measureCtxFromSig :: Value -> [Binder] -> CheckM Ctx
measureCtxFromSig = measureCtxFromSigIn emptyCtx

measureCtxFromSigIn :: Ctx -> Value -> [Binder] -> CheckM Ctx
measureCtxFromSigIn initial sigTy binders = go initial sigTy binders
  where
    go ctx _ [] = pure ctx
    go ctx ty0 bs@(b : rest) = do
      ty <- forceM ty0
      case ty of
        VPiBoundM _ Impl q _ nm assumption dom clo
          | not (bImplicit b)
          , (nameText <$> bName b) /= Just nm -> do
              cod <- clApp clo (VRigid (ctxLen ctx) [])
              withBound <- extendLevelAssumption (bSpan b) ctx assumption
              go (bindCtxQ q nm True dom withBound) cod bs
        VPiBoundM _ _ q _ nm assumption dom clo -> do
          let bn = fromMaybe nm (nameText <$> bName b)
          cod <- clApp clo (VRigid (ctxLen ctx) [])
          withBound <- extendLevelAssumption (bSpan b) ctx assumption
          go (bindCtxQ q bn (bImplicit b) dom withBound) cod rest
        _ -> pure ctx

relationCanonicalKey :: Int -> RelationFlavor -> Term -> CheckM Term
relationCanonicalKey d flavor relTm = do
  isLt <- case flavor of
    RelationReturnsBool -> relationIsPrimitiveLtInt d relTm
    _ -> pure False
  if isLt
    then pure (CGlob (gPrel "ltInt"))
    else normalizeTermAt d relTm

relationExpectedType :: Ctx -> Value -> RelationFlavor -> CheckM Value
relationExpectedType ctx measureTy flavor = do
  mTyTm <- quoteIn ctx measureTy
  let cod = case flavor of
        RelationReturnsType -> CSort LZero
        RelationReturnsBool -> CGlob prelBool
        RelationUnknown -> CSort LZero
      tyTm = CPiFormedM Ordinary FormationOrdinary Expl QW False "_x" mTyTm (CPiFormedM Ordinary FormationOrdinary Expl QW False "_y" (shiftTerm 1 0 mTyTm) cod)
  evalIn ctx tyTm

-- | Evidence that an explicit `by R` relation is well-founded.  The current
-- surface language exposes well-foundedness through `WellFoundedRelation A`:
-- if instance search can synthesize such a dictionary and its `rel` member is
-- definitionally equal to R, then R carries the same well-founded order.  This
-- keeps proof-directed decreases conservative: a per-call proof proves only
-- the local descent fact; the relation itself still needs a well-founded
-- source.
relationWellFoundedEvidence :: Ctx -> Int -> Value -> Term -> RelationFlavor -> CheckM Bool
relationWellFoundedEvidence _ctx _d _measureTy _relTm flavor = do
  case flavor of
    -- The current prelude exposes `WellFoundedRelation.rel`, but not a real
    -- inspectable accessibility proof.  Treating erased placeholders as
    -- well-foundedness would make arbitrary user relations acceptable, so
    -- Type-valued relations remain uncertified here.
    RelationReturnsType -> pure False
    -- Bool-valued relations are a compiler convenience for primitive orders.
    -- They are accepted without an explicit WF dictionary only when the
    -- arithmetic/normalization prover can decide the call-site fact itself.
    -- A user proof for an arbitrary Bool relation does not make the relation
    -- well-founded.
    _ -> pure False

peelTermParams :: Term -> ([(Icit, Int)], Term, Int)
peelTermParams = peelTermParamsAt 0

peelTermParamsAt :: Int -> Term -> ([(Icit, Int)], Term, Int)
peelTermParamsAt initialDepth = go [] initialDepth
  where
    go acc d = \case
      CLam ic _ _ b -> go (acc ++ [(ic, d)]) (d + 1) b
      t -> (acc, t, d)

-- ── SCC call-edge collection ─────────────────────────────────────────
