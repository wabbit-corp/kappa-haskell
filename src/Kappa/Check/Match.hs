-- | Pattern matching and conditionals: coverage and refinement.
--
-- Helpers for @if@ and @match@ — deciding exhaustiveness, computing the
-- flow refinements a branch may assume (§7.4.1), and lowering a checked
-- match into its core form.
--
-- Carved out of "Kappa.Check" as part of splitting that module; see
-- "Kappa.Check.Types" for the shared data dictionary and docs\/CONCEPTS.md
-- for the vocabulary these assume.
module Kappa.Check.Match
  ( canonicalNatRangeBounds
  , commonRepresentationRestrictions
  , complementRefines
  , constructorSourceContracts
  , corePatternCatchAll
  , corePatternCoveredTags
  , corePatternHasVariantRest
  , coreRecordPatternIrrefutable
  , emptyPatternRefinements
  , erasedFieldsForConstructor
  , groundlyApart
  , inhabClassifyHead
  , inhabHasEvidence
  , inhabRecordFieldDependencies
  , inhabRuntimeRecordField
  , lookupActivePattern
  , lowerActiveMatch
  , noRigidSkolemForced
  , orientRefinement
  , peekCtor
  , reflexiveSelfFiber
  , residualCatchAllPatterns
  , uncoveredFinitePatternSkeletons
  , rewriteActiveLetQ
  , rigidLevelThroughUniverseLift
  , rootConstructorForcedRefinements
  , single
  , syntheticConstructorPatternLayout
  , termContainsAtScope
  , uncoveredDataConstructors
  , wildUseful
  , withPatternRefinements
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

-- | Only a whole-condition single `x is C` test yields a usable
-- complement (a failed conjunction proves nothing positive), and
-- only a UNIQUE residual constructor is a usable fact: a wider
-- residual would invent a positive fact the test never proved.
complementRefines :: [(Text, [GName])] -> CheckM [(Text, [GName])]
complementRefines refs = fmap concat . forM refs $ \(x, gs) -> do
  st <- get
  case nub [ciData ci | g <- gs, Just ci <- [Map.lookup g (csCtors st)]] of
    [dataG]
      | Just di <- Map.lookup dataG (csDatas st)
      , [residual] <- [cg | cg <- diCtors di, cg `notElem` gs] ->
          pure [(x, [residual])]
    _ -> pure []

-- | 'resolveCtor' without the unresolved-constructor diagnostic: used
-- while classifying possible active-pattern heads (§17.3.2).
peekCtor :: Ctx -> CtorRef -> CheckM (Maybe (GName, CtorInfo))
peekCtor ctx cref = do
  st0 <- get
  r <- resolveCtor ctx cref
  case r of
    Just _ -> pure r
    Nothing -> put st0 >> pure Nothing

-- | Find an active pattern by (unqualified) head name; same-module
-- definitions take precedence over imported ones (§17.3).
lookupActivePattern :: CtorRef -> CheckM (Maybe APInfo)
lookupActivePattern (CtorRef _ n) = do
  st <- get
  let nm = nameText n
      cands = [(g, i) | (g, i) <- Map.toList (csActive st), gnameText g == nm]
      own = [i | (GName m _, i) <- cands, m == csModule st]
  pure $ case own ++ map snd cands of
    (i : _) -> Just i
    [] -> Nothing

-- | Lower a match containing active-pattern cases (§17.3.2) into
-- nested matches over the pattern functions' results: Option results
-- test Some/None, Match results thread the Miss residue into the
-- remaining cases, and total view results match the view value
-- directly (consecutive cases with the same head share one view
-- match, preserving exhaustiveness over the view type).
lowerActiveMatch :: Ctx -> Expr -> [MatchCase] -> Span -> CheckM Expr
lowerActiveMatch ctx scrut cases sp = case scrut of
  EVar _ -> goCases scrut cases
  _ -> do
    sv <- freshNameM "__apscrut"
    let svn = Name sv sp
    inner <- goCases (EVar svn) cases
    pure (ELet [LetBind False emptyPrefix (PVar svn) Nothing scrut sp] inner sp)
  where
    goCases se cs = do
      classified <- mapM classify cs
      build se classified
    classify c@(MatchImpossible _) = pure (CPlain c)
    classify c@(MatchCase pat mguard body csp) = case pat of
      PCtor cref ps _ | not (null ps) -> do
        mc <- peekCtor ctx cref
        case mc of
          Just _ -> pure (CPlain c)
          Nothing -> do
            mAp <- lookupActivePattern cref
            case mAp of
              Just info -> case mapM activePatArgExpr (init ps) of
                Just args -> pure (CActive (crName cref) info args (last ps) mguard body csp)
                Nothing -> do
                  unsupportedAt csp "this active-pattern argument form is not supported by this implementation"
                  pure (CBad csp)
              Nothing -> do
                mg <- lookupGlobalName (nameText (crName cref))
                case mg of
                  Just _ -> do
                    errAt csp "E_PATTERN_HEAD_NOT_CONSTRUCTOR_OR_ACTIVE_PATTERN" (Just "kappa-hs.pattern.head")
                      ("'" <> nameText (crName cref)
                         <> "' is neither a constructor nor an active pattern, so it cannot head a pattern (§17.3.2)")
                    pure (CBad csp)
                  Nothing -> pure (CPlain c)
      PActive cref args vp psp -> do
        mAp <- lookupActivePattern cref
        case mAp of
          Just info -> pure (CActive (crName cref) info args vp mguard body psp)
          Nothing -> do
            errAt psp "E_PATTERN_HEAD_NOT_CONSTRUCTOR_OR_ACTIVE_PATTERN" (Just "kappa-hs.pattern.head")
              ("'" <> nameText (crName cref) <> "' is not an active pattern (§17.3.2)")
            pure (CBad psp)
      _ -> pure (CPlain c)
    apApp n args se = EApp (EVar n) (map ArgExplicit (args ++ [se]))
    pcon nm ps = PCtor (CtorRef Nothing (Name nm sp)) ps sp
    pconMember owner nm ps =
      PCtor (CtorRef (Just (Name owner sp)) (Name nm sp)) ps sp

    build se classified = case classified of
      [] -> pure (EMatch se [] sp)
      (CBad _ : rest) -> build se rest
      (CPlain _ : _) -> do
        let (plains, rest) = span isPlain classified
            plainCases = [c | CPlain c <- plains]
        if null rest
          then pure (EMatch se plainCases sp)
          else do
            r <- freshNameM "__apk"
            let rn = Name r sp
            inner <- build (EVar rn) rest
            pure (EMatch se (plainCases ++ [MatchCase (PVar rn) Nothing inner sp]) sp)
      (CActive n info args vp mguard body csp : rest) -> case apResult info of
        APOption -> do
          inner <- build se rest
          pure $
            EMatch (apApp n args se)
              [ MatchCase (pcon "Some" [vp]) mguard body csp
              , MatchCase (PWild sp) Nothing inner sp
              ]
              sp
        APMatch -> do
          r <- freshNameM "__apresid"
          let rn = Name r sp
          inner <- build (EVar rn) rest
          pure $
            EMatch (apApp n args se)
              [ MatchCase (pconMember "Match" "Hit" [vp]) mguard body csp
              , MatchCase (pconMember "Match" "Miss" [PVar rn]) Nothing inner sp
              ]
              sp
        APTotal -> do
          let sameHead = \case
                CActive n2 i2 _ _ _ _ _ -> nameText n2 == nameText n && apResult i2 == APTotal
                _ -> False
              (run, rest') = span sameHead (CActive n info args vp mguard body csp : rest)
              viewCases = [MatchCase vp' g' b' c' | CActive _ _ _ vp' g' b' c' <- run]
          extra <-
            if null rest'
              then pure []
              else do
                inner <- build se rest'
                pure [MatchCase (PWild sp) Nothing inner sp]
          pure (EMatch (apApp n args se) (viewCases ++ extra) sp)
      where
        isPlain = \case
          CPlain _ -> True
          _ -> False

-- | Rewrite @let? P args (vp) = e@ over an active pattern P into the
-- corresponding match on @P args e@ (§17.3.2). A Match-result pattern
-- threads a residue, which a plain @let?@ cannot receive.
rewriteActiveLetQ :: Ctx -> Pattern -> Expr -> Span -> CheckM (Pattern, Expr)
rewriteActiveLetQ ctx pat rhs dsp = case pat of
  PCtor cref ps psp | not (null ps) -> do
    mc <- peekCtor ctx cref
    case mc of
      Just _ -> pure (pat, rhs)
      Nothing -> do
        mAp <- lookupActivePattern cref
        case mAp of
          Nothing -> pure (pat, rhs)
          Just info -> case mapM activePatArgExpr (init ps) of
            Nothing -> pure (pat, rhs)
            Just args -> do
              let app = EApp (EVar (crName cref)) (map ArgExplicit (args ++ [rhs]))
                  vp = last ps
              case apResult info of
                APOption -> pure (PCtor (CtorRef Nothing (Name "Some" psp)) [vp] psp, app)
                APMatch -> do
                  errAt dsp "E_ACTIVE_PATTERN_MATCH_RESULT_NOT_ALLOWED_IN_PLAIN_LET_QUESTION"
                    (Just "kappa-hs.pattern.active")
                    "a Match-result active pattern threads a residue on a miss and may not be used in a plain 'let?'; use a match with a residue case instead (§17.3.2)"
                  pure
                    ( PCtor
                        (CtorRef (Just (Name "Match" psp)) (Name "Hit" psp))
                        [vp]
                        psp
                    , app
                    )
                APTotal -> pure (vp, app)
  _ -> pure (pat, rhs)

-- | Convert an active-pattern argument (written in pattern position)
-- to the expression it denotes (§17.3.2).
activePatArgExpr :: Pattern -> Maybe Expr
activePatArgExpr = \case
  PLit (LInt v msuf) psp -> Just (EIntLit v ((`Name` psp) <$> msuf) psp)
  PLit (LFloat v msuf) psp -> Just (EFloatLit v ((`Name` psp) <$> msuf) psp)
  PVar n -> Just (EVar n)
  _ -> Nothing

-- | Recover a lexical rigid through an explicit, proof-carrying universe
-- coercion.  The wrapper changes only the classifier level and therefore
-- preserves the term identity used by branch-local flow facts.  No other
-- neutral/application shape is accepted.
rigidLevelThroughUniverseLift :: Value -> Maybe Int
rigidLevelThroughUniverseLift = \case
  VRigid level [] -> Just level
  VUniverseLift _ _ _ inner -> rigidLevelThroughUniverseLift inner
  _ -> Nothing

-- | Recover the endpoint carrier of a structurally reflexive self-fiber.
-- Every decision is made from checked identities and typed telescopes. A
-- malformed, ambiguous, or more general singleton family is left
-- unclassified rather than being granted equality elimination rules.
reflexiveSelfFiber :: Ctx -> Value -> CheckM (Maybe (GName, Value))
reflexiveSelfFiber ctx scrutineeType = do
  forced <- forceM scrutineeType
  case forced of
    VGlobI family _ arguments -> do
      dataInfo <- gets (Map.lookup family . csDatas)
      constructors <- gets csCtors
      case dataInfo >>= singleConstructor of
        Nothing -> pure Nothing
        Just constructor ->
          case Map.lookup constructor constructors >>= reflexiveEndpointPositions family of
            Just (carrierPosition, leftPosition, rightPosition)
              | maximum [carrierPosition, leftPosition, rightPosition]
                  < length arguments -> do
                  let values = map snd arguments
                      carrier = values !! carrierPosition
                      leftEndpoint = values !! leftPosition
                      rightEndpoint = values !! rightPosition
                  evaluation <- ec_
                  pure $
                    if convertible
                         evaluation
                         (ctxLen ctx)
                         (force evaluation leftEndpoint)
                         (force evaluation rightEndpoint)
                      then Just (constructor, carrier)
                      else Nothing
            _ -> pure Nothing
    _ -> pure Nothing
  where
    singleConstructor DataInfo {diCtors = [constructor]} = Just constructor
    singleConstructor _ = Nothing

reflexiveEndpointPositions
  :: GName
  -> CtorInfo
  -> Maybe (Int, Int, Int)
reflexiveEndpointPositions family constructor = do
  guard (ciData constructor == family)
  guard (null (ciSourceFields constructor))
  let (binders, result) = constructorTelescope (ciType constructor)
      (headTerm, resultArguments) =
        spineOfTerm (stripIdentityWrappers result)
      arguments =
        [stripIdentityWrappers argument | (_, argument) <- resultArguments]
  guard (termHeadGlob (stripIdentityWrappers headTerm) == Just family)
  (leftPosition, rightPosition, endpointVariable) <-
    case
        [ (left, right, variable)
        | (left, leftTerm) <- zip [0 :: Int ..] arguments
        , (right, rightTerm) <- zip [0 :: Int ..] arguments
        , left < right
        , leftTerm == rightTerm
        , CVar variable <- [leftTerm]
        ]
      of
        [positions] -> Just positions
        _ -> Nothing
  let binderCount = length binders
      binderPosition = binderCount - endpointVariable - 1
  guard (binderPosition >= 0 && binderPosition < binderCount)
  let endpointDomain =
        shiftTerm
          (binderCount - binderPosition)
          0
          (binders !! binderPosition)
      carrierPositions =
        [ position
        | (position, argument) <- zip [0 :: Int ..] arguments
        , argument == stripIdentityWrappers endpointDomain
        ]
  carrierPosition <- case carrierPositions of
    [position] -> Just position
    _ -> Nothing
  pure (carrierPosition, leftPosition, rightPosition)
  where
    constructorTelescope = go []
      where
        go domains (CPiEvidenceM _ _ _ _ _ _ _ _ domain codomain) =
          go (domains ++ [domain]) codomain
        go domains result = (domains, result)

-- | Does a term from the surrounding scope occur in another term at that
-- scope? The needle is shifted under each traversed binder before comparison,
-- so dependent motives remain detectable beneath Pi/lambda/match nodes.
termContainsAtScope :: Term -> Term -> Bool
termContainsAtScope needle =
  getAny . foldTermWithDepth occurrence 0
  where
    normalizedNeedle = stripIdentityWrappers needle
    occurrence depth candidate =
      Any
        ( stripIdentityWrappers candidate
            == shiftTerm depth 0 normalizedNeedle
        )

erasedFieldsForConstructor
  :: Int
  -> GName
  -> [Value]
  -> CheckM [ConstructorFieldPath]
erasedFieldsForConstructor depth constructor fieldTypes = do
  evaluation <- ec_
  constructorInfo <- gets (Map.lookup constructor . csCtors)
  pure $ case constructorInfo of
    Nothing -> []
    Just info ->
      [ ConstructorFieldPath constructor sourceIndex
      | (sourceIndex, ((icit, quantity, runtimeErasure), fieldType)) <-
          zip [0 :: Int ..]
            (zip (constructorSourceContracts info) fieldTypes)
      , not
          (Repr.runtimeConstructorPiField
            evaluation
            depth
            runtimeErasure
            icit
            quantity
            fieldType)
      ]

-- | Source-field contracts projected from the finalized constructor Pi.
-- The erasure bit is checker-selected authority: consumers may specialize the
-- field type, but must not rerun evidence search or discard this annotation.
-- Evidence terms themselves remain on 'ciType' and are authenticated at the
-- typed-Core boundary; these layout queries need only the selected/relevant
-- distinction.
constructorSourceContracts :: CtorInfo -> [(Icit, Q, RuntimeErasure ())]
constructorSourceContracts info =
  drop (length binders - length (ciSourceFields info)) binders
  where
    binders = collect (ciType info)
    collect = \case
      CPiRuntimeM _ _ icit quantity _ _ _ _ runtimeErasure _ body ->
        (icit, quantity, fmap (const ()) runtimeErasure) : collect body
      _ -> []

commonRepresentationRestrictions :: [BackendProfileRestriction]
commonRepresentationRestrictions =
  [ InternalValuesOnly
  , ExcludeDynamicBoundary
  , ExcludeForeignBoundary
  , ExcludeExportedAbi
  ]

single :: [a] -> Maybe a
single [value] = Just value
single _ = Nothing

inhabRecordFieldDependencies
  :: Ctx
  -> RecordField Value
  -> CheckM [Text]
inhabRecordFieldDependencies ctx field = do
  fieldType <- quoteIn ctx (rfType field)
  pure
    ( nub
        (thisDepsOf fieldType ++ levelFieldDepsOf fieldType)
    )

-- | Mandatory runtime-erasure decisions for inhabitance use the same checked
-- representation predicate as KBackendIR lowering. The source inhabitance of
-- an erased field is still accounted for by 'Kappa.Inhabitance'; this callback
-- says only whether the field has a runtime slot.
inhabRuntimeRecordField :: Ctx -> Int -> RecordField Value -> CheckM Bool
inhabRuntimeRecordField ctx fieldOffset field = do
  evaluation <- ec_
  pure
    (not (Repr.runtimeErasedRecordField evaluation (ctxLen ctx + fieldOffset) field))

-- | Recognize the exact standard inclusive-Nat-range refinement shape. The
-- operation/member dictionaries are authenticated by selected instance
-- identity in 'selectedNatRangeMembershipOperands' and
-- 'decodeSelectedNatRange'; source spellings have no authority here.
canonicalNatRangeBounds
  :: Int
  -> Value
  -> Value
  -> CheckM (Maybe (Term, Term))
canonicalNatRangeBounds depth base predicate = do
  evaluation <- ec_
  base' <- forceM base
  case base' of
    VGlobN natural [] | natural == prelNat ->
      case stripIdentityWrappers (quote evaluation depth predicate) of
        CLam _ _ _ body
          | Just (True, membership) <- booleanLiteralEqualityPayload body -> do
              operands <- selectedNatRangeMembershipOperands membership
              decoded <- case operands of
                Just (rangeValue, member)
                  | stripIdentityWrappers member == CVar 0 ->
                      decodeSelectedNatRange (depth + 1) rangeValue
                _ -> pure Nothing
              pure $ do
                (lowerWithBinder, upperWithBinder, exclusive) <- decoded
                guard (not exclusive)
                let lower = shiftTerm (-1) 0 lowerWithBinder
                    upper = shiftTerm (-1) 0 upperWithBinder
                guard (termScopedAt depth lower)
                guard (termScopedAt depth upper)
                pure (lower, upper)
        _ -> pure Nothing
    _ -> pure Nothing

-- | Classify a forced head: a closed data type registered in 'csDatas' is the
-- only structural case the analysis reasons about. Everything else (type
-- families, abstract/opaque heads, primitives) is reported as "not a data
-- type", which the analysis turns into 'Unknown'.
inhabClassifyHead :: Value -> CheckM (Maybe HeadClass)
inhabClassifyHead t = do
  st <- get
  pure $ case t of
    VGlobN g _ -> case Map.lookup g (csDatas st) of
      Just di -> Just (IsData t (diCtors di))
      Nothing -> Nothing
    _ -> Nothing

-- | Is a (demanded scrutinee index) value GROUND — free of any rigid skolem?
--
-- Soundness hinges on this for the §30.2.7 GADT rule: a constructor's
-- result-index unify-failure means 'Empty' ONLY when the demanded index is
-- ground. A surviving 'VRigid' (a free/abstract index variable like the @b@ in
-- @Tag b@) makes the index non-ground, so a unify-failure there is merely
-- "absent for this instantiation", not a contradiction.
--
-- We FORCE at every node so that (a) solved metavariables are followed to their
-- solutions and (b) a rigid pinned by a branch-local @FactIs@ (§7.4.1 dependent
-- match) resolves to its witness — only a genuinely free 'VRigid' counts.
-- Unsolved 'VFlex' metas are GROUND-COMPATIBLE: unification can still solve them,
-- and any such solve is itself a reachable inhabitant, so they never block the
-- 'Empty' verdict on their own.
--
-- Conservative on the fringes: a recursion-budget exhaustion, an opaque closure
-- (@VLam@/@VPi@/@VThunkV@/…), or any other shape we cannot cheaply prove rigid-
-- free is treated as NON-ground (returns 'False'), which can only refuse an
-- 'Empty' verdict — never fabricate one.
--
-- Residual hole (documented, not load-bearing for the cases we gate): an
-- unsolved 'VFlex' that a /later/ unification would have resolved to a rigid is
-- still counted ground here. Today the only producers of the demanded scrutinee
-- index for this query are real source types, whose abstract indices are 'VRigid'
-- (not metas), so this does not arise; it would need a metas-as-indices caller
-- to ever bite.
noRigidSkolemForced :: EvalCtx -> Value -> Bool
noRigidSkolemForced ec = go (1000 :: Int)
  where
    go fuel v
      | fuel <= 0 = False -- budget exhausted: fail closed (treat as non-ground)
      | otherwise = case force ec v of
          VRigid _ _ -> False -- a surviving free skolem: NOT ground
          VFlex _ sp -> all (go (fuel - 1) . snd) sp -- unsolved meta head is fine; check its args
          VGlobN _ sp -> all (go (fuel - 1) . snd) sp
          VCtor _ args -> all (go (fuel - 1)) args
          VLit _ -> True
          VSort _ -> True
          VInject _ w -> go (fuel - 1) w
          VRecordT fs -> all (go (fuel - 1) . snd) fs
          VRecordV fs -> all (go (fuel - 1) . snd) fs
          VVariantT ms -> all (go (fuel - 1)) ms
          VPrim _ args -> all (go (fuel - 1)) args
          VAppN _ f a -> go (fuel - 1) f && go (fuel - 1) a
          -- Anything else (binders/closures/suspensions/neutral projections and
          -- matches we did not unfold) is conservatively NON-ground: we refuse
          -- the Empty verdict rather than risk hiding a rigid inside it.
          _ -> False

-- | Rigidity-aware structural no-confusion: are these two values PROVABLY
-- distinct — diverging at a pair of different constructor heads, with neither
-- side a rigid skolem or meta at (or above) the point of divergence?
--
-- This is the decidable half of GADT no-confusion (§17.1.2 / §30.2.7). It
-- returns 'True' only when /no/ instantiation of the free variables could make
-- the two sides equal, so concluding the refined fiber 'Empty' is sound:
--
--   * @Z@ vs @S n@ ⇒ True (distinct ground constructor heads; the @n@ below the
--     @S@ is irrelevant — the heads already disagree).
--   * @True@ vs @False@ ⇒ True (distinct nullary constructors / literals).
--   * a 'VRigid' or 'VFlex' against ANYTHING ⇒ False (the variable could be
--     instantiated to match; emptiness is undecidable here).
--   * same constructor head ⇒ recurse pairwise; apart iff some argument is apart
--     (this never fires for a genuine unify-failure root, but keeps the check
--     total and lets a nested ground clash like @S Z@ vs @S (S n)@ be detected).
--   * anything we cannot cheaply classify (closures, Pi, neutral projections) ⇒
--     False (conservative: refuse the 'Empty' verdict rather than fabricate it).
groundlyApart :: (GName -> Bool) -> EvalCtx -> Value -> Value -> Bool
groundlyApart constructorVisible ec = go (1000 :: Int)
  where
    go fuel a b
      | fuel <= 0 = False
      | otherwise = case (force ec a, force ec b) of
          -- Either side a free variable / unsolved meta: could be instantiated
          -- to match, so NOT provably apart.
          (VRigid _ _, _) -> False
          (_, VRigid _ _) -> False
          (VFlex _ _, _) -> False
          (_, VFlex _ _) -> False
          -- Distinct literals are apart; equal literals agree.
          (VLit l1, VLit l2) -> l1 /= l2
          (VLit (LitInt n), VCtor g args)
            | g == prelNatZero -> n /= 0 || not (null args)
            | g == prelNatSucc ->
                n <= 0
                  || case args of
                    [predecessor] -> go (fuel - 1) (VLit (LitInt (n - 1))) predecessor
                    _ -> True
          (VCtor g args, VLit (LitInt n))
            | g == prelNatZero -> n /= 0 || not (null args)
            | g == prelNatSucc ->
                n <= 0
                  || case args of
                    [predecessor] -> go (fuel - 1) predecessor (VLit (LitInt (n - 1)))
                    _ -> True
          -- Data constructors (the index-argument representation, e.g. `Z` is
          -- `VCtor Z []`, `S m` is `VCtor S [m]`). Different heads ⇒ apart
          -- (no-confusion). Same head ⇒ apart iff some argument is apart; the
          -- rigid `m` under a SHARED head (`S m` vs `S k`) is therefore not a
          -- clash, while `Z` vs `S m` clashes at the head regardless of `m`.
          (VCtor g1 as1, VCtor g2 as2)
            | g1 /= g2 ->
                constructorVisible g1 && constructorVisible g2
            | length as1 /= length as2 ->
                constructorVisible g1
            | otherwise -> or (zipWith (go (fuel - 1)) as1 as2)
          -- Same nominal type-application head (e.g. nested `Vec a (S n)` vs
          -- `Vec a Z` appearing as an index): recurse pairwise. Different type
          -- heads are NOT treated as apart — nominal type constructors are not
          -- assumed injective/disjoint at the value level here (conservative).
          (VGlobN g1 sp1, VGlobN g2 sp2)
            | g1 == g2
            , length sp1 == length sp2 ->
                or (zipWith (\(_, x) (_, y) -> go (fuel - 1) x y) sp1 sp2)
          -- Anything else: not cheaply decidable ⇒ conservatively NOT apart.
          _ -> False

-- | §30.2.7 proof-classification evidence: does the /local/ context carry an
-- explicit @C t'@ binder (e.g. @IsEmpty t@) with @t'@ convertible to the
-- analyzed type? This is the conservative, side-effect-free "context contains
-- explicit evidence" rule — it consults only in-scope implicit binders and
-- never triggers instance search, so it cannot fabricate evidence.
inhabHasEvidence :: Ctx -> GName -> Value -> CheckM Bool
inhabHasEvidence ctx traitG ty = do
  ec <- ec_
  t <- forceM ty
  let lvl = ctxLen ctx
      matches e = case ceType e of
        -- a single-parameter proof trait applied to the analyzed type:
        -- `IsEmpty t'` with t' convertible to t. The last spine entry is the
        -- type argument; require a non-empty spine (a bare trait head carries
        -- no type to match against).
        VGlobN g sp
          | g == traitG
          , (_, arg) : _ <- reverse sp -> convertible ec lvl arg t
        _ -> False
  pure (any (\e -> ceImplicitLocal e && matches e) (ctxEntries ctx))

uncoveredDataConstructors
  :: CheckState
  -> DataInfo
  -> Maybe [GName]
  -> [(CorePat, Maybe Term)]
  -> [GName]
uncoveredDataConstructors st di mRefined alts =
  [ c
  | c <- ctorsToCover
  , let arity = ctorArity st c
  , wildUseful st (specializeRows st (KCtor c) arity rows) arity
  ]
  where
    allCtors = diCtors di
    ctorsToCover = case mRefined of
      Just constructors
        | not (null constructors)
        , all (`elem` allCtors) constructors -> constructors
      _ -> allCtors
    rows = [[pattern'] | (pattern', Nothing) <- alts]

corePatternCatchAll :: CorePat -> Bool
corePatternCatchAll = \case
  CPWild -> True
  CPVar _ -> True
  CPAs _ pattern' -> corePatternCatchAll pattern'
  CPOr patterns _ -> any corePatternCatchAll patterns
  _ -> False

corePatternIrrefutableSubpattern :: CorePat -> Bool
corePatternIrrefutableSubpattern = \case
  CPWild -> True
  CPVar _ -> True
  CPAs _ pattern' -> corePatternIrrefutableSubpattern pattern'
  CPTuple patterns -> all corePatternIrrefutableSubpattern patterns
  CPRecord fields _ -> all (corePatternIrrefutableSubpattern . snd) fields
  _ -> False

corePatternCoveredTags :: CorePat -> [Text]
corePatternCoveredTags = \case
  CPInject tag pattern'
    | corePatternIrrefutableSubpattern pattern' -> [tag]
  CPOr patterns _ -> concatMap corePatternCoveredTags patterns
  _ -> []

corePatternHasVariantRest :: CorePat -> Bool
corePatternHasVariantRest = \case
  CPInjectRest _ -> True
  _ -> False

coreRecordPatternIrrefutable :: CorePat -> Bool
coreRecordPatternIrrefutable = \case
  CPRecord fields _ -> all (corePatternIrrefutableSubpattern . snd) fields
  CPTuple patterns -> all corePatternIrrefutableSubpattern patterns
  CPAs _ pattern' -> coreRecordPatternIrrefutable pattern'
  CPOr patterns _ -> any coreRecordPatternIrrefutable patterns
  pattern' -> corePatternCatchAll pattern'

ctorArity :: CheckState -> GName -> Int
ctorArity st c = case Map.lookup c (csCtors st) of
  Just ci -> length (ciFields ci)
  Nothing -> 0

-- unwrap as/or patterns into plain alternatives for the first column
expandRow :: [CorePat] -> [[CorePat]]
expandRow [] = [[]]
expandRow (p : ps) = case p of
  CPAs _ q -> expandRow (q : ps)
  CPOr qs _ -> concat [expandRow (q : ps) | q <- qs]
  _ -> [p : ps]

-- a first-column pattern this analysis treats as matching anything
isWildLike :: CheckState -> CorePat -> Bool
isWildLike st = \case
  CPWild -> True
  CPVar _ -> True
  CPRecord {} -> True -- over-approximation
  CPInject {} -> True -- nested variant injections: over-approximation
  CPInjectRest _ -> True
  -- an arity-mismatched constructor pattern was already diagnosed;
  -- do not cascade a non-exhaustiveness report
  CPCtor c _ ps -> length ps /= ctorArity st c
  _ -> False

patKey :: CheckState -> CorePat -> Maybe (PatKey, Int)
patKey st = \case
  CPCtor c _ ps | length ps == ctorArity st c -> Just (KCtor c, length ps)
  CPTuple ps -> Just (KTup (length ps), length ps)
  CPLit l -> Just (KLit l, 0)
  _ -> Nothing

subPats :: CorePat -> [CorePat]
subPats = \case
  CPCtor _ _ ps -> ps
  CPTuple ps -> ps
  _ -> []

specializeRows :: CheckState -> PatKey -> Int -> [[CorePat]] -> [[CorePat]]
specializeRows st k a rows =
  [ row'
  | row0 <- rows
  , row <- expandRow row0
  , Just row' <- [spec row]
  ]
  where
    spec [] = Nothing
    spec (p : ps)
      | isWildLike st p = Just (replicate a CPWild ++ ps)
      | Just (k', _) <- patKey st p, k' == k = Just (subPats p ++ ps)
      | otherwise = Nothing

defaultRows :: CheckState -> [[CorePat]] -> [[CorePat]]
defaultRows st rows =
  [ ps
  | row0 <- rows
  , (p : ps) <- expandRow row0
  , isWildLike st p
  ]

-- is the all-wildcard row of width n useful w.r.t. the matrix?
wildUseful :: CheckState -> [[CorePat]] -> Int -> Bool
wildUseful _ rows 0 = null rows
wildUseful st rows n =
  let firsts = [p | row0 <- rows, (p : _) <- expandRow row0]
      keys = nub (mapMaybe (patKey st) firsts)
      tupleKeys = [(key, arity) | (key@KTup {}, arity) <- keys]
      constructorKeys = [(key, arity) | (key@KCtor {}, arity) <- keys]
      completeSignature = case tupleKeys of
        signature@((KTup arity, _) : _)
          | all (\case (KTup otherArity, _) -> otherArity == arity; _ -> False) signature ->
              Just signature
        _ -> case constructorKeys of
          signature@((KCtor constructor, _) : _) ->
            case Map.lookup constructor (csCtors st) >>= \info ->
              Map.lookup (ciData info) (csDatas st) of
              Just dataInfo
                | all (\dataConstructor -> KCtor dataConstructor `elem` map fst signature)
                    (diCtors dataInfo) ->
                    Just signature
              _ -> Nothing
          _ -> Nothing
   in case completeSignature of
        Just signature ->
          or
            [ wildUseful st (specializeRows st k a rows) (a + n - 1)
            | (k, a) <- signature
            ]
        Nothing -> wildUseful st (defaultRows st rows) (n - 1)

-- | Expand a binder-free catch-all into the finite constructor/product
-- skeletons not covered by preceding unguarded rows. This is a typed pattern
-- certificate, not an exhaustiveness guess: expansion is available only for
-- closed nominal sums and structural products whose complete constructor
-- signature is known, and is bounded to keep elaboration predictable. The
-- resulting source patterns are re-elaborated normally, so nested branch
-- refinements are serialized in the emitted Core alternatives.
residualCatchAllPatterns
  :: CheckState
  -> Value
  -> [(CorePat, Maybe Term)]
  -> Span
  -> Maybe [Pattern]
residualCatchAllPatterns state scrutineeType preceding site = do
  residuals <- uncoveredFinitePatternSkeletons state scrutineeType preceding
  mapM (skeletonSourcePattern state site) residuals

-- | Enumerate the bounded, structurally complete residual space without
-- interpreting dependency between product fields. Callers may subsequently
-- discharge an individual skeleton only through the typed empty-fiber
-- judgment; this helper alone is never an exhaustiveness proof.
uncoveredFinitePatternSkeletons
  :: CheckState
  -> Value
  -> [(CorePat, Maybe Term)]
  -> Maybe [CorePat]
uncoveredFinitePatternSkeletons state scrutineeType preceding = do
  candidates <- finitePatternSkeletons state 64 scrutineeType
  let covered = [pattern' | (pattern', Nothing) <- preceding]
  pure
    [ candidate
    | candidate <- candidates
    , not (any (`corePatternCovers` candidate) covered)
    ]

finitePatternSkeletons :: CheckState -> Int -> Value -> Maybe [CorePat]
finitePatternSkeletons state budget = go budget . force (ecOf state)
  where
    go remaining value
      | remaining <= 0 = Nothing
      | otherwise = case value of
          VUniverseLift _ _ _ inner -> go remaining (force (ecOf state) inner)
          VRecordTQ fields -> do
            alternatives <- mapM (go remaining . rfType) fields
            products <- boundedCartesian remaining alternatives
            pure (map CPTuple products)
          VRecordT fields -> do
            alternatives <- mapM (go remaining . snd) fields
            products <- boundedCartesian remaining alternatives
            pure (map CPTuple products)
          VGlobN family _ -> nominal remaining family
          VGlobI family _ _ -> nominal remaining family
          _ -> Nothing
    nominal remaining family = do
      dataInfo <- Map.lookup family (csDatas state)
      guard (not (null (diCtors dataInfo)))
      constructors <- mapM constructorSkeleton (diCtors dataInfo)
      guard (length constructors <= remaining)
      pure constructors
    constructorSkeleton constructor = do
      info <- Map.lookup constructor (csCtors state)
      pure
        ( CPCtorM
            []
            []
            []
            constructor
            []
            (replicate (length (ciFields info)) CPWild)
        )

boundedCartesian :: Int -> [[a]] -> Maybe [[a]]
boundedCartesian budget alternatives =
  let cardinality = product (map length alternatives)
   in if cardinality > budget
        then Nothing
        else Just (sequence alternatives)

corePatternCovers :: CorePat -> CorePat -> Bool
corePatternCovers covering candidate = case covering of
  CPWild -> True
  CPVar _ -> True
  CPAs _ nested -> corePatternCovers nested candidate
  CPOr alternatives _ -> any (`corePatternCovers` candidate) alternatives
  CPCtor constructor _ fields -> case candidate of
    CPCtor candidateConstructor _ candidateFields ->
      constructor == candidateConstructor
        && length fields == length candidateFields
        && and (zipWith corePatternCovers fields candidateFields)
    _ -> False
  CPTuple fields -> case candidate of
    CPTuple candidateFields ->
      length fields == length candidateFields
        && and (zipWith corePatternCovers fields candidateFields)
    _ -> False
  CPLit literal -> case candidate of
    CPLit candidateLiteral -> literal == candidateLiteral
    _ -> False
  _ -> False

skeletonSourcePattern :: CheckState -> Span -> CorePat -> Maybe Pattern
skeletonSourcePattern state site = \case
  CPWild -> Just (PWild site)
  CPTuple fields -> PTuple <$> mapM (skeletonSourcePattern state site) fields <*> pure site
  CPCtor constructor _ fields -> do
    info <- Map.lookup constructor (csCtors state)
    nested <- mapM (skeletonSourcePattern state site) fields
    let qualifier = Name (gnameText (ciData info)) site
        constructorName = Name (gnameText constructor) site
    pure
      ( PCtor
          (CtorRef (Just qualifier) constructorName)
          nested
          site
      )
  _ -> Nothing

emptyPatternRefinements :: PatternRefinements
emptyPatternRefinements = PatternRefinements Map.empty

withPatternRefinements :: PatternRefinements -> CheckM a -> CheckM a
withPatternRefinements (PatternRefinements refinements) action = do
  surrounding <- gets csFacts
  modify' $ \state ->
    state {csFacts = Map.union refinements surrounding}
  result <- action
  modify' $ \state -> state {csFacts = surrounding}
  pure result

-- | Build a compiler-generated constructor eliminator from the same checked
-- source-field telescope used to instantiate the constructor.  This is the
-- single offset authority for synthetic projections, @is@ tests, and
-- match-and-rebuild updates: omitted implicit fields introduce hidden branch
-- slots at their declared positions, and explicit binder indices are computed
-- from that complete layout.
--
-- The constructor identity and instantiated Pi binders authenticate the
-- layout.  Any disagreement with 'ciSourceFields' reports an internal error and
-- returns 'Nothing'; callers must not guess a prefix/suffix offset.
syntheticConstructorPatternLayout
  :: Span
  -> GName
  -> [Level]
  -> CtorInfo
  -> [(Int, Text, ObservationMode, Q, Value)]
  -> [CorePat]
  -> CheckM (Maybe SyntheticConstructorPatternLayout)
syntheticConstructorPatternLayout
  site
  constructor
  universes
  info
  namedBinders
  explicitPatterns =
    case sourceBinders of
      Nothing -> invalid
      Just source ->
        case build 0 0 source explicitPatterns [] [] [] of
          Just (binderCount, hidden, patterns, positions) ->
            pure
              ( Just
                  SyntheticConstructorPatternLayout
                    { scplPattern =
                        CPCtorM [] [] hidden constructor universes patterns
                    , scplExplicitBinderIndices =
                        [ fmap (\position -> binderCount - position - 1) entry
                        | entry <- positions
                        ]
                    , scplBinderCount = binderCount
                    }
              )
          Nothing -> invalid
  where
    sourceCount = length (ciSourceFields info)
    sourceBinders
      | sourceCount > length namedBinders = Nothing
      | otherwise = do
          let suffix = drop (length namedBinders - sourceCount) namedBinders
          guard (length suffix == sourceCount)
          let source = zip (ciSourceFields info) suffix
          guard
            ( and
                [ maybe True (== binderName) sourceName
                | ((_, sourceName), (_, binderName, _, _, _)) <- source
                ]
            )
          pure source

    build
      binderOffset
      explicitPrefix
      []
      []
      hidden
      patterns
      positions =
        Just
          ( binderOffset
          , reverse hidden
          , reverse patterns
          , reverse positions
          )
    build
      binderOffset
      explicitPrefix
      (((Impl, _), (_, _, mode, _, _)) : source)
      patterns
      hidden
      builtPatterns
      positions =
        build
          (binderOffset + 1)
          explicitPrefix
          source
          patterns
          (ConstructorHiddenBinder explicitPrefix mode : hidden)
          builtPatterns
          positions
    build
      binderOffset
      explicitPrefix
      (((Expl, _), (_, _, mode, _, _)) : source)
      (pattern' : patterns)
      hidden
      builtPatterns
      positions =
        let checkedPattern = setOuterMode mode pattern'
            binderCount = patBindersC checkedPattern
            position
              | binderCount == 1 = Just binderOffset
              | otherwise = Nothing
         in build
              (binderOffset + binderCount)
              (explicitPrefix + 1)
              source
              patterns
              hidden
              (checkedPattern : builtPatterns)
              (position : positions)
    build _ _ _ _ _ _ _ = Nothing

    setOuterMode mode = \case
      CPVarM _ name -> CPVarM mode name
      CPAsM _ name pattern' -> CPAsM mode name pattern'
      pattern' -> pattern'

    invalid = do
      errAt
        site
        "E_INTERNAL_CONSTRUCTOR_TELESCOPE"
        (Just "kappa.internal.compiler")
        ( "generated constructor pattern for "
            <> gnameText constructor
            <> " does not match its checked source-field telescope"
        )
      pure Nothing

-- | Orient a residual definitional equation toward an acyclic branch-local
-- stable-subject substitution. Either source direction may expose the subject.
orientRefinement
  :: Ctx
  -> Value
  -> Value
  -> CheckM (Maybe (RefinementSubject, Value))
orientRefinement ctx left0 right0 = do
  left <- forceM left0
  right <- forceM right0
  rightToLeft <- directedRefinement ctx right left
  case rightToLeft of
    Just refinement -> pure (Just refinement)
    Nothing -> directedRefinement ctx left right

directedRefinement
  :: Ctx
  -> Value
  -> Value
  -> CheckM (Maybe (RefinementSubject, Value))
directedRefinement ctx candidate0 replacement0 = do
  candidate <- forceM candidate0
  replacement <- forceM replacement0
  ec <- ec_
  pure (orient ec candidate replacement)
  where
    orient ec candidate replacement
      | Just subject <- refinementSubject candidate
      , refinementSubjectInScope subject
      , not (subjectOccurs ec subject replacement) =
          Just (subject, replacement)
    orient _ _ _ = Nothing

    refinementSubjectInScope subject =
      subjectRoot subject >= 0 && subjectRoot subject < ctxLen ctx

    subjectRoot = \case
      RefinementRigid rigid -> rigid
      RefinementProjection parent _ -> subjectRoot parent

    -- Reject every replacement mentioning the subject's root binder. This is
    -- deliberately more conservative than path-sensitive occurs checking:
    -- it cannot admit a cyclic projection equation, and independent sibling
    -- projection equations remain a future widening rather than an unsound
    -- conversion rule.
    subjectOccurs ec subject value =
      let depth = ctxLen ctx
          rigid = subjectRoot subject
          index = depth - rigid - 1
       in index >= 0 && mentionsVar index (quote ec depth value)

-- | Recover the root constructor's checked definitional equations at the
-- final pattern context depth.  Propositional bridges remain lexical proof
-- binders and never become conversion facts; only equations already certified
-- as 'ConstructorForcedEquality' may orient a rigid variable.
rootConstructorForcedRefinements
  :: Ctx
  -> CorePat
  -> CheckM (Map RefinementSubject RigidFact)
rootConstructorForcedRefinements ctx = \case
  CPCtorM _ bridges _ _ _ _ ->
    foldM addBridge Map.empty bridges
  _ -> pure Map.empty
  where
    addBridge refinements = \case
      ConstructorForcedEquality leftTerm rightTerm -> do
        left <- evalIn ctx leftTerm
        right <- evalIn ctx rightTerm
        orientRefinement ctx left right >>= \case
          Nothing -> pure refinements
          Just (subject, replacement) ->
            pure (Map.insert subject (FactIs replacement) refinements)
      ConstructorPropositionalBridge {} -> pure refinements
