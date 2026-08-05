-- | Assorted elaboration helpers.
--
-- Support used directly by the bidirectional core in "Kappa.Check" that is
-- not specific to any one syntactic form.
--
-- Carved out of "Kappa.Check" as part of splitting that module; see
-- "Kappa.Check.Types" for the shared data dictionary and docs\/CONCEPTS.md
-- for the vocabulary these assume.
module Kappa.Check.Elab
  ( deriveGoalRigid
  , exactLocalRuntimeErasureEvidence
  , fastListLiteral
  , finishExplicitArgument
  , lamSection
  , postponeEqualityEvidence
  , preexistingAssignmentsUnchanged
  , principalPlanningSynthesis
  , recordInferredMetaUniverseCoercion
  , renameLevelFieldAssumption
  , renameThisLabels
  , reportQuantityBorrowMarker
  , retagExplicitImplicitFailure
  , retagNew
  , retagNewMismatches
  , retagTerminalFailureArmMismatch
  , schemaLevelTermsAuthenticated
  , tagOf
  , unresolvedExpectedClassifierLevels
  , visibleDerivationLocals
  , withArgFlatFor
  , withArgIndexRetag
  , withDefinitionalEqualityOnly
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

postponeEqualityEvidence :: Ctx -> Span -> Value -> CheckM Term
postponeEqualityEvidence ctx site goal = do
  (meta, placeholder) <- freshMetaForWithId ctx goal
  facts <- gets csBoolFacts
  modify' $ \state ->
    state {csPending = (meta, goal, site, ctx, facts) : csPending state}
  pure placeholder

-- | Whether a bare derivation request has the rigid expected goal required by
-- §16.3.2A. Ordinary and universe metavariables both make the request
-- under-directed; an explicit @derive (G)@ is checked by the normal type
-- elaborator and does not use this guard.
deriveGoalRigid :: Ctx -> Value -> CheckM Bool
deriveGoalRigid _ goal =
  forceM goal >>= \case
    VFlex {} -> pure False
    _ -> pure True

visibleDerivationLocals :: Ctx -> [(Int, CtxEntry)]
visibleDerivationLocals ctx = go Set.empty 0 (ctxEntries ctx)
  where
    go _ _ [] = []
    go shadowed index (entry : rest)
      | ceName entry `Set.member` shadowed =
          go shadowed (index + 1) rest
      | otherwise =
          let name = ceName entry
              referenceable =
                name `notElem` ["_", "_ev", "this"]
                  && isNothing (ceVarInfo entry)
              shadowed' = Set.insert name shadowed
           in (if referenceable then [(index, entry)] else [])
                ++ go shadowed' (index + 1) rest

-- | Emit the dedicated §3.2.6 diagnostic for an expression-position borrow
-- marker. Keeping this marker in the parsed tree lets the enclosing
-- declaration continue through ordinary checking without reinterpreting @&@
-- as an operator or dropping the declaration during parser recovery.
reportQuantityBorrowMarker :: Span -> CheckM ()
reportQuantityBorrowMarker sp = do
  diagnostics <- gets csDiags
  unless
    ( any
        (\diagnostic ->
           dCode diagnostic == "E_QUANTITY_BORROW_NOT_QUANTITY"
             && dPrimary diagnostic == sp
        )
        diagnostics
    ) $
    report $
      withPayload
        ( withPayloadField "sourceExpression" "&" $
            withPayloadField "expectedClassifier" "Quantity" $
              withPayloadField "sourceOrigin" (T.pack (show sp)) $
                withPayloadField "enclosingDeclaration" "<current declaration>" $
                  withPayloadField "reason" "borrowed binder access is not a quantity" $
                    withPayloadField
                      "repairHint"
                      "use (& x : A), (1 & x : A), or an interval quantity such as 1, <=1, >=1, or ω"
                      (payloadKind "quantity-borrow-confusion")
        ) $
        diag
          SevError
          StageElaborate
          "E_QUANTITY_BORROW_NOT_QUANTITY"
          (Just "kappa.quantity.borrow-not-quantity")
          sp
          "'&' is not a Quantity; it is a borrowed binder access marker (§3.2.6, §12.1.1)"

-- | List literal syntax names the canonical prelude family and constructors,
-- so its desugaring may reuse their independently checked constructor
-- interfaces. This avoids re-running general constructor application and
-- conversion against the complete, growing nested-list type at every node.
-- Every semantic premise is authenticated by identity and typed metadata;
-- disagreement uses the ordinary generated-constructor path above.
fastListLiteral :: Value -> Term -> [Term] -> CheckM (Maybe Term)
fastListLiteral listType elementTypeTerm terms = do
  state <- get
  forcedListType <- forceM listType
  case
      ( forcedListType
      , Map.lookup prelList (csDatas state)
      , Map.lookup prelNil (csCtors state)
      , Map.lookup prelCons (csCtors state)
      )
    of
      ( VGlobI family universes [(_, _)]
        , Just dataInfo
        , Just nilInfo
        , Just consInfo
        )
          | family == prelList
          , diParamCount dataInfo == 1
          , prelNil `elem` diCtors dataInfo
          , prelCons `elem` diCtors dataInfo
          , ciData nilInfo == prelList
          , ciData consInfo == prelList
          , null (ciSourceFields nilInfo)
          , map fst (ciSourceFields consInfo) == [Expl, Expl]
          , constructorUniverseArity nilInfo == length universes
          , constructorUniverseArity consInfo == length universes -> do
              nilEta <- specializedEta nilInfo prelNil universes
              consEta <- specializedEta consInfo prelCons universes
              pure $ do
                nilTerm <-
                  instantiateEtaConstructor
                    [(Impl, elementTypeTerm)]
                    nilEta
                foldM
                  (\tailTerm headTerm ->
                    instantiateEtaConstructor
                      [ (Impl, elementTypeTerm)
                      , (Expl, headTerm)
                      , (Expl, tailTerm)
                      ]
                      consEta
                  )
                  nilTerm
                  (reverse terms)
      _ -> pure Nothing
  where
    constructorUniverseArity = dutParameterCount . ciUniverses

    specializedEta constructorInfo constructor universes = do
      assignments <- gets csLevelAssignments
      evaluator <- ec_
      let constructorType =
            specializeDeclarationUniverses
              (ciUniverses constructorInfo)
              universes
              (zonkLevels assignments (ciType constructorInfo))
      pure (etaCtor evaluator constructor universes constructorType)

-- helper shared by section desugarings
lamSection :: Span -> Text -> (Expr -> Expr) -> Expr
lamSection sp nm f =
  ELambda Nothing [simpleBinder (Name nm sp)] (f (EVar (Name nm sp))) sp

-- | Stable member identity of a variant member type (§31.3): rendered
-- from the alias-normalized type so @Int@ and @Integer@ coincide.
tagOf :: Ctx -> Value -> CheckM Text
tagOf ctx v = do
  ec <- ec_
  pure (semanticTypeTag ec (ctxLen ctx) v)

-- | Check the §11.1.2.3A.1 capability boundary structurally. A schema-level
-- value is legal only below a proposition whose comparison head, TypeLevel
-- carrier, and selected Ord dictionary all authenticate by identity. The
-- elaborator calls this at every type-forming boundary, including an outer Pi
-- whose codomain contains a later proof binder, so requiring the whole term to
-- be one comparison incorrectly rejects valid nested telescopes.
--
-- Authenticated proposition subtrees are opaque to the residual scan. Any
-- CLevel left after pruning them occurred outside the capability and is
-- rejected. Same-spelling user operations remain excluded because
-- 'typeLevelRelationSpine' is the sole trust boundary.
schemaLevelTermsAuthenticated :: Term -> CheckM Bool
schemaLevelTermsAuthenticated term = do
  authenticated <- filterM authenticates candidates
  let prune _ candidate
        | candidate `elem` authenticated = Just (CSort LZero)
        | otherwise = Nothing
      residual = mapTermWithDepth prune 0 term
  pure (not (containsSchemaLevel residual))
  where
    candidates =
      nub
        [ candidate
        | candidate <- foldTerm (: []) (const []) term
        , isJust (boolEqualityTruePayload candidate)
        ]

    authenticates candidate = case boolEqualityTruePayload candidate of
      Just relation -> isJust <$> typeLevelRelationSpine relation
      Nothing -> pure False

    containsSchemaLevel = getAny . foldTerm termHasLevel (const mempty)
    termHasLevel = \case
      CLevel _ -> Any True
      _ -> Any False

-- | Rewrite @this.<binderName>@ projections to @this.<internalLabel>@
-- inside an elaborated existential member type, per the binder->label
-- map. Only projections rooted at the §13.2.1 'this' neutral are
-- renamed (other projections keep their labels).
renameThisLabels :: [(Text, Text)] -> Term -> Term
renameThisLabels labelOf =
  zonkTermWith (\_ _ -> Nothing) renameLevel 0 . go
  where
    renameLevel = normalizeLevel . \case
      LField identity field ->
        LField identity (fromMaybe field (lookup field labelOf))
      LSucc level -> LSucc (renameLevel level)
      LAdd lhs rhs -> LAdd (renameLevel lhs) (renameLevel rhs)
      LMax lhs rhs -> LMax (renameLevel lhs) (renameLevel rhs)
      other -> other
    go t = case t of
      CUniverseLift from to evidence inner ->
        CUniverseLift from to evidence (go inner)
      CSchemaLift family source target roles evidence certificate sourceArguments targetArguments inner ->
        CSchemaLift family (map renameLevel source) (map renameLevel target) roles
          (map (mapSchemaRoleEvidence renameLevel) evidence) certificate
          (map go sourceArguments) (map go targetArguments) (go inner)
      CProjM mode e f
        | CGlob g <- e, g == thisG, Just lbl <- lookup f labelOf -> CProjM mode e lbl
        | otherwise -> CProjM mode (go e) f
      -- P0.4: renaming a this-label invalidates the fixed offset, so DROP to a
      -- name-based CProj when renamed; otherwise keep the CProjAt index.
      CProjAtM mode e f i
        | CGlob g <- e, g == thisG, Just lbl <- lookup f labelOf -> CProjM mode e lbl
        | otherwise -> CProjAtM mode (go e) f i
      CLamM mode ic q n b -> CLamM mode ic q n (go b)
      CPiRuntimeM mode formation ic q brw n assumption origin runtimeErasure a b ->
        CPiRuntimeM mode formation ic q brw n assumption origin
          (fmap go runtimeErasure)
          (go a)
          (go b)
      CAppM ic runtimeErasure f a ->
        CAppRuntime ic (fmap go runtimeErasure) (go f) (go a)
      CCtorI g universes ann arguments ->
        CCtorI g universes (fmap go ann)
          [argument {caTerm = go (caTerm argument)} | argument <- arguments]
      CMatch s ann resultAnn alts ->
        CMatch
          (go s)
          (fmap go ann)
          (fmap go resultAnn)
          [CaseAlt p (fmap go gd) (go b) | CaseAlt p gd b <- alts]
      CRecordTQ fs -> CRecordTQ (map (fmap go) fs)
      CRecordV fs -> CRecordV [(n, go x) | (n, x) <- fs]
      CVariantT ms -> CVariantT (map go ms)
      CInject tag e -> CInject tag (go e)
      CLetRuntimeM mode q n runtimeErasure a b c ->
        CLetRuntimeM mode q n (fmap go runtimeErasure) (go a) (go b) (go c)
      CLetRecRuntimeM mode q n runtimeErasure a b c ->
        CLetRecRuntimeM mode q n (fmap go runtimeErasure) (go a) (go b) (go c)
      CLetPolyRuntimeM mode q n telescope runtimeErasure a b c ->
        CLetPolyRuntimeM mode q n telescope (fmap go runtimeErasure) (go a) (go b) (go c)
      CLetRecPolyRuntimeM mode q n telescope runtimeErasure a b c ->
        CLetRecPolyRuntimeM mode q n telescope (fmap go runtimeErasure) (go a) (go b) (go c)
      CLetRecGroupM telescope definitions body ->
        CLetRecGroupM telescope
          [ definition
              { clrdRuntimeErasure = fmap go (clrdRuntimeErasure definition)
              , clrdType = go (clrdType definition)
              , clrdRhs = go (clrdRhs definition)
              }
          | definition <- definitions
          ]
          (go body)
      CSealE ls e -> CSealE ls (go e)
      CSigT ls e -> CSigT ls (go e)
      CThunkE e suspensionType -> CThunkE (go e) (go <$> suspensionType)
      CLazyE e suspensionType -> CLazyE (go e) (go <$> suspensionType)
      CForceE e resultType -> CForceE (go e) (go <$> resultType)
      CIf a b c -> CIf (go a) (go b) (go c)
      CQuote qs slots -> CQuote qs (map go slots)
      CGlobal _ _ -> t
      CLocal _ _ -> t
      CVar _ -> t
      CSort _ -> t
      CLevel _ -> t
      CLit _ -> t
      CMeta _ -> t
      CDo _ _ -> t

-- | Existential alpha-renaming applies to authenticated level assumptions as
-- well as their field types. Keeping either endpoint under a source witness
-- label would detach the proof metadata from the canonical hidden telescope.
renameLevelFieldAssumption
  :: [(Text, Text)]
  -> Maybe (Level, Level)
  -> Maybe (Level, Level)
renameLevelFieldAssumption labelOf = fmap (\(lower, upper) -> (renameLevel lower, renameLevel upper))
  where
    renameLevel = normalizeLevel . \case
      LField identity field ->
        LField identity (fromMaybe field (lookup field labelOf))
      LSucc level -> LSucc (renameLevel level)
      LAdd lhs rhs -> LAdd (renameLevel lhs) (renameLevel rhs)
      LMax lhs rhs -> LMax (renameLevel lhs) (renameLevel rhs)
      other -> other

-- | Preserve whether the enclosing call has a resolved ordinary-function
-- head while checking its argument. Nested applications must not replace that
-- outer diagnostic context with the nested expression's head classification.
withArgFlatFor :: Expr -> CheckM a -> CheckM a
withArgFlatFor function action = do
  previous <- gets csArgFlatOk
  checkingOuterArgument <- gets csArgIndexRetag
  ordinaryFunction <-
    if checkingOuterArgument
      then pure previous
      else case function of
        EOpRef {} -> pure False
        EVar name ->
          lookupGlobalName (nameText name) >>= \case
            Just global -> gets (not . Map.member global . csCtors)
            Nothing -> pure False
        _ -> pure False
  modify' $ \state -> state {csArgFlatOk = ordinaryFunction}
  result <- action
  modify' $ \state -> state {csArgFlatOk = previous}
  pure result

-- | Run an explicit-argument check with §16.1.7.1/§16.1.8 argument-index
-- retagging enabled, restoring the prior flag afterward. A mismatch
-- raised while checking an explicit argument against its parameter type
-- is reclassified as an application-argument error (see 'expectType').
withArgIndexRetag :: CheckM a -> CheckM a
withArgIndexRetag act = do
  old <- gets csArgIndexRetag
  modify' $ \st -> st {csArgIndexRetag = True}
  r <- act
  modify' $ \st -> st {csArgIndexRetag = old}
  pure r

-- | Check one explicit argument @e@ of quantity @q@ against the binder
-- domain @dom@, shared by the two application-spine algorithms (the
-- 'Slot'-folding 'step' and the recursive 'elabSpine'). The argument is
-- checked under the binder's demand ('demandOfQ') with argument-index
-- retagging enabled (§16.1.7.1) so any equality mismatch is attributed
-- to this argument slot. A non-type argument supplied to a type-former's
-- @Type@ slot is an application-argument error rather than a plain
  -- mismatch (§16.1), so when @dom@ is a universe the freshly emitted
  -- mismatches are retagged via 'retagNewMismatches'; for the ordinary
  -- (non-sort) domain this branch is a no-op.

-- | Whether an explicit operand may soundly pin an application-planning meta
-- from its synthesized type. Unsuffixed overloaded literals have no principal
-- carrier in isolation: inference applies the §6.1.5 default, while checking
-- deliberately leaves @FromInteger ?a@ / @FromFloat ?a@ pending for later
-- operands and the expected result. An ascription or suffix makes the carrier
-- source-determined again and therefore follows the ordinary exact probe.
principalPlanningSynthesis :: Expr -> Bool
principalPlanningSynthesis = \case
  EIntLit _ Nothing _ -> False
  EFloatLit _ Nothing _ -> False
  _ -> True

-- | Record the observation/erasure obligations shared by ordinary checked
-- arguments and the exact inferred arguments used in instance heads.
finishExplicitArgument
  :: Ctx
  -> ObservationMode
  -> Q
  -> Bool
  -> Bool
  -> Expr
  -> Term
  -> Value
  -> CheckM ()
finishExplicitArgument ctx mode q borrowed evidenceErased expression term classifier = do
  evaluation <- ec_
  -- Export the same checked erasure decision consumed by representation and
  -- backend lowering. Quantity zero is only one erasure source: kind domains
  -- and proof domains established RuntimeErased are static arguments too.
  -- Usage receives the occurrence identity and never re-derives this fact
  -- from source spelling or a hard-coded proof/operator name.
  when (evidenceErased || Repr.runtimeErasedParam evaluation (ctxLen ctx) q classifier) $
    modify' $ \state ->
      state
        { csErasedArgumentSpans =
            Set.insert (exprSpan expression) (csErasedArgumentSpans state)
        }
  when borrowed $
    modify' $ \state ->
      state
        { csBorrowedArgumentDemands =
            Map.insert (exprSpan expression) q (csBorrowedArgumentDemands state)
        }
  when (mode == Ordinary) $ do
    observation <- observationJudgmentForTerm ctx term classifier
    when (ojMode observation == Parametric) $
      reportParametricPromotion
        (exprSpan expression)
        "ordinary application argument"
        observation

-- | Select a local @RuntimeErased carrier@ dictionary before constructing a
-- fresh trait occurrence. The local's checked type is retained as the exact
-- goal, including its already-selected universe instantiation. This keeps
-- representation discovery read-only even before declaration universe metas
-- have been generalized.
exactLocalRuntimeErasureEvidence :: Ctx -> Value -> CheckM (Maybe (Value, Term))
exactLocalRuntimeErasureEvidence ctx carrier = do
  state <- get
  let evaluation = ecOf state
  go state evaluation 0 [] (ctxEntries ctx) >>= \case
    Just selected -> pure (Just selected)
    Nothing -> pure (thisEvidence state evaluation)
  where
    shadowName entry = [ceName entry | ceName entry `notElem` ["_", "_ev"]]
    go _ _ _ _ [] = pure Nothing
    go state evaluation index seen (entry : rest) = do
      let level = ctxLen ctx - 1 - index
          borrowEscapes =
            ceBorrow entry && any (> level) (ctxBarriers ctx)
          visible = ceName entry `notElem` seen
          -- Keep the checked trait head neutral here. Forcing a trait goal
          -- delta-unfolds its dictionary record and destroys the resolved
          -- semantic identity needed to authenticate RuntimeErased.
          candidateCarrier = case ceType entry of
            VGlobI trait _ arguments
              | trait == prelRuntimeErased ->
                  case traitSemanticSpineIn state trait arguments of
                    Just [(Expl, selectedCarrier)] -> Just selectedCarrier
                    _ -> Nothing
            _ -> Nothing
          matches =
            visible
              && not borrowEscapes
              && maybe False
                (convertible evaluation (ctxLen ctx) carrier)
                candidateCarrier
       in if matches
            then pure (Just (ceType entry, CVar index))
            else go state evaluation (index + 1) (shadowName entry ++ seen) rest

    -- Dependent record telescopes expose earlier fields through the semantic
    -- @this@ root rather than ordinary de Bruijn locals. A prior erased
    -- evidence field is therefore selected by its checked field identity and
    -- retained as a projection; fabricating a dictionary would lose both its
    -- type and its dependency on the record telescope.
    thisEvidence state evaluation =
      listToMaybe
        [ (rfType field, CProjM (rfMode field) (CGlob thisG) (rfName field))
        | field <- thisFields (csThis state)
        , Just selectedCarrier <- [runtimeErasedCarrier state (rfType field)]
        , convertible evaluation (ctxLen ctx) carrier selectedCarrier
        ]

    thisFields = \case
      Just (ThisType fields) -> fields
      Just (ThisTraitSibs fields) -> fields
      Just (ThisValue _ fields) -> fields
      Nothing -> []

    runtimeErasedCarrier state = \case
      VGlobI trait _ arguments
        | trait == prelRuntimeErased ->
            case traitSemanticSpineIn state trait arguments of
              Just [(Expl, selectedCarrier)] -> Just selectedCarrier
              _ -> Nothing
      _ -> Nothing

-- | An optional semantic probe may allocate and solve fresh internal metas,
-- but it must not improve any assignment that existed at the call boundary.
-- Otherwise evidence can depend on a speculative refinement that is erased by
-- the surrounding rollback, leaving a closed-looking certificate whose source
-- derivation is no longer well typed. This checks both term and universe metas;
-- fresh entries are deliberately ignored because the returned Core term is
-- independently zonked and closure-checked before it escapes.
preexistingAssignmentsUnchanged :: CheckState -> CheckState -> Bool
preexistingAssignmentsUnchanged before after =
  all
    (\(meta, assignment) ->
       fmap isJust (Map.lookup meta (csMetas after)) == Just (isJust assignment)
         && Map.lookup meta (csMetaAssignmentGenerations before)
              == Map.lookup meta (csMetaAssignmentGenerations after))
    (Map.toList (csMetas before))
    && all
      (\(meta, assignment) -> Map.lookup meta (csLevelAssignments after) == Just assignment)
      (Map.toList (csLevelAssignments before))
    && all
      (\meta ->
         meta >= csNextMeta before
           || Map.member meta (csLevelAssignments before))
      (Map.keys (csLevelAssignments after))

-- | Preserve the unsolved part of a higher-kinded trait parameter's checked
-- classifier.  Exact checking has already assigned every level forced by a
-- monomorphic argument, so the residual metas are precisely the abstract
-- classifier dimensions that the generated instance dictionary must own.
-- Reading the expected classifier after checking avoids treating fresh
-- occurrence metas from the observational inference probe as source schema.
unresolvedExpectedClassifierLevels :: Ctx -> Value -> CheckM (Set LevelMeta)
unresolvedExpectedClassifierLevels ctx expected = do
  expectedTerm <- quoteIn ctx expected >>= zonkTermM (ctxLen ctx)
  pure (Set.fromList (levelMetasOfTerm expectedTerm))

withDefinitionalEqualityOnly :: CheckM a -> CheckM a
withDefinitionalEqualityOnly act = do
  old <- gets csDefinitionalEqualityOnly
  modify' $ \st -> st {csDefinitionalEqualityOnly = True}
  result <- act
  modify' $ \st -> st {csDefinitionalEqualityOnly = old}
  pure result

-- | Attach a cumulative proof only to the typed inference meta whose
-- creation-site classifier was checked above. Non-meta generated arguments
-- are coerced directly by 'coerceTerm'; recovery terms deliberately do not
-- acquire guessed metadata.
recordInferredMetaUniverseCoercion :: Term -> UniverseEvidence -> CheckM ()
recordInferredMetaUniverseCoercion term evidence =
  case term of
    CMeta meta ->
      modify' $ \st ->
        st
          { csMetaClassifiers =
              Map.adjust
                (\classifier ->
                   classifier
                     { micUniverseCoercion =
                         micUniverseCoercion classifier <|> Just evidence
                     })
                meta
                (csMetaClassifiers st)
          }
    _ -> pure ()

-- | Apply a rewrite to every diagnostic reported since a marker.
-- @nBefore@ is the @length csDiags@ captured before the elaboration
-- step whose newly-added diagnostics are to be re-tagged; @retag@ is
-- the per-diagnostic rewrite (applied only to the new prefix, leaving
-- the older diagnostics untouched). Shared skeleton for the
-- count-and-rollback re-tag idiom (§3.1.4).
retagNew :: Int -> (Diagnostic -> Diagnostic) -> CheckM ()
retagNew nBefore retag = modify' $ \st ->
  let ds = csDiags st
      (new, old) = splitAt (length ds - nBefore) ds
   in st {csDiags = map retag new ++ old}

-- | Re-tag type mismatches reported since the marker as
-- application-argument errors (a literal in a Type parameter slot).
retagNewMismatches :: Int -> CheckM ()
retagNewMismatches nBefore = retagNew nBefore $ \d ->
  if dCode d == "E_TYPE_EQUALITY_MISMATCH"
    then d {dCode = "E_APPLICATION_ARGUMENT_MISMATCH", dFamily = Just "kappa.application.argument-mismatch"}
    else d

-- | A @let? ... else@ expression arm is checked against the whole
-- @m Void@ terminal contract (§18.2.1). Expected-directed checking is needed
-- to select @m@ before resolving overloaded operations, but it can expose an
-- inner numeric-literal witness failure for a branch such as @pure 42@. At
-- this boundary the primary failure is that the completed action is not an
-- @m Void@ action, so retain all unrelated diagnostics and reclassify only
-- that contextual literal failure as the enclosing type mismatch.
retagTerminalFailureArmMismatch :: Int -> CheckM ()
retagTerminalFailureArmMismatch nBefore = retagNew nBefore $ \diagnostic ->
  if dFamily diagnostic == Just "kappa.type.literal-domain-mismatch"
    then
      diagnostic
        { dCode = "E_TYPE_EQUALITY_MISMATCH"
        , dFamily = Just "kappa.type.mismatch"
        }
    else diagnostic

-- | §3.1.4/§16.1.7.2: re-tag any error diagnostics reported since the
-- marker with the portable @E_EXPLICIT_IMPLICIT_CLASSIFIER_MISMATCH@
-- code (family @kappa.application.explicit-implicit-classifier@). This
-- is the general rewrite for a failed elaboration of an explicit
-- implicit argument's @\@payload@ against the selected implicit
-- binder's demanded type or classifier: §16.1.7.2 step 6 says the
-- explicit implicit argument fails for that binder when the selected
-- elaboration mode fails, and §3.2 lists typing, classifier mismatch,
-- quantity mismatch, unresolved name, and ambiguous name as in-scope
-- payload-failure kinds — so the payload-internal code (whatever it
-- happens to be) is replaced rather than special-cased on its spelling.
retagExplicitImplicitFailure :: Int -> CheckM ()
retagExplicitImplicitFailure nBefore = retagNew nBefore $ \d ->
  if isError d && dFamily d /= Just "kappa.var.mutable-binding"
    then
      d
        { dCode = "E_EXPLICIT_IMPLICIT_CLASSIFIER_MISMATCH"
        , dFamily = Just "kappa.application.explicit-implicit-classifier"
        }
    else d

-- ── Projection applications (§16.1.5, §16.1.6) ───────────────────────
