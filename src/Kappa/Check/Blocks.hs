-- | Lambdas, @let@ bindings, and block scoping.
--
-- Helpers for binder-introducing forms: finalizing a lambda's inferred
-- contracts, qualifying block-local declaration identities, and the
-- bookkeeping that keeps local universe telescopes well-scoped.
--
-- Carved out of "Kappa.Check" as part of splitting that module; see
-- "Kappa.Check.Types" for the shared data dictionary and docs\/CONCEPTS.md
-- for the vocabulary these assume.
module Kappa.Check.Blocks
  ( generalizeLocalDeclarationMetas
  , generalizeLocalDeclarationUniverses
  , generalizeLocalDeclarationUniversesWithRoles
  , generalizeLocalDeclarationUniversesWithRolesRaw
  , localDataCaptureTelescope
  , renameLocalDataDeclaration
  , validateInferredLambdaGeneralization
  , withLocalNominalEscapeBoundary
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

-- | Principalize and generalize one completed local declaration boundary.
-- Only level metas allocated while elaborating this declaration and still
-- observable in its type can enter the local telescope. Dependency-use metas
-- remain minimizable occurrence choices, and outer declaration parameters are
-- already rigid 'LParam's (§11.1.2.3A.1, §11.1.2.4A).
generalizeLocalDeclarationMetas
  :: Int
  -> Ctx
  -> Span
  -> [Text]
  -> Term
  -> Term
  -> CheckM (Term, Term)
generalizeLocalDeclarationMetas firstMeta ctx diagnosticSpan declarations ty0 rhs0 = do
  ty <- zonkTermM (ctxLen ctx) ty0
  rhs <- zonkTermM (ctxLen ctx) rhs0
  st <- get
  -- Evidence obligations outrank fresh declaration generalization. A meta
  -- mentioned by a postponed goal is constrained by that goal, even when the
  -- goal cannot yet be selected. Excluding it prevents @newRef None@ from
  -- quantifying over the enclosing monad while leaving unrelated universe
  -- proofs deferred until their level variables are principalized.
  pendingMetas <-
    nub . concat
      <$> mapM (unsolvedMetaIdsIn . pendingGoal) (csPending st)
  let ordinaryMetas = nub . foldTerm collect (const [])
      collect = \case
        CMeta meta -> [meta]
        _ -> []
      localUnsolved meta =
        meta >= firstMeta
          && meta `notElem` pendingMetas
          && case Map.lookup meta (csMetas st) of
            Just (Just _) -> False
            _ -> True
      candidates =
        sort
          [ meta
          | meta <- ordinaryMetas ty
          , localUnsolved meta
          , Just classifier <- [Map.lookup meta (csMetaClassifiers st)]
          , micDepth classifier == ctxLen ctx
          ]

  binders <- selectBinders st ordinaryMetas [] candidates
  if null binders
    then pure (ty, rhs)
    else do
      let metas = map lmbMeta binders
          binderCount = length binders
          abstractAll = abstractMetas metas binderCount
          tyBody = abstractAll ty
          rhsBody = abstractAll rhs
          ty' = foldr makePi tyBody binders
          rhs' = foldr makeLambda rhsBody binders
      validateRigidGeneralization diagnosticSpan declarations ctx binders rhs' ty'
      pure (ty', rhs')
  where
    pendingGoal = peeGoal

    selectBinders _ _ selected [] = pure selected
    selectBinders st ordinaryMetas selected remaining =
      case find (ready st ordinaryMetas (map lmbMeta selected)) remaining of
        Nothing -> pure selected
        Just meta ->
          case Map.lookup meta (csMetaClassifiers st) of
            Nothing -> pure selected
            Just classifier -> do
              let prior = map lmbMeta selected
                  classifier0 =
                    zonkTermWith
                      (resolvedMetaCore st (ecOf st))
                      (substituteLevelMetas (csLevelAssignments st))
                      (ctxLen ctx)
                      (micType classifier)
              classifierValue <- evalIn ctx classifier0
              kindLike <- isKindLike (ctxLen ctx) classifierValue
              if not kindLike
                then selectBinders st ordinaryMetas selected (filter (/= meta) remaining)
                else do
                  formation <- selectFormationMode ctx Parametric classifierValue
                  let domain = abstractMetas prior (length prior) classifier0
                      binder =
                        LocalMetaBinder
                          { lmbMeta = meta
                          , lmbFormation = formation
                          , lmbName = "__generalized" <> T.pack (show (length selected))
                          , lmbDomain = domain
                          }
                  selectBinders st ordinaryMetas (selected ++ [binder]) (filter (/= meta) remaining)

    ready st ordinaryMetas selected meta =
      case Map.lookup meta (csMetaClassifiers st) of
        Nothing -> False
        Just classifier ->
          let dependencies =
                [ dependency
                | dependency <- ordinaryMetas (micType classifier)
                , case Map.lookup dependency (csMetas st) of
                    Just (Just _) -> False
                    _ -> True
                ]
           in all (`elem` selected) dependencies

    abstractMetas metas binderCount term =
      zonkTermWith replace id 0 (shiftTerm binderCount 0 term)
      where
        positions = Map.fromList (zip metas [0 ..])
        replace depth meta = do
          position <- Map.lookup meta positions
          pure (CVar (depth + binderCount - position - 1))

    makePi binder body =
      CPiBoundFormedM Parametric (lmbFormation binder) Impl Q0 False
        (lmbName binder) Nothing (lmbDomain binder) body
    makeLambda binder body = CLamM Parametric Impl Q0 (lmbName binder) body

-- | Recheck a candidate local declaration abstraction with each selected
-- metavariable represented by the rigid parametric binder that will actually
-- appear in Core. The term was already typechecked before abstraction, so the
-- remaining proof obligation is the finite observation judgment: the newly
-- rigid binder must not reach an ordinary sink, and analysis failure is
-- rejected rather than changing the declaration's inferred observation mode.
validateRigidGeneralization
  :: Span
  -> [Text]
  -> Ctx
  -> [LocalMetaBinder]
  -> Term
  -> Term
  -> CheckM ()
validateRigidGeneralization diagnosticSpan declarations = go
  where
    go _ [] _ _ = pure ()
    go ctx (candidate : candidates) (CLamM mode icit quantity name body) typeTerm = do
      typeValue <- evalIn ctx typeTerm >>= forceM
      case typeValue of
        VPiBoundM expectedMode expectedIcit expectedQuantity borrowed _ assumption domain closure
          | mode == expectedMode
          , icit == expectedIcit
          , quantity == expectedQuantity -> do
              withAssumption <- extendLevelAssumption diagnosticSpan ctx assumption
              let rigid = VRigid (ctxLen withAssumption) []
                  nextCtx =
                    bindCtxMQB mode quantity name (icit == Impl) borrowed domain withAssumption
              codomain <- clApp closure rigid
              dependencies <- observationDependenciesForTerm nextCtx body codomain
              let escaped =
                    find
                      ( \case
                          ParametricExternal 0 _ -> True
                          dependency -> dependencyIsAnalysisFailure dependency
                      )
                      (Set.toAscList dependencies)
              case escaped of
                Just dependency -> reportEscape candidate candidates dependency
                Nothing -> do
                  codomainTerm <- quoteIn nextCtx codomain
                  go nextCtx candidates body codomainTerm
        _ -> reportEscape candidate candidates (ParametricAnalysisFailure [] "generalized binder telescope is malformed")
    go _ (candidate : candidates) _ _ =
      reportEscape candidate candidates (ParametricAnalysisFailure [] "generalized term is not a lambda telescope")

    reportEscape candidate remaining dependency = do
      owner <- gets csModule
      let qualifiedDeclarations = qualifyDeclarationIdentities owner declarations
          declarationIdentity = fromMaybe "<anonymous>" (listToMaybe qualifiedDeclarations)
          declarationSccIdentity = T.intercalate "," qualifiedDeclarations
      report $
        withPayload
          ( withPayloadField "declarationIdentity" declarationIdentity $
              withPayloadField "declarationSccIdentity" declarationSccIdentity $
                withPayloadField "failedCandidateKind" "type" $
                  withPayloadField "declarations" (T.intercalate "," qualifiedDeclarations) $
              withPayloadField "sccIdentities" (T.intercalate "," qualifiedDeclarations) $
                withPayloadField "candidateMetavariables"
                  (T.intercalate "," (map (T.pack . show . lmbMeta) (candidate : remaining))) $
                    withPayloadField "candidateClassifiers"
                      (T.intercalate "," (map (renderTerm . lmbDomain) (candidate : remaining))) $
                        withPayloadField "rigidParametricBinders"
                          (T.intercalate "," (map lmbName (candidate : remaining))) $
                            withPayloadField "escapingDependency" (T.pack (show dependency)) $
                              withPayloadField "candidateKind" "type" $
                                withPayloadField "sourceOrigin" (T.pack (show diagnosticSpan)) $
                                  withPayloadField "nearestMonomorphicAnnotation" "none" $
                                    payloadKind "generalization-parametric-escape"
          ) $
          diag SevError StageElaborate "E_GENERALIZATION_PARAMETRIC_ESCAPE"
            (Just "kappa.generalization.parametric-escape") diagnosticSpan
            "candidate declaration generalization observes a rigid parametric binder in an ordinary position (§11.3.3)"

-- | Source-unannotated lambda parameters are finalized as part of the named
-- declaration boundary, so they require the same rigid observation replay as
-- free-meta abstraction. Anonymous lambdas outside a declaration never call
-- this function and therefore remain ordinary inference sites rather than
-- accidental generalization boundaries.
validateInferredLambdaGeneralization
  :: Span
  -> [Text]
  -> Ctx
  -> [Binder]
  -> Term
  -> Term
  -> CheckM ()
validateInferredLambdaGeneralization diagnosticSpan declarations = go 0
  where
    go _ _ [] _ _ = pure ()
    go index ctx (sourceBinder : sourceBinders) (CLamM mode icit quantity name body) typeTerm = do
      typeValue <- evalIn ctx typeTerm >>= forceM
      case typeValue of
        VPiBoundM expectedMode expectedIcit expectedQuantity borrowed _ assumption domain closure
          | mode == expectedMode
          , icit == expectedIcit
          , quantity == expectedQuantity -> do
              withAssumption <- extendLevelAssumption diagnosticSpan ctx assumption
              let rigid = VRigid (ctxLen withAssumption) []
                  nextCtx =
                    bindCtxMQB mode quantity name (icit == Impl) borrowed domain withAssumption
                  candidate =
                    isNothing (binderTypeExpr sourceBinder)
                      && not (bUnitBinder sourceBinder)
                      && mode == Parametric
              codomain <- clApp closure rigid
              dependencies <- observationDependenciesForTerm nextCtx body codomain
              let escaped =
                    find
                      ( \case
                          ParametricExternal 0 _ -> candidate
                          dependency -> candidate && dependencyIsAnalysisFailure dependency
                      )
                      (Set.toAscList dependencies)
              case escaped of
                Just dependency -> reportEscape ctx index name domain dependency
                Nothing -> do
                  codomainTerm <- quoteIn nextCtx codomain
                  go (index + 1) nextCtx sourceBinders body codomainTerm
        _ ->
          when (isNothing (binderTypeExpr sourceBinder) && not (bUnitBinder sourceBinder)) $
            reportEscape ctx index name (VSort LZero)
              (ParametricAnalysisFailure [] "finalized inferred binder telescope is malformed")
    go index ctx (sourceBinder : _) _ _ =
      when (isNothing (binderTypeExpr sourceBinder) && not (bUnitBinder sourceBinder)) $
        reportEscape ctx index "<missing>" (VSort LZero)
          (ParametricAnalysisFailure [] "finalized declaration is not a lambda telescope")

    reportEscape ctx index name domain dependency = do
      domainTerm <- quoteIn ctx domain
      owner <- gets csModule
      let qualifiedDeclarations = qualifyDeclarationIdentities owner declarations
          declarationIdentity = fromMaybe "<anonymous>" (listToMaybe qualifiedDeclarations)
          declarationSccIdentity = T.intercalate "," qualifiedDeclarations
      report $
        withPayload
          ( withPayloadField "declarationIdentity" declarationIdentity $
              withPayloadField "declarationSccIdentity" declarationSccIdentity $
                withPayloadField "failedCandidateKind" "type" $
                  withPayloadField "declarations" (T.intercalate "," qualifiedDeclarations) $
              withPayloadField "sccIdentities" (T.intercalate "," qualifiedDeclarations) $
                withPayloadField "candidateMetavariables" ("inferred-binder:" <> T.pack (show index)) $
                  withPayloadField "candidateClassifiers" (renderTerm domainTerm) $
                    withPayloadField "rigidParametricBinders" name $
                      withPayloadField "escapingDependency" (T.pack (show dependency)) $
                        withPayloadField "candidateKind" "type" $
                          withPayloadField "sourceOrigin" (T.pack (show diagnosticSpan)) $
                            withPayloadField "nearestMonomorphicAnnotation" "none" $
                              payloadKind "generalization-parametric-escape"
          ) $
          diag SevError StageElaborate "E_GENERALIZATION_PARAMETRIC_ESCAPE"
            (Just "kappa.generalization.parametric-escape") diagnosticSpan
            "candidate declaration generalization observes a rigid parametric binder in an ordinary position (§11.3.3)"

qualifyDeclarationIdentities :: ModuleName -> [Text] -> [Text]
qualifyDeclarationIdentities owner =
  map $ \declaration ->
    if declaration == "<anonymous>"
      || declaration == "<local-declaration>"
      || (moduleNameText owner <> ".") `T.isPrefixOf` declaration
      then declaration
      else moduleNameText owner <> "." <> declaration

generalizeLocalDeclarationUniverses
  :: Int
  -> Int
  -> Ctx
  -> Span
  -> [Text]
  -> Term
  -> Term
  -> CheckM (DeclarationUniverseTelescope, Term, Term)
generalizeLocalDeclarationUniverses firstMeta firstConstraint ctx diagnosticSpan declarations ty0 rhs0 =
  projectResult
    <$> generalizeLocalDeclarationUniversesWithRoles
      firstMeta firstConstraint ctx diagnosticSpan declarations [ty0] ty0 rhs0
  where
    projectResult (telescope, ty, rhs, _) = (telescope, ty, rhs)

-- | Collapse unconditional atomic equality cycles among inferred declaration
-- metas before choosing the hidden telescope. In the TypeLevel order,
-- @u <= v@ and @v <= u@ imply @u = v@ by antisymmetry, so retaining both as
-- independent schema parameters would be non-principal and would publish two
-- mutually interchangeable proof binders. Explicit schema parameters never
-- enter @candidates@ and therefore remain distinct source identities.
collapseInferredGeneralizableLevelEqualities
  :: Int
  -> Set LevelMeta
  -> CheckM ()
collapseInferredGeneralizableLevelEqualities firstConstraint candidates
  | Set.null candidates = pure ()
  | otherwise = do
      state <- get
      let assignments = csLevelAssignments state
          edges =
            [ (lower, upper)
            | constraint <- csLevelConstraints state
            , lcIdentity constraint >= firstConstraint
            , null (assumptionsList (lcAssumptions constraint))
            , LMeta lower <-
                [normalizeLevel (substituteLevelMetas assignments (lcLhs constraint))]
            , LMeta upper <-
                [normalizeLevel (substituteLevelMetas assignments (lcRhs constraint))]
            , lower `Set.member` candidates
            , upper `Set.member` candidates
            ]
          aliases =
            Map.fromList
              [ (meta, LMeta representative)
              | members <- DirectedGraph.stronglyConnectedComponents
                  (DirectedGraph.fromEdges edges)
              , representative <- take 1 members
              , meta <- drop 1 members
              ]
      unless (Map.null aliases) (installLevelAssignments aliases)

generalizeLocalDeclarationUniversesWithRoles
  :: Int
  -> Int
  -> Ctx
  -> Span
  -> [Text]
  -> [Term]
  -> Term
  -> Term
  -> CheckM (DeclarationUniverseTelescope, Term, Term, [LevelMeta])
generalizeLocalDeclarationUniversesWithRoles firstMeta firstConstraint ctx diagnosticSpan declarations roleTerms0 ty0 rhs0 = do
  (telescope, ty, rhs, retained, constraints) <-
    generalizeLocalDeclarationUniversesWithRolesRaw
      firstMeta firstConstraint ctx diagnosticSpan declarations roleTerms0 ty0 rhs0
  let (tyWithProofs, rhsWithProofs) =
        prependGeneratedConstraintBinders
          (dutParameterCount telescope)
          constraints
          ty
          rhs
  pure (telescope, tyWithProofs, rhsWithProofs, retained)

-- | Principalize a local declaration boundary without choosing where its
-- generated proof telescope is attached. Ordinary local declarations use the
-- wrapper above. A mutually recursive group attaches the same authenticated
-- constraints to each member and rechecks the SCC against those final member
-- contracts, rather than wrapping and then destructuring a record under a
-- proof lambda.
generalizeLocalDeclarationUniversesWithRolesRaw
  :: Int
  -> Int
  -> Ctx
  -> Span
  -> [Text]
  -> [Term]
  -> Term
  -> Term
  -> CheckM
       ( DeclarationUniverseTelescope
       , Term
       , Term
       , [LevelMeta]
       , [UniverseConstraint]
       )
generalizeLocalDeclarationUniversesWithRolesRaw firstMeta firstConstraint _ctx diagnosticSpan declarations roleTerms0 ty0 rhs0 = do
  st0 <- get
  let explicitCount = csActiveLocalUniverseSchemaCount st0
      assignments0 = csLevelAssignments st0
      roleTerms = map (zonkLevels assignments0) roleTerms0
      localMeta meta = meta >= firstMeta
      occurrenceMetas = csLevelInstantiationMetas st0
      roles = mconcat (map declarationUniverseRoles roleTerms)
      candidateGeneralizable =
        Set.filter
          (\meta -> localMeta meta && meta `Set.notMember` occurrenceMetas)
          (durGeneralizable roles)
      generalizable = maybe candidateGeneralizable (const Set.empty) explicitCount
      explicitMinimizable = maybe Set.empty (const candidateGeneralizable) explicitCount
      occurrenceMinimizable = Set.filter localMeta occurrenceMetas
      minimizable =
        Set.filter localMeta
          ( Set.difference
              (Set.unions [durMinimizable roles, explicitMinimizable, occurrenceMinimizable])
              generalizable
          )
      localConstraints0 =
        [ substituteLevelConstraintMetas assignments0 constraint
        | constraint <- csLevelConstraints st0
        , lcIdentity constraint >= firstConstraint
        ]
  unless (Set.null minimizable) $
    do
      let declarationIdentities =
            map (localDeclarationDiagnosticIdentity st0 diagnosticSpan) declarations
          -- Completeness of an explicit schema is a separate source contract
          -- from principal minimization. Preserve the old provenance check:
          -- a source-generalizable level that the detailed rules did not
          -- determine cannot be accepted merely because zero is the checked
          -- least value for an otherwise unconstrained selected meta.
          explicitUnresolved = case (explicitCount, solveLevelConstraintsFor minimizable localConstraints0) of
            (Just _, Right solution) ->
              let solved = lsAssignments solution
               in Set.intersection candidateGeneralizable
                    (Set.filter (`Map.notMember` solved) minimizable)
            _ -> Set.empty
      inferred <-
        inferPrincipalAtDeclarationBoundary
          diagnosticSpan declarationIdentities (isJust explicitCount) minimizable localConstraints0
      case inferred of
        PrincipalBoundarySolved candidate -> do
          unless (Set.null explicitUnresolved) $
            reportNoPrincipalUniverseDiagnostic
              diagnosticSpan declarationIdentities True explicitUnresolved localConstraints0
              Nothing
              "an explicit local declaration universe schema is incomplete (§11.1.2.3A.1)"
          -- Continue with the principal recovery assignment after an explicit
          -- schema diagnostic so later terms remain well scoped without making
          -- the invalid schema successful.
          installLevelAssignments candidate
        PrincipalBoundaryDeferred -> pure ()
        PrincipalBoundaryRejected failure ->
          reportPrincipalBoundaryFailure
            diagnosticSpan declarationIdentities (isJust explicitCount)
            minimizable localConstraints0 failure
  collapseInferredGeneralizableLevelEqualities firstConstraint generalizable
  st <- get
  let assignments = csLevelAssignments st
      finalizedRoleTerms = map (zonkLevels assignments) roleTerms0
      ty = zonkLevels assignments ty0
      rhs = zonkLevels assignments rhs0
      retained = case explicitCount of
        Just _ -> []
        Nothing ->
          nub
            [ meta
            | meta <- concatMap levelMetasOfTerm finalizedRoleTerms
            , meta `Set.member` generalizable
            ]
      parameterSubstitution =
        Map.fromList (zip retained (map LParam [0 ..]))
      localParameterCount = fromMaybe (length retained) explicitCount
      abstractLevel = case explicitCount of
        Just _ -> id
        Nothing ->
          substituteLevelMetas parameterSubstitution
            . abstractLocalLevelParams localParameterCount
      transform = case explicitCount of
        Just _ -> id
        Nothing -> zonkTermWith (\_ _ -> Nothing) abstractLevel 0
      constraints =
        [ substituteLevelConstraintMetas assignments constraint
        | constraint <- csLevelConstraints st
        , lcIdentity constraint >= firstConstraint
        ]
      constraintMetas constraint =
        nub (levelMetas (lcLhs constraint) ++ levelMetas (lcRhs constraint))
      generalizedConstraint constraint =
        let metas = constraintMetas constraint
         in not (null metas)
              && null (assumptionsList (lcAssumptions constraint))
              && all (`elem` retained) metas
      explicitConstraint constraint =
        let levels = [lcLhs constraint, lcRhs constraint]
            parameters = nub (concatMap levelParams levels)
         in null (assumptionsList (lcAssumptions constraint))
              && null (constraintMetas constraint)
              && any (< localParameterCount) parameters
      selected = case explicitCount of
        Just _ -> filter explicitConstraint constraints
        Nothing -> filter generalizedConstraint constraints
      selectedIds = Set.fromList (map lcIdentity selected)
      selectedConstraints =
        dedupeUniverseConstraints $
          [ candidate
          | constraint <- orderLevelConstraintsBySignatureOccurrence st selected
          , let candidate =
                  UniverseConstraint
                    (abstractLevel (lcLhs constraint))
                    (abstractLevel (lcRhs constraint))
          , proveLevelLeq
              emptyAssumptions
              (ucLower candidate)
              (ucUpper candidate)
              /= Proved
          ]
      telescope =
        DeclarationUniverseTelescope
          localParameterCount
          (isJust explicitCount)
  unless (Set.null selectedIds) $
    modify' $ \current ->
      reindexLevelConstraints $
        current
        { csLevelConstraints =
            filter ((`Set.notMember` selectedIds) . lcIdentity) (csLevelConstraints current)
        , csLevelConstraintOwners =
            Map.withoutKeys (csLevelConstraintOwners current) selectedIds
        , csLevelConstraintSpans =
            Map.withoutKeys (csLevelConstraintSpans current) selectedIds
        }
  pure
    ( telescope
    , transform ty
    , transform rhs
    , retained
    , selectedConstraints
    )
  where
    localDeclarationDiagnosticIdentity state span' declaration =
      moduleNameText (csModule state)
        <> "::local:"
        <> declaration
        <> "@"
        <> T.pack (spanFile span')
        <> ":"
        <> T.pack (show (posLine (spanStart span')))
        <> ":"
        <> T.pack (show (posCol (spanStart span')))

-- | Enforce §9.3.1.1/§30.1.1 at the common lexical boundary for both pure
-- blocks and do blocks. Scoped declarations remain in the semantic tables so
-- malformed downstream Core cannot forget their status, but a successful
-- result may not expose an identity introduced by this scope. Runtime values
-- whose interface omits the family remain admissible; compile-time values and
-- monadic compile-time payloads additionally inspect their result term.
withLocalNominalEscapeBoundary
  :: Ctx
  -> Span
  -> CheckM (Term, Value)
  -> CheckM (Term, Value)
withLocalNominalEscapeBoundary outerCtx site action = do
  before <- gets (Map.keysSet . csScopedLocalNominals)
  result@(term, resultType) <- action
  st <- get
  let introduced = Map.keysSet (csScopedLocalNominals st) `Set.difference` before
  unless (Set.null introduced) $ do
    resultTypeTerm <- quoteIn outerCtx resultType
    typeDependencies <- expandedGlobalsOfTermM resultTypeTerm
    inspectTerm <- resultMayCarryCompileTimeValue resultType
    termDependencies <-
      if inspectTerm then expandedGlobalsOfTermM term else pure Set.empty
    let escaped =
          Set.intersection introduced (Set.union typeDependencies termDependencies)
    unless (Set.null escaped) $ do
      let escapedNames = sort (map gnameText (Set.toList escaped))
          declarationSites =
            [ related RoleDeclarationSite declarationSite
                "scoped local nominal declared here"
            | identity <- Set.toList escaped
            , Just declarationSite <- [Map.lookup identity (csScopedLocalNominals st)]
            ]
          diagnostic =
            withPayload
              ( withPayloadField "phase" "local-nominal-escape-check" $
                  withPayloadField "escapedIdentities" (T.intercalate "," escapedNames) $
                    payloadKind "local-nominal-scope-escape"
              ) $
              diag SevError StageElaborate "E_LOCAL_NOMINAL_SCOPE_ESCAPE"
                (Just "kappa-hs.local-nominal.scope-escape") site
                ( "this block result transparently exposes scoped local nominal "
                    <> T.intercalate ", " escapedNames
                    <> "; scoped local families and their nominal-scope dependencies may not escape their lexical block (§9.3.1.1, §30.1.1)"
                )
      report (withRelateds declarationSites diagnostic)
  pure result
  where
    resultMayCarryCompileTimeValue value =
      forceM value >>= \case
        VSort {} -> pure True
        VGlobN global arguments
          | global `elem` [prelIO, prelEff, prelSTM, prelElab]
          , not (null arguments) ->
              resultMayCarryCompileTimeValue (snd (last arguments))
        _ -> pure False

-- | Declaration-site names are stable for one checker run and unspellable by
-- source lookup.  Preserve the written universe schema: it is part of the
-- declaration interface, not of textual symbol identity.
renameLocalDataDeclaration :: DataDecl -> Span -> CheckM DataDecl
renameLocalDataDeclaration declaration declarationSpan = do
  dataText <- stableGeneratedNameAt "local-data" (nameText (ddName declaration)) declarationSpan
  constructorTexts <-
    forM (ddCtors declaration) $ \constructor ->
      if nameText (cdName constructor) == nameText (ddName declaration)
        then pure dataText
        else stableGeneratedNameAt "local-constructor" (nameText (cdName constructor)) (nameSpan (cdName constructor))
  let renameName text source =
        case nameUniverseSchema source of
          Nothing -> Name text (nameSpan source)
          Just schema -> NameWithUniverseSchema text (nameSpan source) schema
      renamedConstructors =
        [ constructor {cdName = renameName text (cdName constructor)}
        | (constructor, text) <- zip (ddCtors declaration) constructorTexts
        ]
  pure
    declaration
      { ddName = renameName dataText (ddName declaration)
      , ddCtors = renamedConstructors
      }

-- | Conservative source-level capture set for local data interfaces. Names
-- bound by the data/constructor telescopes are removed before consulting the
-- semantic local context. False negatives would be unsound; false positives
-- only take the explicit fail-closed path above.
localDataCaptures :: Ctx -> DataDecl -> [Text]
localDataCaptures ctx declaration =
  sort . nub $
    [ occurrence
    | expression <- expressionsIn declaration
    , name <- freeVarOccurrences expression
    , let occurrence = nameText name
    , occurrence `Set.notMember` declarationBinders
    , isJust (lookupCtx occurrence ctx)
    ]
  where
    declarationBinders =
      Set.fromList $
        mapMaybe (fmap nameText . bName) (ddParams declaration)
          ++ concatMap
               (mapMaybe (fmap nameText . bName) . cdBinders)
               (ddCtors declaration)
    expressionsIn :: Data a => a -> [Expr]
    expressionsIn value =
      case cast value of
        Just expression -> [expression]
        Nothing -> concat (gmapQ expressionsIn value)

-- | Build the exact closure-converted capture telescope of a local data
-- family. Direct source references select semantic binder levels; types of
-- those binders add their transitive dependencies. References to an earlier
-- local nominal add that family's already-closed capture set rather than its
-- source spelling.
localDataCaptureTelescope
  :: Ctx
  -> DataDecl
  -> CheckM (Ctx, Telescope, [LocalNominalCapture])
localDataCaptureTelescope original declaration = do
  st <- get
  let directNames = localDataCaptures original declaration
      directLevels =
        [ ctxLen original - index - 1
        | name <- directNames
        , Just (index, _) <- [lookupCtx name original]
        ]
      nominalLevels =
        [ lncLevel capture
        | name <- freeDeclarationNames declaration
        , Just nominal <- [Map.lookup name (csLocalDeclScope st)]
        , capture <- Map.findWithDefault [] nominal (csLocalNominalCaptures st)
        ]
  levels <- closeCaptureLevels (Set.fromList (directLevels ++ nominalLevels))
  let ordered = sort (Set.toList levels)
      positions = Map.fromList (zip ordered [0 ..])
  (captureCtx, telescope) <- foldM (appendCapture positions) (emptyCtx, []) ordered
  let captures =
        [ LocalNominalCapture (ceName (entryAtLevel level)) level
        | level <- ordered
        ]
  pure (captureCtx, telescope, captures)
  where
    entryAtLevel level = ctxEntries original !! (ctxLen original - level - 1)

    freeDeclarationNames :: Data a => a -> [Text]
    freeDeclarationNames value =
      case cast value of
        Just expression -> map nameText (freeVarOccurrences expression)
        Nothing -> concat (gmapQ freeDeclarationNames value)

    closeCaptureLevels selected = do
      dependencies <- fmap Set.unions $
        forM (Set.toList selected) $ \level -> do
          typeTerm <- quoteIn original (ceType (entryAtLevel level))
          pure (ambientTermLevels (ctxLen original) typeTerm)
      let next = Set.union selected dependencies
      if next == selected then pure selected else closeCaptureLevels next

    appendCapture positions (captureCtx, telescope) oldLevel = do
      rawType <- quoteIn original (ceType (entryAtLevel oldLevel))
      let newDepth = length telescope
          closedType = reindexAmbientTerm (ctxLen original) positions newDepth rawType
          sourceEntry = entryAtLevel oldLevel
      unless (termScopedAt newDepth closedType) $
        report $
          withPayload
            ( withPayloadField "capture" (ceName sourceEntry) $
                payloadKind "local-declaration-capture-interface"
            ) $
            diag SevError StageElaborate "E_LOCAL_DECLARATION_CAPTURE_INTERFACE"
              (Just "kappa.internal.compiler") (ceOrigin sourceEntry)
              ( "the capture type of '" <> ceName sourceEntry
                  <> "' could not be closed over the local declaration's semantic capture telescope"
              )
      typeValue <- evalIn captureCtx closedType
      let mode = ceMode sourceEntry
          quantity = ceCoreQ sourceEntry
          borrowed = ceBorrow sourceEntry
      formation <- selectFormationMode captureCtx mode typeValue
      let
          telescopeEntry =
            TelescopeEntry Impl mode formation quantity borrowed (ceName sourceEntry) closedType Nothing
          nextCtx = bindCtxMQB mode quantity (ceName sourceEntry) True borrowed typeValue captureCtx
      pure (nextCtx, telescope ++ [telescopeEntry])

-- | Free declaration-site binder levels mentioned by a typed term, including
-- levels embedded in universe indices and replayable lift evidence.
ambientTermLevels :: Int -> Term -> Set Int
ambientTermLevels ambient term =
  Set.fromList (termLevels ++ solverLevels)
  where
    termLevels = foldTermWithDepth termVariable 0 term
    termVariable depth = \case
      CVar index | index >= depth -> [ambient - (index - depth) - 1]
      CLocal index _ | index >= depth -> [ambient - (index - depth) - 1]
      _ -> []
    solverLevels =
      [ level
      | level <- foldTerm levelVariables (const []) term
      , level >= 0
      , level < ambient
      ]
    levelVariables = \case
      CGlobal _ universes -> concatMap levelVars universes
      CLocal _ universes -> concatMap levelVars universes
      CSort level -> levelVars level
      CLevel level -> levelVars level
      CUniverseLift from to evidence _ ->
        concatMap levelVars
          ( from : to
              : concatMap
                  (\step -> uesLower step : uesUpper step
                    : concatMap (\(lower, upper) -> [lower, upper]) (uesAssumptions step))
                  (ueSteps evidence)
          )
      _ -> []

-- | Rebase a term from an arbitrary declaration-site context to the ordered
-- capture telescope. Bound variables introduced inside the term remain bound;
-- ambient term indices and absolute level variables are transported together.
reindexAmbientTerm :: Int -> Map Int Int -> Int -> Term -> Term
reindexAmbientTerm oldAmbient positions newAmbient =
  zonkTermWith (\_ _ -> Nothing) reindexLevel 0
    . mapTermWithDepth reindexVariable 0
  where
    reindexVariable depth = \case
      CVar index | index >= depth ->
        let oldLevel = oldAmbient - (index - depth) - 1
         in CVar . (depth +) . (newAmbient - 1 -) <$> Map.lookup oldLevel positions
      CLocal index universes | index >= depth ->
        let oldLevel = oldAmbient - (index - depth) - 1
         in (\newLevel -> CLocal (depth + newAmbient - newLevel - 1) universes)
              <$> Map.lookup oldLevel positions
      _ -> Nothing

    reindexLevel = normalizeLevel . go
    go = \case
      LZero -> LZero
      LFinite value -> LFinite value
      LOmega -> LOmega
      LSucc level -> LSucc (go level)
      LAdd left right -> LAdd (go left) (go right)
      LMax left right -> LMax (go left) (go right)
      LNeutral atom -> LNeutral (mapNeutralLevelAtomLevels go atom)
      LVar level -> LVar (reindexAbsolute level)
      LProjection level fields -> LProjection (reindexAbsolute level) fields
      LParam parameter -> LParam parameter
      LField identity field -> LField identity field
      LMeta meta -> LMeta meta

    reindexAbsolute level
      | level < oldAmbient = Map.findWithDefault level level positions
      | otherwise = newAmbient + level - oldAmbient

-- ── Algebraic effects (§9.3.1.1, §18.1.14–§18.1.22) ──────────────────
--
-- Runtime model (realized by 'Kappa.Eval.evalEffPrim'): an @Eff r a@
-- value is a tree — @__EffPure v@, or @__EffOp label op payload cont@
-- with @cont@ the captured continuation from the operation site
-- (§30.2.2.7 OpCall). Handlers elaborate to @__handleEff@ applications;
-- the continuation is an ordinary closure, so resumption is naturally
-- re-entrant (one-shot/multi-shot discipline is enforced statically by
-- 'Kappa.Usage').
