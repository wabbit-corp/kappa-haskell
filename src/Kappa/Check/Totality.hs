-- | Totality: proving that recursive definitions actually terminate
-- (Spec §10.4, §19).
--
-- Kappa wants functions to be total, because types-as-propositions is only
-- sound if a proof cannot loop forever. This module runs the check in three
-- stages, each with its own section below:
--
--   * __call-edge collection__ — walk each definition in a recursive group
--     and record every call it makes back into the group, together with how
--     each argument changed across that call ('CallEdge');
--   * __structural size-change__ — the default criterion: some argument must
--     get strictly smaller on a well-founded ordering along every cycle in
--     the call graph, tracked through constructor patterns;
--   * __explicit measures__ — when a definition declares @decreases@, check
--     that user-supplied measure instead, discharging the arithmetic side
--     conditions through "Kappa.Check.Arith".
--
-- Background on why totality matters and what size-change analysis is:
-- docs\/CONCEPTS.md.
module Kappa.Check.Totality
  ( collectSccEdges
  , measureSccOKWithEdges
  , structuralSccOKWithEdges
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

collectSccEdges :: Map GName TermFun -> CheckM (Maybe [CallEdge])
collectSccEdges funMap = do
  edges <- mapM (collectFunEdges funMap) (Map.elems funMap)
  pure (concat <$> sequence edges)

collectFunEdges :: Map GName TermFun -> TermFun -> CheckM (Maybe [CallEdge])
collectFunEdges funMap src =
  go (tfDepth src) parameterOrigins Map.empty Set.empty [] [] (tfBody src)
  where
    sccNames = Map.keysSet funMap
    parameterOrigins =
      StructuralOrigins
        { structuralLocals =
            Map.fromList
              [ (level, Set.singleton (StructuralOrigin level []))
              | level <- tfExplParams src
              ]
        , structuralShapes = Map.empty
        }

    go :: Int -> StructuralOrigins -> Map Int PartialCall -> Set Int -> [AFact] -> [(Term, Bool)] -> Term -> CheckM (Maybe [CallEdge])
    go d sub ho esc facts boolFacts t = case t of
      CApp {} -> do
        case partialCallOf d ho t of
          Just pc | Set.member (pcTarget pc) sccNames, partialCallComplete pc ->
            collectApplication d sub ho esc facts boolFacts t
          _ -> do
            exposesRecursiveCall <- reducibleApplicationContainsSccReference d ho esc t
            if exposesRecursiveCall
              then do
                tNorm <- normalizeTermAt d t
                if tNorm /= t
                  -- §15.11: transparent higher-order helpers are part of the
                  -- semantic call shape.  Do not reject the pre-normalized term
                  -- just because it appears to pass a partial recursive closure
                  -- through a helper; unfold the helper first, then classify the
                  -- actual application that remains.  However, transparent
                  -- normalization must not erase recursive calls that occur while
                  -- evaluating strict helper arguments, such as `ignore (f n)`.
                  -- Collect complete recursive calls from the original strict
                  -- subterms and combine them with the normalized semantic edge.
                  -- Incomplete partial calls are not charged here; they are either
                  -- exposed by transparent normalization or rejected as opaque
                  -- higher-order escape by 'goArg'.
                  then joinEdges <$> collectStrictSubtermEdges d sub ho facts boolFacts t <*> go d sub ho esc facts boolFacts tNorm
                  else collectApplication d sub ho esc facts boolFacts t
              else collectApplication d sub ho esc facts boolFacts t
      CGlob callee | Set.member callee sccNames -> pure Nothing
      CVar i
        | Set.member (d - 1 - i) esc -> pure Nothing
      CVar i
        | Just pc0 <- Map.lookup (d - 1 - i) ho -> do
            let pc = instantiatePartialCall d pc0
                edge = CallEdge (tfName src) (pcTarget pc) (pcUniverses pc) d facts boolFacts (pcArgs pc) sub
            pure (Just [edge])
      CLam _ _ _ b -> go (d + 1) sub ho esc facts boolFacts b
      CPi _ _ _ _ a b -> joinEdges <$> go d sub ho esc facts boolFacts a <*> go (d + 1) sub ho esc facts boolFacts b
      CLet _ _ a b c -> do
        ra <- go d sub ho esc facts boolFacts a
        exposesRecursiveCall <- reducibleApplicationContainsSccReference d ho esc b
        bNorm <-
          if exposesRecursiveCall
            then normalizeTermAt d b
            else pure b
        let normalizedPartial =
              if bNorm /= b
                then partialCallOf d ho bNorm
                else Nothing
        case partialCallOf d ho b <|> normalizedPartial of
          Just pc | not (partialCallComplete pc) -> do
            -- A let-bound partial SCC application is a first-class closure;
            -- track the closure and charge the recursive edge at each use.
            -- Its captured arguments are still checked for nested recursive
            -- calls, and any later escape as an opaque higher-order argument is
            -- rejected by 'goArg'.
            rbArgs <- joinManyEdges <$> mapM (goArg d sub ho esc facts boolFacts . snd) (pcArgs pc)
            let sub' = insertStructuralAlias d sub b
            rc <- go (d + 1) sub' (Map.insert d pc ho) esc facts boolFacts c
            pure (joinManyEdges [ra, rbArgs, rc])
          _ -> do
            let closureAlias =
                  recursiveClosureEscapes d ho esc b
                    || (bNorm /= b && recursiveClosureEscapes d ho esc bNorm)
                esc' = if closureAlias then Set.insert d esc else esc
                sub' = insertStructuralAlias d sub b
            join3Edges
              <$> pure ra
              <*> go d sub ho esc facts boolFacts b
              <*> go (d + 1) sub' ho esc' facts boolFacts c
      CLetRec _ _ a b c ->
        join3Edges
          <$> go d sub ho esc facts boolFacts a
          <*> go (d + 1) sub ho esc facts boolFacts b
          <*> go (d + 1) sub ho esc facts boolFacts c
      CIf c th el -> do
        rc <- go d sub ho esc facts boolFacts c
        c' <- normalizeTermAt d c
        trueFacts <- assumeBoolM d True c'
        falseFacts <- assumeBoolM d False c'
        rt <- go d sub ho esc (trueFacts ++ facts) ((c', True) : boolFacts) th
        re <- go d sub ho esc (falseFacts ++ facts) ((c', False) : boolFacts) el
        pure (joinManyEdges [rc, rt, re])
      CMatch scrut _ _ alts -> do
        rs <- go d sub ho esc facts boolFacts scrut
        let scrutOrigins = termStructuralOrigins d sub scrut
        ralts <- forM alts $ \(CaseAlt pat gd b) -> do
          let nb = patBindersC pat
              d' = d + nb
              sub' =
                recordMatchedStructuralShape scrutOrigins pat
                  (bindPatternStructuralOrigins d sub scrut pat)
              ho' = ho
          rg <- maybe (pure (Just [])) (go d' sub' ho' esc facts boolFacts) gd
          gd' <- traverse (normalizeTermAt d') gd
          patFacts <- comparePatternFactsM d scrut pat
          guardFacts <- maybe (pure []) (assumeBoolM d' True) gd'
          let facts' = guardFacts ++ patFacts ++ facts
              boolFacts' = maybe boolFacts (\guardTm -> (guardTm, True) : boolFacts) gd'
          rb <- go d' sub' ho' esc facts' boolFacts' b
          pure (joinEdges rg rb)
        pure (joinManyEdges (rs : ralts))
      CCtor _ _ as -> joinManyEdges <$> mapM (goArg d sub ho esc facts boolFacts) as
      CRecordT fs -> joinManyEdges <$> mapM (goArg d sub ho esc facts boolFacts . snd) fs
      CRecordV fs -> joinManyEdges <$> mapM (goArg d sub ho esc facts boolFacts . snd) fs
      CProj e _ -> go d sub ho esc facts boolFacts e
      CProjAt e _ _ -> go d sub ho esc facts boolFacts e
      CVariantT ms -> joinManyEdges <$> mapM (goArg d sub ho esc facts boolFacts) ms
      CInject _ e -> goArg d sub ho esc facts boolFacts e
      CThunkE e _ -> goArg d sub ho esc facts boolFacts e
      CLazyE e _ -> goArg d sub ho esc facts boolFacts e
      CForceE e _ -> go d sub ho esc facts boolFacts e
      CSealE _ e -> goArg d sub ho esc facts boolFacts e
      CSigT _ e -> goArg d sub ho esc facts boolFacts e
      CUniverseLift _ _ _ e -> go d sub ho esc facts boolFacts e
      CSchemaLift _ _ _ _ _ _ _ _ e -> go d sub ho esc facts boolFacts e
      CLetPolyM _ _ _ _ a b c ->
        join3Edges
          <$> go d sub ho esc facts boolFacts a
          <*> go d sub ho esc facts boolFacts b
          <*> go (d + 1) (insertStructuralAlias d sub b) ho esc facts boolFacts c
      CLetRecPolyM _ _ _ _ a b c ->
        join3Edges
          <$> go d sub ho esc facts boolFacts a
          <*> go (d + 1) sub ho esc facts boolFacts b
          <*> go (d + 1) sub ho esc facts boolFacts c
      CLetRecGroupM _ definitions body -> do
        let count = length definitions
            depth' = d + count
        types <- joinManyEdges <$> mapM (go d sub ho esc facts boolFacts . clrdType) definitions
        rhss <- joinManyEdges <$> mapM (go depth' sub ho esc facts boolFacts . clrdRhs) definitions
        bodyEdges <- go depth' sub ho esc facts boolFacts body
        pure (joinManyEdges [types, rhss, bodyEdges])
      CQuote _ slots -> joinManyEdges <$> mapM (goArg d sub ho esc facts boolFacts) slots
      CDo _ items -> goKItems d sub ho esc facts boolFacts items
      _ -> pure (Just [])

    collectApplication d sub ho esc facts boolFacts t =
      case partialCallOf d ho t of
        Just pc | Set.member (pcTarget pc) sccNames -> do
          argEdges <- joinManyEdges <$> mapM (goArg d sub ho esc facts boolFacts . snd) (pcArgs pc)
          let edge = CallEdge (tfName src) (pcTarget pc) (pcUniverses pc) d facts boolFacts (pcArgs pc) sub
          pure ((edge :) <$> argEdges)
        _ -> case spineOfTerm t of
          (f, args) -> do
            rf <- go d sub ho esc facts boolFacts f
            rs <- joinManyEdges <$> mapM (goArg d sub ho esc facts boolFacts . snd) args
            pure (joinEdges rf rs)

    -- Strict source subterms are still evaluated even when a transparent helper
    -- later normalizes away their value.  This traversal records only complete
    -- recursive calls.  It deliberately ignores incomplete partial recursive
    -- closures: a partial closure is not a call edge until transparent code
    -- applies it, and if opaque code receives it 'goArg' rejects the escape.
    collectStrictSubtermEdges :: Int -> StructuralOrigins -> Map Int PartialCall -> [AFact] -> [(Term, Bool)] -> Term -> CheckM (Maybe [CallEdge])
    collectStrictSubtermEdges d sub ho facts boolFacts t = case t of
      CApp {} -> do
        let here = case partialCallOf d ho t of
              Just pc | Set.member (pcTarget pc) sccNames, partialCallComplete pc ->
                Just [CallEdge (tfName src) (pcTarget pc) (pcUniverses pc) d facts boolFacts (pcArgs pc) sub]
              _ -> Just []
            (f, args) = spineOfTerm t
        children <- joinManyEdges <$> mapM (collectStrictSubtermEdges d sub ho facts boolFacts) (f : [a | (_, a) <- args])
        pure (joinEdges here children)
      CVar i
        | Just pc0 <- Map.lookup (d - 1 - i) ho -> do
            let pc = instantiatePartialCall d pc0
            pure $ case () of
              _ | Set.member (pcTarget pc) sccNames, partialCallComplete pc ->
                    Just [CallEdge (tfName src) (pcTarget pc) (pcUniverses pc) d facts boolFacts (pcArgs pc) sub]
                | otherwise -> Just []
      CLam {} -> pure (Just [])
      CThunkE {} -> pure (Just [])
      CLazyE {} -> pure (Just [])
      CQuote {} -> pure (Just [])
      CPi _ _ _ _ a b -> joinEdges <$> collectStrictSubtermEdges d sub ho facts boolFacts a <*> collectStrictSubtermEdges (d + 1) sub ho facts boolFacts b
      CLet _ _ a b c ->
        join3Edges
          <$> collectStrictSubtermEdges d sub ho facts boolFacts a
          <*> collectStrictSubtermEdges d sub ho facts boolFacts b
          <*> collectStrictSubtermEdges (d + 1) (insertStructuralAlias d sub b) ho facts boolFacts c
      CLetRec _ _ a b c ->
        join3Edges
          <$> collectStrictSubtermEdges d sub ho facts boolFacts a
          <*> collectStrictSubtermEdges (d + 1) sub ho facts boolFacts b
          <*> collectStrictSubtermEdges (d + 1) sub ho facts boolFacts c
      CIf c th el -> do
        rc <- collectStrictSubtermEdges d sub ho facts boolFacts c
        c' <- normalizeTermAt d c
        trueFacts <- assumeBoolM d True c'
        falseFacts <- assumeBoolM d False c'
        rt <- collectStrictSubtermEdges d sub ho (trueFacts ++ facts) ((c', True) : boolFacts) th
        re <- collectStrictSubtermEdges d sub ho (falseFacts ++ facts) ((c', False) : boolFacts) el
        pure (joinManyEdges [rc, rt, re])
      CMatch scrut _ _ alts -> do
        rs <- collectStrictSubtermEdges d sub ho facts boolFacts scrut
        let scrutOrigins = termStructuralOrigins d sub scrut
        ralts <- forM alts $ \(CaseAlt pat gd b) -> do
          let nb = patBindersC pat
              d' = d + nb
              sub' =
                recordMatchedStructuralShape scrutOrigins pat
                  (bindPatternStructuralOrigins d sub scrut pat)
          rg <- maybe (pure (Just [])) (collectStrictSubtermEdges d' sub' ho facts boolFacts) gd
          gd' <- traverse (normalizeTermAt d') gd
          patFacts <- comparePatternFactsM d scrut pat
          guardFacts <- maybe (pure []) (assumeBoolM d' True) gd'
          let facts' = guardFacts ++ patFacts ++ facts
              boolFacts' = maybe boolFacts (\guardTm -> (guardTm, True) : boolFacts) gd'
          rb <- collectStrictSubtermEdges d' sub' ho facts' boolFacts' b
          pure (joinEdges rg rb)
        pure (joinManyEdges (rs : ralts))
      CCtor _ _ as -> joinManyEdges <$> mapM (collectStrictSubtermEdges d sub ho facts boolFacts) as
      CRecordT fs -> joinManyEdges <$> mapM (collectStrictSubtermEdges d sub ho facts boolFacts . snd) fs
      CRecordV fs -> joinManyEdges <$> mapM (collectStrictSubtermEdges d sub ho facts boolFacts . snd) fs
      CProj e _ -> collectStrictSubtermEdges d sub ho facts boolFacts e
      CProjAt e _ _ -> collectStrictSubtermEdges d sub ho facts boolFacts e
      CVariantT ms -> joinManyEdges <$> mapM (collectStrictSubtermEdges d sub ho facts boolFacts) ms
      CInject _ e -> collectStrictSubtermEdges d sub ho facts boolFacts e
      CForceE e _ -> collectStrictSubtermEdges d sub ho facts boolFacts e
      CSealE _ e -> collectStrictSubtermEdges d sub ho facts boolFacts e
      CSigT _ e -> collectStrictSubtermEdges d sub ho facts boolFacts e
      CUniverseLift _ _ _ e -> collectStrictSubtermEdges d sub ho facts boolFacts e
      CSchemaLift _ _ _ _ _ _ _ _ e -> collectStrictSubtermEdges d sub ho facts boolFacts e
      CLetPolyM _ _ _ _ a b c ->
        join3Edges
          <$> collectStrictSubtermEdges d sub ho facts boolFacts a
          <*> collectStrictSubtermEdges d sub ho facts boolFacts b
          <*> collectStrictSubtermEdges (d + 1) (insertStructuralAlias d sub b) ho facts boolFacts c
      CLetRecPolyM _ _ _ _ a b c ->
        join3Edges
          <$> collectStrictSubtermEdges d sub ho facts boolFacts a
          <*> collectStrictSubtermEdges (d + 1) sub ho facts boolFacts b
          <*> collectStrictSubtermEdges (d + 1) sub ho facts boolFacts c
      CLetRecGroupM _ definitions body -> do
        let count = length definitions
            depth' = d + count
        types <- joinManyEdges <$> mapM (collectStrictSubtermEdges d sub ho facts boolFacts . clrdType) definitions
        rhss <- joinManyEdges <$> mapM (collectStrictSubtermEdges depth' sub ho facts boolFacts . clrdRhs) definitions
        bodyEdges <- collectStrictSubtermEdges depth' sub ho facts boolFacts body
        pure (joinManyEdges [types, rhss, bodyEdges])
      CDo _ items -> collectStrictSubtermEdgesItems d sub ho facts boolFacts items
      _ -> pure (Just [])

    collectStrictSubtermEdgesItems
      :: Int
      -> StructuralOrigins
      -> Map Int PartialCall
      -> [AFact]
      -> [(Term, Bool)]
      -> [KItem]
      -> CheckM (Maybe [CallEdge])
    collectStrictSubtermEdgesItems _ _ _ _ _ [] = pure (Just [])
    collectStrictSubtermEdgesItems d sub ho facts boolFacts (item : rest) = do
      current <- collectStrictSubtermEdgesK d sub ho facts boolFacts item
      let (d', sub') = advanceKItemStructuralContext d sub item
      following <- collectStrictSubtermEdgesItems d' sub' ho facts boolFacts rest
      pure (joinEdges current following)

    collectStrictSubtermEdgesK :: Int -> StructuralOrigins -> Map Int PartialCall -> [AFact] -> [(Term, Bool)] -> KItem -> CheckM (Maybe [CallEdge])
    collectStrictSubtermEdgesK d sub ho facts boolFacts = \case
      KBind _ _ t _ -> collectStrictSubtermEdges d sub ho facts boolFacts t
      KLet _ _ t -> collectStrictSubtermEdges d sub ho facts boolFacts t
      KLetQ _ t m -> do
        rt <- collectStrictSubtermEdges d sub ho facts boolFacts t
        rm <-
          maybe
            (pure (Just []))
            (\(rejectionPattern, rejection) ->
               collectStrictSubtermEdges
                 (d + patBindersC rejectionPattern)
                 sub
                 ho
                 facts
                 boolFacts
                 rejection)
            m
        pure (joinEdges rt rm)
      KExpr t -> collectStrictSubtermEdges d sub ho facts boolFacts t
      KVarItem _ initT actT _ ->
        joinEdges <$> collectStrictSubtermEdges d sub ho facts boolFacts initT <*> collectStrictSubtermEdges d sub ho facts boolFacts actT
      KAssign lhs _ rhs actT _ ->
        joinManyEdges
          <$> sequence
            [ collectStrictSubtermEdges d sub ho facts boolFacts lhs
            , collectStrictSubtermEdges d sub ho facts boolFacts rhs
            , collectStrictSubtermEdges d sub ho facts boolFacts actT
            ]
      KReturn t -> collectStrictSubtermEdges d sub ho facts boolFacts t
      KWhile _ c b e ->
        join3Edges
          <$> collectStrictSubtermEdges d sub ho facts boolFacts (kCondTerm c)
          <*> collectStrictSubtermEdgesItems d sub ho facts boolFacts b
          <*> maybe
            (pure (Just []))
            (collectStrictSubtermEdgesItems d sub ho facts boolFacts)
            e
      KFor _ pattern' s b e ->
        join3Edges
          <$> collectStrictSubtermEdges d sub ho facts boolFacts s
          <*> collectStrictSubtermEdgesItems
            (d + patBindersC pattern')
            sub
            ho
            facts
            boolFacts
            b
          <*> maybe
            (pure (Just []))
            (collectStrictSubtermEdgesItems d sub ho facts boolFacts)
            e
      KIf alts e -> do
        ralts <- forM alts $ \(c, b) -> do
          rc <- collectStrictSubtermEdges d sub ho facts boolFacts c
          c' <- normalizeTermAt d c
          trueFacts <- assumeBoolM d True c'
          rb <-
            collectStrictSubtermEdgesItems
              d
              sub
              ho
              (trueFacts ++ facts)
              ((c', True) : boolFacts)
              b
          pure (joinEdges rc rb)
        relse <-
          maybe
            (pure (Just []))
            (collectStrictSubtermEdgesItems d sub ho facts boolFacts)
            e
        pure (joinManyEdges (ralts ++ [relse]))
      KDefer _ t -> collectStrictSubtermEdges d sub ho facts boolFacts t
      KUsing _ a r -> joinEdges <$> collectStrictSubtermEdges d sub ho facts boolFacts a <*> collectStrictSubtermEdges d sub ho facts boolFacts r
      KSubDo _ b -> collectStrictSubtermEdgesItems d sub ho facts boolFacts b
      _ -> pure (Just [])

    -- Traversal for syntactic positions that pass a value to an unknown
    -- consumer.  A partial recursive function may be returned directly or
    -- applied through a transparent helper, but it may not be hidden inside an
    -- opaque higher-order argument, record, constructor, thunk, or quote slot:
    -- that would let unknown code call it at arbitrary measures.
    goArg :: Int -> StructuralOrigins -> Map Int PartialCall -> Set Int -> [AFact] -> [(Term, Bool)] -> Term -> CheckM (Maybe [CallEdge])
    goArg d sub ho esc facts boolFacts t = do
      if opaqueRecursiveEscape t
        then pure Nothing
        else do
          exposesRecursiveCall <- reducibleApplicationContainsSccReference d ho esc t
          if exposesRecursiveCall
            then do
              tNorm <- normalizeTermAt d t
              if tNorm /= t && opaqueRecursiveEscape tNorm
                then pure Nothing
                else joinEdges <$> go d sub ho esc facts boolFacts t <*> go d sub ho esc facts boolFacts tNorm
            else go d sub ho esc facts boolFacts t
      where
        opaqueRecursiveEscape x =
          case partialCallOf d ho x of
            Just pc | Set.member (pcTarget pc) sccNames, not (partialCallComplete pc) -> True
            _ -> case x of
              CVar i -> Set.member (d - 1 - i) esc
              _ -> recursiveClosureEscapes d ho esc x

    recursiveClosureEscapes :: Int -> Map Int PartialCall -> Set Int -> Term -> Bool
    recursiveClosureEscapes d ho esc = \case
      CLam _ _ _ b -> containsSccReference (d + 1) ho esc b
      CThunkE t _ -> containsSccReference d ho esc t
      CLazyE t _ -> containsSccReference d ho esc t
      _ -> False

    -- Normalizing an application can reveal a recursive call only when its
    -- head is definitionally reducible. Testing every application subtree
    -- with 'containsSccReference' before descending makes a left-associated
    -- Core spine quadratic. Opaque heads cannot expose a hidden call; their
    -- function and arguments are visited exactly once by 'collectApplication',
    -- where a partial recursive closure remains a fail-closed escape.
    reducibleApplicationContainsSccReference
      :: Int -> Map Int PartialCall -> Set Int -> Term -> CheckM Bool
    reducibleApplicationContainsSccReference d ho esc term =
      case spineOfTerm term of
        (headTerm, arguments) -> do
          reducible <- reducibleApplicationHead headTerm
          pure
            ( reducible
                && ( containsSccReference d ho esc headTerm
                       || any (containsSccReference d ho esc . snd) arguments
                   )
            )

    reducibleApplicationHead :: Term -> CheckM Bool
    reducibleApplicationHead = \case
      CGlobI global _ ->
        gets (maybe False gdReducible . Map.lookup global . csGlobals)
      CLamM {} -> pure True
      CLetM {} -> pure True
      CLetPolyM {} -> pure True
      CProj (CRecordV {}) _ -> pure True
      CProjAt (CRecordV {}) _ _ -> pure True
      CUniverseLift _ _ _ term -> reducibleApplicationHead term
      CSchemaLift _ _ _ _ _ _ _ _ term -> reducibleApplicationHead term
      CSealE _ term -> reducibleApplicationHead term
      _ -> pure False

    containsSccReference
      :: Int -> Map Int PartialCall -> Set Int -> Term -> Bool
    containsSccReference d ho esc term =
      case term of
        CGlobI g _ -> Set.member g sccNames
        CVar i -> Map.member (d - 1 - i) ho || Set.member (d - 1 - i) esc
        CLam _ _ _ b -> at (d + 1) b
        CPi _ _ _ _ a b -> here a || at (d + 1) b
        CApp _ f a -> here f || here a
        CCtor _ _ as -> any here as
        CMatch s _ _ alts ->
          here s
            || any
              ( \(CaseAlt pat gd b) ->
                  let d' = d + patBindersC pat
                   in maybe False (at d') gd || at d' b
              )
              alts
        CRecordT fs -> any (here . snd) fs
        CRecordV fs -> any (here . snd) fs
        CProj e _ -> here e
        CProjAt e _ _ -> here e
        CVariantT ms -> any here ms
        CInject _ e -> here e
        CLet _ _ a b c -> here a || here b || at (d + 1) c
        CLetRec _ _ a b c -> here a || at (d + 1) b || at (d + 1) c
        CLetPolyM _ _ _ _ a b c -> here a || here b || at (d + 1) c
        CLetRecPolyM _ _ _ _ a b c -> here a || at (d + 1) b || at (d + 1) c
        CLetRecGroupM _ definitions body ->
          let depth' = d + length definitions
           in any (here . clrdType) definitions
                || any (at depth' . clrdRhs) definitions
                || at depth' body
        CDo _ items -> containsSccReferenceItems d ho esc items
        CSealE _ e -> here e
        CSigT _ e -> here e
        CUniverseLift _ _ _ e -> here e
        CSchemaLift _ _ _ _ _ _ _ _ e -> here e
        CThunkE e _ -> here e
        CLazyE e _ -> here e
        CForceE e _ -> here e
        CIf a b c -> any here [a, b, c]
        CQuote _ slots -> any here slots
        _ -> False
      where
        here = containsSccReference d ho esc
        at depth = containsSccReference depth ho esc

    containsSccReferenceItems
      :: Int -> Map Int PartialCall -> Set Int -> [KItem] -> Bool
    containsSccReferenceItems _ _ _ [] = False
    containsSccReferenceItems d ho esc (item : rest) =
      containsSccReferenceK d ho esc item
        || containsSccReferenceItems (advanceKItemDepth d item) ho esc rest

    containsSccReferenceK
      :: Int -> Map Int PartialCall -> Set Int -> KItem -> Bool
    containsSccReferenceK d ho esc = \case
      KBind _ _ t _ -> here t
      KLet _ _ t -> here t
      KLetQ _ t m ->
        here t
          || maybe
            False
            (\(rejectionPattern, rejection) ->
               containsSccReference
                 (d + patBindersC rejectionPattern)
                 ho
                 esc
                 rejection)
            m
      KExpr t -> here t
      KVarItem _ initT actT _ -> here initT || here actT
      KAssign lhs _ rhs actT _ -> here lhs || here rhs || here actT
      KReturn t -> here t
      KWhile _ c b e ->
        here (kCondTerm c)
          || items d b
          || maybe False (items d) e
      KFor _ pattern' s b e ->
        here s
          || items (d + patBindersC pattern') b
          || maybe False (items d) e
      KIf alts e ->
        any (\(c, b) -> here c || items d b) alts
          || maybe False (items d) e
      KDefer _ t -> here t
      KUsing _ a r -> here a || here r
      KSubDo _ b -> items d b
      _ -> False
      where
        here = containsSccReference d ho esc
        items depth = containsSccReferenceItems depth ho esc

    partialCallOf :: Int -> Map Int PartialCall -> Term -> Maybe PartialCall
    partialCallOf d ho t = case spineOfTerm t of
      (CGlobI callee universes, args)
        | Set.member callee sccNames -> Just (PartialCall callee universes d args)
      (CVar i, args) -> do
        pc0 <- Map.lookup (d - 1 - i) ho
        let pc = instantiatePartialCall d pc0
        pure pc {pcArgs = pcArgs pc ++ args}
      _ -> Nothing

    instantiatePartialCall :: Int -> PartialCall -> PartialCall
    instantiatePartialCall d pc =
      pc
        { pcDepth = d
        , pcArgs = [(ic, shiftTerm (d - pcDepth pc) 0 a) | (ic, a) <- pcArgs pc]
        }

    partialCallComplete :: PartialCall -> Bool
    partialCallComplete pc =
      case Map.lookup (pcTarget pc) funMap of
        Nothing -> False
        Just target -> length (pcArgs pc) >= length (tfParams target)

    goKItems
      :: Int
      -> StructuralOrigins
      -> Map Int PartialCall
      -> Set Int
      -> [AFact]
      -> [(Term, Bool)]
      -> [KItem]
      -> CheckM (Maybe [CallEdge])
    goKItems _ _ _ _ _ _ [] = pure (Just [])
    goKItems d sub ho esc facts boolFacts (item : rest) = do
      current <- goK d sub ho esc facts boolFacts item
      let (d', sub') = advanceKItemStructuralContext d sub item
      following <- goKItems d' sub' ho esc facts boolFacts rest
      pure (joinEdges current following)

    goK :: Int -> StructuralOrigins -> Map Int PartialCall -> Set Int -> [AFact] -> [(Term, Bool)] -> KItem -> CheckM (Maybe [CallEdge])
    goK d sub ho esc facts boolFacts = \case
      KBind _ _ t _ -> goArg d sub ho esc facts boolFacts t
      KLet _ _ t -> goArg d sub ho esc facts boolFacts t
      KLetQ _ t m -> do
        rt <- goArg d sub ho esc facts boolFacts t
        rm <-
          maybe
            (pure (Just []))
            (\(rejectionPattern, rejection) ->
               goArg
                 (d + patBindersC rejectionPattern)
                 sub
                 ho
                 esc
                 facts
                 boolFacts
                 rejection)
            m
        pure (joinEdges rt rm)
      KExpr t -> goArg d sub ho esc facts boolFacts t
      KVarItem _ initT actT _ ->
        joinEdges <$> goArg d sub ho esc facts boolFacts initT <*> goArg d sub ho esc facts boolFacts actT
      KAssign lhs _ rhs actT _ ->
        joinManyEdges
          <$> sequence
            [ goArg d sub ho esc facts boolFacts lhs
            , goArg d sub ho esc facts boolFacts rhs
            , goArg d sub ho esc facts boolFacts actT
            ]
      KReturn t -> go d sub ho esc facts boolFacts t
      KWhile _ c b e ->
        join3Edges
          <$> go d sub ho esc facts boolFacts (kCondTerm c)
          <*> goKItems d sub ho esc facts boolFacts b
          <*> maybe
            (pure (Just []))
            (goKItems d sub ho esc facts boolFacts)
            e
      KFor _ pattern' s b e ->
        join3Edges
          <$> goArg d sub ho esc facts boolFacts s
          <*> goKItems
            (d + patBindersC pattern')
            sub
            ho
            esc
            facts
            boolFacts
            b
          <*> maybe
            (pure (Just []))
            (goKItems d sub ho esc facts boolFacts)
            e
      KIf alts e -> do
        ralts <- forM alts $ \(c, b) -> do
          rc <- go d sub ho esc facts boolFacts c
          c' <- normalizeTermAt d c
          trueFacts <- assumeBoolM d True c'
          rb <-
            goKItems
              d
              sub
              ho
              esc
              (trueFacts ++ facts)
              ((c', True) : boolFacts)
              b
          pure (joinEdges rc rb)
        relse <-
          maybe
            (pure (Just []))
            (goKItems d sub ho esc facts boolFacts)
            e
        pure (joinManyEdges (ralts ++ [relse]))
      KDefer _ t -> goArg d sub ho esc facts boolFacts t
      KUsing _ a r -> joinEdges <$> goArg d sub ho esc facts boolFacts a <*> goArg d sub ho esc facts boolFacts r
      KSubDo _ b -> goKItems d sub ho esc facts boolFacts b
      _ -> pure (Just [])

    advanceKItemDepth :: Int -> KItem -> Int
    advanceKItemDepth d = \case
      KBind _ pattern' _ _ -> d + patBindersC pattern'
      KLet _ pattern' _ -> d + patBindersC pattern'
      KLetQ pattern' _ _ -> d + patBindersC pattern'
      KVarItem {} -> d + 1
      KUsing pattern' _ _ -> d + patBindersC pattern'
      _ -> d

    advanceKItemStructuralContext
      :: Int -> StructuralOrigins -> KItem -> (Int, StructuralOrigins)
    advanceKItemStructuralContext d sub item =
      ( advanceKItemDepth d item
      , case item of
          KLet _ pattern' value ->
            bindPatternStructuralOrigins d sub value pattern'
          KLetQ pattern' value _ ->
            bindPatternStructuralOrigins d sub value pattern'
          _ -> sub
      )

    joinEdges :: Maybe [CallEdge] -> Maybe [CallEdge] -> Maybe [CallEdge]
    joinEdges (Just a) (Just b) = Just (a ++ b)
    joinEdges _ _ = Nothing

    join3Edges :: Maybe [CallEdge] -> Maybe [CallEdge] -> Maybe [CallEdge] -> Maybe [CallEdge]
    join3Edges a b c = joinManyEdges [a, b, c]

    joinManyEdges :: [Maybe [CallEdge]] -> Maybe [CallEdge]
    joinManyEdges xs = concat <$> sequence xs

-- | Bind structural provenance per pattern binder. A positional pattern over
-- an explicit tuple/record scrutinee must follow each source field separately:
-- collapsing @(xs, ys)@ to one reconstructed origin loses the fact that @xr@
-- descends from @xs@ and @yr@ from @ys@. Unknown scrutinee structure still
-- uses exact typed pattern paths, preserving the ordinary constructor case.
bindPatternStructuralOrigins
  :: Int -> StructuralOrigins -> Term -> CorePat -> StructuralOrigins
bindPatternStructuralOrigins depth context scrutinee pattern' =
  foldr insert context
    (zip [depth ..] (patternStructuralBinderOrigins depth context scrutinee pattern'))
  where
    insert (_, origins) current | Set.null origins = current
    insert (level, origins) current =
      current
        { structuralLocals =
            Map.insertWith Set.union level origins (structuralLocals current)
        }

patternStructuralBinderOrigins
  :: Int -> StructuralOrigins -> Term -> CorePat -> [Set StructuralOrigin]
patternStructuralBinderOrigins depth context scrutinee =
  go (Just scrutinee) (termStructuralOrigins depth context scrutinee)
  where
    go concrete origins = \case
      CPWild -> []
      CPVarM _ _ -> [origins]
      CPLit _ -> []
      CPCtorM existentialModes bridges hidden _ _ patterns ->
        replicate
          (length existentialModes + constructorBridgeBinderCount bridges)
          Set.empty
          ++ case
            interleaveConstructorSourceBinders
              hidden
              [ descendPosition concrete origins index pattern'
              | (index, pattern') <- zip [0 ..] patterns
              ]
          of
            Just source ->
              concatMap (either (const [Set.empty]) id) source
            Nothing ->
              -- Structural descent evidence is optional. On malformed layout
              -- preserve binder cardinality but refuse to attach any origin.
              replicate
                (length hidden + sum (map patBindersC patterns))
                Set.empty
      CPTuple patterns ->
        concat
          [ descendPosition concrete origins index pattern'
          | (index, pattern') <- zip [0 ..] patterns
          ]
      CPRecordM fields rest ->
        concat
          [ descendField concrete origins field pattern'
          | (field, pattern') <- fields
          ]
          ++ maybe [] (const [Set.empty]) rest
      CPInject member pattern' ->
        case concrete >>= injectedPayload member of
          Just payload ->
            go
              (Just payload)
              (termStructuralOrigins depth context payload)
              pattern'
          Nothing ->
            go Nothing (appendOriginStep (StructuralVariant member) origins) pattern'
      CPInjectRestM _ _ -> [Set.empty]
      CPOr patterns _ -> maybe [] (go concrete origins) (listToMaybe patterns)
      CPAsM _ _ pattern' -> origins : go concrete origins pattern'

    descendPosition concrete origins index pattern' =
      case concrete >>= positionalPayload index of
        Just payload ->
          go
            (Just payload)
            (termStructuralOrigins depth context payload)
            pattern'
        Nothing ->
          go Nothing (appendOriginStep (StructuralPosition index) origins) pattern'

    descendField concrete origins field pattern' =
      case concrete >>= recordPayload field of
        Just payload ->
          go
            (Just payload)
            (termStructuralOrigins depth context payload)
            pattern'
        Nothing ->
          go Nothing (appendOriginStep (StructuralField field) origins) pattern'

    appendOriginStep step =
      Set.map
        (\origin ->
           origin
             { structuralPath = structuralPath origin ++ [step]
             })

    positionalPayload index term =
      nthMaybe index $ case stripIdentityWrappers term of
        CCtorI _ _ _ arguments ->
          [caTerm argument | argument <- arguments, caPayload argument]
        CCtor _ _ arguments -> arguments
        CRecordV fields -> map snd fields
        _ -> []

    recordPayload field term =
      lookup field $ case stripIdentityWrappers term of
        CRecordV fields -> fields
        _ -> []

    injectedPayload member term = case stripIdentityWrappers term of
      CInject actual payload | actual == member -> Just payload
      _ -> Nothing

-- ── Structural size-change checking ──────────────────────────────────

structuralSccOK :: Map GName TermFun -> Maybe (Map GName [Text]) -> CheckM Bool
structuralSccOK funMap selectedNames = do
  edges <- collectSccEdges funMap
  structuralSccOKWithEdges funMap selectedNames edges

-- | Check a structural certificate against one authenticated call-edge
-- snapshot. Inferred measures change only the proposed rank, so sibling
-- certificate attempts must not re-traverse and re-normalize the SCC bodies.
structuralSccOKWithEdges
  :: Map GName TermFun
  -> Maybe (Map GName [Text])
  -> Maybe [CallEdge]
  -> CheckM Bool
structuralSccOKWithEdges funMap selectedNames mEdges = do
  case mEdges of
    Nothing -> pure False
    Just edges -> do
      st <- get
      let hasSchema function =
            maybe False ((> 0) . dutParameterCount . gdUniverses)
              (Map.lookup (tfName function) (csGlobals st))
          useSchemaDimension = any hasSchema (Map.elems funMap)
      candidates <- mapM (edgeStructuralGraph st funMap selectedNames useSchemaDimension) edges
      case sequence candidates of
        Nothing -> pure False
        Just graphs -> pure (not (null graphs) && sizeChangeTerminates graphs)

edgeStructuralGraph
  :: CheckState
  -> Map GName TermFun
  -> Maybe (Map GName [Text])
  -> Bool
  -> CallEdge
  -> CheckM (Maybe (SCGraph GName))
edgeStructuralGraph st funMap selectedNames useSchemaDimension edge =
  case (Map.lookup (edgeFrom edge) funMap, Map.lookup (edgeTo edge) funMap) of
    (Just src, Just tgt) -> do
      let srcRefs = selectedParamRefs src selectedNames
          tgtRefs = selectedParamRefs tgt selectedNames
          srcParams = map snd srcRefs
          tgtParams = map snd tgtRefs
          explArgs = [argument | (Expl, argument) <- edgeArgs edge]
          schemaChange =
            if useSchemaDimension
              then recursiveSchemaChangeForEdge st edge
              else Nothing
      case traverse (\(argumentIndex, _) -> nthMaybe argumentIndex explArgs) tgtRefs of
        Nothing -> pure Nothing
        Just targetArguments -> do
          -- Constructor values are commonly represented by eta-expanded Core
          -- applications. Classification uses definitional normal forms so the
          -- path proof below sees the same constructor reconstruction without
          -- baking an elaborator presentation into the termination checker.
          normalizedArguments <-
            mapM (normalizeTermAt (edgeDepth edge)) targetArguments
          if (null srcParams || null tgtParams) && not useSchemaDimension
            then pure Nothing
            else do
              let ordinaryEntries =
                    [ ((sourceIndex, targetIndex), change)
                    | (targetIndex, argument) <- zip [0 :: Int ..] normalizedArguments
                    , (sourceIndex, change) <-
                        structuralArgChanges
                          srcParams
                          (edgeDepth edge)
                          (edgeStructuralOrigins edge)
                          argument
                    ]
                  schemaEntries =
                    [ ((length srcParams, length tgtParams), change)
                    | useSchemaDimension
                    , change <- maybeToList schemaChange
                    ]
              pure
                ( Just
                    SCGraph
                      { scFrom = edgeFrom edge
                      , scTo = edgeTo edge
                      , scRows = length srcParams + if useSchemaDimension then 1 else 0
                      , scCols = length tgtParams + if useSchemaDimension then 1 else 0
                      , scMat = Map.fromListWith strongerChange (ordinaryEntries ++ schemaEntries)
                      }
                )
    _ -> pure Nothing

-- | Classify the static declaration-schema component of one SCT call edge.
-- Calls carry their exact finalized universe spine.  We match that spine
-- against elaboration-time occurrences and admit a strict edge only when
-- every matching occurrence proves pointwise non-increase and at least one
-- strict component.  Multiple same-shaped call sites with different lexical
-- assumptions therefore degrade to weak rather than borrowing another site's
-- proof.  Missing or incomparable evidence contributes no static edge.
recursiveSchemaChangeForEdge :: CheckState -> CallEdge -> Maybe Change
recursiveSchemaChangeForEdge st edge
  | sourceArity == 0 && targetArity == 0 = Just ChWeak
  | sourceArity == 0 || targetArity == 0 = Nothing
  | null matching = Nothing
  | any isNothing classified = Nothing
  | all (== Just ChStrict) classified = Just ChStrict
  | otherwise = Just ChWeak
  where
    assignments = csLevelAssignments st
    sourceArity = declarationArity (edgeFrom edge)
    targetArity = declarationArity (edgeTo edge)
    declarationArity name =
      maybe 0 (dutParameterCount . gdUniverses) (Map.lookup name (csGlobals st))
    normalize = normalizeLevel . substituteLevelMetas assignments
    edgeSpine = map normalize (edgeUniverses edge)
    matching =
      [ occurrence
      | occurrence <- csRecursiveSchemaOccurrences st
      , rsoCaller occurrence == edgeFrom edge
      , rsoCallee occurrence == edgeTo edge
      , map normalize (rsoLevels occurrence) == edgeSpine
      ]
    sourceLevels = map LParam [0 .. sourceArity - 1]
    classify occurrence =
      let targetLevels = map normalize (rsoLevels occurrence)
          occurrenceAssumptions = substituteLevelAssumptions assignments (rsoAssumptions occurrence)
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
       in if not pointwise
            then Nothing
            else Just (if strict then ChStrict else ChWeak)
    classified = map classify matching

selectedParamRefs :: TermFun -> Maybe (Map GName [Text]) -> [(Int, Int)]
selectedParamRefs f Nothing = zip [0 :: Int ..] (tfExplParams f)
selectedParamRefs f (Just byName) =
  case Map.lookup (tfName f) byName of
    Nothing -> []
    Just names ->
      [ (ix, lvl)
      | wanted <- names
      , Just ix <- [elemIndex wanted (tfParamNames f)]
      , Just lvl <- [nthMaybe ix (tfExplParams f)]
      ]

structuralArgChanges :: [Int] -> Int -> StructuralOrigins -> Term -> [(Int, Change)]
structuralArgChanges selected depth origins term =
  [ (index, if null (structuralPath origin) then ChWeak else ChStrict)
  | origin <- Set.toList (termStructuralOrigins depth origins term)
  , Just index <- [Map.lookup (structuralRoot origin) selectedIndex]
  ]
  where
    selectedIndex = Map.fromList (zip selected [0 :: Int ..])

insertStructuralAlias :: Int -> StructuralOrigins -> Term -> StructuralOrigins
insertStructuralAlias level origins rhs =
  let aliases = termStructuralOrigins level origins rhs
   in if Set.null aliases
        then origins
        else
          origins
            { structuralLocals =
                Map.insertWith Set.union level aliases (structuralLocals origins)
            }

recordMatchedStructuralShape
  :: Set StructuralOrigin -> CorePat -> StructuralOrigins -> StructuralOrigins
recordMatchedStructuralShape origins pattern' context
  | Set.null origins = context
  | otherwise = case pattern' of
      CPCtorM _ _ _ constructor universes [] ->
        insertShape (StructuralCtor constructor universes)
      CPLit literal -> insertShape (StructuralLiteral literal)
      CPOr (first : _) _ -> recordMatchedStructuralShape origins first context
      CPAsM _ _ inner -> recordMatchedStructuralShape origins inner context
      _ -> context
  where
    insertShape shape =
      context
        { structuralShapes =
            Map.insertWith Set.union shape origins (structuralShapes context)
        }

-- | Recover a structural subterm identity only from typed Core facts. A
-- constructor/record reconstruction is accepted when every argument is the
-- correctly ordered immediate child of one common path. This proves rebuilt
-- tails such as @second :: tail@ while rejecting reordered, duplicated, or
-- unrelated payloads.
termStructuralOrigins :: Int -> StructuralOrigins -> Term -> Set StructuralOrigin
termStructuralOrigins depth origins = go
  where
    go = \case
      CVar index ->
        Map.findWithDefault Set.empty (depth - 1 - index) (structuralLocals origins)
      -- Strictly-positive function-valued constructor fields denote families
      -- of recursive children. Application selects one child without changing
      -- the field's structural provenance.
      CApp _ function _ -> go function
      CProj receiver field -> Set.map (appendStep (StructuralField field)) (go receiver)
      CProjAt receiver field _ -> Set.map (appendStep (StructuralField field)) (go receiver)
      CCtorI constructor universes _ arguments ->
        let payload = [caTerm argument | argument <- arguments, caPayload argument]
         in if null payload
              then Map.findWithDefault Set.empty
                (StructuralCtor constructor universes)
                (structuralShapes origins)
              else reconstructPositions payload
      CRecordV fields -> reconstructFields fields
      CInject member value -> reconstructVariant member value
      CUniverseLift _ _ _ value -> go value
      CSchemaLift _ _ _ _ _ _ _ _ value -> go value
      CSealE _ value -> go value
      CLit literal ->
        Map.findWithDefault Set.empty
          (StructuralLiteral literal)
          (structuralShapes origins)
      _ -> Set.empty

    appendStep step origin =
      origin {structuralPath = structuralPath origin ++ [step]}

    reconstructPositions arguments =
      reconstructFromSuffixes
        [ (StructuralPosition index, go argument)
        | (index, argument) <- zip [0 ..] arguments
        ]

    reconstructFields fields =
      reconstructFromSuffixes
        [ (StructuralField field, go value)
        | (field, value) <- fields
        ]

    reconstructVariant member value =
      reconstructFromSuffixes [(StructuralVariant member, go value)]

    reconstructFromSuffixes [] = Set.empty
    reconstructFromSuffixes expected =
      case [Set.fromList
              (mapMaybe (stripExpected expectedStep) (Set.toList childOrigins))
           | (expectedStep, childOrigins) <- expected] of
        [] -> Set.empty
        first : rest -> foldl' Set.intersection first rest

    stripExpected expectedStep origin = do
      (prefix, actualStep) <- unsnoc (structuralPath origin)
      guard (actualStep == expectedStep)
      pure origin {structuralPath = prefix}

    unsnoc [] = Nothing
    unsnoc values = Just (init values, last values)

-- ── Explicit measure checking ────────────────────────────────────────

measureSccOK :: Map GName TermFun -> CheckM Bool
measureSccOK funMap = do
  edges <- collectSccEdges funMap
  measureSccOKWithEdges funMap edges

measureSccOKWithEdges :: Map GName TermFun -> Maybe [CallEdge] -> CheckM Bool
measureSccOKWithEdges funMap mEdges = do
  let specs = map tfMeasure (Map.elems funMap)
  if any isNothing specs
    then pure False
    else do
      compatible <- measureSpecsCompatible (catMaybes specs)
      if not compatible
        then pure False
        else do
          case mEdges of
            Nothing -> pure False
            Just edges -> case traverse (measureCallOfEdge funMap) edges of
              Nothing -> pure False
              Just calls -> do
                oks <- mapM measureCallOK calls
                pure (not (null calls) && and oks)

measureSpecsCompatible :: [MeasureSpec] -> CheckM Bool
measureSpecsCompatible [] = pure False
measureSpecsCompatible specs@(s0 : _) =
  do
    normalizedMeasures <- traverse (\s -> normalizeTermAt (msDepth s) (msMeasureTerm s)) specs
    case normalizedMeasures of
      [] -> pure False
      firstMeasure : restMeasures -> do
        let arity t = length (rankComponents t)
            expectedArity = arity firstMeasure
            sameArity = all (\t -> arity t == expectedArity) restMeasures
        pure (sameArity && sameMeasureType && sameRelationShape)
  where
    sameMeasureType = all (\s -> msMeasureTypeKey s == msMeasureTypeKey s0) specs
    relKey = fmap rsKey . msRelation
    relType = fmap rsTypeKey . msRelation
    sameRelationShape =
      all (\s -> fmap rsFlavor (msRelation s) == fmap rsFlavor (msRelation s0)) specs
        && all (\s -> relKey s == relKey s0) specs
        && all (\s -> relType s == relType s0) specs

measureCallOfEdge :: Map GName TermFun -> CallEdge -> Maybe MeasureCall
measureCallOfEdge funMap edge = do
  src <- Map.lookup (edgeFrom edge) funMap
  tgt <- Map.lookup (edgeTo edge) funMap
  srcSpec <- tfMeasure src
  tgtSpec <- tfMeasure tgt
  let tgtFormalLvls = map snd (tfParams tgt)
      supplied = take (length tgtFormalLvls) (edgeArgs edge)
      subst = Map.fromList (zip tgtFormalLvls (map snd supplied))
  if edgeDepth edge < msDepth srcSpec
    then Nothing
    else do
      newHere <- instantiateByLevelMaybe (msDepth tgtSpec) (edgeDepth edge) subst (msMeasureTerm tgtSpec)
      let oldHere = shiftTerm (edgeDepth edge - msDepth srcSpec) 0 (msMeasureTerm srcSpec)
      Just
        MeasureCall
          { mcDepth = edgeDepth edge
          , mcFacts = edgeFacts edge
          , mcOldMeasure = oldHere
          , mcNewMeasure = newHere
          , mcRelation = msRelation srcSpec
          , mcProof = msProof srcSpec
          , mcSource = src
          }

measureCallOK :: MeasureCall -> CheckM Bool
measureCallOK call = do
  let d = mcDepth call
      facts = mcFacts call
      oldM0 = mcOldMeasure call
      newM0 = mcNewMeasure call
      mRel = mcRelation call
      mProof = mcProof call
      src = mcSource call
  oldM <- normalizeTermAt d oldM0
  newM <- normalizeTermAt d newM0
  case (mRel, mProof) of
    (Nothing, Nothing) -> defaultMeasureCallOK (tfNatLvls src) d facts oldM newM
    (Nothing, Just _proofE) ->
      -- `using` is parsed and retained, but erased proof terms are not a
      -- termination oracle. Until proof checking produces inspectable descent
      -- evidence, a proof annotation can only accompany an internally proved
      -- measure decrease.
      defaultMeasureCallOK (tfNatLvls src) d facts oldM newM
    (Just rel, Nothing) -> do
      wf <- relationWellFoundedAtCall (tfNatLvls src) d facts rel oldM newM
      holds <- relationCallHolds (tfNatLvls src) d facts rel oldM newM
      pure (wf && holds)
    (Just rel, Just _proofE) -> do
      wf <- relationWellFoundedAtCall (tfNatLvls src) d facts rel oldM newM
      holds <- relationCallHolds (tfNatLvls src) d facts rel oldM newM
      pure (wf && holds)

defaultMeasureCallOK :: Set Int -> Int -> [AFact] -> Term -> Term -> CheckM Bool
defaultMeasureCallOK natLvls d facts oldM newM = do
  let oldCs = rankComponents oldM
      newCs = rankComponents newM
  if length oldCs /= length newCs
    then pure False
    else do
      nonNegOld <- mapM (componentNonNegative oldCs) oldCs
      nonNegNew <- mapM (componentNonNegative newCs) newCs
      dec <- lexDecreases (zip oldCs newCs)
      pure (and nonNegOld && and nonNegNew && dec)
  where
    componentNonNegative _ t = proveNonNeg natLvls facts d t
    lexDecreases [] = pure False
    lexDecreases ((oldC, newC) : rest) = do
      lt <- proveLt natLvls facts d newC oldC
      if lt
        then pure True
        else do
          eq <- proveEq natLvls facts d newC oldC
          if eq then lexDecreases rest else pure False

relationWellFoundedAtCall :: Set Int -> Int -> [AFact] -> RelationSpec -> Term -> Term -> CheckM Bool
relationWellFoundedAtCall natLvls d facts rel oldM newM
  | rsWellFounded rel = pure True
  | otherwise = do
      relHere <- normalizeTermAt d (shiftTerm (d - rsDepth rel) 0 (rsTerm rel))
      isLt <- relationIsPrimitiveLtInt d relHere
      if isLt
        then do
          oldOK <- and <$> mapM (proveNonNeg natLvls facts d) (rankComponents oldM)
          newOK <- and <$> mapM (proveNonNeg natLvls facts d) (rankComponents newM)
          pure (oldOK && newOK)
        else pure False

relationCallHolds :: Set Int -> Int -> [AFact] -> RelationSpec -> Term -> Term -> CheckM Bool
relationCallHolds natLvls d facts rel oldM newM = do
  relHere <- normalizeTermAt d (shiftTerm (d - rsDepth rel) 0 (rsTerm rel))
  goal <- normalizeTermAt d (CApp Expl (CApp Expl relHere newM) oldM)
  case rsFlavor rel of
    RelationReturnsBool -> proveBoolTrue natLvls facts d goal
    RelationReturnsType -> proveTypeRelationTrue natLvls facts d goal
    RelationUnknown -> pure False

-- ── Normalization and arithmetic evidence ────────────────────────────
