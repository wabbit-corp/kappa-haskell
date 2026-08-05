-- | Syntax quotes, splices, and macros (Spec §21).
--
-- Helpers for quoted syntax and its grafting slots, including the hygiene
-- bookkeeping that keeps a spliced binder from capturing the wrong name.
--
-- Carved out of "Kappa.Check" as part of splitting that module; see
-- "Kappa.Check.Types" for the shared data dictionary and docs\/CONCEPTS.md
-- for the vocabulary these assume.
module Kappa.Check.Quotes
  ( canonicalReflectionQuery
  , elabCarrierUniverses
  , elabPrimitiveAt
  , elabPureAt
  , evalRT
  , extendHyg
  , graftQuoteV
  , headGlobalOf
  , metaPhaseType
  , mkQuotedSyntax
  , splicePhaseCheck
  , symbolValue
  , trySpec
  , validateCaptures
  , vappRT
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

evalRT :: Ctx -> Term -> CheckM Value
evalRT ctx t = do
  ec <- ecRT_
  pure (eval ec (ctxEnv ctx) t)

vappRT :: Value -> [Value] -> CheckM Value
vappRT f as = do
  ec <- ecRT_
  pure (List.foldl' (\g a -> vapp ec g Expl a) f as)

-- | Run an elaboration speculatively: keep its result only when it
-- reported no new diagnostics; otherwise restore the full state.
trySpec :: CheckM a -> CheckM (Maybe a)
trySpec act = do
  st0 <- get
  n0 <- gets (length . csDiags)
  r <- act
  n1 <- gets (length . csDiags)
  if n1 == n0 then pure (Just r) else put st0 >> pure Nothing

-- | Prefer an expected-directed elaboration, but admit a compatibility
-- alternative when that alternative succeeds without diagnostics. If both
-- paths fail, retain the primary result and its diagnostics. This is the
-- diagnostic-preserving counterpart of 'trySpec': callers must not replace a
-- precise checked failure with a noisier inference failure merely because a
-- legacy accommodation was attempted second.
preferPrimaryElaboration :: CheckM a -> CheckM a -> CheckM a
preferPrimaryElaboration primary alternative = do
  initial <- get
  diagnosticCount <- gets (length . csDiags)
  primaryResult <- primary
  primaryState <- get
  primaryDiagnosticCount <- gets (length . csDiags)
  if primaryDiagnosticCount == diagnosticCount
    then pure primaryResult
    else do
      put initial
      trySpec alternative >>= \case
        Just alternativeResult -> pure alternativeResult
        Nothing -> put primaryState >> pure primaryResult

elabPrimitiveAt :: Text -> [Level] -> Term
elabPrimitiveAt name universes = CGlobI (GName primModule name) universes

elabPureAt :: Ctx -> [Level] -> Value -> Term -> CheckM Term
elabPureAt ctx universes valueType value = do
  valueTypeTerm <- quoteIn ctx valueType
  pure (CApp Expl (CApp Impl (elabPrimitiveAt "__elabPure" universes) valueTypeTerm) value)

elabCarrierUniverses :: Value -> CheckM [Level]
elabCarrierUniverses carrier =
  forceM carrier >>= \case
    VGlobI global universes _ | global == prelElab -> pure universes
    _ -> pure []

-- | §21.4 hygiene metadata: rename quote-site local references to
-- fresh hygienic spellings and record (spelling, original, level).
mkQuotedSyntax :: Ctx -> Expr -> Span -> CheckM QuotedSyntax
mkQuotedSyntax ctx payload sp = do
  let bound = boundNamesIn payload
      occ = nub [nameText n | n <- freeVarOccurrences payload]
      capturable =
        [ (nm, i)
        | nm <- occ
        , nm `notElem` bound
        , Just (i, _) <- [lookupCtx nm ctx]
        ]
  caps <- forM capturable $ \(nm, i) -> do
    h <- freshNameM (nm <> "__hyg")
    pure (QuoteCapture h nm (ctxLen ctx - 1 - i))
  let ren = Map.fromList [(qcOrig c, qcHyg c) | c <- caps]
  pure (QuotedSyntax (renameVarOccurrences ren payload) caps sp)

-- | The §21.6 convenience reflection queries that may be run directly
-- by the elaborator in ordinary term positions.
reflQueryNames :: [Text]
reflQueryNames = ["defEqSyntax", "headSymbolSyntax", "typeOfSyntax"]

-- | Authenticate a convenience query by exact resolved declaration identity.
-- A same-spelling local, alias declaration, or member is an ordinary value.
-- An ascribed expression is deliberately excluded: its asserted type must be
-- checked by the ordinary application path before any convenience behavior.
canonicalReflectionQuery :: Ctx -> Expr -> CheckM (Maybe GName)
canonicalReflectionQuery ctx expression
  | staticQueryHead expression = do
      resolved <- staticGlobalExpr ctx expression
      pure $ do
        global@(GName owner name) <- resolved
        guard (owner == preludeModule && name `elem` reflQueryNames)
        pure global
  | otherwise = pure Nothing
  where
    staticQueryHead = \case
      EVar {} -> True
      EDot {} -> True
      _ -> False

-- | The global declaration head of an elaborated core term, if any
-- (§21.6 'headSymbol': None for variables, binders, locals, and
-- literals).
headGlobalOf :: Term -> Maybe GName
headGlobalOf = \case
  CApp _ f _ -> headGlobalOf f
  CGlob g@(GName m _) | m /= primModule -> Just g
  CCtor g _ _ -> Just g
  _ -> Nothing

-- | A §21.6 'Symbol' value: resolved declaration identity.
symbolValue :: GName -> Value
symbolValue (GName (ModuleName segs) n) =
  VPrim "__symbolV" [VLit (LitStr (T.intercalate "." segs <> "::" <> n))]

-- | §21.9 phase check: object-phase runtime locals cannot enter an
-- elaboration-time splice argument (only meta-phase carriers may).
splicePhaseCheck :: Ctx -> Expr -> CheckM Bool
splicePhaseCheck ctx me = do
  let bound = boundNamesIn me
      occs =
        [ (n, i)
        | n <- freeVarOccurrences me
        , nameText n `notElem` bound
        , not (Map.member (nameText n) (ctxHyg ctx))
        , Just (i, _) <- [lookupCtx (nameText n) ctx]
        ]
  bad <- filterM (\(_, i) -> not <$> metaPhaseType (ceType (ctxEntries ctx !! i))) occs
  case bad of
    [] -> pure True
    ((n, _) : _) -> do
      errAt (nameSpan n) "E_ELAB_PHASE" (Just "kappa-hs.macro.phase")
        ("the object-phase runtime binding '" <> nameText n
           <> "' cannot be captured by an elaboration-time splice; object-phase terms enter 'Elab' only through meta-phase carriers such as 'Syntax' (§21.9)")
      pure False

-- | Is a local's type a meta-phase carrier admissible inside 'Elab'?
metaPhaseType :: Value -> CheckM Bool
metaPhaseType v = do
  t <- forceM v
  case t of
    -- type, row, quantity, and region parameters are erased
    -- classifier-level entities; mentioning them does not smuggle an
    -- object-phase runtime value into Elab (§21.9)
    VSort _ -> pure True
    VGlobN (GName pm g) args
      | pm == preludeModule
      , g `elem`
          [ "Syntax", "Elab", "SyntaxOrigin", "SyntaxFragment"
          , "RawComprehension", "ComprehensionPlan"
          , "RecRow", "EffRow", "Quantity", "Region", "EffLabel"
          ] ->
          pure True
      | pm == preludeModule
      , g `elem` ["List", "Option"]
      , ((_, a) : _) <- args ->
          metaPhaseType a
    VGlobN (GName m _) _ | m == shapeModule -> pure True
    _ -> pure False

-- | Graft a syntax value: force the slot values to quotes and
-- substitute them into the payload's grafting holes (§21.2).
graftQuoteV :: Ctx -> Span -> Value -> CheckM (Maybe QuotedSyntax)
graftQuoteV ctx sp v0 = do
  v <- forceRT v0
  case v of
    VQuote qs slots -> do
      subs <- mapM (graftQuoteV ctx sp) slots
      case sequence subs of
        Nothing -> pure Nothing
        Just qss ->
          pure $
            Just
              QuotedSyntax
                { qsExpr = substQuoteHoles (Map.fromList (zip [0 ..] (map qsExpr qss))) (qsExpr qs)
                , qsCaptures = qsCaptures qs ++ concatMap qsCaptures qss
                , qsSpan = qsSpan qs
                }
    _ -> do
      errAt sp "E_SPLICE_REQUIRES_SYNTAX" (Just "kappa-hs.syntax.splice")
        "the elaboration-time action did not produce a 'Syntax' value this implementation can splice (§21.2)"
      pure Nothing

-- | §21.4: every free hygienic binder of spliced syntax must still be
-- valid at the splice site.
validateCaptures :: Ctx -> Span -> [QuoteCapture] -> CheckM Bool
validateCaptures ctx sp caps = do
  let n = ctxLen ctx
      entryOk c =
        let i = n - 1 - qcLevel c
         in i >= 0 && i < n && ceName (ctxEntries ctx !! i) == qcOrig c
      bad = [c | c <- caps, not (entryOk c)]
  forM_ (take 1 bad) $ \c ->
    errAt sp "E_SYNTAX_SCOPE_ESCAPE" (Just "kappa-hs.syntax.scope-escape")
      ("this Syntax value mentions the local binder '" <> qcOrig c
         <> "' (or its borrow region) whose scope has ended; a Syntax value may escape a lexical scope only while every free hygienic binder it references remains valid, and splicing requires those binders at the splice site (§21.4)")
  pure (null bad)

extendHyg :: Ctx -> [QuoteCapture] -> Ctx
extendHyg ctx caps = ctx {ctxHyg = foldr ins (ctxHyg ctx) caps}
  where
    n = ctxLen ctx
    ins c m = case drop (n - 1 - qcLevel c) (ctxEntries ctx) of
      e : _ -> Map.insert (qcHyg c) (qcLevel c, ceType e) m
      [] -> m
