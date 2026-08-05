-- | Algebraic effects: labels, operations, handlers.
--
-- Helpers for scoped effect declarations (§9.3.1.1) and for selecting an
-- operation against its owning interface's parameter telescope.
--
-- Carved out of "Kappa.Check" as part of splitting that module; see
-- "Kappa.Check.Types" for the shared data dictionary and docs\/CONCEPTS.md
-- for the vocabulary these assume.
module Kappa.Check.Effects
  ( applicativeDoShape
  , canonicalApplicativePurePayload
  , declSpan
  , doItemSpan
  , doItemsRequireEffectAwareLifting
  , effLabelKey
  , effMerged
  , effTupleField
  , effectOpValueInfo
  , instOpTypes
  , isMultishotOpValue
  , lookupEffLabelM
  , monadDoNeedsStructuredElaboration
  , nonDepPiModeV
  , nonDepPiV
  , operationValueInfoOfExpr
  , preferCheckByErrors
  , recordMultishotOpApplication
  , recordMultishotOps
  , tailResumptiveField
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

-- | §18.1.16/§18.1.17: record the MULTI-SHOT operation names (resumption
-- quantity ω or 1+) of an effect declaration, for the §34.3.3 native-backend
-- capability gate (rt-multishot-effects absent).  Called for both scoped and top-level
-- effect declarations so scoped-effect multi-shot ops are covered too.
recordMultishotOps :: [EffOpInfo] -> CheckM ()
recordMultishotOps ops =
  let names = [eoiName op | op <- ops, eoiQ op `elem` [QW, QGe1]]
   in unless (null names) $
        modify' $ \st -> st {csMultishotOps = foldr Set.insert (csMultishotOps st) names}

-- | Effect-label resolution (§18.1): a §9.3.1.1 lexically scoped effect in
-- 'ctxEffLabels' wins; otherwise a module-level (top-level) @effect@
-- declaration in 'csModEffLabels' is visible everywhere in the module.
-- | §18.1.18: the unique runtime identity string of an effect label (its
-- fully-qualified global name), used as the native label token.
effLabelKey :: GName -> Text
effLabelKey (GName (ModuleName segs) nm) = T.intercalate "." (segs ++ [nm])

lookupEffLabelM :: Ctx -> Text -> CheckM (Maybe EffLabelInfo)
lookupEffLabelM ctx nm = case Map.lookup nm (ctxEffLabels ctx) of
  Just e -> pure (Just e)
  Nothing -> gets (Map.lookup nm . csModEffLabels)

-- | The scoped (§9.3.1.1) and top-level (§18.1) effect labels visible here,
-- merged (scoped wins), for use in pure pattern guards.
effMerged :: Ctx -> CheckM (Map Text EffLabelInfo)
effMerged ctx = gets (\st -> Map.union (ctxEffLabels ctx) (csModEffLabels st))

-- | A non-dependent function-type value (level-safe: the codomain is
-- captured in the closure environment).
nonDepPiV :: Q -> Value -> Value -> Value
nonDepPiV q dom cod =
  VPiEvidenceM Ordinary FormationOrdinary Expl q False "_" Nothing BinderSourceWritten dom
    (Closure [cod] (CVar 1))

nonDepPiModeV :: ObservationMode -> FormationMode -> Q -> Bool -> Value -> Value -> Value
nonDepPiModeV mode formation q borrowed dom cod =
  VPiEvidenceM mode formation Expl q borrowed "_" Nothing BinderSourceWritten dom
    (Closure [cod] (CVar 1))

-- | Instantiate an operation's payload and result types at concrete effect
-- parameter VALUES (outer-to-inner). The stored types are de Bruijn under the
-- parameter binders, so the eval environment lists the parameters
-- innermost-first.
instOpTypes :: EvalCtx -> [Value] -> EffOpInfo -> ([Value], Value)
instOpTypes ec ps op =
  let step (values, bound) entry =
        let domain = eval ec (reverse (ps ++ bound)) (teDomain entry)
            -- Handler clause binders are introduced immediately after the
            -- operation's implicit skolems. These rigids keep later argument
            -- domains and the result type scoped over the same telescope.
            rigid = VRigid (length ps + length bound) []
         in (values ++ [domain], bound ++ [rigid])
      (arguments, argumentRigids) = foldl' step ([], []) (eoiArgs op)
   in (arguments, eval ec (reverse (ps ++ argumentRigids)) (eoiResT op))

-- | The field name of the @i@-th tuple component (§6.6 tuples are records with
-- @_1@, @_2@, … fields), used to bundle a multi-argument operation payload.
effTupleField :: Int -> Text
effTupleField i = "_" <> T.pack (show (i + 1))

-- | §4b reserved field on a handler's @ops@ record carrying the set of
-- tail-resumptive operation names (a sub-record @{ opName -> Unit }@). The
-- runtime @do_perform@ projects it to take the constant-@Cont@-depth fast
-- path. The @__@ prefix keeps it disjoint from every user operation name
-- (operations are source identifiers), so @kproj(ops, opName)@ never sees
-- it; the interpreter's @lookup opn fs@ likewise ignores it.
tailResumptiveField :: Text
tailResumptiveField = "__tailResumptive"

effectOpValueInfo :: EffLabelInfo -> EffOpInfo -> EffectOpValueInfo
effectOpValueInfo eli op =
  EffectOpValueInfo
    { eoviLabel = eliLabel eli
    , eoviName = eoiName op
    , eoviQ = eoiQ op
    , eoviArity = length (eoiArgs op)
    }

isMultishotOpValue :: EffectOpValueInfo -> Bool
isMultishotOpValue info = eoviQ info `elem` [QW, QGe1]

operationValueInfoOfExpr :: Ctx -> Expr -> CheckM (Maybe EffectOpValueInfo)
operationValueInfoOfExpr ctx = \case
  EAscription e _ _ -> operationValueInfoOfExpr ctx e
  EDot (EVar ln) member -> do
    merged <- effMerged ctx
    let opname = case member of
          DotName n -> nameText n
          DotOperator n -> nameText n
    pure $ do
      eli <- Map.lookup (nameText ln) merged
      op <- find ((== opname) . eoiName) (eliOps eli)
      pure (effectOpValueInfo eli op)
  EVar n ->
    case lookupCtx (nameText n) ctx of
      Just (_, entry) -> pure (ceOpValueInfo entry)
      Nothing -> do
        mg <- lookupGlobalName (nameText n)
        case mg of
          Nothing -> pure Nothing
          Just g -> gets (Map.lookup g . csEffectOpValueGlobals)
  EApp f args
    | all isImplicitArg args -> operationValueInfoOfExpr ctx f
  _ -> pure Nothing
  where
    isImplicitArg = \case
      ArgImplicit {} -> True
      _ -> False

recordMultishotOpApplication :: Ctx -> Expr -> [Arg] -> Span -> CheckM ()
recordMultishotOpApplication ctx f args sp = do
  minfo <- operationValueInfoOfExpr ctx f
  forM_ minfo $ \info ->
    when (isMultishotOpValue info && explicitArgCount args >= eoviArity info) $
      recordRecognizedMultishotOp sp info
  where
    explicitArgCount = length . mapMaybe (\case
      ArgExplicit _ -> Just ()
      _ -> Nothing)

-- | Conservative Appendix G.2 applicability check. The dependency set is
-- lexical, but the resulting term is elaborated normally: names do not select
-- any operation, and every pattern still passes the ordinary irrefutability,
-- exhaustiveness, quantity, and borrow judgments.
applicativeDoShape
  :: [DoItem]
  -> Maybe ([(Pattern, Expr)], [LetBind], Expr, Set Text)
applicativeDoShape = go Set.empty [] []
  where
    go bound actions lets = \case
      [DoExpr finalExpression] ->
        Just (reverse actions, reverse lets, finalExpression, bound)
      DoBind binding : rest
        | let dependencies =
                Set.fromList
                  (map nameText (freeVarOccurrencesScoped (lbExpr binding)))
        , Set.null (Set.intersection bound dependencies) ->
            let introduced =
                  Set.fromList (map nameText (surfPatVars (lbPattern binding)))
             in go
                  (Set.union bound introduced)
                  ((lbPattern binding, lbExpr binding) : actions)
                  lets
                  rest
      DoLet binding : rest ->
        let introduced =
              Set.fromList (map nameText (surfPatVars (lbPattern binding)))
         in go
              (Set.union bound introduced)
              actions
              (binding : lets)
              rest
      _ -> Nothing

-- | Whether any expression in a user-carrier do block requires semantic
-- lifting. Independent binds remain eligible for Applicative lowering, but the
-- fast path must not bypass mutable-current reads, explicit splices, generated
-- reads, or reference-facet effects.
doItemsRequireEffectAwareLifting :: Ctx -> [DoItem] -> Bool
doItemsRequireEffectAwareLifting ctx = any go
  where
    exprNeedsLift e =
      exprHasCurrentRead ctx e
        || exprHasBang e
        || exprHasGeneratedVarRead e
        || not (Set.null (collectRefFacets e))
    exprHasGeneratedVarRead = \case
      EVarRead {} -> True
      _ -> False
    go = \case
      DoBind binding -> exprNeedsLift (lbExpr binding)
      DoVar _ _ rhs _ -> exprNeedsLift rhs
      DoWhile _ condition body mElse _ ->
        exprNeedsLift condition || any go body || maybe False (any go) mElse
      DoFor _ _ src body mels _ ->
        exprNeedsLift src || any go body || maybe False (any go) mels
      DoIf alts mels _ ->
        any (\(cnd, body) -> exprNeedsLift cnd || any go body) alts
          || maybe False (any go) mels
      DoExpr e -> exprNeedsLift e
      DoLet lb -> exprNeedsLift (lbExpr lb)
      DoLetQ _ rhs mElse _ ->
        exprNeedsLift rhs || maybe False (exprNeedsLift . snd) mElse
      DoAssign _ _ rhs _ -> exprNeedsLift rhs
      DoUsing _ _ rhs _ -> exprNeedsLift rhs
      DoDefer _ e _ -> exprNeedsLift e
      _ -> False

-- | The Monad lowering additionally owns sequencing forms whose typing depends
-- on completed action boundaries, even if their expressions need no lifting.
monadDoNeedsStructuredElaboration :: Ctx -> [DoItem] -> Bool
monadDoNeedsStructuredElaboration ctx items =
  doItemsRequireEffectAwareLifting ctx items
    || any structurallyTyped items
    || any isDiscardedExpression (dropLast items)
  where
    dropLast [] = []
    dropLast [_] = []
    dropLast (item : rest) = item : dropLast rest
    isDiscardedExpression DoExpr {} = True
    isDiscardedExpression DoIf {} = True
    isDiscardedExpression _ = False
    structurallyTyped = \case
      DoBind {} -> True
      DoVar {} -> True
      DoWhile {} -> True
      DoFor {} -> True
      DoReturn {} -> True
      DoBreak {} -> True
      DoContinue {} -> True
      _ -> False

-- | Authenticate a source application as the canonical prelude
-- @Applicative.pure@ projection. The source spelling only identifies a lookup
-- candidate; the resolved Core head is the authority.
canonicalApplicativePurePayload :: Ctx -> Expr -> CheckM (Maybe Expr)
canonicalApplicativePurePayload ctx = \case
  EApp headExpression [ArgExplicit payload] -> do
    resolvedHead <- staticGlobalExpr ctx headExpression
    pure (payload <$ guard (resolvedHead == Just (gPrel "pure")))
  _ -> pure Nothing

-- | Prefer the first expected-directed elaboration, but retry from the complete
-- checker state when it emits errors and retain whichever branch emits fewer.
-- Failed speculative checks may allocate metas, constraints, evidence, and
-- diagnostics, so rolling back only a subset of 'CheckState' is unsound.
preferCheckByErrors :: CheckM Term -> CheckM Term -> CheckM Term
preferCheckByErrors primary fallback = do
  checkpoint <- get
  baselineErrors <- gets (length . filter isError . csDiags)
  primaryTerm <- primary
  primaryErrors <- gets (length . filter isError . csDiags)
  if primaryErrors == baselineErrors
    then pure primaryTerm
    else do
      primaryState <- get
      put checkpoint
      fallbackTerm <- fallback
      fallbackErrors <- gets (length . filter isError . csDiags)
      if fallbackErrors < primaryErrors
        then pure fallbackTerm
        else put primaryState >> pure primaryTerm

doItemSpan :: DoItem -> Span
doItemSpan = \case
  DoBind lb -> lbSpan lb
  DoLet lb -> lbSpan lb
  DoLetQ _ _ _ s -> s
  DoVar _ _ _ s -> s
  DoAssign _ _ _ s -> s
  DoExpr e -> exprSpan e
  DoUsing _ _ _ s -> s
  DoDefer _ _ s -> s
  DoReturn _ _ s -> s
  DoBreak _ s -> s
  DoContinue _ s -> s
  DoWhile _ _ _ _ s -> s
  DoFor _ _ _ _ _ s -> s
  DoIf _ _ s -> s
  DoDecl d -> declSpan d

declSpan :: Decl -> Span
declSpan = \case
  DSig _ _ _ sp -> sp
  DLet _ _ sp -> sp
  DData _ _ sp -> sp
  DTypeAlias _ _ _ _ _ sp -> sp
  DTrait _ _ sp -> sp
  DInstance _ sp -> sp
  DDerive _ sp -> sp
  DEffect _ _ sp -> sp
  DFixity _ sp -> sp
  DImport _ sp -> sp
  DExport _ sp -> sp
  DExpect _ _ sp -> sp
  DPattern _ _ sp -> sp
  DProjection _ _ _ _ _ sp -> sp
  DTopSplice _ sp -> sp
  DUnsafeAssert _ _ sp -> sp

-- ── if / match ───────────────────────────────────────────────────────
