-- | Comprehension desugaring (Spec §20).
--
-- Rewriting a comprehension into ordinary iteration before elaboration
-- proper sees it.
--
-- Carved out of "Kappa.Check" as part of splitting that module; see
-- "Kappa.Check.Types" for the shared data dictionary and docs\/CONCEPTS.md
-- for the vocabulary these assume.
module Kappa.Check.Comprehensions
  ( cardManyHi
  , cardName
  , cardSub
  , cardZeroLo
  , conflictLam
  , decodeLinearQuantity
  , decodeQueryMode
  , defaultAnn
  , desugarComp
  , filterCard
  , mulCard
  , occursVar
  , pairEqLam
  , prelApp1
  , yieldExprsOf
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

cardName :: QCard -> Text
cardName = \case
  CZero -> "QZero"
  COne -> "QOne"
  CZeroOrOne -> "QZeroOrOne"
  COneOrMore -> "QOneOrMore"
  CZeroOrMore -> "QZeroOrMore"

cardIv :: QCard -> (Int, Maybe Int)
cardIv = \case
  CZero -> (0, Just 0)
  COne -> (1, Just 1)
  CZeroOrOne -> (0, Just 1)
  COneOrMore -> (1, Nothing)
  CZeroOrMore -> (0, Nothing)

cardOf :: (Int, Maybe Int) -> QCard
cardOf = \case
  (0, Just 0) -> CZero
  (1, Just 1) -> COne
  (0, Just 1) -> CZeroOrOne
  (1, Nothing) -> COneOrMore
  _ -> CZeroOrMore

mulCard :: QCard -> QCard -> QCard
mulCard a b =
  let (al, ah) = cardIv a
      (bl, bh) = cardIv b
      hi = case (ah, bh) of
        (Just x, Just y) -> Just (min 1 (x * y))
        (Just 0, _) -> Just 0
        (_, Just 0) -> Just 0
        _ -> Nothing
   in cardOf (min 1 (al * bl), hi)

filterCard :: QCard -> QCard
filterCard c = let (_, h) = cardIv c in cardOf (0, h)

-- | May the inferred cardinality be checked against the demanded one
-- (interval subset, §20.10.1)?
cardSub :: QCard -> QCard -> Bool
cardSub a b =
  let (al, ah) = cardIv a
      (bl, bh) = cardIv b
      hiOk = case (ah, bh) of
        (_, Nothing) -> True
        (Just x, Just y) -> x <= y
        (Nothing, Just _) -> False
   in al >= bl && hiOk

cardManyHi :: QCard -> Bool
cardManyHi c = case snd (cardIv c) of
  Nothing -> True
  Just h -> h > 1

cardZeroLo :: QCard -> Bool
cardZeroLo c = fst (cardIv c) == 0

decodeQueryMode :: Value -> CheckM (Bool, QCard)
decodeQueryMode m0 = do
  m <- forceM m0
  case m of
    VCtor (GName _ "QueryMode") [u0, c0] -> do
      u <- forceM u0
      c <- forceM c0
      let oneShot = case u of
            VCtor (GName _ "OneShot") _ -> True
            _ -> False
          card = case c of
            VCtor (GName _ "QZero") _ -> CZero
            VCtor (GName _ "QOne") _ -> COne
            VCtor (GName _ "QZeroOrOne") _ -> CZeroOrOne
            VCtor (GName _ "QOneOrMore") _ -> COneOrMore
            _ -> CZeroOrMore
      pure (oneShot, card)
    _ -> pure (False, CZeroOrMore)

-- | Is the quantity value the linear quantity @1@?
decodeLinearQuantity :: Value -> CheckM Bool
decodeLinearQuantity q0 = do
  q <- forceM q0
  pure $ case q of
    VPrim "__quantityOfNat" [VLit (LitInt 1)] -> True
    _ -> False

-- | Does the variable occur (syntactically) in the expression?
occursVar :: Text -> Expr -> Bool
occursVar v = go
  where
    go = \case
      EVar (Name n _) -> n == v
      EApp f as -> go f || any goA as
      EDot b _ -> go b
      EQDot b _ -> go b
      EOpChain els -> or [go x | ChainOperand x <- els]
      ETuple es _ -> any go es
      ERecordLit is _ -> or [go e | RecItem _ _ (Just e) <- is]
      ERecordPatch b items _ ->
        go b
          || or
            [ case it of
                PatchUpdate _ (PatchValue e) -> go e
                PatchExtend _ e -> go e
                PatchSection a e -> go a || go e
                PatchPun _ -> False
            | it <- items
            ]
      EListLit es _ -> any go es
      ESetLit es _ -> any go es
      EMapLit kvs _ -> any (\(k, w) -> go k || go w) kvs
      EIf alts mels _ -> any (\(c, t) -> go c || go t) alts || maybe False go mels
      EMatch s cs _ -> go s || or [maybe False go g || go b | MatchCase _ g b _ <- cs]
      ELambda _ _ b _ -> go b
      ELet bs b _ -> any (go . lbExpr) bs || go b
      EAscription e _ _ -> go e
      ESectionLeft e _ _ -> go e
      ESectionRight _ e _ -> go e
      EElvis a b _ -> go a || go b
      EIs e _ -> go e
      EThunk e _ -> go e
      ELazy e _ -> go e
      EForce e _ -> go e
      EBang _ e _ -> go e
      EStringLit _ parts _ -> any (go . ipExpr) parts
      EDo _ items _ -> any goItem items
      EComprehension _ cls yy _ ->
        any goClause cls || any go (yieldExprsOf yy)
      _ -> False
    goA = \case
      ArgExplicit e -> go e
      ArgImplicit e -> go e
      ArgInout e _ -> go e
      ArgNamedBlock fs _ -> or [maybe False go me | (_, me) <- fs]
    goItem = \case
      DoBind lb -> go (lbExpr lb)
      DoLet lb -> go (lbExpr lb)
      DoLetQ _ e mfb _ -> go e || maybe False (go . snd) mfb
      DoExpr e -> go e
      _ -> True -- conservative for loops/var/defer items
    goClause = \case
      S.CFor _ _ _ src _ -> go src
      S.CLet _ _ _ rhs _ -> go rhs
      S.CIf e -> go e
      S.COrderBy ks _ -> any (go . snd) ks
      S.CSkip e _ -> go e
      S.CTake e _ -> go e
      S.CDistinct me _ -> maybe False go me
      S.CGroupBy k aggs _ _ -> go k || or [go e || maybe False go mu | (_, e, mu) <- aggs]
      S.CJoin _ _ src cond _ _ -> go src || go cond

yieldExprsOf :: CompYield -> [Expr]
yieldExprsOf = \case
  YieldExpr e -> [e]
  YieldPair k v -> [k, v]

defaultAnn :: CAnn
defaultAnn = CAnn SKUnknown False

prelApp1 :: Span -> Text -> [Expr] -> Expr
prelApp1 sp n es = EApp (EVar (Name n sp)) (map ArgExplicit es)

-- | @\\a b -> a == b@.
pairEqLam :: Span -> CheckM Expr
pairEqLam sp = do
  a <- freshNameM "__a"
  b <- freshNameM "__b"
  let an = Name a sp
      bn = Name b sp
  pure $
    ELambda Nothing [simpleBinder an, simpleBinder bn]
      (EApp (EOpRef Nothing (Name "==" sp) sp) [ArgExplicit (EVar an), ArgExplicit (EVar bn)])
      sp

-- | The map-conflict combine function (§20.5.1); default keep last.
conflictLam :: Ctx -> Maybe OnConflict -> Span -> CheckM Expr
conflictLam ctx mconf sp = case fromMaybe KeepLast mconf of
  KeepLast -> two (\_ b -> EVar b)
  KeepFirst -> two (\a _ -> EVar a)
  CombineWith f -> pure f
  CombineUsing w -> case ctorRefOfExpr w of
    Just cref -> do
      a <- freshNameM "__old"
      b <- freshNameM "__new"
      x <- freshNameM "__x"
      let an = Name a sp
          bn = Name b sp
          xn = Name x sp
          wrap e = EApp w [ArgExplicit e]
          appended = prelApp1 sp "append" [wrap (EVar an), wrap (EVar bn)]
      pure $
        ELambda Nothing [simpleBinder an, simpleBinder bn]
          (EMatch appended [MatchCase (PCtor cref [PVar xn] sp) Nothing (EVar xn) sp] sp)
          sp
    Nothing -> do
      _ <- unsupported ctx sp "this 'combine using' wrapper form"
      two (\_ b -> EVar b)
  where
    two f = do
      a <- freshNameM "__old"
      b <- freshNameM "__new"
      let an = Name a sp
          bn = Name b sp
      pure (ELambda Nothing [simpleBinder an, simpleBinder bn] (f an bn) sp)

ctorRefOfExpr :: Expr -> Maybe CtorRef
ctorRefOfExpr = \case
  EVar n -> Just (CtorRef Nothing n)
  EDot (EVar q) (DotName n) -> Just (CtorRef (Just q) n)
  _ -> Nothing

-- | Pass 2: desugar the clause pipeline over lists (§20.10.11 as-if).
-- The pipeline expression has type @List Row@ where @Row@ is the tuple
-- of the variables bound so far.
desugarComp :: Ctx -> [(S.CompClause, CAnn)] -> CompYield -> Span -> CheckM Expr
desugarComp ctx clauses yld sp = do
  (vars, pipe) <- foldM step ([], EListLit [EUnit sp] sp) clauses
  yf <- perRow vars (yieldElem yld)
  pure (prelApp1 sp "__pipeMap" [pipe, yf])
  where
    yieldElem = \case
      YieldExpr e -> e
      YieldPair k v ->
        ERecordLit [RecItem False (Name "key" sp) (Just k), RecItem False (Name "value" sp) (Just v)] sp

    rowE vars = case vars of
      [] -> EUnit sp
      [v] -> EVar v
      vs -> ETuple (map EVar vs) sp
    rowP vars = case vars of
      [] -> PWild sp
      [v] -> PVar v
      vs -> PTuple (map PVar vs) sp

    perRow vars body = do
      r <- freshNameM "__row"
      let rn = Name r sp
      pure $
        ELambda Nothing [simpleBinder rn]
          (EMatch (EVar rn) [MatchCase (rowP vars) Nothing body sp] sp)
          sp

    cmap f l = prelApp1 sp "__pipeConcatMap" [l, f]

    wrapSrc k src = case k of
      SKQuery -> prelApp1 sp "__queryToList" [src]
      SKSet -> prelApp1 sp "__setToList" [src]
      SKMap -> prelApp1 sp "__mapToList" [src]
      SKOption -> prelApp1 sp "__optionToList" [src]
      SKArray -> prelApp1 sp "__arrayToList" [src]
      SKRange -> prelApp1 sp "rangeToList" [src]
      SKIntoQuery ->
        prelApp1 sp "__intoQueryToListAs" [src]
      _ -> src

    -- element function: match one element against the pattern, emit
    -- the extended row on success (wildcard fallback when filtering)
    elemLam pat filtering successBody = do
      el <- freshNameM "__el"
      let en = Name el sp
          cases =
            MatchCase pat Nothing successBody sp
              : [MatchCase (PWild sp) Nothing (EListLit [] sp) sp | filtering]
      pure (ELambda Nothing [simpleBinder en] (EMatch (EVar en) cases sp) sp)

    step (vars, pipe) (clause, ann) = case clause of
      S.CFor refut _ pat src _ -> do
        let vars' = vars ++ surfPatVars pat
            filtering = refut || caForceRefut ann
        ef <- elemLam pat filtering (EListLit [rowE vars'] sp)
        f <- perRow vars (cmap ef (wrapSrc (caKind ann) src))
        pure (vars', cmap f pipe)
      S.CLet refut pat mty rhs _ -> do
        let vars' = vars ++ surfPatVars pat
            filtering = refut || caForceRefut ann
            rhs' = maybe rhs (\t -> EAscription rhs t sp) mty
            cases =
              MatchCase pat Nothing (EListLit [rowE vars'] sp) sp
                : [MatchCase (PWild sp) Nothing (EListLit [] sp) sp | filtering]
        f <- perRow vars (EMatch rhs' cases sp)
        pure (vars', cmap f pipe)
      S.CIf cond -> do
        f <- perRow vars (EIf [(cond, EListLit [rowE vars] sp)] (Just (EListLit [] sp)) sp)
        pure (vars, cmap f pipe)
      S.COrderBy keys _ -> do
        -- decorate-sort-undecorate: pair each row with its key tuple,
        -- stably sort on the keys, then drop the decoration (§20.6.1)
        let keyTuple = case keys of
              [(_, k)] -> k
              _ -> ETuple (map snd keys) sp
        deco <- perRow vars (ETuple [keyTuple, rowE vars] sp)
        cmp <- decoCmpLam keys
        und <- undecorateLam
        pure
          ( vars
          , prelApp1 sp "__pipeMap"
              [prelApp1 sp "__sortBy" [prelApp1 sp "__pipeMap" [pipe, deco], cmp], und]
          )
      S.CSkip n _ -> pure (vars, prelApp1 sp "__listDrop" [n, pipe])
      S.CTake n _ -> pure (vars, prelApp1 sp "__listTake" [n, pipe])
      S.CDistinct Nothing _ -> do
        eqLam <- rowEqLam vars
        pure (vars, prelApp1 sp "__distinctBy" [pipe, eqLam])
      S.CDistinct (Just k) _ -> do
        -- decorate with the key, dedupe on it via Eq, undecorate
        deco <- perRow vars (ETuple [k, rowE vars] sp)
        pure (vars, prelApp1 sp "__distinctOnFst" [prelApp1 sp "__pipeMap" [pipe, deco]])
      S.CGroupBy key aggs n _ -> do
        kf <- perRow vars key
        eqLam <- pairEqLam sp
        let groups = prelApp1 sp "__groupBy" [pipe, kf, eqLam]
        g <- freshNameM "__g"
        let gn = Name g sp
            gRows = EDot (EVar gn) (DotName (Name "rows" sp))
        aggItems <- forM aggs $ \(an, ae, mUsing) -> do
          valF <- perRow vars ae
          body <- case mUsing of
            Nothing -> pure (prelApp1 sp "__aggFold" [gRows, valF])
            Just w -> case ctorRefOfExpr w of
              Just cref -> do
                r <- freshNameM "__r"
                x <- freshNameM "__x"
                let rn = Name r sp
                    xn = Name x sp
                    wrapF =
                      ELambda Nothing [simpleBinder rn]
                        (EApp w [ArgExplicit (EApp valF [ArgExplicit (EVar rn)])])
                        sp
                    folded = prelApp1 sp "__aggFold" [gRows, wrapF]
                pure (EMatch folded [MatchCase (PCtor cref [PVar xn] sp) Nothing (EVar xn) sp] sp)
              Nothing -> do
                _ <- unsupported ctx (exprSpan w) "this aggregate 'using' wrapper form"
                pure (prelApp1 sp "__aggFold" [gRows, valF])
          pure (RecItem False an (Just body))
        let rec' =
              ERecordLit
                (RecItem False (Name "key" sp) (Just (EDot (EVar gn) (DotName (Name "key" sp)))) : aggItems)
                sp
            gLam = ELambda Nothing [simpleBinder gn] rec' sp
        pure ([n], prelApp1 sp "__pipeMap" [groups, gLam])
      S.CJoin True pat src cond (Just into) _ -> do
        let vars' = vars ++ [into]
        ef <- elemLamKeep pat cond
        let matches = cmap ef (wrapSrc (caKind ann) src)
            qVal = prelApp1 sp "__queryOfMatches" [matches]
            inner = ELet [LetBind False emptyPrefix (PVar into) Nothing qVal sp] (EListLit [rowE vars'] sp) sp
        f <- perRow vars inner
        pure (vars', cmap f pipe)
      S.CJoin _ pat src cond _ _ -> do
        let vars' = vars ++ surfPatVars pat
        ef <- elemLam pat True (EIf [(cond, EListLit [rowE vars'] sp)] (Just (EListLit [] sp)) sp)
        f <- perRow vars (cmap ef (wrapSrc (caKind ann) src))
        pure (vars', cmap f pipe)

    -- left join: keep the matching element itself (§20.8)
    elemLamKeep pat cond = do
      el <- freshNameM "__el"
      let en = Name el sp
          succBody = EIf [(cond, EListLit [EVar en] sp)] (Just (EListLit [] sp)) sp
          cases =
            [ MatchCase pat Nothing succBody sp
            , MatchCase (PWild sp) Nothing (EListLit [] sp) sp
            ]
      pure (ELambda Nothing [simpleBinder en] (EMatch (EVar en) cases sp) sp)

    -- row equality: componentwise (==) over the row tuple (§20.6.3)
    rowEqLam vars = do
      ra <- freshNameM "__ra"
      rb <- freshNameM "__rb"
      asV <- mapM (const (freshNameM "__qa")) vars
      bsV <- mapM (const (freshNameM "__qb")) vars
      let ran = Name ra sp
          rbn = Name rb sp
          aNames = map (`Name` sp) asV
          bNames = map (`Name` sp) bsV
          eqOne a b = EApp (EOpRef Nothing (Name "==" sp) sp) [ArgExplicit (EVar a), ArgExplicit (EVar b)]
          trueE = EVar (Name "True" sp)
          falseE = EVar (Name "False" sp)
          conj = foldr (\(a, b) acc -> EIf [(eqOne a b, acc)] (Just falseE) sp) trueE (zip aNames bNames)
          body =
            EMatch (EVar ran)
              [MatchCase (rowP aNames) Nothing (EMatch (EVar rbn) [MatchCase (rowP bNames) Nothing conj sp] sp) sp]
              sp
      pure (ELambda Nothing [simpleBinder ran, simpleBinder rbn] body sp)

    -- lexicographic stable comparator over decorated (keys, row)
    -- pairs (§20.6.1); 'desc' swaps the comparison operands
    decoCmpLam keys = do
      ra <- freshNameM "__pa"
      rb <- freshNameM "__pb"
      asV <- mapM (const (freshNameM "__ka")) keys
      bsV <- mapM (const (freshNameM "__kb")) keys
      let ran = Name ra sp
          rbn = Name rb sp
          aNames = map (`Name` sp) asV
          bNames = map (`Name` sp) bsV
          keyP ns = case ns of
            [v] -> PVar v
            vs -> PTuple (map PVar vs) sp
          pairP ns = PTuple [keyP ns, PWild sp] sp
          cmpOne desc a b =
            let (x, y) = if desc then (b, a) else (a, b)
             in prelApp1 sp "compare" [EVar x, EVar y]
          chain [] = prelApp1 sp "compare" [EIntLit 0 Nothing sp, EIntLit 0 Nothing sp]
          chain [(desc, a, b)] = cmpOne desc a b
          chain ((desc, a, b) : restK) =
            EMatch (cmpOne desc a b)
              [ MatchCase (PCtor (CtorRef Nothing (Name "EQ" sp)) [] sp) Nothing (chain restK) sp
              , MatchCase (PVar (Name "__o" sp)) Nothing (EVar (Name "__o" sp)) sp
              ]
              sp
          keyed = [(desc, a, b) | ((desc, _), (a, b)) <- zip keys (zip aNames bNames)]
          body =
            EMatch (EVar ran)
              [ MatchCase (pairP aNames) Nothing
                  (EMatch (EVar rbn) [MatchCase (pairP bNames) Nothing (chain keyed) sp] sp)
                  sp
              ]
              sp
      pure (ELambda Nothing [simpleBinder ran, simpleBinder rbn] body sp)

    -- drop the (keys, row) decoration after sorting
    undecorateLam = do
      p <- freshNameM "__p"
      r <- freshNameM "__r"
      let pn = Name p sp
          rn = Name r sp
      pure $
        ELambda Nothing [simpleBinder pn]
          (EMatch (EVar pn) [MatchCase (PTuple [PWild sp, PVar rn] sp) Nothing (EVar rn) sp] sp)
          sp

-- ── Declarations ─────────────────────────────────────────────────────
