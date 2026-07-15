{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

-- | KBackendIR §30.2.7 inhabitance summaries.
--
-- A /conservative/, /terminating/ analysis that classifies how many
-- inhabitants a (normalized, first-order, algebraic) KCore type has. The
-- summary is consumed by source-level reachability checks — @impossible@
-- (§17.1.4), @case impossible@ (§17.1.5), and GADT-refined exhaustiveness
-- (§17.1.1). For those purposes the only load-bearing answer is the exact
-- 'Empty': a branch over a provably-empty fiber is unreachable.
--
-- Two non-negotiable invariants make this safe to trust:
--
--   * __Soundness/conservatism.__ Every returned interval contains the actual
--     inhabitant count. 'Unknown' is always a permitted reply, so
--     anything outside the required structural fragment — functions, recursive
--     or inductive types, open rows, opaque/'Dyn'/foreign — collapses to
--     'Unknown'. Acceptance never depends on an optional strengthening rule.
--
--   * __Termination.__ The walk is structural over the /spelling/ of the type.
--     Recursive constructor occurrences are never unfolded; a data head that
--     reappears within its own analysis short-circuits to 'Unknown'. So even a
--     cyclic family terminates with a safe answer.
--
-- The actual NbE/unification/table plumbing lives behind 'InhabEnv', which the
-- elaborator (@Kappa.Check@) supplies. This module therefore depends only on
-- the value representation and stays free of the @CheckM@ monad, the context,
-- and the metavariable machinery.
module Kappa.Inhabitance
  ( CardinalityBound (..)
  , InhabitanceSummary (Empty, Subsingleton, Contractible, Finite, Unknown)
  , minCount
  , maxCount
  , InhabitancePurpose (..)
  , InhabEnv (..)
  , HeadClass (..)
  , CtorFiber (..)
  , isEmpty
  , canonicalizeFinite
  , multiplySummaries
  , addSummaries
  , inhabitanceSummary
  ) where

import Data.Set (Set)
import qualified Data.Set as Set
import Kappa.Core (GName, Value (..))
import Numeric.Natural (Natural)

-- | A finite upper cardinality bound or the absence of a finite upper bound.
-- 'Unbounded' does not assert a particular infinite cardinality; it says only
-- that this analysis has established no finite maximum.
data CardinalityBound
  = FiniteBound !Natural
  | Unbounded
  deriving (Eq, Ord, Show)

-- | A normalized cardinality interval with a finite lower bound and an optional
-- finite upper bound. The constructor is deliberately hidden: when 'maxCount'
-- is finite, the invariant @minCount <= maxCount@ must hold. 'Natural' keeps
-- exact arithmetic from overflowing into a false exact-zero result. There is
-- intentionally no derived 'Ord': precision is interval containment, not
-- lexicographic field ordering. Accessors are ordinary functions rather than
-- record selectors so the hidden constructor cannot be bypassed by record
-- update syntax.
data InhabitanceSummary = InhabitanceSummary !Natural !CardinalityBound
  deriving (Eq)

minCount :: InhabitanceSummary -> Natural
minCount (InhabitanceSummary lo _) = lo

maxCount :: InhabitanceSummary -> CardinalityBound
maxCount (InhabitanceSummary _ hi) = hi

-- The familiar §30.2.7 names are canonical interval aliases. Keeping them as
-- patterns preserves the proof-oriented vocabulary at use sites without
-- restricting the domain to those five points.
pattern Empty :: InhabitanceSummary
pattern Empty = InhabitanceSummary 0 (FiniteBound 0)

pattern Subsingleton :: InhabitanceSummary
pattern Subsingleton = InhabitanceSummary 0 (FiniteBound 1)

pattern Contractible :: InhabitanceSummary
pattern Contractible = InhabitanceSummary 1 (FiniteBound 1)

pattern Finite :: Natural -> InhabitanceSummary
pattern Finite n <- (exactFiniteAboveOne -> Just n)
  where
    Finite n = canonicalizeFinite n

pattern Unknown :: InhabitanceSummary
pattern Unknown = InhabitanceSummary 0 Unbounded

exactFiniteAboveOne :: InhabitanceSummary -> Maybe Natural
exactFiniteAboveOne (InhabitanceSummary lo (FiniteBound hi))
  | lo == hi && lo >= 2 = Just lo
exactFiniteAboveOne _ = Nothing

instance Show InhabitanceSummary where
  show (InhabitanceSummary 0 (FiniteBound 0)) = "Empty"
  show (InhabitanceSummary 0 (FiniteBound 1)) = "Subsingleton"
  show (InhabitanceSummary 1 (FiniteBound 1)) = "Contractible"
  show (InhabitanceSummary lo (FiniteBound hi))
    | lo == hi = "Finite " ++ show lo
    | otherwise = "Range " ++ show lo ++ " " ++ show hi
  show (InhabitanceSummary 0 Unbounded) = "Unknown"
  show (InhabitanceSummary lo Unbounded) = "Range " ++ show lo ++ " Unbounded"

-- | Why the summary is being computed (§30.2.7). The same source type may
-- receive different answers under different purposes. Only 'SourceReachability'
-- is consumed today; the rest are reserved so the keying is explicit and a
-- future @RuntimeShape@/@Optimization@ view cannot be silently substituted for
-- a source-acceptance decision.
data InhabitancePurpose
  = SourceReachability -- ^ source-level inhabitants: match reachability, @impossible@
  | Completion -- ^ source-level inhabitants for diagnostics / case-split tooling
  | RuntimeShape -- ^ runtime-distinguishable representations after §31.2 erasure
  | Optimization -- ^ backend-independent optimization view
  deriving (Eq, Show)

-- | The exact-'Empty' test the reachability checks care about. A lower bound of
-- zero is not enough: only the singleton interval @[0,0]@ proves unreachable.
isEmpty :: InhabitanceSummary -> Bool
isEmpty Empty = True
isEmpty _ = False

-- | Collapse a raw cardinality into the canonical summary: @0@ → 'Empty',
-- @1@ → 'Contractible', @n >= 2@ → @'Finite' n@. Negative inputs cannot arise
-- because the input is a 'Natural'.
canonicalizeFinite :: Natural -> InhabitanceSummary
canonicalizeFinite n = InhabitanceSummary n (FiniteBound n)

-- | The elaborator-supplied interface. Every monadic effect the analysis needs
-- — normalization, table lookups, and speculative GADT refinement — is routed
-- through here so this module never reaches into @CheckM@.
data InhabEnv m = InhabEnv
  { -- | Reduce a value to weak-head normal form (NbE force, honouring active
    -- refinement facts). The analysis only ever inspects forced heads.
    ieForce :: Value -> m Value
  , -- | Classify a forced 'VGlobN' head. 'Nothing' means "not a closed
    -- algebraic data type I should reason about structurally" (parameterised
    -- abstract types, type families, opaque imports, …) and the caller must
    -- treat the whole type as 'Unknown'. @Just ('IsData' tag ctors)@ exposes a
    -- closed data type's constructor set so sums/finite-enumeration rules fire.
    ieClassifyHead :: Value -> m (Maybe HeadClass)
  , -- | Speculatively refine one constructor of a GADT-style family against the
    -- demanded scrutinee type (§17.1.2). The three-way result distinguishes the
    -- two reasons a constructor's result family arguments can fail to unify:
    --
    --   * @'CtorRefined' fieldTys@ ⇒ unification succeeded; these are the
    --     constructor's retained field types under the branch-local equalities,
    --     and the arm's summary is their product.
    --
    --   * 'CtorContradiction' ⇒ unification failed /and/ the demanded
    --     family-argument index is GROUND (no rigid skolem). This is a genuine
    --     no-confusion contradiction, so this arm is 'Empty'. (e.g. @FF : Tag
    --     False@ against a @Tag True@ scrutinee.)
    --
    --   * 'CtorIndexUnknown' ⇒ unification failed but the demanded index
    --     contains a RIGID/free skolem (e.g. @FF : Tag False@ against an abstract
    --     @Tag b@). The failure only means "this constructor is absent for /this/
    --     instantiation of @b@", not that the arm is empty for /every/
    --     instantiation — so emptiness is 'Unknown', never 'Empty'. Concluding
    --     'Empty' here is the §30.2.7 soundness bug. (Unsolved metavariables in
    --     the index are FINE: unification can still solve them, and a solve is a
    --     reachable inhabitant.)
    --
    -- The implementation MUST NOT leak meta solutions or diagnostics from the
    -- speculative unification.
    ieCtorFiber :: Value -> GName -> m CtorFiber
  , -- | Does the local context carry @IsEmpty t@ evidence for this type?
    ieIsEmptyEvidence :: Value -> m Bool
  , -- | @IsContr t@ evidence.
    ieIsContrEvidence :: Value -> m Bool
  , -- | @IsSubsingleton t@ / @IsProp t@ evidence.
    ieIsSubsingletonEvidence :: Value -> m Bool
  , -- | A no-confusion verdict for a propositional equality type @x = y@.
    -- @Just True@ ⇒ provably 'Empty' (distinct visible constructors, discrete
    -- literals, family-argument contradiction). @Just False@ ⇒ the sides are
    -- definitionally equal /and/ proof/set evidence is available, so the
    -- equality is 'Contractible'. 'Nothing' ⇒ no portable fact ('Unknown').
    -- 'Nothing' when the head is not an equality type at all.
    ieEqualityVerdict :: Value -> m (Maybe Bool)
  }

-- | How 'ieClassifyHead' describes a 'VGlobN' head the analysis may reason
-- about structurally.
data HeadClass
  = -- | A closed algebraic data type: the scrutinee value plus its
    -- constructor list. The scrutinee is threaded back through 'ieCtorFiber'
    -- so each constructor can be refined against /these/ family arguments.
    IsData !Value ![GName]
  deriving (Show)

-- | The three-way verdict of speculatively refining one constructor's result
-- type against the demanded scrutinee index (see 'ieCtorFiber'). The split
-- between 'CtorContradiction' (ground index, genuinely empty arm) and
-- 'CtorIndexUnknown' (rigid index, emptiness undecidable) is what keeps
-- §30.2.7 sound under abstract/free GADT indices.
data CtorFiber
  = -- | Unification succeeded; the constructor's retained field types.
    CtorRefined ![Value]
  | -- | Unification failed against a GROUND demanded index: a real no-confusion
    -- contradiction, so this arm is 'Empty'.
    CtorContradiction
  | -- | Unification failed but the demanded index carries a rigid/free skolem:
    -- the arm is present for /some/ instantiation, so emptiness is 'Unknown'.
    CtorIndexUnknown

-- | Compute the §30.2.7 inhabitance summary of a (already context-aware) type.
--
-- The 'Set' of 'GName's is the in-progress data-head guard: a head already on
-- the stack is a recursive occurrence and yields 'Unknown' without unfolding,
-- which is what guarantees termination on inductive types like @Nat@/@List@.
--
-- Only 'SourceReachability' is implemented; every other purpose conservatively
-- answers 'Unknown' (it is always safe, and source acceptance must never lean
-- on a runtime-shape summary).
inhabitanceSummary
  :: forall m
   . Monad m
  => InhabEnv m
  -> InhabitancePurpose
  -> Value
  -> m InhabitanceSummary
inhabitanceSummary env purpose ty0
  | purpose /= SourceReachability = pure Unknown
  | otherwise = go Set.empty ty0
  where
    go :: Set GName -> Value -> m InhabitanceSummary
    go seen ty = do
      t <- ieForce env ty
      case t of
        -- Records / closed nondependent products: exact multiplication.
        VRecordT fields -> productOf seen (map snd fields)
        -- Closed `Variant` rows: exact addition over the member types.
        VVariantT members -> sumOf seen members
        -- A nominal data head. First consult the no-confusion / evidence rules
        -- that key on the type as a whole, then fall through to the structural
        -- data-type analysis.
        VGlobN g _ -> do
          mverdict <- ieEqualityVerdict env t
          case mverdict of
            Just True -> pure Empty
            Just False -> pure Contractible
            Nothing -> do
              evid <- classifyByEvidence env t
              case evid of
                Just s -> pure s
                Nothing -> dataHead seen g t
        _ -> do
          -- Not a structural-fragment head: still admit proof-classification
          -- evidence (IsEmpty/IsContr/IsSubsingleton) keyed on the type, then
          -- conservatively give up.
          evid <- classifyByEvidence env t
          pure (maybe Unknown id evid)

    -- A nominal data type. Guard against recursive unfolding, then summarise as
    -- a closed sum over its constructors with per-constructor GADT refinement.
    dataHead :: Set GName -> GName -> Value -> m InhabitanceSummary
    dataHead seen g scrutTy
      | g `Set.member` seen = pure Unknown -- recursive occurrence: do not unfold
      | otherwise = do
          mcls <- ieClassifyHead env scrutTy
          case mcls of
            Nothing -> pure Unknown -- not a closed data type I can reason about
            Just (IsData scrut ctors) ->
              sumOfCtors (Set.insert g seen) scrut ctors

    -- Exact product of component summaries (records / nondependent tuples).
    -- Any Empty component ⇒ Empty (the absorbing element); see
    -- 'multiplySummaries'.
    productOf :: Set GName -> [Value] -> m InhabitanceSummary
    productOf seen comps = do
      ss <- mapM (go seen) comps
      pure (foldr multiplySummaries Contractible ss)

    -- Exact sum over closed variant member types (no GADT refinement: a bare
    -- `Variant` row has no family arguments to contradict).
    sumOf :: Set GName -> [Value] -> m InhabitanceSummary
    sumOf seen members = do
      ss <- mapM (go seen) members
      pure (foldr addSummaries Empty ss)

    -- Exact sum over a data type's constructor arms, each refined against the
    -- scrutinee's family arguments. A constructor whose result type cannot unify
    -- with a GROUND demanded target contributes Empty (§17.1.2); against an
    -- abstract (rigid-indexed) target a unify-failure is Unknown, which makes the
    -- whole sum Unknown — the sound answer for @Tag b@ and friends. Otherwise the
    -- arm summary is the product of its retained field-type summaries.
    sumOfCtors :: Set GName -> Value -> [GName] -> m InhabitanceSummary
    sumOfCtors seen scrut ctors = do
      arms <- mapM (armSummary seen scrut) ctors
      pure (foldr addSummaries Empty arms)

    armSummary :: Set GName -> Value -> GName -> m InhabitanceSummary
    armSummary seen scrut c = do
      fiber <- ieCtorFiber env scrut c
      case fiber of
        CtorRefined fieldTys -> productOf seen fieldTys
        CtorContradiction -> pure Empty -- ground-index no-confusion: arm is Empty
        CtorIndexUnknown -> pure Unknown -- rigid index: emptiness undecidable

-- | Proof-classification evidence (§30.2.7). Precedence is exact-over-bound:
-- 'IsEmpty' and 'IsContr' win over 'IsSubsingleton'. 'Nothing' means no
-- evidence applied (the caller continues structurally).
classifyByEvidence :: Monad m => InhabEnv m -> Value -> m (Maybe InhabitanceSummary)
classifyByEvidence env t = do
  emptyE <- ieIsEmptyEvidence env t
  if emptyE
    then pure (Just Empty)
    else do
      contrE <- ieIsContrEvidence env t
      if contrE
        then pure (Just Contractible)
        else do
          subE <- ieIsSubsingletonEvidence env t
          pure (if subE then Just Subsingleton else Nothing)

-- | Interval product for closed nondependent products / records (§30.2.7).
-- Cardinalities are nonnegative, so multiplication is monotone at both bounds.
-- Exact zero remains absorbing even against an unbounded interval.
multiplySummaries :: InhabitanceSummary -> InhabitanceSummary -> InhabitanceSummary
multiplySummaries (InhabitanceSummary loA hiA) (InhabitanceSummary loB hiB) =
  InhabitanceSummary (loA * loB) (multiplyUpper hiA hiB)
  where
    multiplyUpper (FiniteBound 0) _ = FiniteBound 0
    multiplyUpper _ (FiniteBound 0) = FiniteBound 0
    multiplyUpper (FiniteBound a) (FiniteBound b) = FiniteBound (a * b)
    multiplyUpper Unbounded _ = Unbounded
    multiplyUpper _ Unbounded = Unbounded

-- | Interval sum for closed sums / variants / data-type arms (§30.2.7).
-- Lower and upper bounds add independently. In particular, two subsingleton
-- arms retain @[0,2]@ and adding an exact inhabited arm to 'Unknown' retains
-- the established positive lower bound.
addSummaries :: InhabitanceSummary -> InhabitanceSummary -> InhabitanceSummary
addSummaries (InhabitanceSummary loA hiA) (InhabitanceSummary loB hiB) =
  InhabitanceSummary (loA + loB) (addUpper hiA hiB)
  where
    addUpper (FiniteBound a) (FiniteBound b) = FiniteBound (a + b)
    addUpper Unbounded _ = Unbounded
    addUpper _ Unbounded = Unbounded
