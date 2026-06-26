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
--   * __Soundness/conservatism.__ A non-'Unknown' answer is returned only
--     when it is provably correct. 'Unknown' is always a permitted reply, so
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
  ( InhabitanceSummary (..)
  , InhabitancePurpose (..)
  , InhabEnv (..)
  , HeadClass (..)
  , isEmpty
  , canonicalizeFinite
  , multiplySummaries
  , addSummaries
  , inhabitanceSummary
  ) where

import Data.Set (Set)
import qualified Data.Set as Set
import Kappa.Core (GName, Value (..))

-- | The portable summary lattice of §30.2.7. 'Finite' is kept canonical:
-- @Finite 0@ is normalized to 'Empty', @Finite 1@ to 'Contractible', and the
-- 'Finite' constructor is only ever produced for @n >= 2@ (see
-- 'canonicalizeFinite'). 'Subsingleton' is the only non-exact rung — "at most
-- one inhabitant, not known to be inhabited".
data InhabitanceSummary
  = Empty -- ^ exactly zero inhabitants
  | Subsingleton -- ^ at most one inhabitant (upper bound, not exact)
  | Contractible -- ^ exactly one inhabitant
  | Finite !Int -- ^ exactly @n@ inhabitants, @n >= 2@
  | Unknown -- ^ no portable fact established
  deriving (Eq, Show)

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

-- | The exact-'Empty' test the reachability checks care about. @Finite 0@ never
-- escapes 'canonicalizeFinite', but we match it anyway for total safety.
isEmpty :: InhabitanceSummary -> Bool
isEmpty Empty = True
isEmpty (Finite 0) = True
isEmpty _ = False

-- | Collapse a raw cardinality into the canonical summary: @0@ → 'Empty',
-- @1@ → 'Contractible', @n >= 2@ → @'Finite' n@. Negative inputs cannot arise
-- but are clamped to 'Empty' rather than trusted.
canonicalizeFinite :: Int -> InhabitanceSummary
canonicalizeFinite n
  | n <= 0 = Empty
  | n == 1 = Contractible
  | otherwise = Finite n

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
    -- demanded scrutinee type (§17.1.2). 'Nothing' ⇒ the constructor's result
    -- family arguments do /not/ unify with the target, so this arm is 'Empty'.
    -- @Just fieldTys@ ⇒ unification succeeded and these are the constructor's
    -- retained field types under the branch-local equalities; the arm's summary
    -- is their product. The implementation MUST NOT leak meta solutions or
    -- diagnostics from the speculative unification.
    ieCtorFiber :: Value -> GName -> m (Maybe [Value])
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
    -- scrutinee's family arguments. A constructor whose result type cannot
    -- unify with the demanded target contributes Empty (§17.1.2); otherwise its
    -- arm summary is the product of its retained field-type summaries.
    sumOfCtors :: Set GName -> Value -> [GName] -> m InhabitanceSummary
    sumOfCtors seen scrut ctors = do
      arms <- mapM (armSummary seen scrut) ctors
      pure (foldr addSummaries Empty arms)

    armSummary :: Set GName -> Value -> GName -> m InhabitanceSummary
    armSummary seen scrut c = do
      mfiber <- ieCtorFiber env scrut c
      case mfiber of
        Nothing -> pure Empty -- family-argument unification failed: arm is Empty
        Just fieldTys -> productOf seen fieldTys

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

-- | The product rule of §30.2.7 (closed nondependent products / records).
--
--   * 'Empty' is absorbing: any 'Empty' factor ⇒ 'Empty'.
--   * 'Contractible' is the identity (exact factor 1).
--   * Exact factors multiply; the canonical form keeps @0,1,n@ tidy.
--   * 'Subsingleton' bounds the product at @<= 1@ only while every /other/
--     factor is 'Contractible' (all-Contractible-but-some-Subsingleton ⇒
--     'Subsingleton'). The moment a 'Subsingleton' meets a @Finite n (n>=2)@ or
--     anything 'Unknown', the upper bound is lost and the result is 'Unknown'.
--   * 'Unknown' poisons the product — unless an 'Empty' factor is also present,
--     in which case 'Empty' (the harder fact) wins. The right-fold below
--     handles that because 'Empty' short-circuits regardless of order.
multiplySummaries :: InhabitanceSummary -> InhabitanceSummary -> InhabitanceSummary
multiplySummaries a b = case (a, b) of
  (Empty, _) -> Empty
  (_, Empty) -> Empty
  (Contractible, y) -> y
  (x, Contractible) -> x
  (Subsingleton, Subsingleton) -> Subsingleton
  -- Subsingleton against a >=2 cardinality or anything Unknown loses the bound.
  (Subsingleton, _) -> Unknown
  (_, Subsingleton) -> Unknown
  (Unknown, _) -> Unknown
  (_, Unknown) -> Unknown
  (Finite m, Finite n) -> canonicalizeFinite (m * n)

-- | The sum rule of §30.2.7 (closed sums / variants / data-type arms).
--
--   * 'Empty' arms contribute exact factor 0 (the identity here).
--   * Exact arms add; a single non-'Empty' 'Contractible'/'Subsingleton' arm
--     among 'Empty's keeps its own summary.
--   * Two non-'Empty' arms known only as 'Subsingleton' lose exactness ⇒
--     'Unknown' (no optional strengthening is applied). A 'Subsingleton' summed
--     with any exact @>= 1@ arm likewise drops to 'Unknown'.
--   * 'Unknown' in any arm with no derivable exact total ⇒ 'Unknown'.
addSummaries :: InhabitanceSummary -> InhabitanceSummary -> InhabitanceSummary
addSummaries a b = case (a, b) of
  (Empty, y) -> y
  (x, Empty) -> x
  (Unknown, _) -> Unknown
  (_, Unknown) -> Unknown
  -- Once two non-empty arms are involved, only fully-exact ones combine.
  (Subsingleton, _) -> Unknown
  (_, Subsingleton) -> Unknown
  (Contractible, Contractible) -> Finite 2
  (Contractible, Finite n) -> canonicalizeFinite (1 + n)
  (Finite n, Contractible) -> canonicalizeFinite (n + 1)
  (Finite m, Finite n) -> canonicalizeFinite (m + n)
