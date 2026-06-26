-- | KBackendIR Stage 2: the shared compile-time representation/layout table.
--
-- This module is the SINGLE source of truth for how a value head is
-- represented at runtime — the reasoning the C and LLVM backends used to
-- duplicate, each approximating it with its own ad-hoc scalar-kind and
-- tag-id logic.  Centralizing it here means the two backends agree BY
-- CONSTRUCTION rather than by parallel hand-maintenance: a tag-id divergence
-- between them is a latent miscompile (a value built on one backend would be
-- matched with the wrong id on the other), and that whole class of bug is
-- eliminated once both consult the same function.
--
-- DESIGN CONSTRAINT (do not violate): this is a TABLE of pure functions, NOT
-- per-IR-node decoration.  Nothing here hangs a @rep@ field on an expression
-- node; the backends CONSULT these functions at the point they need a
-- representation decision.  The module is pure (no @IO@, no codegen monad) so
-- the Stage-3 legality verifier (§34.3.3) and the Stage-4 niche/coercion pass
-- can consume the SAME table the backends emit against.
--
-- What it currently centralizes:
--
--   * 'tagId' / 'assignUserCtorTags' — the constructor → numeric tag-id
--     authority.  Builtins take their fixed @KCT_*@ ids from "Kappa.Builtins";
--     user constructors are numbered @KCT_USER_BASE + i@ over the
--     gKey-sorted set.  Both backends previously open-coded this numbering
--     (C in @tagEnumBlock@, LLVM in @hostCtorTags@); now both consult here.
--   * 'ctorLayout' / 'CtorLayout' — the STATIC per-constructor shape: a
--     nullary ctor is the canonical @b010@ immediate (the proven runtime
--     decision in @kctor@); a ctor all of whose fields are statically
--     immediate-typed MAY pack into a @b011@ word; everything else is boxed.
--     The runtime @kctor@ makes the final PER-VALUE packing call; this table
--     records the static classification the backends and Stage 3/4 consume.
--   * 'scalarRep' / 'Rep' — the int/float/bool/boxed marshalling
--     classification a value head can take, generalizing the C backend's
--     @scalarHeadKindV@ head-type discriminator.
--
-- See the module note in "Kappa.Backend.C" (LR2 §244) and the Milestone-C
-- note in "Kappa.Backend.LLVM" for the two-bucket tag-id rule this enforces.
module Kappa.Backend.Repr
  ( -- * Runtime representation classes
    Rep (..)
  , scalarRep
  , scalarRepName

    -- * Static constructor layout
  , CtorLayout (..)
  , ctorLayout
  , ctorLayoutByArity

    -- * Constructor tag ids (the single authority)
  , tagId
  , isBuiltinCtor
  , assignUserCtorTags
  , userCtorTagOf
  ) where

import Data.List (sort)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Kappa.Builtins (builtinCtorTagId, kctUserBase)
import Kappa.Core (GName, Value (..), gKey)

-- ── Runtime representation classes ───────────────────────────────────
--
-- 'Rep' is the union of runtime representations a value HEAD can take.  It
-- generalizes the C backend's 'Kappa.Backend.C.ScalarKind' (which only knew
-- @KInt64@/@KDouble@) into the full set the unboxing roadmap distinguishes,
-- so Stage 3/4 and both backends name the same classes.  The C backend's
-- scalar-worker optimization consumes the 'RepInt'/'RepDouble' cases (the
-- only ones it currently unboxes); 'RepBoxed' is the uniform @KValue *@
-- fallback every other head takes today.

-- | The runtime representation class of a value head.
--
--   * 'RepBoxed'   — a uniform heap-or-immediate @KValue *@ pointer word: the
--                    default for anything not specially unboxed (records,
--                    ADTs, closures, strings, …).
--   * 'RepInt'     — an unboxed 64-bit signed integer (@Int@/@Nat@/@Integer@
--                    in the small-immediate range; the C backend's @KInt64@).
--   * 'RepDouble'  — an unboxed IEEE-754 double (@Float@/@Double@; the C
--                    backend's @KDouble@).
--   * 'RepImmCtor' — a nullary constructor packed as the canonical @b010@
--                    immediate carrying its tag id (Bool, Unit, Nil, None, and
--                    every nullary user enum variant).  This is the
--                    representation a 'LayoutImmediate' ctor takes.
data Rep
  = RepBoxed
  | RepInt
  | RepDouble
  | RepImmCtor
  deriving stock (Eq, Show)

-- | The runtime representation of a value of the given (whnf) head type, or
-- 'RepBoxed' for anything not specially unboxed.  This is the pure core the C
-- backend's @scalarHeadKindV@ wraps: a head whose type constructor is one of
-- the primitive numeric types is unboxed; everything else stays boxed.
--
-- It matches ONLY the bare, fully-applied primitive type heads
-- (@VGlobN T []@) the runtime gives a dedicated immediate encoding.  A type
-- with arguments (@List Int@, @Option a@) or any other head is 'RepBoxed' —
-- exactly the conservative classification @scalarHeadKindV@ made, so the
-- existing scalar-worker eligibility is unchanged.
scalarRep :: Value -> Rep
scalarRep = \case
  VGlobN g [] -> scalarRepName (gKey g)
  _ -> RepBoxed

-- | The representation a primitive type NAME (its 'gKey') denotes, by spelling.
-- Factored out so a caller that already has the name (not a 'Value') can
-- consult the same table.  The name set mirrors the C backend's historical
-- @scalarHeadKindV@ exactly: @Int@/@Nat@/@Integer@ are int-represented,
-- @Float@/@Double@ are double-represented, everything else is boxed.
--
-- NOTE: the @gKey@ of a bare prelude type head is its short spelling (e.g.
-- @"Int"@), matching how @scalarHeadKindV@ pattern-matched on the @GName@'s
-- text; this preserves byte-identical behaviour.
scalarRepName :: Text -> Rep
scalarRepName nm
  | nm `elem` ["Int", "Nat", "Integer"] = RepInt
  | nm `elem` ["Float", "Double"] = RepDouble
  | otherwise = RepBoxed

-- ── Static constructor layout ────────────────────────────────────────
--
-- 'CtorLayout' is the STATIC, compile-time-knowable shape of a constructor —
-- the classification the runtime's @kctor@ (runtime/kappart.c) seeds its
-- per-value packing from.  The runtime makes the FINAL per-VALUE call (a
-- single-field ctor packs to @b011@ only if THAT value's field is itself a
-- fitting immediate); this table records what the backends and the Stage-3/4
-- passes can know statically, before any value exists.

-- | The static layout class of a constructor.
--
--   * 'LayoutImmediate' — a NULLARY ctor.  @kctor@ ALWAYS encodes it as the
--     canonical @b010@ immediate carrying its tag id (no heap box, ever): a
--     proven, value-independent decision.  Both backends already emit
--     @kctor0@ (vs @kctor@) for exactly this case; 'LayoutImmediate' is that
--     decision lifted to the compile-time table.
--   * 'LayoutMayPack' — a ctor (arity 1 or 2 today) ALL of whose fields are
--     statically immediate-typed, so it is a CANDIDATE for the runtime's
--     @b011@ packed encoding.  "May", not "will": @kctor@ still checks each
--     actual field value fits the per-slot immediate budget and otherwise
--     boxes.  The static type tells the backends/Stage-4 it is a packing
--     candidate; the runtime decides per value.
--   * 'LayoutBoxed' — every other ctor: a boxed @K_CTOR@ with heap-stored
--     fields.
data CtorLayout
  = LayoutImmediate
  | LayoutMayPack
  | LayoutBoxed
  deriving stock (Eq, Show)

-- | The static layout of a constructor given its field-type representations.
-- A nullary ctor is the canonical @b010@ immediate; a 1- or 2-field ctor whose
-- fields are ALL immediate-typed (int/double/immediate-ctor — i.e. not
-- 'RepBoxed') is a @b011@ packing candidate; otherwise boxed.
--
-- The per-field 'Rep' list is the field types' representations IN ORDER (the
-- caller computes them via 'scalarRep' on each field's head type); its LENGTH
-- is the constructor's runtime arity.  The arity bound (≤ 2) and the
-- "all fields immediate" gate mirror @kctor@'s @argc == 1@ / @argc == 2@
-- packing paths (runtime/kappart.c, UNBOXING Stage 1d/1e).
ctorLayout :: [Rep] -> CtorLayout
ctorLayout fieldReps = case fieldReps of
  [] -> LayoutImmediate
  _
    | length fieldReps <= 2 && all immediateRep fieldReps -> LayoutMayPack
    | otherwise -> LayoutBoxed
  where
    immediateRep r = r /= RepBoxed

-- | The static layout knowable from ARITY ALONE — the slice both backends act
-- on today.  Only the nullary ⇒ 'LayoutImmediate' decision is arity-pure (it
-- needs no field types); any positive arity is reported 'LayoutBoxed' here
-- because deciding @b011@-packability requires the field types ('ctorLayout').
-- This is the function the @kctor0@-vs-@kctor@ call-shape choice in both
-- backends corresponds to.
ctorLayoutByArity :: Int -> CtorLayout
ctorLayoutByArity 0 = LayoutImmediate
ctorLayoutByArity _ = LayoutBoxed

-- ── Constructor tag ids (the single authority) ───────────────────────
--
-- A constructor value carries a small integer tag id; a @match@ dispatches on
-- an int compare.  The id MUST be identical at every construction and every
-- match site for a given ctor, ACROSS backends — a divergence is a silent
-- miscompile.  This is the single authority both backends consult:
--
--   * a BUILTIN ctor (the runtime-built set: Bool/Unit/list/Option/__rat and
--     the §18 effect/outcome ctors) takes its FIXED @KCT_*@ id from
--     'Kappa.Builtins.builtinCtorTagId' — load-bearing for cross-backend value
--     flow (e.g. every comparison prim builds its Bool via the runtime's
--     @kbool@, tagged @KCT_TRUE@/@KCT_FALSE@; a match only fires if both
--     backends' True/False ids equal the runtime's).
--   * a USER ctor takes @KCT_USER_BASE + i@, where @i@ is its index in the
--     gKey-SORTED set of all user ctors in the program ('assignUserCtorTags').

-- | Is this a runtime-built BUILTIN constructor (fixed @KCT_*@ id) rather than
-- a codegen-numbered user constructor?
isBuiltinCtor :: GName -> Bool
isBuiltinCtor g = case builtinCtorTagId (gKey g) of
  Just _ -> True
  Nothing -> False

-- | Assign every USER constructor in the given gKey set a @KCT_USER_BASE + i@
-- tag id, numbering by the SORTED gKeys so the result is deterministic and
-- identical across backends (and across runs).  The input is the set of user
-- ctor gKeys a program references; builtins must already be excluded by the
-- caller (they keep their fixed ids and are never numbered here).
--
-- This is THE user-ctor numbering scheme.  The C backend's @tagEnumBlock@
-- (which emits @KT_<mangle> = KCT_USER_BASE + i@) and the LLVM backend's
-- @hostCtorTags@ (which builds a @gKey -> i32 id@ map) both previously
-- open-coded @sort@ + @zip [kctUserBase ..]@; both now derive the SAME id map
-- from this function, so they agree on every id by construction.
assignUserCtorTags :: [Text] -> Map Text Int
assignUserCtorTags userKeys =
  Map.fromList (zip (sort userKeys) [kctUserBase ..])

-- | The numeric tag id of a USER constructor, looked up in a map produced by
-- 'assignUserCtorTags'.  A user ctor missing from the map (an internal bug —
-- the map should cover every referenced user ctor) defaults to 'kctUserBase':
-- a clean non-match at worst, never a silent collision with a builtin id.
userCtorTagOf :: Map Text Int -> GName -> Int
userCtorTagOf tags g = Map.findWithDefault kctUserBase (gKey g) tags

-- | The numeric tag id of ANY constructor: the fixed builtin id if it is a
-- runtime-built builtin, else its 'assignUserCtorTags' user id (looked up in
-- the supplied map).  This is the one resolver both backends route through, so
-- the C backend's symbolic @KCT_*@/@KT_*@ names and the LLVM backend's literal
-- @i32@ both resolve to identical numbers.
tagId :: Map Text Int -> GName -> Int
tagId userTags g = case builtinCtorTagId (gKey g) of
  Just i -> i
  Nothing -> userCtorTagOf userTags g
