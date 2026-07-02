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
--   * 'repSelect' — KBackendIR Stage 3: the SINGLE authority that, given a
--     function's elaborated type, yields the per-parameter + result 'Rep' plan a
--     scalar/unboxed worker is built against.  The C backend's @typeScalarKinds@
--     used to recompute this (walking the Pi telescope and re-running the
--     head-type rep classification inline); it now DERIVES its
--     @ParamKind@/@ScalarKind@ from this one function, so the rep verdict has a
--     single source the backends and the §34.3.3 verifier share.
--
-- See the module note in "Kappa.Backend.C" (LR2 §244) and the Milestone-C
-- note in "Kappa.Backend.LLVM" for the two-bucket tag-id rule this enforces.
module Kappa.Backend.Repr
  ( -- * Runtime representation classes
    Rep (..)
  , scalarRep

    -- * Function rep/worker-plan selection (the single authority)
  , repSelect
  , runtimeParamMask

    -- * S1.5 owned/borrowed calling convention (telescope-derived; observe-only)
  , ArgConv (..)
  , argConvSelect
  , argConvSelectGlobal
  , argConvGlobalType

    -- * Static constructor layout
  , CtorLayout (..)
  , ctorLayout
  , ctorLayoutByArity

    -- * S1.3 ctor layout authority (observe-only; consumed by S5 FBIP reuse)
  , CtorLayoutInfo (..)
  , ctorLayoutOf

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
import Kappa.Builtins (builtinCtorTagId, gPrel, kctUserBase, prelDouble, prelInt, prelInteger, prelNat, primModule)
import Kappa.Core
  ( CaseAlt (..)
  , Closure (..)
  , CorePat (..)
  , GName (..)
  , Icit (..)
  , Q (..)
  , Term (..)
  , Value (..)
  , gKey
  )
import Kappa.Eval (EvalCtx (..), GlobalDef (..), Globals (..), eval, force, quote)

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
-- It matches ONLY a bare, fully-applied primitive type head (@VGlobN T []@); a
-- type with arguments (@List Int@, @Option a@) or any other head is 'RepBoxed' —
-- the conservative classification @scalarHeadKindV@ made, so the existing
-- scalar-worker eligibility is unchanged.
scalarRep :: Value -> Rep
scalarRep = \case
  VGlobN g [] | Just r <- primScalarRep g -> r
  _ -> RepBoxed

-- | The scalar representation of a primitive type's DECLARATION-SYMBOL IDENTITY.
--
-- Spec §1.2 (\"Typed compiler artifacts, not stringly-typed compilation\"):
-- after @BODY_RESOLVE@, \"every resolved reference MUST target a declaration
-- symbol, semantic object identity, … It MUST NOT target a spelling string.\"
-- So this classifies by 'GName' EQUALITY against the canonical prelude type
-- globals — which compares the MODULE-QUALIFIED identity — never by surface
-- name.  A user type named @Double@ declared in another module is a different
-- 'GName' and correctly stays 'RepBoxed'; the bare-name match this replaced
-- would have mis-unboxed it (and an earlier 'gKey' spelling match dropped the
-- workers entirely — both were spelling-string keys this avoids).
primScalarRep :: GName -> Maybe Rep
primScalarRep g
  | g `elem` intIds = Just RepInt
  | g `elem` dblIds = Just RepDouble
  | otherwise = Nothing
  where
    intIds = [prelInt, prelNat, prelInteger]
    -- @Float@ is the transparent prelude alias @type Float = Double@; the
    -- elaborator unfolds it to @Double@ before this point, so 'prelDouble'
    -- normally suffices — matching the alias identity too is robust and free.
    dblIds = [prelDouble, gPrel "Float"]

-- ── Function rep / worker-plan selection (the single authority) ───────
--
-- 'repSelect' is the ONE authority that, given a function's elaborated type,
-- yields the rep PLAN a scalar/unboxed worker would be built against: the
-- 'Rep' of every RUNTIME-RELEVANT explicit parameter (in telescope order) plus
-- the 'Rep' of the result.  The C backend's @typeScalarKinds@ used to recompute
-- this — walking the same Pi telescope and re-running the head-type rep
-- classification ('scalarRep', via @scalarHeadKindV@) inline — so the
-- int/double/boxed verdict lived in two places.  Now the backend DERIVES its
-- @[ParamKind]@/@ScalarKind@ from this single 'Rep' plan, and the §34.3.3
-- verifier and the LLVM backend can consult the SAME function.
--
-- It does rep SELECTION only — no worker-emission policy.  Whether a 'RepInt'
-- param actually becomes an unboxed slot, what the worker is named, the
-- @kunbox_*@/overflow escape, the C/LLVM string emission: all of that stays in
-- the backends.  This decides ONLY which type heads are int/double/boxed.

-- | Walk a function's (whnf-forced) type telescope and return the rep plan:
-- @(perParamReps, resultRep)@, where @perParamReps@ lists the 'scalarRep' of
-- every EXPLICIT, RUNTIME-RELEVANT parameter domain in telescope order, and
-- @resultRep@ is the 'scalarRep' of the final (non-Pi) result head.
--
-- Implicit binders, 'Q0'-erased binders, and explicit kind-domain binders
-- (@Type@, @Type -> Type@, …) are skipped: they have no runtime argument slot
-- and a scalar worker must never read one. This exactly mirrors the
-- owned/borrowed convention walk below and the ownership pass's
-- @erasedOrKind@ zipper.
--
-- @Nothing@ is returned for a telescope whose codomain closure references a
-- variable beyond its own environment (@closureHasBoundEnv@ fails) — a shape the
-- rep walk cannot soundly instantiate; the backend treats that as ineligible
-- (→ boxed-only), never a miscompile.  The 'EvalCtx' is needed to 'force' and
-- to instantiate each Pi codomain under a fresh rigid variable.
repSelect :: EvalCtx -> Value -> Maybe ([Rep], Rep)
repSelect ctx = walk 0 []
  where
    walk lvl acc ty =
      case force ctx ty of
        VPi ic q _ _ dom clo@(Closure env body) ->
          if not (closureHasBoundEnv env body)
            then Nothing
            else
              let x = VRigid lvl []
                  cod = closApplyV x clo
                  acc' =
                    if runtimeRelevantParam ctx lvl ic q dom
                      then scalarRep dom : acc
                      else acc
               in walk (lvl + 1) acc' cod
        other -> Just (reverse acc, scalarRep other)
    closApplyV v (Closure env body) = eval ctx (v : env) body
    -- The codomain closure may reference only variables BOUND in its own
    -- environment plus the binder just introduced; a reference beyond that is a
    -- shape this static walk cannot instantiate, so the whole plan is rejected.
    closureHasBoundEnv env body = maxVar body < length env + 1

-- | The same telescope walk as 'repSelect', but retaining one Boolean per Pi
-- binder in source order. Backends that still see a leading Core lambda for a
-- static/kind-domain parameter use this mask to drop that binder from optimized
-- runtime ABIs while preserving de-Bruijn alignment in the body.
runtimeParamMask :: EvalCtx -> Value -> Maybe [Bool]
runtimeParamMask ctx = walk 0 []
  where
    walk lvl acc ty =
      case force ctx ty of
        VPi ic q _ _ dom (Closure env body) ->
          if not (closureHasBoundEnv env body)
            then Nothing
            else
              let x = VRigid lvl []
                  cod = eval ctx (x : env) body
               in walk (lvl + 1) (runtimeRelevantParam ctx lvl ic q dom : acc) cod
        _ -> Just (reverse acc)
    closureHasBoundEnv env body = maxVar body < length env + 1

-- ── S1.5 owned/borrowed calling convention (telescope-derived) ────────
--
-- Perceus's dup/drop pass (PERCEUS-RC-DESIGN §3, stage S2) reads the
-- owned/borrowed PARAMETER convention at each 'Kappa.Core.CApp': it is already
-- in the IR (the callee's 'CPi'\/'VPi' telescope carries each binder's quantity
-- 'Q' and borrow marker 'Bool'), so the convention needs NO new metadata — only
-- a backend that ACTS on what is already there (PERCEUS-S1-PLAN finding 2 / (d)).
-- This is the accessor that surfaces it, mirroring 'repSelect' (same telescope
-- walk, same implicit\/'Q0' skip rules) so the rep PLAN and the ownership PLAN
-- agree argument-for-argument.
--
-- __Observe-only in S1__: a future S2 consumes it to decide, per argument,
-- whether the caller transfers ownership (no post-call drop) or retains it; no
-- current codegen reads it, so call shapes are byte-identical. The S1.5 deliverable
-- is the debug assert (test\/lint path) that every call site CAN classify each
-- argument — i.e. 'argConvSelect' yields a verdict for every runtime arg.

-- | The owned\/borrowed convention of one runtime argument position, per
-- Perceus's parameter convention (PERCEUS-RC-DESIGN §3).
data ArgConv
  = -- | An OWNED parameter (declared @1@\/@≥1@): the callee CONSUMES it (drops
    -- or reuses its storage), so the caller TRANSFERS ownership and emits no
    -- post-call drop. The §12.2.6 non-droppable quantities.
    ArgOwned
  | -- | A BORROWED (@&@) parameter: the callee reads (and may @dup@) but NEVER
    -- drops it; the CALLER retains ownership across the call. The borrow marker
    -- on the 'CPi'\/'VPi' binder.
    ArgBorrowed
  | -- | A SHARED parameter (declared @ω@\/@≤1@, non-borrowed): a duplicable\/
    -- droppable value the callee may @dup@ or @drop@ freely; the caller passes a
    -- shareable reference. (S1.4's §3a refinement may TIGHTEN such a parameter
    -- to effectively 'ArgOwned' within a statically-linked unit, but the
    -- declared convention surfaced here stays 'ArgShared' — the contract at any
    -- separately-compilable boundary.)
    ArgShared
  deriving stock (Eq, Show)

-- | Walk a callee's (whnf-forced) type telescope and return the owned\/borrowed
-- 'ArgConv' of every EXPLICIT runtime-relevant parameter, in telescope order —
-- exactly the positions 'repSelect' returns a 'Rep' for, so the two zip
-- argument-for-argument. The borrow marker takes precedence (a borrowed
-- parameter is 'ArgBorrowed' regardless of its quantity); otherwise the
-- quantity decides owned (@1@\/@≥1@) vs shared (@ω@\/@≤1@). Implicit binders,
-- 'Q0'-erased binders, and explicit kind-domain binders carry no runtime
-- argument and are skipped.
--
-- @Nothing@ is returned for the same unwalkable-codomain shape 'repSelect'
-- rejects (a codomain closure escaping its environment) — the caller then has no
-- per-arg convention and (in S2) must fall back to the conservative
-- treat-as-shared default, never a miscompile.
argConvSelect :: EvalCtx -> Value -> Maybe [ArgConv]
argConvSelect ctx = walk 0 []
  where
    walk lvl acc ty =
      case force ctx ty of
        VPi ic q borrowed _ dom (Closure env body) ->
          if not (closureHasBoundEnv env body)
            then Nothing
            else
              let x = VRigid lvl []
                  cod = eval ctx (x : env) body
                  acc' =
                    if runtimeRelevantParam ctx lvl ic q dom
                      then argConv q borrowed : acc
                      else acc
               in walk (lvl + 1) acc' cod
        _ -> Just (reverse acc)
    closureHasBoundEnv env body = maxVar body < length env + 1

-- | Like 'argConvSelect', but with the S2.3c primitive convention override.
--
-- Primitive declarations use unrestricted surface arrows because the source
-- language does not expose runtime ownership transfer at primitive boundaries.
-- Perceus needs the lower-level convention: confirmed runtime-cell publishers
-- take ownership of the published value; confirmed read-only cell/container
-- operations borrow their handles and indices. This function keys the override
-- from the resolved primitive identity: either a @primModule@ global or the
-- canonical 'VPrim' identity stored in the prelude 'GlobalDef'. It does not
-- inspect source spellings or user globals.
--
-- An override whose arity no longer matches the walked telescope returns
-- 'Nothing'. The S1.5 verifier treats that as a hard drift finding, so adding
-- a primitive argument cannot silently inherit a stale convention.
argConvSelectGlobal :: EvalCtx -> GName -> Maybe [ArgConv]
argConvSelectGlobal ctx g =
  case primitiveGlobalDef (globalsMap (ecGlobals ctx)) g of
    Nothing -> Nothing
    Just gd ->
      let base = argConvSelect ctx (gdType gd)
       in case primitiveIdentity g gd >>= primArgConvOverride of
            Nothing -> base
            Just convs -> do
              walked <- base
              if length convs == length walked then Just convs else Nothing

argConvGlobalType :: EvalCtx -> GName -> Maybe Value
argConvGlobalType ctx g = gdType <$> primitiveGlobalDef (globalsMap (ecGlobals ctx)) g

primitiveGlobalDef :: Map GName GlobalDef -> GName -> Maybe GlobalDef
primitiveGlobalDef globals g@(GName m nm) =
  case Map.lookup g globals of
    Just gd -> Just gd
    Nothing
      | m == primModule -> Map.lookup (gPrel nm) globals
      | otherwise -> Nothing

primitiveIdentity :: GName -> GlobalDef -> Maybe Text
primitiveIdentity (GName m nm) gd
  | m == primModule = Just nm
  | Just (VPrim p _) <- gdValue gd = Just p
  | otherwise = Nothing

-- | S2.3c audited primitive convention table.
--
-- 'ArgOwned' appears only at positions that publish the argument into a
-- runtime-owned cell/container on the operation's semantic execution path.
-- 'ArgBorrowed' appears for confirmed read-only handles, indices, memory-order
-- codes, and compare operands. 'ArgShared' is deliberately retained for
-- arguments whose ownership is tied to action-node/result transfer rather than
-- this cell-publishing boundary; those remain conservative until result/action
-- ownership is modeled.
primArgConvOverride :: Text -> Maybe [ArgConv]
primArgConvOverride p = Map.lookup p primArgConvOverrides

primArgConvOverrides :: Map Text [ArgConv]
primArgConvOverrides =
  Map.fromList
    [ ("__ioNewRef", [owned])
    , ("__ioReadRef", [borrowed])
    , ("__ioWriteRef", [borrowed, owned])
    , ("__newArray", [borrowed, owned])
    , ("__arrayRead", [borrowed, borrowed])
    , ("__arrayWrite", [borrowed, borrowed, owned])
    , ("__arrayLen", [borrowed])
    , ("newTVar", [owned])
    , ("readTVar", [borrowed])
    , ("writeTVar", [borrowed, owned])
    , ("__newAtomicRef", [owned])
    , ("__atomicLoad", [borrowed, borrowed])
    , ("__atomicStore", [borrowed, borrowed, owned])
    , ("__atomicExchange", [borrowed, borrowed, owned])
    , ("__atomicCompareExchange", [borrowed, borrowed, borrowed, borrowed, owned])
    , ("__atomicFetchAdd", [borrowed, borrowed, borrowed])
    , ("__atomicFetchSub", [borrowed, borrowed, borrowed])
    , ("__atomicFetchAnd", [borrowed, borrowed, borrowed])
    , ("__atomicFetchOr", [borrowed, borrowed, borrowed])
    , ("__atomicFetchXor", [borrowed, borrowed, borrowed])
    , ("newFiberRef", [owned])
    , ("getFiberRef", [borrowed])
    , ("setFiberRef", [borrowed, owned])
    , ("modifyFiberRef", [borrowed, shared])
    , ("locallyFiberRef", [borrowed, owned, shared])
    , ("completePromise", [borrowed, owned])
    , ("awaitPromiseExit", [borrowed])
    , ("pollPromise", [borrowed])
    , ("isDonePromise", [borrowed])
    ]
  where
    owned = ArgOwned
    borrowed = ArgBorrowed
    shared = ArgShared

-- | The owned\/borrowed verdict for one explicit runtime parameter from its
-- declared quantity and borrow marker. Borrow wins; then quantity: @1@\/@≥1@ are
-- owned (non-droppable, must be consumed — §12.2.6), @ω@\/@≤1@ are shared
-- (droppable). @0@ never reaches here (it is skipped as a non-runtime binder).
argConv :: Q -> Bool -> ArgConv
argConv q borrowed
  | borrowed = ArgBorrowed
  | otherwise = case q of
      Q1 -> ArgOwned
      QGe1 -> ArgOwned
      QW -> ArgShared
      QLe1 -> ArgShared
      Q0 -> ArgShared -- unreachable (Q0 is skipped); shared is the safe default

-- | The shared runtime-argument filter for representation and ownership
-- convention selection. A non-'Q0' explicit parameter whose domain is a kind is
-- still a static/type argument, not a runtime value. Keeping this predicate in
-- Repr prevents primitive override arity checks from counting a position that
-- Ownership.classifyCallArgs will skip as @erasedOrKind@.
runtimeRelevantParam :: EvalCtx -> Int -> Icit -> Q -> Value -> Bool
runtimeRelevantParam ctx lvl ic q dom =
  ic == Expl && q /= Q0 && not (isKindDomainValueAt ctx lvl dom)

isKindDomainValueAt :: EvalCtx -> Int -> Value -> Bool
isKindDomainValueAt ctx lvl v = isKindDomainTerm (quote ctx lvl (force ctx v))

isKindDomainTerm :: Term -> Bool
isKindDomainTerm = \case
  CSort _ -> True
  CPi _ _ _ _ _ cod -> isKindDomainTerm cod
  _ -> False

-- | The largest de-Bruijn INDEX a 'Term' references relative to its own top
-- (a @CVar i@ contributes @i@; entering a binder subtracts one from the body's
-- count, so a fully closed term reports @-1@).  Used by 'repSelect' to reject a
-- Pi codomain whose closure body escapes its environment.
maxVar :: Term -> Int
maxVar = \case
  CVar i -> i
  CGlob _ -> -1
  CLam _ _ _ b -> maxVar b - 1
  CPi _ _ _ _ a b -> max (maxVar a) (maxVar b - 1)
  CApp _ f a -> max (maxVar f) (maxVar a)
  CSort _ -> -1
  CLit _ -> -1
  CCtor _ _ as -> maximum (-1 : map maxVar as)
  CMatch s _ alts ->
    maximum (-1 : maxVar s : [max (maybe (-1) (\guardTm -> maxVar guardTm - patBinders p) gd) (maxVar b - patBinders p) | CaseAlt p gd b <- alts])
  CRecordT fs -> maximum (-1 : map (maxVar . snd) fs)
  CRecordV fs -> maximum (-1 : map (maxVar . snd) fs)
  CProj e _ -> maxVar e
  CProjAt e _ _ -> maxVar e
  CVariantT ms -> maximum (-1 : map maxVar ms)
  CInject _ e -> maxVar e
  CLet _ _ a b c -> maximum [maxVar a, maxVar b, maxVar c - 1]
  CLetRec _ _ a b c -> maximum [maxVar a, maxVar b - 1, maxVar c - 1]
  CMeta _ -> -1
  CDo _ _ -> -1
  CSealE _ e -> maxVar e
  CSigT _ e -> maxVar e
  CThunkE e -> maxVar e
  CLazyE e -> maxVar e
  CForceE e -> maxVar e
  CIf a b c -> maximum [maxVar a, maxVar b, maxVar c]
  CQuote _ slots -> maximum (-1 : map maxVar slots)

-- | How many runtime binder slots a pattern introduces (used by 'maxVar' to
-- offset a match arm's body/guard).  Mirrors the @patBindings@ runtime slot
-- count, including the §17.1 existential-skolem placeholders below the fields.
patBinders :: CorePat -> Int
patBinders = \case
  CPWild -> 0
  CPVar _ -> 1
  CPLit _ -> 0
  CPCtor _ nEx ps -> nEx + sum (map patBinders ps)
  CPTuple ps -> sum (map patBinders ps)
  CPRecord fs mr -> sum (map (patBinders . snd) fs) + maybe 0 (const 1) mr
  CPInject _ p -> patBinders p
  CPInjectRest _ -> 1
  CPOr ps _ -> maximum (0 : map patBinders ps)
  CPAs _ p -> 1 + patBinders p

-- ── Static constructor layout ────────────────────────────────────────
--
-- 'CtorLayout' is the STATIC, compile-time-knowable shape of a constructor —
-- the classification the runtime's @kctor@ (runtime/value.c) seeds its
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
-- packing paths (runtime/value.c, UNBOXING Stage 1d/1e).
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

-- ── S1.3 ctor layout authority (observe-only; consumed by S5 FBIP reuse) ──
--
-- Perceus drop-guided reuse (PERCEUS-RC-DESIGN §3, stage S5) needs the
-- field count and per-field representation of the constructor at every
-- @CCtor@ construct site and every @CMatch@ arm so a unique k-field node can
-- be rebuilt IN PLACE (the @drop-reuse@ token + same-size constructor write).
-- That layout is statically knowable from the constructor's instantiated type
-- telescope, but it is ERASED before the backend lowers the term (§31.2), so
-- the @CCtor@\/@CMatch@ /head-type annotation/ channel ('Kappa.Core.CCtor's
-- @Maybe Term@) re-attaches it. This function reads that annotation back into a
-- layout verdict.
--
-- __It is observe-only in S1__ — populated alongside the annotation
-- (PERCEUS-S1-PLAN (c)), consumed by the S5 reuse pass, NOT by any current
-- codegen. So it changes no tag id, no call shape, and nothing about parity.

-- | The full static layout of a constructor at a construct\/match site: its
-- runtime arity, its 'CtorLayout' packing class, and the per-field 'Rep' list
-- (in field order). 'clLayoutClass' is exactly the 'ctorLayout' verdict over
-- 'clFieldReps', surfaced here so an S5 consumer reads one record rather than
-- recomputing it.
data CtorLayoutInfo = CtorLayoutInfo
  { clArity :: !Int
  -- ^ The constructor's runtime arity (the number of explicit, non-'Q0'
  -- parameter slots in its type telescope) = @length clFieldReps@.
  , clLayoutClass :: !CtorLayout
  -- ^ The static packing class ('ctorLayout' over 'clFieldReps').
  , clFieldReps :: ![Rep]
  -- ^ The 'scalarRep' of each runtime field's domain head, in field order.
  }
  deriving stock (Eq, Show)

-- | Resolve the @CCtor@\/@CMatch@ head-type annotation into a 'CtorLayoutInfo'.
--
-- __TOTAL with @Nothing ⇒ Nothing@__: an absent annotation yields no layout,
-- which is the conservative no-reuse contract S5 relies on (PERCEUS-S1-PLAN
-- (c): \"@Nothing ⇒ conservatively skip reuse@\" — sound, just slower). A
-- present annotation is the constructor's instantiated type as a quoted Core
-- type term; this evaluates it and walks the Pi telescope counting each runtime
-- field by the __RUNTIME__ field rule ('ctorFieldReps').
--
-- == Why NOT 'repSelect' (the §S1.3 evidence-field bug)
--
-- The runtime field set a constructor is actually BUILT with is 'etaCtor's
-- @runtimeField@ ("Kappa.Check") = @compileCtor@'s argument list
-- ("Kappa.Backend.C"): @Expl _ -> True@; @Impl q -> q \/= Q0@. It KEEPS an
-- implicit, non-'Q0' binder — an EVIDENCE\/DICTIONARY field, e.g. the
-- @Show a =>@ obligation of @MkShowable : forall (a:Type). Show a => a ->
-- Showable@ (the @Show a =>@ elaborates to a 'CPi' @Impl@ @QW@ existential
-- dictionary). 'repSelect', by contrast, gates on @ic == Expl && q \/= Q0@ and
-- DROPS such fields — correct for the scalar-worker plan it serves (a worker
-- never reads a dictionary slot as a scalar), but WRONG for the ctor's runtime
-- arity. So the layout must count by the runtime rule, not 'repSelect''s
-- explicit-only one; otherwise an S5 FBIP reuse would rebuild a same-tag node
-- with too few fields (a miscompile). 'repSelect' itself is left unchanged
-- (the scalar-worker callers rely on its explicit-only semantics); the runtime
-- walk lives in 'ctorFieldReps'.
--
-- Every runtime field contributes its 'scalarRep'; a dictionary field's domain
-- head is a trait type, which is not a scalar primitive, so it classifies as
-- 'RepBoxed' — exactly the boxed slot the runtime stores it in.
--
-- An annotation that does NOT force to a Pi telescope (e.g. a bare data-head
-- type, as the record-patch construct site records) walks to zero fields and
-- reports the nullary 'LayoutImmediate' class — a sound conservative reading
-- (no fields known ⇒ no reuse claimed), never a wrong-arity miscompile, because
-- nothing in S1 acts on it. A telescope whose codomain closure escapes its
-- environment (the same shape 'repSelect' rejects) yields 'Nothing'.
ctorLayoutOf :: EvalCtx -> Maybe Term -> Maybe CtorLayoutInfo
ctorLayoutOf _ Nothing = Nothing
ctorLayoutOf ctx (Just ty) =
  case ctorFieldReps ctx (eval ctx [] ty) of
    Nothing -> Nothing
    Just fieldReps ->
      Just
        CtorLayoutInfo
          { clArity = length fieldReps
          , clLayoutClass = ctorLayout fieldReps
          , clFieldReps = fieldReps
          }

-- | Walk a constructor's (whnf-forced) type telescope and return the 'scalarRep'
-- of every __RUNTIME__ field, in field order — the field set the backend
-- actually builds the node with.
--
-- This is the RUNTIME-rule counterpart to 'repSelect''s explicit-only walk: a
-- field counts iff it is @Expl _@ OR @Impl q@ with @q \/= Q0@, EXACTLY matching
-- 'etaCtor's @runtimeField@ ("Kappa.Check") and @compileCtor@'s argument list
-- ("Kappa.Backend.C"). The crucial difference from 'repSelect' is the @Impl@,
-- non-'Q0' case: that is an evidence\/dictionary field (an elaborated @C a =>@
-- trait obligation), which the runtime DOES store as a (boxed) field but
-- 'repSelect' drops. A 'Q0'-erased binder (of either icity) is skipped — it is
-- erased before the backend and occupies no runtime slot.
--
-- @Nothing@ is returned for the same unwalkable-codomain shape 'repSelect'
-- rejects (a codomain closure escaping its environment); a non-Pi head ends the
-- walk with the fields gathered so far.
ctorFieldReps :: EvalCtx -> Value -> Maybe [Rep]
ctorFieldReps ctx = walk 0 []
  where
    walk lvl acc ty =
      case force ctx ty of
        VPi ic q _ _ dom clo@(Closure env body) ->
          if not (closureHasBoundEnv env body)
            then Nothing
            else
              let x = VRigid lvl []
                  cod = closApplyV x clo
                  acc' = if runtimeField ic q then scalarRep dom : acc else acc
               in walk (lvl + 1) acc' cod
        _ -> Just (reverse acc)
    closApplyV v (Closure env body) = eval ctx (v : env) body
    closureHasBoundEnv env body = maxVar body < length env + 1
    -- the RUNTIME field rule, copied VERBATIM from 'etaCtor's @runtimeField@
    -- ("Kappa.Check") which feeds @compileCtor@'s argument list
    -- ("Kappa.Backend.C"): an EXPLICIT field always counts (even a 'Q0' one — it
    -- still occupies a positional slot, erased to a @kunit()@ placeholder); an
    -- IMPLICIT field counts iff it is non-'Q0' (an evidence\/dictionary field).
    runtimeField Expl _ = True
    runtimeField Impl q = q /= Q0

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
