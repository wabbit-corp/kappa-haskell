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
  , runtimeErasedParam
  , runtimeRelevantParam
  , runtimeConstructorField
  , erasedParamMask
  , erasedSpinePositions
  , erasedSpinePositionsForArgs
  , keptSpinePositions

    -- * Function rep/worker-plan selection (the single authority)
  , repSelect
  , runtimeParamMask

    -- * S1.5 owned/borrowed calling convention (telescope-derived; observe-only)
  , ArgConv (..)
  , ArgPlan
  , argConvSelect
  , argConvSelectForArgs
  , argConvSelectForArgsAt
  , argPlanSelectForArgsAt
  , argConvSelectGlobal
  , argConvSelectGlobalForArgs
  , argConvGlobalType
  , resultIsProofGlobal
  , resultIsProofValue
  , resultIsProofBodyGlobal
  , resultIsProofBodyValue

    -- * Static constructor layout
  , CtorLayout (..)
  , ctorLayout
  , ctorLayoutByArity
  , ctorBoxedFootprintBytes

    -- * S1.3 ctor layout authority (observe-only; S5 Phase B reuse substrate)
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
import Kappa.Builtins
  ( builtinCtorTagId
  , gPrel
  , kctUserBase
  , prelDouble
  , prelEqType
  , prelInt
  , prelInteger
  , prelIsProp
  , prelIsSet
  , prelIsSubsingleton
  , prelNat
  , primModule
  )
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
argConvSelect ctx = argConvSelectAt ctx 0

argConvSelectAt :: EvalCtx -> Int -> Value -> Maybe [ArgConv]
argConvSelectAt ctx startLvl = walk startLvl []
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

-- | A global whose result is a runtime-erased proof has no native value body.
-- This is shared by KBackendIR lowering and native emitters so erased proof
-- bodies do not look like runtime erasure bugs while real runtime references to
-- erased values still fail closed.
resultIsProofGlobal :: Map GName GlobalDef -> EvalCtx -> GName -> Bool
resultIsProofGlobal globals ctx g =
  case Map.lookup g globals of
    Nothing -> False
    Just gd -> resultIsProofValue ctx 0 (gdType gd)

-- | True when the semantic type's result is explicitly known to be
-- runtime-erased proposition evidence. This is a runtime-erasure classifier,
-- not a source-name recognizer: callers pass the already elaborated/evaluated
-- type, and the classifier inspects the quoted normal form for 'IsProp' heads
-- or variables constrained by 'IsProp' hypotheses in the telescope. Equality
-- proofs, 'IsSubsingleton', 'IsSet', and higher groupoid-style evidence are not
-- erased by this predicate unless the source supplies the explicit proposition
-- evidence the spec assigns runtime-erasure semantics to.
resultIsProofValue :: EvalCtx -> Int -> Value -> Bool
resultIsProofValue ctx lvl ty =
  resultIsProofTerm proofHeads [prelIsProp] lvl [] (quote ctx lvl (force ctx ty))

-- | Broader native proof-body classifier. This is deliberately NOT used for
-- parameter/field representation erasure: it is only for proof-producing global
-- bodies and already-erased proof applications whose generated native value is
-- never observed. It preserves the pre-S5 native backend behavior while keeping
-- ordinary equality-proof fields runtime-relevant unless a real RuntimeErased
-- proof is present.
resultIsProofBodyGlobal :: Map GName GlobalDef -> EvalCtx -> GName -> Bool
resultIsProofBodyGlobal globals ctx g =
  case Map.lookup g globals of
    Nothing -> False
    Just gd -> resultIsProofBodyValue ctx 0 (gdType gd)

resultIsProofBodyValue :: EvalCtx -> Int -> Value -> Bool
resultIsProofBodyValue ctx lvl ty =
  resultIsProofTerm proofBodyHeads [prelIsProp, prelIsSubsingleton] lvl [] (quote ctx lvl (force ctx ty))

resultIsProofTerm :: [GName] -> [GName] -> Int -> [Int] -> Term -> Bool
resultIsProofTerm heads hypHeads lvl propLvls ty = case ty of
  CPi _ _ _ _ dom cod ->
    let propLvls' = case hypProofVarLevel hypHeads lvl dom of
          Just l -> l : propLvls
          Nothing -> propLvls
     in resultIsProofTerm heads hypHeads (lvl + 1) propLvls' cod
  r ->
    case coreHeadGlob r of
      Just h | h `elem` heads -> True
      _ -> case r of
        CVar i -> (lvl - 1 - i) `elem` propLvls
        _ -> False

hypProofVarLevel :: [GName] -> Int -> Term -> Maybe Int
hypProofVarLevel heads lvl dom =
  case coreSpine dom of
    (CGlob h, [(_, CVar j)])
      | h `elem` heads ->
          Just (lvl - 1 - j)
    _ -> Nothing

proofHeads :: [GName]
proofHeads = [prelIsProp]

proofBodyHeads :: [GName]
proofBodyHeads =
  [ prelEqType
  , prelIsProp
  , prelIsSubsingleton
  , prelIsSet
  , gPrel "IsContr"
  , gPrel "IsGroupoid"
  , gPrel "CoreEq"
  ]

coreHeadGlob :: Term -> Maybe GName
coreHeadGlob t = case fst (coreSpine t) of
  CGlob h -> Just h
  CCtor h _ _ -> Just h
  _ -> Nothing

coreSpine :: Term -> (Term, [(Icit, Term)])
coreSpine = go []
  where
    go acc (CApp ic f a) = go ((ic, a) : acc) f
    go acc h = (h, acc)

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

-- | The shared runtime-erasure classifier for one telescope binder. A
-- quantity-0 binder is erased by quantity; any binder whose domain is itself a
-- kind (@Type@, @Type -> Type@, …) is erased by phase; and domains explicitly
-- known runtime-erased by proposition evidence are erased. The classifier
-- inspects the semantic 'Value' directly, so code generation no longer performs
-- the old @quote . force@ readback just to rediscover kind-domain status.
runtimeErasedParam :: EvalCtx -> Int -> Q -> Value -> Bool
runtimeErasedParam ctx lvl q dom =
  q == Q0 || valueDomainIsKind ctx lvl dom || resultIsProofValue ctx lvl dom

-- | The shared runtime-argument filter for representation and ownership
-- convention selection. A non-'Q0' explicit parameter whose domain is a kind is
-- still a static/type argument, not a runtime value. Keeping this predicate in
-- Repr prevents primitive override arity checks from counting a position that
-- Ownership.classifyCallArgs will skip as @erasedOrKind@.
runtimeRelevantParam :: EvalCtx -> Int -> Icit -> Q -> Value -> Bool
runtimeRelevantParam ctx lvl ic q dom =
  ic == Expl && not (runtimeErasedParam ctx lvl q dom)

-- | Constructor payload fields use the same erasure classifier as ordinary
-- runtime parameters, with one extra allowance: implicit non-erased evidence
-- and dictionary binders are retained because constructor values can carry
-- selected runtime dictionaries. Explicit quantity-0 fields, explicit
-- kind-domain/type fields, implicit quantity-0 indices, and implicit
-- kind-domain type parameters are absent from the runtime payload.
runtimeConstructorField :: EvalCtx -> Int -> Icit -> Q -> Value -> Bool
runtimeConstructorField ctx lvl ic q dom =
  (ic == Expl || q /= Q0) && not (runtimeErasedParam ctx lvl q dom)

-- | One erasure bit per Pi binder in source telescope order. This is the S5.A
-- erasure fact lowered once and shared by C, LLVM, Verify, and the materialized
-- KBackendIR artifact: @True@ means the argument is absent from runtime
-- representation.
erasedParamMask :: EvalCtx -> Value -> [Bool]
erasedParamMask ctx = walk 0 []
  where
    walk lvl acc ty =
      case force ctx ty of
        VPi _ q _ _ dom clo ->
          let x = VRigid lvl []
              cod = closApplyV x clo
           in walk (lvl + 1) (runtimeErasedParam ctx lvl q dom : acc) cod
        _ -> reverse acc
    closApplyV v (Closure env body) = eval ctx (v : env) body

-- | The erased-argument mask for a global-headed application spine. Unknown
-- globals fail safe by erasing nothing.
erasedSpinePositions :: Map GName GlobalDef -> EvalCtx -> GName -> [Bool]
erasedSpinePositions globals ctx g =
  maybe [] (erasedParamMask ctx . gdType) (Map.lookup g globals)

-- | Erasure bits aligned to the ACTUAL application spine, not just to raw
-- telescope position.  KCore may omit erased implicit type arguments while
-- still applying the explicit runtime arguments, so a position-only mask would
-- shift a skipped implicit's erased verdict onto the first explicit value.  The
-- aligner may skip only omitted implicit binders that are themselves erased;
-- unalignable shapes fail conservatively by keeping all supplied arguments.
erasedSpinePositionsForArgs :: Map GName GlobalDef -> EvalCtx -> GName -> [Icit] -> [Bool]
erasedSpinePositionsForArgs globals ctx g actuals =
  case Map.lookup g globals >>= \gd -> alignErasedArgs ctx (gdType gd) actuals of
    Just flags -> flags
    Nothing -> replicate (length actuals) False

-- | The dual of 'erasedSpinePositions': @True@ means the argument remains a
-- runtime value after KCore→KBackendIR erasure.
keptSpinePositions :: Map GName GlobalDef -> EvalCtx -> GName -> [Bool]
keptSpinePositions globals ctx g =
  map not (erasedSpinePositions globals ctx g)

-- | Per-supplied-argument calling conventions for a non-global callee type,
-- aligned with 'erasedSpinePositionsForArgs'. Erased or implicit arguments have
-- no runtime convention; explicit kept arguments consume one convention from
-- 'argConvSelect'. If either the callee telescope or the supplied spine cannot
-- be aligned, return 'Nothing' so callers use their conservative fallback
-- instead of assigning a convention to the wrong argument.
argConvSelectForArgs :: EvalCtx -> Value -> [Icit] -> Maybe [Maybe ArgConv]
argConvSelectForArgs ctx = argConvSelectForArgsAt ctx 0

-- | Per supplied argument: whether it is erased, and the runtime calling
-- convention if it remains as an explicit runtime value.
type ArgPlan = (Bool, Maybe ArgConv)

-- | Like 'argConvSelectForArgs', but the callee type lives under @startLvl@
-- already-bound Core variables. This is required for first-class/local callee
-- heads whose telescope may mention outer binders; globals use level 0.
argConvSelectForArgsAt :: EvalCtx -> Int -> Value -> [Icit] -> Maybe [Maybe ArgConv]
argConvSelectForArgsAt ctx startLvl ty actuals =
  map snd <$> argPlanSelectForArgsAt ctx startLvl ty actuals

argPlanSelectForArgsAt :: EvalCtx -> Int -> Value -> [Icit] -> Maybe [ArgPlan]
argPlanSelectForArgsAt ctx startLvl ty actuals = do
  flags <- alignErasedArgsAt ctx startLvl ty actuals
  convs <- argConvSelectAt ctx startLvl ty
  convs' <- assignArgConvs convs (zip actuals flags)
  pure (zip flags convs')

-- | Per-supplied-argument calling conventions, aligned with
-- 'erasedSpinePositionsForArgs'.  Erased or implicit arguments have no runtime
-- convention; explicit kept arguments consume one convention from
-- 'argConvSelectGlobal'.  If either the callee telescope or the supplied spine
-- cannot be aligned, return 'Nothing' so callers use their conservative
-- fallback instead of assigning a convention to the wrong argument.
argConvSelectGlobalForArgs :: EvalCtx -> GName -> [Icit] -> Maybe [Maybe ArgConv]
argConvSelectGlobalForArgs ctx g actuals = do
  gd <- primitiveGlobalDef (globalsMap (ecGlobals ctx)) g
  flags <- alignErasedArgsAt ctx 0 (gdType gd) actuals
  convs <- argConvSelectGlobal ctx g
  assignArgConvs convs (zip actuals flags)

assignArgConvs :: [ArgConv] -> [(Icit, Bool)] -> Maybe [Maybe ArgConv]
assignArgConvs convs0 = assign convs0
  where
    assign [] [] = Just []
    assign _ [] = Just []
    assign cs ((ic, erased) : rest)
      | erased || ic /= Expl = (Nothing :) <$> assign cs rest
      | c : cs' <- cs = (Just c :) <$> assign cs' rest
      | otherwise = Nothing

alignErasedArgs :: EvalCtx -> Value -> [Icit] -> Maybe [Bool]
alignErasedArgs ctx = alignErasedArgsAt ctx 0

alignErasedArgsAt :: EvalCtx -> Int -> Value -> [Icit] -> Maybe [Bool]
alignErasedArgsAt ctx startLvl = walk startLvl []
  where
    walk _ acc _ [] = Just (reverse acc)
    walk lvl acc ty actuals@(actualIc : restActuals) =
      case force ctx ty of
        VPi ic q _ _ dom clo ->
          let erased = runtimeErasedParam ctx lvl q dom
              cod = closApply lvl clo
           in if ic == actualIc
                then walk (lvl + 1) (erased : acc) cod restActuals
                else
                  if ic == Impl && erased
                    then walk (lvl + 1) acc cod actuals
                    else Nothing
        _ -> Nothing
    closApply l (Closure env body) = eval ctx (VRigid l [] : env) body

valueDomainIsKind :: EvalCtx -> Int -> Value -> Bool
valueDomainIsKind ctx lvl v =
  case force ctx v of
    VSort _ -> True
    VPi _ _ _ _ _ clo ->
      valueDomainIsKind ctx (lvl + 1) (closApply lvl clo)
    _ -> False
  where
    closApply l (Closure env body) = eval ctx (VRigid l [] : env) body

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

-- | Current native boxed-ctor footprint, in bytes.
--
-- A boxed constructor is represented by the outer 'KValue' cell (statically
-- asserted to 48 bytes in @runtime/kappart.h@) plus a scanned array of
-- @KValue *@ argument slots allocated by @kctor@.  S5 Phase B compares this
-- footprint before reusing a just-dropped constructor cell.  Nullary ctors are
-- canonical immediates and have no reusable heap footprint; 'LayoutMayPack'
-- exposes the boxed fallback footprint because the runtime may still allocate
-- when the actual fields do not fit the packed immediate encoding.
ctorBoxedFootprintBytes :: Int -> Int
ctorBoxedFootprintBytes arity = 48 + (8 * arity)

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

-- ── S1.3 ctor layout authority (observe-only; S5 Phase B reuse substrate) ──
--
-- Perceus drop-guided reuse (PERCEUS-RC-DESIGN §3, stage S5) will need the
-- field count and per-field representation of constructors at allocation and
-- match sites before it can pair a drop-reuse token with a same-size
-- constructor write. This record supplies the node-local layout evidence; the
-- actual same-size reuse-site discriminator is built by Phase B, not here.
-- That layout is statically knowable from the constructor's instantiated type
-- telescope, but it is ERASED before the backend lowers the term (§31.2), so
-- the @CCtor@\/@CMatch@ /head-type annotation/ channel ('Kappa.Core.CCtor's
-- @Maybe Term@) re-attaches it. This function reads that annotation back into a
-- layout verdict.
--
-- __It is observe-only before Phase B__ — populated alongside the annotation
-- (PERCEUS-S1-PLAN (c)) and now carried/validated on KBackendIR nodes, but NOT
-- used by current emitters to rewrite allocations or drops. So it changes no
-- tag id, no call shape, and nothing about parity.

-- | The full static layout of a constructor at a construct\/match site: its
-- runtime arity, its 'CtorLayout' packing class, its boxed heap footprint when
-- one can exist, and the per-field 'Rep' list (in field order).
-- 'clLayoutClass' is exactly the 'ctorLayout' verdict over 'clFieldReps',
-- surfaced here so an S5 consumer reads one record rather than recomputing it.
data CtorLayoutInfo = CtorLayoutInfo
  { clArity :: !Int
  -- ^ The constructor's runtime arity (the number of explicit, non-'Q0'
  -- parameter slots in its type telescope) = @length clFieldReps@.
  , clLayoutClass :: !CtorLayout
  -- ^ The static packing class ('ctorLayout' over 'clFieldReps').
  , clBoxedFootprintBytes :: !(Maybe Int)
  -- ^ Current native boxed storage footprint for a constructor with this
  -- layout, if such a heap object can exist. 'Nothing' means the constructor is
  -- always immediate and cannot produce or consume a reuse token.
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
      let layout = ctorLayout fieldReps
          arity = length fieldReps
       in Just
            CtorLayoutInfo
              { clArity = arity
              , clLayoutClass = layout
              , clBoxedFootprintBytes =
                  case layout of
                    LayoutImmediate -> Nothing
                    LayoutMayPack -> Just (ctorBoxedFootprintBytes arity)
                    LayoutBoxed -> Just (ctorBoxedFootprintBytes arity)
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
                  acc' = if runtimeConstructorField ctx lvl ic q dom then scalarRep dom : acc else acc
               in walk (lvl + 1) acc' cod
        _ -> Just (reverse acc)
    closApplyV v (Closure env body) = eval ctx (v : env) body
    closureHasBoundEnv env body = maxVar body < length env + 1

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
