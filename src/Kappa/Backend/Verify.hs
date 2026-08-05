-- | KBackendIR __Stage 3__ — a user-invokable, OBSERVE-ONLY lowering-legality
-- verifier (§34.3.3 / §34.3.4).
--
-- This module implements the three §34.3.3 lowering-legality checkpoints that
-- are actually checkable against today's elaborated Core ("Kappa.Check"'s
-- 'CheckState') and the Stage-2 representation table ("Kappa.Backend.Repr").
-- It builds on the Stage-0 lint ("Kappa.CoreLint") and reuses the Stage-0
-- head-type annotations on 'CCtor'\/'CMatch'.
--
-- __Contract (do not violate).__ This pass is OBSERVE-ONLY:
--
--   * it only produces 'Diagnostic's (all at 'SevWarning'); it never aborts
--     compilation, mutates 'CheckState', or changes a single byte of emitted
--     code — a valid program is byte-identical with or without it;
--   * it is CONSERVATIVE: every check fires only when a property is /statically
--     and unambiguously/ violated, so a well-typed corpus is reported clean
--     (zero false positives). Anything whose legality cannot be decided from
--     Core + the Repr table alone is skipped, not guessed.
--
-- The §34.3.3 promotion to a hard compile-time error (and the §34.3.6
-- "interpreter executes only verified IR" gate) is the deliberate follow-on
-- once this is proven false-positive-free on the whole corpus.
--
-- The three checkpoints implemented here:
--
--   1. __Erasure legality__ (§34.3.3 bullet 2 + the line-34688 reject rule):
--      no runtime term in a head\/argument\/value position refers to an erased
--      entity (a 'Type'\/universe term, or a constructor used as if callable)
--      that was not reified as an ordinary runtime value. This is the class
--      the @kapp(unit, unit)@ miscompile belonged to. See 'erasureViolations'.
--
--   2. __Fixed runtime arity__ (§34.3.3 bullet 3): every 'CCtor' is saturated
--      to exactly its constructor's runtime arity (the count of runtime fields
--      in its declared type), so no closure-less partial application or arity
--      mismatch reaches lowering. See 'arityViolations'.
--
--   3. __Layout consistency__ (§34.3.3 "data\/variant\/record layout choices
--      fixed consistently with §§31.3-31.4"): the per-datatype constructor tag
--      ids assigned by "Kappa.Backend.Repr" are INJECTIVE within each datatype;
--      every constructor a datatype lists points BACK to it ('ciData'); and a
--      constructor's explicit-field count does not exceed its type-derived
--      runtime arity (so its chosen layout reserves enough slots). See
--      'layoutViolations'.
module Kappa.Backend.Verify
  ( verifyUnit
  , VerifyInputs (..)
  , verifyInputs
  ) where

import Data.List (sort)
import qualified Data.Map.Strict as Map
import Data.Map.Strict (Map)
import Data.Maybe (mapMaybe)
import Data.Text (Text)
import qualified Data.Text as T

import Kappa.Backend.Repr
  ( assignUserCtorTags
  , erasedSpinePositionsForArgs
  , isBuiltinCtor
  , runtimeConstructorPiField
  , tagId
  )
import Kappa.Builtins (prelUnit)
import Kappa.Check (CheckState (..), CtorInfo (..), DataInfo (..), linkedCoreBodies)
import Kappa.Core
import Kappa.CoreOps (spineOfTerm)
import Kappa.Diagnostic
import Kappa.Eval
  ( EvalCtx (..)
  , GlobalDef (..)
  , Globals (..)
  , MetaState
  , eval
  , force
  , quote
  )
import Kappa.Source (noSpan)

-- ── The verifier surface ─────────────────────────────────────────────

-- | The minimal slice of a checked compilation unit the verifier consumes.
-- Factored out so a caller can build it from a 'CheckState' ('verifyInputs')
-- or hand-construct one in a test (to exercise a deliberately-malformed IR).
data VerifyInputs = VerifyInputs
  { viGlobals :: !(Map GName GlobalDef)
  -- ^ global signatures\/values (for head-callability + spine erasure).
  , viMetas :: !MetaState
  -- ^ meta solutions (so 'force'\/'eval' see the final, zonked types).
  , viBodies :: !(Map GName Term)
  -- ^ the elaborated, zonked runtime bodies to walk.
  , viDatas :: !(Map GName DataInfo)
  -- ^ datatype → constructor list (for layout cross-checking).
  , viCtors :: !(Map GName CtorInfo)
  -- ^ constructor → parent + declared type (for runtime-arity + layout).
  }

-- | Build the verifier inputs from a checked 'CheckState'.
verifyInputs :: CheckState -> VerifyInputs
verifyInputs st =
  VerifyInputs
    { viGlobals = csGlobals st
    , viMetas = csMetas st
    , viBodies = linkedCoreBodies st
    , viDatas = csDatas st
    , viCtors = csCtors st
    }

-- | Run all three §34.3.3 checkpoints. An empty result is the clean case.
-- The order is body-checks first (erasure, arity), then the program-global
-- layout cross-check, so a reader sees per-definition findings before the
-- whole-program table findings.
verifyUnit :: VerifyInputs -> [Diagnostic]
verifyUnit vi =
  concatMap perBody (Map.toList (viBodies vi))
    ++ layoutViolations vi
  where
    ctx = EvalCtx (Globals (viGlobals vi)) (viMetas vi) False Map.empty
    perBody (g, body) =
      let who = gnameText g
       in erasureViolations vi ctx who body
            ++ arityViolations vi who body

-- ── Checkpoint 1 — erasure legality (§34.3.3 bullet 2 / line 34688) ──
--
-- "no unerased Type, universe term, row term, anonymous region, quantity-0
-- binder, or proof-only term remains unless it has been explicitly reified as
-- an ordinary runtime value" / "A KBackendIR legality verifier MUST reject a
-- runtime term that refers to erased Type, TypeLevel, Quantity, Region, row,
-- label, proof, syntax, … except through a specified runtime carrier".
--
-- We soundly check the two manifestations that exist in today's Core:
--
--   (a) a value-application SPINE whose head is statically a non-function value
--       — a saturated constructor, a literal, a record\/variant value, a sort,
--       or a global whose declared type is a non-function (e.g. 'Unit'). This
--       is the @kapp(unit, unit)@ class. (Generalizes the Stage-0 lint.)
--
--   (b) a manifestly-erased TYPE form (a 'CSort' universe, a 'CPi' function
--       type, a 'CRecordT'\/'CVariantT'\/'CSigT' type) sitting in a runtime
--       argument slot the lowering KEEPS — i.e. NOT one the callee's signature
--       erases by quantity-0 or kind-domain. (A type form at an erased slot is
--       the backend's own @CSort 0@ placeholder, or a legitimately-erased type
--       argument, and is left alone — checking only kept slots is what keeps
--       this free of false positives on kind-polymorphic code.)

-- | Erasure-legality findings for one body. @who@ names the enclosing
-- definition (used only in messages).
erasureViolations :: VerifyInputs -> EvalCtx -> Text -> Term -> [Diagnostic]
erasureViolations vi ctx who = go
  where
    go t = case t of
      CUniverseLift _ _ _ inner -> go inner
      CSchemaLift _ _ _ _ _ _ sourceArguments targetArguments inner ->
        concatMap go sourceArguments ++ concatMap go targetArguments ++ go inner
      CArithmeticProof _ -> []
      CApp {} ->
        let (hd, args) = spineOfTerm t
            headDiag = case classifyHead ctx hd of
              Just reason -> [nonFunctionHeadDiag who reason]
              Nothing -> []
            -- (b): for a CGlob-headed spine, flag a manifestly-erased type
            -- form at a runtime-KEPT argument position (per the shared S5.A
            -- erasure mask). The mask is the same 'Repr' verdict the backends
            -- consume, so we never flag what lowering erases.
            argDiags = case hd of
              CGlob g ->
                let erased = erasedSpinePositionsForArgs (viGlobals vi) ctx g (map fst args)
                    kept = map not erased
                 in concat
                      [ [erasedArgDiag who g i (typeFormReason a) | typeForm a]
                      | (keep, (_, a), i) <- zip3 (kept ++ repeat True) args [0 ..]
                      , keep
                      ]
              _ -> []
         in headDiag ++ argDiags ++ go hd ++ concatMap (go . snd) args
      CVar _ -> []
      CGlob _ -> []
      CLam _ _ _ b -> go b
      CPi _ _ _ _ a b -> go a ++ go b
      CSort _ -> []
      CLevel _ -> []
      CLit _ -> []
      CCtor _ _ as -> concatMap go as
      CMatch s _ _ alts -> go s ++ concatMap goAlt alts
      CRecordT fs -> concatMap (go . snd) fs
      CRecordV fs -> concatMap (go . snd) fs
      CProj e _ -> go e
      CProjAt e _ _ -> go e
      CVariantT ms -> concatMap go ms
      CInject _ e -> go e
      CLet _ _ a b c -> go a ++ go b ++ go c
      CLetRec _ _ a b c -> go a ++ go b ++ go c
      CLetPolyM _ _ _ _ a b c -> go a ++ go b ++ go c
      CLetRecPolyM _ _ _ _ a b c -> go a ++ go b ++ go c
      CLetRecGroupM _ definitions body ->
        concatMap (\definition -> go (clrdType definition) ++ go (clrdRhs definition)) definitions ++ go body
      CMeta _ -> []
      CDo {} -> []
      CSealE _ e -> go e
      CSigT _ e -> go e
      CThunkE e suspensionType -> go e ++ maybe [] go suspensionType
      CLazyE e suspensionType -> go e ++ maybe [] go suspensionType
      CForceE e resultType -> go e ++ maybe [] go resultType
      CIf a b c -> go a ++ go b ++ go c
      CQuote _ slots -> concatMap go slots
      CLocal _ _ -> []
    goAlt (CaseAlt _ gd b) = maybe [] go gd ++ go b

-- | Is @t@ a manifestly-erased TYPE form — something with no runtime value
-- representation, which in a runtime-kept slot is an erased reference?
-- We are deliberately narrow: only forms that are UNAMBIGUOUSLY types
-- (a universe, a function type, a record\/variant\/signature type). A bare
-- type-constructor name ('CGlob' of a datatype) is NOT included, because the
-- same name can head a runtime-relevant value spine; restricting to syntactic
-- type forms keeps this sound.
typeForm :: Term -> Bool
typeForm = \case
  CSort _ -> True
  CPi {} -> True
  CRecordT _ -> True
  CVariantT _ -> True
  CSigT _ _ -> True
  _ -> False

typeFormReason :: Term -> Text
typeFormReason = \case
  CSort _ -> "a universe ('Type')"
  CPi {} -> "a function type"
  CRecordT _ -> "a record type"
  CVariantT _ -> "a variant type"
  CSigT _ _ -> "a signature type"
  _ -> "an erased type form"

-- | Decide whether @hd@, used as the head of a value application, is
-- /statically/ a non-function value. (This is the Stage-0 lint's classifier,
-- re-stated here so the Stage-3 verifier is self-contained; the two agree by
-- construction.) 'Just' a human-readable reason when provably bad; 'Nothing'
-- when the head is fine or its type cannot be decided from Core alone.
classifyHead :: EvalCtx -> Term -> Maybe Text
classifyHead ctx = \case
  CCtor g _ _ -> Just ("the saturated constructor '" <> gnameText g <> "' is a value, not a function")
  CLit _ -> Just "a literal is a value, not a function"
  CRecordV _ -> Just "a record value is not a function"
  CRecordT _ -> Just "a record type is not a function"
  CVariantT _ -> Just "a variant type is not a function"
  CInject _ _ -> Just "a variant injection is a value, not a function"
  CSort _ -> Just "a sort ('Type') is not a function"
  CGlob g -> case Map.lookup g (globalsMap (ecGlobals ctx)) of
    Just gd
      | isNonFunctionType ctx (gdType gd) ->
          Just ("the global '" <> gnameText g <> "' has a non-function type, so it cannot be applied")
    _ -> Nothing
  _ -> Nothing

-- | Is @ty@ (a global's declared type, as a 'Value') statically a
-- non-function? A residual explicit 'CPi' anywhere is callable; only a
-- concrete non-function head ('Unit' or a sort) is flagged. Identical to the
-- Stage-0 lint's classifier.
isNonFunctionType :: EvalCtx -> Value -> Bool
isNonFunctionType ctx ty0 = case force ctx ty0 of
  VPi {} -> False
  v -> case stripImplicitPis (quote ctx 0 v) of
    CPi {} -> False
    CSort _ -> True
    CGlob g -> g == prelUnit
    _ -> False

stripImplicitPis :: Term -> Term
stripImplicitPis (CPi Impl _ _ _ _ b) = stripImplicitPis b
stripImplicitPis t = t

-- ── Checkpoint 2 — fixed runtime arity (§34.3.3 bullet 3) ────────────
--
-- "every call, closure, and entrypoint has a fixed runtime arity and runtime
-- calling convention". The checkable manifestation in today's Core is the
-- saturated-constructor invariant: a 'CCtor g _ as' MUST carry a fixed shape
-- the KCore→KBackendIR lowerer knows how to erase. KCore constructors may be
-- source-shaped (explicit fields retained for interpretation/conversion) or
-- already runtime-shaped; KBackendIR then drops the erased fields. Any other
-- count is a partial application or stale constructor payload.

-- | Constructor runtime-arity findings for one body.
arityViolations :: VerifyInputs -> Text -> Term -> [Diagnostic]
arityViolations vi who = go
  where
    go t = case t of
      CUniverseLift _ _ _ inner -> go inner
      CSchemaLift _ _ _ _ _ _ sourceArguments targetArguments inner ->
        concatMap go sourceArguments ++ concatMap go targetArguments ++ go inner
      CArithmeticProof _ -> []
      CCtor g _ as ->
        let here = case ctorValidPayloadArities vi g of
              Just ns
                | length as `notElem` ns ->
                    [ ctorArityDiag who g (length as) ns ]
              _ -> []
         in here ++ concatMap go as
      CApp _ f a -> go f ++ go a
      CVar _ -> []
      CGlob _ -> []
      CLam _ _ _ b -> go b
      CPi _ _ _ _ a b -> go a ++ go b
      CSort _ -> []
      CLevel _ -> []
      CLit _ -> []
      CMatch s _ _ alts -> go s ++ concatMap goAlt alts
      CRecordT fs -> concatMap (go . snd) fs
      CRecordV fs -> concatMap (go . snd) fs
      CProj e _ -> go e
      CProjAt e _ _ -> go e
      CVariantT ms -> concatMap go ms
      CInject _ e -> go e
      CLet _ _ a b c -> go a ++ go b ++ go c
      CLetRec _ _ a b c -> go a ++ go b ++ go c
      CLetPolyM _ _ _ _ a b c -> go a ++ go b ++ go c
      CLetRecPolyM _ _ _ _ a b c -> go a ++ go b ++ go c
      CLetRecGroupM _ definitions body ->
        concatMap (\definition -> go (clrdType definition) ++ go (clrdRhs definition)) definitions ++ go body
      CMeta _ -> []
      CDo {} -> []
      CSealE _ e -> go e
      CSigT _ e -> go e
      CThunkE e suspensionType -> go e ++ maybe [] go suspensionType
      CLazyE e suspensionType -> go e ++ maybe [] go suspensionType
      CForceE e resultType -> go e ++ maybe [] go resultType
      CIf a b c -> go a ++ go b ++ go c
      CQuote _ slots -> concatMap go slots
      CLocal _ _ -> []
    goAlt (CaseAlt _ gd b) = maybe [] go gd ++ go b

-- | Accepted saturated constructor payload arities. Runtime arity is accepted
-- for already-lowered Core fragments. Core payload arity is accepted for
-- ordinary constructor values: all explicit fields are retained in KCore, and
-- non-erased implicit evidence fields are retained as hidden payload slots.
-- Plain explicit-field arity is also accepted when there are no hidden runtime
-- implicit fields; this covers direct checker rewrites such as constructor
-- record-patch rebuilds before KBackendIR erases explicit Q0/type fields.
ctorValidPayloadArities :: VerifyInputs -> GName -> Maybe [Int]
ctorValidPayloadArities vi g = do
  ci <- Map.lookup g (viCtors vi)
  let ctx = EvalCtx (Globals (viGlobals vi)) (viMetas vi) False Map.empty
      counts = ctorPayloadCounts ctx (eval ctx [] (ciType ci))
      base = [cpcRuntime counts, cpcCore counts]
      explicit =
        [ length (ciFields ci)
        | cpcImplicitRuntime counts == 0
        ]
  pure (dedupeSorted (base ++ explicit))
  where
    dedupeSorted = Map.keys . Map.fromList . map (\n -> (n, ()))

data CtorPayloadCounts = CtorPayloadCounts
  { cpcRuntime :: !Int
  , cpcCore :: !Int
  , cpcImplicitRuntime :: !Int
  }

ctorPayloadCounts :: EvalCtx -> Value -> CtorPayloadCounts
ctorPayloadCounts ctx = count 0
  where
    count lvl ty = case force ctx ty of
      VPiRuntimeM _ _ ic q _ _ _ _ runtimeErasure dom clo ->
        let runtime = runtimeConstructorPiField ctx lvl runtimeErasure ic q dom
            core = ic == Expl || runtime
            implicitRuntime = ic /= Expl && runtime
            rest = count (lvl + 1) (closApply ctx lvl clo)
         in CtorPayloadCounts
              { cpcRuntime = boolCount runtime + cpcRuntime rest
              , cpcCore = boolCount core + cpcCore rest
              , cpcImplicitRuntime = boolCount implicitRuntime + cpcImplicitRuntime rest
              }
      _ -> CtorPayloadCounts 0 0 0
    boolCount b = if b then 1 else 0
    closApply ctx lvl (Closure env body) = eval ctx (VRigid lvl [] : env) body

-- ── Checkpoint 3 — layout consistency (§34.3.3 / §§31.3-31.4) ────────
--
-- "data, variant, and record layout choices are fixed consistently with
-- §§31.3-31.4". We cross-check the Core's datatypes ('viDatas'\/'viCtors')
-- against the Stage-2 representation table ("Kappa.Backend.Repr"):
--
--   (a) TAG-ID INJECTIVITY: within each datatype, the 'Repr.tagId' assigned to
--       its constructors are pairwise DISTINCT. A collision is a silent
--       miscompile (one constructor's value would match another's arm). This
--       cross-checks the actual program-wide tag map the backends consult.
--
--   (b) PARENT BACK-REFERENCE: every constructor a datatype lists in its
--       'diCtors' must be a KNOWN constructor whose 'ciData' points BACK to
--       that datatype. A constructor with the wrong (or missing) parent would
--       be laid out under the wrong datatype's tag context — a layout-identity
--       inconsistency the §13.1\/§31.3 stable-member-identity rules forbid.
--
--   (c) FIELD-COUNT ⟹ LAYOUT CONSISTENCY: a constructor has TWO views of its
--       field count — the explicit-field list ('ciFields') the elaborator
--       recorded, and the runtime arity derived from its declared TYPE
--       telescope ('ctorRuntimeArity'). Under S5.A, raw explicit fields can be
--       runtime-erased type/proof fields, so the raw explicit count is not a
--       layout obligation. The runtime arity must cover the runtime-kept
--       explicit fields; non-Q0 implicit fields are extra runtime slots. A
--       constructor whose runtime-kept explicit fields exceed its type's
--       runtime arity is structurally inconsistent: the chosen
--       'Repr.CtorLayout' would reserve fewer slots than the constructor
--       carries. This cross-checks the two field-count sources the layout
--       decision depends on.
--
-- The tag map is derived through the SAME 'Repr.assignUserCtorTags' the
-- backends use, over the program's full user-ctor set, so this is the exact
-- table lowering will consult.

layoutViolations :: VerifyInputs -> [Diagnostic]
layoutViolations vi = concatMap perData (Map.toList (viDatas vi))
  where
    -- the program-wide user-ctor tag map (builtins keep their fixed ids and
    -- are excluded from numbering), built exactly as the backends build it.
    userKeys =
      sort
        [ gKey c
        | (c, _) <- Map.toList (viCtors vi)
        , not (isBuiltinCtor c)
        ]
    userTags = assignUserCtorTags userKeys

    perData (d, di) =
      let ctors = diCtors di
          ids = [(c, tagId userTags c) | c <- ctors]
          -- (a) injectivity: group by id; any id shared by ≥2 ctors collides.
          collisions =
            [ tagCollisionDiag d i cs
            | (i, cs) <- groupByTag ids
            , length cs >= 2
            ]
          -- (b) parent back-reference + (c) field-count consistency.
          fieldCountBad = mapMaybe (fieldCountWF d) ctors
       in collisions ++ mapMaybe (parentWF d) ctors ++ fieldCountBad

    -- (b): a listed constructor must be known with 'ciData' == this datatype.
    parentWF d c = case Map.lookup c (viCtors vi) of
      Nothing -> Just (ctorUnknownDiag d c)
      Just ci
        | ciData ci /= d -> Just (ctorParentMismatchDiag d c (ciData ci))
        | otherwise -> Nothing

    -- (c): the runtime-kept explicit-field count must not EXCEED the
    -- type-derived runtime arity. Raw explicit fields can include erased
    -- type/proof payloads under S5.A, so comparing 'length ciFields' here
    -- would reject valid erased-layout constructors.
    fieldCountWF d c = do
      ci <- Map.lookup c (viCtors vi)
      let ctx = EvalCtx (Globals (viGlobals vi)) (viMetas vi) False Map.empty
          n = cpcRuntime (ctorPayloadCounts ctx (eval ctx [] (ciType ci)))
      (explicitBinders, explicitRuntime) <- ctorRuntimeExplicitFacts vi c (length (ciFields ci))
      let explicitFields = length (ciFields ci)
      if explicitFields > explicitBinders
        then Just (fieldBinderCountDiag d c explicitFields explicitBinders)
        else
          if explicitRuntime > n
            then Just (fieldCountDiag d c explicitRuntime n)
            else Nothing

ctorRuntimeExplicitFacts :: VerifyInputs -> GName -> Int -> Maybe (Int, Int)
ctorRuntimeExplicitFacts vi g fieldCount = do
  ci <- Map.lookup g (viCtors vi)
  let ctx = EvalCtx (Globals (viGlobals vi)) (viMetas vi) False Map.empty
      explicitFlags = collect ctx 0 (eval ctx [] (ciType ci))
      fieldFlags = drop (max 0 (length explicitFlags - fieldCount)) explicitFlags
  pure (length explicitFlags, length (filter id (take fieldCount fieldFlags)))
  where
    collect ctx lvl ty = case force ctx ty of
      VPiRuntimeM _ _ ic q _ _ _ _ runtimeErasure dom clo ->
        let rest = collect ctx (lvl + 1) (closApply ctx lvl clo)
         in if ic == Expl
              then runtimeConstructorPiField ctx lvl runtimeErasure ic q dom : rest
              else rest
      _ -> []
    closApply ctx lvl (Closure env body) = eval ctx (VRigid lvl [] : env) body

-- | Group @(ctor, id)@ pairs by id, preserving a deterministic id order.
groupByTag :: [(GName, Int)] -> [(Int, [GName])]
groupByTag pairs =
  Map.toList (Map.fromListWith (++) [(i, [c]) | (c, i) <- pairs])

-- ── Diagnostics ──────────────────────────────────────────────────────
--
-- All findings are 'SevWarning' (observe-only). The codes are registered in
-- "Kappa.Explain"; the families are under this implementation's reserved
-- @kappa-hs.backendir.*@ namespace.

mkDiag :: DiagnosticCode -> DiagnosticFamily -> Text -> Diagnostic
mkDiag code fam msg =
  diag SevWarning StageElaborate code (Just fam) noSpan msg

nonFunctionHeadDiag :: Text -> Text -> Diagnostic
nonFunctionHeadDiag who reason =
  mkDiag
    "W_BACKENDIR_NON_FUNCTION_HEAD"
    "kappa-hs.backendir.non-function-head"
    ( "in '" <> who <> "': a value application has a non-function head — "
        <> reason
        <> " (KBackendIR §34.3.3 erasure-legality; this would lower to an ill-typed 'kapp')"
    )

erasedArgDiag :: Text -> GName -> Int -> Text -> Diagnostic
erasedArgDiag who g i reason =
  mkDiag
    "W_BACKENDIR_ERASED_REFERENCE"
    "kappa-hs.backendir.erased-reference"
    ( "in '" <> who <> "': argument " <> tshow i <> " of '" <> gnameText g
        <> "' is " <> reason
        <> " in a runtime-kept slot — an erased reference (KBackendIR §34.3.3 "
        <> "erasure-legality / Spec line 34688)"
    )

ctorArityDiag :: Text -> GName -> Int -> [Int] -> Diagnostic
ctorArityDiag who g got wants =
  mkDiag
    "W_BACKENDIR_ARITY_MISMATCH"
    "kappa-hs.backendir.arity-mismatch"
    ( "in '" <> who <> "': constructor '" <> gnameText g <> "' is built with "
        <> tshow got <> " payload field(s) but its signature admits fixed payload arity "
        <> T.intercalate "/" (map tshow wants)
        <> " (KBackendIR §34.3.3 fixed-runtime-arity)"
    )

tagCollisionDiag :: GName -> Int -> [GName] -> Diagnostic
tagCollisionDiag d i cs =
  mkDiag
    "W_BACKENDIR_LAYOUT_INCONSISTENT"
    "kappa-hs.backendir.layout-inconsistent"
    ( "datatype '" <> gnameText d <> "': constructors "
        <> T.intercalate ", " (map (\c -> "'" <> gnameText c <> "'") (sortNames cs))
        <> " share tag id " <> tshow i
        <> " — non-injective tag assignment (KBackendIR §34.3.3 layout-consistency / §§31.3-31.4)"
    )

fieldCountDiag :: GName -> GName -> Int -> Int -> Diagnostic
fieldCountDiag d c explicitRuntime n =
  mkDiag
    "W_BACKENDIR_LAYOUT_INCONSISTENT"
    "kappa-hs.backendir.layout-inconsistent"
    ( "datatype '" <> gnameText d <> "': constructor '" <> gnameText c
        <> "' has " <> tshow explicitRuntime <> " runtime-kept explicit field(s) but its type "
        <> "has runtime arity " <> tshow n
        <> " — the chosen layout would under-reserve field slots (KBackendIR "
        <> "§34.3.3 layout-consistency / §§31.3-31.4)"
    )

fieldBinderCountDiag :: GName -> GName -> Int -> Int -> Diagnostic
fieldBinderCountDiag d c explicitFields explicitBinders =
  mkDiag
    "W_BACKENDIR_LAYOUT_INCONSISTENT"
    "kappa-hs.backendir.layout-inconsistent"
    ( "datatype '" <> gnameText d <> "': constructor '" <> gnameText c
        <> "' records " <> tshow explicitFields <> " explicit field(s) but its type "
        <> "has only " <> tshow explicitBinders
        <> " explicit binder(s) — constructor field metadata and type layout disagree "
        <> "(KBackendIR §34.3.3 layout-consistency / §§31.3-31.4)"
    )

ctorUnknownDiag :: GName -> GName -> Diagnostic
ctorUnknownDiag d c =
  mkDiag
    "W_BACKENDIR_LAYOUT_INCONSISTENT"
    "kappa-hs.backendir.layout-inconsistent"
    ( "datatype '" <> gnameText d <> "' lists constructor '" <> gnameText c
        <> "' which has no constructor info — its layout/tag context is "
        <> "undetermined (KBackendIR §34.3.3 layout-consistency / §§31.3-31.4)"
    )

ctorParentMismatchDiag :: GName -> GName -> GName -> Diagnostic
ctorParentMismatchDiag d c actual =
  mkDiag
    "W_BACKENDIR_LAYOUT_INCONSISTENT"
    "kappa-hs.backendir.layout-inconsistent"
    ( "datatype '" <> gnameText d <> "' lists constructor '" <> gnameText c
        <> "' but that constructor's parent is '" <> gnameText actual
        <> "' — it would be laid out under the wrong datatype's tag context "
        <> "(KBackendIR §34.3.3 layout-consistency / §§31.3-31.4)"
    )

sortNames :: [GName] -> [GName]
sortNames = map snd . sort . map (\g -> (gKey g, g))

tshow :: Int -> Text
tshow = T.pack . show
