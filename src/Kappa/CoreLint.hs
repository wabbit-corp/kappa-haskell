-- | KBackendIR Stage 0 — an OBSERVE-ONLY lint over elaborated Core.
--
-- This module is the first consumer of the Stage 0 head-type annotations
-- added to 'CCtor' and 'CMatch' in "Kappa.Core". It walks every elaborated
-- definition body and checks a single structural property:
--
--   * __every value application has a function-typed head__.
--
-- The motivating bug is the @kapp(unit, unit)@ crash: a 'CApp' whose head,
-- after elaboration, is an erased\/unit-valued term (e.g. a global whose
-- declared type is @Unit@, or a bare saturated constructor used as if it were
-- callable). Such a term lowers to an ill-typed @kapp@ in the native
-- backends. Catching it at the Core level — before codegen — turns a runtime
-- crash into a diagnostic.
--
-- Contract: this lint NEVER changes codegen or evaluation. It only produces
-- 'Diagnostic's (at 'SevWarning'), and it is deliberately conservative — it
-- fires only when the head is /statically and unambiguously/ a non-function
-- value, so it has no false positives on well-typed programs. Heads whose type
-- cannot be determined from Core alone (a local variable, a metavariable, a
-- projection, a nested match, …) are skipped rather than guessed at.
module Kappa.CoreLint
  ( lintCoreBodies
  , lintTermHeads
  ) where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Text (Text)

import Kappa.Builtins (prelUnit)
import Kappa.Core
import Kappa.CoreOps (spineOfTerm)
import Kappa.Diagnostic
import Kappa.Eval (EvalCtx (..), GlobalDef (..), Globals (..), MetaState, force, quote)
import Kappa.Source (noSpan)

-- | Lint every elaborated body in @bodies@ against the globals in @globals@
-- (with meta solutions @metas@). Returns one diagnostic per ill-typed
-- application head found. An empty result is the clean case.
--
-- The traversal is intentionally cheap: it is a pure structural fold over the
-- already-zonked Core, with a global-type lookup (and at most a 'force'\/
-- 'quote' of that type) per 'CGlob' application head.
lintCoreBodies ::
  Map GName GlobalDef ->
  MetaState ->
  Map GName Term ->
  [Diagnostic]
lintCoreBodies globals metas bodies =
  concatMap lintOne (Map.toList bodies)
  where
    ctx = EvalCtx (Globals globals) metas False Map.empty
    lintOne (g, body) = lintTermHeads ctx (gnameText g) body

-- | The core walk: report every application SPINE in @body@ whose head is
-- statically a non-function value. @who@ names the enclosing definition (used
-- only in the diagnostic message).
--
-- A spine @f a₁ … aₙ@ is checked exactly once — at its outermost 'CApp' — by
-- splitting it with 'spineOfTerm' and classifying the head @f@, then recursing
-- into @f@ and each argument @aᵢ@ separately. We deliberately do NOT recurse
-- through the 'CApp' chain node-by-node, which would re-classify the same head
-- once per argument. The do-kernel ('CDo') carries no value-application heads
-- relevant to this property and is not descended into here.
lintTermHeads :: EvalCtx -> Text -> Term -> [Diagnostic]
lintTermHeads ctx who = go
  where
    go t = case t of
      CApp {} ->
        let (hd, args) = spineOfTerm t
            here = case classifyHead ctx hd of
              Just reason -> [nonFunctionHeadDiag who reason]
              Nothing -> []
         in here ++ go hd ++ concatMap (go . snd) args
      CVar _ -> []
      CLocal _ _ -> []
      CGlob _ -> []
      CLam _ _ _ b -> go b
      CPi _ _ _ _ a b -> go a ++ go b
      CUniverseLift _ _ _ t' -> go t'
      CSchemaLift _ _ _ _ _ _ sourceArguments targetArguments t' ->
        concatMap go sourceArguments ++ concatMap go targetArguments ++ go t'
      CSort _ -> []
      CLevel _ -> []
      CLit _ -> []
      CCtor _ _ as -> concatMap go as
      CMatch s _ alts -> go s ++ concatMap goAlt alts
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
      CDo _ items -> concatMap goItem items
      CSealE _ e -> go e
      CSigT _ e -> go e
      CThunkE e -> go e
      CLazyE e -> go e
      CForceE e -> go e
      CIf a b c -> go a ++ go b ++ go c
      CQuote _ slots -> concatMap go slots
    goAlt (CaseAlt _ gd b) = maybe [] go gd ++ go b

    goItem = \case
      KBind _ _ action _ -> go action
      KLet _ _ value -> go value
      KLetQ _ value mElse -> go value ++ maybe [] (go . snd) mElse
      KExpr term -> go term
      KVarItem _ initial action _ -> go initial ++ go action
      KAssign root _ value action _ -> go root ++ go value ++ go action
      KReturn term -> go term
      KBreak {} -> []
      KContinue {} -> []
      KWhile _ condition body mElse ->
        goCondition condition ++ concatMap goItem body ++ maybe [] (concatMap goItem) mElse
      KFor _ _ source body mElse ->
        go source ++ concatMap goItem body ++ maybe [] (concatMap goItem) mElse
      KIf alternatives mElse ->
        concatMap (\(condition, body) -> go condition ++ concatMap goItem body) alternatives
          ++ maybe [] (concatMap goItem) mElse
      KDefer _ action -> go action
      KUsing _ acquire release -> go acquire ++ go release
      KSubDo _ body -> concatMap goItem body

    goCondition = \case
      KCondPure condition -> go condition
      KCondAction condition -> go condition

-- | Decide whether @hd@, used as the head of a value application, is
-- /statically/ a non-function value. Returns 'Just' a human-readable reason
-- when it is provably bad, and 'Nothing' when the head is either fine or its
-- type cannot be determined from Core alone (in which case we do not guess).
classifyHead :: EvalCtx -> Term -> Maybe Text
classifyHead ctx = \case
  -- A saturated constructor is a data VALUE, not a function. Well-typed Core
  -- never applies one directly (constructor application is eta-expanded to a
  -- lambda over runtime fields); a bare 'CCtor' head is the bug.
  CCtor g _ _ -> Just ("the saturated constructor '" <> gnameText g <> "' is a value, not a function")
  -- Manifest value\/type forms that obviously cannot be applied.
  CLit _ -> Just "a literal is a value, not a function"
  CRecordV _ -> Just "a record value is not a function"
  CRecordT _ -> Just "a record type is not a function"
  CVariantT _ -> Just "a variant type is not a function"
  CInject _ _ -> Just "a variant injection is a value, not a function"
  CSort _ -> Just "a sort ('Type') is not a function"
  -- A global head: its callability is decided by its DECLARED type. We only
  -- flag it when that type is unambiguously a non-function (e.g. 'Unit'),
  -- which is exactly the erased\/unit-valued head behind the 'kapp(unit,…)'
  -- crash. Polymorphic or neutral types are left alone.
  CGlob g -> case Map.lookup g (globalsMap (ecGlobals ctx)) of
    Just gd
      | isNonFunctionType ctx (gdType gd) ->
          Just ("the global '" <> gnameText g <> "' has a non-function type, so it cannot be applied")
    _ -> Nothing
  -- Everything else (a variable, a meta, a projection, a nested match, a
  -- lambda — which IS a function — …) is not a static non-function head.
  _ -> Nothing

-- | Is @ty@ (a global's declared type, as a 'Value') statically a
-- non-function? We strip leading implicit/Pi binders by quoting and looking
-- at the head: an explicit 'CPi' anywhere in the spine means "callable", so
-- we answer 'False'. We answer 'True' only for a concrete, manifestly
-- non-function head — a known nullary type like 'Unit', or 'Type'. A neutral
-- head (a type variable, an unsolved meta, or an applied type constructor) is
-- treated as POSSIBLY a function and never flagged.
isNonFunctionType :: EvalCtx -> Value -> Bool
isNonFunctionType ctx ty0 = case force ctx ty0 of
  VPi {} -> False
  v ->
    -- not a Pi at the head; quote and inspect the (de Bruijn) Term head
    case stripImplicitPis (quote ctx 0 v) of
      CPi {} -> False -- a residual explicit function arrow → callable
      CSort _ -> True -- 'Type u' is not a value-application head
      CGlob g -> g == prelUnit -- the canonical erased/unit type
      _ -> False -- variable / meta / applied ctor → don't guess

-- | Drop leading 'CPi' binders, returning the result head term. (Both icits
-- are stripped: an all-implicit-prefixed function with NO explicit arrow is
-- still not value-callable, but such shapes are vanishingly rare and we err
-- toward not flagging.)
stripImplicitPis :: Term -> Term
stripImplicitPis (CPi Impl _ _ _ _ b) = stripImplicitPis b
stripImplicitPis t = t

-- | The lint's diagnostic. 'SevWarning' so it is observe-only — it never
-- fails a build or perturbs a conformance fixture's error count.
nonFunctionHeadDiag :: Text -> Text -> Diagnostic
nonFunctionHeadDiag who reason =
  diag
    SevWarning
    StageElaborate
    "W_BACKENDIR_NON_FUNCTION_HEAD"
    (Just "kappa-hs.backendir.non-function-head")
    noSpan
    ( "in '" <> who <> "': a value application has a non-function head — "
        <> reason
        <> " (KBackendIR Stage 0 lint; this would lower to an ill-typed 'kapp')"
    )
