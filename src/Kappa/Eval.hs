-- | Normalization by evaluation and definitional equality (Spec §31.1).
--
-- Conversion includes β, δ (transparent conversion-reducible definitions
-- only), ι (match\/if reduction on known scrutinees), record\/variant
-- canonical-form equality, suspension reduction (@force (thunk e) ↦ e@),
-- and function η. Quantities participate in Pi identity. Normalization is
-- fuel-bounded for safety but only ever answers "equal" soundly.
module Kappa.Eval
  ( Globals (..)
  , GlobalDef (..)
  , MetaState
  , emptyMetas
  , EvalCtx (..)
  , RigidFact (..)
  , eval
  , evalApp
  , force
  , quote
  , convertible
  , matchPat
  , vapp
  , evalPurePrim
  , evalPrimCtx
  , lookupEnv
  ) where

import Data.Bits (xor)
import qualified Data.ByteString as BS
import Data.Char (chr, ord)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.Text.Encoding.Error as TEE
import Data.Word (Word64, Word8)
import GHC.Float (castDoubleToWord64)
import Kappa.Core
import Kappa.Source (ModuleName (..))
import Kappa.Unicode
  ( NormForm (..)
  , graphemeClusters
  , isSingleGrapheme
  , normalizeText
  , sentenceChunks
  , wordChunks
  )
import Numeric (showHex)

-- | One global definition.
data GlobalDef = GlobalDef
  { gdType :: !Value
  , gdValue :: !(Maybe Value)
  -- ^ 'Nothing' for primitives\/postulates and opaque-at-use-site defs.
  , gdReducible :: !Bool
  -- ^ Conversion-reducible (§15.1): may δ-unfold during conversion.
  }

newtype Globals = Globals {globalsMap :: Map GName GlobalDef}

type MetaState = Map MetaId (Maybe Value)

emptyMetas :: MetaState
emptyMetas = Map.empty

-- | Branch-local fact about a rigid variable, established by the
-- enclosing match case (§7.4.1 flow refinement at conversion level):
-- either solved to a constructor value, or known to lack constructors.
data RigidFact = FactIs !Value | FactNot ![GName]

-- | Evaluation context: globals plus current meta solutions.
data EvalCtx = EvalCtx
  { ecGlobals :: !Globals
  , ecMetas :: !MetaState
  , ecRuntime :: !Bool
  -- ^ Runtime evaluation (§32.1): every global with a value unfolds,
  -- with a deep fuel budget. Conversion-time forcing (False) unfolds
  -- only conversion-reducible definitions and stays tightly bounded.
  , ecFacts :: !(Map Int RigidFact)
  -- ^ Branch-local facts about rigid levels (dependent-match
  -- normalization; see Check.checkMatchPlain).
  }

lookupGlobal :: EvalCtx -> GName -> Maybe GlobalDef
lookupGlobal ctx g = Map.lookup g (globalsMap (ecGlobals ctx))

-- ── Evaluation ───────────────────────────────────────────────────────

-- | Checked de Bruijn lookup. An out-of-range index is an elaborator
-- bug; fail with context instead of a bare 'Prelude.!!' pattern error.
lookupEnv :: Int -> Env -> Value
lookupEnv i env = case drop i env of
  v : _ -> v
  [] ->
    error
      ("Kappa.Eval.lookupEnv: internal error: de Bruijn index " ++ show i
         ++ " out of range (environment has " ++ show (length env) ++ " entries)")

eval :: EvalCtx -> Env -> Term -> Value
eval ctx env = \case
  CVar i -> lookupEnv i env
  -- primitives quoted by 'quote' round-trip back to 'VPrim'
  CGlob g@(GName m p) -> if m == primModule then VPrim p [] else VGlobN g []
  CLam ic q n body -> VLam ic q n (Closure env body)
  CPi ic q n a b -> VPi ic q n (eval ctx env a) (Closure env b)
  CApp ic f a -> vapp ctx (eval ctx env f) ic (eval ctx env a)
  CSort n -> VSort n
  CLit l -> VLit l
  CCtor g args -> VCtor g (map (eval ctx env) args)
  CMatch scrut alts ->
    reduceMatch ctx (eval ctx env scrut) alts env
  CRecordT fs -> VRecordT [(n, eval ctx env t) | (n, t) <- fs]
  CRecordV fs -> VRecordV [(n, eval ctx env t) | (n, t) <- fs]
  CProj e f -> vproj ctx (eval ctx env e) f
  CVariantT ms -> VVariantT (map (eval ctx env) ms)
  CInject tag e -> VInject tag (eval ctx env e)
  CLet _ _ _ rhs body -> eval ctx (eval ctx env rhs : env) body
  CLetRec _ _ _ rhs body ->
    -- recursive local definition: tie the knot lazily (the rhs is a
    -- lambda, so forcing the binding terminates)
    let env' = eval ctx env' rhs : env in eval ctx env' body
  CMeta m -> case Map.lookup m (ecMetas ctx) of
    Just (Just v) -> v
    _ -> VFlex m []
  CDo items -> VDoV items env
  CSealE ls e -> VSealV ls (eval ctx env e)
  CSigT ls e -> VSigT ls (eval ctx env e)
  CThunkE e -> VThunkV (Closure env e)
  CLazyE e -> VLazyV (Closure env e)
  CForceE e -> vforce ctx (eval ctx env e)
  CIf c t f ->
    case force ctx (eval ctx env c) of
      VCtor (GName _ "True") [] -> eval ctx env t
      VCtor (GName _ "False") [] -> eval ctx env f
      v -> VIfN v (Closure env t) (Closure env f)

closApply :: EvalCtx -> Closure -> Value -> Value
closApply ctx (Closure env body) v = eval ctx (v : env) body

vapp :: EvalCtx -> Value -> Icit -> Value -> Value
vapp ctx fv ic av = case fv of
  VLam _ _ _ clo -> closApply ctx clo av
  VRigid l sp -> VRigid l (sp ++ [(ic, av)])
  VFlex m sp -> VFlex m (sp ++ [(ic, av)])
  VGlobN g sp -> VGlobN g (sp ++ [(ic, av)])
  -- implicit arguments are erased at runtime for constructors and
  -- primitives (§31.2); neutral globals keep them (types).
  VCtor g args
    | ic == Impl -> VCtor g args
    | otherwise -> VCtor g (args ++ [av])
  VPrim p args
    -- an implicit argument to a stuck application must not be erased;
    -- nest another marker so 'force' can replay it faithfully
    | isStuckMarker p, ic == Impl -> VPrim (stuckAppMarker Impl) [fv, av]
    | ic == Impl -> VPrim p args
    | otherwise ->
        let args' = args ++ [av]
         in case evalPrimCtx ctx p (map (force ctx) args') of
              Just v -> v
              Nothing -> VPrim p args'
  -- stuck application: keep the icit so 'force' can re-apply once the
  -- head becomes canonical (e.g. a solved meta's dictionary projection).
  _ -> VPrim (stuckAppMarker ic) [fv, av]

stuckAppMarker :: Icit -> Text
stuckAppMarker = \case
  Expl -> "__stuck_app"
  Impl -> "__stuck_appI"

isStuckMarker :: Text -> Bool
isStuckMarker p = p == "__stuck_app" || p == "__stuck_appI"

evalApp :: EvalCtx -> Value -> [(Icit, Value)] -> Value
evalApp ctx = foldl (\f (ic, a) -> vapp ctx f ic a)

vproj :: EvalCtx -> Value -> Text -> Value
vproj ctx v f = case force ctx v of
  VRecordV fs | Just x <- lookup f fs -> x
  -- §13.2.10: projection computes through a seal except for opaque
  -- members, whose defining equations are hidden (runtime projections
  -- of retained ordinary fields always compute)
  VSealV ls r | f `notElem` ls || ecRuntime ctx -> vproj ctx r f
  v' -> VProjN v' f

vforce :: EvalCtx -> Value -> Value
vforce ctx v = case force ctx v of
  VThunkV clo -> closApply ctx clo (VRecordV []) `seq` runSusp clo
  VLazyV clo -> runSusp clo
  v' -> VPrim "force" [v']
  where
    runSusp (Closure env body) = eval ctx env body

-- | Unfold solved metas and (reducible) global heads at the value root,
-- and re-reduce values that got stuck on a then-unsolved metavariable
-- (projections, applications, ifs and matches re-fire once their head
-- becomes canonical).
force :: EvalCtx -> Value -> Value
force ctx = go (if ecRuntime ctx then 200000000 else 1000 :: Int)
  where
    go 0 v = v
    go fuel v = case v of
      VFlex m sp
        | Just (Just sol) <- Map.lookup m (ecMetas ctx) ->
            go (fuel - 1) (evalApp ctx sol sp)
      -- branch-local dependent-match solution for a rigid (§7.4.1)
      VRigid l []
        | Just (FactIs sol) <- Map.lookup l (ecFacts ctx) ->
            go (fuel - 1) sol
      VGlobN g sp
        | Just gd <- lookupGlobal ctx g
        , Just body <- gdValue gd
        , ecRuntime ctx || gdReducible gd || isPrimRoot body ->
            -- runtime is strict (§32.1): force arguments before entry so
            -- deep recursion does not pile up unreduced argument chains
            let sp' =
                  if ecRuntime ctx
                    then [(ic, go (fuel - 1) a) | (ic, a) <- sp]
                    else sp
             in go (fuel - 1) (evalApp ctx body sp')
      -- a stuck application: explicit over-applications append to the
      -- marker's argument list, so replay the head against all of them
      VPrim p (f : a : rest)
        | Just ic <- stuckAppIcit p
        , f' <- go (fuel - 1) f
        , reapplicable f' ->
            go (fuel - 1) (foldl (\acc x -> vapp ctx acc Expl x) (vapp ctx f' ic a) rest)
      VPrim p sp
        | Just v' <- evalPrimCtx ctx p (map (go (fuel - 1)) sp) -> go (fuel - 1) v'
      VProjN inner fld ->
        -- §13.2.10: a projection re-fires through seal layers unless
        -- the member is opaque (always computes at runtime)
        let unseal x = case x of
              VSealV ls r | ecRuntime ctx || fld `notElem` ls -> unseal (go (fuel - 1) r)
              _ -> x
         in case unseal (go (fuel - 1) inner) of
              VRecordV fs | Just x <- lookup fld fs -> go (fuel - 1) x
              _ -> v
      VIfN c t f -> case go (fuel - 1) c of
        VCtor (GName _ "True") [] -> go (fuel - 1) (closRun t)
        VCtor (GName _ "False") [] -> go (fuel - 1) (closRun f)
        _ -> v
      VMatchN scrut alts env
        | Just v' <- tryReduceMatch ctx scrut alts env ->
            go (fuel - 1) v'
      _ -> v
      where
        isPrimRoot = \case
          VPrim _ [] -> True
          _ -> False
        stuckAppIcit = \case
          "__stuck_app" -> Just Expl
          "__stuck_appI" -> Just Impl
          _ -> Nothing
        -- shapes 'vapp' can make progress on (avoids rebuilding the same
        -- stuck application forever)
        reapplicable = \case
          VLam {} -> True
          VRigid {} -> True
          VFlex {} -> True
          VGlobN {} -> True
          VCtor {} -> True
          VPrim p _ | p /= "__stuck_app" && p /= "__stuck_appI" -> True
          _ -> False
        closRun (Closure env body) = eval ctx env body

-- ι-reduction of match when the scrutinee is canonical.
reduceMatch :: EvalCtx -> Value -> [CaseAlt] -> Env -> Value
reduceMatch ctx scrut alts env =
  case tryReduceMatch ctx scrut alts env of
    Just v -> v
    Nothing -> VMatchN scrut alts env

-- | 'Just' iff some alternative definitely fires (used by 'force' to
-- re-reduce matches stuck on metavariables).
tryReduceMatch :: EvalCtx -> Value -> [CaseAlt] -> Env -> Maybe Value
tryReduceMatch ctx scrut alts env = tryAlts alts
  where
    scrut' = force ctx scrut
    tryAlts [] = Nothing
    tryAlts (CaseAlt pat g body : rest) =
      case matchPat ctx pat scrut' of
        Just binds ->
          let env' = reverse binds ++ env
           in case g of
                Nothing -> Just (eval ctx env' body)
                Just gd -> case force ctx (eval ctx env' gd) of
                  VCtor (GName _ "True") [] -> Just (eval ctx env' body)
                  VCtor (GName _ "False") [] -> tryAlts rest
                  _ -> Nothing -- stuck guard: whole match stuck
        Nothing
          | definitelyNoMatch pat scrut' -> tryAlts rest
          | otherwise -> Nothing -- stuck

    -- Recursive: a definite mismatch in any nested sub-pattern rules
    -- out the whole alternative (e.g. @_ :: y :: _@ vs @1 :: Nil@).
    definitelyNoMatch pat v0 = case (pat, force ctx v0) of
      -- a rigid known to lack the constructor cannot match it (§7.4.1)
      (CPCtor g _, VRigid l _)
        | Just (FactNot gs) <- Map.lookup l (ecFacts ctx) -> g `elem` gs
      (CPCtor g ps, VCtor g' args) ->
        g /= g'
          || ( length ps <= length args
                 && or
                   [ definitelyNoMatch p a
                   | (p, a) <- zip ps (drop (length args - length ps) args)
                   ]
             )
      (CPLit l, VLit l') -> l /= l'
      (CPTuple ps, VRecordV fs)
        | length ps == length fs ->
            or [definitelyNoMatch p a | (p, (_, a)) <- zip ps fs]
      (CPRecord pfs _, VRecordV fs) ->
        or [maybe False (definitelyNoMatch p) (lookup n fs) | (n, p) <- pfs]
      (CPInject t p, VInject t' x) -> t /= t' || definitelyNoMatch p x
      (CPInjectRest excl, VInject t _) -> t `elem` excl
      (CPOr ps, v) -> all (`definitelyNoMatch` v) ps
      (CPAs _ p, v) -> definitelyNoMatch p v
      _ -> False

-- | First-order pattern matching on values. 'Nothing' means "did not
-- match or could not decide" — callers must distinguish via
-- 'definitelyNoMatch' for soundness during conversion.
matchPat :: EvalCtx -> CorePat -> Value -> Maybe [Value]
matchPat ctx pat v0 =
  let v = force ctx v0
   in case (pat, v) of
        (CPWild, _) -> Just []
        (CPVar _, _) -> Just [v]
        (CPLit l, VLit l') | l == l' -> Just []
        (CPCtor g ps, VCtor g' args)
          | g == g', length ps <= length args ->
              concatM [matchPat ctx p a | (p, a) <- zip ps (drop (length args - length ps) args)]
        (CPTuple ps, VRecordV fs)
          | length ps == length fs ->
              concatM [matchPat ctx p a | (p, (_, a)) <- zip ps fs]
        (CPRecord pfs mrest, VRecordV fs) -> do
          sub <- concatM [maybe Nothing (matchPat ctx p) (lookup n fs) | (n, p) <- pfs]
          case mrest of
            Just nm | not (T.null nm) ->
              -- bind the remaining fields as a narrower record (§17.2.5)
              Just (sub ++ [VRecordV [(n, x) | (n, x) <- fs, n `notElem` map fst pfs]])
            _ -> Just sub
        (CPInject t p, VInject t' x) | t == t' -> matchPat ctx p x
        (CPInjectRest excl, VInject t _) | t `notElem` excl -> Just [v]
        (CPOr ps, _) -> firstJust [matchPat ctx p v | p <- ps]
        (CPAs _ p, _) -> (v :) <$> matchPat ctx p v
        _ -> Nothing
  where
    concatM = fmap concat . sequence
    firstJust xs = case [x | Just x <- xs] of
      (x : _) -> Just x
      [] -> Nothing

-- ── Quotation ────────────────────────────────────────────────────────

-- | Quotation-time forcing: resolve solved metavariables and replay
-- applications stuck on them, but do NOT δ-unfold globals. Quoting must
-- terminate on recursive definitions and produce small, re-evaluable
-- terms (zonking depends on this; unfolding a recursive dictionary here
-- would diverge).
forceQ :: EvalCtx -> Value -> Value
forceQ ctx = go (1000 :: Int)
  where
    go :: Int -> Value -> Value
    go 0 v = v
    go fuel v = case v of
      VFlex m sp
        | Just (Just sol) <- Map.lookup m (ecMetas ctx) ->
            go (fuel - 1) (evalApp ctx sol sp)
      VPrim p (f : a : rest)
        | p == "__stuck_app" || p == "__stuck_appI"
        , f' <- go (fuel - 1) f
        , progressed f' ->
            go (fuel - 1) (foldl (\acc x -> vapp ctx acc Expl x) (vapp ctx f' (markerIcit p) a) rest)
      VPrim p sp
        | Just v' <- evalPrimCtx ctx p (map (go (fuel - 1)) sp) -> go (fuel - 1) v'
      _ -> v
      where
        markerIcit p = if p == "__stuck_appI" then Impl else Expl
        progressed = \case
          VLam {} -> True
          VRigid {} -> True
          VFlex {} -> True
          VGlobN {} -> True
          VCtor {} -> True
          VPrim p _ | p /= "__stuck_app" && p /= "__stuck_appI" -> True
          _ -> False

quote :: EvalCtx -> Int -> Value -> Term
quote ctx lvl v = case forceQ ctx v of
  VRigid l sp -> quoteSpine (CVar (lvl - 1 - l)) sp
  VFlex m sp -> quoteSpine (CMeta m) sp
  VGlobN g sp -> quoteSpine (CGlob g) sp
  VLam ic q n clo ->
    CLam ic q n (quote ctx (lvl + 1) (closApply ctx clo (VRigid lvl [])))
  VPi ic q n a clo ->
    CPi ic q n (quote ctx lvl a) (quote ctx (lvl + 1) (closApply ctx clo (VRigid lvl [])))
  VSort n -> CSort n
  VLit l -> CLit l
  VCtor g args -> CCtor g (map (quote ctx lvl) args)
  VRecordT fs -> CRecordT [(n, quote ctx lvl t) | (n, t) <- fs]
  VRecordV fs -> CRecordV [(n, quote ctx lvl t) | (n, t) <- fs]
  VVariantT ms -> CVariantT (map (quote ctx lvl) ms)
  VInject t x -> CInject t (quote ctx lvl x)
  VMatchN scrut alts env ->
    -- Stuck match: quote scrutinee, keep alts with their env baked in
    -- only when env is empty; otherwise approximate via fresh rigids.
    CMatch (quote ctx lvl scrut) (map (quoteAlt env) alts)
  VProjN e f -> CProj (quote ctx lvl e) f
  VSealV ls x -> CSealE ls (quote ctx lvl x)
  VSigT ls x -> CSigT ls (quote ctx lvl x)
  VDoV items _ -> CDo items
  VThunkV (Closure env body) -> CThunkE (quoteUnder env body)
  VLazyV (Closure env body) -> CLazyE (quoteUnder env body)
  VIfN c t f ->
    -- branch closures bind nothing: run them in their own env
    CIf
      (quote ctx lvl c)
      (quote ctx lvl (closRun t))
      (quote ctx lvl (closRun f))
  VPrim p args -> foldl (\f a -> CApp Expl f (quote ctx lvl a)) (CGlob (GName primModule p)) args
  -- runtime-only values; never legitimately quoted, render opaquely
  VRef _ -> CGlob (GName primModule "__ref")
  VIOAction p args -> foldl (\f a -> CApp Expl f (quote ctx lvl a)) (CGlob (GName primModule p)) args
  where
    quoteSpine = foldl (\f (ic, a) -> CApp ic f (quote ctx lvl a))
    quoteAlt _ alt = alt
    closRun (Closure env body) = eval ctx env body
    quoteUnder env body
      | null env = body
      | otherwise = body -- conservative; suspensions compare by closure body

-- ── Conversion ───────────────────────────────────────────────────────

-- | Definitional equality (§31.1). Sound; may conservatively answer
-- 'False' on stuck terms it cannot decide.
convertible :: EvalCtx -> Int -> Value -> Value -> Bool
convertible ctx = go (200 :: Int)
  where
    go :: Int -> Int -> Value -> Value -> Bool
    go 0 _ _ _ = False
    go fuel lvl v1 v2 = case (force ctx v1, force ctx v2) of
      (VSort a, VSort b) -> a == b
      (VLit a, VLit b) -> a == b
      (VPi i1 q1 _ a1 b1, VPi i2 q2 _ a2 b2) ->
        i1 == i2
          && q1 == q2 -- quantities are part of function-type identity
          && go (fuel - 1) lvl a1 a2
          && goClos fuel lvl b1 b2
      (VLam i1 _ _ b1, VLam i2 _ _ b2)
        | i1 == i2 -> goClos fuel lvl b1 b2
      -- η for functions
      (VLam i _ _ b, f) ->
        let x = VRigid lvl []
         in go (fuel - 1) (lvl + 1) (closApply ctx b x) (vapp ctx f i x)
      (f, VLam i _ _ b) ->
        let x = VRigid lvl []
         in go (fuel - 1) (lvl + 1) (vapp ctx f i x) (closApply ctx b x)
      (VRigid l1 sp1, VRigid l2 sp2) -> l1 == l2 && goSpine fuel lvl sp1 sp2
      (VFlex m1 sp1, VFlex m2 sp2) -> m1 == m2 && goSpine fuel lvl sp1 sp2
      (VGlobN g1 sp1, VGlobN g2 sp2)
        | g1 == g2, goSpine fuel lvl sp1 sp2 -> True
      -- unfold non-reducible-blocked globals only if reducible (force
      -- already unfolded those); different heads -> try nothing more
      (VCtor g1 a1, VCtor g2 a2) ->
        g1 == g2 && length a1 == length a2 && and (zipWith (go (fuel - 1) lvl) a1 a2)
      (VRecordT f1, VRecordT f2) ->
        map fst f1 == map fst f2 && and (zipWith (go (fuel - 1) lvl) (map snd f1) (map snd f2))
      (VRecordV f1, VRecordV f2) ->
        map fst f1 == map fst f2 && and (zipWith (go (fuel - 1) lvl) (map snd f1) (map snd f2))
      -- record η: zero-field record ≡ Unit value
      (VRecordV [], VCtor (GName _ "Unit") []) -> True
      (VCtor (GName _ "Unit") [], VRecordV []) -> True
      (VVariantT m1, VVariantT m2) ->
        length m1 == length m2 && and (zipWith (go (fuel - 1) lvl) m1 m2)
      (VInject t1 x1, VInject t2 x2) -> t1 == t2 && go (fuel - 1) lvl x1 x2
      (VProjN e1 f1, VProjN e2 f2) -> f1 == f2 && go (fuel - 1) lvl e1 e2
      -- §13.2.10: seal is pure and non-generative; sealed packages are
      -- equal iff the underlying records are (seal e as S ≡ e)
      (VSealV _ x1, y1) -> go (fuel - 1) lvl x1 y1
      (x1, VSealV _ y1) -> go (fuel - 1) lvl x1 y1
      (VSigT l1 x1, VSigT l2 x2) -> l1 == l2 && go (fuel - 1) lvl x1 x2
      (VIfN c1 t1 f1, VIfN c2 t2 f2) ->
        -- if-branch closures bind nothing
        go (fuel - 1) lvl c1 c2
          && go (fuel - 1) lvl (closRun t1) (closRun t2)
          && go (fuel - 1) lvl (closRun f1) (closRun f2)
      (VPrim p1 a1, VPrim p2 a2) ->
        p1 == p2 && length a1 == length a2 && and (zipWith (go (fuel - 1) lvl) a1 a2)
      _ -> False
      where
        closRun (Closure env body) = eval ctx env body
        goClos fl l c1 c2 =
          let x = VRigid l []
           in go (fl - 1) (l + 1) (closApply ctx c1 x) (closApply ctx c2 x)
        goSpine fl l sp1 sp2 =
          length sp1 == length sp2
            && and (zipWith (\(_, a) (_, b) -> go (fl - 1) l a b) sp1 sp2)

-- | Pure primitive reduction shared by conversion and runtime.
evalPurePrim :: Text -> [Value] -> Maybe Value
evalPurePrim p args = case (p, args) of
  ("addInt", [VLit (LitInt a), VLit (LitInt b)]) -> int (a + b)
  ("subInt", [VLit (LitInt a), VLit (LitInt b)]) -> int (a - b)
  ("mulInt", [VLit (LitInt a), VLit (LitInt b)]) -> int (a * b)
  ("divInt", [VLit (LitInt a), VLit (LitInt b)]) | b /= 0 -> int (a `quot` b)
  ("modInt", [VLit (LitInt a), VLit (LitInt b)]) | b /= 0 -> int (a `rem` b)
  ("negInt", [VLit (LitInt a)]) -> int (negate a)
  ("eqInt", [VLit (LitInt a), VLit (LitInt b)]) -> bool (a == b)
  ("ltInt", [VLit (LitInt a), VLit (LitInt b)]) -> bool (a < b)
  ("leInt", [VLit (LitInt a), VLit (LitInt b)]) -> bool (a <= b)
  ("addDouble", [VLit (LitDouble a), VLit (LitDouble b)]) -> dbl (a + b)
  ("subDouble", [VLit (LitDouble a), VLit (LitDouble b)]) -> dbl (a - b)
  ("mulDouble", [VLit (LitDouble a), VLit (LitDouble b)]) -> dbl (a * b)
  ("divDouble", [VLit (LitDouble a), VLit (LitDouble b)]) -> dbl (a / b)
  ("negDouble", [VLit (LitDouble a)]) -> dbl (negate a)
  ("eqDouble", [VLit (LitDouble a), VLit (LitDouble b)]) -> bool (identicalIEEE a b)
  ("ltDouble", [VLit (LitDouble a), VLit (LitDouble b)]) -> bool (a < b)
  ("floatEq", [VLit (LitDouble a), VLit (LitDouble b)]) -> bool (a == b)
  ("eqStr", [VLit (LitStr a), VLit (LitStr b)]) -> bool (a == b)
  ("ltStr", [VLit (LitStr a), VLit (LitStr b)]) -> bool (a < b)
  ("eqScalar", [VLit (LitScalar a), VLit (LitScalar b)]) -> bool (a == b)
  ("ltScalar", [VLit (LitScalar a), VLit (LitScalar b)]) -> bool (a < b)
  -- §6.5/§29.5 text atoms: Byte/Bytes/Grapheme comparison + rendering
  ("eqByte", [VLit (LitByte a), VLit (LitByte b)]) -> bool (a == b)
  ("ltByte", [VLit (LitByte a), VLit (LitByte b)]) -> bool (a < b)
  ("showByte", [VLit (LitByte a)]) ->
    str (T.pack ("b'\\x" <> pad2 (showHex a "") <> "'"))
  ("eqBytes", [VLit (LitBytes a), VLit (LitBytes b)]) -> bool (a == b)
  ("ltBytes", [VLit (LitBytes a), VLit (LitBytes b)]) -> bool (a < b) -- lexicographic by byte
  ("showBytes", [VLit (LitBytes a)]) ->
    str (T.pack ("0x" <> concatMap (\w -> pad2 (showHex w "")) (BS.unpack a)))
  ("eqGrapheme", [VLit (LitGrapheme a), VLit (LitGrapheme b)]) -> bool (a == b) -- exact scalars
  ("showGrapheme", [VLit (LitGrapheme a)]) -> str ("g'" <> a <> "'")
  -- §29.4 std.unicode internals
  ("__utf8Bytes", [VLit (LitStr s)]) -> bytes (TE.encodeUtf8 s)
  ("__utf8Valid", [VLit (LitBytes bs)]) ->
    bool (either (const False) (const True) (TE.decodeUtf8' bs))
  ("__decodeUtf8Lossy", [VLit (LitBytes bs)]) ->
    str (TE.decodeUtf8With TEE.lenientDecode bs)
  ("__byteLength", [VLit (LitStr s)]) -> int (fromIntegral (BS.length (TE.encodeUtf8 s)))
  ("__uniScalarValue", [VLit (LitScalar c)]) -> int (fromIntegral (ord c))
  ("__scalarInRange", [VLit (LitInt n)]) ->
    bool (n >= 0 && n <= 0x10FFFF && not (n >= 0xD800 && n <= 0xDFFF))
  ("__scalarOfValue", [VLit (LitInt n)])
    | n >= 0 && n <= 0x10FFFF && not (n >= 0xD800 && n <= 0xDFFF) ->
        Just (VLit (LitScalar (chr (fromIntegral n))))
  ("__scalarToString", [VLit (LitScalar c)]) -> str (T.singleton c)
  ("__stringScalars", [VLit (LitStr s)]) ->
    Just (listV [VLit (LitScalar c) | c <- T.unpack s])
  ("__scalarCount", [VLit (LitStr s)]) -> int (fromIntegral (T.length s))
  ("__graphemeToString", [VLit (LitGrapheme g)]) -> str g
  ("__graphemeValid", [VLit (LitStr s)]) -> bool (isSingleGrapheme s)
  ("__graphemeOfString", [VLit (LitStr s)])
    | isSingleGrapheme s -> Just (VLit (LitGrapheme s))
  ("__stringGraphemes", [VLit (LitStr s)]) ->
    Just (listV [VLit (LitGrapheme g) | g <- graphemeClusters s])
  ("__graphemeCount", [VLit (LitStr s)]) ->
    int (fromIntegral (length (graphemeClusters s)))
  ("__normalize", [VLit (LitInt form), VLit (LitStr s)]) ->
    let f = case form of
          0 -> NFC
          1 -> NFD
          2 -> NFKC
          _ -> NFKD
     in str (normalizeText f s)
  ("__caseFold", [VLit (LitStr s)]) -> str (T.toCaseFold s)
  ("__stringWords", [VLit (LitStr s)]) ->
    Just (listV [VLit (LitStr w) | w <- wordChunks s])
  ("__stringSentences", [VLit (LitStr s)]) ->
    Just (listV [VLit (LitStr w) | w <- sentenceChunks s])
  ("__byteToNat", [VLit (LitByte w)]) -> int (fromIntegral w)
  -- §29.3 hash mixing: FNV-1a over a 64-bit lane, deterministic per run
  ("__hashMixInt", [VLit (LitInt s), VLit (LitInt v)]) -> int (fnvMixInteger s v)
  ("__hashMixDouble", [VLit (LitInt s), VLit (LitDouble d)]) ->
    int (fnvMixInteger s (toInteger (castDoubleToWord64 d)))
  ("__hashMixString", [VLit (LitInt s), VLit (LitStr t)]) ->
    int (fnvMixBytes s (TE.encodeUtf8 t))
  ("__hashMixBytes", [VLit (LitInt s), VLit (LitBytes bs)]) ->
    int (fnvMixBytes s bs)
  ("stringAppend", [VLit (LitStr a), VLit (LitStr b)]) -> Just (VLit (LitStr (a <> b)))
  ("showInt", [VLit (LitInt a)]) -> str (T.pack (show a))
  ("primitiveIntToString", [VLit (LitInt a)]) -> str (T.pack (show a))
  ("showDouble", [VLit (LitDouble a)]) -> str (T.pack (show a))
  ("showStringLit", [VLit (LitStr a)]) -> str (T.pack (show a))
  ("showScalar", [VLit (LitScalar a)]) -> str (T.pack (show a))
  ("intToDouble", [VLit (LitInt a)]) -> dbl (fromInteger a)
  ("natOfInt", [VLit (LitInt a)]) -> int a
  ("natToInt", [VLit (LitInt a)]) -> int a
  -- partial: a negative Int has no Nat image; the application stays
  -- stuck and is reported as a runtime error
  ("intToNat", [VLit (LitInt a)]) | a >= 0 -> int a
  -- discard a (linear) value: implicit type argument + the value
  ("unsafeConsume", [_, _]) -> Just (VCtor (GName (ModuleName ["std", "prelude"]) "Unit") [])
  -- §20 collection carriers are list-backed at runtime (§20.10.11
  -- as-if rule); conversion/wrapping is the identity on the element
  -- stream (modes, quantities, and orderedness are static metadata)
  ("__queryFromList", [v]) -> Just v
  ("__queryToList", [v]) -> Just v
  ("__setFromList", [v]) -> Just v
  ("__setToList", [v]) -> Just v
  ("__arrayFromList", [v]) -> Just v
  ("__arrayToList", [v]) -> Just v
  ("__mapFromEntries", [v]) -> Just v
  ("__mapToList", [v]) -> Just v
  _ -> Nothing
  where
    int = Just . VLit . LitInt
    dbl = Just . VLit . LitDouble
    str = Just . VLit . LitStr
    bytes = Just . VLit . LitBytes
    bool b = Just (VCtor (prelG (if b then "True" else "False")) [])
    prelG = GName (ModuleName ["std", "prelude"])
    listV = foldr (\x acc -> VCtor (prelG "::") [x, acc]) (VCtor (prelG "Nil") [])
    pad2 s = if length s < 2 then replicate (2 - length s) '0' ++ s else s
    -- FNV-1a over one 64-bit lane; integers mix their 8 low-endian bytes
    fnvMixByte :: Integer -> Word8 -> Integer
    fnvMixByte s w =
      let s64 = fromIntegral s :: Word64
       in fromIntegral ((s64 `xor` fromIntegral w) * 1099511628211)
    fnvMixBytes = BS.foldl' fnvMixByte
    fnvMixInteger s v =
      foldl fnvMixByte s [fromIntegral ((v `div` (256 ^ i)) `mod` 256) :: Word8 | i <- [0 .. 7 :: Int]]
    identicalIEEE a b = (a == b && (1 / a == 1 / b)) || (a /= a && b /= b)

-- | Context-aware primitive reduction: the pure table first, then the
-- §18.1 algebraic-effect kernel (whose continuations are ordinary
-- closure values, so the driver needs application).
evalPrimCtx :: EvalCtx -> Text -> [Value] -> Maybe Value
evalPrimCtx ctx p args = case evalPurePrim p args of
  Just v -> Just v
  Nothing -> evalEffPrim ctx p args

-- | The §30.2.2.7 effect kernel over the runtime 'Eff' tree
-- representation: @__EffPure v@ for a finished computation and
-- @__EffOp label op payload cont@ for a suspended operation, where
-- @cont@ is the captured continuation (a closure — re-entrant, so
-- multi-shot resumption per §32.2.14 is supported).
evalEffPrim :: EvalCtx -> Text -> [Value] -> Maybe Value
evalEffPrim ctx p args = case (p, args) of
  -- runPure : Eff <[ ]> a -> a (§18.1.14)
  ("runPure", [comp]) -> case force ctx comp of
    VCtor (GName _ "__EffPure") [v] -> Just v
    _ -> Nothing
  -- monadic bind over the tree (Eff is a Monad, §18.1.14)
  ("__effBind", [m, f]) -> case force ctx m of
    VCtor (GName _ "__EffPure") [v] -> Just (vapp ctx f Expl v)
    VCtor g@(GName _ "__EffOp") [l, op, a, cont] ->
      -- Op l op a (\x -> __effBind (cont x) f)
      Just (VCtor g [l, op, a, VLam Expl QW "x" (Closure [f, cont] bindBody)])
    _ -> Nothing
  -- __handleEff deep label ret ops comp (HandleShallow plus the
  -- §18.1.22 deep recursive driver)
  ("__handleEff", [deepV, label, ret, ops, comp]) -> case force ctx comp of
    VCtor (GName _ "__EffPure") [v] -> Just (vapp ctx ret Expl v)
    VCtor g@(GName _ "__EffOp") [l, opName, a, cont]
      | sameLabel (force ctx l) (force ctx label) ->
          -- nearest matching handler intercepts (§18.1.18); a deep
          -- handler's k reinstalls itself around the resumption
          case (force ctx opName, force ctx ops) of
            (VLit (LitStr opn), VRecordV fs)
              | Just clause <- lookup opn fs ->
                  let k
                        | isTrueV (force ctx deepV) = reinstall cont
                        | otherwise = cont
                   in Just (vapp ctx (vapp ctx clause Expl a) Expl k)
            _ -> Nothing
      | otherwise ->
          -- operations at other labels propagate outward unchanged,
          -- with this handler still installed inside the resumption
          Just (VCtor g [l, opName, a, reinstall cont])
    _ -> Nothing
    where
      reinstall cont = VLam Expl QW "x" (Closure [cont, ops, ret, label, deepV] handleBody)
  _ -> Nothing
  where
    effBindG = CGlob (GName (ModuleName ["std", "prelude"]) "__effBind")
    handleEffG = CGlob (GName (ModuleName ["std", "prelude"]) "__handleEff")
    appE = CApp Expl
    -- env [f, cont], binder x: __effBind (cont x) f
    bindBody = appE (appE effBindG (appE (CVar 2) (CVar 0))) (CVar 1)
    -- env [cont, ops, ret, label, deepV], binder x:
    -- __handleEff deepV label ret ops (cont x)
    handleBody =
      appE
        (appE (appE (appE (appE handleEffG (CVar 5)) (CVar 4)) (CVar 3)) (CVar 2))
        (appE (CVar 1) (CVar 0))
    sameLabel a b = case (a, b) of
      (VGlobN g1 [], VGlobN g2 []) -> g1 == g2
      (VCtor g1 [], VCtor g2 []) -> g1 == g2
      _ -> False
    isTrueV = \case
      VCtor (GName _ "True") [] -> True
      _ -> False
