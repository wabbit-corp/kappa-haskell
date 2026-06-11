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
  , eval
  , evalApp
  , force
  , quote
  , convertible
  , normalize
  , matchPat
  , vapp
  , evalPurePrim
  ) where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as T
import Kappa.Core
import Kappa.Source (ModuleName (..))

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

-- | Evaluation context: globals plus current meta solutions.
data EvalCtx = EvalCtx
  { ecGlobals :: !Globals
  , ecMetas :: !MetaState
  }

lookupGlobal :: EvalCtx -> GName -> Maybe GlobalDef
lookupGlobal ctx g = Map.lookup g (globalsMap (ecGlobals ctx))

-- ── Evaluation ───────────────────────────────────────────────────────

eval :: EvalCtx -> Env -> Term -> Value
eval ctx env = \case
  CVar i -> env !! i
  CGlob g -> VGlobN g []
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
  CMeta m -> case Map.lookup m (ecMetas ctx) of
    Just (Just v) -> v
    _ -> VFlex m []
  CDo items -> VDoV items env
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
    | ic == Impl -> VPrim p args
    | otherwise ->
        let args' = args ++ [av]
         in case evalPurePrim p (map (force ctx) args') of
              Just v -> v
              Nothing -> VPrim p args'
  _ -> VPrim "__stuck_app" [fv, av]

evalApp :: EvalCtx -> Value -> [(Icit, Value)] -> Value
evalApp ctx = foldl (\f (ic, a) -> vapp ctx f ic a)

vproj :: EvalCtx -> Value -> Text -> Value
vproj ctx v f = case force ctx v of
  VRecordV fs | Just x <- lookup f fs -> x
  v' -> VProjN v' f

vforce :: EvalCtx -> Value -> Value
vforce ctx v = case force ctx v of
  VThunkV clo -> closApply ctx clo (VRecordV []) `seq` runSusp clo
  VLazyV clo -> runSusp clo
  v' -> VPrim "force" [v']
  where
    runSusp (Closure env body) = eval ctx env body

-- | Unfold solved metas and (reducible) global heads at the value root.
force :: EvalCtx -> Value -> Value
force ctx = go (1000 :: Int)
  where
    go 0 v = v
    go fuel v = case v of
      VFlex m sp
        | Just (Just sol) <- Map.lookup m (ecMetas ctx) ->
            go (fuel - 1) (evalApp ctx sol sp)
      VGlobN g sp
        | Just gd <- lookupGlobal ctx g
        , Just body <- gdValue gd
        , gdReducible gd || isPrimRoot body ->
            go (fuel - 1) (evalApp ctx body sp)
      VPrim p sp
        | Just v' <- evalPurePrim p (map (go (fuel - 1)) sp) -> go (fuel - 1) v'
      _ -> v
      where
        isPrimRoot = \case
          VPrim _ [] -> True
          _ -> False

-- ι-reduction of match when the scrutinee is canonical.
reduceMatch :: EvalCtx -> Value -> [CaseAlt] -> Env -> Value
reduceMatch ctx scrut alts env =
  case tryAlts alts of
    Just v -> v
    Nothing -> VMatchN scrut alts env
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

    definitelyNoMatch pat v = case (pat, v) of
      (CPCtor g _, VCtor g' _) -> g /= g'
      (CPLit l, VLit l') -> l /= l'
      (CPInject t _, VInject t' _) -> t /= t'
      (CPInjectRest excl, VInject t _) -> t `elem` excl
      (CPOr ps, _) -> all (`definitelyNoMatch` v) ps
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
        (CPRecord pfs _, VRecordV fs) ->
          concatM [maybe Nothing (matchPat ctx p) (lookup n fs) | (n, p) <- pfs]
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

quote :: EvalCtx -> Int -> Value -> Term
quote ctx lvl v = case force ctx v of
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
  VDoV items _ -> CDo items
  VThunkV (Closure env body) -> CThunkE (quoteUnder env body)
  VLazyV (Closure env body) -> CLazyE (quoteUnder env body)
  VIfN c t f ->
    CIf
      (quote ctx lvl c)
      (quote ctx lvl (closApply ctx t (VRecordV [])))
      (quote ctx lvl (closApply ctx f (VRecordV [])))
  VPrim p args -> foldl (\f a -> CApp Expl f (quote ctx lvl a)) (CGlob (GName primModule p)) args
  where
    quoteSpine = foldl (\f (ic, a) -> CApp ic f (quote ctx lvl a))
    quoteAlt _ alt = alt
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
      (VIfN c1 t1 f1, VIfN c2 t2 f2) ->
        go (fuel - 1) lvl c1 c2 && goClos fuel lvl t1 t2 && goClos fuel lvl f1 f2
      (VPrim p1 a1, VPrim p2 a2) ->
        p1 == p2 && length a1 == length a2 && and (zipWith (go (fuel - 1) lvl) a1 a2)
      _ -> False
      where
        goClos fl l c1 c2 =
          let x = VRigid l []
           in go (fl - 1) (l + 1) (closApply ctx c1 x) (closApply ctx c2 x)
        goSpine fl l sp1 sp2 =
          length sp1 == length sp2
            && and (zipWith (\(_, a) (_, b) -> go (fl - 1) l a b) sp1 sp2)

normalize :: EvalCtx -> Env -> Term -> Term
normalize ctx env t = quote ctx (length env) (eval ctx env t)

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
  ("stringAppend", [VLit (LitStr a), VLit (LitStr b)]) -> Just (VLit (LitStr (a <> b)))
  ("showInt", [VLit (LitInt a)]) -> str (T.pack (show a))
  ("showDouble", [VLit (LitDouble a)]) -> str (T.pack (show a))
  ("showStringLit", [VLit (LitStr a)]) -> str (T.pack (show a))
  ("showScalar", [VLit (LitScalar a)]) -> str (T.pack (show a))
  ("intToDouble", [VLit (LitInt a)]) -> dbl (fromInteger a)
  ("natOfInt", [VLit (LitInt a)]) -> int a
  ("natToInt", [VLit (LitInt a)]) -> int a
  _ -> Nothing
  where
    int = Just . VLit . LitInt
    dbl = Just . VLit . LitDouble
    str = Just . VLit . LitStr
    bool b = Just (VCtor (GName (ModuleName ["std", "prelude"]) (if b then "True" else "False")) [])
    identicalIEEE a b = (a == b && (1 / a == 1 / b)) || (a /= a && b /= b)
