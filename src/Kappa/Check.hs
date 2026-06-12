-- | Bidirectional elaboration to the core (Spec §30.1; expressions §16,
-- patterns §17, traits §14, literals §6.1.5, do blocks §18).
--
-- Implicit arguments are inserted per the application-spine rules
-- (§16.1.7.1); trait goals follow the §16.3.3 ladder: local implicit
-- context, then global instance search (§14.3.1, with a
-- unique-candidate coherence rule), then boolean-proposition
-- normalization for @(lhs = rhs)@ goals decided by conversion.
--
-- Deliberate v1 restrictions surface as @E_UNSUPPORTED@ diagnostics and
-- are catalogued in SPEC_COVERAGE.md; approximations (quantity usage
-- checking, termination) are catalogued in IMPLEMENTATION_NOTES.md.
module Kappa.Check
  ( CheckState (..)
  , initCheckState
  , DataInfo (..)
  , CtorInfo (..)
  , TraitInfo (..)
  , InstanceEntry (..)
  , GlobalDef (..)
  , checkModule
  , expectUnsatisfiedDiags
  , preludeModule
  ) where

import Control.Monad.State.Strict
import Data.List (elemIndex, foldl', nub, sort, sortOn, (\\))
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes, fromMaybe, isJust, isNothing, mapMaybe)
import Data.Text (Text)
import qualified Data.Text as T
import Kappa.Core
import Kappa.Diagnostic
import Kappa.Eval
import Kappa.Pretty (renderTerm)
import Kappa.Source
import Kappa.Syntax hiding (CompClause (..), Quantity (..))
import qualified Kappa.Syntax as S
import Kappa.Token (QuotedLit (..), StrFragment (..), StringLit (..))

-- ── State ────────────────────────────────────────────────────────────

data DataInfo = DataInfo
  { diCtors :: ![GName]
  , diParamCount :: !Int
  }

data CtorInfo = CtorInfo
  { ciData :: !GName
  , ciType :: !Term
  , ciFields :: ![(Maybe Text, Maybe Expr)] -- ^ explicit fields: name, default (§10.1.1; elaborated at the application site)
  }

data TraitInfo = TraitInfo
  { tiParamCount :: !Int
  , tiMembers :: ![Text]
  , tiDefaults :: !(Map Text LetDef)
  , tiSupers :: ![Term] -- ^ supertrait premises as @\\params -> C params@ (§14.1.4)
  -- ^ default member definitions, instantiated per instance (§14.2.3)
  }

data InstanceEntry = InstanceEntry
  { ieTrait :: !GName
  , ieTeleLen :: !Int
  , iePremises :: ![Term] -- ^ de Bruijn under the telescope
  , ieHead :: ![Term] -- ^ trait arguments under the telescope
  , ieDict :: !GName
  }

data CheckState = CheckState
  { csGlobals :: !(Map GName GlobalDef)
  , csDatas :: !(Map GName DataInfo)
  , csCtors :: !(Map GName CtorInfo)
  , csTraits :: !(Map GName TraitInfo)
  , csInstances :: ![InstanceEntry]
  , csMetas :: !MetaState
  , csNextMeta :: !Int
  , csDiags :: !Diagnostics
  , csModule :: !ModuleName
  , csScope :: !(Map Text GName) -- ^ unqualified import scope
  , csModuleAliases :: !(Map Text ModuleName)
  , csModuleExports :: !(Map ModuleName [Text])
  , csFresh :: !Int
  , csPending :: ![(MetaId, Value, Span, Ctx)]
  -- ^ postponed implicit goals with the local context they were raised
  -- in (premise dictionaries live there, §14.3.2)
  , csScopeAmbig :: !(Map Text [GName])
  -- ^ §7.1 names provided ambiguously by several wildcard imports
  , csExpects :: !(Map GName (Span, Int))
  -- ^ §9.4 expect declarations: span and number of satisfiers seen
  , csSigPending :: !(Map GName Span)
  -- ^ §9.1 top-level signatures not yet satisfied in this file
  }

initCheckState :: CheckState
initCheckState =
  CheckState Map.empty Map.empty Map.empty Map.empty [] emptyMetas 0 []
    (ModuleName ["main"]) Map.empty Map.empty Map.empty 0 [] Map.empty Map.empty Map.empty

preludeModule :: ModuleName
preludeModule = ModuleName ["std", "prelude"]

gPrel :: Text -> GName
gPrel = GName preludeModule

type CheckM = State CheckState

-- local context
data CtxEntry = CtxEntry
  { ceName :: !Text
  , ceType :: !Value
  , ceImplicitLocal :: !Bool
  , ceVarBind :: !Bool
  -- ^ Introduced by @var@ (§18.6.1): reads auto-dereference.
  }

data Ctx = Ctx
  { ctxEntries :: ![CtxEntry]
  , ctxEnv :: !Env
  }

emptyCtx :: Ctx
emptyCtx = Ctx [] []

ctxLen :: Ctx -> Int
ctxLen = length . ctxEntries

bindCtx :: Text -> Bool -> Value -> Ctx -> Ctx
bindCtx n implocal ty (Ctx es env) =
  Ctx (CtxEntry n ty implocal False : es) (VRigid (length env) [] : env)

-- | Bind a local definition: the environment carries the definiens, so
-- conversion sees through local lets (delta for locals, §15.1).
bindCtxLet :: Text -> Bool -> Value -> Value -> Ctx -> Ctx
bindCtxLet n implocal ty v (Ctx es env) =
  Ctx (CtxEntry n ty implocal False : es) (v : env)

-- | Bind a @var@ cell (type @Ref a@); uses read through it (§18.6.1).
bindCtxVar :: Text -> Value -> Ctx -> Ctx
bindCtxVar n ty (Ctx es env) =
  Ctx (CtxEntry n ty False True : es) (VRigid (length env) [] : env)

lookupCtx :: Text -> Ctx -> Maybe (Int, CtxEntry)
lookupCtx n (Ctx es _) = go 0 es
  where
    go _ [] = Nothing
    go i (e : rest)
      | ceName e == n = Just (i, e)
      | otherwise = go (i + 1) rest

ec_ :: CheckM EvalCtx
ec_ = gets (\st -> EvalCtx (Globals (csGlobals st)) (csMetas st) False)

evalIn :: Ctx -> Term -> CheckM Value
evalIn ctx t = do
  ec <- ec_
  pure (eval ec (ctxEnv ctx) t)

quoteIn :: Ctx -> Value -> CheckM Term
quoteIn ctx v = do
  ec <- ec_
  pure (quote ec (ctxLen ctx) v)

forceM :: Value -> CheckM Value
forceM v = do
  ec <- ec_
  pure (force ec v)

clApp :: Closure -> Value -> CheckM Value
clApp (Closure env body) v = do
  ec <- ec_
  pure (eval ec (v : env) body)

-- | Record a diagnostic. Diagnostics accumulate in reverse (prepend)
-- order; 'checkModule' restores source order once at the end.
report :: Diagnostic -> CheckM ()
report d = modify' $ \st -> st {csDiags = d : csDiags st}

errAt :: Span -> DiagnosticCode -> Maybe DiagnosticFamily -> Text -> CheckM ()
errAt sp code fam msg = report (diag SevError StageElaborate code fam sp msg)

freshMeta :: CheckM Term
freshMeta = do
  st <- get
  let m = csNextMeta st
  put st {csNextMeta = m + 1, csMetas = Map.insert m Nothing (csMetas st)}
  pure (CMeta m)

freshMetaV :: Ctx -> CheckM Value
freshMetaV ctx = freshMeta >>= evalIn ctx

solveMeta :: MetaId -> Value -> CheckM ()
solveMeta m v = modify' $ \st -> st {csMetas = Map.insert m (Just v) (csMetas st)}

freshNameM :: Text -> CheckM Text
freshNameM base = do
  st <- get
  put st {csFresh = csFresh st + 1}
  pure (base <> T.pack (show (csFresh st)))

addGlobal :: GName -> GlobalDef -> CheckM ()
addGlobal g gd = modify' $ \st -> st {csGlobals = Map.insert g gd (csGlobals st)}

-- ── Unification ──────────────────────────────────────────────────────

unify :: Ctx -> Value -> Value -> CheckM Bool
unify ctx = goTop
  where
    goTop a b = do
      a' <- forceM a
      b' <- forceM b
      go (ctxLen ctx) a' b'
    go lvl a b = case (a, b) of
      (VFlex m [], t) -> solveFlex lvl m t
      (t, VFlex m []) -> solveFlex lvl m t
      (VSort m, VSort n) -> pure (m <= n) -- cumulativity (§11.1.1)
      (VPi i1 q1 _ d1 c1, VPi i2 q2 _ d2 c2) | i1 == i2 && q1 == q2 -> do
        ok <- goTop d1 d2
        if not ok
          then pure False
          else do
            let x = VRigid lvl []
            b1 <- clApp c1 x
            b2 <- clApp c2 x
            b1' <- forceM b1
            b2' <- forceM b2
            go (lvl + 1) b1' b2'
      (VRecordT f1, VRecordT f2) | map fst f1 == map fst f2 ->
        andM [goTop x y | ((_, x), (_, y)) <- zip f1 f2]
      (VVariantT m1, VVariantT m2) | length m1 == length m2 ->
        andM (zipWith goTop m1 m2)
      (VCtor g1 a1, VCtor g2 a2) | g1 == g2 && length a1 == length a2 ->
        andM (zipWith goTop a1 a2)
      (VGlobN g1 sp1, VGlobN g2 sp2)
        | g1 == g2 && length sp1 == length sp2 -> do
            ok <- andM (zipWith (\(_, x) (_, y) -> goTop x y) sp1 sp2)
            if ok then pure True else fallback lvl a b
      _ -> fallback lvl a b
      where
        andM [] = pure True
        andM (m : ms) = m >>= \ok -> if ok then andM ms else pure False
    fallback lvl a b = do
      ec <- ec_
      pure (convertible ec lvl a b)
    solveFlex lvl m t = do
      st <- get
      case Map.lookup m (csMetas st) of
        Just (Just sol) -> do
          sol' <- forceM sol
          t' <- forceM t
          go lvl sol' t'
        _ -> case t of
          -- a meta is trivially equal to itself; the occurs check must
          -- not reject reflexive flex-flex problems
          VFlex m' [] | m' == m -> pure True
          _ -> do
            ec <- ec_
            let tm = quote ec lvl t
            if occursMeta m tm then pure False else solveMeta m t >> pure True

occursMeta :: MetaId -> Term -> Bool
occursMeta m = go
  where
    go = \case
      CMeta m' -> m == m'
      CApp _ f a -> go f || go a
      CLam _ _ _ b -> go b
      CPi _ _ _ a b -> go a || go b
      CCtor _ as -> any go as
      CMatch s alts -> go s || any (\(CaseAlt _ g b) -> maybe False go g || go b) alts
      CRecordT fs -> any (go . snd) fs
      CRecordV fs -> any (go . snd) fs
      CProj e _ -> go e
      CVariantT ms -> any go ms
      CInject _ e -> go e
      CLet _ _ a b c -> go a || go b || go c
      CLetRec _ _ a b c -> go a || go b || go c
      CIf a b c -> go a || go b || go c
      CThunkE e -> go e
      CLazyE e -> go e
      CForceE e -> go e
      _ -> False

expectType :: Ctx -> Span -> Value -> Value -> CheckM ()
expectType ctx sp actual expected = do
  ok <- unify ctx actual expected
  unless ok $ do
    aT <- quoteIn ctx actual
    eT <- quoteIn ctx expected
    report $
      withNote ("expected: " <> renderTerm eT) $
        withNote ("actual:   " <> renderTerm aT) $
          diag SevError StageElaborate "E_TYPE_EQUALITY_MISMATCH" (Just "kappa.type.mismatch") sp
            "type mismatch"

-- ── Names ────────────────────────────────────────────────────────────

lookupGlobalName :: Text -> CheckM (Maybe GName)
lookupGlobalName n = do
  st <- get
  let own = GName (csModule st) n
  if Map.member own (csGlobals st) || Map.member own (csCtors st)
    then pure (Just own)
    else pure (Map.lookup n (csScope st))

globalTerm :: GName -> CheckM (Maybe (Term, Value))
globalTerm g = do
  st <- get
  -- §7.2: in term position the constructor facet of a same-spelling
  -- data family wins over the type facet.
  case Map.lookup g (csCtors st) of
    Just ci -> do
      ec <- ec_
      let tm = etaCtor ec g (ciType ci)
      ty <- evalIn emptyCtx (ciType ci)
      pure (Just (tm, ty))
    Nothing -> case Map.lookup g (csGlobals st) of
      Nothing -> pure Nothing
      Just gd -> pure (Just (CGlob g, gdType gd))

-- type-facet lookup (type positions, §7.2)
globalType :: GName -> CheckM (Maybe (Term, Value))
globalType g = do
  st <- get
  case Map.lookup g (csGlobals st) of
    Just gd -> pure (Just (CGlob g, gdType gd))
    Nothing -> pure Nothing

-- Constructors as values: λ-wrap to a saturated 'CCtor' (erased
-- implicit parameters are dropped from the runtime payload).
etaCtor :: EvalCtx -> GName -> Term -> Term
etaCtor ec g cty = build 0 [] (eval ec [] cty)
  where
    build n acc fty = case force ec fty of
      VPi ic q _ _ clo ->
        CLam ic q ("x" <> T.pack (show n)) $
          build (n + 1) ((ic, q, n) : acc) (evalClosure clo (VRigid n []))
      _ ->
        CCtor g [CVar (n - 1 - i) | (ic, q, i) <- reverse acc, runtimeField ic q]
    runtimeField Expl _ = True
    runtimeField Impl q = q /= Q0
    evalClosure (Closure env body) v = eval ec (v : env) body

resolveName :: Ctx -> Name -> CheckM (Term, Value)
resolveName ctx (Name n sp) =
  case lookupCtx n ctx of
    Just (i, e)
      | ceVarBind e -> derefVar ctx i (ceType e)
      | otherwise -> pure (CVar i, ceType e)
    Nothing -> do
      st <- get
      case Map.lookup n (csScopeAmbig st) of
        Just gs -> do
          errAt sp "E_NAME_AMBIGUOUS" (Just "kappa.name.ambiguous")
            ( "name '" <> n <> "' is ambiguous; it is provided by "
                <> T.intercalate " and " [renderMod mg | GName mg _ <- gs]
                <> " (qualify the name or import it explicitly, Spec §7.1)"
            )
          anyHole ctx
        Nothing -> do
          mg <- lookupGlobalName n
          case mg of
            Just g -> do
              mt <- globalTerm g
              case mt of
                Just r -> pure r
                Nothing -> failUnresolved
            Nothing -> failUnresolved
  where
    renderMod (ModuleName segs) = "module " <> T.intercalate "." segs
    failUnresolved = do
      errAt sp "E_NAME_UNRESOLVED" (Just "kappa.name.unresolved") ("unresolved name '" <> n <> "'")
      anyHole emptyCtxDummy
    emptyCtxDummy = ctx

-- | Does a name resolve at all (locals or globals)? Used for §6.3.4
-- literal-prefix resolution, which is ordinary term name resolution.
prefixResolves :: Ctx -> Text -> CheckM Bool
prefixResolves ctx n =
  case lookupCtx n ctx of
    Just _ -> pure True
    Nothing -> do
      mg <- lookupGlobalName n
      pure (maybe False (const True) mg)

-- | A read of a @var@-bound name (§18.6.1): elaborate to a splice that
-- reads the cell, @__runIO (readRef x)@, typed at the element type.
derefVar :: Ctx -> Int -> Value -> CheckM (Term, Value)
derefVar ctx i refTy = do
  elemTy <-
    forceM refTy >>= \case
      VGlobN (GName _ "Ref") [(_, a)] -> pure a
      _ -> freshMetaV ctx
  e <- freshMeta
  aTm <- quoteIn ctx elemTy
  let rd = CApp Expl (CApp Impl (CApp Impl (CGlob (gPrel "readRef")) e) aTm) (CVar i)
      run = CApp Expl (CApp Impl (CApp Impl (CGlob (gPrel "__runIO")) e) aTm) rd
  pure (run, elemTy)

-- universe spellings: Type, Type0, Type1, ..., and '*' (§11.1)
sortName :: Text -> Maybe Int
sortName t
  | t == "Type" || t == "*" = Just 0
  | Just rest <- T.stripPrefix "Type" t
  , not (T.null rest)
  , T.all (\c -> c >= '0' && c <= '9') rest
  , -- bounds check: a suffix this long would overflow 'Int'; treat the
    -- spelling as an ordinary (unresolved) identifier instead
    T.length rest <= 9 =
      Just (read (T.unpack rest))
  | otherwise = Nothing

anyHole :: Ctx -> CheckM (Term, Value)
anyHole ctx = do
  m <- freshMeta
  ty <- freshMetaV ctx
  pure (m, ty)

reportUnsupported :: Span -> Text -> CheckM ()
reportUnsupported sp what =
  report $
    withNote "see SPEC_COVERAGE.md for the implemented subset" $
      diag SevError StageElaborate "E_UNSUPPORTED" Nothing sp
        (what <> " is not supported by this implementation")

unsupported :: Ctx -> Span -> Text -> CheckM (Term, Value)
unsupported ctx sp what = reportUnsupported sp what >> anyHole ctx

-- ── Implicit resolution (§16.3.3) ────────────────────────────────────

resolveImplicit :: Ctx -> Span -> Value -> CheckM Term
resolveImplicit ctx sp goal = do
  g <- forceM goal
  case g of
    VSort _ -> freshMeta
    _ -> do
      isTrait <- isTraitGoal g
      isEq <- isEqGoal g
      flexed <- goalHasFlex g
      if (isTrait || isEq) && flexed
        then do
          -- postpone resolution until explicit arguments solve the head
          -- metavariables (§16.1.7.1 spine order); committing to a local
          -- candidate now could wrongly solve the metas
          m <- freshMeta
          let mid = case m of
                CMeta i -> i
                _ -> error "freshMeta"
          modify' $ \st -> st {csPending = (mid, g, sp, ctx) : csPending st}
          pure m
        else do
          -- §16.3.3 step 1: the local implicit context goes first.
          mLoc <- localCandidate ctx g
          case mLoc of
            Just tm -> pure tm
            Nothing -> do
              mInst <- instanceSearch ctx sp g
              case mInst of
                Just tm -> pure tm
                Nothing -> do
                  mProp <- propProof g
                  case mProp of
                    Just tm -> pure tm
                    Nothing ->
                      if isTrait || isEq
                        then do
                          gT <- quoteIn ctx g
                          errAt sp "E_IMPLICIT_UNSOLVED" (Just "kappa.implicit.unsolved")
                            ("could not resolve implicit argument of type " <> renderTerm gT)
                          freshMeta
                        else freshMeta

localCandidate :: Ctx -> Value -> CheckM (Maybe Term)
localCandidate ctx goal = go 0 (ctxEntries ctx)
  where
    go _ [] = pure Nothing
    go i (e : rest)
      | ceImplicitLocal e = do
          st0 <- get
          ok <- unify ctx (ceType e) goal
          if ok then pure (Just (CVar i)) else put st0 >> go (i + 1) rest
      | otherwise = go (i + 1) rest

goalHasFlex :: Value -> CheckM Bool
goalHasFlex v = do
  ec <- ec_
  t <- pure (quote ec 0 v)
  st <- get
  let unsolved m = case Map.lookup m (csMetas st) of
        Just (Just _) -> False
        _ -> True
  pure (anyMeta unsolved t)
  where
    anyMeta f = goT
      where
        goT = \case
          CMeta m -> f m
          CApp _ a b -> goT a || goT b
          CPi _ _ _ a b -> goT a || goT b
          CLam _ _ _ b -> goT b
          CCtor _ as -> any goT as
          CRecordT fs -> any (goT . snd) fs
          CVariantT ms -> any goT ms
          CProj e _ -> goT e
          _ -> False

-- flush postponed trait goals after a body has been elaborated.
flushPending :: CheckM ()
flushPending = do
  st <- get
  let pend = reverse (csPending st)
  put st {csPending = []}
  forM_ pend $ \(mid, goal, sp, ctx) -> do
    stNow <- get
    case Map.lookup mid (csMetas stNow) of
      Just (Just _) -> pure ()
      _ -> do
        g <- forceM goal
        mLoc <- localCandidate ctx g
        r <- case mLoc of
          Just tm -> pure (Just tm)
          Nothing -> do
            mi <- instanceSearch ctx sp g
            case mi of
              Just tm -> pure (Just tm)
              Nothing -> propProof g
        case r of
          Just tm -> do
            v <- evalIn ctx tm
            solveMeta mid v
          Nothing -> do
            ec <- ec_
            errAt sp "E_IMPLICIT_UNSOLVED" (Just "kappa.implicit.unsolved")
              ("could not resolve implicit argument of type " <> renderTerm (quote ec (ctxLen ctx) g))

-- | Replace solved metavariables by their solutions, quoted at the
-- correct binder depth. Run after 'flushPending' so terms stored as
-- globals (and instance dictionaries) contain no live 'CMeta' whose
-- solution mentions local rigids (premise dictionaries, §14.3.2).
zonkTermM :: Int -> Term -> CheckM Term
zonkTermM depth0 t0 = do
  ec <- ec_
  let goI :: Int -> [KItem] -> [KItem]
      goI _ [] = []
      goI d (k : ks) =
        let (k', d') = goK d k
         in k' : goI d' ks
      goK d = \case
        KBind q p t -> (KBind q p (go d t), d + patBindersC p)
        KLet q p t -> (KLet q p (go d t), d + patBindersC p)
        KLetQ p t mElse ->
          ( KLetQ p (go d t) (fmap (\(rp, e) -> (rp, go (d + patBindersC rp) e)) mElse)
          , d + patBindersC p
          )
        KExpr t -> (KExpr (go d t), d)
        KVarItem n t -> (KVarItem n (go d t), d + 1)
        KAssign r monadic t -> (KAssign (go d r) monadic (go d t), d)
        KReturn t -> (KReturn (go d t), d)
        k@KBreak {} -> (k, d)
        k@KContinue {} -> (k, d)
        KWhile l c b e -> (KWhile l (go d c) (goI d b) (fmap (goI d) e), d)
        KFor l p s b e -> (KFor l p (go d s) (goI (d + patBindersC p) b) (fmap (goI d) e), d)
        KIf alts e -> (KIf [(go d c, goI d b) | (c, b) <- alts] (fmap (goI d) e), d)
        KDefer t -> (KDefer (go d t), d)
        KUsing p a r -> (KUsing p (go d a) (go d r), d)
      go :: Int -> Term -> Term
      go d = \case
        CMeta m -> case Map.lookup m (ecMetas ec) of
          Just (Just v) -> quote ec d v
          _ -> CMeta m
        CVar i -> CVar i
        CGlob g -> CGlob g
        CLam ic q n b -> CLam ic q n (go (d + 1) b)
        CPi ic q n a b -> CPi ic q n (go d a) (go (d + 1) b)
        CApp ic f a -> CApp ic (go d f) (go d a)
        CSort s -> CSort s
        CLit l -> CLit l
        CCtor g as -> CCtor g (map (go d) as)
        CMatch s alts ->
          CMatch (go d s) [CaseAlt p (fmap (go (d + patBindersC p)) gd) (go (d + patBindersC p) b) | CaseAlt p gd b <- alts]
        CRecordT fs -> CRecordT [(n, go d t) | (n, t) <- fs]
        CRecordV fs -> CRecordV [(n, go d t) | (n, t) <- fs]
        CProj e f -> CProj (go d e) f
        CVariantT ms -> CVariantT (map (go d) ms)
        CInject tg e -> CInject tg (go d e)
        CLet q n a b c -> CLet q n (go d a) (go d b) (go (d + 1) c)
        CLetRec q n a b c -> CLetRec q n (go d a) (go (d + 1) b) (go (d + 1) c)
        CDo items -> CDo (goI d items)
        CThunkE e -> CThunkE (go d e)
        CLazyE e -> CLazyE (go d e)
        CForceE e -> CForceE (go d e)
        CIf a b c -> CIf (go d a) (go d b) (go d c)
  pure (go depth0 t0)

isTraitGoal :: Value -> CheckM Bool
isTraitGoal v =
  forceM v >>= \case
    VGlobN g _ -> gets (Map.member g . csTraits)
    _ -> pure False

isEqGoal :: Value -> CheckM Bool
isEqGoal v =
  forceM v >>= \case
    VGlobN (GName _ "=") _ -> pure True
    VCtor (GName _ "=") _ -> pure True
    _ -> pure False

instanceSearch :: Ctx -> Span -> Value -> CheckM (Maybe Term)
instanceSearch ctx sp goal = searchDepth 0 ctx sp goal

searchDepth :: Int -> Ctx -> Span -> Value -> CheckM (Maybe Term)
searchDepth depth ctx sp goal
  | depth > 16 = pure Nothing -- §14.3.5 termination backstop
  | otherwise = do
      g <- forceM goal
      case g of
        VGlobN traitG spine -> do
          st <- get
          if not (Map.member traitG (csTraits st))
            then pure Nothing
            else do
              let cands = [ie | ie <- csInstances st, ieTrait ie == traitG]
              hits <- catMaybes <$> mapM (tryInstance depth ctx (map snd spine)) cands
              case hits of
                [tm] -> pure (Just tm)
                [] -> pure Nothing
                (tm : _) -> do
                  report $
                    diag SevError StageElaborate "E_INSTANCE_INCOHERENT" (Just "kappa.trait.incoherent") sp
                      "multiple instances match this trait obligation (§14.3.1 coherence)"
                  pure (Just tm)
        _ -> pure Nothing

tryInstance :: Int -> Ctx -> [Value] -> InstanceEntry -> CheckM (Maybe Term)
tryInstance depth ctx goalArgs ie
  | length (ieHead ie) /= length goalArgs = pure Nothing
  | otherwise = do
      saved <- get
      metas <- forM [1 .. ieTeleLen ie] (const freshMeta)
      metaVs <- mapM (evalIn emptyCtx) metas
      ec <- ec_
      let headVs = [eval ec (reverse metaVs) t | t <- ieHead ie]
      oks <- zipWithM (unify ctx) headVs goalArgs
      if and oks
        then do
          let premVs = [eval ec (reverse metaVs) p | p <- iePremises ie]
          prems <- forM premVs $ \pv -> do
            mLoc <- localCandidate ctx pv
            case mLoc of
              Just t -> pure (Just t)
              Nothing -> do
                mi <- searchDepth (depth + 1) ctx noSpan pv
                case mi of
                  Just t -> pure (Just t)
                  Nothing -> propProof pv
          if all isJust prems
            then do
              metaTms <- mapM (quoteIn ctx) =<< mapM (evalIn emptyCtx) metas
              -- the dictionary lambda binds only the head's type
              -- variables and then the premise dictionaries; the metas
              -- standing for premise slots are not applied
              let nFv = ieTeleLen ie - length (iePremises ie)
                  dict =
                    foldl' (\f a -> CApp Impl f a)
                      (foldl' (\f a -> CApp Impl f a) (CGlob (ieDict ie)) (take nFv metaTms))
                      (catMaybes prems)
              pure (Just dict)
            else put saved >> pure Nothing
        else put saved >> pure Nothing

-- Boolean-proposition normalization (§16.3.3 step 3): goals of shape
-- (lhs = rhs) decided by conversion yield refl.
propProof :: Value -> CheckM (Maybe Term)
propProof goal = do
  g <- forceM goal
  case g of
    VGlobN (GName _ "=") sp | [(_, l), (_, r)] <- drop (length sp - 2) sp -> tryRefl l r
    VCtor (GName _ "=") [_, l, r] -> tryRefl l r
    _ -> pure Nothing
  where
    tryRefl l r = do
      ec <- ec_
      pure $
        if convertible ec 0 (force ec l) (force ec r)
          then Just (CCtor (gPrel "refl") [])
          else Nothing

-- ── Quantities (surface → core) ──────────────────────────────────────

qOf :: Maybe S.Quantity -> Q
qOf = \case
  Nothing -> QW
  Just S.QZero -> Q0
  Just S.QOne -> Q1
  Just S.QOmega -> QW
  Just S.QAtMostOne -> QLe1
  Just S.QAtLeastOne -> QGe1
  Just (S.QTerm _) -> QW -- symbolic quantities: approximated as ω

binderQ :: Binder -> Q
binderQ b = case bpQuantity (bPrefix b) of
  Just q -> qOf (Just q)
  Nothing
    | isJust (bpBorrow (bPrefix b)) -> QW -- borrowed reads (approximation)
    | bImplicit b -> QW
    | otherwise -> QW

-- | The binder's annotation with suspension sugar applied: a
-- @(thunk x : T)@ binder has type @Thunk T@ (§16.2.4).
binderTypeExpr :: Binder -> Maybe Expr
binderTypeExpr b = case (bSusp b, bType b) of
  (Just SuspThunk, Just t) ->
    Just (EApp (EVar (Name "Thunk" (bSpan b))) [ArgExplicit t])
  (Just SuspLazy, Just t) ->
    Just (EApp (EVar (Name "Need" (bSpan b))) [ArgExplicit t])
  (_, mt) -> mt

-- ── Elaboration ──────────────────────────────────────────────────────

insertAllImplicits :: Ctx -> Span -> Term -> Value -> CheckM (Term, Value)
insertAllImplicits ctx sp tm ty = do
  t <- forceM ty
  case t of
    VPi Impl _ _ dom clo -> do
      arg <- resolveImplicit ctx sp dom
      argV <- evalIn ctx arg
      ty' <- clApp clo argV
      insertAllImplicits ctx sp (CApp Impl tm arg) ty'
    _ -> pure (tm, t)

infer :: Ctx -> Expr -> CheckM (Term, Value)
infer ctx expr = case expr of
  EVar n
    | Nothing <- lookupCtx (nameText n) ctx
    , Just lvl <- sortName (nameText n) ->
        -- '*' is a universe spelling only when it does not resolve to
        -- an operator (the prelude defines multiplication) (§11.1)
        if nameText n == "*"
          then do
            mg <- lookupGlobalName "*"
            case mg of
              Just _ -> resolveName ctx n
              Nothing -> pure (CSort lvl, VSort (lvl + 1))
          else pure (CSort lvl, VSort (lvl + 1))
    | otherwise -> resolveName ctx n
  EHole mn sp -> do
    (tm, ty) <- anyHole ctx
    tyT <- quoteIn ctx ty
    report $
      diag SevError StageElaborate "E_HOLE_UNSOLVED" (Just "kappa.hole.unsolved") sp
        (("hole " <> maybe "_" (("?" <>) . nameText) mn) <> " : " <> renderTerm tyT)
    pure (tm, ty)
  EIntLit v msuf sp -> elabIntLit ctx v msuf sp Nothing
  EFloatLit v msuf sp -> elabFloatLit ctx v msuf sp Nothing
  EStringLit sl parts sp -> elabString ctx sl parts sp
  EQuotedLit ql sp
    | Nothing <- qlPrefix ql
    , Just txt <- qlText ql
    , [c] <- T.unpack txt ->
        pure (CLit (LitScalar c), VGlobN (gPrel "UnicodeScalar") [])
    | otherwise -> snd <$> ((,) () <$> unsupported ctx sp "this quoted-literal form")
  EUnit _ -> pure (CCtor (gPrel "Unit") [], VGlobN (gPrel "Unit") [])
  ETuple es _ -> do
    rs <- mapM (infer ctx) es
    let fields = [(tupleField i, tm) | (i, (tm, _)) <- zip [0 :: Int ..] rs]
        ftys = [(tupleField i, ty) | (i, (_, ty)) <- zip [0 :: Int ..] rs]
    pure (CRecordV fields, VRecordT ftys)
  ERecordLit items sp -> elabRecordLit ctx items sp
  ERecordType fs mtail sp -> do
    when (isJust mtail) . void $ unsupported ctx sp "open record row tails"
    fields <- forM fs $ \f -> do
      (t, _) <- inferType ctx (rtfType f)
      pure (nameText (rtfName f), t)
    let names = map fst fields
    forM_ (duplicatesOf names) $ \n ->
      errAt sp "E_RECORD_DUPLICATE_FIELD" (Just "kappa.record.duplicate-field")
        ("record type has duplicate field '" <> n <> "'")
    pure (CRecordT (sortOn fst fields), VSort 0)
  EApp f args -> do
    (fTm, fTy) <- infer ctx f
    elabSpine ctx (exprSpan f) fTm fTy args
  EDot e m -> elabDot ctx e m
  EQDot e m -> elabSafeNav ctx e m
  EIs e cref -> elabIs ctx e cref
  EAscription e tyE _ -> do
    (tyTm, _) <- inferType ctx tyE
    tyV <- evalIn ctx tyTm
    tm <- check ctx e tyV
    pure (tm, tyV)
  EArrow b body -> do
    domE <- case binderTypeExpr b of
      Just t -> pure t
      Nothing -> pure (EUnit (bSpan b))
    (domTm, _) <- inferType ctx domE
    domV <- evalIn ctx domTm
    let nm = maybe "_" nameText (bName b)
        ic = if bImplicit b then Impl else Expl
        -- implicit Pi binders join the local implicit context (§16.3.3)
        ctx' = bindCtx nm (bImplicit b) domV ctx
    (codTm, _) <- inferType ctx' body
    pure (CPi ic (binderQ b) nm domTm codTm, VSort 0)
  EForall bs body _ -> elabForall ctx bs body
  EExists _ _ sp -> unsupported ctx sp "exists types"
  ETraitArrow c rest -> do
    (cTm, _) <- inferType ctx c
    cV <- evalIn ctx cTm
    -- the evidence binder joins the local implicit context (§16.3.3)
    let ctx' = bindCtx "_ev" True cV ctx
    (restTm, _) <- inferType ctx' rest
    pure (CPi Impl QW "_ev" cTm restTm, VSort 0)
  EOptionSugar t _ -> do
    (tm, _) <- inferType ctx t
    pure (CApp Expl (CGlob (gPrel "Option")) tm, VSort 0)
  EVariant arms mtail sp -> elabVariant ctx arms mtail sp Nothing
  -- a lambda label is only consumable by return@label (§18.5.1), which
  -- is rejected as unsupported at its use site, so the label is inert
  ELambda _ bs body sp -> elabLambda ctx bs body sp Nothing
  ELet binds body _ -> elabLet ctx binds body Nothing
  EBlock ds fin sp -> elabBlock ctx ds fin sp
  EIf alts mels sp -> do
    resT <- freshMetaV ctx
    tm <- checkIf ctx alts mels sp resT
    pure (tm, resT)
  EMatch scrut cases sp -> do
    resT <- freshMetaV ctx
    tm <- checkMatch ctx scrut cases sp resT
    pure (tm, resT)
  -- a do-scope label is only consumable by defer@label, which is
  -- rejected as unsupported at its use site, so the label is inert here
  EDo _ items sp -> elabDo ctx items sp Nothing
  EThunk e sp
    -- §5.2: soft keywords shadowed by a local binding are ordinary names
    | Just _ <- lookupCtx "thunk" ctx ->
        infer ctx (EApp (EVar (Name "thunk" sp)) [ArgExplicit e])
    | otherwise -> do
        (tm, ty) <- infer ctx e
        pure (CThunkE tm, VGlobN (gPrel "Thunk") [(Expl, ty)])
  ELazy e sp
    | Just _ <- lookupCtx "lazy" ctx ->
        infer ctx (EApp (EVar (Name "lazy" sp)) [ArgExplicit e])
    | otherwise -> do
        (tm, ty) <- infer ctx e
        pure (CLazyE tm, VGlobN (gPrel "Need") [(Expl, ty)])
  EForce e sp | Just _ <- lookupCtx "force" ctx ->
    infer ctx (EApp (EVar (Name "force" sp)) [ArgExplicit e])
  EForce e sp -> do
    (tm, ty) <- infer ctx e
    t <- forceM ty
    case t of
      VGlobN (GName _ "Thunk") [(_, a)] -> pure (CForceE tm, a)
      VGlobN (GName _ "Need") [(_, a)] -> pure (CForceE tm, a)
      _ -> do
        errAt sp "E_TYPE_EQUALITY_MISMATCH" (Just "kappa.type.mismatch") "force expects a Thunk or Need value"
        anyHole ctx
  EListLit es _ -> do
    elemT <- freshMetaV ctx
    tms <- mapM (\e -> check ctx e elemT) es
    pure
      ( foldr (\h t -> CCtor (gPrel "::") [h, t]) (CCtor (gPrel "Nil") []) tms
      , VGlobN (gPrel "List") [(Expl, elemT)]
      )
  -- no Map type or constructor exists in the prelude, so '{}' would
  -- elaborate to a stuck neutral; report it like the non-empty case
  EMapLit _ sp -> unsupported ctx sp "map literals"
  ESetLit _ sp -> unsupported ctx sp "set literals"
  ESectionLeft e op sp ->
    infer ctx (lam1 sp "__x" (\x -> EApp (EVar op) [ArgExplicit e, ArgExplicit x]))
  ESectionRight op e sp ->
    infer ctx (lam1 sp "__x" (\x -> EApp (EVar op) [ArgExplicit x, ArgExplicit e]))
  EOpRef _ op _ -> resolveName ctx op
  EReceiverSection ms args sp ->
    infer ctx . lam1 sp "__x" $ \x ->
      let base = foldl' EDot x ms
       in case args of
            [] -> base
            _ -> EApp base args
  ETry e excepts mfin sp -> elabTry ctx e excepts mfin sp
  ETryMatch e cases excepts mfin sp -> do
    tmp <- freshNameM "__scrut"
    let tn = Name tmp sp
        inner =
          EDo Nothing
            [ DoBind (LetBind False emptyPrefix (PVar tn) Nothing e sp)
            , DoExpr (EMatch (EVar tn) cases sp)
            ]
            sp
    elabTry ctx inner excepts mfin sp
  EHandle _ _ _ _ sp -> unsupported ctx sp "effect handlers"
  EEffRow _ _ sp -> unsupported ctx sp "effect rows"
  ESeal _ _ sp -> unsupported ctx sp "sealed packages"
  ESealExists _ _ _ sp -> unsupported ctx sp "existential packages"
  EOpenExists _ _ _ _ sp -> unsupported ctx sp "existential packages"
  EQuote _ sp -> unsupported ctx sp "syntax quotation"
  ESplice _ sp -> unsupported ctx sp "elaboration-time splices"
  EBang _ sp -> do
    errAt sp "E_SPLICE_OUTSIDE_DO" Nothing "monadic splice '!' is only valid inside a do block"
    anyHole ctx
  ERecordPatch e items sp -> elabPatch ctx e items sp
  EComprehension k cs y sp -> elabComprehension ctx k cs y sp
  ECaptures e _ _ -> infer ctx e -- erased capture annotation
  EKindQualified sel n sp -> elabKindQualified ctx sel n sp
  EModuleSig _ sp -> unsupported ctx sp "moduleSig"
  EImpossible sp -> do
    errAt sp "E_IMPOSSIBLE_REACHABLE" (Just "kappa.match.impossible-reachable")
      "'impossible' is not provably unreachable here"
    anyHole ctx
  EOpChain {} -> do
    -- the resolver re-associates every chain (§5.5.2); reaching one here
    -- means a resolution diagnostic was already emitted for it
    anyHole ctx
  where
    tupleField i = "_" <> T.pack (show (i + 1))
    lam1 sp nm f =
      ELambda Nothing [simpleBinder (Name nm sp)] (f (EVar (Name nm sp))) sp

check :: Ctx -> Expr -> Value -> CheckM Term
check ctx expr expected0 = do
  expected <- forceM expected0
  case (expr, expected) of
    (ELambda l bs body sp, VPi Impl q nm dom clo)
      | not (firstImplicit bs) -> do
          let ctx' = bindCtx nm True dom ctx
          cod <- clApp clo (VRigid (ctxLen ctx) [])
          inner <- check ctx' (ELambda l bs body sp) cod
          pure (CLam Impl q nm inner)
    (ELambda _ bs body sp, _) -> do
      (tm, ty) <- elabLambda ctx bs body sp (Just expected)
      expectType ctx sp ty expected
      pure tm
    (_, VPi Impl q nm dom clo)
      | not (isHole expr) -> do
          let ctx' = bindCtx nm True dom ctx
          cod <- clApp clo (VRigid (ctxLen ctx) [])
          inner <- check ctx' expr cod
          pure (CLam Impl q nm inner)
    (EVar n, VSort _)
      | Nothing <- lookupCtx (nameText n) ctx -> do
          (tm, ty) <- inferT ctx (EVar n)
          expectType ctx (nameSpan n) ty expected
          pure tm
    -- (x : T) checked against a universe is a single-field record type
    -- (§13.1); the parser cannot distinguish it from an ascription
    (EAscription (EVar _) _ sp, VSort _) -> do
      (tm, ty) <- inferT ctx expr
      expectType ctx sp ty expected
      pure tm
    -- §7.2: an application checked against a universe is a type
    -- position, so its head prefers the type facet of a same-spelling
    -- data family; arguments of sort 'Type' recurse through this same
    -- case, covering nested parenthesized type applications such as
    -- 'Wrap (Wrap Integer)' or 'List (Wrap Integer)'.
    (EApp _ _, VSort _) -> do
      (tm, ty) <- inferT ctx expr
      expectType ctx (exprSpan expr) ty expected
      pure tm
    (EIf alts mels sp, _) -> checkIf ctx alts mels sp expected
    (EMatch scrut cases sp, _) -> checkMatch ctx scrut cases sp expected
    (EDo _ items sp, _) -> do
      (tm, ty) <- elabDo ctx items sp (Just expected)
      expectType ctx sp ty expected
      pure tm
    (ELet binds body _, _) -> do
      (tm, ty) <- elabLet ctx binds body (Just expected)
      expectType ctx (exprSpan body) ty expected
      pure tm
    -- operator/receiver sections check as their lambda desugaring so
    -- the expected type guides the receiver (§16.1.6)
    (ESectionLeft e op sp, _) ->
      check ctx (lamSection sp "__x" (\x -> EApp (EVar op) [ArgExplicit e, ArgExplicit x])) expected
    (ESectionRight op e sp, _) ->
      check ctx (lamSection sp "__x" (\x -> EApp (EVar op) [ArgExplicit x, ArgExplicit e])) expected
    (EReceiverSection ms args sp, _) ->
      check ctx
        ( lamSection sp "__x" $ \x ->
            let base = foldl' EDot x ms
             in case args of
                  [] -> base
                  _ -> EApp base args
        )
        expected
    (EThunk e _, VGlobN (GName _ "Thunk") [(_, a)]) -> CThunkE <$> check ctx e a
    (ELazy e _, VGlobN (GName _ "Need") [(_, a)]) -> CLazyE <$> check ctx e a
    (_, VGlobN (GName _ "Thunk") [(_, a)]) -> do
      -- §16.1.7.1 step 0: try the suspension type itself first
      r <- tryInferAgainst expr expected
      case r of
        Just tm -> pure tm
        Nothing -> CThunkE <$> check ctx expr a
    -- expected-type-directed injection (§13.1.3) must see literals too
    (_, VVariantT members)
      | not (isVariant expr) -> do
          (tm, ty) <- infer ctx expr
          (tm1, ty1) <- insertAllImplicits ctx (exprSpan expr) tm ty
          injectInto ctx tm1 ty1 members expected (exprSpan expr)
    (EIntLit v msuf sp, _) -> do
      (tm, ty) <- elabIntLit ctx v msuf sp (Just expected)
      expectType ctx sp ty expected
      pure tm
    (EFloatLit v msuf sp, _) -> do
      (tm, ty) <- elabFloatLit ctx v msuf sp (Just expected)
      expectType ctx sp ty expected
      pure tm
    (EVariant arms mtail sp, _) -> do
      (tm, ty) <- elabVariant ctx arms mtail sp (Just expected)
      expectType ctx sp ty expected
      pure tm
    (ETuple es sp, VRecordT fs)
      | length es == length fs -> do
          -- expected-type-directed punning (§13.1.2): a parenthesized
          -- list of bare names matching the record's field names is the
          -- punned record literal
          let punVars = [(nameText n, EVar n) | EVar n <- es]
          tms <-
            if length punVars == length es && sort (map fst punVars) == map fst fs
              then forM fs $ \(fn, fty) ->
                check ctx (fromMaybe (ETuple es sp) (lookup fn punVars)) fty
              else zipWithM (\e (_, t) -> check ctx e t) es fs
          pure (CRecordV (zip (map fst fs) tms))
    _ -> do
      (tm, ty) <- infer ctx expr
      (tm1, ty1) <- insertAllImplicits ctx (exprSpan expr) tm ty
      expectType ctx (exprSpan expr) ty1 expected
      pure tm1
  where
    tryInferAgainst e t = do
      saved <- get
      (tm, ty) <- infer ctx e
      ok <- unify ctx ty t
      if ok then pure (Just tm) else put saved >> pure Nothing
    firstImplicit (b : _) = bImplicit b
    firstImplicit [] = False
    isHole = \case
      EHole {} -> True
      _ -> False
    isVariant = \case
      EVariant {} -> True
      _ -> False

-- helper shared by section desugarings
lamSection :: Span -> Text -> (Expr -> Expr) -> Expr
lamSection sp nm f =
  ELambda Nothing [simpleBinder (Name nm sp)] (f (EVar (Name nm sp))) sp

-- expected-type-directed injection / widening (§13.1.3)
injectInto :: Ctx -> Term -> Value -> [Value] -> Value -> Span -> CheckM Term
injectInto ctx tm ty members expected sp = do
  t <- forceM ty
  case t of
    VVariantT src -> do
      srcTags <- mapM (tagOf ctx) src
      tgtTags <- mapM (tagOf ctx) members
      if all (`elem` tgtTags) srcTags
        then pure tm
        else do
          expectType ctx sp ty expected
          pure tm
    _ -> do
      tag <- tagOf ctx t
      tags <- mapM (tagOf ctx) members
      if tag `elem` tags
        then pure (CInject tag tm)
        else do
          expectType ctx sp ty expected
          pure tm

-- | Stable member identity of a variant member type (§31.3): rendered
-- from the alias-normalized type so @Int@ and @Integer@ coincide.
tagOf :: Ctx -> Value -> CheckM Text
tagOf ctx v = do
  ec <- ec_
  pure (renderTerm (quote ec (ctxLen ctx) (deepForceV ec v)))

-- normalize alias heads recursively through type structure
deepForceV :: EvalCtx -> Value -> Value
deepForceV ec = go (32 :: Int)
  where
    go :: Int -> Value -> Value
    go 0 v = v
    go fuel v = case force ec v of
      VGlobN g sp -> VGlobN g [(ic, go (fuel - 1) a) | (ic, a) <- sp]
      VCtor g as -> VCtor g (map (go (fuel - 1)) as)
      VRecordT fs -> VRecordT [(n, go (fuel - 1) t) | (n, t) <- fs]
      VVariantT ms -> VVariantT (map (go (fuel - 1)) ms)
      v' -> v'

inferType :: Ctx -> Expr -> CheckM (Term, Int)
inferType ctx e = do
  (tm, ty) <- inferT ctx e
  goSort tm ty
  where
    goSort tm ty = do
      t <- forceM ty
      case t of
        VSort n -> pure (tm, n)
        VFlex m [] -> solveMeta m (VSort 0) >> pure (tm, 0)
        other -> do
          oT <- quoteIn ctx other
          errAt (exprSpan e) "E_NOT_A_TYPE" (Just "kappa.type.expected-type")
            ("expected a type; this expression has type " <> renderTerm oT)
          pure (tm, 0)

-- type-position inference: prefer the type facet for head names (§7.2).
inferT :: Ctx -> Expr -> CheckM (Term, Value)
inferT ctx e = case e of
  -- in type position a universe spelling (incl. '*') is the universe
  EVar n
    | Nothing <- lookupCtx (nameText n) ctx
    , Just lvl <- sortName (nameText n) ->
        pure (CSort lvl, VSort (lvl + 1))
  EVar n
    | Nothing <- lookupCtx (nameText n) ctx
    , Nothing <- sortName (nameText n) -> do
        mg <- lookupGlobalName (nameText n)
        case mg of
          Just g -> do
            mt <- globalType g
            case mt of
              Just r -> pure r
              Nothing -> infer ctx e
          Nothing -> infer ctx e
  EApp f args -> do
    (fTm, fTy) <- inferT ctx f
    elabSpine ctx (exprSpan f) fTm fTy args
  -- a parenthesized tuple in type position is a positional record type
  -- (§13.1): (Integer, String) ≡ (_1 : Integer, _2 : String)
  ETuple es _ -> do
    fields <- forM (zip [1 :: Int ..] es) $ \(i, fe) -> do
      (t, _) <- inferType ctx fe
      pure ("_" <> T.pack (show i), t)
    pure (CRecordT fields, VSort 0)
  -- (x : T) in type position is a single-field record type (§13.1); the
  -- parser cannot distinguish it from an ascription
  EAscription (EVar n) tyE _
    | isLowerName (nameText n) -> do
        (t, _) <- inferType ctx tyE
        pure (CRecordT [(nameText n, t)], VSort 0)
  _ -> infer ctx e
  where
    isLowerName t = case T.uncons t of
      Just (c, _) -> c >= 'a' && c <= 'z'
      Nothing -> False

elabForall :: Ctx -> [Binder] -> Expr -> CheckM (Term, Value)
elabForall ctx0 bs0 body = go ctx0 bs0
  where
    go ctx [] = do
      (tm, _) <- inferType ctx body
      pure (tm, VSort 0)
    go ctx (b : rest) = do
      domTm <- case bType b of
        Just t -> fst <$> inferType ctx t
        Nothing -> pure (CSort 0) -- `forall a.` binds a : Type (§11.3)
      domV <- evalIn ctx domTm
      let nm = maybe "_" nameText (bName b)
          q = maybe Q0 (qOf . Just) (bpQuantity (bPrefix b))
          ctx' = bindCtx nm False domV ctx
      (restTm, _) <- go ctx' rest
      pure (CPi Impl q nm domTm restTm, VSort 0)

-- application spine (§16.1.7.1)
elabSpine :: Ctx -> Span -> Term -> Value -> [Arg] -> CheckM (Term, Value)
elabSpine _ _ fTm fTy [] = pure (fTm, fTy)
elabSpine ctx sp fTm fTy0 (arg : rest) = do
  fTy <- forceM fTy0
  case (arg, fTy) of
    (ArgImplicit e, VPi Impl _ _ dom clo) -> do
      aTm <- check ctx e dom
      aV <- evalIn ctx aTm
      ty' <- clApp clo aV
      elabSpine ctx sp (CApp Impl fTm aTm) ty' rest
    (_, VPi Impl _ _ dom clo) -> do
      iTm <- resolveImplicit ctx sp dom
      iV <- evalIn ctx iTm
      ty' <- clApp clo iV
      elabSpine ctx sp (CApp Impl fTm iTm) ty' (arg : rest)
    (ArgExplicit e, VPi Expl _ _ dom clo) -> do
      aTm <- check ctx e dom
      aV <- evalIn ctx aTm
      ty' <- clApp clo aV
      elabSpine ctx sp (CApp Expl fTm aTm) ty' rest
    (ArgExplicit e, VFlex m []) -> do
      dom <- freshMetaV ctx
      codM <- freshMeta
      domT <- quoteIn ctx dom
      piV <- evalIn ctx (CPi Expl QW "_a" domT codM)
      solveMeta m piV
      elabSpine ctx sp fTm piV (ArgExplicit e : rest)
    (ArgNamedBlock items bsp, _) -> elabNamedBlock ctx fTm fTy items bsp rest
    (ArgInout _ isp, _) -> unsupported ctx isp "inout call-site arguments (~)"
    (ArgImplicit e, _) -> do
      errAt (exprSpan e) "E_APPLICATION_ARGUMENT_MISMATCH" (Just "kappa.application.argument")
        "an explicit implicit argument was supplied, but the callee has no implicit parameter here (§16.1.7.1)"
      pure (fTm, fTy)
    (ArgExplicit e, _)
      -- a saturated constructor given extra arguments (§10.1.1)
      | Just _ <- termHeadCtor fTm -> do
          errAt (exprSpan e) "E_CONSTRUCTOR_ARITY_MISMATCH" (Just "kappa.application.arity")
            "too many arguments in constructor application"
          anyHole ctx
      | otherwise -> do
          fT <- quoteIn ctx fTy
          report $
            withNote ("callee type: " <> renderTerm fT) $
              diag SevError StageElaborate "E_APPLICATION_NONCALLABLE" (Just "kappa.application.non-callable")
                (exprSpan e)
                "this expression is not callable"
          anyHole ctx
  where
    termHeadCtor = \case
      CApp _ f _ -> termHeadCtor f
      CLam _ _ _ b -> termHeadCtor b
      CCtor g _ -> Just g
      _ -> Nothing

-- named constructor application (§10.1.1): supplied fields + defaults in
-- constructor order.
elabNamedBlock :: Ctx -> Term -> Value -> [(Name, Maybe Expr)] -> Span -> [Arg] -> CheckM (Term, Value)
elabNamedBlock ctx fTm fTy items sp rest = do
  st <- get
  forM_ (duplicatesOf [nameText n | (n, _) <- items]) $ \dn ->
    errAt sp "E_NAMED_ARG_DUPLICATE" (Just "kappa.application.named")
      ("named argument '" <> dn <> "' is supplied more than once")
  mCtorG <- case ctorOf fTm of
    Just g -> pure (Just g)
    Nothing -> case fTm of
      -- a local rebinding of a constructor (§16.1.7.2): the binding's
      -- definiens reveals the constructor
      CVar i -> case drop i (ctxEnv ctx) of
        (v : _) -> do
          v' <- forceM v
          pure (valueCtorOf v')
        [] -> pure Nothing
      _ -> pure Nothing
  case mCtorG of
    Just g | Just ci <- Map.lookup g (csCtors st) -> do
      let fieldNames = mapMaybe fst (ciFields ci)
      forM_ items $ \(n, _) ->
        unless (nameText n `elem` fieldNames) $
          errAt (nameSpan n) "E_NAMED_ARG_UNKNOWN" (Just "kappa.application.named")
            ("constructor has no named parameter '" <> nameText n <> "'")
      let supplied = [(nameText n, fromMaybe (EVar n) me) | (n, me) <- items]
      args <- forM (ciFields ci) $ \(mname, mdef) ->
        case mname >>= \fn -> lookup fn supplied of
          Just e -> pure (Just (mname, False, Left e))
          Nothing -> case mdef of
            -- field default (§10.1.1): elaborated here, at the
            -- application site, against the field's type, with the
            -- earlier field arguments in scope
            Just d -> pure (Just (mname, True, Left d))
            Nothing -> do
              errAt sp "E_NAMED_ARG_MISSING" (Just "kappa.application.named")
                ("missing constructor argument" <> maybe "" (\n -> " '" <> n <> "'") mname)
              pure Nothing
      -- run the spine with mixed surface/core arguments
      goSpine ctx fTm fTy (catMaybes args)
    -- ordinary function: match named items against the remaining
    -- explicit Pi binder names (§16.1.7.2)
    _ -> goPiNamed fTm fTy [(nameText n, fromMaybe (EVar n) me) | (n, me) <- items]
  where
    ctorOf = \case
      CLam _ _ _ b -> ctorOf b
      CCtor g _ -> Just g
      CGlob g -> Just g
      _ -> Nothing
    valueCtorOf = \case
      VCtor g _ -> Just g
      VLam _ _ _ (Closure _ body) -> ctorOf body
      VGlobN g _ -> Just g
      _ -> Nothing
    goPiNamed tm ty0 remaining = do
      ty <- forceM ty0
      case ty of
        VPi Impl _ _ dom clo -> do
          iTm <- resolveImplicit ctx sp dom
          iV <- evalIn ctx iTm
          ty' <- clApp clo iV
          goPiNamed (CApp Impl tm iTm) ty' remaining
        VPi Expl _ nm dom clo
          | Just e <- lookup nm remaining -> do
              aTm <- check ctx e dom
              aV <- evalIn ctx aTm
              ty' <- clApp clo aV
              goPiNamed (CApp Expl tm aTm) ty' [(n, x) | (n, x) <- remaining, n /= nm]
          | not (null remaining) -> do
              errAt sp "E_NAMED_ARG_MISSING" (Just "kappa.application.named")
                ("missing named argument '" <> nm <> "'")
              pure (tm, ty)
        _
          | null remaining -> elabSpine ctx sp tm ty rest
          | otherwise -> do
              forM_ remaining $ \(n, _) ->
                errAt sp "E_NAMED_ARG_UNKNOWN" (Just "kappa.application.named")
                  ("callee has no named parameter '" <> n <> "'")
              pure (tm, ty)
    goSpine _ tm ty [] = elabSpine ctx sp tm ty rest
    goSpine ctxAcc tm ty0 (a@(_, _, _) : as) = do
      ty <- forceM ty0
      case ty of
        VPi Impl _ _ dom clo -> do
          iTm <- resolveImplicit ctx sp dom
          iV <- evalIn ctx iTm
          ty' <- clApp clo iV
          goSpine ctxAcc (CApp Impl tm iTm) ty' (a : as)
        VPi Expl _ _ dom clo -> do
          let (mname, isDefault, payload) = a
              argCtx = if isDefault then ctxAcc else ctx
          (aTm, aV) <- case payload of
            Left e -> do
              aTm0 <- check argCtx e dom
              aV <- evalIn argCtx aTm0
              if isDefault
                then do
                  -- a default's term lives under the accumulated field
                  -- bindings; re-quote its value at the outer depth
                  aTm1 <- quoteIn ctx aV
                  pure (aTm1, aV)
                else pure (aTm0, aV)
            Right coreTm -> (,) coreTm <$> evalIn argCtx coreTm
          ty' <- clApp clo aV
          let ctxAcc' = case mname of
                Just fn -> bindCtxLet fn False dom aV ctxAcc
                Nothing -> ctxAcc
          goSpine ctxAcc' (CApp Expl tm aTm) ty' as
        _ -> do
          errAt sp "E_CONSTRUCTOR_ARITY_MISMATCH" (Just "kappa.application.arity")
            "too many constructor arguments"
          pure (tm, ty)

-- ── Literals (§6.1.5, §6.1.6) ────────────────────────────────────────

elabIntLit :: Ctx -> Integer -> Maybe Name -> Span -> Maybe Value -> CheckM (Term, Value)
elabIntLit ctx v msuf sp mexp = case msuf of
  Just suf -> do
    (fTm, fTy) <- resolveName ctx suf
    elabSpine ctx sp fTm fTy [ArgExplicit (EIntLit v Nothing sp)] -- payload : Nat
  Nothing -> do
    expected <- maybe (pure Nothing) (fmap Just . forceM) mexp
    case expected of
      Just t
        | isNumHead t -> pure (CLit (LitInt v), t)
        | Just other <- nonDefault t -> do
            -- FromInteger elaboration (§6.1.5)
            dict <- resolveImplicit ctx sp (VGlobN (gPrel "FromInteger") [(Expl, other)])
            pure (CApp Expl (CProj dict "fromInteger") (CLit (LitInt v)), other)
      _ -> pure (CLit (LitInt v), VGlobN (gPrel "Int") []) -- defaulting (§6.1.5)
  where
    isNumHead = \case
      VGlobN (GName _ n) [] -> n `elem` ["Int", "Nat", "Integer"]
      _ -> False
    nonDefault = \case
      VFlex {} -> Nothing
      t@(VGlobN (GName _ n) [])
        | n `elem` ["Float", "Double"] -> Just t
      t@VGlobN {} -> Just t
      _ -> Nothing

elabFloatLit :: Ctx -> Double -> Maybe Name -> Span -> Maybe Value -> CheckM (Term, Value)
elabFloatLit ctx v msuf sp mexp = case msuf of
  Just suf -> do
    (fTm, fTy) <- resolveName ctx suf
    elabSpine ctx sp fTm fTy [ArgExplicit (EFloatLit v Nothing sp)]
  Nothing -> do
    expected <- maybe (pure Nothing) (fmap Just . forceM) mexp
    case expected of
      Just t
        | isFloatHead t -> pure (CLit (LitDouble v), t)
        | Just other <- nonDefault t -> do
            -- FromFloat elaboration (§6.1.5)
            dict <- resolveImplicit ctx sp (VGlobN (gPrel "FromFloat") [(Expl, other)])
            pure (CApp Expl (CProj dict "fromFloat") (CLit (LitDouble v)), other)
      _ -> pure (CLit (LitDouble v), VGlobN (gPrel "Double") []) -- defaulting (§6.1.5)
  where
    isFloatHead = \case
      VGlobN (GName _ n) [] -> n `elem` ["Float", "Double"]
      _ -> False
    nonDefault = \case
      VFlex {} -> Nothing
      t@VGlobN {} -> Just t
      _ -> Nothing

elabString :: Ctx -> StringLit -> [InterpPart] -> Span -> CheckM (Term, Value)
elabString ctx sl parts sp = case (slPrefix sl, parts) of
  (Nothing, _) ->
    -- interpolation applies only to prefixed strings (§6.3.4)
    case slFragments sl of
      [FragLit t] -> pure (CLit (LitStr t), VGlobN (gPrel "String") [])
      [] -> pure (CLit (LitStr ""), VGlobN (gPrel "String") [])
      _ -> do
        errAt sp "E_INTERNAL" Nothing "plain string with interpolation fragments"
        anyHole ctx
  (Just "f", _) -> do
    -- conventional f-string: concatenate shows of interpolations
    let strTy = VGlobN (gPrel "String") []
    pieces <- forM (zip [0 ..] (slFragments sl)) $ \(i, frag) -> case frag of
      FragLit t -> pure (CLit (LitStr t))
      FragInterp _ _ -> interpPiece i
      FragInterpFmt _ _ _ -> interpPiece i
    let appendG a b = CApp Expl (CApp Expl (CGlob (gPrel "stringAppend")) a) b
    pure (foldr appendG (CLit (LitStr "")) pieces, strTy)
    where
      interpPiece i = case [ipExpr p | p <- parts, ipIndex p == i] of
        [e] -> do
          (tm, ty) <- infer ctx e
          (tm1, ty1) <- insertAllImplicits ctx sp tm ty
          showDict <- resolveImplicit ctx sp (VGlobN (gPrel "Show") [(Expl, ty1)])
          pure (CApp Expl (CProj showDict "show") tm1)
        _ -> pure (CLit (LitStr ""))
  (Just p, _) -> do
    -- §6.3.4: the prefix is resolved by ordinary term name resolution;
    -- an unknown prefix is an unresolved name, a known one names a
    -- literal handler this implementation does not provide.
    resolvable <- prefixResolves ctx p
    if resolvable
      then do
        _ <- unsupported ctx sp ("the '" <> p <> "' string-literal handler")
        pure (CLit (LitStr ""), VGlobN (gPrel "String") [])
      else do
        errAt sp "E_NAME_UNRESOLVED" (Just "kappa.name.unresolved")
          ("unresolved name '" <> p <> "' used as a string-literal prefix (Spec §6.3.4)")
        pure (CLit (LitStr ""), VGlobN (gPrel "String") [])

-- ── Records, projections, patches ────────────────────────────────────

elabRecordLit :: Ctx -> [RecItem] -> Span -> CheckM (Term, Value)
elabRecordLit ctx items sp = do
  rs <- forM items $ \(RecItem _ n mv) -> do
    let e = fromMaybe (EVar n) mv -- punning
    (tm, ty) <- infer ctx e
    (tm1, ty1) <- insertAllImplicits ctx (nameSpan n) tm ty
    pure (nameText n, tm1, ty1)
  forM_ (duplicatesOf [n | (n, _, _) <- rs]) $ \n ->
    errAt sp "E_RECORD_DUPLICATE_FIELD" (Just "kappa.record.duplicate-field")
      ("record literal has duplicate field '" <> n <> "'")
  -- evaluate fields in source order via lets, assemble canonically
  let sorted = sortOn (\(n, _, _) -> n) rs
  pure
    ( CRecordV [(n, tm) | (n, tm, _) <- sorted]
    , VRecordT [(n, ty) | (n, _, ty) <- sorted]
    )

-- | Names that occur more than once (each reported once).
duplicatesOf :: [Text] -> [Text]
duplicatesOf ns = nub [n | n <- ns, length (filter (== n) ns) > 1]

elabDot :: Ctx -> Expr -> DotMember -> CheckM (Term, Value)
elabDot ctx e member = do
  let mname = case member of
        DotName n -> n
        DotOperator n -> n
  -- reified module objects: (module a).b chains (§2.8.6)
  case modObjPathOf e of
    Just segs -> elabModuleMember ctx (segs ++ [nameText mname]) (nameSpan mname)
    Nothing -> do
      -- fully-qualified module path, e.g. std.prelude.Bool or main.T (§8.3)
      mPath <- case modulePathOf e of
        Just segs@(s0 : _) | Nothing <- lookupCtx s0 ctx -> do
          let mn = ModuleName segs
              g = GName mn (nameText mname)
          st <- get
          if (Map.member g (csGlobals st) || Map.member g (csCtors st))
            && memberVisible st mn (nameText mname)
            then globalTerm g
            else pure Nothing
        _ -> pure Nothing
      case mPath of
        Just r -> pure r
        Nothing -> elabDotUnqualified ctx e member mname
  where
    modulePathOf = \case
      EVar (Name s _) -> Just [s]
      EDot inner (DotName (Name s _)) -> (++ [s]) <$> modulePathOf inner
      _ -> Nothing
    modObjPathOf = \case
      EKindQualified SelModule (Name s _) _ -> Just [s]
      EDot inner (DotName (Name s _)) -> (++ [s]) <$> modObjPathOf inner >>= ensureModObj
      _ -> Nothing
      where
        ensureModObj segs = Just segs

-- visibility of a member of another module (§8.5): only exported names
-- are accessible from outside the defining module
memberVisible :: CheckState -> ModuleName -> Text -> Bool
memberVisible st mn nm =
  mn == csModule st
    || case Map.lookup mn (csModuleExports st) of
      Just ex -> nm `elem` ex
      Nothing -> True -- prelude and unknown modules: unrestricted

-- a member completion of a reified module path: either a deeper module
-- object or nothing nameable (§2.8.6)
elabModuleMember :: Ctx -> [Text] -> Span -> CheckM (Term, Value)
elabModuleMember ctx segs sp = do
  st <- get
  if Map.member (ModuleName segs) (csModuleExports st) || ModuleName segs == csModule st
    then pure moduleObject
    else do
      errAt sp "E_STATIC_OBJECT_UNRESOLVED" (Just "kappa.name.unresolved")
        ("no module named '" <> T.intercalate "." segs <> "' is in this compilation unit (Spec §2.8.6)")
      anyHole ctx

-- §2.8.6 kind-qualified static-object expressions: select the named
-- facet; an unknown subject is E_STATIC_OBJECT_UNRESOLVED.
elabKindQualified :: Ctx -> KindSelector -> Name -> Span -> CheckM (Term, Value)
elabKindQualified ctx sel (Name n nsp) sp = case sel of
  SelModule -> do
    st <- get
    let known =
          Map.member (ModuleName [n]) (csModuleExports st)
            || Map.member n (csModuleAliases st)
    if known
      then pure moduleObject
      else do
        errAt sp "E_STATIC_OBJECT_UNRESOLVED" (Just "kappa.name.unresolved")
          ("no module named '" <> n <> "' is in scope (Spec §2.8.6)")
        anyHole ctx
  _ -> do
    mg <- lookupGlobalName n
    mr <- case mg of
      Just g -> globalType g
      Nothing -> pure Nothing
    case mr of
      Just r -> pure r
      Nothing -> do
        errAt nsp "E_STATIC_OBJECT_UNRESOLVED" (Just "kappa.name.unresolved")
          ("kind-qualified name does not resolve to a static object: '" <> n <> "' (Spec §2.8.6)")
        anyHole ctx

-- the trivial reified module object (§2.8.6): identity only
moduleObject :: (Term, Value)
moduleObject = (CRecordV [], VRecordT [])

elabDotUnqualified :: Ctx -> Expr -> DotMember -> Name -> CheckM (Term, Value)
elabDotUnqualified ctx e member mname = do
  -- module-qualified reference?
  case e of
    EVar (Name base _) -> do
      st <- get
      case lookupCtx base ctx of
        Just (i, _) -> do
          -- a local rebinding of a reified type object (§2.8.3): its
          -- definiens names the data type, select the constructor
          mv <- case drop i (ctxEnv ctx) of
            (v : _) -> Just <$> forceM v
            [] -> pure Nothing
          case mv of
            Just (VGlobN d _)
              | Just di <- Map.lookup d (csDatas st)
              , (ctorG : _) <- [c | c <- diCtors di, gnameText c == nameText mname] -> do
                  mt <- globalTerm ctorG
                  case mt of
                    Just r -> pure r
                    Nothing -> ordinary mname
            _ -> ordinary mname
        Nothing ->
          case Map.lookup base (csModuleAliases st) of
            Just modName -> do
              let g = GName modName (nameText mname)
              mt <-
                if memberVisible st modName (nameText mname)
                  then globalTerm g
                  else pure Nothing -- private members are not accessible (§8.5)
              case mt of
                Just r -> pure r
                Nothing -> do
                  errAt (nameSpan mname) "E_NAME_UNRESOLVED" (Just "kappa.name.unresolved")
                    ("module '" <> base <> "' has no exported member '" <> nameText mname <> "' (Spec §8.5)")
                  anyHole ctx
            Nothing -> do
              -- static member of a type: T.C selects constructor (§7.3)
              mg <- lookupGlobalName base
              stx <- get
              mDataG <- case mg of
                Just tyG
                  | Map.member tyG (csDatas stx) -> pure (Just tyG)
                  | Just gd <- Map.lookup tyG (csGlobals stx)
                  , Just v <- gdValue gd -> do
                      -- a rebound reified type object (§2.8.3): the
                      -- binding's value names the data type
                      v' <- forceM v
                      pure $ case v' of
                        VGlobN d _ | Map.member d (csDatas stx) -> Just d
                        _ -> Nothing
                _ -> pure Nothing
              case mDataG of
                Just tyG
                  | Just di <- Map.lookup tyG (csDatas stx)
                  , Just ctorG <- lookupCtorIn di (nameText mname) -> do
                      mt <- globalTerm ctorG
                      case mt of
                        Just r -> pure r
                        Nothing -> anyHole ctx
                _ -> ordinary mname
              where
                lookupCtorIn di nm =
                  case [c | c <- diCtors di, gnameText c == nm] of
                    (c : _) -> Just c
                    [] -> Nothing
    _ -> ordinary mname
  where
    ordinary mn0 = do
      (tm, ty) <- infer ctx e
      (tm1, ty1) <- insertAllImplicits ctx (exprSpan e) tm ty
      t <- forceM ty1
      case t of
        VRecordT fs
          | Just fty <- lookup (nameText mn0) fs ->
              pure (CProj tm1 (nameText mn0), fty)
          | otherwise -> do
              -- a record receiver without the field: try method sugar,
              -- otherwise report the missing field (§13.1.4)
              mg <- lookupGlobalName (nameText mn0)
              case mg of
                Just _ -> methodSugar tm1 t mn0
                Nothing -> do
                  errAt (nameSpanOf member) "E_RECORD_PROJECTION_MISSING_FIELD"
                    (Just "kappa.record.unknown-field")
                    ("record has no field '" <> nameText mn0
                       <> "' (fields: " <> T.intercalate ", " (map fst fs) <> ")")
                  anyHole ctx
        -- trait-dictionary member projection d.(==) (§14.2.1)
        VGlobN headG spine -> do
          st <- get
          case Map.lookup headG (csTraits st) of
            Just ti
              | nameText mn0 `elem` tiMembers ti -> do
                  memberTy <- memberTypeOf headG (nameText mn0) (map snd spine) tm1
                  pure (CProj tm1 (nameText mn0), memberTy)
            _ ->
              -- named-field projection on single-constructor data (§10.2)
              case Map.lookup headG (csDatas st) of
                Just di
                  | [ctorG] <- diCtors di
                  , Just ci <- Map.lookup ctorG (csCtors st)
                  , Just idx <- elemIndex (Just (nameText mn0)) (map fst (ciFields ci)) -> do
                      fieldTys <- ctorFieldTypes ctx ctorG ci t (nameSpanOf member)
                      fty <- case drop idx fieldTys of
                        (x : _) -> pure x
                        [] -> freshMetaV ctx
                      let arity = length (ciFields ci)
                          pats = [if i == idx then CPVar "__field" else CPWild | i <- [0 .. arity - 1]]
                      pure (CMatch tm1 [CaseAlt (CPCtor ctorG pats) Nothing (CVar 0)], fty)
                _ -> methodSugar tm1 t mn0
        _ -> methodSugar tm1 t mn0

    -- method-call sugar (§7.4): recv.name args → name recv (receiver
    -- insertion at the first explicit binder).
    methodSugar recvTm recvTy mn0 = do
      mg <- lookupGlobalName (nameText mn0)
      case mg of
        Just g -> do
          mt <- globalTerm g
          case mt of
            Just (fTm, fTy) -> applyRecv fTm fTy recvTm recvTy
            Nothing -> failMember recvTy mn0
        Nothing -> failMember recvTy mn0

    applyRecv fTm fTy0 recvTm recvTy = do
      fTy <- forceM fTy0
      case fTy of
        VPi Impl _ _ dom clo -> do
          iTm <- resolveImplicit ctx (nameSpanOf member) dom
          iV <- evalIn ctx iTm
          ty' <- clApp clo iV
          applyRecv (CApp Impl fTm iTm) ty' recvTm recvTy
        VPi Expl _ _ dom clo -> do
          expectType ctx (exprSpan e) recvTy dom
          rV <- evalIn ctx recvTm
          ty' <- clApp clo rV
          pure (CApp Expl fTm recvTm, ty')
        _ -> do
          errAt (nameSpanOf member) "E_APPLICATION_NONCALLABLE" (Just "kappa.application.non-callable")
            "member is not callable with a receiver"
          anyHole ctx

    failMember recvTy mn0 = do
      rT <- quoteIn ctx recvTy
      report $
        withNote ("receiver type: " <> renderTerm rT) $
          diag SevError StageElaborate "E_UNRESOLVED_MEMBER" (Just "kappa.name.unresolved-member")
            (nameSpanOf member)
            ("no member '" <> nameText mn0 <> "' on this receiver (§7.3)")
      anyHole ctx

    nameSpanOf = \case
      DotName n -> nameSpan n
      DotOperator n -> nameSpan n

memberTypeOf :: GName -> Text -> [Value] -> Term -> CheckM Value
memberTypeOf traitG member args dictTm = do
  -- member projection type: stored as global "<trait>.<member>" Pi type;
  -- here we re-derive from the member-projection global.
  mt <- globalTerm (memberGlobal traitG member)
  case mt of
    Just (_, ty) -> peel ty args
    Nothing -> pure (VSort 0)
  where
    peel ty [] = do
      t <- forceM ty
      case t of
        VPi Impl _ _ _ clo -> do
          dv <- evalInEmpty dictTm
          clApp clo dv
        _ -> pure t
    peel ty (a : as) = do
      t <- forceM ty
      case t of
        VPi Impl _ _ _ clo -> do
          r <- clApp clo a
          peel r as
        _ -> pure t
    evalInEmpty tm = do
      ec <- ec_
      pure (eval ec [] tm)

memberGlobal :: GName -> Text -> GName
memberGlobal (GName m t) member = GName m (t <> "." <> member)

-- safe navigation e?.m (§16.1.1.2)
elabSafeNav :: Ctx -> Expr -> DotMember -> CheckM (Term, Value)
elabSafeNav ctx e member = do
  (pTm, pTy) <- infer ctx e
  (pTm1, pTy1) <- insertAllImplicits ctx (exprSpan e) pTm pTy
  t <- forceM pTy1
  case t of
    VGlobN (GName _ "Option") [(_, payloadTy)] -> do
      -- bind __x : payload, elaborate body member access
      let nm = "__nav"
          ctx' = bindCtx nm False payloadTy ctx
      (bodyTm, bodyTy) <- elabDot ctx' (EVar (Name nm (memberSpan member))) member
      bodyT <- forceM bodyTy
      (wrapTm, resTy) <- case bodyT of
        VGlobN (GName _ "Option") [(_, u)] -> pure (bodyTm, u)
        VFlex {} -> do
          errAt (memberSpan member) "E_SAFE_NAV_GENERIC_AMBIGUOUS" (Just "kappa.type.mismatch")
            "the result type of '?.' is undetermined; annotate the member type (§16.1.1.2)"
          pure (bodyTm, bodyT)
        u -> pure (CCtor (gPrel "Some") [bodyTm], u)
      let alts =
            [ CaseAlt (CPCtor (gPrel "Some") [CPVar "__nav"]) Nothing wrapTm
            , CaseAlt (CPCtor (gPrel "None") []) Nothing (CCtor (gPrel "None") [])
            ]
      pure (CMatch pTm1 alts, VGlobN (gPrel "Option") [(Expl, resTy)])
    _ -> do
      errAt (exprSpan e) "E_TYPE_EQUALITY_MISMATCH" (Just "kappa.type.mismatch")
        "the receiver of '?.' must have type Option T (§16.1.1.2)"
      anyHole ctx
  where
    memberSpan = \case
      DotName n -> nameSpan n
      DotOperator n -> nameSpan n

elabIs :: Ctx -> Expr -> CtorRef -> CheckM (Term, Value)
elabIs ctx e cref = do
  (tm, ty) <- infer ctx e
  (tm1, _) <- insertAllImplicits ctx (exprSpan e) tm ty
  mg <- resolveCtor ctx cref
  case mg of
    Just (g, ci) -> do
      let arity = length (ciFields ci)
          alts =
            [ CaseAlt (CPCtor g (replicate arity CPWild)) Nothing (CCtor (gPrel "True") [])
            , CaseAlt CPWild Nothing (CCtor (gPrel "False") [])
            ]
      pure (CMatch tm1 alts, VGlobN (gPrel "Bool") [])
    Nothing -> anyHole ctx

resolveCtor :: Ctx -> CtorRef -> CheckM (Maybe (GName, CtorInfo))
resolveCtor _ (CtorRef mqual n) = do
  st <- get
  let candidates = case mqual of
        Nothing ->
          [ g | (g, _) <- Map.toList (csCtors st), gnameText g == nameText n
          , inScope st g
          ]
        Just q ->
          [ ctorG
          | (dg, di) <- Map.toList (csDatas st)
          , gnameText dg == nameText q
          , inScope st dg
          , ctorG <- diCtors di
          , gnameText ctorG == nameText n
          ]
  case candidates of
    (g : _) -> do
      pure ((,) g <$> Map.lookup g (csCtors st))
    [] -> do
      errAt (nameSpan n) "E_NAME_UNRESOLVED" (Just "kappa.name.unresolved")
        ("unresolved constructor '" <> nameText n <> "'")
      pure Nothing
  where
    inScope st g@(GName m _) =
      m == csModule st || Map.lookup (gnameText g) (csScope st) == Just g || isPrel m
    isPrel m = m == preludeModule

-- record patch (§13.2.5): closed records, '='-updates only.
elabPatch :: Ctx -> Expr -> [PatchItem] -> Span -> CheckM (Term, Value)
elabPatch ctx e items sp = do
  (tm, ty) <- infer ctx e
  (tm1, ty1) <- insertAllImplicits ctx (exprSpan e) tm ty
  t <- forceM ty1
  case t of
    VRecordT fs -> do
      let updateNames = [nameText n | PatchUpdate [(False, n)] _ <- items]
      forM_ (duplicatesOf updateNames) $ \n ->
        errAt sp "E_RECORD_PATCH_DUPLICATE_PATH" (Just "kappa.record.patch-duplicate")
          ("record patch updates field '" <> n <> "' more than once (§13.2.5)")
      updates <- forM items $ \case
        PatchUpdate [(False, n)] (PatchValue v) -> do
          case lookup (nameText n) fs of
            Just fty -> do
              vt <- check ctx v fty
              pure (Just (nameText n, vt))
            Nothing -> do
              errAt (nameSpan n) "E_UNKNOWN_FIELD" (Just "kappa.record.unknown-field")
                ("record has no field '" <> nameText n <> "'")
              pure Nothing
        PatchUpdate _ _ -> do
          errAt sp "E_UNSUPPORTED" Nothing "nested or implicit patch paths are not supported by this implementation"
          pure Nothing
        PatchExtend n _ -> do
          errAt (nameSpan n) "E_UNSUPPORTED" Nothing "row extension ':=' requires open records, which this implementation does not support"
          pure Nothing
        PatchSection _ _ -> do
          errAt sp "E_UNSUPPORTED" Nothing "projection-section updates are not supported by this implementation"
          pure Nothing
      let ups = catMaybes updates
          fields = [(n, fromMaybe (CProj tm1 n) (lookup n ups)) | (n, _) <- fs]
      pure (CRecordV fields, t)
    _ -> do
      errAt sp "E_TYPE_EQUALITY_MISMATCH" (Just "kappa.type.mismatch") "record patch requires a closed record"
      anyHole ctx

-- ── Variants ─────────────────────────────────────────────────────────

elabVariant :: Ctx -> [VariantArm] -> Maybe Expr -> Span -> Maybe Value -> CheckM (Term, Value)
elabVariant ctx arms mtail sp mexpected = do
  when (isJust mtail) . void $ unsupported ctx sp "open variant rows"
  expected <- traverse forceM mexpected
  case (arms, expected) of
    -- single arm in term position: injection
    ([VariantArm payload mty], Just (VVariantT members)) -> do
      (tm, ty) <- case mty of
        Just tyE -> do
          (tyTm, _) <- inferType ctx tyE
          tyV <- evalIn ctx tyTm
          (,tyV) <$> check ctx payload tyV
        Nothing -> infer ctx payload
      tm2 <- injectInto ctx tm ty members (VVariantT members) sp
      pure (tm2, VVariantT members)
    _ -> do
      -- type formation: every arm is a type
      memberTms <- forM arms $ \(VariantArm e mty) -> do
        when (isJust mty) $
          errAt sp "E_VARIANT_ARM" Nothing "variant type arms do not take ascriptions"
        fst <$> inferType ctx e
      memberVs <- mapM (evalIn ctx) memberTms
      tags <- mapM (tagOf ctx) memberVs
      let canon = map snd (sortOn fst (zip tags memberTms))
      when (length (nub tags) /= length tags) $
        errAt sp "E_VARIANT_DUPLICATE" (Just "kappa.variant.duplicate-member")
          "duplicate variant member types"
      pure (CVariantT canon, VSort 0)

-- ── Lambdas, lets, blocks ────────────────────────────────────────────

elabLambda :: Ctx -> [Binder] -> Expr -> Span -> Maybe Value -> CheckM (Term, Value)
elabLambda ctx0 bs0 body sp mexpected = go ctx0 bs0 mexpected
  where
    go ctx [] mexp = case mexp of
      Just t -> do
        tm <- check ctx body t
        pure (tm, t)
      Nothing -> do
        (tm, ty) <- infer ctx body
        insertAllImplicits ctx (exprSpan body) tm ty
    go ctx (b : rest) mexp = do
      mexp' <- traverse forceM mexp
      case mexp' of
        Just expectedPi@(VPi ic q nm dom clo)
          | ic == (if bImplicit b then Impl else Expl) -> do
              -- check declared annotation against expected domain
              forM_ (binderTypeExpr b) $ \tyE -> do
                (tyTm, _) <- inferType ctx tyE
                tyV <- evalIn ctx tyTm
                expectType ctx (bSpan b) dom tyV
              let bn = binderName b nm
                  ctx' = bindCtx bn (bImplicit b) dom ctx
              cod <- clApp clo (VRigid (ctxLen ctx) [])
              (inner, _) <- go ctx' rest (Just cod)
              pure (CLam ic q bn inner, expectedPi)
        _ -> do
          domV <- case binderTypeExpr b of
            Just tyE -> do
              (tyTm, _) <- inferType ctx tyE
              evalIn ctx tyTm
            Nothing
              | bUnitBinder b -> pure (VGlobN (gPrel "Unit") [])
              | otherwise -> freshMetaV ctx
          let bn = binderName b "_"
              ic = if bImplicit b then Impl else Expl
              q = binderQ b
              ctx' = bindCtx bn (bImplicit b) domV ctx
          (inner, innerTy) <- go ctx' rest Nothing
          domTm <- quoteIn ctx domV
          innerTyTm <- quoteIn ctx' innerTy
          piV <- evalIn ctx (CPi ic q bn domTm innerTyTm)
          case mexp' of
            Just t -> expectType ctx sp piV t
            Nothing -> pure ()
          pure (CLam ic q bn inner, piV)

    binderName b dflt = maybe (if bUnitBinder b then "_" else dflt) nameText (bName b)

elabLet :: Ctx -> [LetBind] -> Expr -> Maybe Value -> CheckM (Term, Value)
elabLet ctx0 binds body mexpected = go ctx0 binds []
  where
    mkLet (q, n, tyT, rhs, isRec) b
      | isRec = CLetRec q n tyT rhs b
      | otherwise = CLet q n tyT rhs b
    go ctx [] acc = do
      (bodyTm, bodyTy) <- case mexpected of
        Just t -> (,t) <$> check ctx body t
        Nothing -> infer ctx body
      pure (foldl' (flip mkLet) bodyTm acc, bodyTy)
    -- an annotated local function may refer to itself (§9.2 mirrored
    -- locally): elaborate the lambda under its own binder
    go ctx (LetBind implocal prefix (PVar n) (Just tyE) rhs@ELambda {} sp : rest) acc = do
      (tyTm, _) <- inferType ctx tyE
      tyV <- evalIn ctx tyTm
      let q = qOf (bpQuantity prefix)
          ctxRec = bindCtx (nameText n) implocal tyV ctx
      tm <- check ctxRec rhs tyV
      _ <- pure sp
      go ctxRec rest ((q, nameText n, tyTm, tm, True) : acc)
    go ctx (LetBind implocal prefix pat0 mty rhs sp : rest) acc = do
      -- §9.1.2: a let pattern that is a bare capitalized name not naming
      -- any constructor in scope is an ordinary (rebinding) binder,
      -- e.g. `let M = type MaybeBox` (§2.8.3)
      pat <- case pat0 of
        PCtor (CtorRef Nothing n) [] _ -> do
          st <- get
          let isCtor =
                any
                  (\g -> gnameText g == nameText n)
                  (Map.keys (csCtors st))
          pure (if isCtor then pat0 else PVar n)
        _ -> pure pat0
      (rhsTm, rhsTy) <- case mty of
        Just tyE -> do
          (tyTm, _) <- inferType ctx tyE
          tyV <- evalIn ctx tyTm
          tm <- check ctx rhs tyV
          pure (tm, tyV)
        Nothing -> do
          (tm, ty) <- infer ctx rhs
          insertAllImplicits ctx sp tm ty
      case pat of
        PVar n -> do
          rhsTyTm <- quoteIn ctx rhsTy
          rhsV <- evalIn ctx rhsTm
          let q = qOf (bpQuantity prefix)
              ctx' = bindCtxLet (nameText n) implocal rhsTy rhsV ctx
          go ctx' rest ((q, nameText n, rhsTyTm, rhsTm, False) : acc)
        PWild _ -> do
          rhsTyTm <- quoteIn ctx rhsTy
          rhsV <- evalIn ctx rhsTm
          let ctx' = bindCtxLet "_" False rhsTy rhsV ctx
          go ctx' rest ((QW, "_", rhsTyTm, rhsTm, False) : acc)
        _ -> do
          -- irrefutable destructuring: elaborate as single-case match by
          -- rewriting `let pat = rhs; rest` to `match rhs case pat -> ...`
          (patC, ctx', _) <- elabPattern ctx pat rhsTy
          (bodyTm, bodyTy) <- goUnder ctx' rest
          checkIrrefutable ctx pat rhsTy sp
          let matchTm = CMatch rhsTm [CaseAlt patC Nothing bodyTm]
          pure (foldl' (flip mkLet) matchTm acc, bodyTy)
      where
        goUnder c rs = case rs of
          [] -> case mexpected of
            Just t -> (,t) <$> check c body t
            Nothing -> infer c body
          _ -> elabLet c rs body mexpected
elabBlock :: Ctx -> [Decl] -> Maybe Expr -> Span -> CheckM (Term, Value)
elabBlock ctx ds mfin sp = do
  -- v1: block-local declarations support signatures and lets; other
  -- local declaration forms are reported.
  binds <- goDecls [] ds
  case mfin of
    Nothing -> do
      errAt sp "E_BLOCK_NO_RESULT" Nothing "a pure block must end with an expression (§9.3.1)"
      anyHole ctx
    Just fin -> elabLet ctx binds fin Nothing
  where
    goDecls _ [] = pure []
    goDecls sigs (d : rest) = case d of
      -- a local signature annotates the following definition (§9.3.1)
      DSig _ n tyE _ -> goDecls ((nameText n, tyE) : sigs) rest
      DLet _ (LetDef (Just n) Nothing [] mty Nothing rhs) _ ->
        (LetBind False emptyPrefix (PVar n) (annOf n mty sigs) rhs sp :) <$> goDecls sigs rest
      DLet _ (LetDef (Just n) Nothing bs mty _ rhs) dsp -> do
        -- local named function: elaborate as lambda
        let lam = ELambda Nothing bs (maybe rhs (\t -> EAscription rhs t dsp) mty) dsp
        (LetBind False emptyPrefix (PVar n) (lookup (nameText n) sigs) lam sp :) <$> goDecls sigs rest
      DLet _ (LetDef Nothing (Just p) [] mty Nothing rhs) _ ->
        (LetBind False emptyPrefix p mty rhs sp :) <$> goDecls sigs rest
      -- a local type alias is a type-level let binding (§9.3.1, §10.2)
      DTypeAlias _ n params _ (Just rhs) dsp ->
        let (body, ann) = case params of
              [] -> (rhs, Just (EVar (Name "Type" dsp)))
              bs -> (ELambda Nothing bs rhs dsp, Nothing)
         in (LetBind False emptyPrefix (PVar n) ann body sp :) <$> goDecls sigs rest
      _ -> do
        errAt (declSpan d) "E_UNSUPPORTED" Nothing
          "this local declaration form is not supported inside block by this implementation"
        goDecls sigs rest
    annOf n mty sigs = case mty of
      Just t -> Just t
      Nothing -> lookup (nameText n) sigs

declSpan :: Decl -> Span
declSpan = \case
  DSig _ _ _ sp -> sp
  DLet _ _ sp -> sp
  DData _ _ sp -> sp
  DTypeAlias _ _ _ _ _ sp -> sp
  DTrait _ _ sp -> sp
  DInstance _ sp -> sp
  DDerive _ sp -> sp
  DEffect _ _ sp -> sp
  DFixity _ sp -> sp
  DImport _ sp -> sp
  DExport _ sp -> sp
  DExpect _ _ sp -> sp
  DPattern _ _ sp -> sp
  DProjection _ _ _ _ _ sp -> sp
  DTopSplice _ sp -> sp

-- ── if / match ───────────────────────────────────────────────────────

checkIf :: Ctx -> [(Expr, Expr)] -> Maybe Expr -> Span -> Value -> CheckM Term
checkIf ctx alts mels sp resT = go alts
  where
    boolT = VGlobN (gPrel "Bool") []
    go [] = case mels of
      Just e -> check ctx e resT
      Nothing -> do
        errAt sp "E_IF_MISSING_ELSE" (Just "kappa.control.if-missing-else")
          "if without else is only permitted as a do-block statement (§16.4, §18.4)"
        pure (CCtor (gPrel "Unit") [])
    go ((c, t) : rest) = do
      cTm <- check ctx c boolT
      tTm <- check ctx t resT
      eTm <- go rest
      pure (CIf cTm tTm eTm)

checkMatch :: Ctx -> Expr -> [MatchCase] -> Span -> Value -> CheckM Term
checkMatch ctx scrut cases sp resT = do
  (sTm, sTy) <- infer ctx scrut
  (sTm1, sTy1) <- insertAllImplicits ctx (exprSpan scrut) sTm sTy
  alts <- fmap catMaybes . forM cases $ \case
    MatchImpossible isp -> do
      empty <- scrutineeEmpty sTy1
      unless empty $
        errAt isp "E_INDEXED_IMPOSSIBLE_REACHABLE" (Just "kappa.match.impossible-reachable")
          "'case impossible' requires the remaining scrutinee type to be uninhabited (§17.1.5)"
      pure Nothing
    MatchCase pat mguard body _ -> do
      (patC, ctx', _) <- elabPattern ctx pat sTy1
      gTm <- traverse (\g -> check ctx' g (VGlobN (gPrel "Bool") [])) mguard
      bTm <- check ctx' body resT
      pure (Just (CaseAlt patC gTm bTm))
  checkExhaustive ctx sp sTy1 [(p, g) | CaseAlt p g _ <- alts]
  pure (CMatch sTm1 alts)

scrutineeEmpty :: Value -> CheckM Bool
scrutineeEmpty ty = do
  t <- forceM ty
  case t of
    VGlobN g [] -> do
      st <- get
      pure $ case Map.lookup g (csDatas st) of
        Just di -> null (diCtors di)
        Nothing -> False
    _ -> pure False

-- exhaustiveness (§17.1): closed ADTs / Bool / variants / records /
-- tuples; literal scrutinees require a catch-all.
checkExhaustive :: Ctx -> Span -> Value -> [(CorePat, Maybe Term)] -> CheckM ()
checkExhaustive ctx sp ty alts = do
  t <- forceM ty
  let catchAll = any isCatchAll [p | (p, Nothing) <- alts]
  if catchAll
    then pure ()
    else case t of
      VGlobN g _ -> do
        st <- get
        case Map.lookup g (csDatas st) of
          Just di -> do
            let rows = [[p] | (p, Nothing) <- alts]
                missing =
                  [ c
                  | c <- diCtors di
                  , let a = ctorArity st c
                  , wildUseful st (specializeRows st (KCtor c) a rows) (a :: Int)
                  ]
            unless (null missing) $
              report $
                withNote ("missing cases: " <> T.intercalate ", " (map gnameText missing)) $
                  diag SevError StageElaborate "E_PATTERN_NON_EXHAUSTIVE" (Just "kappa.match.nonexhaustive") sp
                    "match is not exhaustive"
          Nothing -> requireCatchAll
      VVariantT members -> do
        tags <- mapM (tagOf ctx) members
        let covered = concat [coveredTags p | (p, Nothing) <- alts]
            hasRest = any hasRestPat [p | (p, Nothing) <- alts]
            missing = tags \\ covered
        unless (null missing || hasRest) $
          report $
            withNote ("missing member types: " <> T.intercalate ", " missing) $
              diag SevError StageElaborate "E_PATTERN_NON_EXHAUSTIVE" (Just "kappa.match.nonexhaustive") sp
                "variant match is not exhaustive"
      VRecordT _ -> unless (any isRecordIrrefutable [p | (p, Nothing) <- alts]) requireCatchAll
      _ -> requireCatchAll
  where
    requireCatchAll =
      report $
        diag SevError StageElaborate "E_PATTERN_NON_EXHAUSTIVE" (Just "kappa.match.nonexhaustive") sp
          "match requires a catch-all case for this scrutinee type (§17.1)"
    isCatchAll = \case
      CPWild -> True
      CPVar _ -> True
      CPAs _ p -> isCatchAll p
      CPOr ps -> any isCatchAll ps
      _ -> False
    irrefutableSub = \case
      CPWild -> True
      CPVar _ -> True
      CPAs _ p -> irrefutableSub p
      CPTuple ps -> all irrefutableSub ps
      CPRecord fs _ -> all (irrefutableSub . snd) fs
      _ -> False
    coveredTags = \case
      CPInject tag p | irrefutableSub p -> [tag]
      CPOr ps -> concatMap coveredTags ps
      _ -> []
    hasRestPat = \case
      CPInjectRest _ -> True
      _ -> False
    isRecordIrrefutable = \case
      CPRecord fs _ -> all (irrefutableSub . snd) fs
      CPTuple ps -> all irrefutableSub ps
      p -> isCatchAll p

-- §17.1 exhaustiveness for nested constructor patterns, via pattern-
-- matrix usefulness (Maranget-style, over-approximating coverage for
-- record, variant and as-patterns so positives never regress): a match
-- is non-exhaustive iff the all-wildcard row is useful w.r.t. the
-- unguarded rows.
data PatKey = KCtor !GName | KTup !Int | KLit !Literal
  deriving stock (Eq)

ctorArity :: CheckState -> GName -> Int
ctorArity st c = case Map.lookup c (csCtors st) of
  Just ci -> length (ciFields ci)
  Nothing -> 0

-- unwrap as/or patterns into plain alternatives for the first column
expandRow :: [CorePat] -> [[CorePat]]
expandRow [] = [[]]
expandRow (p : ps) = case p of
  CPAs _ q -> expandRow (q : ps)
  CPOr qs -> concat [expandRow (q : ps) | q <- qs]
  _ -> [p : ps]

-- a first-column pattern this analysis treats as matching anything
isWildLike :: CorePat -> Bool
isWildLike = \case
  CPWild -> True
  CPVar _ -> True
  CPRecord {} -> True -- over-approximation
  CPInject {} -> True -- nested variant injections: over-approximation
  CPInjectRest _ -> True
  _ -> False

patKey :: CorePat -> Maybe (PatKey, Int)
patKey = \case
  CPCtor c ps -> Just (KCtor c, length ps)
  CPTuple ps -> Just (KTup (length ps), length ps)
  CPLit l -> Just (KLit l, 0)
  _ -> Nothing

subPats :: CorePat -> [CorePat]
subPats = \case
  CPCtor _ ps -> ps
  CPTuple ps -> ps
  _ -> []

specializeRows :: CheckState -> PatKey -> Int -> [[CorePat]] -> [[CorePat]]
specializeRows st k a rows =
  [ row'
  | row0 <- rows
  , row <- expandRow row0
  , Just row' <- [spec row]
  ]
  where
    _ = st
    spec [] = Nothing
    spec (p : ps)
      | isWildLike p = Just (replicate a CPWild ++ ps)
      | Just (k', _) <- patKey p, k' == k = Just (subPats p ++ ps)
      | otherwise = Nothing

defaultRows :: [[CorePat]] -> [[CorePat]]
defaultRows rows =
  [ ps
  | row0 <- rows
  , (p : ps) <- expandRow row0
  , isWildLike p
  ]

-- is the all-wildcard row of width n useful w.r.t. the matrix?
wildUseful :: CheckState -> [[CorePat]] -> Int -> Bool
wildUseful _ rows 0 = null rows
wildUseful st rows n =
  let firsts = [p | row0 <- rows, (p : _) <- expandRow row0]
      keys = nub (mapMaybe patKey firsts)
      complete = case keys of
        ((KTup _, _) : _) -> True
        ks@((KCtor c, _) : _) ->
          case Map.lookup c (csCtors st) >>= \ci -> Map.lookup (ciData ci) (csDatas st) of
            Just di -> all (\dc -> KCtor dc `elem` map fst ks) (diCtors di)
            Nothing -> False
        _ -> False -- literals: never a complete signature here
   in if complete
        then
          or
            [ wildUseful st (specializeRows st k a rows) (a + n - 1)
            | (k, a) <- keys
            ]
        else wildUseful st (defaultRows rows) (n - 1)

checkIrrefutable :: Ctx -> Pattern -> Value -> Span -> CheckM ()
checkIrrefutable ctx pat ty sp = do
  ok <- irrefutableFor ctx pat ty
  unless ok $
    errAt sp "E_REFUTABLE_LET_PATTERN" (Just "kappa.pattern.refutable-binding")
      "let bindings require an irrefutable pattern (§9.1.2); use match or let? instead"

irrefutableFor :: Ctx -> Pattern -> Value -> CheckM Bool
irrefutableFor ctx pat ty = case pat of
  PWild _ -> pure True
  PVar _ -> pure True
  PAs _ p -> irrefutableFor ctx p ty
  PTyped p _ _ -> irrefutableFor ctx p ty
  PTuple ps _ -> pure (all shallowIrrefutable ps)
  PUnit _ -> pure True
  PRecord fs _ _ -> pure (all (\(_, _, mp) -> maybe True shallowIrrefutable mp) fs)
  PCtor cref _ _ -> do
    t <- forceM ty
    case t of
      VGlobN g _ -> do
        st <- get
        case Map.lookup g (csDatas st) of
          Just di | [single] <- diCtors di -> do
            mr <- resolveCtor ctx cref
            pure (fmap fst mr == Just single)
          _ -> pure False
      _ -> pure False
  _ -> pure False
  where
    shallowIrrefutable = \case
      PWild _ -> True
      PVar _ -> True
      PAs _ p -> shallowIrrefutable p
      PTuple ps _ -> all shallowIrrefutable ps
      _ -> False

-- pattern elaboration: produce core pattern and extended context.
elabPattern :: Ctx -> Pattern -> Value -> CheckM (CorePat, Ctx, Bool)
elabPattern ctx0 pat0 ty0 = do
  (p, ctx) <- go ctx0 pat0 ty0
  forM_ (duplicatesOf (corePatNames p)) $ \n ->
    errAt (patternSpan pat0) "E_DUPLICATE_PATTERN_BINDER" (Just "kappa.pattern.duplicate-binder")
      ("pattern binds '" <> n <> "' more than once (§17.2)")
  pure (p, ctx, True)
  where
    corePatNames :: CorePat -> [Text]
    corePatNames = \case
      CPVar n -> [n]
      CPAs n p -> n : corePatNames p
      CPCtor _ ps -> concatMap corePatNames ps
      CPTuple ps -> concatMap corePatNames ps
      CPRecord fs mr -> concatMap (corePatNames . snd) fs ++ [nm | Just nm <- [mr], not (T.null nm)]
      CPInject _ p -> corePatNames p
      -- or-pattern alternatives bind the same names; count one side
      CPOr (p : _) -> corePatNames p
      _ -> []
    go ctx pat tyIn = do
      ty <- forceM tyIn
      case pat of
        PWild _ -> pure (CPWild, ctx)
        PVar n
          -- a Var pattern naming an in-scope nullary constructor is a
          -- constructor pattern (lowercase ctors exist, e.g. ω-free code)
          | otherwise -> pure (CPVar (nameText n), bindCtx (nameText n) False ty ctx)
        PUnit _ -> pure (CPCtor (gPrel "Unit") [], ctx)
        PLit l _ -> pure (CPLit (coreLit l), ctx)
        PAs n p -> do
          let ctx1 = bindCtx (nameText n) False ty ctx
          (p', ctx2) <- go ctx1 p ty
          pure (CPAs (nameText n) p', ctx2)
        PTyped p tyE _ -> do
          (tyTm, _) <- inferType ctx tyE
          tyV <- evalIn ctx tyTm
          _ <- unify ctx tyV ty
          go ctx p tyV
        PTuple ps _ -> do
          fts <- case ty of
            VRecordT fs | length fs == length ps -> pure (map snd fs)
            _ -> mapM (const (freshMetaV ctx)) ps
          (ps', ctx') <- goList ctx (zip ps fts)
          pure (CPTuple ps', ctx')
        PRecord fs mrest _ -> do
          fields <- case ty of
            VRecordT fts -> pure fts
            _ -> pure []
          (ps', ctx') <-
            goList ctx [(fromMaybe (PVar n) mp, fromMaybe (VSort 0) (lookup (nameText n) fields)) | (_, n, mp) <- fs]
          let names = [nameText n | (_, n, _) <- fs]
          case mrest of
            Just (PatRestBind restN) -> do
              -- ..rest binds the remaining fields as a record (§17.2.5)
              let remaining = [(fn, ft) | (fn, ft) <- fields, fn `notElem` names]
                  ctx'' = bindCtx (nameText restN) False (VRecordT remaining) ctx'
              pure (CPRecord (zip names ps') (Just (nameText restN)), ctx'')
            Just PatRestDiscard -> pure (CPRecord (zip names ps') (Just ""), ctx')
            Nothing -> pure (CPRecord (zip names ps') Nothing, ctx')
        POr ps sp -> do
          rs <- mapM (\p -> go ctx p ty) ps
          let pats = map fst rs
          case rs of
            ((p1, ctx1) : _) -> do
              -- §17.2.3: each alternative must bind the same names; we
              -- approximate by requiring the same binder count.
              let count1 = patBindersCount p1
              unless (all (\(p, _) -> patBindersCount p == count1) rs) $
                errAt sp "E_OR_PATTERN_BINDINGS" (Just "kappa.pattern.or-bindings")
                  "all alternatives of an or-pattern must bind the same names (§17.2.3)"
              pure (CPOr pats, ctx1)
            [] -> pure (CPWild, ctx)
        PVariant mn mtyE isWild mrest _ -> case ty of
          VVariantT members -> case (mn, mtyE, mrest) of
            (_, Just tyE, Nothing) -> do
              (tyTm, _) <- inferType ctx tyE
              tyV <- evalIn ctx tyTm
              tag <- tagOf ctx tyV
              tags <- mapM (tagOf ctx) members
              unless (tag `elem` tags) $
                errAt (patternSpan pat) "E_VARIANT_MEMBER" (Just "kappa.variant.unknown-member")
                  "variant pattern type is not a member of the scrutinee union"
              if isWild
                then pure (CPInject tag CPWild, ctx)
                else case mn of
                  Just n -> pure (CPInject tag (CPVar (nameText n)), bindCtx (nameText n) False tyV ctx)
                  Nothing -> pure (CPInject tag CPWild, ctx)
            (Just n, Nothing, Nothing)
              | [single] <- members -> do
                  tag <- tagOf ctx single
                  pure (CPInject tag (CPVar (nameText n)), bindCtx (nameText n) False single ctx)
              | otherwise -> do
                  errAt (nameSpan n) "E_VARIANT_AMBIGUOUS" (Just "kappa.variant.ambiguous")
                    "untyped variant pattern requires a singleton union (§13.1.7)"
                  pure (CPWild, ctx)
            (Nothing, Nothing, Just restN) -> do
              pure (CPInjectRest [], bindCtx (nameText restN) False ty ctx)
            _ -> do
              errAt (patternSpan pat) "E_VARIANT_PATTERN" Nothing "malformed variant pattern"
              pure (CPWild, ctx)
          _ -> do
            errAt (patternSpan pat) "E_TYPE_EQUALITY_MISMATCH" (Just "kappa.type.mismatch")
              "variant pattern requires a union scrutinee"
            pure (CPWild, ctx)
        PCtorNamed cref fields sp -> do
          mr <- resolveCtor ctx cref
          case mr of
            Nothing -> pure (CPWild, ctx)
            Just (_, ci) -> do
              let fieldNames = mapMaybe fst (ciFields ci)
              forM_ fields $ \(n, _) ->
                unless (nameText n `elem` fieldNames) $
                  errAt (nameSpan n) "E_PATTERN_FIELD_UNKNOWN" (Just "kappa.pattern.field")
                    ("constructor has no named field '" <> nameText n <> "'")
              let posPats =
                    [ case lookup fn [(nameText n, fromMaybe (PVar n) mp) | (n, mp) <- fields] of
                        Just p -> p
                        Nothing -> PWild sp
                    | Just fn <- map fst (ciFields ci)
                    ]
              go ctx (PCtor cref posPats sp) tyIn
        PCtor cref ps sp -> do
          mr <- resolveCtor ctx cref
          case mr of
            Nothing -> pure (CPWild, ctx)
            Just (g, ci) -> do
              fieldTys <- ctorFieldTypes ctx g ci ty sp
              when (length ps /= length fieldTys) $
                errAt sp "E_PATTERN_CONSTRUCTOR_ARITY_MISMATCH" (Just "kappa.pattern.arity")
                  ("constructor pattern arity mismatch: expected "
                     <> T.pack (show (length fieldTys))
                     <> ", got "
                     <> T.pack (show (length ps)))
              -- Surplus binders get fresh metas, not Type: after the
              -- arity diagnostic the bodies must not cascade (§3.1).
              padTys <- mapM (const (freshMetaV ctx)) (drop (length fieldTys) ps)
              (ps', ctx') <- goList ctx (zip ps (fieldTys ++ padTys))
              pure (CPCtor g ps', ctx')
        PActive _ _ _ sp -> do
          errAt sp "E_UNSUPPORTED" Nothing "active patterns are not supported by this implementation"
          pure (CPWild, ctx)
        POpChain {} -> do
          errAt (patternSpan pat) "E_INTERNAL" Nothing "operator pattern not re-associated"
          pure (CPWild, ctx)

    goList ctx [] = pure ([], ctx)
    goList ctx ((p, t) : rest) = do
      (p', ctx') <- go ctx p t
      (ps, ctx'') <- goList ctx' rest
      pure (p' : ps, ctx'')

    patBindersCount :: CorePat -> Int
    patBindersCount = \case
      CPVar _ -> 1
      CPAs _ p -> 1 + patBindersCount p
      CPCtor _ ps -> sum (map patBindersCount ps)
      CPTuple ps -> sum (map patBindersCount ps)
      CPRecord fs mr -> sum (map (patBindersCount . snd) fs) + (case mr of Just nm | not (T.null nm) -> 1; _ -> 0)
      CPInject _ p -> patBindersCount p
      CPInjectRest _ -> 1
      CPOr ps -> case ps of
        (p : _) -> patBindersCount p
        [] -> 0
      _ -> 0

    coreLit = \case
      LInt v _ -> LitInt v
      LFloat v _ -> LitDouble v
      LString s -> LitStr s
      LScalar c -> LitScalar c

-- instantiate the constructor's field types against the scrutinee type
-- (GADT-lite: unify the constructor's result with the scrutinee type).
ctorFieldTypes :: Ctx -> GName -> CtorInfo -> Value -> Span -> CheckM [Value]
ctorFieldTypes ctx _ ci scrutTy _ = do
  ctype <- evalIn emptyCtx (ciType ci)
  peel ctype []
  where
    peel t acc = do
      t' <- forceM t
      case t' of
        VPi Impl _ _ _ clo -> do
          m <- freshMetaV ctx
          r <- clApp clo m
          peel r acc
        VPi Expl _ _ dom clo -> do
          m <- freshMetaV ctx
          r <- clApp clo m
          peel r (acc ++ [dom])
        result -> do
          _ <- unify ctx result scrutTy
          pure acc

-- ── try / do ─────────────────────────────────────────────────────────

ioType :: Value -> Value -> Value
ioType e a = VGlobN (gPrel "IO") [(Expl, e), (Expl, a)]

elabTry :: Ctx -> Expr -> [ExceptCase] -> Maybe Expr -> Span -> CheckM (Term, Value)
elabTry ctx body excepts mfin sp = do
  errT <- freshMetaV ctx
  resT <- freshMetaV ctx
  bodyTm <- check ctx body (ioType errT resT)
  errT' <- forceM errT
  -- handlers discharge the body's error type; the try expression's own
  -- error type is whatever the handlers / finalizer may still raise
  outErr <- if null excepts then pure errT' else freshMetaV ctx
  caught <-
    if null excepts
      then pure bodyTm
      else do
        -- \err -> match err cases
        let nm = "__err"
            ctx' = bindCtx nm False errT' ctx
        alts <- forM excepts $ \(ExceptCase pat mguard hbody _) -> do
          (patC, ctx'', _) <- elabPattern ctx' pat errT'
          gTm <- traverse (\g -> check ctx'' g (VGlobN (gPrel "Bool") [])) mguard
          hTm <- check ctx'' hbody (ioType outErr resT)
          pure (CaseAlt patC gTm hTm)
        checkExhaustive ctx sp errT' [(p, g) | CaseAlt p g _ <- alts]
        let handlerTm = CLam Expl QW nm (CMatch (CVar 0) alts)
        pure (CApp Expl (CApp Expl (CGlob (gPrel "catchIO")) bodyTm) handlerTm)
  final <- case mfin of
    Nothing -> pure caught
    Just finE -> do
      finTm <- check ctx finE (ioType outErr (VGlobN (gPrel "Unit") []))
      pure (CApp Expl (CApp Expl (CGlob (gPrel "finallyIO")) caught) finTm)
  pure (final, ioType outErr resT)

-- do blocks (§18.2): the carrier is IO in this implementation.
--
-- @loops@ tracks the enclosing loops of this do-scope (one entry per
-- loop, @Just label@ when labeled) so @break@\/@continue@ are resolved
-- at compile time: a labeled form must name an enclosing labeled loop
-- (§18.2.5) and an unlabeled form must occur inside some loop body
-- (§18.6 "Using them outside a loop body is a compile-time error").
-- The loop's @else@ suite runs after normal completion, so the loop
-- itself is not in scope as a target there. Each do-expression starts a
-- fresh scope: targets never cross a first-class do-value boundary.
elabDo :: Ctx -> [DoItem] -> Span -> Maybe Value -> CheckM (Term, Value)
elabDo ctx items _sp mexpected = do
  (errT, resT) <- do
    me <- traverse forceM mexpected
    case me of
      Just (VGlobN (GName _ "IO") [(_, e), (_, a)]) -> pure (e, a)
      _ -> (,) <$> freshMetaV ctx <*> freshMetaV ctx
  kitems <- goItems [] ctx errT resT items
  pure (CDo kitems, ioType errT resT)
  where
    goItems :: [Maybe Text] -> Ctx -> Value -> Value -> [DoItem] -> CheckM [KItem]
    goItems _ _ _ _ [] = pure []
    goItems loops c errT resT (item : rest) = do
      let lastItem = null rest
      case item of
        DoExpr e -> do
          tm <-
            if lastItem
              then check c (desugarBang e) (ioType errT resT)
              else do
                a <- freshMetaV c
                check c (desugarBang e) (ioType errT a)
          (KExpr tm :) <$> goItems loops c errT resT rest
        DoBind (LetBind implocal prefix pat mty rhs bsp) -> do
          aT <- case mty of
            Just tyE -> do
              (tyTm, _) <- inferType c tyE
              evalIn c tyTm
            Nothing -> freshMetaV c
          rhsTm <- check c (desugarBang rhs) (ioType errT aT)
          checkIrrefutable c pat aT bsp
          (patC, cBound, _) <- elabPattern c pat aT
          let c' = markImplicitLocal implocal c cBound
          ks <- goItems loops c' errT resT rest
          pure (KBind (qOf (bpQuantity prefix)) patC rhsTm : ks)
        DoLet (LetBind implocal prefix pat mty rhs bsp) -> do
          (rhsTm, rhsTy) <- case mty of
            Just tyE -> do
              (tyTm, _) <- inferType c tyE
              tyV <- evalIn c tyTm
              tm <- check c rhs tyV
              pure (tm, tyV)
            Nothing -> do
              (tm, ty) <- infer c rhs
              insertAllImplicits c bsp tm ty
          checkIrrefutable c pat rhsTy bsp
          (patC, cBound, _) <- elabPattern c pat rhsTy
          let c' = markImplicitLocal implocal c cBound
          ks <- goItems loops c' errT resT rest
          pure (KLet (qOf (bpQuantity prefix)) patC rhsTm : ks)
        DoLetQ pat rhs mElse _ -> do
          (rhsTm, rhsTy) <- infer c rhs
          (patC, c', _) <- elabPattern c pat rhsTy
          mElse' <- forM mElse $ \(rp, fe) -> do
            (rpC, c2, _) <- elabPattern c rp rhsTy
            feTm <- check c2 fe (ioType errT resT)
            pure (rpC, feTm)
          ks <- goItems loops c' errT resT rest
          pure (KLetQ patC rhsTm mElse' : ks)
        DoVar n rhs _ -> do
          (rhsTm, rhsTy) <- infer c rhs
          (rhsTm1, rhsTy1) <- insertAllImplicits c (nameSpan n) rhsTm rhsTy
          let refTy = VGlobN (gPrel "Ref") [(Expl, rhsTy1)]
              c' = bindCtxVar (nameText n) refTy c
          ks <- goItems loops c' errT resT rest
          pure (KVarItem (nameText n) rhsTm1 : ks)
        DoAssign n monadic rhs asp -> do
          mref <- pure (lookupCtx (nameText n) c)
          case mref of
            Just (i, entry) -> do
              et <- forceM (ceType entry)
              case et of
                VGlobN (GName _ "Ref") [(_, a)] -> do
                  rhsTm <-
                    if monadic
                      then check c (desugarBang rhs) (ioType errT a)
                      else check c (desugarBang rhs) a
                  ks <- goItems loops c errT resT rest
                  pure (KAssign (CVar i) monadic rhsTm : ks)
                _ -> do
                  errAt asp "E_ASSIGN_NOT_VAR" (Just "kappa.do.assign-non-var")
                    ("'" <> nameText n <> "' is not a mutable var binding (§18.6.1)")
                  goItems loops c errT resT rest
            Nothing -> do
              errAt asp "E_NAME_UNRESOLVED" (Just "kappa.name.unresolved")
                ("unresolved name '" <> nameText n <> "'")
              goItems loops c errT resT rest
        DoReturn ml me rsp -> do
          -- return@label targets named functions or labeled lambdas
          -- (§18.5.1); this implementation's kernel only returns from
          -- the current do-scope, so a labeled return is rejected
          -- rather than silently retargeted.
          forM_ ml $ \l ->
            reportUnsupported (nameSpan l) "labeled return (return@label)"
          tm <- case me of
            Just e -> check c (desugarBang e) resT
            Nothing -> do
              expectType c rsp (VGlobN (gPrel "Unit") []) resT
              pure (CCtor (gPrel "Unit") [])
          ks <- goItems loops c errT resT rest
          pure (KReturn tm : ks)
        DoBreak ml bsp -> do
          checkLoopTarget "break" ml bsp
          (KBreak (nameText <$> ml) :) <$> goItems loops c errT resT rest
        DoContinue ml csp -> do
          checkLoopTarget "continue" ml csp
          (KContinue (nameText <$> ml) :) <$> goItems loops c errT resT rest
        DoWhile ml cond body mels _ -> do
          condTm <- check c (desugarBang cond) (VGlobN (gPrel "Bool") [])
          bodyKs <- goItems (withLoop ml) c errT (VGlobN (gPrel "Unit") []) body
          elsKs <- traverse (goItems loops c errT (VGlobN (gPrel "Unit") [])) mels
          ks <- goItems loops c errT resT rest
          pure (KWhile (nameText <$> ml) condTm bodyKs elsKs : ks)
        DoFor ml pat src body mels fsp -> do
          elemT <- freshMetaV c
          srcTm <- check c (desugarBang src) (VGlobN (gPrel "List") [(Expl, elemT)])
          checkIrrefutable c pat elemT fsp
          (patC, c', _) <- elabPattern c pat elemT
          bodyKs <- goItems (withLoop ml) c' errT (VGlobN (gPrel "Unit") []) body
          elsKs <- traverse (goItems loops c errT (VGlobN (gPrel "Unit") [])) mels
          ks <- goItems loops c errT resT rest
          pure (KFor (nameText <$> ml) patC srcTm bodyKs elsKs : ks)
        DoIf alts mels _ -> do
          alts' <- forM alts $ \(cond, body) -> do
            condTm <- check c (desugarBang cond) (VGlobN (gPrel "Bool") [])
            bodyKs <- goItems loops c errT (VGlobN (gPrel "Unit") []) body
            pure (condTm, bodyKs)
          elsKs <- traverse (goItems loops c errT (VGlobN (gPrel "Unit") [])) mels
          ks <- goItems loops c errT resT rest
          pure (KIf alts' elsKs : ks)
        DoDefer ml e _ -> do
          -- defer@label schedules onto a labeled outer do-scope
          -- (§18.7); the kernel only schedules onto the current scope,
          -- so a labeled defer is rejected rather than run too early.
          forM_ ml $ \l ->
            reportUnsupported (nameSpan l) "labeled defer (defer@label)"
          eTm <- check c (desugarBang e) (ioType errT (VGlobN (gPrel "Unit") []))
          ks <- goItems loops c errT resT rest
          pure (KDefer eTm : ks)
        DoUsing _ _ usp -> do
          _ <- unsupported c usp "'using' resource binds"
          goItems loops c errT resT rest
        DoDecl d -> do
          case d of
            DLet _ (LetDef (Just n) Nothing [] mty Nothing rhs) dsp ->
              goItems loops c errT resT (DoLet (LetBind False emptyPrefix (PVar n) mty rhs dsp) : rest)
            _ -> do
              errAt (declSpan d) "E_UNSUPPORTED" Nothing
                "this local declaration form inside do is not supported by this implementation"
              goItems loops c errT resT rest
      where
        withLoop ml = (nameText <$> ml) : loops
        checkLoopTarget what ml sp = case ml of
          Just l ->
            unless (Just (nameText l) `elem` loops) $
              errAt (nameSpan l) "E_LABEL_UNRESOLVED" (Just "kappa.do.label-unresolved")
                (what <> "@" <> nameText l
                   <> " does not target an enclosing labeled loop of this do-scope (§18.2.5)")
          Nothing ->
            when (null loops) $
              errAt sp "E_BREAK_OUTSIDE_LOOP" (Just "kappa.do.break-outside-loop")
                ("'" <> what
                   <> "' is valid only within the body of a loop of this do-scope (§18.6)")

-- | §16.3.3: an implicit do-binding @let (\@x : T) = e@ joins the local
-- implicit context for the remaining items. @before@ is the context the
-- pattern was elaborated in; the entries added on top of it are marked.
markImplicitLocal :: Bool -> Ctx -> Ctx -> Ctx
markImplicitLocal False _ after = after
markImplicitLocal True before (Ctx es env) =
  let (new, old) = splitAt (length es - ctxLen before) es
   in Ctx (map (\e -> e {ceImplicitLocal = True}) new ++ old) env

-- `!e` splicing inside do items (§18.3): rewritten to runIO marker the
-- interpreter understands; typing treats !e : a where e : IO err a.
desugarBang :: Expr -> Expr
desugarBang = \case
  EBang e sp -> EApp (EVar (Name "__runIO" sp)) [ArgExplicit (desugarBang e)]
  EApp f args -> EApp (desugarBang f) (map mapArg args)
  EIf alts mels sp ->
    EIf [(desugarBang c, desugarBang t) | (c, t) <- alts] (fmap desugarBang mels) sp
  EMatch scrut cases sp ->
    EMatch (desugarBang scrut)
      [case mc of
         MatchCase p g b csp -> MatchCase p (fmap desugarBang g) (desugarBang b) csp
         other -> other
      | mc <- cases]
      sp
  EAscription e t sp -> EAscription (desugarBang e) t sp
  ETuple es sp -> ETuple (map desugarBang es) sp
  EDot e m -> EDot (desugarBang e) m
  e -> e
  where
    mapArg = \case
      ArgExplicit e -> ArgExplicit (desugarBang e)
      ArgImplicit e -> ArgImplicit (desugarBang e)
      a -> a

-- ── Comprehensions (§20, list subset) ────────────────────────────────

elabComprehension :: Ctx -> CompKind -> [S.CompClause] -> CompYield -> Span -> CheckM (Term, Value)
elabComprehension ctx kind clauses yld sp = case kind of
  CompList -> do
    e <- desugar clauses
    infer ctx e
  _ -> unsupported ctx sp "non-list comprehensions"
  where
    yieldExpr = case yld of
      YieldExpr e -> e
      YieldPair k _ -> k
    desugar [] = pure (EListLit [yieldExpr] sp)
    desugar (c : rest) = do
      inner <- desugar rest
      case c of
        S.CFor False False pat src _ -> do
          x <- freshNameM "__c"
          let xe = Name x sp
          pure $
            EApp (EVar (Name "concatMap" sp))
              [ ArgExplicit (ELambda Nothing [simpleBinder xe] (EMatch (EVar xe) [MatchCase pat Nothing inner sp] sp) sp)
              , ArgExplicit src
              ]
        S.CIf cond ->
          pure (EIf [(cond, inner)] (Just (EListLit [] sp)) sp)
        S.CLet False pat mty rhs lsp ->
          pure (ELet [LetBind False emptyPrefix pat mty rhs lsp] inner sp)
        _ -> do
          _ <- unsupported ctx sp "this comprehension clause"
          pure inner

-- ── Declarations ─────────────────────────────────────────────────────

-- | Check a resolved module: two passes (headers then bodies), per the
-- preceding-signature recursion rule (§15.16, §9.2).
checkModule :: CheckState -> Module -> (CheckState, Diagnostics)
checkModule st0 m =
  let passes = do
        mapM_ predeclarePass (modDecls m)
        mapM_ headerPass (modDecls m)
        mapM_ bodyPass (modDecls m)
        sigSatisfactionPass
      (_, st1) = runState passes (st0 {csSigPending = Map.empty})
   in -- 'report' prepends; restore emission (source) order here
      (st1 {csDiags = []}, reverse (csDiags st1))

-- §9.1: a non-expect top-level term signature must be satisfied by
-- exactly one matching definition in the same source file.
sigSatisfactionPass :: CheckM ()
sigSatisfactionPass = do
  st <- get
  unless (csModule st == preludeModule) $
    forM_ (Map.toList (csSigPending st)) $ \(g, sp) ->
      errAt sp "E_SIGNATURE_UNSATISFIED" (Just "kappa.signature.unsatisfied")
        ("top-level signature '" <> gnameText g
           <> "' has no definition in this source file (Spec §9.1); use 'expect term' for external requirements (§9.4)")

-- Pre-register data type-constructor names so declarations in one file
-- may refer to data types declared later (§10.1: declaration order
-- within a module is immaterial for type references).
predeclarePass :: Decl -> CheckM ()
predeclarePass = \case
  DData _ (DataDecl n params _ _) _ -> do
    g <- ownName n
    exists <- gets (Map.member g . csGlobals)
    unless exists $ do
      paramTele <- elabTele emptyCtx params
      let tyTm = foldr (\(ic, q, nm, t) acc -> CPi ic q nm t acc) (CSort 0) paramTele
      tyV <- evalIn emptyCtx tyTm
      addGlobal g (GlobalDef tyV Nothing False)
  _ -> pure ()

headerPass :: Decl -> CheckM ()
headerPass = \case
  DSig _ n tyE sp -> do
    -- §11.3.3 (approximation): free ASCII-lowercase heads in the
    -- signature that resolve to no global are implicitly universalized
    -- as erased implicit Type binders.
    fvs <- filterM (fmap isNothing . lookupGlobalName) (nub (freeLower tyE))
    let ctx0 = foldl (\c v -> bindCtx v False (VSort 0) c) emptyCtx fvs
    (tyTm0, _) <- inferType ctx0 tyE
    let tyTm = foldr (\v acc -> CPi Impl Q0 v (CSort 0) acc) tyTm0 fvs
    tyV <- evalIn emptyCtx tyTm
    g <- ownName n
    exists <- gets (Map.member g . csGlobals)
    isExpected <- gets (Map.member g . csExpects)
    when (exists && not isExpected) $
      errAt sp "E_DUPLICATE_DECLARATION" (Just "kappa.name.duplicate") ("duplicate declaration of '" <> nameText n <> "'")
    addGlobal g (GlobalDef tyV Nothing False)
    -- §9.1: the signature awaits its same-file definition (an expected
    -- name is governed by §9.4 satisfaction instead)
    unless isExpected $
      modify' $ \st -> st {csSigPending = Map.insert g sp (csSigPending st)}
  DData _ dd sp -> headerData dd sp
  DTypeAlias _ n params _ (Just rhs) sp -> do
    -- alias: a definition at a universe type
    (tm, ty) <- elabAliasBody params rhs
    g <- ownName n
    noteDefinition g sp
    tmV <- evalIn emptyCtx tm
    addGlobal g (GlobalDef ty (Just tmV) True)
  DTypeAlias _ n params _ Nothing _ -> do
    g <- ownName n
    tyV <- aliasKind params
    addGlobal g (GlobalDef tyV Nothing False)
  DTrait _ td sp -> headerTrait td sp
  DEffect _ _ sp ->
    errAt sp "E_UNSUPPORTED" Nothing "effect declarations are accepted syntactically but not elaborated by this implementation"
  DExpect _ form sp -> headerExpect form sp
  _ -> pure ()

ownName :: Name -> CheckM GName
ownName n = do
  st <- get
  pure (GName (csModule st) (nameText n))

aliasKind :: [Binder] -> CheckM Value
aliasKind params = do
  -- (p1 : K1) -> ... -> Type
  let go [] = CSort 0
      go (b : rest) = CPi (if bImplicit b then Impl else Expl) Q0 (maybe "_" nameText (bName b)) (CSort 0) (go rest)
  evalIn emptyCtx (go params)

elabAliasBody :: [Binder] -> Expr -> CheckM (Term, Value)
elabAliasBody params rhs = go emptyCtx params
  where
    go ctx [] = do
      (tm, _) <- inferType ctx rhs
      pure (tm, VSort 0)
    go ctx (b : rest) = do
      domTm <- case bType b of
        Just t -> fst <$> inferType ctx t
        Nothing -> pure (CSort 0)
      domV <- evalIn ctx domTm
      let nm = maybe "_" nameText (bName b)
          ctx' = bindCtx nm False domV ctx
      (tm, _) <- go ctx' rest
      ty' <- do
        innerK <- pure (CSort 0)
        pure (CPi (if bImplicit b then Impl else Expl) Q0 nm domTm innerK)
      tyV <- evalIn ctx ty'
      pure (CLam (if bImplicit b then Impl else Expl) Q0 nm tm, tyV)

headerData :: DataDecl -> Span -> CheckM ()
headerData (DataDecl n params _mkind ctors) sp = do
  -- the optional kind annotation is not validated: every data type
  -- lives at 'Type' in this implementation (see SPEC_COVERAGE.md)
  g <- ownName n
  noteDefinition g sp
  forM_ (duplicatesOf [nameText cn | CtorDecl cn _ _ _ <- ctors]) $ \dn ->
    errAt sp "E_DUPLICATE_DECLARATION" (Just "kappa.name.duplicate")
      ("duplicate constructor '" <> dn <> "' in data declaration")
  -- data type constructor type: params -> Type
  paramTele <- elabTele emptyCtx params
  let sortT = CSort 0
  let tyTm = foldr (\(ic, q, nm, t) acc -> CPi ic q nm t acc) sortT paramTele
  tyV <- evalIn emptyCtx tyTm
  addGlobal g (GlobalDef tyV Nothing False)
  ctorGs <- forM ctors $ \(CtorDecl cn binders mgadt _) -> do
    cg <- ownName cn
    cty <- case mgadt of
      Just sig -> do
        -- GADT signature: elaborate under data params implicitly bound
        (tm, _) <- elabUnderParams paramTele sig
        pure tm
      Nothing -> do
        -- ordinary ctor: params implicit, fields explicit, result = data applied
        fieldsTele <- elabTele' paramTele binders
        -- §10.1.1: a field default is checked at declaration against
        -- the field's type, with only the EARLIER fields in scope
        checkFieldDefaults paramTele fieldsTele binders
        let resultT =
              foldl
                (\f i -> CApp Expl f (CVar i))
                (CGlob g)
                (reverse [length fieldsTele .. length fieldsTele + length paramTele - 1])
            full =
              foldr (\(ic, q, nm, t) acc -> CPi ic q nm t acc) resultT
                ([(Impl, Q0, nm, t) | (_, _, nm, t) <- paramTele] ++ fieldsTele)
        pure full
    let fields = ctorFieldsOf binders mgadt
    modify' $ \st -> st {csCtors = Map.insert cg (CtorInfo g cty fields) (csCtors st)}
    pure cg
  modify' $ \st -> st {csDatas = Map.insert g (DataInfo ctorGs (length params)) (csDatas st)}
  where
    ctorFieldsOf binders mgadt = case mgadt of
      Just sig -> gadtFields sig
      Nothing -> [(nameText <$> bName b, bDefault b) | b <- binders, not (bImplicit b)]
    gadtFields = \case
      EArrow b rest | not (bImplicit b) -> (nameText <$> bName b, bDefault b) : gadtFields rest
      EArrow _ rest -> gadtFields rest
      EForall _ rest _ -> gadtFields rest
      ETraitArrow _ rest -> gadtFields rest
      _ -> []

-- §10.1.1 declaration-time validation of constructor field defaults:
-- each default must elaborate, with the preceding fields in scope, at
-- the field's declared type (later fields and the field itself are not
-- in scope).
checkFieldDefaults :: Telescope -> Telescope -> [Binder] -> CheckM ()
checkFieldDefaults paramTele fieldsTele binders = do
  pctx <- teleCtx paramTele
  let explicitBs = [b | b <- binders, not (bImplicit b)]
  _ <-
    foldM
      ( \(ctx, tele) b -> case tele of
          ((_, _, nm, domTm) : rest) -> do
            domV <- evalIn ctx domTm
            forM_ (bDefault b) $ \d -> do
              (dTm, dTy) <- infer ctx d
              eq <- unify ctx dTy domV
              unless eq $ do
                domR <- quoteIn ctx domV
                dTyR <- quoteIn ctx dTy
                errAt (exprSpan d) "E_TYPE_EQUALITY_MISMATCH" (Just "kappa.type.mismatch")
                  ( "constructor field default for '" <> nm
                      <> "' has type " <> renderTerm dTyR
                      <> ", but the field's type is " <> renderTerm domR <> " (Spec §10.1.1)"
                  )
              _ <- pure dTm
              pure ()
            pure (bindCtx nm False domV ctx, rest)
          [] -> pure (ctx, tele)
      )
      (pctx, fieldsTele)
      explicitBs
  pure ()

-- bind each telescope entry at its elaborated domain type (the domain
-- term is closed over the preceding entries)
teleCtx :: Telescope -> CheckM Ctx
teleCtx = foldM step emptyCtx
  where
    step c (_, _, nm, domTm) = do
      domV <- evalIn c domTm
      pure (bindCtx nm False domV c)

elabTele' :: Telescope -> [Binder] -> CheckM Telescope
elabTele' tele bs = do
  ctx <- teleCtx tele
  elabTele ctx bs

-- elaborate binders to a telescope (left to right).
elabTele :: Ctx -> [Binder] -> CheckM Telescope
elabTele _ [] = pure []
elabTele ctx (b : rest) = do
  domTm <- case binderTypeExpr b of
    Just t -> fst <$> inferType ctx t
    Nothing -> pure (CSort 0) -- unannotated params default to Type (§11.3.3)
  domV <- evalIn ctx domTm
  let nm = maybe "_" nameText (bName b)
      ic = if bImplicit b then Impl else Expl
      ctx' = bindCtx nm False domV ctx
  restT <- elabTele ctx' rest
  pure ((ic, binderQ b, nm, domTm) : restT)

elabUnderParams :: Telescope -> Expr -> CheckM (Term, Value)
elabUnderParams tele e = do
  ctx <- teleCtx tele
  (tm, _) <- inferType ctx e
  -- close over params as implicit Pi
  let closed = foldr (\(_, _, nm, t) acc -> CPi Impl Q0 nm t acc) tm tele
  pure (closed, VSort 0)

headerTrait :: TraitDecl -> Span -> CheckM ()
headerTrait (TraitDecl supers n params members) sp = do
  g <- ownName n
  noteDefinition g sp
  paramTele <- elabTele emptyCtx params
  -- trait constructor: params -> Type
  let tyTm = foldr (\(_, _, nm, t) acc -> CPi Expl Q0 nm t acc) (CSort 0) paramTele
  tyV <- evalIn emptyCtx tyTm
  -- dict record type: member name -> member type (under params)
  pctx <- teleCtx paramTele
  memberTys <- forM members $ \case
    TraitSig mn mtyE _ -> do
      (mtyTm, _) <- inferType pctx mtyE
      pure (Just (nameText mn, mtyTm, Nothing))
    TraitDefault (LetDef (Just mn) _ _ mty _ body) _ -> do
      mtyTm <- case mty of
        Just t -> fst <$> inferType pctx t
        Nothing -> freshMeta
      pure (Just (nameText mn, mtyTm, Just body))
    TraitDefault {} -> pure Nothing
  let ms = catMaybes memberTys
      dictBody = CRecordT (sortOn fst [(mn, mt) | (mn, mt, _) <- ms])
      dictTm = foldr (\(_, _, nm, t) acc -> CLam Expl Q0 nm acc `withDom` t) dictBody paramTele
      withDom lam _ = lam
  dictV <- evalIn emptyCtx dictTm
  -- the trait constructor is abstract (§14.1.1): not conversion-reducible
  addGlobal g (GlobalDef tyV (Just dictV) False)
  let defaults = Map.fromList [(nameText dn, ld) | TraitDefault ld@(LetDef (Just dn) _ _ _ _ _) _ <- members]
  -- supertrait premises (§14.1.4), stored as functions of the params
  supTms <- forM supers $ \s -> do
    (sTm, _) <- inferType pctx s
    pure (foldr (\(_, _, nm, _) acc -> CLam Expl Q0 nm acc) sTm paramTele)
  modify' $ \st -> st {csTraits = Map.insert g (TraitInfo (length paramTele) [mn | (mn, _, _) <- ms] defaults supTms) (csTraits st)}
  -- member projection globals: m : forall params. (@d : Tr params) -> τ
  forM_ ms $ \(mn, mtyTm, _mdef) -> do
    let dictTy =
          foldl
            (\f i -> CApp Expl f (CVar i))
            (CGlob g)
            (reverse [0 .. length paramTele - 1])
        projTy =
          foldr (\(_, _, nm, t) acc -> CPi Impl Q0 nm t acc) (CPi Impl QW "__d" dictTy (shiftUnder mtyTm)) paramTele
        projTm =
          foldr
            (\(_, _, nm, _) acc -> CLam Impl Q0 nm acc)
            (CLam Impl QW "__d" (CProj (CVar 0) mn))
            paramTele
    projTyV <- evalIn emptyCtx projTy
    projV <- evalIn emptyCtx projTm
    mg <- ownName (Name mn sp)
    -- both the bare member name and the qualified projection global
    addGlobal mg (GlobalDef projTyV (Just projV) True)
    addGlobal (memberGlobal g mn) (GlobalDef projTyV (Just projV) True)
  where
    -- member type sits under (params, dict); we bound only params when
    -- elaborating, so weaken by one for the dict binder.
    shiftUnder = shiftTerm 1 0

shiftTerm :: Int -> Int -> Term -> Term
shiftTerm by = go
  where
    go d = \case
      CVar i
        | i >= d -> CVar (i + by)
        | otherwise -> CVar i
      CGlob g -> CGlob g
      CLam ic q n b -> CLam ic q n (go (d + 1) b)
      CPi ic q n a b -> CPi ic q n (go d a) (go (d + 1) b)
      CApp ic f a -> CApp ic (go d f) (go d a)
      CSort s -> CSort s
      CLit l -> CLit l
      CCtor g as -> CCtor g (map (go d) as)
      CMatch s alts ->
        CMatch (go d s) [CaseAlt p (fmap (go (d + nb p)) gd) (go (d + nb p) b) | CaseAlt p gd b <- alts]
        where
          nb = patBindersC
      CRecordT fs -> CRecordT [(n, go d t) | (n, t) <- fs]
      CRecordV fs -> CRecordV [(n, go d t) | (n, t) <- fs]
      CProj e f -> CProj (go d e) f
      CVariantT ms -> CVariantT (map (go d) ms)
      CInject t e -> CInject t (go d e)
      CLet q n a b c -> CLet q n (go d a) (go d b) (go (d + 1) c)
      CLetRec q n a b c -> CLetRec q n (go d a) (go (d + 1) b) (go (d + 1) c)
      CMeta m -> CMeta m
      CDo items -> CDo items
      CThunkE e -> CThunkE (go d e)
      CLazyE e -> CLazyE (go d e)
      CForceE e -> CForceE (go d e)
      CIf a b c -> CIf (go d a) (go d b) (go d c)

patBindersC :: CorePat -> Int
patBindersC = \case
  CPWild -> 0
  CPVar _ -> 1
  CPLit _ -> 0
  CPCtor _ ps -> sum (map patBindersC ps)
  CPTuple ps -> sum (map patBindersC ps)
  CPRecord fs mr -> sum (map (patBindersC . snd) fs) + (case mr of Just nm | not (T.null nm) -> 1; _ -> 0)
  CPInject _ p -> patBindersC p
  CPInjectRest _ -> 1
  CPOr ps -> case ps of
    (p : _) -> patBindersC p
    [] -> 0
  CPAs _ p -> 1 + patBindersC p

headerExpect :: ExpectForm -> Span -> CheckM ()
headerExpect form sp = case form of
  ExpectTerm n tyE -> do
    g <- ownName n
    fresh <- registerExpect g
    when fresh $ do
      (tyTm, _) <- inferType emptyCtx tyE
      tyV <- evalIn emptyCtx tyTm
      addGlobal g (GlobalDef tyV Nothing False)
  ExpectType n params _ -> abstractType n params
  ExpectData n params _ -> do
    abstractType n params
    g <- ownName n
    modify' $ \st -> st {csDatas = Map.insertWith (\_ old -> old) g (DataInfo [] (length params)) (csDatas st)}
  ExpectTrait n params _ -> abstractType n params
  where
    abstractType n params = do
      g <- ownName n
      fresh <- registerExpect g
      when fresh $ do
        tyV <- aliasKind params
        addGlobal g (GlobalDef tyV Nothing False)
    -- Record the §9.4 expectation. When the name is already defined
    -- earlier in the unit, that definition is its (single) satisfier and
    -- the existing global is kept. Returns True when the expect should
    -- introduce the declaration into the global table itself.
    registerExpect g = do
      st <- get
      let satisfied = case Map.lookup g (csGlobals st) of
            Just gd -> isJust (gdValue gd)
            Nothing -> Map.member g (csDatas st) || Map.member g (csTraits st)
          count = if satisfied then 1 else 0
      put st {csExpects = Map.insert g (sp, count) (csExpects st)}
      pure (not satisfied)

-- | Note a top-level definition of @g@: it satisfies a pending same-file
-- signature (§9.1) and counts toward §9.4 expect satisfaction (a second
-- satisfier is ambiguous).
noteDefinition :: GName -> Span -> CheckM ()
noteDefinition g sp = do
  st <- get
  put st {csSigPending = Map.delete g (csSigPending st)}
  case Map.lookup g (csExpects st) of
    Nothing -> pure ()
    Just (esp, cnt) -> do
      modify' $ \st' -> st' {csExpects = Map.insert g (esp, cnt + 1) (csExpects st')}
      when (cnt + 1 == 2) $
        errAt sp "E_EXPECT_AMBIGUOUS" (Just "kappa.expect.ambiguous")
          ("more than one definition satisfies expected declaration '" <> gnameText g <> "' (Spec §9.4)")

-- | §9.4: expects with no satisfier at the end of the compilation unit.
expectUnsatisfiedDiags :: CheckState -> Diagnostics
expectUnsatisfiedDiags st =
  [ diag SevError StageElaborate "E_EXPECT_UNSATISFIED" (Just "kappa.expect.unsatisfied") sp
      ("expected declaration '" <> gnameText g
         <> "' is not satisfied by any definition, backend intrinsic, or imported artifact in this compilation unit (Spec §9.4)")
  | (g, (sp, n)) <- Map.toList (csExpects st)
  , n == 0
  ]

bodyPass :: Decl -> CheckM ()
bodyPass = \case
  DLet mods ld sp -> elabLetDecl mods ld sp
  DInstance inst sp -> elabInstance inst sp
  DPattern _ _ sp ->
    errAt sp "E_UNSUPPORTED" Nothing "active-pattern declarations are not supported by this implementation"
  DProjection _ _ _ _ _ sp ->
    errAt sp "E_UNSUPPORTED" Nothing "projection declarations are not supported by this implementation"
  DDerive _ sp ->
    errAt sp "E_UNSUPPORTED" Nothing "derive declarations are not supported by this implementation"
  DTopSplice _ sp ->
    errAt sp "E_UNSUPPORTED" Nothing "top-level splices are not supported by this implementation"
  _ -> pure ()

elabLetDecl :: DeclMods -> LetDef -> Span -> CheckM ()
-- the parsed decreases clause is not consulted: termination is verified
-- by the structural analysis below (see IMPLEMENTATION_NOTES.md)
elabLetDecl _ (LetDef (Just n) Nothing binders mResTy _mdec body) sp = do
  -- resolve any goals postponed from signature elaboration first, so the
  -- signature's value is canonical while checking the body
  flushPending
  g <- ownName n
  noteDefinition g sp
  st <- get
  msig <- pure (Map.lookup g (csGlobals st))
  case msig of
    Just gd | Nothing <- gdValue gd -> do
      -- Pending goals raised inside the signature may have been solved
      -- to the signature's own binder rigids; re-quote the type so the
      -- solutions are baked in as proper de Bruijn variables.
      sigTy <- do
        ec <- ec_
        evalIn emptyCtx (quote ec 0 (gdType gd))
      addGlobal g gd {gdType = sigTy}
      -- signature first: check the definition against it (recursion OK)
      tm0 <- checkAgainstSig sigTy binders body sp
      flushPending
      tm <- zonkTermM 0 tm0
      tmV <- evalIn emptyCtx tm
      let recursive = occursGlobal g tm
          isFunction = case tm of
            CLam {} -> True
            _ -> not (null binders)
      reducible <-
        if recursive && not isFunction
          then do
            -- a self-referential value (no intervening function
            -- abstraction) is a definitional cycle (§15.3, §16.4)
            errAt sp "E_RECURSIVE_VALUE_CYCLE" (Just "kappa.termination.cycle")
              ("recursive value cycle: '" <> nameText n
                 <> "' refers to itself without an intervening function abstraction, so its evaluation cannot terminate (§15.3)")
            pure False
          else if recursive
            then do
              let okStructural = structuralOK g binders tm
              unless okStructural $
                report $
                  withNote "the definition is accepted but not conversion-reducible (§15.1)" $
                    diag SevWarning StageElaborate "W_TERMINATION_UNVERIFIED" (Just "kappa.termination.unverified") sp
                      ("could not verify structural termination of '" <> nameText n <> "' (§15.3)")
              pure okStructural
            else pure True
      addGlobal g gd {gdType = sigTy, gdValue = Just tmV, gdReducible = reducible}
    _ -> do
      -- a previous definition with a value: duplicate declaration (§9.2)
      case msig of
        Just gd' | isJust (gdValue gd') ->
          errAt sp "E_DUPLICATE_DECLARATION" (Just "kappa.name.duplicate")
            ("duplicate declaration of '" <> nameText n <> "'")
        _ -> pure ()
      -- no preceding signature: pre-register the name so self-references
      -- resolve and are reported as recursion-without-signature (§9.2)
      placeholderTy <- freshMetaV emptyCtx
      addGlobal g (GlobalDef placeholderTy Nothing False)
      (tm0, ty) <- elabFunction binders mResTy body sp
      flushPending
      tm <- zonkTermM 0 tm0
      when (occursGlobal g tm) $
        errAt sp "E_RECURSION_REQUIRES_SIGNATURE" (Just "kappa.termination.recursion-needs-signature")
          "recursive definitions require a preceding signature declaration (§15, §9.2)"
      tmV <- evalIn emptyCtx tm
      addGlobal g (GlobalDef ty (Just tmV) True)
elabLetDecl _ (LetDef Nothing (Just pat) [] mty Nothing body) sp = do
  -- top-level pattern binding: bind each variable to a projection
  (bodyTm, bodyTy) <- case mty of
    Just tyE -> do
      (tyTm, _) <- inferType emptyCtx tyE
      tyV <- evalIn emptyCtx tyTm
      tm <- check emptyCtx body tyV
      pure (tm, tyV)
    Nothing -> infer emptyCtx body
  checkIrrefutable emptyCtx pat bodyTy sp
  case pat of
    PVar n -> do
      g <- ownName n
      tmV <- evalIn emptyCtx bodyTm
      addGlobal g (GlobalDef bodyTy (Just tmV) True)
    _ -> do
      (patC, ctxP, _) <- elabPattern emptyCtx pat bodyTy
      let names = ctxEntries ctxP
      forM_ (zip [0 ..] names) $ \(i, entry) -> do
        let proj = CMatch bodyTm [CaseAlt patC Nothing (CVar i)]
        g <- ownName (Name (ceName entry) sp)
        projV <- evalIn emptyCtx proj
        addGlobal g (GlobalDef (ceType entry) (Just projV) True)
elabLetDecl _ _ sp =
  errAt sp "E_UNSUPPORTED" Nothing "this let-definition form is not supported at top level"

occursGlobal :: GName -> Term -> Bool
occursGlobal g = go
  where
    go = \case
      CGlob g' -> g == g'
      CApp _ f a -> go f || go a
      CLam _ _ _ b -> go b
      CPi _ _ _ a b -> go a || go b
      CCtor _ as -> any go as
      CMatch s alts -> go s || any (\(CaseAlt _ gd b) -> maybe False go gd || go b) alts
      CRecordT fs -> any (go . snd) fs
      CRecordV fs -> any (go . snd) fs
      CProj e _ -> go e
      CVariantT ms -> any go ms
      CInject _ e -> go e
      CLet _ _ a b c -> go a || go b || go c
      CLetRec _ _ a b c -> go a || go b || go c
      CIf a b c -> go a || go b || go c
      CThunkE e -> go e
      CLazyE e -> go e
      CForceE e -> go e
      CDo items -> any goK items
      _ -> False
    goK = \case
      KBind _ _ t -> go t
      KLet _ _ t -> go t
      KLetQ _ t m -> go t || maybe False (go . snd) m
      KExpr t -> go t
      KVarItem _ t -> go t
      KAssign _ _ t -> go t
      KReturn t -> go t
      KWhile _ c b e -> go c || any goK b || maybe False (any goK) e
      KFor _ _ s b e -> go s || any goK b || maybe False (any goK) e
      KIf alts e -> any (\(c, b) -> go c || any goK b) alts || maybe False (any goK) e
      KDefer t -> go t
      KUsing _ a r -> go a || go r
      _ -> False

-- Structural-descent verification (§15.3 minimum, direct recursion):
-- accepted iff some explicit parameter position strictly decreases at
-- every direct self-call, where "decreases" means the argument is a
-- variable bound by a constructor sub-pattern of a match on that
-- parameter (or a variable transitively below it).
structuralOK :: GName -> [Binder] -> Term -> Bool
structuralOK g _ tm0 =
  let (params, body, depth0) = peel [] tm0 0
   in case params of
        [] -> False
        _ ->
          let calls = collect depth0 Map.empty body
           in case calls of
                Nothing -> False -- a self-call escaped spine position
                Just cs ->
                  any
                    (\i -> all (decreasingAt i) cs)
                    [0 .. length params - 1]
  where
    -- peel leading lambdas; record levels of explicit params
    peel acc (CLam ic _ _ b) d = peel (acc ++ [(ic, d)]) b (d + 1)
    peel acc t d = ([lvl | (Expl, lvl) <- acc], t, d)
      where
        _params = acc

    paramLevels = let (ps, _, _) = peel [] tm0 0 in ps

    -- collect self-calls: depth and per-call explicit args as
    -- (argIndex, Maybe boundLevelSubOfParam)
    -- subMap: level -> root param level it descends from
    collect :: Int -> Map.Map Int Int -> Term -> Maybe [[(Int, Maybe Int)]]
    collect d sub t = case t of
      CApp {} ->
        case spineOf t of
          (CGlob g', args) | g' == g ->
              Just [zipWith (\i a -> (i, argRoot d sub a)) [0 ..] [a | (Expl, a) <- args]]
          (f, args) -> do
            rs <- mapM (collect d sub . snd) args
            r0 <- collect d sub f
            pure (r0 ++ concat rs)
      CGlob g' | g' == g -> Nothing -- bare self-reference (escapes analysis)
      CLam _ _ _ b -> collect (d + 1) sub b
      CPi _ _ _ a b -> (++) <$> collect d sub a <*> collect (d + 1) sub b
      CLet _ _ a b c -> do
        ra <- collect d sub a
        rb <- collect d sub b
        rc <- collect (d + 1) sub c
        pure (ra ++ rb ++ rc)
      CLetRec _ _ a b c -> do
        ra <- collect d sub a
        rb <- collect (d + 1) sub b
        rc <- collect (d + 1) sub c
        pure (ra ++ rb ++ rc)
      CIf a b c -> concat3 <$> collect d sub a <*> collect d sub b <*> collect d sub c
      CMatch scrut alts -> do
        rs <- collect d sub scrut
        let scrutLvl = case scrut of
              CVar i -> rootOf (d - 1 - i)
              _ -> Nothing
            rootOf lvl
              | lvl `elem` paramLevels = Just lvl
              | otherwise = Map.lookup lvl sub
        ralts <- forM alts $ \(CaseAlt pat gd b) -> do
          let nb = patBindersC pat
              newLvls = [d .. d + nb - 1]
              sub' = case scrutLvl of
                Just root | ctorBinds pat -> foldr (\l m -> Map.insert l root m) sub newLvls
                _ -> sub
          rg <- maybe (Just []) (collect (d + nb) sub') gd
          rb <- collect (d + nb) sub' b
          pure (rg ++ rb)
        pure (rs ++ concat ralts)
      CCtor _ as -> concat <$> mapM (collect d sub) as
      CRecordT fs -> concat <$> mapM (collect d sub . snd) fs
      CRecordV fs -> concat <$> mapM (collect d sub . snd) fs
      CProj e _ -> collect d sub e
      CVariantT ms -> concat <$> mapM (collect d sub) ms
      CInject _ e -> collect d sub e
      CThunkE e -> collect d sub e
      CLazyE e -> collect d sub e
      CForceE e -> collect d sub e
      CDo _ -> Just [] -- loops handle their own progress; no self-calls expected
      _ -> Just []
      where
        concat3 a b c = a ++ b ++ c

    ctorBinds = \case
      CPCtor _ _ -> True
      CPInject _ _ -> True
      CPOr ps -> all ctorBinds ps
      CPAs _ p -> ctorBinds p
      _ -> False

    spineOf :: Term -> (Term, [(Icit, Term)])
    spineOf = go []
      where
        go acc (CApp ic f a) = go ((ic, a) : acc) f
        go acc f = (f, acc)

    -- the root param level an argument descends from, if any
    argRoot d sub = \case
      CVar i ->
        let lvl = d - 1 - i
         in Map.lookup lvl sub
      _ -> Nothing

    decreasingAt i call =
      case lookup i call of
        Just (Just root) -> root `elem` take (i + 1) paramLevels || root `elem` paramLevels
        _ -> False

checkAgainstSig :: Value -> [Binder] -> Expr -> Span -> CheckM Term
checkAgainstSig sigTy binders body sp = do
  -- consume binders against the signature's Pi telescope
  go emptyCtx sigTy binders
  where
    go ctx ty [] = check ctx body ty
    go ctx ty0 (b : rest) = do
      ty <- forceM ty0
      case ty of
        VPi Impl q nm dom clo
          | not (bImplicit b) -> do
              -- skip implicit binder: bind it for the body
              let ctx' = bindCtx nm True dom ctx
              cod <- clApp clo (VRigid (ctxLen ctx) [])
              CLam Impl q nm <$> go ctx' cod (b : rest)
        VPi ic q nm dom clo -> do
          let bn = fromMaybe nm (nameText <$> bName b)
          forM_ (binderTypeExpr b) $ \tyE -> do
            (tyTm, _) <- inferType ctx tyE
            tyV <- evalIn ctx tyTm
            expectType ctx (bSpan b) dom tyV
          unless (ic == (if bImplicit b then Impl else Expl)) $
            errAt (bSpan b) "E_BINDER_MISMATCH" (Just "kappa.type.binder")
              "binder implicitness does not match the signature"
          let ctx' = bindCtx bn (bImplicit b) dom ctx
          cod <- clApp clo (VRigid (ctxLen ctx) [])
          CLam ic q bn <$> go ctx' cod rest
        _ -> do
          errAt sp "E_SIGNATURE_ARITY" (Just "kappa.type.signature-arity")
            "definition has more parameters than its signature type"
          check ctx body ty

elabFunction :: [Binder] -> Maybe Expr -> Expr -> Span -> CheckM (Term, Value)
elabFunction [] mResTy body _ = case mResTy of
  Just tyE -> do
    (tyTm, _) <- inferType emptyCtx tyE
    tyV <- evalIn emptyCtx tyTm
    tm <- check emptyCtx body tyV
    pure (tm, tyV)
  Nothing -> do
    (tm, ty) <- infer emptyCtx body
    insertAllImplicits emptyCtx (exprSpan body) tm ty
elabFunction binders mResTy body sp = do
  let bodyE = case mResTy of
        Just tyE -> EAscription body tyE sp
        Nothing -> body
  elabLambda emptyCtx binders bodyE sp Nothing

elabInstance :: InstanceDecl -> Span -> CheckM ()
elabInstance (InstanceDecl premises hd members) sp = do
  flushPending
  -- head must be Trait args...
  (traitG, argEs) <- splitHead hd
  st <- get
  case traitG >>= \g -> (,) g <$> Map.lookup g (csTraits st) of
    Nothing ->
      errAt sp "E_INSTANCE_HEAD" (Just "kappa.trait.bad-instance-head")
        "instance head must be a trait applied to type arguments"
    Just (g, ti) -> do
      -- collect implicitly-universalized lowercase variables (§11.3.3)
      let fvs = nub (concatMap freeLower (hd : premises))
      -- telescope: fvs as Type params, then premise dicts
      let teleLen = length fvs + length premises
      -- elaborate under fvs bound
      let ctx0 = foldl (\c v -> bindCtx v False (VSort 0) c) emptyCtx fvs
      premTms <- forM premises $ \p -> fst <$> inferType ctx0 p
      ctxP' <- bindPremises ctx0 premTms
      argTms <- mapM (\e -> fst <$> inferType ctxP' e) argEs
      -- register the instance before checking members so member bodies
      -- can use the instance being defined (recursive instances, §14.3)
      dictName <- freshNameM ("__inst_" <> gnameText g <> "_")
      stm0 <- get
      let dictG = GName (csModule stm0) dictName
      dictTy <- instanceDictTy g fvs premTms argTms
      addGlobal dictG (GlobalDef dictTy Nothing False)
      modify' $ \s ->
        s
          { csInstances =
              InstanceEntry g teleLen (map (shiftTerm (length premises) 0) premTms) argTms dictG
                : csInstances s
          }
      -- §14.1.4/§14.3.3 (minimum): every supertrait premise of the
      -- trait must be satisfiable at the instance head (from the
      -- instance's own premises — including their transitive
      -- supertrait conformance paths — or the global instance set)
      forM_ (tiSupers ti) $ \supClosed -> do
        ec <- ec_
        argVs <- mapM (evalIn ctxP') argTms
        supF <- evalIn ctxP' supClosed
        supGoal <- forceM (evalApp ec supF [(Expl, a) | a <- argVs])
        mLoc <- localCandidate ctxP' supGoal
        satisfied <- case mLoc of
          Just _ -> pure True
          Nothing -> do
            mInst <- instanceSearch ctxP' sp supGoal
            case mInst of
              Just _ -> pure True
              Nothing -> do
                let premTys = [ceType e | e <- ctxEntries ctxP', ceImplicitLocal e]
                    anyPath [] = pure False
                    anyPath (t : ts) = do
                      found <- supertraitPath ctxP' 4 t supGoal
                      if found then pure True else anyPath ts
                anyPath premTys
        unless satisfied $ do
          gT <- quoteIn ctxP' supGoal
          errAt sp "E_SUPERTRAIT_UNSATISFIED" (Just "kappa.trait.supertrait-unsatisfied")
            ("instance does not satisfy the supertrait premise '" <> renderTerm gT <> "' of trait '" <> gnameText g <> "' (§14.1.4)")
      -- member definitions checked against member types
      dictFields <- forM (tiMembers ti) $ \mn -> do
        case findMember mn members of
          Just (LetDef _ _ mbinders mResTy _ mbody, msp) -> do
            memberTyV <- memberSigInstance g mn argTms ctxP'
            tm <- checkMemberAgainst ctxP' memberTyV mbinders mResTy mbody msp
            pure (Just (mn, tm))
          Nothing -> case Map.lookup mn (tiDefaults ti) of
            -- the trait's default definition fills the member (§14.2.3)
            -- the default's own annotation mentions trait parameters
            -- and is superseded by the instantiated member type
            Just (LetDef _ _ dbinders _ _ dbody) -> do
              memberTyV <- memberSigInstance g mn argTms ctxP'
              tm <- checkMemberAgainst ctxP' memberTyV dbinders Nothing dbody sp
              pure (Just (mn, tm))
            Nothing -> do
              errAt sp "E_INSTANCE_MEMBER_MISSING" (Just "kappa.trait.member-missing")
                ("instance does not define member '" <> mn <> "'")
              pure Nothing
      flushPending
      let fields = sortOn fst (catMaybes dictFields)
          dictBody = CRecordV fields
          -- order: fvs outermost, then premises
          wrapped =
            foldr (\v acc -> CLam Impl Q0 v acc) (foldr (\_ acc -> CLam Impl QW "__p" acc) dictBody premises) fvs
      wrapped' <- zonkTermM 0 wrapped
      dictV <- evalIn emptyCtx wrapped'
      addGlobal dictG (GlobalDef dictTy (Just dictV) True)
  where
    splitHead e = case e of
      EApp f args -> do
        (g, es) <- splitHead f
        pure (g, es ++ [a | ArgExplicit a <- args])
      EVar n -> do
        mg <- lookupGlobalName (nameText n)
        pure (mg, [])
      _ -> pure (Nothing, [])
    findMember mn ms =
      case [ (ld, dsp) | DLet _ ld@(LetDef (Just dn) _ _ _ _ _) dsp <- ms, nameText dn == mn
           ] of
        (x : _) -> Just x
        [] -> Nothing

    bindPremises ctx [] = pure ctx
    bindPremises ctx (p : rest) = do
      pv <- evalIn ctx p
      bindPremises (bindCtx "__prem" True pv ctx) rest

    memberSigInstance traitG mn argTms ctx = do
      mt <- globalTerm (memberGlobal traitG mn)
      case mt of
        Just (_, projTy) -> do
          argVs <- mapM (evalIn ctx) argTms
          peelArgs projTy argVs
        Nothing -> pure (VSort 0)
      where
        peelArgs ty [] = do
          t <- forceM ty
          case t of
            VPi Impl _ _ _ clo -> do
              -- the dict binder: instantiate with a fresh meta (the dict
              -- being defined); member types may not depend on it.
              m <- freshMetaV ctx
              clApp clo m
            _ -> pure t
        peelArgs ty (a : as) = do
          t <- forceM ty
          case t of
            VPi Impl _ _ _ clo -> do
              r <- clApp clo a
              peelArgs r as
            _ -> pure t

    checkMemberAgainst ctx memberTy mbinders mResTy mbody msp =
      case mbinders of
        [] -> check ctx (maybe mbody (\t -> EAscription mbody t msp) mResTy) memberTy
        _ -> checkLambdaAgainst ctx memberTy mbinders mbody msp

    checkLambdaAgainst ctx ty binders body msp = do
      t <- forceM ty
      case (binders, t) of
        ([], _) -> check ctx body t
        (b : rest, VPi Impl q nm dom clo)
          | not (bImplicit b) -> do
              let ctx' = bindCtx nm True dom ctx
              cod <- clApp clo (VRigid (ctxLen ctx) [])
              CLam Impl q nm <$> checkLambdaAgainst ctx' cod (b : rest) body msp
        (b : rest, VPi ic q nm dom clo) -> do
          let bn = fromMaybe nm (nameText <$> bName b)
              ctx' = bindCtx bn (bImplicit b) dom ctx
          cod <- clApp clo (VRigid (ctxLen ctx) [])
          CLam ic q bn <$> checkLambdaAgainst ctx' cod rest body msp
        (_ : _, _) -> do
          errAt msp "E_SIGNATURE_ARITY" (Just "kappa.type.signature-arity")
            "instance member has more parameters than the trait member type"
          check ctx body t

    instanceDictTy traitG fvs premTms argTms = do
      -- premises were elaborated under the fv binders only; the k-th
      -- premise domain sits under k earlier premise binders, so shift by
      -- k. The head ('argTms') was elaborated under fvs + all premises
      -- and is already correctly indexed.
      let dictHead = foldl (\f a -> CApp Expl f a) (CGlob traitG) argTms
          withPrems = go (0 :: Int) premTms
          go _ [] = dictHead
          go k (p : ps) = CPi Impl QW "__p" (shiftTerm k 0 p) (go (k + 1) ps)
          nest [] = withPrems
          nest (v : vs) = CPi Impl Q0 v (CSort 0) (nest vs)
      evalIn emptyCtx (nest fvs)

-- §14.3.3 conformance paths (depth-bounded): evidence of type 'evTy'
-- (a trait application) yields the trait goal 'goal' either directly or
-- through the evidence trait's transitive supertrait premises.
supertraitPath :: Ctx -> Int -> Value -> Value -> CheckM Bool
supertraitPath _ 0 _ _ = pure False
supertraitPath ctx depth evTy goal = do
  st0 <- get
  ok <- unify ctx evTy goal
  if ok
    then pure True
    else do
      put st0
      ev <- forceM evTy
      case ev of
        VGlobN tg args -> do
          mti <- gets (Map.lookup tg . csTraits)
          case mti of
            Just ti -> anyPath (tiSupers ti)
              where
                anyPath [] = pure False
                anyPath (supClosed : rest) = do
                  ec <- ec_
                  supF <- evalIn ctx supClosed
                  supV <- forceM (evalApp ec supF [(Expl, a) | (_, a) <- args])
                  found <- supertraitPath ctx (depth - 1) supV goal
                  if found then pure True else anyPath rest
            Nothing -> pure False
        _ -> pure False

-- free lowercase identifiers (implicit universalization, §11.3.3
-- approximation: ASCII lowercase heads not resolving to globals).
freeLower :: Expr -> [Text]
freeLower = go
  where
    go = \case
      EVar (Name n _)
        | isLowerHead n -> [n]
        | otherwise -> []
      EApp f args -> go f ++ concatMap goArg args
      EArrow b e -> maybe [] go (bType b) ++ withoutBinders [b] (go e)
      EForall bs e _ -> concatMap (maybe [] go . bType) bs ++ withoutBinders bs (go e)
      ETraitArrow a b -> go a ++ go b
      EOptionSugar e _ -> go e
      ETuple es _ -> concatMap go es
      -- a dotted head (module path / projection, e.g. `main.Big`) is
      -- never an implicitly-universalized type variable
      EDot {} -> []
      _ -> []
    withoutBinders bs fvs =
      let bound = [nameText n | b <- bs, Just n <- [bName b]]
       in filter (`notElem` bound) fvs
    goArg = \case
      ArgExplicit e -> go e
      ArgImplicit e -> go e
      _ -> []
    isLowerHead n = case T.uncons n of
      Just (c, _) -> c >= 'a' && c <= 'z'
      Nothing -> False
