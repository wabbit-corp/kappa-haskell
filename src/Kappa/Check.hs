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
  , csManifest :: !(Map GName ())
  -- ^ §2.8.4 manifest bindings (no widening signature): reified
  -- static-object identity is preserved through them
  , csActive :: !(Map GName APInfo)
  -- ^ §17.3 active-pattern definitions and their result classification
  , csFacts :: !(Map Int RigidFact)
  -- ^ Branch-local dependent-match facts about rigid levels (§7.4.1),
  -- consulted by conversion-time match reduction
  , csProjections :: !(Map GName ProjInfo)
  -- ^ §9.1.1 projection definitions: binder structure for the
  -- projection facet at application sites
  , csDemand :: !PlaceDemand
  -- ^ surrounding place demand of the expression being elaborated
  -- (selects the §16.1.5/§16.1.6 eliminator and accessor capability)
  }

-- | §16.1.5/§16.1.6 surrounding demand at a descriptor application.
data PlaceDemand = DemandRead | DemandConsume | DemandOpen
  deriving stock (Eq, Show)

-- | §9.1.1 projection-facet metadata (one entry per declared name).
data ProjInfo = ProjInfo
  { pjIsPlace :: ![Bool] -- ^ per explicit binder, declaration order
  , pjPlaceNames :: ![Text] -- ^ place binder names, declaration order
  , pjSelector :: !Bool -- ^ selector form (vs expanded accessor form)
  , pjYields :: ![(Text, [Text])] -- ^ selector yield places: root binder, path
  }

-- | Active-pattern result classification (§17.3.1).
data APResult = APOption | APMatch | APTotal
  deriving stock (Eq, Show)

newtype APInfo = APInfo
  { apResult :: APResult
  }

initCheckState :: CheckState
initCheckState =
  CheckState Map.empty Map.empty Map.empty Map.empty [] emptyMetas 0 []
    (ModuleName ["main"]) Map.empty Map.empty Map.empty 0 [] Map.empty Map.empty Map.empty
    Map.empty Map.empty Map.empty Map.empty DemandRead

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
  , ceQ :: !(Maybe S.Quantity)
  -- ^ Quantity prefix of an implicit local binder (§16.3.3).
  , ceBorrow :: !Bool
  -- ^ @\@&@-marked implicit local: may not escape into closures.
  }

data Ctx = Ctx
  { ctxEntries :: ![CtxEntry]
  , ctxEnv :: !Env
  , ctxRefines :: !(Map Text [GName])
  -- ^ §7.4.1 flow refinement: variable → possible constructors.
  , ctxAliases :: !(Map Text Text)
  -- ^ §7.4.3 stable aliases: @let q = p@ makes q transport p's refinement.
  , ctxBarriers :: ![Int]
  -- ^ Context lengths at which lambda bodies began (closure
  -- boundaries for §16.3.3 borrow-escape and scope grouping).
  }

emptyCtx :: Ctx
emptyCtx = Ctx [] [] Map.empty Map.empty []

ctxLen :: Ctx -> Int
ctxLen = length . ctxEntries

-- | Mark a closure boundary: entries below it are captured (§16.2.1).
pushCtxBarrier :: Ctx -> Ctx
pushCtxBarrier ctx = ctx {ctxBarriers = ctxLen ctx : ctxBarriers ctx}

bindCtx :: Text -> Bool -> Value -> Ctx -> Ctx
bindCtx n implocal ty (Ctx es env refs als bars) =
  Ctx (CtxEntry n ty implocal False Nothing False : es) (VRigid (length env) [] : env)
    (Map.delete n refs) (Map.delete n als) bars

-- | Bind a local definition: the environment carries the definiens, so
-- conversion sees through local lets (delta for locals, §15.1).
bindCtxLet :: Text -> Bool -> Value -> Value -> Ctx -> Ctx
bindCtxLet n implocal ty v (Ctx es env refs als bars) =
  Ctx (CtxEntry n ty implocal False Nothing False : es) (v : env)
    (Map.delete n refs) (Map.delete n als) bars

-- | Bind a @var@ cell (type @Ref a@); uses read through it (§18.6.1).
bindCtxVar :: Text -> Value -> Ctx -> Ctx
bindCtxVar n ty (Ctx es env refs als bars) =
  Ctx (CtxEntry n ty False True Nothing False : es) (VRigid (length env) [] : env)
    (Map.delete n refs) (Map.delete n als) bars

-- | Record the implicit binder prefix on the most recent entry
-- (quantity and borrow marker, §16.3.3).
setTopPrefix :: BinderPrefix -> Ctx -> Ctx
setTopPrefix (BinderPrefix mq mb) ctx = case ctxEntries ctx of
  (e : rest) -> ctx {ctxEntries = e {ceQ = mq, ceBorrow = isJust mb} : rest}
  [] -> ctx

-- | The §7.4.3 stable-alias root of a variable.
refineRoot :: Ctx -> Text -> Text
refineRoot ctx = go (16 :: Int)
  where
    go 0 n = n
    go fuel n = case Map.lookup n (ctxAliases ctx) of
      Just n' -> go (fuel - 1) n'
      Nothing -> n

-- | Record §7.4.1 refinements (through alias roots).
refineCtx :: [(Text, [GName])] -> Ctx -> Ctx
refineCtx refs ctx =
  ctx {ctxRefines = foldr add (ctxRefines ctx) refs}
  where
    add (n, gs) = Map.insert (refineRoot ctx n) gs

-- | Record a stable alias @q = p@ (§7.4.3).
addCtxAlias :: Text -> Text -> Ctx -> Ctx
addCtxAlias q p ctx = ctx {ctxAliases = Map.insert q p (ctxAliases ctx)}

-- | Current refinement of a variable, through its alias root.
ctxRefinementOf :: Ctx -> Text -> Maybe [GName]
ctxRefinementOf ctx n = Map.lookup (refineRoot ctx n) (ctxRefines ctx)

lookupCtx :: Text -> Ctx -> Maybe (Int, CtxEntry)
lookupCtx n ctx = go 0 (ctxEntries ctx)
  where
    go _ [] = Nothing
    go i (e : rest)
      | ceName e == n = Just (i, e)
      | otherwise = go (i + 1) rest

ec_ :: CheckM EvalCtx
ec_ = gets (\st -> EvalCtx (Globals (csGlobals st)) (csMetas st) False (csFacts st))

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

-- | Run an action under a given §16.1.5 place demand, restoring the
-- ambient demand afterwards.
withDemand :: PlaceDemand -> CheckM a -> CheckM a
withDemand d act = do
  old <- gets csDemand
  modify' $ \st -> st {csDemand = d}
  r <- act
  modify' $ \st -> st {csDemand = old}
  pure r

demandOfQ :: Q -> PlaceDemand
demandOfQ q
  | q `elem` [Q1, QGe1] = DemandConsume
  | otherwise = DemandRead

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

-- | Pi binder-quantity subsumption (§12.2.1): a function whose demand
-- interval is contained in the expected binder's demand may stand at
-- that type — every argument capability satisfying the expected demand
-- also satisfies the actual one (e.g. a @(1 x : A) -> B@ value may be
-- used where @(x : A) -> B@ is expected, but not vice versa).
qSubsumes :: Q -> Q -> Bool
qSubsumes qa qe = qa == qe || qInterval qa `contained` qInterval qe
  where
    qInterval :: Q -> (Int, Maybe Int)
    qInterval = \case
      Q0 -> (0, Just 0)
      Q1 -> (1, Just 1)
      QLe1 -> (0, Just 1)
      QGe1 -> (1, Nothing)
      QW -> (0, Nothing)
    contained (lo1, hi1) (lo2, hi2) =
      lo1 >= lo2 && case (hi1, hi2) of
        (_, Nothing) -> True
        (Nothing, Just _) -> False
        (Just h1, Just h2) -> h1 <= h2

unify :: Ctx -> Value -> Value -> CheckM Bool
unify ctx = goTop True
  where
    -- qok: §12.2.1 binder-quantity subsumption applies only along the
    -- outer Pi spine of the unified types, never under records, type
    -- arguments, or domains (no deep subsumption)
    goTop qok a b = do
      a' <- forceM a
      b' <- forceM b
      go qok (ctxLen ctx) a' b'
    go qok lvl a b = case (a, b) of
      (VFlex m [], t) -> solveFlex lvl m t
      (t, VFlex m []) -> solveFlex lvl m t
      -- applied metas: first-order decomposition (?m a̅ ≡ G b̅ pre a̅'
      -- solves ?m := G b̅ pre and unifies the argument tails pairwise) —
      -- the standard Miller-adjacent approximation for higher-kinded
      -- goals like ?f Int ≡ Option Int (§14.3.1)
      (VFlex m sp, t) | not (null sp) -> solveFlexSpine lvl m sp t
      (t, VFlex m sp) | not (null sp) -> solveFlexSpine lvl m sp t
      (VSort m, VSort n) -> pure (m <= n) -- cumulativity (§11.1.1)
      (VPi i1 q1 _ d1 c1, VPi i2 q2 _ d2 c2) | i1 == i2 && (q1 == q2 || (qok && qSubsumes q1 q2)) -> do
        ok <- goTop False d1 d2
        if not ok
          then pure False
          else do
            let x = VRigid lvl []
            b1 <- clApp c1 x
            b2 <- clApp c2 x
            b1' <- forceM b1
            b2' <- forceM b2
            go qok (lvl + 1) b1' b2'
      (VRecordT f1, VRecordT f2) | map fst f1 == map fst f2 ->
        andM [goTop False x y | ((_, x), (_, y)) <- zip f1 f2]
      (VVariantT m1, VVariantT m2) | length m1 == length m2 ->
        andM (zipWith (goTop False) m1 m2)
      (VCtor g1 a1, VCtor g2 a2) | g1 == g2 && length a1 == length a2 ->
        andM (zipWith (goTop False) a1 a2)
      (VGlobN g1 sp1, VGlobN g2 sp2)
        | g1 == g2 && length sp1 == length sp2 -> do
            ok <- andM (zipWith (\(_, x) (_, y) -> goTop False x y) sp1 sp2)
            if ok then pure True else fallback lvl a b
      -- rigid-rigid spine decomposition (incomplete but standard; the
      -- definitional-equality fallback still decides the rest)
      (VRigid l1 sp1, VRigid l2 sp2)
        | l1 == l2 && length sp1 == length sp2 && not (null sp1) -> do
            st0 <- get
            ok <- andM (zipWith (\(_, x) (_, y) -> goTop False x y) sp1 sp2)
            if ok then pure True else put st0 >> fallback lvl a b
      _ -> fallback lvl a b
      where
        andM [] = pure True
        andM (m : ms) = m >>= \ok -> if ok then andM ms else pure False
    fallback lvl a b = do
      ec <- ec_
      pure (convertible ec lvl a b)
    solveFlexSpine lvl m sp t = case t of
      VGlobN g sp2
        | length sp2 >= length sp -> do
            st0 <- get
            let (pre, post) = splitAt (length sp2 - length sp) sp2
            ok <- solveFlex lvl m (VGlobN g pre)
            oks <-
              if ok
                then andM' [goTop False x y | ((_, x), (_, y)) <- zip sp post]
                else pure False
            if oks then pure True else put st0 >> fallback lvl (VFlex m sp) t
      VRigid l sp2
        | length sp2 >= length sp -> do
            st0 <- get
            let (pre, post) = splitAt (length sp2 - length sp) sp2
            ok <- solveFlex lvl m (VRigid l pre)
            oks <-
              if ok
                then andM' [goTop False x y | ((_, x), (_, y)) <- zip sp post]
                else pure False
            if oks then pure True else put st0 >> fallback lvl (VFlex m sp) t
      VFlex m2 sp2
        | length sp2 == length sp -> do
            st0 <- get
            ok <- solveFlex lvl m (VFlex m2 [])
            oks <-
              if ok
                then andM' [goTop False x y | ((_, x), (_, y)) <- zip sp sp2]
                else pure False
            if oks then pure True else put st0 >> fallback lvl (VFlex m sp) t
      _ -> fallback lvl (VFlex m sp) t
      where
        andM' [] = pure True
        andM' (mx : ms) = mx >>= \ok -> if ok then andM' ms else pure False
    solveFlex lvl m t = do
      st <- get
      case Map.lookup m (csMetas st) of
        Just (Just sol) -> do
          sol' <- forceM sol
          t' <- forceM t
          go False lvl sol' t'
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
resolveImplicit ctx sp goal = resolveImplicitQ ctx sp Q0 goal

-- | Resolve an implicit argument for a binder of quantity @q@ (§16.3.3).
-- The quantity distinguishes runtime implicits (which demand an actual
-- candidate, fixtures' @\@ω env : Env@ style) from erased ones (whose
-- values may be inferred later by unification).
resolveImplicitQ :: Ctx -> Span -> Q -> Value -> CheckM Term
resolveImplicitQ ctx sp q goal = do
  g <- forceM goal
  kindLike <- isKindLike (ctxLen ctx) g
  case g of
    _ | kindLike -> freshMeta -- type\/type-constructor params are inferred
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
          -- a flex-headed goal type is not searchable evidence: its
          -- value is inferred by unification at the use site (§16.3.3)
          gIsFlex <- do
            gF <- forceM g
            pure $ case gF of
              VFlex {} -> True
              _ -> False
          if gIsFlex && not (isTrait || isEq)
            then freshMeta
            else resolveLadder g isTrait isEq
  where
    resolveLadder g isTrait isEq = do
      do
          -- §16.3.3 step 1: the local implicit context goes first.
          mLoc <- localCandidate ctx sp q g
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
                      if isTrait || isEq || q /= Q0
                        then do
                          gT <- quoteIn ctx g
                          errAt sp "E_IMPLICIT_UNSOLVED" (Just "kappa.implicit.unsolved")
                            ("could not resolve implicit argument of type " <> renderTerm gT
                               <> (if isTrait || isEq then "" else "; a runtime implicit binder requires an implicit local candidate in scope (§16.3.3), and top-level terms are not candidates"))
                          freshMeta
                        else freshMeta

-- | Kind-like goals — @Type@, @Type -> Type@, … — are inferred from
-- use sites (metavariables), never searched as evidence (§16.3.3).
isKindLike :: Int -> Value -> CheckM Bool
isKindLike lvl v = do
  t <- forceM v
  case t of
    VSort _ -> pure True
    VPi _ _ _ _ clo -> do
      cod <- clApp clo (VRigid lvl [])
      isKindLike (lvl + 1) cod
    _ -> pure False

localCandidate :: Ctx -> Span -> Q -> Value -> CheckM (Maybe Term)
localCandidate ctx sp q goal = go 0 [] (ctxEntries ctx)
  where
    -- anonymous binders are not referenceable and never shadow
    shadowName e = [ceName e | ceName e `notElem` ["_", "_ev"]]
    go _ _ [] = pure Nothing
    go i seen (e : rest)
      | ceImplicitLocal e
      , ceName e `notElem` seen = do
          st0 <- get
          ok <- unify ctx (ceType e) goal
          if ok
            then do
              checkAmbiguous i (shadowName e ++ seen) rest
              checkCandidate i e
              pure (Just (CVar i))
            else put st0 >> go (i + 1) (shadowName e ++ seen) rest
      | otherwise = go (i + 1) (shadowName e ++ seen) rest
    -- a second matching candidate in the same scope (no closure
    -- boundary between the two) is ambiguous (§16.3.3)
    checkAmbiguous i seen rest = do
      let lvlOf ix = ctxLen ctx - 1 - ix
      next <- findNext (i + 1) seen rest
      forM_ next $ \j -> do
        let l1 = lvlOf i
            l2 = lvlOf j
            separated = any (\b -> l2 < b && b <= l1) (ctxBarriers ctx)
        unless separated $
          errAt sp "E_IMPLICIT_AMBIGUOUS" (Just "kappa.implicit.ambiguous")
            "two implicit candidates in the same scope satisfy this implicit goal; the resolution is ambiguous (§16.3.3)"
    findNext _ _ [] = pure Nothing
    findNext j seen (e : rest)
      | ceImplicitLocal e
      , ceName e `notElem` seen = do
          st0 <- get
          ok <- unify ctx (ceType e) goal
          put st0
          if ok then pure (Just j) else findNext (j + 1) (shadowName e ++ seen) rest
      | otherwise = findNext (j + 1) (shadowName e ++ seen) rest
    checkCandidate i e = do
      -- an erased candidate cannot satisfy a runtime implicit (§12.2)
      when (q /= Q0 && ceQ e == Just S.QZero) $
        errAt sp "E_QTT_ERASED_RUNTIME_USE" (Just "kappa.qtt.erased-runtime-use")
          ("the implicit candidate '" <> ceName e <> "' is erased (@0) and cannot satisfy a runtime implicit binder (§12.2)")
      -- a borrowed candidate may not be captured across a closure
      -- boundary (§16.3.3, §12.3.2)
      let lvl = ctxLen ctx - 1 - i
      when (ceBorrow e && any (> lvl) (ctxBarriers ctx)) $
        errAt sp "E_QTT_BORROW_ESCAPE" (Just "kappa.qtt.borrow-escape")
          ("the borrowed implicit candidate '" <> ceName e <> "' may not be captured by a closure (§12.3.2)")

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
        mLoc <- localCandidate ctx sp Q0 g
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
            mLoc <- localCandidate ctx noSpan Q0 pv
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
    VPi Impl q _ dom clo -> do
      arg <- resolveImplicitQ ctx sp q dom
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
  -- carrier-prefixed comprehension (§20.9): a type-valued head applied
  -- to a comprehension literal selects a collection carrier
  EApp f args
    | not (null args)
    , ArgExplicit (EComprehension k cs y csp) <- last args -> do
        st0 <- get
        let preArgs = init args
        mPrefix <- carrierPrefix ctx f preArgs
        case mPrefix of
          Just prefix -> elabComprehensionC ctx k cs y csp (Just prefix)
          Nothing -> do
            put st0
            (fTm, fTy) <- infer ctx f
            elabSpine ctx (exprSpan f) fTm fTy args
  EApp f args -> do
    mproj <- projectionHead ctx f
    case mproj of
      Just (g, pj) -> elabProjApp ctx (exprSpan f) g pj args
      Nothing -> do
        (fTm, fTy) <- infer ctx f
        elabSpine ctx (exprSpan f) fTm fTy args
  EDot e m -> elabDot ctx e m
  EQDot e m -> elabSafeNav ctx e m
  EElvis l r sp -> elabElvis ctx l r sp
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
  EMapLit kvs _ -> do
    keyT <- freshMetaV ctx
    valT <- freshMetaV ctx
    entries <- forM kvs $ \(k, v) -> do
      kTm <- check ctx k keyT
      vTm <- check ctx v valT
      pure (CRecordV [("key", kTm), ("value", vTm)])
    let listTm = foldr (\h t -> CCtor (gPrel "::") [h, t]) (CCtor (gPrel "Nil") []) entries
    pure
      ( CApp Expl (CGlob (gPrel "__mapFromEntries")) listTm
      , VGlobN (gPrel "Map") [(Expl, keyT), (Expl, valT)]
      )
  ESetLit es _ -> do
    elemT <- freshMetaV ctx
    tms <- mapM (\e -> check ctx e elemT) es
    let listTm = foldr (\h t -> CCtor (gPrel "::") [h, t]) (CCtor (gPrel "Nil") []) tms
    pure
      ( CApp Expl (CGlob (gPrel "__setFromList")) listTm
      , VGlobN (gPrel "Set") [(Expl, elemT)]
      )
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
    (_, VGlobN (GName _ "Need") [(_, a)]) -> do
      -- §16.1.7.1 lazy insertion: a value in Need position suspends
      r <- tryInferAgainst expr expected
      case r of
        Just tm -> pure tm
        Nothing -> CLazyE <$> check ctx expr a
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
      special <- projDescriptorMismatch ctx expr ty1 expected
      unless special $
        expectType ctx (exprSpan expr) ty1 expected
      pure tm1
  where
    -- §16.1.5: a fully applied projection in descriptor-typed position
    -- gets the dedicated diagnostic rather than a plain mismatch
    projDescriptorMismatch c ex actual expect = case expect of
      VGlobN (GName pm dn) _
        | pm == preludeModule
        , dn `elem` ["Projector", "Getter", "Opener", "Setter", "Sinker"]
        , EApp f args <- ex -> do
            mproj <- projectionHead c f
            case mproj of
              Just (_, pj) | projFullApp pj args -> do
                ok <- unify c actual expect
                if ok
                  then pure False
                  else do
                    errAt (exprSpan ex) "E_PROJECTION_DESCRIPTOR_VALUE_EXPECTED"
                      (Just "kappa.projection.descriptor")
                      "a fully applied projection denotes its focus value, not a first-class descriptor; use the unapplied projection name (§16.1.5)"
                    pure True
              _ -> pure False
      _ -> pure False
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
-- a match in type position selects the type facet in its arms
-- (dependent-match types, §17.1.4)
inferType ctx (EMatch scrut cases msp) = do
  tm <- checkMatch ctx scrut cases msp (VSort 0)
  pure (tm, 0)
inferType ctx e = do
  (tm, ty) <- inferT ctx e
  goSort tm ty
  where
    goSort tm ty = do
      t <- forceM ty
      case t of
        VSort n -> pure (tm, n)
        VFlex m [] -> solveMeta m (VSort 0) >> pure (tm, 0)
        -- compatibility accommodation for the external corpus: `IO a`
        -- written for `IO ?e a` (§18.1 IO : Type -> Type -> Type); the
        -- missing error parameter becomes a fresh metavariable
        VPi Expl _ _ _ _
          | CApp Expl (CGlob g) argTm <- tm
          , g == gPrel "IO" -> do
              m <- freshMeta
              pure (CApp Expl (CApp Expl (CGlob g) m) argTm, 0)
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
-- ── Projection applications (§16.1.5, §16.1.6) ───────────────────────

-- | Resolve an application head to a projection facet, if any.
projectionHead :: Ctx -> Expr -> CheckM (Maybe (GName, ProjInfo))
projectionHead ctx = \case
  EVar hn
    | Nothing <- lookupCtx (nameText hn) ctx -> do
        mg <- lookupGlobalName (nameText hn)
        st <- get
        pure $ do
          g <- mg
          pj <- Map.lookup g (csProjections st)
          pure (g, pj)
  _ -> pure Nothing

-- | Does a projection-head application supply every declared binder?
projFullApp :: ProjInfo -> [Arg] -> Bool
projFullApp pj args =
  all isExpl args && length args == length (pjIsPlace pj) && or (pjIsPlace pj)
  where
    isExpl = \case
      ArgExplicit _ -> True
      _ -> False

-- | Application of a named projection (§9.1.1): a full application in
-- declaration order supplies the place binders directly; otherwise the
-- ordinary term facet (descriptor) is applied (§16.1.5).
elabProjApp :: Ctx -> Span -> GName -> ProjInfo -> [Arg] -> CheckM (Term, Value)
elabProjApp ctx sp g pj args = do
  mt <- globalTerm g
  case mt of
    Nothing -> anyHole ctx
    Just (dTm, dTy)
      | projFullApp pj args -> do
          let split = zip (pjIsPlace pj) args
              ordArgs = [a | (False, a) <- split]
              placePairs =
                [ (nm, e)
                | ((True, ArgExplicit e), nm) <-
                    zip [p | p@(True, _) <- split] (pjPlaceNames pj)
                ]
          (dTm1, dTy1) <- elabSpine ctx sp dTm dTy ordArgs
          applyDescriptor ctx sp dTm1 dTy1 (RootsSeparate placePairs)
      | otherwise -> elabSpine ctx sp dTm dTy args

-- | How the place arguments of a descriptor application are supplied.
data RootsSupply
  = RootsSeparate ![(Text, Expr)] -- ^ full application: place binder ↦ argument
  | RootsSingle !Expr -- ^ §16.1.5 single roots argument

-- | The accessor capabilities of a structural bundle record type
-- (§16.1.6): @Just [(field, roots, focus)]@ when every field is an
-- accessor descriptor.
bundleCapsM :: [(Text, Value)] -> CheckM (Maybe [(Text, Value, Value)])
bundleCapsM fs
  | null fs = pure Nothing
  | otherwise = do
      caps <- forM fs $ \(nm, tv) -> do
        t <- forceM tv
        pure $ case t of
          VGlobN (GName pm former) [(_, roots), (_, focus)]
            | pm == preludeModule
            , lookup nm capFormers == Just former ->
                Just (nm, roots, focus)
          _ -> Nothing
      pure (sequence caps)
  where
    capFormers = [("get", "Getter"), ("open", "Opener"), ("set", "Setter"), ("sink", "Sinker")]

-- | If the callee elaborates to a projector or accessor-bundle
-- descriptor, elaborate the §16.1.5/§16.1.6 descriptor application.
descriptorApp :: Ctx -> Span -> Term -> Value -> Expr -> Maybe PlaceDemand -> CheckM (Maybe (Term, Value))
descriptorApp ctx sp fTm fTy e mdemand = case fTy of
  VGlobN (GName pm "Projector") [_, _]
    | pm == preludeModule -> Just <$> run
  VRecordT caps -> do
    mb <- bundleCapsM caps
    case mb of
      Just _ -> Just <$> run
      Nothing -> pure Nothing
  _ -> pure Nothing
  where
    run = maybe id withDemand mdemand (applyDescriptor ctx sp fTm fTy (RootsSingle e))

-- | Apply a descriptor value to its roots (§16.1.5/§16.1.6): validate
-- the place pack, select the eliminator for the surrounding demand, and
-- yield the focus.
applyDescriptor :: Ctx -> Span -> Term -> Value -> RootsSupply -> CheckM (Term, Value)
applyDescriptor ctx sp dTm dTy0 supply = do
  dTy <- forceM dTy0
  case dTy of
    VGlobN (GName pm "Projector") [(_, rootsV), (_, focusV)]
      | pm == preludeModule -> do
          placeTms <- elabRootsSupply ctx sp rootsV supply
          pure (foldl (CApp Expl) dTm placeTms, focusV)
    VRecordT capFs -> do
      mcaps <- bundleCapsM capFs
      case mcaps of
        Just caps@((_, rootsV, focusV) : _) -> do
          demand <- gets csDemand
          let want = case demand of
                DemandRead -> "get"
                DemandConsume -> "sink"
                DemandOpen -> "open"
              capNames = [nm | (nm, _, _) <- caps]
          placeTms <- elabRootsSupply ctx sp rootsV supply
          unless (want `elem` capNames) $
            errAt sp "E_PROJECTION_CAPABILITY_REQUIRED" (Just "kappa.projection.capability")
              ( "this use requires the '" <> capabilityWord demand
                  <> "' capability, but the accessor bundle provides only: "
                  <> T.intercalate ", " capNames <> " (§16.1.6)"
              )
          -- the value facet of the application always reads through
          -- 'get' when available (under '~' the §18.9 threading reads
          -- the focus and fills through 'set'/'open' at usage level)
          let readCap
                | demand == DemandConsume && "sink" `elem` capNames = "sink"
                | "get" `elem` capNames = "get"
                | otherwise = ""
          tm <-
            if T.null readCap
              then fst <$> anyHole ctx
              else pure (foldl (CApp Expl) (CProj dTm readCap) placeTms)
          pure (tm, focusV)
        _ -> do
          errAt sp "E_PROJECTION_DESCRIPTOR_VALUE_EXPECTED" (Just "kappa.projection.descriptor")
            "expected a projector or accessor-bundle descriptor value here (§16.1.5)"
          anyHole ctx
    _ -> do
      errAt sp "E_PROJECTION_DESCRIPTOR_VALUE_EXPECTED" (Just "kappa.projection.descriptor")
        "expected a projector or accessor-bundle descriptor value here (§16.1.5)"
      anyHole ctx
  where
    capabilityWord = \case
      DemandRead -> "get"
      DemandConsume -> "sink"
      DemandOpen -> "open"

-- | Elaborate the roots of a descriptor application in place-pack mode
-- (§16.1.5): each supplied field must be a stable place expression of
-- the corresponding field type. Returns the place terms in canonical
-- (lexicographic) root order.
elabRootsSupply :: Ctx -> Span -> Value -> RootsSupply -> CheckM [Term]
elabRootsSupply ctx _sp rootsV supply = do
  rootsF <- forceM rootsV
  let rfs = case rootsF of
        VRecordT fs -> fs
        _ -> []
  case supply of
    RootsSeparate pairs ->
      forM rfs $ \(nm, fty) ->
        case lookup nm pairs of
          Just e -> elabPlaceArg ctx e fty
          Nothing -> fst <$> anyHole ctx
    RootsSingle e -> case rfs of
      [(nm, fty)] -> case e of
        ERecordLit items isp -> do
          let fields = [(nameText fn, fe) | RecItem _ fn (Just fe) <- items]
          case fields of
            [(fn, fe)]
              | fn == nm, length items == 1 -> (: []) <$> elabPlaceArg ctx fe fty
            _ -> do
              errAt isp "E_PROJECTION_ROOTS_PACK_MISMATCH" (Just "kappa.projection.roots")
                ("the roots record literal must supply exactly the field '" <> nm <> "' (§16.1.5)")
              (: []) . fst <$> anyHole ctx
        _ -> (: []) <$> elabPlaceArg ctx e fty
      _ -> case e of
        ERecordLit items isp -> do
          let fields = [(nameText fn, fe) | RecItem _ fn (Just fe) <- items]
          if sort (map fst fields) /= map fst rfs || length items /= length fields
            then do
              errAt isp "E_PROJECTION_ROOTS_PACK_MISMATCH" (Just "kappa.projection.roots")
                ( "the roots record literal must supply exactly the fields: "
                    <> T.intercalate ", " (map fst rfs) <> " (§16.1.5)"
                )
              mapM (const (fst <$> anyHole ctx)) rfs
            else forM rfs $ \(nm, fty) ->
              case lookup nm fields of
                Just fe -> elabPlaceArg ctx fe fty
                Nothing -> fst <$> anyHole ctx
        _ -> do
          errAt (exprSpan e) "E_PROJECTION_DESCRIPTOR_ROOTS_LITERAL_REQUIRED" (Just "kappa.projection.roots")
            "the roots argument of a multi-root projector descriptor application must be a closed record literal (§16.1.5)"
          _ <- infer ctx e
          mapM (const (fst <$> anyHole ctx)) rfs

-- | One root of a place pack: must be a stable place expression
-- (§12.4.1) of the root field's type.
elabPlaceArg :: Ctx -> Expr -> Value -> CheckM Term
elabPlaceArg ctx e fty
  | stablePlaceExpr e = withDemand DemandRead (check ctx e fty)
  | otherwise = do
      errAt (exprSpan e) "E_PROJECTION_ROOT_INVALID" (Just "kappa.projection.roots")
        "a projection place argument must be a stable place expression (§12.4.1, §16.1.5)"
      _ <- withDemand DemandRead (infer ctx e)
      fst <$> anyHole ctx

-- | Syntactic stable-place check (§12.4.1 subset: variables and
-- record\/constructor field paths).
stablePlaceExpr :: Expr -> Bool
stablePlaceExpr = \case
  EVar _ -> True
  EDot e (DotName _) -> stablePlaceExpr e
  EAscription e _ _ -> stablePlaceExpr e
  _ -> False

elabSpine :: Ctx -> Span -> Term -> Value -> [Arg] -> CheckM (Term, Value)
elabSpine _ _ fTm fTy [] = pure (fTm, fTy)
elabSpine ctx sp fTm fTy0 (arg : rest) = do
  fTy <- forceM fTy0
  -- §16.1.5/§16.1.6: a descriptor-typed callee consumes its roots
  -- argument in place-pack mode
  mdesc <- case arg of
    ArgExplicit e -> descriptorApp ctx sp fTm fTy e Nothing
    ArgInout e _ -> descriptorApp ctx sp fTm fTy e (Just DemandOpen)
    _ -> pure Nothing
  case mdesc of
    Just (tm', ty') -> elabSpine ctx sp tm' ty' rest
    Nothing -> elabSpineArg ctx sp fTm fTy arg rest

elabSpineArg :: Ctx -> Span -> Term -> Value -> Arg -> [Arg] -> CheckM (Term, Value)
elabSpineArg ctx sp fTm fTy arg rest = do
  case (arg, fTy) of
    (ArgImplicit e, VPi Impl _ _ dom clo) -> do
      aTm <- check ctx e dom
      aV <- evalIn ctx aTm
      ty' <- clApp clo aV
      elabSpine ctx sp (CApp Impl fTm aTm) ty' rest
    (_, VPi Impl q _ dom clo) -> do
      iTm <- resolveImplicitQ ctx sp q dom
      iV <- evalIn ctx iTm
      ty' <- clApp clo iV
      elabSpine ctx sp (CApp Impl fTm iTm) ty' (arg : rest)
    (ArgExplicit e, VPi Expl q _ dom clo) -> do
      aTm <- withDemand (demandOfQ q) (check ctx e dom)
      aV <- evalIn ctx aTm
      ty' <- clApp clo aV
      elabSpine ctx sp (CApp Expl fTm aTm) ty' rest
    -- a '~place' marker against a callable parameter: the place value
    -- is demanded in open mode (§18.9.3, §16.1.6)
    (ArgInout e _, VPi Expl _ _ dom clo) -> do
      aTm <- withDemand DemandOpen (check ctx e dom)
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
    -- a '~place' call-site marker elaborates as the place expression;
    -- marker/parameter agreement is judged by the §18.9.3 usage analysis
    (ArgInout e _, _) -> elabSpine ctx sp fTm fTy (ArgExplicit e : rest)
    (ArgImplicit e, _) -> do
      errAt (exprSpan e) "E_APPLICATION_ARGUMENT_MISMATCH" (Just "kappa.application.argument")
        "an explicit implicit argument was supplied, but the callee has no implicit parameter here (§16.1.7.1)"
      -- recovery: do not cascade a type mismatch from the broken spine
      anyHole ctx
    (ArgExplicit e, _)
      -- a saturated constructor given extra arguments (§10.1.1)
      | Just _ <- termHeadCtor fTm -> do
          errAt (exprSpan e) "E_CONSTRUCTOR_ARITY_MISMATCH" (Just "kappa.application.arity")
            "too many arguments in constructor application"
          anyHole ctx
      -- a data-type head applied in term position selects its
      -- same-named constructor (§2.8.3 static-object term facet)
      | CGlob dg <- fTm -> do
          st <- get
          case Map.lookup dg (csDatas st) of
            Just di
              | (ctorG : _) <- [c | c <- diCtors di, gnameText c == gnameText dg] -> do
                  mt <- globalTerm ctorG
                  case mt of
                    Just (cTm, cTy) -> elabSpine ctx sp cTm cTy (ArgExplicit e : rest)
                    Nothing -> noncallable e
            _ -> noncallable e
      | otherwise -> noncallable e
      where
        noncallable e' = do
          fT <- quoteIn ctx fTy
          report $
            withNote ("callee type: " <> renderTerm fT) $
              diag SevError StageElaborate "E_APPLICATION_NONCALLABLE" (Just "kappa.application.non-callable")
                (exprSpan e')
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
        VPi Impl q _ dom clo -> do
          iTm <- resolveImplicitQ ctx sp q dom
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
        VPi Impl q _ dom clo -> do
          iTm <- resolveImplicitQ ctx sp q dom
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
    then pure (moduleObjectFor (ModuleName segs))
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
    let target = case Map.lookup n (csModuleAliases st) of
          Just mn -> Just mn
          Nothing
            | Map.member (ModuleName [n]) (csModuleExports st) -> Just (ModuleName [n])
            | otherwise -> Nothing
    case target of
      Just mn -> pure (moduleObjectFor mn)
      Nothing -> do
        errAt sp "E_STATIC_OBJECT_UNRESOLVED" (Just "kappa.name.unresolved")
          ("no module named '" <> n <> "' is in scope (Spec §2.8.6)")
        anyHole ctx
  _ -> do
    mg <- lookupGlobalName n
    -- §2.8.3: the selector must agree with the named facet — a trait
    -- has no type facet, so `type C` on a trait is rejected
    isTrait <- case mg of
      Just g -> gets (Map.member g . csTraits)
      Nothing -> pure False
    if sel == SelType && isTrait
      then do
        errAt nsp "E_STATIC_OBJECT_KIND_MISMATCH" (Just "kappa.static-object.kind")
          ("'" <> n <> "' names a trait; the 'type' selector does not apply (Spec §2.8.3)")
        anyHole ctx
      else do
        mr <- case mg of
          Just g -> globalType g
          Nothing -> pure Nothing
        case mr of
          Just r -> pure r
          Nothing -> do
            errAt nsp "E_STATIC_OBJECT_UNRESOLVED" (Just "kappa.name.unresolved")
              ("kind-qualified name does not resolve to a static object: '" <> n <> "' (Spec §2.8.6)")
            anyHole ctx

-- | §2.8.4: the manifest value of a receiver term — resolved through
-- local definientia, module-level lets without widening signatures,
-- record projections of such, and direct (immediately-used) results.
-- A binding under a widening signature forgets static-object identity.
manifestValue :: Ctx -> Term -> CheckM (Maybe Value)
manifestValue ctx tm = case tm of
  CGlob g -> do
    st <- get
    if Map.member g (csManifest st) || Map.member g (csDatas st)
      then case Map.lookup g (csGlobals st) >>= gdValue of
        Just v -> Just <$> forceM v
        Nothing -> pure (Just (VGlobN g []))
      else pure Nothing
  CProj t f -> do
    mv <- manifestValue ctx t
    case mv of
      Just (VRecordV fs) | Just v <- lookup f fs -> Just <$> forceM v
      _ -> pure Nothing
  CVar i -> case drop i (ctxEnv ctx) of
    (v : _) -> do
      v' <- forceM v
      pure $ case v' of
        VRigid {} -> Nothing -- an opaque binder, not a let definiens
        _ -> Just v'
    [] -> pure Nothing
  _ -> Just <$> (evalIn ctx tm >>= forceM)

-- a reified module object (§2.8.6): a record carrying the module
-- identity in a tag field, so member access through rebindings works
moduleObjectFor :: ModuleName -> (Term, Value)
moduleObjectFor (ModuleName segs) =
  let tag = "__module:" <> T.intercalate "." segs
   in (CRecordV [(tag, CRecordV [])], VRecordT [(tag, VRecordT [])])

-- member access on a reified module object (§2.8.6/§8.5)
moduleMember :: Ctx -> ModuleName -> Name -> CheckM (Term, Value)
moduleMember ctx modName mname = do
  st <- get
  let g = GName modName (nameText mname)
  mt <-
    if memberVisible st modName (nameText mname)
      then case (Map.member g (csDatas st), Map.lookup g (csGlobals st)) of
        -- a member naming a data type denotes the type facet; term
        -- applications fall through to its same-named constructor
        (True, Just gd) -> pure (Just (CGlob g, gdType gd))
        _ -> globalTerm g
      else pure Nothing
  case mt of
    Just r -> pure r
    Nothing -> do
      errAt (nameSpan mname) "E_NAME_UNRESOLVED" (Just "kappa.name.unresolved")
        ("module object has no exported member '" <> nameText mname <> "' (Spec §2.8.6, §8.5)")
      anyHole ctx

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
      -- §2.8.3/§2.8.6: a receiver VALUE that is a reified type object
      -- selects static constructors; a reified module object selects
      -- module members. Only §2.8.4 manifest bindings (no widening
      -- signature) preserve the identity.
      mrv <- manifestValue ctx tm1
      st0 <- get
      case fromMaybe (VRecordV []) mrv of
        VGlobN d _
          | Just di <- Map.lookup d (csDatas st0)
          , (ctorG : _) <- [c | c <- diCtors di, gnameText c == nameText mn0] -> do
              mt <- globalTerm ctorG
              case mt of
                Just r -> pure r
                Nothing -> ordinaryAt mn0 tm1 ty1
        VRecordV [(tag, _)]
          | Just modTxt <- T.stripPrefix "__module:" tag ->
              moduleMember ctx (ModuleName (T.splitOn "." modTxt)) mn0
        _ -> ordinaryAt mn0 tm1 ty1

    ordinaryAt mn0 tm1 ty1 = do
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
              -- named-field projection on single-constructor data
              -- (§10.2), or on a §7.4.1 flow-refined subset of the
              -- constructors when the receiver is a refined variable
              case Map.lookup headG (csDatas st) of
                Just di
                  | ctors <- projectableCtors ctx di
                  , not (null ctors)
                  , Just alts0 <-
                      sequence
                        [ do
                            ci <- Map.lookup ctorG (csCtors st)
                            idx <- elemIndex (Just (nameText mn0)) (map fst (ciFields ci))
                            Just (ctorG, ci, idx)
                        | ctorG <- ctors
                        ] -> do
                      fty <- do
                        let (ctorG, ci, idx) = head alts0
                        fieldTys <- ctorFieldTypes ctx ctorG ci t (nameSpanOf member)
                        case drop idx fieldTys of
                          (x : _) -> pure x
                          [] -> freshMetaV ctx
                      let altOf (ctorG, ci, idx) =
                            let arity = length (ciFields ci)
                                pats = [if i == idx then CPVar "__field" else CPWild | i <- [0 .. arity - 1]]
                             in CaseAlt (CPCtor ctorG pats) Nothing (CVar 0)
                      pure (CMatch tm1 (map altOf alts0), fty)
                _ -> methodSugar tm1 t mn0
        _ -> methodSugar tm1 t mn0

    -- method-call sugar (§7.4): recv.name args → name recv (receiver
    -- insertion at the first explicit binder).
    methodSugar recvTm recvTy mn0 = do
      mg <- lookupGlobalName (nameText mn0)
      case mg of
        Just g -> do
          st <- get
          mt <- globalTerm g
          case (Map.lookup g (csProjections st), mt) of
            -- receiver-projection sugar (§7.4): the receiver place
            -- supplies the unique place binder
            (Just pj, Just (dTm, dTy))
              | [pn] <- pjPlaceNames pj
              , pjIsPlace pj == [True] ->
                  applyDescriptor ctx (nameSpanOf member) dTm dTy (RootsSeparate [(pn, e)])
            (_, Just (fTm, fTy)) -> applyRecv fTm fTy recvTm recvTy
            (_, Nothing) -> failMember recvTy mn0
        Nothing -> failMember recvTy mn0

    applyRecv fTm fTy0 recvTm recvTy = do
      fTy <- forceM fTy0
      case fTy of
        VPi Impl q _ dom clo -> do
          iTm <- resolveImplicitQ ctx (nameSpanOf member) q dom
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

    -- which constructors a field projection may assume (§10.2 single
    -- constructor, or the §7.4.1 flow-refined subset for a refined
    -- variable receiver)
    projectableCtors c di
      | [ctorG] <- diCtors di = [ctorG]
      | EVar n <- e
      , Just gs <- ctxRefinementOf c (nameText n)
      , not (null gs)
      , all (`elem` diCtors di) gs =
          gs
      | otherwise = []

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

-- Elvis `l ?: r` (§16.1.2): unwrap an Option left operand, with the
-- right operand as the None fallback.
elabElvis :: Ctx -> Expr -> Expr -> Span -> CheckM (Term, Value)
elabElvis ctx l r sp = do
  (lTm, lTy) <- infer ctx l
  (lTm1, lTy1) <- insertAllImplicits ctx (exprSpan l) lTm lTy
  t <- forceM lTy1
  case t of
    VGlobN (GName _ "Option") [(_, payloadTy)] -> do
      rTm <- check ctx r payloadTy
      let alts =
            [ CaseAlt (CPCtor (gPrel "Some") [CPVar "__elvis"]) Nothing (CVar 0)
            , CaseAlt (CPCtor (gPrel "None") []) Nothing rTm
            ]
      pure (CMatch lTm1 alts, payloadTy)
    _ -> do
      lT <- quoteIn ctx t
      report $
        withNote ("left operand type: " <> renderTerm lT) $
          diag SevError StageElaborate "E_TYPE_EQUALITY_MISMATCH" (Just "kappa.type.mismatch") sp
            "the left operand of the Elvis operator '?:' must have type Option T (§16.1.2)"
      _ <- check ctx r t
      pure (lTm1, t)

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
          errAt (memberSpan member) "E_SAFE_NAVIGATION_AMBIGUOUS" (Just "kappa.type.mismatch")
            "the result type of '?.' is undetermined; annotate the member type (§16.1.1.2)"
          pure (bodyTm, bodyT)
        u -> pure (CCtor (gPrel "Some") [bodyTm], u)
      let alts =
            [ CaseAlt (CPCtor (gPrel "Some") [CPVar "__nav"]) Nothing wrapTm
            , CaseAlt (CPCtor (gPrel "None") []) Nothing (CCtor (gPrel "None") [])
            ]
      pure (CMatch pTm1 alts, VGlobN (gPrel "Option") [(Expl, resTy)])
    VFlex {} -> do
      errAt (exprSpan e) "E_SAFE_NAVIGATION_AMBIGUOUS" (Just "kappa.type.mismatch")
        "the receiver type of '?.' is undetermined here, so the navigation is ambiguous; annotate the receiver (§16.1.1.2)"
      anyHole ctx
    _ -> do
      errAt (exprSpan e) "E_SAFE_NAVIGATION_RECEIVER_NOT_OPTION" (Just "kappa.type.mismatch")
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

-- record patch (§13.2.5): closed records, '='-updates and ':='-extends.
elabPatch :: Ctx -> Expr -> [PatchItem] -> Span -> CheckM (Term, Value)
elabPatch = elabPatchWith False

-- @nested@ selects the §13.2.5 path diagnostic for unknown fields.
elabPatchWith :: Bool -> Ctx -> Expr -> [PatchItem] -> Span -> CheckM (Term, Value)
elabPatchWith _ ctx e [PatchSection recv rhs] sp = elabSectionUpdate ctx e recv rhs sp
elabPatchWith nested ctx e items sp = do
  (tm, ty) <- infer ctx e
  (tm1, ty1) <- insertAllImplicits ctx (exprSpan e) tm ty
  t <- forceM ty1
  case t of
    VRecordT fs -> do
      let updateNames = [nameText n | PatchUpdate [(False, n)] _ <- items]
          extendNames = [nameText n | PatchExtend n _ <- items]
          -- nested paths (§13.2.5): group by head segment
          nestedHeads =
            foldr (\n acc -> if nameText n `elem` map nameText acc then acc else n : acc) []
              [h | PatchUpdate ((False, h) : _ : _) _ <- items]
      forM_ (duplicatesOf updateNames) $ \n ->
        errAt sp "E_RECORD_PATCH_DUPLICATE_PATH" (Just "kappa.record.patch-duplicate")
          ("record patch updates field '" <> n <> "' more than once (§13.2.5)")
      forM_ (duplicatesOf extendNames) $ \n ->
        errAt sp "E_ROW_EXTENSION_DUPLICATE_LABEL" (Just "kappa.row.extension-duplicate")
          ("row extension introduces label '" <> n <> "' more than once (§13.2.6)")
      forM_ [h | h <- nestedHeads, nameText h `elem` updateNames] $ \h ->
        errAt (nameSpan h) "E_RECORD_PATCH_PREFIX_CONFLICT" (Just "kappa.record.patch-prefix-conflict")
          ("record patch both replaces '" <> nameText h <> "' and updates a path beneath it (§13.2.5)")
      groupUps <- forM nestedHeads $ \h -> do
        let subItems =
              [ PatchUpdate restPath v
              | PatchUpdate ((False, h0) : restPath@(_ : _)) v <- items
              , nameText h0 == nameText h
              ]
        if nameText h `elem` map fst fs
          then do
            (htm, _) <- elabPatchWith True ctx (EDot e (DotName h)) subItems sp
            pure (Just (nameText h, htm, Nothing))
          else do
            errAt (nameSpan h) "E_RECORD_PATCH_UNKNOWN_PATH" (Just "kappa.record.patch-unknown-path")
              ("record patch path starts at unknown field '" <> nameText h <> "' (§13.2.5)")
            pure Nothing
      results0 <- forM items $ \case
        PatchUpdate [(False, n)] (PatchValue v) -> do
          case lookup (nameText n) fs of
            Just fty -> do
              vt <- check ctx v fty
              pure (Just (nameText n, vt, Nothing))
            Nothing -> do
              if nested
                then
                  errAt (nameSpan n) "E_RECORD_PATCH_UNKNOWN_PATH" (Just "kappa.record.patch-unknown-path")
                    ("record patch path names unknown field '" <> nameText n <> "' (§13.2.5)")
                else
                  errAt (nameSpan n) "E_UNKNOWN_FIELD" (Just "kappa.record.unknown-field")
                    ("record has no field '" <> nameText n <> "'")
              pure Nothing
        PatchUpdate ((False, _) : _ : _) _ -> pure Nothing -- grouped above
        PatchUpdate _ _ -> do
          errAt sp "E_UNSUPPORTED" Nothing "implicit patch paths are not supported by this implementation"
          pure Nothing
        -- §13.2.6 row extension: the label must be absent; the result
        -- row gains the field
        PatchExtend n v ->
          case lookup (nameText n) fs of
            Just fty -> do
              errAt (nameSpan n) "E_ROW_EXTENSION_EXISTING_FIELD" (Just "kappa.row.extension-existing")
                ("row extension ':=' introduces '" <> nameText n <> "', but the record already has that field (§13.2.6)")
              vt <- check ctx v fty
              pure (Just (nameText n, vt, Nothing))
            Nothing -> do
              (vt0, vty0) <- infer ctx v
              (vt, vty) <- insertAllImplicits ctx (exprSpan v) vt0 vty0
              pure (Just (nameText n, vt, Just vty))
        PatchSection _ _ -> do
          -- a projection-section item mixed with other patch items
          errAt sp "E_PROJECTION_UPDATE_TARGET_UNSUPPORTED" (Just "kappa.projection.update")
            "a projection-section update must be the only item of its update (§13.2.5, §30.2.2.4)"
          pure Nothing
      let entries = catMaybes (results0 ++ groupUps)
          ups = [(n, vt) | (n, vt, _) <- entries]
          news =
            foldl
              (\acc p -> if fst p `elem` map fst acc then acc else acc ++ [p])
              []
              [(n, (vt, vty)) | (n, vt, Just vty) <- entries, n `notElem` map fst fs]
          allTypes = sortOn fst (fs ++ [(n, vty) | (n, (_, vty)) <- news])
          fields =
            [ ( n
              , fromMaybe
                  (maybe (CProj tm1 n) fst (lookup n news))
                  (lookup n ups)
              )
            | (n, _) <- allTypes
            ]
      pure (CRecordV fields, VRecordT allTypes)
    _ -> do
      errAt sp "E_TYPE_EQUALITY_MISMATCH" (Just "kappa.type.mismatch") "record patch requires a closed record"
      anyHole ctx

-- | Projection-section update @lhs.{ (.member args) = rhs }@
-- (§13.2.5, §30.2.2.4): the member must resolve to a stable field, a
-- single-leaf selector projection, or an accessor bundle providing
-- @set@; the update rebuilds the root.
elabSectionUpdate :: Ctx -> Expr -> Expr -> Expr -> Span -> CheckM (Term, Value)
elabSectionUpdate ctx baseE recv rhs sp = case recv of
  EReceiverSection (DotName mn : _) sArgs _ -> do
    (baseTm, baseTy0) <- infer ctx baseE
    baseTy <- forceM baseTy0
    mg <- lookupGlobalName (nameText mn)
    st <- get
    let mpj = (\g -> (,) g <$> Map.lookup g (csProjections st)) =<< mg
    case (baseTy, mpj) of
      -- a plain stable field: FillPlace, i.e. the ordinary update
      (VRecordT fs, _)
        | nameText mn `elem` map fst fs, null sArgs ->
            elabPatchWith False ctx baseE [PatchUpdate [(False, mn)] (PatchValue rhs)] sp
      (_, Just (g, pj))
        | pjSelector pj ->
            case (sArgs, nub (pjYields pj)) of
              -- unique static leaf: FillProjector ≡ nested field update
              ([], [(_, path@(_ : _))]) ->
                elabPatchWith False ctx baseE
                  [PatchUpdate [(False, Name seg (nameSpan mn)) | seg <- path] (PatchValue rhs)] sp
              -- whole-root leaf: filling replaces the root
              ([], [(_, [])]) -> do
                rhsTm <- check ctx rhs baseTy
                pure (rhsTm, baseTy)
              _ -> unsupportedTarget (baseTm, baseTy)
        | otherwise -> do
            mt <- globalTerm g
            case mt of
              Nothing -> unsupportedTarget (baseTm, baseTy)
              Just (dTm, dTy) -> do
                (dTm1, dTy1) <- elabSpine ctx sp dTm dTy sArgs
                dTyF <- forceM dTy1
                mcaps <- case dTyF of
                  VRecordT capFs -> bundleCapsM capFs
                  _ -> pure Nothing
                case [(r, f) | ("set", r, f) <- fromMaybe [] mcaps] of
                  ((rootsV, focusV) : _) -> do
                    rootsF <- forceM rootsV
                    case rootsF of
                      VRecordT [(_, sV)] -> expectType ctx (exprSpan baseE) baseTy sV
                      _ -> pure ()
                    rhsTm <- check ctx rhs focusV
                    pure (CApp Expl (CApp Expl (CProj dTm1 "set") baseTm) rhsTm, baseTy)
                  [] -> unsupportedTarget (baseTm, baseTy)
      _ -> unsupportedTarget (baseTm, baseTy)
  _ -> do
    (baseTm, baseTy) <- infer ctx baseE
    unsupportedTarget (baseTm, baseTy)
  where
    unsupportedTarget (baseTm, baseTy) = do
      errAt sp "E_PROJECTION_UPDATE_TARGET_UNSUPPORTED" (Just "kappa.projection.update")
        "the projection-section update target must resolve to a stable place, a selector projection, or an accessor bundle providing 'set' (§13.2.5, §30.2.2.4)"
      pure (baseTm, baseTy)

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
elabLambda ctx0 bs0 body sp mexpected =
  -- the lambda is a closure boundary: borrowed implicit locals from
  -- the surrounding scope may not be captured into it (§16.3.3)
  go (pushCtxBarrier ctx0) bs0 mexpected
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
        Nothing -> do
          -- trailing implicits resolve against the let-local implicit
          -- context, not the caller's (§16.3.3)
          (tm, ty) <- infer ctx body
          insertAllImplicits ctx (exprSpan body) tm ty
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
              ctx0' = bindCtxLet (nameText n) implocal rhsTy rhsV ctx
              ctx1 = if implocal then setTopPrefix prefix ctx0' else ctx0'
              -- §7.4.3 stable alias: `let q = p` transports refinement
              ctx' = case rhs of
                EVar pn | Just _ <- lookupCtx (nameText pn) ctx ->
                  addCtxAlias (nameText n) (nameText pn) ctx1
                _ -> ctx1
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
      DLet _ (LetDef (Just n) _ Nothing _ [] mty Nothing rhs) _ ->
        (LetBind False emptyPrefix (PVar n) (annOf n mty sigs) rhs sp :) <$> goDecls sigs rest
      DLet _ (LetDef (Just n) _ Nothing _ bs mty _ rhs) dsp -> do
        -- local named function: elaborate as lambda
        let lam = ELambda Nothing bs (maybe rhs (\t -> EAscription rhs t dsp) mty) dsp
        (LetBind False emptyPrefix (PVar n) (lookup (nameText n) sigs) lam sp :) <$> goDecls sigs rest
      DLet _ (LetDef Nothing imp (Just p) prefix [] mty Nothing rhs) _ ->
        (LetBind imp prefix p mty rhs sp :) <$> goDecls sigs rest
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
checkIf ctx alts mels sp resT = go ctx alts
  where
    boolT = VGlobN (gPrel "Bool") []
    go c [] = case mels of
      Just e -> check c e resT
      Nothing -> do
        errAt sp "E_IF_MISSING_ELSE" (Just "kappa.control.if-missing-else")
          "if without else is only permitted as a do-block statement (§16.4, §18.4)"
        pure (CCtor (gPrel "Unit") [])
    go c ((cnd, t) : rest) = do
      -- §7.4.1 flow refinement: constructor tests in the condition
      -- refine their subjects in the condition's own conjuncts and in
      -- the then-branch
      refs <- condRefines c cnd
      let ctxR = refineCtx refs c
      cTm <- check ctxR cnd boolT
      tTm <- check ctxR t resT
      -- the negative side refines the subject to the complementary
      -- constructors of its data type (§7.4.1 lacks-refinement); only
      -- a bare `x is C` condition licenses the complement
      negs <- case cnd of
        EIs (EVar _) _ -> complementRefines refs
        _ -> pure []
      eTm <- go (refineCtx negs c) rest
      pure (CIf cTm tTm eTm)
    -- only a whole-condition single `x is C` test yields a usable
    -- complement (a failed conjunction proves nothing positive), and
    -- only a UNIQUE residual constructor is a usable fact: a wider
    -- residual would invent a positive fact the test never proved
    complementRefines refs = fmap concat . forM refs $ \(x, gs) -> do
      st <- get
      case nub [ciData ci | g <- gs, Just ci <- [Map.lookup g (csCtors st)]] of
        [dataG]
          | Just di <- Map.lookup dataG (csDatas st)
          , [residual] <- [cg | cg <- diCtors di, cg `notElem` gs] ->
              pure [(x, [residual])]
        _ -> pure []

-- | §7.4.1/§7.4.2 refinements induced by an if-condition: `x is C`
-- refines x to {C}; conjunction collects both sides; disjunction
-- refines a subject to the union of constructors when both sides
-- refine it.
condRefines :: Ctx -> Expr -> CheckM [(Text, [GName])]
condRefines _ctx = go
  where
    go = \case
      EIs (EVar n) cref -> do
        mg <- quietCtor cref
        pure [(nameText n, [g]) | Just g <- [mg]]
      EApp (EVar (Name op _)) [ArgExplicit l, ArgExplicit r]
        | op == "&&" -> (++) <$> go l <*> go r
        | op == "||" -> do
            ls <- go l
            rs <- go r
            pure [(x, gs ++ gs') | (x, gs) <- ls, (x', gs') <- rs, x == x']
      EThunk e _ -> go e
      _ -> pure []
    quietCtor (CtorRef mqual n) = do
      st <- get
      let inScope g@(GName m _) =
            m == csModule st || Map.lookup (gnameText g) (csScope st) == Just g || m == preludeModule
          cands = case mqual of
            Nothing ->
              [g | (g, _) <- Map.toList (csCtors st), gnameText g == nameText n, inScope g]
            Just q ->
              [ ctorG
              | (dg, di) <- Map.toList (csDatas st)
              , gnameText dg == nameText q
              , inScope dg
              , ctorG <- diCtors di
              , gnameText ctorG == nameText n
              ]
      pure (case cands of (g : _) -> Just g; [] -> Nothing)

checkMatch :: Ctx -> Expr -> [MatchCase] -> Span -> Value -> CheckM Term
checkMatch ctx scrut cases sp resT = do
  hasAp <- or <$> mapM caseUsesActive cases
  if hasAp
    then do
      lowered <- lowerActiveMatch ctx scrut cases sp
      check ctx lowered resT
    else checkMatchPlain ctx scrut cases sp resT
  where
    caseUsesActive = \case
      MatchCase pat _ _ _ -> patUsesActive pat
      MatchImpossible _ -> pure False
    patUsesActive pat = case pat of
      PCtor cref ps _ | not (null ps) -> do
        mc <- peekCtor ctx cref
        case mc of
          Just _ -> pure False
          Nothing -> do
            mAp <- lookupActivePattern cref
            case mAp of
              Just _ -> pure True
              Nothing -> isJust <$> lookupGlobalName (nameText (crName cref))
      PActive {} -> pure True
      _ -> pure False

-- | 'resolveCtor' without the unresolved-constructor diagnostic: used
-- while classifying possible active-pattern heads (§17.3.2).
peekCtor :: Ctx -> CtorRef -> CheckM (Maybe (GName, CtorInfo))
peekCtor ctx cref = do
  st0 <- get
  r <- resolveCtor ctx cref
  case r of
    Just _ -> pure r
    Nothing -> put st0 >> pure Nothing

-- | Find an active pattern by (unqualified) head name; same-module
-- definitions take precedence over imported ones (§17.3).
lookupActivePattern :: CtorRef -> CheckM (Maybe APInfo)
lookupActivePattern (CtorRef _ n) = do
  st <- get
  let nm = nameText n
      cands = [(g, i) | (g, i) <- Map.toList (csActive st), gnameText g == nm]
      own = [i | (GName m _, i) <- cands, m == csModule st]
  pure $ case own ++ map snd cands of
    (i : _) -> Just i
    [] -> Nothing

-- | Lower a match containing active-pattern cases (§17.3.2) into
-- nested matches over the pattern functions' results: Option results
-- test Some/None, Match results thread the Miss residue into the
-- remaining cases, and total view results match the view value
-- directly (consecutive cases with the same head share one view
-- match, preserving exhaustiveness over the view type).
lowerActiveMatch :: Ctx -> Expr -> [MatchCase] -> Span -> CheckM Expr
lowerActiveMatch ctx scrut cases sp = case scrut of
  EVar _ -> goCases scrut cases
  _ -> do
    sv <- freshNameM "__apscrut"
    let svn = Name sv sp
    inner <- goCases (EVar svn) cases
    pure (ELet [LetBind False emptyPrefix (PVar svn) Nothing scrut sp] inner sp)
  where
    goCases se cs = do
      classified <- mapM classify cs
      build se classified
    classify c@(MatchImpossible _) = pure (CPlain c)
    classify c@(MatchCase pat mguard body csp) = case pat of
      PCtor cref ps _ | not (null ps) -> do
        mc <- peekCtor ctx cref
        case mc of
          Just _ -> pure (CPlain c)
          Nothing -> do
            mAp <- lookupActivePattern cref
            case mAp of
              Just info -> case mapM activePatArgExpr (init ps) of
                Just args -> pure (CActive (crName cref) info args (last ps) mguard body csp)
                Nothing -> do
                  errAt csp "E_UNSUPPORTED" Nothing "this active-pattern argument form is not supported by this implementation"
                  pure (CBad csp)
              Nothing -> do
                mg <- lookupGlobalName (nameText (crName cref))
                case mg of
                  Just _ -> do
                    errAt csp "E_PATTERN_HEAD_NOT_CONSTRUCTOR_OR_ACTIVE_PATTERN" (Just "kappa.pattern.head")
                      ("'" <> nameText (crName cref)
                         <> "' is neither a constructor nor an active pattern, so it cannot head a pattern (§17.3.2)")
                    pure (CBad csp)
                  Nothing -> pure (CPlain c)
      PActive cref args vp psp -> do
        mAp <- lookupActivePattern cref
        case mAp of
          Just info -> pure (CActive (crName cref) info args vp mguard body psp)
          Nothing -> do
            errAt psp "E_PATTERN_HEAD_NOT_CONSTRUCTOR_OR_ACTIVE_PATTERN" (Just "kappa.pattern.head")
              ("'" <> nameText (crName cref) <> "' is not an active pattern (§17.3.2)")
            pure (CBad psp)
      _ -> pure (CPlain c)
    apApp n args se = EApp (EVar n) (map ArgExplicit (args ++ [se]))
    pcon nm ps = PCtor (CtorRef Nothing (Name nm sp)) ps sp

    build se classified = case classified of
      [] -> pure (EMatch se [] sp)
      (CBad _ : rest) -> build se rest
      (CPlain _ : _) -> do
        let (plains, rest) = span isPlain classified
            plainCases = [c | CPlain c <- plains]
        if null rest
          then pure (EMatch se plainCases sp)
          else do
            r <- freshNameM "__apk"
            let rn = Name r sp
            inner <- build (EVar rn) rest
            pure (EMatch se (plainCases ++ [MatchCase (PVar rn) Nothing inner sp]) sp)
      (CActive n info args vp mguard body csp : rest) -> case apResult info of
        APOption -> do
          inner <- build se rest
          pure $
            EMatch (apApp n args se)
              [ MatchCase (pcon "Some" [vp]) mguard body csp
              , MatchCase (PWild sp) Nothing inner sp
              ]
              sp
        APMatch -> do
          r <- freshNameM "__apresid"
          let rn = Name r sp
          inner <- build (EVar rn) rest
          pure $
            EMatch (apApp n args se)
              [ MatchCase (pcon "Hit" [vp]) mguard body csp
              , MatchCase (pcon "Miss" [PVar rn]) Nothing inner sp
              ]
              sp
        APTotal -> do
          let sameHead = \case
                CActive n2 i2 _ _ _ _ _ -> nameText n2 == nameText n && apResult i2 == APTotal
                _ -> False
              (run, rest') = span sameHead (CActive n info args vp mguard body csp : rest)
              viewCases = [MatchCase vp' g' b' c' | CActive _ _ _ vp' g' b' c' <- run]
          extra <-
            if null rest'
              then pure []
              else do
                inner <- build se rest'
                pure [MatchCase (PWild sp) Nothing inner sp]
          pure (EMatch (apApp n args se) (viewCases ++ extra) sp)
      where
        isPlain = \case
          CPlain _ -> True
          _ -> False

-- | One classified match case during active-pattern lowering.
data CaseClass
  = CPlain !MatchCase
  | CActive !Name !APInfo ![Expr] !Pattern !(Maybe Expr) !Expr !Span
  | CBad !Span

-- | Rewrite @let? P args (vp) = e@ over an active pattern P into the
-- corresponding match on @P args e@ (§17.3.2). A Match-result pattern
-- threads a residue, which a plain @let?@ cannot receive.
rewriteActiveLetQ :: Ctx -> Pattern -> Expr -> Span -> CheckM (Pattern, Expr)
rewriteActiveLetQ ctx pat rhs dsp = case pat of
  PCtor cref ps psp | not (null ps) -> do
    mc <- peekCtor ctx cref
    case mc of
      Just _ -> pure (pat, rhs)
      Nothing -> do
        mAp <- lookupActivePattern cref
        case mAp of
          Nothing -> pure (pat, rhs)
          Just info -> case mapM activePatArgExpr (init ps) of
            Nothing -> pure (pat, rhs)
            Just args -> do
              let app = EApp (EVar (crName cref)) (map ArgExplicit (args ++ [rhs]))
                  vp = last ps
              case apResult info of
                APOption -> pure (PCtor (CtorRef Nothing (Name "Some" psp)) [vp] psp, app)
                APMatch -> do
                  errAt dsp "E_ACTIVE_PATTERN_MATCH_RESULT_NOT_ALLOWED_IN_PLAIN_LET_QUESTION"
                    (Just "kappa.pattern.active")
                    "a Match-result active pattern threads a residue on a miss and may not be used in a plain 'let?'; use a match with a residue case instead (§17.3.2)"
                  pure (PCtor (CtorRef Nothing (Name "Hit" psp)) [vp] psp, app)
                APTotal -> pure (vp, app)
  _ -> pure (pat, rhs)

-- | Convert an active-pattern argument (written in pattern position)
-- to the expression it denotes (§17.3.2).
activePatArgExpr :: Pattern -> Maybe Expr
activePatArgExpr = \case
  PLit (LInt v msuf) psp -> Just (EIntLit v ((`Name` psp) <$> msuf) psp)
  PLit (LFloat v msuf) psp -> Just (EFloatLit v ((`Name` psp) <$> msuf) psp)
  PVar n -> Just (EVar n)
  _ -> Nothing

checkMatchPlain :: Ctx -> Expr -> [MatchCase] -> Span -> Value -> CheckM Term
checkMatchPlain ctx scrut cases sp resT = do
  (sTm, sTy) <- infer ctx scrut
  (sTm1, sTy1) <- insertAllImplicits ctx (exprSpan scrut) sTm sTy
  -- a variable scrutinee yields branch-local rigid facts: the matched
  -- nullary constructor on the success side, the lacks-set on later
  -- cases (dependent-match normalization, §7.4.1)
  let mLvl = case scrut of
        EVar n -> case lookupCtx (nameText n) ctx of
          Just (i, _) -> case drop i (ctxEnv ctx) of
            (VRigid l [] : _) -> Just l
            _ -> Nothing
          Nothing -> Nothing
        _ -> Nothing
      goCase (accAlts, prior) c = case c of
        MatchImpossible isp -> do
          empty <- scrutineeEmpty sTy1
          unless empty $
            errAt isp "E_INDEXED_IMPOSSIBLE_REACHABLE" (Just "kappa.match.impossible-reachable")
              "'case impossible' requires the remaining scrutinee type to be uninhabited (§17.1.5)"
          pure (accAlts, prior)
        MatchCase pat mguard body _ -> do
          (patC, ctx', _) <- elabPattern ctx pat sTy1
          let fact = case patC of
                CPCtor g [] -> Just (FactIs (VCtor g []))
                _ | not (null prior) -> Just (FactNot prior)
                _ -> Nothing
          oldFacts <- gets csFacts
          forM_ ((,) <$> mLvl <*> fact) $ \(l, f) ->
            modify' $ \st -> st {csFacts = Map.insert l f (csFacts st)}
          gTm <- traverse (\g -> check ctx' g (VGlobN (gPrel "Bool") [])) mguard
          bTm <- check ctx' body resT
          modify' $ \st -> st {csFacts = oldFacts}
          let prior' = prior ++ [g | CPCtor g _ <- [patC]]
          pure (accAlts ++ [CaseAlt patC gTm bTm], prior')
  (alts, _) <- foldM goCase ([], []) cases
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
isWildLike :: CheckState -> CorePat -> Bool
isWildLike st = \case
  CPWild -> True
  CPVar _ -> True
  CPRecord {} -> True -- over-approximation
  CPInject {} -> True -- nested variant injections: over-approximation
  CPInjectRest _ -> True
  -- an arity-mismatched constructor pattern was already diagnosed;
  -- do not cascade a non-exhaustiveness report
  CPCtor c ps -> length ps /= ctorArity st c
  _ -> False

patKey :: CheckState -> CorePat -> Maybe (PatKey, Int)
patKey st = \case
  CPCtor c ps | length ps == ctorArity st c -> Just (KCtor c, length ps)
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
    spec [] = Nothing
    spec (p : ps)
      | isWildLike st p = Just (replicate a CPWild ++ ps)
      | Just (k', _) <- patKey st p, k' == k = Just (subPats p ++ ps)
      | otherwise = Nothing

defaultRows :: CheckState -> [[CorePat]] -> [[CorePat]]
defaultRows st rows =
  [ ps
  | row0 <- rows
  , (p : ps) <- expandRow row0
  , isWildLike st p
  ]

-- is the all-wildcard row of width n useful w.r.t. the matrix?
wildUseful :: CheckState -> [[CorePat]] -> Int -> Bool
wildUseful _ rows 0 = null rows
wildUseful st rows n =
  let firsts = [p | row0 <- rows, (p : _) <- expandRow row0]
      keys = nub (mapMaybe (patKey st) firsts)
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
        else wildUseful st (defaultRows st rows) (n - 1)

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
                errAt sp "E_OR_PATTERN_BINDER_MISMATCH" (Just "kappa.pattern.or-bindings")
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
  me <- traverse forceM mexpected
  (errT, resT, doTy) <- case me of
    Just (VGlobN (GName _ "IO") [(_, e), (_, a)]) ->
      pure (e, a, Nothing)
    -- an STM-typed do sequences IO-shaped items (§18.1.13); the kernel
    -- runs it as the underlying action
    Just expd@(VGlobN (GName _ "STM") [(_, a)]) -> do
      e <- freshMetaV ctx
      pure (e, a, Just expd)
    -- pure-result do (corpus): a do block in a position expecting a
    -- known non-IO type sequences pure statements; the §18.8 kernel
    -- passes pure statement values through, so it runs unchanged
    Just expd | not (isFlexHead expd) -> do
      e <- freshMetaV ctx
      pure (e, expd, Just expd)
    _ -> do
      e <- freshMetaV ctx
      a <- freshMetaV ctx
      pure (e, a, Nothing)
  kitems <- goItems [] ctx errT resT items
  pure (CDo kitems, fromMaybe (ioType errT resT) doTy)
  where
    goItems :: [Maybe Text] -> Ctx -> Value -> Value -> [DoItem] -> CheckM [KItem]
    goItems _ _ _ _ [] = pure []
    goItems loops c errT resT (item : rest) = do
      let lastItem = null rest
      case item of
        DoExpr e -> do
          aT <- if lastItem then pure resT else freshMetaV c
          let eD = desugarBang e
              ioT = ioType errT aT
          -- statements are IO actions (§18.2); the corpus also
          -- sequences pure expressions as statements, and the §18.8
          -- kernel passes pure statement values through unchanged, so
          -- an inferable statement may also check at the bare type
          tm <- case eD of
            _ | statementInferable eD -> do
                  (tm0, ty0) <- infer c eD
                  (tm1, ty1) <- insertAllImplicits c (exprSpan eD) tm0 ty0
                  okIO <- unify c ty1 ioT
                  if okIO
                    then pure tm1
                    else do
                      okPure <- unify c ty1 aT
                      okDiscard <-
                        if okPure
                          then pure True
                          else do
                            -- a final action of unit-result do-scopes
                            -- may have a non-unit result; it is
                            -- discarded (corpus accommodation)
                            isUnit <-
                              forceM aT >>= \case
                                VGlobN (GName _ "Unit") [] -> pure True
                                _ -> pure False
                            if isUnit
                              then do
                                b <- freshMetaV c
                                unify c ty1 (ioType errT b)
                              else pure False
                      unless okDiscard $ expectType c (exprSpan eD) ty1 ioT
                      pure tm1
            _ -> check c eD ioT
          (KExpr tm :) <$> goItems loops c errT resT rest
        DoBind (LetBind implocal prefix pat mty rhs bsp) -> do
          aT <- case mty of
            Just tyE -> do
              (tyTm, _) <- inferType c tyE
              evalIn c tyTm
            Nothing -> freshMetaV c
          let rhsD = desugarBang rhs
          st0 <- get
          n0 <- gets (length . csDiags)
          rhsTm0 <- check c rhsD (ioType errT aT)
          n1 <- gets (length . csDiags)
          rhsTm <-
            if n1 == n0
              then pure rhsTm0
              else do
                -- container bind (§18.3 accommodation): a do block in a
                -- non-IO container position binds through that container
                put st0
                (tm0, ty0) <- infer c rhsD
                (tm1, ty1) <- insertAllImplicits c bsp tm0 ty0
                ty1F <- forceM ty1
                case ty1F of
                  VGlobN (GName _ h) args
                    | h /= "IO"
                    , ((_, lastArg) : _) <- reverse args -> do
                        expectType c bsp lastArg aT
                        pure tm1
                  _ -> do
                    -- not container-shaped: restore the IO diagnosis
                    put st0
                    check c rhsD (ioType errT aT)
          checkIrrefutable c pat aT bsp
          (patC, cBound, _) <- elabPattern c pat aT
          let c' = markImplicitLocal implocal prefix c cBound
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
          let cBound' = case (pat, rhs) of
                -- §7.4.3 stable alias: `let q = p` transports refinement
                (PVar qn, EVar pn)
                  | Just _ <- lookupCtx (nameText pn) c ->
                      addCtxAlias (nameText qn) (nameText pn) cBound
                _ -> cBound
          let c' = markImplicitLocal implocal prefix c cBound'
          ks <- goItems loops c' errT resT rest
          pure (KLet (qOf (bpQuantity prefix)) patC rhsTm : ks)
        DoLetQ pat0 rhs0 mElse dsp -> do
          (pat, rhs) <- rewriteActiveLetQ c pat0 rhs0 dsp
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
        DoUsing pat rhs usp ->
          -- §19.5 resource bind: typed like a monadic bind of the
          -- acquired resource (the scope-exit release action is not
          -- modelled by this kernel; the binding is borrowed for the
          -- §12.3 usage analysis, which inspects the surface item)
          goItems loops c errT resT
            (DoBind (LetBind False emptyPrefix pat Nothing rhs usp) : rest)
        DoDecl d -> do
          case d of
            DLet _ (LetDef (Just n) _ Nothing _ [] mty Nothing rhs) dsp ->
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

-- | Is the (forced) value headed by an unsolved metavariable?
isFlexHead :: Value -> Bool
isFlexHead = \case
  VFlex {} -> True
  _ -> False

-- | Statement shapes that elaborate soundly by inference, allowing the
-- pure-statement accommodation in 'elabDo' (variants, literals and other
-- expected-type-directed forms keep the plain IO checking path).
statementInferable :: Expr -> Bool
statementInferable = \case
  EApp f _ -> statementInferable f
  EVar {} -> True
  EDot {} -> True
  EQDot {} -> True
  EOpChain {} -> True
  EIf {} -> True
  EMatch {} -> True
  EUnit {} -> True
  ETuple {} -> True
  EIntLit {} -> True
  EFloatLit {} -> True
  EStringLit {} -> True
  _ -> False

-- | §16.3.3: an implicit do-binding @let (\@x : T) = e@ joins the local
-- implicit context for the remaining items. @before@ is the context the
-- pattern was elaborated in; the entries added on top of it are marked.
markImplicitLocal :: Bool -> BinderPrefix -> Ctx -> Ctx -> Ctx
markImplicitLocal False _ _ after = after
markImplicitLocal True (BinderPrefix mq mb) before after =
  let es = ctxEntries after
      (new, old) = splitAt (length es - ctxLen before) es
      mark e = e {ceImplicitLocal = True, ceQ = mq, ceBorrow = isJust mb}
   in after {ctxEntries = map mark new ++ old}

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

-- ── Comprehensions (§20) ─────────────────────────────────────────────
--
-- Lowered per the §20.10 normative algebra, realized directly over
-- lists (the §20.10.11 as-if rule). A first pass infers the plan
-- (source kinds, use mode, cardinality, orderedness, row-entry
-- quantities) against a state snapshot; a second pass desugars to
-- surface syntax and elaborates once.

-- | How a generator source is iterated (§20.10.2 built-in obligations).
data SrcKind = SKList | SKArray | SKSet | SKMap | SKOption | SKQuery | SKUnknown
  deriving stock (Eq, Show)

-- | Cardinality approximation (§20.10.1).
data QCard = CZero | COne | CZeroOrOne | COneOrMore | CZeroOrMore
  deriving stock (Eq, Show)

cardName :: QCard -> Text
cardName = \case
  CZero -> "QZero"
  COne -> "QOne"
  CZeroOrOne -> "QZeroOrOne"
  COneOrMore -> "QOneOrMore"
  CZeroOrMore -> "QZeroOrMore"

cardIv :: QCard -> (Int, Maybe Int)
cardIv = \case
  CZero -> (0, Just 0)
  COne -> (1, Just 1)
  CZeroOrOne -> (0, Just 1)
  COneOrMore -> (1, Nothing)
  CZeroOrMore -> (0, Nothing)

cardOf :: (Int, Maybe Int) -> QCard
cardOf = \case
  (0, Just 0) -> CZero
  (1, Just 1) -> COne
  (0, Just 1) -> CZeroOrOne
  (1, Nothing) -> COneOrMore
  _ -> CZeroOrMore

mulCard :: QCard -> QCard -> QCard
mulCard a b =
  let (al, ah) = cardIv a
      (bl, bh) = cardIv b
      hi = case (ah, bh) of
        (Just x, Just y) -> Just (min 1 (x * y))
        (Just 0, _) -> Just 0
        (_, Just 0) -> Just 0
        _ -> Nothing
   in cardOf (min 1 (al * bl), hi)

filterCard :: QCard -> QCard
filterCard c = let (_, h) = cardIv c in cardOf (0, h)

-- | May the inferred cardinality be checked against the demanded one
-- (interval subset, §20.10.1)?
cardSub :: QCard -> QCard -> Bool
cardSub a b =
  let (al, ah) = cardIv a
      (bl, bh) = cardIv b
      hiOk = case (ah, bh) of
        (_, Nothing) -> True
        (Just x, Just y) -> x <= y
        (Nothing, Just _) -> False
   in al >= bl && hiOk

cardManyHi :: QCard -> Bool
cardManyHi c = case snd (cardIv c) of
  Nothing -> True
  Just h -> h > 1

cardZeroLo :: QCard -> Bool
cardZeroLo c = fst (cardIv c) == 0

-- | What pass 1 learned about one generator source.
data SrcInfo = SrcInfo
  { siKind :: !SrcKind
  , siItem :: !Value
  , siOrdered :: !Bool
  , siOneShot :: !Bool
  , siCard :: !QCard
  , siItemLinear :: !Bool
  }

sourceInfo :: Ctx -> Value -> CheckM SrcInfo
sourceInfo ctx ty = do
  t <- forceM ty
  case t of
    VGlobN (GName _ "List") [(_, a)] -> pure (SrcInfo SKList a True False CZeroOrMore False)
    VGlobN (GName _ "Array") [(_, a)] -> pure (SrcInfo SKArray a True False CZeroOrMore False)
    VGlobN (GName _ "Set") [(_, a)] -> pure (SrcInfo SKSet a False False CZeroOrMore False)
    VGlobN (GName _ "Map") [(_, k), (_, v)] ->
      pure (SrcInfo SKMap (VRecordT [("key", k), ("value", v)]) False False CZeroOrMore False)
    VGlobN (GName _ "Option") [(_, a)] -> pure (SrcInfo SKOption a True False CZeroOrOne False)
    VGlobN (GName _ "QueryCore") [(_, m), (_, q), (_, a)] -> do
      (oneShot, card) <- decodeQueryMode m
      lin <- decodeLinearQuantity q
      pure (SrcInfo SKQuery a True oneShot card lin)
    _ -> do
      item <- freshMetaV ctx
      pure (SrcInfo SKUnknown item True False CZeroOrMore False)

decodeQueryMode :: Value -> CheckM (Bool, QCard)
decodeQueryMode m0 = do
  m <- forceM m0
  case m of
    VCtor (GName _ "QueryMode") [u0, c0] -> do
      u <- forceM u0
      c <- forceM c0
      let oneShot = case u of
            VCtor (GName _ "OneShot") _ -> True
            _ -> False
          card = case c of
            VCtor (GName _ "QZero") _ -> CZero
            VCtor (GName _ "QOne") _ -> COne
            VCtor (GName _ "QZeroOrOne") _ -> CZeroOrOne
            VCtor (GName _ "QOneOrMore") _ -> COneOrMore
            _ -> CZeroOrMore
      pure (oneShot, card)
    _ -> pure (False, CZeroOrMore)

-- | Is the quantity value the linear quantity @1@?
decodeLinearQuantity :: Value -> CheckM Bool
decodeLinearQuantity q0 = do
  q <- forceM q0
  pure $ case q of
    VPrim "__quantityOfNat" [VLit (LitInt 1)] -> True
    _ -> False

-- | Does the variable occur (syntactically) in the expression?
occursVar :: Text -> Expr -> Bool
occursVar v = go
  where
    go = \case
      EVar (Name n _) -> n == v
      EApp f as -> go f || any goA as
      EDot b _ -> go b
      EQDot b _ -> go b
      EOpChain els -> or [go x | ChainOperand x <- els]
      ETuple es _ -> any go es
      ERecordLit is _ -> or [go e | RecItem _ _ (Just e) <- is]
      ERecordPatch b items _ ->
        go b
          || or
            [ case it of
                PatchUpdate _ (PatchValue e) -> go e
                PatchExtend _ e -> go e
                PatchSection a e -> go a || go e
            | it <- items
            ]
      EListLit es _ -> any go es
      ESetLit es _ -> any go es
      EMapLit kvs _ -> any (\(k, w) -> go k || go w) kvs
      EIf alts mels _ -> any (\(c, t) -> go c || go t) alts || maybe False go mels
      EMatch s cs _ -> go s || or [maybe False go g || go b | MatchCase _ g b _ <- cs]
      ELambda _ _ b _ -> go b
      ELet bs b _ -> any (go . lbExpr) bs || go b
      EAscription e _ _ -> go e
      ESectionLeft e _ _ -> go e
      ESectionRight _ e _ -> go e
      EElvis a b _ -> go a || go b
      EIs e _ -> go e
      EThunk e _ -> go e
      ELazy e _ -> go e
      EForce e _ -> go e
      EBang e _ -> go e
      EStringLit _ parts _ -> any (go . ipExpr) parts
      EDo _ items _ -> any goItem items
      EComprehension _ cls yy _ ->
        any goClause cls || any go (yieldExprsOf yy)
      _ -> False
    goA = \case
      ArgExplicit e -> go e
      ArgImplicit e -> go e
      ArgInout e _ -> go e
      ArgNamedBlock fs _ -> or [maybe False go me | (_, me) <- fs]
    goItem = \case
      DoBind lb -> go (lbExpr lb)
      DoLet lb -> go (lbExpr lb)
      DoLetQ _ e mfb _ -> go e || maybe False (go . snd) mfb
      DoExpr e -> go e
      _ -> True -- conservative for loops/var/defer items
    goClause = \case
      S.CFor _ _ _ src _ -> go src
      S.CLet _ _ _ rhs _ -> go rhs
      S.CIf e -> go e
      S.COrderBy ks _ -> any (go . snd) ks
      S.CSkip e _ -> go e
      S.CTake e _ -> go e
      S.CDistinct me _ -> maybe False go me
      S.CGroupBy k aggs _ _ -> go k || or [go e || maybe False go mu | (_, e, mu) <- aggs]
      S.CJoin _ _ src cond _ _ -> go src || go cond

yieldExprsOf :: CompYield -> [Expr]
yieldExprsOf = \case
  YieldExpr e -> [e]
  YieldPair k v -> [k, v]

-- | Surface pattern variables, in binding order.
surfPatVars :: Pattern -> [Name]
surfPatVars = \case
  PWild _ -> []
  PVar n -> [n]
  PLit _ _ -> []
  PAs n p -> n : surfPatVars p
  PCtor _ ps _ -> concatMap surfPatVars ps
  PCtorNamed _ fs _ -> concatMap surfPatVars [p | (_, Just p) <- fs]
  PActive _ _ p _ -> surfPatVars p
  PTuple ps _ -> concatMap surfPatVars ps
  PUnit _ -> []
  PRecord fs mrest _ ->
    concatMap (\(_, n, mp) -> maybe [n] surfPatVars mp) fs
      ++ [n | Just (PatRestBind n) <- [mrest]]
  PTyped p _ _ -> surfPatVars p
  POr ps _ -> case ps of
    (p : _) -> surfPatVars p
    [] -> []
  POpChain p chain _ -> surfPatVars p ++ concatMap (surfPatVars . snd) chain
  PVariant mb _ _ mrest _ -> maybe [] pure mb ++ maybe [] pure mrest

-- | Per-clause pass-1 annotation consumed by the desugaring pass.
data CAnn = CAnn
  { caKind :: !SrcKind -- ^ generator/join source kind
  , caForceRefut :: !Bool -- ^ desugar with a wildcard fallback case
  }

defaultAnn :: CAnn
defaultAnn = CAnn SKUnknown False

-- | Pass-1 result: plan metadata plus pending diagnostics.
data CompPlan = CompPlan
  { cpAnns :: ![CAnn]
  , cpOneShot :: !Bool
  , cpCard :: !QCard
  , cpItemLinear :: !Bool
  , cpDiags :: ![(Span, Text, Maybe Text, Text)]
  }

-- | Pass 1: infer the comprehension plan. Elaboration side effects
-- (diagnostics, metas) are rolled back; only the plan survives.
planComp :: Ctx -> [S.CompClause] -> CompYield -> Span -> CheckM CompPlan
planComp ctx0 clauses yld _sp = do
  st0 <- get
  plan <- go ctx0 [] True False COne [] [] clauses
  put st0
  pure plan
  where
    linsOf row = [v | (v, True) <- row]
    directComponent v = goD
      where
        goD = \case
          EVar (Name n _) -> n == v
          ETuple es _ -> any goD es
          ERecordLit is _ -> or [goD e | RecItem _ _ (Just e) <- is]
          EAscription e _ _ -> goD e
          _ -> False
    pend csp code fam msg = (csp, code, fam, msg)
    dropMsg what vs csp =
      pend csp "E_QUERY_ROW_NOT_DROPPABLE" (Just "kappa.query.row-quantity")
        (what <> " may discard the current row, but linear row entry '"
           <> T.intercalate "', '" vs <> "' is not droppable (§20.10.4)")
    go _ctx row _ordered oneShot card anns diags [] = do
      -- the yielded item carries quantity 1 only when a linear row
      -- entry flows into it as a direct component (not when an
      -- application consumes the entry and yields its result)
      let lins = linsOf row
          itemLinear = not (null [v | v <- lins, any (directComponent v) (yieldExprsOf yld)])
      pure (CompPlan (reverse anns) oneShot card itemLinear (reverse diags))
    go ctx row ordered oneShot card anns diags (c : cs) = case c of
      S.CFor refut _ pat src csp -> do
        (_, srcTy) <- infer ctx src
        si <- sourceInfo ctx srcTy
        irr <- irrefutableFor ctx pat (siItem si)
        let lins = linsOf row
            refutD =
              [ pend csp "E_QUERY_FOR_REFUTABLE" (Just "kappa.query.refutable-for")
                  "the pattern of a 'for' clause must be irrefutable for the element type; use the refutable form 'for?' instead (§20.4)"
              | not refut && not irr
              ]
            dropD = [dropMsg "the refutable generator 'for?'" lins csp | refut, not (null lins)]
            dupD =
              [ pend csp "E_QUERY_ROW_NOT_DUPLICABLE" (Just "kappa.query.row-quantity")
                  ("a nested 'for' over a zero-or-many source may drop or duplicate the current row, but linear row entry '"
                     <> T.intercalate "', '" lins <> "' is neither droppable nor duplicable (§20.10.4)")
              | not refut
              , not (null lins)
              , cardManyHi (siCard si) || cardZeroLo (siCard si)
              ]
        (_, ctx', _) <- elabPattern ctx pat (siItem si)
        let row' = row ++ [(nameText n, siItemLinear si) | n <- surfPatVars pat]
        go ctx' row' (ordered && siOrdered si) (oneShot || siOneShot si)
          (mulCard card (siCard si))
          (CAnn (siKind si) (not irr) : anns)
          (reverse (refutD ++ dropD ++ dupD) ++ diags)
          cs
      S.CLet refut pat mty rhs csp -> do
        rhsTy <- case mty of
          Just tyE -> do
            (tyTm, _) <- inferType ctx tyE
            tyV <- evalIn ctx tyTm
            _ <- check ctx rhs tyV
            pure tyV
          Nothing -> snd <$> infer ctx rhs
        irr <- irrefutableFor ctx pat rhsTy
        let lins = linsOf row
            refutD =
              [ pend csp "E_REFUTABLE_LET_PATTERN" (Just "kappa.pattern.refutable-binding")
                  "a 'let' comprehension clause requires an irrefutable pattern; use 'let?' instead (§20.4.1)"
              | not refut && not irr
              ]
            dropD = [dropMsg "the refutable binding 'let?'" lins csp | refut, not (null lins)]
        (_, ctx', _) <- elabPattern ctx pat rhsTy
        let row' = row ++ [(nameText n, False) | n <- surfPatVars pat]
        go ctx' row' ordered oneShot (if refut then filterCard card else card)
          (CAnn SKUnknown (not irr) : anns)
          (reverse (refutD ++ dropD) ++ diags)
          cs
      S.CIf cond -> do
        let lins = linsOf row
            dropD =
              [ pend (exprSpan cond) "E_QUERY_ROW_NOT_DROPPABLE" (Just "kappa.query.row-quantity")
                  ("an 'if' filter may drop the current row, but linear row entry '"
                     <> T.intercalate "', '" lins <> "' is not droppable (§20.10.4)")
              | not (null lins)
              ]
        go ctx row ordered oneShot (filterCard card) (defaultAnn : anns) (dropD ++ diags) cs
      S.COrderBy keys csp -> do
        let lins = linsOf row
        consumed <- concat <$> mapM (consumesLin ctx lins . snd) keys
        let consD =
              [ pend csp "E_QUERY_ORDER_KEY_CONSUMES" (Just "kappa.query.order-key")
                  ("an 'order by' key is checked in a non-consuming context, but this key consumes linear row entry '"
                     <> T.intercalate "', '" (nub consumed) <> "' (§20.6.1)")
              | not (null consumed)
              ]
        go ctx row True oneShot card (defaultAnn : anns) (consD ++ diags) cs
      S.CSkip _ csp -> pagingClause ctx row ordered oneShot card anns diags cs "skip" csp
      S.CTake _ csp -> pagingClause ctx row ordered oneShot card anns diags cs "take" csp
      S.CDistinct _ csp -> do
        let lins = linsOf row
            dropD = [dropMsg "'distinct' deduplication" lins csp | not (null lins)]
        go ctx row ordered oneShot (filterCard card) (defaultAnn : anns) (dropD ++ diags) cs
      S.CGroupBy key aggs n csp -> do
        (_, kTy) <- infer ctx key
        aggTys <- forM aggs $ \(an, ae, _) -> do
          (_, aTy) <- infer ctx ae
          pure (nameText an, aTy)
        let keyD =
              [ pend csp "E_QUERY_GROUP_KEY_FIELD" (Just "kappa.query.group")
                  "the group record always contains the field 'key'; an aggregate may not be named 'key' (§20.7)"
              | any ((== "key") . fst) aggTys
              ]
            recTy = VRecordT (sortOn fst (("key", kTy) : aggTys))
            ctx' = bindCtx (nameText n) False recTy ctx
        go ctx' [(nameText n, False)] False oneShot CZeroOrMore (defaultAnn : anns) (keyD ++ diags) cs
      S.CJoin left pat src cond mInto csp -> do
        (_, srcTy) <- infer ctx src
        si <- sourceInfo ctx srcTy
        let lins = linsOf row
        case (left, mInto) of
          (True, Just into) -> do
            let captured = [v | v <- lins, occursVar v src || occursVar v cond]
                capD =
                  [ pend csp "E_QUERY_LEFT_JOIN_LINEAR_CAPTURE" (Just "kappa.query.left-join")
                      ("the delayed inner query of a 'left join ... into' may not capture linear row entry '"
                         <> T.intercalate "', '" captured <> "' (§20.8)")
                  | not (null captured)
                  ]
                qTy =
                  VGlobN (gPrel "QueryCore")
                    [ (Expl, VCtor (gPrel "QueryMode") [VCtor (gPrel "Reusable") [], VCtor (gPrel "QZeroOrMore") []])
                    , (Expl, VPrim "__omegaQ" [])
                    , (Expl, siItem si)
                    ]
                ctx' = bindCtx (nameText into) False qTy ctx
                row' = row ++ [(nameText into, False)]
            go ctx' row' (ordered && siOrdered si) (oneShot || siOneShot si) card
              (CAnn (siKind si) False : anns) (capD ++ diags) cs
          _ -> do
            let dupD =
                  [ pend csp "E_QUERY_ROW_NOT_DUPLICABLE" (Just "kappa.query.row-quantity")
                      ("a 'join' may drop or duplicate the current row, but linear row entry '"
                         <> T.intercalate "', '" lins <> "' is neither droppable nor duplicable (§20.10.4)")
                  | not (null lins)
                  ]
            (_, ctx', _) <- elabPattern ctx pat (siItem si)
            let row' = row ++ [(nameText nm, siItemLinear si) | nm <- surfPatVars pat]
            go ctx' row' (ordered && siOrdered si) (oneShot || siOneShot si)
              (mulCard card (filterCard (siCard si)))
              (CAnn (siKind si) False : anns) (dupD ++ diags) cs
    pagingClause ctx row ordered oneShot card anns diags cs what csp = do
      let lins = linsOf row
          ordD =
            [ pend csp "E_QUERY_UNORDERED_PAGING" (Just "kappa.query.orderedness")
                ("'" <> what <> "' requires an Ordered pipeline, but the pipeline is unordered here; insert an 'order by' before paging (§20.6.2)")
            | not ordered
            ]
          dropD = [dropMsg ("'" <> what <> "' paging") lins csp | not (null lins)]
      go ctx row ordered oneShot (filterCard card) (defaultAnn : anns) (ordD ++ dropD ++ diags) cs

-- | Which linear row entries does an ordering/distinct key expression
-- consume? Direct arguments at borrow-or-unrestricted callee binders
-- are non-consuming; quantity-1/>=1 binders and bare moves consume.
consumesLin :: Ctx -> [Text] -> Expr -> CheckM [Text]
consumesLin _ [] _ = pure []
consumesLin ctx lins e0 = case e0 of
  EVar (Name v _) -> pure [v | v `elem` lins]
  EDot b _ -> case b of
    EVar _ -> pure [] -- borrowed place read (§12.4 approximation)
    _ -> consumesLin ctx lins b
  EAscription e _ _ -> consumesLin ctx lins e
  EApp (EVar f) args -> do
    st0 <- get
    (_, fTy0) <- resolveName ctx f
    fTy <- forceM fTy0
    put st0
    let explQs = piExplQs fTy
        explArgs = [e | ArgExplicit e <- args]
        slot (mq, arg) = case arg of
          EVar (Name v _)
            | v `elem` lins ->
                pure [v | mq `elem` [Just Q1, Just QGe1, Nothing]]
          _ -> consumesLin ctx lins arg
    concat <$> mapM slot (zip (map Just explQs ++ repeat Nothing) explArgs)
  _ -> pure [v | v <- lins, occursVar v e0]
  where
    piExplQs ty = case ty of
      VPi Expl q _ _ clo -> q : piExplQs (peek clo)
      VPi Impl _ _ _ clo -> piExplQs (peek clo)
      _ -> []
    -- peeking under the binder with a dummy is enough for quantities
    peek (Closure env body) =
      eval (EvalCtx (Globals Map.empty) Map.empty False Map.empty) (VSort 0 : env) body

-- | The elaborated carrier prefix of a prefixed comprehension (§20.9):
-- the prefix term and its (forced) type.
type CarrierPrefix = (Term, Value)

elabComprehension :: Ctx -> CompKind -> [S.CompClause] -> CompYield -> Span -> CheckM (Term, Value)
elabComprehension ctx kind clauses yld sp = elabComprehensionC ctx kind clauses yld sp Nothing

elabComprehensionC :: Ctx -> CompKind -> [S.CompClause] -> CompYield -> Span -> Maybe CarrierPrefix -> CheckM (Term, Value)
elabComprehensionC ctx kind clauses yld sp mCarrier = do
  plan <- planComp ctx clauses yld sp
  forM_ (cpDiags plan) $ \(dsp, code, fam, msg) -> errAt dsp code fam msg
  lowered <- desugarComp ctx (zip clauses (cpAnns plan ++ repeat defaultAnn)) yld sp
  case mCarrier of
    Just prefix -> collectCarrier ctx plan lowered prefix sp
    Nothing -> case kind of
      CompList -> infer ctx lowered
      CompSet -> do
        eqLam <- pairEqLam sp
        infer ctx (prelApp1 sp "__setFromList" [prelApp1 sp "__distinctBy" [lowered, eqLam]])
      CompMap mconf -> do
        eqLam <- pairEqLam sp
        comb <- conflictLam ctx mconf sp
        infer ctx (prelApp1 sp "__mapFromEntries" [prelApp1 sp "__mapResolve" [lowered, eqLam, comb]])
      CompCarrier _ -> infer ctx lowered

prelApp1 :: Span -> Text -> [Expr] -> Expr
prelApp1 sp n es = EApp (EVar (Name n sp)) (map ArgExplicit es)

-- | @\\a b -> a == b@.
pairEqLam :: Span -> CheckM Expr
pairEqLam sp = do
  a <- freshNameM "__a"
  b <- freshNameM "__b"
  let an = Name a sp
      bn = Name b sp
  pure $
    ELambda Nothing [simpleBinder an, simpleBinder bn]
      (EApp (EOpRef Nothing (Name "==" sp) sp) [ArgExplicit (EVar an), ArgExplicit (EVar bn)])
      sp

-- | The map-conflict combine function (§20.5.1); default keep last.
conflictLam :: Ctx -> Maybe OnConflict -> Span -> CheckM Expr
conflictLam ctx mconf sp = case fromMaybe KeepLast mconf of
  KeepLast -> two (\_ b -> EVar b)
  KeepFirst -> two (\a _ -> EVar a)
  CombineWith f -> pure f
  CombineUsing w -> case ctorRefOfExpr w of
    Just cref -> do
      a <- freshNameM "__old"
      b <- freshNameM "__new"
      x <- freshNameM "__x"
      let an = Name a sp
          bn = Name b sp
          xn = Name x sp
          wrap e = EApp w [ArgExplicit e]
          appended = prelApp1 sp "append" [wrap (EVar an), wrap (EVar bn)]
      pure $
        ELambda Nothing [simpleBinder an, simpleBinder bn]
          (EMatch appended [MatchCase (PCtor cref [PVar xn] sp) Nothing (EVar xn) sp] sp)
          sp
    Nothing -> do
      _ <- unsupported ctx sp "this 'combine using' wrapper form"
      two (\_ b -> EVar b)
  where
    two f = do
      a <- freshNameM "__old"
      b <- freshNameM "__new"
      let an = Name a sp
          bn = Name b sp
      pure (ELambda Nothing [simpleBinder an, simpleBinder bn] (f an bn) sp)

ctorRefOfExpr :: Expr -> Maybe CtorRef
ctorRefOfExpr = \case
  EVar n -> Just (CtorRef Nothing n)
  EDot (EVar q) (DotName n) -> Just (CtorRef (Just q) n)
  _ -> Nothing

-- | Speculatively elaborate the head of a possible carrier-prefixed
-- comprehension (§20.9). 'Just' when the prefix is type-valued: either
-- a fully applied result type or a unary @Type -> Type@ sink head. The
-- caller restores elaboration state when this returns 'Nothing'.
carrierPrefix :: Ctx -> Expr -> [Arg] -> CheckM (Maybe CarrierPrefix)
carrierPrefix ctx f preArgs = do
  let headE = if null preArgs then f else EApp f preArgs
  case f of
    EVar _ -> goInfer headE
    EDot _ _ -> goInfer headE
    EApp _ _ -> goInfer headE
    _ -> pure Nothing
  where
    goInfer headE = do
      n0 <- gets (length . csDiags)
      (hTm, hTy) <- infer ctx headE
      n1 <- gets (length . csDiags)
      hTy' <- forceM hTy
      if n1 /= n0
        then pure Nothing
        else case hTy' of
          VSort _ -> pure (Just (hTm, hTy'))
          VPi Expl _ _ dom _ -> do
            domF <- forceM dom
            case domF of
              VSort _ -> pure (Just (hTm, hTy'))
              _ -> pure Nothing
          _ -> pure Nothing

-- | Terminal collection through an explicit carrier prefix (§20.9).
collectCarrier :: Ctx -> CompPlan -> Expr -> CarrierPrefix -> Span -> CheckM (Term, Value)
collectCarrier ctx plan lowered (prefTm, prefTy) sp = do
  (listTm0, listTy) <- infer ctx lowered
  itemV <- elemOfList listTy
  candidate <- case prefTy of
    VSort _ -> evalIn ctx prefTm
    VPi Expl _ _ _ _ -> do
      itemTm <- quoteIn ctx itemV
      evalIn ctx (CApp Expl prefTm itemTm)
    _ -> freshMetaV ctx
  cand <- forceM candidate
  case cand of
    VGlobN (GName _ "QueryCore") [(_, m), (_, q), (_, a)] -> do
      (expOneShot, expCard) <- decodeQueryMode m
      expLinear <- decodeLinearQuantity q
      when (cpOneShot plan && not expOneShot) $
        errAt sp "E_QUERY_MODE_MISMATCH" (Just "kappa.query.mode")
          "this comprehension's plan is one-shot, but the carrier requires a reusable query; use 'OnceQuery [ ... ]' or an explicitly indexed 'QueryCore' carrier (§20.9)"
      unless (cardSub (cpCard plan) expCard) $
        errAt sp "E_QUERY_CARDINALITY_MISMATCH" (Just "kappa.query.cardinality")
          ("the inferred plan cardinality " <> cardName (cpCard plan)
             <> " cannot be checked against the demanded cardinality " <> cardName expCard
             <> "; cardinality may only be widened (§20.10.1)")
      when (cpItemLinear plan && not expLinear) $
        errAt sp "E_QUERY_ITEM_QUANTITY_MISMATCH" (Just "kappa.query.item-quantity")
          "the yielded item is available only at linear quantity 1, but the carrier demands unrestricted (ω) items (§20.9)"
      listTm <- checkAsList listTm0 listTy a
      pure (CApp Expl (CGlob (gPrel "__queryFromList")) listTm, candidate)
    VGlobN (GName _ "Array") [(_, a)] -> do
      listTm <- checkAsList listTm0 listTy a
      pure (CApp Expl (CGlob (gPrel "__arrayFromList")) listTm, candidate)
    VGlobN (GName _ "List") [(_, a)] -> do
      listTm <- checkAsList listTm0 listTy a
      pure (listTm, candidate)
    VGlobN (GName _ "Set") [(_, a)] -> do
      listTm <- checkAsList listTm0 listTy a
      pure (CApp Expl (CGlob (gPrel "__setFromList")) listTm, candidate)
    _ -> unsupported ctx sp "this comprehension carrier"
  where
    elemOfList ty = do
      t <- forceM ty
      case t of
        VGlobN (GName _ "List") [(_, a)] -> pure a
        _ -> freshMetaV ctx
    checkAsList tm ty a = do
      expectType ctx sp ty (VGlobN (gPrel "List") [(Expl, a)])
      pure tm

-- | Pass 2: desugar the clause pipeline over lists (§20.10.11 as-if).
-- The pipeline expression has type @List Row@ where @Row@ is the tuple
-- of the variables bound so far.
desugarComp :: Ctx -> [(S.CompClause, CAnn)] -> CompYield -> Span -> CheckM Expr
desugarComp ctx clauses yld sp = do
  (vars, pipe) <- foldM step ([], EListLit [EUnit sp] sp) clauses
  yf <- perRow vars (yieldElem yld)
  pure (prelApp1 sp "__pipeMap" [pipe, yf])
  where
    yieldElem = \case
      YieldExpr e -> e
      YieldPair k v ->
        ERecordLit [RecItem False (Name "key" sp) (Just k), RecItem False (Name "value" sp) (Just v)] sp

    rowE vars = case vars of
      [] -> EUnit sp
      [v] -> EVar v
      vs -> ETuple (map EVar vs) sp
    rowP vars = case vars of
      [] -> PWild sp
      [v] -> PVar v
      vs -> PTuple (map PVar vs) sp

    perRow vars body = do
      r <- freshNameM "__row"
      let rn = Name r sp
      pure $
        ELambda Nothing [simpleBinder rn]
          (EMatch (EVar rn) [MatchCase (rowP vars) Nothing body sp] sp)
          sp

    cmap f l = prelApp1 sp "__pipeConcatMap" [l, f]

    wrapSrc k src = case k of
      SKQuery -> prelApp1 sp "__queryToList" [src]
      SKSet -> prelApp1 sp "__setToList" [src]
      SKMap -> prelApp1 sp "__mapToList" [src]
      SKOption -> prelApp1 sp "__optionToList" [src]
      SKArray -> prelApp1 sp "__arrayToList" [src]
      _ -> src

    -- element function: match one element against the pattern, emit
    -- the extended row on success (wildcard fallback when filtering)
    elemLam pat filtering successBody = do
      el <- freshNameM "__el"
      let en = Name el sp
          cases =
            MatchCase pat Nothing successBody sp
              : [MatchCase (PWild sp) Nothing (EListLit [] sp) sp | filtering]
      pure (ELambda Nothing [simpleBinder en] (EMatch (EVar en) cases sp) sp)

    step (vars, pipe) (clause, ann) = case clause of
      S.CFor refut _ pat src _ -> do
        let vars' = vars ++ surfPatVars pat
            filtering = refut || caForceRefut ann
        ef <- elemLam pat filtering (EListLit [rowE vars'] sp)
        f <- perRow vars (cmap ef (wrapSrc (caKind ann) src))
        pure (vars', cmap f pipe)
      S.CLet refut pat mty rhs _ -> do
        let vars' = vars ++ surfPatVars pat
            filtering = refut || caForceRefut ann
            rhs' = maybe rhs (\t -> EAscription rhs t sp) mty
            cases =
              MatchCase pat Nothing (EListLit [rowE vars'] sp) sp
                : [MatchCase (PWild sp) Nothing (EListLit [] sp) sp | filtering]
        f <- perRow vars (EMatch rhs' cases sp)
        pure (vars', cmap f pipe)
      S.CIf cond -> do
        f <- perRow vars (EIf [(cond, EListLit [rowE vars] sp)] (Just (EListLit [] sp)) sp)
        pure (vars, cmap f pipe)
      S.COrderBy keys _ -> do
        -- decorate-sort-undecorate: pair each row with its key tuple,
        -- stably sort on the keys, then drop the decoration (§20.6.1)
        let keyTuple = case keys of
              [(_, k)] -> k
              _ -> ETuple (map snd keys) sp
        deco <- perRow vars (ETuple [keyTuple, rowE vars] sp)
        cmp <- decoCmpLam keys
        und <- undecorateLam
        pure
          ( vars
          , prelApp1 sp "__pipeMap"
              [prelApp1 sp "__sortBy" [prelApp1 sp "__pipeMap" [pipe, deco], cmp], und]
          )
      S.CSkip n _ -> pure (vars, prelApp1 sp "__listDrop" [n, pipe])
      S.CTake n _ -> pure (vars, prelApp1 sp "__listTake" [n, pipe])
      S.CDistinct Nothing _ -> do
        eqLam <- rowEqLam vars
        pure (vars, prelApp1 sp "__distinctBy" [pipe, eqLam])
      S.CDistinct (Just k) _ -> do
        -- decorate with the key, dedupe on it via Eq, undecorate
        deco <- perRow vars (ETuple [k, rowE vars] sp)
        pure (vars, prelApp1 sp "__distinctOnFst" [prelApp1 sp "__pipeMap" [pipe, deco]])
      S.CGroupBy key aggs n _ -> do
        kf <- perRow vars key
        eqLam <- pairEqLam sp
        let groups = prelApp1 sp "__groupBy" [pipe, kf, eqLam]
        g <- freshNameM "__g"
        let gn = Name g sp
            gRows = EDot (EVar gn) (DotName (Name "rows" sp))
        aggItems <- forM aggs $ \(an, ae, mUsing) -> do
          valF <- perRow vars ae
          body <- case mUsing of
            Nothing -> pure (prelApp1 sp "__aggFold" [gRows, valF])
            Just w -> case ctorRefOfExpr w of
              Just cref -> do
                r <- freshNameM "__r"
                x <- freshNameM "__x"
                let rn = Name r sp
                    xn = Name x sp
                    wrapF =
                      ELambda Nothing [simpleBinder rn]
                        (EApp w [ArgExplicit (EApp valF [ArgExplicit (EVar rn)])])
                        sp
                    folded = prelApp1 sp "__aggFold" [gRows, wrapF]
                pure (EMatch folded [MatchCase (PCtor cref [PVar xn] sp) Nothing (EVar xn) sp] sp)
              Nothing -> do
                _ <- unsupported ctx (exprSpan w) "this aggregate 'using' wrapper form"
                pure (prelApp1 sp "__aggFold" [gRows, valF])
          pure (RecItem False an (Just body))
        let rec' =
              ERecordLit
                (RecItem False (Name "key" sp) (Just (EDot (EVar gn) (DotName (Name "key" sp)))) : aggItems)
                sp
            gLam = ELambda Nothing [simpleBinder gn] rec' sp
        pure ([n], prelApp1 sp "__pipeMap" [groups, gLam])
      S.CJoin True pat src cond (Just into) _ -> do
        let vars' = vars ++ [into]
        ef <- elemLamKeep pat cond
        let matches = cmap ef (wrapSrc (caKind ann) src)
            qVal = prelApp1 sp "__queryOfMatches" [matches]
            inner = ELet [LetBind False emptyPrefix (PVar into) Nothing qVal sp] (EListLit [rowE vars'] sp) sp
        f <- perRow vars inner
        pure (vars', cmap f pipe)
      S.CJoin _ pat src cond _ _ -> do
        let vars' = vars ++ surfPatVars pat
        ef <- elemLam pat True (EIf [(cond, EListLit [rowE vars'] sp)] (Just (EListLit [] sp)) sp)
        f <- perRow vars (cmap ef (wrapSrc (caKind ann) src))
        pure (vars', cmap f pipe)

    -- left join: keep the matching element itself (§20.8)
    elemLamKeep pat cond = do
      el <- freshNameM "__el"
      let en = Name el sp
          succBody = EIf [(cond, EListLit [EVar en] sp)] (Just (EListLit [] sp)) sp
          cases =
            [ MatchCase pat Nothing succBody sp
            , MatchCase (PWild sp) Nothing (EListLit [] sp) sp
            ]
      pure (ELambda Nothing [simpleBinder en] (EMatch (EVar en) cases sp) sp)

    -- row equality: componentwise (==) over the row tuple (§20.6.3)
    rowEqLam vars = do
      ra <- freshNameM "__ra"
      rb <- freshNameM "__rb"
      asV <- mapM (const (freshNameM "__qa")) vars
      bsV <- mapM (const (freshNameM "__qb")) vars
      let ran = Name ra sp
          rbn = Name rb sp
          aNames = map (`Name` sp) asV
          bNames = map (`Name` sp) bsV
          eqOne a b = EApp (EOpRef Nothing (Name "==" sp) sp) [ArgExplicit (EVar a), ArgExplicit (EVar b)]
          trueE = EVar (Name "True" sp)
          falseE = EVar (Name "False" sp)
          conj = foldr (\(a, b) acc -> EIf [(eqOne a b, acc)] (Just falseE) sp) trueE (zip aNames bNames)
          body =
            EMatch (EVar ran)
              [MatchCase (rowP aNames) Nothing (EMatch (EVar rbn) [MatchCase (rowP bNames) Nothing conj sp] sp) sp]
              sp
      pure (ELambda Nothing [simpleBinder ran, simpleBinder rbn] body sp)

    -- lexicographic stable comparator over decorated (keys, row)
    -- pairs (§20.6.1); 'desc' swaps the comparison operands
    decoCmpLam keys = do
      ra <- freshNameM "__pa"
      rb <- freshNameM "__pb"
      asV <- mapM (const (freshNameM "__ka")) keys
      bsV <- mapM (const (freshNameM "__kb")) keys
      let ran = Name ra sp
          rbn = Name rb sp
          aNames = map (`Name` sp) asV
          bNames = map (`Name` sp) bsV
          keyP ns = case ns of
            [v] -> PVar v
            vs -> PTuple (map PVar vs) sp
          pairP ns = PTuple [keyP ns, PWild sp] sp
          cmpOne desc a b =
            let (x, y) = if desc then (b, a) else (a, b)
             in prelApp1 sp "compare" [EVar x, EVar y]
          chain [] = prelApp1 sp "compare" [EIntLit 0 Nothing sp, EIntLit 0 Nothing sp]
          chain [(desc, a, b)] = cmpOne desc a b
          chain ((desc, a, b) : restK) =
            EMatch (cmpOne desc a b)
              [ MatchCase (PCtor (CtorRef Nothing (Name "EQ" sp)) [] sp) Nothing (chain restK) sp
              , MatchCase (PVar (Name "__o" sp)) Nothing (EVar (Name "__o" sp)) sp
              ]
              sp
          keyed = [(desc, a, b) | ((desc, _), (a, b)) <- zip keys (zip aNames bNames)]
          body =
            EMatch (EVar ran)
              [ MatchCase (pairP aNames) Nothing
                  (EMatch (EVar rbn) [MatchCase (pairP bNames) Nothing (chain keyed) sp] sp)
                  sp
              ]
              sp
      pure (ELambda Nothing [simpleBinder ran, simpleBinder rbn] body sp)

    -- drop the (keys, row) decoration after sorting
    undecorateLam = do
      p <- freshNameM "__p"
      r <- freshNameM "__r"
      let pn = Name p sp
          rn = Name r sp
      pure $
        ELambda Nothing [simpleBinder pn]
          (EMatch (EVar pn) [MatchCase (PTuple [PWild sp, PVar rn] sp) Nothing (EVar rn) sp] sp)
          sp

-- ── Declarations ─────────────────────────────────────────────────────

-- | Check a resolved module: two passes (headers then bodies), per the
-- preceding-signature recursion rule (§15.16, §9.2).
checkModule :: CheckState -> Module -> (CheckState, Diagnostics)
checkModule st0 m =
  let sigNames = [nameText n | DSig _ n _ _ <- modDecls m]
      siglessLets =
        [ nameText n
        | DLet _ (LetDef (Just n) _ _ _ _ _ _ _) _ <- modDecls m
        , nameText n `notElem` sigNames
        ]
      passes = do
        mapM_ predeclarePass (modDecls m)
        mapM_ (headerPassIn siglessLets) (modDecls m)
        mapM_ (bodyPassIn siglessLets) (modDecls m)
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

-- | Header pass, knowing which module-level lets have no signature: a
-- signature whose type mentions such a name (a reified static object,
-- §2.8.3) is deferred to the body pass, where the binding's value is
-- available in declaration order.
headerPassIn :: [Text] -> Decl -> CheckM ()
headerPassIn siglessLets = \case
  DSig _ _ tyE _
    | any (`elem` siglessLets) (sigHeadNames tyE) ->
        -- deferred to 'bodyPassIn' (the let's value is needed first)
        pure ()
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
    TraitDefault (LetDef (Just mn) _ _ _ _ mty _ body) _ -> do
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
  let defaults = Map.fromList [(nameText dn, ld) | TraitDefault ld@(LetDef (Just dn) _ _ _ _ _ _ _) _ <- members]
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

-- | Body pass: elaborates definitions, plus any signatures the header
-- pass deferred because they mention signature-less module lets.
bodyPassIn :: [Text] -> Decl -> CheckM ()
bodyPassIn siglessLets d = case d of
  DSig _ _ tyE _
    | any (`elem` siglessLets) (sigHeadNames tyE) -> headerPassIn [] d
  _ -> bodyPass d

-- names a signature's type may resolve through (heads of applications,
-- dotted bases, binder domains)
sigHeadNames :: Expr -> [Text]
sigHeadNames = go
  where
    go = \case
      EVar (Name t _) -> [t]
      EApp f args -> go f ++ concatMap goArg args
      EDot e _ -> go e
      EQDot e _ -> go e
      EArrow b e -> maybe [] go (bType b) ++ go e
      EForall bs e _ -> concatMap (maybe [] go . bType) bs ++ go e
      EExists bs e _ -> concatMap (maybe [] go . bType) bs ++ go e
      ETuple es _ -> concatMap go es
      EOptionSugar e _ -> go e
      ETraitArrow a b -> go a ++ go b
      EOpChain els -> concat [go x | ChainOperand x <- els]
      _ -> []
    goArg = \case
      ArgExplicit e -> go e
      ArgImplicit e -> go e
      _ -> []

bodyPass :: Decl -> CheckM ()
bodyPass = \case
  DLet mods ld sp -> elabLetDecl mods ld sp
  DInstance inst sp -> elabInstance inst sp
  DPattern mods ld sp -> elabActivePatternDecl mods ld sp
  DProjection mods n bs ty body sp -> elabProjectionDecl mods n bs ty body sp
  DDerive _ sp ->
    errAt sp "E_UNSUPPORTED" Nothing "derive declarations are not supported by this implementation"
  DTopSplice _ sp ->
    errAt sp "E_UNSUPPORTED" Nothing "top-level splices are not supported by this implementation"
  _ -> pure ()

-- | An active-pattern declaration (§17.3.1) elaborates as an ordinary
-- function definition (the pattern name is also a first-class value)
-- and registers pattern metadata: its result classification and the
-- number of pattern arguments before the scrutinee.
elabActivePatternDecl :: DeclMods -> LetDef -> Span -> CheckM ()
elabActivePatternDecl mods ld sp = do
  elabLetDecl mods ld sp
  case ldName ld of
    Nothing -> pure ()
    Just n -> do
      g <- ownName n
      mgd <- gets (Map.lookup g . csGlobals)
      forM_ mgd $ \gd -> do
        (_argc, res) <- unrollExplicit 0 (gdType gd)
        resF <- forceM res
        let kind = case resF of
              VGlobN (GName _ "Option") _ -> Right APOption
              VGlobN (GName _ "Match") _ -> Right APMatch
              VGlobN (GName _ h) _ | h `elem` ["IO", "STM", "Elab"] -> Left h
              _ -> Right APTotal
        case kind of
          Left h ->
            errAt sp "E_ACTIVE_PATTERN_MONADIC_RESULT" (Just "kappa.pattern.active")
              ("an active pattern's result type may not be the monadic type '" <> h
                 <> "'; return Option, Match, or a total view type (§17.3.1)")
          Right k -> do
            -- an Option/total-view pattern cannot return a residue, so
            -- a linear scrutinee would be lost on the miss path
            let explBinders = [b | b <- ldBinders ld, not (bImplicit b)]
                scrutLinear = case reverse explBinders of
                  (b : _) ->
                    bpQuantity (bPrefix b) `elem` [Just S.QOne, Just S.QAtLeastOne]
                      && isNothing (bpBorrow (bPrefix b))
                  [] -> False
            when (scrutLinear && k /= APMatch) $
              errAt sp "E_ACTIVE_PATTERN_LINEARITY_VIOLATION" (Just "kappa.pattern.active")
                "this active pattern consumes a linear scrutinee but cannot thread a residue back on a miss; return 'Match item residue' instead (§17.3)"
            modify' $ \st -> st {csActive = Map.insert g (APInfo k) (csActive st)}
  where
    unrollExplicit :: Int -> Value -> CheckM (Int, Value)
    unrollExplicit = goU 0
      where
        goU expl lvl v = do
          vf <- forceM v
          case vf of
            VPi ic _ _ _ clo -> do
              inner <- clApp clo (VRigid lvl [])
              goU (if ic == Expl then expl + 1 else expl) (lvl + 1) inner
            _ -> pure (expl, vf)

-- | A projection definition (§9.1.1). Both forms register a term facet
-- global (a first-class descriptor) plus 'csProjections' metadata used
-- by the application-site elaborators of §16.1.5/§16.1.6.
--
--   * selector form: term facet @Δ -> Projector Roots T@; the runtime
--     value is @λΔ. λplaces. body@ with each @yield p@ reading @p@.
--   * expanded form: term facet @Δ -> Bundle@, a structural record of
--     @Getter/Opener/Setter/Sinker@ accessor closures with the §9.1.1
--     descriptor-field synthesis (get+set ⇒ open, inout ⇒ set).
--
-- Place lambdas/applications use the canonical (lexicographic) order of
-- the @Roots@ record so descriptor applications can be elaborated from
-- the roots record type alone.
elabProjectionDecl :: DeclMods -> Name -> [Binder] -> Expr -> ProjBody -> Span -> CheckM ()
elabProjectionDecl _mods n binders resTyE body sp = do
  flushPending
  g <- ownName n
  let groups = projBinderGroups binders
      placeBs = [b | (True, b) <- groups]
      ordBs = [b | (False, b) <- groups]
  when (null placeBs) $
    errAt sp "E_PROJECTION_MISSING_PLACE_BINDER" (Just "kappa.projection.place-binder")
      "a projection definition must contain at least one 'place' binder (§9.1.1)"
  -- Δ context: ordinary binders, declaration order
  (ctxD, ordTele) <- elabOrdBinders emptyCtx ordBs
  -- place binder types and the focus, under the full Δ
  places0 <- forM placeBs $ \b -> do
    tyTm <- case binderTypeExpr b of
      Just tyE -> fst <$> inferType ctxD tyE
      Nothing -> freshMeta
    tyV <- evalIn ctxD tyTm
    pure (maybe "_" nameText (bName b), tyTm, tyV)
  (focusTm, _) <- inferType ctxD resTyE
  focusV <- evalIn ctxD focusTm
  let placesLex = sortOn (\(nm, _, _) -> nm) places0
      rootsTm = CRecordT [(nm, t) | (nm, t, _) <- placesLex]
      placeNames = [nm | (nm, _, _) <- places0]
      lamsOrd t = foldr (\(q, nm, _) acc -> CLam Expl q nm acc) t ordTele
      pisOrd t = foldr (\(q, nm, ty) acc -> CPi Expl q nm ty acc) t ordTele
      app2 h a b = CApp Expl (CApp Expl (CGlob (gPrel h)) a) b
  case body of
    ProjSelector bodyE0 -> do
      let yields0 = projYieldPlaces bodyE0
      yields <- fmap catMaybes . forM yields0 $ \case
        Right (root, path)
          -- with no place binders at all the declaration-level
          -- diagnostic already covers every yield
          | root `elem` placeNames || null placeNames -> pure (Just (root, path))
        Right (_, _) -> do
          errAt sp "E_PROJECTION_YIELD_INVALID" (Just "kappa.projection.yield")
            "each 'yield' operand must be a stable place rooted in a 'place' binder of this projection (§9.1.1)"
          pure Nothing
        Left ysp -> do
          errAt ysp "E_PROJECTION_YIELD_INVALID" (Just "kappa.projection.yield")
            "each 'yield' operand must be a stable place rooted in a 'place' binder of this projection (§9.1.1)"
          pure Nothing
      let bodyE = stripYields bodyE0
          ctxBody = foldl (\c (nm, _, tv) -> bindCtx nm False tv c) ctxD placesLex
      bodyTm <- check ctxBody bodyE focusV
      let coreTy = pisOrd (app2 "Projector" rootsTm focusTm)
          defTm = lamsOrd (foldr (\(nm, _, _) acc -> CLam Expl QW nm acc) bodyTm placesLex)
      registerProjection g coreTy defTm $
        ProjInfo [isP | (isP, _) <- groups] placeNames True yields
    ProjAccessors clauses -> do
      forM_ (duplicatesOf [k | (k, _, _) <- clauses]) $ \k ->
        errAt sp "E_PROJECTION_ACCESSOR_CLAUSE_DUPLICATE" (Just "kappa.projection.accessor")
          ("the accessor clause '" <> k <> "' appears more than once (§9.1.1)")
      when (length placeBs /= 1) $
        errAt sp "E_PROJECTION_EXPANDED_ACCESSOR_PLACE_BINDER_MISMATCH" (Just "kappa.projection.accessor")
          "an expanded-form projection must have exactly one 'place' binder (§9.1.1)"
      case places0 of
        [] -> pure ()
        ((pName, pTyTm, pTyV) : _) -> do
          let ctxP = bindCtx pName False pTyV ctxD
              zipperTm = CApp Expl (CApp Expl (CApp Expl (CGlob (gPrel "Zipper")) pTyTm) focusTm) focusTm
          zipperV <- evalIn ctxD zipperTm
          let clauseOf k = [(mb, e) | (k', mb, e) <- clauses, k' == k]
              getC = clauseOf "get"
              setC = clauseOf "set"
              inoutC = clauseOf "inout"
              sinkC = clauseOf "sink"
          -- direct clause bodies
          getTm <- forM (take 1 getC) $ \(_, e) -> check ctxP e focusV
          sinkTm <- forM (take 1 sinkC) $ \(_, e) -> check ctxP e focusV
          inoutTm <- forM (take 1 inoutC) $ \(_, e) -> check ctxP e zipperV
          setTm <- forM (take 1 setC) $ \(mb, e) -> do
            let nv = fromMaybe "new_value" (mb >>= fmap nameText . bName)
            nvV <- case mb >>= bType of
              Just tyE -> do
                (t, _) <- inferType ctxD tyE
                evalIn ctxD t
              Nothing -> pure focusV
            tm <- check (bindCtx nv False nvV ctxP) e pTyV
            pure (nv, tm)
          -- synthesized descriptors (§9.1.1)
          synthOpen <-
            case (inoutTm, getC, setC) of
              ([], ((_, getE) : _), ((mb, setE) : _)) -> do
                let nvB = fromMaybe (simpleBinder (Name "new_value" sp)) mb
                    openE =
                      EApp (EVar (Name "Zipper" sp))
                        [ ArgExplicit getE
                        , ArgExplicit (ELambda Nothing [nvB] setE sp)
                        ]
                tm <- check ctxP openE zipperV
                pure [tm]
              _ -> pure []
          synthSet <-
            case (setTm, inoutC) of
              ([], ((_, inoutE) : _)) -> do
                let newE = EVar (Name "__new" sp)
                    fillE = EApp (EDot inoutE (DotName (Name "fill" sp))) [ArgExplicit newE]
                tm <- check (bindCtx "__new" False focusV ctxP) fillE pTyV
                pure [("__new", tm)]
              _ -> pure []
          let lamP t = CLam Expl QW pName t
              caps =
                [ ("get", app2 "Getter" rootsTm focusTm, lamP t) | t <- take 1 getTm ]
                  ++ [ ("open", app2 "Opener" rootsTm focusTm, lamP t)
                     | t <- take 1 (inoutTm ++ synthOpen)
                     ]
                  ++ [ ("set", app2 "Setter" rootsTm focusTm, lamP (CLam Expl Q1 nv t))
                     | (nv, t) <- take 1 (setTm ++ synthSet)
                     ]
                  ++ [ ("sink", app2 "Sinker" rootsTm focusTm, lamP t) | t <- take 1 sinkTm ]
              capsSorted = sortOn (\(nm, _, _) -> nm) caps
              coreTy = pisOrd (CRecordT [(nm, t) | (nm, t, _) <- capsSorted])
              defTm = lamsOrd (CRecordV [(nm, t) | (nm, _, t) <- capsSorted])
          registerProjection g coreTy defTm $
            ProjInfo [isP | (isP, _) <- groups] placeNames False []
  where
    stripYields e0 = case e0 of
      EApp (EVar y) [ArgExplicit e] | nameText y == "yield" -> e
      EIf alts mels isp ->
        EIf [(c, stripYields b) | (c, b) <- alts] (stripYields <$> mels) isp
      EMatch scrut cases msp ->
        EMatch scrut
          [ case c of
              MatchCase p mg b csp -> MatchCase p mg (stripYields b) csp
              other -> other
          | c <- cases
          ]
          msp
      EBlock ds (Just fin) bsp -> EBlock ds (Just (stripYields fin)) bsp
      EAscription e tyE asp -> EAscription (stripYields e) tyE asp
      e -> e

-- | Elaborate the ordinary (non-place) binders of a projection in
-- declaration order, returning the extended context and the telescope.
elabOrdBinders :: Ctx -> [Binder] -> CheckM (Ctx, [(Q, Text, Term)])
elabOrdBinders ctx0 [] = pure (ctx0, [])
elabOrdBinders ctx0 (b : bs) = do
  tyTm <- case binderTypeExpr b of
    Just tyE -> fst <$> inferType ctx0 tyE
    Nothing -> freshMeta
  tyV <- evalIn ctx0 tyTm
  let nm = maybe "_" nameText (bName b)
      ctx1 = bindCtx nm (bImplicit b) tyV ctx0
  (ctx2, rest) <- elabOrdBinders ctx1 bs
  pure (ctx2, (binderQ b, nm, tyTm) : rest)

-- | Register a projection's term facet and projection-facet metadata.
registerProjection :: GName -> Term -> Term -> ProjInfo -> CheckM ()
registerProjection g coreTy defTm pj = do
  flushPending
  coreTy' <- zonkTermM 0 coreTy
  defTm' <- zonkTermM 0 defTm
  tyV <- evalIn emptyCtx coreTy'
  tmV <- evalIn emptyCtx defTm'
  addGlobal g (GlobalDef tyV (Just tmV) False)
  modify' $ \st -> st {csProjections = Map.insert g pj (csProjections st)}

elabLetDecl :: DeclMods -> LetDef -> Span -> CheckM ()
-- the parsed decreases clause is not consulted: termination is verified
-- by the structural analysis below (see IMPLEMENTATION_NOTES.md)
elabLetDecl _ (LetDef (Just n) _ Nothing _ binders mResTy _mdec body) sp = do
  -- resolve any goals postponed from signature elaboration first, so the
  -- signature's value is canonical while checking the body
  flushPending
  g <- ownName n
  noteDefinition g sp
  st <- get
  msig <- pure (Map.lookup g (csGlobals st))
  case msig of
    Just gd | Nothing <- gdValue gd -> pure ()
    _ ->
      -- no governing signature: the binding is manifest (§2.8.4)
      modify' $ \stM -> stM {csManifest = Map.insert g () (csManifest stM)}
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
elabLetDecl _ (LetDef Nothing _ (Just pat) _ [] mty Nothing body) sp = do
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
          | not (bImplicit b)
          , (nameText <$> bName b) /= Just nm -> do
              -- skip implicit binder: bind it for the body (an explicit
              -- definition binder with the SAME name instead claims the
              -- implicit parameter, e.g. `let f r = …` against
              -- `f : forall (r : T). …`)
              let ctx' = bindCtx nm True dom ctx
              cod <- clApp clo (VRigid (ctxLen ctx) [])
              CLam Impl q nm <$> go ctx' cod (b : rest)
        VPi ic q nm dom clo -> do
          let bn = fromMaybe nm (nameText <$> bName b)
          forM_ (binderTypeExpr b) $ \tyE -> do
            (tyTm, _) <- inferType ctx tyE
            tyV <- evalIn ctx tyTm
            expectType ctx (bSpan b) dom tyV
          unless (ic == (if bImplicit b then Impl else Expl) || ic == Impl) $
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
      -- head arguments check against the trait constructor's parameter
      -- types (so type constructors are valid arguments of
      -- higher-kinded traits, §14.1.2)
      traitTy <- gets (fmap gdType . Map.lookup g . csGlobals)
      argTms <- case traitTy of
        Just tt -> checkHeadArgs ctxP' tt argEs
        Nothing -> mapM (\e -> fst <$> inferType ctxP' e) argEs
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
        mLoc <- localCandidate ctxP' sp Q0 supGoal
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
          errAt sp "E_TRAIT_SUPERTRAIT_UNSATISFIED" (Just "kappa.trait.supertrait-unsatisfied")
            ("instance does not satisfy the supertrait premise '" <> renderTerm gT <> "' of trait '" <> gnameText g <> "' (§14.1.4)")
      -- member definitions checked against member types
      dictFields <- forM (tiMembers ti) $ \mn -> do
        case findMember mn members of
          Just (LetDef _ _ _ _ mbinders mResTy _ mbody, msp) -> do
            memberTyV <- memberSigInstance g mn argTms ctxP'
            tm <- checkMemberAgainst ctxP' memberTyV mbinders mResTy mbody msp
            pure (Just (mn, tm))
          Nothing -> case Map.lookup mn (tiDefaults ti) of
            -- the trait's default definition fills the member (§14.2.3)
            -- the default's own annotation mentions trait parameters
            -- and is superseded by the instantiated member type
            Just (LetDef _ _ _ _ dbinders _ _ dbody) -> do
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
      case [ (ld, dsp) | DLet _ ld@(LetDef (Just dn) _ _ _ _ _ _ _) dsp <- ms, nameText dn == mn
           ] of
        (x : _) -> Just x
        [] -> Nothing

    bindPremises ctx [] = pure ctx
    bindPremises ctx (p : rest) = do
      pv <- evalIn ctx p
      bindPremises (bindCtx "__prem" True pv ctx) rest

    checkHeadArgs _ _ [] = pure []
    checkHeadArgs ctx ty (e : es) = do
      t <- forceM ty
      case t of
        VPi Expl _ _ dom clo -> do
          tm <- check ctx e dom
          v <- evalIn ctx tm
          rest <- clApp clo v >>= \cod -> checkHeadArgs ctx cod es
          pure (tm : rest)
        _ -> do
          tm <- fst <$> inferType ctx e
          rest <- checkHeadArgs ctx t es
          pure (tm : rest)

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
