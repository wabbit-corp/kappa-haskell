-- | Quantity-and-borrow usage analysis (Spec §12.2–§12.4).
--
-- A post-elaboration pass over the resolved surface module. Each named
-- definition body is walked once, computing for every tracked binding a
-- usage interval [lo, hi] (sequential composition adds, branch joins
-- take min\/max, §12.2.2) plus borrow\/escape facts:
--
--   * @1@ / @>=1@ bindings unused on some path  → E_QTT_LINEAR_DROP
--   * @1@ / @<=1@ bindings used more than once  → E_QTT_LINEAR_OVERUSE
--   * @0@ bindings referenced at runtime        → E_QTT_ERASED_RUNTIME_USE
--   * borrowed bindings moved into a consuming
--     (quantity @1@\/@>=1@) parameter           → E_QTT_BORROW_CONSUME
--   * closures capturing borrowed bindings
--     escaping through the definition's result  → E_QTT_BORROW_ESCAPE
--   * call-site @~place@ markers against the
--     callee's @inout@ parameters (§18.9.3)     → E_QTT_INOUT_MARKER_*
--   * @inout@ parameters whose declared result
--     does not thread the place back as a field → E_QTT_INOUT_THREADED_FIELD_MISSING
--
-- The analysis is deliberately conservative: only bindings with explicit
-- quantity prefixes (or parameters claiming erased signature binders)
-- are counted, parameter demand comes from same-module signatures, and a
-- definition containing constructs outside the modelled subset is
-- skipped entirely rather than misjudged.
module Kappa.Usage
  ( usageDiagnostics
  ) where

import Control.Monad (forM_, unless, when)
import Control.Monad.State.Strict (State, execState, gets, modify')
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes, fromMaybe, isJust, mapMaybe)
import Data.Text (Text)
import qualified Data.Text as T
import Kappa.Diagnostic
import Kappa.Source (Span)
import Kappa.Syntax

-- ── Tables ───────────────────────────────────────────────────────────

-- | Demand a callee places on one explicit argument position.
data PInfo = PInfo
  { pQuantity :: !(Maybe Quantity)
  , pBorrow :: !Bool
  , pInout :: !Bool
  }

defaultP :: PInfo
defaultP = PInfo Nothing False False

-- | One tracked binding in scope.
data VInfo = VInfo
  { vKey :: !Text -- ^ unique usage-map key (shadowing-safe)
  , vQ :: !(Maybe Quantity) -- ^ counted quantity (@1@, @<=1@, @>=1@, @0@)
  , vBorrowed :: !Bool
  , vAnonBorrow :: !Bool -- ^ anonymous @&@ borrow: capture may not escape
  , vTaint :: !(Maybe Span) -- ^ closure capturing a borrow, formed here
  , vSpan :: !Span -- ^ binding site (drop reports)
  }

-- | Usage interval of one binding plus reporting metadata: move lo\/hi,
-- chronological move occurrences, touch lower bound (touches include
-- borrow-uses; a binding is dropped iff some path never touches it).
data Cnt = Cnt !Int !Int ![Span] !Int

cTouch :: Cnt -> Bool
cTouch (Cnt _ _ _ t) = t > 0

zeroC :: Cnt
zeroC = Cnt 0 0 [] 0

oneC :: Span -> Cnt
oneC sp = Cnt 1 1 [sp] 1

touchC :: Cnt
touchC = Cnt 0 0 [] 1

seqC :: Cnt -> Cnt -> Cnt
seqC (Cnt a b o t) (Cnt c d o' t') = Cnt (a + c) (b + d) (o ++ o') (t + t')

altC :: Cnt -> Cnt -> Cnt
altC (Cnt a b o t) (Cnt c d o' t') =
  Cnt (min a c) (max b d) (if d > b then o' else o) (min t t')

type Usage = Map Text Cnt

seqU :: Usage -> Usage -> Usage
seqU = Map.unionWith seqC

altU :: Usage -> Usage -> Usage
altU u1 u2 =
  Map.mergeWithKey (\_ a b -> Just (altC a b)) (Map.map (altC zeroC)) (Map.map (altC zeroC)) u1 u2

altUs :: [Usage] -> Usage
altUs [] = Map.empty
altUs us = foldr1 altU us

-- mark every binding as possibly-unused (loops may run zero times)
loopU :: Usage -> Usage
loopU = Map.map (\(Cnt _ hi occs _) -> Cnt 0 hi occs 0)

-- ── Analysis monad ───────────────────────────────────────────────────

data S = S
  { sDiags :: ![Diagnostic]
  , sBail :: !Bool
  , sFresh :: !Int
  }

type M = State S

emit :: DiagnosticCode -> DiagnosticFamily -> Span -> Text -> M ()
emit code fam sp msg =
  modify' $ \s ->
    s {sDiags = diag SevError StageElaborate code (Just fam) sp msg : sDiags s}

bailOut :: M ()
bailOut = modify' $ \s -> s {sBail = True}

-- | Shadowing-safe usage key for a new binding of @nm@.
freshKey :: Text -> M Text
freshKey nm = do
  n <- gets sFresh
  modify' $ \s -> s {sFresh = n + 1}
  pure (nm <> "#" <> T.pack (show n))

type Env = (Map Text VInfo, Map Text [PInfo])

-- ── Entry point ──────────────────────────────────────────────────────

-- | Analyze a resolved module; returns the §12.2–§12.4 usage
-- diagnostics for its named definitions.
usageDiagnostics :: Module -> [Diagnostic]
usageDiagnostics m = concatMap analyzeDecl lets
  where
    decls = modDecls m
    sigs = Map.fromList [(nameText n, ty) | DSig _ n ty _ <- decls]
    lets = [ld | DLet _ ld _ <- decls, Just _ <- [ldName ld]]
    fns =
      Map.fromList
        [ (nameText n, fnParams (Map.lookup (nameText n) sigs) ld)
        | ld <- lets
        , Just n <- [ldName ld]
        ]
        `Map.union` builtinFns
    analyzeDecl ld =
      let nm = maybe "" nameText (ldName ld)
          sigTy = Map.lookup nm sigs
          final = execState (analyzeLet fns sigTy ld) (S [] False 0)
       in if sBail final then [] else reverse (sDiags final)

-- Callee demand for prelude helpers the fixtures rely on.
builtinFns :: Map Text [PInfo]
builtinFns =
  Map.fromList
    [ ("unsafeConsume", [PInfo (Just QOne) False False])
    ]

-- ── Signature alignment ──────────────────────────────────────────────

-- | The signature's binder chain, implicits included (forall binders
-- and trait obligations are erased\/implicit slots, §11.3).
sigBinders :: Expr -> [Binder]
sigBinders = \case
  EForall bs body _ ->
    -- §11.3: forall (x : S). T ≡ (@0 x : S) -> T
    map
      ( \b ->
          b
            { bImplicit = True
            , bPrefix =
                (bPrefix b)
                  { bpQuantity = Just (fromMaybe QZero (bpQuantity (bPrefix b)))
                  }
            }
      )
      bs
      ++ sigBinders body
  ETraitArrow _ body -> sigBinders body
  EArrow b body -> b : sigBinders body
  ECaptures e _ _ -> sigBinders e
  _ -> []

-- | Align definition binders with signature binders: an explicit
-- definition binder claims a leading implicit signature binder of the
-- same name (§9.2); otherwise implicits are skipped.
alignParams :: [Binder] -> [Binder] -> [(Binder, Maybe Binder)]
alignParams [] _ = []
alignParams (b : bs) sbs = case sbs of
  (s : ss)
    | bImplicit s && not (bImplicit b) && not (sameName b s) ->
        alignParams (b : bs) ss
    | otherwise -> (b, Just s) : alignParams bs ss
  [] -> (b, Nothing) : alignParams bs []
  where
    sameName x y = case (bName x, bName y) of
      (Just nx, Just ny) -> nameText nx == nameText ny
      _ -> False

-- | Explicit-argument demand of a definition, signature preferred.
fnParams :: Maybe Expr -> LetDef -> [PInfo]
fnParams msig ld =
  let sigPs = maybe [] sigBinders msig
      fromSig = [binderP b | b <- sigPs, not (bImplicit b)]
      aligned = alignParams (ldBinders ld) sigPs
      fromLet =
        [ mergeP (binderP b) (maybe defaultP binderP ms)
        | (b, ms) <- aligned
        , not (bImplicit b)
        , maybe True (not . bImplicit) ms
        ]
   in if null (ldBinders ld) then fromSig else fromLet
  where
    binderP b =
      let BinderPrefix mq mb = bPrefix b
       in PInfo mq (isJust mb) (bInout b)
    mergeP (PInfo q1 b1 i1) (PInfo q2 b2 i2) =
      PInfo (q1 `orElse` q2) (b1 || b2) (i1 || i2)
    orElse (Just x) _ = Just x
    orElse Nothing y = y

-- ── Definition analysis ──────────────────────────────────────────────

analyzeLet :: Map Text [PInfo] -> Maybe Expr -> LetDef -> M ()
analyzeLet fns msig ld = do
  let aligned = alignParams (ldBinders ld) (maybe [] sigBinders msig)
  binds <- catMaybes <$> mapM paramBind aligned
  let env = (Map.fromList binds, fns)
  checkInoutResult msig ld
  (u, taint) <- walkE env (ldBody ld)
  forM_ binds $ \(_, vi) -> closeVar vi u
  forM_ taint $ \sp ->
    emit "E_QTT_BORROW_ESCAPE" "kappa.qtt.borrow-escape" sp
      "a closure capturing a borrowed binding escapes through the result (§12.3.2)"
  where
    paramBind (b, ms) = case bName b of
      Nothing -> pure Nothing
      Just n -> do
        let BinderPrefix mq mb = bPrefix b
            BinderPrefix sq sb = maybe emptyPrefix bPrefix ms
            q = mq `orElse` sq
            mark = mb `orElse` sb
            anon = mark == Just (BorrowMark Nothing)
        k <- freshKey (nameText n)
        pure (Just (nameText n, VInfo k q (isJust mark) anon Nothing (bSpan b)))
    orElse (Just x) _ = Just x
    orElse Nothing y = y

-- | §18.9.3: an @inout@ parameter must be threaded back through the
-- declared result as a record field of the same name.
checkInoutResult :: Maybe Expr -> LetDef -> M ()
checkInoutResult msig ld =
  forM_ [b | b <- ldBinders ld, bInout b, Just _ <- [bName b]] $ \b -> do
    let nm = maybe "" nameText (bName b)
        resTy = ldResultType ld `orElse` (sigResult <$> msig)
    forM_ resTy $ \ty ->
      unless (threadsField nm (unwrapIO ty)) $
        emit "E_QTT_INOUT_THREADED_FIELD_MISSING" "kappa.qtt.inout-threading" (bSpan b)
          ("the result type does not thread the inout place '" <> nm <> "' back as a field (§18.9.3)")
  where
    orElse (Just x) _ = Just x
    orElse Nothing y = y
    sigResult e = case sigBinders e of
      [] -> e
      _ -> dropBinders e
    dropBinders = \case
      EForall _ body _ -> dropBinders body
      ETraitArrow _ body -> dropBinders body
      EArrow _ body -> dropBinders body
      e -> e
    unwrapIO = \case
      EApp (EVar hd) args
        | nameText hd `elem` ["IO", "UIO"]
        , (a : _) <- reverse [e | ArgExplicit e <- args] ->
            a
      e -> e
    threadsField nm = \case
      ERecordType fs _ _ -> nm `elem` map (nameText . rtfName) fs
      EAscription (EVar n) _ _ -> nameText n == nm
      ETuple {} -> True -- positional threading is not modelled
      _ -> False

-- | Close one binding's scope: enforce its quantity interval.
closeVar :: VInfo -> Usage -> M ()
closeVar vi u = do
  let Cnt _ hi occs tlo = Map.findWithDefault zeroC (vKey vi) u
  case vQ vi of
    Just QOne -> do
      when (hi > 1) (overuse occs)
      when (tlo < 1 && hi <= 1) (dropErr "linear")
    Just QAtLeastOne -> when (tlo < 1) (dropErr "relevant")
    Just QAtMostOne -> when (hi > 1) (overuse occs)
    _ -> pure ()
  where
    nm = T.takeWhile (/= '#') (vKey vi)
    overuse occs =
      emit "E_QTT_LINEAR_OVERUSE" "kappa.qtt.linear-overuse"
        (occAt occs)
        ("'" <> nm <> "' is used more often than its quantity permits (§12.2)")
    occAt occs = case drop 1 occs of
      (sp : _) -> sp
      [] -> vSpan vi
    dropErr kind =
      emit "E_QTT_LINEAR_DROP" "kappa.qtt.linear-drop" (vSpan vi)
        ("'" <> nm <> "' (" <> kind <> ") may be dropped without being consumed (§12.2.5)")

-- ── Expression walk ──────────────────────────────────────────────────

walkE :: Env -> Expr -> M (Usage, Maybe Span)
walkE env@(vars, _) e0 = case e0 of
  EVar n -> case Map.lookup (nameText n) vars of
    Just vi -> do
      when (vQ vi == Just QZero) $
        emit "E_QTT_ERASED_RUNTIME_USE" "kappa.qtt.erased-use" (nameSpan n)
          ("erased (quantity 0) binding '" <> nameText n <> "' is used at runtime (§12.2.1)")
      pure (Map.singleton (vKey vi) (oneC (nameSpan n)), vTaint vi)
    Nothing -> pure (Map.empty, Nothing)
  EHole {} -> none
  EIntLit {} -> none
  EFloatLit {} -> none
  EStringLit _ parts _ -> seqWalk [ipExpr p | p <- parts]
  EUnit {} -> none
  ETuple es _ -> seqWalk es
  ERecordLit items _ -> seqWalk [v | RecItem _ _ (Just v) <- items]
  EApp f args -> walkApp env f args
  EDot (EVar n) _
    | Just vi <- Map.lookup (nameText n) vars ->
        -- a field projection touches a disjoint path of the root, not
        -- the whole binding (§12.3.3 path-sensitive footprints)
        pure (Map.singleton (vKey vi) touchC, Nothing)
  EDot b _ -> walkE env b
  EQDot b _ -> walkE env b
  ERecordPatch b items _ ->
    walks (b : concatMap patchExprs items)
  ESectionLeft l _ _ -> walkE env l
  ESectionRight _ r _ -> walkE env r
  EOpRef {} -> none
  EElvis l r _ -> walks [l, r]
  ELambda _ bs body sp -> do
    bound <- catMaybes <$> mapM lamBind bs
    let env' = (foldr (uncurry Map.insert) vars bound, snd env)
    (u, t) <- walkE env' body
    forM_ bound $ \(_, vi) -> closeVar vi u
    let u' = foldr (Map.delete . vKey . snd) u bound
        anonKeys = [vKey vi | vi <- Map.elems vars, vAnonBorrow vi]
        captured =
          or [cTouch c | (k, c) <- Map.toList u', k `elem` anonKeys]
    pure (u', if captured || isJust t then Just sp else Nothing)
  ELet binds body _ -> do
    (u1, bound) <- walkBinds env binds
    let env' = (foldr (uncurry Map.insert) vars bound, snd env)
    (u2, t) <- walkE env' body
    forM_ bound $ \(_, vi) -> closeVar vi u2
    pure (u1 `seqU` foldr (Map.delete . vKey . snd) u2 bound, t)
  EBlock decls mres _ -> do
    binds <- declsToBinds decls
    walkE env (ELet binds (fromMaybe (EUnit (exprSpan e0)) mres) (exprSpan e0))
  EDo _ items _ -> walkItems env items
  EIf alts mels _ -> do
    condsU <- mapM (fmap fst . walkE env . fst) alts
    branches <- mapM (walkE env . snd) alts
    melsR <- traverse (walkE env) mels
    let bs = map fst branches ++ [maybe Map.empty fst melsR]
        taints = mapMaybe snd branches ++ catMaybes [snd =<< melsR]
    pure (foldr seqU (altUs bs) condsU, firstJust taints)
  EMatch scrut cases _ -> do
    (us, ts) <- walkMatch env scrut cases
    pure (us, ts)
  ETry {} -> bailOut >> none
  ETryMatch {} -> bailOut >> none
  EHandle {} -> bailOut >> none
  EIs b _ -> walkE env b
  EThunk b _ -> walkE env b
  ELazy b _ -> walkE env b
  EForce b _ -> walkE env b
  ESeal {} -> bailOut >> none
  EOpenExists {} -> bailOut >> none
  ESealExists {} -> bailOut >> none
  EListLit es _ -> seqWalk es
  ESetLit es _ -> seqWalk es
  EMapLit kvs _ -> seqWalk (concatMap (\(k, v) -> [k, v]) kvs)
  EComprehension {} -> bailOut >> none
  EArrow {} -> none -- type position: erased
  ERecordType {} -> none
  EForall {} -> none
  EExists {} -> none
  ETraitArrow {} -> none
  EEffRow {} -> none
  EVariant arms _ _ -> seqWalk (map vaExpr arms)
  EOptionSugar {} -> none
  EAscription b _ _ -> walkE env b
  ECaptures b _ _ -> walkE env b
  EBang b _ -> walkE env b
  EQuote {} -> bailOut >> none
  ESplice {} -> bailOut >> none
  EImpossible {} -> none
  EKindQualified {} -> none
  EModuleSig {} -> none
  EQuotedLit {} -> none
  EReceiverSection {} -> bailOut >> none
  EOpChain {} -> bailOut >> none -- resolver output should not contain chains
  where
    none = pure (Map.empty, Nothing)
    walks es = do
      rs <- mapM (walkE env) es
      pure (foldr (seqU . fst) Map.empty rs, firstJust (mapMaybe snd rs))
    seqWalk = walks
    patchExprs = \case
      PatchUpdate _ (PatchValue v) -> [v]
      PatchExtend _ v -> [v]
      PatchSection _ v -> [v]
    lamBind b = case bName b of
      Nothing -> pure Nothing
      Just n -> do
        let BinderPrefix mq mb = bPrefix b
        k <- freshKey (nameText n)
        pure (Just (nameText n, VInfo k mq (isJust mb) (mb == Just (BorrowMark Nothing)) Nothing (bSpan b)))
    walkMatch envM scrut cases = do
      (su, _) <- walkE envM scrut
      rs <- mapM (walkCase envM) [c | c@MatchCase {} <- cases]
      pure (su `seqU` altUs (map fst rs), firstJust (mapMaybe snd rs))
    walkCase (vsM, fsM) (MatchCase pat mguard body csp) = do
      when (hasActive pat) bailOut
      shadow <- mapM (\nm -> (,) nm . (\k -> VInfo k Nothing False False Nothing csp) <$> freshKey nm) (patVars pat)
      let envC = (foldr (uncurry Map.insert) vsM shadow, fsM)
      gu <- maybe (pure Map.empty) (fmap fst . walkE envC) mguard
      (bu, t) <- walkE envC body
      pure (gu `seqU` bu, t)
    walkCase _ (MatchImpossible _) = pure (Map.empty, Nothing)
    hasActive = \case
      PActive {} -> True
      PAs _ p -> hasActive p
      PCtor _ ps _ -> any hasActive ps
      PCtorNamed _ fs _ -> any hasActive [p | (_, Just p) <- fs]
      PTuple ps _ -> any hasActive ps
      PRecord fs _ _ -> any hasActive [p | (_, _, Just p) <- fs]
      PTyped p _ _ -> hasActive p
      POr ps _ -> any hasActive ps
      POpChain p chain _ -> hasActive p || any (hasActive . snd) chain
      _ -> False

firstJust :: [Span] -> Maybe Span
firstJust (s : _) = Just s
firstJust [] = Nothing

-- ── Applications ─────────────────────────────────────────────────────

walkApp :: Env -> Expr -> [Arg] -> M (Usage, Maybe Span)
walkApp env@(vars, fns) f args = do
  (fu, _ft) <- walkE env f
  let params = case f of
        EVar n
          | not (Map.member (nameText n) vars) ->
              Map.findWithDefault [] (nameText n) fns
        _ -> []
      named = or [True | ArgNamedBlock {} <- args]
      ps = (if named then [] else params) ++ repeat defaultP
  rs <- sequence (zipWith (walkArg env) args ps)
  -- a callee neither stores nor returns its tainted callees/arguments
  -- in general; only result-carrying lifts propagate the taint
  let liftLike = case f of
        EVar n -> nameText n `elem` ["pure", "ioPure", "return"]
        _ -> False
      taint
        | liftLike = firstJust (mapMaybe snd rs)
        | otherwise = Nothing
  pure (foldr (seqU . fst) fu rs, taint)

walkArg :: Env -> Arg -> PInfo -> M (Usage, Maybe Span)
walkArg env@(vars, _) arg p = case arg of
  ArgImplicit _ -> pure (Map.empty, Nothing) -- erased position (§12.2.1)
  ArgNamedBlock items _ -> do
    rs <- mapM (walkE env) [fromMaybe (EVar n) me | (n, me) <- items]
    pure (foldr (seqU . fst) Map.empty rs, firstJust (mapMaybe snd rs))
  ArgInout e sp
    | pInout p -> borrowish e
    | hasDemand -> do
        emit "E_QTT_INOUT_MARKER_UNEXPECTED" "kappa.qtt.inout-marker" sp
          "call-site '~' marker on an argument whose parameter is not declared inout (§18.9.3)"
        walkE env e
    | otherwise -> borrowish e
  ArgExplicit e
    | pInout p -> do
        emit "E_QTT_INOUT_MARKER_REQUIRED" "kappa.qtt.inout-marker" (exprSpan e)
          "this argument flows into an inout parameter and must be marked '~place' (§18.9.3)"
        walkE env e
    | pQuantity p == Just QZero -> pure (Map.empty, Nothing) -- erased argument
    | pBorrow p -> borrowish e
    | consuming, EVar n <- e, Just vi <- Map.lookup (nameText n) vars, vBorrowed vi -> do
        emit "E_QTT_BORROW_CONSUME" "kappa.qtt.borrow-consume" (nameSpan n)
          ("borrowed binding '" <> nameText n <> "' cannot be consumed by a quantity-1 parameter (§12.3.1)")
        pure (Map.singleton (vKey vi) touchC, Nothing)
    | otherwise -> walkE env e
  where
    hasDemand = isJust (pQuantity p) || pBorrow p
    consuming = pQuantity p `elem` [Just QOne, Just QAtLeastOne]
    borrowish e = case e of
      EVar n
        | Just vi <- Map.lookup (nameText n) vars ->
            pure (Map.singleton (vKey vi) touchC, Nothing)
      -- borrowing a projection path touches its root only
      EDot (EVar n) _
        | Just vi <- Map.lookup (nameText n) vars ->
            pure (Map.singleton (vKey vi) touchC, Nothing)
      _ -> walkE env e

-- ── Bindings and do items ────────────────────────────────────────────

-- | Walk a let-group's right-hand sides; returns their usage plus the
-- tracked bindings the group introduces.
walkBinds :: Env -> [LetBind] -> M (Usage, [(Text, VInfo)])
walkBinds env binds = go env binds
  where
    go _ [] = pure (Map.empty, [])
    go envc@(vs, fs) (LetBind _ prefix pat _ rhs bsp : rest) = do
      (u, taint) <- case (pat, rhs) of
        -- a wildcard discard of a bare binding is not a use (§12.2.4)
        (PWild _, EVar n)
          | Map.member (nameText n) vs -> pure (Map.empty, Nothing)
        _ -> walkE envc rhs
      let BinderPrefix mq mb = prefix
          borrowed = isJust mb
          anon = mb == Just (BorrowMark Nothing)
          names = patVars pat
          single = length names == 1
          mk nm = do
            k <- freshKey nm
            pure
              ( nm
              , VInfo k
                  (if single then mq else Nothing)
                  borrowed
                  anon
                  (if single then taint else Nothing)
                  bsp
              )
      -- every pattern name is bound (untracked entries still shadow
      -- outer bindings); only prefixed/tainted ones carry checks
      bound <- mapM mk names
      (u2, bound2) <- go (foldr (uncurry Map.insert) vs bound, fs) rest
      pure (u `seqU` u2, bound ++ bound2)

patVars :: Pattern -> [Text]
patVars = \case
  PVar n -> [nameText n]
  PAs n p -> nameText n : patVars p
  PCtor _ ps _ -> concatMap patVars ps
  PCtorNamed _ fs _ -> concatMap patVars [p | (_, Just p) <- fs]
  PTuple ps _ -> concatMap patVars ps
  PRecord fs rest _ ->
    concatMap patVars [p | (_, _, Just p) <- fs]
      ++ [nameText f | (_, f, Nothing) <- fs]
      ++ [nameText n | Just (PatRestBind n) <- [rest]]
  PTyped p _ _ -> patVars p
  POr ps _ -> concatMap patVars ps
  POpChain p chain _ -> patVars p ++ concatMap (patVars . snd) chain
  PVariant mb _ _ mrest _ ->
    [nameText n | Just n <- [mb]] ++ [nameText n | Just n <- [mrest]]
  _ -> []

declsToBinds :: [Decl] -> M [LetBind]
declsToBinds [] = pure []
declsToBinds (d : ds) = case d of
  DLet _ (LetDef (Just n) Nothing _ [] _ Nothing body) sp ->
    (LetBind False emptyPrefix (PVar n) Nothing body sp :) <$> declsToBinds ds
  DLet _ (LetDef Nothing (Just pat) brw [] _ Nothing body) sp ->
    (LetBind False (BinderPrefix Nothing (if brw then Just (BorrowMark Nothing) else Nothing)) pat Nothing body sp :) <$> declsToBinds ds
  DSig {} -> declsToBinds ds
  _ -> bailOut >> pure []

-- | Walk a do-scope; sequential items, branch joins for statement-ifs,
-- loop bodies may run zero times. The returned taint is the do result's
-- (its final expression or any @return@), used for escape detection.
walkItems :: Env -> [DoItem] -> M (Usage, Maybe Span)
walkItems env0 items0 = do
  (u, t, bound) <- go env0 items0
  forM_ bound $ \(_, vi) -> closeVar vi u
  pure (foldr (Map.delete . vKey . snd) u bound, t)
  where
    go _ [] = pure (Map.empty, Nothing, [])
    go env@(vs, fs) (item : rest) = case item of
      DoExpr e -> do
        (u, t) <- walkE env e
        (u2, t2, bound) <- go env rest
        -- the final statement's value escapes the do-scope: report the
        -- escape at that statement, not at the closure formation
        let tn = if null rest then (exprSpan e <$ t) else t2
        pure (u `seqU` u2, tn, bound)
      DoLet lb -> bindLike env lb rest
      DoBind lb -> bindLike env lb rest
      DoUsing pat rhs sp ->
        -- §19.5: the bound resource is borrowed for the rest of scope
        bindLike env (LetBind False (BinderPrefix Nothing (Just (BorrowMark Nothing))) pat Nothing rhs sp) rest
      DoLetQ pat rhs mElse _ -> do
        (u, _) <- walkE env rhs
        eu <- case mElse of
          Just (_, fe) -> fst <$> walkE env fe
          Nothing -> pure Map.empty
        let env' = (foldr (\nm -> Map.delete nm) vs (patVars pat), fs)
        (u2, t2, bound) <- go env' rest
        pure (u `seqU` eu `seqU` u2, t2, bound)
      DoVar n rhs _ -> do
        (u, _) <- walkE env rhs
        let env' = (Map.delete (nameText n) vs, fs)
        (u2, t2, bound) <- go env' rest
        pure (u `seqU` u2, t2, bound)
      DoAssign _ _ rhs _ -> do
        (u, _) <- walkE env rhs
        (u2, t2, bound) <- go env rest
        pure (u `seqU` u2, t2, bound)
      DoReturn _ me _ -> do
        (u, t) <- maybe (pure (Map.empty, Nothing)) (walkE env) me
        (u2, t2, bound) <- go env rest
        pure (u `seqU` u2, firstJust (catMaybes [t, t2]), bound)
      DoBreak {} -> go env rest
      DoContinue {} -> go env rest
      DoWhile _ cond body mels _ -> do
        (cu, _) <- walkE env cond
        (bu, _, _) <- scope env body
        eu <- maybe (pure Map.empty) (fmap fst3 . scope env) mels
        (u2, t2, bound) <- go env rest
        pure (cu `seqU` loopU bu `seqU` eu `seqU` u2, t2, bound)
      DoFor _ pat src body mels _ -> do
        (su, _) <- walkE env src
        let env' = (foldr Map.delete vs (patVars pat), fs)
        (bu, _, _) <- scope env' body
        eu <- maybe (pure Map.empty) (fmap fst3 . scope env) mels
        (u2, t2, bound) <- go env rest
        pure (su `seqU` loopU bu `seqU` eu `seqU` u2, t2, bound)
      DoIf alts mels _ -> do
        cus <- mapM (fmap fst . walkE env . fst) alts
        bs <- mapM (fmap fst3 . scope env . snd) alts
        eb <- maybe (pure Map.empty) (fmap fst3 . scope env) mels
        (u2, t2, bound) <- go env rest
        pure (foldr seqU (altUs (bs ++ [eb])) cus `seqU` u2, t2, bound)
      DoDefer _ e _ -> do
        (u, _) <- walkE env e
        (u2, t2, bound) <- go env rest
        pure (u `seqU` u2, t2, bound)
      DoDecl d -> do
        lbs <- declsToBinds [d]
        case lbs of
          [lb] -> bindLike env lb rest
          _ -> go env rest
      where
        fst3 (x, _, _) = x
        scope envc its = go envc its
        bindLike envc@(vs', fs') lb@(LetBind {}) restItems = do
          (u, bound) <- walkBinds envc [lb]
          let env' = (foldr (uncurry Map.insert) vs' bound, fs')
          (u2, t2, bound2) <- go env' restItems
          pure (u `seqU` u2, t2, bound ++ bound2)
