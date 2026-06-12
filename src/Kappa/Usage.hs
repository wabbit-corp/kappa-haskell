-- | Quantity-and-borrow usage analysis (Spec §12.2–§12.4).
--
-- A post-elaboration pass over the resolved surface module. Each named
-- definition body is walked once, computing for every tracked binding a
-- usage interval [lo, hi] (sequential composition adds, branch joins
-- take min\/max, §12.2.2) plus borrow\/escape facts:
--
--   * @1@ / @>=1@ bindings unused on some completion path
--     (§12.2.5)                                   → E_QTT_LINEAR_DROP
--   * @1@ / @<=1@ bindings used more than once    → E_QTT_LINEAR_OVERUSE
--   * @0@ bindings referenced at runtime          → E_QTT_ERASED_RUNTIME_USE
--   * borrowed bindings moved into a consuming
--     (quantity @1@\/@>=1@) parameter             → E_QTT_BORROW_CONSUME
--   * closures\/thunks capturing borrowed bindings
--     escaping through the definition's result    → E_QTT_BORROW_ESCAPE
--   * consuming a place while a live borrow of an
--     overlapping path exists (§12.4)             → E_QTT_BORROW_OVERLAP
--   * call-site @~place@ markers against the
--     callee's @inout@ parameters (§18.9.3)       → E_QTT_INOUT_MARKER_*
--   * @inout@ parameters whose declared result
--     does not thread the place back as a field   → E_QTT_INOUT_THREADED_FIELD_MISSING
--   * abrupt control flow escaping a deferred
--     action (§18.7)                              → E_DEFER_ABRUPT_CONTROL
--
-- Demand scaling (§12.2.1–§12.2.2): an argument occurrence is counted at
-- the callee parameter's demand interval, so a relevant binding passed
-- to an affine or unrestricted parameter fails its positive lower bound
-- and a linear binding passed to an unrestricted parameter fails its
-- upper bound. Closure-shaped values (lambdas, thunks, @lazy@,
-- operator\/receiver sections) carry their captured usage as a /latent/
-- multiset that is multiplied by the consumer's demand (§16.2.1):
-- exactly-once for an immediate call or a quantity-1 slot, zero-or-more
-- for an unrestricted slot, zero for an unused binding.
--
-- Record paths (§12.4): projecting a quantity-1 field out of a tracked
-- record consumes that path; the path can be restored by a record patch,
-- while a patch consumes the residue (and any moved-but-unpatched linear
-- path counts as reused). A @let &@ borrow of a path locks every
-- overlapping path for the binder's lexical scope.
--
-- The analysis is deliberately conservative: only bindings with explicit
-- quantity prefixes (or parameters claiming erased signature binders, or
-- projections of quantity-1 fields) are counted, parameter demand comes
-- from same-module signatures, and a definition containing constructs
-- outside the modelled subset is skipped entirely rather than misjudged.
module Kappa.Usage
  ( usageDiagnostics
  ) where

import Control.Monad (forM, forM_, unless, when)
import Control.Monad.State.Strict (State, execState, gets, modify')
import Data.List (find, isPrefixOf)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes, fromMaybe, isJust, mapMaybe, maybeToList)
import Data.Text (Text)
import qualified Data.Text as T
import Kappa.Diagnostic
import Kappa.Source (Span)
import Kappa.Syntax

-- ── Tables ───────────────────────────────────────────────────────────

-- | Demand a callee places on one explicit argument position.
data PInfo = PInfo
  { pName :: !(Maybe Text)
  , pQuantity :: !(Maybe Quantity)
  , pBorrow :: !Bool
  , pInout :: !Bool
  , pKnown :: !Bool -- ^ from a same-module signature (vs. assumed)
  }

defaultP :: PInfo
defaultP = PInfo Nothing Nothing False False False

-- | Demand interval of a parameter (§12.2.1); 'Nothing' upper = ω.
pDemand :: PInfo -> (Int, Maybe Int)
pDemand p = case pQuantity p of
  Just QOne -> (1, Just 1)
  Just QAtMostOne -> (0, Just 1)
  Just QAtLeastOne -> (1, Nothing)
  Just QZero -> (0, Just 0)
  Just QOmega
    | pKnown p -> (0, Nothing)
    | otherwise -> (1, Just 1)
  Just (QTerm _) -> (1, Just 1) -- symbolic: assume exactly-once
  Nothing
    | pKnown p -> (0, Nothing) -- known unrestricted parameter
    | otherwise -> (1, Just 1) -- unknown callee: assume exactly-once

-- | One tracked binding in scope.
data VInfo = VInfo
  { vKey :: !Text -- ^ unique usage-map key (shadowing-safe)
  , vQ :: !(Maybe Quantity) -- ^ counted quantity (@1@, @<=1@, @>=1@, @0@)
  , vBorrowed :: !Bool
  , vAnonBorrow :: !Bool -- ^ anonymous @&@ borrow: capture may not escape
  , vUsing :: !Bool -- ^ @using@-scoped resource: may not escape itself (§19.5)
  , vTaint :: !(Maybe Span) -- ^ closure capturing a borrow, formed here
  , vLatent :: !Usage -- ^ per-call captured usage (closure-valued bindings)
  , vFields :: ![(Text, Maybe Quantity)] -- ^ record fields, when known
  , vSpan :: !Span -- ^ binding site (drop reports)
  }

plainV :: Text -> Span -> VInfo
plainV k sp = VInfo k Nothing False False False Nothing Map.empty [] sp

-- | The taint a bare occurrence of the binding carries: a closure that
-- captured a borrow, or a @using@-scoped resource escaping itself.
vEscape :: VInfo -> Span -> Maybe Span
vEscape vi sp
  | Just t <- vTaint vi = Just t
  | vUsing vi = Just sp
  | otherwise = Nothing

-- | Quantity-1 field names of a tracked record binding (§12.4).
linFields :: VInfo -> [Text]
linFields vi = [f | (f, Just QOne) <- vFields vi]

-- | Usage interval of one binding plus reporting metadata: move lo\/hi,
-- chronological move occurrences, touch lower bound (touches include
-- borrow-uses; a binding is dropped iff some path never touches it).
data Cnt = Cnt !Int !Int ![Span] !Int

cHi :: Cnt -> Int
cHi (Cnt _ b _ _) = b

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

-- | Upper bound standing in for ω in scaled intervals.
wInf :: Int
wInf = 1000000

-- | Multiply a usage interval by a demand interval (§12.2.2, §16.2.1).
scaleC :: (Int, Maybe Int) -> Cnt -> Cnt
scaleC (lo, hi) (Cnt a b o t) =
  Cnt
    (min wInf (lo * a))
    b'
    (if b' > b then o ++ o else o)
    (if lo == 0 then 0 else t)
  where
    b' = case hi of
      Nothing -> if b > 0 then wInf else 0
      Just h -> min wInf (h * b)

type Usage = Map Text Cnt

scaleU :: (Int, Maybe Int) -> Usage -> Usage
scaleU d = Map.map (scaleC d)

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

data Env = Env
  { eVars :: !(Map Text VInfo)
  , eFns :: !(Map Text [PInfo])
  , eBorrows :: ![(Text, [Text])] -- ^ live lexical borrows: root key, path
  , eAliases :: !(Map Text [(Text, Maybe Quantity)])
  , eCtors :: !(Map Text [(Text, [Maybe Quantity])])
  -- ^ ctor name → all sibling ctors of its data type with field quantities
  }

bindVars :: [(Text, VInfo)] -> Env -> Env
bindVars bs env = env {eVars = foldr (uncurry Map.insert) (eVars env) bs}

addBorrows :: [(Text, [Text])] -> Env -> Env
addBorrows bs env = env {eBorrows = bs ++ eBorrows env}

-- | Walk result: immediate usage, escape taint, latent per-call usage.
data R = R
  { rU :: !Usage
  , rT :: !(Maybe Span)
  , rL :: !Usage
  }

rPlain :: Usage -> R
rPlain u = R u Nothing Map.empty

rNone :: R
rNone = rPlain Map.empty

-- | Fold latent usage in at exactly-once consumption.
flatR :: R -> (Usage, Maybe Span)
flatR r = (rU r `seqU` rL r, rT r)

-- ── Entry point ──────────────────────────────────────────────────────

-- | Analyze a resolved module; returns the §12.2–§12.4 usage
-- diagnostics for its named definitions.
usageDiagnostics :: Module -> [Diagnostic]
usageDiagnostics m = concatMap analyzeDecl lets
  where
    decls = modDecls m
    sigs = Map.fromList [(nameText n, ty) | DSig _ n ty _ <- decls]
    lets = [ld | DLet _ ld _ <- decls, Just _ <- [ldName ld]]
    aliases =
      Map.fromList
        [ (nameText n, fieldsOf rhs)
        | DTypeAlias _ n [] _ (Just rhs) _ <- decls
        , ERecordType {} <- [rhs]
        ]
    fieldsOf (ERecordType fs _ _) =
      [(nameText (rtfName f), bpQuantity (rtfPrefix f)) | f <- fs]
    fieldsOf _ = []
    ctors =
      Map.fromList
        [ (nameText (cdName c), siblings)
        | DData _ dd _ <- decls
        , let siblings =
                [ ( nameText (cdName c')
                  , [bpQuantity (bPrefix b) | b <- cdBinders c']
                  )
                | c' <- ddCtors dd
                ]
        , c <- ddCtors dd
        ]
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
          final = execState (analyzeLet fns aliases ctors sigTy ld) (S [] False 0)
       in if sBail final then [] else reverse (sDiags final)

-- Callee demand for prelude helpers the fixtures rely on.
builtinFns :: Map Text [PInfo]
builtinFns =
  Map.fromList
    [ ("unsafeConsume", [PInfo Nothing (Just QOne) False False True])
    ]

-- | Resolve a (possibly aliased) record type to its field list.
resolveFields :: Map Text [(Text, Maybe Quantity)] -> Expr -> [(Text, Maybe Quantity)]
resolveFields aliases = go
  where
    go = \case
      ERecordType fs _ _ ->
        [(nameText (rtfName f), bpQuantity (rtfPrefix f)) | f <- fs]
      EVar n -> Map.findWithDefault [] (nameText n) aliases
      EAscription e _ _ -> go e
      ECaptures e _ _ -> go e
      _ -> []

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
       in PInfo (nameText <$> bName b) mq (isJust mb) (bInout b) True
    mergeP (PInfo n1 q1 b1 i1 k1) (PInfo n2 q2 b2 i2 k2) =
      PInfo (n1 `orElse` n2) (q1 `orElse` q2) (b1 || b2) (i1 || i2) (k1 || k2)
    orElse (Just x) _ = Just x
    orElse Nothing y = y

-- ── Definition analysis ──────────────────────────────────────────────

analyzeLet ::
  Map Text [PInfo] ->
  Map Text [(Text, Maybe Quantity)] ->
  Map Text [(Text, [Maybe Quantity])] ->
  Maybe Expr ->
  LetDef ->
  M ()
analyzeLet fns aliases ctors msig ld = do
  let aligned = alignParams (ldBinders ld) (maybe [] sigBinders msig)
  binds <- catMaybes <$> mapM paramBind aligned
  let env = Env (Map.fromList binds) fns [] aliases ctors
  checkInoutResult msig ld
  r <- walkE env (ldBody ld)
  let (u, taint) = flatR r
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
            ty = bType b `orElse` (bType =<< ms)
            fields = maybe [] (resolveFields aliases) ty
        k <- freshKey (nameText n)
        pure (Just (nameText n, VInfo k q (isJust mark) anon False Nothing Map.empty fields (bSpan b)))
    orElse (Just x) _ = Just x
    orElse Nothing y = y

-- | §18.9.3: an @inout@ parameter must be threaded back through the
-- declared result as a record field of the same name.
checkInoutResult :: Maybe Expr -> LetDef -> M ()
checkInoutResult msig ld =
  forM_ inouts $ \(nm, bsp) -> do
    let resTy = ldResultType ld `orElse` (sigResult <$> msig)
    forM_ resTy $ \ty ->
      unless (threadsField nm (unwrapIO ty)) $
        emit "E_QTT_INOUT_THREADED_FIELD_MISSING" "kappa.qtt.inout-threading" bsp
          ("the result type does not thread the inout place '" <> nm <> "' back as a field (§18.9.3)")
  where
    -- a definition binder claims its signature binder's inout marker
    aligned = alignParams (ldBinders ld) (maybe [] sigBinders msig)
    inouts
      | null (ldBinders ld) =
          [ (nameText n, bSpan b)
          | b <- maybe [] sigBinders msig
          , bInout b
          , Just n <- [bName b]
          ]
      | otherwise =
          [ (nameText n, bSpan b)
          | (b, ms) <- aligned
          , bInout b || maybe False bInout ms
          , Just n <- [bName b `orElse` (bName =<< ms)]
          ]
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

-- | Close one binding's scope: enforce its quantity interval, including
-- per-path consumption of its quantity-1 record fields (§12.4).
closeVar :: VInfo -> Usage -> M ()
closeVar vi u = do
  let Cnt _ rHi rOccs rTlo = Map.findWithDefault zeroC (vKey vi) u
      res = Map.findWithDefault zeroC (vKey vi <> ".~") u
      rootHi = rHi + cHi res
  -- per-path overuse: a whole-record use re-consumes every moved path
  -- (a patch consumes the residue only, not the paths it replaces)
  pathOver <- fmap or . forM (linFields vi) $ \f -> do
    let pc@(Cnt _ pHi pOccs _) = Map.findWithDefault zeroC (vKey vi <> "." <> f) u
    if vQ vi `elem` [Just QOne, Just QAtMostOne] && cHi pc > 0 && rHi + pHi > 1
      then do
        overuse (nm <> "." <> f) (pOccs ++ rOccs)
        pure True
      else pure False
  case vQ vi of
    Just QOne -> do
      when (rootHi > 1) (overuse nm rOccs)
      when (rTlo < 1 && rootHi <= 1 && not pathOver) (dropErr "linear")
    Just QAtLeastOne -> when (rTlo < 1) (dropErr "relevant")
    Just QAtMostOne -> when (rootHi > 1) (overuse nm rOccs)
    _ -> pure ()
  where
    nm = T.takeWhile (/= '#') (vKey vi)
    overuse what occs =
      emit "E_QTT_LINEAR_OVERUSE" "kappa.qtt.linear-overuse"
        (occAt occs)
        ("'" <> what <> "' is used more often than its quantity permits (§12.2)")
    occAt occs = case drop 1 occs of
      (sp : _) -> sp
      [] -> vSpan vi
    dropErr kind =
      emit "E_QTT_LINEAR_DROP" "kappa.qtt.linear-drop" (vSpan vi)
        ("'" <> nm <> "' (" <> kind <> ") may be dropped without being consumed (§12.2.5)")

-- ── Place helpers (§12.4) ────────────────────────────────────────────

-- | A stable place rooted at a tracked binding: root info plus path.
placeOf :: Env -> Expr -> Maybe (VInfo, [Text], Span)
placeOf env = \case
  EVar n -> do
    vi <- Map.lookup (nameText n) (eVars env)
    pure (vi, [], nameSpan n)
  EDot b (DotName f) -> do
    (vi, path, _) <- placeOf env b
    pure (vi, path ++ [nameText f], nameSpan f)
  _ -> Nothing

pathsOverlap :: [Text] -> [Text] -> Bool
pathsOverlap a b = a `isPrefixOf` b || b `isPrefixOf` a

-- | Report a consuming use of @path@ under @vi@ while an overlapping
-- borrow is live (§12.4).
checkBorrowOverlap :: Env -> VInfo -> [Text] -> Span -> M ()
checkBorrowOverlap env vi path sp =
  when (any conflict (eBorrows env)) $
    emit "E_QTT_BORROW_OVERLAP" "kappa.qtt.borrow-overlap" sp
      ("'" <> T.takeWhile (/= '#') (vKey vi)
         <> T.concat (map ("." <>) path)
         <> "' is consumed while a live borrow of an overlapping path exists (§12.4)")
  where
    conflict (root, bpath) = root == vKey vi && pathsOverlap bpath path

-- | Usage of a consuming occurrence of a place (whole binding or a
-- quantity-1 field path), checked against live borrows.
movePlace :: Env -> VInfo -> [Text] -> Span -> M Usage
movePlace env vi path sp = do
  when (vQ vi == Just QZero) $
    emit "E_QTT_ERASED_RUNTIME_USE" "kappa.qtt.erased-use" sp
      ("erased (quantity 0) binding '" <> T.takeWhile (/= '#') (vKey vi) <> "' is used at runtime (§12.2.1)")
  checkBorrowOverlap env vi path sp
  pure $ case path of
    [] -> Map.singleton (vKey vi) (oneC sp)
    fs ->
      Map.fromList
        [ (vKey vi <> "." <> T.intercalate "." fs, oneC sp)
        , (vKey vi, touchC)
        ]

-- | Is the one-segment path a quantity-1 field of the binding?
isLinearPath :: VInfo -> [Text] -> Bool
isLinearPath vi [f] = f `elem` linFields vi
isLinearPath _ _ = False

-- ── Expression walk ──────────────────────────────────────────────────

walkE :: Env -> Expr -> M R
walkE env e0 = case e0 of
  EVar n -> case Map.lookup (nameText n) (eVars env) of
    Just vi -> do
      u <- movePlace env vi [] (nameSpan n)
      pure (R u (vEscape vi (nameSpan n)) (vLatent vi))
    Nothing -> pure rNone
  EHole {} -> pure rNone
  EIntLit {} -> pure rNone
  EFloatLit {} -> pure rNone
  EStringLit _ parts _ -> walks [ipExpr p | p <- parts]
  EUnit {} -> pure rNone
  ETuple es _ -> walks es
  ERecordLit items _ -> walks [v | RecItem _ _ (Just v) <- items]
  EApp f args -> walkApp env f args
  EDot {}
    | Just (vi, path, sp) <- placeOf env e0 ->
        if isLinearPath vi path
          then rPlain <$> movePlace env vi path sp
          else
            -- a non-linear field projection touches a disjoint path of
            -- the root, not the whole binding (§12.4)
            pure (rPlain (Map.singleton (vKey vi) touchC))
  EDot b _ -> walkE env b
  EQDot b _ -> walkE env b
  ERecordPatch b items _ -> walkPatch env b items (exprSpan e0)
  ESectionLeft l _ sp -> latentOf env l sp
  ESectionRight _ r sp -> latentOf env r sp
  EOpRef {} -> pure rNone
  EElvis l r _ -> walks [l, r]
  ELambda _ bs body sp -> do
    bound <- catMaybes <$> mapM (lamBind env) bs
    let env' = bindVars bound env
    r <- walkE env' body
    let (u, t) = flatR r
    forM_ bound $ \(_, vi) -> closeVar vi u
    let u' = foldr (Map.delete . vKey . snd) u bound
    taintLatent env u' t sp
  ELet binds body _ -> do
    (segs, env') <- walkBinds env binds
    R u2 t l2 <- walkE env' body
    let bodyU = u2 `seqU` l2
        sufs = drop 1 (scanr seqU bodyU [u | (u, _, _) <- segs])
    -- each binding is checked against everything sequenced after it
    forM_ (zip segs sufs) $ \((_, bound, _), suf) ->
      forM_ bound $ \(_, vi) -> closeVar vi suf
    let allBound = concat [bound | (_, bound, _) <- segs]
        del u = foldr (Map.delete . vKey . snd) u allBound
        u1 = foldr (\(u, _, _) acc -> u `seqU` acc) Map.empty segs
    pure (R (u1 `seqU` del u2) t (del l2))
  EBlock decls mres _ -> do
    binds <- declsToBinds decls
    walkE env (ELet binds (fromMaybe (EUnit (exprSpan e0)) mres) (exprSpan e0))
  EDo _ items _ -> do
    fl <- walkItems env items
    let paths = maybeToList (fU fl) ++ fRet fl ++ fBC fl
    pure (R (altUs paths) (fT fl) Map.empty)
  EIf alts mels _ -> do
    condsU <- mapM (fmap (fst . flatR) . walkE env . fst) alts
    branches <- mapM (fmap flatR . walkE env . snd) alts
    melsR <- traverse (fmap flatR . walkE env) mels
    let bs = map fst branches ++ [maybe Map.empty fst melsR]
        taints = mapMaybe snd branches ++ catMaybes [snd =<< melsR]
    pure ((rPlain (foldr seqU (altUs bs) condsU)) {rT = firstJust taints})
  EMatch scrut cases _ -> walkMatch env scrut cases
  ETry {} -> bailOut >> pure rNone
  ETryMatch {} -> bailOut >> pure rNone
  EHandle {} -> bailOut >> pure rNone
  EIs b _ -> walkE env b
  EThunk b sp -> suspend env b sp
  ELazy b sp -> suspend env b sp
  EForce b _ -> do
    r <- walkE env b
    let (u, t) = flatR r
    pure (R u t Map.empty)
  ESeal {} -> bailOut >> pure rNone
  EOpenExists {} -> bailOut >> pure rNone
  ESealExists {} -> bailOut >> pure rNone
  EListLit es _ -> walks es
  ESetLit es _ -> walks es
  EMapLit kvs _ -> walks (concatMap (\(k, v) -> [k, v]) kvs)
  EComprehension {} -> bailOut >> pure rNone
  EArrow {} -> pure rNone -- type position: erased
  ERecordType {} -> pure rNone
  EForall {} -> pure rNone
  EExists {} -> pure rNone
  ETraitArrow {} -> pure rNone
  EEffRow {} -> pure rNone
  EVariant arms _ _ -> walks (map vaExpr arms)
  EOptionSugar {} -> pure rNone
  EAscription b _ _ -> walkE env b
  ECaptures b _ _ -> walkE env b
  EBang b _ -> walkE env b
  EQuote {} -> bailOut >> pure rNone
  ESplice {} -> bailOut >> pure rNone
  EImpossible {} -> pure rNone
  EKindQualified {} -> pure rNone
  EModuleSig {} -> pure rNone
  EQuotedLit {} -> pure rNone
  EReceiverSection _ args sp -> do
    rs <- mapM (walkE env) [e | ArgExplicit e <- args]
    let (u, t) = foldr (\r (au, at) -> let (u', t') = flatR r in (u' `seqU` au, firstJust (catMaybes [t', at]))) (Map.empty, Nothing) rs
    taintLatent env u t sp
  EOpChain {} -> bailOut >> pure rNone -- resolver output should not contain chains
  where
    walks es = do
      rs <- mapM (walkE env) es
      let parts = map flatR rs
      pure ((rPlain (foldr (seqU . fst) Map.empty parts)) {rT = firstJust (mapMaybe snd parts)})
    -- a delayed computation: its body usage becomes latent, and it is
    -- tainted when it captures an anonymous borrow (§12.3.2)
    suspend envS b sp = do
      r <- walkE envS b
      let (u, t) = flatR r
      taintLatent envS u t sp
    -- shared by lambda/thunk/lazy/section formation
    taintLatent envS u t sp = do
      let anonKeys = [vKey vi | vi <- Map.elems (eVars envS), vAnonBorrow vi]
          captured = or [cTouch c | (k, c) <- Map.toList u, k `elem` anonKeys]
      pure (R Map.empty (if captured || isJust t then Just sp else Nothing) u)
    latentOf envS operand sp = do
      r <- walkE envS operand
      let (u, t) = flatR r
      taintLatent envS u t sp

firstJust :: [Span] -> Maybe Span
firstJust (s : _) = Just s
firstJust [] = Nothing

-- ── Lambda binders and matches ───────────────────────────────────────

lamBind :: Env -> Binder -> M (Maybe (Text, VInfo))
lamBind env b = case bName b of
  Nothing -> pure Nothing
  Just n -> do
    let BinderPrefix mq mb = bPrefix b
        fields = maybe [] (resolveFields (eAliases env)) (bType b)
    k <- freshKey (nameText n)
    pure
      ( Just
          ( nameText n
          , VInfo k mq (isJust mb) (mb == Just (BorrowMark Nothing)) False Nothing Map.empty fields (bSpan b)
          )
      )

walkMatch :: Env -> Expr -> [MatchCase] -> M R
walkMatch env scrut cases = do
  su <- fst . flatR <$> walkE env scrut
  let scrutV = case scrut of
        EVar n -> Map.lookup (nameText n) (eVars env)
        _ -> Nothing
  rs <- mapM (walkCase scrutV) [c | c@MatchCase {} <- cases]
  pure ((rPlain (su `seqU` altUs (map fst rs))) {rT = firstJust (mapMaybe snd rs)})
  where
    walkCase scrutV (MatchCase pat mguard body csp) = do
      when (hasActive pat) bailOut
      checkRecordRest scrutV pat csp
      shadow <- forM (patBindings scrutV pat) $ \(nm, mq) -> do
        k <- freshKey nm
        pure (nm, (plainV k csp) {vQ = mq})
      let envC = bindVars shadow env
      gu <- maybe (pure Map.empty) (fmap (fst . flatR) . walkE envC) mguard
      r <- walkE envC body
      let (bu, t) = flatR r
      forM_ shadow $ \(_, vi) -> closeVar vi bu
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

-- | Pattern-bound names, with quantity-1 fields of a tracked record
-- scrutinee inherited by the bindings that receive them (§12.4).
patBindings :: Maybe VInfo -> Pattern -> [(Text, Maybe Quantity)]
patBindings scrutV pat = case (scrutV, pat) of
  (Just vi, PRecord fs rest _) ->
    [ (nm, if fld `elem` linFields vi then Just QOne else Nothing)
    | (_, f, mp) <- fs
    , let fld = nameText f
    , nm <- case mp of
        Nothing -> [fld]
        Just (PVar x) -> [nameText x]
        Just p -> map fst (patBindings Nothing p)
    ]
      ++ [ (nameText n, if any (`notElem` named fs) (linFields vi) then Just QOne else Nothing)
         | Just (PatRestBind n) <- [rest]
         ]
  _ -> map (\nm -> (nm, Nothing)) (patVars pat)
  where
    named fs = [nameText f | (_, f, _) <- fs]

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

-- | A @..@ rest that silently discards a quantity-1 field of a tracked
-- record is a drop (§12.2.6, §12.4).
checkRecordRest :: Maybe VInfo -> Pattern -> Span -> M ()
checkRecordRest (Just vi) (PRecord fs (Just PatRestDiscard) _) csp = do
  let named = [nameText f | (_, f, _) <- fs]
      missing = [f | f <- linFields vi, f `notElem` named]
  forM_ missing $ \f ->
    emit "E_QTT_LINEAR_DROP" "kappa.qtt.linear-drop" csp
      ("the '..' rest pattern drops the quantity-1 field '" <> f <> "' (§12.2.6)")
checkRecordRest _ _ _ = pure ()

-- ── Record patches (§12.4) ───────────────────────────────────────────

walkPatch :: Env -> Expr -> [PatchItem] -> Span -> M R
walkPatch env base items sp = do
  vu <- walks (concatMap patchExprs items)
  bu <- case base of
    EVar n
      | Just vi <- Map.lookup (nameText n) (eVars env) -> do
          -- replacing patched paths conflicts with any live borrow of
          -- the record; the residue (and every moved-but-unpatched
          -- quantity-1 path) is consumed by the patch
          checkBorrowOverlap env vi [] sp
          let patched = concatMap patchLabels items
              reconsumed =
                [ (vKey vi <> "." <> f, oneC sp)
                | f <- linFields vi
                , f `notElem` patched
                ]
          pure $
            Map.fromList ((vKey vi <> ".~", oneC sp) : (vKey vi, touchC) : reconsumed)
    _ -> fst . flatR <$> walkE env base
  pure (rPlain (bu `seqU` vu))
  where
    patchExprs = \case
      PatchUpdate _ (PatchValue v) -> [v]
      PatchExtend _ v -> [v]
      PatchSection _ v -> [v]
    patchLabels = \case
      PatchUpdate ((_, n) : _) _ -> [nameText n]
      PatchUpdate [] _ -> []
      PatchExtend n _ -> [nameText n]
      PatchSection {} -> []
    walks es = do
      rs <- mapM (walkE env) es
      pure (foldr (seqU . fst . flatR) Map.empty rs)

-- ── Applications ─────────────────────────────────────────────────────

-- | Same-call facts for §12.4 disjointness: borrowed and consumed places.
data Fact
  = FBorrow !Text ![Text]
  | FMove !Text ![Text] !Span

argSpan :: Arg -> Span
argSpan = \case
  ArgExplicit e -> exprSpan e
  ArgImplicit e -> exprSpan e
  ArgNamedBlock _ sp -> sp
  ArgInout _ sp -> sp

walkApp :: Env -> Expr -> [Arg] -> M R
walkApp env f args = do
  hr <- walkE env f
  let (hu, _ht) = flatR hr -- an application calls its head exactly once
      params = case f of
        EVar n
          | not (Map.member (nameText n) (eVars env)) ->
              Map.findWithDefault [] (nameText n) (eFns env)
        _ -> []
      ps = params ++ repeat defaultP
  rs <- sequence (zipWith (walkArg env params) args ps)
  -- §12.4: places borrowed and consumed by the same call must be disjoint
  let facts = concatMap snd rs
      borrows = [(k, p) | FBorrow k p <- facts]
  forM_ facts $ \case
    FMove k p msp
      | any (\(bk, bp) -> bk == k && pathsOverlap bp p) borrows ->
          emit "E_QTT_BORROW_OVERLAP" "kappa.qtt.borrow-overlap" msp
            "a place is consumed by the same call that borrows an overlapping place (§12.4)"
    _ -> pure ()
  -- §18.11: a forked computation outlives the current scope, so its
  -- action may not touch an anonymous borrow
  let headName = case f of
        EVar n | not (Map.member (nameText n) (eVars env)) -> Just (nameText n)
        _ -> Nothing
      anonKeys = [vKey vi | vi <- Map.elems (eVars env), vAnonBorrow vi]
  when (headName == Just "fork") $
    forM_ (zip args (map fst rs)) $ \(a, r) ->
      when (any (`elem` anonKeys) (Map.keys (Map.filter cTouch (rU r `seqU` rL r)))) $
        emit "E_QTT_BORROW_ESCAPE" "kappa.qtt.borrow-escape" (argSpan a)
          "a forked computation may not capture an anonymous borrow (§12.3.2, §18.11)"
  -- a callee neither stores nor returns its tainted callees/arguments
  -- in general; only result-carrying lifts propagate the taint
  let liftLike = case f of
        EVar n -> nameText n `elem` ["pure", "ioPure", "return"]
        _ -> False
      taint
        | liftLike = firstJust (mapMaybe (rT . fst) rs)
        | otherwise = Nothing
  pure ((rPlain (foldr (seqU . rU . fst) hu rs)) {rT = taint})

walkArg :: Env -> [PInfo] -> Arg -> PInfo -> M (R, [Fact])
walkArg env params arg p = case arg of
  ArgImplicit _ -> pure (rNone, []) -- erased position (§12.2.1)
  ArgNamedBlock items _ -> do
    rs <- forM items $ \(n, me) -> do
      let np = fromMaybe defaultP (find ((== Just (nameText n)) . pName) params)
      walkArg env params (ArgExplicit (fromMaybe (EVar n) me)) np
    let r = (rPlain (foldr (seqU . rU . fst) Map.empty rs)) {rT = firstJust (mapMaybe (rT . fst) rs)}
    pure (r, concatMap snd rs)
  ArgInout e sp
    | pInout p -> borrowish e
    | hasDemand -> do
        emit "E_QTT_INOUT_MARKER_UNEXPECTED" "kappa.qtt.inout-marker" sp
          "call-site '~' marker on an argument whose parameter is not declared inout (§18.9.3)"
        (,[]) <$> walkE env e
    | otherwise -> borrowish e
  ArgExplicit e
    | pInout p -> do
        emit "E_QTT_INOUT_MARKER_REQUIRED" "kappa.qtt.inout-marker" (exprSpan e)
          "this argument flows into an inout parameter and must be marked '~place' (§18.9.3)"
        (,[]) <$> walkE env e
    | pQuantity p == Just QZero -> pure (rNone, []) -- erased argument
    | pBorrow p -> borrowish e
    | consuming
    , Just (vi, [], sp) <- placeOf env e
    , vBorrowed vi -> do
        emit "E_QTT_BORROW_CONSUME" "kappa.qtt.borrow-consume" sp
          ("borrowed binding '" <> T.takeWhile (/= '#') (vKey vi) <> "' cannot be consumed by a quantity-1 parameter (§12.3.1)")
        pure (rPlain (Map.singleton (vKey vi) touchC), [])
    -- a direct place argument is counted at the parameter's demand
    -- interval (§12.2.2); a definite consume is a move fact (§12.4)
    | Just (vi, path, sp) <- placeOf env e
    , null path || isLinearPath vi path -> do
        let d = pDemand p
        u <-
          if fst d >= 1
            then movePlace env vi path sp
            else pure (placeUse vi path sp)
        let latent = scaleU d (vLatent vi)
        -- a tainted closure binding may flow only into an at-most-once
        -- consuming position, like a directly written closure (§12.3.2)
        case vTaint vi of
          Just tsp
            | pKnown p
            , pQuantity p `notElem` [Just QOne, Just QAtMostOne] ->
                emit "E_QTT_BORROW_ESCAPE" "kappa.qtt.borrow-escape" tsp
                  "a closure capturing a borrowed binding flows into an unrestricted parameter (§12.3.2)"
          _ -> pure ()
        pure
          ( R (scaleU d u `seqU` latent) (vEscape vi sp) Map.empty
          , [FMove (vKey vi) path sp | fst d >= 1]
          )
    | otherwise -> do
        R u t l <- walkE env e
        let d = pDemand p
        -- a borrow-capturing closure may flow only into an
        -- at-most-once consuming position (§12.3.2); an unrestricted
        -- parameter may retain it beyond the borrow's scope
        case t of
          Just tsp
            | pKnown p
            , pQuantity p `notElem` [Just QOne, Just QAtMostOne] -> do
                emit "E_QTT_BORROW_ESCAPE" "kappa.qtt.borrow-escape" tsp
                  "a closure capturing a borrowed binding flows into an unrestricted parameter (§12.3.2)"
                pure (rPlain (u `seqU` scaleU d l), [])
          _ -> pure (R (u `seqU` scaleU d l) t Map.empty, [])
  where
    hasDemand = isJust (pQuantity p) || pBorrow p
    consuming = pQuantity p `elem` [Just QOne, Just QAtLeastOne]
    placeUse vi path sp =
      case path of
        [] -> Map.singleton (vKey vi) (oneC sp)
        fs ->
          Map.fromList
            [ (vKey vi <> "." <> T.intercalate "." fs, oneC sp)
            , (vKey vi, touchC)
            ]
    borrowish e = case placeOf env e of
      Just (vi, path, _) ->
        pure
          ( rPlain (Map.singleton (vKey vi) touchC)
          , [FBorrow (vKey vi) path]
          )
      Nothing -> (,[]) <$> walkE env e

-- ── Bindings and do items ────────────────────────────────────────────

-- | Walk a let-group's right-hand sides; returns one segment per
-- binding (its RHS usage, the tracked bindings it introduces, and the
-- borrows it opens) plus the fully-extended environment.
walkBinds :: Env -> [LetBind] -> M ([(Usage, [(Text, VInfo)], [(Text, [Text])])], Env)
walkBinds env binds = go env binds
  where
    go envc [] = pure ([], envc)
    go envc (LetBind _ prefix pat mty rhs bsp : rest) = do
      let BinderPrefix mq mb = prefix
          borrowed = isJust mb
          anon = mb == Just (BorrowMark Nothing)
          place = placeOf envc rhs
      (u, taint, latent, brs) <-
        if borrowed
          then case place of
            -- `let & v = p.f` opens a lexical borrow of the place: a
            -- non-consuming read that locks overlapping paths (§12.4)
            Just (vi, path, _) ->
              pure (Map.singleton (vKey vi) touchC, Nothing, Map.empty, [(vKey vi, path)])
            Nothing -> do
              r <- walkE envc rhs
              let (u', t') = flatR r
              pure (u', t', Map.empty, [])
          else case (pat, rhs) of
            -- a wildcard discard of a bare binding is not a use and
            -- never discharges a positive lower bound (§12.2.6)
            (PWild _, EVar n)
              | Map.member (nameText n) (eVars envc) -> pure (Map.empty, Nothing, Map.empty, [])
            _ -> do
              R u' t' l' <- walkE envc rhs
              pure (u', t', l', [])
      let names = patVars pat
          single = length names == 1
          -- a binding receiving a quantity-1 field projection inherits
          -- the field's linearity (§12.4)
          inherited = case place of
            Just (vi, path, _)
              | not borrowed, isLinearPath vi path -> Just QOne
            _ -> Nothing
          q = if single then mq `orElse` inherited else Nothing
          fields = maybe [] (resolveFields (eAliases envc)) mty
          mk nm = do
            k <- freshKey nm
            pure
              ( nm
              , VInfo k
                  q
                  borrowed
                  anon
                  False
                  (if single then taint else Nothing)
                  (if single then latent else Map.empty)
                  fields
                  bsp
              )
      -- every pattern name is bound (untracked entries still shadow
      -- outer bindings); only prefixed/tainted ones carry checks
      bound <- mapM mk names
      (segs, env') <- go (addBorrows brs (bindVars bound envc)) rest
      pure ((u, bound, brs) : segs, env')
    orElse (Just x) _ = Just x
    orElse Nothing y = y

declsToBinds :: [Decl] -> M [LetBind]
declsToBinds [] = pure []
declsToBinds (d : ds) = case d of
  DLet _ (LetDef (Just n) Nothing prefix [] _ Nothing body) sp ->
    (LetBind False prefix (PVar n) Nothing body sp :) <$> declsToBinds ds
  DLet _ (LetDef Nothing (Just pat) prefix [] mty Nothing body) sp ->
    (LetBind False prefix pat mty body sp :) <$> declsToBinds ds
  DSig {} -> declsToBinds ds
  _ -> bailOut >> pure []

-- | Control-flow result of a do-scope segment: fall-through usage
-- ('Nothing' when unreachable), result taint, and the usage of each
-- early-exit path (§12.2.5: positive lower bounds hold on every
-- completion path; break\/continue stop at the enclosing loop, returns
-- exit the do-scope).
data Flow = Flow
  { fU :: !(Maybe Usage)
  , fT :: !(Maybe Span)
  , fBC :: ![Usage]
  , fRet :: ![Usage]
  }

-- | Sequence a prefix usage before a segment's flow.
prefixFlow :: Usage -> Flow -> Flow
prefixFlow u (Flow mu t bc ret) =
  Flow ((u `seqU`) <$> mu) t (map (u `seqU`) bc) (map (u `seqU`) ret)

-- | All paths of a segment (fall-through plus early exits).
flowPaths :: Flow -> [Usage]
flowPaths fl = maybeToList (fU fl) ++ fBC fl ++ fRet fl

-- | Walk a do-scope; sequential items, branch joins for statement-ifs,
-- loop bodies may run zero times and every break\/continue\/return path
-- is a completion path of the bindings in scope. The returned taint is
-- the do result's (its final expression or any @return@), used for
-- escape detection.
walkItems :: Env -> [DoItem] -> M Flow
walkItems env0 items0 = go env0 items0
  where
    go _ [] = pure (Flow (Just Map.empty) Nothing [] [])
    go env (item : rest) = case item of
      DoExpr e -> do
        r <- walkE env e
        let (u, t) = flatR r
        fl <- go env rest
        let fl' = prefixFlow u fl
        -- the final statement's value escapes the do-scope: report the
        -- escape at that statement, not at the closure formation
        pure fl' {fT = if null rest then (exprSpan e <$ t) else fT fl'}
      DoLet lb -> bindLike env lb rest
      DoBind lb -> bindLike env lb rest
      DoUsing pat rhs sp -> do
        -- §19.5: the bound resource is borrowed for the rest of scope
        -- and may not itself escape the do-scope
        (segs, env') <- walkBinds env [LetBind False (BinderPrefix Nothing (Just (BorrowMark Nothing))) pat Nothing rhs sp]
        let bound = concat [b | (_, b, _) <- segs]
            u = foldr (\(su, _, _) acc -> su `seqU` acc) Map.empty segs
            markUsing = foldr (\(nm, _) -> Map.adjust (\vi -> vi {vUsing = True}) nm) (eVars env') bound
        fl <- go env' {eVars = markUsing} rest
        forM_ bound $ \(_, vi) -> closeVar vi (altUs (flowPaths fl))
        pure (prefixFlow u fl)
      DoLetQ pat rhs mElse sp -> do
        u <- fst . flatR <$> walkE env rhs
        -- the else handler is an alternative completion path (§18.2)
        eu <- case mElse of
          Just (rp, fe) -> do
            shadow <- shadowVars (patVars rp) sp
            Just . fst . flatR <$> walkE (bindVars shadow env) fe
          Nothing -> do
            -- a plain let? silently discards the residual alternatives;
            -- a residue carrying a positive-lower-bound field may not be
            -- dropped that way (§12.2.5, §18.2)
            forM_ (residueLinear env pat) $ \cn ->
              emit "E_QTT_LINEAR_DROP" "kappa.qtt.linear-drop" sp
                ("the residual constructor '" <> cn <> "' carries a quantity-1 or relevant field; a plain let? may not discard it (§12.2.5)")
            pure Nothing
        shadow <- shadowVars (patVars pat) sp
        fl <- go (bindVars shadow env) rest
        let fl' = prefixFlow u fl
        pure fl' {fRet = maybeToList eu ++ fRet fl'}
      DoVar n rhs _ -> do
        u <- fst . flatR <$> walkE env rhs
        shadowK <- freshKey (nameText n)
        let env' = bindVars [(nameText n, plainV shadowK (nameSpan n))] env
        prefixFlow u <$> go env' rest
      DoAssign _ _ rhs _ -> do
        u <- fst . flatR <$> walkE env rhs
        prefixFlow u <$> go env rest
      DoReturn _ me _ -> do
        -- a return ends this path; items after it are unreachable
        (u, t) <- maybe (pure (Map.empty, Nothing)) (fmap flatR . walkE env) me
        pure (Flow Nothing t [] [u])
      DoBreak {} -> pure (Flow Nothing Nothing [Map.empty] [])
      DoContinue {} -> pure (Flow Nothing Nothing [Map.empty] [])
      DoWhile _ cond body mels _ -> do
        cu <- fst . flatR <$> walkE env cond
        bodyFl <- go env body
        -- per-iteration paths: fall-through and break/continue exits;
        -- the loop may run zero times (§18.2.4)
        let iter = loopU (altUs (maybeToList (fU bodyFl) ++ fBC bodyFl))
        eu <- maybe (pure Map.empty) (fmap (altUs . flowPaths) . go env) mels
        fl <- go env rest
        let fl' = prefixFlow (cu `seqU` iter `seqU` eu) fl
        pure fl' {fRet = fRet bodyFl ++ fRet fl'}
      DoFor _ pat src body mels sp -> do
        su <- fst . flatR <$> walkE env src
        shadow <- shadowVars (patVars pat) sp
        bodyFl <- go (bindVars shadow env) body
        let iter = loopU (altUs (maybeToList (fU bodyFl) ++ fBC bodyFl))
        eu <- maybe (pure Map.empty) (fmap (altUs . flowPaths) . go env) mels
        fl <- go env rest
        let fl' = prefixFlow (su `seqU` iter `seqU` eu) fl
        pure fl' {fRet = fRet bodyFl ++ fRet fl'}
      DoIf alts mels _ -> do
        cus <- mapM (fmap (fst . flatR) . walkE env . fst) alts
        bfs <- mapM (go env . snd) alts
        mef <- traverse (go env) mels
        let branchFls = bfs ++ maybeToList mef
            -- with no else there is an implicit empty fall-through path
            fallts =
              mapMaybe fU branchFls
                ++ [Map.empty | case mef of Nothing -> True; Just _ -> False]
            condU = foldr seqU Map.empty cus
            branchFall
              | null fallts = Nothing
              | otherwise = Just (altUs fallts)
        fl <- go env rest
        let fl' = case branchFall of
              Nothing -> Flow Nothing (fT fl) [] []
              Just bu -> prefixFlow (condU `seqU` bu) fl
            exitsB = map (condU `seqU`) (concatMap fBC branchFls)
            exitsR = map (condU `seqU`) (concatMap fRet branchFls)
        pure fl' {fBC = exitsB ++ fBC fl', fRet = exitsR ++ fRet fl'}
      DoDefer _ e sp -> do
        u <- fst . flatR <$> walkE env e
        when (deferAbrupt e) $
          emit "E_DEFER_ABRUPT_CONTROL" "kappa.do.defer" sp
            "a deferred action must not return, break, or continue out of itself (§18.7)"
        prefixFlow u <$> go env rest
      DoDecl d -> do
        lbs <- declsToBinds [d]
        case lbs of
          [lb] -> bindLike env lb rest
          _ -> go env rest
      where
        shadowVars nms sp =
          mapM (\nm -> (\k -> (nm, plainV k sp)) <$> freshKey nm) nms
        bindLike envc lb@(LetBind {}) restItems = do
          (segs, env') <- walkBinds envc [lb]
          let u = foldr (\(su, _, _) acc -> su `seqU` acc) Map.empty segs
              bound = concat [b | (_, b, _) <- segs]
          fl <- go env' restItems
          -- every path leaving the binding's scope must satisfy it
          forM_ bound $ \(_, vi) -> closeVar vi (altUs (flowPaths fl))
          pure (prefixFlow u fl)

-- | Residual constructors of a plain @let?@ pattern that carry a
-- positive-lower-bound (quantity @1@\/@>=1@) field (§12.2.5).
residueLinear :: Env -> Pattern -> [Text]
residueLinear env pat = case headCtor pat of
  Just cn ->
    [ cn'
    | (cn', qs) <- Map.findWithDefault [] cn (eCtors env)
    , cn' /= cn
    , any (`elem` [Just QOne, Just QAtLeastOne]) qs
    ]
  Nothing -> []
  where
    headCtor = \case
      PCtor cr _ _ -> Just (nameText (crName cr))
      PCtorNamed cr _ _ -> Just (nameText (crName cr))
      PTyped p _ _ -> headCtor p
      PAs _ p -> headCtor p
      _ -> Nothing

-- | Abrupt control flow escaping a deferred action (§18.7): any
-- @return@, or a @break@\/@continue@ not enclosed by a loop inside the
-- deferred expression itself; nested lambdas are separate targets.
deferAbrupt :: Expr -> Bool
deferAbrupt = goE
  where
    goE = \case
      EDo _ items _ -> any (goI False) items
      EBlock {} -> False
      ELambda {} -> False
      EIf alts mels _ -> any (goE . snd) alts || maybe False goE mels
      ELet _ body _ -> goE body
      _ -> False
    goI inLoop = \case
      DoReturn {} -> True
      DoBreak {} -> not inLoop
      DoContinue {} -> not inLoop
      DoWhile _ _ body mels _ -> any (goI True) body || maybe False (any (goI inLoop)) mels
      DoFor _ _ _ body mels _ -> any (goI True) body || maybe False (any (goI inLoop)) mels
      DoIf alts mels _ -> any (any (goI inLoop) . snd) alts || maybe False (any (goI inLoop)) mels
      DoExpr e -> goE e
      DoLet lb -> goE (lbExpr lb)
      DoBind lb -> goE (lbExpr lb)
      _ -> False
