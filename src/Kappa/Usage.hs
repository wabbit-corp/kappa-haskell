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
import Data.List (find, isPrefixOf, tails)
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
  , pReceiver :: !Bool -- ^ §7.4 receiver-marked binder
  }

defaultP :: PInfo
defaultP = PInfo Nothing Nothing False False False False

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
  , vDeps :: ![(Text, [Text])] -- ^ §13.2.1 field dependencies (field ↦ siblings its type mentions)
  , vSpan :: !Span -- ^ binding site (drop reports)
  }

plainV :: Text -> Span -> VInfo
plainV k sp = VInfo k Nothing False False False Nothing Map.empty [] [] sp

-- | Expand a borrow lock over a field path with the §12.4 dependency
-- rule: borrowing a dependent field also locks the fields its type
-- mentions ("dependent fields are not disjoint merely because their
-- labels differ").
lockWithDeps :: VInfo -> [Text] -> [[Text]]
lockWithDeps vi path = case path of
  (f : _) -> path : [[d] | d <- fromMaybe [] (lookup f (vDeps vi))]
  [] -> [path]

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
  , eProjs :: !(Map Text ProjUse)
  -- ^ §9.1.1 projection definitions of the module
  , eDescs :: !(Map Text ProjUse)
  -- ^ local bindings holding a (partially applied) projection descriptor
  , eBorrowAliases :: !(Map Text (Text, [Text]))
  -- ^ borrowed place-alias bindings: binder key ↦ root key + path (§12.4)
  , eFieldDeps :: !(Map Text [(Text, [Text])])
  -- ^ record type alias ↦ §13.2.1 field dependencies
  , eEffOps :: !(Map Text [(Text, Quantity)])
  -- ^ scoped effect label ↦ operations with declared resumption
  -- quantities (§9.3.1.1, §18.1.16)
  , eExpansions :: !(Map Span Expr)
  -- ^ §21.2 splice expansions recorded by the elaborator (keyed by the
  -- splice span): the object-level uses charged at each splice site
  }

-- | §9.1.1 projection shape for the §12.4 footprint analysis.
data ProjUse = ProjUse
  { puIsPlace :: ![Bool] -- ^ per explicit binder, declaration order
  , puPlaceNames :: ![Text] -- ^ place binder names, declaration order
  , puYields :: ![(Text, [Text])] -- ^ yield leaves: place name, path suffix
  }

bindVars :: [(Text, VInfo)] -> Env -> Env
bindVars bs env =
  env
    { eVars = foldr (uncurry Map.insert) (eVars env) bs
    , eDescs = foldr (Map.delete . fst) (eDescs env) bs
    }

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
-- diagnostics for its named definitions. The first argument carries the
-- elaborator's §21.2 splice expansions (splice span ↦ expanded syntax).
usageDiagnostics :: Map Span Expr -> Module -> [Diagnostic]
usageDiagnostics expansions m = concatMap analyzeDecl lets
  where
    decls = modDecls m
    sigs = Map.fromList [(nameText n, ty) | DSig _ n ty _ <- decls]
    lets = [ld | DLet _ ld _ <- decls, Just _ <- [ldName ld]]
    projs =
      Map.fromList
        [ (nameText n, ProjUse isPlace placeNames yields)
        | DProjection _ n bs _ body _ <- decls
        , let groups = projBinderGroups bs
              isPlace = map fst groups
              placeNames = [maybe "_" nameText (bName b) | (True, b) <- groups]
              yields = case body of
                ProjSelector e ->
                  [ (root, path)
                  | Right (root, path) <- projYieldPlaces e
                  , root `elem` placeNames
                  ]
                -- an accessor bundle's footprint is its whole root
                ProjAccessors _ -> [(p, []) | p <- placeNames]
        ]
    aliases =
      Map.fromList
        [ (nameText n, fieldsOf rhs)
        | DTypeAlias _ n [] _ (Just rhs) _ <- decls
        , ERecordType {} <- [rhs]
        ]
    aliasDeps =
      Map.fromList
        [ (nameText n, fieldDepsOf fs)
        | DTypeAlias _ n [] _ (Just rhs) _ <- decls
        , ERecordType fs _ _ <- [rhs]
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
          final = execState (analyzeLet expansions fns aliases aliasDeps ctors projs sigTy ld) (S [] False 0)
       in if sBail final then [] else reverse (sDiags final)

-- Callee demand for prelude helpers the fixtures rely on.
builtinFns :: Map Text [PInfo]
builtinFns =
  Map.fromList
    [ ("unsafeConsume", [PInfo Nothing (Just QOne) False False True False])
    , -- §14.3.2 'summon': the explicit goal argument is a type, erased
      -- at runtime (§31.2), so mentioning an erased type binder there
      -- is not a runtime use
      ("summon", [PInfo Nothing (Just QZero) False False True False])
    ]

-- | Resolve a (possibly aliased) record type to its field list.
resolveFields :: Map Text [(Text, Maybe Quantity)] -> Expr -> [(Text, Maybe Quantity)]
resolveFields aliases = go
  where
    go = \case
      ERecordType fs _ _ ->
        [(nameText (rtfName f), bpQuantity (rtfPrefix f)) | f <- fs]
      EVar n -> Map.findWithDefault [] (nameText n) aliases
      -- the §12.4.3 prelude zipper: a linear fill closure
      EApp (EVar n) _
        | nameText n == "Zipper"
        , not (Map.member "Zipper" aliases) ->
            [("focus", Nothing), ("fill", Just QOne)]
      EAscription e _ _ -> go e
      ECaptures e _ _ -> go e
      _ -> []

-- | Resolve a (possibly aliased) record type to its §13.2.1 field
-- dependencies: field ↦ sibling labels its type mentions via 'this'.
resolveDeps :: Map Text [(Text, [Text])] -> Expr -> [(Text, [Text])]
resolveDeps depAliases = go
  where
    go = \case
      ERecordType fs _ _ -> fieldDepsOf fs
      EVar n -> Map.findWithDefault [] (nameText n) depAliases
      EAscription e _ _ -> go e
      ECaptures e _ _ -> go e
      _ -> []

-- | §13.2.1 field dependencies of a surface record type.
fieldDepsOf :: [RecTypeField] -> [(Text, [Text])]
fieldDepsOf fs =
  [ (nameText (rtfName f), deps)
  | f <- fs
  , let deps = [l | l <- surfaceThisRefs (rtfType f), l `elem` names]
  , not (null deps)
  ]
  where
    names = [nameText (rtfName f) | f <- fs]

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
       in PInfo (nameText <$> bName b) mq (isJust mb) (bInout b) True (bReceiver b /= NoReceiver)
    mergeP (PInfo n1 q1 b1 i1 k1 r1) (PInfo n2 q2 b2 i2 k2 r2) =
      PInfo (n1 `orElse` n2) (q1 `orElse` q2) (b1 || b2) (i1 || i2) (k1 || k2) (r1 || r2)
    orElse (Just x) _ = Just x
    orElse Nothing y = y

-- ── Definition analysis ──────────────────────────────────────────────

analyzeLet ::
  Map Span Expr ->
  Map Text [PInfo] ->
  Map Text [(Text, Maybe Quantity)] ->
  Map Text [(Text, [Text])] ->
  Map Text [(Text, [Maybe Quantity])] ->
  Map Text ProjUse ->
  Maybe Expr ->
  LetDef ->
  M ()
analyzeLet expansions fns aliases aliasDeps ctors projs msig ld = do
  let aligned = alignParams (ldBinders ld) (maybe [] sigBinders msig)
  binds <- catMaybes <$> mapM paramBind aligned
  let env = Env (Map.fromList binds) fns [] aliases ctors projs Map.empty Map.empty aliasDeps Map.empty expansions
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
            deps = maybe [] (resolveDeps aliasDeps) ty
        k <- freshKey (nameText n)
        pure (Just (nameText n, VInfo k q (isJust mark) anon False Nothing Map.empty fields deps (bSpan b)))
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
        ("'" <> what <> "' is consumed more often than its "
           <> (if vQ vi == Just QOne then "linear" else "affine")
           <> " quantity permits (§12.2)")
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

-- | Resolve a place through any §12.4 borrowed place-alias binding:
-- @let & x = root.path@ makes @x.f@ an alias of @root.path.f@ for
-- borrow-lock purposes.
resolveBorrowAlias :: Env -> (VInfo, [Text], Span) -> (Text, [Text], Span)
resolveBorrowAlias env (vi, path, sp) =
  case Map.lookup (vKey vi) (eBorrowAliases env) of
    Just (rootK, rootPath) -> (rootK, rootPath ++ path, sp)
    Nothing -> (vKey vi, path, sp)

-- | The lock set a lexical borrow of a place opens: the path itself
-- (rebased through borrow aliases) plus, for a §13.2.1 dependent
-- record, the sibling fields the borrowed field's type mentions.
borrowLocks :: Env -> (VInfo, [Text], Span) -> [(Text, [Text])]
borrowLocks env pl@(vi, path, _) =
  let (rootK, fullPath, _) = resolveBorrowAlias env pl
      depLocks
        | rootK == vKey vi = drop 1 (lockWithDeps vi path)
        | otherwise = []
   in (rootK, fullPath) : [(rootK, p) | p <- depLocks]

-- | A fully applied §9.1.1 projection (or local descriptor binding)
-- call: the stable places its yield leaves touch, plus the auxiliary
-- expressions (ordinary arguments, descriptor head) to walk normally.
projPlacesOf :: Env -> Expr -> Maybe ([(VInfo, [Text], Span)], [Expr])
projPlacesOf env e0 = case e0 of
  EApp (EVar f) args
    | not (Map.member (nameText f) (eVars env))
    , Just pu <- Map.lookup (nameText f) (eProjs env)
    , length args == length (puIsPlace pu)
    , or (puIsPlace pu) -> do
        let split = zip (puIsPlace pu) args
            placeArgs =
              [ (nm, e)
              | ((True, ArgExplicit e), nm) <-
                  zip [p | p@(True, _) <- split] (puPlaceNames pu)
              ]
            ordArgs = [e | (False, ArgExplicit e) <- split]
        (places, aux) <- packPlaces pu placeArgs
        pure (places, ordArgs ++ aux)
    | Just du <- Map.lookup (nameText f) (eDescs env)
    , [arg] <- args -> do
        e <- case arg of
          ArgExplicit e -> Just e
          ArgInout e _ -> Just e
          _ -> Nothing
        (places, aux) <- case (puPlaceNames du, e) of
          (_, ERecordLit items _) ->
            packPlaces du
              [(nameText fn, fe) | RecItem _ fn (Just fe) <- items]
          ([pn], _) -> packPlaces du [(pn, e)]
          _ -> Nothing
        pure (places, EVar f : aux)
  _ -> Nothing
  where
    -- map each yield leaf through the supplied place arguments; place
    -- arguments that are not stable places are walked normally
    packPlaces pu pairs = do
      let leaves =
            [ (root, suffix, lookup root pairs)
            | (root, suffix) <- puYields pu
            ]
      resolved <- Just (mapMaybe leafPlace leaves)
      let aux = [e | (_, e) <- pairs, Nothing <- [placeOf env e]]
      pure (resolved, aux)
    leafPlace (_, suffix, Just argE) = do
      (vi, path, sp) <- placeOf env argE
      pure (vi, path ++ suffix, sp)
    leafPlace _ = Nothing

-- | Does this expression denote a (partially applied) projection
-- descriptor value (§16.1.5)?
descOf :: Env -> Expr -> Maybe ProjUse
descOf env = \case
  EVar f
    | not (Map.member (nameText f) (eVars env))
    , Just pu <- Map.lookup (nameText f) (eProjs env) ->
        Just pu
    | Just du <- Map.lookup (nameText f) (eDescs env) -> Just du
  EApp (EVar f) args
    | not (Map.member (nameText f) (eVars env))
    , Just pu <- Map.lookup (nameText f) (eProjs env)
    , length args == length (filter not (puIsPlace pu)) ->
        Just pu
  EAscription e _ _ -> descOf env e
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
    -- §9.3.1.1: collect scoped effect declarations (label ↦ op
    -- quantities) for the handler checks before walking the lets
    let env' = addEffDecls env decls
    binds <- declsToBinds [d | d <- decls, not (isEffDecl d)]
    walkE env' (ELet binds (fromMaybe (EUnit (exprSpan e0)) mres) (exprSpan e0))
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
  -- §18.1.21/.22 handler: the scrutinee is used once; each clause is an
  -- alternative path. The clause's resumption binder `k` is counted at
  -- the operation's declared resumption quantity (§18.1.16).
  EHandle _ lblE scrut cases _ -> do
    r0 <- walkE env scrut
    let mops = case lblE of
          EVar n
            | not (Map.member (nameText n) (eVars env)) ->
                Map.lookup (nameText n) (eEffOps env)
          _ -> Nothing
        bindPats sp nms = mapM (\nm -> (\k -> (nm, plainV k sp)) <$> freshKey nm) nms
    crs <- forM cases $ \case
      HandlerReturn pat body sp -> do
        shadow <- bindPats sp (patVars pat)
        fst . flatR <$> walkE (bindVars shadow env) body
      HandlerOp opN argPats kN body sp -> do
        shadow <- bindPats sp (concatMap patVars argPats)
        kKey <- freshKey (nameText kN)
        let q = maybe QOne (fromMaybe QOne . lookup (nameText opN)) mops
            kvi = (plainV kKey (nameSpan kN)) {vQ = countedQ q}
            env' = bindVars (shadow ++ [(nameText kN, kvi)]) env
        u <- fst . flatR <$> walkE env' body
        closeVar kvi u
        pure u
    pure (rPlain (fst (flatR r0) `seqU` altUs crs))
  EIs b _ -> walkE env b
  EThunk b sp -> suspend env b sp
  ELazy b sp -> suspend env b sp
  EForce b _ -> do
    r <- walkE env b
    let (u, t) = flatR r
    pure (R u t Map.empty)
  ESeal b _ _ -> walkE env b -- §13.2.10: hiding is not a consuming destructor
  EOpenExists {} -> bailOut >> pure rNone
  ESealExists {} -> bailOut >> pure rNone
  EListLit es _ -> walks es
  ESetLit es _ -> walks es
  EMapLit kvs _ -> walks (concatMap (\(k, v) -> [k, v]) kvs)
  EComprehension _ cls y _ -> walkComp env cls y (exprSpan e0)
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
  -- §21.2: a quote's object-level uses are charged when (and where) it
  -- is spliced, through the recorded expansion; the quote itself only
  -- captures meta-level syntax data
  EQuote {} -> pure rNone
  ESpliceInQuote {} -> pure rNone
  EQuoteHole {} -> pure rNone
  ESplice _ sp -> case Map.lookup sp (eExpansions env) of
    Just ex -> walkE env ex
    Nothing -> bailOut >> pure rNone
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

-- | Comprehension usage (§20.10.5): each generator/join source is
-- evaluated exactly once for the pipeline, so a one-shot source place
-- is consumed once per comprehension. All other clause expressions run
-- once per row; demands on outer variables are scaled by the pipeline
-- cardinality, approximated as [0, ω]. Row binders introduced by
-- clause patterns are tracked separately by elaboration (§20.10.4) and
-- enter this analysis untracked.
walkComp :: Env -> [CompClause] -> CompYield -> Span -> M R
walkComp env0 cls0 y sp = go env0 cls0 []
  where
    go env [] acc = do
      yu <- scaled env (case y of YieldExpr e -> [e]; YieldPair k v -> [k, v])
      pure (rPlain (foldr seqU yu acc))
    go env (c : rest) acc = case c of
      CFor _ _ pat src _ -> do
        su <- once env src
        env' <- bindPat env pat
        go env' rest (su : acc)
      CLet _ pat _ rhs _ -> do
        u <- scaled env [rhs]
        env' <- bindPat env pat
        go env' rest (u : acc)
      CIf e -> withScaled env rest acc [e]
      COrderBy ks _ -> withScaled env rest acc (map snd ks)
      CSkip e _ -> withScaled env rest acc [e]
      CTake e _ -> withScaled env rest acc [e]
      CDistinct me _ -> withScaled env rest acc (maybeToList me)
      CGroupBy k aggs n _ -> do
        u <- scaled env (k : concatMap (\(_, e, mu) -> e : maybeToList mu) aggs)
        env' <- bindName env n
        go env' rest (u : acc)
      CJoin _ pat src cond mInto _ -> do
        su <- once env src
        envP <- bindPat env pat
        cu <- scaled envP [cond]
        env' <- case mInto of
          Just n -> bindName env n
          Nothing -> pure envP
        go env' rest (su : cu : acc)
    withScaled env rest acc es = do
      u <- scaled env es
      go env rest (u : acc)
    once env src = fst . flatR <$> walkE env src
    scaled env es = do
      rs <- mapM (walkE env) es
      pure (scaleU (0, Nothing) (foldr (seqU . fst . flatR) Map.empty rs))
    bindPat env pat = do
      shadow <- forM (patVars pat) $ \nm -> do
        k <- freshKey nm
        pure (nm, plainV k sp)
      pure (bindVars shadow env)
    bindName env n = do
      k <- freshKey (nameText n)
      pure (bindVars [(nameText n, plainV k sp)] env)

-- ── Lambda binders and matches ───────────────────────────────────────

lamBind :: Env -> Binder -> M (Maybe (Text, VInfo))
lamBind env b = case bName b of
  Nothing -> pure Nothing
  Just n -> do
    let BinderPrefix mq mb = bPrefix b
        fields = maybe [] (resolveFields (eAliases env)) (bType b)
        deps = maybe [] (resolveDeps (eFieldDeps env)) (bType b)
    k <- freshKey (nameText n)
    pure
      ( Just
          ( nameText n
          , VInfo k mq (isJust mb) (mb == Just (BorrowMark Nothing)) False Nothing Map.empty fields deps (bSpan b)
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
      PatchPun _ -> []
    patchLabels = \case
      PatchUpdate ((_, n) : _) _ -> [nameText n]
      PatchUpdate [] _ -> []
      PatchExtend n _ -> [nameText n]
      PatchSection {} -> []
      PatchPun n -> [nameText n]
    walks es = do
      rs <- mapM (walkE env) es
      pure (foldr (seqU . fst . flatR) Map.empty rs)

-- ── Applications ─────────────────────────────────────────────────────

-- | Same-call facts for §12.4 disjointness: borrowed and consumed places.
data Fact
  = FBorrow !Text ![Text]
  | FMove !Text ![Text] !Span
  | FInout !Text ![Text] !Span
  -- ^ a '~'-marked inout argument's place footprint (§18.9.3)

argSpan :: Arg -> Span
argSpan = \case
  ArgExplicit e -> exprSpan e
  ArgImplicit e -> exprSpan e
  ArgNamedBlock _ sp -> sp
  ArgInout _ sp -> sp

walkApp :: Env -> Expr -> [Arg] -> M R
walkApp env (EDot recv (DotName m)) args
  -- §7.4 method-call sugar: the receiver is one ordinary argument of
  -- the callee, demanded at its receiver-marked binder position
  | not (Map.member (nameText m) (eVars env))
  , Just params <- Map.lookup (nameText m) (eFns env)
  , (i : _) <- [ix | (ix, pp) <- zip [0 ..] params, pReceiver pp] =
      walkApp env (EVar m) (take i args ++ [ArgExplicit recv] ++ drop i args)
walkApp env f args
  -- a projection call in an ordinary value position is a non-consuming
  -- read of its yield leaves (§30.2.2.3 ReadProjector)
  | Just (places, aux) <- projPlacesOf env (EApp f args) = do
      rs <- mapM (walkE env) aux
      let u = foldr (seqU . fst . flatR) Map.empty rs
          touch = Map.fromList [(vKey vi, touchC) | (vi, _, _) <- places]
      pure (rPlain (u `seqU` touch))
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
      borrows =
        [(k, p) | FBorrow k p <- facts] ++ [(k, p) | FInout k p _ <- facts]
  forM_ facts $ \case
    FMove k p msp
      | any (\(bk, bp) -> bk == k && pathsOverlap bp p) borrows ->
          emit "E_QTT_BORROW_OVERLAP" "kappa.qtt.borrow-overlap" msp
            "a place is consumed by the same call that borrows an overlapping place (§12.4)"
    _ -> pure ()
  -- §18.9.3: the place footprints of the '~' arguments of one call must
  -- be pairwise disjoint ("a given stable place, or a given projection
  -- call occurrence, may appear in at most one '~' argument")
  let inouts = [(k, p, isp) | FInout k p isp <- facts]
      overlapPairs =
        [ isp2
        | ((k1, p1, _), rest') <- zip inouts (drop 1 (tails inouts))
        , (k2, p2, isp2) <- rest'
        , k1 == k2
        , pathsOverlap p1 p2
        ]
  case overlapPairs of
    (osp : _) ->
      emit "E_QTT_BORROW_OVERLAP" "kappa.qtt.borrow-overlap" osp
        "two '~' inout arguments of the same call have overlapping place footprints (§18.9.3, §12.4)"
    [] -> pure ()
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
    | pInout p -> inoutish e sp
    | hasDemand -> do
        emit "E_QTT_INOUT_MARKER_UNEXPECTED" "kappa.qtt.inout-marker" sp
          "call-site '~' marker on an argument whose parameter is not declared inout (§18.9.3)"
        (,[]) <$> walkE env e
    | otherwise -> inoutish e sp
  ArgExplicit e
    | pInout p -> do
        emit "E_QTT_INOUT_MARKER_REQUIRED" "kappa.qtt.inout-marker" (exprSpan e)
          "this argument flows into an inout parameter and must be marked '~place' (§18.9.3)"
        (,[]) <$> walkE env e
    | pQuantity p == Just QZero -> pure (rNone, []) -- erased argument
    | pBorrow p -> borrowish e
    -- a projection call argument touches its yield leaves: a move per
    -- leaf under a consuming parameter (§30.2.2.3 MoveProjector), a
    -- call-scoped borrow otherwise (ReadProjector)
    | consuming
    , Just (places, aux) <- projPlacesOf env e -> do
        rs <- mapM (walkE env) aux
        us <- mapM (\(vi, path, psp) -> movePlace env vi path psp) places
        let u = foldr seqU (foldr (seqU . fst . flatR) Map.empty rs) us
        pure (rPlain u, [FMove (vKey vi) path psp | (vi, path, psp) <- places])
    | Just (places, aux) <- projPlacesOf env e -> do
        rs <- mapM (walkE env) aux
        let u = foldr (seqU . fst . flatR) Map.empty rs
            touch = Map.fromList [(vKey vi, touchC) | (vi, _, _) <- places]
        pure (rPlain (u `seqU` touch), [FBorrow (vKey vi) path | (vi, path, _) <- places])
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
    -- a definite consume of a deeper (non-linear) path still conflicts
    -- with a live borrow of an overlapping path (§12.4)
    | consuming
    , Just (vi, path, sp) <- placeOf env e -> do
        checkBorrowOverlap env vi path sp
        pure
          ( rPlain (Map.singleton (vKey vi) touchC)
          , [FMove (vKey vi) path sp]
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
      Nothing
        -- a projection call in borrow demand borrows every yield leaf
        -- for the call (§30.2.2.3 BorrowProjector)
        | Just (places, aux) <- projPlacesOf env e -> do
            rs <- mapM (walkE env) aux
            let u = foldr (seqU . fst . flatR) Map.empty rs
                touch = Map.fromList [(vKey vi, touchC) | (vi, _, _) <- places]
            pure (rPlain (u `seqU` touch), [FBorrow (vKey vi) path | (vi, path, _) <- places])
        | otherwise -> (,[]) <$> walkE env e
    -- like 'borrowish', but the facts carry the marker span for the
    -- §18.9.3 pairwise-disjointness check of one call's '~' arguments
    inoutish e isp = do
      (r, fs) <- borrowish e
      pure (r, [FInout k path isp | FBorrow k path <- fs])

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
            -- non-consuming read that locks overlapping paths (§12.4,
            -- §13.2.1: plus the fields a dependent field's type
            -- mentions); borrowing through a borrowed alias locks the
            -- original
            Just pl@(vi, _, _) ->
              pure (Map.singleton (vKey vi) touchC, Nothing, Map.empty, borrowLocks envc pl)
            -- `let & v = proj places` locks every yield leaf for the
            -- binder's scope (§30.2.2.3 BorrowProjector)
            Nothing
              | Just (places, aux) <- projPlacesOf envc rhs -> do
                  rs <- mapM (walkE envc) aux
                  let u' =
                        foldr (seqU . fst . flatR)
                          (Map.fromList [(vKey vi, touchC) | (vi, _, _) <- places])
                          rs
                  pure (u', Nothing, Map.empty, concatMap (borrowLocks envc) places)
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
          fdeps = maybe [] (resolveDeps (eFieldDeps envc)) mty
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
                  fdeps
                  bsp
              )
      -- every pattern name is bound (untracked entries still shadow
      -- outer bindings); only prefixed/tainted ones carry checks
      bound <- mapM mk names
      -- a borrowed binding of a place is a place alias for §12.4 locks;
      -- a binding of a (partial) projection application is a descriptor
      let aliasEntries =
            [ (vKey vi, (rk, fp))
            | borrowed
            , Just pl <- [place]
            , let (rk, fp, _) = resolveBorrowAlias envc pl
            , (_, vi) <- bound
            ]
          descEntries =
            [ (nm, du)
            | not borrowed
            , [nm] <- [names]
            , Just du <- [descOf envc rhs]
            ]
          envb0 = bindVars bound envc
          envb =
            envb0
              { eDescs = foldr (uncurry Map.insert) (eDescs envb0) descEntries
              , eBorrowAliases = foldr (uncurry Map.insert) (eBorrowAliases envb0) aliasEntries
              }
      (segs, env') <- go (addBorrows brs envb) rest
      pure ((u, bound, brs) : segs, env')
    orElse (Just x) _ = Just x
    orElse Nothing y = y

-- | Record a block's scoped effect declarations: label spelling ↦
-- operation names with declared resumption quantities (default 1,
-- §18.1.17).
addEffDecls :: Env -> [Decl] -> Env
addEffDecls env decls =
  env {eEffOps = foldr (uncurry Map.insert) (eEffOps env) effs}
  where
    effs =
      [ ( nameText (effName ed)
        , [(nameText (eoName o), fromMaybe QOne (eoQuantity o)) | o <- effOps ed]
        )
      | DEffect _ ed _ <- decls
      , not (effIsLabelDecl ed)
      ]

isEffDecl :: Decl -> Bool
isEffDecl = \case
  DEffect {} -> True
  _ -> False

-- | The counted quantity of a resumption binder: ω resumption values
-- are unrestricted (their soundness is the §18.1.20 capture rule), and
-- a one-shot resumption may be abandoned without use — the clause then
-- abandons the captured segment (§18.1.21, §32.2.20) — so the declared
-- quantity 1 counts as at-most-once.
countedQ :: Quantity -> Maybe Quantity
countedQ = \case
  QOmega -> Nothing
  QTerm {} -> Nothing
  QOne -> Just QAtMostOne
  q -> Just q

-- | Is this right-hand side an invocation of a scoped effect's
-- multi-shot operation (declared quantity permitting more than one
-- resumption, §18.1.17)? Returns the operation's span and name.
multishotOpCall :: Env -> Expr -> Maybe (Span, Text)
multishotOpCall env = \case
  EApp f _ -> multishotOpCall env f
  EDot (EVar l) (DotName op)
    | not (Map.member (nameText l) (eVars env))
    , Just ops <- Map.lookup (nameText l) (eEffOps env)
    , Just q <- lookup (nameText op) ops
    , q `elem` [QOmega, QAtLeastOne] ->
        Just (nameSpan op, nameText op)
  _ -> Nothing

declsToBinds :: [Decl] -> M [LetBind]
declsToBinds [] = pure []
declsToBinds (d : ds) = case d of
  DLet _ (LetDef (Just n) _ Nothing prefix [] _ Nothing body) sp ->
    (LetBind False prefix (PVar n) Nothing body sp :) <$> declsToBinds ds
  DLet _ (LetDef Nothing imp (Just pat) prefix [] mty Nothing body) sp ->
    (LetBind imp prefix pat mty body sp :) <$> declsToBinds ds
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
      DoBind lb -> do
        (fl, suffixFl) <- bindLike' env lb rest
        -- §18.1.20 call-site capture rule: the suffix from a multi-shot
        -- operation site to the handler boundary is captured by a
        -- reusable resumption, so every runtime-relevant captured value
        -- must be duplicable and free of borrow obligations
        forM_ (multishotOpCall env (lbExpr lb)) $ \(osp, opn) ->
          checkMultishotCapture env osp opn (flowPaths suffixFl)
        pure fl
      DoUsing _ pat rhs sp -> do
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
      DoDecl d | isEffDecl d -> go (addEffDecls env [d]) rest
      DoDecl d -> do
        lbs <- declsToBinds [d]
        case lbs of
          [lb] -> bindLike env lb rest
          _ -> go env rest
      where
        shadowVars nms sp =
          mapM (\nm -> (\k -> (nm, plainV k sp)) <$> freshKey nm) nms
        bindLike envc lb restItems = fst <$> bindLike' envc lb restItems
        bindLike' envc lb@(LetBind {}) restItems = do
          (segs, env') <- walkBinds envc [lb]
          let u = foldr (\(su, _, _) acc -> su `seqU` acc) Map.empty segs
              bound = concat [b | (_, b, _) <- segs]
          fl <- go env' restItems
          -- every path leaving the binding's scope must satisfy it
          forM_ bound $ \(_, vi) -> closeVar vi (altUs (flowPaths fl))
          pure (prefixFlow u fl, fl)
        -- a use of any outer non-duplicable binding in the captured
        -- suffix of a multi-shot operation (§18.1.20.2)
        checkMultishotCapture envc osp opn paths = do
          let usesVar vi u =
                any
                  (\(k, c) -> cTouch c && (k == vKey vi || (vKey vi <> ".") `T.isPrefixOf` k))
                  (Map.toList u)
              offenders =
                [ (vi, kind)
                | vi <- Map.elems (eVars envc)
                , Just kind <- [captureKind vi]
                , any (usesVar vi) paths
                ]
          case offenders of
            ((vi, kind) : _) ->
              emit "E_QTT_CONTINUATION_CAPTURE" "kappa.qtt.continuation-capture" osp
                ( "the multi-shot operation '" <> opn <> "' would capture '"
                    <> T.takeWhile (/= '#') (vKey vi) <> "' (" <> kind
                    <> ") in its resumption; every value captured by a multi-shot resumption must be duplicable and free of borrow obligations (§18.1.20)"
                )
            [] -> pure ()
        captureKind vi
          | vBorrowed vi = Just "a borrowed binding"
          | vQ vi `elem` [Just QOne, Just QAtMostOne] = Just "a quantity-1 binding"
          | otherwise = Nothing

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
