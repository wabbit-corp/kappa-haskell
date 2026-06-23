-- | Shared structural operations over Kappa Core terms.
--
-- Keep this module pure and checker-independent.  It is the place for reusable
-- folds, queries, and small de Bruijn operations that otherwise tend to be
-- copied into elaboration, termination, and backend passes.
module Kappa.CoreOps
  ( foldTerm
  , foldTermWithDepth
  , mapTermWithDepth
  , patBindersC
  , mentionsGlobal
  , projectionDepsOf
  , substGlobal
  , shiftTerm
  , substTerm
  , substTopTerm
  , zonkTermWith
  , maxFreeIndexTerm
  , metaIdsOf
  , metaOccursInTermShallow
  , metaOccursInTermShallowFuel
  , termClosed
  , globalsOfTerm
  , spineOfTerm
  ) where

import Data.List (nub)
import Data.Monoid (All (..), Any (..))
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T

import Kappa.Core

-- | Fold over a term and all term-bearing do-kernel children.  The first
-- function observes every 'Term'; the second observes every 'KItem'.  Binder
-- depth is intentionally not exposed here; use 'foldTermWithDepth' when a query
-- cares about de Bruijn levels.
foldTerm :: Monoid m => (Term -> m) -> (KItem -> m) -> Term -> m
foldTerm termF itemF = go
  where
    go t = termF t <> case t of
      CVar _ -> mempty
      CGlob _ -> mempty
      CLam _ _ _ b -> go b
      CPi _ _ _ a b -> go a <> go b
      CApp _ f a -> go f <> go a
      CSort _ -> mempty
      CLit _ -> mempty
      CCtor _ as -> foldMap go as
      CMatch s alts -> go s <> foldMap goAlt alts
      CRecordT fs -> foldMap (go . snd) fs
      CRecordV fs -> foldMap (go . snd) fs
      CProj e _ -> go e
      CProjAt e _ _ -> go e
      CVariantT ms -> foldMap go ms
      CInject _ e -> go e
      CLet _ _ a b c -> go a <> go b <> go c
      CLetRec _ _ a b c -> go a <> go b <> go c
      CMeta _ -> mempty
      CDo _ items -> foldMap goK items
      CSealE _ e -> go e
      CSigT _ e -> go e
      CThunkE e -> go e
      CLazyE e -> go e
      CForceE e -> go e
      CIf a b c -> go a <> go b <> go c
      CQuote _ slots -> foldMap go slots

    goAlt (CaseAlt _ gd b) = foldMap go gd <> go b

    goK k = itemF k <> case k of
      KBind _ _ t -> go t
      KLet _ _ t -> go t
      KLetQ _ t m -> go t <> foldMap (go . snd) m
      KExpr t -> go t
      KVarItem _ t -> go t
      KAssign lhs _ rhs -> go lhs <> go rhs
      KReturn t -> go t
      KBreak _ -> mempty
      KContinue _ -> mempty
      KWhile _ c b e -> go c <> foldMap goK b <> foldMap (foldMap goK) e
      KFor _ _ s b e -> go s <> foldMap goK b <> foldMap (foldMap goK) e
      KIf alts e -> foldMap (\(c, b) -> go c <> foldMap goK b) alts <> foldMap (foldMap goK) e
      KDefer _ t -> go t
      KUsing _ a r -> go a <> go r
      KSubDo _ b -> foldMap goK b

-- | Depth-aware fold over the pure Core term tree.  This intentionally treats
-- suspended do-kernel bodies as opaque, matching the de Bruijn assumptions used
-- by shifting/substitution and free-index queries in the checker.
foldTermWithDepth :: Monoid m => (Int -> Term -> m) -> Int -> Term -> m
foldTermWithDepth termF = go
  where
    go d t = termF d t <> case t of
      CVar _ -> mempty
      CGlob _ -> mempty
      CLam _ _ _ b -> go (d + 1) b
      CPi _ _ _ a b -> go d a <> go (d + 1) b
      CApp _ f a -> go d f <> go d a
      CSort _ -> mempty
      CLit _ -> mempty
      CCtor _ as -> foldMap (go d) as
      CMatch s alts -> go d s <> foldMap (goAlt d) alts
      CRecordT fs -> foldMap (go d . snd) fs
      CRecordV fs -> foldMap (go d . snd) fs
      CProj e _ -> go d e
      CProjAt e _ _ -> go d e
      CVariantT ms -> foldMap (go d) ms
      CInject _ e -> go d e
      CLet _ _ a b c -> go d a <> go d b <> go (d + 1) c
      CLetRec _ _ a b c -> go d a <> go (d + 1) b <> go (d + 1) c
      CMeta _ -> mempty
      CDo _ _ -> mempty
      CSealE _ e -> go d e
      CSigT _ e -> go d e
      CThunkE e -> go d e
      CLazyE e -> go d e
      CForceE e -> go d e
      CIf a b c -> go d a <> go d b <> go d c
      CQuote _ slots -> foldMap (go d) slots

    goAlt d (CaseAlt p gd b) =
      let d' = d + patBindersC p
       in foldMap (go d') gd <> go d' b

-- | Depth-aware pure Core transform.  Returning 'Just' replaces the current
-- node and suppresses descent, which is the useful behavior for de Bruijn var
-- rewrites such as shift and substitution.
mapTermWithDepth :: (Int -> Term -> Maybe Term) -> Int -> Term -> Term
mapTermWithDepth f = go
  where
    go d t = case f d t of
      Just t' -> t'
      Nothing -> case t of
        CVar i -> CVar i
        CGlob g -> CGlob g
        CLam ic q n b -> CLam ic q n (go (d + 1) b)
        CPi ic q n a b -> CPi ic q n (go d a) (go (d + 1) b)
        CApp ic fn a -> CApp ic (go d fn) (go d a)
        CSort u -> CSort u
        CLit l -> CLit l
        CCtor g as -> CCtor g (map (go d) as)
        CMatch s alts -> CMatch (go d s) (map (goAlt d) alts)
        CRecordT fs -> CRecordT [(n, go d x) | (n, x) <- fs]
        CRecordV fs -> CRecordV [(n, go d x) | (n, x) <- fs]
        CProj e n -> CProj (go d e) n
        CProjAt e n i -> CProjAt (go d e) n i
        CVariantT ms -> CVariantT (map (go d) ms)
        CInject tag e -> CInject tag (go d e)
        CLet q n a b c -> CLet q n (go d a) (go d b) (go (d + 1) c)
        CLetRec q n a b c -> CLetRec q n (go d a) (go (d + 1) b) (go (d + 1) c)
        CMeta m -> CMeta m
        CDo lbl items -> CDo lbl items
        CSealE ls e -> CSealE ls (go d e)
        CSigT ls e -> CSigT ls (go d e)
        CThunkE e -> CThunkE (go d e)
        CLazyE e -> CLazyE (go d e)
        CForceE e -> CForceE (go d e)
        CIf a b c -> CIf (go d a) (go d b) (go d c)
        CQuote qs slots -> CQuote qs (map (go d) slots)

    goAlt d (CaseAlt p gd b) =
      let d' = d + patBindersC p
       in CaseAlt p (go d' <$> gd) (go d' b)

-- | Number of de Bruijn binders introduced by a core pattern.  This is the
-- structural binder count used when descending into match guards/bodies and
-- do-kernel binders.  Keep the semantics aligned with the pattern elaborator:
-- residual record binders count only when they are named, and residual variant
-- rest patterns bind one value.
patBindersC :: CorePat -> Int
patBindersC = \case
  CPWild -> 0
  CPVar _ -> 1
  CPLit _ -> 0
  CPCtor _ ps -> sum (map patBindersC ps)
  CPTuple ps -> sum (map patBindersC ps)
  CPRecord fs rest -> sum (map (patBindersC . snd) fs) + case rest of
    Just nm | not (T.null nm) -> 1
    _ -> 0
  CPInject _ p -> patBindersC p
  CPInjectRest _ -> 1
  CPOr ps _ -> case ps of
    p : _ -> patBindersC p
    [] -> 0
  CPAs _ p -> 1 + patBindersC p

-- | Whether a global name occurs anywhere in the pure Core term tree.  This
-- deliberately uses the depth-aware fold even though it does not inspect depth,
-- because that fold has the same opaque-do treatment as de Bruijn-sensitive
-- operations.
mentionsGlobal :: GName -> Term -> Bool
mentionsGlobal target = getAny . foldTermWithDepth here 0
  where
    here _ = \case
      CGlob g | g == target -> Any True
      _ -> mempty

-- | Field labels projected directly from a distinguished global.  Used for
-- dependent record/trait-member ordering, where @this.foo@ means the field type
-- depends on sibling field @foo@.
projectionDepsOf :: GName -> Term -> [Text]
projectionDepsOf target = nub . foldTermWithDepth here 0
  where
    here _ = \case
      CProj (CGlob g) f | g == target -> [f]
      CProjAt (CGlob g) f _ | g == target -> [f]
      _ -> []

-- | Substitute a term for a distinguished global, shifting the replacement
-- under binders at the occurrence site.  This is for compiler-internal neutral
-- globals such as @this@, not for general delta-reduction.
substGlobal :: GName -> Term -> Term -> Term
substGlobal target replacement = mapTermWithDepth rewrite 0
  where
    rewrite d = \case
      CGlob g | g == target -> Just (shiftTerm d 0 replacement)
      _ -> Nothing

-- | Shift de Bruijn indices by @by@ at and above the cutoff depth.
shiftTerm :: Int -> Int -> Term -> Term
shiftTerm by = mapTermWithDepth $ \d -> \case
  CVar i
    | i >= d -> Just (CVar (i + by))
  _ -> Nothing

-- | Substitute an argument for the outermost binder in a body.
substTopTerm :: Term -> Term -> Term
substTopTerm arg body = shiftTerm (-1) 0 (substTerm 0 (shiftTerm 1 0 arg) body)

-- | Substitute a replacement for the binder identified by its de Bruijn index at
-- the top level.  The replacement is shifted as traversal moves under binders.
substTerm :: Int -> Term -> Term -> Term
substTerm target replacement = mapTermWithDepth rewrite 0
  where
    rewrite d = \case
      CVar i
        | i == target + d -> Just (shiftTerm d 0 replacement)
      _ -> Nothing

-- | Replace solved metavariables using a caller-supplied resolver.  The resolver
-- receives the current binder depth so the caller can quote a meta solution at
-- the correct scope.
--
-- Unlike 'mapTermWithDepth', this walks do-kernel items and updates their
-- sequential binder depth: @KBind@/@KLet@ patterns extend the following item
-- scope, @KVarItem@ introduces one binder, @KFor@ extends only its body, and
-- nested @KSubDo@ shares the current surrounding depth.  Keeping this logic
-- pure lets 'Kappa.Check.zonkTermM' be a thin state adapter over solved metas.
zonkTermWith :: (Int -> MetaId -> Maybe Term) -> Int -> Term -> Term
zonkTermWith resolveMeta = go
  where
    goItems _ [] = []
    goItems d (k : ks) =
      let (k', d') = goItem d k
       in k' : goItems d' ks

    goItem d = \case
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
      KWhile l c b e -> (KWhile l (go d c) (goItems d b) (fmap (goItems d) e), d)
      KFor l p s b e -> (KFor l p (go d s) (goItems (d + patBindersC p) b) (fmap (goItems d) e), d)
      KIf alts e -> (KIf [(go d c, goItems d b) | (c, b) <- alts] (fmap (goItems d) e), d)
      KDefer ml t -> (KDefer ml (go d t), d)
      KUsing p a r -> (KUsing p (go d a) (go d r), d)
      KSubDo l b -> (KSubDo l (goItems d b), d)

    go d = \case
      CMeta m -> maybe (CMeta m) id (resolveMeta d m)
      CVar i -> CVar i
      CGlob g -> CGlob g
      CLam ic q n b -> CLam ic q n (go (d + 1) b)
      CPi ic q n a b -> CPi ic q n (go d a) (go (d + 1) b)
      CApp ic f a -> CApp ic (go d f) (go d a)
      CSort u -> CSort u
      CLit l -> CLit l
      CCtor g as -> CCtor g (map (go d) as)
      CMatch s alts ->
        CMatch (go d s) [CaseAlt p (fmap (go (d + patBindersC p)) gd) (go (d + patBindersC p) b) | CaseAlt p gd b <- alts]
      CRecordT fs -> CRecordT [(n, go d t) | (n, t) <- fs]
      CRecordV fs -> CRecordV [(n, go d t) | (n, t) <- fs]
      CProj e f -> CProj (go d e) f
      CProjAt e f i -> CProjAt (go d e) f i
      CVariantT ms -> CVariantT (map (go d) ms)
      CInject tg e -> CInject tg (go d e)
      CLet q n a b c -> CLet q n (go d a) (go d b) (go (d + 1) c)
      CLetRec q n a b c -> CLetRec q n (go d a) (go (d + 1) b) (go (d + 1) c)
      CDo lbl items -> CDo lbl (goItems d items)
      CSealE ls e -> CSealE ls (go d e)
      CSigT ls e -> CSigT ls (go d e)
      CThunkE e -> CThunkE (go d e)
      CLazyE e -> CLazyE (go d e)
      CForceE e -> CForceE (go d e)
      CIf a b c -> CIf (go d a) (go d b) (go d c)
      CQuote qs slots -> CQuote qs (map (go d) slots)

-- | Largest free de Bruijn index relative to the supplied top-level depth, or
-- @-1@ when the term is closed with respect to that depth.
maxFreeIndexTerm :: Term -> Int
maxFreeIndexTerm = getMaxFree . foldTermWithDepth here 0
  where
    here d = \case
      CVar i | i >= d -> MaxFree (i - d)
      _ -> MaxFree (-1)

newtype MaxFree = MaxFree {getMaxFree :: Int}

instance Semigroup MaxFree where
  MaxFree a <> MaxFree b = MaxFree (max a b)

instance Monoid MaxFree where
  mempty = MaxFree (-1)

-- | Metavariable identifiers that occur syntactically in a term, including
-- term-bearing do-kernel items.  The result is de-duplicated in traversal order.
metaIdsOf :: Term -> [MetaId]
metaIdsOf = nub . foldTerm here (const [])
  where
    here = \case
      CMeta m -> [m]
      _ -> []

-- | Whether a term has no free de Bruijn variables and no metavariables.
-- Do-kernels are rejected as reusable evidence because their sequential
-- bindings and control-flow effects are not pure proof terms.
termClosed :: Term -> Bool
termClosed = getAll . foldTermWithDepth here 0
  where
    here d = \case
      CVar i -> All (i < d)
      CMeta _ -> All False
      CDo _ _ -> All False
      _ -> mempty

-- | Bounded syntactic occurrence check for a metavariable in a term.
metaOccursInTermShallow :: MetaId -> Term -> Bool
metaOccursInTermShallow = metaOccursInTermShallowFuel 512

-- | Fuel-limited occurrence check used from semantic occurs checks.  Exhaustion
-- is conservative: it returns True so the caller refuses a direct solve rather
-- than risk installing a cyclic solution.
--
-- This deliberately does not use the generic folds: every recursive descent
-- consumes fuel, including do-kernel items, so pathological terms cannot make
-- the occurs check diverge.
metaOccursInTermShallowFuel :: Int -> MetaId -> Term -> Bool
metaOccursInTermShallowFuel fuel0 target = go fuel0
  where
    next n = n - 1
    exhausted n = n <= 0

    goK n
      | exhausted n = const True
      | otherwise = \case
          KBind _ _ t -> go (next n) t
          KLet _ _ t -> go (next n) t
          KLetQ _ t m -> go (next n) t || maybe False (go (next n) . snd) m
          KExpr t -> go (next n) t
          KVarItem _ t -> go (next n) t
          KAssign lhs _ rhs -> go (next n) lhs || go (next n) rhs
          KReturn t -> go (next n) t
          KBreak _ -> False
          KContinue _ -> False
          KWhile _ c b e ->
            go (next n) c
              || any (goK (next n)) b
              || maybe False (any (goK (next n))) e
          KFor _ _ src b e ->
            go (next n) src
              || any (goK (next n)) b
              || maybe False (any (goK (next n))) e
          KIf alts e ->
            any (\(c, b) -> go (next n) c || any (goK (next n)) b) alts
              || maybe False (any (goK (next n))) e
          KDefer _ t -> go (next n) t
          KUsing _ acquire release -> go (next n) acquire || go (next n) release
          KSubDo _ items -> any (goK (next n)) items

    go n t
      | exhausted n = True
      | otherwise = case t of
          CMeta m -> m == target
          CApp _ f a -> go (next n) f || go (next n) a
          CLam _ _ _ b -> go (next n) b
          CPi _ _ _ a b -> go (next n) a || go (next n) b
          CCtor _ as -> any (go (next n)) as
          CMatch scrut alts ->
            go (next n) scrut
              || any (\(CaseAlt _ gd b) -> maybe False (go (next n)) gd || go (next n) b) alts
          CRecordT fs -> any (go (next n) . snd) fs
          CRecordV fs -> any (go (next n) . snd) fs
          CProj e _ -> go (next n) e
          CProjAt e _ _ -> go (next n) e
          CVariantT ms -> any (go (next n)) ms
          CInject _ e -> go (next n) e
          CLet _ _ a b c -> go (next n) a || go (next n) b || go (next n) c
          CLetRec _ _ a b c -> go (next n) a || go (next n) b || go (next n) c
          CIf a b c -> go (next n) a || go (next n) b || go (next n) c
          CThunkE e -> go (next n) e
          CLazyE e -> go (next n) e
          CForceE e -> go (next n) e
          CSealE _ e -> go (next n) e
          CSigT _ e -> go (next n) e
          CQuote _ slots -> any (go (next n)) slots
          CDo _ items -> any (goK (next n)) items
          _ -> False

-- | Global names mentioned by a term.  Constructor heads count as globals; do
-- items are traversed through 'foldTerm'.
globalsOfTerm :: Term -> Set GName
globalsOfTerm = foldTerm here (const Set.empty)
  where
    here = \case
      CGlob g -> Set.singleton g
      CCtor g _ -> Set.singleton g
      _ -> Set.empty

-- | Split a left-associated application spine into its head and ordered
-- arguments.
spineOfTerm :: Term -> (Term, [(Icit, Term)])
spineOfTerm = go []
  where
    go acc (CApp ic f a) = go ((ic, a) : acc) f
    go acc f = (f, acc)
