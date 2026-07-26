{-# LANGUAGE TupleSections #-}

-- | Shared structural operations over Kappa Core terms.
--
-- Keep this module pure and checker-independent.  It is the place for reusable
-- folds, queries, and small de Bruijn operations that otherwise tend to be
-- copied into elaboration, termination, and backend passes.
module Kappa.CoreOps
  ( foldTerm
  , foldTermWithDepth
  , mapTermWithDepth
  , mapPatternConstructorUniverses
  , patBindersC
  , mentionsGlobal
  , projectionDepsOf
  , substGlobal
  , shiftTerm
  , weakenTermUnderBinderAt
  , substTerm
  , substTopTerm
  , substTopTermAt
  , coreToNeutralLevelTerm
  , termAsLevel
  , zonkTermWith
  , mapSchemaRoleEvidence
  , maxFreeIndexTerm
  , termScopedAt
  , metaIdsOf
  , levelMetasOfTerm
  , levelParamsOfTerm
  , termNodeLevels
  , itemPatternLevels
  , declarationUniverseConstraints
  , declarationUniverseConstraintBinder
  , authenticatedLevelAssumption
  , authenticatedLevelAssumptionWith
  , dedupeUniverseConstraints
  , equivalentUniverseConstraint
  , specializeTraitMemberProjectionType
  , specializeTraitMemberStorageType
  , metaOccursInTermShallow
  , metaOccursInTermShallowFuel
  , termClosed
  , globalsOfTerm
  , spineOfTerm
  ) where

import Control.Applicative ((<|>))
import Data.Bifunctor (bimap)
import qualified Data.ByteString as BS
import Data.List (nub)
import Data.Monoid (All (..), Any (..))
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T

import Kappa.Builtins
  ( gPrel
  , prelBool
  , prelEqType
  , prelLevelLe
  , prelLevelLt
  , prelTrue
  , prelTypeLevel
  )
import Kappa.Core
import Kappa.Level
  ( LevelMeta
  , SolveResult (Proved)
  , abstractLocalLevelParams
  , emptyAssumptions
  , levelMetas
  , levelFields
  , levelParams
  , levelSucc
  , levelVars
  , mapNeutralLevelAtomLevels
  , normalizeLevel
  , proveLevelLeq
  , weakenLevelLocalsAt
  )
import Kappa.Source (ModuleName (..))

-- | Recover the declaration-level universe obligations represented by erased
-- implicit proof binders in a finalized Core type.  This is the single
-- structural authority used by checking, interchange, and backend validation;
-- 'DeclarationUniverseTelescope' deliberately carries only level parameters.
declarationUniverseConstraints :: Int -> Term -> [UniverseConstraint]
declarationUniverseConstraints parameterCount = dedupeUniverseConstraints . go
  where
    go term@(CPiEvidenceM _ _ _ _ _ _ _ _ _ codomain) =
      case declarationUniverseConstraintBinder parameterCount term of
        Just constraint -> constraint : go codomain
        Nothing -> []
    go _ = []

-- | Recognize one authoritative declaration-universe proof binder.  Keeping
-- this predicate shared with 'declarationUniverseConstraints' lets consumers
-- distinguish erased constraint arguments from the nominal family's actual
-- term telescope without reconstructing the proof shape independently.
declarationUniverseConstraintBinder :: Int -> Term -> Maybe UniverseConstraint
declarationUniverseConstraintBinder parameterCount = \case
  CPiEvidenceM Ordinary FormationOrdinary Impl Q0 _ _ (Just (lower, upper)) _ _ _
    | schemaLevel lower
    , schemaLevel upper ->
        Just (UniverseConstraint (normalizeLevel lower) (normalizeLevel upper))
  _ -> Nothing
  where
    schemaLevel level =
      null (levelMetas level)
        && null (levelVars level)
        && null (levelFields level)
        && all (\parameter -> parameter >= 0 && parameter < parameterCount) (levelParams level)

-- | Recheck that proof-interface metadata denotes exactly the comparison in
-- its checked canonical domain. This function is intentionally pure and uses
-- resolved global identities, so source checking, KCore import, and backend
-- validation share one authority.
authenticatedLevelAssumption
  :: Int
  -> Term
  -> Maybe (Level, Level)
  -> Either Text (Maybe (Level, Level))
authenticatedLevelAssumption depth domain relation =
  authenticatedLevelAssumptionWith (const False) (termAsLevel depth) depth domain relation

-- | Recheck an elaborated comparison proposition. Direct 'LevelLe'/'LevelLt'
-- aliases are self-authenticating by nominal identity. The pre-alias source
-- form is accepted only when the caller authenticates the selected @Ord
-- TypeLevel@ dictionary by semantic global identity from the checked instance
-- environment; the overloaded operation identity alone is insufficient.
authenticatedLevelAssumptionWith
  :: (Term -> Bool)
  -> (Term -> Maybe Level)
  -> Int
  -> Term
  -> Maybe (Level, Level)
  -> Either Text (Maybe (Level, Level))
authenticatedLevelAssumptionWith _ _ _ _ Nothing = Right Nothing
authenticatedLevelAssumptionWith dictionaryIsAuthorized decodeLevel depth domain (Just recorded) = do
  derived <-
    maybe
      (Left "level-assumption metadata is not backed by a canonical checked comparison domain")
      Right
      (directRelation domain <|> overloadedRelation domain)
  if normalizePair recorded == normalizePair derived
    then Right (Just (normalizePair derived))
    else
      Left
        ( "level-assumption metadata endpoints disagree with the checked comparison domain: recorded "
            <> renderPair recorded <> ", domain " <> renderPair derived
        )
  where
    directRelation term =
      case spineOfTerm (strip term) of
        (CGlobal relation _, arguments)
          | relation == prelLevelLe || relation == prelLevelLt
          , [lowerTerm, upperTerm] <- [argument | (Expl, argument) <- arguments]
          , Just lower <- decodeLevel lowerTerm
          , Just upper <- decodeLevel upperTerm ->
              Just
                ( if relation == prelLevelLt then levelSucc lower else lower
                , upper
                )
        _ -> Nothing

    overloadedRelation term = do
      relation <- equalityTruePayload (strip term)
      case spineOfTerm (strip relation) of
        (CGlobal operator _, arguments)
          | operator == gPrel "<=" || operator == gPrel "<"
          , [(Impl, carrier), (Impl, dictionary), (Expl, lowerTerm), (Expl, upperTerm)] <- arguments
          , isTypeLevelCarrier carrier
          , dictionaryIsAuthorized (strip dictionary)
          , Just lower <- decodeLevel lowerTerm
          , Just upper <- decodeLevel upperTerm ->
              Just
                ( if operator == gPrel "<" then levelSucc lower else lower
                , upper
                )
        _ -> Nothing

    equalityTruePayload term =
      case spineOfTerm term of
        (CGlobal equality _, [(Impl, carrier), (Expl, payload), (Expl, truth)])
          | equality == prelEqType
          , isBoolCarrier carrier
          , isTrue truth -> Just payload
        _ -> Nothing

    isTypeLevelCarrier term = case strip term of
      CGlobal carrier [] -> carrier == prelTypeLevel
      _ -> False
    isBoolCarrier term = case strip term of
      CGlobal carrier [] -> carrier == prelBool
      _ -> False
    isTrue term = case strip term of
      CCtorI constructor [] _ [] -> constructor == prelTrue
      _ -> False
    strip = \case
      CUniverseLift _ _ _ inner -> strip inner
      CSchemaLift _ _ _ _ _ _ _ _ inner -> strip inner
      term -> term
    normalizePair (lower, upper) = (normalizeLevel lower, normalizeLevel upper)
    renderPair (lower, upper) = "(" <> T.pack (show (normalizeLevel lower)) <> " <= "
      <> T.pack (show (normalizeLevel upper)) <> ")"

-- | Canonicalize a generated proof telescope without changing declaration
-- order. Universe propositions are equal when both endpoints are mutually
-- entailed by the rigid level algebra, not merely when their constructors
-- happen to have the same source shape.
dedupeUniverseConstraints :: [UniverseConstraint] -> [UniverseConstraint]
dedupeUniverseConstraints = foldl insert []
  where
    insert retained constraint
      | any (equivalentUniverseConstraint constraint) retained = retained
      | otherwise = retained ++ [constraint]

equivalentUniverseConstraint :: UniverseConstraint -> UniverseConstraint -> Bool
equivalentUniverseConstraint left right =
  equalLevel (ucLower left) (ucLower right)
    && equalLevel (ucUpper left) (ucUpper right)
  where
    equalLevel lhs rhs =
      proveLevelLeq emptyAssumptions lhs rhs == Proved
        && proveLevelLeq emptyAssumptions rhs lhs == Proved

-- | Specialize the trait-parameter and dictionary prefix of a qualified trait
-- member type while preserving its leading generated universe-evidence
-- telescope. Trait member declarations may generalize level constraints before
-- the trait parameters, so consumers must not assume that the first implicit
-- binders are the trait arguments. The retained evidence binders remain
-- explicit in Core and are discharged at the projected-member occurrence.
--
-- The caller terms live in a context of @outerDepth@ binders. They are shifted
-- under the retained evidence prefix before substitution. Any unexpected
-- binder shape or arity fails closed.
specializeTraitMemberProjectionType
  :: Int
  -> Int
  -> [Term]
  -> Term
  -> Term
  -> Maybe Term
specializeTraitMemberProjectionType outerDepth parameterCount arguments dictionary memberType
  | length arguments /= parameterCount = Nothing
  | otherwise = preserveEvidence 0 memberType
  where
    preserveEvidence evidenceDepth = \case
      CPiEvidenceM mode formation Impl q borrowed name assumption@(Just _) origin domain codomain ->
        CPiEvidenceM mode formation Impl q borrowed name assumption origin domain
          <$> preserveEvidence (evidenceDepth + 1) codomain
      residual ->
        specializePrefix evidenceDepth (arguments ++ [dictionary]) residual

    specializePrefix _ [] residual = Just residual
    specializePrefix evidenceDepth (argument : rest) residual = case residual of
      CPiEvidenceM _ _ Impl _ _ _ Nothing _ _ codomain ->
        specializePrefix
          evidenceDepth
          rest
          (substTopTermAt
            (outerDepth + evidenceDepth)
            (shiftTerm evidenceDepth 0 argument)
            codomain)
      _ -> Nothing

-- | Specialize the contract of a member value stored in a trait dictionary.
-- Generated universe-constraint proofs are obligations of the accessor use
-- site and are not fields of the runtime dictionary.  Their binders may be
-- removed only when the residual member type does not mention the proof term;
-- the trait head and dictionary receiver are then specialized normally.
specializeTraitMemberStorageType
  :: Int
  -> Int
  -> [Term]
  -> Term
  -> Term
  -> Maybe Term
specializeTraitMemberStorageType outerDepth parameterCount arguments dictionary memberType
  | length arguments /= parameterCount = Nothing
  | otherwise = discardEvidence memberType >>= specializePrefix (arguments ++ [dictionary])
  where
    discardEvidence = \case
      CPiEvidenceM _ _ Impl Q0 False _ (Just _) _ _ codomain
        | not (mentionsTopBinder codomain) ->
            discardEvidence (shiftTerm (-1) 0 codomain)
      residual -> Just residual

    specializePrefix [] residual = Just residual
    specializePrefix (argument : rest) residual = case residual of
      CPiEvidenceM _ _ Impl _ _ _ Nothing _ _ codomain ->
        specializePrefix rest
          (substTopTermAt outerDepth argument codomain)
      _ -> Nothing

    mentionsTopBinder = getAny . foldTermWithDepth occurrence 0
      where
        occurrence depth = \case
          CVar index | index == depth -> Any True
          _ -> mempty

-- | Fold over a term and all term-bearing do-kernel children.  The first
-- function observes every 'Term'; the second observes every 'KItem'.  Binder
-- depth is intentionally not exposed here; use 'foldTermWithDepth' when a query
-- cares about de Bruijn levels.
foldTerm :: Monoid m => (Term -> m) -> (KItem -> m) -> Term -> m
foldTerm termF itemF = go
  where
    go t = termF t <> case t of
      CVar _ -> mempty
      CLocal _ _ -> mempty
      CGlobal _ _ -> mempty
      CLamM _ _ _ _ b -> go b
      CPiEvidenceM _ _ _ _ _ _ _ _ a b -> go a <> go b
      CApp _ f a -> go f <> go a
      CSort _ -> mempty
      CLevel _ -> mempty
      CUniverseLift _ _ _ t' -> go t'
      CSchemaLift _ _ _ _ _ _ sourceArguments targetArguments t' ->
        foldMap go sourceArguments <> foldMap go targetArguments <> go t'
      CLit _ -> mempty
      CCtorI _ _ ann arguments -> foldMap go ann <> foldMap (go . caTerm) arguments
      CMatch s ann alts -> go s <> foldMap go ann <> foldMap goAlt alts
      CRecordTQ fs -> foldMap (go . rfType) fs
      CRecordV fs -> foldMap (go . snd) fs
      CProjM _ e _ -> go e
      CProjAtM _ e _ _ -> go e
      CVariantT ms -> foldMap go ms
      CInject _ e -> go e
      CLetM _ _ _ a b c -> go a <> go b <> go c
      CLetRecM _ _ _ a b c -> go a <> go b <> go c
      CLetPolyM _ _ _ _ a b c -> go a <> go b <> go c
      CLetRecPolyM _ _ _ _ a b c -> go a <> go b <> go c
      CLetRecGroupM _ definitions body ->
        foldMap (\definition -> go (clrdType definition) <> go (clrdRhs definition)) definitions <> go body
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
      KBind _ _ t _ -> go t
      KLet _ _ t -> go t
      KLetQ _ t m -> go t <> foldMap (go . snd) m
      KExpr t -> go t
      KVarItem _ initT actT _ -> go initT <> go actT
      KAssign lhs _ rhs actT _ -> go lhs <> go rhs <> go actT
      KReturn t -> go t
      KBreak _ -> mempty
      KContinue _ -> mempty
      KWhile _ c b e -> goCond c <> foldMap goK b <> foldMap (foldMap goK) e
      KFor _ _ s b e -> go s <> foldMap goK b <> foldMap (foldMap goK) e
      KIf alts e -> foldMap (\(c, b) -> go c <> foldMap goK b) alts <> foldMap (foldMap goK) e
      KDefer _ t -> go t
      KUsing _ a r -> go a <> go r
      KSubDo _ b -> foldMap goK b

    goCond = \case
      KCondPure t -> go t
      KCondAction t -> go t

-- | Depth-aware fold over the pure Core term tree.  This intentionally treats
-- suspended do-kernel bodies as opaque, matching the de Bruijn assumptions used
-- by shifting/substitution and free-index queries in the checker.
foldTermWithDepth :: Monoid m => (Int -> Term -> m) -> Int -> Term -> m
foldTermWithDepth termF = go
  where
    goItems _ [] = mempty
    goItems d (item : rest) =
      let (current, d') = goItem d item
       in current <> goItems d' rest

    goItem d = \case
      KBind _ pattern' action _ -> (go d action, d + patBindersC pattern')
      KLet _ pattern' value -> (go d value, d + patBindersC pattern')
      KLetQ pattern' value mElse ->
        ( go d value
            <> foldMap (\(rejectionPattern, rejection) -> go (d + patBindersC rejectionPattern) rejection) mElse
        , d + patBindersC pattern'
        )
      KExpr term -> (go d term, d)
      KVarItem _ initial action _ -> (go d initial <> go d action, d + 1)
      KAssign root _ value action _ -> (go d root <> go d value <> go d action, d)
      KReturn term -> (go d term, d)
      KBreak {} -> (mempty, d)
      KContinue {} -> (mempty, d)
      KWhile _ condition body mElse ->
        (goCondition d condition <> goItems d body <> foldMap (goItems d) mElse, d)
      KFor _ pattern' source body mElse ->
        (go d source <> goItems (d + patBindersC pattern') body <> foldMap (goItems d) mElse, d)
      KIf alternatives mElse ->
        ( foldMap (\(condition, body) -> go d condition <> goItems d body) alternatives
            <> foldMap (goItems d) mElse
        , d
        )
      KDefer _ action -> (go d action, d)
      KUsing _ acquire release -> (go d acquire <> go d release, d)
      KSubDo _ body -> (goItems d body, d)

    goCondition d = \case
      KCondPure condition -> go d condition
      KCondAction condition -> go d condition

    go d t = termF d t <> case t of
      CVar _ -> mempty
      CLocal _ _ -> mempty
      CGlobal _ _ -> mempty
      CLamM _ _ _ _ b -> go (d + 1) b
      CPiEvidenceM _ _ _ _ _ _ _ _ a b -> go d a <> go (d + 1) b
      CApp _ f a -> go d f <> go d a
      CSort _ -> mempty
      CLevel _ -> mempty
      CUniverseLift _ _ _ t' -> go d t'
      CSchemaLift _ _ _ _ _ _ sourceArguments targetArguments t' ->
        foldMap (go d) sourceArguments <> foldMap (go d) targetArguments <> go d t'
      CLit _ -> mempty
      CCtorI _ _ ann arguments -> foldMap (go d) ann <> foldMap (go d . caTerm) arguments
      CMatch s ann alts -> go d s <> foldMap (go d) ann <> foldMap (goAlt d) alts
      CRecordTQ fs -> foldMap (go d . rfType) fs
      CRecordV fs -> foldMap (go d . snd) fs
      CProjM _ e _ -> go d e
      CProjAtM _ e _ _ -> go d e
      CVariantT ms -> foldMap (go d) ms
      CInject _ e -> go d e
      CLetM _ _ _ a b c -> go d a <> go d b <> go (d + 1) c
      CLetRecM _ _ _ a b c -> go d a <> go (d + 1) b <> go (d + 1) c
      CLetPolyM _ _ _ _ a b c -> go d a <> go d b <> go (d + 1) c
      CLetRecPolyM _ _ _ _ a b c -> go d a <> go (d + 1) b <> go (d + 1) c
      CLetRecGroupM _ definitions body ->
        let d' = d + length definitions
         in foldMap (\definition -> go d (clrdType definition) <> go d' (clrdRhs definition)) definitions
              <> go d' body
      CMeta _ -> mempty
      CDo _ items -> goItems d items
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
mapTermWithDepth f = mapTermAndPatternsWithDepth f id

-- | Rewrite the declaration-universe spine of every constructor pattern in a
-- term, including patterns nested in do-kernel items. Constructor patterns
-- are not child 'Term' nodes, so a term-only traversal cannot keep them in
-- sync when provisional declaration instances are projected to finalized
-- schemas.
mapPatternConstructorUniverses
  :: (GName -> [Level] -> [Level])
  -> Term
  -> Term
mapPatternConstructorUniverses rewrite =
  mapTermAndPatternsWithDepth (\_ _ -> Nothing) (goPattern rewrite) 0
  where
    goPattern transform = \case
      CPWild -> CPWild
      CPVarM mode name -> CPVarM mode name
      CPLit literal -> CPLit literal
      CPCtorM existentialModes constructor universes patterns ->
        CPCtorM
          existentialModes
          constructor
          (transform constructor universes)
          (map (goPattern transform) patterns)
      CPTuple patterns -> CPTuple (map (goPattern transform) patterns)
      CPRecordM fields rest ->
        CPRecordM
          [(name, goPattern transform pattern') | (name, pattern') <- fields]
          rest
      CPInject tag pattern' -> CPInject tag (goPattern transform pattern')
      CPInjectRestM mode tags -> CPInjectRestM mode tags
      CPOr patterns permutations ->
        CPOr (map (goPattern transform) patterns) permutations
      CPAsM mode name pattern' ->
        CPAsM mode name (goPattern transform pattern')

-- The pattern callback must preserve binder count. This is deliberately
-- internal; the exported pattern operation above changes only universe
-- instantiations and therefore satisfies that invariant.
mapTermAndPatternsWithDepth
  :: (Int -> Term -> Maybe Term)
  -> (CorePat -> CorePat)
  -> Int
  -> Term
  -> Term
mapTermAndPatternsWithDepth f rewritePattern = go
  where
    goItems _ [] = []
    goItems d (item : rest) =
      let (item', d') = goItem d item
       in item' : goItems d' rest

    goItem d = \case
      KBind q p t w ->
        let p' = rewritePattern p
         in (KBind q p' (go d t) w, d + patBindersC p')
      KLet q p t ->
        let p' = rewritePattern p
         in (KLet q p' (go d t), d + patBindersC p')
      KLetQ p t mElse ->
        let p' = rewritePattern p
            rewriteRecovery (rp, e) =
              let rp' = rewritePattern rp
               in (rp', go (d + patBindersC rp') e)
         in
          ( KLetQ p' (go d t) (fmap rewriteRecovery mElse)
          , d + patBindersC p'
          )
      KExpr t -> (KExpr (go d t), d)
      KVarItem n initT actT w -> (KVarItem n (go d initT) (go d actT) w, d + 1)
      KAssign root monadic rhs action w ->
        (KAssign (go d root) monadic (go d rhs) (go d action) w, d)
      KReturn t -> (KReturn (go d t), d)
      item@KBreak {} -> (item, d)
      item@KContinue {} -> (item, d)
      KWhile label condition body mElse ->
        (KWhile label (goCondition d condition) (goItems d body) (fmap (goItems d) mElse), d)
      KFor label p source body mElse ->
        let p' = rewritePattern p
         in
          ( KFor label p' (go d source)
              (goItems (d + patBindersC p') body)
              (fmap (goItems d) mElse)
          , d
          )
      KIf alternatives mElse ->
        (KIf [(go d condition, goItems d body) | (condition, body) <- alternatives] (fmap (goItems d) mElse), d)
      KDefer label action -> (KDefer label (go d action), d)
      KUsing p acquire release ->
        (KUsing (rewritePattern p) (go d acquire) (go d release), d)
      KSubDo label body -> (KSubDo label (goItems d body), d)

    goCondition d = \case
      KCondPure t -> KCondPure (go d t)
      KCondAction t -> KCondAction (go d t)

    go d t = case f d t of
      Just t' -> t'
      Nothing -> case t of
        CVar i -> CVar i
        CLocal i universes -> CLocal i universes
        CGlobal g universes -> CGlobal g universes
        CLamM mode ic q n b -> CLamM mode ic q n (go (d + 1) b)
        CPiEvidenceM mode formation ic q brw n assumption origin a b ->
          CPiEvidenceM mode formation ic q brw n assumption origin (go d a) (go (d + 1) b)
        CApp ic fn a -> CApp ic (go d fn) (go d a)
        CSort u -> CSort u
        CLevel u -> CLevel u
        CUniverseLift from to evidence t' ->
          CUniverseLift from to evidence (go d t')
        CSchemaLift family source target roles evidence certificate sourceArguments targetArguments t' ->
          CSchemaLift family source target roles evidence certificate
            (map (go d) sourceArguments) (map (go d) targetArguments) (go d t')
        CLit l -> CLit l
        CCtorI g universes ann arguments ->
          CCtorI g universes (fmap (go d) ann) (map (\argument -> argument {caTerm = go d (caTerm argument)}) arguments)
        CMatch s ann alts -> CMatch (go d s) (fmap (go d) ann) (map (goAlt d) alts)
        CRecordTQ fs -> CRecordTQ (map (fmap (go d)) fs)
        CRecordV fs -> CRecordV [(n, go d x) | (n, x) <- fs]
        CProjM mode e n -> CProjM mode (go d e) n
        CProjAtM mode e n i -> CProjAtM mode (go d e) n i
        CVariantT ms -> CVariantT (map (go d) ms)
        CInject tag e -> CInject tag (go d e)
        CLetM mode q n a b c -> CLetM mode q n (go d a) (go d b) (go (d + 1) c)
        CLetRecM mode q n a b c -> CLetRecM mode q n (go d a) (go (d + 1) b) (go (d + 1) c)
        CLetPolyM mode q n telescope a b c ->
          CLetPolyM mode q n telescope (go d a) (go d b) (go (d + 1) c)
        CLetRecPolyM mode q n telescope a b c ->
          CLetRecPolyM mode q n telescope (go d a) (go (d + 1) b) (go (d + 1) c)
        CLetRecGroupM telescope definitions body ->
          let d' = d + length definitions
           in CLetRecGroupM telescope
                [ definition
                    { clrdType = go d (clrdType definition)
                    , clrdRhs = go d' (clrdRhs definition)
                    }
                | definition <- definitions
                ]
                (go d' body)
        CMeta m -> CMeta m
        CDo lbl items -> CDo lbl (goItems d items)
        CSealE ls e -> CSealE ls (go d e)
        CSigT ls e -> CSigT ls (go d e)
        CThunkE e -> CThunkE (go d e)
        CLazyE e -> CLazyE (go d e)
        CForceE e -> CForceE (go d e)
        CIf a b c -> CIf (go d a) (go d b) (go d c)
        CQuote qs slots -> CQuote qs (map (go d) slots)

    goAlt d (CaseAlt p gd b) =
      let p' = rewritePattern p
          d' = d + patBindersC p'
       in CaseAlt p' (go d' <$> gd) (go d' b)

-- | Number of de Bruijn binders introduced by a core pattern.  This is the
-- structural binder count used when descending into match guards/bodies and
-- do-kernel binders.  Keep the semantics aligned with the pattern elaborator:
-- residual record binders count only when they are named, and residual variant
-- rest patterns bind one value.
patBindersC :: CorePat -> Int
patBindersC = \case
  CPWild -> 0
  CPVarM _ _ -> 1
  CPLit _ -> 0
  -- @nEx@ existential-skolem placeholder slots (§17.1) sit below the field
  -- binders; they push real runtime slots, so they count.
  CPCtorM existentialModes _ _ ps -> length existentialModes + sum (map patBindersC ps)
  CPTuple ps -> sum (map patBindersC ps)
  CPRecordM fs rest -> sum (map (patBindersC . snd) fs) + case rest of
    Just (_, nm) | not (T.null nm) -> 1
    _ -> 0
  CPInject _ p -> patBindersC p
  CPInjectRestM _ _ -> 1
  CPOr ps _ -> case ps of
    p : _ -> patBindersC p
    [] -> 0
  CPAsM _ _ p -> 1 + patBindersC p

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
  CLocal i universes
    | i >= d -> Just (CLocal (i + by) universes)
  _ -> Nothing

-- | Weaken a term under a newly inserted binder while transporting the
-- absolute local identities carried by universe metadata. Plain 'shiftTerm'
-- is sufficient for Core variables, but level assumptions, lift evidence,
-- neutral level atoms, and record-field metadata use de Bruijn /levels/ and
-- therefore need the matching insertion at @outerDepth@.
weakenTermUnderBinderAt :: Int -> Term -> Term
weakenTermUnderBinderAt outerDepth =
  zonkTermWith (\_ _ -> Nothing) (weakenLevelLocalsAt outerDepth) 0
    . shiftTerm 1 0

-- | Substitute an argument for the outermost binder in a body.
substTopTerm :: Term -> Term -> Term
substTopTerm = substTopTermAt 0

-- | Substitute an argument for the innermost binder of a body whose enclosing
-- context has the supplied depth.  Kappa level variables use de Bruijn
-- /levels/ (outermost first), so ordinary de Bruijn-index substitution is not
-- sufficient: every level occurrence rooted at the removed binder and every
-- replayable lift-evidence endpoint must move with the term substitution.
--
-- A TypeLevel argument is expected to have reached one of the canonical Core
-- level forms below.  If it has not, a rooted level occurrence is deliberately
-- left out of scope; the finalized-Core checkpoint then rejects it rather than
-- silently retargeting the level to a different binder.
substTopTermAt :: Int -> Term -> Term -> Term
substTopTermAt outerDepth arg body =
  zonkTermWith (\_ _ -> Nothing) rewriteLevel 0 termSubstituted
  where
    termSubstituted = shiftTerm (-1) 0 (substTerm 0 (shiftTerm 1 0 arg) body)
    replacementLevel = termAsLevel outerDepth arg
    replacementNeutral =
      maybe
        (NLTUnsupported ("unserializable-substitution:" <> T.pack (show arg)))
        id
        (coreToNeutralLevelTerm outerDepth arg)

    rewriteLevel = normalizeLevel . goLevel

    goLevel = \case
      LZero -> LZero
      LFinite n -> LFinite n
      LOmega -> LOmega
      LSucc level -> LSucc (goLevel level)
      LAdd left right -> LAdd (goLevel left) (goLevel right)
      LMax left right -> LMax (goLevel left) (goLevel right)
      LNeutral atom -> LNeutral (rewriteNeutralAtom atom)
      LVar level
        | level == outerDepth -> maybe (LVar level) id replacementLevel
        | level > outerDepth -> LVar (level - 1)
        | otherwise -> LVar level
      LProjection level fields
        | level == outerDepth ->
            maybe (LProjection level fields) (`projectLevel` fields) replacementLevel
        | level > outerDepth -> LProjection (level - 1) fields
        | otherwise -> LProjection level fields
      LParam parameter -> LParam parameter
      LField identity field -> LField identity field
      LMeta meta -> LMeta meta

    rewriteNeutralAtom = \case
      NeutralLevelSymbol identity arguments ->
        NeutralLevelSymbol identity (map goLevel arguments)
      NeutralLevelTermAtom _ term ->
        neutralLevelTermAtom (rewriteNeutralTerm term)

    rewriteNeutralTerm = \case
      NLTLocal level
        | level == outerDepth -> replacementNeutral
        | level > outerDepth -> NLTLocal (level - 1)
        | otherwise -> NLTLocal level
      NLTLocalDeclaration level universes
        | level == outerDepth -> replacementNeutral
        | level > outerDepth -> NLTLocalDeclaration (level - 1) (map goLevel universes)
        | otherwise -> NLTLocalDeclaration level (map goLevel universes)
      NLTGlobal owner name universes -> NLTGlobal owner name (map goLevel universes)
      NLTConstruct owner name universes arguments ->
        NLTConstruct owner name (map goLevel universes)
          [(explicit, rewriteNeutralTerm argument) | (explicit, argument) <- arguments]
      NLTApply explicit function argument ->
        NLTApply explicit (rewriteNeutralTerm function) (rewriteNeutralTerm argument)
      NLTProject field receiver -> NLTProject field (rewriteNeutralTerm receiver)
      NLTLevel level -> NLTLevel (goLevel level)
      NLTLiteral literal -> NLTLiteral literal
      NLTRecord fields -> NLTRecord [(field, rewriteNeutralTerm value) | (field, value) <- fields]
      NLTIf condition thenBranch elseBranch ->
        NLTIf (rewriteNeutralTerm condition) (rewriteNeutralTerm thenBranch) (rewriteNeutralTerm elseBranch)
      NLTUnsupported reason -> NLTUnsupported reason

    projectLevel replacement [] = replacement
    projectLevel (LVar level) fields = LProjection level fields
    projectLevel (LProjection level prefix) fields = LProjection level (prefix ++ fields)
    projectLevel _ fields = LProjection outerDepth fields

-- | Recover the typed level represented by a finalized Core term in a context
-- of the supplied depth.  The elaborator canonicalizes arithmetic to 'CLevel';
-- the variable/projection cases preserve dependent TypeLevel binders.
termAsLevel :: Int -> Term -> Maybe Level
termAsLevel depth = go []
  where
    go fields = \case
      CUniverseLift _ _ _ inner -> go fields inner
      CSchemaLift _ _ _ _ _ _ _ _ inner -> go fields inner
      CVar index -> rooted index fields
      CLocal index _ -> rooted index fields
      CProjM _ record field -> go (field : fields) record
      CProjAtM _ record field _ -> go (field : fields) record
      CLevel level | null fields -> Just level
      _ -> Nothing

    rooted index fields
      | index < 0 || index >= depth = Nothing
      | null fields = Just (LVar (depth - index - 1))
      | otherwise = Just (LProjection (depth - index - 1) fields)

-- | Convert the serializable, stable Core fragment accepted for an opaque
-- TypeLevel neutral into the solver-independent artifact carried by 'Level'.
-- The caller remains responsible for ordinary typing, totality, stability,
-- and meta-freedom; this function proves only structural serializability and
-- alpha-stable resolved identity.
coreToNeutralLevelTerm :: Int -> Term -> Maybe NeutralLevelTerm
coreToNeutralLevelTerm depth = go
  where
    go = \case
      CVar index -> NLTLocal <$> localLevel index
      CLocal index universes -> NLTLocalDeclaration <$> localLevel index <*> pure universes
      CGlobal (GName (ModuleName owner) name) universes -> pure (NLTGlobal owner name universes)
      CApp icit function argument -> NLTApply (icit == Expl) <$> go function <*> go argument
      CUniverseLift _ _ _ inner -> go inner
      CSchemaLift _ _ _ _ _ _ _ _ inner -> go inner
      CCtorI (GName (ModuleName owner) name) universes _ arguments ->
        NLTConstruct owner name universes
          <$> mapM (\argument -> (caIcit argument == Expl,) <$> go (caTerm argument)) arguments
      CProjM _ receiver field -> NLTProject field <$> go receiver
      CProjAtM _ receiver field _ -> NLTProject field <$> go receiver
      CLevel level -> pure (NLTLevel level)
      CLit literal -> pure (NLTLiteral (literalArtifact literal))
      CRecordV fields -> NLTRecord <$> mapM (\(field, value) -> (field,) <$> go value) fields
      CIf condition thenBranch elseBranch -> NLTIf <$> go condition <*> go thenBranch <*> go elseBranch
      _ -> Nothing

    localLevel index
      | index >= 0 && index < depth = Just (depth - index - 1)
      | otherwise = Nothing

    literalArtifact = \case
      LitInt value -> NLLInt value
      LitDouble value -> NLLDouble value
      LitStr value -> NLLString value
      LitScalar value -> NLLScalar value
      LitByte value -> NLLByte value
      LitBytes value -> NLLBytes (BS.unpack value)
      LitGrapheme value -> NLLGrapheme value

-- | Substitute a replacement for the binder identified by its de Bruijn index at
-- the top level.  The replacement is shifted as traversal moves under binders.
substTerm :: Int -> Term -> Term -> Term
substTerm target replacement = mapTermWithDepth rewrite 0
  where
    rewrite d = \case
      CVar i
        | i == target + d -> Just (shiftTerm d 0 replacement)
      CLocal i _
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
zonkTermWith :: (Int -> MetaId -> Maybe Term) -> (Level -> Level) -> Int -> Term -> Term
zonkTermWith resolveMeta resolveLevel = go Set.empty resolveLevel
  where
    goItems _ _ _ [] = []
    goItems seen resolve d (k : ks) =
      let (k', d') = goItem seen resolve d k
       in k' : goItems seen resolve d' ks

    goItem seen resolve d = \case
      KBind q p t w -> (KBind q (goPat resolve p) (go seen resolve d t) w, d + patBindersC p)
      KLet q p t -> (KLet q (goPat resolve p) (go seen resolve d t), d + patBindersC p)
      KLetQ p t mElse ->
        ( KLetQ (goPat resolve p) (go seen resolve d t) (fmap (\(rp, e) -> (goPat resolve rp, go seen resolve (d + patBindersC rp) e)) mElse)
        , d + patBindersC p
        )
      KExpr t -> (KExpr (go seen resolve d t), d)
      KVarItem n initT actT w -> (KVarItem n (go seen resolve d initT) (go seen resolve d actT) w, d + 1)
      KAssign r monadic rhs actT w -> (KAssign (go seen resolve d r) monadic (go seen resolve d rhs) (go seen resolve d actT) w, d)
      KReturn t -> (KReturn (go seen resolve d t), d)
      k@KBreak {} -> (k, d)
      k@KContinue {} -> (k, d)
      KWhile l c b e -> (KWhile l (goCond seen resolve d c) (goItems seen resolve d b) (fmap (goItems seen resolve d) e), d)
      KFor l p s b e -> (KFor l (goPat resolve p) (go seen resolve d s) (goItems seen resolve (d + patBindersC p) b) (fmap (goItems seen resolve d) e), d)
      KIf alts e -> (KIf [(go seen resolve d c, goItems seen resolve d b) | (c, b) <- alts] (fmap (goItems seen resolve d) e), d)
      KDefer ml t -> (KDefer ml (go seen resolve d t), d)
      KUsing p a r -> (KUsing (goPat resolve p) (go seen resolve d a) (go seen resolve d r), d)
      KSubDo l b -> (KSubDo l (goItems seen resolve d b), d)

    goCond seen resolve d = \case
      KCondPure t -> KCondPure (go seen resolve d t)
      KCondAction t -> KCondAction (go seen resolve d t)

    go seen resolve d = \case
      CMeta m
        | m `Set.member` seen -> CMeta m
        | otherwise -> maybe (CMeta m) (go (Set.insert m seen) resolve d) (resolveMeta d m)
      CVar i -> CVar i
      CLocal i universes -> CLocal i (map resolve universes)
      CGlobal g universes -> CGlobal g (map resolve universes)
      CLamM mode ic q n b -> CLamM mode ic q n (go seen resolve (d + 1) b)
      CPiEvidenceM mode formation ic q brw n assumption origin a b ->
        let assumption' = fmap (bimap resolve resolve) assumption
         in CPiEvidenceM mode formation ic q brw n assumption' origin (go seen resolve d a) (go seen resolve (d + 1) b)
      CApp ic f a -> CApp ic (go seen resolve d f) (go seen resolve d a)
      CSort u -> CSort (resolve u)
      CLevel u -> CLevel (resolve u)
      CUniverseLift from to evidence t ->
        let from' = normalizeLevel (resolve from)
            to' = normalizeLevel (resolve to)
            evidence' = mapUniverseEvidenceLevels resolve evidence
            lifted = universeLift evidence' (go seen resolve d t)
         in case lifted of
              CUniverseLift evidenceFrom evidenceTo _ _
                | (evidenceFrom, evidenceTo) == (from', to') -> lifted
              _ | from' == to' -> lifted
              _ -> CUniverseLift from' to' evidence' (go seen resolve d t)
      CSchemaLift family source target roles evidence certificate sourceArguments targetArguments t ->
        CSchemaLift family (map resolve source) (map resolve target) roles
          (map (mapSchemaRoleEvidence resolve) evidence) certificate
          (map (go seen resolve d) sourceArguments)
          (map (go seen resolve d) targetArguments)
          (go seen resolve d t)
      CLit l -> CLit l
      CCtorI g universes ann arguments ->
        CCtorI g (map resolve universes) (fmap (go seen resolve d) ann)
          (map (\argument -> argument {caTerm = go seen resolve d (caTerm argument)}) arguments)
      CMatch s ann alts ->
        CMatch (go seen resolve d s) (fmap (go seen resolve d) ann)
          [ CaseAlt (goPat resolve p)
              (fmap (go seen resolve (d + patBindersC p)) gd)
              (go seen resolve (d + patBindersC p) b)
          | CaseAlt p gd b <- alts
          ]
      CRecordTQ fs -> CRecordTQ (map (goRecordField seen resolve d) fs)
      CRecordV fs -> CRecordV [(n, go seen resolve d t) | (n, t) <- fs]
      CProjM mode e f -> CProjM mode (go seen resolve d e) f
      CProjAtM mode e f i -> CProjAtM mode (go seen resolve d e) f i
      CVariantT ms -> CVariantT (map (go seen resolve d) ms)
      CInject tg e -> CInject tg (go seen resolve d e)
      CLetM mode q n a b c -> CLetM mode q n (go seen resolve d a) (go seen resolve d b) (go seen resolve (d + 1) c)
      CLetRecM mode q n a b c -> CLetRecM mode q n (go seen resolve d a) (go seen resolve (d + 1) b) (go seen resolve (d + 1) c)
      CLetPolyM mode q n telescope a b c ->
        let scoped = liftLevelResolver (dutParameterCount telescope) resolve
         in CLetPolyM mode q n (resolveTelescope scoped telescope)
              (go seen scoped d a) (go seen scoped d b) (go seen resolve (d + 1) c)
      CLetRecPolyM mode q n telescope a b c ->
        let scoped = liftLevelResolver (dutParameterCount telescope) resolve
         in CLetRecPolyM mode q n (resolveTelescope scoped telescope)
              (go seen scoped d a) (go seen scoped (d + 1) b) (go seen resolve (d + 1) c)
      CLetRecGroupM telescope definitions body ->
        let scoped = liftLevelResolver (dutParameterCount telescope) resolve
            d' = d + length definitions
         in CLetRecGroupM
              (resolveTelescope scoped telescope)
              [ definition
                  { clrdType = go seen scoped d (clrdType definition)
                  , clrdRhs = go seen scoped d' (clrdRhs definition)
                  }
              | definition <- definitions
              ]
              (go seen resolve d' body)
      CDo lbl items -> CDo lbl (goItems seen resolve d items)
      CSealE ls e -> CSealE ls (go seen resolve d e)
      CSigT ls e -> CSigT ls (go seen resolve d e)
      CThunkE e -> CThunkE (go seen resolve d e)
      CLazyE e -> CLazyE (go seen resolve d e)
      CForceE e -> CForceE (go seen resolve d e)
      CIf a b c -> CIf (go seen resolve d a) (go seen resolve d b) (go seen resolve d c)
      CQuote qs slots -> CQuote qs (map (go seen resolve d) slots)

    goRecordField seen resolve d field =
      field
        { rfLevelAssumption = fmap (bimap resolve resolve) (rfLevelAssumption field)
        , rfType = go seen resolve d (rfType field)
        }

    goPat resolve = \case
      CPWild -> CPWild
      CPVarM mode name -> CPVarM mode name
      CPLit literal -> CPLit literal
      CPCtorM existentialModes constructor universes patterns ->
        CPCtorM existentialModes constructor (map resolve universes) (map (goPat resolve) patterns)
      CPTuple patterns -> CPTuple (map (goPat resolve) patterns)
      CPRecordM fields rest -> CPRecordM [(name, goPat resolve pattern') | (name, pattern') <- fields] rest
      CPInject tag pattern' -> CPInject tag (goPat resolve pattern')
      CPInjectRestM mode tags -> CPInjectRestM mode tags
      CPOr patterns permutations -> CPOr (map (goPat resolve) patterns) permutations
      CPAsM mode name pattern' -> CPAsM mode name (goPat resolve pattern')

    resolveTelescope _ telescope = telescope

    -- A local declaration telescope prefixes its own parameters and shifts
    -- every enclosing declaration parameter by its arity. Lift an outer level
    -- substitution through that binder: bound prefix parameters are rigid,
    -- while replacements for outer parameters/metas are shifted to avoid
    -- capture by the local prefix.
    liftLevelResolver count resolve = normalizeLevel . liftLevel
      where
        shifted atom = abstractLocalLevelParams count (resolve atom)
        liftLevel = \case
          LZero -> shifted LZero
          LFinite n -> shifted (LFinite n)
          LOmega -> shifted LOmega
          LSucc level -> LSucc (liftLevel level)
          LAdd left right -> LAdd (liftLevel left) (liftLevel right)
          LMax left right -> LMax (liftLevel left) (liftLevel right)
          LNeutral atom -> LNeutral (mapNeutralLevelAtomLevels liftLevel atom)
          LVar index -> shifted (LVar index)
          LParam parameter
            | parameter < count -> LParam parameter
            | otherwise -> shifted (LParam (parameter - count))
          LField index field -> shifted (LField index field)
          LProjection index fields -> shifted (LProjection index fields)
          LMeta meta -> shifted (LMeta meta)

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
      term -> concatMap levelMetas (termNodeLevels term)

-- | Universe metavariables occurring in level-bearing Core positions.  Term
-- metavariables are deliberately excluded: declaration-universe
-- generalization must never turn an ordinary elaboration hole into a hidden
-- universe parameter merely because both identifiers use the same integer
-- namespace.
levelMetasOfTerm :: Term -> [LevelMeta]
levelMetasOfTerm = nub . foldTerm here item
  where
    here = concatMap levelMetas . termNodeLevels
    item = concatMap levelMetas . itemPatternLevels

-- | Hidden declaration-universe parameters occurring in level-bearing Core
-- positions.  This is the rigid counterpart of 'levelMetasOfTerm' and is used
-- by built-in/interface verification to derive and validate telescope arity.
levelParamsOfTerm :: Term -> [Int]
levelParamsOfTerm = nub . foldTerm here item
  where
    here = concatMap levelParams . termNodeLevels
    item = concatMap levelParams . itemPatternLevels

-- | Every level-bearing position stored directly on a Core node. Keep proof
-- assumption metadata in this shared inventory: it is authenticated static
-- input, not an annotation that meta collection or scope validation may skip.
termNodeLevels :: Term -> [Level]
termNodeLevels = \case
  CGlobal _ universes -> universes
  CLocal _ universes -> universes
  CPiEvidenceM _ _ _ _ _ _ relation _ _ _ -> maybe [] (\(lower, upper) -> [lower, upper]) relation
  CSort level -> [level]
  CLevel level -> [level]
  CUniverseLift from to evidence _ ->
    from : to : universeEvidenceLevels evidence
  CSchemaLift _ source target _ evidence _ _ _ _ ->
    source ++ target ++ concatMap schemaRoleEvidenceLevels evidence
  CCtorI _ universes _ _ -> universes
  CMatch _ _ alternatives ->
    concatMap (corePatternLevels . caPat) alternatives
  CRecordTQ fields ->
    concatMap
      (maybe [] (\(lower, upper) -> [lower, upper]) . rfLevelAssumption)
      fields
  _ -> []

-- | Universe spines in Core patterns are semantic level-bearing positions.
-- They are not child 'Term's, so the generic term folds cannot discover them.
-- Keep this query shared by meta collection and finalized-parameter scope
-- checking; otherwise pattern occurrences become invisible to declaration
-- principalization but remain visible to backend validation.
corePatternLevels :: CorePat -> [Level]
corePatternLevels = \case
  CPCtorM _ _ universes patterns -> universes ++ concatMap corePatternLevels patterns
  CPTuple patterns -> concatMap corePatternLevels patterns
  CPRecordM fields _ -> concatMap (corePatternLevels . snd) fields
  CPInject _ pattern' -> corePatternLevels pattern'
  CPOr patterns _ -> concatMap corePatternLevels patterns
  CPAsM _ _ pattern' -> corePatternLevels pattern'
  _ -> []

itemPatternLevels :: KItem -> [Level]
itemPatternLevels = \case
  KBind _ pattern' _ _ -> corePatternLevels pattern'
  KLet _ pattern' _ -> corePatternLevels pattern'
  KLetQ pattern' _ recovery ->
    corePatternLevels pattern'
      ++ maybe [] (corePatternLevels . fst) recovery
  KFor _ pattern' _ _ _ -> corePatternLevels pattern'
  KUsing pattern' _ _ -> corePatternLevels pattern'
  _ -> []

-- | Whether a term has no free de Bruijn variables and no metavariables.
-- Do-kernels are rejected as reusable evidence because their sequential
-- bindings and control-flow effects are not pure proof terms.
termClosed :: Term -> Bool
termClosed = getAll . foldTermWithDepth here 0
  where
    here d = \case
      CVar i -> All (i >= 0 && i < d)
      CLocal i _ -> All (i >= 0 && i < d)
      CMeta _ -> All False
      CDo _ _ -> All False
      _ -> mempty

-- | Whether every de Bruijn index is valid in an ambient context of the given
-- depth. Unlike 'maxFreeIndexTerm', this also rejects negative recovery indices.
-- Metavariables and do-kernels are permitted: this predicate is solely about
-- lexical scope.
termScopedAt :: Int -> Term -> Bool
termScopedAt ambient = getAll . foldTermWithDepth here ambient
  where
    here depth = \case
      CVar index -> All (index >= 0 && index < depth)
      CLocal index _ -> All (index >= 0 && index < depth)
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
          KBind _ _ t _ -> go (next n) t
          KLet _ _ t -> go (next n) t
          KLetQ _ t m -> go (next n) t || maybe False (go (next n) . snd) m
          KExpr t -> go (next n) t
          KVarItem _ initT actT _ -> go (next n) initT || go (next n) actT
          KAssign lhs _ rhs actT _ -> go (next n) lhs || go (next n) rhs || go (next n) actT
          KReturn t -> go (next n) t
          KBreak _ -> False
          KContinue _ -> False
          KWhile _ c b e ->
            goCond (next n) c
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
          CUniverseLift _ _ _ t' -> go (next n) t'
          CSchemaLift _ _ _ _ _ _ sourceArguments targetArguments t' ->
            any (go (next n)) sourceArguments
              || any (go (next n)) targetArguments
              || go (next n) t'
          CLam _ _ _ b -> go (next n) b
          CPi _ _ _ _ a b -> go (next n) a || go (next n) b
          CCtorI _ _ _ arguments -> any (go (next n) . caTerm) arguments
          CMatch scrut _ alts ->
            go (next n) scrut
              || any (\(CaseAlt _ gd b) -> maybe False (go (next n)) gd || go (next n) b) alts
          CRecordTQ fs -> any (go (next n) . rfType) fs
          CRecordV fs -> any (go (next n) . snd) fs
          CProj e _ -> go (next n) e
          CProjAt e _ _ -> go (next n) e
          CVariantT ms -> any (go (next n)) ms
          CInject _ e -> go (next n) e
          CLet _ _ a b c -> go (next n) a || go (next n) b || go (next n) c
          CLetRec _ _ a b c -> go (next n) a || go (next n) b || go (next n) c
          CLetPolyM _ _ _ _ a b c -> go (next n) a || go (next n) b || go (next n) c
          CLetRecPolyM _ _ _ _ a b c -> go (next n) a || go (next n) b || go (next n) c
          CLetRecGroupM _ definitions body ->
            any (\definition -> go (next n) (clrdType definition) || go (next n) (clrdRhs definition)) definitions
              || go (next n) body
          CIf a b c -> go (next n) a || go (next n) b || go (next n) c
          CThunkE e -> go (next n) e
          CLazyE e -> go (next n) e
          CForceE e -> go (next n) e
          CSealE _ e -> go (next n) e
          CSigT _ e -> go (next n) e
          CQuote _ slots -> any (go (next n)) slots
          CDo _ items -> any (goK (next n)) items
          _ -> False

    goCond n = \case
      KCondPure t -> go n t
      KCondAction t -> go n t

universeEvidenceLevels :: UniverseEvidence -> [Level]
universeEvidenceLevels (UniverseEvidence steps) =
  concat
    [ uesLower : uesUpper : concatMap (\(a, b) -> [a, b]) uesAssumptions
    | UniverseEvidenceStep {..} <- steps
    ]

schemaRoleEvidenceLevels :: SchemaRoleEvidence -> [Level]
schemaRoleEvidenceLevels = \case
  SchemaInvariantEvidence -> []
  SchemaCovariantEvidence evidence -> universeEvidenceLevels evidence
  SchemaIrrelevantEvidence -> []

mapSchemaRoleEvidence :: (Level -> Level) -> SchemaRoleEvidence -> SchemaRoleEvidence
mapSchemaRoleEvidence resolve = \case
  SchemaInvariantEvidence -> SchemaInvariantEvidence
  SchemaCovariantEvidence evidence -> SchemaCovariantEvidence (mapUniverseEvidenceLevels resolve evidence)
  SchemaIrrelevantEvidence -> SchemaIrrelevantEvidence

-- | Global names mentioned by a term.  Constructor heads count as globals; do
-- items are traversed through 'foldTerm'.
globalsOfTerm :: Term -> Set GName
globalsOfTerm = foldTerm here (const Set.empty)
  where
    here = \case
      CGlob g -> Set.singleton g
      CCtorI g _ _ _ -> Set.singleton g
      _ -> Set.empty

-- | Split a left-associated application spine into its head and ordered
-- arguments.
spineOfTerm :: Term -> (Term, [(Icit, Term)])
spineOfTerm = go []
  where
    go acc (CApp ic f a) = go ((ic, a) : acc) f
    go acc f = (f, acc)
