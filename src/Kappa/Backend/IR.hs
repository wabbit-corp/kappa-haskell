{-# LANGUAGE BangPatterns #-}

-- | KBackendIR Phase A: a target-neutral runtime tree.
--
-- This module is deliberately not an annotated 'Kappa.Core.Term'. The lowering
-- constructs a separate recursive datatype whose runtime children are already
-- erased: q0/kind-domain binders are not KBackendIR binders, erased call
-- arguments are not KBackendIR arguments, and type/proof-only subterms that
-- still reach runtime value position are recorded as lowering violations before
-- target emission.
module Kappa.Backend.IR
  ( BackendNodeId (..)
  , BackendBinderId (..)
  , BackendUseId (..)
  , KBackendIR (..)
  , BackendBody (..)
  , BackendParam (..)
  , BackendTerm (..)
  , BackendPat (..)
  , backendPatToCorePat
  , BackendAlt (..)
  , BackendItem (..)
  , BackendCond (..)
  , BackendMeta (..)
  , BackendBinder (..)
  , BackendUse (..)
  , BackendCtorLayout (..)
  , BackendIRViolation (..)
  , lowerKBackendIR
  , validateKBackendIR
  ) where

import Control.Applicative ((<|>))
import Control.Monad (forM, forM_, when)
import Control.Monad.Reader
import Control.Monad.State.Strict
import Data.List (elemIndex, sort)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes, fromMaybe, listToMaybe, mapMaybe)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T

import qualified Kappa.Backend.Repr as Repr
import Kappa.Backend.Repr (ArgConv, CtorLayoutInfo (..))
import Kappa.Check (CheckState (..), CtorInfo (..), TraitInfo (..))
import Kappa.Core
import Kappa.CoreOps (spineOfTerm)
import Kappa.Eval (EvalCtx (..), GlobalDef (..), Globals (..), eval, force, quote)
import Kappa.Ownership
  ( BinderOwn (..)
  , UseKind (..)
  )
import Kappa.Pretty (renderTerm)

data ParamLowerSite = ParamLowerSite
  { plsIcit :: !Icit
  , plsQ :: !Q
  , plsBorrowed :: !Bool
  , plsErased :: !Bool
  , plsDomain :: !Value
  }
  deriving stock (Show)

newtype BackendNodeId = BackendNodeId Int
  deriving stock (Eq, Ord, Show)

newtype BackendBinderId = BackendBinderId Int
  deriving stock (Eq, Ord, Show)

newtype BackendUseId = BackendUseId Int
  deriving stock (Eq, Ord, Show)

data KBackendIR = KBackendIR
  { kbirBodies :: !(Map GName BackendBody)
  , kbirLoweringViolations :: ![BackendIRViolation]
  }
  deriving stock (Eq, Show)

data BackendBody = BackendBody
  { bbOwner :: !GName
  , bbParams :: ![BackendParam]
  , bbRoot :: !BackendTerm
  }
  deriving stock (Eq, Show)

data BackendParam = BackendParam
  { bpIcit :: !Icit
  , bpName :: !Text
  , bpBinder :: !(Maybe BackendBinder)
  }
  deriving stock (Eq, Show)

data BackendMeta = BackendMeta
  { bmNodeId :: !BackendNodeId
  , bmBranchDrops :: ![BackendBinder]
  }
  deriving stock (Eq, Show)

data BackendBinder = BackendBinder
  { bbBinderId :: !BackendBinderId
  , bbBinderOrigin :: !Text
  , bbBinderOwn :: !BinderOwn
  , bbBinderHasConsumingLastUse :: !Bool
  }
  deriving stock (Eq, Show)

data BackendUse = BackendUse
  { buUseId :: !BackendUseId
  , buUseKind :: !UseKind
  , buConsumes :: !Bool
  }
  deriving stock (Eq, Show)

data BackendCtorLayout = BackendCtorLayout
  { bclCtor :: !GName
  , bclInfo :: !(Maybe CtorLayoutInfo)
  , bclRuntimeFields :: !Int
  }
  deriving stock (Eq, Show)

data BackendIRViolation = BackendIRViolation
  { bivBody :: !GName
  , bivNode :: !BackendNodeId
  , bivCode :: !Text
  , bivMessage :: !Text
  }
  deriving stock (Eq, Show)

data BackendTerm
  = BUnit !BackendMeta
  | BVar !BackendMeta !(Maybe BackendUse) !Int
  | BGlob !BackendMeta !GName
  | BLit !BackendMeta !Literal
  | BLam !BackendMeta !(Maybe BackendBinder) !Icit !Q !Text !BackendTerm
  | BApp !BackendMeta !BackendTerm ![(Icit, Maybe ArgConv, BackendTerm)]
  | BCtor !BackendMeta !BackendCtorLayout ![BackendTerm]
  | BMatch !BackendMeta !BackendTerm ![BackendAlt] ![(GName, BackendCtorLayout)]
  | BRecord !BackendMeta ![(Text, BackendTerm)]
  | BProj !BackendMeta !BackendTerm !Text !(Maybe Int)
  | BInject !BackendMeta !Text !BackendTerm
  | BLet !BackendMeta !(Maybe BackendBinder) !Q !Text !BackendTerm !BackendTerm
  | BLetRec !BackendMeta !(Maybe BackendBinder) !Q !Text !BackendTerm !BackendTerm
  | BDo !BackendMeta !(Maybe Text) ![BackendItem]
  | BSeal !BackendMeta ![Text] !BackendTerm
  | BThunk !BackendMeta !BackendTerm
  | BLazy !BackendMeta !BackendTerm
  | BForce !BackendMeta !BackendTerm
  | BIf !BackendMeta !BackendTerm !BackendTerm !BackendTerm
  deriving stock (Eq, Show)

data BackendAlt = BackendAlt
  { baMeta :: !BackendMeta
  , baPat :: !BackendPat
  , baBinders :: ![Maybe BackendBinder]
  , baGuard :: !(Maybe BackendTerm)
  , baBody :: !BackendTerm
  }
  deriving stock (Eq, Show)

data BackendPat
  = BPWild
  | BPVar !Text
  | BPLit !Literal
  | BPCtor !GName ![BackendPat]
  | BPTuple ![BackendPat]
  | BPRecord ![(Text, BackendPat)] !(Maybe Text)
  | BPInject !Text !BackendPat
  | BPInjectRest ![Text]
  | BPOr ![BackendPat] ![[Int]]
  | BPAs !Text !BackendPat
  deriving stock (Eq, Show)

data BackendItem
  = BKBind !BackendMeta !Q !BackendPat ![Maybe BackendBinder] !BackendTerm !(Maybe RefActionWitness)
  | BKLet !BackendMeta !Q !BackendPat ![Maybe BackendBinder] !BackendTerm
  | BKLetQ !BackendMeta !BackendPat ![Maybe BackendBinder] !BackendTerm !(Maybe (BackendPat, [Maybe BackendBinder], BackendTerm))
  | BKExpr !BackendMeta !BackendTerm
  | BKVarItem !BackendMeta !(Maybe BackendBinder) !BackendTerm !BackendTerm !(Maybe RefActionWitness)
  | BKAssign !BackendMeta !Bool !BackendTerm !BackendTerm !(Maybe RefActionWitness)
  | BKReturn !BackendMeta !BackendTerm
  | BKWhile !BackendMeta !(Maybe Text) !BackendCond ![BackendItem] !(Maybe [BackendItem])
  | BKFor !BackendMeta !(Maybe Text) !BackendPat ![Maybe BackendBinder] !BackendTerm ![BackendItem] !(Maybe [BackendItem])
  | BKIf !BackendMeta ![(BackendTerm, [BackendItem])] !(Maybe [BackendItem])
  | BKDefer !BackendMeta !(Maybe Text) !BackendTerm
  | BKUsing !BackendMeta !BackendPat ![Maybe BackendBinder] !BackendTerm !BackendTerm
  | BKSubDo !BackendMeta !(Maybe Text) ![BackendItem]
  | BKBreak !BackendMeta !(Maybe Text)
  | BKContinue !BackendMeta !(Maybe Text)
  deriving stock (Eq, Show)

data BackendCond
  = BKCondPure !BackendTerm
  | BKCondAction !BackendTerm
  deriving stock (Eq, Show)

data LowerStatic = LowerStatic
  { lsOwner :: !GName
  , lsGlobals :: !(Map GName GlobalDef)
  , lsCtors :: !(Map GName CtorInfo)
  , lsTraits :: !(Map GName TraitInfo)
  , lsCtx :: !EvalCtx
  }

data LowerState = LowerState
  { lstNextNode :: !Int
  , lstNextBinder :: !Int
  , lstLoweringViolations :: ![BackendIRViolation]
  }

data ScopeSlot = ScopeSlot !(Maybe BackendBinderId) !(Maybe Value)

type ScopeStack = [ScopeSlot]
type Lower = ReaderT LowerStatic (State LowerState)
type BinderEnv = Map BackendBinderId BackendBinder

lowerKBackendIR :: CheckState -> KBackendIR
lowerKBackendIR st =
  let lowered = Map.mapWithKey (lowerBody ctx globals (csCtors st) (csTraits st)) (csCoreBodies st)
   in KBackendIR
        { kbirBodies = Map.map fst lowered
        , kbirLoweringViolations = concatMap snd (Map.elems lowered)
        }
  where
    globals = csGlobals st
    ctx = EvalCtx (Globals globals) (csMetas st) False (csFacts st)

validateKBackendIR :: KBackendIR -> [BackendIRViolation]
validateKBackendIR (KBackendIR bodies loweringViolations) =
  loweringViolations ++ concatMap (uncurry validateBody) (Map.toList bodies)

validateBody :: GName -> BackendBody -> [BackendIRViolation]
validateBody owner body =
  duplicateNodeFindings owner metas
    ++ duplicateBinderFindings owner rootMeta (collectBodyBinders body)
    ++ duplicateUseFindings owner rootMeta (collectBodyUses body)
    ++ concatMap (validateParam owner rootMeta) (bbParams body)
    ++ validateTerm owner (bbRoot body)
    ++ validateBranchDropsTerm owner rootEnv (bbRoot body)
  where
    metas = collectMetas (bbRoot body)
    rootMeta = backendMeta (bbRoot body)
    rootEnv =
      Map.fromList
        [ (bbBinderId b, b)
        | BackendParam _ _ (Just b) <- bbParams body
        ]

validateParam :: GName -> BackendMeta -> BackendParam -> [BackendIRViolation]
validateParam owner rootMeta (BackendParam _ name mb) =
  case mb of
    Just {} -> []
    Nothing ->
      [ violation owner rootMeta "W_BACKENDIR_MISSING_BINDER" $
          "runtime parameter has no backend ownership binder: " <> T.unpack name
      ]

validateBinder :: GName -> BackendMeta -> Text -> Maybe BackendBinder -> [BackendIRViolation]
validateBinder owner meta what = \case
  Just {} -> []
  Nothing ->
    [ violation owner meta "W_BACKENDIR_MISSING_BINDER" $
        T.unpack what <> " has no backend ownership binder"
    ]

validateUse :: GName -> BackendMeta -> Maybe BackendUse -> [BackendIRViolation]
validateUse owner meta = \case
  Just {} -> []
  Nothing ->
    [ violation owner meta "W_BACKENDIR_MISSING_USE" $
        "runtime variable has no backend ownership use"
    ]

validateCtor :: GName -> BackendMeta -> BackendCtorLayout -> [BackendTerm] -> [BackendIRViolation]
validateCtor owner meta layout args =
  fieldCountFinding ++ validateCtorLayout owner meta layout
  where
    fieldCountFinding
      | bclRuntimeFields layout == length args = []
      | otherwise =
          [ violation owner meta "W_BACKENDIR_CTOR_FIELD_MISMATCH" $
              "constructor layout runtime field count "
                <> show (bclRuntimeFields layout)
                <> " does not match lowered field count "
                <> show (length args)
          ]

validateCtorLayout :: GName -> BackendMeta -> BackendCtorLayout -> [BackendIRViolation]
validateCtorLayout owner meta layout =
  case bclInfo layout of
    Nothing -> []
    Just info
      | clArity info == bclRuntimeFields layout
          && length (clFieldReps info) == clArity info
          && clLayoutClass info == Repr.ctorLayout (clFieldReps info)
          && clBoxedFootprintBytes info == expectedFootprint info ->
          []
      | otherwise ->
          [ violation owner meta "W_BACKENDIR_CTOR_LAYOUT_INCONSISTENT" $
              "constructor layout metadata is internally inconsistent or does not match the runtime field count"
          ]
  where
    expectedFootprint info =
      case clLayoutClass info of
        Repr.LayoutImmediate -> Nothing
        Repr.LayoutMayPack -> Just (Repr.ctorBoxedFootprintBytes (clArity info))
        Repr.LayoutBoxed -> Just (Repr.ctorBoxedFootprintBytes (clArity info))

validateTerm :: GName -> BackendTerm -> [BackendIRViolation]
validateTerm owner = \case
  BUnit {} -> []
  BVar meta use _ -> validateUse owner meta use
  BGlob {} -> []
  BLit {} -> []
  BLam meta mb _ _ name body ->
    validateBinder owner meta (T.pack "lambda binder " <> name) mb ++ validateTerm owner body
  BApp _ hd args ->
    validateTerm owner hd ++ concatMap (\(_, _, arg) -> validateTerm owner arg) args
  BCtor meta layout args ->
    validateCtor owner meta layout args ++ concatMap (validateTerm owner) args
  BMatch _ scrut alts layouts ->
    let layoutMap = Map.fromList [(bclCtor layout, layout) | (_, layout) <- layouts]
     in validateTerm owner scrut ++ concatMap (validateAlt owner layoutMap) alts
  BRecord _ fs -> concatMap (validateTerm owner . snd) fs
  BProj _ e _ _ -> validateTerm owner e
  BInject _ _ e -> validateTerm owner e
  BLet meta mb _ name rhs body ->
    validateBinder owner meta (T.pack "let binder " <> name) mb
      ++ validateTerm owner rhs
      ++ validateTerm owner body
  BLetRec meta mb _ name rhs body ->
    validateBinder owner meta (T.pack "letrec binder " <> name) mb
      ++ validateTerm owner rhs
      ++ validateTerm owner body
  BDo _ _ items -> concatMap (validateItem owner) items
  BSeal _ _ e -> validateTerm owner e
  BThunk _ e -> validateTerm owner e
  BLazy _ e -> validateTerm owner e
  BForce _ e -> validateTerm owner e
  BIf _ c th el -> validateTerm owner c ++ validateTerm owner th ++ validateTerm owner el

validateAlt :: GName -> Map GName BackendCtorLayout -> BackendAlt -> [BackendIRViolation]
validateAlt owner layoutMap (BackendAlt meta pat binders guard body) =
  validatePattern owner meta layoutMap pat
    ++ concatMap (validateBinder owner meta (T.pack "pattern binder")) binders
    ++ maybe [] (validateTerm owner) guard
    ++ validateTerm owner body

validatePattern :: GName -> BackendMeta -> Map GName BackendCtorLayout -> BackendPat -> [BackendIRViolation]
validatePattern owner meta layoutMap = \case
  BPWild -> []
  BPVar {} -> []
  BPLit {} -> []
  BPCtor g ps ->
    ctorArityFinding g ps
      ++ concatMap (validatePattern owner meta layoutMap) ps
  BPTuple ps -> concatMap (validatePattern owner meta layoutMap) ps
  BPRecord fs _ -> concatMap (validatePattern owner meta layoutMap . snd) fs
  BPInject _ p -> validatePattern owner meta layoutMap p
  BPInjectRest {} -> []
  BPOr ps _ -> concatMap (validatePattern owner meta layoutMap) ps
  BPAs _ p -> validatePattern owner meta layoutMap p
  where
    ctorArityFinding g ps =
      case Map.lookup g layoutMap of
        Just layout ->
          validateCtorLayout owner meta layout
            ++ [ violation owner meta "W_BACKENDIR_CTOR_PATTERN_FIELD_MISMATCH" $
                  "constructor pattern has "
                    <> show (length ps)
                    <> " runtime field pattern(s), but layout records "
                    <> show (bclRuntimeFields layout)
                    <> " runtime field(s)"
               | length ps /= bclRuntimeFields layout
               ]
        Nothing ->
          [ violation owner meta "W_BACKENDIR_CTOR_PATTERN_LAYOUT_MISSING" $
              "constructor pattern has no matching layout metadata entry for " <> T.unpack (gKey g)
          ]

validateBranchDropsItemMeta :: GName -> BackendMeta -> [BackendIRViolation]
validateBranchDropsItemMeta owner meta
  | null (bmBranchDrops meta) = []
  | otherwise =
      [ violation owner meta "W_BACKENDIR_BRANCH_DROP_UNEMITTED_ITEM" $
          "branch-drop metadata is attached to a do-item node, but native emission only drains branch drops from BackendTerm and BackendAlt nodes"
      ]

validateItem :: GName -> BackendItem -> [BackendIRViolation]
validateItem owner = \case
  BKBind meta _ _ binders action _ ->
    concatMap (validateBinder owner meta (T.pack "do-bind pattern binder")) binders
      ++ validateTerm owner action
  BKLet meta _ _ binders value ->
    concatMap (validateBinder owner meta (T.pack "do-let pattern binder")) binders
      ++ validateTerm owner value
  BKLetQ meta _ binders scrut mElse ->
    concatMap (validateBinder owner meta (T.pack "let? pattern binder")) binders
      ++ validateTerm owner scrut
      ++ maybe
        []
        ( \( _pat
           , ebinders
           , body
           ) ->
            concatMap (validateBinder owner meta (T.pack "let? else pattern binder")) ebinders
              ++ validateTerm owner body
        )
        mElse
  BKExpr _ action -> validateTerm owner action
  BKVarItem meta mb _initT action _ ->
    validateBinder owner meta (T.pack "var binder") mb
      ++ validateTerm owner action
  BKAssign _ _ _rhs action _ -> validateTerm owner action
  BKReturn _ value -> validateTerm owner value
  BKWhile _ _ cond body mElse ->
    validateCond owner cond
      ++ concatMap (validateItem owner) body
      ++ maybe [] (concatMap (validateItem owner)) mElse
  BKFor meta _ _ binders source body mElse ->
    concatMap (validateBinder owner meta (T.pack "for pattern binder")) binders
      ++ validateTerm owner source
      ++ concatMap (validateItem owner) body
      ++ maybe [] (concatMap (validateItem owner)) mElse
  BKIf _ arms mElse ->
    concatMap (\(cond, body) -> validateTerm owner cond ++ concatMap (validateItem owner) body) arms
      ++ maybe [] (concatMap (validateItem owner)) mElse
  BKDefer _ _ action -> validateTerm owner action
  BKUsing meta _ binders acquire release ->
    concatMap (validateBinder owner meta (T.pack "using pattern binder")) binders
      ++ validateTerm owner acquire
      ++ validateTerm owner release
  BKSubDo _ _ body -> concatMap (validateItem owner) body
  BKBreak {} -> []
  BKContinue {} -> []

validateCond :: GName -> BackendCond -> [BackendIRViolation]
validateCond owner = \case
  BKCondPure t -> validateTerm owner t
  BKCondAction t -> validateTerm owner t

validateBranchDropsMeta :: GName -> BinderEnv -> BackendMeta -> [BackendIRViolation]
validateBranchDropsMeta owner env meta =
  duplicateFindings ++ concatMap checkDrop drops
  where
    drops = bmBranchDrops meta
    counts =
      Map.fromListWith
        (+)
        [(bbBinderId b, 1 :: Int) | b <- drops]
    duplicateFindings =
      [ violation owner meta "W_BACKENDIR_BRANCH_DROP_DUPLICATE" $
          "branch-drop metadata names the same binder more than once at this branch node: " <> show bid
      | (bid, count) <- Map.toList counts
      , count > 1
      ]
    checkDrop b =
      let bid = bbBinderId b
       in case Map.lookup bid env of
            Nothing ->
              [ violation owner meta "W_BACKENDIR_BRANCH_DROP_OUT_OF_SCOPE" $
                  "branch-drop metadata names binder outside this runtime scope: " <> show bid
              ]
            Just canonical
              | canonical == b -> []
              | otherwise ->
                  [ violation owner meta "W_BACKENDIR_BRANCH_DROP_MISMATCH" $
                      "branch-drop metadata for "
                        <> show bid
                        <> " does not match the in-scope backend binder payload"
                  ]

validateBranchDropsTerm :: GName -> BinderEnv -> BackendTerm -> [BackendIRViolation]
validateBranchDropsTerm owner env term =
  validateBranchDropsMeta owner env (backendMeta term)
    ++ case term of
      BUnit {} -> []
      BVar {} -> []
      BGlob {} -> []
      BLit {} -> []
      BLam _ mb _ _ _ body ->
        validateBranchDropsTerm owner (addMaybeBinder mb env) body
      BApp _ hd args ->
        validateBranchDropsTerm owner env hd
          ++ concatMap (\(_, _, arg) -> validateBranchDropsTerm owner env arg) args
      BCtor _ _ args -> concatMap (validateBranchDropsTerm owner env) args
      BMatch _ scrut alts _ ->
        validateBranchDropsTerm owner env scrut
          ++ concatMap (validateBranchDropsAlt owner env) alts
      BRecord _ fs -> concatMap (validateBranchDropsTerm owner env . snd) fs
      BProj _ e _ _ -> validateBranchDropsTerm owner env e
      BInject _ _ e -> validateBranchDropsTerm owner env e
      BLet _ mb _ _ rhs body ->
        validateBranchDropsTerm owner env rhs
          ++ validateBranchDropsTerm owner (addMaybeBinder mb env) body
      BLetRec _ mb _ _ rhs body ->
        let env' = addMaybeBinder mb env
         in validateBranchDropsTerm owner env' rhs
              ++ validateBranchDropsTerm owner env' body
      BDo _ _ items -> fst (validateBranchDropsItems owner env items)
      BSeal _ _ e -> validateBranchDropsTerm owner env e
      BThunk _ e -> validateBranchDropsTerm owner env e
      BLazy _ e -> validateBranchDropsTerm owner env e
      BForce _ e -> validateBranchDropsTerm owner env e
      BIf _ c th el ->
        validateBranchDropsTerm owner env c
          ++ validateBranchDropsTerm owner env th
          ++ validateBranchDropsTerm owner env el

validateBranchDropsAlt :: GName -> BinderEnv -> BackendAlt -> [BackendIRViolation]
validateBranchDropsAlt owner env (BackendAlt meta _ binders guard body) =
  validateBranchDropsMeta owner env meta
    ++ maybe [] (validateBranchDropsTerm owner env') guard
    ++ validateBranchDropsTerm owner env' body
  where
    env' = addMaybeBinders binders env

validateBranchDropsItems :: GName -> BinderEnv -> [BackendItem] -> ([BackendIRViolation], BinderEnv)
validateBranchDropsItems owner = go
  where
    go env [] = ([], env)
    go env (item : rest) =
      let (here, env') = validateBranchDropsItem owner env item
          (there, env'') = go env' rest
       in (here ++ there, env'')

validateBranchDropsItem :: GName -> BinderEnv -> BackendItem -> ([BackendIRViolation], BinderEnv)
validateBranchDropsItem owner env item =
  case item of
    BKBind meta _ _ binders action _ ->
      ( validateBranchDropsItemMeta owner meta
          ++ validateBranchDropsTerm owner env action
      , addMaybeBinders binders env
      )
    BKLet meta _ _ binders value ->
      ( validateBranchDropsItemMeta owner meta
          ++ validateBranchDropsTerm owner env value
      , addMaybeBinders binders env
      )
    BKLetQ meta _ binders scrut mElse ->
      let env' = addMaybeBinders binders env
          elseFindings = case mElse of
            Nothing -> []
            Just (_, ebinders, body) ->
              validateBranchDropsTerm owner (addMaybeBinders ebinders env) body
       in ( validateBranchDropsItemMeta owner meta
              ++ validateBranchDropsTerm owner env scrut
              ++ elseFindings
          , env'
          )
    BKExpr meta action ->
      (validateBranchDropsItemMeta owner meta ++ validateBranchDropsTerm owner env action, env)
    BKVarItem meta mb initT action _ ->
      ( validateBranchDropsItemMeta owner meta
          ++ validateBranchDropsTerm owner env initT
          ++ validateBranchDropsTerm owner env action
      , addMaybeBinder mb env
      )
    BKAssign meta _ rhs action _ ->
      ( validateBranchDropsItemMeta owner meta
          ++ validateBranchDropsTerm owner env rhs
          ++ validateBranchDropsTerm owner env action
      , env
      )
    BKReturn meta value ->
      (validateBranchDropsItemMeta owner meta ++ validateBranchDropsTerm owner env value, env)
    BKWhile meta _ cond body mElse ->
      ( validateBranchDropsItemMeta owner meta
          ++ validateBranchDropsCond owner env cond
          ++ fst (validateBranchDropsItems owner env body)
          ++ maybe [] (fst . validateBranchDropsItems owner env) mElse
      , env
      )
    BKFor meta _ _ binders source body mElse ->
      let bodyEnv = addMaybeBinders binders env
       in ( validateBranchDropsItemMeta owner meta
              ++ validateBranchDropsTerm owner env source
              ++ fst (validateBranchDropsItems owner bodyEnv body)
              ++ maybe [] (fst . validateBranchDropsItems owner env) mElse
          , env
          )
    BKIf meta arms mElse ->
      ( validateBranchDropsItemMeta owner meta
          ++ concatMap (\(cond, body) -> validateBranchDropsTerm owner env cond ++ fst (validateBranchDropsItems owner env body)) arms
          ++ maybe [] (fst . validateBranchDropsItems owner env) mElse
      , env
      )
    BKDefer meta _ action ->
      (validateBranchDropsItemMeta owner meta ++ validateBranchDropsTerm owner env action, env)
    BKUsing meta _ binders acquire release ->
      ( validateBranchDropsItemMeta owner meta
          ++ validateBranchDropsTerm owner env acquire
          ++ validateBranchDropsTerm owner env release
      , addMaybeBinders binders env
      )
    BKSubDo meta _ body ->
      (validateBranchDropsItemMeta owner meta ++ fst (validateBranchDropsItems owner env body), env)
    BKBreak meta _ -> (validateBranchDropsItemMeta owner meta, env)
    BKContinue meta _ -> (validateBranchDropsItemMeta owner meta, env)

validateBranchDropsCond :: GName -> BinderEnv -> BackendCond -> [BackendIRViolation]
validateBranchDropsCond owner env = \case
  BKCondPure t -> validateBranchDropsTerm owner env t
  BKCondAction t -> validateBranchDropsTerm owner env t

addMaybeBinder :: Maybe BackendBinder -> BinderEnv -> BinderEnv
addMaybeBinder Nothing env = env
addMaybeBinder (Just b) env = Map.insert (bbBinderId b) b env

addMaybeBinders :: [Maybe BackendBinder] -> BinderEnv -> BinderEnv
addMaybeBinders bs env = foldr addMaybeBinder env bs

duplicateNodeFindings :: GName -> [BackendMeta] -> [BackendIRViolation]
duplicateNodeFindings owner metas =
  [ BackendIRViolation owner (BackendNodeId n) (T.pack "W_BACKENDIR_DUPLICATE_NODE_ID") $
      T.pack ("backend node id is not unique within body: " <> show n)
  | (n, count) <- Map.toList counts
  , count > (1 :: Int)
  ]
  where
    counts =
      Map.fromListWith
        (+)
        [(n, 1 :: Int) | BackendMeta (BackendNodeId n) _ <- metas]

duplicateBinderFindings :: GName -> BackendMeta -> [BackendBinder] -> [BackendIRViolation]
duplicateBinderFindings owner meta binders =
  [ violation owner meta "W_BACKENDIR_DUPLICATE_BINDER_ID" $
      "backend binder id is not unique within body: " <> show bid
  | (bid, count) <- Map.toList counts
  , count > (1 :: Int)
  ]
  where
    counts =
      Map.fromListWith
        (+)
        [(bid, 1 :: Int) | BackendBinder bid _ _ _ <- binders]

duplicateUseFindings :: GName -> BackendMeta -> [BackendUse] -> [BackendIRViolation]
duplicateUseFindings owner meta uses =
  [ violation owner meta "W_BACKENDIR_DUPLICATE_USE_ID" $
      "backend use id is not unique within body: " <> show uid
  | (uid, count) <- Map.toList counts
  , count > (1 :: Int)
  ]
  where
    counts =
      Map.fromListWith
        (+)
        [(uid, 1 :: Int) | BackendUse uid _ _ <- uses]

violation :: GName -> BackendMeta -> String -> String -> BackendIRViolation
violation owner meta code msg =
  BackendIRViolation owner (bmNodeId meta) (T.pack code) (T.pack msg)

collectMetas :: BackendTerm -> [BackendMeta]
collectMetas t =
  backendMeta t : case t of
    BUnit {} -> []
    BVar {} -> []
    BGlob {} -> []
    BLit {} -> []
    BLam _ _ _ _ _ body -> collectMetas body
    BApp _ hd args -> collectMetas hd ++ concatMap (\(_, _, arg) -> collectMetas arg) args
    BCtor _ _ args -> concatMap collectMetas args
    BMatch _ scrut alts _ -> collectMetas scrut ++ concatMap collectAltMetas alts
    BRecord _ fs -> concatMap (collectMetas . snd) fs
    BProj _ e _ _ -> collectMetas e
    BInject _ _ e -> collectMetas e
    BLet _ _ _ _ rhs body -> collectMetas rhs ++ collectMetas body
    BLetRec _ _ _ _ rhs body -> collectMetas rhs ++ collectMetas body
    BDo _ _ items -> concatMap collectItemMetas items
    BSeal _ _ e -> collectMetas e
    BThunk _ e -> collectMetas e
    BLazy _ e -> collectMetas e
    BForce _ e -> collectMetas e
    BIf _ c th el -> collectMetas c ++ collectMetas th ++ collectMetas el

collectAltMetas :: BackendAlt -> [BackendMeta]
collectAltMetas (BackendAlt meta _ _ guard body) =
  meta : maybe [] collectMetas guard ++ collectMetas body

collectItemMetas :: BackendItem -> [BackendMeta]
collectItemMetas = \case
  BKBind meta _ _ _ action _ -> meta : collectMetas action
  BKLet meta _ _ _ value -> meta : collectMetas value
  BKLetQ meta _ _ scrut mElse ->
    meta : collectMetas scrut ++ maybe [] (\(_, _, body) -> collectMetas body) mElse
  BKExpr meta action -> meta : collectMetas action
  BKVarItem meta _ initT action _ -> meta : collectMetas initT ++ collectMetas action
  BKAssign meta _ rhs action _ -> meta : collectMetas rhs ++ collectMetas action
  BKReturn meta value -> meta : collectMetas value
  BKWhile meta _ cond body mElse ->
    meta : collectCondMetas cond ++ concatMap collectItemMetas body ++ maybe [] (concatMap collectItemMetas) mElse
  BKFor meta _ _ _ source body mElse ->
    meta : collectMetas source ++ concatMap collectItemMetas body ++ maybe [] (concatMap collectItemMetas) mElse
  BKIf meta arms mElse ->
    meta
      : concatMap (\(cond, body) -> collectMetas cond ++ concatMap collectItemMetas body) arms
        ++ maybe [] (concatMap collectItemMetas) mElse
  BKDefer meta _ action -> meta : collectMetas action
  BKUsing meta _ _ acquire release -> meta : collectMetas acquire ++ collectMetas release
  BKSubDo meta _ body -> meta : concatMap collectItemMetas body
  BKBreak meta _ -> [meta]
  BKContinue meta _ -> [meta]

collectCondMetas :: BackendCond -> [BackendMeta]
collectCondMetas = \case
  BKCondPure t -> collectMetas t
  BKCondAction t -> collectMetas t

collectBodyBinders :: BackendBody -> [BackendBinder]
collectBodyBinders body =
  mapMaybe bpBinder (bbParams body) ++ collectTermBinders (bbRoot body)

collectTermBinders :: BackendTerm -> [BackendBinder]
collectTermBinders = \case
  BUnit {} -> []
  BVar {} -> []
  BGlob {} -> []
  BLit {} -> []
  BLam _ mb _ _ _ body -> maybe [] pure mb ++ collectTermBinders body
  BApp _ hd args -> collectTermBinders hd ++ concatMap (\(_, _, arg) -> collectTermBinders arg) args
  BCtor _ _ args -> concatMap collectTermBinders args
  BMatch _ scrut alts _ -> collectTermBinders scrut ++ concatMap collectAltBinders alts
  BRecord _ fs -> concatMap (collectTermBinders . snd) fs
  BProj _ e _ _ -> collectTermBinders e
  BInject _ _ e -> collectTermBinders e
  BLet _ mb _ _ rhs body -> maybe [] pure mb ++ collectTermBinders rhs ++ collectTermBinders body
  BLetRec _ mb _ _ rhs body -> maybe [] pure mb ++ collectTermBinders rhs ++ collectTermBinders body
  BDo _ _ items -> concatMap collectItemBinders items
  BSeal _ _ e -> collectTermBinders e
  BThunk _ e -> collectTermBinders e
  BLazy _ e -> collectTermBinders e
  BForce _ e -> collectTermBinders e
  BIf _ c th el -> collectTermBinders c ++ collectTermBinders th ++ collectTermBinders el

collectAltBinders :: BackendAlt -> [BackendBinder]
collectAltBinders (BackendAlt _ _ binders guard body) =
  catMaybes binders ++ maybe [] collectTermBinders guard ++ collectTermBinders body

collectItemBinders :: BackendItem -> [BackendBinder]
collectItemBinders = \case
  BKBind _ _ _ binders action _ -> catMaybes binders ++ collectTermBinders action
  BKLet _ _ _ binders value -> catMaybes binders ++ collectTermBinders value
  BKLetQ _ _ binders scrut mElse ->
    catMaybes binders
      ++ collectTermBinders scrut
      ++ maybe [] (\(_, ebinders, body) -> catMaybes ebinders ++ collectTermBinders body) mElse
  BKExpr _ action -> collectTermBinders action
  BKVarItem _ mb initT action _ -> maybe [] pure mb ++ collectTermBinders initT ++ collectTermBinders action
  BKAssign _ _ rhs action _ -> collectTermBinders rhs ++ collectTermBinders action
  BKReturn _ value -> collectTermBinders value
  BKWhile _ _ cond body mElse ->
    collectCondBinders cond ++ concatMap collectItemBinders body ++ maybe [] (concatMap collectItemBinders) mElse
  BKFor _ _ _ binders source body mElse ->
    catMaybes binders ++ collectTermBinders source ++ concatMap collectItemBinders body ++ maybe [] (concatMap collectItemBinders) mElse
  BKIf _ arms mElse ->
    concatMap (\(cond, body) -> collectTermBinders cond ++ concatMap collectItemBinders body) arms
      ++ maybe [] (concatMap collectItemBinders) mElse
  BKDefer _ _ action -> collectTermBinders action
  BKUsing _ _ binders acquire release ->
    catMaybes binders ++ collectTermBinders acquire ++ collectTermBinders release
  BKSubDo _ _ body -> concatMap collectItemBinders body
  BKBreak {} -> []
  BKContinue {} -> []

collectCondBinders :: BackendCond -> [BackendBinder]
collectCondBinders = \case
  BKCondPure t -> collectTermBinders t
  BKCondAction t -> collectTermBinders t

collectBodyUses :: BackendBody -> [BackendUse]
collectBodyUses body = collectTermUses (bbRoot body)

collectTermUses :: BackendTerm -> [BackendUse]
collectTermUses = \case
  BUnit {} -> []
  BVar _ mb _ -> maybe [] pure mb
  BGlob {} -> []
  BLit {} -> []
  BLam _ _ _ _ _ body -> collectTermUses body
  BApp _ hd args -> collectTermUses hd ++ concatMap (\(_, _, arg) -> collectTermUses arg) args
  BCtor _ _ args -> concatMap collectTermUses args
  BMatch _ scrut alts _ -> collectTermUses scrut ++ concatMap collectAltUses alts
  BRecord _ fs -> concatMap (collectTermUses . snd) fs
  BProj _ e _ _ -> collectTermUses e
  BInject _ _ e -> collectTermUses e
  BLet _ _ _ _ rhs body -> collectTermUses rhs ++ collectTermUses body
  BLetRec _ _ _ _ rhs body -> collectTermUses rhs ++ collectTermUses body
  BDo _ _ items -> concatMap collectItemUses items
  BSeal _ _ e -> collectTermUses e
  BThunk _ e -> collectTermUses e
  BLazy _ e -> collectTermUses e
  BForce _ e -> collectTermUses e
  BIf _ c th el -> collectTermUses c ++ collectTermUses th ++ collectTermUses el

collectAltUses :: BackendAlt -> [BackendUse]
collectAltUses (BackendAlt _ _ _ guard body) =
  maybe [] collectTermUses guard ++ collectTermUses body

collectItemUses :: BackendItem -> [BackendUse]
collectItemUses = \case
  BKBind _ _ _ _ action _ -> collectTermUses action
  BKLet _ _ _ _ value -> collectTermUses value
  BKLetQ _ _ _ scrut mElse ->
    collectTermUses scrut ++ maybe [] (\(_, _, body) -> collectTermUses body) mElse
  BKExpr _ action -> collectTermUses action
  BKVarItem _ _ initT action _ -> collectTermUses initT ++ collectTermUses action
  BKAssign _ _ rhs action _ -> collectTermUses rhs ++ collectTermUses action
  BKReturn _ value -> collectTermUses value
  BKWhile _ _ cond body mElse ->
    collectCondUses cond ++ concatMap collectItemUses body ++ maybe [] (concatMap collectItemUses) mElse
  BKFor _ _ _ _ source body mElse ->
    collectTermUses source ++ concatMap collectItemUses body ++ maybe [] (concatMap collectItemUses) mElse
  BKIf _ arms mElse ->
    concatMap (\(cond, body) -> collectTermUses cond ++ concatMap collectItemUses body) arms
      ++ maybe [] (concatMap collectItemUses) mElse
  BKDefer _ _ action -> collectTermUses action
  BKUsing _ _ _ acquire release -> collectTermUses acquire ++ collectTermUses release
  BKSubDo _ _ body -> concatMap collectItemUses body
  BKBreak {} -> []
  BKContinue {} -> []

collectCondUses :: BackendCond -> [BackendUse]
collectCondUses = \case
  BKCondPure t -> collectTermUses t
  BKCondAction t -> collectTermUses t

-- ── Backend-IR ownership annotation ──────────────────────────────────

data BackendUseMode = BackendConsumes | BackendReads
  deriving stock (Eq, Show)

data BackendOwnState = BackendOwnState
  { bosNextUse :: !Int
  , bosConsumingLastUses :: !(Set BackendBinderId)
  , bosBorrowDeps :: !(Map BackendBinderId (Set BackendBinderId))
  }

type OwnAnnot = State BackendOwnState

annotateBackendBodyOwnership :: BackendBody -> BackendBody
annotateBackendBodyOwnership body =
  let initialScopes = reverse (mapMaybe bpBinder (bbParams body))
      (root0, st') =
        runState
          (fst <$> walkBackendTerm BackendConsumes initialScopes (bbRoot body) Set.empty)
          (BackendOwnState 0 Set.empty Map.empty)
      hot = bosConsumingLastUses st'
   in refreshBodyBinders hot body {bbRoot = root0}

freshUse :: OwnAnnot BackendUseId
freshUse = do
  n <- gets bosNextUse
  modify' $ \st -> st {bosNextUse = n + 1}
  pure (BackendUseId n)

recordConsumingLast :: BackendBinderId -> OwnAnnot ()
recordConsumingLast bid =
  modify' $ \st -> st {bosConsumingLastUses = Set.insert bid (bosConsumingLastUses st)}

recordBorrowDeps :: BackendBinderId -> Set BackendBinderId -> OwnAnnot ()
recordBorrowDeps bid deps =
  modify' $ \st ->
    st
      { bosBorrowDeps =
          if Set.null deps
            then Map.delete bid (bosBorrowDeps st)
            else Map.insert bid deps (bosBorrowDeps st)
      }

expandLiveDeps :: Set BackendBinderId -> OwnAnnot (Set BackendBinderId)
expandLiveDeps seeds = do
  deps <- gets bosBorrowDeps
  pure (closeIds deps seeds)

closeIds :: Map BackendBinderId (Set BackendBinderId) -> Set BackendBinderId -> Set BackendBinderId
closeIds deps seeds = go seeds (Set.toList seeds)
  where
    go seen [] = seen
    go seen (bid : rest) =
      let next = Map.findWithDefault Set.empty bid deps `Set.difference` seen
       in go (seen `Set.union` next) (Set.toList next ++ rest)

walkBackendTerm :: BackendUseMode -> [BackendBinder] -> BackendTerm -> Set BackendBinderId -> OwnAnnot (BackendTerm, Set BackendBinderId)
walkBackendTerm mode scopes term liveOut = case term of
  BUnit {} -> pure (term, liveOut)
  BGlob {} -> pure (term, liveOut)
  BLit {} -> pure (term, liveOut)
  BVar meta _ i ->
    case binderAtRuntimeIndex i scopes of
      Nothing -> pure (BVar meta Nothing i, liveOut)
      Just binder -> do
        uid <- freshUse
        let bid = bbBinderId binder
            kind
              | boBorrowed (bbBinderOwn binder) = Borrowed
              | bid `Set.member` liveOut = NonLast
              | otherwise = LastUse
            consumes = mode == BackendConsumes && kind /= Borrowed
        when (consumes && kind == LastUse) (recordConsumingLast bid)
        pure (BVar meta (Just (BackendUse uid kind consumes)) i, Set.insert bid liveOut)
  BLam meta mb ic q nm body -> do
    let scopes' = maybe scopes (: scopes) mb
    (body', liveBody) <- walkBackendTerm BackendConsumes scopes' body liveOut
    pure (BLam meta mb ic q nm body', maybe liveBody (`Set.delete` liveBody) (bbBinderId <$> mb))
  BApp meta hd args -> do
    (args', liveArgs) <-
      foldr
        ( \(ic, conv, arg) action -> do
            (restArgs, restLive) <- action
            (arg', argLive) <- walkBackendTerm (backendArgUseMode ic conv) scopes arg restLive
            pure ((ic, conv, arg') : restArgs, argLive)
        )
        (pure ([], liveOut))
        args
    (hd', liveHead) <- walkBackendTerm BackendConsumes scopes hd liveArgs
    pure (BApp meta hd' args', liveHead)
  BCtor meta layout args -> do
    (args', liveArgs) <- walkBackendTerms BackendConsumes scopes args liveOut
    pure (BCtor meta layout args', liveArgs)
  BMatch meta scrut alts layouts -> do
    (alts0, armInfos) <- walkBackendAlts scopes alts liveOut
    entryLives <- mapM (expandLiveDeps . baiEntryLive) armInfos
    bodyLives <- mapM (expandLiveDeps . baiBodyLive) armInfos
    let liveAll = Set.unions entryLives
        (alts', _) =
          mapAccumLStrict
            ( \(fallthrough, idx) (alt, info) ->
                let liveAtDrop = if baiHasGuard info then bodyLives !! idx else entryLives !! idx
                    excluded = fallthrough `Set.union` baiGuardConsumes info
                    dropIds = (liveAll `Set.difference` liveAtDrop) `Set.difference` excluded
                    drops = bindersForIds scopes dropIds
                    alt' = addDropsToAlt drops alt
                 in ((fallthrough `Set.union` baiGuardConsumes info, idx + 1), alt')
            )
            (Set.empty, 0 :: Int)
            (zip alts0 armInfos)
    (scrut', liveScrut) <- walkBackendTerm BackendConsumes scopes scrut liveAll
    pure (BMatch meta scrut' alts' layouts, liveScrut)
  BRecord meta fs -> do
    (vals, liveVals) <- walkBackendTerms BackendConsumes scopes (map snd fs) liveOut
    pure (BRecord meta (zip (map fst fs) vals), liveVals)
  BProj meta e f mi -> do
    (e', liveE) <- walkBackendTerm BackendReads scopes e liveOut
    pure (BProj meta e' f mi, liveE)
  BInject meta tag e -> do
    (e', liveE) <- walkBackendTerm BackendConsumes scopes e liveOut
    pure (BInject meta tag e', liveE)
  BLet meta mb q nm rhs body -> do
    forM_ mb $ \binder ->
      recordBorrowDeps (bbBinderId binder) (borrowedResultDeps scopes rhs)
    let scopes' = maybe scopes (: scopes) mb
    (body', liveBody) <- walkBackendTerm mode scopes' body liveOut
    let liveBeforeRhs = maybe liveBody (`Set.delete` liveBody) (bbBinderId <$> mb)
    (rhs', liveRhs) <- walkBackendTerm BackendConsumes scopes rhs liveBeforeRhs
    pure (BLet meta mb q nm rhs' body', liveRhs)
  BLetRec meta mb q nm rhs body -> do
    forM_ mb $ \binder ->
      recordBorrowDeps (bbBinderId binder) (borrowedResultDeps scopes rhs)
    let scopes' = maybe scopes (: scopes) mb
    (body', liveBody) <- walkBackendTerm mode scopes' body liveOut
    (rhs', liveRhs) <- walkBackendTerm BackendConsumes scopes' rhs liveBody
    pure (BLetRec meta mb q nm rhs' body', maybe liveRhs (`Set.delete` liveRhs) (bbBinderId <$> mb))
  BDo meta lbl items -> do
    (items', liveItems) <- walkBackendItems scopes items liveOut
    pure (BDo meta lbl items', liveItems)
  BSeal meta labs e -> do
    (e', liveE) <- walkBackendTerm mode scopes e liveOut
    pure (BSeal meta labs e', liveE)
  BThunk meta e -> do
    (e', liveE) <- walkBackendTerm BackendConsumes scopes e liveOut
    pure (BThunk meta e', liveE)
  BLazy meta e -> do
    (e', liveE) <- walkBackendTerm BackendConsumes scopes e liveOut
    pure (BLazy meta e', liveE)
  BForce meta e -> do
    (e', liveE) <- walkBackendTerm BackendConsumes scopes e liveOut
    pure (BForce meta e', liveE)
  BIf meta c th el -> do
    (th0, liveTh) <- walkBackendTerm mode scopes th liveOut
    (el0, liveEl) <- walkBackendTerm mode scopes el liveOut
    liveTh' <- expandLiveDeps liveTh
    liveEl' <- expandLiveDeps liveEl
    let liveBranches = liveTh' `Set.union` liveEl'
        thDrops = bindersForIds scopes (liveBranches `Set.difference` liveTh')
        elDrops = bindersForIds scopes (liveBranches `Set.difference` liveEl')
        th' = addDropsToTerm thDrops th0
        el' = addDropsToTerm elDrops el0
    (c', liveC) <- walkBackendTerm BackendConsumes scopes c liveBranches
    pure (BIf meta c' th' el', liveC)

walkBackendTerms :: BackendUseMode -> [BackendBinder] -> [BackendTerm] -> Set BackendBinderId -> OwnAnnot ([BackendTerm], Set BackendBinderId)
walkBackendTerms mode scopes terms liveOut =
  foldr
    ( \term action -> do
        (restTerms, restLive) <- action
        (term', termLive) <- walkBackendTerm mode scopes term restLive
        pure (term' : restTerms, termLive)
    )
    (pure ([], liveOut))
    terms

data BackendAltInfo = BackendAltInfo
  { baiEntryLive :: !(Set BackendBinderId)
  , baiBodyLive :: !(Set BackendBinderId)
  , baiGuardConsumes :: !(Set BackendBinderId)
  , baiHasGuard :: !Bool
  }

walkBackendAlts :: [BackendBinder] -> [BackendAlt] -> Set BackendBinderId -> OwnAnnot ([BackendAlt], [BackendAltInfo])
walkBackendAlts scopes alts liveOut = go alts
  where
    go [] = pure ([], [])
    go (alt : rest) = do
      (rest', restInfo) <- go rest
      let guardFailLive = Set.unions (map baiEntryLive restInfo)
      (alt', info) <- walkBackendAlt scopes alt liveOut guardFailLive
      pure (alt' : rest', info : restInfo)

walkBackendAlt :: [BackendBinder] -> BackendAlt -> Set BackendBinderId -> Set BackendBinderId -> OwnAnnot (BackendAlt, BackendAltInfo)
walkBackendAlt scopes (BackendAlt meta pat binders guard body) liveOut guardFailLive = do
  let newBinders = catMaybes binders
      scopes' = newBinders ++ scopes
      localIds = Set.fromList (map bbBinderId newBinders)
  (body', liveBody0) <- walkBackendTerm BackendConsumes scopes' body liveOut
  beforeGuard <- gets bosConsumingLastUses
  (guard', liveEntry0) <-
    case guard of
      Nothing -> pure (Nothing, liveBody0)
      Just g -> do
        (g', liveG) <- walkBackendTerm BackendConsumes scopes' g (liveBody0 `Set.union` guardFailLive)
        pure (Just g', liveG)
  afterGuard <- gets bosConsumingLastUses
  let liveBody = liveBody0 `Set.difference` localIds
      liveEntry = liveEntry0 `Set.difference` localIds
      guardConsumes =
        case guard of
          Nothing -> Set.empty
          Just {} -> afterGuard `Set.difference` beforeGuard
      info =
        BackendAltInfo
          { baiEntryLive = liveEntry
          , baiBodyLive = liveBody
          , baiGuardConsumes = guardConsumes
          , baiHasGuard = maybe False (const True) guard
          }
  pure (BackendAlt meta pat binders guard' body', info)

walkBackendCond :: [BackendBinder] -> BackendCond -> Set BackendBinderId -> OwnAnnot (BackendCond, Set BackendBinderId)
walkBackendCond scopes cond liveOut =
  case cond of
    BKCondPure t -> do
      (t', liveT) <- walkBackendTerm BackendConsumes scopes t liveOut
      pure (BKCondPure t', liveT)
    BKCondAction t -> do
      (t', liveT) <- walkBackendTerm BackendConsumes scopes t liveOut
      pure (BKCondAction t', liveT)

walkBackendItems :: [BackendBinder] -> [BackendItem] -> Set BackendBinderId -> OwnAnnot ([BackendItem], Set BackendBinderId)
walkBackendItems scopes items liveOut = go scopes items liveOut
  where
    go _ [] lo = pure ([], lo)
    go scs (item : rest) lo =
      case item of
        BKBind meta q pat binders action wit -> do
          let newBinders = catMaybes binders
              scs' = newBinders ++ scs
              localIds = Set.fromList (map bbBinderId newBinders)
          (rest', liveRest) <- go scs' rest lo
          (action', liveAction) <- walkBackendTerm BackendConsumes scs action (liveRest `Set.difference` localIds)
          pure (BKBind meta q pat binders action' wit : rest', liveAction)
        BKLet meta q pat binders value -> do
          let newBinders = catMaybes binders
              scs' = newBinders ++ scs
              localIds = Set.fromList (map bbBinderId newBinders)
          forM_ newBinders $ \binder ->
            recordBorrowDeps (bbBinderId binder) (borrowedResultDeps scs value)
          (rest', liveRest) <- go scs' rest lo
          (value', liveValue) <- walkBackendTerm BackendConsumes scs value (liveRest `Set.difference` localIds)
          pure (BKLet meta q pat binders value' : rest', liveValue)
        BKLetQ meta pat binders scrut mElse -> do
          let newBinders = catMaybes binders
              scs' = newBinders ++ scs
              localIds = Set.fromList (map bbBinderId newBinders)
          (rest', liveRest) <- go scs' rest lo
          let liveSuccess = liveRest `Set.difference` localIds
          (mElse', liveElse) <-
            case mElse of
              Nothing -> pure (Nothing, Set.empty)
              Just (ep, ebinders, et) -> do
                let ebs = catMaybes ebinders
                    escs = ebs ++ scs
                    eids = Set.fromList (map bbBinderId ebs)
                (et', liveEt) <- walkBackendTerm BackendConsumes escs et lo
                pure (Just (ep, ebinders, et'), liveEt `Set.difference` eids)
          (scrut', liveScrut) <- walkBackendTerm BackendConsumes scs scrut (liveSuccess `Set.union` liveElse)
          pure (BKLetQ meta pat binders scrut' mElse' : rest', liveScrut)
        BKExpr meta action -> do
          (rest', liveRest) <- go scs rest lo
          (action', liveAction) <- walkBackendTerm BackendConsumes scs action liveRest
          pure (BKExpr meta action' : rest', liveAction)
        BKVarItem meta mb initT action wit -> do
          let scs' = maybe scs (: scs) mb
              localIds = maybe Set.empty (Set.singleton . bbBinderId) mb
          (rest', liveRest) <- go scs' rest lo
          (action', liveAction) <- walkBackendTerm BackendConsumes scs action (liveRest `Set.difference` localIds)
          (initT', _) <- walkBackendTerm BackendReads scs initT Set.empty
          pure (BKVarItem meta mb initT' action' wit : rest', liveAction)
        BKAssign meta monadic rhs action wit -> do
          (rest', liveRest) <- go scs rest lo
          (action', liveAction) <- walkBackendTerm BackendConsumes scs action liveRest
          (rhs', liveRhs) <- walkBackendTerm BackendConsumes scs rhs liveAction
          pure (BKAssign meta monadic rhs' action' wit : rest', liveRhs)
        BKReturn meta value -> do
          (value', liveValue) <- walkBackendTerm BackendConsumes scs value lo
          pure ([BKReturn meta value'], liveValue)
        BKWhile meta pureCond cond body mElse -> do
          (rest', liveRest) <- go scs rest lo
          let loopUses = freeBackendCond scs cond `Set.union` freeBackendItems scs body
              loopLiveOut = liveRest `Set.union` loopUses
          (body', liveBody) <- walkBackendItems scs body loopLiveOut
          (mElse', liveElse) <-
            case mElse of
              Nothing -> pure (Nothing, liveRest)
              Just els -> do
                (els', liveEls) <- walkBackendItems scs els liveRest
                pure (Just els', liveEls)
          (cond', liveCond) <- walkBackendCond scs cond (Set.unions [loopLiveOut, liveBody, liveElse])
          pure (BKWhile meta pureCond cond' body' mElse' : rest', liveCond)
        BKFor meta ml pat binders source body mElse -> do
          (rest', liveRest) <- go scs rest lo
          let newBinders = catMaybes binders
              scs' = newBinders ++ scs
              localIds = Set.fromList (map bbBinderId newBinders)
              loopUses = freeBackendItems scs' body `Set.difference` localIds
              loopLiveOut = liveRest `Set.union` loopUses
          (body', liveBody0) <- walkBackendItems scs' body loopLiveOut
          let liveBody = liveBody0 `Set.difference` localIds
          (mElse', liveElse) <-
            case mElse of
              Nothing -> pure (Nothing, liveRest)
              Just els -> do
                (els', liveEls) <- walkBackendItems scs els liveRest
                pure (Just els', liveEls)
          (source', liveSource) <- walkBackendTerm BackendConsumes scs source (Set.unions [liveRest, liveBody, liveElse])
          pure (BKFor meta ml pat binders source' body' mElse' : rest', liveSource)
        BKIf meta arms mElse -> do
          (rest', liveRest) <- go scs rest lo
          (arms', mElse', liveIf) <- walkBackendIfItems scs arms mElse liveRest
          pure (BKIf meta arms' mElse' : rest', liveIf)
        BKDefer meta lbl action -> do
          (rest', liveRest) <- go scs rest lo
          (action', liveAction) <- walkBackendTerm BackendConsumes scs action liveRest
          pure (BKDefer meta lbl action' : rest', liveAction)
        BKUsing meta pat binders acquire release -> do
          let newBinders = catMaybes binders
              scs' = newBinders ++ scs
              localIds = Set.fromList (map bbBinderId newBinders)
          (rest', liveRest) <- go scs' rest lo
          (release', liveRelease) <- walkBackendTerm BackendConsumes scs release (liveRest `Set.difference` localIds)
          (acquire', liveAcquire) <- walkBackendTerm BackendConsumes scs acquire liveRelease
          pure (BKUsing meta pat binders acquire' release' : rest', liveAcquire)
        BKSubDo meta lbl body -> do
          (rest', liveRest) <- go scs rest lo
          (body', liveBody) <- walkBackendItems scs body liveRest
          pure (BKSubDo meta lbl body' : rest', liveBody)
        BKBreak {} -> pure (item : rest, lo)
        BKContinue {} -> pure (item : rest, lo)

walkBackendIfItems
  :: [BackendBinder]
  -> [(BackendTerm, [BackendItem])]
  -> Maybe [BackendItem]
  -> Set BackendBinderId
  -> OwnAnnot ([(BackendTerm, [BackendItem])], Maybe [BackendItem], Set BackendBinderId)
walkBackendIfItems scopes arms mElse liveRest = do
  (mElse', liveElse) <-
    case mElse of
      Nothing -> pure (Nothing, liveRest)
      Just els -> do
        (els', liveEls) <- walkBackendItems scopes els liveRest
        pure (Just els', liveEls)
  (arms', liveArms) <- go arms liveElse
  pure (arms', mElse', liveArms)
  where
    go [] liveMore = pure ([], liveMore)
    go ((cond, body) : rest) liveMore = do
      (rest', liveRestArms) <- go rest liveMore
      (body', liveBody) <- walkBackendItems scopes body liveRest
      (cond', liveCond) <- walkBackendTerm BackendConsumes scopes cond (liveBody `Set.union` liveRestArms)
      pure ((cond', body') : rest', liveCond)

freeBackendCond :: [BackendBinder] -> BackendCond -> Set BackendBinderId
freeBackendCond scopes cond =
  snd $
    evalState
      (walkBackendCond scopes cond Set.empty)
      (BackendOwnState 0 Set.empty Map.empty)

freeBackendItems :: [BackendBinder] -> [BackendItem] -> Set BackendBinderId
freeBackendItems scopes items =
  snd $
    evalState
      (walkBackendItems scopes items Set.empty)
      (BackendOwnState 0 Set.empty Map.empty)

freeBackendTermPlain :: [BackendBinder] -> BackendTerm -> Set BackendBinderId
freeBackendTermPlain scopes term =
  snd $
    evalState
      (walkBackendTerm BackendConsumes scopes term Set.empty)
      (BackendOwnState 0 Set.empty Map.empty)

borrowedResultDeps :: [BackendBinder] -> BackendTerm -> Set BackendBinderId
borrowedResultDeps scopes = \case
  BProj _ e _ _ -> freeBackendTermPlain scopes e
  BSeal _ _ e -> borrowedResultDeps scopes e
  BIf _ _ th el -> borrowedResultDeps scopes th `Set.union` borrowedResultDeps scopes el
  BLet _ mb _ _ rhs body ->
    let rhsDeps = borrowedResultDeps scopes rhs
        scopes' = maybe scopes (: scopes) mb
        bodyDeps = borrowedResultDeps scopes' body
     in rhsDeps `Set.union` (bodyDeps `Set.difference` maybe Set.empty (Set.singleton . bbBinderId) mb)
  BLetRec _ mb _ _ rhs body ->
    let scopes' = maybe scopes (: scopes) mb
        localIds = maybe Set.empty (Set.singleton . bbBinderId) mb
     in (borrowedResultDeps scopes' rhs `Set.union` borrowedResultDeps scopes' body) `Set.difference` localIds
  BMatch _ scrut alts _ ->
    freeBackendTermPlain scopes scrut
      `Set.union` Set.unions [maybe Set.empty (borrowedResultDeps scopes) guard `Set.union` borrowedResultDeps scopes body | BackendAlt _ _ _ guard body <- alts]
  t@BApp {} -> freeBackendTermPlain scopes t
  _ -> Set.empty

backendArgUseMode :: Icit -> Maybe ArgConv -> BackendUseMode
backendArgUseMode ic conv
  | ic /= Expl = BackendReads
  | otherwise =
      case conv of
        Just Repr.ArgBorrowed -> BackendReads
        _ -> BackendConsumes

binderAtRuntimeIndex :: Int -> [BackendBinder] -> Maybe BackendBinder
binderAtRuntimeIndex i scopes
  | i < 0 = Nothing
  | otherwise = indexMaybeLocal i scopes

indexMaybeLocal :: Int -> [a] -> Maybe a
indexMaybeLocal i xs
  | i < 0 = Nothing
  | otherwise = go i xs
  where
    go 0 (x : _) = Just x
    go n (_ : rest) = go (n - 1) rest
    go _ [] = Nothing

bindersForIds :: [BackendBinder] -> Set BackendBinderId -> [BackendBinder]
bindersForIds scopes ids =
  [ binder
  | binder <- scopes
  , bbBinderId binder `Set.member` ids
  ]

addDropsToAlt :: [BackendBinder] -> BackendAlt -> BackendAlt
addDropsToAlt drops alt@(BackendAlt meta pat binders guard body)
  | null drops = alt
  | otherwise = BackendAlt (addDropsToMeta drops meta) pat binders guard body

addDropsToTerm :: [BackendBinder] -> BackendTerm -> BackendTerm
addDropsToTerm drops term
  | null drops = term
  | otherwise = mapTermMeta (addDropsToMeta drops) term

addDropsToMeta :: [BackendBinder] -> BackendMeta -> BackendMeta
addDropsToMeta drops (BackendMeta nid existing) =
  BackendMeta nid (existing ++ drops)

mapAccumLStrict :: (acc -> x -> (acc, y)) -> acc -> [x] -> ([y], acc)
mapAccumLStrict f = go []
  where
    go ys !acc [] = (reverse ys, acc)
    go ys !acc (x : xs) =
      let (!acc', !y) = f acc x
       in go (y : ys) acc' xs

mapTermMeta :: (BackendMeta -> BackendMeta) -> BackendTerm -> BackendTerm
mapTermMeta f = \case
  BUnit meta -> BUnit (f meta)
  BVar meta use i -> BVar (f meta) use i
  BGlob meta g -> BGlob (f meta) g
  BLit meta l -> BLit (f meta) l
  BLam meta mb ic q nm body -> BLam (f meta) mb ic q nm body
  BApp meta hd args -> BApp (f meta) hd args
  BCtor meta layout args -> BCtor (f meta) layout args
  BMatch meta scrut alts layouts -> BMatch (f meta) scrut alts layouts
  BRecord meta fs -> BRecord (f meta) fs
  BProj meta e fld mi -> BProj (f meta) e fld mi
  BInject meta tag e -> BInject (f meta) tag e
  BLet meta mb q nm rhs body -> BLet (f meta) mb q nm rhs body
  BLetRec meta mb q nm rhs body -> BLetRec (f meta) mb q nm rhs body
  BDo meta lbl items -> BDo (f meta) lbl items
  BSeal meta labs e -> BSeal (f meta) labs e
  BThunk meta e -> BThunk (f meta) e
  BLazy meta e -> BLazy (f meta) e
  BForce meta e -> BForce (f meta) e
  BIf meta c th el -> BIf (f meta) c th el

refreshBodyBinders :: Set BackendBinderId -> BackendBody -> BackendBody
refreshBodyBinders hot body =
  body
    { bbParams = map (refreshParamBinders hot) (bbParams body)
    , bbRoot = refreshTermBinders hot (bbRoot body)
    }

refreshParamBinders :: Set BackendBinderId -> BackendParam -> BackendParam
refreshParamBinders hot p =
  p {bpBinder = refreshMaybeBinder hot (bpBinder p)}

refreshMaybeBinder :: Set BackendBinderId -> Maybe BackendBinder -> Maybe BackendBinder
refreshMaybeBinder hot = fmap (refreshBinder hot)

refreshBinder :: Set BackendBinderId -> BackendBinder -> BackendBinder
refreshBinder hot binder =
  binder {bbBinderHasConsumingLastUse = bbBinderId binder `Set.member` hot}

refreshMetaBinders :: Set BackendBinderId -> BackendMeta -> BackendMeta
refreshMetaBinders hot (BackendMeta nid drops) =
  BackendMeta nid (map (refreshBinder hot) drops)

refreshTermBinders :: Set BackendBinderId -> BackendTerm -> BackendTerm
refreshTermBinders hot = \case
  BUnit meta -> BUnit (refreshMetaBinders hot meta)
  BVar meta use i -> BVar (refreshMetaBinders hot meta) use i
  BGlob meta g -> BGlob (refreshMetaBinders hot meta) g
  BLit meta l -> BLit (refreshMetaBinders hot meta) l
  BLam meta mb ic q nm body ->
    BLam (refreshMetaBinders hot meta) (refreshMaybeBinder hot mb) ic q nm (refreshTermBinders hot body)
  BApp meta hd args ->
    BApp (refreshMetaBinders hot meta) (refreshTermBinders hot hd) [(ic, conv, refreshTermBinders hot arg) | (ic, conv, arg) <- args]
  BCtor meta layout args ->
    BCtor (refreshMetaBinders hot meta) layout (map (refreshTermBinders hot) args)
  BMatch meta scrut alts layouts ->
    BMatch (refreshMetaBinders hot meta) (refreshTermBinders hot scrut) (map (refreshAltBinders hot) alts) layouts
  BRecord meta fs -> BRecord (refreshMetaBinders hot meta) [(n, refreshTermBinders hot v) | (n, v) <- fs]
  BProj meta e fld mi -> BProj (refreshMetaBinders hot meta) (refreshTermBinders hot e) fld mi
  BInject meta tag e -> BInject (refreshMetaBinders hot meta) tag (refreshTermBinders hot e)
  BLet meta mb q nm rhs body ->
    BLet (refreshMetaBinders hot meta) (refreshMaybeBinder hot mb) q nm (refreshTermBinders hot rhs) (refreshTermBinders hot body)
  BLetRec meta mb q nm rhs body ->
    BLetRec (refreshMetaBinders hot meta) (refreshMaybeBinder hot mb) q nm (refreshTermBinders hot rhs) (refreshTermBinders hot body)
  BDo meta lbl items -> BDo (refreshMetaBinders hot meta) lbl (map (refreshItemBinders hot) items)
  BSeal meta labs e -> BSeal (refreshMetaBinders hot meta) labs (refreshTermBinders hot e)
  BThunk meta e -> BThunk (refreshMetaBinders hot meta) (refreshTermBinders hot e)
  BLazy meta e -> BLazy (refreshMetaBinders hot meta) (refreshTermBinders hot e)
  BForce meta e -> BForce (refreshMetaBinders hot meta) (refreshTermBinders hot e)
  BIf meta c th el ->
    BIf (refreshMetaBinders hot meta) (refreshTermBinders hot c) (refreshTermBinders hot th) (refreshTermBinders hot el)

refreshAltBinders :: Set BackendBinderId -> BackendAlt -> BackendAlt
refreshAltBinders hot (BackendAlt meta pat binders guard body) =
  BackendAlt
    (refreshMetaBinders hot meta)
    pat
    (map (refreshMaybeBinder hot) binders)
    (refreshTermBinders hot <$> guard)
    (refreshTermBinders hot body)

refreshItemBinders :: Set BackendBinderId -> BackendItem -> BackendItem
refreshItemBinders hot = \case
  BKBind meta q pat binders action wit ->
    BKBind (refreshMetaBinders hot meta) q pat (map (refreshMaybeBinder hot) binders) (refreshTermBinders hot action) wit
  BKLet meta q pat binders value ->
    BKLet (refreshMetaBinders hot meta) q pat (map (refreshMaybeBinder hot) binders) (refreshTermBinders hot value)
  BKLetQ meta pat binders scrut mElse ->
    BKLetQ
      (refreshMetaBinders hot meta)
      pat
      (map (refreshMaybeBinder hot) binders)
      (refreshTermBinders hot scrut)
      ( (\(ep, ebinders, body) -> (ep, map (refreshMaybeBinder hot) ebinders, refreshTermBinders hot body)) <$> mElse
      )
  BKExpr meta action -> BKExpr (refreshMetaBinders hot meta) (refreshTermBinders hot action)
  BKVarItem meta mb initT action wit ->
    BKVarItem (refreshMetaBinders hot meta) (refreshMaybeBinder hot mb) (refreshTermBinders hot initT) (refreshTermBinders hot action) wit
  BKAssign meta monadic rhs action wit ->
    BKAssign (refreshMetaBinders hot meta) monadic (refreshTermBinders hot rhs) (refreshTermBinders hot action) wit
  BKReturn meta value -> BKReturn (refreshMetaBinders hot meta) (refreshTermBinders hot value)
  BKWhile meta pureCond cond body mElse ->
    BKWhile
      (refreshMetaBinders hot meta)
      pureCond
      (refreshCondBinders hot cond)
      (map (refreshItemBinders hot) body)
      (fmap (map (refreshItemBinders hot)) mElse)
  BKFor meta ml pat binders source body mElse ->
    BKFor
      (refreshMetaBinders hot meta)
      ml
      pat
      (map (refreshMaybeBinder hot) binders)
      (refreshTermBinders hot source)
      (map (refreshItemBinders hot) body)
      (fmap (map (refreshItemBinders hot)) mElse)
  BKIf meta arms mElse ->
    BKIf
      (refreshMetaBinders hot meta)
      [(refreshTermBinders hot cond, map (refreshItemBinders hot) body) | (cond, body) <- arms]
      (fmap (map (refreshItemBinders hot)) mElse)
  BKDefer meta lbl action -> BKDefer (refreshMetaBinders hot meta) lbl (refreshTermBinders hot action)
  BKUsing meta pat binders acquire release ->
    BKUsing
      (refreshMetaBinders hot meta)
      pat
      (map (refreshMaybeBinder hot) binders)
      (refreshTermBinders hot acquire)
      (refreshTermBinders hot release)
  BKSubDo meta lbl body -> BKSubDo (refreshMetaBinders hot meta) lbl (map (refreshItemBinders hot) body)
  BKBreak meta lbl -> BKBreak (refreshMetaBinders hot meta) lbl
  BKContinue meta lbl -> BKContinue (refreshMetaBinders hot meta) lbl

refreshCondBinders :: Set BackendBinderId -> BackendCond -> BackendCond
refreshCondBinders hot = \case
  BKCondPure t -> BKCondPure (refreshTermBinders hot t)
  BKCondAction t -> BKCondAction (refreshTermBinders hot t)

backendMeta :: BackendTerm -> BackendMeta
backendMeta = \case
  BUnit meta -> meta
  BVar meta _ _ -> meta
  BGlob meta _ -> meta
  BLit meta _ -> meta
  BLam meta _ _ _ _ _ -> meta
  BApp meta _ _ -> meta
  BCtor meta _ _ -> meta
  BMatch meta _ _ _ -> meta
  BRecord meta _ -> meta
  BProj meta _ _ _ -> meta
  BInject meta _ _ -> meta
  BLet meta _ _ _ _ _ -> meta
  BLetRec meta _ _ _ _ _ -> meta
  BDo meta _ _ -> meta
  BSeal meta _ _ -> meta
  BThunk meta _ -> meta
  BLazy meta _ -> meta
  BForce meta _ -> meta
  BIf meta _ _ _ -> meta

lowerBody :: EvalCtx -> Map GName GlobalDef -> Map GName CtorInfo -> Map GName TraitInfo -> GName -> Term -> (BackendBody, [BackendIRViolation])
lowerBody ctx globals ctors traits g body =
  let (body0, st') = runState (runReaderT go static) (LowerState 0 0 [])
      body' = annotateBackendBodyOwnership body0
   in (body', reverse (lstLoweringViolations st'))
  where
    static =
      LowerStatic
        { lsOwner = g
        , lsGlobals = globals
        , lsCtors = ctors
        , lsTraits = traits
        , lsCtx = ctx
        }
    paramSites = maybe [] (paramLowerSites ctx . gdType) (Map.lookup g globals)
    go = do
      (params, scopes, root0) <- lowerLeadingParams paramSites [] [] body
      if bodyRuntimeErased g root0
        then do
          meta <- metaAt
          pure BackendBody {bbOwner = g, bbParams = [], bbRoot = BUnit meta}
        else do
          root <- lowerTermExpected (bodyResultExpected (length scopes)) root0 (length scopes) scopes
          pure BackendBody {bbOwner = g, bbParams = params, bbRoot = root}

    bodyRuntimeErased owner root =
      Repr.resultIsProofBodyGlobal globals ctx owner
        || maybe False (globalResultIsKind ctx . gdType) (Map.lookup owner globals)
        || sourceArgErased globals ctx root

    bodyResultExpected paramCount =
      Map.lookup g globals >>= resultTypeAfterParams ctx paramCount . gdType

globalResultIsKind :: EvalCtx -> Value -> Bool
globalResultIsKind ctx = go 0
  where
    go lvl ty =
      case force ctx ty of
        VPi _ _ _ _ _ (Closure env cod) ->
          go (lvl + 1) (eval ctx (VRigid lvl [] : env) cod)
        VSort {} -> True
        _ -> False

resultTypeAfterParams :: EvalCtx -> Int -> Value -> Maybe Value
resultTypeAfterParams ctx count = go 0 count
  where
    go _ 0 ty = Just ty
    go lvl n ty =
      case force ctx ty of
        VPi _ _ _ _ _ (Closure env cod) ->
          go (lvl + 1) (n - 1) (eval ctx (VRigid lvl [] : env) cod)
        _ -> Nothing

paramLowerSites :: EvalCtx -> Value -> [ParamLowerSite]
paramLowerSites ctx = go 0
  where
    go lvl ty =
      case force ctx ty of
        VPi ic q borrowed _ dom (Closure env cod) ->
          let x = VRigid lvl []
              domV = force ctx dom
              codV = eval ctx (x : env) cod
              site =
                ParamLowerSite
                  { plsIcit = ic
                  , plsQ = q
                  , plsBorrowed = borrowed
                  , plsErased = Repr.runtimeErasedParam ctx lvl q domV
                  , plsDomain = domV
                  }
           in site : go (lvl + 1) codV
        _ -> []

qDroppable :: Q -> Bool
qDroppable = \case
  Q0 -> True
  QLe1 -> True
  QW -> True
  Q1 -> False
  QGe1 -> False

lowerLeadingParams :: [ParamLowerSite] -> [BackendParam] -> ScopeStack -> Term -> Lower ([BackendParam], ScopeStack, Term)
lowerLeadingParams sites params scopes = \case
  CLam ic q nm body -> do
    let (declQ, borrowed, erased, mTy, sites') = case takeMatchingParam ic sites of
          Just (site, rest) -> (plsQ site, plsBorrowed site, plsErased site, Just (plsDomain site), rest)
          Nothing -> (q, False, q == Q0, Nothing, sites)
    mb <- if erased then pure Nothing else binderAtWith declQ borrowed (T.pack ("parameter " <> T.unpack nm))
    let scopes' = ScopeSlot (mbId mb) mTy : scopes
        params' = params ++ [BackendParam ic nm mb | not erased]
    lowerLeadingParams sites' params' scopes' body
  t -> pure (params, scopes, t)
  where
    mbId = fmap bbBinderId
    takeMatchingParam _ [] = Nothing
    takeMatchingParam ic (site : rest)
      | ic == plsIcit site = Just (site, rest)
      | otherwise =
          second (site :) <$> takeMatchingParam ic rest

second :: (b -> c) -> (a, b) -> (a, c)
second f (a, b) = (a, f b)

lowerTerm :: Term -> Int -> ScopeStack -> Lower BackendTerm
lowerTerm = lowerTermExpected Nothing

lowerTermExpected :: Maybe Value -> Term -> Int -> ScopeStack -> Lower BackendTerm
lowerTermExpected expected term depth scopes = case term of
  CVar i -> do
    meta <- metaAt
    let runtimeIdx = length [() | ScopeSlot (Just _) _ <- take i scopes]
    case drop i scopes of
      ScopeSlot (Just _) _ : _ -> pure (BVar meta Nothing runtimeIdx)
      ScopeSlot Nothing _ : _ -> erasedRuntimeAt meta "erased variable occurrence reached a runtime BackendIR value position"
      _ -> erasedRuntimeAt meta "out-of-scope variable occurrence reached a runtime BackendIR value position"
  CGlob g -> do
    meta <- metaAt
    globals <- asks lsGlobals
    ctx <- asks lsCtx
    if globalRuntimeErased globals ctx g
      then erasedRuntimeAt meta ("erased global reached a runtime BackendIR value position: " <> gKey g)
      else pure (BGlob meta g)
  CLit l -> BLit <$> metaAt <*> pure l
  CLam ic q nm body -> do
    meta <- metaAt
    ctx <- asks lsCtx
    let mSite = lambdaExpectedSite ctx depth ic expected
        (declQ, borrowed, erased, mDom, mCod) = case mSite of
          Just site -> site
          Nothing -> (q, False, q == Q0, Nothing, Nothing)
    if erased
      then lowerTermExpected mCod body (depth + 1) (ScopeSlot Nothing mDom : scopes)
      else do
        mb <- binderAtWith declQ borrowed (T.pack ("lambda " <> T.unpack nm))
        body' <- lowerTermExpected mCod body (depth + 1) (ScopeSlot (fmap bbBinderId mb) mDom : scopes)
        pure (BLam meta mb ic declQ nm body')
  CApp {} -> lowerApp term depth scopes
  CSort {} -> metaAt >>= \meta -> erasedRuntimeAt meta "sort/type term reached a runtime BackendIR value position"
  CPi {} -> metaAt >>= \meta -> erasedRuntimeAt meta "function type reached a runtime BackendIR value position"
  CRecordT {} -> metaAt >>= \meta -> erasedRuntimeAt meta "record type reached a runtime BackendIR value position"
  CVariantT {} -> metaAt >>= \meta -> erasedRuntimeAt meta "variant type reached a runtime BackendIR value position"
  CSigT {} -> metaAt >>= \meta -> erasedRuntimeAt meta "signature type reached a runtime BackendIR value position"
  CMeta {} -> metaAt >>= \meta -> erasedRuntimeAt meta "unsolved compile-time meta reached a runtime BackendIR value position"
  CQuote {} -> metaAt >>= \meta -> erasedRuntimeAt meta "quoted syntax/proof term reached a runtime BackendIR value position"
  CCtor g ann args -> do
    meta <- metaAt
    lowerCtorTerm meta g ann args depth scopes
  CMatch s _ann alts -> do
    meta <- metaAt
    ctors <- asks lsCtors
    globals <- asks lsGlobals
    traits <- asks lsTraits
    ctx <- asks lsCtx
    s' <- lowerTerm s depth scopes
    let scrutTy = termTypeAt globals traits ctx depth scopes s
    alts' <- forM alts $ \a -> lowerAlt scrutTy a depth scopes
    pure (BMatch meta s' alts' (concatMap (patLayouts ctx ctors . caPat) alts))
  CRecordV fs -> do
    meta <- metaAt
    globals <- asks lsGlobals
    traits <- asks lsTraits
    ctx <- asks lsCtx
    let mRuntimeFields =
          case expected of
            Just ty -> runtimeRecordFieldNamesOfType globals traits ctx depth ty
            Nothing -> runtimeRecordFieldNames globals traits ctx depth scopes term
    fs' <-
      fmap catMaybes $
        forM fs $ \(name, v) ->
          if recordFieldErased mRuntimeFields globals traits ctx depth scopes name v
            then pure Nothing
            else do
              v' <- lowerTerm v depth scopes
              pure (Just (name, v'))
    pure (BRecord meta fs')
  CProj e f -> BProj <$> metaAt <*> lowerTerm e depth scopes <*> pure f <*> pure Nothing
  CProjAt e f _i -> do
    meta <- metaAt
    globals <- asks lsGlobals
    traits <- asks lsTraits
    ctx <- asks lsCtx
    e' <- lowerTerm e depth scopes
    pure (BProj meta e' f (runtimeRecordFieldIndex globals traits ctx depth scopes e f))
  CInject tag e -> BInject <$> metaAt <*> pure tag <*> lowerTerm e depth scopes
  CLet q nm _ty rhs body -> do
    ctx <- asks lsCtx
    let tyV = evalTypeAt ctx depth _ty
        erasedByType = Repr.runtimeErasedParam ctx depth q tyV
    if erasedByType
      then lowerTerm body (depth + 1) (ScopeSlot Nothing (Just tyV) : scopes)
      else do
        meta <- metaAt
        mb <- binderAtWith q False (T.pack ("let " <> T.unpack nm))
        rhs' <- lowerTermExpected (Just tyV) rhs depth scopes
        body' <- lowerTerm body (depth + 1) (ScopeSlot (fmap bbBinderId mb) (Just tyV) : scopes)
        pure (BLet meta mb q nm rhs' body')
  CLetRec q nm _ty rhs body -> do
    ctx <- asks lsCtx
    let tyV = evalTypeAt ctx depth _ty
        erasedByType = Repr.runtimeErasedParam ctx depth q tyV
    if erasedByType
      then lowerTerm body (depth + 1) (ScopeSlot Nothing (Just tyV) : scopes)
      else do
        meta <- metaAt
        mb <- binderAtWith q False (T.pack ("letrec " <> T.unpack nm))
        let scopes' = ScopeSlot (fmap bbBinderId mb) (Just tyV) : scopes
        rhs' <- lowerTermExpected (Just tyV) rhs (depth + 1) scopes'
        body' <- lowerTerm body (depth + 1) scopes'
        pure (BLetRec meta mb q nm rhs' body')
  CDo lbl items -> BDo <$> metaAt <*> pure lbl <*> lowerItems items depth scopes
  CSealE labs e -> BSeal <$> metaAt <*> pure labs <*> lowerTerm e depth scopes
  CThunkE e -> BThunk <$> metaAt <*> lowerTerm e depth scopes
  CLazyE e -> BLazy <$> metaAt <*> lowerTerm e depth scopes
  CForceE e -> BForce <$> metaAt <*> lowerTerm e depth scopes
  CIf c t e ->
    BIf <$> metaAt
      <*> lowerTerm c depth scopes
      <*> lowerTerm t depth scopes
      <*> lowerTerm e depth scopes

lowerApp :: Term -> Int -> ScopeStack -> Lower BackendTerm
lowerApp term depth scopes = do
  meta <- metaAt
  globals <- asks lsGlobals
  traits <- asks lsTraits
  ctx <- asks lsCtx
  case coreEtaCtorApp term of
    Just (g, ann, _k, picks) -> do
      lowerCtorTerm meta g ann (map snd picks) depth scopes
    Nothing -> do
      let (hd, args) = spineOfTerm term
          k = length args
          actualIcs = map fst args
          expectedArgs = appExpectedArgTypes globals traits ctx depth scopes term
          localPlan = case hd of
            CGlob {} -> Nothing
            _ ->
              termTypeAt globals traits ctx depth scopes hd >>= \ty ->
                Repr.argPlanSelectForArgsAt ctx depth ty actualIcs
          flags = case hd of
            CGlob g -> Repr.erasedSpinePositionsForArgs globals ctx g actualIcs
            _ -> maybe (replicate k False) (map fst) localPlan
          convs = case hd of
            CGlob g -> fromMaybe (replicate k Nothing) (Repr.argConvSelectGlobalForArgs ctx g actualIcs)
            _ -> maybe (replicate k Nothing) (map snd) localPlan
          kept =
            [ (ic, conv, expectedArg, a)
            | (((ic, a), (erased, conv)), expectedArg) <-
                zip (zip args (zip (flags ++ repeat False) (convs ++ repeat Nothing))) (expectedArgs ++ repeat Nothing)
            , not erased
            ]
      hd' <- lowerTerm hd depth scopes
      args' <-
        forM kept $ \(ic, conv, expectedArg, a) -> do
          a' <- lowerTermExpected expectedArg a depth scopes
          pure (ic, conv, a')
      pure (BApp meta hd' (filter (not . implicitErasedUnitArg) args'))
  where
    implicitErasedUnitArg (Impl, _, BUnit {}) = True
    implicitErasedUnitArg _ = False

lowerCtorTerm :: BackendMeta -> GName -> Maybe Term -> [Term] -> Int -> ScopeStack -> Lower BackendTerm
lowerCtorTerm meta g ann args depth scopes = do
  ctx <- asks lsCtx
  ctors <- asks lsCtors
  let mCi = Map.lookup g ctors
      sourceFacts =
        case mCi of
          Nothing -> []
          Just ci -> explicitCtorFieldRuntimeFacts ctx (length (ciFields ci)) (eval ctx [] (ciType ci))
      coreFacts =
        case mCi of
          Nothing -> []
          Just ci -> coreCtorPayloadRuntimeFacts ctx (eval ctx [] (ciType ci))
      sourceShape = maybe False (\ci -> length args == length (ciFields ci)) mCi
      coreShape = not (null coreFacts) && length args == length coreFacts
      kept =
        if coreShape
          then [(fieldTy, arg) | (arg, (True, fieldTy)) <- zip args coreFacts]
          else
            if sourceShape
              then [(fieldTy, arg) | (arg, (True, fieldTy)) <- zip args sourceFacts]
              else [(Nothing, arg) | arg <- args]
      annInfo = Repr.ctorLayoutOf ctx ann
      ctorInfo = Repr.ctorLayoutOf ctx (ciType <$> mCi)
      info = selectCtorLayoutInfo (length kept) annInfo ctorInfo
  args' <- forM kept $ \(expectedField, arg) ->
    lowerTermExpected expectedField arg depth scopes
  pure (BCtor meta (BackendCtorLayout g info (length args')) args')

selectCtorLayoutInfo :: Int -> Maybe CtorLayoutInfo -> Maybe CtorLayoutInfo -> Maybe CtorLayoutInfo
selectCtorLayoutInfo runtimeFields annInfo ctorInfo =
  case annInfo of
    Just info | clArity info == runtimeFields -> Just info
    _ ->
      case ctorInfo of
        Just info | clArity info == runtimeFields -> Just info
        _ ->
          case annInfo of
            Just info -> Just info
            Nothing -> ctorInfo

sourceArgErased :: Map GName GlobalDef -> EvalCtx -> Term -> Bool
sourceArgErased globals ctx = \case
  CSort {} -> True
  CPi {} -> True
  CRecordT {} -> True
  CVariantT {} -> True
  CSigT {} -> True
  CMeta {} -> True
  CQuote {} -> True
  CSealE _ e -> sourceArgErased globals ctx e
  CApp _ f _ -> sourceArgErased globals ctx f
  CGlob g ->
    Repr.resultIsProofGlobal globals ctx g
      || maybe False (typeKindValue ctx 0 . gdType) (Map.lookup g globals)
  _ -> False

sourceTermErased :: Map GName GlobalDef -> Map GName TraitInfo -> EvalCtx -> Int -> ScopeStack -> Term -> Bool
sourceTermErased globals traits ctx depth scopes = \case
  CVar i -> case drop i scopes of
    ScopeSlot Nothing _ : _ -> True
    _ -> False
  CSealE _ e -> sourceTermErased globals traits ctx depth scopes e
  CLam _ q _ body ->
    let mb = if q == Q0 then Nothing else Just (BackendBinderId (-1))
     in sourceTermErased globals traits ctx (depth + 1) (ScopeSlot mb Nothing : scopes) body
  CLet _ _ _ rhs body ->
    sourceTermErased globals traits ctx depth scopes rhs
      && sourceTermErased globals traits ctx (depth + 1) (ScopeSlot Nothing Nothing : scopes) body
  t@CApp {} ->
    sourceArgErased globals ctx t
      || sourceProofApplicationErased globals traits ctx depth scopes t
  t -> sourceArgErased globals ctx t

sourceProofApplicationErased :: Map GName GlobalDef -> Map GName TraitInfo -> EvalCtx -> Int -> ScopeStack -> Term -> Bool
sourceProofApplicationErased globals traits ctx depth scopes term =
  case termTypeAt globals traits ctx depth scopes term of
    Just ty | Repr.resultIsProofBodyValue ctx depth ty || sourceProofHeadErased hd ->
      let (headTerm, args) = spineOfTerm term
          k = length args
          actualIcs = map fst args
          localPlan = case headTerm of
            CGlob {} -> Nothing
            _ ->
              termTypeAt globals traits ctx depth scopes headTerm >>= \tyH ->
                Repr.argPlanSelectForArgsAt ctx depth tyH actualIcs
          flags = case headTerm of
            CGlob g -> Repr.erasedSpinePositionsForArgs globals ctx g actualIcs
            _ -> maybe (replicate k False) (map fst) localPlan
          runtimeArgs =
            [ a
            | ((_, a), erased) <- zip args (flags ++ repeat False)
            , not erased
            ]
       in not (null runtimeArgs)
            && all (sourceTermErased globals traits ctx depth scopes) runtimeArgs
    _ -> False
  where
    (hd, _argsForHead) = spineOfTerm term
    sourceProofHeadErased = \case
      CGlob g -> Repr.resultIsProofBodyGlobal globals ctx g
      CSealE _ e -> sourceProofHeadErased e
      _ -> False

globalRuntimeErased :: Map GName GlobalDef -> EvalCtx -> GName -> Bool
globalRuntimeErased globals ctx g =
  Repr.resultIsProofGlobal globals ctx g
    || maybe False (globalResultIsKind ctx . gdType) (Map.lookup g globals)

lambdaExpectedSite :: EvalCtx -> Int -> Icit -> Maybe Value -> Maybe (Q, Bool, Bool, Maybe Value, Maybe Value)
lambdaExpectedSite ctx depth actualIc expected = do
  ty <- expected
  case force ctx ty of
    VPi ic q borrowed _ dom (Closure env cod)
      | ic == actualIc ->
          let domV = force ctx dom
              codV = eval ctx (VRigid depth [] : env) cod
           in Just
                ( q
                , borrowed
                , Repr.runtimeErasedParam ctx depth q domV
                , Just domV
                , Just codV
                )
    _ -> Nothing

recordFieldErased :: Maybe (Set Text) -> Map GName GlobalDef -> Map GName TraitInfo -> EvalCtx -> Int -> ScopeStack -> Text -> Term -> Bool
recordFieldErased mRuntimeFields globals traits ctx depth scopes name value =
  case mRuntimeFields of
    Just runtimeFields ->
      name `Set.notMember` runtimeFields
        || sourceTermErased globals traits ctx depth scopes value
    Nothing -> sourceTermErased globals traits ctx depth scopes value

typeKindValue :: EvalCtx -> Int -> Value -> Bool
typeKindValue ctx lvl v =
  case force ctx v of
    VSort _ -> True
    VPi _ _ _ _ _ clo ->
      typeKindValue ctx (lvl + 1) (closApply lvl clo)
    _ -> False
  where
    closApply l (Closure env body) = eval ctx (VRigid l [] : env) body

termTypeAt :: Map GName GlobalDef -> Map GName TraitInfo -> EvalCtx -> Int -> ScopeStack -> Term -> Maybe Value
termTypeAt globals traits ctx depth scopes = go
  where
    go = \case
      CGlob g -> gdType <$> Map.lookup g globals <|> Repr.argConvGlobalType ctx g
      CVar i -> scopeSlotType =<< indexMaybeLocal i scopes
      CProj e field -> projectionFieldType globals traits ctx depth scopes e field =<< go e
      CProjAt e field _ -> projectionFieldType globals traits ctx depth scopes e field =<< go e
      CSealE _ e -> go e
      CIf _ t f -> sameType (go t) (go f)
      CMatch _ ann _ -> evalTypeAt ctx depth <$> ann
      t@CApp {} ->
        let (h, args) = spineOfTerm t
         in go h >>= \ty -> applyArgs ty args
      _ -> Nothing

    applyArgs ty [] = Just ty
    applyArgs ty ((ic, arg) : rest) =
      case force ctx ty of
        VPi pic _ _ _ _ (Closure env cod)
          | ic == pic ->
              let argV = eval ctx (rigidEnv depth) arg
               in applyArgs (eval ctx (argV : env) cod) rest
        _ -> Nothing

    sameType (Just a) (Just b)
      | renderTerm (quote ctx depth (force ctx a))
          == renderTerm (quote ctx depth (force ctx b)) =
          Just a
    sameType _ _ = Nothing

appExpectedArgTypes :: Map GName GlobalDef -> Map GName TraitInfo -> EvalCtx -> Int -> ScopeStack -> Term -> [Maybe Value]
appExpectedArgTypes globals traits ctx depth scopes appTerm =
  case spineOfTerm appTerm of
    (hd, args) ->
      case termTypeAt globals traits ctx depth scopes hd of
        Nothing -> replicate (length args) Nothing
        Just ty0 -> walk ty0 args
  where
    walk _ [] = []
    walk ty ((ic, arg) : rest) =
      case force ctx ty of
        VPi pic _ _ _ dom (Closure env cod)
          | ic == pic ->
              let argV = eval ctx (rigidEnv depth) arg
               in Just dom : walk (eval ctx (argV : env) cod) rest
        _ -> replicate (1 + length rest) Nothing

projectionFieldType :: Map GName GlobalDef -> Map GName TraitInfo -> EvalCtx -> Int -> ScopeStack -> Term -> Text -> Value -> Maybe Value
projectionFieldType globals traits ctx depth scopes recvTerm field recvTy =
  case force ctx recvTy of
    VRecordT fs -> lookup field fs
    VGlobN traitG spine
      | Just ti <- Map.lookup traitG traits ->
          traitProjectionType globals traits ctx depth scopes traitG (map snd spine) recvTerm field ti
    _ -> Nothing

traitProjectionType :: Map GName GlobalDef -> Map GName TraitInfo -> EvalCtx -> Int -> ScopeStack -> GName -> [Value] -> Term -> Text -> TraitInfo -> Maybe Value
traitProjectionType globals _traits ctx depth scopes traitG args recvTerm field ti
  | field `elem` tiMembers ti =
      traitMemberType globals ctx depth scopes traitG field args recvTerm
  | Just supClosed <- lookup field (tiSupers ti) =
      traitSuperType ctx args supClosed
  | otherwise =
      Nothing
traitMemberType :: Map GName GlobalDef -> EvalCtx -> Int -> ScopeStack -> GName -> Text -> [Value] -> Term -> Maybe Value
traitMemberType globals ctx depth _scopes traitG member args dictTm = do
  gd <- Map.lookup (traitMemberGlobal traitG member) globals
  peel (gdType gd) args
  where
    peel ty [] =
      case force ctx ty of
        VPi Impl _ _ _ _ (Closure env cod) ->
          let dictV = eval ctx (rigidEnv depth) dictTm
           in Just (eval ctx (dictV : env) cod)
        t -> Just t
    peel ty (a : as) =
      case force ctx ty of
        VPi Impl _ _ _ _ (Closure env cod) ->
          peel (eval ctx (a : env) cod) as
        t -> Just t
traitSuperType :: EvalCtx -> [Value] -> Term -> Maybe Value
traitSuperType ctx args superClosed =
  applyExpl (eval ctx [] superClosed) args
  where
    applyExpl v [] = Just (force ctx v)
    applyExpl v (a : as) =
      case force ctx v of
        VLam Expl _ _ (Closure env body) ->
          applyExpl (eval ctx (a : env) body) as
        _ -> Nothing

runtimeRecordFieldIndex :: Map GName GlobalDef -> Map GName TraitInfo -> EvalCtx -> Int -> ScopeStack -> Term -> Text -> Maybe Int
runtimeRecordFieldIndex globals traits ctx depth scopes recordTerm field =
  termTypeAt globals traits ctx depth scopes recordTerm >>= runtimeRecordFieldIndexOfType globals traits ctx depth field

runtimeRecordFieldIndexOfType :: Map GName GlobalDef -> Map GName TraitInfo -> EvalCtx -> Int -> Text -> Value -> Maybe Int
runtimeRecordFieldIndexOfType globals traits ctx depth field ty =
  runtimeRecordFieldOrderOfType globals traits ctx depth ty >>= elemIndex field

runtimeRecordFieldNames :: Map GName GlobalDef -> Map GName TraitInfo -> EvalCtx -> Int -> ScopeStack -> Term -> Maybe (Set Text)
runtimeRecordFieldNames globals traits ctx depth scopes recordTerm =
  termTypeAt globals traits ctx depth scopes recordTerm >>= runtimeRecordFieldNamesOfType globals traits ctx depth

runtimeRecordFieldNamesOfType :: Map GName GlobalDef -> Map GName TraitInfo -> EvalCtx -> Int -> Value -> Maybe (Set Text)
runtimeRecordFieldNamesOfType globals traits ctx depth ty =
  Set.fromList <$> runtimeRecordFieldOrderOfType globals traits ctx depth ty

runtimeRecordFieldOrderOfType :: Map GName GlobalDef -> Map GName TraitInfo -> EvalCtx -> Int -> Value -> Maybe [Text]
runtimeRecordFieldOrderOfType globals traits ctx depth ty =
  case force ctx ty of
    VRecordT fs ->
      Just
        [ name
        | (name, fieldTy) <- fs
        , not (Repr.runtimeErasedParam ctx depth QW fieldTy)
        ]
    VGlobN traitG _
      | Just ti <- Map.lookup traitG traits ->
          Just (traitRuntimeFieldOrder globals ctx traitG ti)
    _ -> Nothing

traitRuntimeFieldOrder :: Map GName GlobalDef -> EvalCtx -> GName -> TraitInfo -> [Text]
traitRuntimeFieldOrder globals ctx traitG ti =
  sort $
    map fst (tiSupers ti)
      ++ [ member
         | member <- tiMembers ti
         , not (globalRuntimeErased globals ctx (traitMemberGlobal traitG member))
         ]

traitMemberGlobal :: GName -> Text -> GName
traitMemberGlobal (GName m t) member = GName m (t <> "." <> member)

scopeSlotType :: ScopeSlot -> Maybe Value
scopeSlotType (ScopeSlot _ ty) = ty

evalTypeAt :: EvalCtx -> Int -> Term -> Value
evalTypeAt ctx depth = eval ctx (rigidEnv depth)

rigidEnv :: Int -> [Value]
rigidEnv depth = [VRigid (depth - 1 - i) [] | i <- [0 .. depth - 1]]

coreEtaCtorApp :: Term -> Maybe (GName, Maybe Term, Int, [(Int, Term)])
coreEtaCtorApp term =
  case spineOfTerm term of
    (hd, sargs)
      | (k, body) <- coreFuncArity hd
      , k >= 1
      , k == length sargs
      , CCtor g ann fieldVars <- body ->
          (\picks -> (g, ann, k, picks)) <$> traverse (pick (map snd sargs) k) fieldVars
    _ -> Nothing
  where
    pick args k = \case
      CVar j | j >= 0, j < k -> Just (k - 1 - j, args !! (k - 1 - j))
      _ -> Nothing

coreFuncArity :: Term -> (Int, Term)
coreFuncArity = go 0
  where
    go !n (CLam _ _ _ b) = go (n + 1) b
    go !n t = (n, t)

lowerAlt :: Maybe Value -> CaseAlt -> Int -> ScopeStack -> Lower BackendAlt
lowerAlt expected (CaseAlt pat guard body) depth scopes = do
  meta <- metaAt
  (pat', binders, patScopes, totalSlots) <- lowerPattern depth expected QW False (T.pack "match pattern") pat
  let scopes' = patScopes ++ scopes
      depth' = depth + totalSlots
  guard' <- mapM (\g -> lowerTerm g depth' scopes') guard
  body' <- lowerTerm body depth' scopes'
  pure (BackendAlt meta pat' binders guard' body')

lowerItems :: [KItem] -> Int -> ScopeStack -> Lower [BackendItem]
lowerItems items depth scopes = go depth scopes items
  where
    go _ _ [] = pure []
    go d scs (item : rest) = do
      (out, d', scs') <- lowerItem item d scs
      (out :) <$> go d' scs' rest

lowerItem :: KItem -> Int -> ScopeStack -> Lower (BackendItem, Int, ScopeStack)
lowerItem item depth scopes = case item of
  KBind q pat action wit -> do
    meta <- metaAt
    action' <- lowerTerm action depth scopes
    (pat', binders, patScopes, totalSlots) <- lowerPattern depth Nothing q False (T.pack "do-bind pattern") pat
    pure (BKBind meta q pat' binders action' wit, depth + totalSlots, patScopes ++ scopes)
  KLet q pat value -> do
    meta <- metaAt
    globals <- asks lsGlobals
    traits <- asks lsTraits
    ctx <- asks lsCtx
    let expected = termTypeAt globals traits ctx depth scopes value
    value' <- lowerTerm value depth scopes
    (pat', binders, patScopes, totalSlots) <- lowerPattern depth expected q False (T.pack "do-let pattern") pat
    pure (BKLet meta q pat' binders value', depth + totalSlots, patScopes ++ scopes)
  KLetQ pat scrut mElse -> do
    meta <- metaAt
    globals <- asks lsGlobals
    traits <- asks lsTraits
    ctx <- asks lsCtx
    let expected = termTypeAt globals traits ctx depth scopes scrut
    scrut' <- lowerTerm scrut depth scopes
    (pat', binders, patScopes, totalSlots) <- lowerPattern depth expected QW False (T.pack "let? pattern") pat
    else' <- forM mElse $ \(ep, et) -> do
      (ep', ebinders, eScopes, eSlots) <- lowerPattern depth Nothing QW False (T.pack "let? else pattern") ep
      et' <- lowerTerm et (depth + eSlots) (eScopes ++ scopes)
      pure (ep', ebinders, et')
    pure (BKLetQ meta pat' binders scrut' else', depth + totalSlots, patScopes ++ scopes)
  KExpr action -> do
    meta <- metaAt
    action' <- lowerTerm action depth scopes
    pure (BKExpr meta action', depth, scopes)
  KVarItem _ initT act wit -> do
    meta <- metaAt
    mb <- binderAtWith QW False (T.pack "var")
    initT' <- lowerTerm initT depth scopes
    act' <- lowerTerm act depth scopes
    pure (BKVarItem meta mb initT' act' wit, depth + 1, binderSlotUnknown mb : scopes)
  KAssign _ monadic rhs act wit -> do
    meta <- metaAt
    rhs' <- lowerTerm rhs depth scopes
    act' <- lowerTerm act depth scopes
    pure (BKAssign meta monadic rhs' act' wit, depth, scopes)
  KReturn value -> do
    meta <- metaAt
    value' <- lowerTerm value depth scopes
    pure (BKReturn meta value', depth, scopes)
  KWhile pureCond cond body mElse -> do
    meta <- metaAt
    cond' <- lowerCond cond depth scopes
    body' <- lowerItems body depth scopes
    else' <- mapM (\es -> lowerItems es depth scopes) mElse
    pure (BKWhile meta pureCond cond' body' else', depth, scopes)
  KFor q pat source body mElse -> do
    meta <- metaAt
    source' <- lowerTerm source depth scopes
    (pat', binders, patScopes, totalSlots) <- lowerPattern depth Nothing QW False (T.pack "for pattern") pat
    let scopes' = patScopes ++ scopes
    body' <- lowerItems body (depth + totalSlots) scopes'
    else' <- mapM (\es -> lowerItems es depth scopes) mElse
    pure (BKFor meta q pat' binders source' body' else', depth, scopes)
  KIf arms mElse -> do
    meta <- metaAt
    arms' <-
      forM arms $ \(cond, body) -> do
        cond' <- lowerTerm cond depth scopes
        body' <- lowerItems body depth scopes
        pure (cond', body')
    else' <- mapM (\es -> lowerItems es depth scopes) mElse
    pure (BKIf meta arms' else', depth, scopes)
  KDefer lbl action -> do
    meta <- metaAt
    action' <- lowerTerm action depth scopes
    pure (BKDefer meta lbl action', depth, scopes)
  KUsing pat acquire release -> do
    meta <- metaAt
    acquire' <- lowerTerm acquire depth scopes
    release' <- lowerTerm release depth scopes
    (pat', binders, patScopes, totalSlots) <- lowerPattern depth Nothing QW True (T.pack "using pattern") pat
    pure (BKUsing meta pat' binders acquire' release', depth + totalSlots, patScopes ++ scopes)
  KSubDo lbl body -> do
    meta <- metaAt
    body' <- lowerItems body depth scopes
    pure (BKSubDo meta lbl body', depth, scopes)
  KBreak lbl -> do
    meta <- metaAt
    pure (BKBreak meta lbl, depth, scopes)
  KContinue lbl -> do
    meta <- metaAt
    pure (BKContinue meta lbl, depth, scopes)

lowerPattern :: Int -> Maybe Value -> Q -> Bool -> Text -> CorePat -> Lower (BackendPat, [Maybe BackendBinder], ScopeStack, Int)
lowerPattern depth expected q borrowed origin pat = do
  (pat', slots) <- lowerPatShape depth expected pat
  binders <- forM slots $ \slot ->
    if slot
      then binderAtWith q borrowed origin
      else pure Nothing
  -- Core pattern binders are produced in matchPat/source order, and evaluation
  -- extends the environment with reverse binds so the rightmost/runtime-latest
  -- binder becomes de Bruijn 0 while erased existential slots sit below the
  -- runtime fields. KBackendIR carries only runtime binders outward, but its
  -- internal scope map must preserve the full reversed slot stream.
  let runtimeBinders = reverse [mb | (True, mb) <- zip slots binders]
      scopeSlots = reverse (map binderSlotFromMaybe binders)
  pure (pat', runtimeBinders, scopeSlots, length slots)

lowerPatShape :: Int -> Maybe Value -> CorePat -> Lower (BackendPat, [Bool])
lowerPatShape depth expected = \case
  CPWild -> pure (BPWild, [])
  CPVar n -> pure (BPVar n, [True])
  CPLit l -> pure (BPLit l, [])
  CPCtor g nEx ps -> do
    fieldFacts <- ctorExplicitRuntimePatternFacts g (length ps)
    lowered <- forM (zip ps (map snd fieldFacts ++ repeat Nothing)) $ \(p, fieldTy) ->
      lowerPatShape depth fieldTy p
    let mask = map fst fieldFacts ++ repeat True
        fields = zip3 mask (map fst lowered) (map snd lowered)
        pats' = [p' | (True, p', _) <- fields]
        slots =
          replicate nEx False
            ++ concat
              [ if keep then patSlots else map (const False) patSlots
              | (keep, _, patSlots) <- fields
              ]
    pure (BPCtor g pats', slots)
  CPTuple ps -> do
    ctx <- asks lsCtx
    let fieldFacts = positionalRecordPatternFacts ctx depth expected (length ps)
    lowered <- forM (zip ps (map snd fieldFacts ++ repeat Nothing)) $ \(p, fieldTy) ->
      lowerPatShape depth fieldTy p
    let fields = zip3 (map fst fieldFacts ++ repeat True) (map fst lowered) (map snd lowered)
        pats' = [p' | (True, p', _) <- fields]
        slots =
          concat
            [ if keep then patSlots else map (const False) patSlots
            | (keep, _, patSlots) <- fields
            ]
    pure (BPTuple pats', slots)
  CPRecord fs rest ->
    do
      ctx <- asks lsCtx
      let fieldFacts = namedRecordPatternFacts ctx depth expected
      lowered <- forM fs $ \(name, p) -> do
        let fieldTy = fromMaybe Nothing (lookup name [(n, ty) | (n, _, ty) <- fieldFacts])
        loweredPat <- lowerPatShape depth fieldTy p
        pure (name, maybe True id (lookup name [(n, keep) | (n, keep, _) <- fieldFacts]), loweredPat)
      let
        restSlot = case rest of
          Just nm | not (T.null nm) -> [True]
          _ -> []
        fields =
          [ (keep, (name, p'), patSlots)
          | (name, keep, (p', patSlots)) <- lowered
          ]
        pats' = [(name, p') | (True, (name, p'), _) <- fields]
        slots =
          concat
            [ if keep then patSlots else map (const False) patSlots
            | (keep, _, patSlots) <- fields
            ]
      pure (BPRecord pats' rest, slots ++ restSlot)
  CPInject tag p -> do
    (p', slots) <- lowerPatShape depth Nothing p
    pure (BPInject tag p', slots)
  CPInjectRest tags -> pure (BPInjectRest tags, [True])
  CPAs name p -> do
    (p', slots) <- lowerPatShape depth expected p
    pure (BPAs name p', True : slots)
  CPOr ps perms -> do
    lowered <- mapM (lowerPatShape depth expected) ps
    let runtimePerms = adjustRuntimePerms (map snd lowered) perms
    pure (BPOr (map fst lowered) runtimePerms, maybe [] snd (listToMaybe lowered))

ctorExplicitRuntimePatternFacts :: GName -> Int -> Lower [(Bool, Maybe Value)]
ctorExplicitRuntimePatternFacts g patCount = do
  ctors <- asks lsCtors
  ctx <- asks lsCtx
  pure $
    case Map.lookup g ctors of
      Nothing -> replicate patCount (True, Nothing)
      Just ci ->
        take patCount $
          explicitCtorFieldRuntimeFacts ctx (length (ciFields ci)) (eval ctx [] (ciType ci))
            ++ repeat (True, Nothing)

explicitCtorFieldRuntimeFacts :: EvalCtx -> Int -> Value -> [(Bool, Maybe Value)]
explicitCtorFieldRuntimeFacts ctx fieldCount ty =
  let explicitMask = collect 0 ty
      fieldMask = drop (max 0 (length explicitMask - fieldCount)) explicitMask
   in fieldMask
  where
    collect lvl v =
      case force ctx v of
        VPi ic q _ _ dom (Closure env cod) ->
          let x = VRigid lvl []
              rest = collect (lvl + 1) (eval ctx (x : env) cod)
           in if ic == Expl
                then (Repr.runtimeConstructorField ctx lvl ic q dom, Just dom) : rest
                else rest
        _ -> []

coreCtorPayloadRuntimeFacts :: EvalCtx -> Value -> [(Bool, Maybe Value)]
coreCtorPayloadRuntimeFacts ctx = collect 0
  where
    collect lvl v =
      case force ctx v of
        VPi ic q _ _ dom (Closure env cod) ->
          let x = VRigid lvl []
              runtime = Repr.runtimeConstructorField ctx lvl ic q dom
              keepInCore = ic == Expl || runtime
              rest = collect (lvl + 1) (eval ctx (x : env) cod)
           in if keepInCore
                then (runtime, Just dom) : rest
                else rest
        _ -> []

positionalRecordPatternFacts :: EvalCtx -> Int -> Maybe Value -> Int -> [(Bool, Maybe Value)]
positionalRecordPatternFacts ctx depth expected patCount =
  take patCount $
    case expected of
      Just ty ->
        case forceRecordType ctx ty of
          Just fs ->
            [ (not (Repr.runtimeErasedParam ctx depth QW fieldTy), Just fieldTy)
            | (_, fieldTy) <- fs
            ]
          Nothing -> repeat (True, Nothing)
      Nothing -> repeat (True, Nothing)

namedRecordPatternFacts :: EvalCtx -> Int -> Maybe Value -> [(Text, Bool, Maybe Value)]
namedRecordPatternFacts ctx depth expected =
  case expected >>= forceRecordType ctx of
    Just fs ->
      [ (name, not (Repr.runtimeErasedParam ctx depth QW fieldTy), Just fieldTy)
      | (name, fieldTy) <- fs
      ]
    Nothing -> []

forceRecordType :: EvalCtx -> Value -> Maybe [(Text, Value)]
forceRecordType ctx ty =
  case force ctx ty of
    VRecordT fs -> Just fs
    _ -> Nothing

adjustRuntimePerms :: [[Bool]] -> [[Int]] -> [[Int]]
adjustRuntimePerms [] _ = []
adjustRuntimePerms (canonSlots : altSlots) perms =
  zipWith adjust (canonSlots : altSlots) perms
  where
    runtimeCanon = [i | (i, True) <- zip [0 ..] canonSlots]
    adjust slots perm =
      mapMaybe
        ( \canonIx -> do
            altIx <- indexMaybeLocal canonIx perm
            if altIx >= 0 && altIx < length slots && slots !! altIx
              then Just (length (filter id (take altIx slots)))
              else Nothing
        )
        runtimeCanon

lowerCond :: KCond -> Int -> ScopeStack -> Lower BackendCond
lowerCond cond depth scopes = case cond of
  KCondPure t -> BKCondPure <$> lowerTerm t depth scopes
  KCondAction t -> BKCondAction <$> lowerTerm t depth scopes

metaAt :: Lower BackendMeta
metaAt = do
  nid <- freshNode
  pure (BackendMeta nid [])

erasedRuntimeAt :: BackendMeta -> Text -> Lower BackendTerm
erasedRuntimeAt meta msg = do
  owner <- asks lsOwner
  modify' $ \st ->
    st
      { lstLoweringViolations =
          BackendIRViolation owner (bmNodeId meta) (T.pack "E_BACKENDIR_ERASED_RUNTIME_TERM") msg
            : lstLoweringViolations st
      }
  pure (BUnit meta)

freshNode :: Lower BackendNodeId
freshNode = do
  n <- gets lstNextNode
  modify' $ \st -> st {lstNextNode = n + 1}
  pure (BackendNodeId n)

freshBinder :: Lower BackendBinderId
freshBinder = do
  n <- gets lstNextBinder
  modify' $ \st -> st {lstNextBinder = n + 1}
  pure (BackendBinderId n)

binderAtWith :: Q -> Bool -> Text -> Lower (Maybe BackendBinder)
binderAtWith q borrowed origin = do
  bid <- freshBinder
  pure
    ( Just
        ( BackendBinder
            bid
            origin
            (BinderOwn q Nothing borrowed (qDroppable q))
            False
        )
    )

binderSlotUnknown :: Maybe BackendBinder -> ScopeSlot
binderSlotUnknown mb = ScopeSlot (fmap bbBinderId mb) Nothing

binderSlotFromMaybe :: Maybe BackendBinder -> ScopeSlot
binderSlotFromMaybe mb = ScopeSlot (fmap bbBinderId mb) Nothing

patLayouts :: EvalCtx -> Map GName CtorInfo -> CorePat -> [(GName, BackendCtorLayout)]
patLayouts ctx ctors = \case
  CPCtor g _ ps ->
    let info = Repr.ctorLayoutOf ctx (ciType <$> Map.lookup g ctors)
        layout = BackendCtorLayout g info (maybe 0 clArity info)
     in (g, layout) : concatMap (patLayouts ctx ctors) ps
  CPTuple ps -> concatMap (patLayouts ctx ctors) ps
  CPRecord fs _ -> concatMap (patLayouts ctx ctors . snd) fs
  CPInject _ p -> patLayouts ctx ctors p
  CPOr ps _ -> concatMap (patLayouts ctx ctors) ps
  CPAs _ p -> patLayouts ctx ctors p
  CPWild -> []
  CPVar _ -> []
  CPLit _ -> []
  CPInjectRest _ -> []

backendPatToCorePat :: BackendPat -> CorePat
backendPatToCorePat = \case
  BPWild -> CPWild
  BPVar n -> CPVar n
  BPLit l -> CPLit l
  BPCtor g ps -> CPCtor g 0 (map backendPatToCorePat ps)
  BPTuple ps -> CPTuple (map backendPatToCorePat ps)
  BPRecord fs rest -> CPRecord [(name, backendPatToCorePat p) | (name, p) <- fs] rest
  BPInject tag p -> CPInject tag (backendPatToCorePat p)
  BPInjectRest tags -> CPInjectRest tags
  BPOr ps perms -> CPOr (map backendPatToCorePat ps) perms
  BPAs name p -> CPAs name (backendPatToCorePat p)
