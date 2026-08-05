{-# LANGUAGE PatternSynonyms #-}

-- | Perceus RC Stage S1.1 — the ownership side-table with last-use analysis.
--
-- This module is the analysis half of the Perceus reference-counting arc
-- (see @runtime/docs/PERCEUS-RC-DESIGN.md@ §3 and @runtime/docs/PERCEUS-S1-PLAN.md@).
-- S1.0 landed the EMPTY plumbing — the type shapes, the 'annotateOwnership'
-- entry point, and the @csOwnership@ threading through the pipeline. __S1.1
-- fills in the analysis__: for every
-- top-level body it walks the elaborated, zonked Core 'Term' and populates
-- 'OwnInfo' with per-binder ownership facts ('oiBinders') and per-occurrence
-- last-use classification ('oiUses').
--
-- The ownership facts are computed during elaboration (§12.2 quantity\/borrow
-- accounting, ported here from the source-of-truth lattice in "Kappa.Usage").
-- This legacy S1 side-table still renders @dump-ownership@ output and
-- cross-checks/refines the historical analysis, but S5.A native emission no
-- longer consumes it. 'Kappa.Backend.IR' computes backend-facing uses,
-- binders, and branch-dead drops on the separate KBackendIR tree itself, using
-- node-local 'BackendUseId'/'BackendBinderId' metadata rather than this
-- observe-only Core audit table.
--
-- __Stage S1.1 is OBSERVE-ONLY for native codegen.__ The recorded decisions
-- remain continuously validated against the declared quantities by
-- 'crossCheckOwnInfo' (S1.2, gated in the test suite), so a wrong analysis
-- fails rather than drifts, but the S5.A backend path does not reattach or look
-- up this table when deciding dup/drop emission.
--
-- == The analysis (PERCEUS-RC-DESIGN §3, ported from "Kappa.Usage")
--
-- The classification is a per-branch free-variable liveness, computed by a
-- single structural walk that threads, for each subterm, the set of binders
-- that are still LIVE after it (the "live-out" set). An occurrence of a binder
-- is the LAST use on a completion path iff that binder is not in the live-out
-- set at the occurrence — i.e. it is not used again later on the same path.
-- Sequential composition (an application head before its argument, a @let@ rhs
-- before its body) flows the live set backward through the sequence; a branch
-- ('CMatch'\/'CIf') is a join — each arm is its own completion path, so a
-- binder used in one arm but not another is dropped (absent ⇒ a drop point) on
-- the arms that do not use it. Borrowed (@&@) binders are non-consuming: their
-- uses are all 'Borrowed' and never participate in last-use.
--
-- == Conservative starting points (PERCEUS-S1-PLAN risks R1\/R3)
--
--   * __Whole-binder last-use__ (R3): a partially-consumed record (§13.2.4) is
--     treated as non-reusable — per-field path-sensitivity is deferred to a
--     later stage. We classify whole binders only; an occurrence is a use of
--     the entire binder regardless of which field path it projects. Sound (it
--     never claims a reuse that the per-field analysis would forbid); it just
--     leaves the S5 field-reuse win on the table.
--
--   * __Do-kernel sequencing__ (the §18.8 do-kernel): do-local binders occupy
--     real de Bruijn slots in the backend environment, so mutable variables and
--     do pattern bindings are tracked as ordinary value binders rather than
--     treated as an ownership-erased island.
--
-- == R1 — de-Bruijn key stability (legacy audit table; see PERCEUS-S1-PLAN (e))
--
-- The side-table keys are owner-local ORDINAL identities assigned by this
-- analysis walk, not raw de Bruijn indices and not structural child positions.
-- An ordinal is minted at the binder/use/drop-site occurrence itself, so it is
-- stable under the index renumbering a de Bruijn walk performs without
-- preserving the old R-path bridge. S5.A moved native C/LLVM dup/drop emission
-- to node-local KBackendIR ownership metadata; this table remains useful only
-- as a legacy dump/cross-check artifact over KCore. Erased argument subterms
-- still record no 'UseSite' and do not flow liveness upstream.
module Kappa.Ownership
  ( -- * Stable Core identities (side-table keys)
    BinderId (..)
  , UseSite (..)
  , BranchSite (..)
    -- * Use classification
  , UseKind (..)
    -- * Per-binder ownership facts
  , BinderOwn (..)
    -- * The per-definition side-table
  , OwnInfo (..)
  , emptyOwnInfo
  , OwnershipCtorType (..)
    -- * The annotation pass
  , annotateOwnership
  , annotateOwnershipWithUniverses
    -- * S1.4 §3a whole-program usage refinement
  , refineOwnership
  , refineOwnershipWithUniverses
    -- * S1.2 cross-check against the declared quantities
  , crossCheckOwnInfo
  , crossCheckBodies
  , crossCheckBodiesWithUniverses
    -- * S1.5 backend owned/borrowed accessor (call-site classification assert)
  , argConvFindings
  , argConvBodies
    -- * Dump rendering (the @dump-ownership@ CLI surface)
  , renderOwnInfo
  ) where

import Data.Foldable (toList)
import Data.List (find, sortOn)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T

import Kappa.Backend.Repr (ArgConv (..), argConvGlobalType, argConvSelectGlobal, runtimeErasedPiParam)
import Kappa.Core
  ( CaseAlt (..)
  , Closure (..)
  , ConstructorArg (..)
  , ConstructorValueArg (..)
  , CoreLocalRecDef (..)
  , CorePat (..)
  , DeclarationUniverseTelescope (..)
  , GName (..)
  , Icit (..)
  , KCond (..)
  , KItem (..)
  , Level (..)
  , Q (..)
  , RecordField (..)
  , RuntimeErasure (..)
  , Term (..)
  , Value (..)
  , pattern VPiEvidenceM
  , constructorBridgeBinderCount
  , interleaveConstructorSourceBinders
  , mapArithmeticCertificate
  , gKey
  )
import Kappa.CoreOps (patBindersC, spineOfTerm, zonkTermWith)
import Kappa.Eval (EvalCtx (..), GlobalDef (..), Globals (..), eval, evalApp, force, quote)
import Kappa.Level (substituteLevelParams)
import Kappa.Pretty (renderTerm)

-- | A stable identity for a binder within a definition's elaborated Core.
--
-- Core is de Bruijn /indexed/ (a 'Kappa.Core.CVar' is an index relative to the
-- enclosing binders), so an index alone is not stable — it shifts as the term
-- is traversed under binders. The stable audit key is therefore the owning
-- global plus a deterministic owner-local ordinal minted at the binding
-- occurrence by the single analysis walk. It names the same binder everywhere
-- that walk resolves the de Bruijn level, without retaining structural child
-- positions as a key.
data BinderId = BinderId
  { biOwner :: !GName
  -- ^ The top-level definition whose body contains the binder.
  , biOrdinal :: !Int
  -- ^ Owner-local ordinal assigned by the ownership analysis walk.
  }
  deriving stock (Eq, Ord, Show)

-- | A stable identity for a /use occurrence/ of a binder — a single
-- 'Kappa.Core.CVar' site. Same scheme as 'BinderId': the owning global plus an
-- owner-local ordinal minted at the occurrence. Two distinct occurrences of the
-- same variable are distinct 'UseSite's, which is exactly what last-use analysis
-- needs (one occurrence is the last use, the others are not).
data UseSite = UseSite
  { usOwner :: !GName
  -- ^ The top-level definition whose body contains the use.
  , usOrdinal :: !Int
  -- ^ Owner-local ordinal assigned by the ownership analysis walk.
  }
  deriving stock (Eq, Ord, Show)

-- | Constructor type information needed by the legacy ownership audit. The
-- declaration universe telescope is part of the type's identity: dropping it
-- and comparing a raw @LParam@ result against a specialized scrutinee loses
-- field-domain substitutions for universe-polymorphic constructors.
data OwnershipCtorType = OwnershipCtorType
  { octUniverses :: !DeclarationUniverseTelescope
  , octType :: !Term
  }
  deriving stock (Eq, Show)

type OwnershipCtorTypes = Map GName OwnershipCtorType

-- | Stable identity for an observe-only branch-dead drop site in one owner.
newtype BranchSite = BranchSite Int
  deriving stock (Eq, Ord, Show)

-- | The liveness classification of a particular use occurrence. S2.3b records
-- the separate 'oiUseConsumes' bit because a 'LastUse' can be either a true
-- ownership transfer or a final read (projection base, borrowed call argument).
data UseKind
  = -- | The /last/ use of an owned binder on this control-flow path: the dup
    -- can be elided. Whether this occurrence moves/reuses ownership is recorded
    -- separately in 'oiUseConsumes'.
    LastUse
  | -- | A non-final use of an owned binder: the value is still live afterward,
    -- so this use must @dup@ (incref-share).
    NonLast
  | -- | A borrowed (@&@) use: read-only, never consumes — the caller still
    -- owns the value, so neither @dup@ nor @drop@ is emitted here.
    Borrowed
  deriving stock (Eq, Ord, Show)

-- | The ownership facts about a single binder.
data BinderOwn = BinderOwn
  { boDeclQ :: !Q
  -- ^ The quantity the binder was declared with (§12.2) — the upper bound the
  -- programmer committed to in the signature.
  , boRefined :: !(Maybe (Int, Maybe Int))
  -- ^ A whole-program /tighter-than-declared/ usage interval (§3a), when the
  -- visible call graph proves the binder is used more narrowly than 'boDeclQ'
  -- allows: @Just (lo, hi)@ with @hi == Nothing@ meaning unbounded above.
  -- 'Nothing' means no refinement (fall back to the declared quantity — the
  -- mandatory choice for any binder reachable through a separately-compiled
  -- interface, which is EMPTY in the current whole-program-static compile, so
  -- in practice 'Nothing' here means only \"usage was not strictly tighter than
  -- declared\"). Refinement only ever /tightens/, never widens, so it can never
  -- violate the source contract. S1.1 always leaves this 'Nothing'; the §3a
  -- whole-program pass (S1.4) fills it in.
  , boBorrowed :: !Bool
  -- ^ Whether the binder is a borrowed (@&@) parameter: the callee reads (and
  -- may @dup@) but never @drop@s it; the caller retains ownership.
  , boDroppable :: !Bool
  -- ^ Whether the value may be silently RC-decref-freed when it goes dead
  -- (@0@\/@≤1@\/@ω@), versus carrying a consumption obligation (@1@\/@≥1@,
  -- which must be explicitly consumed) (Spec §11403).
  }
  deriving stock (Eq, Ord, Show)

-- | The ownership side-table for one definition: the per-binder facts plus the
-- per-occurrence use classification. Keyed by the stable Core identities above.
data OwnInfo = OwnInfo
  { oiBinders :: !(Map BinderId BinderOwn)
  , oiUses :: !(Map UseSite UseKind)
  , oiUseConsumes :: !(Map UseSite Bool)
  -- ^ Perceus RC Stage S2.3b: whether this occurrence transfers an owned
  -- reference to its syntactic consumer. A 'LastUse' at a non-consuming site
  -- (projection base, borrowed call argument) is only a read, so the binder
  -- still owns its reference. S2.3b records that distinction for callers that
  -- can prove a safe ownership transfer; scope-close codegen remains
  -- conservative outside the S3.2 structural projection subset that C codegen
  -- can materialize with a balancing @kdup@.
  , oiBinderUses :: !(Map BinderId [UseKind])
  -- ^ Perceus RC Stage S2.3: the per-binder MULTISET of use classifications its
  -- occurrences resolved to (the @accAssoc@ the cross-check S1.2 already
  -- computes, surfaced here for the backend). The S2.3 drop discipline (b.4)
  -- needs ONE fact per binder that @oiUses@ (keyed by occurrence, not binder)
  -- cannot answer without the binder↔occurrence link: \"does this binder have a
  -- 'LastUse'?\". Ordinary whole-scope close-drop codegen is deliberately
  -- conservative: any consuming 'LastUse' suppresses that close-drop, while
  -- read-only projection results are only accepted where C codegen can prove and
  -- materialize owned results. S2.3d branch-dead drops use
  -- 'oiBranchDropSites' instead of this all-uses summary. Derivable from
  -- @oiUses@ + the body, but accumulated during the single analysis walk so the
  -- backend needs no re-walk.
  , oiBinderConsumingUses :: !(Map BinderId [UseKind])
  -- ^ The subset of 'oiBinderUses' whose occurrences are consuming. S2.3b uses
  -- this to distinguish transfer from read-only last-use at analysis and
  -- validation time. Whole-scope close drops intentionally consult this
  -- consuming subset plus codegen's separate owned-result proof.
  , oiBranchDropSites :: !(Map BranchSite [BinderId])
  -- ^ Perceus RC Stage S2.3d: branch-local dead-binder drops. Keyed by the
  -- branch/arm ordinal where a normal completion should drop existing flat
  -- locals for the listed binders. A binder appears here when it is live in a
  -- sibling branch (or after the join) but absent from this branch's live-in set.
  -- Native emission no longer consumes this table; KBackendIR carries branch
  -- drops on node metadata.
  }
  deriving stock (Eq, Show)

-- | The empty side-table — no binders, no uses.
emptyOwnInfo :: OwnInfo
emptyOwnInfo = OwnInfo Map.empty Map.empty Map.empty Map.empty Map.empty Map.empty

-- | §12.2.6 droppability: @0@\/@≤1@\/@ω@ are droppable (may be silently
-- decref-freed when dead); @1@\/@≥1@ carry a consumption obligation and are not
-- droppable.
qDroppable :: Q -> Bool
qDroppable = \case
  Q0 -> True
  QLe1 -> True
  QW -> True
  Q1 -> False
  QGe1 -> False

-- ── The annotation pass ──────────────────────────────────────────────

-- | Stage S1.1 ownership annotation.
--
-- Given the typing context and the elaborated, zonked Core body of each
-- top-level definition (the same @csCoreBodies@ map the native backend lowers),
-- produce the per-definition ownership side-table: for every runtime-relevant
-- binder its 'BinderOwn' facts, and for every 'CVar' occurrence its 'UseKind'
-- ('LastUse'\/'NonLast'\/'Borrowed') under per-branch liveness.
--
-- @ctx@ supplies the global signatures: a top-level body is a chain of leading
-- 'CLam's whose ownership convention — the declared quantity, borrow (@&@)
-- marker, and erased-kind-domain status — lives on the corresponding 'CPi' of
-- the global's /type/, not on the 'CLam' (which carries no borrow field or
-- domain). So we read the owner's type telescope (via 'paramTelescope') and zip
-- it against the leading 'CLam's, the single source of truth for the
-- owned\/borrowed parameter convention (avoiding a second side table, per
-- PERCEUS-S1-PLAN A3).
annotateOwnership :: EvalCtx -> Map GName Term -> Map GName Term -> Map GName OwnInfo
annotateOwnership ctx = annotateOwnershipWithUniverses ctx . monomorphicCtorTypes

annotateOwnershipWithUniverses :: EvalCtx -> OwnershipCtorTypes -> Map GName Term -> Map GName OwnInfo
annotateOwnershipWithUniverses ctx ctorTypes =
  Map.mapWithKey (\g body -> analyzeBody ctx ctorTypes (paramTelescope ctx g) g body)

monomorphicCtorTypes :: Map GName Term -> OwnershipCtorTypes
monomorphicCtorTypes =
  Map.map (OwnershipCtorType (DeclarationUniverseTelescope 0 False))

-- | The leading parameter telescope of a global's declared type, as a list of
-- parameter sites in binder order (the owned\/borrowed convention §12.3 plus
-- the domain needed to detect RuntimeErased kind arguments). Read by zipping
-- against the body's leading 'CLam's. An unknown global or a type that does not
-- force to a 'VPi' telescope yields @[]@ — fail-safe (the binders then fall back
-- to their 'CLam' quantity with borrow=False and unknown type).
data ParamSite = ParamSite
  { psIcit :: !Icit
  , psQ :: !Q
  , psBorrowed :: !Bool
  , psLevel :: !Int
  , psRuntimeErasure :: !(RuntimeErasure Value)
  , psDomainValue :: !Value
  }
  deriving stock (Show)

paramTelescope :: EvalCtx -> GName -> [ParamSite]
paramTelescope ctx g =
  case Map.lookup g (globalsMap (ecGlobals ctx)) of
    Nothing -> []
    Just gd -> paramConvTelescopeFromValue ctx (gdType gd)

-- | A binder in scope during the walk, paired with its absolute de Bruijn LEVEL
-- (depth at which it was introduced). The level is the stable key for liveness
-- bookkeeping inside one body; the 'BinderId' is the external key recorded in
-- 'oiBinders'.
--
-- A binder may be UNTRACKED ('scId == Nothing'): it occupies a de Bruijn slot —
-- so it must be pushed to keep indices aligned — but it is type-level (a 'CPi'
-- binder, or any binder occurring inside an erased type position), so it
-- records no 'BinderOwn' and a 'CVar' resolving to it is not a runtime use. Only
-- value-producing binders ('CLam' params, @let@\/@letrec@ names, match-arm
-- pattern vars) are tracked.
data Scope = Scope
  { scLevel :: !Int -- ^ absolute de Bruijn level of this binder (0 = outermost)
  , scId :: !(Maybe BinderId) -- ^ 'Nothing' for an untracked (type-level) binder
  , scBorrowed :: !Bool
  , scType :: !(Maybe Value)
  -- ^ The binder's type when available. Used only to classify first-class
  -- call arguments; unknown means the S2 all-shared fallback.
  }

-- | A lightweight scope used only while computing S2.3d borrowed-result owner
-- dependencies for one RHS. Local binders inside that RHS do not become public
-- 'OwnInfo' binders here, but they must still occupy de Bruijn levels and carry
-- any borrowed-owner dependencies of their initializer so aliases like
-- @let y = let z = h.box in z@ keep @h@ live while @y@ is live.
data BorrowDepScope = BorrowDepScope
  { bdsLevel :: !Int
  , bdsBid :: !(Maybe BinderId)
  , bdsDeps :: !(Set BinderId)
  , bdsType :: !(Maybe Value)
  }

-- | The output accumulated by the walk: the binder facts, the per-occurrence
-- use classifications, and (for the S1.2 cross-check) the per-binder multiset of
-- classifications its occurrences resolved to. The third map is derivable from
-- the first two only WITH the body in hand (the binder↔occurrence link is the de
-- Bruijn resolution), so it is accumulated here during the single walk rather
-- than reconstructed — that keeps exactly one traversal as the source of truth.
data Acc = Acc
  { accBinders :: !(Map BinderId BinderOwn)
  , accUses :: !(Map UseSite UseKind)
  , accUseConsumes :: !(Map UseSite Bool)
  , accAssoc :: !(Map BinderId [UseKind])
  , accConsumingAssoc :: !(Map BinderId [UseKind])
  , accBranchDropSites :: !(Map BranchSite [BinderId])
  , accBorrowDeps :: !(Map BinderId (Set BinderId))
  , accNextBinderId :: !Int
  , accNextUseSite :: !Int
  , accNextBranchSite :: !Int
  }

emptyAcc :: Acc
emptyAcc = Acc Map.empty Map.empty Map.empty Map.empty Map.empty Map.empty Map.empty 0 0 0

freshBinderId :: GName -> Acc -> (BinderId, Acc)
freshBinderId owner acc =
  let n = accNextBinderId acc
   in (BinderId owner n, acc {accNextBinderId = n + 1})

freshUseSite :: GName -> Acc -> (UseSite, Acc)
freshUseSite owner acc =
  let n = accNextUseSite acc
   in (UseSite owner n, acc {accNextUseSite = n + 1})

freshBranchSite :: Acc -> (BranchSite, Acc)
freshBranchSite acc =
  let n = accNextBranchSite acc
   in (BranchSite n, acc {accNextBranchSite = n + 1})

-- | Analyze one top-level body into its 'OwnInfo' plus the binder→kinds
-- association the cross-check consumes. @tele@ is the owner's declared parameter
-- telescope ('paramTelescope'), consumed by the body's leading 'CLam's to pick
-- up the owned\/borrowed convention and parameter types from the type.
analyzeBodyFull :: EvalCtx -> OwnershipCtorTypes -> [ParamSite] -> GName -> Term -> (OwnInfo, Map BinderId [UseKind], Map BinderId [UseKind])
analyzeBodyFull ctx ctorTypes tele owner body =
  let (acc, _live) = walk ctx ctorTypes tele owner 0 [] UseConsumes body Set.empty emptyAcc
   in ( OwnInfo
          (accBinders acc)
          (accUses acc)
          (accUseConsumes acc)
          (accAssoc acc)
          (accConsumingAssoc acc)
          (accBranchDropSites acc)
      , accAssoc acc
      , accConsumingAssoc acc
      )

-- | Analyze one top-level body into its 'OwnInfo'.
analyzeBody :: EvalCtx -> OwnershipCtorTypes -> [ParamSite] -> GName -> Term -> OwnInfo
analyzeBody ctx ctorTypes tele owner body =
  let (oi, _, _) = analyzeBodyFull ctx ctorTypes tele owner body
   in oi

-- | Record a binder fact.
addBinder :: BinderId -> Q -> Bool -> Acc -> Acc
addBinder bid q borrowed acc =
  acc
    { accBinders =
        Map.insert
          bid
          (BinderOwn q Nothing borrowed (qDroppable q))
          (accBinders acc)
    }

data UseConsumes = UseConsumes | UseReads | UseErased
  deriving stock (Eq, Show)

useConsumesBool :: UseConsumes -> Bool
useConsumesBool = \case
  UseConsumes -> True
  UseReads -> False
  UseErased -> False

useRuntimeUseBool :: UseConsumes -> Bool
useRuntimeUseBool = \case
  UseErased -> False
  UseConsumes -> True
  UseReads -> True

-- | Record one occurrence's use classification (both the per-occurrence key and
-- the per-binder association), plus whether this syntactic use consumes the
-- binder's owned reference.
addUse :: UseConsumes -> UseSite -> BinderId -> UseKind -> Acc -> Acc
addUse uc us bid k acc =
  let consumes = useConsumesBool uc && k /= Borrowed
   in acc
        { accUses = Map.insert us k (accUses acc)
        , accUseConsumes = Map.insert us consumes (accUseConsumes acc)
        , accAssoc = Map.insertWith (++) bid [k] (accAssoc acc)
        , accConsumingAssoc =
            if consumes
              then Map.insertWith (++) bid [k] (accConsumingAssoc acc)
              else accConsumingAssoc acc
        }

addBorrowDeps :: BinderId -> Set BinderId -> Acc -> Acc
addBorrowDeps bid deps acc
  | Set.null deps = acc {accBorrowDeps = Map.delete bid (accBorrowDeps acc)}
  | otherwise = acc {accBorrowDeps = Map.insert bid deps (accBorrowDeps acc)}

-- | Record the S2.3d drop sites for binders that are live in the branch join
-- but absent from this particular branch. The ownership walk already computes
-- each branch against the same live-out set; this only preserves the branch-local
-- omission fact for codegen instead of collapsing it into the per-binder use
-- multiset. Filtering by 'BinderOwn' is intentionally left to the backend so
-- the same stored table can be drift-checked against a fresh walk.
addBranchDeadDrops :: GName -> [Scope] -> Set Int -> Set Int -> Acc -> Acc
addBranchDeadDrops owner scopes liveJoin liveBranch =
  addBranchDeadDropsExcept owner scopes liveJoin liveBranch Set.empty

addBranchDeadDropsExcept :: GName -> [Scope] -> Set Int -> Set Int -> Set BinderId -> Acc -> Acc
addBranchDeadDropsExcept owner scopes liveJoin liveBranch excluded acc =
  case bids of
    [] -> acc
    _ ->
      let (site, acc') = freshBranchSite acc
       in acc'
        { accBranchDropSites =
            Map.insertWith (++) site bids (accBranchDropSites acc')
        }
  where
    liveBranchWithDeps = expandLiveWithBorrowDeps scopes (accBorrowDeps acc) liveBranch
    deadHere = Set.toList (liveJoin `Set.difference` liveBranchWithDeps)
    bids =
      [ bid
      | lvl <- deadHere
      , Just sc <- [lookupLevel lvl scopes]
      , Just bid <- [scId sc]
      , biOwner bid == owner
      , bid `Set.notMember` excluded
      ]

expandLiveWithBorrowDeps :: [Scope] -> Map BinderId (Set BinderId) -> Set Int -> Set Int
expandLiveWithBorrowDeps scopes deps live =
  live `Set.union` depLevels
  where
    levelByBid =
      Map.fromList
        [ (bid, scLevel sc)
        | sc <- scopes
        , Just bid <- [scId sc]
        ]
    liveBids =
      Set.fromList
        [ bid
        | lvl <- Set.toList live
        , Just sc <- [lookupLevel lvl scopes]
        , Just bid <- [scId sc]
        ]
    closedBids = closeBids deps liveBids
    depLevels =
      Set.fromList
        [ lvl
        | bid <- Set.toList (closedBids `Set.difference` liveBids)
        , Just lvl <- [Map.lookup bid levelByBid]
        ]

closeBids :: Map BinderId (Set BinderId) -> Set BinderId -> Set BinderId
closeBids deps seeds = go seeds (Set.toList seeds)
  where
    go seen [] = seen
    go seen (bid : rest) =
      let next = Map.findWithDefault Set.empty bid deps `Set.difference` seen
       in go (seen `Set.union` next) (Set.toList next ++ rest)

rhsBorrowDeps :: EvalCtx -> OwnershipCtorTypes -> Int -> [Scope] -> Map BinderId (Set BinderId) -> Term -> Set BinderId
rhsBorrowDeps ctx ctorTypes depth scopes deps term0 =
  closeBids deps (borrowedResultDeps depth (map liftScope scopes) term0)
  where
    liftScope sc =
      BorrowDepScope
        (scLevel sc)
        (scId sc)
        (maybe Set.empty (\bid -> closeBids deps (Map.findWithDefault Set.empty bid deps)) (scId sc))
        (scType sc)

    lookupDepLevel lvl = go
      where
        go [] = Nothing
        go (sc : rest)
          | bdsLevel sc == lvl = Just sc
          | otherwise = go rest

    scopeAt d scs i = lookupDepLevel (d - 1 - i) scs

    scopeTypeAtDep scs lvl = lookupDepLevel lvl scs >>= bdsType

    resultDepsOf sc = bdsDeps sc

    readDepsOf uc sc
      | useConsumesBool uc = bdsDeps sc
      | otherwise = maybe id Set.insert (bdsBid sc) (bdsDeps sc)

    freeDepsOf sc = maybe id Set.insert (bdsBid sc) (bdsDeps sc)

    localScope lvl deps' mTy =
      BorrowDepScope lvl Nothing (closeBids deps deps') mTy

    borrowedResultDeps d scs = \case
      CVar i -> maybe Set.empty resultDepsOf (scopeAt d scs i)
      CProjM _ e _ -> termFreeDeps d scs e
      CProjAtM _ e _ _ -> termFreeDeps d scs e
      CSealE _ e -> borrowedResultDeps d scs e
      t@CApp {} -> termFreeDeps d scs t
      CIf c t e ->
        termReadDeps d scs UseConsumes c
          `Set.union` borrowedResultDeps d scs t
          `Set.union` borrowedResultDeps d scs e
      CMatch s ann _resultAnn alts ->
        let scrutDeps = termReadDeps d scs UseReads s
            armDeps (CaseAlt pat mg b) =
              let n = patBindersC pat
                  slotTypes = reverse (patBindingTypes ctx ctorTypes d pat Nothing)
                  patScopes =
                    [ localScope (d + n - 1 - k) scrutDeps (indexMaybe k slotTypes >>= id)
                    | k <- [0 .. n - 1]
                    ]
                  scs' = patScopes ++ scs
                  d' = d + n
               in maybe Set.empty (termReadDeps d' scs' UseConsumes) mg
                    `Set.union` borrowedResultDeps d' scs' b
         in termReadDeps d scs UseConsumes s
              `Set.union` maybe Set.empty (termReadDeps d scs UseErased) ann
              `Set.union` Set.unions (map armDeps alts)
      CLetRuntimeM _ _ _ _ ty rhs b ->
        let rhsDeps = borrowedResultDeps d scs rhs
            rhsReads = termReadDeps d scs UseConsumes rhs
            sc = localScope d rhsDeps (Just (evalTypeAt ctx d ty))
         in rhsReads `Set.union` borrowedResultDeps (d + 1) (sc : scs) b
      CLetRecRuntimeM _ _ _ _ ty rhs b ->
        let sc0 = localScope d Set.empty (Just (evalTypeAt ctx d ty))
            rhsDeps = borrowedResultDeps (d + 1) (sc0 : scs) rhs
            rhsReads = termReadDeps (d + 1) (sc0 : scs) UseConsumes rhs
            sc = localScope d rhsDeps (Just (evalTypeAt ctx d ty))
         in rhsReads `Set.union` borrowedResultDeps (d + 1) (sc : scs) b
      CLamM _ _ _ _ b ->
        let sc = localScope d Set.empty Nothing
         in termFreeDeps (d + 1) (sc : scs) b
      CPiRuntimeM _ _ _ _ _ _ _ _ _ dom cod ->
        let sc = localScope d Set.empty (Just (evalTypeAt ctx d dom))
         in termReadDeps d scs UseErased dom `Set.union` termReadDeps (d + 1) (sc : scs) UseErased cod
      CThunkE e _ -> termFreeDeps d scs e
      CLazyE e _ -> termFreeDeps d scs e
      CDo _ items -> freeDoItems d scs items
      term -> termReadDeps d scs UseConsumes term

    termFreeDeps d scs = closeBids deps . freeDeps d scs

    freeDeps d scs = \case
      CVar i -> maybe Set.empty freeDepsOf (scopeAt d scs i)
      CApp _ f x -> freeDeps d scs f `Set.union` freeDeps d scs x
      CLamM _ _ _ _ b ->
        let sc = localScope d Set.empty Nothing
         in freeDeps (d + 1) (sc : scs) b
      CPiRuntimeM _ _ _ _ _ _ _ _ _ dom cod ->
        let sc = localScope d Set.empty (Just (evalTypeAt ctx d dom))
         in freeDeps d scs dom `Set.union` freeDeps (d + 1) (sc : scs) cod
      CLetRuntimeM _ _ _ _ ty rhs b ->
        let rhsDeps = borrowedResultDeps d scs rhs
            sc = localScope d rhsDeps (Just (evalTypeAt ctx d ty))
         in freeDeps d scs rhs `Set.union` freeDeps (d + 1) (sc : scs) b
      CLetRecRuntimeM _ _ _ _ ty rhs b ->
        let sc0 = localScope d Set.empty (Just (evalTypeAt ctx d ty))
            rhsDeps = borrowedResultDeps (d + 1) (sc0 : scs) rhs
            sc = localScope d rhsDeps (Just (evalTypeAt ctx d ty))
         in freeDeps (d + 1) (sc : scs) rhs `Set.union` freeDeps (d + 1) (sc : scs) b
      CMatch s ann _resultAnn alts ->
        let scrutDeps = termReadDeps d scs UseReads s
            freeAlt (CaseAlt pat mg b) =
              let n = patBindersC pat
                  slotTypes = reverse (patBindingTypes ctx ctorTypes d pat Nothing)
                  patScopes =
                    [ localScope (d + n - 1 - k) scrutDeps (indexMaybe k slotTypes >>= id)
                    | k <- [0 .. n - 1]
                    ]
                  scs' = patScopes ++ scs
                  d' = d + n
               in maybe Set.empty (freeDeps d' scs') mg `Set.union` freeDeps d' scs' b
         in freeDeps d scs s `Set.union` maybe Set.empty (freeDeps d scs) ann `Set.union` Set.unions (map freeAlt alts)
      CIf c t e -> freeDeps d scs c `Set.union` freeDeps d scs t `Set.union` freeDeps d scs e
      CCtorI _ _ ann arguments ->
        maybe Set.empty (freeDeps d scs) ann
          `Set.union` Set.unions
            [freeDeps d scs (caTerm argument) | argument <- arguments, caPayload argument]
      CRecordTQ fs -> Set.unions (map (freeDeps d scs . rfType) fs)
      CRecordV fs -> Set.unions (map (freeDeps d scs . snd) fs)
      CVariantT ms -> Set.unions (map (freeDeps d scs) ms)
      CProjM _ e _ -> freeDeps d scs e
      CProjAtM _ e _ _ -> freeDeps d scs e
      CInject _ e -> freeDeps d scs e
      CSealE _ e -> freeDeps d scs e
      CSigT _ e -> freeDeps d scs e
      CThunkE e _ -> freeDeps d scs e
      CLazyE e _ -> freeDeps d scs e
      CForceE e _ -> freeDeps d scs e
      CQuote _ slots -> Set.unions (map (freeDeps d scs) slots)
      CDo _ items -> freeDoItems d scs items
      _ -> Set.empty

    termReadDeps d scs uc = \case
      CVar i -> maybe Set.empty (readDepsOf uc) (scopeAt d scs i)
      t@CApp {} ->
        let (hd, args) = spineOfTerm t
            argConsumes = callArgConsumes ctx d (scopeTypeAtDep scs) hd args
            argDeps =
              Set.unions
                [ termReadDeps d scs argUse arg
                | ((_, arg), argUse) <- zip args argConsumes
                ]
         in termReadDeps d scs UseConsumes hd `Set.union` argDeps
      CProjM _ e _ -> termFreeDeps d scs e
      CProjAtM _ e _ _ -> termFreeDeps d scs e
      CSealE _ e -> termReadDeps d scs uc e
      CSigT _ e -> termReadDeps d scs uc e
      CThunkE e _ -> termReadDeps d scs UseConsumes e
      CLazyE e _ -> termReadDeps d scs UseConsumes e
      CForceE e _ -> termReadDeps d scs UseConsumes e
      CInject _ e -> termReadDeps d scs UseConsumes e
      CCtorI _ _ ann arguments ->
        maybe Set.empty (termReadDeps d scs UseErased) ann
          `Set.union` Set.unions
            [ termReadDeps d scs (if caPayload argument then UseConsumes else UseErased) (caTerm argument)
            | argument <- arguments
            ]
      CRecordTQ fs -> Set.unions (map (termReadDeps d scs UseErased . rfType) fs)
      CRecordV fs -> Set.unions (map (termReadDeps d scs UseConsumes . snd) fs)
      CVariantT ms -> Set.unions (map (termReadDeps d scs UseErased) ms)
      CIf c t e -> termReadDeps d scs UseConsumes c `Set.union` termReadDeps d scs uc t `Set.union` termReadDeps d scs uc e
      CMatch s ann _resultAnn alts ->
        let scrutDeps = termReadDeps d scs UseReads s
            readAlt (CaseAlt pat mg b) =
              let n = patBindersC pat
                  slotTypes = reverse (patBindingTypes ctx ctorTypes d pat Nothing)
                  patScopes =
                    [ localScope (d + n - 1 - k) scrutDeps (indexMaybe k slotTypes >>= id)
                    | k <- [0 .. n - 1]
                    ]
                  scs' = patScopes ++ scs
                  d' = d + n
               in maybe Set.empty (termReadDeps d' scs' UseConsumes) mg
                    `Set.union` termReadDeps d' scs' uc b
         in termReadDeps d scs UseConsumes s
              `Set.union` maybe Set.empty (termReadDeps d scs UseErased) ann
              `Set.union` Set.unions (map readAlt alts)
      CLetRuntimeM _ _ _ _ ty rhs b ->
        let rhsDeps = borrowedResultDeps d scs rhs
            sc = localScope d rhsDeps (Just (evalTypeAt ctx d ty))
         in termReadDeps d scs UseConsumes rhs `Set.union` termReadDeps (d + 1) (sc : scs) uc b
      CLetRecRuntimeM _ _ _ _ ty rhs b ->
        let sc0 = localScope d Set.empty (Just (evalTypeAt ctx d ty))
            rhsDeps = borrowedResultDeps (d + 1) (sc0 : scs) rhs
            sc = localScope d rhsDeps (Just (evalTypeAt ctx d ty))
         in termReadDeps (d + 1) (sc : scs) UseConsumes rhs `Set.union` termReadDeps (d + 1) (sc : scs) uc b
      CLamM _ _ _ _ b ->
        let sc = localScope d Set.empty Nothing
         in termReadDeps (d + 1) (sc : scs) uc b
      CPiRuntimeM _ _ _ _ _ _ _ _ _ dom cod ->
        let sc = localScope d Set.empty (Just (evalTypeAt ctx d dom))
         in termReadDeps d scs UseErased dom `Set.union` termReadDeps (d + 1) (sc : scs) UseErased cod
      CQuote _ slots -> Set.unions (map (termReadDeps d scs UseErased) slots)
      CDo _ items -> readDoItems d scs items
      _ -> Set.empty

    bindPatScopes d scs pat mTy valDeps =
      let n = patBindersC pat
          slotTypes = reverse (patBindingTypes ctx ctorTypes d pat mTy)
          newScopes =
            [ localScope (d + n - 1 - k) valDeps (indexMaybe k slotTypes >>= id)
            | k <- [0 .. n - 1]
            ]
       in (n, newScopes ++ scs)

    freeDoItems d scs = \case
      [] -> Set.empty
      item : rest ->
        case item of
          KBind _ pat t _ ->
            let valDeps = borrowedResultDeps d scs t
                (n, scs') = bindPatScopes d scs pat Nothing valDeps
             in termReadDeps d scs UseConsumes t `Set.union` freeDoItems (d + n) scs' rest
          KLet _ pat t ->
            let valDeps = borrowedResultDeps d scs t
                (n, scs') = bindPatScopes d scs pat Nothing valDeps
             in termReadDeps d scs UseConsumes t `Set.union` freeDoItems (d + n) scs' rest
          KLetQ pat t mElse ->
            let valDeps = borrowedResultDeps d scs t
                (n, scs') = bindPatScopes d scs pat Nothing valDeps
                success = freeDoItems (d + n) scs' rest
                failure = maybe Set.empty (\(_, e) -> termReadDeps d scs UseConsumes e `Set.union` freeDoItems d scs rest) mElse
             in termReadDeps d scs UseConsumes t `Set.union` success `Set.union` failure
          KVarItem _ initT actT _ ->
            let sc = localScope d Set.empty Nothing
             in termReadDeps d scs UseErased initT `Set.union` termReadDeps d scs UseConsumes actT `Set.union` freeDoItems (d + 1) (sc : scs) rest
          KExpr t -> termReadDeps d scs UseConsumes t `Set.union` freeDoItems d scs rest
          KAssign _ _ _ actT _ -> termReadDeps d scs UseConsumes actT `Set.union` freeDoItems d scs rest
          KReturn t -> termReadDeps d scs UseConsumes t
          KBreak _ -> Set.empty
          KContinue _ -> Set.empty
          KWhile _ cond body mElse ->
            readKCond d scs cond
              `Set.union` freeDoItems d scs body
              `Set.union` maybe Set.empty (freeDoItems d scs) mElse
              `Set.union` freeDoItems d scs rest
          KFor _ pat src body mElse ->
            let valDeps = termFreeDeps d scs src
                (n, scs') = bindPatScopes d scs pat Nothing valDeps
             in termReadDeps d scs UseConsumes src
                  `Set.union` freeDoItems (d + n) scs' body
                  `Set.union` maybe Set.empty (freeDoItems d scs) mElse
                  `Set.union` freeDoItems d scs rest
          KIf alts mElse ->
            Set.unions [termReadDeps d scs UseConsumes c `Set.union` freeDoItems d scs body | (c, body) <- alts]
              `Set.union` maybe Set.empty (freeDoItems d scs) mElse
              `Set.union` freeDoItems d scs rest
          KDefer _ t -> termReadDeps d scs UseConsumes t `Set.union` freeDoItems d scs rest
          KUsing pat acquireT releaseT ->
            let valDeps = borrowedResultDeps d scs acquireT
                (n, scs') = bindPatScopes d scs pat Nothing valDeps
             in termReadDeps d scs UseConsumes acquireT
                  `Set.union` termReadDeps d scs UseConsumes releaseT
                  `Set.union` freeDoItems (d + n) scs' rest
          KSubDo _ items -> freeDoItems d scs items `Set.union` freeDoItems d scs rest

    readDoItems d scs items = freeDoItems d scs items

    readKCond d scs = \case
      KCondPure t -> termReadDeps d scs UseConsumes t
      KCondAction t -> termReadDeps d scs UseConsumes t

-- | The core backward liveness walk.
--
-- Arguments:
--
--   * @tele@  — the owner's REMAINING declared parameter telescope @(Q, borrow)@
--     ('paramTelescope'), consumed one entry per leading 'CLam' so a top-level
--     parameter picks up the owned\/borrowed convention from its 'CPi'. Empty
--     once the leading-lambda chain ends (or for a non-top-level subterm).
--   * @owner@ — the global whose body is being walked (the key prefix).
--   * @depth@ — the number of binders currently in scope (= the absolute de
--     Bruijn level of the next binder to be introduced).
--   * @scopes@ — the binders in scope, innermost first, each tagged with its
--     absolute level (so a 'CVar' index @i@ resolves to level @depth-1-i@).
--   * @term@  — the node to walk.
--   * @liveOut@ — the set of binder LEVELS that are still live AFTER this term
--     on the current completion path (used to decide last-use).
--   * @acc@   — the accumulated facts.
--
-- Returns the updated @acc@ and the set of binder levels live AT (i.e. on
-- entry to) this term — its free-variable set restricted to tracked binders,
-- unioned with what flows in from @liveOut@ where appropriate.
walk
  :: EvalCtx
  -> OwnershipCtorTypes
  -> [ParamSite]
  -> GName
  -> Int
  -> [Scope]
  -> UseConsumes
  -> Term
  -> Set Int
  -> Acc
  -> (Acc, Set Int)
walk _ctx _ctorTypes _tele _owner _depth _scopes UseErased _term liveOut acc = (acc, liveOut)
walk ctx ctorTypes tele owner depth scopes useConsumes term liveOut acc = case term of
  CUniverseLift _ _ _ inner ->
    walk ctx ctorTypes tele owner depth scopes useConsumes inner liveOut acc
  CSchemaLift _ _ _ _ _ _ _ _ inner ->
    walk ctx ctorTypes tele owner depth scopes useConsumes inner liveOut acc
  CArithmeticProof _ -> (acc, liveOut)

  CVar i ->
    -- An occurrence of binder at level @lvl@. It is a LAST use on this path iff
    -- the same binder is not already live downstream (@lvl `notElem` liveOut@).
    -- A borrowed binder's uses are always 'Borrowed'.
    let lvl = depth - 1 - i
     in case lookupLevel lvl scopes of
          Just sc
            | Just bid <- scId sc ->
                let (us, acc0) = freshUseSite owner acc
                    kind
                      | scBorrowed sc = Borrowed
                      | lvl `Set.member` liveOut = NonLast
                      | otherwise = LastUse
                    acc' = addUse useConsumes us bid kind acc0
                    -- this binder is now a free variable of the surrounding
                    -- term; flow it upstream so an earlier occurrence sees it
                    -- as still-live (and is therefore NonLast).
                    live' = Set.insert lvl liveOut
                 in (acc', live')
          -- an untracked (type-level) or out-of-body binder: no runtime use.
          _ -> (acc, liveOut)

  CLocal i _ ->
    let lvl = depth - 1 - i
     in case lookupLevel lvl scopes of
          Just sc
            | Just bid <- scId sc ->
                let (us, acc0) = freshUseSite owner acc
                    kind
                      | scBorrowed sc = Borrowed
                      | lvl `Set.member` liveOut = NonLast
                      | otherwise = LastUse
                 in (addUse useConsumes us bid kind acc0, Set.insert lvl liveOut)
          _ -> (acc, liveOut)

  -- Binders ----------------------------------------------------------------
  CLamM _ _ q _nm b ->
    -- The top-level Pi telescope is authoritative for both ownership and
    -- runtime erasure. Kind/proof/Q0 parameters still occupy a Core de Bruijn
    -- slot, but they do not mint an ownership binder or occurrence identity.
    let site = case tele of
          p : _ -> Just p
          [] -> Nothing
        tele' = case tele of
          _ : rest -> rest
          [] -> []
        erased = case site of
          Just p -> runtimeErasedPiParam ctx (psLevel p) (psRuntimeErasure p) (psQ p) (psDomainValue p)
          Nothing -> q == Q0
     in if erased
          then
            let (declQ, mTy) = case site of
                  Just p -> (psQ p, Just (psDomainValue p))
                  Nothing -> (q, Nothing)
                (bid, accBid) = freshBinderId owner acc
                acc0 = addBinder bid declQ False accBid
                sc = Scope depth Nothing False mTy
                (acc1, liveB) = walk ctx ctorTypes tele' owner (depth + 1) (sc : scopes) UseConsumes b liveOut acc0
             in (acc1, dropLevel depth liveB)
          else
            let (declQ, borrowed, mTy) = case site of
                  Just p -> (psQ p, psBorrowed p, Just (psDomainValue p))
                  Nothing -> (q, False, Nothing)
                (bid, accBid) = freshBinderId owner acc
                sc = Scope depth (Just bid) borrowed mTy
                acc0 = addBinder bid declQ borrowed accBid
                (acc1, liveB) = walk ctx ctorTypes tele' owner (depth + 1) (sc : scopes) UseConsumes b liveOut acc0
             in (acc1, dropLevel depth liveB)

  CPiRuntimeM _ _ _ _q _borrowed _nm _ _ _ dom cod ->
    -- A Pi is a TYPE; its binder carries no runtime value. We descend (a
    -- dependent type can mention runtime binders in erased positions, and a
    -- type-valued top-level body is a bare 'CPi'), pushing an UNTRACKED scope so
    -- de Bruijn indices stay aligned, but record no binder fact and treat any
    -- codomain reference to it as a non-runtime (type-level) reference.
    let (acc1, liveDom) = walk ctx ctorTypes [] owner depth scopes UseErased dom liveOut acc
        sc = Scope depth Nothing False Nothing
        (acc2, liveCod) = walk ctx ctorTypes [] owner (depth + 1) (sc : scopes) UseErased cod liveDom acc1
     in (acc2, dropLevel depth liveCod)

  CLetRuntimeM _ q _nm runtimeErasure ty rhs b ->
    -- Sequential: the rhs runs, binds the name, then the body. Liveness flows
    -- backward — the body's live-out (minus the new binder) is the rhs's
    -- live-out. The binder's last-use is decided inside the body.
    let tyV = evalTypeAt ctx depth ty
        erased = runtimeErasedLocalAt ctx depth q runtimeErasure tyV
        rhsTele = paramConvTelescopeFromValueAt ctx depth tyV
     in if erased
          then
            let sc = Scope depth Nothing False (Just tyV)
                (acc1, liveBody) = walk ctx ctorTypes [] owner (depth + 1) (sc : scopes) useConsumes b liveOut acc
                liveBody' = dropLevel depth liveBody
             in walk ctx ctorTypes rhsTele owner depth scopes UseErased rhs liveBody' acc1
          else
            let (bid, accBid) = freshBinderId owner acc
                deps = rhsBorrowDeps ctx ctorTypes depth scopes (accBorrowDeps acc) rhs
                acc0 = addBorrowDeps bid deps (addBinder bid q False accBid)
                sc = Scope depth (Just bid) False (Just tyV)
                (acc1, liveBody) = walk ctx ctorTypes [] owner (depth + 1) (sc : scopes) useConsumes b liveOut acc0
                liveBody' = dropLevel depth liveBody
                (acc2, liveRhs) = walk ctx ctorTypes rhsTele owner depth scopes UseConsumes rhs liveBody' acc1
             in (acc2, liveRhs)

  CLetRecRuntimeM _ q _nm runtimeErasure ty rhs b ->
    -- Recursive local let: the binder is in scope in BOTH its rhs and its body.
    let tyV = evalTypeAt ctx depth ty
        erased = runtimeErasedLocalAt ctx depth q runtimeErasure tyV
        rhsTele = paramConvTelescopeFromValueAt ctx (depth + 1) tyV
     in if erased
          then
            let sc = Scope depth Nothing False (Just tyV)
                (acc1, liveBody) = walk ctx ctorTypes [] owner (depth + 1) (sc : scopes) useConsumes b liveOut acc
                (acc2, liveRhs) = walk ctx ctorTypes rhsTele owner (depth + 1) (sc : scopes) UseErased rhs liveBody acc1
             in (acc2, dropLevel depth liveRhs)
          else
            let (bid, accBid) = freshBinderId owner acc
                acc0 = addBinder bid q False accBid
                sc = Scope depth (Just bid) False (Just tyV)
                (acc1, liveBody) = walk ctx ctorTypes [] owner (depth + 1) (sc : scopes) useConsumes b liveOut acc0
                (acc2, liveRhs) = walk ctx ctorTypes rhsTele owner (depth + 1) (sc : scopes) UseConsumes rhs liveBody acc1
             in (acc2, dropLevel depth liveRhs)

  CLetPolyRuntimeM _ q _nm _ runtimeErasure ty rhs b ->
    let tyV = evalTypeAt ctx depth ty
        erased = runtimeErasedLocalAt ctx depth q runtimeErasure tyV
        rhsTele = paramConvTelescopeFromValueAt ctx depth tyV
     in if erased
          then
            let sc = Scope depth Nothing False (Just tyV)
                (acc1, liveBody) = walk ctx ctorTypes [] owner (depth + 1) (sc : scopes) useConsumes b liveOut acc
                liveBody' = dropLevel depth liveBody
             in walk ctx ctorTypes rhsTele owner depth scopes UseErased rhs liveBody' acc1
          else
            let (bid, accBid) = freshBinderId owner acc
                deps = rhsBorrowDeps ctx ctorTypes depth scopes (accBorrowDeps acc) rhs
                acc0 = addBorrowDeps bid deps (addBinder bid q False accBid)
                sc = Scope depth (Just bid) False (Just tyV)
                (acc1, liveBody) = walk ctx ctorTypes [] owner (depth + 1) (sc : scopes) useConsumes b liveOut acc0
                liveBody' = dropLevel depth liveBody
                (acc2, liveRhs) = walk ctx ctorTypes rhsTele owner depth scopes UseConsumes rhs liveBody' acc1
             in (acc2, liveRhs)

  CLetRecPolyRuntimeM _ q _nm _ runtimeErasure ty rhs b ->
    let tyV = evalTypeAt ctx depth ty
        erased = runtimeErasedLocalAt ctx depth q runtimeErasure tyV
        rhsTele = paramConvTelescopeFromValueAt ctx (depth + 1) tyV
     in if erased
          then
            let sc = Scope depth Nothing False (Just tyV)
                (acc1, liveBody) = walk ctx ctorTypes [] owner (depth + 1) (sc : scopes) useConsumes b liveOut acc
                (acc2, liveRhs) = walk ctx ctorTypes rhsTele owner (depth + 1) (sc : scopes) UseErased rhs liveBody acc1
             in (acc2, dropLevel depth liveRhs)
          else
            let (bid, accBid) = freshBinderId owner acc
                acc0 = addBinder bid q False accBid
                sc = Scope depth (Just bid) False (Just tyV)
                (acc1, liveBody) = walk ctx ctorTypes [] owner (depth + 1) (sc : scopes) useConsumes b liveOut acc0
                (acc2, liveRhs) = walk ctx ctorTypes rhsTele owner (depth + 1) (sc : scopes) UseConsumes rhs liveBody acc1
             in (acc2, dropLevel depth liveRhs)

  CLetRecGroupM _ definitions b ->
    let groupDepth = depth + length definitions
        allocate [] current = ([], current)
        allocate (definition : rest) current =
          let tyV = evalTypeAt ctx depth (clrdType definition)
              erased = runtimeErasedLocalAt ctx depth (clrdQuantity definition) (clrdRuntimeErasure definition) tyV
              (maybeBid, current1) =
                if erased
                  then (Nothing, current)
                  else
                    let (bid, next) = freshBinderId owner current
                     in (Just bid, addBinder bid (clrdQuantity definition) False next)
              (allocatedRest, current2) = allocate rest current1
           in ((definition, maybeBid, tyV, erased) : allocatedRest, current2)
        (allocated, acc0) = allocate definitions acc
        groupScopes =
          reverse
            [Scope (depth + index) maybeBid False (Just tyV) | (index, (_, maybeBid, tyV, _)) <- zip [0 ..] allocated]
              ++ scopes
        (acc1, liveBody) = walk ctx ctorTypes [] owner groupDepth groupScopes useConsumes b liveOut acc0
        walkDefinition (current, live) (definition, _, tyV, erased) =
          let rhsTele = paramConvTelescopeFromValueAt ctx groupDepth tyV
           in walk ctx ctorTypes rhsTele owner groupDepth groupScopes (if erased then UseErased else UseConsumes)
                (clrdRhs definition) live current
        (acc2, liveGroup) = foldl walkDefinition (acc1, liveBody) allocated
        liveOuter = foldr dropLevel liveGroup [depth .. groupDepth - 1]
     in (acc2, liveOuter)

  -- Branching: each arm is its own completion path -------------------------
  CMatch s ann _resultAnn alts ->
    -- The arms are independent completion paths joined here; the scrutinee runs
    -- first (sequentially before all arms). An arm uses a binder it pattern-
    -- binds, or an outer binder; an outer binder used in one arm but not
    -- another is dropped on the arms that omit it (its absence = a drop point),
    -- which falls out of computing each arm against the SAME @liveOut@.
    let (acc1, liveArms) = walkAlts ctx ctorTypes owner depth scopes useConsumes ann alts liveOut acc 0
        (acc2, liveS) = walk ctx ctorTypes [] owner depth scopes UseConsumes s liveArms acc1
     in (acc2, liveS)

  CIf c t e ->
    let (acc1, liveT) = walk ctx ctorTypes [] owner depth scopes useConsumes t liveOut acc
        (acc2, liveE) = walk ctx ctorTypes [] owner depth scopes useConsumes e liveOut acc1
        liveBranches = Set.union liveT liveE
        accDrops =
          addBranchDeadDrops owner scopes liveBranches liveE $
            addBranchDeadDrops owner scopes liveBranches liveT acc2
        (acc3, liveC) = walk ctx ctorTypes [] owner depth scopes UseConsumes c liveBranches accDrops
     in (acc3, liveC)

  -- Sequential, multi-child nodes ------------------------------------------
  CApp {} ->
    -- Evaluation order for a flat spine is head, then arguments left-to-right.
    -- Liveness flows backward through the arguments right-to-left, then through
    -- the head. Decomposing the full spine lets each argument be marked
    -- consuming/read according to the callee position while preserving the same
    -- nested application semantics the backend lowering consumes.
    let (hd, args) = spineOfTerm term
        argConsumes = callArgConsumes ctx depth (scopeTypeAt scopes) hd args
        argEntries = [(a, uc) | ((_, a), uc) <- zip args argConsumes]
        (accArgs, liveArgs) =
          foldr
            (\(a, uc) (aAcc, lo) -> walk ctx ctorTypes [] owner depth scopes uc a lo aAcc)
            (acc, liveOut)
            argEntries
        (accHead, liveHead) = walk ctx ctorTypes [] owner depth scopes UseConsumes hd liveArgs accArgs
     in (accHead, liveHead)

  CCtorI _ _ _ann arguments ->
    foldr
      ( \argument (nextAcc, nextLive) ->
          walk ctx ctorTypes [] owner depth scopes
            (if caPayload argument then UseConsumes else UseErased)
            (caTerm argument) nextLive nextAcc
      )
      (acc, liveOut)
      arguments

  CRecordTQ fs ->
    seqChildren ctx ctorTypes owner depth scopes UseErased (map rfType fs) liveOut acc
  CRecordV fs ->
    seqChildren ctx ctorTypes owner depth scopes UseConsumes (map snd fs) liveOut acc
  CVariantT ms ->
    seqChildren ctx ctorTypes owner depth scopes UseErased ms liveOut acc
  CQuote _ slots ->
    seqChildren ctx ctorTypes owner depth scopes UseErased slots liveOut acc

  -- Single-child nodes -----------------------------------------------------
  CProjM _ e _ -> descend1 ctx ctorTypes owner depth scopes UseReads e liveOut acc
  CProjAtM _ e _ _ -> descend1 ctx ctorTypes owner depth scopes UseReads e liveOut acc
  CInject _ e -> descend1 ctx ctorTypes owner depth scopes UseConsumes e liveOut acc
  CSealE _ e -> descend1 ctx ctorTypes owner depth scopes UseConsumes e liveOut acc
  CSigT _ e -> descend1 ctx ctorTypes owner depth scopes UseErased e liveOut acc
  CThunkE e _ -> descend1 ctx ctorTypes owner depth scopes UseConsumes e liveOut acc
  CLazyE e _ -> descend1 ctx ctorTypes owner depth scopes UseConsumes e liveOut acc
  CForceE e _ -> descend1 ctx ctorTypes owner depth scopes UseConsumes e liveOut acc

  -- Leaves and do-kernel ---------------------------------------------------
  CGlobal _ _ -> (acc, liveOut)
  CSort _ -> (acc, liveOut)
  CLevel _ -> (acc, liveOut)
  CLit _ -> (acc, liveOut)
  CMeta _ -> (acc, liveOut)
  CDo _ items -> walkDoItems ctx ctorTypes owner depth scopes items liveOut acc

-- | Walk a single child.
descend1 :: EvalCtx -> OwnershipCtorTypes -> GName -> Int -> [Scope] -> UseConsumes -> Term -> Set Int -> Acc -> (Acc, Set Int)
descend1 ctx ctorTypes owner depth scopes uc e liveOut acc =
  walk ctx ctorTypes [] owner depth scopes uc e liveOut acc

-- | Walk a sequence of children in left-to-right evaluation order, threading
-- liveness backward through them.
seqChildren
  :: EvalCtx -> OwnershipCtorTypes -> GName -> Int -> [Scope] -> UseConsumes -> [Term] -> Set Int -> Acc -> (Acc, Set Int)
seqChildren ctx ctorTypes owner depth scopes uc children liveOut acc =
  -- process right-to-left so a later child's liveness flows into the earlier
  -- child's live-out (an earlier occurrence is NonLast if a later one exists).
  foldr
    (\t (a, lo) -> walk ctx ctorTypes [] owner depth scopes uc t lo a)
    (acc, liveOut)
    children

bindPatternScopes :: GName -> Int -> Q -> Bool -> [Maybe Value] -> Acc -> Int -> ([Scope], Acc)
bindPatternScopes owner depth q borrowed slotTypes acc0 n =
  go 0 acc0 []
  where
    go k accRev rev
      | k >= n = (reverse rev, accRev)
      | otherwise =
          let (bid, acc1) = freshBinderId owner accRev
              sc = Scope (depth + n - 1 - k) (Just bid) borrowed (indexMaybe k slotTypes >>= id)
              acc2 = addBinder bid q borrowed acc1
           in go (k + 1) acc2 (sc : rev)

-- | Walk a §18.8 do-kernel. The sequencing is backward for liveness, but binder
-- scopes are introduced forward: a binding item is in scope for the remaining
-- items, not for the item action that creates it.
walkDoItems :: EvalCtx -> OwnershipCtorTypes -> GName -> Int -> [Scope] -> [KItem] -> Set Int -> Acc -> (Acc, Set Int)
walkDoItems ctx ctorTypes owner depth scopes items liveOut acc = go depth scopes items liveOut acc
  where
    go _ _ [] lo a = (a, lo)
    go d scs (item : rest) lo a =
      let dropLocal n live = foldr Set.delete live [d .. d + n - 1]
          bindPat q borrowed pat mTy a0 =
            let n = patBindersC pat
                slotTypes = reverse (patBindingTypes ctx ctorTypes d pat mTy)
                (newScopes, a1) = bindPatternScopes owner d q borrowed slotTypes a0 n
             in (n, newScopes, a1)
          walkRest d' scs' a0 = go d' scs' rest lo a0
          doRestThen uc t =
            let (aRest, liveRest) = go d scs rest lo a
             in walk ctx ctorTypes [] owner d scs uc t liveRest aRest
       in case item of
            KBind q pat t _ ->
              let (n, newScopes, aBind) = bindPat q False pat Nothing a
                  (aRest, liveRest) = walkRest (d + n) (newScopes ++ scs) aBind
                  liveBeforeRest = dropLocal n liveRest
               in walk ctx ctorTypes [] owner d scs UseConsumes t liveBeforeRest aRest

            KLet q pat t ->
              let (n, newScopes, aBind) = bindPat q False pat Nothing a
                  (aRest, liveRest) = walkRest (d + n) (newScopes ++ scs) aBind
                  liveBeforeRest = dropLocal n liveRest
               in walk ctx ctorTypes [] owner d scs UseConsumes t liveBeforeRest aRest

            KLetQ pat t mElse ->
              let (n, newScopes, aBind) = bindPat QW False pat Nothing a
                  (aRest, liveRest) = walkRest (d + n) (newScopes ++ scs) aBind
                  liveSuccess = dropLocal n liveRest
                  (aElse, liveElse) = case mElse of
                    Nothing -> (aRest, Set.empty)
                    Just (rp, fe) ->
                      let (rn, rScopes, aResidue) = bindPat QW False rp Nothing aRest
                          (aFe, liveFe) = walk ctx ctorTypes [] owner (d + rn) (rScopes ++ scs) UseConsumes fe lo aResidue
                       in (aFe, dropLocal rn liveFe)
                  liveBranches = Set.union liveSuccess liveElse
               in walk ctx ctorTypes [] owner d scs UseConsumes t liveBranches aElse

            KExpr t -> doRestThen UseConsumes t

            KVarItem _ _initT actT _ ->
              let (bid, aBid) = freshBinderId owner a
                  sc = Scope d (Just bid) False Nothing
                  aBind = addBinder bid QW False aBid
                  (aRest, liveRest) = walkRest (d + 1) (sc : scs) aBind
                  liveBeforeRest = Set.delete d liveRest
               in walk ctx ctorTypes [] owner d scs UseConsumes actT liveBeforeRest aRest

            KAssign _ _ _ actT _ -> doRestThen UseConsumes actT

            KReturn t ->
              walk ctx ctorTypes [] owner d scs UseConsumes t lo a

            KBreak _ -> (a, lo)
            KContinue _ -> (a, lo)

            KWhile _ cond body mElse ->
              let (aRest, liveRest) = walkRest d scs a
                  loopUses =
                    Set.unions
                      [ freeKCond d scs cond
                      , freeDoItems d scs body
                      ]
                  loopLiveOut = Set.union liveRest loopUses
                  (aBody, liveBody) = walkDoItems ctx ctorTypes owner d scs body loopLiveOut aRest
                  (aElse, liveElse) = case mElse of
                    Nothing -> (aBody, liveRest)
                    Just els -> walkDoItems ctx ctorTypes owner d scs els liveRest aBody
                  liveBeforeCond = Set.unions [loopLiveOut, liveBody, liveElse]
               in walkKCond d scs cond liveBeforeCond aElse

            KFor _ pat src body mElse ->
              let (aRest, liveRest) = walkRest d scs a
                  (n, newScopes, aBind) = bindPat QW False pat Nothing aRest
                  loopUses = Set.filter (< d) (freeDoItems (d + n) (newScopes ++ scs) body)
                  loopLiveOut = Set.union liveRest loopUses
                  (aBody, liveBody) = walkDoItems ctx ctorTypes owner (d + n) (newScopes ++ scs) body loopLiveOut aBind
                  liveBody' = dropLocal n liveBody
                  (aElse, liveElse) = case mElse of
                    Nothing -> (aBody, liveRest)
                    Just els -> walkDoItems ctx ctorTypes owner d scs els liveRest aBody
                  liveBeforeSrc = Set.unions [liveRest, liveBody', liveElse]
               in walk ctx ctorTypes [] owner d scs UseConsumes src liveBeforeSrc aElse

            KIf alts mElse ->
              let (aRest, liveRest) = walkRest d scs a
                  (aIf, liveIf) = walkKIf d scs alts mElse liveRest aRest
               in (aIf, liveIf)

            KDefer _ t -> doRestThen UseConsumes t

            KUsing pat acquireT releaseT ->
              let (n, newScopes, aBind) = bindPat QW True pat Nothing a
                  (aRest, liveRest) = walkRest (d + n) (newScopes ++ scs) aBind
                  liveBeforeRest = dropLocal n liveRest
                  (aRelease, liveRelease) = walk ctx ctorTypes [] owner d scs UseConsumes releaseT liveBeforeRest aRest
               in walk ctx ctorTypes [] owner d scs UseConsumes acquireT liveRelease aRelease

            KSubDo _ subItems ->
              let (aRest, liveRest) = walkRest d scs a
               in walkDoItems ctx ctorTypes owner d scs subItems liveRest aRest

    walkKCond d scs = \case
      KCondPure t -> walk ctx ctorTypes [] owner d scs UseConsumes t
      KCondAction t -> walk ctx ctorTypes [] owner d scs UseConsumes t

    freeTerm d scs t =
      snd (walk ctx ctorTypes [] owner d scs UseConsumes t Set.empty emptyAcc)

    freeKCond d scs = \case
      KCondPure t -> freeTerm d scs t
      KCondAction t -> freeTerm d scs t

    freeDoItems d scs kis =
      snd (walkDoItems ctx ctorTypes owner d scs kis Set.empty emptyAcc)

    walkKIf d scs alts mElse liveRest a =
      goAlts alts a
      where
        goAlts [] a0 =
          case mElse of
            Nothing -> (a0, liveRest)
            Just els -> walkDoItems ctx ctorTypes owner d scs els liveRest a0
        goAlts ((cond, body) : more) a0 =
          let (aBody, liveBody) = walkDoItems ctx ctorTypes owner d scs body liveRest a0
              (aMore, liveMore) = goAlts more aBody
              liveAfterCond = Set.union liveBody liveMore
           in walk ctx ctorTypes [] owner d scs UseConsumes cond liveAfterCond aMore

-- | Walk all arms of a 'CMatch'. Each arm is an INDEPENDENT completion path
-- joined against the same @liveOut@; the returned live set is the union over
-- arms (an outer binder is live before the match iff some arm uses it).
data AltLive = AltLive
  { altLiveEntry :: !(Set Int)
  , altLiveBody :: !(Set Int)
  , altLiveGuardConsumes :: !(Set BinderId)
  , altLiveHasGuard :: !Bool
  }

walkAlts
  :: EvalCtx -> OwnershipCtorTypes -> GName -> Int -> [Scope] -> UseConsumes -> Maybe Term -> [CaseAlt] -> Set Int -> Acc -> Int -> (Acc, Set Int)
walkAlts _ctx _ctorTypes _owner _depth _scopes _useConsumes _mScrutTy [] _liveOut acc _ai = (acc, Set.empty)
walkAlts ctx ctorTypes owner depth scopes useConsumes mScrutTy alts liveOut acc _ai0 =
  let (accWalk, armLives) = go alts acc
      liveAll = Set.unions (map altLiveEntry armLives)
      (_, accDrops) =
        foldl
          ( \(fallthroughConsumes, a) alt ->
              let liveAtDrop =
                    if altLiveHasGuard alt
                      then altLiveBody alt
                      else altLiveEntry alt
                  -- A consuming LastUse in an earlier guard may have transferred
                  -- the original value before this later arm is reached by guard
                  -- fallthrough. Until guard result/path-sensitive ownership is
                  -- modeled, suppress those later branch-dead drops rather than
                  -- risk a duplicate drop. If a later arm really uses the value,
                  -- 'guardFailLive' already makes the guard occurrence NonLast
                  -- and codegen emits a kdup, so it will not appear here.
                  excluded = fallthroughConsumes `Set.union` altLiveGuardConsumes alt
                  a' =
                    addBranchDeadDropsExcept
                      owner
                      scopes
                      liveAll
                      liveAtDrop
                      excluded
                      a
               in (fallthroughConsumes `Set.union` altLiveGuardConsumes alt, a')
          )
          (Set.empty, accWalk)
          armLives
   in (accDrops, liveAll)
  where
    go [] a = (a, [])
    go (alt : rest) a =
      let (aRest, liveRestAlts) = go rest a
          liveRest = Set.unions (map altLiveEntry liveRestAlts)
          (aAlt, liveAlt) = walkAlt ctx ctorTypes owner depth scopes useConsumes mScrutTy alt liveOut liveRest aRest
       in (aAlt, liveAlt : liveRestAlts)

-- | Walk one match arm. The pattern introduces @n = patBindersC@ binders that
-- are in scope for the guard and body, pushed innermost-LAST (so in the arm
-- body, the last pattern slot is de Bruijn 0; see 'Kappa.Eval.matchPat' /
-- @reverse binds@). We register one binder fact per pattern slot.
--
-- The arm's binder QUANTITY is not carried on the 'CorePat' node (patterns hold
-- no 'Q'), so a pattern binder's declared quantity is recorded as 'QW' — the
-- conservative droppable default. (The cross-check's linear\/borrowed
-- assertions therefore apply to 'CLam'\/'CLet'\/'CPi' binders, which DO carry
-- their 'Q'; pattern binders carry no linearity claim to validate.)
walkAlt
  :: EvalCtx -> OwnershipCtorTypes -> GName -> Int -> [Scope] -> UseConsumes -> Maybe Term -> CaseAlt -> Set Int -> Set Int -> Acc -> (Acc, AltLive)
walkAlt ctx ctorTypes owner depth scopes useConsumes mScrutTy (CaseAlt pat mguard body) liveOut guardFailLive acc =
  let n = patBindersC pat
      slotTypes = reverse (patBindingTypes ctx ctorTypes depth pat (evalTypeAt ctx depth <$> mScrutTy))
      -- pattern slots, innermost-first as they sit in the arm-body de Bruijn
      -- order: slot at body index @k@ was introduced at level @depth+n-1-k@.
      (newScopes, acc0) = bindPatternScopes owner depth QW False slotTypes acc n
      depth' = depth + n
      scopes' = newScopes ++ scopes
      -- guard (if any) runs before the body; both are under the pattern binders
      (acc1, liveBody) = walk ctx ctorTypes [] owner depth' scopes' useConsumes body liveOut acc0
      consumingBeforeGuard = accConsumingAssoc acc1
      (acc2, liveArm) = case mguard of
        Nothing -> (acc1, liveBody)
        Just g -> walk ctx ctorTypes [] owner depth' scopes' UseConsumes g (liveBody `Set.union` guardFailLive) acc1
      guardConsumes = case mguard of
        Nothing -> Set.empty
        Just _ -> consumingLastUseAssocDelta consumingBeforeGuard (accConsumingAssoc acc2)
      -- drop the pattern-bound levels: they are local to the arm
      liveBody' = foldr Set.delete liveBody [depth .. depth + n - 1]
      liveArm' = foldr Set.delete liveArm [depth .. depth + n - 1]
   in ( acc2
      , AltLive
          { altLiveEntry = liveArm'
          , altLiveBody = liveBody'
          , altLiveGuardConsumes = guardConsumes
          , altLiveHasGuard = case mguard of Nothing -> False; Just _ -> True
          }
      )

consumingLastUseAssocDelta :: Map BinderId [UseKind] -> Map BinderId [UseKind] -> Set BinderId
consumingLastUseAssocDelta before after =
  Map.keysSet $
    Map.filterWithKey
      ( \bid uses ->
          count LastUse uses > count LastUse (Map.findWithDefault [] bid before)
      )
      after
  where
    count k = length . filter (== k)

-- | Best-effort types for pattern-bound runtime slots, returned in the same
-- structural binding order as 'patBindings'. This is intentionally narrow:
-- unknown shapes yield 'Nothing' and keep the all-shared fallback. The common
-- S2.3b higher-order case is a constructor or record field whose annotated
-- scrutinee type exposes the field's function type.
patBindingTypes :: EvalCtx -> OwnershipCtorTypes -> Int -> CorePat -> Maybe Value -> [Maybe Value]
patBindingTypes ctx ctorTypes depth pat mTy =
  case pat of
    CPWild -> []
    CPLit _ -> []
    CPVarM _ _ -> [mTy]
    CPAsM _ _ p -> mTy : patBindingTypes ctx ctorTypes depth p mTy
    CPCtorM existentialModes bridges hidden g universes ps ->
      let nEx =
            length existentialModes + constructorBridgeBinderCount bridges
          fields = ctorFieldDomains ctx ctorTypes depth g universes (length ps) mTy
       in replicate nEx Nothing
            ++ constructorSourceBindingTypes hidden ps fields
    CPTuple ps ->
      concat [patBindingTypes ctx ctorTypes depth p (tupleFieldType ctx i =<< mTy) | (i, p) <- zip [0 ..] ps]
    CPRecordM fs mrest ->
      concat [patBindingTypes ctx ctorTypes depth p (recordFieldType ctx n =<< mTy) | (n, p) <- fs]
        ++ case mrest of
          Just (_, nm) | not (T.null nm) -> [Nothing]
          _ -> []
    CPInject tag p -> patBindingTypes ctx ctorTypes depth p (variantMemberType ctx depth tag =<< mTy)
    CPInjectRestM _ _ -> [mTy]
    CPOr ps _ ->
      case ps of
        p : _ -> patBindingTypes ctx ctorTypes depth p mTy
        [] -> []
  where
    constructorSourceBindingTypes hidden patterns fields =
      case
          interleaveConstructorSourceBinders
            hidden
            (zip patterns (fields ++ repeat Nothing))
        of
          Just slots ->
            concatMap
              ( \case
                  Left _ -> [Nothing]
                  Right (pattern', fieldType) ->
                    patBindingTypes ctx ctorTypes depth pattern' fieldType
              )
              slots
          Nothing ->
            replicate (length hidden) Nothing
              ++ concatMap
                (\pattern' -> patBindingTypes ctx ctorTypes depth pattern' Nothing)
                patterns

ctorFieldDomains :: EvalCtx -> OwnershipCtorTypes -> Int -> GName -> [Level] -> Int -> Maybe Value -> [Maybe Value]
ctorFieldDomains ctx ctorTypes depth g universes arity mScrutTy =
  let (sites, resultTy) =
        case Map.lookup g ctorTypes of
          Nothing -> ([], VSort LZero)
          Just constructorType ->
            let specialized = specializeCtorForOccurrence constructorType universes
             in paramConvTelescopeWithResult ctx (eval ctx [] specialized)
      fields = drop (max 0 (length sites - arity)) sites
   in case maybe (Just Map.empty) (ctorResultSubst ctx depth resultTy) mScrutTy of
        Nothing -> replicate arity Nothing
        Just subst -> map (Just . substValue ctx subst . psDomainValue) fields

specializeCtorForOccurrence :: OwnershipCtorType -> [Level] -> Term
specializeCtorForOccurrence OwnershipCtorType {..} universes
  | length universes == dutParameterCount octUniverses =
      zonkTermWith (\_ _ -> Nothing) (substituteLevelParams universes) 0 octType
  | otherwise = octType

ctorResultSubst :: EvalCtx -> Int -> Value -> Value -> Maybe (Map Int Value)
ctorResultSubst ctx depth resultTy scrutTy =
  matchValue Map.empty resultTy scrutTy
  where
    matchValue subst pat actual =
      let pat' = force ctx pat
          actual' = force ctx actual
       in case (pat', actual') of
        (VRigid lvl [], a) -> bindLevel subst lvl a
        (VRigid lvl psp, VRigid lvl' asp)
          | lvl == lvl', length psp == length asp -> matchSpines subst psp asp
          | lvl == lvl' -> Nothing
        (VFlex m psp, VFlex m' asp)
          | m == m', length psp == length asp -> matchSpines subst psp asp
          | m == m' -> Nothing
        (VGlobal g pus psp, VGlobal g' aus asp)
          | g == g', pus == aus, length psp == length asp -> matchSpines subst psp asp
          | g == g' -> Nothing
          | otherwise -> Nothing
        (VCtor g pas, VCtor g' aas)
          | g == g', length pas == length aas -> matchValues subst pas aas
          | otherwise -> Nothing
        (VRecordTQ pfs, VRecordTQ afs)
          | map rfName pfs == map rfName afs -> matchValues subst (map rfType pfs) (map rfType afs)
          | otherwise -> Nothing
        (VVariantT pms, VVariantT ams)
          | length pms == length ams -> matchValues subst pms ams
          | otherwise -> Nothing
        (VInject ptag px, VInject atag ax)
          | ptag == atag -> matchValue subst px ax
          | otherwise -> Nothing
        (VSort p, VSort a)
          | p == a -> Just subst
          | otherwise -> Nothing
        (VLit p, VLit a)
          | p == a -> Just subst
          | otherwise -> Nothing
        _
          | sameValue pat' actual' -> Just subst
          | neutralOrOpaque pat' || neutralOrOpaque actual' -> Just subst
          | otherwise -> Nothing

    matchSpines subst psp asp =
      foldl
        ( \m ((pic, pv), (aic, av)) ->
            m >>= \subst' ->
              if pic == aic then matchValue subst' pv av else Nothing
        )
        (Just subst)
        (zip psp asp)

    matchValues subst ps as =
      foldl
        (\m (p, a) -> m >>= \subst' -> matchValue subst' p a)
        (Just subst)
        (zip ps as)

    bindLevel subst lvl actual =
      case Map.lookup lvl subst of
        Nothing -> Just (Map.insert lvl actual subst)
        Just old
          | sameValue old actual -> Just subst
          | otherwise -> Nothing

    sameValue a b =
      renderTerm (quote ctx depth (deepForceValue ctx a))
        == renderTerm (quote ctx depth (deepForceValue ctx b))

    neutralOrOpaque = \case
      VRigid {} -> True
      VFlex {} -> True
      VMatchN {} -> True
      VProjN {} -> True
      VAppN {} -> True
      VIfN {} -> True
      VMVar {} -> True
      VRef {} -> True
      VArr {} -> True
      VFiber {} -> True
      VScope {} -> True
      VFiberRef {} -> True
      VTVar {} -> True
      VDoV {} -> True
      VIOAction {} -> True
      _ -> False

substValue :: EvalCtx -> Map Int Value -> Value -> Value
substValue ctx subst = go
  where
    go v =
      case v of
        VRigid lvl sp ->
          let sp' = [(ic, go a) | (ic, a) <- sp]
           in case Map.lookup lvl subst of
                Just base -> evalApp ctx base sp'
                Nothing -> VRigid lvl sp'
        VFlex m sp -> VFlex m [(ic, go a) | (ic, a) <- sp]
        VGlobal g universes sp -> VGlobal g universes [(ic, go a) | (ic, a) <- sp]
        VLamM mode ic q n clo -> VLamM mode ic q n (substClosure clo)
        VPiRuntimeM mode formation ic q borrowed n assumption origin runtimeErasure dom clo ->
          VPiRuntimeM
            mode
            formation
            ic
            q
            borrowed
            n
            assumption
            origin
            (fmap go runtimeErasure)
            (go dom)
            (substClosure clo)
        VCtorI g universes arguments ->
          VCtorI g universes
            [argument {cvaValue = go (cvaValue argument)} | argument <- arguments]
        VRecordTQ fs -> VRecordTQ (map (fmap go) fs)
        VRecordV fs -> VRecordV [(n, go x) | (n, x) <- fs]
        VVariantT ms -> VVariantT (map go ms)
        VInject tag x -> VInject tag (go x)
        VMatchN scrut scrutineeAnnotation resultAnnotation alts env ->
          VMatchN
            (go scrut)
            (go <$> scrutineeAnnotation)
            (go <$> resultAnnotation)
            alts
            (map go env)
        VProjN mode x field -> VProjN mode (go x) field
        VAppN ic f a -> VAppN ic (go f) (go a)
        VSealV ls x -> VSealV ls (go x)
        VSigT ls x -> VSigT ls (go x)
        VDoV lbl items env -> VDoV lbl items (map go env)
        VThunkV clo -> VThunkV (substClosure clo)
        VLazyV clo -> VLazyV (substClosure clo)
        VIfN c t f -> VIfN (go c) (substClosure t) (substClosure f)
        VArithmeticProof certificate -> VArithmeticProof (mapArithmeticCertificate go certificate)
        VPrim p args -> VPrim p (map go args)
        VQuote qs slots -> VQuote qs (map go slots)
        VSort {} -> v
        VLevel {} -> v
        VUniverseLift from to evidence inner ->
          VUniverseLift from to evidence (go inner)
        VLit {} -> v
        VRef {} -> v
        VArr {} -> v
        VMVar {} -> v
        VFiber {} -> v
        VScope {} -> v
        VFiberRef {} -> v
        VTVar {} -> v
        VIOAction p args -> VIOAction p (map go args)

    substClosure (Closure env body) = Closure (map go env) body

recordFieldType :: EvalCtx -> Text -> Value -> Maybe Value
recordFieldType ctx name v =
  case force ctx v of
    VRecordTQ fs -> rfType <$> find ((== name) . rfName) fs
    _ -> Nothing

tupleFieldType :: EvalCtx -> Int -> Value -> Maybe Value
tupleFieldType ctx i v =
  case force ctx v of
    VRecordTQ fs -> rfType <$> indexMaybe i fs
    _ -> Nothing

variantMemberType :: EvalCtx -> Int -> Text -> Value -> Maybe Value
variantMemberType ctx depth tag v =
  case force ctx v of
    VVariantT members -> go members
    _ -> Nothing
  where
    go [] = Nothing
    go (m : rest)
      | variantTag ctx depth m == tag = Just m
      | otherwise = go rest

variantTag :: EvalCtx -> Int -> Value -> Text
variantTag ctx depth v = renderTerm (quote ctx depth (deepForceValue ctx v))

deepForceValue :: EvalCtx -> Value -> Value
deepForceValue ctx = go (32 :: Int)
  where
    go 0 v = v
    go fuel v =
      case force ctx v of
        VGlobal g universes sp -> VGlobal g universes [(ic, go (fuel - 1) a) | (ic, a) <- sp]
        VCtor g as -> VCtor g (map (go (fuel - 1)) as)
        VRecordTQ fs -> VRecordTQ (map (fmap (go (fuel - 1))) fs)
        VVariantT ms -> VVariantT (map (go (fuel - 1)) ms)
        v' -> v'

evalTypeAt :: EvalCtx -> Int -> Term -> Value
evalTypeAt ctx depth = eval ctx (rigidEnv depth)

runtimeErasedLocalAt :: EvalCtx -> Int -> Q -> RuntimeErasure Term -> Value -> Bool
runtimeErasedLocalAt ctx depth quantity runtimeErasure ty =
  runtimeErasedPiParam ctx depth (fmap (evalTypeAt ctx depth) runtimeErasure) quantity ty

rigidEnv :: Int -> [Value]
rigidEnv depth = [VRigid (depth - 1 - i) [] | i <- [0 .. depth - 1]]

indexMaybe :: Int -> [a] -> Maybe a
indexMaybe i xs
  | i < 0 = Nothing
  | otherwise = go i xs
  where
    go 0 (x : _) = Just x
    go n (_ : rest) = go (n - 1) rest
    go _ [] = Nothing

-- | Resolve a de Bruijn LEVEL to its in-scope binder, if tracked.
lookupLevel :: Int -> [Scope] -> Maybe Scope
lookupLevel lvl = go
  where
    go [] = Nothing
    go (sc : rest)
      | scLevel sc == lvl = Just sc
      | otherwise = go rest

-- | Remove a binder level from a live set (its scope has ended).
dropLevel :: Int -> Set Int -> Set Int
dropLevel = Set.delete

scopeTypeAt :: [Scope] -> Int -> Maybe Value
scopeTypeAt scopes lvl = lookupLevel lvl scopes >>= scType

callArgConsumes :: EvalCtx -> Int -> (Int -> Maybe Value) -> Term -> [(Icit, Term)] -> [UseConsumes]
callArgConsumes ctx depth localType hd args =
  case hd of
    CGlobal g _ -> classifyCallArgs ctx GlobalCall (argConvSelectGlobal ctx g) (paramConvTelescope ctx g) args
    _ ->
      case termTypeAt ctx depth localType hd of
        Just ty -> classifyCallArgs ctx LocalCall Nothing (paramConvTelescopeFromValueAt ctx depth ty) args
        Nothing -> sharedFallback
  where
    -- S2 all-shared fallback for non-global/unknown function values. Shared is
    -- represented as a consuming transfer in this side table: the caller cannot
    -- prove it retains ownership.
    sharedFallback = replicate (length args) UseConsumes

termTypeAt :: EvalCtx -> Int -> (Int -> Maybe Value) -> Term -> Maybe Value
termTypeAt ctx depth localType = go
  where
    go = \case
      CGlobal g _ -> argConvGlobalType ctx g
      CVar i -> localType (depth - 1 - i)
      CProjM _ e field -> recordFieldType ctx field =<< go e
      CProjAtM _ e field _ -> recordFieldType ctx field =<< go e
      CSealE _ e -> go e
      CMatch _ _ resultAnn _ -> evalTypeAt ctx depth <$> resultAnn
      CIf _ t f -> sameType (go t) (go f)
      t@CApp {} ->
        let (h, args) = spineOfTerm t
         in go h >>= \ty -> applyArgs ty args
      _ -> Nothing

    applyArgs ty [] = Just ty
    applyArgs ty ((ic, arg) : rest) =
      case force ctx ty of
        VPiEvidenceM _ _ pic _ _ _ _ _ _ (Closure env cod)
          | ic == pic ->
              let argV = eval ctx (rigidEnv depth) arg
               in applyArgs (eval ctx (argV : env) cod) rest
        _ -> Nothing

    sameType (Just a) (Just b)
      | renderTerm (quote ctx depth (deepForceValue ctx a))
          == renderTerm (quote ctx depth (deepForceValue ctx b)) =
          Just a
    sameType _ _ = Nothing

data CallMode = GlobalCall | LocalCall
  deriving stock (Eq, Show)

paramConvTelescope :: EvalCtx -> GName -> [ParamSite]
paramConvTelescope ctx g =
  case argConvGlobalType ctx g of
    Nothing -> []
    Just ty -> paramConvTelescopeFromValue ctx ty

paramConvTelescopeFromValue :: EvalCtx -> Value -> [ParamSite]
paramConvTelescopeFromValue ctx = paramConvTelescopeFromValueAt ctx 0

paramConvTelescopeFromValueAt :: EvalCtx -> Int -> Value -> [ParamSite]
paramConvTelescopeFromValueAt ctx lvl ty = fst (paramConvTelescopeWithResultAt ctx lvl ty)

paramConvTelescopeWithResult :: EvalCtx -> Value -> ([ParamSite], Value)
paramConvTelescopeWithResult ctx = paramConvTelescopeWithResultAt ctx 0

paramConvTelescopeWithResultAt :: EvalCtx -> Int -> Value -> ([ParamSite], Value)
paramConvTelescopeWithResultAt ctx = go
  where
    go lvl ty =
      case force ctx ty of
        VPiRuntimeM _ _ ic q borrowed _ _ _ runtimeErasure dom (Closure env cod) ->
          let x = VRigid lvl []
              domV = force ctx dom
              codV = eval ctx (x : env) cod
              (sites, resultTy) = go (lvl + 1) codV
           in (ParamSite ic q borrowed lvl runtimeErasure domV : sites, resultTy)
        resultTy -> ([], resultTy)

classifyCallArgs :: EvalCtx -> CallMode -> Maybe [ArgConv] -> [ParamSite] -> [(Icit, Term)] -> [UseConsumes]
classifyCallArgs ctx mode mConvs tele0 = go mConvs tele0
  where
    go _ _ [] = []
    go convs tele ((ic, _) : rest) =
      case takeMatching ic tele of
        Just (site, tele') ->
          let (use, convs') = paramConsumes convs site
           in use : go convs' tele' rest
        Nothing ->
          UseConsumes : go convs tele rest

    takeMatching _ [] = Nothing
    takeMatching ic (p : ps)
      | ic == psIcit p = Just (p, ps)
      | otherwise = takeMatching ic ps

    paramConsumes convs site
      | mode == GlobalCall && erasedOrKind site = (UseErased, convs)
      | mode == LocalCall && erasedOrKind site = (UseReads, convs)
      | Just (conv : rest) <- convs = (argConvConsumes conv, Just rest)
      | Just [] <- convs = (UseConsumes, convs)
      | psBorrowed site = (UseReads, convs)
      | otherwise =
          ( case psQ site of
              Q1 -> UseConsumes
              QGe1 -> UseConsumes
              QW -> UseConsumes
              QLe1 -> UseConsumes
              Q0 -> UseErased
          , convs
          )

    erasedOrKind site =
      runtimeErasedPiParam ctx (psLevel site) (psRuntimeErasure site) (psQ site) (psDomainValue site)

argConvConsumes :: ArgConv -> UseConsumes
argConvConsumes = \case
  ArgBorrowed -> UseReads
  ArgOwned -> UseConsumes
  ArgShared -> UseConsumes

-- ── S1.4 §3a whole-program usage refinement ──────────────────────────
--
-- A declared quantity is the UPPER BOUND the programmer committed to in the
-- signature; the program's ACTUAL usage may be tighter (PERCEUS-RC-DESIGN §3a).
-- @foo : ω Foo -> Bar@ whose body uses the @Foo@ exactly once supports refining
-- the effective range to @[1,1]@ — which lets a future S2 treat the parameter as
-- OWNED (drop\/reuse its storage instead of conservatively sharing it) and ELIDE
-- the @dup@ a conservative @ω@ would force. The refinement only ever TIGHTENS a
-- declared range, never widens it, so it can never violate the source contract.
--
-- == Whole-program soundness and the (currently empty) refinement boundary
--
-- The refinement is SOUND whenever the analysis sees ALL runtime uses of a
-- binder: a tightened interval is the exact count of non-borrowed runtime
-- occurrences over the binder's whole scope, so if every consumer is visible the
-- tightened bound cannot be wrong. Kappa's current compile is WHOLE-PROGRAM
-- STATIC — there is no dynamic linking and no separate compilation — so the
-- analysis ALWAYS sees every runtime use, and EVERY provably-single-use binder
-- is refinable, EXPORTED,
-- RE-EXPORTED, and internal alike. The earlier module-export\/re-export gating
-- (the 'csModuleExports'\/'csReExports' boundary suppression) was premature
-- conservatism: it suppressed sound cross-module refinements for a boundary that
-- does not yet exist. It is removed.
--
-- The boundary that genuinely gates §3a is the DYNAMIC-LINK \/ SEPARATELY-
-- COMPILED interface — the one place the analysis CANNOT see all uses (a
-- separately-compiled caller may use the value differently → an S2
-- use-after-free if S2 dropped\/reused it). That interface is EMPTY right now.
--
-- TODO — DYNAMIC LINKING \/ SEPARATE COMPILATION (a hard prerequisite before S2
-- ships under it): when a separately-compiled boundary exists, §3a MUST fall
-- back to the DECLARED quantity ('boRefined' = 'Nothing') for any binder
-- reachable through that interface. Re-add the gate then, keyed on the REAL
-- separate-compilation interface (NOT on module exports\/re-exports, which were
-- only a premature proxy for it).
--
-- __S1.4 is observe-only__ (no codegen reads 'boRefined' yet). The cross-check
-- ('crossCheckBodies') still asserts the tighten-only invariant: every
-- 'boRefined' is @<=@ its 'boDeclQ' as an interval (it never widens the declared
-- bound). The export-boundary assertion is gone — the boundary is empty in the
-- whole-program-static model.

-- | Stage S1.4 §3a refinement. Given the bodies and the S1.1 'OwnInfo' table,
-- TIGHTEN each binder's 'boRefined' to its actual whole-program usage interval
-- where it is strictly narrower than the declared 'boDeclQ'. EVERY binder is
-- eligible — exported, re-exported, and internal alike — because the compile is
-- whole-program static, so the analysis sees all uses (see the section note). The
-- refinement only ever tightens.
--
-- The actual per-binder usage interval is the precise abstract count of runtime
-- (non-borrowed) occurrences over the binder's scope ('usageIntervals'): summed
-- in sequence, joined (min\/max) across branches. Erased type/proof/staging
-- positions do not count. It is intersected with the declared interval, and
-- recorded only when STRICTLY tighter than the declared one (otherwise the
-- declared quantity already says everything).
refineOwnership
  :: EvalCtx -> Map GName Term -> Map GName Term -> Map GName OwnInfo -> Map GName OwnInfo
refineOwnership ctx = refineOwnershipWithUniverses ctx . monomorphicCtorTypes

refineOwnershipWithUniverses
  :: EvalCtx -> OwnershipCtorTypes -> Map GName Term -> Map GName OwnInfo -> Map GName OwnInfo
refineOwnershipWithUniverses ctx ctorTypes bodies =
  Map.mapWithKey refineOne
  where
    refineOne g oi =
      case Map.lookup g bodies of
        Nothing -> oi
        Just body ->
          let intervals = usageIntervals ctx ctorTypes g body
           in oi
                { oiBinders =
                    Map.mapWithKey (refineBinder intervals) (oiBinders oi)
                }

    refineBinder intervals bid bo
      -- a borrowed binder is governed by the borrow convention, not the
      -- runtime-use interval; leave it unrefined.
      | boBorrowed bo = bo {boRefined = Nothing}
      | otherwise =
          case Map.lookup bid intervals of
            Nothing -> bo {boRefined = Nothing}
            Just actual ->
              let declared = declInterval (boDeclQ bo)
                  tightened = intersectInterval declared actual
               in if strictlyTighter tightened declared
                    then bo {boRefined = Just tightened}
                    else bo {boRefined = Nothing}

-- | The declared quantity as a usage interval @(lo, hi)@ with @hi == Nothing@
-- meaning unbounded above.
declInterval :: Q -> (Int, Maybe Int)
declInterval = \case
  Q0 -> (0, Just 0)
  Q1 -> (1, Just 1)
  QW -> (0, Nothing)
  QLe1 -> (0, Just 1)
  QGe1 -> (1, Nothing)

-- | Intersect two intervals (the tighter of the two bounds on each side). The
-- declared interval is always the wider one here (the actual usage cannot exceed
-- what the quantity admits on a well-typed program), so this never produces an
-- empty interval; @max@ on the lower bound and the @minHi@ on the upper keep the
-- result a sub-interval of both.
intersectInterval :: (Int, Maybe Int) -> (Int, Maybe Int) -> (Int, Maybe Int)
intersectInterval (lo1, hi1) (lo2, hi2) = (max lo1 lo2, minHi hi1 hi2)
  where
    minHi Nothing h = h
    minHi h Nothing = h
    minHi (Just a) (Just b) = Just (min a b)

-- | Is the first interval STRICTLY tighter than (a proper sub-interval of) the
-- second? True iff it is contained in the second AND differs from it. Used so a
-- refinement is recorded only when it actually narrows the declared range.
strictlyTighter :: (Int, Maybe Int) -> (Int, Maybe Int) -> Bool
strictlyTighter inner outer = subInterval inner outer && inner /= outer

-- | Is the first interval contained in the second (@inner ⊆ outer@)? An open
-- upper bound ('Nothing') is @+∞@: it contains any @Just@ and is contained only
-- by another 'Nothing'.
subInterval :: (Int, Maybe Int) -> (Int, Maybe Int) -> Bool
subInterval (lo1, hi1) (lo2, hi2) = lo1 >= lo2 && hiLe hi1 hi2
  where
    hiLe _ Nothing = True
    hiLe Nothing (Just _) = False
    hiLe (Just a) (Just b) = a <= b

type CountScope = (Int, Maybe BinderId, Bool, Maybe Value)

-- | The precise per-binder runtime-use interval over a whole body, keyed by the
-- same 'BinderId's 'annotateOwnership' records. The interval @(lo, hi)@ counts how
-- many times the binder is used at runtime (read-only occurrences of owned
-- binders count; erased type/proof/staging positions do NOT count) along a
-- completion path: @lo@ over the path that uses it least, @hi@ over the path
-- that uses it most (@Nothing@ = unbounded, which never arises for a finite term
-- but is carried for totality). Sequential composition ADDS the per-binder
-- intervals; a branch ('CMatch'\/'CIf') JOINS them (min lower, max upper) since
-- each arm is its own path.
--
-- This mirrors the structure of the 'walk' liveness pass but tracks counts rather
-- than last-use, so the two stay independent (a bug in one cannot silently mask
-- the other). It returns intervals for value binders only; an untracked
-- (type-level) binder records none.
usageIntervals :: EvalCtx -> OwnershipCtorTypes -> GName -> Term -> Map BinderId (Int, Maybe Int)
usageIntervals ctx ctorTypes owner body =
  let (_uses, sub, _next) = count (paramTelescope ctx owner) 0 [] UseConsumes body 0
   in sub
  where
    fresh n = (BinderId owner n, n + 1)

    count
      :: [ParamSite]
      -> Int
      -> [CountScope]
      -> UseConsumes
      -> Term
      -> Int
      -> (Map BinderId (Int, Maybe Int), Map BinderId (Int, Maybe Int), Int)
    count _tele _depth _scopes UseErased _term next = (Map.empty, Map.empty, next)
    count tele depth scopes uc term next = case term of
      CUniverseLift _ _ _ inner -> count tele depth scopes uc inner next
      CSchemaLift _ _ _ _ _ _ _ _ inner -> count tele depth scopes uc inner next
      CArithmeticProof _ -> (Map.empty, Map.empty, next)

      CVar i ->
        let lvl = depth - 1 - i
         in case resolve lvl scopes of
              Just (Just bid, borrowed)
                | not borrowed, useRuntimeUseBool uc -> (Map.singleton bid (1, Just 1), Map.empty, next)
              _ -> (Map.empty, Map.empty, next)

      CLocal i _ ->
        let lvl = depth - 1 - i
         in case resolve lvl scopes of
              Just (Just bid, borrowed)
                | not borrowed, useRuntimeUseBool uc -> (Map.singleton bid (1, Just 1), Map.empty, next)
              _ -> (Map.empty, Map.empty, next)

      CLamM _ _ q _ b ->
        let site = case tele of
              p : _ -> Just p
              [] -> Nothing
            tele' = case tele of
              _ : rest -> rest
              [] -> []
            erased = case site of
              Just p -> runtimeErasedPiParam ctx (psLevel p) (psRuntimeErasure p) (psQ p) (psDomainValue p)
              Nothing -> q == Q0
         in if erased
              then
                let (bid, next1) = fresh next
                    (uses, sub, next2) = count tele' (depth + 1) ((depth, Nothing, False, psDomainValue <$> site) : scopes) UseConsumes b next1
                 in (uses, recordSelf bid Map.empty sub, next2)
              else
                let (bid, next1) = fresh next
                    (borrowed, mTy) = case site of
                      Just p -> (psBorrowed p, Just (psDomainValue p))
                      Nothing -> (False, Nothing)
                    (uses, sub, next2) = count tele' (depth + 1) ((depth, Just bid, borrowed, mTy) : scopes) UseConsumes b next1
                 in (Map.delete bid uses, recordSelf bid uses sub, next2)

      CPiRuntimeM _ _ _ _ _ _ _ _ _ dom cod ->
        let (uDom, sDom, next1) = count [] depth scopes UseErased dom next
            (uCod, sCod, next2) = count [] (depth + 1) ((depth, Nothing, False, Nothing) : scopes) UseErased cod next1
         in (addUses uDom uCod, Map.union sDom sCod, next2)

      CLetRuntimeM _ q _ runtimeErasure ty rhs b ->
        let tyV = evalTypeAt ctx depth ty
            erased = runtimeErasedLocalAt ctx depth q runtimeErasure tyV
            rhsTele = paramConvTelescopeFromValueAt ctx depth tyV
         in if erased
              then count [] (depth + 1) ((depth, Nothing, False, Just tyV) : scopes) UseConsumes b next
              else
                let (bid, next1) = fresh next
                    (uB, sB, next2) = count [] (depth + 1) ((depth, Just bid, False, Just tyV) : scopes) UseConsumes b next1
                    body' = Map.delete bid uB
                    (uRhs, sRhs, next3) = count rhsTele depth scopes UseConsumes rhs next2
                 in (addUses uRhs body', recordSelf bid uB (Map.union sRhs sB), next3)

      CLetRecRuntimeM _ q _ runtimeErasure ty rhs b ->
        let tyV = evalTypeAt ctx depth ty
            erased = runtimeErasedLocalAt ctx depth q runtimeErasure tyV
            rhsTele = paramConvTelescopeFromValueAt ctx (depth + 1) tyV
         in if erased
              then count [] (depth + 1) ((depth, Nothing, False, Just tyV) : scopes) UseConsumes b next
              else
                let (bid, next1) = fresh next
                    scopes' = (depth, Just bid, False, Just tyV) : scopes
                    (uB, sB, next2) = count [] (depth + 1) scopes' UseConsumes b next1
                    (uRhs, sRhs, next3) = count rhsTele (depth + 1) scopes' UseConsumes rhs next2
                    combined = addUses uRhs uB
                 in (Map.delete bid combined, recordSelf bid combined (Map.union sRhs sB), next3)

      CLetPolyRuntimeM _ q _ _ runtimeErasure ty rhs b ->
        let tyV = evalTypeAt ctx depth ty
            erased = runtimeErasedLocalAt ctx depth q runtimeErasure tyV
            rhsTele = paramConvTelescopeFromValueAt ctx depth tyV
         in if erased
              then count [] (depth + 1) ((depth, Nothing, False, Just tyV) : scopes) UseConsumes b next
              else
                let (bid, next1) = fresh next
                    (uB, sB, next2) = count [] (depth + 1) ((depth, Just bid, False, Just tyV) : scopes) UseConsumes b next1
                    body' = Map.delete bid uB
                    (uRhs, sRhs, next3) = count rhsTele depth scopes UseConsumes rhs next2
                 in (addUses uRhs body', recordSelf bid uB (Map.union sRhs sB), next3)

      CLetRecPolyRuntimeM _ q _ _ runtimeErasure ty rhs b ->
        let tyV = evalTypeAt ctx depth ty
            erased = runtimeErasedLocalAt ctx depth q runtimeErasure tyV
            rhsTele = paramConvTelescopeFromValueAt ctx (depth + 1) tyV
         in if erased
              then count [] (depth + 1) ((depth, Nothing, False, Just tyV) : scopes) UseConsumes b next
              else
                let (bid, next1) = fresh next
                    scopes' = (depth, Just bid, False, Just tyV) : scopes
                    (uB, sB, next2) = count [] (depth + 1) scopes' UseConsumes b next1
                    (uRhs, sRhs, next3) = count rhsTele (depth + 1) scopes' UseConsumes rhs next2
                    combined = addUses uRhs uB
                 in (Map.delete bid combined, recordSelf bid combined (Map.union sRhs sB), next3)

      CLetRecGroupM _ definitions b ->
        let groupDepth = depth + length definitions
            allocate [] current = ([], current)
            allocate (definition : rest) current =
              let tyV = evalTypeAt ctx depth (clrdType definition)
                  erased = runtimeErasedLocalAt ctx depth (clrdQuantity definition) (clrdRuntimeErasure definition) tyV
                  (maybeBid, current1) = if erased then (Nothing, current) else let (bid, next') = fresh current in (Just bid, next')
                  (allocatedRest, current2) = allocate rest current1
               in ((definition, maybeBid, tyV, erased) : allocatedRest, current2)
            (allocated, next1) = allocate definitions next
            groupScopes =
              reverse
                [(depth + index, maybeBid, False, Just tyV) | (index, (_, maybeBid, tyV, _)) <- zip [0 ..] allocated]
                ++ scopes
            (bodyUses, bodySub, next2) = count [] groupDepth groupScopes UseConsumes b next1
            countDefinition (uses, sub, current) (definition, _, tyV, erased) =
              let rhsTele = paramConvTelescopeFromValueAt ctx groupDepth tyV
                  (rhsUses, rhsSub, current') =
                    count rhsTele groupDepth groupScopes (if erased then UseErased else UseConsumes) (clrdRhs definition) current
               in (addUses rhsUses uses, Map.union rhsSub sub, current')
            (combined, combinedSub, next3) = foldl countDefinition (bodyUses, bodySub, next2) allocated
            binderIds = [bid | (_, Just bid, _, _) <- allocated]
            external = foldr Map.delete combined binderIds
            recorded = foldr (\bid sub -> recordSelf bid combined sub) combinedSub binderIds
         in (external, recorded, next3)

      CMatch s ann _resultAnn alts ->
        let (uAlts, sAlts, next1) = countAlts depth scopes ann alts next
            (uS, sS, next2) = count [] depth scopes UseConsumes s next1
         in (addUses uS uAlts, Map.union sS sAlts, next2)

      CIf c t e ->
        let (uT, sT, next1) = count [] depth scopes UseConsumes t next
            (uE, sE, next2) = count [] depth scopes UseConsumes e next1
            (uC, sC, next3) = count [] depth scopes UseConsumes c next2
         in (addUses uC (joinUses uT uE), Map.unions [sC, sT, sE], next3)

      CApp {} ->
        let (hd, args) = spineOfTerm term
            argConsumes = callArgConsumes ctx depth (countScopeTypeAt scopes) hd args
            argTerms = [(a, auc) | ((_, a), auc) <- zip args argConsumes]
            (uArgs, sArgs, nextArgs) = countSeqR depth scopes argTerms next
            (uHead, sHead, nextHead) = count [] depth scopes UseConsumes hd nextArgs
         in (addUses uHead uArgs, Map.union sHead sArgs, nextHead)
      CCtorI _ _ _ arguments ->
        countSeqR depth scopes
          [ (caTerm argument, if caPayload argument then UseConsumes else UseErased)
          | argument <- arguments
          ]
          next
      CRecordTQ fs -> countSeqR depth scopes [(rfType field, UseErased) | field <- fs] next
      CRecordV fs -> countSeqR depth scopes [(x, UseConsumes) | x <- map snd fs] next
      CVariantT ms -> countSeqR depth scopes [(x, UseErased) | x <- ms] next
      CQuote _ slots -> countSeqR depth scopes [(x, UseErased) | x <- slots] next

      CProjM _ e _ -> count [] depth scopes UseReads e next
      CProjAtM _ e _ _ -> count [] depth scopes UseReads e next
      CInject _ e -> count [] depth scopes UseConsumes e next
      CSealE _ e -> count [] depth scopes UseConsumes e next
      CSigT _ e -> count [] depth scopes UseErased e next
      CThunkE e _ -> count [] depth scopes UseConsumes e next
      CLazyE e _ -> count [] depth scopes UseConsumes e next
      CForceE e _ -> count [] depth scopes UseConsumes e next

      CGlobal _ _ -> (Map.empty, Map.empty, next)
      CSort _ -> (Map.empty, Map.empty, next)
      CLevel _ -> (Map.empty, Map.empty, next)
      CLit _ -> (Map.empty, Map.empty, next)
      CMeta _ -> (Map.empty, Map.empty, next)
      CDo _ items -> countDoItems depth scopes items next

    recordSelf bid uses sub =
      Map.insert bid (Map.findWithDefault (0, Just 0) bid uses) sub

    countSeqR depth scopes children next0 =
      foldr
        ( \(t, uc) (uses, subs, nextIn) ->
            let (u, s, nextOut) = count [] depth scopes uc t nextIn
             in (addUses u uses, Map.union s subs, nextOut)
        )
        (Map.empty, Map.empty, next0)
        children

    bindPat d pat borrowed next0 =
      let n = patBindersC pat
       in go 0 next0 [] n
      where
        go k nextAcc rev n
          | k >= n = (n, reverse rev, nextAcc)
          | otherwise =
              let (bid, next1) = fresh nextAcc
                  sc = (d + n - 1 - k, Just bid, borrowed, Nothing)
               in go (k + 1) next1 (sc : rev) n

    recordPatSelf uses sub scopes =
      foldr
        (\(_, mbid, _, _) m -> maybe m (\bid -> Map.insert bid (Map.findWithDefault (0, Just 0) bid uses) m) mbid)
        sub
        scopes

    countDoItems depth scopes items next0 = go depth scopes items next0
      where
        go _ _ [] next = (Map.empty, Map.empty, next)
        go d scs (item : rest) next =
          let bindThen pat term =
                let (n, newScopes, next1) = bindPat d pat False next
                    (uRest, sRest, next2) = go (d + n) (newScopes ++ scs) rest next1
                    (uTerm, sTerm, next3) = count [] d scs UseConsumes term next2
                    uLocal = addUses uTerm uRest
                    bids = [bid | (_, Just bid, _, _) <- newScopes]
                    outward = foldr Map.delete uLocal bids
                 in (outward, recordPatSelf uRest (Map.union sTerm sRest) newScopes, next3)
              restThen term =
                let (uRest, sRest, next1) = go d scs rest next
                    (uTerm, sTerm, next2) = count [] d scs UseConsumes term next1
                 in (addUses uTerm uRest, Map.union sTerm sRest, next2)
           in case item of
                KBind _ pat t _ -> bindThen pat t
                KLet _ pat t -> bindThen pat t
                KLetQ pat t mElse ->
                  let (n, newScopes, next1) = bindPat d pat False next
                      (uRest, sRest, next2) = go (d + n) (newScopes ++ scs) rest next1
                      bids = [bid | (_, Just bid, _, _) <- newScopes]
                      uSuccess = foldr Map.delete uRest bids
                      sSuccess = recordPatSelf uRest sRest newScopes
                      (uElse, sElse, next3) = case mElse of
                        Nothing -> (Map.empty, Map.empty, next2)
                        Just (rp, fe) ->
                          let (rn, rScopes, nextR) = bindPat d rp False next2
                              (uFe, sFe, nextFe) = count [] (d + rn) (rScopes ++ scs) UseConsumes fe nextR
                              rbids = [bid | (_, Just bid, _, _) <- rScopes]
                           in (foldr Map.delete uFe rbids, recordPatSelf uFe sFe rScopes, nextFe)
                      (uScrut, sScrut, next4) = count [] d scs UseConsumes t next3
                   in (addUses uScrut (joinUses uSuccess uElse), Map.unions [sScrut, sSuccess, sElse], next4)
                KExpr t -> restThen t
                KVarItem _ _ actT _ ->
                  let (bid, next1) = fresh next
                      sc = (d, Just bid, False, Nothing)
                      (uRest, sRest, next2) = go (d + 1) (sc : scs) rest next1
                      (uAct, sAct, next3) = count [] d scs UseConsumes actT next2
                      uLocal = addUses uAct uRest
                   in (Map.delete bid uLocal, recordSelf bid uRest (Map.union sAct sRest), next3)
                KAssign _ _ _ actT _ -> restThen actT
                KReturn t -> count [] d scs UseConsumes t next
                KBreak _ -> (Map.empty, Map.empty, next)
                KContinue _ -> (Map.empty, Map.empty, next)
                KWhile _ cond loopBody mElse ->
                  let (uRest, sRest, next1) = go d scs rest next
                      (uCond, sCond, next2) = countKCond d scs cond next1
                      (uBody, sBody, next3) = countDoItems d scs loopBody next2
                      loopUses = Map.map (\_ -> (0, Nothing)) (addUses uCond uBody)
                      (uElse, sElse, next4) = maybe (Map.empty, Map.empty, next3) (\els -> countDoItems d scs els next3) mElse
                   in (addUses uRest (joinUses loopUses uElse), Map.unions [sRest, sCond, sBody, sElse], next4)
                KFor _ pat src loopBody mElse ->
                  let (uRest, sRest, next1) = go d scs rest next
                      (n, newScopes, next2) = bindPat d pat False next1
                      (uSrc, sSrc, next3) = count [] d scs UseConsumes src next2
                      (uBody, sBody, next4) = countDoItems (d + n) (newScopes ++ scs) loopBody next3
                      bids = [bid | (_, Just bid, _, _) <- newScopes]
                      bodyOut = foldr Map.delete uBody bids
                      loopUses = Map.map (\_ -> (0, Nothing)) bodyOut
                      sBody' = recordPatSelf uBody sBody newScopes
                      (uElse, sElse, next5) = maybe (Map.empty, Map.empty, next4) (\els -> countDoItems d scs els next4) mElse
                   in (addUses uSrc (addUses uRest (joinUses loopUses uElse)), Map.unions [sRest, sSrc, sBody', sElse], next5)
                KIf alts mElse ->
                  let (uRest, sRest, next1) = go d scs rest next
                      (uIf, sIf, next2) = countKIf d scs alts mElse next1
                   in (addUses uIf uRest, Map.union sRest sIf, next2)
                KDefer _ t -> restThen t
                KUsing pat acquireT releaseT ->
                  let (n, newScopes, next1) = bindPat d pat True next
                      (uRest, sRest, next2) = go (d + n) (newScopes ++ scs) rest next1
                      bids = [bid | (_, Just bid, _, _) <- newScopes]
                      uRestOut = foldr Map.delete uRest bids
                      sRest' = recordPatSelf uRest sRest newScopes
                      (uRelease, sRelease, next3) = count [] d scs UseConsumes releaseT next2
                      (uAcquire, sAcquire, next4) = count [] d scs UseConsumes acquireT next3
                   in (addUses uAcquire (addUses uRelease uRestOut), Map.unions [sRest', sRelease, sAcquire], next4)
                KSubDo _ subItems ->
                  let (uRest, sRest, next1) = go d scs rest next
                      (uSub, sSub, next2) = countDoItems d scs subItems next1
                   in (addUses uSub uRest, Map.union sSub sRest, next2)

    countKCond depth scopes cond next = case cond of
      KCondPure t -> count [] depth scopes UseConsumes t next
      KCondAction t -> count [] depth scopes UseConsumes t next

    countKIf depth scopes alts mElse next = go alts next
      where
        go [] nextIn = case mElse of
          Nothing -> (Map.empty, Map.empty, nextIn)
          Just els -> countDoItems depth scopes els nextIn
        go ((cond, armBody) : more) nextIn =
          let (uBody, sBody, next1) = countDoItems depth scopes armBody nextIn
              (uMore, sMore, next2) = go more next1
              (uCond, sCond, next3) = count [] depth scopes UseConsumes cond next2
           in (addUses uCond (joinUses uBody uMore), Map.unions [sCond, sBody, sMore], next3)

    countAlts _depth _scopes _mScrutTy [] next = (Map.empty, Map.empty, next)
    countAlts depth scopes mScrutTy (alt : rest) next =
      let (uRest, sRest, next1) = countAlts depth scopes mScrutTy rest next
          (uAlt, sAlt, next2) = countAlt depth scopes mScrutTy alt next1
       in (joinUses uAlt uRest, Map.union sAlt sRest, next2)

    countAlt depth scopes mScrutTy (CaseAlt pat mguard b) next =
      let n = patBindersC pat
          slotTypes = reverse (patBindingTypes ctx ctorTypes depth pat (evalTypeAt ctx depth <$> mScrutTy))
          (newScopes, next1) = bindCountPattern depth slotTypes next n
          depth' = depth + n
          scopes' = newScopes ++ scopes
          (uB, sB, next2) = count [] depth' scopes' UseConsumes b next1
          (uArm, sArm, next3) = case mguard of
            Nothing -> (uB, sB, next2)
            Just gd ->
              let (uG, sG, nextG) = count [] depth' scopes' UseConsumes gd next2
               in (addUses uG uB, Map.union sG sB, nextG)
          bids = [bid | (_, Just bid, _, _) <- newScopes]
          selfRecorded = foldr (\bid m -> Map.insert bid (Map.findWithDefault (0, Just 0) bid uArm) m) sArm bids
          outward = foldr Map.delete uArm bids
       in (outward, selfRecorded, next3)

    bindCountPattern depth slotTypes next0 n =
      go 0 next0 []
      where
        go k nextAcc rev
          | k >= n = (reverse rev, nextAcc)
          | otherwise =
              let (bid, next1) = fresh nextAcc
                  sc = (depth + n - 1 - k, Just bid, False, indexMaybe k slotTypes >>= id)
               in go (k + 1) next1 (sc : rev)

    resolve lvl = go
      where
        go [] = Nothing
        go ((l, mbid, brw, _mTy) : rest)
          | l == lvl = Just (mbid, brw)
          | otherwise = go rest

    countScopeTypeAt scopes lvl = go scopes
      where
        go [] = Nothing
        go ((l, _mbid, _brw, mTy) : rest)
          | l == lvl = mTy
          | otherwise = go rest

-- | Add two per-binder usage maps componentwise (SEQUENTIAL composition:
-- a binder used in both subterms is used the sum of the two counts on a path that
-- runs through both). A binder absent on one side counts as @(0,0)@ there.
addUses
  :: Map BinderId (Int, Maybe Int)
  -> Map BinderId (Int, Maybe Int)
  -> Map BinderId (Int, Maybe Int)
addUses = Map.unionWith addInterval
  where
    addInterval (lo1, hi1) (lo2, hi2) = (lo1 + lo2, addHi hi1 hi2)
    addHi (Just a) (Just b) = Just (a + b)
    addHi _ _ = Nothing

-- | Join two per-binder usage maps (a BRANCH: each is its own completion
-- path, so a binder's interval is the min lower bound and max upper bound across
-- the arms). A binder used in only one arm is dropped (count @0@) on the other,
-- so its lower bound becomes @0@ — exactly the @[0,1]@-style \"used on some paths\"
-- refinement.
joinUses
  :: Map BinderId (Int, Maybe Int)
  -> Map BinderId (Int, Maybe Int)
  -> Map BinderId (Int, Maybe Int)
joinUses a b =
  Map.unionWith joinInterval (fillZero a b) (fillZero b a)
  where
    -- ensure every key present on either side appears on both, defaulting a
    -- missing arm to @(0, Just 0)@ (the binder is unused on that path).
    fillZero x other = Map.union x (Map.map (const (0, Just 0)) other)
    joinInterval (lo1, hi1) (lo2, hi2) = (min lo1 lo2, maxHi hi1 hi2)
    maxHi Nothing _ = Nothing
    maxHi _ Nothing = Nothing
    maxHi (Just x) (Just y) = Just (max x y)

-- ── S1.2 cross-check ─────────────────────────────────────────────────

-- | Validate one definition's 'OwnInfo' against the declared quantities already
-- on its Core binder nodes (PERCEUS-S1-PLAN (f) item 2). Returns a list of
-- human-readable mismatch descriptions; the empty list means the analysis is
-- consistent with the declared quantities.
--
-- The invariants checked (the recorded last-use decisions must agree with the
-- declared @Q@\/borrow — a violation means the analysis is WRONG, not that the
-- program is ill-typed):
--
--   * a binder with @boDeclQ == 1@ (linear) has at least one CONSUMING
--     'LastUse' and NO consuming 'NonLast' occurrence;
--   * a @boBorrowed@ binder has NO 'LastUse' and no 'NonLast' — all its uses
--     are 'Borrowed'.
--
-- The binder↔occurrence association the per-binder invariants need is the de
-- Bruijn resolution, which is only available with the body in hand, so this
-- re-runs the same liveness walk 'annotateOwnership' runs ('analyzeBodyFull')
-- — the SINGLE traversal that is the source of truth — to recover it. It is
-- therefore equivalent to 'crossCheckBodies' restricted to one definition.
--
-- IMPORTANT: this is meaningful only on WELL-TYPED definitions. An ill-typed
-- program (e.g. a conformance fixture that intentionally over- or under-uses a
-- linear binding) genuinely violates "linear ⇒ exactly one last use" — and the
-- analysis correctly reports that violation in its classification. So this
-- check is run as a test-suite gate over a well-typed corpus (the whole prelude
-- + std library + crafted fixtures), NOT as a crash inside 'annotateOwnership'
-- on every compilation (which would fire on the intentionally-ill-typed
-- fixtures). See 'crossCheckBodies'.
crossCheckOwnInfo
  :: EvalCtx
  -> OwnershipCtorTypes
  -> GName
  -> Term
  -> OwnInfo
  -> [String]
crossCheckOwnInfo ctx ctorTypes owner body oi =
  let (oiWalk, assoc, consumingAssoc) = analyzeBodyFull ctx ctorTypes (paramTelescope ctx owner) owner body
   in checkAll owner body oi assoc consumingAssoc
        ++ checkConsumeTables owner oi oiWalk

-- | Run the cross-check over a whole set of WELL-TYPED bodies and their
-- 'OwnInfo'. Returns a flat list of mismatch messages (empty ⇒ clean). This is
-- the test-suite gate: a non-empty result fails the build, so a wrong last-use
-- analysis (S1.1) or an unsound refinement (S1.4) is caught rather than allowed
-- to drift.
--
-- The binder↔occurrence association the per-binder S1.1 invariants need comes
-- from the same single walk 'annotateOwnership' runs ('analyzeBodyFull'), so the
-- check validates EXACTLY the classification that was recorded — there is no
-- second, drift-prone traversal.
--
-- It ALSO validates the S1.4 §3a refinement: every @boRefined@ is @<=@ its
-- @boDeclQ@ as an interval (refinement only ever TIGHTENS, never widens — the
-- source-contract guarantee). A violation is an internal-invariant error,
-- exactly like an S1.1 mismatch.
--
-- == No export-boundary assertion (the corrected whole-program-static model)
--
-- The earlier gate ALSO asserted @boRefined@ was 'Nothing' at every
-- export\/re-export boundary parameter, on the theory that refining an exported
-- signature was unsound. That was premature: the §3a refinement is whole-program
-- SOUND (the analysis sees all uses), and its genuine gating boundary is the
-- DYNAMIC-LINK \/ separately-compiled interface, which is EMPTY in the current
-- whole-program-static compile. So exported and re-exported binders are now
-- legitimately refined, and the boundary assertion (with its independent
-- @csModuleExports@\/@csReExports@ boundary recomputation) is removed. The
-- tighten-only invariant alone is the soundness gate. Re-add a boundary
-- assertion when a real separate-compilation interface lands (see the §3a
-- section note above).
crossCheckBodies
  :: EvalCtx
  -> Map GName Term
  -> Map GName Term
  -> Map GName OwnInfo
  -> [String]
crossCheckBodies ctx = crossCheckBodiesWithUniverses ctx . monomorphicCtorTypes

crossCheckBodiesWithUniverses
  :: EvalCtx
  -> OwnershipCtorTypes
  -> Map GName Term
  -> Map GName OwnInfo
  -> [String]
crossCheckBodiesWithUniverses ctx ctorTypes bodies own =
  concatMap one (Map.toList bodies)
  where
    one (g, body) =
      let (oiWalk, assoc, consumingAssoc) = analyzeBodyFull ctx ctorTypes (paramTelescope ctx g) g body
       in case Map.lookup g own of
            Nothing -> [T.unpack (gKey g) <> ": missing OwnInfo entry"]
            Just oi ->
              checkAll g body oi assoc consumingAssoc
                ++ checkConsumeTables g oi oiWalk

-- | Check the declared-quantity invariants (S1.1) AND the §3a refinement
-- invariant (S1.4 — tighten-only) for one body, given the binder→kinds
-- association.
checkAll :: GName -> Term -> OwnInfo -> Map BinderId [UseKind] -> Map BinderId [UseKind] -> [String]
checkAll g _body oi perBinder perConsumingBinder =
  concatMap checkOne (Map.toList (oiBinders oi))
  where
    checkOne (bid, bo) =
      let ks = Map.findWithDefault [] bid perBinder
          cks = Map.findWithDefault [] bid perConsumingBinder
       in checkKinds g bid bo ks cks
            ++ checkRefined g bid bo

-- | Validate that the supplied 'OwnInfo' carries the same backend-visible
-- classification maps as the freshly-recomputed ownership walk. The
-- binder-quantity checks intentionally recompute associations from the body,
-- but the dump and backend consume the stored maps, so drift here must be
-- reported explicitly.
checkConsumeTables :: GName -> OwnInfo -> OwnInfo -> [String]
checkConsumeTables g supplied fresh =
  compareMap "oiBinders" (Map.map unrefined (oiBinders supplied)) (Map.map unrefined (oiBinders fresh))
    ++ compareMap "oiUses" (oiUses supplied) (oiUses fresh)
    ++ compareMap "oiUseConsumes" (oiUseConsumes supplied) (oiUseConsumes fresh)
    ++ compareMap "oiBinderUses" (oiBinderUses supplied) (oiBinderUses fresh)
    ++ compareMap "oiBinderConsumingUses" (oiBinderConsumingUses supplied) (oiBinderConsumingUses fresh)
    ++ compareMap "oiBranchDropSites" (oiBranchDropSites supplied) (oiBranchDropSites fresh)
  where
    unrefined bo = bo {boRefined = Nothing}

    compareMap label got want =
      [ T.unpack (gKey g) <> ": " <> label <> " differs from ownership walk"
          <> " (stored=" <> show (Map.size got)
          <> ", fresh=" <> show (Map.size want) <> ")"
      | got /= want
      ]

-- | The S1.4 §3a refinement invariant for one binder: @boRefined@ only ever
-- TIGHTENS — its interval must be @<=@ (a sub-interval of) the declared
-- @boDeclQ@'s interval. A refinement that WIDENED the declared bound would let
-- S2 drop\/reuse a value the contract says is shared (a use-after-free), so a
-- widen is an internal-invariant error.
--
-- There is NO export-boundary assertion: the §3a refinement is whole-program
-- sound, and its genuine gating boundary (the dynamic-link \/ separately-
-- compiled interface) is EMPTY in the current whole-program-static compile, so
-- exported and re-exported binders are legitimately refined. See the §3a section
-- note for the TODO to re-add a boundary check when separate compilation lands.
checkRefined :: GName -> BinderId -> BinderOwn -> [String]
checkRefined g bid bo =
  case boRefined bo of
    Nothing -> []
    Just refined ->
      [ msg
          ( "refinement " <> showI refined <> " WIDENS the declared "
              <> showI (declInterval (boDeclQ bo)) <> " (must only tighten)"
          )
      | not (subInterval refined (declInterval (boDeclQ bo)))
      ]
  where
    msg s = T.unpack (gKey g) <> " @" <> renderBinderIdString bid <> ": " <> s
    showI (lo, Just hi) = "[" <> show lo <> "," <> show hi <> "]"
    showI (lo, Nothing) = "[" <> show lo <> ",ω]"

-- | The per-binder declared-quantity invariant (§12.2.5\/§12.2.6).
--
-- The classification multiset is read completion-path-awarely by exploiting a structural
-- property of the backward walk: within one sequential completion path it
-- threads @liveOut@ so an upstream occurrence always sees a downstream one and
-- is therefore 'NonLast'. Hence two 'LastUse's for the same binder can ONLY
-- arise on DISTINCT branches (e.g. a linear @state@ consumed once in each
-- match arm), never twice on one path. Therefore:
--
--   * a __linear__ (@1@) binder is well-classified iff it has NO consuming
--     'NonLast' (every consuming occurrence is the last on its path) and at
--     least one consuming 'LastUse' (it is consumed — §12.2.5 forbids dropping
--     it on any path). Multiple consuming 'LastUse's are fine: one per branch.
--     A consuming 'NonLast' means the analysis put a non-final consuming use
--     where the linear contract guarantees a single per-path use;
--   * a __borrowed__ (@&@) binder has NO consuming use at all — every use is
--     'Borrowed'.
checkKinds :: GName -> BinderId -> BinderOwn -> [UseKind] -> [UseKind] -> [String]
checkKinds g bid bo ks cks
  | boBorrowed bo =
      [ msg ("borrowed binder has a consuming " <> show k <> " use")
      | k <- ks, k == LastUse || k == NonLast
      ]
  | boDeclQ bo == Q1 =
      let lasts = length (filter (== LastUse) cks)
          nonlasts = length (filter (== NonLast) cks)
       in [ msg
              ( "linear binder has " <> show lasts <> " LastUse / "
                  <> show nonlasts <> " NonLast (want ≥1 LastUse, 0 NonLast — "
                  <> "one consuming use per completion path)"
              )
          | nonlasts /= 0 || lasts < 1
          ]
  | otherwise = []
  where
    msg s =
      T.unpack (gKey g) <> " @" <> renderBinderIdString bid <> ": " <> s

-- ── S1.5 call-site classification assert ─────────────────────────────
--
-- The S1.5 deliverable (PERCEUS-S1-PLAN (d)\/(e)) is the OBSERVE-ONLY debug
-- assert that every call site CAN classify each of its arguments under the
-- owned\/borrowed convention 'Kappa.Backend.Repr.argConvSelectGlobal' derives
-- from the callee telescope plus the audited S2.3c primitive override — the
-- exact lookup the S2 dup\/drop pass performs at each
-- 'CApp'. NO codegen changes; this only checks that the data S2 will need is
-- recoverable at every statically-resolvable call site.
--
-- \"Statically resolvable\" = a call spine whose head is a known GLOBAL
-- ('CGlob') — the case S2 resolves via the callee 'CPi' telescope (PERCEUS-RC-
-- DESIGN §3 / PERCEUS-S1-PLAN (d): \"at each 'CApp', resolve the callee 'CPi'
-- telescope (already done by 'repSelect')\"). For such a spine,
-- 'argConvSelectGlobal' MUST SUCCEED — the telescope is walkable and any
-- primitive override has the right arity — so S2 has a
-- per-parameter owned\/borrowed convention list to zip against the spine. A
-- non-global head (a local variable\/lambda\/partial application) carries no
-- statically-known global telescope here and is not asserted — S2 classifies it
-- from the local binder's type, outside this side-table.
--
-- NOTE on what is NOT asserted: the assert deliberately does NOT compare the
-- per-arg convention COUNT against the spine's explicit-argument count. The two
-- do not align position-for-position at the Core level — an erased ('Q0') or
-- type-valued argument (e.g. a trait dictionary's @Type@ index, or a proof) is
-- supplied EXPLICITLY on the spine but is 'Q0'\/implicit in the telescope, so
-- 'argConvSelectGlobal' (correctly) skips it. Matching spine arguments to telescope
-- parameters — skipping the erased ones — is the lockstep zip S2 itself performs;
-- the S1.5 deliverable is only that the convention list EXISTS at every such site.

-- | Walk a whole corpus and return every call-site classification finding (empty
-- ⇒ every statically-resolvable call site can classify each argument). The
-- test-suite\/lint gate for S1.5.
argConvBodies :: EvalCtx -> Map GName Term -> [String]
argConvBodies ctx = concatMap (\(g, body) -> argConvFindings ctx g body) . Map.toList

-- | Call-site classification findings for one body: for every application spine
-- with a 'CGlob' head, check 'argConvSelectGlobal' classifies each supplied explicit
-- argument. Returns a list of human-readable findings (empty ⇒ clean).
argConvFindings :: EvalCtx -> GName -> Term -> [String]
argConvFindings ctx owner = goTerm
  where
    -- A bespoke spine-aware walk: at a 'CApp' we decompose the FULL spine once
    -- ('spineOfTerm') so an intermediate spine 'CApp' is not re-checked on a
    -- partial argument list, then recurse only into the arguments (and a
    -- non-global head), never back into the spine's inner 'CApp's.
    goTerm t = case t of
      CUniverseLift _ _ _ inner -> goTerm inner
      CSchemaLift _ _ _ _ _ _ _ _ inner -> goTerm inner
      CArithmeticProof _ -> []
      CApp {} ->
        let (hd, args) = spineOfTerm t
            here = case hd of
              CGlobal g _ -> checkCall g args
              _ -> goTerm hd
         in here ++ concatMap (goTerm . snd) args
      CLamM _ _ _ _ b -> goTerm b
      CPiRuntimeM _ _ _ _ _ _ _ _ runtimeErasure a b ->
        concatMap goTerm (a : b : toList runtimeErasure)
      CCtorI _ _ _ arguments ->
        concatMap (goTerm . caTerm) [argument | argument <- arguments, caPayload argument]
      CMatch s _ _ alts ->
        goTerm s ++ concatMap (\(CaseAlt _ gd b) -> maybe [] goTerm gd ++ goTerm b) alts
      CRecordTQ fs -> concatMap (\field -> concatMap goTerm (rfType field : toList (rfRuntimeErasure field))) fs
      CRecordV fs -> concatMap (goTerm . snd) fs
      CProjM _ e _ -> goTerm e
      CProjAtM _ e _ _ -> goTerm e
      CVariantT ms -> concatMap goTerm ms
      CInject _ e -> goTerm e
      CLetRuntimeM _ _ _ runtimeErasure ty rhs b -> concatMap goTerm (ty : rhs : b : toList runtimeErasure)
      CLetRecRuntimeM _ _ _ runtimeErasure ty rhs b -> concatMap goTerm (ty : rhs : b : toList runtimeErasure)
      CLetPolyRuntimeM _ _ _ _ runtimeErasure ty rhs b -> concatMap goTerm (ty : rhs : b : toList runtimeErasure)
      CLetRecPolyRuntimeM _ _ _ _ runtimeErasure ty rhs b -> concatMap goTerm (ty : rhs : b : toList runtimeErasure)
      CLetRecGroupM _ definitions b ->
        concatMap
          (\definition -> concatMap goTerm (clrdType definition : clrdRhs definition : toList (clrdRuntimeErasure definition)))
          definitions
          ++ goTerm b
      CSealE _ e -> goTerm e
      CSigT _ e -> goTerm e
      CThunkE e _ -> goTerm e
      CLazyE e _ -> goTerm e
      CForceE e _ -> goTerm e
      CIf c th el -> goTerm c ++ goTerm th ++ goTerm el
      CQuote _ slots -> concatMap goTerm slots
      -- leaves
      CVar _ -> []
      CLocal _ _ -> []
      CGlobal _ _ -> []
      CSort _ -> []
      CLevel _ -> []
      CLit _ -> []
      CMeta _ -> []
      CDo _ items -> concatMap goKItem items

    goKItem = \case
      KBind _ _ t _ -> goTerm t
      KLet _ _ t -> goTerm t
      KLetQ _ t mElse -> goTerm t ++ maybe [] (goTerm . snd) mElse
      KExpr t -> goTerm t
      KVarItem _ _ actT _ -> goTerm actT
      KAssign _ _ _ actT _ -> goTerm actT
      KReturn t -> goTerm t
      KBreak _ -> []
      KContinue _ -> []
      KWhile _ cond body mElse -> goKCond cond ++ concatMap goKItem body ++ maybe [] (concatMap goKItem) mElse
      KFor _ _ src body mElse -> goTerm src ++ concatMap goKItem body ++ maybe [] (concatMap goKItem) mElse
      KIf alts mElse -> concatMap (\(c, body) -> goTerm c ++ concatMap goKItem body) alts ++ maybe [] (concatMap goKItem) mElse
      KDefer _ t -> goTerm t
      KUsing _ acquire release -> goTerm acquire ++ goTerm release
      KSubDo _ items -> concatMap goKItem items

    goKCond = \case
      KCondPure t -> goTerm t
      KCondAction t -> goTerm t

    -- Assert the callee telescope/primitive override is WALKABLE so S2 has a
    -- per-parameter convention list. Only fired when the spine actually supplies
    -- an explicit argument (a bare 'CGlob' with no args is not a consuming call
    -- site).
    checkCall g args =
      case argConvGlobalType ctx g of
        -- an unknown global (e.g. a runtime prim with no recorded type) cannot be
        -- classified here; that is not a failure of the accessor — skip it.
        Nothing -> []
        Just _ ->
          let hasExpl = not (null [() | (Expl, _) <- args])
              walkable = case argConvSelectGlobal ctx g of
                Just _ -> True
                Nothing -> False
           in [ T.unpack (gKey owner) <> " → " <> T.unpack (gKey g)
                  <> ": callee telescope/primitive convention is not walkable (argConvSelectGlobal = Nothing)"
              | hasExpl
              , not walkable
              ]

-- ── Dump rendering ───────────────────────────────────────────────────

-- | Render one definition's 'OwnInfo' for the @kappa dump-ownership@ CLI
-- surface: per binder its @(declQ, refined, borrowed, droppable)@, and per
-- 'CVar' occurrence its @LastUse|NonLast|Borrowed@ classification plus whether
-- the syntactic position consumes the reference. The output is sorted by
-- owner-local ordinal so it is deterministic and diffable.
renderOwnInfo :: GName -> OwnInfo -> Text
renderOwnInfo g oi =
  T.unlines $
    [gKey g]
      ++ [ "  binder " <> renderBinderId bid
             <> " declQ=" <> renderQ (boDeclQ bo)
             <> " refined=" <> renderRefined (boRefined bo)
             <> " borrowed=" <> tshow (boBorrowed bo)
             <> " droppable=" <> tshow (boDroppable bo)
         | (bid, bo) <- sortOn (biOrdinal . fst) (Map.toList (oiBinders oi))
         ]
      ++ [ "  use " <> renderUseSite us <> " " <> renderKind k
             <> " consumes=" <> renderConsumes us
         | (us, k) <- sortOn (usOrdinal . fst) (Map.toList (oiUses oi))
         ]
      ++ [ "  drop-site " <> renderBranchSite p <> " binders=" <> T.pack (show (map biOrdinal bids))
         | (p, bids) <- sortOn fst (Map.toList (oiBranchDropSites oi))
         ]
  where
    tshow :: Show a => a -> Text
    tshow = T.pack . show
    renderQ = \case
      Q0 -> "0"
      Q1 -> "1"
      QW -> "ω"
      QLe1 -> "≤1"
      QGe1 -> "≥1"
    renderRefined = \case
      Nothing -> "—"
      Just (lo, Just hi) -> T.pack ("[" <> show lo <> "," <> show hi <> "]")
      Just (lo, Nothing) -> T.pack ("[" <> show lo <> ",ω]")
    renderKind = \case
      LastUse -> "LastUse"
      NonLast -> "NonLast"
      Borrowed -> "Borrowed"
    renderConsumes us =
      case Map.lookup us (oiUseConsumes oi) of
        Just b -> tshow b
        Nothing -> "?"

renderBinderId :: BinderId -> Text
renderBinderId = T.pack . renderBinderIdString

renderBinderIdString :: BinderId -> String
renderBinderIdString bid = "#" <> show (biOrdinal bid)

renderUseSite :: UseSite -> Text
renderUseSite us = "#" <> T.pack (show (usOrdinal us))

renderBranchSite :: BranchSite -> Text
renderBranchSite (BranchSite n) = "#" <> T.pack (show n)
