-- | Perceus RC Stage S1.1 — the ownership side-table with last-use analysis.
--
-- This module is the analysis half of the Perceus reference-counting arc
-- (see @runtime/docs/PERCEUS-RC-DESIGN.md@ §3 and @runtime/docs/PERCEUS-S1-PLAN.md@).
-- S1.0 landed the EMPTY plumbing — the type shapes, the 'annotateOwnership'
-- entry point, and the @csOwnership@\/@gsOwnership@ threading through the
-- pipeline and the native backend. __S1.1 fills in the analysis__: for every
-- top-level body it walks the elaborated, zonked Core 'Term' and populates
-- 'OwnInfo' with per-binder ownership facts ('oiBinders') and per-occurrence
-- last-use classification ('oiUses').
--
-- The ownership facts are computed during elaboration (§12.2 quantity\/borrow
-- accounting, ported here from the source-of-truth lattice in "Kappa.Usage"),
-- but they are ERASED before KBackendIR (§31.2), so they must be re-attached as
-- backend metadata rather than read off the IR. They live in a SIDE-TABLE keyed
-- by stable Core identities ('BinderId'\/'UseSite'), threaded beside the
-- existing @csCoreBodies@\/@gsSuspenders@ metadata, never as new 'Term' fields.
--
-- __Stage S1.1 is OBSERVE-ONLY.__ Like the Stage-0 'CCtor'\/'CMatch'
-- annotations, NO consumer reads the table for codegen — the later dup\/drop
-- pass (S2+) is what consumes it. So conformance fixtures and interp\/C\/LLVM
-- parity stay byte-identical; this stage only RECORDS the already-validated
-- decisions in Core coordinates. The recorded decisions are continuously
-- validated against the declared quantities by 'crossCheckOwnInfo' (S1.2,
-- gated in the test suite), so a wrong analysis fails rather than drifts.
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
--   * __Opaque @do@__ (the §18.8 do-kernel): a 'CDo' is not descended into,
--     matching the established opaque-do convention in "Kappa.CoreOps"
--     ('foldTermWithDepth'). Binders introduced inside a do-block are executed
--     structurally by a separate lowering path; S1.1 records no ownership for
--     them. Sound and conservative — the backend simply gets no side-table
--     hint there.
--
-- == R1 — de-Bruijn key stability (the highest risk; see PERCEUS-S1-PLAN (e))
--
-- The side-table keys are STRUCTURAL PATHS ('biPath'\/'usPath'): the list of
-- child-positions taken from the body root down to the node, NOT raw de Bruijn
-- indices. A path is invariant under the index renumbering a de Bruijn walk
-- performs, and — crucially — it is invariant under the one post-zonk rewrite
-- the backend applies before lowering, @eraseQ0Args@ (@C.hs@). That rewrite
-- ONLY replaces ARGUMENT subterms at erased global-application spine positions
-- with a @CSort 0@ placeholder; it removes NO binder ('CLam'\/'CLet'\/match
-- arm) and shifts NO de Bruijn index. Every binder node and every surviving
-- 'CVar' occurrence keeps its exact structural path. So choice (a) holds: the
-- keys are robust to the shift, with no re-keying required by the backend. The
-- only side-table entries that could name an erased argument are 'UseSite's for
-- 'CVar's that sit INSIDE such an argument; those occurrences are dropped by
-- the rewrite, but their key simply goes unconsulted (a stale key the backend
-- never looks up, never a misattributed one). The 'crossCheckOwnInfo'
-- regression includes a body with a 'Q0' (erased) binder bound before a runtime
-- binder, proving the runtime binder's key is unaffected by the erased one.
module Kappa.Ownership
  ( -- * Stable Core identities (side-table keys)
    BinderId (..)
  , UseSite (..)
    -- * Use classification
  , UseKind (..)
    -- * Per-binder ownership facts
  , BinderOwn (..)
    -- * The per-definition side-table
  , OwnInfo (..)
  , emptyOwnInfo
    -- * The annotation pass
  , annotateOwnership
    -- * S1.4 §3a whole-program usage refinement
  , refineOwnership
    -- * S1.2 cross-check against the declared quantities
  , crossCheckOwnInfo
  , crossCheckBodies
    -- * S1.5 backend owned/borrowed accessor (call-site classification assert)
  , argConvFindings
  , argConvBodies
    -- * Dump rendering (the @dump-ownership@ CLI surface)
  , renderOwnInfo
  ) where

import Data.List (sortOn)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T

import Kappa.Backend.Repr (argConvSelect)
import Kappa.Core
  ( CaseAlt (..)
  , GName (..)
  , Icit (..)
  , Q (..)
  , Term (..)
  , gKey
  )
import Kappa.CoreOps (patBindersC, spineOfTerm)
import Kappa.Eval (EvalCtx (..), GlobalDef (..), Globals (..), quote)

-- | A stable identity for a binder within a definition's elaborated Core.
--
-- Core is de Bruijn /indexed/ (a 'Kappa.Core.CVar' is an index relative to the
-- enclosing binders), so an index alone is not stable — it shifts as the term
-- is traversed under binders. The stable key is therefore the owning global
-- plus a /path/ from that global's body root down to the binder: the list of
-- child-positions taken at each 'Term' node on the way to the binder that
-- introduces the variable (e.g. into the body of a 'Kappa.Core.CLam', into the
-- right-hand side of a @let@, into a particular match arm). A path is invariant
-- under the index renumbering that de Bruijn traversal performs, so it names
-- the same binder no matter where in the walk it is observed.
data BinderId = BinderId
  { biOwner :: !GName
  -- ^ The top-level definition whose body contains the binder.
  , biPath :: ![Int]
  -- ^ Child-position path from the body root to the binding node (de
  -- Bruijn-stable; see the type doc).
  }
  deriving stock (Eq, Ord, Show)

-- | A stable identity for a /use occurrence/ of a binder — a single
-- 'Kappa.Core.CVar' site. Same scheme as 'BinderId': the owning global plus the
-- child-position path from the body root down to the 'CVar' node. Two distinct
-- occurrences of the same variable are distinct 'UseSite's (distinct paths),
-- which is exactly what last-use analysis needs (one occurrence is the last
-- use, the others are not).
data UseSite = UseSite
  { usOwner :: !GName
  -- ^ The top-level definition whose body contains the use.
  , usPath :: ![Int]
  -- ^ Child-position path from the body root to the 'CVar' occurrence.
  }
  deriving stock (Eq, Ord, Show)

-- | How a particular use occurrence consumes its binder, per Perceus's
-- owned\/borrowed parameter convention (PERCEUS-RC-DESIGN §3).
data UseKind
  = -- | The /last/ use of an owned binder on this control-flow path: the dup
    -- can be elided and the value moved\/reused (or dropped) here.
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
  }
  deriving stock (Eq, Show)

-- | The empty side-table — no binders, no uses.
emptyOwnInfo :: OwnInfo
emptyOwnInfo = OwnInfo Map.empty Map.empty

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
-- 'CLam's whose ownership convention — the declared quantity AND the borrow
-- (@&@) marker — lives on the corresponding 'CPi' of the global's /type/, not on
-- the 'CLam' (which carries no borrow field). So we read the owner's type
-- telescope (via 'paramTelescope') and zip it against the leading 'CLam's, the
-- single source of truth for the owned\/borrowed parameter convention (avoiding
-- a second side table, per PERCEUS-S1-PLAN A3).
annotateOwnership :: EvalCtx -> Map GName Term -> Map GName OwnInfo
annotateOwnership ctx =
  Map.mapWithKey (\g body -> analyzeBody (paramTelescope ctx g) g body)

-- | The leading parameter telescope of a global's declared type, as a list of
-- @(Q, borrow)@ pairs in binder order (the owned\/borrowed convention §12.3).
-- Read by zipping against the body's leading 'CLam's. An unknown global or a
-- type that does not force to a 'VPi' telescope yields @[]@ — fail-safe (the
-- binders then fall back to their 'CLam' quantity with borrow=False).
paramTelescope :: EvalCtx -> GName -> [(Q, Bool)]
paramTelescope ctx g =
  case Map.lookup g (globalsMap (ecGlobals ctx)) of
    Nothing -> []
    Just gd -> walkTy (quote ctx 0 (gdType gd))
  where
    walkTy = \case
      CPi _ q borrowed _ _ cod -> (q, borrowed) : walkTy cod
      _ -> []

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
  , accAssoc :: !(Map BinderId [UseKind])
  }

emptyAcc :: Acc
emptyAcc = Acc Map.empty Map.empty Map.empty

-- | Analyze one top-level body into its 'OwnInfo' plus the binder→kinds
-- association the cross-check consumes. @tele@ is the owner's declared parameter
-- telescope ('paramTelescope'), consumed by the body's leading 'CLam's to pick
-- up the owned\/borrowed convention from the type.
analyzeBodyFull :: [(Q, Bool)] -> GName -> Term -> (OwnInfo, Map BinderId [UseKind])
analyzeBodyFull tele owner body =
  let (acc, _live) = walk tele owner [] 0 [] body Set.empty emptyAcc
   in (OwnInfo (accBinders acc) (accUses acc), accAssoc acc)

-- | Analyze one top-level body into its 'OwnInfo'.
analyzeBody :: [(Q, Bool)] -> GName -> Term -> OwnInfo
analyzeBody tele owner body = fst (analyzeBodyFull tele owner body)

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

-- | Record one occurrence's use classification (both the per-occurrence key and
-- the per-binder association).
addUse :: UseSite -> BinderId -> UseKind -> Acc -> Acc
addUse us bid k acc =
  acc
    { accUses = Map.insert us k (accUses acc)
    , accAssoc = Map.insertWith (++) bid [k] (accAssoc acc)
    }

-- | The core backward liveness walk.
--
-- Arguments:
--
--   * @tele@  — the owner's REMAINING declared parameter telescope @(Q, borrow)@
--     ('paramTelescope'), consumed one entry per leading 'CLam' so a top-level
--     parameter picks up the owned\/borrowed convention from its 'CPi'. Empty
--     once the leading-lambda chain ends (or for a non-top-level subterm).
--   * @owner@ — the global whose body is being walked (the key prefix).
--   * @path@  — the reversed child-position path from the body root to the
--     current node (prepended at each descent; reversed when a key is built).
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
  :: [(Q, Bool)]
  -> GName
  -> [Int]
  -> Int
  -> [Scope]
  -> Term
  -> Set Int
  -> Acc
  -> (Acc, Set Int)
walk tele owner path depth scopes term liveOut acc = case term of
  CVar i ->
    -- An occurrence of binder at level @lvl@. It is a LAST use on this path iff
    -- the same binder is not already live downstream (@lvl `notElem` liveOut@).
    -- A borrowed binder's uses are always 'Borrowed'.
    let lvl = depth - 1 - i
     in case lookupLevel lvl scopes of
          Just sc
            | Just bid <- scId sc ->
                let us = UseSite owner (reverse path)
                    kind
                      | scBorrowed sc = Borrowed
                      | lvl `Set.member` liveOut = NonLast
                      | otherwise = LastUse
                    acc' = addUse us bid kind acc
                    -- this binder is now a free variable of the surrounding
                    -- term; flow it upstream so an earlier occurrence sees it
                    -- as still-live (and is therefore NonLast).
                    live' = Set.insert lvl liveOut
                 in (acc', live')
          -- an untracked (type-level) or out-of-body binder: no runtime use.
          _ -> (acc, liveOut)

  -- Binders ----------------------------------------------------------------
  CLam _ q _nm b ->
    -- A lambda parameter is a real runtime binder. The borrow marker (and the
    -- authoritative declared quantity) for a TOP-LEVEL parameter lives on the
    -- enclosing 'CPi', not the 'CLam' (which has no borrow field), so we pull it
    -- from the next telescope entry; once the telescope is exhausted (a nested
    -- or non-top-level lambda) we fall back to the 'CLam' quantity, owned.
    let (declQ, borrowed, tele') = case tele of
          (tq, tb) : trest -> (tq, tb, trest)
          [] -> (q, False, [])
        bid = BinderId owner (reverse path)
        sc = Scope depth (Just bid) borrowed
        acc0 = addBinder bid declQ borrowed acc
        (acc1, liveB) = walk tele' owner (3 : path) (depth + 1) (sc : scopes) b liveOut acc0
     in (acc1, dropLevel depth liveB)

  CPi _ _q _borrowed _nm dom cod ->
    -- A Pi is a TYPE; its binder carries no runtime value. We descend (a
    -- dependent type can mention runtime binders in erased positions, and a
    -- type-valued top-level body is a bare 'CPi'), pushing an UNTRACKED scope so
    -- de Bruijn indices stay aligned, but record no binder fact and treat any
    -- codomain reference to it as a non-runtime (type-level) reference.
    let (acc1, liveDom) = walk [] owner (4 : path) depth scopes dom liveOut acc
        sc = Scope depth Nothing False
        (acc2, liveCod) = walk [] owner (5 : path) (depth + 1) (sc : scopes) cod liveDom acc1
     in (acc2, dropLevel depth liveCod)

  CLet q _nm _ty rhs b ->
    -- Sequential: the rhs runs, binds the name, then the body. Liveness flows
    -- backward — the body's live-out (minus the new binder) is the rhs's
    -- live-out. The binder's last-use is decided inside the body.
    let bid = BinderId owner (reverse path)
        acc0 = addBinder bid q False acc
        sc = Scope depth (Just bid) False
        (acc1, liveBody) = walk [] owner (3 : path) (depth + 1) (sc : scopes) b liveOut acc0
        liveBody' = dropLevel depth liveBody
        (acc2, liveRhs) = walk [] owner (2 : path) depth scopes rhs liveBody' acc1
     in (acc2, liveRhs)

  CLetRec q _nm _ty rhs b ->
    -- Recursive local let: the binder is in scope in BOTH its rhs and its body.
    let bid = BinderId owner (reverse path)
        acc0 = addBinder bid q False acc
        sc = Scope depth (Just bid) False
        (acc1, liveBody) = walk [] owner (3 : path) (depth + 1) (sc : scopes) b liveOut acc0
        (acc2, liveRhs) = walk [] owner (2 : path) (depth + 1) (sc : scopes) rhs liveBody acc1
     in (acc2, dropLevel depth liveRhs)

  -- Branching: each arm is its own completion path -------------------------
  CMatch s _ann alts ->
    -- The arms are independent completion paths joined here; the scrutinee runs
    -- first (sequentially before all arms). An arm uses a binder it pattern-
    -- binds, or an outer binder; an outer binder used in one arm but not
    -- another is dropped on the arms that omit it (its absence = a drop point),
    -- which falls out of computing each arm against the SAME @liveOut@.
    let (acc1, liveArms) = walkAlts owner (2 : path) depth scopes alts liveOut acc 0
        (acc2, liveS) = walk [] owner (1 : path) depth scopes s liveArms acc1
     in (acc2, liveS)

  CIf c t e ->
    let (acc1, liveT) = walk [] owner (2 : path) depth scopes t liveOut acc
        (acc2, liveE) = walk [] owner (3 : path) depth scopes e liveOut acc1
        liveBranches = Set.union liveT liveE
        (acc3, liveC) = walk [] owner (1 : path) depth scopes c liveBranches acc2
     in (acc3, liveC)

  -- Sequential, multi-child nodes ------------------------------------------
  CApp _ f a ->
    -- Evaluation order: function head then argument. Liveness flows backward —
    -- the argument's live-out is @liveOut@; the head's live-out includes
    -- everything live in the argument.
    let (acc1, liveA) = walk [] owner (2 : path) depth scopes a liveOut acc
        (acc2, liveF) = walk [] owner (1 : path) depth scopes f liveA acc1
     in (acc2, liveF)

  CCtor _ _ann args ->
    seqChildren owner path depth scopes [(i + 3, x) | (i, x) <- zip [0 ..] args] liveOut acc

  CRecordT fs ->
    seqChildren owner path depth scopes [(i, snd f) | (i, f) <- zip [1 ..] fs] liveOut acc
  CRecordV fs ->
    seqChildren owner path depth scopes [(i, snd f) | (i, f) <- zip [1 ..] fs] liveOut acc
  CVariantT ms ->
    seqChildren owner path depth scopes [(i, m) | (i, m) <- zip [1 ..] ms] liveOut acc
  CQuote _ slots ->
    seqChildren owner path depth scopes [(i, sl) | (i, sl) <- zip [1 ..] slots] liveOut acc

  -- Single-child nodes -----------------------------------------------------
  CProj e _ -> descend1 owner path depth scopes e liveOut acc
  CProjAt e _ _ -> descend1 owner path depth scopes e liveOut acc
  CInject _ e -> descend1 owner path depth scopes e liveOut acc
  CSealE _ e -> descend1 owner path depth scopes e liveOut acc
  CSigT _ e -> descend1 owner path depth scopes e liveOut acc
  CThunkE e -> descend1 owner path depth scopes e liveOut acc
  CLazyE e -> descend1 owner path depth scopes e liveOut acc
  CForceE e -> descend1 owner path depth scopes e liveOut acc

  -- Leaves and opaque-do ---------------------------------------------------
  CGlob _ -> (acc, liveOut)
  CSort _ -> (acc, liveOut)
  CLit _ -> (acc, liveOut)
  CMeta _ -> (acc, liveOut)
  -- §18.8 do-kernel: opaque here, matching the 'CoreOps.foldTermWithDepth'
  -- convention. Binders inside a do-block are lowered by a separate path; S1.1
  -- records no ownership for them (sound, conservative).
  CDo _ _ -> (acc, liveOut)

-- | Walk a single child at child-position @c@.
descend1 :: GName -> [Int] -> Int -> [Scope] -> Term -> Set Int -> Acc -> (Acc, Set Int)
descend1 owner path depth scopes e liveOut acc =
  walk [] owner (1 : path) depth scopes e liveOut acc

-- | Walk a sequence of children (left-to-right evaluation order) at the given
-- child-positions, threading liveness backward through them. Each entry is
-- @(childPos, subterm)@.
seqChildren
  :: GName -> [Int] -> Int -> [Scope] -> [(Int, Term)] -> Set Int -> Acc -> (Acc, Set Int)
seqChildren owner path depth scopes children liveOut acc =
  -- process right-to-left so a later child's liveness flows into the earlier
  -- child's live-out (an earlier occurrence is NonLast if a later one exists).
  foldr
    (\(c, t) (a, lo) -> walk [] owner (c : path) depth scopes t lo a)
    (acc, liveOut)
    children

-- | Walk all arms of a 'CMatch'. Each arm is an INDEPENDENT completion path
-- joined against the same @liveOut@; the returned live set is the union over
-- arms (an outer binder is live before the match iff some arm uses it). @ai@ is
-- the running arm index (its child-position under the match node).
walkAlts
  :: GName -> [Int] -> Int -> [Scope] -> [CaseAlt] -> Set Int -> Acc -> Int -> (Acc, Set Int)
walkAlts _owner _path _depth _scopes [] _liveOut acc _ai = (acc, Set.empty)
walkAlts owner path depth scopes (alt : rest) liveOut acc ai =
  let (acc1, liveAlt) = walkAlt owner (ai : path) depth scopes alt liveOut acc
      (acc2, liveRest) = walkAlts owner path depth scopes rest liveOut acc1 (ai + 1)
   in (acc2, Set.union liveAlt liveRest)

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
  :: GName -> [Int] -> Int -> [Scope] -> CaseAlt -> Set Int -> Acc -> (Acc, Set Int)
walkAlt owner path depth scopes (CaseAlt pat mguard body) liveOut acc =
  let n = patBindersC pat
      -- pattern slots, innermost-first as they sit in the arm-body de Bruijn
      -- order: slot at body index @k@ was introduced at level @depth+n-1-k@.
      -- We register them under the arm path with a slot-position suffix so each
      -- has a distinct, stable BinderId.
      newScopes =
        [ Scope (depth + n - 1 - k) (Just (BinderId owner (reverse (negate (k + 1) : path)))) False
        | k <- [0 .. n - 1]
        ]
      acc0 =
        foldr
          (\sc a -> maybe a (\bid -> addBinder bid QW False a) (scId sc))
          acc
          newScopes
      depth' = depth + n
      scopes' = newScopes ++ scopes
      -- guard (if any) runs before the body; both are under the pattern binders
      (acc1, liveBody) = walk [] owner (1 : path) depth' scopes' body liveOut acc0
      (acc2, liveArm) = case mguard of
        Nothing -> (acc1, liveBody)
        Just g -> walk [] owner (0 : path) depth' scopes' g liveBody acc1
      -- drop the pattern-bound levels: they are local to the arm
      liveArm' = foldr Set.delete liveArm [depth .. depth + n - 1]
   in (acc2, liveArm')

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
-- The refinement is SOUND whenever the analysis sees ALL uses of a binder: a
-- tightened interval is the exact count of consuming occurrences over the
-- binder's whole scope, so if every consumer is visible the tightened bound
-- cannot be wrong. Kappa's current compile is WHOLE-PROGRAM STATIC — there is no
-- dynamic linking and no separate compilation — so the analysis ALWAYS sees
-- every use, and EVERY provably-single-use binder is refinable, EXPORTED,
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
-- The actual per-binder usage interval is the precise abstract count of CONSUMING
-- (non-borrowed) occurrences over the binder's scope ('usageIntervals'): summed
-- in sequence, joined (min\/max) across branches. It is intersected with the
-- declared interval, and recorded only when STRICTLY tighter than the declared
-- one (otherwise the declared quantity already says everything).
refineOwnership
  :: Map GName Term -> Map GName OwnInfo -> Map GName OwnInfo
refineOwnership bodies =
  Map.mapWithKey refineOne
  where
    refineOne g oi =
      case Map.lookup g bodies of
        Nothing -> oi
        Just body ->
          let intervals = usageIntervals g body
           in oi
                { oiBinders =
                    Map.mapWithKey (refineBinder intervals) (oiBinders oi)
                }

    refineBinder intervals bid bo
      -- a borrowed binder is governed by the borrow convention, not the
      -- consuming-use interval; leave it unrefined.
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

-- | The precise per-binder CONSUMING-use interval over a whole body, keyed by the
-- same 'BinderId's 'annotateOwnership' records. The interval @(lo, hi)@ counts how
-- many times the binder is consumingly used (a borrowed occurrence does NOT
-- count) along a completion path: @lo@ over the path that uses it least, @hi@ over
-- the path that uses it most (@Nothing@ = unbounded, which never arises for a
-- finite term but is carried for totality). Sequential composition ADDS the
-- per-binder intervals; a branch ('CMatch'\/'CIf') JOINS them (min lower, max
-- upper) since each arm is its own path.
--
-- This mirrors the structure of the 'walk' liveness pass but tracks counts rather
-- than last-use, so the two stay independent (a bug in one cannot silently mask
-- the other). It returns intervals for value binders only; an untracked
-- (type-level) binder records none.
usageIntervals :: GName -> Term -> Map BinderId (Int, Maybe Int)
usageIntervals owner body = snd (count 0 [] [] body)
  where
    -- @count depth scopes path term@ → (per-binder interval over @term@, accum of
    -- binders introduced under @term@). @scopes@ resolves a 'CVar' index to its
    -- binder (innermost first); @path@ is the reversed child path (for keys).
    count
      :: Int
      -> [(Int, Maybe BinderId, Bool)] -- (level, binderId?, borrowed?)
      -> [Int]
      -> Term
      -> (Map BinderId (Int, Maybe Int), Map BinderId (Int, Maybe Int))
    count depth scopes path term = case term of
      CVar i ->
        let lvl = depth - 1 - i
         in case resolve lvl scopes of
              Just (Just bid, borrowed)
                | not borrowed -> (Map.singleton bid (1, Just 1), Map.empty)
              _ -> (Map.empty, Map.empty)

      CLam _ _ _ b ->
        let bid = BinderId owner (reverse path)
            (uses, sub) = count (depth + 1) ((depth, Just bid, False) : scopes) (3 : path) b
         in (Map.delete bid uses, recordSelf bid uses sub)

      CPi _ _ _ _ dom cod ->
        let (uDom, sDom) = count depth scopes (4 : path) dom
            (uCod, sCod) = count (depth + 1) ((depth, Nothing, False) : scopes) (5 : path) cod
         in (addUses uDom uCod, Map.union sDom sCod)

      CLet _ _ _ rhs b ->
        let bid = BinderId owner (reverse path)
            (uRhs, sRhs) = count depth scopes (2 : path) rhs
            (uB, sB) = count (depth + 1) ((depth, Just bid, False) : scopes) (3 : path) b
            body' = Map.delete bid uB
         in (addUses uRhs body', recordSelf bid uB (Map.union sRhs sB))

      CLetRec _ _ _ rhs b ->
        let bid = BinderId owner (reverse path)
            scopes' = (depth, Just bid, False) : scopes
            (uRhs, sRhs) = count (depth + 1) scopes' (2 : path) rhs
            (uB, sB) = count (depth + 1) scopes' (3 : path) b
            combined = addUses uRhs uB
         in (Map.delete bid combined, recordSelf bid combined (Map.union sRhs sB))

      CMatch s _ alts ->
        let (uAlts, sAlts) = countAlts depth scopes (2 : path) alts 0
            (uS, sS) = count depth scopes (1 : path) s
         in (addUses uS uAlts, Map.union sS sAlts)

      CIf c t e ->
        let (uT, sT) = count depth scopes (2 : path) t
            (uE, sE) = count depth scopes (3 : path) e
            (uC, sC) = count depth scopes (1 : path) c
         in (addUses uC (joinUses uT uE), Map.unions [sC, sT, sE])

      CApp _ f a -> seqK depth scopes path [(1, f), (2, a)]
      CCtor _ _ args -> seqK depth scopes path (zip [3 ..] args)
      CRecordT fs -> seqK depth scopes path (zip [1 ..] (map snd fs))
      CRecordV fs -> seqK depth scopes path (zip [1 ..] (map snd fs))
      CVariantT ms -> seqK depth scopes path (zip [1 ..] ms)
      CQuote _ slots -> seqK depth scopes path (zip [1 ..] slots)

      CProj e _ -> count depth scopes (1 : path) e
      CProjAt e _ _ -> count depth scopes (1 : path) e
      CInject _ e -> count depth scopes (1 : path) e
      CSealE _ e -> count depth scopes (1 : path) e
      CSigT _ e -> count depth scopes (1 : path) e
      CThunkE e -> count depth scopes (1 : path) e
      CLazyE e -> count depth scopes (1 : path) e
      CForceE e -> count depth scopes (1 : path) e

      CGlob _ -> (Map.empty, Map.empty)
      CSort _ -> (Map.empty, Map.empty)
      CLit _ -> (Map.empty, Map.empty)
      CMeta _ -> (Map.empty, Map.empty)
      CDo _ _ -> (Map.empty, Map.empty)

    -- record a freshly-bound binder's own interval (its scope is the subterm just
    -- walked) into the accumulator alongside any deeper binders.
    recordSelf bid uses sub =
      Map.insert bid (Map.findWithDefault (0, Just 0) bid uses) sub

    -- a sequence of children evaluated in order: ADD per-binder counts.
    seqK depth scopes path children =
      let results = [count depth scopes (c : path) t | (c, t) <- children]
          uses = foldr addUses Map.empty (map fst results)
          subs = Map.unions (map snd results)
       in (uses, subs)

    countAlts _depth _scopes _path [] _ai = (Map.empty, Map.empty)
    countAlts depth scopes path (alt : rest) ai =
      let (uAlt, sAlt) = countAlt depth scopes (ai : path) alt
          (uRest, sRest) = countAlts depth scopes path rest (ai + 1)
       in (joinUses uAlt uRest, Map.union sAlt sRest)

    countAlt depth scopes path (CaseAlt pat mguard b) =
      let n = patBindersC pat
          newScopes =
            [ (depth + n - 1 - k, Just (BinderId owner (reverse (negate (k + 1) : path))), False)
            | k <- [0 .. n - 1]
            ]
          depth' = depth + n
          scopes' = newScopes ++ scopes
          (uB, sB) = count depth' scopes' (1 : path) b
          (uArm, sArm) = case mguard of
            Nothing -> (uB, sB)
            Just gd ->
              let (uG, sG) = count depth' scopes' (0 : path) gd
               in (addUses uG uB, Map.union sG sB)
          -- the arm's pattern binders are local: record their own intervals and
          -- drop them from the outward-facing use map.
          bids = [bid | (_, Just bid, _) <- newScopes]
          selfRecorded = foldr (\bid m -> Map.insert bid (Map.findWithDefault (0, Just 0) bid uArm) m) sArm bids
          outward = foldr Map.delete uArm bids
       in (outward, selfRecorded)

    resolve lvl = go
      where
        go [] = Nothing
        go ((l, mbid, brw) : rest)
          | l == lvl = Just (mbid, brw)
          | otherwise = go rest

-- | Add two per-binder consuming-use maps componentwise (SEQUENTIAL composition:
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

-- | Join two per-binder consuming-use maps (a BRANCH: each is its own completion
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
--   * a binder with @boDeclQ == 1@ (linear) has EXACTLY ONE 'LastUse' and NO
--     'NonLast' occurrence;
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
  -> GName
  -> Term
  -> OwnInfo
  -> [String]
crossCheckOwnInfo ctx owner body oi =
  let (_, assoc) = analyzeBodyFull (paramTelescope ctx owner) owner body
   in checkAll owner body oi assoc

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
  -> Map GName OwnInfo
  -> [String]
crossCheckBodies ctx bodies own =
  concatMap one (Map.toList bodies)
  where
    one (g, body) =
      let (oiWalk, assoc) = analyzeBodyFull (paramTelescope ctx g) g body
          -- prefer the supplied 'OwnInfo' (the one threaded through the
          -- pipeline) but fall back to the freshly-walked one; they are equal
          -- by construction (same walk), so this only guards a missing entry.
          oi = Map.findWithDefault oiWalk g own
       in checkAll g body oi assoc

-- | Check the declared-quantity invariants (S1.1) AND the §3a refinement
-- invariant (S1.4 — tighten-only) for one body, given the binder→kinds
-- association.
checkAll :: GName -> Term -> OwnInfo -> Map BinderId [UseKind] -> [String]
checkAll g _body oi perBinder =
  concatMap checkOne (Map.toList (oiBinders oi))
  where
    checkOne (bid, bo) =
      let ks = Map.findWithDefault [] bid perBinder
       in checkKinds g bid bo ks
            ++ checkRefined g bid bo

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
    msg s = T.unpack (gKey g) <> " @" <> show (biPath bid) <> ": " <> s
    showI (lo, Just hi) = "[" <> show lo <> "," <> show hi <> "]"
    showI (lo, Nothing) = "[" <> show lo <> ",ω]"

-- | The per-binder declared-quantity invariant (§12.2.5\/§12.2.6).
--
-- The classification multiset is read PATH-AWARELY by exploiting a structural
-- property of the backward walk: within one sequential completion path it
-- threads @liveOut@ so an upstream occurrence always sees a downstream one and
-- is therefore 'NonLast'. Hence two 'LastUse's for the same binder can ONLY
-- arise on DISTINCT branches (e.g. a linear @state@ consumed once in each
-- match arm), never twice on one path. Therefore:
--
--   * a __linear__ (@1@) binder is well-classified iff it has NO 'NonLast'
--     (every occurrence is the last on its path) and at least one 'LastUse'
--     (it is consumed — §12.2.5 forbids dropping it on any path). Multiple
--     'LastUse's are fine: one per branch. A 'NonLast' means the analysis put a
--     non-final use where the linear contract guarantees a single per-path use,
--     i.e. the analysis is wrong;
--   * a __borrowed__ (@&@) binder has NO consuming use at all — every use is
--     'Borrowed'.
checkKinds :: GName -> BinderId -> BinderOwn -> [UseKind] -> [String]
checkKinds g bid bo ks
  | boBorrowed bo =
      [ msg ("borrowed binder has a consuming " <> show k <> " use")
      | k <- ks, k == LastUse || k == NonLast
      ]
  | boDeclQ bo == Q1 =
      let lasts = length (filter (== LastUse) ks)
          nonlasts = length (filter (== NonLast) ks)
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
      T.unpack (gKey g) <> " @" <> show (biPath bid) <> ": " <> s

-- ── S1.5 call-site classification assert ─────────────────────────────
--
-- The S1.5 deliverable (PERCEUS-S1-PLAN (d)\/(e)) is the OBSERVE-ONLY debug
-- assert that every call site CAN classify each of its arguments under the
-- owned\/borrowed convention 'Kappa.Backend.Repr.argConvSelect' derives from the
-- callee telescope — the exact lookup a future S2 dup\/drop pass performs at each
-- 'CApp'. NO codegen changes; this only checks that the data S2 will need is
-- recoverable at every statically-resolvable call site.
--
-- \"Statically resolvable\" = a call spine whose head is a known GLOBAL
-- ('CGlob') — the case S2 resolves via the callee 'CPi' telescope (PERCEUS-RC-
-- DESIGN §3 / PERCEUS-S1-PLAN (d): \"at each 'CApp', resolve the callee 'CPi'
-- telescope (already done by 'repSelect')\"). For such a spine, 'argConvSelect'
-- on the callee's type MUST SUCCEED — the telescope is walkable — so S2 has a
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
-- 'argConvSelect' (correctly) skips it. Matching spine arguments to telescope
-- parameters — skipping the erased ones — is the lockstep zip S2 itself performs;
-- the S1.5 deliverable is only that the convention list EXISTS at every such site.

-- | Walk a whole corpus and return every call-site classification finding (empty
-- ⇒ every statically-resolvable call site can classify each argument). The
-- test-suite\/lint gate for S1.5.
argConvBodies :: EvalCtx -> Map GName Term -> [String]
argConvBodies ctx = concatMap (\(g, body) -> argConvFindings ctx g body) . Map.toList

-- | Call-site classification findings for one body: for every application spine
-- with a 'CGlob' head, check 'argConvSelect' classifies each supplied explicit
-- argument. Returns a list of human-readable findings (empty ⇒ clean).
argConvFindings :: EvalCtx -> GName -> Term -> [String]
argConvFindings ctx owner = goTerm
  where
    -- A bespoke spine-aware walk: at a 'CApp' we decompose the FULL spine once
    -- ('spineOfTerm') so an intermediate spine 'CApp' is not re-checked on a
    -- partial argument list, then recurse only into the arguments (and a
    -- non-global head), never back into the spine's inner 'CApp's.
    goTerm t = case t of
      CApp {} ->
        let (hd, args) = spineOfTerm t
            here = case hd of
              CGlob g -> checkCall g args
              _ -> goTerm hd
         in here ++ concatMap (goTerm . snd) args
      CLam _ _ _ b -> goTerm b
      CPi _ _ _ _ a b -> goTerm a ++ goTerm b
      CCtor _ _ as -> concatMap goTerm as
      CMatch s _ alts ->
        goTerm s ++ concatMap (\(CaseAlt _ gd b) -> maybe [] goTerm gd ++ goTerm b) alts
      CRecordT fs -> concatMap (goTerm . snd) fs
      CRecordV fs -> concatMap (goTerm . snd) fs
      CProj e _ -> goTerm e
      CProjAt e _ _ -> goTerm e
      CVariantT ms -> concatMap goTerm ms
      CInject _ e -> goTerm e
      CLet _ _ ty rhs b -> goTerm ty ++ goTerm rhs ++ goTerm b
      CLetRec _ _ ty rhs b -> goTerm ty ++ goTerm rhs ++ goTerm b
      CSealE _ e -> goTerm e
      CSigT _ e -> goTerm e
      CThunkE e -> goTerm e
      CLazyE e -> goTerm e
      CForceE e -> goTerm e
      CIf c th el -> goTerm c ++ goTerm th ++ goTerm el
      CQuote _ slots -> concatMap goTerm slots
      -- leaves and opaque-do
      CVar _ -> []
      CGlob _ -> []
      CSort _ -> []
      CLit _ -> []
      CMeta _ -> []
      CDo _ _ -> []

    -- assert the callee telescope is WALKABLE so S2 has a per-parameter
    -- convention list. Only fired when the spine actually supplies an explicit
    -- argument (a bare 'CGlob' with no args is not a consuming call site).
    checkCall g args =
      case Map.lookup g (globalsMap (ecGlobals ctx)) of
        -- an unknown global (e.g. a runtime prim with no recorded type) cannot be
        -- classified here; that is not a failure of the accessor — skip it.
        Nothing -> []
        Just gd ->
          let hasExpl = not (null [() | (Expl, _) <- args])
              walkable = case argConvSelect ctx (gdType gd) of
                Just _ -> True
                Nothing -> False
           in [ T.unpack (gKey owner) <> " → " <> T.unpack (gKey g)
                  <> ": callee telescope is not walkable (argConvSelect = Nothing)"
              | hasExpl
              , not walkable
              ]

-- ── Dump rendering ───────────────────────────────────────────────────

-- | Render one definition's 'OwnInfo' for the @kappa dump-ownership@ CLI
-- surface: per binder its @(declQ, refined, borrowed, droppable)@, and per
-- 'CVar' occurrence its @LastUse|NonLast|Borrowed@ classification. The output
-- is sorted by path so it is deterministic and diffable.
renderOwnInfo :: GName -> OwnInfo -> Text
renderOwnInfo g oi =
  T.unlines $
    [gKey g]
      ++ [ "  binder " <> renderPath (biPath bid)
             <> " declQ=" <> renderQ (boDeclQ bo)
             <> " refined=" <> renderRefined (boRefined bo)
             <> " borrowed=" <> tshow (boBorrowed bo)
             <> " droppable=" <> tshow (boDroppable bo)
         | (bid, bo) <- sortOn (biPath . fst) (Map.toList (oiBinders oi))
         ]
      ++ [ "  use " <> renderPath (usPath us) <> " " <> renderKind k
         | (us, k) <- sortOn (usPath . fst) (Map.toList (oiUses oi))
         ]
  where
    tshow :: Show a => a -> Text
    tshow = T.pack . show
    renderPath p = T.pack (show p)
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
