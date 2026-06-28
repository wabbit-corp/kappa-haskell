-- | Perceus RC Stage S1.0 — the ownership side-table (an EMPTY pass).
--
-- This module is the foundational plumbing for the Perceus reference-counting
-- arc (see @runtime/docs/PERCEUS-RC-DESIGN.md@ §7 stage S1). The full S1 work
-- is to thread the elaborated owned(@1@)\/borrowed(@&@)\/last-use ownership
-- decisions onto the IR the native backends lower, so a later dup\/drop pass
-- (S2+) can consume them. Those decisions are computed during elaboration
-- (§12.2 quantity\/borrow accounting) but ERASED before KBackendIR (§31.2), so
-- they must be re-attached as backend metadata rather than read off the IR.
--
-- The S1 plan deliberately does NOT add fields to 'Term'\/'CVar' — there are
-- hundreds of 'CVar' construction sites and §31.2 erasure machinery that would
-- all have to change, and an unused field on the hot Core type is pure cost.
-- Instead the ownership facts live in this SIDE-TABLE, keyed by stable Core
-- identities, and are threaded through the pipeline beside the existing
-- @csCoreBodies@ \/ @gsSuspenders@ metadata.
--
-- __Stage S1.0 is the empty pass.__ 'annotateOwnership' returns EMPTY maps.
-- The point of S1.0 is purely structural: the type shapes exist, the function
-- exists, and it is wired through "Kappa.Pipeline" (populating @csOwnership@)
-- and "Kappa.Backend.C" (carried as @gsOwnership@) EXACTLY mirroring the
-- @gsSuspenders@ precedent. No consumer reads the table yet — like the
-- Stage-0 'CCtor'\/'CMatch' annotations, it is observe-only, so codegen,
-- conformance fixtures, and interp\/C\/LLVM parity are all byte-identical. A
-- later stage replaces the empty body with the real owned\/borrowed\/last-use
-- computation without touching any of this plumbing.
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
    -- * The (empty) annotation pass
  , annotateOwnership
  ) where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import Kappa.Core (GName, Q, Term)
import Kappa.Eval (EvalCtx)

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
--
-- (The 'biPath' is left abstract as an @[Int]@ child-position list; the exact
-- node-position encoding is fixed when the real S1 pass is written. S1.0 builds
-- no keys, so the encoding is unconstrained here.)
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
  -- mandatory choice at any dynamic-link boundary). Refinement only ever
  -- /tightens/, never widens, so it can never violate the source contract.
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

-- | The empty side-table — no binders, no uses. The S1.0 result for every
-- definition.
emptyOwnInfo :: OwnInfo
emptyOwnInfo = OwnInfo Map.empty Map.empty

-- | Stage S1.0 ownership annotation — __the empty pass.__
--
-- Given the typing context and the elaborated, zonked Core body of each
-- top-level definition (the same @csCoreBodies@ map the native backend lowers),
-- produce the per-definition ownership side-table.
--
-- At S1.0 this returns EMPTY maps: every definition maps to 'emptyOwnInfo'
-- (equivalently, the result is empty). It exists so the plumbing — populate in
-- "Kappa.Pipeline", carry to the backend "Kappa.Backend.C" — is in place and
-- threading, with NOTHING changing in codegen. A later stage replaces this body
-- with the real owned\/borrowed\/last-use computation over @bodies@ (consulting
-- @ctx@ for global signatures\/quantities and the §3a whole-program call graph)
-- without altering its signature or any caller.
annotateOwnership :: EvalCtx -> Map GName Term -> Map GName OwnInfo
annotateOwnership _ctx _bodies = Map.empty
