-- | Perceus RC — the canonical structural CHILD-POSITION path scheme.
--
-- The ownership side-table ("Kappa.Ownership") keys every binder and use
-- occurrence by a /structural path/: the list of child-positions taken from a
-- definition's body root down to the node (see 'Kappa.Ownership.BinderId' /
-- 'Kappa.Ownership.UseSite'). That path is de Bruijn-stable, so it survives the
-- index renumbering a Core walk performs and the one post-zonk backend rewrite
-- (@eraseQ0Args@), which lets the analysis (computed once over the elaborated
-- Core) be re-attached to the lowered term by WALKING that term and looking up
-- each node's path — never iterating the table (the S1.1-R1 discipline).
--
-- For that to work the TWO walks must agree on the child-position numbering at
-- every node: the analysis walk ('Kappa.Ownership.walk', which BUILDS the keys)
-- and the codegen walk ("Kappa.Backend.C", which RE-DERIVES a path to look the
-- key up). If they ever diverge, every op is silently misattributed (PERCEUS-S2-
-- PLAN risk R-path, "the single highest-value correctness investment"). This
-- module is the ONE source of those constants, consulted by both walks, so the
-- scheme cannot drift between them.
--
-- == The scheme
--
-- The numbers are arbitrary but FIXED; their only constraints are that distinct
-- children of one node get distinct positions and that both walks use the same
-- function for the same node. A pattern slot gets a NEGATIVE position so it can
-- never collide with a real child position (which are all @>= 0@).
module Kappa.PathScheme
  ( -- * Multi-child nodes
    appHeadPos
  , appArgPos
  , ctorArgPos
  , recordFieldPos
  , variantMemberPos
  , quoteSlotPos
    -- * Binder nodes
  , lamBodyPos
  , piDomPos
  , piCodPos
  , letRhsPos
  , letBodyPos
    -- * Branching
  , matchScrutPos
  , matchArmsPos
  , matchArmPos
  , ifCondPos
  , ifThenPos
  , ifElsePos
    -- * Match arms
  , altBodyPos
  , altGuardPos
  , patSlotPos
    -- * Single-child nodes
  , childPos
  ) where

-- ── Multi-child nodes ────────────────────────────────────────────────

-- | The function-head child of a 'Kappa.Core.CApp'.
appHeadPos :: Int
appHeadPos = 1

-- | The argument child of a 'Kappa.Core.CApp'.
appArgPos :: Int
appArgPos = 2

-- | The @i@-th argument (0-based) of a 'Kappa.Core.CCtor'. Constructor args
-- start at 3 so they never collide with the 1\/2 a binder node uses for its own
-- children at the same depth (a defensive disjointness, not strictly required).
ctorArgPos :: Int -> Int
ctorArgPos i = i + 3

-- | The @i@-th field (0-based) of a record term ('Kappa.Core.CRecordT' \/
-- 'Kappa.Core.CRecordV'). Fields are numbered from 1.
recordFieldPos :: Int -> Int
recordFieldPos i = i + 1

-- | The @i@-th member (0-based) of a 'Kappa.Core.CVariantT'. Numbered from 1.
variantMemberPos :: Int -> Int
variantMemberPos i = i + 1

-- | The @i@-th slot (0-based) of a 'Kappa.Core.CQuote'. Numbered from 1.
quoteSlotPos :: Int -> Int
quoteSlotPos i = i + 1

-- ── Binder nodes ─────────────────────────────────────────────────────

-- | The body child of a 'Kappa.Core.CLam'.
lamBodyPos :: Int
lamBodyPos = 3

-- | The domain child of a 'Kappa.Core.CPi'.
piDomPos :: Int
piDomPos = 4

-- | The codomain child of a 'Kappa.Core.CPi'.
piCodPos :: Int
piCodPos = 5

-- | The right-hand side child of a 'Kappa.Core.CLet' \/ 'Kappa.Core.CLetRec'.
letRhsPos :: Int
letRhsPos = 2

-- | The body child of a 'Kappa.Core.CLet' \/ 'Kappa.Core.CLetRec'.
letBodyPos :: Int
letBodyPos = 3

-- ── Branching ────────────────────────────────────────────────────────

-- | The scrutinee child of a 'Kappa.Core.CMatch'.
matchScrutPos :: Int
matchScrutPos = 1

-- | The position introduced ABOVE the arms of a 'Kappa.Core.CMatch'. Each arm's
-- path is @armPos : matchArmsPos : <match path>@ (see 'matchArmPos'), so the
-- arms collectively sit under this one slot, disjoint from the scrutinee's.
matchArmsPos :: Int
matchArmsPos = 2

-- | The @i@-th arm (0-based) of a 'Kappa.Core.CMatch', as the position directly
-- under 'matchArmsPos'. The arm index is the position (0, 1, 2, …).
matchArmPos :: Int -> Int
matchArmPos i = i

-- | The condition child of a 'Kappa.Core.CIf'.
ifCondPos :: Int
ifCondPos = 1

-- | The then-branch child of a 'Kappa.Core.CIf'.
ifThenPos :: Int
ifThenPos = 2

-- | The else-branch child of a 'Kappa.Core.CIf'.
ifElsePos :: Int
ifElsePos = 3

-- ── Match arms ───────────────────────────────────────────────────────

-- | The body child of a match arm ('Kappa.Core.CaseAlt'), under the arm's path.
altBodyPos :: Int
altBodyPos = 1

-- | The guard child of a match arm ('Kappa.Core.CaseAlt'), under the arm's path.
altGuardPos :: Int
altGuardPos = 0

-- | The position of the @k@-th (0-based) pattern slot binder of a match arm,
-- under the arm's path. A NEGATIVE value (@-(k+1)@) so a pattern-slot binder key
-- can never collide with any real child position (all @>= 0@). Each slot gets a
-- distinct, stable position.
patSlotPos :: Int -> Int
patSlotPos k = negate (k + 1)

-- ── Single-child nodes ───────────────────────────────────────────────

-- | The sole child of a single-child node ('Kappa.Core.CProj',
-- 'Kappa.Core.CProjAt', 'Kappa.Core.CInject', 'Kappa.Core.CSealE',
-- 'Kappa.Core.CSigT', 'Kappa.Core.CThunkE', 'Kappa.Core.CLazyE',
-- 'Kappa.Core.CForceE').
childPos :: Int
childPos = 1
