-- | Legacy Perceus RC audit path scheme.
--
-- The ownership side-table ("Kappa.Ownership") keys every binder and use
-- occurrence by a /structural path/: the list of child-positions taken from a
-- definition's body root down to the node (see 'Kappa.Ownership.BinderId' /
-- 'Kappa.Ownership.UseSite'). That path is de Bruijn-stable, so it survives the
-- index renumbering a Core walk performs. Before S5.A, native codegen also
-- re-derived these paths to reattach ownership facts; current C/LLVM emission
-- instead consumes node-local KBackendIR ownership metadata. This module remains
-- the shared numbering authority for the legacy ownership dump/cross-check and
-- for old plan documents.
--
-- For the legacy table to remain meaningful, every producer/checker walk must
-- still agree on child-position numbering at every Core node. Native dup/drop
-- emission no longer depends on that agreement.
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
    -- * Do-kernel items
  , doItemPos
  , kBindActionPos
  , kLetValuePos
  , kLetQScrutPos
  , kLetQElsePos
  , kExprActionPos
  , kVarActionPos
  , kAssignActionPos
  , kReturnValuePos
  , kWhileCondPos
  , kWhileBodyPos
  , kWhileElsePos
  , kForSourcePos
  , kForBodyPos
  , kForElsePos
  , kIfCondPos
  , kIfBodyPos
  , kIfElsePos
  , kDeferActionPos
  , kUsingAcquirePos
  , kUsingReleasePos
  , kSubDoBodyPos
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

-- ── Do-kernel items ─────────────────────────────────────────────────

-- | The @i@-th statement (0-based) of a 'Kappa.Core.CDo' \/ nested
-- 'Kappa.Core.KSubDo'. Numbered from 1 like ordinary field/member slots.
doItemPos :: Int -> Int
doItemPos i = i + 1

-- | The action child of 'Kappa.Core.KBind'.
kBindActionPos :: Int
kBindActionPos = 1

-- | The value child of 'Kappa.Core.KLet'.
kLetValuePos :: Int
kLetValuePos = 1

-- | The scrutinee child of 'Kappa.Core.KLetQ'.
kLetQScrutPos :: Int
kLetQScrutPos = 1

-- | The optional else-action child of 'Kappa.Core.KLetQ'.
kLetQElsePos :: Int
kLetQElsePos = 2

-- | The action child of 'Kappa.Core.KExpr'.
kExprActionPos :: Int
kExprActionPos = 1

-- | The checker-selected @MonadRef.newRef@ action child of
-- 'Kappa.Core.KVarItem'. The source initializer is deliberately not a separate
-- runtime child here: the action already contains it.
kVarActionPos :: Int
kVarActionPos = 1

-- | The checker-selected @MonadRef.writeRef@ action child of
-- 'Kappa.Core.KAssign'. The source ref/rhs fields are retained for diagnostics
-- and interpreter parity, but the backend executes the selected action.
kAssignActionPos :: Int
kAssignActionPos = 1

-- | The value child of 'Kappa.Core.KReturn'.
kReturnValuePos :: Int
kReturnValuePos = 1

-- | The condition child of 'Kappa.Core.KWhile'.
kWhileCondPos :: Int
kWhileCondPos = 1

-- | The body child of 'Kappa.Core.KWhile'.
kWhileBodyPos :: Int
kWhileBodyPos = 2

-- | The optional else child of 'Kappa.Core.KWhile'.
kWhileElsePos :: Int
kWhileElsePos = 3

-- | The source child of 'Kappa.Core.KFor'.
kForSourcePos :: Int
kForSourcePos = 1

-- | The body child of 'Kappa.Core.KFor'.
kForBodyPos :: Int
kForBodyPos = 2

-- | The optional else child of 'Kappa.Core.KFor'.
kForElsePos :: Int
kForElsePos = 3

-- | The condition child of the @i@-th 'Kappa.Core.KIf' arm.
kIfCondPos :: Int -> Int
kIfCondPos i = 1 + (2 * i)

-- | The body child of the @i@-th 'Kappa.Core.KIf' arm.
kIfBodyPos :: Int -> Int
kIfBodyPos i = 2 + (2 * i)

-- | The optional else child of a 'Kappa.Core.KIf'. Placed after every arm slot.
kIfElsePos :: Int -> Int
kIfElsePos armCount = 1 + (2 * armCount)

-- | The action child of 'Kappa.Core.KDefer'.
kDeferActionPos :: Int
kDeferActionPos = 1

-- | The acquire child of 'Kappa.Core.KUsing'.
kUsingAcquirePos :: Int
kUsingAcquirePos = 1

-- | The release-function child of 'Kappa.Core.KUsing'.
kUsingReleasePos :: Int
kUsingReleasePos = 2

-- | The child do-body of 'Kappa.Core.KSubDo'.
kSubDoBodyPos :: Int
kSubDoBodyPos = 1

-- ── Single-child nodes ───────────────────────────────────────────────

-- | The sole child of a single-child node ('Kappa.Core.CProj',
-- 'Kappa.Core.CProjAt', 'Kappa.Core.CInject', 'Kappa.Core.CSealE',
-- 'Kappa.Core.CSigT', 'Kappa.Core.CThunkE', 'Kappa.Core.CLazyE',
-- 'Kappa.Core.CForceE').
childPos :: Int
childPos = 1
