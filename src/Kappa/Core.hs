-- | Core calculus (a pragmatic KCore subset, Spec §30.2) and its
-- normalization-by-evaluation machinery (§31.1).
--
-- Two central types live here, and the difference between them is the key
-- to the whole back half of the compiler:
--
--   * 'Term' is /syntax/ — what elaboration produces. Variables are de
--     Bruijn __indices__ ('CVar', counting outward from the use site).
--   * 'Value' is the /semantic/ domain used during evaluation. Variables
--     are de Bruijn __levels__ ('VRigid', counting inward from the top),
--     and functions are real Haskell 'Closure's.
--
-- 'Kappa.Eval' shuttles between them (@eval :: Term -> Value@,
-- @quote :: Value -> Term@) to normalize and compare terms. See
-- docs/CONCEPTS.md for the index-vs-level and NbE background.
--
-- Representation choices, mapped to the spec:
--
--   * Pi binders carry quantities; quantity is part of function-type
--     identity in conversion (§31.1).
--   * Record types and values are canonicalized to lexicographic field
--     order (the §31.4 canonical order for non-dependent records); field
--     initializers are still evaluated in source order by elaborating
--     through a 'CLet' chain.
--   * Variant members are identified by the canonical rendering of the
--     member type (§31.3 stable member identities); widening is a no-op.
--   * @do@ blocks, loops and abrupt control are kept structured ('CDo')
--     and executed by the interpreter per the §18.8 completion kernel.
--   * Definitions record 'conversionReducible' separately from being
--     total-certified (§15.1); only reducible definitions δ-unfold.
module Kappa.Core
  ( GName (..)
  , gnameText
  , gKey
  , primModule
  , Icit (..)
  , Q (..)
  , Term (..)
  , CaseAlt (..)
  , CorePat (..)
  , KItem (..)
  , KCond (..)
  , RefCellId (..)
  , RefLoweringWitness (..)
  , RefActionWitness (..)
  , Literal (..)
  , Telescope
  , Value (..)
  , Closure (..)
  , Env
  , Spine
  , MetaId
  , QuoteCapture (..)
  , QuotedSyntax (..)
  ) where

import Control.Concurrent (ThreadId)
import Control.Concurrent.MVar (MVar)
import Control.Concurrent.STM (TVar)
import Data.Array.IO (IOArray)
import Data.ByteString (ByteString)
import Data.IORef (IORef)
import Data.Text (Text)
import qualified Data.Text as T
import Data.Word (Word8)
import Kappa.Source (ModuleName (..), Span)
import Kappa.Syntax (Expr)

-- | Module owning interpreter primitives.
primModule :: ModuleName
primModule = ModuleName ["__prim"]

-- | Global name: defining module + spelling.
data GName = GName !ModuleName !Text
  deriving stock (Eq, Ord, Show)

gnameText :: GName -> Text
gnameText (GName _ t) = t

-- | The fully-qualified dotted key of a global: its module path segments and
-- spelling joined by @.@ (e.g. @std.prelude.Unit@, or just @__rat@ for a
-- module-less runtime name). The stable string identity used by the backends
-- (and "Kappa.Builtins") to key constructor-tag and primitive tables.
gKey :: GName -> Text
gKey (GName (ModuleName segs) nm) = T.intercalate "." (segs ++ [nm])

data Icit = Expl | Impl
  deriving stock (Eq, Ord, Show)

-- | Core quantities (§12.2). The five portable interval quantities.
data Q = Q0 | Q1 | QW | QLe1 | QGe1
  deriving stock (Eq, Ord, Show)

type MetaId = Int

-- | Stable identity for a checker-created mutable cell within one elaborated
-- Core body. Backends use it only as proof-carrying metadata; it is not a
-- source-visible reference and does not affect runtime values.
newtype RefCellId = RefCellId Int
  deriving stock (Eq, Ord, Show)

-- | A lowering witness proving that a source `var` cell was created through the
-- checker-selected prelude `MonadRef (IO e)` dictionary, whose members are the
-- builtin native IO-ref primitives. Absence of this witness means backend
-- optimizations must use the generic selected-action path.
data RefLoweringWitness
  = BuiltinIORefWitness
      { rlwCellId :: !RefCellId
      }
  deriving stock (Eq, Ord, Show)

-- | Occurrence-level evidence for a mutable-reference action selected by the
-- checker. The action term remains authoritative for semantics; the witness is
-- only a conservative optimization proof for backends.
data RefActionWitness
  = BuiltinIORefNew !RefLoweringWitness
  | BuiltinIORefRead !RefLoweringWitness
  | BuiltinIORefWrite !RefLoweringWitness
  deriving stock (Eq, Ord, Show)

data Literal
  = LitInt !Integer -- Nat/Int/Integer share representation
  | LitDouble !Double
  | LitStr !Text
  | LitScalar !Char
  | LitByte !Word8 -- §6.5 conventional 'b' handler payload
  | LitBytes !ByteString -- §29.5 byte sequences (exact byte content)
  | LitGrapheme !Text -- §6.5 conventional 'g' handler payload (exact scalar sequence)
  deriving stock (Eq, Ord, Show)

-- | Core terms, de Bruijn indexed. Grouped into families below for reading.
data Term
  = -- Lambda-calculus core ------------------------------------------------
    CVar !Int -- ^ a bound variable, as a de Bruijn /index/ (0 = nearest binder)
  | CGlob !GName
  | CLam !Icit !Q !Text !Term
  -- | Dependent function type. The 'Bool' is the binder's borrow marker
  -- (§12.3: @(& x : A) -> …@) — part of the binder information carried in
  -- core so usage analysis reads it from the type, not the surface AST. It
  -- is metadata for the quantity/borrow checker: conversion ignores it
  -- (borrow on a parameter is not part of definitional type identity here).
  | CPi !Icit !Q !Bool !Text !Term !Term
  | CApp !Icit !Term !Term
  | CSort !Int -- ^ @Type u@
  | CLit !Literal
  -- Data and pattern matching --------------------------------------------
  -- | Saturated constructor application. The optional 'Term' is the
  -- KBackendIR Stage 0 /head-type annotation/: the constructor's
  -- instantiated, monomorphic head type as a quoted Core type term
  -- (e.g. @Option Int@ rather than the polymorphic @Option a@), or
  -- 'Nothing' where the concrete head was not in scope at the build
  -- site. It is observe-only metadata: NO backend reads it, and
  -- conversion\/'Eq' must ignore it (see 'Eq' instance note below), so
  -- it can never change tag ids, codegen, or evaluation.
  | CCtor !GName !(Maybe Term) ![Term]
  -- | Pattern match. The optional 'Term' is the KBackendIR Stage 0
  -- annotation: the scrutinee's monomorphic type as a quoted Core type
  -- term (populated from the elaborator's @sTy1@). Like 'CCtor's
  -- annotation it is observe-only — backends ignore it and 'Eq'\/
  -- conversion drop it.
  | CMatch !Term !(Maybe Term) ![CaseAlt]
  -- Records --------------------------------------------------------------
  | CRecordT ![(Text, Term)] -- ^ canonical (lexicographic) field order
  | CRecordV ![(Text, Term)]
  | CProj !Term !Text
  | -- | @CProjAt e f i@: a projection of field @f@ from a record of a
    -- statically-known CLOSED layout, where @i@ is @f@'s index in the
    -- lexicographically-sorted field list (= the @K_REC@ slot order).
    -- Semantically identical to @CProj e f@ — the interpreter ignores @i@ and
    -- looks up by name; the native backend (P0.4) reads the field at a fixed
    -- offset (@krec_at@) instead of a name scan.  Emitted only by the closed
    -- @VRecordT@ projection branch in elaboration; every other projection
    -- stays a plain @CProj@.
    CProjAt !Term !Text !Int
  -- Variants -------------------------------------------------------------
  | CVariantT ![Term] -- ^ canonical member order
  | CInject !Text !Term -- ^ member-identity tag + payload
  -- Binding and metavariables --------------------------------------------
  | CLet !Q !Text !Term !Term !Term -- ^ q, name, type, rhs, body
  | CLetRec !Q !Text !Term !Term !Term -- ^ recursive local let: rhs and body live under the binder
  | CMeta !MetaId -- ^ an unsolved unification variable (a "hole" the checker will fill)
  -- Effectful do-kernel --------------------------------------------------
  | CDo !(Maybe Text) ![KItem] -- ^ §18.8 do kernel (optional scope label, §18.7); executed natively
  -- Sealed packages / existentials ---------------------------------------
  | CSealE ![Text] !Term -- ^ §13.2.10 sealed package: opaque labels + record
  | CSigT ![Text] !Term -- ^ §13.2.10 signature type: opaque labels + record type
  -- Suspensions (laziness) -----------------------------------------------
  | CThunkE !Term -- ^ Delay
  | CLazyE !Term -- ^ Memo
  | CForceE !Term
  -- Conditional and metaprogramming --------------------------------------
  | CIf !Term !Term !Term
  | CQuote !QuotedSyntax ![Term] -- ^ §21.1 syntax quote: payload + in-quote splice slots
  deriving stock (Show)

-- | Structural equality on 'Term'.
--
-- Hand-written rather than derived for ONE reason: the KBackendIR Stage 0
-- head-type annotations on 'CCtor' and 'CMatch' are observe-only metadata
-- and MUST NOT participate in term identity. Two terms that differ only in
-- their annotation are the same term for every existing client (conversion
-- caches, quote-payload comparison, dedup), so we compare the structural
-- fields and deliberately drop the annotation. Every other constructor is
-- compared field-by-field exactly as the derived instance would.
instance Eq Term where
  CVar a == CVar a' = a == a'
  CGlob a == CGlob a' = a == a'
  CLam a b c d == CLam a' b' c' d' = a == a' && b == b' && c == c' && d == d'
  CPi a b c d e f == CPi a' b' c' d' e' f' =
    a == a' && b == b' && c == c' && d == d' && e == e' && f == f'
  CApp a b c == CApp a' b' c' = a == a' && b == b' && c == c'
  CSort a == CSort a' = a == a'
  CLit a == CLit a' = a == a'
  -- annotation (the 'Maybe Term') is intentionally NOT compared
  CCtor g _ as == CCtor g' _ as' = g == g' && as == as'
  CMatch s _ alts == CMatch s' _ alts' = s == s' && alts == alts'
  CRecordT a == CRecordT a' = a == a'
  CRecordV a == CRecordV a' = a == a'
  CProj a b == CProj a' b' = a == a' && b == b'
  CProjAt a b c == CProjAt a' b' c' = a == a' && b == b' && c == c'
  CVariantT a == CVariantT a' = a == a'
  CInject a b == CInject a' b' = a == a' && b == b'
  CLet a b c d e == CLet a' b' c' d' e' =
    a == a' && b == b' && c == c' && d == d' && e == e'
  CLetRec a b c d e == CLetRec a' b' c' d' e' =
    a == a' && b == b' && c == c' && d == d' && e == e'
  CMeta a == CMeta a' = a == a'
  CDo a b == CDo a' b' = a == a' && b == b'
  CSealE a b == CSealE a' b' = a == a' && b == b'
  CSigT a b == CSigT a' b' = a == a' && b == b'
  CThunkE a == CThunkE a' = a == a'
  CLazyE a == CLazyE a' = a == a'
  CForceE a == CForceE a' = a == a'
  CIf a b c == CIf a' b' c' = a == a' && b == b' && c == c'
  CQuote a b == CQuote a' b' = a == a' && b == b'
  _ == _ = False

-- | A free object-language binder captured by a syntax quote (§21.4
-- hidden syntax-scope metadata): the fresh hygienic spelling used in
-- the quoted payload, the original source spelling, and the de Bruijn
-- LEVEL of the binder in the quote site's elaboration context.
data QuoteCapture = QuoteCapture
  { qcHyg :: !Text
  , qcOrig :: !Text
  , qcLevel :: !Int
  }
  deriving stock (Eq, Show)

-- | The meta-phase payload of an elaborated syntax quote (§21.1):
-- surface syntax (with 'Kappa.Syntax.EQuoteHole' grafting slots for
-- in-quote splices) plus hygiene metadata and the quote's origin.
data QuotedSyntax = QuotedSyntax
  { qsExpr :: !Expr
  , qsCaptures :: ![QuoteCapture]
  , qsSpan :: !Span
  }
  deriving stock (Show)

-- | Quotes compare by rendered payload and captures ('Expr' has no
-- structural equality); used only by 'Term' equality, where comparing
-- two quotes is rare and a conservative answer is sound.
instance Eq QuotedSyntax where
  a == b =
    show (qsExpr a) == show (qsExpr b)
      && qsCaptures a == qsCaptures b

-- | Match alternative over core patterns.
data CaseAlt = CaseAlt
  { caPat :: !CorePat
  , caGuard :: !(Maybe Term) -- ^ guard, under pattern binders
  , caBody :: !Term -- ^ under pattern binders (left-to-right)
  }
  deriving stock (Eq, Show)

data CorePat
  = CPWild
  | CPVar !Text
  | CPLit !Literal
  | -- | A constructor pattern @C p₁ … pₖ@. The @Int@ is the number of EXISTENTIAL
    -- GADT-index skolems the unpack binds (§17.1): @MkP : forall s. Tag s -> P@
    -- binds an existential @s@ not pinned by the result type, which the checker
    -- promotes to a rigid skolem occupying a real de Bruijn slot in the arm's
    -- elaboration context (see 'Kappa.Check.ctorFieldTypesCtx'). Those skolems sit
    -- BELOW the field binders in the de Bruijn order, so Core matching accounts
    -- for the same N erased slots UNDER the field values
    -- — otherwise every index in the arm body referring to an outer-bound variable
    -- is inflated by N with no matching Core environment slot. The placeholders are never
    -- read (a skolem is an erased type); the slots only keep the OTHER indices
    -- correct. @0@ for an ordinary (non-existential) constructor pattern.
    CPCtor !GName !Int ![CorePat]
  | CPTuple ![CorePat]
  | CPRecord ![(Text, CorePat)] !(Maybe Text)
  -- ^ fields, optional rest binder (binds the remaining fields; @Just ""@
  -- discards them)
  | CPInject !Text !CorePat -- ^ variant member pattern
  | CPInjectRest ![Text] -- ^ residual-row pattern: excluded tags
  | -- | An or-pattern @p₁ | … | pₖ@ (§17.2.3). All alternatives bind the same
    -- set of names; the BODY uses the first alternative's binder order
    -- (canonical). The parallel @[[Int]]@ holds, per alternative, the
    -- permutation from that alternative's own structural binder order to the
    -- canonical order: when alternative @i@ matches and yields bindings @bs@
    -- (structural order), the canonical bindings are @[bs !! (perm!!j)]@. This
    -- keeps the body's de Bruijn layout correct no matter which alternative
    -- matched, even when alternatives list the shared binders in different
    -- positions (e.g. @A p q | B q p@).
    CPOr ![CorePat] ![[Int]]
  | CPAs !Text !CorePat -- ^ as-pattern: binds the whole value, then inner
  deriving stock (Eq, Show)

-- | do-kernel items (typed during elaboration, executed by Interp).
data KItem
  = KBind !Q !CorePat !Term !(Maybe RefActionWitness) -- ^ let pat <- e
  | KLet !Q !CorePat !Term -- ^ let pat = e
  | KLetQ !CorePat !Term !(Maybe (CorePat, Term)) -- ^ let? with optional else
  | KExpr !Term
  | KVarItem !Text !Term !Term !(Maybe RefActionWitness) -- ^ name, initializer value, MonadRef.newRef action
  | KAssign !Term !Bool !Term !Term !(Maybe RefActionWitness) -- ^ ref-term, monadic?, rhs, MonadRef.writeRef action
  | KReturn !Term
  | KBreak !(Maybe Text)
  | KContinue !(Maybe Text)
  | KWhile !(Maybe Text) !KCond ![KItem] !(Maybe [KItem])
  | KFor !(Maybe Text) !CorePat !Term ![KItem] !(Maybe [KItem])
  | KIf ![(Term, [KItem])] !(Maybe [KItem])
  | KDefer !(Maybe Text) !Term -- ^ defer (Nothing) / defer@label (§18.7)
  | KUsing !CorePat !Term !Term -- ^ pattern, acquire, release-dict-member
  | -- | A nested @do@ block written in statement position (§18.8.3.1): it runs
    -- as a child scope — its own optional label, bindings, and LIFO exit
    -- actions — but it is TRANSPARENT to abrupt completion, so a @break@ /
    -- @continue@ / @return\@L@ inside it that targets an enclosing loop or
    -- function (resolved against the inherited lexical context) propagates
    -- outward. Distinct from a first-class @do@ VALUE (e.g. @let x = do …@),
    -- which is an opaque computation reached through 'KExpr'/'KBind'.
    KSubDo !(Maybe Text) ![KItem]
  deriving stock (Eq, Show)

-- | A while condition is either the ordinary pure Bool condition, or the
-- §18.6 monadic condition action that must be run again for every test.
data KCond
  = KCondPure !Term
  | KCondAction !Term
  deriving stock (Eq, Show)

type Telescope = [(Icit, Q, Text, Term)]

-- ── Values (NbE domain) ──────────────────────────────────────────────

type Env = [Value]

-- | Application spine of a neutral value.
type Spine = [(Icit, Value)]

data Closure = Closure !Env !Term
  deriving stock (Show)

-- | The result of evaluating a 'Term' ('Kappa.Eval'). The first three are
-- the /neutral heads/: a head that can't reduce yet (a variable, an unsolved
-- meta, or an unfolded-elsewhere global) applied to a 'Spine' of arguments.
-- They are how evaluation represents "stuck" computation; the stuck
-- /eliminators/ 'VMatchN', 'VProjN', and 'VIfN' (a match\/projection\/if on
-- a neutral) are neutral too. The distinction between 'VRigid' (a real
-- variable — stuck for good until substituted) and 'VFlex' (a meta — could
-- still reduce once the meta is solved) is what unification keys off.
data Value
  = VRigid !Int !Spine -- ^ neutral: a bound variable as a de Bruijn /level/ (0 = outermost) + its args
  | VFlex !MetaId !Spine -- ^ neutral: an unsolved metavariable + its args
  | VGlobN !GName !Spine -- ^ neutral global (opaque or not yet unfolded)
  | VLam !Icit !Q !Text !Closure
  | VPi !Icit !Q !Bool !Text !Value !Closure -- ^ 'Bool': binder borrow marker (§12.3), see 'CPi'
  | VSort !Int
  | VLit !Literal
  | VCtor !GName ![Value]
  | VRecordT ![(Text, Value)]
  | VRecordV ![(Text, Value)]
  | VVariantT ![Value]
  | VInject !Text !Value
  | VMatchN !Value ![CaseAlt] !Env -- ^ stuck match
  | VProjN !Value !Text -- ^ stuck projection
  | VSealV ![Text] !Value -- ^ §13.2.10 sealed package (opaque member projections stick)
  | VSigT ![Text] !Value -- ^ §13.2.10 signature type (opaque labels + record type)
  | VDoV !(Maybe Text) ![KItem] !Env -- ^ suspended do block (optional scope label, §18.7)
  | VThunkV !Closure
  | VLazyV !Closure
  | VIfN !Value !Closure !Closure -- ^ stuck if
  | VPrim !Text ![Value] -- ^ builtin primitive, partially applied
  | VRef !(IORef Value) -- ^ runtime mutable cell (MonadRef, §18.6.1)
  | VArr !Int !(IOArray Int Value) -- ^ MUTABLE-ARRAY-DESIGN: boxed mutable O(1) array (K_ARRAY oracle); fixed length (cached, so arrayLen is pure) + in-place get/set
  | VMVar !(MVar Value) -- ^ §18.11 one-shot-promise cell (blocking read parks the fiber)
  | VFiber !ThreadId !(MVar Value) -- ^ §18.1.4 fiber handle: interrupt target (ThreadId) + terminal-Exit cell
  | VScope !(IORef [Value]) -- ^ §18.1.8 explicit supervision scope: registry of attached fibers
  | VFiberRef !Int -- ^ §18.1.7 fiber-local cell identity (per-fiber values live in the runtime registry)
  | VTVar !(TVar Value) -- ^ §18.1.13 STM transactional variable
  | VIOAction !Text ![Value] -- ^ suspended IO primitive application
  | VQuote !QuotedSyntax ![Value] -- ^ §21.1 syntax value: payload + slot values (grafted lazily)

instance Show Value where
  show _ = "<value>"
