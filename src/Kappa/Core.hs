-- | Core calculus (a pragmatic KCore subset, Spec §30.2) and its
-- normalization-by-evaluation machinery (§31.1).
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
  , primModule
  , Icit (..)
  , Q (..)
  , Term (..)
  , CaseAlt (..)
  , CorePat (..)
  , KItem (..)
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
import Data.ByteString (ByteString)
import Data.IORef (IORef)
import Data.Text (Text)
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

data Icit = Expl | Impl
  deriving stock (Eq, Ord, Show)

-- | Core quantities (§12.2). The five portable interval quantities.
data Q = Q0 | Q1 | QW | QLe1 | QGe1
  deriving stock (Eq, Ord, Show)

type MetaId = Int

data Literal
  = LitInt !Integer -- Nat/Int/Integer share representation
  | LitDouble !Double
  | LitStr !Text
  | LitScalar !Char
  | LitByte !Word8 -- §6.5 conventional 'b' handler payload
  | LitBytes !ByteString -- §29.5 byte sequences (exact byte content)
  | LitGrapheme !Text -- §6.5 conventional 'g' handler payload (exact scalar sequence)
  deriving stock (Eq, Ord, Show)

-- | Core terms, de Bruijn indexed.
data Term
  = CVar !Int
  | CGlob !GName
  | CLam !Icit !Q !Text !Term
  | CPi !Icit !Q !Text !Term !Term
  | CApp !Icit !Term !Term
  | CSort !Int -- ^ @Type u@
  | CLit !Literal
  | CCtor !GName ![Term] -- ^ saturated constructor application
  | CMatch !Term ![CaseAlt]
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
  | CVariantT ![Term] -- ^ canonical member order
  | CInject !Text !Term -- ^ member-identity tag + payload
  | CLet !Q !Text !Term !Term !Term -- ^ q, name, type, rhs, body
  | CLetRec !Q !Text !Term !Term !Term -- ^ recursive local let: rhs and body live under the binder
  | CMeta !MetaId
  | CDo !(Maybe Text) ![KItem] -- ^ §18.8 do kernel (optional scope label, §18.7); executed natively
  | CSealE ![Text] !Term -- ^ §13.2.10 sealed package: opaque labels + record
  | CSigT ![Text] !Term -- ^ §13.2.10 signature type: opaque labels + record type
  | CThunkE !Term -- ^ Delay
  | CLazyE !Term -- ^ Memo
  | CForceE !Term
  | CIf !Term !Term !Term
  | CQuote !QuotedSyntax ![Term] -- ^ §21.1 syntax quote: payload + in-quote splice slots
  deriving stock (Eq, Show)

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
  | CPCtor !GName ![CorePat]
  | CPTuple ![CorePat]
  | CPRecord ![(Text, CorePat)] !(Maybe Text)
  -- ^ fields, optional rest binder (binds the remaining fields; @Just ""@
  -- discards them)
  | CPInject !Text !CorePat -- ^ variant member pattern
  | CPInjectRest ![Text] -- ^ residual-row pattern: excluded tags
  | CPOr ![CorePat]
  | CPAs !Text !CorePat -- ^ as-pattern: binds the whole value, then inner
  deriving stock (Eq, Show)

-- | do-kernel items (typed during elaboration, executed by Interp).
data KItem
  = KBind !Q !CorePat !Term -- ^ let pat <- e
  | KLet !Q !CorePat !Term -- ^ let pat = e
  | KLetQ !CorePat !Term !(Maybe (CorePat, Term)) -- ^ let? with optional else
  | KExpr !Term
  | KVarItem !Text !Term -- ^ var x = e
  | KAssign !Term !Bool !Term -- ^ ref-term, monadic?, rhs (x = e / x <- e)
  | KReturn !Term
  | KBreak !(Maybe Text)
  | KContinue !(Maybe Text)
  | KWhile !(Maybe Text) !Term ![KItem] !(Maybe [KItem])
  | KFor !(Maybe Text) !CorePat !Term ![KItem] !(Maybe [KItem])
  | KIf ![(Term, [KItem])] !(Maybe [KItem])
  | KDefer !(Maybe Text) !Term -- ^ defer (Nothing) / defer@label (§18.7)
  | KUsing !CorePat !Term !Term -- ^ pattern, acquire, release-dict-member
  deriving stock (Eq, Show)

type Telescope = [(Icit, Q, Text, Term)]

-- ── Values (NbE domain) ──────────────────────────────────────────────

type Env = [Value]

-- | Application spine of a neutral value.
type Spine = [(Icit, Value)]

data Closure = Closure !Env !Term
  deriving stock (Show)

data Value
  = VRigid !Int !Spine -- ^ de Bruijn LEVEL + spine
  | VFlex !MetaId !Spine
  | VGlobN !GName !Spine -- ^ neutral global (opaque or not yet unfolded)
  | VLam !Icit !Q !Text !Closure
  | VPi !Icit !Q !Text !Value !Closure
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
  | VMVar !(MVar Value) -- ^ §18.11 one-shot-promise cell (blocking read parks the fiber)
  | VFiber !ThreadId !(MVar Value) -- ^ §18.1.4 fiber handle: interrupt target (ThreadId) + terminal-Exit cell
  | VScope !(IORef [Value]) -- ^ §18.1.8 explicit supervision scope: registry of attached fibers
  | VFiberRef !Int -- ^ §18.1.7 fiber-local cell identity (per-fiber values live in the runtime registry)
  | VTVar !(TVar Value) -- ^ §18.1.13 STM transactional variable
  | VIOAction !Text ![Value] -- ^ suspended IO primitive application
  | VQuote !QuotedSyntax ![Value] -- ^ §21.1 syntax value: payload + slot values (grafted lazily)

instance Show Value where
  show _ = "<value>"
