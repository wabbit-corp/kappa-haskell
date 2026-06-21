-- | Bidirectional elaboration to the core (Spec §30.1; expressions §16,
-- patterns §17, traits §14, literals §6.1.5, do blocks §18).
--
-- Implicit arguments are inserted per the application-spine rules
-- (§16.1.7.1); trait goals follow the §16.3.3 ladder: local implicit
-- context, then global instance search (§14.3.1, with a
-- unique-candidate coherence rule), then boolean-proposition
-- normalization for @(lhs = rhs)@ goals decided by conversion.
--
-- Deliberate v1 restrictions surface as @E_UNSUPPORTED@ diagnostics and
-- are catalogued in SPEC_COVERAGE.md; approximations (quantity usage
-- checking, termination) are catalogued in IMPLEMENTATION_NOTES.md.
module Kappa.Check
  ( CheckState (..)
  , initCheckState
  , DataInfo (..)
  , CtorInfo (..)
  , TraitInfo (..)
  , InstanceEntry (..)
  , GlobalDef (..)
  , UnsafeConfig (..)
  , defaultUnsafeConfig
  , scriptUnsafeConfig
  , AuditRecord (..)
  , checkModule
  , expectUnsatisfiedDiags
  , zonkTermM
  , preludeModule
  , shapeModule
  ) where

import Control.Monad.State.Strict
import Data.Data (Data, cast, gmapQ)
import Data.List (elemIndex, find, foldl', intersect, nub, sort, sortOn, (\\))
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes, fromMaybe, isJust, isNothing, listToMaybe, mapMaybe)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import Kappa.Core
import Kappa.Diagnostic
import Kappa.Eval
import Kappa.Pretty (renderTerm)
import Kappa.Parser (parseExprText)
import Kappa.Source
import Kappa.Syntax hiding (CompClause (..), Quantity (..))
import qualified Kappa.Syntax as S
import Kappa.SyntaxOps
  ( boundNamesIn
  , collectSplices
  , freeVarOccurrences
  , renameVarOccurrences
  , renderExprSrc
  , replaceSplices
  , substQuoteHoles
  )
import Kappa.Token (QuotedLit (..), StrFragment (..), StringLit (..))
import Kappa.Unicode (isSingleGrapheme)

-- ── State ────────────────────────────────────────────────────────────

data DataInfo = DataInfo
  { diCtors :: ![GName]
  , diParamCount :: !Int
  }

data CtorInfo = CtorInfo
  { ciData :: !GName
  , ciType :: !Term
  , ciFields :: ![(Maybe Text, Maybe Expr)] -- ^ explicit fields: name, default (§10.1.1; elaborated at the application site)
  }

data TraitInfo = TraitInfo
  { tiParamCount :: !Int
  , tiMembers :: ![Text]
  , tiDefaults :: !(Map Text LetDef)
  , tiSupers :: ![(Text, Term)]
  -- ^ supertrait premises as (evidence field name, @\\params -> C params@)
  -- (§14.1.4); the field carries the supertrait dictionary (§14.3.3)
  }

data InstanceEntry = InstanceEntry
  { ieTrait :: !GName
  , ieTeleLen :: !Int
  , iePremises :: ![Term] -- ^ de Bruijn under the telescope
  , ieHead :: ![Term] -- ^ trait arguments under the telescope
  , ieDict :: !GName
  }

-- | An instance head elaborated and registered ahead of the body pass,
-- so instance visibility within a module does not depend on
-- declaration order (§14.3: "Instance visibility is global over the
-- compilation unit's module closure"). The members are checked later,
-- in source order, by 'elabInstance'.
data PreInstance = PreInstance
  { piTrait :: !GName
  , piFvs :: ![Text] -- ^ implicitly-universalized head variables (§11.3.3)
  , piPremTms :: ![Term] -- ^ premise types, elaborated under 'piFvs'
  , piArgTms :: ![Term] -- ^ head arguments, under 'piFvs' + premises
  , piDictG :: !GName -- ^ the dictionary global (type already registered)
  }

data CheckState = CheckState
  { csGlobals :: !(Map GName GlobalDef)
  , csDatas :: !(Map GName DataInfo)
  , csCtors :: !(Map GName CtorInfo)
  , csTraits :: !(Map GName TraitInfo)
  , csInstances :: ![InstanceEntry]
  , csMetas :: !MetaState
  , csNextMeta :: !Int
  , csDiags :: !Diagnostics
  , csModule :: !ModuleName
  , csScope :: !(Map Text GName) -- ^ unqualified import scope
  , csModuleAliases :: !(Map Text ModuleName)
  , csModuleExports :: !(Map ModuleName [Text])
  , csFresh :: !Int
  , csPending :: ![(MetaId, Value, Span, Ctx, [(Value, Bool)])]
  -- ^ postponed implicit goals with the local context they were raised
  -- in (premise dictionaries live there, §14.3.2) and the boolean
  -- branch facts active at the raise site
  , csScopeAmbig :: !(Map Text [GName])
  -- ^ §7.1 names provided ambiguously by several wildcard imports
  , csExpects :: !(Map GName (Span, Int))
  -- ^ §9.4 expect declarations: span and number of satisfiers seen
  , csSigPending :: !(Map GName Span)
  -- ^ §9.1 top-level signatures not yet satisfied in this file
  , csManifest :: !(Map GName ())
  -- ^ §2.8.4 manifest bindings (no widening signature): reified
  -- static-object identity is preserved through them
  , csActive :: !(Map GName APInfo)
  -- ^ §17.3 active-pattern definitions and their result classification
  , csFacts :: !(Map Int RigidFact)
  -- ^ Branch-local dependent-match facts about rigid levels (§7.4.1),
  -- consulted by conversion-time match reduction
  , csProjections :: !(Map GName ProjInfo)
  -- ^ §9.1.1 projection definitions: binder structure for the
  -- projection facet at application sites
  , csDemand :: !PlaceDemand
  -- ^ surrounding place demand of the expression being elaborated
  -- (selects the §16.1.5/§16.1.6 eliminator and accessor capability)
  , csThis :: !(Maybe ThisMode)
  -- ^ §13.2.1 sibling-reference scope: what @this@ denotes inside a
  -- dependent record type, literal, or update being elaborated
  , csArgIndexRetag :: !Bool
  -- ^ §16.1.8: inside explicit-argument checking, a same-head indexed
  -- type mismatch reports E_APPLICATION_ARGUMENT_MISMATCH (a failed
  -- transport at an application boundary)
  , csReceivers :: !(Map GName [Int])
  -- ^ §7.4 receiver-marked explicit binder positions (indices among
  -- the explicit binders) per global, for method-call sugar
  , csExpansions :: !(Map Span Expr)
  -- ^ §21.2 splice expansions (splice span ↦ grafted surface syntax,
  -- with captured occurrences under their original spellings) for the
  -- usage analysis to charge object-level uses at splice sites
  , csOpaqueDatas :: !(Map GName ())
  -- ^ §10 'opaque data' declarations: representation visible only in
  -- the defining module (consulted by §22.1 shape inspection)
  , csRecordOrders :: !(Map GName [Text])
  -- ^ Written field order of record type aliases (§22.2 shape order;
  -- core record types are canonicalized to lexicographic order)
  , csReExports :: !(Map ModuleName (Map Text GName))
  -- ^ §8.4 re-exports: per module, exported spelling ↦ the originating
  -- declaration in another module (aliased and kind-selected items)
  , csBoolFacts :: ![(Value, Bool)]
  -- ^ boolean branch refinement: `if c …` makes `c = True` available
  -- in the then-branch and `c = False` in the else-branch as equality
  -- evidence (a §3.2.3 proof source; branch facts in the §15.6 sense)
  , csArgFlatOk :: !Bool
  -- ^ the current application's head is a plain function reference
  -- (not a constructor, not an operator): a flat argument mismatch may
  -- be reported as E_APPLICATION_ARGUMENT_MISMATCH (§16.1.7.1)
  , csPreInstances :: !(Map Span (Maybe PreInstance))
  -- ^ instance heads registered by the §14.3 pre-pass, keyed by the
  -- declaration span ('Nothing' records a head already rejected there,
  -- so the body pass does not re-report it)
  , csPositivity :: !(Map GName [Bool])
  -- ^ §10.4 parameter-positivity signatures: for each accepted data
  -- type (and each strictly-positive built-in/imported abstract type
  -- carrier whose interface declares a signature), one flag per
  -- parameter marking it positive ('True') or non-positive ('False').
  -- Consulted by the strict-positivity check when deciding whether an
  -- application 'F A1 .. An' keeps the defined type in a strictly
  -- positive position.
  , csDeclSites :: !(Map GName Span)
  -- ^ §3.1.1A: the source span where each module-scope name was first
  -- declared, so a duplicate-declaration diagnostic can cite both sites
  -- as related origins (declaration-site of the original).
  , csMultiFixOps :: !(Set Text)
  -- ^ §5.5.1: operator spellings that have more than one callable fixity
  -- in scope for this module (e.g. the prelude `-`, which is both
  -- `infix left 60` and `prefix 80`). A bare `(op)` reference whose
  -- expected type does not select exactly one fixity is ambiguous.
  , csUnsafe :: !UnsafeConfig
  -- ^ §4.2 build-level gating: which unsafe/debug facilities the build
  -- configuration permits. Defaults to all-disabled (package mode).
  , csAuditLedger :: ![AuditRecord]
  -- ^ §4.7 unsafe/debug audit ledger: one record per accepted use of an
  -- unsafe/debug facility, in source order.
  , csScopeNameCache :: !(Maybe (Map Int (Set Text)))
  -- ^ §3.2.2 typo-suggestion candidate index: the module-level in-scope
  -- names (import scope + this module's own globals) bucketed by spelling
  -- length. A single dropped import can leave thousands of references
  -- unresolved, each raising a suggestion diagnostic; rebuilding and
  -- rescanning the whole scope per diagnostic is O(Nerrors * Nscope).
  , csBackendIntrinsics :: !(Map Text Term)
  -- ^ §34.5/§34.5.3 general hook: bare-name backend intrinsics (spelling ↦
  -- expected Core type) that satisfy a §9.4 'expect term' up to defeq. This
  -- is now ALWAYS seeded empty: native host bindings are supplied as
  -- @host.native.*@ modules selected by a build manifest (§8.3.5/§36.28)
  -- and satisfied by ordinary import resolution, not by a bare-name table.
  -- A bare foreign 'expect' therefore has no native provider and is
  -- honestly unsatisfied (E_EXPECT_UNSATISFIED). The hook is retained as an
  -- inert, backend-agnostic seam; see docs/BUILD_AND_NATIVE_BINDINGS.md.
  , csCoreBodies :: !(Map GName Term)
  -- ^ Elaborated KCore body of each top-level term definition, captured
  -- before evaluation to a value. The native backend (Kappa.Backend.C)
  -- lowers these to C: re-deriving a body by 'quote'-ing the stored NbE
  -- 'gdValue' is unsound for do-blocks and suspensions that close over
  -- 'let'/argument bindings (quote drops the captured environment), so we
  -- keep the real elaborator output. Used only by the native backend; the
  -- interpreter path ignores it.
  -- The index is built once (lazily, on the first unresolved name) and
  -- then extended in 'addGlobal' as new module globals appear, so the
  -- build is paid once. Because Levenshtein distance is at least the
  -- length difference, an unresolved name of length L need only consult
  -- the buckets within the suggestion threshold of L, bounding the
  -- per-error scan to the length-compatible names rather than all of
  -- scope. 'Nothing' means "not yet built"; entering a new module clears
  -- it (Pipeline / TestHarness), since the import scope and module change.
  , csModEffLabels :: !(Map Text EffLabelInfo)
  -- ^ §18.1: module-level (top-level) @effect@ declarations, keyed by name.
  -- Unlike §9.3.1.1 @scoped effect@ (which lives in 'ctxEffLabels'), a
  -- top-level effect is visible to every definition in the module; effect
  -- resolution consults this as a fallback to 'ctxEffLabels'.
  }

-- | §4.2 build-level gating record. Each flag enables exactly one
-- unsafe/debug facility; all default to 'False' (package mode, §4.2).
data UnsafeConfig = UnsafeConfig
  { allowUnhiding :: !Bool
  , allowClarify :: !Bool
  , allowAssertTerminates :: !Bool
  , allowAssertReducible :: !Bool
  , allowUnsafeAssertProof :: !Bool
  , allowDebugIntrospection :: !Bool
  }
  deriving stock (Eq, Show)

-- | The default build configuration: every unsafe/debug facility is
-- disabled (§4.2 package-mode defaults).
defaultUnsafeConfig :: UnsafeConfig
defaultUnsafeConfig = UnsafeConfig False False False False False False

-- | §4.2: in script mode implementations MAY default the unsafe/debug
-- settings to @true@ for experimentation. This implementation does so,
-- so scripts can use the escapes without per-build flags.
scriptUnsafeConfig :: UnsafeConfig
scriptUnsafeConfig = UnsafeConfig True True True True True True

-- | §4.7 one audit-ledger entry: the facility used, the module and origin
-- it occurred in, the build setting that permitted it, and an optional
-- reason string supplied by the source form.
data AuditRecord = AuditRecord
  { arFacility :: !Text -- ^ e.g. "unhide", "assertReducible", "unsafeAssertProof"
  , arModule :: !ModuleName
  , arOrigin :: !Span
  , arAffected :: !Text -- ^ declaration / import item identity affected
  , arBuildSetting :: !Text -- ^ the §4.2 allow_* setting that permitted it
  , arReason :: !(Maybe Text) -- ^ structured reason string, when supplied
  }
  deriving stock (Eq, Show)

-- | What @this.label@ resolves to (§13.2.1): inside a record type,
-- the telescope prefix elaborated so far; inside a record literal or
-- update, the sibling field values already elaborated.
data ThisMode
  = ThisType ![(Text, Value)]
  | ThisValue ![(Text, Term)] ![(Text, Value)]
  | ThisTraitSibs ![(Text, Value)]
  -- ^ trait-body member scope: like 'ThisType', but sibling members
  -- shadow same-spelling globals (§14.2.1: "Inside the trait body,
  -- Item refers to the associated static member of the current trait
  -- evidence")

-- | §16.1.5/§16.1.6 surrounding demand at a descriptor application.
data PlaceDemand = DemandRead | DemandConsume | DemandOpen
  deriving stock (Eq, Show)

-- | §9.1.1 projection-facet metadata (one entry per declared name).
data ProjInfo = ProjInfo
  { pjIsPlace :: ![Bool] -- ^ per explicit binder, declaration order
  , pjPlaceNames :: ![Text] -- ^ place binder names, declaration order
  , pjSelector :: !Bool -- ^ selector form (vs expanded accessor form)
  , pjYields :: ![(Text, [Text])] -- ^ selector yield places: root binder, path
  }

-- | Active-pattern result classification (§17.3.1).
data APResult = APOption | APMatch | APTotal
  deriving stock (Eq, Show)

newtype APInfo = APInfo
  { apResult :: APResult
  }

initCheckState :: CheckState
initCheckState =
  CheckState Map.empty Map.empty Map.empty Map.empty [] emptyMetas 0 []
    (ModuleName ["main"]) Map.empty Map.empty Map.empty 0 [] Map.empty Map.empty Map.empty
    Map.empty Map.empty Map.empty Map.empty DemandRead Nothing False Map.empty
    Map.empty Map.empty Map.empty Map.empty [] False Map.empty
    Map.empty Map.empty Set.empty defaultUnsafeConfig [] Nothing
    Map.empty Map.empty Map.empty

preludeModule :: ModuleName
preludeModule = ModuleName ["std", "prelude"]

-- | The §22 derivation-shape reflection module.
shapeModule :: ModuleName
shapeModule = ModuleName ["std", "deriving", "shape"]

gPrel :: Text -> GName
gPrel = GName preludeModule

type CheckM = State CheckState

-- local context
data CtxEntry = CtxEntry
  { ceName :: !Text
  , ceType :: !Value
  , ceImplicitLocal :: !Bool
  , ceVarBind :: !Bool
  -- ^ Introduced by @var@ (§18.6.1): reads auto-dereference.
  , ceQ :: !(Maybe S.Quantity)
  -- ^ Quantity prefix of an implicit local binder (§16.3.3).
  , ceBorrow :: !Bool
  -- ^ @\@&@-marked implicit local: may not escape into closures.
  , ceOrigin :: !Span
  -- ^ §3.1.1A binder origin: the source span where this entry was
  -- introduced, so a borrow/ownership diagnostic about it can cite its
  -- introduction site. 'noSpan' when the introduction is untracked for
  -- this binder kind.
  }

data Ctx = Ctx
  { ctxEntries :: ![CtxEntry]
  , ctxEnv :: !Env
  , ctxRefines :: !(Map Text [GName])
  -- ^ §7.4.1 flow refinement: variable → possible constructors.
  , ctxAliases :: !(Map Text Text)
  -- ^ §7.4.3 stable aliases: @let q = p@ makes q transport p's refinement.
  , ctxBarriers :: ![Int]
  -- ^ Context lengths at which lambda bodies began (closure
  -- boundaries for §16.3.3 borrow-escape and scope grouping).
  , ctxEffLabels :: !(Map Text EffLabelInfo)
  -- ^ Lexically scoped effect labels (§9.3.1.1 @scoped effect@).
  , ctxInDo :: !Bool
  -- ^ Inside a @do@ elaboration: gates the §18.9.3 @~@ marker.
  , ctxHyg :: !(Map Text (Int, Value))
  -- ^ §21.4 hygienic capture references in spliced syntax: fresh
  -- spelling ↦ (binding LEVEL in this context, binder type).
  , ctxQuoteSlots :: !(Map Int Value)
  -- ^ Types of the enclosing quote's grafting slots ('EQuoteHole'),
  -- while the quote payload is being checked (§21.1).
  , ctxCodeDepth :: !Int
  -- ^ Nesting depth of enclosing §23.2 code quotes ('.~' is only
  -- meaningful inside one).
  , ctxReturnTarget :: !(Maybe Text)
  -- ^ §18.5: name/label of the innermost enclosing return target — a named
  -- function/method, an inherited-name lambda, or a labeled lambda. A
  -- @return@L@ resolves only when @L@ matches this (resolution does not
  -- cross user-written lambda boundaries); an anonymous lambda resets it to
  -- Nothing (nothing outside is reachable across it).
  }

-- | A scoped effect's elaborated interface (§9.3.1.1, §18.1.15): label
-- identity, interface-type identity, and operation metadata.
data EffLabelInfo = EffLabelInfo
  { eliLabel :: !GName -- ^ effect-label value identity (§18.1.18)
  , eliIface :: !GName -- ^ effect-interface type constructor
  , eliParams :: ![(Text, Term)]
  -- ^ §18.1.15 effect type parameters (outermost-first; each kind 'Term' is
  -- de Bruijn under the preceding parameters). Empty for an unparameterized
  -- effect; non-empty for e.g. @effect State (s : Type)@.
  , eliOps :: ![EffOpInfo]
  }

data EffOpInfo = EffOpInfo
  { eoiName :: !Text
  , eoiQ :: !Q -- ^ declared resumption quantity (§18.1.16)
  , eoiImplicits :: ![(Text, Term)]
  -- ^ §18.1.15: the operation's own implicit (forall-bound) parameters
  -- (e.g. @op : forall a. a -> a@), name + kind, de Bruijn under the effect's
  -- parameters then the preceding op-implicits. Universally quantified per
  -- operation: instantiated fresh at each call and treated as skolems in the
  -- handler clause.
  , eoiArgsT :: ![Term]
  -- ^ §18.1.21: the operation's explicit parameter types @A₁ … Aₙ@ (an
  -- operation @op : Π(x₁:A₁)…(xₙ:Aₙ). B@ has @n@ arguments), each de Bruijn
  -- under the effect's parameters THEN the op-implicits. Non-empty.
  , eoiResT :: !Term -- ^ the final result type @B@, de Bruijn under params + op-implicits
  }

emptyCtx :: Ctx
emptyCtx = Ctx [] [] Map.empty Map.empty [] Map.empty False Map.empty Map.empty 0 Nothing

ctxLen :: Ctx -> Int
ctxLen = length . ctxEntries

-- | Mark a closure boundary: entries below it are captured (§16.2.1).
pushCtxBarrier :: Ctx -> Ctx
pushCtxBarrier ctx = ctx {ctxBarriers = ctxLen ctx : ctxBarriers ctx}

-- | Shared binder scaffold: prepend @entry@, push @v@ onto the
-- environment, and drop any prior flow-refinement/alias facts about the
-- binder's name (a fresh binder shadows them). All three @bindCtx*@
-- helpers differ only in the entry's flags and the environment value.
bindEntry :: CtxEntry -> Value -> Ctx -> Ctx
bindEntry entry v ctx =
  ctx
    { ctxEntries = entry : ctxEntries ctx
    , ctxEnv = v : ctxEnv ctx
    , ctxRefines = Map.delete (ceName entry) (ctxRefines ctx)
    , ctxAliases = Map.delete (ceName entry) (ctxAliases ctx)
    }

bindCtx :: Text -> Bool -> Value -> Ctx -> Ctx
bindCtx n implocal ty ctx =
  bindEntry (CtxEntry n ty implocal False Nothing False noSpan) (VRigid (length (ctxEnv ctx)) []) ctx

-- | Bind a local definition: the environment carries the definiens, so
-- conversion sees through local lets (delta for locals, §15.1).
bindCtxLet :: Text -> Bool -> Value -> Value -> Ctx -> Ctx
bindCtxLet n implocal ty v ctx =
  bindEntry (CtxEntry n ty implocal False Nothing False noSpan) v ctx

-- | Bind a @var@ cell (type @Ref a@); uses read through it (§18.6.1).
bindCtxVar :: Text -> Value -> Ctx -> Ctx
bindCtxVar n ty ctx =
  bindEntry (CtxEntry n ty False True Nothing False noSpan) (VRigid (length (ctxEnv ctx)) []) ctx

-- | Record the implicit binder prefix on the most recent entry
-- (quantity and borrow marker, §16.3.3). @binderSp@ is the binder's
-- source span; when the prefix marks a borrow (@\@&@) it is recorded as
-- the entry's §3.1.1A introduction origin so a later borrow-escape
-- diagnostic about this candidate can cite where it was borrowed.
setTopPrefix :: Span -> BinderPrefix -> Ctx -> Ctx
setTopPrefix binderSp (BinderPrefix mq mb) ctx = case ctxEntries ctx of
  (e : rest) ->
    ctx
      { ctxEntries =
          e
            { ceQ = mq
            , ceBorrow = isJust mb
            , ceOrigin = if isJust mb then binderSp else ceOrigin e
            }
            : rest
      }
  [] -> ctx

-- | The §7.4.3 stable-alias root of a variable.
refineRoot :: Ctx -> Text -> Text
refineRoot ctx = go (16 :: Int)
  where
    go 0 n = n
    go fuel n = case Map.lookup n (ctxAliases ctx) of
      Just n' -> go (fuel - 1) n'
      Nothing -> n

-- | Record §7.4.1 refinements (through alias roots).
refineCtx :: [(Text, [GName])] -> Ctx -> Ctx
refineCtx refs ctx =
  ctx {ctxRefines = foldr add (ctxRefines ctx) refs}
  where
    add (n, gs) = Map.insert (refineRoot ctx n) gs

-- | Record a stable alias @q = p@ (§7.4.3).
addCtxAlias :: Text -> Text -> Ctx -> Ctx
addCtxAlias q p ctx = ctx {ctxAliases = Map.insert q p (ctxAliases ctx)}

-- | Current refinement of a variable, through its alias root.
ctxRefinementOf :: Ctx -> Text -> Maybe [GName]
ctxRefinementOf ctx n = Map.lookup (refineRoot ctx n) (ctxRefines ctx)

lookupCtx :: Text -> Ctx -> Maybe (Int, CtxEntry)
lookupCtx n ctx = go 0 (ctxEntries ctx)
  where
    go _ [] = Nothing
    go i (e : rest)
      | ceName e == n = Just (i, e)
      | otherwise = go (i + 1) rest

ec_ :: CheckM EvalCtx
ec_ = gets (\st -> EvalCtx (Globals (csGlobals st)) (csMetas st) False (csFacts st))

evalIn :: Ctx -> Term -> CheckM Value
evalIn ctx t = do
  ec <- ec_
  pure (eval ec (ctxEnv ctx) t)

quoteIn :: Ctx -> Value -> CheckM Term
quoteIn ctx v = do
  ec <- ec_
  pure (quote ec (ctxLen ctx) v)

forceM :: Value -> CheckM Value
forceM v = do
  ec <- ec_
  pure (force ec v)

clApp :: Closure -> Value -> CheckM Value
clApp (Closure env body) v = do
  ec <- ec_
  pure (eval ec (v : env) body)

-- | Record a diagnostic. Diagnostics accumulate in reverse (prepend)
-- order; 'checkModule' restores source order once at the end.
report :: Diagnostic -> CheckM ()
report d = modify' $ \st -> st {csDiags = d : csDiags st}

-- | Run an action under a given §16.1.5 place demand, restoring the
-- ambient demand afterwards.
withDemand :: PlaceDemand -> CheckM a -> CheckM a
withDemand d act = do
  old <- gets csDemand
  modify' $ \st -> st {csDemand = d}
  r <- act
  modify' $ \st -> st {csDemand = old}
  pure r

demandOfQ :: Q -> PlaceDemand
demandOfQ q
  | q `elem` [Q1, QGe1] = DemandConsume
  | otherwise = DemandRead

-- | Run an action with @this@ denoting the given §13.2.1 sibling scope.
withThis :: Maybe ThisMode -> CheckM a -> CheckM a
withThis tm act = do
  old <- gets csThis
  modify' $ \st -> st {csThis = tm}
  r <- act
  modify' $ \st -> st {csThis = old}
  pure r

-- | The neutral standing for the record under §13.2.1 elaboration.
thisG :: GName
thisG = gPrel "__this"

-- | §13.2.11 internal existential member labels. The angle-bracket
-- sigil cannot occur in a source identifier (the lexer admits only
-- @[A-Za-z0-9_]@ and non-ASCII letters), so these labels are never
-- source-addressable through @EProj@/@elabDot@ — exactly the spec's
-- requirement that witness members and a non-record payload "are not
-- source-addressable and not rendered as a public field" (Spec.md
-- 13314, 13316-13317). The labels are position-based so that
-- alpha-equivalent existential types elaborate to the same internal
-- shape and remain convertible (Spec.md 13322).
existsWitLabel :: Int -> Text
existsWitLabel i = "⟨wit" <> T.pack (show i) <> "⟩"

-- | The single anonymous non-record payload label of an existential
-- (Spec.md 13316-13317: @⟨payload⟩ : T@, not a field named @value@).
existsPayloadLabel :: Text
existsPayloadLabel = "⟨payload⟩"

-- | Whether a member label is a §13.2.11 internal existential label
-- (witness or anonymous payload). Such labels are not source-visible
-- projection fields.
isExistsInternalLabel :: Text -> Bool
isExistsInternalLabel l = "⟨" `T.isPrefixOf` l

-- | Does a term mention the §13.2.1 @this@ neutral?
mentionsThis :: Term -> Bool
mentionsThis = \case
  CGlob g -> g == thisG
  CVar _ -> False
  CLam _ _ _ b -> mentionsThis b
  CPi _ _ _ a b -> mentionsThis a || mentionsThis b
  CApp _ f a -> mentionsThis f || mentionsThis a
  CSort _ -> False
  CLit _ -> False
  CCtor _ as -> any mentionsThis as
  CMatch s alts ->
    mentionsThis s
      || or [maybe False mentionsThis g || mentionsThis b | CaseAlt _ g b <- alts]
  CRecordT fs -> any (mentionsThis . snd) fs
  CRecordV fs -> any (mentionsThis . snd) fs
  CProj e _ -> mentionsThis e
  CProjAt e _ _ -> mentionsThis e
  CVariantT ms -> any mentionsThis ms
  CInject _ e -> mentionsThis e
  CLet _ _ a b c -> mentionsThis a || mentionsThis b || mentionsThis c
  CLetRec _ _ a b c -> mentionsThis a || mentionsThis b || mentionsThis c
  CMeta _ -> False
  CDo _ _ -> False
  CSealE _ e -> mentionsThis e
  CSigT _ e -> mentionsThis e
  CThunkE e -> mentionsThis e
  CLazyE e -> mentionsThis e
  CForceE e -> mentionsThis e
  CIf a b c -> mentionsThis a || mentionsThis b || mentionsThis c
  CQuote _ slots -> any mentionsThis slots

-- | The sibling field labels a §13.2.1 field type depends on.
thisDepsOf :: Term -> [Text]
thisDepsOf = nub . go
  where
    go = \case
      CProj e f
        | CGlob g <- e, g == thisG -> [f]
        | otherwise -> go e
      CProjAt e f _
        | CGlob g <- e, g == thisG -> [f]
        | otherwise -> go e
      CGlob _ -> []
      CVar _ -> []
      CLam _ _ _ b -> go b
      CPi _ _ _ a b -> go a ++ go b
      CApp _ f a -> go f ++ go a
      CSort _ -> []
      CLit _ -> []
      CCtor _ as -> concatMap go as
      CMatch s alts -> go s ++ concat [maybe [] go g ++ go b | CaseAlt _ g b <- alts]
      CRecordT fs -> concatMap (go . snd) fs
      CRecordV fs -> concatMap (go . snd) fs
      CVariantT ms -> concatMap go ms
      CInject _ e -> go e
      CLet _ _ a b c -> go a ++ go b ++ go c
      CLetRec _ _ a b c -> go a ++ go b ++ go c
      CMeta _ -> []
      CDo _ _ -> []
      CSealE _ e -> go e
      CSigT _ e -> go e
      CThunkE e -> go e
      CLazyE e -> go e
      CForceE e -> go e
      CIf a b c -> go a ++ go b ++ go c
      CQuote _ slots -> concatMap go slots

-- | Substitute a receiver term (well-scoped at the substitution site)
-- for the §13.2.1 @this@ neutral, shifting under binders.
substThisTm :: Term -> Term -> Term
substThisTm recv = go 0
  where
    go d t = case t of
      CGlob g | g == thisG -> shiftTerm d 0 recv
      CGlob _ -> t
      CVar _ -> t
      CLam ic q n b -> CLam ic q n (go (d + 1) b)
      CPi ic q n a b -> CPi ic q n (go d a) (go (d + 1) b)
      CApp ic f a -> CApp ic (go d f) (go d a)
      CSort _ -> t
      CLit _ -> t
      CCtor g as -> CCtor g (map (go d) as)
      CMatch s alts ->
        CMatch (go d s)
          [CaseAlt p (fmap (go (d + patBindersC p)) g) (go (d + patBindersC p) b) | CaseAlt p g b <- alts]
      CRecordT fs -> CRecordT [(n, go d x) | (n, x) <- fs]
      CRecordV fs -> CRecordV [(n, go d x) | (n, x) <- fs]
      CProj e f -> CProj (go d e) f
      CProjAt e f i -> CProjAt (go d e) f i
      CVariantT ms -> CVariantT (map (go d) ms)
      CInject tag e -> CInject tag (go d e)
      CLet q n a b c -> CLet q n (go d a) (go d b) (go (d + 1) c)
      CLetRec q n a b c -> CLetRec q n (go d a) (go (d + 1) b) (go (d + 1) c)
      CMeta _ -> t
      CDo _ _ -> t
      CSealE ls e -> CSealE ls (go d e)
      CSigT ls e -> CSigT ls (go d e)
      CThunkE e -> CThunkE (go d e)
      CLazyE e -> CLazyE (go d e)
      CForceE e -> CForceE (go d e)
      CIf a b c -> CIf (go d a) (go d b) (go d c)
      CQuote qs slots -> CQuote qs (map (go d) slots)

-- | Substitute a receiver term for @this@ inside a field-type value
-- (§13.2.1 dependent projection).
substThisInto :: Ctx -> Term -> Value -> CheckM Value
substThisInto ctx recv fty = do
  ftyTm <- quoteIn ctx fty
  if mentionsThis ftyTm
    then evalIn ctx (substThisTm recv ftyTm)
    else pure fty

-- | Does any field type of the record mention @this@?
recordTypeIsDependent :: Ctx -> [(Text, Value)] -> CheckM Bool
recordTypeIsDependent ctx fs =
  or <$> mapM (fmap mentionsThis . quoteIn ctx . snd) fs

-- | Topologically sort labelled items by their dependency labels;
-- 'Nothing' on a cycle.
topoFields :: [(Text, [Text], a)] -> Maybe [a]
topoFields = goT []
  where
    goT _ [] = Just []
    goT doneLs pending =
      case [x | x@(_, ds, _) <- pending, all (`elem` doneLs) ds] of
        [] -> Nothing
        ready -> do
          let readyLs = [l | (l, _, _) <- ready]
              rest = [x | x@(l, _, _) <- pending, l `notElem` readyLs]
          ((map (\(_, _, a) -> a) ready) ++) <$> goT (doneLs ++ readyLs) rest

-- | Report a diagnostic unless an identical (code, message) one was
-- already reported — for judgements re-checked once per occurrence of
-- the same source type (e.g. a signature and its definition binders).
errOnce :: Span -> DiagnosticCode -> Maybe DiagnosticFamily -> Text -> CheckM ()
errOnce sp code fam msg = do
  ds <- gets csDiags
  unless (any (\d -> dCode d == code && dMessage d == msg) ds) $
    errAt sp code fam msg

-- | Like 'errOnce', but distinct origins each report (one diagnostic
-- per malformed source construct, not per judgement).
errOncePerSpan :: Span -> DiagnosticCode -> Maybe DiagnosticFamily -> Text -> CheckM ()
errOncePerSpan sp code fam msg = do
  ds <- gets csDiags
  unless (any (\d -> dCode d == code && dMessage d == msg && dPrimary d == sp) ds) $
    errAt sp code fam msg

errAt :: Span -> DiagnosticCode -> Maybe DiagnosticFamily -> Text -> CheckM ()
errAt sp code fam msg = report (diag SevError StageElaborate code fam sp msg)

-- | §3 @kappa.unsupported.deterministic@ payload: the family REQUIRES the
-- diagnostic to carry the unsupported action, the selected language profile,
-- and whether source analysis continued (plus a backend profile / required
-- capability when those are relevant — these v1 restrictions are
-- elaboration-level with no owning capability gate, so those fields are
-- recorded as not-applicable). Source analysis continues: the error is
-- collected and the rest of the unit is still checked.
unsupportedPayload :: Text -> Payload
unsupportedPayload action =
  withPayloadField "unsupportedAction" action
    $ withPayloadField "languageProfile" "default"
    $ withPayloadField "backendProfile" "n/a"
    $ withPayloadField "requiredCapability" "none"
    $ withPayloadField "sourceAnalysisContinued" "true"
    $ payloadKind "unsupported-deterministic"

-- | Emit a deterministic-unsupported diagnostic (§3.x family
-- @kappa.unsupported.deterministic@) carrying the mandated payload.
unsupportedAt :: Span -> Text -> CheckM ()
unsupportedAt sp msg =
  report
    ( withPayload (unsupportedPayload msg)
        (diag SevError StageElaborate "E_UNSUPPORTED" (Just "kappa.unsupported.deterministic") sp msg)
    )

-- | Allocate a fresh, unsolved metavariable and return its raw id.
freshMetaId :: CheckM MetaId
freshMetaId = do
  st <- get
  let m = csNextMeta st
  put st {csNextMeta = m + 1, csMetas = Map.insert m Nothing (csMetas st)}
  pure m

freshMeta :: CheckM Term
freshMeta = CMeta <$> freshMetaId

freshMetaV :: Ctx -> CheckM Value
freshMetaV ctx = freshMeta >>= evalIn ctx

solveMeta :: MetaId -> Value -> CheckM ()
solveMeta m v = modify' $ \st -> st {csMetas = Map.insert m (Just v) (csMetas st)}

freshNameM :: Text -> CheckM Text
freshNameM base = do
  st <- get
  put st {csFresh = csFresh st + 1}
  pure (base <> T.pack (show (csFresh st)))

addGlobal :: GName -> GlobalDef -> CheckM ()
addGlobal g@(GName m nm) gd = modify' $ \st ->
  st
    { csGlobals = Map.insert g gd (csGlobals st)
    , -- Keep the §3.2.2 typo-suggestion index (if already built) in step
      -- with the module's own globals, so it never needs a full rebuild
      -- (see 'moduleScopeNameIndex'). Names from other modules are not
      -- unqualified-in-scope here, so only this module's globals extend it.
      csScopeNameCache =
        if m == csModule st
          then fmap (insertScopeName nm) (csScopeNameCache st)
          else csScopeNameCache st
    }

-- | Add one spelling to the length-bucketed §3.2.2 candidate index.
insertScopeName :: Text -> Map Int (Set Text) -> Map Int (Set Text)
insertScopeName nm = Map.insertWith Set.union (T.length nm) (Set.singleton nm)

-- | Record the elaborated KCore body of a top-level term definition for
-- the native backend (see 'csCoreBodies'). Called from 'elabLetDecl'
-- after zonking, with the body the interpreter would evaluate.
recordCoreBody :: GName -> Term -> CheckM ()
recordCoreBody g tm =
  modify' $ \st -> st {csCoreBodies = Map.insert g tm (csCoreBodies st)}

-- | §3.1.1A: record the first declaration site of a module-scope name
-- (later occurrences keep the earliest span). Consulted by the
-- duplicate-declaration diagnostic to cite the original site.
recordDeclSite :: GName -> Span -> CheckM ()
recordDeclSite g sp =
  modify' $ \st -> st {csDeclSites = Map.insertWith (\_ old -> old) g sp (csDeclSites st)}

-- | §3.1.1A duplicate-declaration related origins: the new (rejected)
-- declaration site as @declaration-site@, plus the original declaration
-- site (when recorded) as a second @declaration-site@. Both sites MUST
-- appear (§3.1.1A: "duplicate-declaration diagnostics MUST include both
-- sites"). Also attaches the §3.2.2 name payload.
duplicateRelated :: Text -> GName -> Span -> CheckM (Diagnostic -> Diagnostic)
duplicateRelated nm g sp = do
  mPrior <- gets (Map.lookup g . csDeclSites)
  let payload =
        withPayloadField "name" nm $
          payloadKind "name-duplicate"
      newSite = related RoleDeclarationSite sp ("redeclaration of '" <> nm <> "'")
      priorSite = case mPrior of
        Just psp | psp /= sp -> [related RoleDeclarationSite psp ("'" <> nm <> "' first declared here")]
        _ -> []
  pure (withPayload payload . withRelateds (newSite : priorSite))

-- ── Unification ──────────────────────────────────────────────────────

-- | Pi binder-quantity subsumption (§12.2.1): a function whose demand
-- interval is contained in the expected binder's demand may stand at
-- that type — every argument capability satisfying the expected demand
-- also satisfies the actual one (e.g. a @(1 x : A) -> B@ value may be
-- used where @(x : A) -> B@ is expected, but not vice versa).
qSubsumes :: Q -> Q -> Bool
qSubsumes qa qe = qa == qe || qInterval qa `contained` qInterval qe
  where
    qInterval :: Q -> (Int, Maybe Int)
    qInterval = \case
      Q0 -> (0, Just 0)
      Q1 -> (1, Just 1)
      QLe1 -> (0, Just 1)
      QGe1 -> (1, Nothing)
      QW -> (0, Nothing)
    contained (lo1, hi1) (lo2, hi2) =
      lo1 >= lo2 && case (hi1, hi2) of
        (_, Nothing) -> True
        (Nothing, Just _) -> False
        (Just h1, Just h2) -> h1 <= h2

unify :: Ctx -> Value -> Value -> CheckM Bool
unify ctx = goTop True
  where
    -- qok: §12.2.1 binder-quantity subsumption applies only along the
    -- outer Pi spine of the unified types, never under records, type
    -- arguments, or domains (no deep subsumption)
    goTop qok a b = do
      a' <- forceM a
      b' <- forceM b
      go qok (ctxLen ctx) a' b'
    go qok lvl a b = case (a, b) of
      (VFlex m [], t) -> solveFlex lvl m t
      (t, VFlex m []) -> solveFlex lvl m t
      -- applied metas: first-order decomposition (?m a̅ ≡ G b̅ pre a̅'
      -- solves ?m := G b̅ pre and unifies the argument tails pairwise) —
      -- the standard Miller-adjacent approximation for higher-kinded
      -- goals like ?f Int ≡ Option Int (§14.3.1)
      (VFlex m sp, t) | not (null sp) -> solveFlexSpine lvl m sp t
      (t, VFlex m sp) | not (null sp) -> solveFlexSpine lvl m sp t
      (VSort m, VSort n) -> pure (m <= n) -- cumulativity (§11.1.1)
      (VPi i1 q1 _ d1 c1, VPi i2 q2 _ d2 c2) | i1 == i2 && (q1 == q2 || (qok && qSubsumes q1 q2)) -> do
        ok <- goTop False d1 d2
        if not ok
          then pure False
          else do
            let x = VRigid lvl []
            b1 <- clApp c1 x
            b2 <- clApp c2 x
            b1' <- forceM b1
            b2' <- forceM b2
            go qok (lvl + 1) b1' b2'
      (VRecordT f1, VRecordT f2) | map fst f1 == map fst f2 ->
        andM [goTop False x y | ((_, x), (_, y)) <- zip f1 f2]
      -- §11.3.1A: an open record type meets a closed record type by
      -- matching the explicit prefix against the closed fields and
      -- instantiating the row tail with the leftover fields as a
      -- closed residual row
      (VGlobN (GName pm "__openRec") [(_, rowV), (_, prefixV)], VRecordT fs)
        | pm == preludeModule -> goOpenClosed lvl rowV prefixV fs
      (VRecordT fs, VGlobN (GName pm "__openRec") [(_, rowV), (_, prefixV)])
        | pm == preludeModule -> goOpenClosed lvl rowV prefixV fs
      -- §13.2.10: signature types are equal iff the opaque label sets
      -- and the underlying record types agree
      (VSigT l1 v1, VSigT l2 v2) | l1 == l2 -> goTop False v1 v2
      -- §13.2.10: seal is pure and non-generative (seal e as S ≡ e)
      (VSealV _ x, t) -> goTop qok x t
      (t, VSealV _ x) -> goTop qok t x
      (VVariantT m1, VVariantT m2) | length m1 == length m2 ->
        andM (zipWith (goTop False) m1 m2)
      (VCtor g1 a1, VCtor g2 a2) | g1 == g2 && length a1 == length a2 ->
        andM (zipWith (goTop False) a1 a2)
      (VGlobN g1 sp1, VGlobN g2 sp2)
        | g1 == g2 && length sp1 == length sp2 -> do
            ok <- andM (zipWith (\(_, x) (_, y) -> goTop False x y) sp1 sp2)
            if ok then pure True else fallback lvl a b
      -- rigid-rigid spine decomposition (incomplete but standard; the
      -- definitional-equality fallback still decides the rest)
      (VRigid l1 sp1, VRigid l2 sp2)
        | l1 == l2 && length sp1 == length sp2 && not (null sp1) -> do
            st0 <- get
            ok <- andM (zipWith (\(_, x) (_, y) -> goTop False x y) sp1 sp2)
            if ok then pure True else put st0 >> fallback lvl a b
      _ -> fallback lvl a b
      where
        andM [] = pure True
        andM (m : ms) = m >>= \ok -> if ok then andM ms else pure False
    -- split closed fields fs into the open record's explicit prefix
    -- and a '__closedRow' residual solving the row tail (§11.3.1A)
    goOpenClosed lvl rowV prefixV fs = do
      pf <- forceM prefixV
      case pf of
        VRecordT pfs
          | all ((`elem` map fst fs) . fst) pfs -> do
              okTys <- andAll [goTop False pv fv | (pl, pv) <- pfs, Just fv <- [lookup pl fs]]
              if not okTys
                then pure False
                else do
                  let rest = [f | f@(l, _) <- fs, l `notElem` map fst pfs]
                  goTop False rowV (VGlobN (gPrel "__closedRow") [(Expl, VRecordT rest)])
        _ -> fallback lvl (VGlobN (gPrel "__openRec") [(Expl, rowV), (Expl, prefixV)]) (VRecordT fs)
      where
        andAll [] = pure True
        andAll (m : ms) = m >>= \ok -> if ok then andAll ms else pure False
    fallback lvl a b = do
      ec <- ec_
      pure (convertible ec lvl a b)
    solveFlexSpine lvl m sp t = case t of
      VGlobN g sp2
        | length sp2 >= length sp -> do
            st0 <- get
            let (pre, post) = splitAt (length sp2 - length sp) sp2
            ok <- solveFlex lvl m (VGlobN g pre)
            oks <-
              if ok
                then andM' [goTop False x y | ((_, x), (_, y)) <- zip sp post]
                else pure False
            if oks then pure True else put st0 >> fallback lvl (VFlex m sp) t
      VRigid l sp2
        | length sp2 >= length sp -> do
            st0 <- get
            let (pre, post) = splitAt (length sp2 - length sp) sp2
            ok <- solveFlex lvl m (VRigid l pre)
            oks <-
              if ok
                then andM' [goTop False x y | ((_, x), (_, y)) <- zip sp post]
                else pure False
            if oks then pure True else put st0 >> fallback lvl (VFlex m sp) t
      VFlex m2 sp2
        | length sp2 == length sp -> do
            st0 <- get
            ok <- solveFlex lvl m (VFlex m2 [])
            oks <-
              if ok
                then andM' [goTop False x y | ((_, x), (_, y)) <- zip sp sp2]
                else pure False
            if oks then pure True else put st0 >> fallback lvl (VFlex m sp) t
      _ -> fallback lvl (VFlex m sp) t
      where
        andM' [] = pure True
        andM' (mx : ms) = mx >>= \ok -> if ok then andM' ms else pure False
    solveFlex lvl m t = do
      st <- get
      case Map.lookup m (csMetas st) of
        Just (Just sol) -> do
          sol' <- forceM sol
          t' <- forceM t
          go False lvl sol' t'
        _ -> case t of
          -- a meta is trivially equal to itself; the occurs check must
          -- not reject reflexive flex-flex problems
          VFlex m' [] | m' == m -> pure True
          _ -> do
            ec <- ec_
            let tm = quote ec lvl t
            if occursMeta m tm then pure False else solveMeta m t >> pure True

occursMeta :: MetaId -> Term -> Bool
occursMeta m = go
  where
    go = \case
      CMeta m' -> m == m'
      CApp _ f a -> go f || go a
      CLam _ _ _ b -> go b
      CPi _ _ _ a b -> go a || go b
      CCtor _ as -> any go as
      CMatch s alts -> go s || any (\(CaseAlt _ g b) -> maybe False go g || go b) alts
      CRecordT fs -> any (go . snd) fs
      CRecordV fs -> any (go . snd) fs
      CProj e _ -> go e
      CProjAt e _ _ -> go e
      CVariantT ms -> any go ms
      CInject _ e -> go e
      CLet _ _ a b c -> go a || go b || go c
      CLetRec _ _ a b c -> go a || go b || go c
      CIf a b c -> go a || go b || go c
      CThunkE e -> go e
      CLazyE e -> go e
      CForceE e -> go e
      _ -> False

-- | §3.1.9 expected/actual mismatch payload (the @kappa.type.mismatch@
-- family MUST expose it when both sides are available). The compact
-- rendered fragments are the user-facing renderings (already zonked and
-- metavar-hygienic, §3.1.11). The mismatch kind defaults to
-- @expression-type@ — the bare type-equality check shape (§3.1.9
-- ExpectedActualMismatchKind).
mismatchPayload :: Text -> Text -> Payload
mismatchPayload expectedR actualR =
  withPayloadField "expected" expectedR $
    withPayloadField "actual" actualR $
      withPayloadField "mismatchKind" "expression-type" $
        payloadKind "expected-actual"

-- | §18.1 effect-row subsumption (check direction): succeed when @actual@
-- and @expected@ are both Eff types whose result types unify and every
-- label in actual's row appears in expected's row with a unifiable
-- interface (so actual's effects ⊆ expected's). Restores state on failure.
tryEffRowSubsume :: Ctx -> Value -> Value -> CheckM Bool
tryEffRowSubsume ctx actual expected = do
  aF <- forceM actual
  eF <- forceM expected
  case (aF, eF) of
    (VGlobN (GName _ "Eff") [(_, aRow), (_, aRes)], VGlobN (GName _ "Eff") [(_, eRow), (_, eRes)]) -> do
      st0 <- get
      resOk <- unify ctx aRes eRes
      aEs <- rowEntriesV aRow
      eEs <- rowEntriesV eRow
      case (aEs, eEs) of
        (Just aEntries, Just eEntries) | resOk -> do
          oks <- forM aEntries $ \(al, ai) -> do
            ms <- forM eEntries $ \(el, ei) -> do
              le <- sameLabelV al el
              if le then unify ctx ai ei else pure False
            pure (or ms)
          if and oks then pure True else put st0 >> pure False
        _ -> put st0 >> pure False
    _ -> pure False

-- | The (label, interface) entries of a fully-concrete effect row (ending
-- in @__effRowNil@); Nothing if the row has a non-cons tail (e.g. a
-- metavariable), where this subsumption does not apply.
rowEntriesV :: Value -> CheckM (Maybe [(Value, Value)])
rowEntriesV row0 = do
  row <- forceM row0
  case row of
    VGlobN (GName _ "__effRowNil") [] -> pure (Just [])
    VGlobN (GName _ "__effRowCons") [(_, l), (_, e), (_, rest)] -> do
      mrest <- rowEntriesV rest
      pure (fmap ((l, e) :) mrest)
    _ -> pure Nothing

sameLabelV :: Value -> Value -> CheckM Bool
sameLabelV a b = do
  aF <- forceM a
  bF <- forceM b
  pure $ case (aF, bF) of
    (VGlobN g1 [], VGlobN g2 []) -> g1 == g2
    (VCtor g1 [], VCtor g2 []) -> g1 == g2
    _ -> False

expectType :: Ctx -> Span -> Value -> Value -> CheckM ()
expectType ctx sp actual expected = do
  ok <- unify ctx actual expected
  -- §18.1: effect-row subsumption. A computation whose effect row's labels
  -- are a SUBSET of the expected row's (with matching interfaces) is usable
  -- where the larger row is demanded — it simply does not use the extra
  -- effects. This is what lets an operation `l.op` (natural row `<[l:E]>`)
  -- and any single-effect sub-computation compose inside a do-block whose
  -- row carries several effects. The OpCall tree is row-agnostic at runtime,
  -- so the relaxation is purely at the type level (sound in the check
  -- direction). Tried only after exact unification fails.
  subsumed <- if ok then pure True else tryEffRowSubsume ctx actual expected
  unless subsumed $ do
    aT <- quoteIn ctx actual
    eT <- quoteIn ctx expected
    -- §13.2.10: a mismatch whose head is an opaque sealed-package
    -- member is an attempt to unfold a hidden defining equation
    aOp <- opaqueSealHead actual
    eOp <- opaqueSealHead expected
    -- §16.1.8: at an application boundary, a same-head indexed type
    -- mismatch is a failed transport — an application-argument error
    retag <- gets csArgIndexRetag
    sameHead <- do
      aF <- forceM actual
      eF <- forceM expected
      pure $ case (aF, eF) of
        (VGlobN g1 sp1, VGlobN g2 sp2) ->
          g1 == g2 && not (null sp1) && length sp1 == length sp2
        _ -> False
    -- §16.1.7.1: a mismatch while checking an explicit argument is an
    -- application-argument error when both sides are canonical
    -- non-function types (the argument simply does not fit the
    -- parameter); same-head indexed mismatches additionally cite the
    -- failed transport (§16.1.8).
    --
    -- The expected side must be a *nullary type former* (`VGlobN g []`):
    -- a saturated atomic type with no remaining indices. This is the
    -- §16.1.7.1 "argument does not satisfy the binder" shape. Structural
    -- record types (`VRecordT`) are deliberately excluded on the expected
    -- side: a record-into-record mismatch (e.g. passing a `RawDelayed`
    -- where a `Delayed` record is expected) is a §3.2.3 `kappa.type.mismatch`
    -- on structural type identity, not an argument-classifier failure — so
    -- it must keep its `E_TYPE_EQUALITY_MISMATCH` spelling. Widening this
    -- guard to admit records regresses that diagnostic, which is why the
    -- expected side is restricted to nullary `VGlobN` (any name, since the
    -- old fixed scalar-name list was not load-bearing).
    flatOk <- gets csArgFlatOk
    flatArgMismatch <- do
      if not retag || sameHead || not flatOk
        then pure False
        else do
          aF <- forceM actual
          eF <- forceM expected
          let canonical = \case
                VGlobN _ _ -> True
                VCtor _ _ -> True
                VRecordT _ -> True
                VSort _ -> True
                _ -> False
              nullaryExpected = case eF of
                VGlobN (GName _ _) [] -> True
                _ -> False
          pure (canonical aF && nullaryExpected)
    -- §16.1.7.1: a function value supplied at an explicit argument slot
    -- whose expected parameter type is itself a function type, where the
    -- two function types differ in the outermost explicit binder
    -- (quantity is part of function-type identity, §31.1/§12.2.1) — the
    -- argument simply does not fit the parameter, an
    -- application-argument error rather than a bare type equality.
    funcArgMismatch <- do
      if not retag || not flatOk
        then pure False
        else do
          aF <- forceM actual
          eF <- forceM expected
          pure $ case (aF, eF) of
            (VPi i1 _ _ _ _, VPi i2 _ _ _ _) -> i1 == i2
            _ -> False
    if not (aOp || eOp) && retag && sameHead
      then
        report $
          withNote ("expected: " <> renderTerm eT) $
            withNote ("actual:   " <> renderTerm aT) $
              diag SevError StageElaborate "E_APPLICATION_ARGUMENT_MISMATCH" (Just "kappa.application.argument-mismatch") sp
                "the supplied argument's type differs from the parameter type only in type indices, and no equality evidence licenses the transport (§16.1.8)"
      else if not (aOp || eOp) && (flatArgMismatch || funcArgMismatch)
        then
        report $
          withNote ("expected: " <> renderTerm eT) $
            withNote ("actual:   " <> renderTerm aT) $
              diag SevError StageElaborate "E_APPLICATION_ARGUMENT_MISMATCH" (Just "kappa.application.argument-mismatch") sp
                "the supplied argument's type does not match the parameter type (§16.1.7.1)"
      else if aOp || eOp
        then
        report $
          withNote ("expected: " <> renderTerm eT) $
            withNote ("actual:   " <> renderTerm aT) $
              diag SevError StageElaborate "E_SEAL_OPAQUE_UNFOLDING" (Just "kappa-hs.seal.opaque-unfolding") sp
                "an opaque member of a sealed package does not unfold to its hidden definition (§13.2.10)"
      else do
        -- §3.1.11: zonk before rendering so solved metavariables are
        -- substituted and only genuinely-unknown ones remain (those
        -- render as the stable hole `_`, never as a raw `?mN` solver id).
        aTz <- zonkTermM (ctxLen ctx) aT
        eTz <- zonkTermM (ctxLen ctx) eT
        -- §21: phase-boundary mismatches (a meta-phase 'Elab'/'Syntax'
        -- type against an object-phase one) carry the rendered types in
        -- the message itself, since the phase is the point
        let aR = renderTerm aTz
            eR = renderTerm eTz
            metaish r = "Elab" `T.isInfixOf` r || "Syntax" `T.isInfixOf` r
            msg =
              if (metaish aR || metaish eR) && aR /= eR
                then "type mismatch: expected '" <> eR <> "', actual '" <> aR <> "'"
                else "type mismatch"
        report $
          withPayload (mismatchPayload eR aR) $
            withRelated (related RoleUseSite sp ("this expression has type " <> aR)) $
              withNote ("expected: " <> eR) $
                withNote ("actual:   " <> aR) $
                  diag SevError StageElaborate "E_TYPE_EQUALITY_MISMATCH" (Just "kappa.type.mismatch") sp
                    msg

-- | Is the value a §16.1.7.1 suspension type (Thunk/Need)?
isSuspV :: Value -> Bool
isSuspV = \case
  VGlobN (GName pm n) _ | pm == preludeModule, n == "Thunk" || n == "Need" -> True
  _ -> False

-- | Is the value a §12.3.1 capture-annotated type?
isCapturesV :: Value -> Bool
isCapturesV = \case
  VGlobN (GName pm "__captures") _ | pm == preludeModule -> True
  _ -> False

-- | Strip §12.3.1 capture-annotation layers (elimination positions use
-- the underlying type; the annotation itself is part of type identity).
peelCapturesM :: Value -> CheckM Value
peelCapturesM v = do
  v' <- forceM v
  case v' of
    VGlobN (GName pm "__captures") ((_, inner) : _)
      | pm == preludeModule -> peelCapturesM inner
    _ -> pure v'

-- | Is the value (in whnf) headed by a projection of an opaque member
-- of a sealed package (§13.2.10)?
opaqueSealHead :: Value -> CheckM Bool
opaqueSealHead v = do
  v' <- forceM v
  case v' of
    VProjN r f -> do
      r' <- forceM r
      case r' of
        VSealV ls _ -> pure (f `elem` ls)
        _ -> pure False
    VPrim p (h : _)
      | p == "__stuck_app" || p == "__stuck_appI" -> opaqueSealHead h
    _ -> pure False

-- ── Names ────────────────────────────────────────────────────────────

lookupGlobalName :: Text -> CheckM (Maybe GName)
lookupGlobalName n = do
  st <- get
  let own = GName (csModule st) n
  if Map.member own (csGlobals st) || Map.member own (csCtors st)
    then pure (Just own)
    else pure (Map.lookup n (csScope st))

-- | §3.1.4/§8.3.1A: if the spelling @n@ names a live type, constructor,
-- or other top-level declaration (the kind of declaration a module alias
-- with the same spelling shadows), return a short human label for that
-- kind. Returns 'Nothing' when @n@ denotes no such declaration, so the
-- caller falls back to the ordinary unresolved-member diagnostic. The
-- test is keyed on "the alias spelling also has a declaration", not on
-- any particular name.
shadowedDeclKind :: Text -> CheckM (Maybe Text)
shadowedDeclKind n = do
  mg <- lookupGlobalName n
  st <- get
  pure $ do
    g <- mg
    if
      | Map.member g (csDatas st) -> Just "type"
      | Map.member g (csCtors st) -> Just "constructor"
      | Map.member g (csGlobals st) -> Just "declaration"
      | otherwise -> Nothing

globalTerm :: GName -> CheckM (Maybe (Term, Value))
globalTerm g = do
  st <- get
  -- §7.2: in term position the constructor facet of a same-spelling
  -- data family wins over the type facet.
  case Map.lookup g (csCtors st) of
    Just ci -> do
      ec <- ec_
      let tm = etaCtor ec g (ciType ci)
      ty <- evalIn emptyCtx (ciType ci)
      pure (Just (tm, ty))
    Nothing -> case Map.lookup g (csGlobals st) of
      Nothing -> pure Nothing
      Just gd -> pure (Just (CGlob g, gdType gd))

-- type-facet lookup (type positions, §7.2)
globalType :: GName -> CheckM (Maybe (Term, Value))
globalType g = do
  st <- get
  case Map.lookup g (csGlobals st) of
    Just gd -> pure (Just (CGlob g, gdType gd))
    Nothing -> pure Nothing

-- Constructors as values: λ-wrap to a saturated 'CCtor' (erased
-- implicit parameters are dropped from the runtime payload).
--
-- The native backend recognises a saturated application of this shape and
-- beta-reduces it back to a direct 'CCtor' ('Kappa.Backend.C.etaCtorApp', gap
-- P0-A); that recognizer depends on the exact shape produced here (nested
-- 'CLam's whose body is a 'CCtor' selecting only the runtime-field binders by
-- bare 'CVar'), so keep the two in sync.
etaCtor :: EvalCtx -> GName -> Term -> Term
etaCtor ec g cty = build 0 [] (eval ec [] cty)
  where
    build n acc fty = case force ec fty of
      VPi ic q _ _ clo ->
        CLam ic q ("x" <> T.pack (show n)) $
          build (n + 1) ((ic, q, n) : acc) (evalClosure clo (VRigid n []))
      _ ->
        CCtor g [CVar (n - 1 - i) | (ic, q, i) <- reverse acc, runtimeField ic q]
    runtimeField Expl _ = True
    runtimeField Impl q = q /= Q0
    evalClosure (Closure env body) v = eval ec (v : env) body

-- | §3.2.2 suggestion edit-distance threshold for a spelling of this
-- length. Scales with the length so a one-character name does not match
-- every other one-character name. Used both to bound the candidate
-- buckets ('scopeNamesNear') and to filter by edit distance below.
suggestionThreshold :: Int -> Int
suggestionThreshold tlen = max 1 (min 2 (tlen `div` 3))

-- | §3.2.2 typo suggestions: in-scope names within a small edit distance
-- of the unresolved spelling, nearest first (ties broken alphabetically
-- for determinism, §3.1.10). The threshold scales with the length so a
-- one-character name does not match every other one-character name.
-- @cands@ is expected to already be length-compatible (see
-- 'scopeNamesNear'); the length pre-filter is kept so the function is
-- correct on any candidate list.
closeSpellings :: Text -> [Text] -> [Text]
closeSpellings target cands =
  map snd $
    sort
      [ (d, c)
      | c <- cands
      , c /= target
      -- Levenshtein distance is at least the length difference, so a
      -- candidate whose length differs from the target by more than the
      -- threshold can never be within threshold. Skipping it before the
      -- O(len^2) edit-distance keeps the per-error cost proportional to
      -- the (small) set of length-compatible candidates rather than the
      -- whole scope (avoids an O(Nnames * Nscope * len^2) blowup when a
      -- dropped import breaks many references in a large module).
      , abs (T.length c - tlen) <= threshold
      , let d = editDistance tchars (T.unpack c)
      , d <= threshold
      ]
  where
    tchars = T.unpack target
    tlen = T.length target
    threshold = suggestionThreshold tlen

-- | Standard Levenshtein edit distance.
editDistance :: String -> String -> Int
editDistance a b = last (foldl transform [0 .. length a] b)
  where
    transform prevRow@(p0 : _) c =
      scanl compute (p0 + 1) (zip3 a prevRow (tail prevRow))
      where
        compute z (ca, dDiag, dLeft) =
          minimum [dLeft + 1, z + 1, dDiag + if ca == c then 0 else 1]
    transform [] _ = []

resolveName :: Ctx -> Name -> CheckM (Term, Value)
resolveName ctx (Name n sp) =
  case lookupCtx n ctx of
    Just (i, e)
      | ceVarBind e -> derefVar ctx i (ceType e)
      | otherwise -> pure (CVar i, ceType e)
    Nothing -> do
      st <- get
      case Map.lookup n (csScopeAmbig st) of
        Just gs -> do
          -- §3.2.2 kappa.name.ambiguous payload + §3.1.1A: every
          -- candidate MUST appear. The candidates are cross-module
          -- imports without stored declaration spans, so each is a
          -- related origin anchored at the use site naming its providing
          -- module, with candidateSitesAvailable=false recorded in the
          -- payload (§3.1.1A unavailable-origin clause).
          let cands = T.intercalate ", " [renderMod mg | GName mg _ <- gs]
              payload =
                withPayloadField "name" n $
                  withPayloadField "candidates" cands $
                    withPayloadField "candidateSitesAvailable" "false" $
                      payloadKind "name-ambiguous"
              candRels =
                [ related RoleRejectedCandidateSite sp
                    ("candidate from " <> renderMod mg)
                | GName mg _ <- gs
                ]
          report $
            withPayload payload $
              withRelateds (related RoleUseSite sp ("'" <> n <> "' used here") : candRels) $
                diag SevError StageElaborate "E_NAME_AMBIGUOUS" (Just "kappa.name.ambiguous") sp
                  ( "name '" <> n <> "' is ambiguous; it is provided by "
                      <> T.intercalate " and " [renderMod mg | GName mg _ <- gs]
                      <> " (qualify the name or import it explicitly, Spec §7.1)"
                  )
          anyHole ctx
        Nothing -> do
          mg <- lookupGlobalName n
          case mg of
            Just g -> do
              gateUnsafeAssertProof g sp
              mt <- globalTerm g
              case mt of
                Just r -> pure r
                Nothing -> failUnresolved
            Nothing -> failUnresolved
  where
    renderMod (ModuleName segs) = "module " <> T.intercalate "." segs
    failUnresolved = do
      cands <- nearScopeNames
      -- §3.2.2: if a close spelling exists, suggest it. The fix is
      -- 'maybe-applicable' — the renamed reference type-checks only if
      -- the candidate happens to fit, so it is not 'machine-applicable'.
      let near = take 1 (closeSpellings n cands)
          base =
            withPayload
              ( withPayloadField "name" n $
                  withPayloadField "inGeneratedSyntax" "false" $
                    maybe id (withPayloadField "suggestion") (listToMaybe near) $
                      payloadKind "name-unresolved"
              )
              $ withRelated (related RoleUseSite sp ("'" <> n <> "' used here"))
              $ diag SevError StageElaborate "E_NAME_UNRESOLVED" (Just "kappa.name.unresolved") sp
                  ("unresolved name '" <> n <> "' (not in scope)")
          withFixIt d = case near of
            (cand : _) ->
              withHelp ("did you mean '" <> cand <> "'?") $
                withFix
                  ( DiagnosticFix
                      ("replace '" <> n <> "' with '" <> cand <> "'")
                      FixMaybeApplicable
                      [SourceEdit (spanFile sp) sp cand]
                  )
                  d
            [] -> d
      report (withFixIt base)
      anyHole emptyCtxDummy
    -- §3.2.2 candidate spellings for this unresolved name: only the
    -- length-compatible module-level names (from the cached length-bucket
    -- index, so unbounded scope does not make each diagnostic O(Nscope)),
    -- plus the call-site-local binders, which vary per error and so are
    -- not part of the cached index. There are only a handful of locals,
    -- so merging them in stays cheap per diagnostic.
    nearScopeNames = do
      let threshold = suggestionThreshold (T.length n)
      modLevel <- scopeNamesNear n threshold
      let locals = [ceName e | e <- ctxEntries ctx]
      pure $
        if null locals
          then modLevel
          else Set.toList (Set.fromList (locals ++ modLevel))
    emptyCtxDummy = ctx

-- | §3.2.2 typo-suggestion candidate index, bucketed by spelling length:
-- the import scope plus this module's own globals. A single dropped
-- import can leave thousands of references unresolved, each raising a
-- suggestion diagnostic; rebuilding and rescanning the whole scope per
-- diagnostic is O(Nerrors * Nscope). The index is built once here (on the
-- first unresolved name) and thereafter extended incrementally in
-- 'addGlobal' as the module's own globals appear, so the build is paid
-- once. Bucketing by length lets each diagnostic consult only the
-- length-compatible candidates (Levenshtein distance is at least the
-- length difference), bounding the per-error scan. Entering a new module
-- clears the index (Pipeline / TestHarness), since scope and module change.
moduleScopeNameIndex :: CheckM (Map Int (Set Text))
moduleScopeNameIndex = do
  st <- get
  case csScopeNameCache st of
    Just idx -> pure idx
    Nothing -> do
      let scope = Map.keys (csScope st)
          own = [nm | GName m nm <- Map.keys (csGlobals st), m == csModule st]
          idx = foldr insertScopeName Map.empty (scope ++ own)
      modify' $ \s -> s {csScopeNameCache = Just idx}
      pure idx

-- | The length-compatible §3.2.2 candidates for a target spelling: only
-- names whose length is within @threshold@ of the target can be within
-- edit distance @threshold@, so only those buckets are gathered.
scopeNamesNear :: Text -> Int -> CheckM [Text]
scopeNamesNear target threshold = do
  idx <- moduleScopeNameIndex
  let tlen = T.length target
      buckets =
        [ s
        | len <- [tlen - threshold .. tlen + threshold]
        , Just s <- [Map.lookup len idx]
        ]
  pure (Set.toList (Set.unions buckets))

-- | Does a name resolve at all (locals or globals)? Used for §6.3.4
-- literal-prefix resolution, which is ordinary term name resolution.
prefixResolves :: Ctx -> Text -> CheckM Bool
prefixResolves ctx n =
  case lookupCtx n ctx of
    Just _ -> pure True
    Nothing -> do
      mg <- lookupGlobalName n
      pure (maybe False (const True) mg)

-- | A read of a @var@-bound name (§18.6.1): elaborate to a splice that
-- reads the cell, @__runIO (readRef x)@, typed at the element type.
derefVar :: Ctx -> Int -> Value -> CheckM (Term, Value)
derefVar ctx i refTy = do
  elemTy <-
    forceM refTy >>= \case
      VGlobN (GName _ "Ref") [(_, a)] -> pure a
      _ -> freshMetaV ctx
  e <- freshMeta
  aTm <- quoteIn ctx elemTy
  let rd = CApp Expl (CApp Impl (CApp Impl (CGlob (gPrel "readRef")) e) aTm) (CVar i)
      run = CApp Expl (CApp Impl (CApp Impl (CGlob (gPrel "__runIO")) e) aTm) rd
  pure (run, elemTy)

-- universe spellings: Type, Type0, Type1, ..., and '*' (§11.1)
sortName :: Text -> Maybe Int
sortName t
  | t == "Type" || t == "*" = Just 0
  | Just rest <- T.stripPrefix "Type" t
  , not (T.null rest)
  , T.all (\c -> c >= '0' && c <= '9') rest
  , -- bounds check: a suffix this long would overflow 'Int'; treat the
    -- spelling as an ordinary (unresolved) identifier instead
    T.length rest <= 9 =
      Just (read (T.unpack rest))
  | otherwise = Nothing

anyHole :: Ctx -> CheckM (Term, Value)
anyHole ctx = do
  m <- freshMeta
  ty <- freshMetaV ctx
  pure (m, ty)

reportUnsupported :: Span -> Text -> CheckM ()
reportUnsupported sp what =
  let msg = what <> " is not supported by this implementation"
   in report $
        withNote "see SPEC_COVERAGE.md for the implemented subset" $
          withPayload (unsupportedPayload msg) $
            diag SevError StageElaborate "E_UNSUPPORTED" (Just "kappa.unsupported.deterministic") sp msg

unsupported :: Ctx -> Span -> Text -> CheckM (Term, Value)
unsupported ctx sp what = reportUnsupported sp what >> anyHole ctx

-- §6.5 conventional-handler rejections (§3.1.3 diagnostic codes). The
-- recovery values are well-typed placeholders so later stages do not
-- cascade.
badGrapheme :: Span -> Text -> CheckM (Term, Value)
badGrapheme sp why = do
  errAt sp "E_UNICODE_INVALID_GRAPHEME_LITERAL" (Just "kappa-hs.unicode.invalid-grapheme-literal")
    ("invalid grapheme literal: " <> why <> " (Spec §6.5)")
  pure (CLit (LitGrapheme "?"), VGlobN (gPrel "Grapheme") [])

badByte :: Span -> Text -> CheckM (Term, Value)
badByte sp why = do
  errAt sp "E_UNICODE_INVALID_BYTE_LITERAL" (Just "kappa-hs.unicode.invalid-byte-literal")
    ("invalid byte literal: " <> why <> " (Spec §6.5)")
  pure (CLit (LitByte 0x3F), VGlobN (gPrel "Byte") [])

-- §6.1.6: an out-of-scope numeric-literal suffix is a compile-time
-- name-resolution error identifying the missing suffix name.
badLiteralSuffix :: Ctx -> Name -> CheckM (Term, Value)
badLiteralSuffix ctx (Name n sp) = do
  errAt sp "E_NAME_UNRESOLVED" (Just "kappa.name.unresolved")
    ("the numeric-literal suffix '" <> n <> "' does not resolve to a term in scope (Spec §6.1.6)")
  anyHole ctx

-- ── Implicit resolution (§16.3.3) ────────────────────────────────────

resolveImplicit :: Ctx -> Span -> Value -> CheckM Term
resolveImplicit ctx sp goal = resolveImplicitQ ctx sp Q0 goal

-- | Resolve an implicit argument for a binder of quantity @q@ (§16.3.3).
-- The quantity distinguishes runtime implicits (which demand an actual
-- candidate, fixtures' @\@ω env : Env@ style) from erased ones (whose
-- values may be inferred later by unification).
resolveImplicitQ :: Ctx -> Span -> Q -> Value -> CheckM Term
resolveImplicitQ ctx sp q goal = do
  g <- forceM goal
  kindLike <- isKindLike (ctxLen ctx) g
  case g of
    _ | kindLike -> freshMeta -- type\/type-constructor params are inferred
    _ -> do
      isTrait <- isTraitGoal g
      isEq <- isEqGoal g
      isRow <- isRowGoal g
      flexed <- goalHasFlex g
      if (isTrait || isEq || isRow) && flexed
        then do
          -- postpone resolution until explicit arguments solve the head
          -- metavariables (§16.1.7.1 spine order); committing to a local
          -- candidate now could wrongly solve the metas
          mid <- freshMetaId
          bfs <- gets csBoolFacts
          modify' $ \st -> st {csPending = (mid, g, sp, ctx, bfs) : csPending st}
          pure (CMeta mid)
        else do
          -- a flex-headed goal type is not searchable evidence: its
          -- value is inferred by unification at the use site (§16.3.3)
          gIsFlex <- do
            gF <- forceM g
            pure $ case gF of
              VFlex {} -> True
              _ -> False
          if gIsFlex && not (isTrait || isEq)
            then freshMeta
            else resolveLadder g isTrait isEq
  where
    resolveLadder g isTrait isEq = do
      -- §16.3.3 step 1: the local implicit context goes first.
      mLoc <- localCandidate ctx sp q g
      case mLoc of
        Just tm -> pure tm
        Nothing -> do
          mInst <- instanceSearch ctx sp g
          case mInst of
            Just tm -> pure tm
            Nothing -> do
              -- §14.3.3: project the goal out of in-scope evidence
              -- through declared-supertrait conformance paths
              mSup <- if isTrait then superCandidate ctx g else pure Nothing
              case mSup of
                Just tm -> pure tm
                Nothing -> do
                  mProp <- propProof g
                  case mProp of
                    Just tm -> pure tm
                    Nothing -> do
                      -- §11.3.1A compiler-owned introduction rules for
                      -- the intrinsic row traits
                      mRow <- rowProof g
                      case mRow of
                        Just tm -> pure tm
                        Nothing -> do
                          mWitness <- isTraitWitness ctx g
                          case mWitness of
                            Just tm -> pure tm
                            Nothing -> unresolved g isTrait isEq
    unresolved g isTrait isEq = do
      isRow <- isRowGoal g
      if isTrait || isEq || q /= Q0
        then do
          gT <- quoteIn ctx g
          errAt sp "E_UNSOLVED_IMPLICIT" (Just "kappa.implicit.unsolved")
            ("could not resolve implicit argument of type " <> renderTerm gT
               <> (if isTrait || isEq || isRow then "" else "; a runtime implicit binder requires an implicit local candidate in scope (§16.3.3), and top-level terms are not candidates"))
          freshMeta
        else freshMeta

-- | §22.4: a goal of shape @forall xs. IsTrait (tc x)@ is satisfied by
-- a synthesized witness whenever its head is the builtin 'IsTrait'
-- classifier; the witness carries no information.
isTraitWitness :: Ctx -> Value -> CheckM (Maybe Term)
isTraitWitness ctx goal = go (ctxLen ctx) goal
  where
    go lvl v = do
      vF <- forceM v
      case vF of
        VPi ic q nm _ clo -> do
          cod <- clApp clo (VRigid lvl [])
          fmap (CLam ic q nm) <$> go (lvl + 1) cod
        VGlobN (GName pm "IsTrait") _
          | pm == preludeModule ->
              pure (Just (CGlob (gPrel "__isTraitWitness")))
        _ -> pure Nothing

-- | Kind-like goals — @Type@, @Type -> Type@, … — are inferred from
-- use sites (metavariables), never searched as evidence (§16.3.3).
isKindLike :: Int -> Value -> CheckM Bool
isKindLike lvl v = do
  t <- forceM v
  case t of
    VSort _ -> pure True
    VPi _ _ _ _ clo -> do
      cod <- clApp clo (VRigid lvl [])
      isKindLike (lvl + 1) cod
    _ -> pure False

localCandidate :: Ctx -> Span -> Q -> Value -> CheckM (Maybe Term)
localCandidate ctx sp q goal = go 0 [] (ctxEntries ctx)
  where
    -- anonymous binders are not referenceable and never shadow
    shadowName e = [ceName e | ceName e `notElem` ["_", "_ev"]]
    go _ _ [] = pure Nothing
    go i seen (e : rest)
      | ceImplicitLocal e
      , ceName e `notElem` seen = do
          st0 <- get
          ok <- unify ctx (ceType e) goal
          if ok
            then do
              checkAmbiguous i (shadowName e ++ seen) rest
              checkCandidate i e
              pure (Just (CVar i))
            else put st0 >> go (i + 1) (shadowName e ++ seen) rest
      | otherwise = go (i + 1) (shadowName e ++ seen) rest
    -- a second matching candidate in the same scope (no closure
    -- boundary between the two) is ambiguous (§16.3.3)
    checkAmbiguous i seen rest = do
      let lvlOf ix = ctxLen ctx - 1 - ix
      next <- findNext (i + 1) seen rest
      forM_ next $ \j -> do
        let l1 = lvlOf i
            l2 = lvlOf j
            separated = any (\b -> l2 < b && b <= l1) (ctxBarriers ctx)
        unless separated $
          -- §3.1.1A: cite the goal site; the competing candidates are
          -- local context binders without stored source spans, so the
          -- payload records candidate names with sites unavailable.
          report $
            withPayload
              ( withPayloadField "candidates"
                  (T.intercalate ", " [candName i, candName j]) $
                  withPayloadField "candidateSitesAvailable" "false" $
                    payloadKind "implicit-ambiguous"
              )
              $ withRelated (related RoleObligationRequiredHere sp "implicit goal raised here")
              $ diag SevError StageElaborate "E_IMPLICIT_AMBIGUOUS" (Just "kappa.implicit.ambiguous") sp
                  "two implicit candidates in the same scope satisfy this implicit goal; the resolution is ambiguous (§16.3.3)"
    candName ix = case drop ix (ctxEntries ctx) of
      (e : _) -> ceName e
      [] -> "?"
    findNext _ _ [] = pure Nothing
    findNext j seen (e : rest)
      | ceImplicitLocal e
      , ceName e `notElem` seen = do
          st0 <- get
          ok <- unify ctx (ceType e) goal
          put st0
          if ok then pure (Just j) else findNext (j + 1) (shadowName e ++ seen) rest
      | otherwise = findNext (j + 1) (shadowName e ++ seen) rest
    checkCandidate i e = do
      -- an erased candidate cannot satisfy a runtime implicit (§12.2)
      when (q /= Q0 && ceQ e == Just S.QZero) $
        errAt sp "E_QTT_ERASED_RUNTIME_USE" (Just "kappa.quantity.unsatisfied")
          ("the implicit candidate '" <> ceName e <> "' is erased (@0) and cannot satisfy a runtime implicit binder (§12.2)")
      -- a borrowed candidate may not be captured across a closure
      -- boundary (§16.3.3, §12.3.2). §3.1.1A requires the borrow
      -- introduction site AND the failing escape site as related
      -- origins: cite the candidate's recorded binder origin
      -- (RoleBorrowStart) and the capturing use site (RoleBorrowEscapeSite).
      let lvl = ctxLen ctx - 1 - i
      when (ceBorrow e && any (> lvl) (ctxBarriers ctx)) $ do
        let originKnown = ceOrigin e /= noSpan
            -- §3.1.1A line 610-611: when a required origin is
            -- unavailable, the payload records why.
            payload =
              withPayloadField "candidate" (ceName e) $
                if originKnown
                  then payloadKind "borrow-escape"
                  else
                    withPayloadField "introOriginAvailable" "false" $
                      withPayloadField "introOriginUnavailableReason"
                        "borrow introduction site untracked for this candidate kind" $
                        payloadKind "borrow-escape"
            withIntro =
              if originKnown
                then withRelated (related RoleBorrowStart (ceOrigin e)
                       ("'" <> ceName e <> "' borrowed here"))
                else id
        report $
          withPayload payload $
            withIntro $
              withRelated (related RoleBorrowEscapeSite sp
                "captured across this closure boundary here") $
                diag SevError StageElaborate "E_QTT_BORROW_ESCAPE"
                  (Just "kappa.borrow.escape") sp
                  ("the borrowed implicit candidate '" <> ceName e
                    <> "' may not be captured by a closure (§12.3.2)")

goalHasFlex :: Value -> CheckM Bool
goalHasFlex v = do
  ec <- ec_
  t <- pure (quote ec 0 v)
  st <- get
  let unsolved m = case Map.lookup m (csMetas st) of
        Just (Just _) -> False
        _ -> True
  pure (anyMeta unsolved t)
  where
    anyMeta f = goT
      where
        goT = \case
          CMeta m -> f m
          CApp _ a b -> goT a || goT b
          CPi _ _ _ a b -> goT a || goT b
          CLam _ _ _ b -> goT b
          CCtor _ as -> any goT as
          CRecordT fs -> any (goT . snd) fs
          CVariantT ms -> any goT ms
          CProj e _ -> goT e
          CProjAt e _ _ -> goT e
          _ -> False

-- | Flush postponed trait goals after a body has been elaborated. A
-- goal whose head is still an unsolved metavariable is kept pending
-- (a later declaration's use site may determine the head, e.g. an
-- unannotated @let f x y = x + y@ used at @Int@); 'flushPendingFinal'
-- commits the survivors at the end of the module.
flushPending :: CheckM ()
flushPending = flushPendingWith False

flushPendingFinal :: CheckM ()
flushPendingFinal = flushPendingWith True

flushPendingWith :: Bool -> CheckM ()
flushPendingWith final = do
  st <- get
  let pend = reverse (csPending st)
  put st {csPending = []}
  forM_ pend $ \(mid, goal, sp, ctx, bfs) -> do
    stNow <- get
    case Map.lookup mid (csMetas stNow) of
      Just (Just _) -> pure ()
      _ -> do
        g <- forceM goal
        stillFlex <- goalHasFlex g
        -- deferral across declarations is safe only when no local
        -- implicit candidate could ever apply: the declaration's body
        -- is zonked and stored before the goal is finally committed,
        -- so a late local-candidate solution would leak local rigids
        -- into the stored term (see zonkTermM)
        let noLocalCandidates = not (any ceImplicitLocal (ctxEntries ctx))
        if stillFlex && not final && noLocalCandidates
          then modify' $ \s -> s {csPending = (mid, goal, sp, ctx, bfs) : csPending s}
          else do
            mLoc <- localCandidate ctx sp Q0 g
            r <- case mLoc of
              Just tm -> pure (Just tm)
              Nothing -> do
                mi <- instanceSearch ctx sp g
                case mi of
                  Just tm -> pure (Just tm)
                  Nothing -> do
                    -- §14.3.3 conformance paths from local evidence
                    mSup <- superCandidate ctx g
                    case mSup of
                      Just tm -> pure (Just tm)
                      Nothing -> do
                        -- re-enter the boolean branch facts that were
                        -- in scope when the goal was raised
                        oldBfs <- gets csBoolFacts
                        modify' $ \s -> s {csBoolFacts = bfs ++ oldBfs}
                        r0 <- propProof g
                        modify' $ \s -> s {csBoolFacts = oldBfs}
                        case r0 of
                          Just tm -> pure (Just tm)
                          -- §11.3.1A intrinsic row-trait introduction
                          Nothing -> rowProof g
            case r of
              Just tm -> do
                v <- evalIn ctx tm
                solveMeta mid v
              Nothing -> emitUnsolvedGoal ctx sp g

-- | Emit an unsolved-implicit goal failure, applying §3.1.11 single-cause
-- cascade suppression so one ill-typed expression yields one diagnostic.
--
-- Two cascade shapes collapse to a single root cause:
--
--   * The goal's carrier still mentions an unsolved metavariable that an
--     earlier same-span type-equality mismatch reported against (the
--     mismatch could not be decided precisely because this carrier was
--     never solved). The mismatch is the downstream consequence: drop it
--     and keep the more informative unsolved-goal diagnostic. (e.g. an
--     overloaded value-position member whose result carrier `?m a` fails
--     against the declared result type while its trait goal is unsolved.)
--
--   * The goal's carrier is fully concrete and is exactly the type that an
--     earlier mismatch already rejected at the same site (e.g. a numeric
--     trait goal `Mul T` raised for an operand whose type `T` already
--     failed to unify with the numeric domain). Here the goal is the
--     downstream consequence: suppress it and keep the mismatch.
emitUnsolvedGoal :: Ctx -> Span -> Value -> CheckM ()
emitUnsolvedGoal ctx sp g = do
  ec <- ec_
  let gT = quote ec (ctxLen ctx) g
      gRendered = renderTerm gT
  ms <- unsolvedMetaIdsIn g
  let -- §3.1.11: unsolved metavariables now render as the stable hole
      -- `_` (never a raw `?mN` solver id). A same-span type-equality
      -- mismatch whose rendered expected/actual carries that hole is the
      -- downstream consequence of this goal's unsolved carrier (the
      -- unification was blocked precisely because a metavariable here was
      -- never solved). The structural condition is the goal still has
      -- unsolved metas ('not (null ms)') and the mismatch shows a hole.
      mentionsMeta d = any noteHasHole (dNotes d)
      -- a standalone `_` token (the rendered unsolved hole) inside an
      -- expected:/actual: note, as opposed to `_` embedded in an
      -- identifier or a `(x : _)`-style binder
      noteHasHole note = "_" `elem` T.words (T.map spaceP note)
      spaceP c = if c `elem` ("():," :: String) then ' ' else c
      isMismatch d = dCode d == "E_TYPE_EQUALITY_MISMATCH"
      -- the goal's trait arguments, rendered (e.g. the carrier `T` of
      -- `Mul T`): a concrete carrier already named in a mismatch note
      carrierTexts = case gT of
        CApp _ _ _ -> [renderTerm a | a <- spineArgs gT]
        _ -> []
      spineArgs = reverse . go
        where
          go (CApp _ f a) = a : go f
          go _ = []
  ds <- gets csDiags
  let sameStart d = spanStart (dPrimary d) == spanStart sp
      isDownstreamMismatch d = isMismatch d && sameStart d && mentionsMeta d
      hasDownstreamMismatch = not (null ms) && any isDownstreamMismatch ds
      concreteCarrierAlreadyRejected =
        null ms
          && not (null carrierTexts)
          && any
            ( \d ->
                isMismatch d
                  && posLine (spanStart (dPrimary d)) == posLine (spanStart sp)
                  && any (\ct -> any (ct `T.isInfixOf`) (dNotes d)) carrierTexts
            )
            ds
      goalMsg = "could not resolve implicit argument of type " <> gRendered
      emit = errAt sp "E_UNSOLVED_IMPLICIT" (Just "kappa.implicit.unsolved") goalMsg
      summarize d =
        Suppressed (dCode d) (dFamily d) (dPrimary d) (dMessage d)
  if hasDownstreamMismatch
    then do
      -- §3.1.10/§3.1.11: drop the downstream same-span mismatch and keep
      -- the unsolved goal, recording the dropped mismatch in the survivor's
      -- 'suppressed' summary so tooling can still show it.
      let dropped = [summarize d | d <- ds, isDownstreamMismatch d]
      modify' $ \st -> st {csDiags = filter (not . isDownstreamMismatch) (csDiags st)}
      report $
        withSuppressed dropped $
          diag SevError StageElaborate "E_UNSOLVED_IMPLICIT" (Just "kappa.implicit.unsolved") sp goalMsg
    else
      if concreteCarrierAlreadyRejected
        then
          -- the goal is the cascade of an already-reported mismatch:
          -- record its summary on that surviving root mismatch (§3.1.11).
          modify' $ \st ->
            let supp = Suppressed "E_UNSOLVED_IMPLICIT" (Just "kappa.implicit.unsolved") sp goalMsg
                onLine d = isMismatch d && posLine (spanStart (dPrimary d)) == posLine (spanStart sp)
                -- attach to the first matching root mismatch only
                attachOnce [] = []
                attachOnce (d : rest)
                  | onLine d = withSuppressed [supp] d : rest
                  | otherwise = d : attachOnce rest
             in st {csDiags = attachOnce (csDiags st)}
        else emit

-- | All metavariable identifiers occurring in a term, with full
-- constructor coverage (de-duplicated). Shared by the meta-collection
-- sites so they cannot drift in which constructors they descend into.
metaIdsOf :: Term -> [MetaId]
metaIdsOf = nub . go
  where
    go = \case
      CMeta m -> [m]
      CApp _ a b -> go a ++ go b
      CPi _ _ _ a b -> go a ++ go b
      CLam _ _ _ b -> go b
      CCtor _ as -> concatMap go as
      CRecordT fs -> concatMap (go . snd) fs
      CRecordV fs -> concatMap (go . snd) fs
      CVariantT ms -> concatMap go ms
      CInject _ e -> go e
      CProj e _ -> go e
      CProjAt e _ _ -> go e
      CMatch s alts -> go s ++ concat [maybe [] go g ++ go b | CaseAlt _ g b <- alts]
      CLet _ _ a b c -> go a ++ go b ++ go c
      CLetRec _ _ a b c -> go a ++ go b ++ go c
      CSealE _ e -> go e
      CSigT _ e -> go e
      CThunkE e -> go e
      CLazyE e -> go e
      CForceE e -> go e
      CIf a b c -> go a ++ go b ++ go c
      CQuote _ slots -> concatMap go slots
      CVar _ -> []
      CGlob _ -> []
      CSort _ -> []
      CLit _ -> []
      CDo _ _ -> []

-- | The unsolved subset of 'metaIdsOf' under the current solution map.
unsolvedMetasOf :: CheckState -> Term -> [MetaId]
unsolvedMetasOf st t =
  [ m
  | m <- metaIdsOf t
  , case Map.lookup m (csMetas st) of
      Just (Just _) -> False
      _ -> True
  ]

-- | Unsolved metavariable identifiers occurring in a value's quotation.
unsolvedMetaIdsIn :: Value -> CheckM [MetaId]
unsolvedMetaIdsIn v = do
  ec <- ec_
  let t = quote ec 0 v
  st <- get
  pure (unsolvedMetasOf st t)

-- | Replace solved metavariables by their solutions, quoted at the
-- correct binder depth. Run after 'flushPending' so terms stored as
-- globals (and instance dictionaries) contain no live 'CMeta' whose
-- solution mentions local rigids (premise dictionaries, §14.3.2).
zonkTermM :: Int -> Term -> CheckM Term
zonkTermM depth0 t0 = do
  ec <- ec_
  let goI :: Int -> [KItem] -> [KItem]
      goI _ [] = []
      goI d (k : ks) =
        let (k', d') = goK d k
         in k' : goI d' ks
      goK d = \case
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
        KWhile l c b e -> (KWhile l (go d c) (goI d b) (fmap (goI d) e), d)
        KFor l p s b e -> (KFor l p (go d s) (goI (d + patBindersC p) b) (fmap (goI d) e), d)
        KIf alts e -> (KIf [(go d c, goI d b) | (c, b) <- alts] (fmap (goI d) e), d)
        KDefer ml t -> (KDefer ml (go d t), d)
        KUsing p a r -> (KUsing p (go d a) (go d r), d)
        KSubDo l b -> (KSubDo l (goI d b), d)
      go :: Int -> Term -> Term
      go d = \case
        CMeta m -> case Map.lookup m (ecMetas ec) of
          Just (Just v) -> quote ec d v
          _ -> CMeta m
        CVar i -> CVar i
        CGlob g -> CGlob g
        CLam ic q n b -> CLam ic q n (go (d + 1) b)
        CPi ic q n a b -> CPi ic q n (go d a) (go (d + 1) b)
        CApp ic f a -> CApp ic (go d f) (go d a)
        CSort s -> CSort s
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
        CDo lbl items -> CDo lbl (goI d items)
        CSealE ls e -> CSealE ls (go d e)
        CSigT ls e -> CSigT ls (go d e)
        CThunkE e -> CThunkE (go d e)
        CLazyE e -> CLazyE (go d e)
        CForceE e -> CForceE (go d e)
        CIf a b c -> CIf (go d a) (go d b) (go d c)
        CQuote qs slots -> CQuote qs (map (go d) slots)
  pure (go depth0 t0)

isTraitGoal :: Value -> CheckM Bool
isTraitGoal v =
  forceM v >>= \case
    VGlobN g _ -> gets (Map.member g . csTraits)
    _ -> pure False

isEqGoal :: Value -> CheckM Bool
isEqGoal v =
  forceM v >>= \case
    VGlobN (GName _ "=") _ -> pure True
    VCtor (GName _ "=") _ -> pure True
    _ -> pure False

-- | Is the goal one of the §11.3.1A intrinsic row traits (solved by
-- compiler-owned introduction rules, postponed while its row is flex)?
isRowGoal :: Value -> CheckM Bool
isRowGoal v =
  forceM v >>= \case
    VGlobN (GName pm "LacksRec") _ | pm == preludeModule -> pure True
    _ -> pure False

-- | §11.3.1A compiler-owned introduction rules: @LacksRec r l@ is
-- solvable iff the normalized row tail @r@ contains no label @l@ —
-- for a closed residual row, decided structurally on its fields.
rowProof :: Value -> CheckM (Maybe Term)
rowProof goal = do
  g <- forceM goal
  case g of
    VGlobN (GName pm "LacksRec") [(_, rowV), (_, lblV)]
      | pm == preludeModule -> do
          row <- forceM rowV
          lbl <- forceM lblV
          case (row, lbl) of
            (VGlobN (GName pm2 "__closedRow") [(_, fieldsV)], VLit (LitStr l))
              | pm2 == preludeModule -> do
                  fsF <- forceM fieldsV
                  case fsF of
                    VRecordT fs
                      | l `notElem` map fst fs ->
                          pure (Just (CGlob (gPrel "__rowEvidence")))
                    _ -> pure Nothing
            _ -> pure Nothing
    _ -> pure Nothing

-- | Whether a forced value is an unsolved metavariable (a flexible head).
isFlexV :: Value -> Bool
isFlexV (VFlex _ _) = True
isFlexV _ = False

instanceSearch :: Ctx -> Span -> Value -> CheckM (Maybe Term)
instanceSearch ctx sp goal = searchDepth 0 ctx sp goal

searchDepth :: Int -> Ctx -> Span -> Value -> CheckM (Maybe Term)
searchDepth depth ctx sp goal
  | depth > 16 = pure Nothing -- §14.3.5 termination backstop
  | otherwise = do
      g <- forceM goal
      case g of
        VGlobN traitG spine -> do
          st <- get
          -- §14.3.1/§14.3.5: a PREMISE goal (depth > 0) whose trait arguments
          -- all force to bare unsolved metavars is underdetermined and MUST NOT
          -- drive instance selection. Without this, a recursive multi-premise
          -- instance (e.g. `(Eq e, Eq a) => Eq (Result e a)`) makes its premise
          -- goals `Eq ?e`/`Eq ?a` match the instance's own head, assigning the
          -- metavars and recursing with fan-out — an exponential blow-up up to
          -- the depth backstop. The cut is confined to premise resolution: a
          -- top-level use-site goal (depth 0) whose metavar is solved BY the
          -- matching instance still resolves, and determined goals
          -- (`Eq Integer`, `Eq a`, `Eq (Result ?e ?a)`) always resolve.
          spineFlex <- mapM (fmap isFlexV . forceM . snd) spine
          if depth > 0 && not (null spine) && and spineFlex
            then pure Nothing
          else if not (Map.member traitG (csTraits st))
            then pure Nothing
            else do
              let cands = [ie | ie <- csInstances st, ieTrait ie == traitG]
              hits <- catMaybes <$> mapM (\ie -> fmap ((,) ie) <$> tryInstance depth ctx (map snd spine) ie) cands
              case hits of
                [(_, tm)] -> pure (Just tm)
                [] -> pure Nothing
                ((ie0, tm) : rest) -> do
                  -- §33.2.1 step 3: equivalent evidence artifacts are
                  -- harmless overlap — select the deterministic
                  -- representative; only non-equivalent overlap is
                  -- incoherent
                  ecu <- ec_
                  tmV <- evalIn ctx tm
                  restVs <- mapM (evalIn ctx . snd) rest
                  unless (all (convertible ecu (ctxLen ctx) tmV) restVs) $ do
                    -- a candidate whose dictionary value is not yet
                    -- defined (§14.3 pre-pass entry whose members are
                    -- checked later in this module) cannot be compared
                    -- for equivalence here; the declaration-level
                    -- §14.3/§33.2.1 coherence check judges that pair
                    -- definitively, so do not pre-judge the overlap
                    pending <- filterM (dictValuePending . ieDict) (ie0 : map fst rest)
                    when (null pending) $ do
                      -- §3.1.1A: trait-coherence diagnostics MUST include
                      -- every surviving incoherent instance declaration
                      -- site.
                      rels <- instanceRelateds (ie0 : map fst rest)
                      report $
                        withRelateds rels $
                          diag SevError StageElaborate "E_INSTANCE_INCOHERENT" (Just "kappa-hs.trait.incoherent") sp
                            "multiple instances match this trait obligation (§14.3.1 coherence)"
                  pure (Just tm)
        _ -> pure Nothing

-- | Whether an instance dictionary's value is still pending (its
-- declaration's members have not been checked yet — the §14.3
-- pre-pass registers heads ahead of the body pass).
dictValuePending :: GName -> CheckM Bool
dictValuePending g = gets (maybe True (isNothing . gdValue) . Map.lookup g . csGlobals)

-- | §3.1.1A: the declaration site of an instance, recovered from the
-- §14.3 pre-pass table ('csPreInstances' is keyed by declaration span)
-- by its dictionary global. Returns Nothing for instances with no
-- pre-pass entry (built-in/imported).
instanceDeclSite :: GName -> CheckM (Maybe Span)
instanceDeclSite dictG = do
  pre <- gets csPreInstances
  pure $ listToMaybe [sp | (sp, Just pii) <- Map.toList pre, piDictG pii == dictG]

-- | §3.1.1A trait-coherence related origins: every surviving incoherent
-- instance's declaration site (those with a known pre-pass span).
instanceRelateds :: [InstanceEntry] -> CheckM [RelatedOrigin]
instanceRelateds ies = do
  sites <- mapM (instanceDeclSite . ieDict) ies
  pure
    [ related RoleInstanceDeclarationSite s "a matching instance is declared here"
    | Just s <- sites
    ]

tryInstance :: Int -> Ctx -> [Value] -> InstanceEntry -> CheckM (Maybe Term)
tryInstance depth ctx goalArgs ie
  | length (ieHead ie) /= length goalArgs = pure Nothing
  | otherwise = do
      saved <- get
      metas <- forM [1 .. ieTeleLen ie] (const freshMeta)
      metaVs <- mapM (evalIn emptyCtx) metas
      ec <- ec_
      let headVs = [eval ec (reverse metaVs) t | t <- ieHead ie]
      oks <- zipWithM (unify ctx) headVs goalArgs
      if and oks
        then do
          let premVs = [eval ec (reverse metaVs) p | p <- iePremises ie]
          prems <- forM premVs $ \pv -> do
            mLoc <- localCandidate ctx noSpan Q0 pv
            case mLoc of
              Just t -> pure (Just t)
              Nothing -> do
                mi <- searchDepth (depth + 1) ctx noSpan pv
                case mi of
                  Just t -> pure (Just t)
                  Nothing -> do
                    -- §14.1.4: premise resolution is local implicit
                    -- resolution, so an in-scope evidence value may be
                    -- projected to any of its declared supertraits — e.g.
                    -- discharging an `Eq a` premise from a `Hashable a`
                    -- binder via Hashable's Eq supertrait field.
                    mSup <- superCandidate ctx pv
                    case mSup of
                      Just t -> pure (Just t)
                      Nothing -> propProof pv
          if all isJust prems
            then do
              metaTms <- mapM (quoteIn ctx) =<< mapM (evalIn emptyCtx) metas
              -- the dictionary lambda binds only the head's type
              -- variables and then the premise dictionaries; the metas
              -- standing for premise slots are not applied
              let nFv = ieTeleLen ie - length (iePremises ie)
                  dict =
                    foldl' (\f a -> CApp Impl f a)
                      (foldl' (\f a -> CApp Impl f a) (CGlob (ieDict ie)) (take nFv metaTms))
                      (catMaybes prems)
              pure (Just dict)
            else put saved >> pure Nothing
        else put saved >> pure Nothing

-- | §14.3/§33.2.1 program-level coherence: when two instances of one
-- trait have unifiable heads, the overlap is harmless only if the
-- instantiated dictionary artifacts are definitionally equivalent
-- (structural coherence mode); otherwise the program is rejected at
-- the later declaration, whether or not any use site resolves
-- through the overlapping pair.
checkInstanceOverlap :: Span -> GName -> InstanceEntry -> InstanceEntry -> CheckM ()
checkInstanceOverlap sp g new prior
  | length (ieHead new) /= length (ieHead prior) = pure ()
  | otherwise = do
      saved <- get
      metas <- forM [1 .. ieTeleLen new] (const freshMeta)
      metaVs <- mapM (evalIn emptyCtx) metas
      ec <- ec_
      let goalArgs = [eval ec (reverse metaVs) t | t <- ieHead new]
      -- §33.2.1 step 1: the comparison set holds only candidates that
      -- survive §14.3.1 resolution — an instance whose premises are
      -- unsolvable at the shared instantiation is discarded before
      -- coherence is judged
      mOld <- tryInstance 0 emptyCtx goalArgs prior
      mNew <- tryInstance 0 emptyCtx goalArgs new
      equivalent <- case (mNew, mOld) of
        (Just tmN, Just tmO) -> do
          vN <- evalIn emptyCtx tmN
          vO <- evalIn emptyCtx tmO
          ecu <- ec_
          pure (convertible ecu 0 vN vO)
        _ -> pure True -- disjoint heads or a discarded candidate
      put saved
      unless equivalent $ do
        -- §3.1.1A: a coherence diagnostic MUST include every surviving
        -- incoherent instance declaration site — here the new instance
        -- (primary 'sp') and the prior overlapping instance.
        mPrior <- instanceDeclSite (ieDict prior)
        let rels =
              related RoleInstanceDeclarationSite sp "this overlapping instance"
                : [ related RoleInstanceDeclarationSite psp "conflicts with this instance"
                  | Just psp <- [mPrior]
                  ]
        report $
          withRelateds rels $
            diag SevError StageElaborate "E_INSTANCE_INCOHERENT" (Just "kappa-hs.trait.incoherent") sp
              ("overlapping instances of trait '" <> gnameText g
                 <> "' are not equivalent implementations (§14.3, §33.2.1 coherence)")

-- Boolean-proposition normalization (§16.3.3 step 3): goals of shape
-- (lhs = rhs) decided by conversion yield refl.
propProof :: Value -> CheckM (Maybe Term)
propProof goal = do
  g <- forceM goal
  case g of
    VGlobN (GName _ "=") sp | [(_, l), (_, r)] <- drop (length sp - 2) sp -> tryRefl l r
    VCtor (GName _ "=") [_, l, r] -> tryRefl l r
    _ -> pure Nothing
  where
    tryRefl l r = do
      ec <- ec_
      if convertible ec 0 (force ec l) (force ec r)
        then pure (Just (CCtor (gPrel "refl") []))
        else do
          -- boolean branch refinement (§3.2.3 proof source): reduce a
          -- side stuck on an in-scope `if` condition using the active
          -- branch facts (`c = True`/`c = False`)
          facts <- gets csBoolFacts
          if null facts
            then pure Nothing
            else do
              let lf = factReduce ec facts (4 :: Int) (force ec l)
                  rf = factReduce ec facts (4 :: Int) (force ec r)
              pure $
                if convertible ec 0 lf rf
                  then Just (CCtor (gPrel "refl") [])
                  else Nothing
    factReduce _ _ 0 v = v
    factReduce ec facts depth v =
      let factFor c =
            case [b | (fv, b) <- facts, convertible ec 0 (force ec fv) (force ec c)] of
              (b : _) -> Just b
              [] -> Nothing
          boolV b = VCtor (gPrel (if b then "True" else "False")) []
       in case force ec v of
            v' | Just b <- factFor v' -> boolV b
            VIfN c t f
              | Just b <- factFor c ->
                  let Closure env body = if b then t else f
                   in factReduce ec facts (depth - 1) (force ec (eval ec env body))
            v' -> v'

-- ── Quantities (surface → core) ──────────────────────────────────────

qOf :: Maybe S.Quantity -> Q
qOf = \case
  Nothing -> QW
  Just S.QZero -> Q0
  Just S.QOne -> Q1
  Just S.QOmega -> QW
  Just S.QAtMostOne -> QLe1
  Just S.QAtLeastOne -> QGe1
  Just (S.QTerm _) -> QW -- symbolic quantities: approximated as ω

binderQ :: Binder -> Q
binderQ b = case bpQuantity (bPrefix b) of
  Just q -> qOf (Just q)
  Nothing
    | isJust (bpBorrow (bPrefix b)) -> QW -- borrowed reads (approximation)
    | bImplicit b -> QW
    | otherwise -> QW

-- | The binder's annotation with suspension sugar applied: a
-- @(thunk x : T)@ binder has type @Thunk T@ (§16.2.4).
binderTypeExpr :: Binder -> Maybe Expr
binderTypeExpr b = case (bSusp b, bType b) of
  (Just SuspThunk, Just t) ->
    Just (EApp (EVar (Name "Thunk" (bSpan b))) [ArgExplicit t])
  (Just SuspLazy, Just t) ->
    Just (EApp (EVar (Name "Need" (bSpan b))) [ArgExplicit t])
  (_, mt) -> mt

-- ── Elaboration ──────────────────────────────────────────────────────

insertAllImplicits :: Ctx -> Span -> Term -> Value -> CheckM (Term, Value)
insertAllImplicits ctx sp tm ty = do
  t <- forceM ty
  case t of
    VPi Impl q _ dom clo -> do
      arg <- resolveImplicitQ ctx sp q dom
      argV <- evalIn ctx arg
      ty' <- clApp clo argV
      insertAllImplicits ctx sp (CApp Impl tm arg) ty'
    _ -> pure (tm, t)

infer :: Ctx -> Expr -> CheckM (Term, Value)
infer ctx expr = case expr of
  -- §21.4: a hygienic capture occurrence in spliced syntax refers to
  -- its recorded binder by level, immune to later shadowing
  EVar n
    | Just (lvl, ty) <- Map.lookup (nameText n) (ctxHyg ctx) ->
        pure (CVar (ctxLen ctx - 1 - lvl), ty)
  -- §13.2.1 sibling references: inside a dependent record type,
  -- literal, or update, an unshadowed 'this' denotes the record
  EVar n
    | nameText n == "this"
    , Nothing <- lookupCtx "this" ctx -> do
        mthis <- gets csThis
        case mthis of
          Just (ThisType fields) ->
            pure (CGlob thisG, VRecordT (sortOn fst fields))
          Just (ThisTraitSibs fields) ->
            pure (CGlob thisG, VRecordT (sortOn fst fields))
          Just (ThisValue vals tys) ->
            pure (CRecordV (sortOn fst vals), VRecordT (sortOn fst tys))
          Nothing -> resolveName ctx n
  -- §13.2.1: a bare identifier in a sibling-reference position is
  -- shorthand for 'this.label' when that reading is unambiguous (the
  -- name resolves to nothing else)
  EVar n
    | Nothing <- lookupCtx (nameText n) ctx
    , nameText n /= "this"
    , Nothing <- sortName (nameText n) -> do
        mthis <- gets csThis
        let sib = case mthis of
              Just (ThisType fields) -> isJust (lookup (nameText n) fields)
              Just (ThisTraitSibs fields) -> isJust (lookup (nameText n) fields)
              Just (ThisValue _ tys) -> isJust (lookup (nameText n) tys)
              Nothing -> False
            -- §14.2.1: trait-body sibling members shadow globals
            override = case mthis of
              Just (ThisTraitSibs _) -> True
              _ -> False
        mg <- lookupGlobalName (nameText n)
        if sib && (override || isNothing mg)
          then infer ctx (EDot (EVar (Name "this" (nameSpan n))) (DotName n))
          else resolveName ctx n
  EVar n
    | Nothing <- lookupCtx (nameText n) ctx
    , Just lvl <- sortName (nameText n) ->
        -- '*' is a universe spelling only when it does not resolve to
        -- an operator (the prelude defines multiplication) (§11.1)
        if nameText n == "*"
          then do
            mg <- lookupGlobalName "*"
            case mg of
              Just _ -> resolveName ctx n
              Nothing -> pure (CSort lvl, VSort (lvl + 1))
          else pure (CSort lvl, VSort (lvl + 1))
    | otherwise -> resolveName ctx n
  EHole mn sp -> do
    (tm, ty) <- anyHole ctx
    tyT <- quoteIn ctx ty
    -- §3.1.11: zonk so a solved expected type is shown concretely; a
    -- still-unsolved expected type renders as the stable hole `_`.
    tyTz <- zonkTermM (ctxLen ctx) tyT
    let holeName = maybe "_" (("?" <>) . nameText) mn
        expectedR = renderTerm tyTz
    report $
      -- §3.2.4 kappa.hole.unsolved payload: hole identifier + expected type.
      withPayload
        ( withPayloadField "hole" holeName $
            withPayloadField "expected" expectedR $
              payloadKind "hole-unsolved"
        )
        $ diag SevError StageElaborate "E_HOLE_UNSOLVED" (Just "kappa.hole.unsolved") sp
            ("hole " <> holeName <> " : " <> expectedR)
    pure (tm, ty)
  EIntLit v msuf sp -> elabIntLit ctx v msuf sp Nothing
  EFloatLit v msuf sp -> elabFloatLit ctx v msuf sp Nothing
  EStringLit sl parts sp -> elabString ctx sl parts sp
  EQuotedLit ql sp
    | Nothing <- qlPrefix ql
    , Just txt <- qlText ql
    , [c] <- T.unpack txt ->
        pure (CLit (LitScalar c), VGlobN (gPrel "UnicodeScalar") [])
    -- §6.5 conventional 'g' handler: requires a text view containing
    -- exactly one extended grapheme cluster (UAX #29, pinned UCD).
    | Just "g" <- qlPrefix ql ->
        case qlText ql of
          Just txt
            | isSingleGrapheme txt ->
                pure (CLit (LitGrapheme txt), VGlobN (gPrel "Grapheme") [])
            | T.null txt -> badGrapheme sp "the payload is empty"
            | otherwise ->
                badGrapheme sp
                  "the payload does not contain exactly one extended grapheme cluster"
          Nothing -> badGrapheme sp "the payload has no valid text view"
    -- §6.5 conventional 'b' handler: requires a byte view containing
    -- exactly one byte.
    | Just "b" <- qlPrefix ql ->
        case qlBytes ql of
          Just [w] -> pure (CLit (LitByte w), VGlobN (gPrel "Byte") [])
          Just [] -> badByte sp "the payload is empty"
          Just _ -> badByte sp "the payload contains more than one byte"
          Nothing -> badByte sp "the payload has no single-byte view"
    | otherwise -> snd <$> ((,) () <$> unsupported ctx sp "this quoted-literal form")
  EUnit _ -> pure (CCtor (gPrel "Unit") [], VGlobN (gPrel "Unit") [])
  ETuple es _ -> do
    rs <- mapM (infer ctx) es
    let fields = [(tupleField i, tm) | (i, (tm, _)) <- zip [0 :: Int ..] rs]
        ftys = [(tupleField i, ty) | (i, (_, ty)) <- zip [0 :: Int ..] rs]
    pure (CRecordV fields, VRecordT ftys)
  ERecordLit items sp -> elabRecordLit ctx items sp
  ERecordType fs mtail sp -> do
    let names = [nameText (rtfName f) | f <- fs]
    -- §13.2.1: bare sibling-reference shorthand counts toward the
    -- field-dependency graph when the bare reading is unambiguous
    bareSibs <-
      filterM
        (\l -> do
           mg <- lookupGlobalName l
           pure (isNothing mg && isNothing (lookupCtx l ctx) && isNothing (sortName l)))
        names
    let deps f =
          nub
            ( [l | l <- surfaceThisRefs (rtfType f), l `elem` names]
                ++ [l | l <- surfaceVarNames (rtfType f), l `elem` bareSibs]
            )
        ordered = topoFields [(nameText (rtfName f), deps f, f) | f <- fs]
    forM_ (duplicatesOf names) $ \n ->
      errAt sp "E_RECORD_DUPLICATE_FIELD" (Just "kappa-hs.record.duplicate-field")
        ("record type has duplicate field '" <> n <> "'")
    -- §13.2.1: an explicit field type of an open record may not refer
    -- to a field that would come only from the residual row
    let residualRefs =
          if isJust mtail
            then nub [(nameText (rtfName f), l) | f <- fs, l <- surfaceThisRefs (rtfType f), l `notElem` names]
            else []
    forM_ residualRefs $ \(fn, l) ->
      errOnce sp "E_RECORD_DEPENDENCY_INVALID" (Just "kappa-hs.record.dependency-invalid")
        ( "the explicit field '" <> fn <> "' refers to '" <> l
            <> "', which is not an explicitly listed field of this open record (§13.2.1)"
        )
    -- recovery: the invalid labels stand for opaque placeholders so
    -- the rest of the telescope still elaborates
    phantoms <- forM (nub (map snd residualRefs)) $ \l -> (,) l <$> freshMetaV ctx
    case ordered of
      Nothing -> do
        errAt sp "E_RECORD_DEPENDENCY_CYCLE" (Just "kappa-hs.record.dependency-cycle")
          "the field-dependency graph of this record type contains a cycle (§13.2.1)"
        fields <- forM names $ \n -> (,) n <$> freshMeta
        finish fields
      Just fsOrdered -> do
        -- §13.2.1: elaborate the telescope in dependency order; later
        -- field types see earlier fields through 'this'
        fields <- goDep phantoms fsOrdered
        finish [(nameText (rtfName f), t) | (f, t) <- fields]
    where
      goDep _ [] = pure []
      goDep done (f : rest) = do
        (t0, _) <- withThis (Just (ThisType done)) (inferType ctx (rtfType f))
        -- §13.2.1/§16.1.7.1: a suspension-marked field declares the
        -- suspension type; literals insert the suspension at the field
        let t = case rtfSusp f of
              Just SuspThunk -> CApp Expl (CGlob (gPrel "Thunk")) t0
              Just SuspLazy -> CApp Expl (CGlob (gPrel "Need")) t0
              Nothing -> t0
        tV <- evalIn ctx t
        ((f, t) :) <$> goDep ((nameText (rtfName f), tV) : done) rest
      finish fields = case mtail of
        -- §13.2.10: opaque members make the closed record a signature
        Nothing
          | opaqs@(_ : _) <- sort [nameText (rtfName f) | f <- fs, rtfOpaque f] ->
              pure (CSigT opaqs (CRecordT (sortOn fst fields)), VSort 0)
        Nothing -> pure (CRecordT (sortOn fst fields), VSort 0)
        -- §11.3.1A: open record with a contextual row tail
        Just tailE -> do
          rowTm <- check ctx tailE (VGlobN (gPrel "RecRow") [])
          pure
            ( CApp Expl (CApp Expl (CGlob (gPrel "__openRec")) rowTm)
                (CRecordT (sortOn fst fields))
            , VSort 0
            )
  -- §21.6 convenience reflection queries in ordinary (non-Elab)
  -- positions run at the call site ('elabReflQuery')
  EApp (EVar qn) args
    | nameText qn `elem` reflQueryNames
    , Nothing <- lookupCtx (nameText qn) ctx ->
        elabReflQuery ctx qn args Nothing
  -- carrier-prefixed comprehension (§20.9): a type-valued head applied
  -- to a comprehension literal selects a collection carrier
  EApp f args
    | not (null args)
    , ArgExplicit (EComprehension k cs y csp) <- last args -> do
        st0 <- get
        let preArgs = init args
        mPrefix <- carrierPrefix ctx f preArgs
        case mPrefix of
          Just prefix -> elabComprehensionC ctx k cs y csp (Just prefix)
          Nothing -> do
            put st0
            (fTm, fTy) <- infer ctx f
            elabSpine ctx (exprSpan f) fTm fTy args
  EApp f args -> do
    mproj <- projectionHead ctx f
    mRecvProj <- maybe (projRecvApp ctx f args) (const (pure Nothing)) mproj
    case (mproj, mRecvProj) of
      (_, Just r) -> pure r
      (Just (g, pj), _) -> elabProjApp ctx (exprSpan f) g pj args
      _ -> do
        n0 <- gets (length . csDiags)
        (fTm, fTy) <- infer ctx f
        headUnresolved <- case f of
          EVar {} -> do
            ds <- gets csDiags
            pure (any ((== "E_NAME_UNRESOLVED") . dCode) (take (length ds - n0) ds))
          _ -> pure False
        if headUnresolved
          -- recovery (§3.1.14): an application whose head does not
          -- resolve reports the head once; the arguments cannot be
          -- meaningfully typed against an unknown callee
          then anyHole ctx
          else withArgFlatFor f (elabSpine ctx (exprSpan f) fTm fTy args)
  EDot e m -> elabDot ctx e m
  EQDot e m -> elabSafeNav ctx e m
  EElvis l r sp -> elabElvis ctx l r sp
  EIs e cref -> elabIs ctx e cref
  EAscription e tyE _ -> do
    (tyTm, _) <- inferType ctx tyE
    tyV <- evalIn ctx tyTm
    tm <- check ctx e tyV
    pure (tm, tyV)
  EArrow b body -> do
    domE <- case binderTypeExpr b of
      Just t -> pure t
      Nothing -> pure (EUnit (bSpan b))
    (domTm, _) <- inferType ctx domE
    domV <- evalIn ctx domTm
    let nm = maybe "_" nameText (bName b)
        ic = if bImplicit b then Impl else Expl
        -- implicit Pi binders join the local implicit context (§16.3.3)
        ctx' = bindCtx nm (bImplicit b) domV ctx
    (codTm, _) <- inferType ctx' body
    pure (CPi ic (binderQ b) nm domTm codTm, VSort 0)
  EForall bs body _ -> elabForall ctx bs body
  EExists bs body sp -> elabExists ctx bs body sp
  ETraitArrow c rest -> do
    (cTm, _) <- inferType ctx c
    cV <- evalIn ctx cTm
    -- the evidence binder joins the local implicit context (§16.3.3)
    let ctx' = bindCtx "_ev" True cV ctx
    (restTm, _) <- inferType ctx' rest
    pure (CPi Impl QW "_ev" cTm restTm, VSort 0)
  EOptionSugar t _ -> do
    (tm, _) <- inferType ctx t
    pure (CApp Expl (CGlob (gPrel "Option")) tm, VSort 0)
  EVariant arms mtail sp -> elabVariant ctx arms mtail sp Nothing
  -- §18.5.1: a lambda label names a return target consumable by
  -- @return@L@ inside the body.
  ELambda mlbl bs body sp -> elabLambda (ctx {ctxReturnTarget = nameText <$> mlbl}) bs body sp Nothing
  ELet binds body _ -> elabLet ctx binds body Nothing
  EBlock ds fin sp -> elabBlock ctx ds fin sp
  EIf alts mels sp -> do
    resT <- freshMetaV ctx
    tm <- checkIf ctx alts mels sp resT
    pure (tm, resT)
  EMatch scrut cases sp -> do
    resT <- freshMetaV ctx
    tm <- checkMatch ctx scrut cases sp resT
    pure (tm, resT)
  -- a do-scope label is only consumable by defer@label, which is
  -- rejected as unsupported at its use site, so the label is inert here
  -- a do block in expression position is a NESTED completion boundary: a
  -- `return@outer` cannot cross it at runtime (it is run as a do value), so
  -- reset the return target here (the function/lambda body do is elaborated
  -- directly by checkAgainstSig/elabLambda, which preserve it). §18.5/§18.8.
  EDo mlbl items sp -> elabDo (ctx {ctxReturnTarget = Nothing}) mlbl items sp Nothing
  EThunk e sp
    -- §5.2: soft keywords shadowed by a local binding are ordinary names
    | Just _ <- lookupCtx "thunk" ctx ->
        infer ctx (EApp (EVar (Name "thunk" sp)) [ArgExplicit e])
    | otherwise -> do
        (tm, ty) <- infer ctx e
        pure (CThunkE tm, VGlobN (gPrel "Thunk") [(Expl, ty)])
  ELazy e sp
    | Just _ <- lookupCtx "lazy" ctx ->
        infer ctx (EApp (EVar (Name "lazy" sp)) [ArgExplicit e])
    | otherwise -> do
        (tm, ty) <- infer ctx e
        pure (CLazyE tm, VGlobN (gPrel "Need") [(Expl, ty)])
  EForce e sp | Just _ <- lookupCtx "force" ctx ->
    infer ctx (EApp (EVar (Name "force" sp)) [ArgExplicit e])
  EForce e sp -> do
    (tm, ty) <- infer ctx e
    t <- forceM ty
    case t of
      VGlobN (GName _ "Thunk") [(_, a)] -> pure (CForceE tm, a)
      VGlobN (GName _ "Need") [(_, a)] -> pure (CForceE tm, a)
      _ -> do
        errAt sp "E_TYPE_EQUALITY_MISMATCH" (Just "kappa.type.mismatch") "force expects a Thunk or Need value"
        anyHole ctx
  EListLit es _ -> do
    elemT <- freshMetaV ctx
    tms <- mapM (\e -> check ctx e elemT) es
    pure
      ( foldr (\h t -> CCtor (gPrel "::") [h, t]) (CCtor (gPrel "Nil") []) tms
      , VGlobN (gPrel "List") [(Expl, elemT)]
      )
  -- §20.5/§20.5.1: a map literal resolves duplicate keys (default: keep last),
  -- mirroring the map-comprehension lowering, so `{ 1: 10, 1: 20 }` keeps 20.
  EMapLit kvs sp -> do
    eqLam <- pairEqLam sp
    comb <- conflictLam ctx Nothing sp
    let entry (k, v) =
          ERecordLit
            [RecItem False (Name "key" sp) (Just k), RecItem False (Name "value" sp) (Just v)]
            sp
        entriesE = EListLit (map entry kvs) sp
    infer ctx (prelApp1 sp "__mapFromEntries" [prelApp1 sp "__mapResolve" [entriesE, eqLam, comb]])
  -- §20.1/§20.3.1: a set literal holds each element at most once, mirroring the
  -- set-comprehension lowering, so `{| 7, 7, 8 |}` has two elements.
  ESetLit es sp -> do
    eqLam <- pairEqLam sp
    infer ctx (prelApp1 sp "__setFromList" [prelApp1 sp "__distinctBy" [EListLit es sp, eqLam]])
  ESectionLeft e op sp ->
    infer ctx (lam1 sp "__x" (\x -> EApp (EVar op) [ArgExplicit e, ArgExplicit x]))
  ESectionRight op e sp ->
    infer ctx (lam1 sp "__x" (\x -> EApp (EVar op) [ArgExplicit x, ArgExplicit e]))
  -- §5.5.1: a bare `(op)` with more than one callable fixity in scope is
  -- ambiguous unless an expected type selects exactly one fixity. The
  -- type-directed disambiguation lives in `check` (a function-typed
  -- position picks the prefix or infix reading by arity); reaching `infer`
  -- means there is no such expected type, so a multi-fixity bare operator
  -- here is the ambiguous case. `(infix op)`/`(prefix op)`/`(postfix op)`
  -- carry an explicit fixity tag and are never ambiguous.
  EOpRef Nothing op sp -> do
    multi <- gets csMultiFixOps
    if nameText op `Set.member` multi
      then do
        report $
          diag SevError StageElaborate "E_OPERATOR_FIXITY_AMBIGUOUS" (Just "kappa.name.ambiguous") sp
            ( "bare operator '(" <> nameText op <> ")' is ambiguous: more than one "
                <> "callable fixity for '" <> nameText op <> "' is in scope and no expected "
                <> "type selects one; write '(infix " <> nameText op <> ")', '(prefix "
                <> nameText op <> ")', or '(postfix " <> nameText op
                <> ")', or supply a type annotation (Spec §5.5.1)"
            )
        anyHole ctx
      else resolveName ctx op
  EOpRef _ op _ -> resolveName ctx op
  EReceiverSection ms args sp ->
    infer ctx . lam1 sp "__x" $ \x ->
      let base = foldl' EDot x ms
       in case args of
            [] -> base
            _ -> EApp base args
  ETry e excepts mfin sp -> elabTry ctx e excepts mfin sp
  ETryMatch e cases excepts mfin sp -> do
    tmp <- freshNameM "__scrut"
    let tn = Name tmp sp
        inner =
          EDo Nothing
            [ DoBind (LetBind False emptyPrefix (PVar tn) Nothing e sp)
            , DoExpr (EMatch (EVar tn) cases sp)
            ]
            sp
    elabTry ctx inner excepts mfin sp
  EHandle deep lblE scrutE cases sp -> elabHandle ctx deep lblE scrutE cases sp Nothing
  EEffRow entries mtail sp -> elabEffRow ctx entries mtail sp
  ESeal e tyE sp -> elabSeal ctx e tyE sp
  ESealExists ws e tyE sp -> elabSealExistsExplicit ctx ws e tyE sp
  EOpenExists e ns pat body sp -> elabOpenExists ctx e ns pat body sp
  EQuote e sp -> elabQuote ctx e sp Nothing
  ECodeQuote e sp -> elabCodeQuote ctx e sp Nothing
  ECodeEscape e sp -> elabCodeEscape ctx e sp
  ESplice e sp -> elabSplice ctx e sp Nothing
  ESpliceInQuote _ sp -> do
    errAt sp "E_QUOTE_SPLICE_OUTSIDE_QUOTE" (Just "kappa.syntax.quotation")
      "the in-quote splice form '${...}' is meaningful only inside a syntax quote '{ ... } (§21.1)"
    anyHole ctx
  EQuoteHole i sp -> case Map.lookup i (ctxQuoteSlots ctx) of
    Just ty -> pure (CGlob (GName primModule "__quoteHole"), ty)
    Nothing -> do
      errAt sp "E_INTERNAL" Nothing "quote grafting slot escaped its quote"
      anyHole ctx
  EBang _ _ sp -> do
    -- §3.1.5A: a splice is a desugaring construct; the diagnostic blames
    -- the user-written splice site as primary and records the desugaring
    -- provenance as a desugared-from related origin.
    report $
      withRelated (related RoleDesugaredFrom sp "monadic splice '!e' desugars to a do-block bind") $
        diag SevError StageElaborate "E_SPLICE_OUTSIDE_DO" Nothing sp
          "monadic splice '!' is only valid inside a do block"
    anyHole ctx
  ERecordPatch e items sp -> elabPatch ctx e items sp
  EComprehension k cs y sp -> elabComprehension ctx k cs y sp
  -- §12.3.1/§31.1: the capture set is part of type identity; encode
  -- as a left-nested '__captures' spine in canonical (sorted) order
  ECaptures e regions _ -> do
    (tTm, _) <- inferType ctx e
    rs <- forM regions $ \rn -> do
      (rTm, rTy) <- infer ctx (EVar rn)
      expectType ctx (nameSpan rn) rTy (VGlobN (gPrel "Region") [])
      pure rTm
    let sorted = sortOn renderTerm (nub rs)
        capTm =
          foldl'
            (\acc r -> CApp Expl (CApp Expl (CGlob (gPrel "__captures")) acc) r)
            tTm
            sorted
    pure (capTm, VSort 0)
  EKindQualified sel n sp -> elabKindQualified ctx sel n sp
  EModuleSig _ sp -> unsupported ctx sp "moduleSig"
  EImpossible sp -> do
    errAt sp "E_IMPOSSIBLE_REACHABLE" (Just "kappa.pattern.unreachable")
      "'impossible' is not provably unreachable here"
    anyHole ctx
  EOpChain {} -> do
    -- the resolver re-associates every chain (§5.5.2); reaching one here
    -- means a resolution diagnostic was already emitted for it
    anyHole ctx
  where
    tupleField i = "_" <> T.pack (show (i + 1))
    lam1 sp nm f =
      ELambda Nothing [simpleBinder (Name nm sp)] (f (EVar (Name nm sp))) sp

check :: Ctx -> Expr -> Value -> CheckM Term
check ctx expr expected0 = do
  expected <- forceM expected0
  case (expr, expected) of
    (ELambda l bs body sp, VPi Impl q nm dom clo)
      | not (firstImplicit bs) -> do
          let ctx' = bindCtx nm True dom ctx
          cod <- clApp clo (VRigid (ctxLen ctx) [])
          inner <- check ctx' (ELambda l bs body sp) cod
          pure (CLam Impl q nm inner)
    -- §12.3.1: a closure literal checked at a capture-annotated type
    -- introduces at the underlying type (the annotation licenses the
    -- captures; it does not change the introduction form)
    (ELambda {}, VGlobN (GName pm "__captures") ((_, inner) : _))
      | pm == preludeModule ->
          check ctx expr =<< forceM inner
    (ELambda mlbl bs body sp, _) -> do
      -- §18.5.1: an explicit lambda label, else (anonymous) a reset so a
      -- `return@outer` cannot cross this user-written lambda boundary.
      (tm, ty) <- elabLambda (ctx {ctxReturnTarget = nameText <$> mlbl}) bs body sp (Just expected)
      expectType ctx sp ty expected
      pure tm
    (_, VPi Impl q nm dom clo)
      | not (isHole expr) -> do
          let ctx' = bindCtx nm True dom ctx
          cod <- clApp clo (VRigid (ctxLen ctx) [])
          inner <- check ctx' expr cod
          pure (CLam Impl q nm inner)
    (EVar n, VSort _)
      | Nothing <- lookupCtx (nameText n) ctx -> do
          (tm, ty) <- inferT ctx (EVar n)
          expectType ctx (nameSpan n) ty expected
          pure tm
    -- §6.6: in type position `()` is surface syntax for the type `Unit`
    -- (the would-be empty record), distinct from the unique `Unit` value
    -- it denotes in term position. A `()` checked against a universe is
    -- therefore the type `Unit`, which inhabits that universe.
    (EUnit _, VSort _) -> pure (CGlob (gPrel "Unit"))
    -- §5.5.1: a bare parenthesized operator at a function-typed
    -- position selects the fixity the expected explicit arity calls
    -- for — unary `(-)` is the prefix reading (negate); otherwise the
    -- reference eta-expands so trailing implicit obligations (the
    -- §28.2.1 checked-arithmetic proofs) insert at the application
    (e, VPi Expl _ _ _ _)
      | Just n <- bareOpRef e
      , isOpSpelling (nameText n)
      , Nothing <- lookupCtx (nameText n) ctx -> do
          arity <- explicitArity (ctxLen ctx) expected
          let sp = nameSpan n
          if arity == 1 && nameText n == "-"
            then check ctx (EVar (Name "negate" sp)) expected
            else do
              let vars = [Name ("__op" <> T.pack (show i)) sp | i <- [1 .. arity]]
                  lam =
                    ELambda Nothing (map simpleBinder vars)
                      (EApp (EVar n) [ArgExplicit (EVar v) | v <- vars]) sp
              check ctx lam expected
    -- §18.1.14: Eff r is a monadic carrier, so 'pure' in an Eff-typed
    -- position injects via the Eff kernel (the prelude 'pure' is the IO
    -- instance; carrier-polymorphic 'pure' is not modelled)
    (EApp (EVar pn) [ArgExplicit pa], VGlobN (GName _ "Eff") [(_, _), (_, aT)])
      | nameText pn == "pure"
      , Nothing <- lookupCtx "pure" ctx -> do
          tm <- check ctx pa aT
          pure (CCtor (gPrel "__EffPure") [tm])
    -- §21.9: 'pure' in an Elab-typed position lifts a meta-phase value
    -- through the elaboration-time Applicative (the prelude 'pure' is
    -- the IO instance; carrier-polymorphic 'pure' is not modelled)
    (EApp (EVar pn) [ArgExplicit pa], VGlobN (GName pm "Elab") [(_, aT)])
      | nameText pn == "pure"
      , pm == preludeModule
      , Nothing <- lookupCtx "pure" ctx -> do
          tm <- check ctx pa aT
          pure (CApp Expl (CGlob (GName primModule "__elabPure")) tm)
    -- §21.1: a quote checked against its Syntax index elaborates the
    -- payload at the index's object type
    (EQuote qe sp, VGlobN (GName pm "Syntax") [(_, tT)])
      | pm == preludeModule -> do
          (tm, _) <- elabQuote ctx qe sp (Just tT)
          pure tm
    -- §23.2: a code quote checked against 'Code t' elaborates its
    -- payload at t
    (ECodeQuote qe sp, VGlobN (GName pm "Code") [(_, tT)])
      | pm == preludeModule -> do
          (tm, _) <- elabCodeQuote ctx qe sp (Just tT)
          pure tm
    -- §21.2: a splice's expected type directs both the admissible
    -- argument types and the elaboration of the produced syntax
    (ESplice se sp, _) -> do
      (tm, ty) <- elabSplice ctx se sp (Just expected)
      expectType ctx sp ty expected
      pure tm
    -- §18.9 threading pun (corpus): a bare variable checked against a
    -- single-field record type whose field has the same spelling is the
    -- record literal `(n = n)` (e.g. `pure file : IO (1 file : File)`)
    (EVar n, VRecordT [(f, ft)])
      | nameText n == f
      , Just (i, entry) <- lookupCtx (nameText n) ctx
      , not (ceVarBind entry) -> do
          ok <- unify ctx (ceType entry) ft
          if ok
            then pure (CRecordV [(f, CVar i)])
            else do
              (tm, ty) <- infer ctx expr
              expectType ctx (nameSpan n) ty expected
              pure tm
    -- (x : T) checked against a universe is a single-field record type
    -- (§13.1); the parser cannot distinguish it from an ascription
    (EAscription (EVar _) _ sp, VSort _) -> do
      (tm, ty) <- inferT ctx expr
      expectType ctx sp ty expected
      pure tm
    -- §7.2: an application checked against a universe is a type
    -- position, so its head prefers the type facet of a same-spelling
    -- data family; arguments of sort 'Type' recurse through this same
    -- case, covering nested parenthesized type applications such as
    -- 'Wrap (Wrap Integer)' or 'List (Wrap Integer)'.
    (EApp _ _, VSort _) -> do
      (tm, ty) <- inferT ctx expr
      expectType ctx (exprSpan expr) ty expected
      pure tm
    (EIf alts mels sp, _) -> checkIf ctx alts mels sp expected
    -- §18.1.21: a handler eliminates into the expected target carrier `m`
    -- (which may be `IO e` or another carrier, not only `Eff r`); thread the
    -- expectation in so non-Eff clause bodies type-check.
    (EHandle deep lblE scrutE cases sp, _) -> do
      (tm, ty) <- elabHandle ctx deep lblE scrutE cases sp (Just expected)
      expectType ctx sp ty expected
      pure tm
    (EMatch scrut cases sp, _) -> checkMatch ctx scrut cases sp expected
    (EDo mlbl items sp, _) -> do
      -- nested do in checked expression position: reset the return target
      -- (a `return@outer` cannot cross this do-value boundary at runtime).
      (tm, ty) <- elabDo (ctx {ctxReturnTarget = Nothing}) mlbl items sp (Just expected)
      expectType ctx sp ty expected
      pure tm
    (ELet binds body _, _) -> do
      (tm, ty) <- elabLet ctx binds body (Just expected)
      expectType ctx (exprSpan body) ty expected
      pure tm
    -- operator/receiver sections check as their lambda desugaring so
    -- the expected type guides the receiver (§16.1.6)
    (ESectionLeft e op sp, _) ->
      check ctx (lamSection sp "__x" (\x -> EApp (EVar op) [ArgExplicit e, ArgExplicit x])) expected
    (ESectionRight op e sp, _) ->
      check ctx (lamSection sp "__x" (\x -> EApp (EVar op) [ArgExplicit x, ArgExplicit e])) expected
    (EReceiverSection ms args sp, _) ->
      check ctx
        ( lamSection sp "__x" $ \x ->
            let base = foldl' EDot x ms
             in case args of
                  [] -> base
                  _ -> EApp base args
        )
        expected
    (EThunk e _, VGlobN (GName _ "Thunk") [(_, a)]) -> CThunkE <$> check ctx e a
    (ELazy e _, VGlobN (GName _ "Need") [(_, a)]) -> CLazyE <$> check ctx e a
    (_, VGlobN (GName _ "Thunk") [(_, a)]) -> suspendOrInfer CThunkE expected a
    (_, VGlobN (GName _ "Need") [(_, a)]) -> suspendOrInfer CLazyE expected a
    -- expected-type-directed injection (§13.1.3) must see literals too
    (_, VVariantT members)
      | not (isVariant expr) -> do
          (tm, ty) <- infer ctx expr
          (tm1, ty1) <- insertAllImplicits ctx (exprSpan expr) tm ty
          injectInto ctx tm1 ty1 members expected (exprSpan expr)
    -- §21.6 convenience reflection queries: an 'Elab'-typed position
    -- keeps the ordinary action; any other position runs the
    -- elaboration-time query at the call site ('elabReflQuery')
    (EApp (EVar qn) args, _)
      | nameText qn `elem` reflQueryNames
      , Nothing <- lookupCtx (nameText qn) ctx -> do
          (tm, ty) <- elabReflQuery ctx qn args (Just expected)
          expectType ctx (exprSpan expr) ty expected
          pure tm
    -- §16.1.7.1/§12.2.1: an all-explicit application checked against a
    -- known expected type pre-unifies its result type with the
    -- expectation, so arguments see solved domains (binder quantities
    -- through polymorphic wrappers, literal defaulting, dependent
    -- constructor indices)
    -- §20.9: a carrier-prefixed comprehension in checked position
    -- still selects its sink through the type-valued prefix (the
    -- generic application path would apply the data constructor)
    (EApp f args, _)
      | not (null args)
      , ArgExplicit (EComprehension k cs y csp) <- last args -> do
          st0 <- get
          mPrefix <- carrierPrefix ctx f (init args)
          case mPrefix of
            Just prefix -> do
              (tm, ty) <- elabComprehensionC ctx k cs y csp (Just prefix)
              expectType ctx csp ty expected
              pure tm
            Nothing -> do
              put st0
              (tm, ty) <- infer ctx expr
              (tm1, ty1) <- insertAllImplicits ctx (exprSpan expr) tm ty
              expectType ctx (exprSpan expr) ty1 expected
              pure tm1
    -- §5.5.1: `(-) e` at a non-function expected type selects the
    -- prefix fixity — the application of bare `(-)` to one explicit
    -- argument in a saturated position is negation
    (EApp hd [ArgExplicit a], _)
      | Just n <- bareOpRef hd
      , nameText n == "-"
      , Nothing <- lookupCtx "-" ctx
      , notPi expected ->
          check ctx (EApp (EVar (Name "negate" (nameSpan n))) [ArgExplicit a]) expected
    (EApp f args, _)
      | all isExplicitArg args, not (null args) -> do
          mproj <- projectionHead ctx f
          mRecvProj <- maybe (projRecvApp ctx f args) (const (pure Nothing)) mproj
          case (mproj, mRecvProj) of
            (_, Just (tm, ty)) -> do
              expectType ctx (exprSpan expr) ty expected
              pure tm
            (Just _, _) -> do
              (tm, ty) <- infer ctx expr
              (tm1, ty1) <- insertAllImplicits ctx (exprSpan expr) tm ty
              special <- projDescriptorMismatch ctx expr ty1 expected
              unless special $
                expectType ctx (exprSpan expr) ty1 expected
              pure tm1
            _ -> elabAppChecked ctx f args expected (exprSpan expr)
    (EIntLit v msuf sp, _) -> do
      (tm, ty) <- elabIntLit ctx v msuf sp (Just expected)
      expectType ctx sp ty expected
      pure tm
    (EFloatLit v msuf sp, _) -> do
      (tm, ty) <- elabFloatLit ctx v msuf sp (Just expected)
      expectType ctx sp ty expected
      pure tm
    (EVariant arms mtail sp, _) -> do
      (tm, ty) <- elabVariant ctx arms mtail sp (Just expected)
      expectType ctx sp ty expected
      pure tm
    -- §13.2.1 dependent record literals: sibling references through
    -- 'this' (in field types or initializers) need telescope-ordered
    -- elaboration
    -- §13.2.10: a signature type with opaque members is introduced
    -- only through 'seal ... as ...', never by a direct record literal
    (ERecordLit _ lsp, VSigT _ _) -> do
      errAt lsp "E_SEAL_DIRECT_LITERAL_FOR_SIGNATURE" (Just "kappa-hs.seal.direct-literal")
        "a record literal cannot introduce a signature type with opaque members; use 'seal ... as ...' (§13.2.10)"
      fst <$> anyHole ctx
    (ERecordLit items lsp, VRecordT fs) -> do
      depTy <- recordTypeIsDependent ctx fs
      -- a capture-annotated or suspension-typed field needs
      -- field-directed checking (the literal introduces at the
      -- underlying type; §16.1.7.1 inserts the suspension)
      let needsDirected fuel v0
            | fuel <= (0 :: Int) = pure False
            | otherwise = do
                v <- forceM v0
                if isCapturesV v || isSuspV v
                  then pure True
                  else case v of
                    VRecordT fs' -> or <$> mapM (needsDirected (fuel - 1) . snd) fs'
                    -- a variant-typed field takes expected-type-directed
                    -- injection (§13.1.3)
                    VVariantT _ -> pure True
                    _ -> pure False
      capTy <- or <$> mapM (needsDirected 4 . snd) fs
      let depVal =
            isNothing (lookupCtx "this" ctx)
              && not (null (concat [surfaceThisRefs e | RecItem _ _ (Just e) <- items]))
      if depTy || depVal || capTy
        then do
          (tm, ty) <- elabDependentRecordLit ctx items fs lsp
          expectType ctx lsp ty expected
          pure tm
        else do
          (tm, ty) <- infer ctx expr
          (tm1, ty1) <- insertAllImplicits ctx lsp tm ty
          expectType ctx lsp ty1 expected
          pure tm1
    -- a parenthesized list in type position is the tuple type (§13.1)
    (ETuple {}, VSort _) -> do
      (tm, ty) <- inferT ctx expr
      expectType ctx (exprSpan expr) ty expected
      pure tm
    (ETuple es sp, VRecordT fs)
      | length es == length fs -> do
          -- expected-type-directed punning (§13.1.2): a parenthesized
          -- list of bare names matching the record's field names is the
          -- punned record literal
          let punVars = [(nameText n, EVar n) | EVar n <- es]
          tms <-
            if length punVars == length es && sort (map fst punVars) == map fst fs
              then forM fs $ \(fn, fty) ->
                check ctx (fromMaybe (ETuple es sp) (lookup fn punVars)) fty
              else zipWithM (\e (_, t) -> check ctx e t) es fs
          pure (CRecordV (zip (map fst fs) tms))
    -- expected-type-directed constructor selection: when the expected
    -- type is a data type declaring a constructor with the bare head's
    -- spelling and ordinary resolution would yield a same-spelling
    -- constructor of a *different* data type (or nothing at all), the
    -- expected type's constructor is selected — constructors are
    -- static members of their data type (§7.2) and the unqualified
    -- spelling abbreviates that selection in checked position
    (e, VGlobN dgName _)
      | Just (hn, args) <- bareCtorHead e
      , Nothing <- lookupCtx (nameText hn) ctx -> do
          st0 <- get
          mRetarget <- case Map.lookup dgName (csDatas st0) of
            Just di
              | (ctorG : _) <- [c | c <- diCtors di, gnameText c == nameText hn] -> do
                  mg <- lookupGlobalName (nameText hn)
                  case mg of
                    Nothing -> pure (Just ctorG)
                    Just g
                      | g /= ctorG
                      , Just ci <- Map.lookup g (csCtors st0)
                      , ciData ci /= dgName ->
                          pure (Just ctorG)
                    _ -> pure Nothing
            _ -> pure Nothing
          case mRetarget of
            Just ctorG -> do
              mt <- globalTerm ctorG
              case mt of
                Just (hTm, hTy) -> do
                  (tm, ty) <- elabSpine ctx (exprSpan e) hTm hTy args
                  (tm1, ty1) <- insertAllImplicits ctx (exprSpan e) tm ty
                  expectType ctx (exprSpan e) ty1 expected
                  pure tm1
                Nothing -> checkFallthrough expected
            Nothing -> checkFallthrough expected
    _ -> checkFallthrough expected
  where
    checkFallthrough expected = do
      (tm, ty) <- infer ctx expr
      (tm1, ty1) <- insertAllImplicits ctx (exprSpan expr) tm ty
      special <- projDescriptorMismatch ctx expr ty1 expected
      unless special $
        expectType ctx (exprSpan expr) ty1 expected
      pure tm1
    -- a bare (possibly applied) capitalized head
    bareCtorHead = \case
      EVar n | upperHead n -> Just (n, [])
      EApp (EVar n) args | upperHead n -> Just (n, args)
      _ -> Nothing
    upperHead n = case T.uncons (nameText n) of
      Just (c, _) -> c >= 'A' && c <= 'Z'
      Nothing -> False
    isOpSpelling t = case T.uncons t of
      Just (c, _) ->
        not (c == '_' || (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c >= '\128')
      Nothing -> False
    notPi = \case
      VPi {} -> False
      _ -> True
    bareOpRef = \case
      EVar n -> Just n
      EOpRef Nothing n _ -> Just n
      _ -> Nothing
    explicitArity lvl v = do
      t <- forceM v
      case t of
        VPi Expl _ _ _ clo -> do
          cod <- clApp clo (VRigid lvl [])
          (1 +) <$> explicitArity (lvl + 1) cod
        VPi Impl _ _ _ clo -> do
          cod <- clApp clo (VRigid lvl [])
          explicitArity (lvl + 1) cod
        _ -> pure (0 :: Int)
    -- §16.1.5: a fully applied projection in descriptor-typed position
    -- gets the dedicated diagnostic rather than a plain mismatch
    projDescriptorMismatch c ex actual expect = case expect of
      VGlobN (GName pm dn) _
        | pm == preludeModule
        , dn `elem` ["Projector", "Getter", "Opener", "Setter", "Sinker"]
        , EApp f args <- ex -> do
            mproj <- projectionHead c f
            case mproj of
              Just (_, pj) | projFullApp pj args -> do
                ok <- unify c actual expect
                if ok
                  then pure False
                  else do
                    errAt (exprSpan ex) "E_PROJECTION_DESCRIPTOR_VALUE_EXPECTED"
                      (Just "kappa-hs.projection.descriptor")
                      "a fully applied projection denotes its focus value, not a first-class descriptor; use the unapplied projection name (§16.1.5)"
                    pure True
              _ -> pure False
      _ -> pure False
    -- §16.1.7.1: a failed suspension insertion at an application
    -- boundary is an application-argument error
    suspInsert wrap a = do
      retag <- gets csArgIndexRetag
      nBefore <- gets (length . csDiags)
      tm <- wrap <$> check ctx expr a
      when retag (retagNewMismatches nBefore)
      pure tm
    -- §16.1.7.1 suspension insertion in Thunk/Need position.  Elaborate the
    -- expression ONCE (inference): if it is already a suspension (its type
    -- unifies with the expected Thunk/Need type), use it as-is; if its type is
    -- the content type @a@, suspend the already-elaborated term; otherwise (the
    -- expression needs expected-type-directed checking — e.g. a bare literal or
    -- a variant injection) fall back to checking it against @a@.  Reusing the
    -- inferred term is essential: without it a nested chain of Thunk-argument
    -- operators (e.g. `||`/`&&`) re-elaborated its tail at every level once for
    -- the speculative inference and again for the checking insertion, which is
    -- EXPONENTIAL in nesting depth (the H-4 self-hosting pathology).
    suspendOrInfer wrap expd a = do
      saved <- get
      retag <- gets csArgIndexRetag
      nBefore <- gets (length . csDiags)
      (tm, ty) <- infer ctx expr
      afterInfer <- get
      okT <- unify ctx ty expd -- already a Thunk/Need value?
      if okT
        then pure tm
        else do
          put afterInfer -- discard the failed unification, keep the inference
          okA <- unify ctx ty a -- a plain value of the content type?
          if okA
            then do
              -- suspend the already-elaborated term (no re-elaboration); retag
              -- any mismatch diagnostics from the inference to the argument
              -- index, exactly as the checking-mode 'suspInsert' would, so the
              -- diagnostic code/family is identical to the pre-fix path.
              when retag (retagNewMismatches nBefore)
              pure (wrap tm)
            else put saved >> suspInsert wrap a -- needs checking-mode against a
    firstImplicit (b : _) = bImplicit b
    firstImplicit [] = False
    isExplicitArg = \case
      ArgExplicit _ -> True
      _ -> False
    isHole = \case
      EHole {} -> True
      _ -> False
    isVariant = \case
      EVariant {} -> True
      _ -> False

-- helper shared by section desugarings
lamSection :: Span -> Text -> (Expr -> Expr) -> Expr
lamSection sp nm f =
  ELambda Nothing [simpleBinder (Name nm sp)] (f (EVar (Name nm sp))) sp

-- expected-type-directed injection / widening (§13.1.3)
injectInto :: Ctx -> Term -> Value -> [Value] -> Value -> Span -> CheckM Term
injectInto ctx tm ty members expected sp = do
  t <- forceM ty
  case t of
    VVariantT src -> do
      srcTags <- mapM (tagOf ctx) src
      tgtTags <- mapM (tagOf ctx) members
      if all (`elem` tgtTags) srcTags
        then pure tm
        else do
          expectType ctx sp ty expected
          pure tm
    _ -> do
      tag <- tagOf ctx t
      tags <- mapM (tagOf ctx) members
      if tag `elem` tags
        then pure (CInject tag tm)
        else do
          expectType ctx sp ty expected
          pure tm

-- | Stable member identity of a variant member type (§31.3): rendered
-- from the alias-normalized type so @Int@ and @Integer@ coincide.
tagOf :: Ctx -> Value -> CheckM Text
tagOf ctx v = do
  ec <- ec_
  pure (renderTerm (quote ec (ctxLen ctx) (deepForceV ec v)))

-- normalize alias heads recursively through type structure
deepForceV :: EvalCtx -> Value -> Value
deepForceV ec = go (32 :: Int)
  where
    go :: Int -> Value -> Value
    go 0 v = v
    go fuel v = case force ec v of
      VGlobN g sp -> VGlobN g [(ic, go (fuel - 1) a) | (ic, a) <- sp]
      VCtor g as -> VCtor g (map (go (fuel - 1)) as)
      VRecordT fs -> VRecordT [(n, go (fuel - 1) t) | (n, t) <- fs]
      VVariantT ms -> VVariantT (map (go (fuel - 1)) ms)
      v' -> v'

inferType :: Ctx -> Expr -> CheckM (Term, Int)
-- a match in type position selects the type facet in its arms
-- (dependent-match types, §17.1.4)
inferType ctx (EMatch scrut cases msp) = do
  tm <- checkMatch ctx scrut cases msp (VSort 0)
  pure (tm, 0)
inferType ctx e = do
  (tm, ty) <- inferT ctx e
  goSort tm ty
  where
    goSort tm ty = do
      t <- forceM ty
      case t of
        VSort n -> pure (tm, n)
        VFlex m [] -> solveMeta m (VSort 0) >> pure (tm, 0)
        -- compatibility accommodation for the external corpus: `IO a`
        -- written for `IO ?e a` (§18.1 IO : Type -> Type -> Type); the
        -- missing error parameter becomes a fresh metavariable
        VPi Expl _ _ _ _
          | CApp Expl (CGlob g) argTm <- tm
          , g == gPrel "IO" -> do
              m <- freshMeta
              pure (CApp Expl (CApp Expl (CGlob g) m) argTm, 0)
        other -> do
          oT <- quoteIn ctx other
          errAt (exprSpan e) "E_NOT_A_TYPE" (Just "kappa.type.mismatch")
            ("expected a type; this expression has type " <> renderTerm oT)
          pure (tm, 0)

-- type-position inference: prefer the type facet for head names (§7.2).
inferT :: Ctx -> Expr -> CheckM (Term, Value)
inferT ctx e = case e of
  -- in type position a universe spelling (incl. '*') is the universe
  EVar n
    | Nothing <- lookupCtx (nameText n) ctx
    , Just lvl <- sortName (nameText n) ->
        pure (CSort lvl, VSort (lvl + 1))
  EVar n
    | Nothing <- lookupCtx (nameText n) ctx
    , Nothing <- sortName (nameText n) -> do
        mthis <- gets csThis
        case mthis of
          -- §14.2.1: trait-body sibling members shadow same-spelling
          -- globals, also in type position
          Just (ThisTraitSibs fields)
            | isJust (lookup (nameText n) fields) -> infer ctx e
          _ -> do
            mg <- lookupGlobalName (nameText n)
            case mg of
              Just g -> do
                mt <- globalType g
                case mt of
                  Just r -> pure r
                  Nothing -> infer ctx e
              Nothing -> infer ctx e
  -- compatibility accommodation for the external corpus: the corpus
  -- writes the §12.4 sized array as 'Array n elem' over the prelude
  -- collection carrier 'Array : Type -> Type'. The size index is kept
  -- for definitional equality inside a phantom '__sizedOf n elem'
  -- element, so 'Array n a ≡ Array m a' iff 'n ≡ m'.
  EApp (EVar hd) [ArgExplicit nE, ArgExplicit elemE]
    | nameText hd == "Array"
    , Nothing <- lookupCtx "Array" ctx -> do
        mg <- lookupGlobalName "Array"
        if mg /= Just (gPrel "Array")
          then do
            (fTm, fTy) <- inferT ctx (EVar hd)
            elabSpine ctx (nameSpan hd) fTm fTy [ArgExplicit nE, ArgExplicit elemE]
          else do
            nTm <- check ctx nE (VGlobN (gPrel "Nat") [])
            (elemTm, _) <- inferType ctx elemE
            let sized = CApp Expl (CApp Expl (CGlob (gPrel "__sizedOf")) nTm) elemTm
            pure (CApp Expl (CGlob (gPrel "Array")) sized, VSort 0)
  -- §11.3.1 row constraints take field labels: 'LacksRec r age'
  -- elaborates the label to a string literal
  EApp (EVar hd) [ArgExplicit rowE, ArgExplicit (EVar lbl)]
    | nameText hd == "LacksRec"
    , Nothing <- lookupCtx "LacksRec" ctx
    , Nothing <- lookupCtx (nameText lbl) ctx -> do
        rowTm <- check ctx rowE (VGlobN (gPrel "RecRow") [])
        let lacks = CApp Expl (CApp Expl (CGlob (gPrel "LacksRec")) rowTm) (CLit (LitStr (nameText lbl)))
        pure (lacks, VSort 0)
  EApp f args -> do
    (fTm, fTy) <- inferT ctx f
    withArgFlatFor f (elabSpine ctx (exprSpan f) fTm fTy args)
  -- a parenthesized tuple in type position is a positional record type
  -- (§13.1): (Integer, String) ≡ (_1 : Integer, _2 : String)
  ETuple es _ -> do
    fields <- forM (zip [1 :: Int ..] es) $ \(i, fe) -> do
      (t, _) <- inferType ctx fe
      pure ("_" <> T.pack (show i), t)
    pure (CRecordT fields, VSort 0)
  -- §7.2: in type position a module-qualified name selects the TYPE
  -- facet of a same-spelling data family (term position prefers the
  -- constructor facet)
  EDot base (DotName m)
    | Just segNames <- dottedPathOf base
    , (b : restSegs) <- map nameText segNames
    , Nothing <- lookupCtx b ctx -> do
        st <- get
        let mmn = case Map.lookup b (csModuleAliases st) of
              Just target
                | null restSegs -> Just target
              _
                | ModuleName (b : restSegs) == csModule st -> Just (csModule st)
                | Map.member (ModuleName (b : restSegs)) (csModuleExports st) ->
                    Just (ModuleName (b : restSegs))
                | null restSegs && Map.member (ModuleName [b]) (csModuleExports st) ->
                    Just (ModuleName [b])
                | otherwise -> Nothing
        case mmn of
          Just mn
            | g <- GName mn (nameText m)
            , Map.member g (csGlobals st) -> do
                mr <- globalType g
                case mr of
                  Just r -> pure r
                  Nothing -> infer ctx e
          _ -> infer ctx e
  -- (x : T) in type position is a single-field record type (§13.1); the
  -- parser cannot distinguish it from an ascription
  EAscription (EVar n) tyE _
    | isLowerName (nameText n) -> do
        (t, _) <- inferType ctx tyE
        pure (CRecordT [(nameText n, t)], VSort 0)
  _ -> infer ctx e
  where
    isLowerName t = case T.uncons t of
      Just (c, _) -> c >= 'a' && c <= 'z'
      Nothing -> False
    dottedPathOf = \case
      EVar b -> Just [b]
      EDot b (DotName n) -> (++ [n]) <$> dottedPathOf b
      _ -> Nothing

elabForall :: Ctx -> [Binder] -> Expr -> CheckM (Term, Value)
elabForall ctx0 bs0 body = go ctx0 bs0
  where
    go ctx [] = do
      (tm, _) <- inferType ctx body
      pure (tm, VSort 0)
    go ctx (b : rest) = do
      domTm <- case bType b of
        Just t -> fst <$> inferType ctx t
        Nothing -> pure (CSort 0) -- `forall a.` binds a : Type (§11.3)
      domV <- evalIn ctx domTm
      let nm = maybe "_" nameText (bName b)
          q = maybe Q0 (qOf . Just) (bpQuantity (bPrefix b))
          ctx' = bindCtx nm False domV ctx
      (restTm, _) <- go ctx' rest
      pure (CPi Impl q nm domTm restTm, VSort 0)

-- | §13.2.11 anonymous existential package types. @exists (a1:S1)
-- ... (an:Sn). T@ is surface sugar that elaborates to the §13.2.10
-- sealed-package machinery: a closed signature type whose first members
-- are the hidden witnesses (each an @opaque 0@ member) and whose
-- remaining member(s) are the payload view of @T@:
--
--   * a record/signature payload contributes its fields directly,
--     under their source labels (these are source-addressable);
--   * any other payload becomes one anonymous payload member under the
--     internal label '⟨payload⟩' (not source-addressable).
--
-- Witness binder names are binders only (Spec.md 13321): each elaborates
-- to an internal member label '⟨wit_i⟩' that source code cannot spell,
-- so witnesses are never projectable and never rendered as public
-- fields (Spec.md 13314, 13316-13317). The binder name resolves to its
-- witness during elaboration through the §13.2.1 'this'-sibling
-- machinery; we then rename those @this.<binder>@ projections to the
-- internal label so the field telescope refers to the witness by its
-- canonical internal name. Witnesses being @opaque 0@ are erased static
-- metadata (§31.2). Internal labels are position-based so alpha-equivalent
-- existential types elaborate to the same shape (Spec.md 13322).
elabExists :: Ctx -> [Binder] -> Expr -> Span -> CheckM (Term, Value)
elabExists ctx bs body sp = do
  -- distinct witness names (§13.2.11 surface-name restriction)
  let witNames = [maybe "_" nameText (bName b) | b <- bs]
  forM_ (duplicatesOf (filter (/= "_") witNames)) $ \n ->
    errAt sp "E_RECORD_DUPLICATE_FIELD" (Just "kappa-hs.record.duplicate-field")
      ("an 'exists' type binds the witness name '" <> n <> "' more than once (§13.2.11)")
  -- binder name -> internal witness label (positional). Anonymous '_'
  -- binders still occupy a witness slot but carry no source name.
  let labelOf = zip witNames (map existsWitLabel [0 ..])
  -- elaborate the witness telescope, each field seeing earlier witnesses
  -- through 'this' (the package), then the payload view
  witFields <- goWits labelOf [] (zip3 [0 ..] witNames bs)
  -- (internal label, type) oldest-first, with binder names exposed under
  -- 'this' for resolving later witness/body references
  let witDone = [(n, v) | (n, _, _, v) <- witFields]
  payloadFields0 <- withThis (Just (ThisType witDone)) payloadView
  -- rename binder-name 'this' projections in the payload to the internal
  -- witness labels, mirroring the witness telescope
  let payloadFields = [(fn, renameThisLabels labelOf t) | (fn, t) <- payloadFields0]
      allFields = [(lbl, t) | (_, lbl, t, _) <- witFields] ++ payloadFields
      fields = sortOn fst allFields
      opaqs = sort [lbl | (_, lbl, _, _) <- witFields]
  pure (CSigT opaqs (CRecordT fields), VSort 0)
  where
    -- each witness field, elaborated with prior witnesses in 'this'.
    -- The accumulator threads (binderName, type) so the binder name
    -- resolves to its witness; the produced field type is rewritten so
    -- its 'this' projections name the internal labels instead.
    goWits _ _ [] = pure []
    goWits labelOf done ((i, nm, b) : rest) = do
      (t0, _) <- withThis (Just (ThisType (reverse done))) $ case bType b of
        Just t -> inferType ctx t
        Nothing -> pure (CSort 0, 0) -- `exists a.` binds a : Type (§13.2.11)
      let t0' = renameThisLabels labelOf t0
      tV <- evalIn ctx t0'
      -- expose the witness under its binder name for later references,
      -- but record the field under its internal label
      let lbl = existsWitLabel i
          ent = (nm, lbl, t0', tV)
      (ent :) <$> goWits labelOf ((nm, tV) : done) rest
    -- the payload view of the existential body (§13.2.11)
    payloadView = do
      (tTm, _) <- inferType ctx body
      tV <- forceM =<< evalIn ctx tTm
      case tV of
        -- record/signature payload: contribute its fields directly,
        -- under their source labels (source-addressable, Spec.md 13324)
        VRecordT fs -> recFields fs
        VSigT _ inner ->
          forceM inner >>= \case
            VRecordT fs -> recFields fs
            _ -> anonPayload tTm
        _ -> anonPayload tTm
      where
        recFields fs = forM fs $ \(fn, fty) -> (,) fn <$> quoteIn ctx fty
        -- one anonymous payload slot at quantity ω under the internal
        -- '⟨payload⟩' label (Spec.md 13316-13317, 13279-13280: not
        -- 'value', not source-addressable)
        anonPayload tTm = pure [(existsPayloadLabel, tTm)]

-- | Rewrite @this.<binderName>@ projections to @this.<internalLabel>@
-- inside an elaborated existential member type, per the binder->label
-- map. Only projections rooted at the §13.2.1 'this' neutral are
-- renamed (other projections keep their labels).
renameThisLabels :: [(Text, Text)] -> Term -> Term
renameThisLabels labelOf = go
  where
    go t = case t of
      CProj e f
        | CGlob g <- e, g == thisG, Just lbl <- lookup f labelOf -> CProj e lbl
        | otherwise -> CProj (go e) f
      -- P0.4: renaming a this-label invalidates the fixed offset, so DROP to a
      -- name-based CProj when renamed; otherwise keep the CProjAt index.
      CProjAt e f i
        | CGlob g <- e, g == thisG, Just lbl <- lookup f labelOf -> CProj e lbl
        | otherwise -> CProjAt (go e) f i
      CLam ic q n b -> CLam ic q n (go b)
      CPi ic q n a b -> CPi ic q n (go a) (go b)
      CApp ic f a -> CApp ic (go f) (go a)
      CCtor g as -> CCtor g (map go as)
      CMatch s alts -> CMatch (go s) [CaseAlt p (fmap go gd) (go b) | CaseAlt p gd b <- alts]
      CRecordT fs -> CRecordT [(n, go x) | (n, x) <- fs]
      CRecordV fs -> CRecordV [(n, go x) | (n, x) <- fs]
      CVariantT ms -> CVariantT (map go ms)
      CInject tag e -> CInject tag (go e)
      CLet q n a b c -> CLet q n (go a) (go b) (go c)
      CLetRec q n a b c -> CLetRec q n (go a) (go b) (go c)
      CSealE ls e -> CSealE ls (go e)
      CSigT ls e -> CSigT ls (go e)
      CThunkE e -> CThunkE (go e)
      CLazyE e -> CLazyE (go e)
      CForceE e -> CForceE (go e)
      CIf a b c -> CIf (go a) (go b) (go c)
      CQuote qs slots -> CQuote qs (map go slots)
      CGlob _ -> t
      CVar _ -> t
      CSort _ -> t
      CLit _ -> t
      CMeta _ -> t
      CDo _ _ -> t
-- | Check an all-explicit application against an expected function
-- type by peeling the callee's Pi spine with placeholder metas,
-- unifying the result type with the expectation FIRST, and only then
-- elaborating the arguments — so an argument lambda is checked against
-- the solved domain (binder quantities included). Falls back to the
-- ordinary infer-then-unify path when the shape does not match.
-- | Is the application head a plain (non-constructor, non-operator)
-- function reference? Selects the §16.1.7.1 flat-argument-mismatch
-- diagnostic in 'expectType'.
withArgFlatFor :: Expr -> CheckM a -> CheckM a
withArgFlatFor f act = do
  flat <- case f of
    EVar n
      | Just (c, _) <- T.uncons (nameText n)
      , c == '_' || (c >= 'a' && c <= 'z') -> do
          mg <- lookupGlobalName (nameText n)
          case mg of
            Just g -> gets (not . Map.member g . csCtors)
            Nothing -> pure True
    _ -> pure False
  old <- gets csArgFlatOk
  modify' $ \st -> st {csArgFlatOk = flat}
  r <- act
  modify' $ \st -> st {csArgFlatOk = old}
  pure r

-- | Run an explicit-argument check with §16.1.7.1/§16.1.8 argument-index
-- retagging enabled, restoring the prior flag afterward. A mismatch
-- raised while checking an explicit argument against its parameter type
-- is reclassified as an application-argument error (see 'expectType').
withArgIndexRetag :: CheckM a -> CheckM a
withArgIndexRetag act = do
  old <- gets csArgIndexRetag
  modify' $ \st -> st {csArgIndexRetag = True}
  r <- act
  modify' $ \st -> st {csArgIndexRetag = old}
  pure r

-- | Check one explicit argument @e@ of quantity @q@ against the binder
-- domain @dom@, shared by the two application-spine algorithms (the
-- 'Slot'-folding 'step' and the recursive 'elabSpine'). The argument is
-- checked under the binder's demand ('demandOfQ') with argument-index
-- retagging enabled (§16.1.7.1) so any equality mismatch is attributed
-- to this argument slot. A non-type argument supplied to a type-former's
-- @Type@ slot is an application-argument error rather than a plain
-- mismatch (§16.1), so when @dom@ is a universe the freshly emitted
-- mismatches are retagged via 'retagNewMismatches'; for the ordinary
-- (non-sort) domain this branch is a no-op.
checkExplicitArg :: Ctx -> Q -> Expr -> Value -> CheckM Term
checkExplicitArg ctx q e dom = do
  domF <- forceM dom
  nBefore <- gets (length . csDiags)
  aTm <- withArgIndexRetag (withDemand (demandOfQ q) (check ctx e dom))
  case domF of
    VSort _ -> retagNewMismatches nBefore
    _ -> pure ()
  pure aTm

-- | One planned argument slot of a checked application spine
-- ('elabAppChecked'): a kind-like implicit placeholder, an evidence
-- implicit resolved after result-type pre-unification, or an explicit
-- argument expression checked against its (pre-solved) domain.
data AppSlot
  = SlotKind Term
  | SlotEvid Q Value Value
  | -- | An explicit argument slot, carrying the placeholder meta's id
    -- and value plus a 'Bool' that records whether the function's
    -- codomain actually depends on this argument. When 'False' (a
    -- non-dependent arrow), the placeholder meta is solved directly
    -- (O(1)) instead of unified (O(size)), since it never reaches the
    -- result type — see 'step'.
    SlotExpl Q Expr Value MetaId Value Bool

elabAppChecked :: Ctx -> Expr -> [Arg] -> Value -> Span -> CheckM Term
elabAppChecked ctx f args expected sp = withArgFlatFor f $ do
  st0 <- get
  (fTm, fTy) <- infer ctx f
  plan <- peel fTy args []
  done <- case plan of
    Nothing -> pure Nothing
    Just (slots, resTy) -> do
      ok <- unify ctx resTy expected
      if not ok
        then pure Nothing
        else do
          tm <- foldM step fTm slots
          pure (Just tm)
  case done of
    Just tm -> pure tm
    Nothing -> do
      put st0
      (tm, ty) <- infer ctx (EApp f args)
      (tm1, ty1) <- insertAllImplicits ctx sp tm ty
      expectType ctx sp ty1 expected
      pure tm1
  where
    peel ty as0 acc = do
      tyF <- forceM ty
      case tyF of
        -- kind-like implicits become bare placeholders; evidence
        -- implicits keep the ordinary resolution ladder, run after
        -- the result type has been unified with the expectation so
        -- the goal sees solved metas (§16.1.7.1, §6.1.5). Trailing
        -- implicits (e.g. §28.2.1 proof obligations) are saturated
        -- like 'insertAllImplicits' does on the inference path.
        VPi Impl q _ dom clo -> do
          kindLike <- isKindLike (ctxLen ctx) dom
          m <- freshMeta
          mV <- evalIn ctx m
          ty' <- clApp clo mV
          let slot =
                if kindLike
                  then SlotKind m
                  else SlotEvid q dom mV
          peel ty' as0 (slot : acc)
        VPi Expl q _ dom clo@(Closure _ cloBody)
          | (ArgExplicit e : as) <- as0 -> do
              mid <- freshMetaId
              mV <- evalIn ctx (CMeta mid)
              ty' <- clApp clo mV
              let dep = coreUsesVar0 cloBody
              peel ty' as ((SlotExpl q e dom mid mV dep) : acc)
        _
          | [] <- as0 -> pure (Just (reverse acc, tyF))
          | otherwise -> pure Nothing
    step tm (SlotKind m) = pure (CApp Impl tm m)
    step tm (SlotEvid q dom mV) = do
      -- §3.2.3 proof obligations are postponed to the pending queue
      -- even when fully solved: the boolean branch facts they reduce
      -- under may themselves be stuck on evidence metas that only the
      -- end-of-declaration flush solves
      isEq <- isEqGoal dom
      ev <-
        if isEq
          then do
            mid <- freshMetaId
            bfs <- gets csBoolFacts
            modify' $ \st -> st {csPending = (mid, dom, sp, ctx, bfs) : csPending st}
            pure (CMeta mid)
          else resolveImplicitQ ctx sp q dom
      evV <- evalIn ctx ev
      _ <- unify ctx mV evV
      pure (CApp Impl tm ev)
    step tm (SlotExpl q e dom mid mV dep) = do
      aTm <- checkExplicitArg ctx q e dom
      aV <- evalIn ctx aTm
      -- The placeholder meta 'mid' was substituted into the result type
      -- in 'peel'. When the codomain depends on this argument we must
      -- 'unify' (it may meet an existing structure in the result). When
      -- it does NOT (a non-dependent arrow — the common case for
      -- operator/application chains), 'mid' appears nowhere in the
      -- result, so a direct O(1) 'solveMeta' is equivalent to the full
      -- 'unify' (which would otherwise 'quote' the whole argument value,
      -- costing O(size) per slot → O(n²) over a deep chain) yet keeps
      -- the meta-solution state byte-identical for downstream rendering
      -- and §3.1.11 cascade suppression.
      if dep
        then unify ctx mV aV >> pure ()
        else do
          -- match what 'unify'→'solveFlex' would store (the forced
          -- value), just without its O(size) 'quote'/occurs check, which
          -- is sound here because 'mid' is fresh and unreferenced.
          aVf <- forceM aV
          solveMeta mid aVf
      pure (CApp Expl tm aTm)

-- | Is the value a (possibly parameterized) type former — i.e. is its
-- final codomain a universe?
finalIsSort :: Ctx -> Value -> CheckM Bool
finalIsSort ctx v0 = go (ctxLen ctx) (8 :: Int) v0
  where
    go _ 0 _ = pure False
    go lvl fuel v = do
      vf <- forceM v
      case vf of
        VSort _ -> pure True
        VPi _ _ _ _ clo -> clApp clo (VRigid lvl []) >>= go (lvl + 1) (fuel - 1)
        _ -> pure False

-- | Apply a rewrite to every diagnostic reported since a marker.
-- @nBefore@ is the @length csDiags@ captured before the elaboration
-- step whose newly-added diagnostics are to be re-tagged; @retag@ is
-- the per-diagnostic rewrite (applied only to the new prefix, leaving
-- the older diagnostics untouched). Shared skeleton for the
-- count-and-rollback re-tag idiom (§3.1.4).
retagNew :: Int -> (Diagnostic -> Diagnostic) -> CheckM ()
retagNew nBefore retag = modify' $ \st ->
  let ds = csDiags st
      (new, old) = splitAt (length ds - nBefore) ds
   in st {csDiags = map retag new ++ old}

-- | Re-tag type mismatches reported since the marker as
-- application-argument errors (a literal in a Type parameter slot).
retagNewMismatches :: Int -> CheckM ()
retagNewMismatches nBefore = retagNew nBefore $ \d ->
  if dCode d == "E_TYPE_EQUALITY_MISMATCH"
    then d {dCode = "E_APPLICATION_ARGUMENT_MISMATCH", dFamily = Just "kappa.application.argument-mismatch"}
    else d

-- | §3.1.4/§16.1.7.2: re-tag any error diagnostics reported since the
-- marker with the portable @E_EXPLICIT_IMPLICIT_CLASSIFIER_MISMATCH@
-- code (family @kappa.application.explicit-implicit-classifier@). This
-- is the general rewrite for a failed elaboration of an explicit
-- implicit argument's @\@payload@ against the selected implicit
-- binder's demanded type or classifier: §16.1.7.2 step 6 says the
-- explicit implicit argument fails for that binder when the selected
-- elaboration mode fails, and §3.2 lists typing, classifier mismatch,
-- quantity mismatch, unresolved name, and ambiguous name as in-scope
-- payload-failure kinds — so the payload-internal code (whatever it
-- happens to be) is replaced rather than special-cased on its spelling.
retagExplicitImplicitFailure :: Int -> CheckM ()
retagExplicitImplicitFailure nBefore = retagNew nBefore $ \d ->
  if isError d
    then
      d
        { dCode = "E_EXPLICIT_IMPLICIT_CLASSIFIER_MISMATCH"
        , dFamily = Just "kappa.application.explicit-implicit-classifier"
        }
    else d

-- ── Projection applications (§16.1.5, §16.1.6) ───────────────────────

-- | Resolve an application head to a projection facet, if any.
projectionHead :: Ctx -> Expr -> CheckM (Maybe (GName, ProjInfo))
projectionHead ctx = \case
  EVar hn
    | Nothing <- lookupCtx (nameText hn) ctx -> do
        mg <- lookupGlobalName (nameText hn)
        st <- get
        pure $ do
          g <- mg
          pj <- Map.lookup g (csProjections st)
          pure (g, pj)
  _ -> pure Nothing

-- | Does a projection-head application supply every declared binder?
projFullApp :: ProjInfo -> [Arg] -> Bool
projFullApp pj args =
  all isExpl args && length args == length (pjIsPlace pj) && or (pjIsPlace pj)
  where
    isExpl = \case
      ArgExplicit _ -> True
      _ -> False

-- | Application of a named projection (§9.1.1): a full application in
-- declaration order supplies the place binders directly; otherwise the
-- ordinary term facet (descriptor) is applied (§16.1.5).
elabProjApp :: Ctx -> Span -> GName -> ProjInfo -> [Arg] -> CheckM (Term, Value)
elabProjApp ctx sp g pj args = do
  mt <- globalTerm g
  case mt of
    Nothing -> anyHole ctx
    Just (dTm, dTy)
      | projFullApp pj args -> do
          let split = zip (pjIsPlace pj) args
              ordArgs = [a | (False, a) <- split]
              placePairs =
                [ (nm, e)
                | ((True, ArgExplicit e), nm) <-
                    zip [p | p@(True, _) <- split] (pjPlaceNames pj)
                ]
          (dTm1, dTy1) <- elabSpine ctx sp dTm dTy ordArgs
          applyDescriptor ctx sp dTm1 dTy1 (RootsSeparate placePairs)
      | otherwise -> elabSpine ctx sp dTm dTy args

-- | §7.4 receiver-projection sugar with trailing arguments: a
-- selector-form projection whose declaration has exactly one
-- receiver-marked @place@ binder is eligible for method-call sugar —
-- the receiver fills the place slot and the call-site arguments fill
-- the remaining binders in declaration order. A record field of the
-- receiver with the same name keeps §7.3 precedence.
projRecvApp :: Ctx -> Expr -> [Arg] -> CheckM (Maybe (Term, Value))
projRecvApp ctx (EDot recv (DotName mn)) args
  | all (\case ArgExplicit _ -> True; _ -> False) args
  , Nothing <- lookupCtx (nameText mn) ctx = do
      mg <- lookupGlobalName (nameText mn)
      st <- get
      case mg >>= \g -> (,) g <$> Map.lookup g (csProjections st) of
        Just (g, pj)
          | length (filter id (pjIsPlace pj)) == 1
          , length (pjIsPlace pj) == length args + 1
          , length (pjIsPlace pj) > 1 -> do
              shadowed <- fieldShadows
              if shadowed
                then pure Nothing
                else do
                  let fullArgs = weave (pjIsPlace pj) args
                  Just <$> elabProjApp ctx (exprSpan recv) g pj fullArgs
        _ -> pure Nothing
  where
    weave [] _ = []
    weave (True : rest) as = ArgExplicit recv : weave rest as
    weave (False : rest) (a : as) = a : weave rest as
    weave (False : rest) [] = weave rest [] -- unreachable by the length guard
    fieldShadows = do
      st0 <- get
      (_, rty) <- infer ctx recv
      rtyF <- forceM rty
      inner <- case rtyF of
        VSigT _ i -> forceM i
        t -> pure t
      put st0
      pure $ case inner of
        VRecordT fs -> nameText mn `elem` map fst fs
        _ -> False
projRecvApp _ _ _ = pure Nothing

-- | How the place arguments of a descriptor application are supplied.
data RootsSupply
  = RootsSeparate ![(Text, Expr)] -- ^ full application: place binder ↦ argument
  | RootsSingle !Expr -- ^ §16.1.5 single roots argument

-- | The accessor capabilities of a structural bundle record type
-- (§16.1.6): @Just [(field, roots, focus)]@ when every field is an
-- accessor descriptor.
bundleCapsM :: [(Text, Value)] -> CheckM (Maybe [(Text, Value, Value)])
bundleCapsM fs
  | null fs = pure Nothing
  | otherwise = do
      caps <- forM fs $ \(nm, tv) -> do
        t <- forceM tv
        pure $ case t of
          VGlobN (GName pm former) [(_, roots), (_, focus)]
            | pm == preludeModule
            , lookup nm capFormers == Just former ->
                Just (nm, roots, focus)
          _ -> Nothing
      pure (sequence caps)
  where
    capFormers = [("get", "Getter"), ("open", "Opener"), ("set", "Setter"), ("sink", "Sinker")]

-- | If the callee elaborates to a projector or accessor-bundle
-- descriptor, elaborate the §16.1.5/§16.1.6 descriptor application.
descriptorApp :: Ctx -> Span -> Term -> Value -> Expr -> Maybe PlaceDemand -> CheckM (Maybe (Term, Value))
descriptorApp ctx sp fTm fTy e mdemand = case fTy of
  VGlobN (GName pm "Projector") [_, _]
    | pm == preludeModule -> Just <$> run
  VRecordT caps -> do
    mb <- bundleCapsM caps
    case mb of
      Just _ -> Just <$> run
      Nothing -> pure Nothing
  _ -> pure Nothing
  where
    run = maybe id withDemand mdemand (applyDescriptor ctx sp fTm fTy (RootsSingle e))

-- | Apply a descriptor value to its roots (§16.1.5/§16.1.6): validate
-- the place pack, select the eliminator for the surrounding demand, and
-- yield the focus.
applyDescriptor :: Ctx -> Span -> Term -> Value -> RootsSupply -> CheckM (Term, Value)
applyDescriptor ctx sp dTm dTy0 supply = do
  dTy <- forceM dTy0
  case dTy of
    VGlobN (GName pm "Projector") [(_, rootsV), (_, focusV)]
      | pm == preludeModule -> do
          placeTms <- elabRootsSupply ctx sp rootsV supply
          focusV' <- case placeTms of
            [single] -> substThisInto ctx single focusV
            _ -> pure focusV
          pure (foldl (CApp Expl) dTm placeTms, focusV')
    VRecordT capFs -> do
      mcaps <- bundleCapsM capFs
      case mcaps of
        Just caps@((_, rootsV, focusV) : _) -> do
          demand <- gets csDemand
          let want = case demand of
                DemandRead -> "get"
                DemandConsume -> "sink"
                DemandOpen -> "open"
              capNames = [nm | (nm, _, _) <- caps]
          placeTms <- elabRootsSupply ctx sp rootsV supply
          unless (want `elem` capNames) $
            errAt sp "E_PROJECTION_CAPABILITY_REQUIRED" (Just "kappa-hs.projection.capability")
              ( "this use requires the '" <> capabilityWord demand
                  <> "' capability, but the accessor bundle provides only: "
                  <> T.intercalate ", " capNames <> " (§16.1.6)"
              )
          -- the value facet of the application always reads through
          -- 'get' when available (under '~' the §18.9 threading reads
          -- the focus and fills through 'set'/'open' at usage level)
          let readCap
                | demand == DemandConsume && "sink" `elem` capNames = "sink"
                | "get" `elem` capNames = "get"
                | otherwise = ""
          tm <-
            if T.null readCap
              then fst <$> anyHole ctx
              else pure (foldl (CApp Expl) (CProj dTm readCap) placeTms)
          focusV' <- case placeTms of
            [single] -> substThisInto ctx single focusV
            _ -> pure focusV
          pure (tm, focusV')
        _ -> do
          errAt sp "E_PROJECTION_DESCRIPTOR_VALUE_EXPECTED" (Just "kappa-hs.projection.descriptor")
            "expected a projector or accessor-bundle descriptor value here (§16.1.5)"
          anyHole ctx
    _ -> do
      errAt sp "E_PROJECTION_DESCRIPTOR_VALUE_EXPECTED" (Just "kappa-hs.projection.descriptor")
        "expected a projector or accessor-bundle descriptor value here (§16.1.5)"
      anyHole ctx
  where
    capabilityWord = \case
      DemandRead -> "get"
      DemandConsume -> "sink"
      DemandOpen -> "open"

-- | Elaborate the roots of a descriptor application in place-pack mode
-- (§16.1.5): each supplied field must be a stable place expression of
-- the corresponding field type. Returns the place terms in canonical
-- (lexicographic) root order.
elabRootsSupply :: Ctx -> Span -> Value -> RootsSupply -> CheckM [Term]
elabRootsSupply ctx _sp rootsV supply = do
  rootsF <- forceM rootsV
  let rfs = case rootsF of
        VRecordT fs -> fs
        _ -> []
  case supply of
    RootsSeparate pairs ->
      forM rfs $ \(nm, fty) ->
        case lookup nm pairs of
          Just e -> elabPlaceArg ctx e fty
          Nothing -> fst <$> anyHole ctx
    RootsSingle e -> case rfs of
      [(nm, fty)] -> case e of
        ERecordLit items isp -> do
          let fields = [(nameText fn, fe) | RecItem _ fn (Just fe) <- items]
          case fields of
            [(fn, fe)]
              | fn == nm, length items == 1 -> (: []) <$> elabPlaceArg ctx fe fty
            _ -> do
              errAt isp "E_PROJECTION_ROOTS_PACK_MISMATCH" (Just "kappa-hs.projection.roots")
                ("the roots record literal must supply exactly the field '" <> nm <> "' (§16.1.5)")
              (: []) . fst <$> anyHole ctx
        _ -> (: []) <$> elabPlaceArg ctx e fty
      _ -> case e of
        ERecordLit items isp -> do
          let fields = [(nameText fn, fe) | RecItem _ fn (Just fe) <- items]
          if sort (map fst fields) /= map fst rfs || length items /= length fields
            then do
              errAt isp "E_PROJECTION_ROOTS_PACK_MISMATCH" (Just "kappa-hs.projection.roots")
                ( "the roots record literal must supply exactly the fields: "
                    <> T.intercalate ", " (map fst rfs) <> " (§16.1.5)"
                )
              mapM (const (fst <$> anyHole ctx)) rfs
            else forM rfs $ \(nm, fty) ->
              case lookup nm fields of
                Just fe -> elabPlaceArg ctx fe fty
                Nothing -> fst <$> anyHole ctx
        _ -> do
          errAt (exprSpan e) "E_PROJECTION_DESCRIPTOR_ROOTS_LITERAL_REQUIRED" (Just "kappa-hs.projection.roots")
            "the roots argument of a multi-root projector descriptor application must be a closed record literal (§16.1.5)"
          _ <- infer ctx e
          mapM (const (fst <$> anyHole ctx)) rfs

-- | One root of a place pack: must be a stable place expression
-- (§12.4.1) of the root field's type.
elabPlaceArg :: Ctx -> Expr -> Value -> CheckM Term
elabPlaceArg ctx e fty
  | stablePlaceExpr e = withDemand DemandRead (check ctx e fty)
  | otherwise = do
      errAt (exprSpan e) "E_PROJECTION_ROOT_INVALID" (Just "kappa-hs.projection.roots")
        "a projection place argument must be a stable place expression (§12.4.1, §16.1.5)"
      _ <- withDemand DemandRead (infer ctx e)
      fst <$> anyHole ctx

-- | Syntactic stable-place check (§12.4.1 subset: variables and
-- record\/constructor field paths).
stablePlaceExpr :: Expr -> Bool
stablePlaceExpr = \case
  EVar _ -> True
  EDot e (DotName _) -> stablePlaceExpr e
  EAscription e _ _ -> stablePlaceExpr e
  _ -> False

elabSpine :: Ctx -> Span -> Term -> Value -> [Arg] -> CheckM (Term, Value)
elabSpine _ _ fTm fTy [] = pure (fTm, fTy)
elabSpine ctx sp fTm fTy0 (arg : rest) = do
  -- §12.3.1: a capture-annotated callable applies at its underlying type
  fTy <- peelCapturesM fTy0
  case arg of
    -- §18.9.3/§18.9.6: '~' is valid only inside a do block; recover
    -- with a hole so the broken spine does not cascade a type mismatch
    ArgInout _ msp | not (ctxInDo ctx) -> do
      errAt msp "E_QTT_INOUT_MARKER_UNEXPECTED" (Just "kappa-hs.qtt.inout-marker")
        "a call-site '~' marker is valid only inside a do block (§18.9.3, §18.9.6)"
      anyHole ctx
    _ -> do
      -- §16.1.5/§16.1.6: a descriptor-typed callee consumes its roots
      -- argument in place-pack mode
      mdesc <- case arg of
        ArgExplicit e -> descriptorApp ctx sp fTm fTy e Nothing
        ArgInout e _ -> descriptorApp ctx sp fTm fTy e (Just DemandOpen)
        _ -> pure Nothing
      case mdesc of
        Just (tm', ty') -> elabSpine ctx sp tm' ty' rest
        Nothing -> elabSpineArg ctx sp fTm fTy arg rest

elabSpineArg :: Ctx -> Span -> Term -> Value -> Arg -> [Arg] -> CheckM (Term, Value)
elabSpineArg ctx sp fTm fTy arg rest = do
  case (arg, fTy) of
    (ArgImplicit e, VPi Impl _ _ dom clo) -> do
      -- §16.1.7.2: the explicit implicit argument's payload is elaborated
      -- against the selected implicit binder's demanded type 'dom'. If
      -- that elaboration fails, §3.1.4 mandates the portable
      -- E_EXPLICIT_IMPLICIT_CLASSIFIER_MISMATCH code in place of whatever
      -- payload-internal diagnostic 'check' raised (a general rewrite,
      -- not a per-kind special case).
      n0 <- gets (length . csDiags)
      aTm <- check ctx e dom
      retagExplicitImplicitFailure n0
      aV <- evalIn ctx aTm
      ty' <- clApp clo aV
      elabSpine ctx sp (CApp Impl fTm aTm) ty' rest
    -- a type former's implicit parameters may be saturated positionally
    -- in type application ('Foo Nat (=)' for 'Foo (@0 a) (@0 p)', §7.2):
    -- an explicit argument whose type fits the implicit domain fills it
    (ArgExplicit e, VPi Impl q _ dom clo) -> do
      former <- finalIsSort ctx fTy
      filled <-
        if not former
          then pure Nothing
          else do
            -- speculative: commit only if the whole remaining spine
            -- elaborates cleanly with the argument in the implicit slot
            st0 <- get
            n0 <- gets (length . csDiags)
            (aTm0, aTy0) <- infer ctx e
            (aTm, aTy) <- insertAllImplicits ctx (exprSpan e) aTm0 aTy0
            ok <- unify ctx aTy dom
            n1 <- gets (length . csDiags)
            if not (ok && n0 == n1)
              then put st0 >> pure Nothing
              else do
                aV <- evalIn ctx aTm
                ty' <- clApp clo aV
                r <- elabSpine ctx sp (CApp Impl fTm aTm) ty' rest
                n2 <- gets (length . csDiags)
                if n2 == n0
                  then pure (Just r)
                  else put st0 >> pure Nothing
      case filled of
        Just r -> pure r
        Nothing -> do
          iTm <- resolveImplicitQ ctx sp q dom
          iV <- evalIn ctx iTm
          ty' <- clApp clo iV
          elabSpine ctx sp (CApp Impl fTm iTm) ty' (arg : rest)
    (_, VPi Impl q _ dom clo) -> do
      iTm <- resolveImplicitQ ctx sp q dom
      iV <- evalIn ctx iTm
      ty' <- clApp clo iV
      elabSpine ctx sp (CApp Impl fTm iTm) ty' (arg : rest)
    (ArgExplicit e, VPi Expl q _ dom clo) -> do
      aTm <- checkExplicitArg ctx q e dom
      aV <- evalIn ctx aTm
      ty' <- clApp clo aV
      elabSpine ctx sp (CApp Expl fTm aTm) ty' rest
    -- a '~place' marker against a callable parameter: the place value
    -- is demanded in open mode (§18.9.3, §16.1.6)
    (ArgInout e _, VPi Expl _ _ dom clo) -> do
      aTm <- withDemand DemandOpen (check ctx e dom)
      aV <- evalIn ctx aTm
      ty' <- clApp clo aV
      elabSpine ctx sp (CApp Expl fTm aTm) ty' rest
    (ArgExplicit e, VFlex m []) -> do
      dom <- freshMetaV ctx
      codM <- freshMeta
      domT <- quoteIn ctx dom
      piV <- evalIn ctx (CPi Expl QW "_a" domT codM)
      solveMeta m piV
      elabSpine ctx sp fTm piV (ArgExplicit e : rest)
    (ArgNamedBlock items bsp, _) -> elabNamedBlock ctx fTm fTy items bsp rest
    -- a '~place' call-site marker elaborates as the place expression;
    -- marker/parameter agreement is judged by the §18.9.3 usage analysis
    (ArgInout e _, _) -> elabSpine ctx sp fTm fTy (ArgExplicit e : rest)
    (ArgImplicit e, _) -> do
      errAt (exprSpan e) "E_APPLICATION_ARGUMENT_MISMATCH" (Just "kappa.application.argument-mismatch")
        "an explicit implicit argument was supplied, but the callee has no implicit parameter here (§16.1.7.1)"
      -- recovery: do not cascade a type mismatch from the broken spine
      anyHole ctx
    (ArgExplicit e, _)
      -- a saturated constructor given extra arguments (§10.1.1)
      | Just _ <- termHeadCtor fTm -> do
          errAt (exprSpan e) "E_CONSTRUCTOR_ARITY_MISMATCH" (Just "kappa.constructor.arity")
            "too many arguments in constructor application"
          anyHole ctx
      -- a data-type head applied in term position selects its
      -- same-named constructor (§2.8.3 static-object term facet)
      | CGlob dg <- fTm -> do
          st <- get
          case Map.lookup dg (csDatas st) of
            Just di
              | (ctorG : _) <- [c | c <- diCtors di, gnameText c == gnameText dg] -> do
                  mt <- globalTerm ctorG
                  case mt of
                    Just (cTm, cTy) -> elabSpine ctx sp cTm cTy (ArgExplicit e : rest)
                    Nothing -> noncallable e
            _ -> noncallable e
      | otherwise -> noncallable e
      where
        noncallable e' = do
          fT <- quoteIn ctx fTy
          fTz <- zonkTermM (ctxLen ctx) fT
          let calleeR = renderTerm fTz
          -- §3.1.1A: an application diagnostic MUST include the call site
          -- and the callee type site. The call site is the application
          -- span 'sp'; the callee type is exposed both as a related
          -- origin (call-site) and in the §3.2 payload.
          report $
            withPayload
              ( withPayloadField "calleeType" calleeR $
                  payloadKind "application-non-callable"
              )
              $ withRelated (related RoleCallSite sp ("callee type: " <> calleeR))
              $ withNote ("callee type: " <> calleeR)
              $ diag SevError StageElaborate "E_APPLICATION_NONCALLABLE" (Just "kappa-hs.application.non-callable")
                  (exprSpan e')
                  "this expression is not callable"
          anyHole ctx
  where
    termHeadCtor = \case
      CApp _ f _ -> termHeadCtor f
      CLam _ _ _ b -> termHeadCtor b
      CCtor g _ -> Just g
      _ -> Nothing

-- named constructor application (§10.1.1): supplied fields + defaults in
-- constructor order.
elabNamedBlock :: Ctx -> Term -> Value -> [(Name, Maybe Expr)] -> Span -> [Arg] -> CheckM (Term, Value)
elabNamedBlock ctx fTm fTy items sp rest = do
  st <- get
  mCtorG <- case ctorOf fTm of
    Just g -> pure (Just g)
    Nothing -> case fTm of
      -- a local rebinding of a constructor (§16.1.7.2): the binding's
      -- definiens reveals the constructor
      CVar i -> case drop i (ctxEnv ctx) of
        (v : _) -> do
          v' <- forceM v
          pure (valueCtorOf v')
        [] -> pure Nothing
      _ -> pure Nothing
  forM_ (duplicatesOf [nameText n | (n, _) <- items]) $ \dn ->
    case mCtorG of
      -- §3.2: a malformed *constructor* application uses the
      -- standardized family 'kappa.constructor.arity'; §3.1.4 then
      -- mandates the recoverable portable alias E_CONSTRUCTOR_ARITY_MISMATCH
      -- (wired via 'requiredAliasTable'). The implementation-specific
      -- code carries the precise duplicate/missing/unknown distinction.
      Just g | Map.member g (csCtors st) ->
        errAt sp "E_NAMED_ARG_DUPLICATE" (Just "kappa.constructor.arity")
          ("named argument '" <> dn <> "' is supplied more than once")
      -- §16.1.7.2: on an ordinary callee a malformed block is a
      -- telescope mismatch
      _ -> blockMismatch
  case mCtorG of
    Just g | Just ci <- Map.lookup g (csCtors st) -> do
      let fieldNames = mapMaybe fst (ciFields ci)
      forM_ items $ \(n, _) ->
        unless (nameText n `elem` fieldNames) $
          errAt (nameSpan n) "E_NAMED_ARG_UNKNOWN" (Just "kappa.constructor.arity")
            ("constructor has no named parameter '" <> nameText n <> "'")
      let supplied = [(nameText n, fromMaybe (EVar n) me) | (n, me) <- items]
      args <- forM (ciFields ci) $ \(mname, mdef) ->
        case mname >>= \fn -> lookup fn supplied of
          Just e -> pure (Just (mname, False, Left e))
          Nothing -> case mdef of
            -- field default (§10.1.1): elaborated here, at the
            -- application site, against the field's type, with the
            -- earlier field arguments in scope
            Just d -> pure (Just (mname, True, Left d))
            Nothing -> do
              errAt sp "E_NAMED_ARG_MISSING" (Just "kappa.constructor.arity")
                ("missing constructor argument" <> maybe "" (\n -> " '" <> n <> "'") mname)
              pure Nothing
      -- run the spine with mixed surface/core arguments
      goSpine ctx fTm fTy (catMaybes args)
    -- ordinary function: match named items against the remaining
    -- explicit Pi binder names (§16.1.7.2); a label supplied twice is
    -- a malformed block
    _ -> do
      forM_ (duplicatesOf [nameText n | (n, _) <- items]) $ \_ -> blockMismatch
      goPiNamed fTm fTy [(nameText n, fromMaybe (EVar n) me) | (n, me) <- items]
  where
    -- §16.1.7.2: one diagnostic per malformed block on an ordinary
    -- callee (a telescope mismatch, not a named-argument code)
    blockMismatch =
      errOncePerSpan sp "E_TYPE_EQUALITY_MISMATCH" (Just "kappa.type.mismatch")
        "the named-argument block does not match the callee's remaining parameter telescope (§16.1.7.2)"
    ctorOf = \case
      CLam _ _ _ b -> ctorOf b
      CCtor g _ -> Just g
      CGlob g -> Just g
      _ -> Nothing
    valueCtorOf = \case
      VCtor g _ -> Just g
      VLam _ _ _ (Closure _ body) -> ctorOf body
      VGlobN g _ -> Just g
      _ -> Nothing
    goPiNamed tm ty0 remaining = do
      ty <- forceM ty0
      case ty of
        VPi Impl q _ dom clo -> do
          iTm <- resolveImplicitQ ctx sp q dom
          iV <- evalIn ctx iTm
          ty' <- clApp clo iV
          goPiNamed (CApp Impl tm iTm) ty' remaining
        VPi Expl _ nm dom clo
          | Just e <- lookup nm remaining -> do
              aTm <- check ctx e dom
              aV <- evalIn ctx aTm
              ty' <- clApp clo aV
              goPiNamed (CApp Expl tm aTm) ty' [(n, x) | (n, x) <- remaining, n /= nm]
          | not (null remaining) -> do
              blockMismatch
              anyHole ctx
        _
          | null remaining, null rest -> pure (tm, ty)
          | null remaining -> do
              -- §16.1.7.2: the named-argument block is the final
              -- argument of its application site
              blockMismatch
              anyHole ctx
          | otherwise -> do
              blockMismatch
              anyHole ctx
    goSpine _ tm ty [] = elabSpine ctx sp tm ty rest
    goSpine ctxAcc tm ty0 (a@(_, _, _) : as) = do
      ty <- forceM ty0
      case ty of
        VPi Impl q _ dom clo -> do
          iTm <- resolveImplicitQ ctx sp q dom
          iV <- evalIn ctx iTm
          ty' <- clApp clo iV
          goSpine ctxAcc (CApp Impl tm iTm) ty' (a : as)
        VPi Expl _ _ dom clo -> do
          let (mname, isDefault, payload) = a
              argCtx = if isDefault then ctxAcc else ctx
          (aTm, aV) <- case payload of
            Left e -> do
              aTm0 <- check argCtx e dom
              aV <- evalIn argCtx aTm0
              if isDefault
                then do
                  -- a default's term lives under the accumulated field
                  -- bindings; re-quote its value at the outer depth
                  aTm1 <- quoteIn ctx aV
                  pure (aTm1, aV)
                else pure (aTm0, aV)
            Right coreTm -> (,) coreTm <$> evalIn argCtx coreTm
          ty' <- clApp clo aV
          let ctxAcc' = case mname of
                Just fn -> bindCtxLet fn False dom aV ctxAcc
                Nothing -> ctxAcc
          goSpine ctxAcc' (CApp Expl tm aTm) ty' as
        _ -> do
          errAt sp "E_CONSTRUCTOR_ARITY_MISMATCH" (Just "kappa.constructor.arity")
            "too many constructor arguments"
          pure (tm, ty)

-- ── Literals (§6.1.5, §6.1.6) ────────────────────────────────────────

elabIntLit :: Ctx -> Integer -> Maybe Name -> Span -> Maybe Value -> CheckM (Term, Value)
elabIntLit ctx v msuf sp mexp = case msuf of
  Just suf -> do
    known <- prefixResolves ctx (nameText suf)
    if not known
      then badLiteralSuffix ctx suf
      else do
        (fTm, fTy) <- resolveName ctx suf
        admits <- suffixDomAdmits ctx "FromInteger" ["Int", "Nat", "Integer"] fTy
        if admits
          then elabSpine ctx sp fTm fTy [ArgExplicit (EIntLit v Nothing sp)] -- payload : Nat
          else do
            -- §6.1.6: the literal payload is the suffix application's
            -- argument; a parameter type admitting no integer literal
            -- is an application-argument mismatch
            errAt sp "E_APPLICATION_ARGUMENT_MISMATCH" (Just "kappa.application.argument-mismatch")
              ("the suffix function's parameter type admits no integer literal payload (§6.1.6)")
            anyHole ctx
  Nothing -> do
    expected <- maybe (pure Nothing) (fmap Just . forceM) mexp
    case expected of
      Just t
        | isNumHead t -> pure (CLit (LitInt v), t)
        | Just other <- nonDefault t -> do
            -- FromInteger elaboration (§6.1.5)
            dict <- resolveLiteralWitness ctx sp "FromInteger" "integer" other
            pure (CApp Expl (CProj dict "fromInteger") (CLit (LitInt v)), other)
      _ -> pure (CLit (LitInt v), VGlobN (gPrel "Int") []) -- defaulting (§6.1.5)
  where
    isNumHead = \case
      VGlobN (GName _ n) [] -> n `elem` ["Int", "Nat", "Integer"]
      _ -> False
    nonDefault = \case
      VFlex {} -> Nothing
      t@(VGlobN (GName _ n) [])
        | n `elem` ["Float", "Double"] -> Just t
      t@VGlobN {} -> Just t
      _ -> Nothing

elabFloatLit :: Ctx -> Double -> Maybe Name -> Span -> Maybe Value -> CheckM (Term, Value)
elabFloatLit ctx v msuf sp mexp = case msuf of
  Just suf -> do
    known <- prefixResolves ctx (nameText suf)
    if not known
      then badLiteralSuffix ctx suf
      else do
        (fTm, fTy) <- resolveName ctx suf
        admits <- suffixDomAdmits ctx "FromFloat" ["Float", "Double"] fTy
        if admits
          then elabSpine ctx sp fTm fTy [ArgExplicit (EFloatLit v Nothing sp)]
          else do
            errAt sp "E_APPLICATION_ARGUMENT_MISMATCH" (Just "kappa.application.argument-mismatch")
              ("the suffix function's parameter type admits no float literal payload (§6.1.6)")
            anyHole ctx
  Nothing -> do
    expected <- maybe (pure Nothing) (fmap Just . forceM) mexp
    case expected of
      Just t
        | isFloatHead t -> pure (CLit (LitDouble v), t)
        | Just other <- nonDefault t -> do
            -- FromFloat elaboration (§6.1.5)
            dict <- resolveLiteralWitness ctx sp "FromFloat" "float" other
            pure (CApp Expl (CProj dict "fromFloat") (CLit (LitDouble v)), other)
      _ -> pure (CLit (LitDouble v), VGlobN (gPrel "Double") []) -- defaulting (§6.1.5)
  where
    isFloatHead = \case
      VGlobN (GName _ n) [] -> n `elem` ["Float", "Double"]
      _ -> False
    nonDefault = \case
      VFlex {} -> Nothing
      t@VGlobN {} -> Just t
      _ -> Nothing

-- | Resolve a numeric-literal witness (@FromInteger T@ / @FromFloat T@)
-- at a concrete expected type @T@ (§6.1.5). When @T@ admits no such
-- witness, the failure is a literal-domain mismatch, not a generic
-- unsolved implicit: §3.1.4 (Spec.md:928-929) mandates the portable
-- alias @E_NUMERIC_LITERAL_DOMAIN_MISMATCH@ — "emitted when literal
-- elaboration fails because the surrounding expected type or selected
-- literal witness is not compatible with the literal domain" — backed by
-- the §3.2.3 @kappa.type.literal-domain-mismatch@ family ("integer,
-- floating, … literal elaboration fails because the surrounding context
-- expects an incompatible domain or because no suitable literal witness
-- is available"). The primary message foregrounds the user-visible
-- mismatch and notes the missing witness, per §3.2.3's rendering rule.
--
-- The goal carrier @T@ here is always concrete (the caller's
-- @nonDefault@ guard rejects flex/defaultable types), so the witness
-- goal is never postponed; we run the ordinary §16.3.3 resolution ladder
-- (local implicits, then instance search, then supertrait projection)
-- and only divert the *failure* diagnostic.
resolveLiteralWitness :: Ctx -> Span -> Text -> Text -> Value -> CheckM Term
resolveLiteralWitness ctx sp traitName litKind other = do
  let goal = VGlobN (gPrel traitName) [(Expl, other)]
  mLoc <- localCandidate ctx sp Q0 goal
  mTm <- case mLoc of
    Just tm -> pure (Just tm)
    Nothing -> do
      mInst <- instanceSearch ctx sp goal
      case mInst of
        Just tm -> pure (Just tm)
        Nothing -> superCandidate ctx goal
  case mTm of
    Just tm -> pure tm
    Nothing -> do
      tT <- quoteIn ctx other
      let article = if litKind == "integer" then "an " else "a "
      errAt sp "E_NUMERIC_LITERAL_DOMAIN_MISMATCH" (Just "kappa.type.literal-domain-mismatch")
        ( "expected " <> renderTerm tT <> " but found " <> article <> litKind
            <> " literal; " <> renderTerm tT <> " has no " <> traitName
            <> " witness, so it admits no " <> litKind <> " literal domain (§6.1.5)"
        )
      freshMeta

-- | Does the suffix function's first explicit parameter admit the
-- literal payload (§6.1.6)? Either a literal-typed parameter or one
-- with the corresponding literal-trait instance.
suffixDomAdmits :: Ctx -> Text -> [Text] -> Value -> CheckM Bool
suffixDomAdmits ctx traitName litHeads = goPeel (ctxLen ctx)
  where
    goPeel lvl ty = do
      t <- forceM ty
      case t of
        VPi Impl _ _ _ clo -> clApp clo (VRigid lvl []) >>= goPeel (lvl + 1)
        VPi Expl _ _ dom _ -> do
          d <- forceM dom
          case d of
            VGlobN (GName _ n) []
              | n `elem` litHeads -> pure True
            VGlobN {} ->
              isJust <$> instanceSearch ctx (Span "" (Pos 0 0) (Pos 0 0)) (VGlobN (gPrel traitName) [(Expl, d)])
            _ -> pure True
        _ -> pure True

elabString :: Ctx -> StringLit -> [InterpPart] -> Span -> CheckM (Term, Value)
elabString ctx sl parts sp = case (slPrefix sl, parts) of
  (Nothing, _) ->
    -- interpolation applies only to prefixed strings (§6.3.4)
    case slFragments sl of
      [FragLit t] -> pure (CLit (LitStr t), VGlobN (gPrel "String") [])
      [] -> pure (CLit (LitStr ""), VGlobN (gPrel "String") [])
      _ -> do
        errAt sp "E_INTERNAL" Nothing "plain string with interpolation fragments"
        anyHole ctx
  (Just "f", _) -> do
    -- conventional f-string: concatenate shows of interpolations
    let strTy = VGlobN (gPrel "String") []
    pieces <- forM (zip [0 ..] (slFragments sl)) $ \(i, frag) -> case frag of
      FragLit t -> pure (CLit (LitStr t))
      FragInterp _ _ -> interpPiece i
      FragInterpFmt _ _ _ -> interpPiece i
    let appendG a b = CApp Expl (CApp Expl (CGlob (gPrel "stringAppend")) a) b
    pure (foldr appendG (CLit (LitStr "")) pieces, strTy)
    where
      interpPiece i = case [ipExpr p | p <- parts, ipIndex p == i] of
        [e] -> do
          (tm, ty) <- infer ctx e
          (tm1, ty1) <- insertAllImplicits ctx sp tm ty
          showDict <- resolveImplicit ctx sp (VGlobN (gPrel "Show") [(Expl, ty1)])
          pure (CApp Expl (CProj showDict "show") tm1)
        _ -> pure (CLit (LitStr ""))
  (Just "type", _)
    -- §6.3.5: the conventional `type"…"` prefix handler. `type` is a soft
    -- keyword (§5.2) that cannot be an ordinary binding, so the
    -- implementation provides this built-in type-producing handler: the
    -- string content is parsed and elaborated as a type expression,
    -- yielding that Type. (Literal content; an interpolation fragment is
    -- reported, since splicing a runtime value into a static type is not a
    -- meaningful type-producing form here.)
    | all (\f -> case f of FragLit _ -> True; _ -> False) (slFragments sl) -> do
        let content = T.concat [t | FragLit t <- slFragments sl]
        case parseExprText "<type-prefix>" content of
          Left d -> do
            report d {dMessage = "type\"…\" content does not parse as a type (§6.3.5): " <> dMessage d}
            anyHole ctx
          Right tyE -> do
            (tyTm, lvl) <- inferType ctx tyE
            pure (tyTm, VSort lvl)
    | otherwise -> do
        errAt sp "E_PREFIX_HANDLER_TYPE" (Just "kappa.macro.failure")
          "the conventional type\"…\" handler (§6.3.5) takes literal type-expression content; it does not support ${…} interpolation (a runtime value cannot be spliced into a static type)"
        anyHole ctx
  (Just p, _) -> do
    -- §6.3.4.3: the prefix is resolved by ordinary term name
    -- resolution and must elaborate to an 'Elab (InterpolatedMacro t)'
    -- handler; the §6.3.4.5 fragment pipeline runs at elaboration time
    resolvable <- prefixResolves ctx p
    if resolvable
      then elabPrefixHandler ctx sl parts sp p
      else do
        errAt sp "E_NAME_UNRESOLVED" (Just "kappa.name.unresolved")
          ("unresolved name '" <> p <> "' used as a string-literal prefix (Spec §6.3.4)")
        pure (CLit (LitStr ""), VGlobN (gPrel "String") [])

-- | §6.3.4.3–5: run a prefixed string through its 'InterpolatedMacro'
-- handler at elaboration time and splice the produced syntax.
elabPrefixHandler :: Ctx -> StringLit -> [InterpPart] -> Span -> Text -> CheckM (Term, Value)
elabPrefixHandler ctx sl parts sp p = do
  let bail = anyHole ctx
  (hTm, hTy) <- infer ctx (EVar (Name p sp))
  (hTm1, hTy1) <- insertAllImplicits ctx sp hTm hTy
  hTyF <- forceM hTy1
  case hTyF of
    VGlobN (GName pm "Elab") [(_, inner)]
      | pm == preludeModule -> do
          innerF <- forceM inner
          case innerF of
            VGlobN (GName pm2 "InterpolatedMacro") [(_, tV)]
              | pm2 == preludeModule -> do
                  frags <- fragmentValues
                  hV <- evalRT ctx hTm1
                  rDict <- runElab ctx sp hV
                  case rDict of
                    Left () -> bail
                    Right dictV -> do
                      ec <- ecRT_
                      let methodV = vproj ec dictV "buildInterpolated"
                      action <- vappRT methodV [listValue frags]
                      res <- runElab ctx sp action
                      case res of
                        Left () -> bail
                        Right sv -> do
                          mtm <- spliceSyntaxValue ctx sp tV sv
                          case mtm of
                            Nothing -> bail
                            Just tm -> pure (tm, tV)
            _ -> badHandler hTyF >> bail
    VGlobN (GName pm "InterpolatedMacro") _
      | pm == preludeModule -> do
          errAt sp "E_PREFIX_RUNTIME_HANDLER" (Just "kappa.macro.failure")
            "a runtime 'InterpolatedMacro' value is not a valid prefixed-string handler; handler evidence must be meta-phase, an 'Elab (InterpolatedMacro _)' term (§6.3.4.3)"
          bail
    _ -> badHandler hTyF >> bail
  where
    badHandler ty = do
      tT <- quoteIn ctx ty
      errAt sp "E_PREFIX_HANDLER_TYPE" (Just "kappa.macro.failure")
        ("the prefixed-string handler '" <> p
           <> "' must elaborate to 'Elab (InterpolatedMacro _)'; this term has type "
           <> renderTerm tT <> " (§6.3.4.3)")
    -- §6.3.4.4 fragment construction (literal merging and escape
    -- decoding already performed by the lexer)
    fragmentValues =
      forM (zip [0 ..] (slFragments sl)) $ \(i, frag) -> case frag of
        FragLit t -> pure (VCtor (gPrel "Lit") [VLit (LitStr t)])
        FragInterp _ isp -> interpValue i isp Nothing
        FragInterpFmt _ isp fmt -> interpValue i isp (Just fmt)
    interpValue i isp mfmt = do
      payload <- case [ipExpr q | q <- parts, ipIndex q == i] of
        [e] -> do
          -- elaborate for diagnostics and the fragment's type index;
          -- the handler receives the quoted surface syntax (§6.3.4.4)
          (tm0, ty0) <- infer ctx e
          _ <- insertAllImplicits ctx isp tm0 ty0
          pure e
        _ -> pure (EUnit isp)
      qs <- mkQuotedSyntax ctx payload isp
      let quoteV = VQuote qs []
      pure $ case mfmt of
        Nothing -> VCtor (gPrel "Interp") [quoteV]
        Just fmt -> VCtor (gPrel "InterpFmt") [quoteV, VLit (LitStr fmt)]

-- ── Records, projections, patches ────────────────────────────────────

elabRecordLit :: Ctx -> [RecItem] -> Span -> CheckM (Term, Value)
elabRecordLit ctx items sp = do
  rs <- forM items $ \(RecItem _ n mv) -> do
    let e = fromMaybe (EVar n) mv -- punning
    (tm, ty) <- infer ctx e
    (tm1, ty1) <- insertAllImplicits ctx (nameSpan n) tm ty
    pure (nameText n, tm1, ty1)
  forM_ (duplicatesOf [n | (n, _, _) <- rs]) $ \n ->
    errAt sp "E_RECORD_DUPLICATE_FIELD" (Just "kappa-hs.record.duplicate-field")
      ("record literal has duplicate field '" <> n <> "'")
  -- evaluate fields in source order via lets, assemble canonically
  let sorted = sortOn (\(n, _, _) -> n) rs
  pure
    ( CRecordV [(n, tm) | (n, tm, _) <- sorted]
    , VRecordT [(n, ty) | (n, _, ty) <- sorted]
    )

-- | Names that occur more than once (each reported once).
duplicatesOf :: [Text] -> [Text]
duplicatesOf ns = nub [n | n <- ns, length (filter (== n) ns) > 1]

elabDot :: Ctx -> Expr -> DotMember -> CheckM (Term, Value)
elabDot ctx e member = do
  let mname = case member of
        DotName n -> n
        DotOperator n -> n
  -- effect-operation selection label.op (§18.1.15, §7.3) — scoped or top-level
  merged <- effMerged ctx
  case e of
    EVar ln
      | Just eli <- Map.lookup (nameText ln) merged
      , Just op <- find ((== nameText mname) . eoiName) (eliOps eli) ->
          effOpSelection eli op
    _ -> elabDotOrdinary ctx e member mname

elabDotOrdinary :: Ctx -> Expr -> DotMember -> Name -> CheckM (Term, Value)
elabDotOrdinary ctx e member mname = do
  -- reified module objects: (module a).b chains (§2.8.6)
  case modObjPathOf e of
    Just segs -> elabModuleMember ctx (segs ++ [nameText mname]) (nameSpan mname)
    Nothing -> do
      -- fully-qualified module path, e.g. std.prelude.Bool or main.T (§8.3)
      mPath <- case modulePathOf e of
        Just segs@(s0 : _) | Nothing <- lookupCtx s0 ctx -> do
          let mn = ModuleName segs
              g = GName mn (nameText mname)
          st <- get
          if (Map.member g (csGlobals st) || Map.member g (csCtors st))
            && memberVisible st mn (nameText mname)
            then globalTerm g
            else pure Nothing
        _ -> pure Nothing
      case mPath of
        Just r -> pure r
        Nothing -> elabDotUnqualified ctx e member mname
  where
    modulePathOf = \case
      EVar (Name s _) -> Just [s]
      EDot inner (DotName (Name s _)) -> (++ [s]) <$> modulePathOf inner
      _ -> Nothing
    modObjPathOf = \case
      EKindQualified SelModule (Name s _) _ -> Just [s]
      EDot inner (DotName (Name s _)) -> (++ [s]) <$> modObjPathOf inner >>= ensureModObj
      _ -> Nothing
      where
        ensureModObj segs = Just segs

-- visibility of a member of another module (§8.5): only exported names
-- are accessible from outside the defining module
memberVisible :: CheckState -> ModuleName -> Text -> Bool
memberVisible st mn nm =
  mn == csModule st
    || case Map.lookup mn (csModuleExports st) of
      Just ex -> nm `elem` ex
      Nothing -> True -- prelude and unknown modules: unrestricted

-- a member completion of a reified module path: either a deeper module
-- object or nothing nameable (§2.8.6)
elabModuleMember :: Ctx -> [Text] -> Span -> CheckM (Term, Value)
elabModuleMember ctx segs sp = do
  st <- get
  if Map.member (ModuleName segs) (csModuleExports st) || ModuleName segs == csModule st
    then pure (moduleObjectFor (ModuleName segs))
    else do
      errAt sp "E_STATIC_OBJECT_UNRESOLVED" (Just "kappa.name.unresolved")
        ("no module named '" <> T.intercalate "." segs <> "' is in this compilation unit (Spec §2.8.6)")
      anyHole ctx

-- §2.8.6 kind-qualified static-object expressions: select the named
-- facet; an unknown subject is E_STATIC_OBJECT_UNRESOLVED.
elabKindQualified :: Ctx -> KindSelector -> Name -> Span -> CheckM (Term, Value)
elabKindQualified ctx sel (Name n nsp) sp = do
 merged <- effMerged ctx
 case sel of
  SelModule -> do
    st <- get
    let target = case Map.lookup n (csModuleAliases st) of
          Just mn -> Just mn
          Nothing
            | Map.member (ModuleName [n]) (csModuleExports st) -> Just (ModuleName [n])
            | otherwise -> Nothing
    case target of
      Just mn -> pure (moduleObjectFor mn)
      Nothing -> do
        errAt sp "E_STATIC_OBJECT_UNRESOLVED" (Just "kappa.name.unresolved")
          ("no module named '" <> n <> "' is in scope (Spec §2.8.6)")
        anyHole ctx
  -- §7.1.1: resolution is by ordinary lookup in the selected position,
  -- so lexically scoped declarations precede globals: a §9.3.1.1
  -- scoped-effect declaration provides both a type facet (its effect
  -- interface, §7.6) and an effect-label facet (its canonical self
  -- label)
  SelEffectLabel
    | Just eli <- Map.lookup n merged ->
        pure (CGlob (eliLabel eli), VGlobN (gPrel "EffLabel") [])
  SelType
    | Just (i, e) <- lookupCtx n ctx -> do
        t <- forceM (ceType e)
        case t of
          VSort _ -> pure (CVar i, ceType e)
          _ -> do
            errAt nsp "E_STATIC_OBJECT_KIND_MISMATCH" (Just "kappa-hs.static-object.kind")
              ("'" <> n <> "' is not a type in this scope; the 'type' selector does not apply (Spec §7.1.1)")
            anyHole ctx
  _ -> do
    mg <- lookupGlobalName n
    -- §2.8.3/§7.1.1: the selector must agree with the named facet — a
    -- trait has no type facet, so `type C` on a trait is rejected, and
    -- `trait T` on a non-trait declaration is rejected
    isTrait <- case mg of
      Just g -> gets (Map.member g . csTraits)
      Nothing -> pure False
    isLabelG <- case mg of
      Just g -> do
        mt <- gets (fmap gdType . Map.lookup g . csGlobals)
        case mt of
          Just tv ->
            forceM tv >>= \case
              VGlobN lg [] -> pure (lg == gPrel "EffLabel")
              _ -> pure False
          Nothing -> pure False
      Nothing -> pure False
    if sel == SelType && isTrait
      then do
        errAt nsp "E_STATIC_OBJECT_KIND_MISMATCH" (Just "kappa-hs.static-object.kind")
          ("'" <> n <> "' names a trait; the 'type' selector does not apply (Spec §2.8.3)")
        anyHole ctx
      else if sel == SelTrait && isJust mg && not isTrait
        then do
          errAt nsp "E_STATIC_OBJECT_KIND_MISMATCH" (Just "kappa-hs.static-object.kind")
            ("'" <> n <> "' does not name a trait; the 'trait' selector requires a trait declaration (Spec §7.1.1)")
          anyHole ctx
      else if sel == SelEffectLabel && isJust mg && not isLabelG
        then do
          errAt nsp "E_STATIC_OBJECT_KIND_MISMATCH" (Just "kappa-hs.static-object.kind")
            ("'" <> n <> "' does not name an effect label; the 'effectLabel' selector requires an effect-label declaration (Spec §7.1.1)")
          anyHole ctx
      else do
        mr <- case mg of
          Just g -> globalType g
          Nothing -> pure Nothing
        case mr of
          Just r -> pure r
          Nothing -> do
            errAt nsp "E_STATIC_OBJECT_UNRESOLVED" (Just "kappa.name.unresolved")
              ("kind-qualified name does not resolve to a static object: '" <> n <> "' (Spec §2.8.6)")
            anyHole ctx

-- | §2.8.4: the manifest value of a receiver term — resolved through
-- local definientia, module-level lets without widening signatures,
-- record projections of such, and direct (immediately-used) results.
-- A binding under a widening signature forgets static-object identity.
manifestValue :: Ctx -> Term -> CheckM (Maybe Value)
manifestValue ctx tm = case tm of
  CGlob g -> do
    st <- get
    if Map.member g (csManifest st) || Map.member g (csDatas st)
      then case Map.lookup g (csGlobals st) >>= gdValue of
        Just v -> Just <$> forceM v
        Nothing -> pure (Just (VGlobN g []))
      else pure Nothing
  CProj t f -> do
    mv <- manifestValue ctx t
    -- §13.2.10: transparent members of a sealed package stay manifest;
    -- opaque members forget static-object identity
    let unwrap v =
          forceM v >>= \case
            VSealV ls r | f `notElem` ls -> unwrap r
            v' -> pure v'
    mv' <- traverse unwrap mv
    case mv' of
      Just (VRecordV fs) | Just v <- lookup f fs -> Just <$> forceM v
      _ -> pure Nothing
  -- P0.4: a fixed-offset projection manifests by NAME exactly like CProj (the
  -- catch-all's eager evalIn would wrongly manifest a non-manifest projection).
  CProjAt t f _ -> do
    mv <- manifestValue ctx t
    let unwrap v =
          forceM v >>= \case
            VSealV ls r | f `notElem` ls -> unwrap r
            v' -> pure v'
    mv' <- traverse unwrap mv
    case mv' of
      Just (VRecordV fs) | Just v <- lookup f fs -> Just <$> forceM v
      _ -> pure Nothing
  CVar i -> case drop i (ctxEnv ctx) of
    (v : _) -> do
      v' <- forceM v
      pure $ case v' of
        VRigid {} -> Nothing -- an opaque binder, not a let definiens
        _ -> Just v'
    [] -> pure Nothing
  _ -> Just <$> (evalIn ctx tm >>= forceM)

-- a reified module object (§2.8.6): a record carrying the module
-- identity in a tag field, so member access through rebindings works
moduleObjectFor :: ModuleName -> (Term, Value)
moduleObjectFor (ModuleName segs) =
  let tag = "__module:" <> T.intercalate "." segs
   in (CRecordV [(tag, CRecordV [])], VRecordT [(tag, VRecordT [])])

-- member access on a reified module object (§2.8.6/§8.5)
moduleMember :: Ctx -> ModuleName -> Name -> CheckM (Term, Value)
moduleMember ctx modName mname = do
  st <- get
  let g = GName modName (nameText mname)
  mt <-
    if memberVisible st modName (nameText mname)
      then case (Map.member g (csDatas st), Map.lookup g (csGlobals st)) of
        -- a member naming a data type denotes the type facet; term
        -- applications fall through to its same-named constructor
        (True, Just gd) -> pure (Just (CGlob g, gdType gd))
        _ -> globalTerm g
      else pure Nothing
  case mt of
    Just r -> pure r
    Nothing -> do
      errAt (nameSpan mname) "E_NAME_UNRESOLVED" (Just "kappa.name.unresolved")
        ("module object has no exported member '" <> nameText mname <> "' (Spec §2.8.6, §8.5)")
      anyHole ctx

elabDotUnqualified :: Ctx -> Expr -> DotMember -> Name -> CheckM (Term, Value)
elabDotUnqualified ctx e member mname = do
  -- module-qualified reference?
  case e of
    EVar (Name base _) -> do
      st <- get
      case lookupCtx base ctx of
        Just (i, _) -> do
          -- a local rebinding of a reified type object (§2.8.3): its
          -- definiens names the data type, select the constructor
          mv <- case drop i (ctxEnv ctx) of
            (v : _) -> Just <$> forceM v
            [] -> pure Nothing
          case mv of
            Just (VGlobN d _)
              | Just di <- Map.lookup d (csDatas st)
              , (ctorG : _) <- [c | c <- diCtors di, gnameText c == nameText mname] -> do
                  mt <- globalTerm ctorG
                  case mt of
                    Just r -> pure r
                    Nothing -> ordinary mname
            _ -> ordinary mname
        Nothing ->
          case Map.lookup base (csModuleAliases st) of
            Just modName -> do
              let g = GName modName (nameText mname)
              mt <-
                if memberVisible st modName (nameText mname)
                  then globalTerm g
                  else pure Nothing -- private members are not accessible (§8.5)
              case mt of
                Just r -> pure r
                Nothing -> do
                  -- §3.1.4/§8.3.1A: when the alias spelling 'base' also
                  -- names a same-spelling type/constructor/declaration,
                  -- the qualified name resolved through the alias rather
                  -- than that declaration, and the alias collision is the
                  -- primary repairable cause (repair: rename the alias or
                  -- qualify the type). Report the §3.1.4-mandated portable
                  -- code; otherwise the alias is unambiguous and the
                  -- member is simply absent.
                  mShadow <- shadowedDeclKind base
                  case mShadow of
                    Just kind ->
                      errAt (nameSpan mname) "E_MODULE_ALIAS_TYPE_COLLISION"
                        (Just "kappa.name.module-alias-collision")
                        ( "qualified name '" <> base <> "." <> nameText mname
                            <> "' resolves through module alias '" <> base
                            <> "' (denoting " <> moduleNameText modName
                            <> "), which shadows the same-spelling " <> kind
                            <> " '" <> base
                            <> "'; the alias has no exported member '"
                            <> nameText mname
                            <> "'. Rename the alias or qualify the "
                            <> kind <> " (Spec §8.3.1A, §3.1.4)"
                        )
                    Nothing ->
                      errAt (nameSpan mname) "E_NAME_UNRESOLVED" (Just "kappa.name.unresolved")
                        ("module '" <> base <> "' has no exported member '" <> nameText mname <> "' (Spec §8.5)")
                  anyHole ctx
            Nothing -> do
              -- static member of a type: T.C selects constructor (§7.3)
              mg <- lookupGlobalName base
              stx <- get
              mDataG <- case mg of
                Just tyG
                  | Map.member tyG (csDatas stx) -> pure (Just tyG)
                  | Just gd <- Map.lookup tyG (csGlobals stx)
                  , Just v <- gdValue gd -> do
                      -- a rebound reified type object (§2.8.3): the
                      -- binding's value names the data type
                      v' <- forceM v
                      pure $ case v' of
                        VGlobN d _ | Map.member d (csDatas stx) -> Just d
                        _ -> Nothing
                _ -> pure Nothing
              case mDataG of
                Just tyG
                  | Just di <- Map.lookup tyG (csDatas stx)
                  , Just ctorG <- lookupCtorIn di (nameText mname) -> do
                      mt <- globalTerm ctorG
                      case mt of
                        Just r -> pure r
                        Nothing -> anyHole ctx
                _ -> ordinary mname
              where
                lookupCtorIn di nm =
                  case [c | c <- diCtors di, gnameText c == nm] of
                    (c : _) -> Just c
                    [] -> Nothing
    _ -> ordinary mname
  where
    ordinary mn0 = do
      (tm, ty) <- infer ctx e
      (tm1, ty1) <- insertAllImplicits ctx (exprSpan e) tm ty
      -- §2.8.3/§2.8.6: a receiver VALUE that is a reified type object
      -- selects static constructors; a reified module object selects
      -- module members. Only §2.8.4 manifest bindings (no widening
      -- signature) preserve the identity.
      mrv <- manifestValue ctx tm1
      st0 <- get
      case fromMaybe (VRecordV []) mrv of
        VGlobN d _
          | Just di <- Map.lookup d (csDatas st0)
          , (ctorG : _) <- [c | c <- diCtors di, gnameText c == nameText mn0] -> do
              mt <- globalTerm ctorG
              case mt of
                Just r -> pure r
                Nothing -> ordinaryAt mn0 tm1 ty1
        VRecordV [(tag, _)]
          | Just modTxt <- T.stripPrefix "__module:" tag ->
              moduleMember ctx (ModuleName (T.splitOn "." modTxt)) mn0
        _ -> ordinaryAt mn0 tm1 ty1

    ordinaryAt mn0 tm1 ty1 = do
      t0 <- forceM ty1
      -- §13.2.10: package-member selection sees the signature's
      -- underlying record type (opacity is enforced by the value)
      t <- case t0 of
        VSigT _ inner -> forceM inner
        _ -> pure t0
      case t of
        VRecordT fs
          | Just fty <- lookup (nameText mn0) fs -> do
              -- §13.2.1: a dependent field type sees the receiver as 'this'
              fty' <- substThisInto ctx tm1 fty
              -- P0.4: this is the ONLY statically-known CLOSED record layout,
              -- so emit a fixed-offset projection — the field's index in the
              -- record's slot order.  The K_REC value's slots follow `fs`
              -- order; for NAMED records that order is `sortOn fst` (the
              -- canonical layout), so the index is the field's position in
              -- `fs`.  CRUCIALLY we only do this when `fs` is *already*
              -- sorted: tuples are the one closed record whose value is built
              -- POSITIONALLY (`_1`.._n), which diverges from lexicographic
              -- order at arity >= 10 (`_10` < `_2`).  Emitting a fixed offset
              -- there would read the wrong slot, so any unsorted layout falls
              -- back to the name-based CProj (kproj).  Every other projection
              -- site (open/sealed/dict/derived) keeps CProj too, and the
              -- backend treats CProjAt == CProj when it cannot use an offset.
              let f = nameText mn0
                  names = map fst fs
                  proj
                    | names == sort names
                    , Just i <- elemIndex f names = CProjAt tm1 f i
                    | otherwise = CProj tm1 f
              pure (proj, fty')
          | otherwise -> do
              -- a record receiver without the field: try method sugar,
              -- otherwise report the missing field (§13.1.4)
              mg <- lookupGlobalName (nameText mn0)
              case mg of
                Just _ -> methodSugar tm1 t mn0
                Nothing -> do
                  -- §3.1.11 / §13.2.11: internal existential labels are
                  -- not source-addressable fields, so they are excluded
                  -- from the user-facing field list (a package that
                  -- exposes only such labels lists no fields).
                  let visibleFields = [n | (n, _) <- fs, not (isExistsInternalLabel n)]
                  errAt (nameSpanOf member) "E_RECORD_PROJECTION_MISSING_FIELD"
                    (Just "kappa.name.unresolved")
                    ("record has no field '" <> nameText mn0
                       <> "' (fields: " <> T.intercalate ", " visibleFields <> ")")
                  anyHole ctx
        -- §11.3.1A: explicit-prefix projection on an open record
        VGlobN (GName pm "__openRec") [_, (_, prefixV)]
          | pm == preludeModule -> do
              pf <- forceM prefixV
              case pf of
                VRecordT fs
                  | Just fty <- lookup (nameText mn0) fs -> do
                      fty' <- substThisInto ctx tm1 fty
                      pure (CProj tm1 (nameText mn0), fty')
                _ -> methodSugar tm1 t mn0
        -- trait-dictionary member projection d.(==) (§14.2.1)
        VGlobN headG spine -> do
          st <- get
          case Map.lookup headG (csTraits st) of
            Just ti
              | nameText mn0 `elem` tiMembers ti -> do
                  memberTy <- memberTypeOf ctx headG (nameText mn0) (map snd spine) tm1
                  pure (CProj tm1 (nameText mn0), memberTy)
            _ ->
              -- named-field projection on single-constructor data
              -- (§10.2), or on a §7.4.1 flow-refined subset of the
              -- constructors when the receiver is a refined variable
              case Map.lookup headG (csDatas st) of
                Just di
                  | ctors <- projectableCtors ctx di
                  , not (null ctors)
                  , Just alts0 <-
                      sequence
                        [ do
                            ci <- Map.lookup ctorG (csCtors st)
                            idx <- elemIndex (Just (nameText mn0)) (map fst (ciFields ci))
                            Just (ctorG, ci, idx)
                        | ctorG <- ctors
                        ] -> do
                      fty <- case alts0 of
                        ((ctorG, ci, idx) : _) -> do
                          fieldTys <- ctorFieldTypes ctx ctorG ci t (nameSpanOf member)
                          case drop idx fieldTys of
                            (x : _) -> pure x
                            [] -> freshMetaV ctx
                        [] -> freshMetaV ctx
                      let altOf (ctorG, ci, idx) =
                            let arity = length (ciFields ci)
                                pats = [if i == idx then CPVar "__field" else CPWild | i <- [0 .. arity - 1]]
                             in CaseAlt (CPCtor ctorG pats) Nothing (CVar 0)
                      pure (CMatch tm1 (map altOf alts0), fty)
                _ -> methodSugar tm1 t mn0
        _ -> methodSugar tm1 t mn0

    -- method-call sugar (§7.4): recv.name args → name recv (receiver
    -- insertion at the first explicit binder).
    methodSugar recvTm recvTy mn0 = do
      mg <- lookupGlobalName (nameText mn0)
      case mg of
        Just g -> do
          st <- get
          mt <- globalTerm g
          case (Map.lookup g (csProjections st), mt) of
            -- receiver-projection sugar (§7.4): the receiver place
            -- supplies the unique place binder
            (Just pj, Just (dTm, dTy))
              | [pn] <- pjPlaceNames pj
              , pjIsPlace pj == [True] ->
                  applyDescriptor ctx (nameSpanOf member) dTm dTy (RootsSeparate [(pn, e)])
            (_, Just (fTm, fTy)) -> case Map.lookup g (csReceivers st) of
              -- §7.4: eligibility requires exactly one explicit
              -- receiver-marked binder; the receiver is inserted at it
              Just [i] -> applyRecvAt i fTm fTy recvTm recvTy
              Just _ -> do
                errAt (nameSpanOf member) "E_UNRESOLVED_MEMBER" (Just "kappa.name.unresolved")
                  ("'" <> nameText mn0
                     <> "' does not have exactly one receiver-marked binder, so it is not eligible for method-call sugar (§7.4)")
                anyHole ctx
              -- §7.4: a callable without a receiver-marked binder is
              -- not eligible for method-call sugar
              Nothing -> do
                errAt (nameSpanOf member) "E_UNRESOLVED_MEMBER" (Just "kappa.name.unresolved")
                  ("'" <> nameText mn0
                     <> "' has no receiver-marked binder, so it is not eligible for method-call sugar (§7.4)")
                anyHole ctx
            (_, Nothing) -> failMember recvTy mn0
        Nothing -> failMember recvTy mn0

    -- receiver insertion at the receiver-marked explicit binder
    -- (§7.4): preceding explicit binders become wrapper-lambda
    -- parameters filled by the remaining call-site arguments
    applyRecvAt recvIdx fTm0 fTy0 recvTm0 recvTy = go ctx (0 :: Int) fTm0 fTy0
      where
        go c depth accTm ty0 = do
          ty <- forceM ty0
          case ty of
            VPi Impl q _ dom clo -> do
              iTm <- resolveImplicitQ c (nameSpanOf member) q dom
              iV <- evalIn c iTm
              ty' <- clApp clo iV
              go c depth (CApp Impl accTm iTm) ty'
            VPi Expl _ _ dom clo
              | depth == recvIdx -> do
                  let recvTm = shiftTerm (ctxLen c - ctxLen ctx) 0 recvTm0
                  expectType c (exprSpan e) recvTy dom
                  rV <- evalIn c recvTm
                  ty' <- clApp clo rV
                  pure (CApp Expl accTm recvTm, ty')
            VPi Expl q nm dom clo -> do
              let c' = bindCtx nm False dom c
              cod <- clApp clo (VRigid (ctxLen c) [])
              (body, bodyTy) <- go c' (depth + 1) (CApp Expl (shiftTerm 1 0 accTm) (CVar 0)) cod
              domTm <- quoteIn c dom
              bodyTyTm <- quoteIn c' bodyTy
              piV <- evalIn c (CPi Expl q nm domTm bodyTyTm)
              pure (CLam Expl q nm body, piV)
            _ -> do
              errAt (nameSpanOf member) "E_APPLICATION_NONCALLABLE" (Just "kappa-hs.application.non-callable")
                "member is not callable with a receiver"
              anyHole ctx

    failMember recvTy mn0 = do
      recvF <- forceM recvTy
      case recvF of
        -- an unsolved flex receiver type usually means the receiver
        -- itself did not elaborate (e.g. an unresolved name); a member
        -- error on '?m' would be cascade noise (§3.1.14 recovery
        -- hygiene) — but only when the receiver actually reported
        VFlex {} -> do
          ds <- gets csDiags
          let recvSp = exprSpan e
              within dd =
                spanFile (dPrimary dd) == spanFile recvSp
                  && spanStart (dPrimary dd) >= spanStart recvSp
                  && spanEnd (dPrimary dd) <= spanEnd recvSp
          unless (any (\dd -> isError dd && within dd) ds) $
            report $
              diag SevError StageElaborate "E_UNRESOLVED_MEMBER" (Just "kappa.name.unresolved")
                (nameSpanOf member)
                ("no member '" <> nameText mn0 <> "' is known on this receiver (its type is undetermined, §7.3)")
        _ -> do
          rT <- quoteIn ctx recvF
          report $
            withNote ("receiver type: " <> renderTerm rT) $
              diag SevError StageElaborate "E_UNRESOLVED_MEMBER" (Just "kappa.name.unresolved")
                (nameSpanOf member)
                ("no member '" <> nameText mn0 <> "' on this receiver (§7.3)")
      anyHole ctx

    -- which constructors a field projection may assume (§10.2 single
    -- constructor, or the §7.4.1 flow-refined subset for a refined
    -- variable receiver)
    projectableCtors c di
      | [ctorG] <- diCtors di = [ctorG]
      | EVar n <- e
      , Just gs <- ctxRefinementOf c (nameText n)
      , not (null gs)
      , all (`elem` diCtors di) gs =
          gs
      | otherwise = []

    nameSpanOf = \case
      DotName n -> nameSpan n
      DotOperator n -> nameSpan n

memberTypeOf :: Ctx -> GName -> Text -> [Value] -> Term -> CheckM Value
memberTypeOf ctx traitG member args dictTm = do
  -- member projection type: stored as global "<trait>.<member>" Pi type;
  -- here we re-derive from the member-projection global.
  mt <- globalTerm (memberGlobal traitG member)
  case mt of
    Just (_, ty) -> peel ty args
    Nothing -> pure (VSort 0)
  where
    peel ty [] = do
      t <- forceM ty
      case t of
        VPi Impl _ _ _ clo -> do
          -- instantiate the dict binder with the receiver itself, so
          -- associated-static-member projections in the member type
          -- (§14.2.1) name the receiver's own members
          dv <- evalIn ctx dictTm
          clApp clo dv
        _ -> pure t
    peel ty (a : as) = do
      t <- forceM ty
      case t of
        VPi Impl _ _ _ clo -> do
          r <- clApp clo a
          peel r as
        _ -> pure t

memberGlobal :: GName -> Text -> GName
memberGlobal (GName m t) member = GName m (t <> "." <> member)

-- Elvis `l ?: r` (§16.1.2): unwrap an Option left operand, with the
-- right operand as the None fallback.
elabElvis :: Ctx -> Expr -> Expr -> Span -> CheckM (Term, Value)
elabElvis ctx l r sp = do
  (lTm, lTy) <- infer ctx l
  (lTm1, lTy1) <- insertAllImplicits ctx (exprSpan l) lTm lTy
  t <- forceM lTy1
  case t of
    VGlobN (GName _ "Option") [(_, payloadTy)] -> do
      rTm <- check ctx r payloadTy
      let alts =
            [ CaseAlt (CPCtor (gPrel "Some") [CPVar "__elvis"]) Nothing (CVar 0)
            , CaseAlt (CPCtor (gPrel "None") []) Nothing rTm
            ]
      pure (CMatch lTm1 alts, payloadTy)
    _ -> do
      lT <- quoteIn ctx t
      report $
        withNote ("left operand type: " <> renderTerm lT) $
          diag SevError StageElaborate "E_TYPE_EQUALITY_MISMATCH" (Just "kappa.type.mismatch") sp
            "the left operand of the Elvis operator '?:' must have type Option T (§16.1.2)"
      _ <- check ctx r t
      pure (lTm1, t)

-- safe navigation e?.m (§16.1.1.2)
elabSafeNav :: Ctx -> Expr -> DotMember -> CheckM (Term, Value)
elabSafeNav ctx e member = do
  (pTm, pTy) <- infer ctx e
  (pTm1, pTy1) <- insertAllImplicits ctx (exprSpan e) pTm pTy
  t <- forceM pTy1
  case t of
    VGlobN (GName _ "Option") [(_, payloadTy)] -> do
      -- bind __x : payload, elaborate body member access
      let nm = "__nav"
          ctx' = bindCtx nm False payloadTy ctx
      (bodyTm, bodyTy) <- elabDot ctx' (EVar (Name nm (memberSpan member))) member
      bodyT <- forceM bodyTy
      (wrapTm, resTy) <- case bodyT of
        VGlobN (GName _ "Option") [(_, u)] -> pure (bodyTm, u)
        VFlex {} -> do
          errAt (memberSpan member) "E_SAFE_NAVIGATION_AMBIGUOUS" (Just "kappa.type.mismatch")
            "the result type of '?.' is undetermined; annotate the member type (§16.1.1.2)"
          pure (bodyTm, bodyT)
        u -> pure (CCtor (gPrel "Some") [bodyTm], u)
      let alts =
            [ CaseAlt (CPCtor (gPrel "Some") [CPVar "__nav"]) Nothing wrapTm
            , CaseAlt (CPCtor (gPrel "None") []) Nothing (CCtor (gPrel "None") [])
            ]
      pure (CMatch pTm1 alts, VGlobN (gPrel "Option") [(Expl, resTy)])
    VFlex {} -> do
      errAt (exprSpan e) "E_SAFE_NAVIGATION_AMBIGUOUS" (Just "kappa.type.mismatch")
        "the receiver type of '?.' is undetermined here, so the navigation is ambiguous; annotate the receiver (§16.1.1.2)"
      anyHole ctx
    _ -> do
      errAt (exprSpan e) "E_SAFE_NAVIGATION_RECEIVER_NOT_OPTION" (Just "kappa.type.mismatch")
        "the receiver of '?.' must have type Option T (§16.1.1.2)"
      anyHole ctx
  where
    memberSpan = \case
      DotName n -> nameSpan n
      DotOperator n -> nameSpan n

elabIs :: Ctx -> Expr -> CtorRef -> CheckM (Term, Value)
elabIs ctx e cref = do
  (tm, ty) <- infer ctx e
  (tm1, _) <- insertAllImplicits ctx (exprSpan e) tm ty
  mg <- resolveCtor ctx cref
  case mg of
    Just (g, ci) -> do
      let arity = length (ciFields ci)
          alts =
            [ CaseAlt (CPCtor g (replicate arity CPWild)) Nothing (CCtor (gPrel "True") [])
            , CaseAlt CPWild Nothing (CCtor (gPrel "False") [])
            ]
      pure (CMatch tm1 alts, VGlobN (gPrel "Bool") [])
    Nothing -> anyHole ctx

resolveCtor :: Ctx -> CtorRef -> CheckM (Maybe (GName, CtorInfo))
resolveCtor ctx (CtorRef mqual n) = do
  st <- get
  let candidates = case mqual of
        Nothing ->
          [ g | (g, _) <- Map.toList (csCtors st), gnameText g == nameText n
          , inScope st g
          ]
        Just q ->
          [ ctorG
          | (dg, di) <- Map.toList (csDatas st)
          , gnameText dg == nameText q
          , inScope st dg
          , ctorG <- diCtors di
          , gnameText ctorG == nameText n
          ]
  case candidates of
    (g : _) -> do
      pure ((,) g <$> Map.lookup g (csCtors st))
    [] -> do
      -- §2.8.4/§7.6: a rebound type object preserves its identity for
      -- dotted lookup — the qualifier may be a local or module binding
      -- whose manifest value is a data type constructor
      mDataG <- case mqual of
        Just q -> do
          mv <- case lookupCtx (nameText q) ctx of
            Just (i, _) -> manifestValue ctx (CVar i)
            Nothing -> do
              mg <- lookupGlobalName (nameText q)
              case mg of
                Just g -> manifestValue ctx (CGlob g)
                Nothing -> pure Nothing
          case mv of
            Just (VGlobN dg []) | Map.member dg (csDatas st) -> pure (Just dg)
            _ -> pure Nothing
        Nothing -> pure Nothing
      case mDataG of
        Just dg
          | Just di <- Map.lookup dg (csDatas st)
          , (ctorG : _) <- [c | c <- diCtors di, gnameText c == nameText n] ->
              pure ((,) ctorG <$> Map.lookup ctorG (csCtors st))
        _ -> do
          errAt (nameSpan n) "E_NAME_UNRESOLVED" (Just "kappa.name.unresolved")
            ("unresolved constructor '" <> nameText n <> "'")
          pure Nothing
  where
    inScope st g@(GName m _) =
      m == csModule st || Map.lookup (gnameText g) (csScope st) == Just g || isPrel m
    isPrel m = m == preludeModule

-- record patch (§13.2.5): closed records, '='-updates and ':='-extends.
elabPatch :: Ctx -> Expr -> [PatchItem] -> Span -> CheckM (Term, Value)
elabPatch = elabPatchWith False

-- @nested@ selects the §13.2.5 path diagnostic for unknown fields.
elabPatchWith :: Bool -> Ctx -> Expr -> [PatchItem] -> Span -> CheckM (Term, Value)
elabPatchWith _ ctx e [PatchSection recv rhs] sp = elabSectionUpdate ctx e recv rhs sp
elabPatchWith nested ctx e items sp = do
  (tm, ty) <- infer ctx e
  (tm1, ty1) <- insertAllImplicits ctx (exprSpan e) tm ty
  t <- forceM ty1
  dep <- case t of
    VRecordT fs -> do
      depTy <- recordTypeIsDependent ctx fs
      let depVal =
            isNothing (lookupCtx "this" ctx)
              && not
                (null (concat [surfaceThisRefs v | PatchUpdate _ (PatchValue v) <- items]))
      pure (depTy || depVal)
    _ -> pure False
  case t of
    VRecordT fs | dep -> elabDependentPatch ctx tm1 fs items sp
    VRecordT fs -> do
      let updateNames = [nameText n | PatchUpdate [(False, n)] _ <- items]
          extendNames = [nameText n | PatchExtend n _ <- items]
          -- nested paths (§13.2.5): group by head segment
          nestedHeads =
            foldr (\n acc -> if nameText n `elem` map nameText acc then acc else n : acc) []
              [h | PatchUpdate ((False, h) : _ : _) _ <- items]
      forM_ (duplicatesOf updateNames) $ \n ->
        errAt sp "E_RECORD_PATCH_DUPLICATE_PATH" (Just "kappa-hs.record.patch-duplicate")
          ("record patch updates field '" <> n <> "' more than once (§13.2.5)")
      forM_ (duplicatesOf extendNames) $ \n ->
        errAt sp "E_ROW_EXTENSION_DUPLICATE_LABEL" (Just "kappa-hs.row.extension-duplicate")
          ("row extension introduces label '" <> n <> "' more than once (§13.2.6)")
      forM_ [h | h <- nestedHeads, nameText h `elem` updateNames] $ \h ->
        errAt (nameSpan h) "E_RECORD_PATCH_PREFIX_CONFLICT" (Just "kappa-hs.record.patch-prefix-conflict")
          ("record patch both replaces '" <> nameText h <> "' and updates a path beneath it (§13.2.5)")
      groupUps <- forM nestedHeads $ \h -> do
        let subItems =
              [ PatchUpdate restPath v
              | PatchUpdate ((False, h0) : restPath@(_ : _)) v <- items
              , nameText h0 == nameText h
              ]
        if nameText h `elem` map fst fs
          then do
            (htm, _) <- elabPatchWith True ctx (EDot e (DotName h)) subItems sp
            pure (Just (nameText h, htm, Nothing))
          else do
            errAt (nameSpan h) "E_RECORD_PATCH_UNKNOWN_PATH" (Just "kappa.name.unresolved")
              ("record patch path starts at unknown field '" <> nameText h <> "' (§13.2.5)")
            pure Nothing
      results0 <- forM items $ \case
        PatchUpdate [(False, n)] (PatchValue v) -> do
          case lookup (nameText n) fs of
            Just fty -> do
              vt <- check ctx v fty
              pure (Just (nameText n, vt, Nothing))
            Nothing -> do
              if nested
                then
                  errAt (nameSpan n) "E_RECORD_PATCH_UNKNOWN_PATH" (Just "kappa.name.unresolved")
                    ("record patch path names unknown field '" <> nameText n <> "' (§13.2.5)")
                else
                  errAt (nameSpan n) "E_UNKNOWN_FIELD" (Just "kappa.name.unresolved")
                    ("record has no field '" <> nameText n <> "'")
              pure Nothing
        PatchUpdate ((False, _) : _ : _) _ -> pure Nothing -- grouped above
        PatchUpdate _ _ -> do
          unsupportedAt sp "implicit patch paths are not supported by this implementation"
          pure Nothing
        -- §13.2.6 row extension: the label must be absent; the result
        -- row gains the field
        PatchExtend n v ->
          case lookup (nameText n) fs of
            Just fty -> do
              errAt (nameSpan n) "E_ROW_EXTENSION_EXISTING_FIELD" (Just "kappa.row.lacks-failed")
                ("row extension ':=' introduces '" <> nameText n <> "', but the record already has that field (§13.2.6)")
              vt <- check ctx v fty
              pure (Just (nameText n, vt, Nothing))
            Nothing -> do
              (vt0, vty0) <- infer ctx v
              (vt, vty) <- insertAllImplicits ctx (exprSpan v) vt0 vty0
              pure (Just (nameText n, vt, Just vty))
        PatchSection _ _ -> do
          -- a projection-section item mixed with other patch items
          errAt sp "E_PROJECTION_UPDATE_TARGET_UNSUPPORTED" (Just "kappa-hs.projection.update")
            "a projection-section update must be the only item of its update (§13.2.5, §30.2.2.4)"
          pure Nothing
        -- §13.2.5: record updates do not admit field punning
        PatchPun n -> do
          errAt (nameSpan n) "E_RECORD_PATCH_INVALID_ITEM" (Just "kappa-hs.record.patch-invalid")
            ("a record update item must be written 'field = value'; punning '" <> nameText n <> "' is not admitted (§13.2.5)")
          pure Nothing
      let entries = catMaybes (results0 ++ groupUps)
          ups = [(n, vt) | (n, vt, _) <- entries]
          news =
            foldl
              (\acc p -> if fst p `elem` map fst acc then acc else acc ++ [p])
              []
              [(n, (vt, vty)) | (n, vt, Just vty) <- entries, n `notElem` map fst fs]
          allTypes = sortOn fst (fs ++ [(n, vty) | (n, (_, vty)) <- news])
          fields =
            [ ( n
              , fromMaybe
                  (maybe (CProj tm1 n) fst (lookup n news))
                  (lookup n ups)
              )
            | (n, _) <- allTypes
            ]
      pure (CRecordV fields, VRecordT allTypes)
    -- §13.2.6 row extension over an open record (§11.3.1A)
    VGlobN (GName pm "__openRec") [(_, rowV), (_, prefixV)]
      | pm == preludeModule -> do
          pf <- forceM prefixV
          case pf of
            VRecordT fs -> elabOpenPatch ctx tm1 rowV fs items sp
            _ -> do
              errAt sp "E_TYPE_EQUALITY_MISMATCH" (Just "kappa.type.mismatch")
                "record patch requires a record"
              anyHole ctx
    _ -> do
      errAt sp "E_TYPE_EQUALITY_MISMATCH" (Just "kappa.type.mismatch") "record patch requires a closed record"
      anyHole ctx

-- | Row extension and explicit-prefix update on an open record
-- (§13.2.6, §11.3.1A): 'rec.{ l := v }' requires 'LacksRec r l'
-- evidence in scope and appends the field to the explicit prefix.
elabOpenPatch :: Ctx -> Term -> Value -> [(Text, Value)] -> [PatchItem] -> Span -> CheckM (Term, Value)
elabOpenPatch ctx tm1 rowV fs items sp = do
  results <- forM items $ \case
    PatchExtend n v
      | Just fty <- lookup (nameText n) fs -> do
          errAt (nameSpan n) "E_ROW_EXTENSION_EXISTING_FIELD" (Just "kappa.row.lacks-failed")
            ("row extension ':=' introduces '" <> nameText n <> "', but the record already has that field (§13.2.6)")
          vt <- check ctx v fty
          pure (Just (nameText n, vt, Nothing))
      | otherwise -> do
          -- §13.2.1 uniqueness side condition: the residual row must
          -- be known to lack the new label
          let goal =
                VGlobN (gPrel "LacksRec")
                  [(Expl, rowV), (Expl, VLit (LitStr (nameText n)))]
          saved <- get
          _ <- resolveImplicitQ ctx (nameSpan n) QW goal
          after <- get
          when (length (csDiags after) /= length (csDiags saved)) $ do
            put saved
            errAt (nameSpan n) "E_ROW_EXTENSION_MISSING_LACKS_CONSTRAINT" (Just "kappa.row.lacks-failed")
              ( "extending the open row with '" <> nameText n
                  <> "' requires a 'LacksRec r " <> nameText n <> "' constraint in scope (§13.2.1, §13.2.6)"
              )
          (vt0, vty0) <- infer ctx v
          (vt, vty) <- insertAllImplicits ctx (exprSpan v) vt0 vty0
          pure (Just (nameText n, vt, Just vty))
    PatchUpdate [(_, n)] (PatchValue v)
      | Just fty <- lookup (nameText n) fs -> do
          vt <- check ctx v fty
          pure (Just (nameText n, vt, Nothing))
    _ -> do
      errAt sp "E_RECORD_PATCH_INVALID_ITEM" (Just "kappa-hs.record.patch-invalid")
        "this update item is not supported on an open record (§13.2.5)"
      pure Nothing
  let entries = catMaybes results
      newFields = [(n, vty) | (n, _, Just vty) <- entries]
  prefixTms <- mapM (\(n, v) -> (,) n <$> quoteIn ctx v) (sortOn fst (fs ++ newFields))
  prefixV' <- evalIn ctx (CRecordT prefixTms)
  let tm' =
        foldl
          ( \acc (n, vt, isNew) -> case isNew of
              Just _ ->
                CApp Expl
                  (CApp Expl
                     (CApp Expl (CGlob (gPrel "__rowExtend")) acc)
                     (CLit (LitStr n)))
                  vt
              Nothing -> acc
          )
          tm1
          entries
  pure (tm', VGlobN (gPrel "__openRec") [(Expl, rowV), (Expl, prefixV')])

-- | Projection-section update @lhs.{ (.member args) = rhs }@
-- (§13.2.5, §30.2.2.4): the member must resolve to a stable field, a
-- single-leaf selector projection, or an accessor bundle providing
-- @set@; the update rebuilds the root.
elabSectionUpdate :: Ctx -> Expr -> Expr -> Expr -> Span -> CheckM (Term, Value)
elabSectionUpdate ctx baseE recv rhs sp = case recv of
  EReceiverSection (DotName mn : _) sArgs _ -> do
    (baseTm, baseTy0) <- infer ctx baseE
    baseTy <- forceM baseTy0
    mg <- lookupGlobalName (nameText mn)
    st <- get
    let mpj = (\g -> (,) g <$> Map.lookup g (csProjections st)) =<< mg
    case (baseTy, mpj) of
      -- a plain stable field: FillPlace, i.e. the ordinary update
      (VRecordT fs, _)
        | nameText mn `elem` map fst fs, null sArgs ->
            elabPatchWith False ctx baseE [PatchUpdate [(False, mn)] (PatchValue rhs)] sp
      (_, Just (g, pj))
        | pjSelector pj ->
            case (sArgs, nub (pjYields pj)) of
              -- unique static leaf: FillProjector ≡ nested field update
              ([], [(_, path@(_ : _))]) ->
                elabPatchWith False ctx baseE
                  [PatchUpdate [(False, Name seg (nameSpan mn)) | seg <- path] (PatchValue rhs)] sp
              -- whole-root leaf: filling replaces the root
              ([], [(_, [])]) -> do
                rhsTm <- check ctx rhs baseTy
                pure (rhsTm, baseTy)
              _ -> unsupportedTarget (baseTm, baseTy)
        | otherwise -> do
            mt <- globalTerm g
            case mt of
              Nothing -> unsupportedTarget (baseTm, baseTy)
              Just (dTm, dTy) -> do
                (dTm1, dTy1) <- elabSpine ctx sp dTm dTy sArgs
                dTyF <- forceM dTy1
                mcaps <- case dTyF of
                  VRecordT capFs -> bundleCapsM capFs
                  _ -> pure Nothing
                case [(r, f) | ("set", r, f) <- fromMaybe [] mcaps] of
                  ((rootsV, focusV) : _) -> do
                    rootsF <- forceM rootsV
                    case rootsF of
                      VRecordT [(_, sV)] -> expectType ctx (exprSpan baseE) baseTy sV
                      _ -> pure ()
                    rhsTm <- check ctx rhs focusV
                    pure (CApp Expl (CApp Expl (CProj dTm1 "set") baseTm) rhsTm, baseTy)
                  [] -> unsupportedTarget (baseTm, baseTy)
      _ -> unsupportedTarget (baseTm, baseTy)
  _ -> do
    (baseTm, baseTy) <- infer ctx baseE
    unsupportedTarget (baseTm, baseTy)
  where
    unsupportedTarget (baseTm, baseTy) = do
      errAt sp "E_PROJECTION_UPDATE_TARGET_UNSUPPORTED" (Just "kappa-hs.projection.update")
        "the projection-section update target must resolve to a stable place, a selector projection, or an accessor bundle providing 'set' (§13.2.5, §30.2.2.4)"
      pure (baseTm, baseTy)

-- | §13.2.10 sealed packages: @seal e as S@. The ascribed type must be
-- a closed record type; opaque members of S keep their defining
-- equations hidden behind the resulting package value.
elabSeal :: Ctx -> Expr -> Expr -> Span -> CheckM (Term, Value)
elabSeal ctx e tyE sp = do
  (sTm, _) <- inferType ctx tyE
  sV <- forceM =<< evalIn ctx sTm
  case sV of
    VGlobN (GName pm "__openRec") _
      | pm == preludeModule -> do
          errAt sp "E_SEAL_OPEN_RECORD_ASCRIPTION" (Just "kappa-hs.seal.open-record")
            "the ascribed type of 'seal ... as ...' must be a closed record type; an open record with a residual row is not a sealing signature (§13.2.10)"
          anyHole ctx
    -- §13.2.11 existential introduction: an existential signature is a
    -- §13.2.10 signature whose opaque members are the internal witness
    -- labels. Sealing an ordinary expression against it uses the
    -- existential-specific payload-checking mode (Spec.md 13347-13364).
    VSigT ls inner
      | any isExistsInternalLabel ls ->
          forceM inner >>= \case
            VRecordT fs -> elabSeal'Exists ctx e sV ls fs witBinderNames sp
            _ -> notRecord
    VSigT ls inner ->
      forceM inner >>= \case
        VRecordT fs -> doSeal ls fs sV
        _ -> notRecord
    VRecordT fs -> doSeal [] fs sV
    _ -> notRecord
  where
    -- the surface witness binder names, recoverable only when the
    -- ascription is written directly as 'exists ...' (used to support the
    -- §13.2.11 compatibility full-surface-package spelling, 13417-13428)
    witBinderNames = case tyE of
      EExists bs _ _ -> [maybe "_" nameText (bName b) | b <- bs]
      _ -> []
    notRecord = do
      errAt sp "E_TYPE_EQUALITY_MISMATCH" (Just "kappa.type.mismatch")
        "the ascribed type of 'seal ... as ...' must elaborate to a closed record type (§13.2.10)"
      anyHole ctx
    -- record-literal payload: elaborate the retained fields in
    -- dependency order against the signature's field types (§13.2.10
    -- signature matching), inferring the hidden extras
    doSeal ls fs sV
      | ERecordLit items lsp <- e = do
          let supplied = [(nameText n, fromMaybe (EVar n) me) | RecItem _ n me <- items]
          forM_ (duplicatesOf (map fst supplied)) $ \n ->
            errAt lsp "E_RECORD_DUPLICATE_FIELD" (Just "kappa-hs.record.duplicate-field")
              ("record literal has duplicate field '" <> n <> "'")
          let missing = [nm | (nm, _) <- fs, nm `notElem` map fst supplied]
          if not (null missing)
            then do
              errAt lsp "E_TYPE_EQUALITY_MISMATCH" (Just "kappa.type.mismatch")
                ( "the sealed expression does not provide the signature field(s) "
                    <> T.intercalate ", " (map (\n -> "'" <> n <> "'") missing)
                    <> " (§13.2.10)"
                )
              anyHole ctx
            else do
              annotated <- forM fs $ \(nm, fty) -> do
                ftyTm <- quoteIn ctx fty
                let fe = fromMaybe (EVar (Name nm lsp)) (lookup nm supplied)
                    deps =
                      nub (thisDepsOf ftyTm ++ [l | l <- surfaceThisRefs fe, l `elem` map fst fs])
                pure (nm, deps, (nm, fty, fe))
              case topoFields annotated of
                Nothing -> do
                  errAt lsp "E_RECORD_DEPENDENCY_CYCLE" (Just "kappa-hs.record.dependency-cycle")
                    "the sibling references of this record literal form a cycle (§13.2.1)"
                  anyHole ctx
                Just ordered -> do
                  retained <- goLit [] [] ordered
                  -- hidden extras are discarded by the seal (§13.2.10);
                  -- they still elaborate
                  forM_ [fe | (nm, fe) <- supplied, nm `notElem` map fst fs] $ \fe ->
                    void (withThis Nothing (infer ctx fe))
                  pure (CSealE ls (CRecordV (sortOn fst retained)), sV)
      | otherwise = do
          (eTm0, eTy0) <- infer ctx e
          (eTm, eTy1) <- insertAllImplicits ctx (exprSpan e) eTm0 eTy0
          eTy <- forceM eTy1
          mefs <- case eTy of
            VRecordT efs -> pure (Just efs)
            VSigT _ inner ->
              forceM inner >>= \case
                VRecordT efs -> pure (Just efs)
                _ -> pure Nothing
            _ -> pure Nothing
          case mefs of
            Nothing -> do
              expectType ctx (exprSpan e) eTy sV
              pure (CSealE ls eTm, sV)
            Just efs -> do
              forM_ fs $ \(nm, fty) -> case lookup nm efs of
                Nothing ->
                  errAt (exprSpan e) "E_TYPE_EQUALITY_MISMATCH" (Just "kappa.type.mismatch")
                    ("the sealed expression does not provide the signature field '" <> nm <> "' (§13.2.10)")
                Just aty -> do
                  aty' <- substThisInto ctx eTm aty
                  fty' <- substThisInto ctx eTm fty
                  expectType ctx (exprSpan e) aty' fty'
              pure (CSealE ls eTm, sV)
    goLit _ _ [] = pure []
    goLit doneV doneT ((nm, fty, fe) : rest) = do
      fty' <- substThisInto ctx (CRecordV (sortOn fst doneV)) fty
      tm <- withThis (Just (ThisValue doneV doneT)) (check ctx fe fty')
      ((nm, tm) :) <$> goLit ((nm, tm) : doneV) ((nm, fty') : doneT) rest

-- | §13.2.11 existential introduction (Spec.md 13347-13364).
--
-- @seal e as exists (a1:S1)...(an:Sn). T@ where the operand is an
-- ordinary expression: create fresh witness metavariables for the
-- hidden witnesses, check the payload against @T@ with those metas
-- substituted for the witness 'this'-references, and solve the witnesses
-- from that checking problem. All witnesses must be solved before the
-- seal is accepted (Spec.md 13363-13364).
--
-- The signature fields are the internal witness labels (opaque) followed
-- by the payload view; a non-record payload is the single internal
-- @⟨payload⟩@ field, while a record-shaped payload exposes its source
-- labels. @witTerms@ supplies the witness terms positionally — fresh
-- metas for the direct form, or the explicitly supplied witnesses for
-- 'ESealExists' (Spec.md 13378-13391).
elabSeal'Exists :: Ctx -> Expr -> Value -> [Text] -> [(Text, Value)] -> [Text] -> Span -> CheckM (Term, Value)
elabSeal'Exists ctx e sV witLabels fs witBinderNames sp = do
  -- Witness fields are exactly the opaque members 'witLabels'; the
  -- payload label '⟨payload⟩' is internal but NOT opaque.
  let anonPayload = case payFs of
        [(payLbl, _)] -> payLbl == existsPayloadLabel
        _ -> False
  -- §13.2.11 compatibility full-surface-package spelling (13417-13428):
  -- when the ascription is a literal 'exists' and the operand is a record
  -- literal mentioning witness binder names, the witness-named fields
  -- supply the witnesses and the rest is the payload. Available only for
  -- record-shaped payloads (13431-13432).
  case e of
    ERecordLit items _
      | not (null witBinderNames)
      , let suppliedNames = [nameText n | RecItem _ n _ <- items]
      , any (`elem` witBinderNames) suppliedNames ->
          if anonPayload
            then do
              errAt sp "E_TYPE_EQUALITY_MISMATCH" (Just "kappa.type.mismatch")
                "the compatibility record-package spelling of 'seal' is not available for a non-record existential payload; use direct payload introduction or 'seal exists (...) . e as ...' (§13.2.11)"
              anyHole ctx
            else sealCompat items
    _ -> do
      -- direct payload introduction: fresh witness metas, solved by
      -- checking the payload (Spec.md 13352, 13359-13361)
      witTerms <- forM witFs $ \(lbl, _) -> (,) lbl <$> freshMeta
      elabSealExistsCore ctx e sV witLabels fs sp witTerms
  where
    witFs = filter ((`elem` witLabels) . fst) fs
    payFs = filter ((`notElem` witLabels) . fst) fs
    -- the record-literal compatibility spelling: bind witness-named
    -- fields as explicit witnesses (positionally, by binder order), then
    -- check the remaining payload fields
    sealCompat items = do
      let supplied = [(nameText n, fromMaybe (EVar n) me) | RecItem _ n me <- items]
          -- explicit witness assignments in binder order
          witWs =
            [ (Name bn sp, we)
            | (bn, _) <- zip witBinderNames witFs
            , Just we <- [lookup bn supplied]
            ]
          -- the payload sub-record (witness fields removed)
          payItems = [it | it@(RecItem _ n _) <- items, nameText n `notElem` witBinderNames]
      witTerms <- goCompatWits [] (zip witFs witWs)
      elabSealExistsCore ctx (ERecordLit payItems (exprSpan e)) sV witLabels fs sp witTerms
    goCompatWits _ [] = pure []
    goCompatWits done (((lbl, wty), (_, we)) : rest) = do
      let thisRecv = CRecordV (sortOn fst done)
      wty' <- substThisInto ctx thisRecv wty
      wt <- check ctx we wty'
      ((lbl, wt) :) <$> goCompatWits ((lbl, wt) : done) rest

-- | The shared core: with the witness terms already chosen (metas for
-- the direct form, supplied terms for the explicit-witness form), check
-- the payload, enforce that all witnesses are solved, and build the
-- sealed package value.
elabSealExistsCore ::
  Ctx -> Expr -> Value -> [Text] -> [(Text, Value)] -> Span -> [(Text, Term)] -> CheckM (Term, Value)
elabSealExistsCore ctx e sV witLabels fs sp witTerms = do
  let payFs = filter ((`notElem` witLabels) . fst) fs
      thisRecv = CRecordV (sortOn fst witTerms)
  payVals <- case payFs of
    -- one anonymous non-record payload: check e against its type with
    -- the witnesses substituted (Spec.md 13316-13317, 13360)
    [(payLbl, payTy)]
      | payLbl == existsPayloadLabel -> do
          payTy' <- substThisInto ctx thisRecv payTy
          eTm <- check ctx e payTy'
          pure [(payLbl, eTm)]
    -- record-shaped payload: e must provide each source-labeled field
    _ -> do
      (eTm0, eTy0) <- infer ctx e
      (eTm, eTy1) <- insertAllImplicits ctx (exprSpan e) eTm0 eTy0
      eTy <- forceM eTy1
      mefs <- case eTy of
        VRecordT efs -> pure (Just efs)
        VSigT _ inner ->
          forceM inner >>= \case
            VRecordT efs -> pure (Just efs)
            _ -> pure Nothing
        _ -> pure Nothing
      case mefs of
        Nothing -> do
          errAt (exprSpan e) "E_TYPE_EQUALITY_MISMATCH" (Just "kappa.type.mismatch")
            "the sealed expression does not have a record type matching the existential payload view (§13.2.11)"
          pure [(lbl, eTm) | (lbl, _) <- payFs]
        Just efs -> do
          forM_ payFs $ \(nm, fty) -> case lookup nm efs of
            Nothing ->
              errAt (exprSpan e) "E_TYPE_EQUALITY_MISMATCH" (Just "kappa.type.mismatch")
                ("the sealed expression does not provide the payload field '" <> nm <> "' (§13.2.11)")
            Just aty -> do
              aty' <- substThisInto ctx eTm aty
              fty' <- substThisInto ctx thisRecv fty
              expectType ctx (exprSpan e) aty' fty'
          pure [(nm, CProj eTm nm) | (nm, _) <- payFs]
  -- §13.2.11 13363-13364: every witness must be solved
  forM_ witTerms $ \(lbl, wt) -> case wt of
    CMeta m ->
      gets (Map.lookup m . csMetas) >>= \case
        Just (Just _) -> pure ()
        _ ->
          errAt sp "E_UNSOLVED_IMPLICIT" (Just "kappa.implicit.unsolved")
            ( "the existential witness "
                <> lbl
                <> " could not be inferred; use the explicit-witness 'seal exists (...) . e as ...' form or annotate the payload (§13.2.11)"
            )
    _ -> pure ()
  pure (CSealE witLabels (CRecordV (sortOn fst (witTerms ++ payVals))), sV)

-- | §13.2.11 explicit-witness introduction (Spec.md 13376-13415):
-- @seal exists (a1 = w1, ..., an = wn). e as exists (b1:S1)...(bn:Sn). T@.
-- The witness assignments are checked sequentially against the binder
-- telescope (positionally — witness labels are canonical and internal),
-- then the payload is checked with those witnesses supplied.
elabSealExistsExplicit :: Ctx -> [(Name, Expr)] -> Expr -> Expr -> Span -> CheckM (Term, Value)
elabSealExistsExplicit ctx ws e tyE sp = do
  (sTm, _) <- inferType ctx tyE
  sV <- forceM =<< evalIn ctx sTm
  case sV of
    VSigT ls inner
      | any isExistsInternalLabel ls ->
          forceM inner >>= \case
            VRecordT fs -> do
              let witFs = filter ((`elem` ls) . fst) fs
              when (length ws /= length witFs) $
                errAt sp "E_TYPE_EQUALITY_MISMATCH" (Just "kappa.type.mismatch")
                  ( "this explicit-witness 'seal' supplies "
                      <> T.pack (show (length ws))
                      <> " witness(es) but the existential type has "
                      <> T.pack (show (length witFs))
                      <> " (§13.2.11)"
                  )
              -- check each witness assignment against its (dependent)
              -- type, threading earlier witnesses through 'this'
              witTerms <- goWits [] (zip witFs ws)
              elabSealExistsCore ctx e sV ls fs sp witTerms
            _ -> notExists sV
    _ -> notExists sV
  where
    notExists sV = do
      _ <- pure sV
      errAt sp "E_TYPE_EQUALITY_MISMATCH" (Just "kappa.type.mismatch")
        "the ascribed type of 'seal exists (...) . e as ...' must be an existential type (§13.2.11)"
      anyHole ctx
    goWits _ [] = pure []
    goWits done (((lbl, wty), (_, we)) : rest) = do
      let thisRecv = CRecordV (sortOn fst done)
      wty' <- substThisInto ctx thisRecv wty
      wt <- check ctx we wty'
      ((lbl, wt) :) <$> goWits ((lbl, wt) : done) rest

-- | §13.2.11 existential elimination (Spec.md 13469-13540):
-- @open e as exists (a1, ..., an). pat in body@. The witnesses are
-- introduced as rigid quantity-0 locals bound to the (opaque) witness
-- selections of the package; the payload view is bound by @pat@; @body@
-- is elaborated in that extended scope; the opened witnesses must not
-- escape the inferred result type.
--
-- Following the normative schematic elaboration (Spec.md 13528-13536),
-- we emit @let 0 a_i = pkg.⟨wit_i⟩@ for each witness and a single
-- irrefutable @match@ binding the payload pattern.
elabOpenExists :: Ctx -> Expr -> [Name] -> Pattern -> Expr -> Span -> CheckM (Term, Value)
elabOpenExists ctx e ns pat body sp = do
  (eTm, eTy) <- infer ctx e
  eTyF <- forceM eTy
  case eTyF of
    VSigT ls inner
      | any isExistsInternalLabel ls ->
          forceM inner >>= \case
            VRecordT fs -> openWith eTm eTyF ls fs
            _ -> notExists
    _ -> notExists
  where
    notExists = do
      errAt (exprSpan e) "E_TYPE_EQUALITY_MISMATCH" (Just "kappa.type.mismatch")
        "the operand of 'open ... as exists ...' must have an existential type (§13.2.11)"
      anyHole ctx
    openWith eTm pkgTy ls fs = do
      let witFs = filter ((`elem` ls) . fst) fs
          payFs = filter ((`notElem` ls) . fst) fs
          names = map nameText ns
          nWit = length witFs
      when (length ns /= nWit) $
        errAt sp "E_TYPE_EQUALITY_MISMATCH" (Just "kappa.type.mismatch")
          ( "this 'open' binds "
              <> T.pack (show (length ns))
              <> " witness(es) but the existential type has "
              <> T.pack (show nWit)
              <> " (§13.2.11)"
          )
      forM_ (duplicatesOf (filter (/= "_") names)) $ \n ->
        errAt sp "E_RECORD_DUPLICATE_FIELD" (Just "kappa-hs.record.duplicate-field")
          ("'open ... as exists' binds the witness name '" <> n <> "' more than once (§13.2.11)")
      -- Schematic elaboration (Spec.md 13528-13536): bind the package as
      -- an outer let so all witness/payload selections refer to it by a
      -- properly-shifting de Bruijn variable, then bind each opened
      -- witness as a quantity-0 local and the payload via 'pat'.
      let ctxP = bindCtx "__pkg" False pkgTy ctx
          pkgLvl = ctxLen ctx -- de Bruijn LEVEL of __pkg
          pkgAt c = CVar (ctxLen c - 1 - pkgLvl)
      -- bind each opened witness as a rigid quantity-0 local; record its
      -- de Bruijn level so we can later detect escape in the result type
      (ctxW, witAccRev) <- foldM (bindWit pkgAt) (ctxP, []) (zip names witFs)
      let witAcc = reverse witAccRev -- (level, typeTerm) per witness, oldest-first
          witLvls = map fst witAcc
      -- the payload view (Spec.md 13535)
      (payTm, payTy) <- case payFs of
        [(payLbl, payTy)]
          | payLbl == existsPayloadLabel -> do
              payTy' <- substThisInto ctxW (pkgAt ctxW) payTy
              pure (CProj (pkgAt ctxW) payLbl, payTy')
        _ -> do
          payT' <- substThisInto ctxW (pkgAt ctxW) (VRecordT (sortOn fst payFs))
          pure (CRecordV (sortOn fst [(nm, CProj (pkgAt ctxW) nm) | (nm, _) <- payFs]), payT')
      (patC, ctx2, _) <- elabPattern ctxW pat payTy
      checkIrrefutable ctxW pat payTy sp
      (bodyTm, bodyTy) <- infer ctx2 body
      -- §13.2.11 13517-13524: opened witnesses must not escape the result
      bodyTyTm <- quoteIn ctx2 bodyTy
      let n2 = ctxLen ctx2
          escaping = [nm | (nm, lvl) <- zip names witLvls, nm /= "_", varUsedAt (n2 - 1 - lvl) bodyTyTm]
      forM_ escaping $ \nm ->
        errAt sp "E_EXISTENTIAL_WITNESS_ESCAPE" (Just "kappa-hs.exists.escape")
          ("the opened existential witness '" <> nm <> "' escapes in the result type of 'open' (§13.2.11)")
      -- assemble: let __pkg = e in (let 0 a_i = __pkg.<wit_i>)* in
      --           (match payload case pat -> body). At witness-let i's
      --           rhs position, __pkg is i binders up (index i).
      pkgTyTm <- quoteIn ctx pkgTy
      let payMatch = CMatch payTm [CaseAlt patC Nothing bodyTm]
          witLets =
            foldr
              (\(i, (nm, (lbl, _)), wtyTm) b -> CLet Q0 nm wtyTm (CProj (CVar i) lbl) b)
              payMatch
              (zip3 [0 ..] (zip names witFs) (map snd witAcc))
          whole = CLet QW "__pkg" pkgTyTm eTm witLets
      pure (whole, bodyTy)
    -- bind one opened witness as a quantity-0 local; returns the extended
    -- context and the witness's (de Bruijn LEVEL, quoted type term)
    bindWit pkgAt (c, acc) (nm, (_lbl, wty)) = do
      wty' <- substThisInto c (pkgAt c) wty
      wtyTm <- quoteIn c wty'
      let lvl = ctxLen c
          c' = bindCtx nm False wty' c
      pure (c', (lvl, wtyTm) : acc)

-- | Whether the de Bruijn /index/ @ix@ (relative to the term's top
-- scope) is referenced by any @CVar@ in the term, incrementing the
-- target under each binder. Used by 'elabOpenExists' to detect witness
-- escape in the inferred result type.
varUsedAt :: Int -> Term -> Bool
varUsedAt = go
  where
    go ix = \case
      CVar i -> i == ix
      CLam _ _ _ b -> go (ix + 1) b
      CPi _ _ _ a b -> go ix a || go (ix + 1) b
      CApp _ f a -> go ix f || go ix a
      CCtor _ as -> any (go ix) as
      CMatch s alts -> go ix s || or [maybe False (go (ix + patBindersC p)) g || go (ix + patBindersC p) b | CaseAlt p g b <- alts]
      CRecordT fs -> any (go ix . snd) fs
      CRecordV fs -> any (go ix . snd) fs
      CProj x _ -> go ix x
      CProjAt x _ _ -> go ix x
      CVariantT ms -> any (go ix) ms
      CInject _ x -> go ix x
      CLet _ _ a b c -> go ix a || go ix b || go (ix + 1) c
      CLetRec _ _ a b c -> go ix a || go (ix + 1) b || go (ix + 1) c
      CSealE _ x -> go ix x
      CSigT _ x -> go ix x
      CThunkE x -> go ix x
      CLazyE x -> go ix x
      CForceE x -> go ix x
      CIf a b c -> go ix a || go ix b || go ix c
      CQuote _ slots -> any (go ix) slots
      CGlob _ -> False
      CSort _ -> False
      CLit _ -> False
      CMeta _ -> False
      CDo _ _ -> False

-- | A record literal against a §13.2.1 dependent record type (or one
-- whose initializers use sibling references): fields elaborate in
-- dependency order; each initializer sees the earlier siblings as
-- 'this' and checks against its field type with 'this' substituted.
elabDependentRecordLit :: Ctx -> [RecItem] -> [(Text, Value)] -> Span -> CheckM (Term, Value)
elabDependentRecordLit ctx items fs sp = do
  let supplied = [(nameText n, fromMaybe (EVar n) me) | RecItem _ n me <- items]
  forM_ (duplicatesOf (map fst supplied)) $ \n ->
    errAt sp "E_RECORD_DUPLICATE_FIELD" (Just "kappa-hs.record.duplicate-field")
      ("record literal has duplicate field '" <> n <> "'")
  if sort (map fst supplied) /= map fst fs
    then do
      errAt sp "E_TYPE_EQUALITY_MISMATCH" (Just "kappa.type.mismatch")
        ( "record literal fields do not match the expected record type (expected: "
            <> T.intercalate ", " (map fst fs) <> ")"
        )
      pure (CRecordV [], VRecordT fs)
    else do
      annotated <- forM fs $ \(nm, fty) -> do
        ftyTm <- quoteIn ctx fty
        let e = fromMaybe (EVar (Name nm sp)) (lookup nm supplied)
            deps =
              nub (thisDepsOf ftyTm ++ [l | l <- surfaceThisRefs e, l `elem` map fst fs])
        pure (nm, deps, (nm, fty, e))
      case topoFields annotated of
        Nothing -> do
          errAt sp "E_RECORD_DEPENDENCY_CYCLE" (Just "kappa-hs.record.dependency-cycle")
            "the sibling references of this record literal form a cycle (§13.2.1)"
          anyHole ctx
        Just ordered -> do
          allFields <- goLit [] [] ordered
          pure (CRecordV (sortOn fst allFields), VRecordT fs)
  where
    goLit _ _ [] = pure []
    goLit doneV doneT ((nm, fty, e) : rest) = do
      fty' <- substThisInto ctx (CRecordV (sortOn fst doneV)) fty
      tm <- withThis (Just (ThisValue doneV doneT)) (check ctx e fty')
      ((nm, tm) :) <$> goLit ((nm, tm) : doneV) ((nm, fty') : doneT) rest

-- | A record update on a §13.2.1 dependent record: updated fields check
-- against their field types with 'this' bound to the evolving record;
-- a non-updated field whose type depends on an updated field must still
-- be well-typed after the update (else it needed repair).
elabDependentPatch :: Ctx -> Term -> [(Text, Value)] -> [PatchItem] -> Span -> CheckM (Term, Value)
elabDependentPatch ctx baseTm fs items sp = do
  ups <- fmap catMaybes . forM items $ \case
    PatchUpdate [(_, n)] (PatchValue v)
      | nameText n `elem` map fst fs -> pure (Just (nameText n, v))
      | otherwise -> do
          errAt (nameSpan n) "E_UNKNOWN_FIELD" (Just "kappa.name.unresolved")
            ("record has no field '" <> nameText n <> "'")
          pure Nothing
    it -> do
      unsupportedAt (patchItemSpan it sp)
        "this update form is not supported on a dependent record"
      pure Nothing
  forM_ (duplicatesOf (map fst ups)) $ \n ->
    errAt sp "E_RECORD_PATCH_DUPLICATE_PATH" (Just "kappa-hs.record.patch-duplicate")
      ("record patch updates field '" <> n <> "' more than once (§13.2.5)")
  annotated <- forM fs $ \(nm, fty) -> do
    ftyTm <- quoteIn ctx fty
    pure (nm, thisDepsOf ftyTm, (nm, fty, thisDepsOf ftyTm))
  case topoFields annotated of
    Nothing -> do
      errAt sp "E_RECORD_DEPENDENCY_CYCLE" (Just "kappa-hs.record.dependency-cycle")
        "the field-dependency graph of this record type contains a cycle (§13.2.1)"
      anyHole ctx
    Just ordered -> do
      allFields <- goUp ups [] [] ordered
      -- staleness (§13.2.5): a kept field whose type mentions an
      -- updated sibling keeps its old value of the OLD instantiation
      let newRec = CRecordV (sortOn fst allFields)
      forM_ ordered $ \(nm, fty, deps) ->
        when (nm `notElem` map fst ups && not (null (deps `intersect` map fst ups))) $ do
          oldTy <- substThisInto ctx baseTm fty
          newTy <- substThisInto ctx newRec fty
          ok <- unify ctx oldTy newTy
          unless ok $
            errAt sp "E_TYPE_EQUALITY_MISMATCH" (Just "kappa.type.mismatch")
              ( "the dependent field '" <> nm
                  <> "' is stale after this update; it must be repaired in the same update (§13.2.5)"
              )
      pure (newRec, VRecordT fs)
  where
    goUp _ _ _ [] = pure []
    goUp ups doneV doneT ((nm, fty, _) : rest) = do
      fty' <- substThisInto ctx (CRecordV (sortOn fst doneV)) fty
      tm <- case lookup nm ups of
        Just v -> withThis (Just (ThisValue doneV doneT)) (check ctx v fty')
        Nothing -> pure (CProj baseTm nm)
      ((nm, tm) :) <$> goUp ups ((nm, tm) : doneV) ((nm, fty') : doneT) rest
    patchItemSpan it dflt = case it of
      PatchUpdate ((_, n) : _) _ -> nameSpan n
      PatchExtend n _ -> nameSpan n
      _ -> dflt

-- ── Variants ─────────────────────────────────────────────────────────

elabVariant :: Ctx -> [VariantArm] -> Maybe Expr -> Span -> Maybe Value -> CheckM (Term, Value)
elabVariant ctx arms mtail sp mexpected = do
  when (isJust mtail) . void $ unsupported ctx sp "open variant rows"
  expected <- traverse forceM mexpected
  case (arms, expected) of
    -- single arm in term position: injection
    ([VariantArm payload mty], Just (VVariantT members)) -> do
      (tm, ty) <- case mty of
        Just tyE -> do
          (tyTm, _) <- inferType ctx tyE
          tyV <- evalIn ctx tyTm
          (,tyV) <$> check ctx payload tyV
        Nothing -> infer ctx payload
      tm2 <- injectInto ctx tm ty members (VVariantT members) sp
      pure (tm2, VVariantT members)
    -- §13.1.3: a single non-type arm with no expected union type is
    -- an injection the term grammar does not admit standalone
    ([VariantArm payload Nothing], Nothing) -> do
      st0 <- get
      n0 <- gets (length . csDiags)
      r <- inferType ctx payload
      n1 <- gets (length . csDiags)
      if n1 == n0
        then pure (CVariantT [fst r], VSort 0)
        else do
          put st0
          errAt sp "E_EXPECTED_SYNTAX_TOKEN" (Just "kappa-hs.parse.error")
            "a union injection (| e |) is admitted only against an expected union type (§13.1.3)"
          anyHole ctx
    _ -> do
      -- type formation: every arm is a type
      memberTms <- forM arms $ \(VariantArm e mty) -> do
        when (isJust mty) $
          errAt sp "E_VARIANT_ARM" Nothing "variant type arms do not take ascriptions"
        fst <$> inferType ctx e
      memberVs <- mapM (evalIn ctx) memberTms
      tags <- mapM (tagOf ctx) memberVs
      let canon = map snd (sortOn fst (zip tags memberTms))
      when (length (nub tags) /= length tags) $
        errAt sp "E_VARIANT_DUPLICATE" (Just "kappa-hs.variant.duplicate-member")
          "duplicate variant member types"
      pure (CVariantT canon, VSort 0)

-- ── Lambdas, lets, blocks ────────────────────────────────────────────

elabLambda :: Ctx -> [Binder] -> Expr -> Span -> Maybe Value -> CheckM (Term, Value)
elabLambda ctx0 bs0 body sp mexpected =
  -- the lambda is a closure boundary: borrowed implicit locals from
  -- the surrounding scope may not be captured into it (§16.3.3)
  go (pushCtxBarrier ctx0) bs0 mexpected
  where
    -- §18.5.1: the lambda body do IS the labeled lambda's completion
    -- boundary, so elaborate an EDo body directly with ctxReturnTarget
    -- preserved (the generic EDo path resets it as a nested do).
    go ctx [] mexp = case (body, mexp) of
      (EDo mlbl items isp, Just t) -> do
        (tm, ty') <- elabDo ctx mlbl items isp (Just t)
        expectType ctx isp ty' t
        pure (tm, t)
      (EDo mlbl items isp, Nothing) -> do
        (tm, ty) <- elabDo ctx mlbl items isp Nothing
        insertAllImplicits ctx (exprSpan body) tm ty
      (_, Just t) -> do
        tm <- check ctx body t
        pure (tm, t)
      (_, Nothing) -> do
        (tm, ty) <- infer ctx body
        insertAllImplicits ctx (exprSpan body) tm ty
    go ctx (b : rest) mexp = do
      mexp' <- traverse forceM mexp
      case mexp' of
        Just expectedPi@(VPi ic q nm dom clo)
          | ic == (if bImplicit b then Impl else Expl) -> do
              -- check declared annotation against expected domain
              forM_ (binderTypeExpr b) $ \tyE -> do
                (tyTm, _) <- inferType ctx tyE
                tyV <- evalIn ctx tyTm
                expectType ctx (bSpan b) dom tyV
              let bn = binderName b nm
                  ctx' = bindCtx bn (bImplicit b) dom ctx
              cod <- clApp clo (VRigid (ctxLen ctx) [])
              (inner, _) <- go ctx' rest (Just cod)
              pure (CLam ic q bn inner, expectedPi)
        _ -> do
          domV <- case binderTypeExpr b of
            Just tyE -> do
              (tyTm, _) <- inferType ctx tyE
              evalIn ctx tyTm
            Nothing
              | bUnitBinder b -> pure (VGlobN (gPrel "Unit") [])
              | otherwise -> freshMetaV ctx
          let bn = binderName b "_"
              ic = if bImplicit b then Impl else Expl
              q = binderQ b
              ctx' = bindCtx bn (bImplicit b) domV ctx
          (inner, innerTy) <- go ctx' rest Nothing
          domTm <- quoteIn ctx domV
          innerTyTm <- quoteIn ctx' innerTy
          piV <- evalIn ctx (CPi ic q bn domTm innerTyTm)
          case mexp' of
            Just t -> expectType ctx sp piV t
            Nothing -> pure ()
          pure (CLam ic q bn inner, piV)

    binderName b dflt = maybe (if bUnitBinder b then "_" else dflt) nameText (bName b)

elabLet :: Ctx -> [LetBind] -> Expr -> Maybe Value -> CheckM (Term, Value)
elabLet ctx0 binds body mexpected = go ctx0 binds []
  where
    mkLet (q, n, tyT, rhs, isRec) b
      | isRec = CLetRec q n tyT rhs b
      | otherwise = CLet q n tyT rhs b
    go ctx [] acc = do
      (bodyTm, bodyTy) <- case mexpected of
        Just t -> (,t) <$> check ctx body t
        Nothing -> do
          -- trailing implicits resolve against the let-local implicit
          -- context, not the caller's (§16.3.3)
          (tm, ty) <- infer ctx body
          insertAllImplicits ctx (exprSpan body) tm ty
      pure (foldl' (flip mkLet) bodyTm acc, bodyTy)
    -- an annotated local function may refer to itself (§9.2 mirrored
    -- locally): elaborate the lambda under its own binder
    go ctx (LetBind implocal prefix (PVar n) (Just tyE) rhs@ELambda {} sp : rest) acc = do
      (tyTm, _) <- inferType ctx tyE
      tyV <- evalIn ctx tyTm
      let q = qOf (bpQuantity prefix)
          ctxRec = bindCtx (nameText n) implocal tyV ctx
      tm <- check ctxRec rhs tyV
      _ <- pure sp
      go ctxRec rest ((q, nameText n, tyTm, tm, True) : acc)
    go ctx (LetBind implocal prefix pat0 mty rhs sp : rest) acc = do
      -- §9.1.2: a let pattern that is a bare capitalized name not naming
      -- any constructor in scope is an ordinary (rebinding) binder,
      -- e.g. `let M = type MaybeBox` (§2.8.3)
      pat <- do
        st <- get
        let isCtor n = any (\g -> gnameText g == nameText n) (Map.keys (csCtors st))
            -- applies recursively inside tuple/record let patterns:
            -- `let (F = G, value = v) = pkg` rebinds the type object
            -- under G (§2.8.4)
            normRebind p = case p of
              PCtor (CtorRef Nothing n) [] _
                | not (isCtor n) -> PVar n
              PTuple ps tsp -> PTuple (map normRebind ps) tsp
              PRecord items mr rsp ->
                PRecord [(o, f, fmap normRebind mp) | (o, f, mp) <- items] mr rsp
              _ -> p
        pure (normRebind pat0)
      (rhsTm, rhsTy) <- case mty of
        Just tyE -> do
          (tyTm, _) <- inferType ctx tyE
          tyV <- evalIn ctx tyTm
          tm <- check ctx rhs tyV
          pure (tm, tyV)
        Nothing -> do
          (tm, ty) <- infer ctx rhs
          insertAllImplicits ctx sp tm ty
      case pat of
        PVar n -> do
          rhsTyTm <- quoteIn ctx rhsTy
          rhsV <- evalIn ctx rhsTm
          let q = qOf (bpQuantity prefix)
              ctx0' = bindCtxLet (nameText n) implocal rhsTy rhsV ctx
              ctx1 = if implocal then setTopPrefix sp prefix ctx0' else ctx0'
              -- §7.4.3 stable alias: `let q = p` transports refinement
              ctx' = case rhs of
                EVar pn | Just _ <- lookupCtx (nameText pn) ctx ->
                  addCtxAlias (nameText n) (nameText pn) ctx1
                _ -> ctx1
          go ctx' rest ((q, nameText n, rhsTyTm, rhsTm, False) : acc)
        PWild _ -> do
          rhsTyTm <- quoteIn ctx rhsTy
          rhsV <- evalIn ctx rhsTm
          let ctx' = bindCtxLet "_" False rhsTy rhsV ctx
          go ctx' rest ((QW, "_", rhsTyTm, rhsTm, False) : acc)
        _ -> do
          rhsTyF <- forceM rhsTy
          let mProj = case (pat, rhsTyF) of
                -- a variables-only tuple/record pattern over a closed
                -- record type destructures by projection, so the
                -- binding normalizes for definitional equality (§31.1)
                (PTuple ps _, VRecordT fs)
                  | Just ns <- mapM patVarName ps
                  , length ns == length fs ->
                      Just (zip ns (map fst fs), fs)
                (PRecord items Nothing _, VRecordT fs)
                  | Just ns <- mapM recItemVar items
                  , sort (map fst ns) == map fst fs ->
                      Just ([(fromMaybe Nothing (lookup f ns), f) | (f, _) <- fs], fs)
                _ -> Nothing
          case mProj of
            Just (named, fs) -> do
              rhsTyTm <- quoteIn ctx rhsTy
              rhsV <- evalIn ctx rhsTm
              let q = qOf (bpQuantity prefix)
                  scrutN = "__scrut"
                  ctxS = bindCtxLet scrutN False rhsTy rhsV ctx
              let bindFields c _ [] = pure (c, [])
                  bindFields c i ((mn, f) : restFs) = do
                    let projTm = CProj (CVar i) f
                    projV <- evalIn c projTm
                    fldTy <- case lookup f fs of
                      Just t -> substThisInto c (CVar i) t
                      Nothing -> freshMetaV c
                    fldTyTm <- quoteIn c fldTy
                    let nm = maybe "_" nameText mn
                        c' = bindCtxLet nm False fldTy projV c
                    (cFin, more) <- bindFields c' (i + 1) restFs
                    pure (cFin, (nm, fldTyTm, projTm) : more)
              (ctxFin, projBinds) <- bindFields ctxS 0 named
              (bodyTm, bodyTy) <- goUnder ctxFin rest
              checkIrrefutable ctx pat rhsTy sp
              let inner = foldr (\(nm, tyT, tm) b -> CLet q nm tyT tm b) bodyTm projBinds
                  whole = CLet q scrutN rhsTyTm rhsTm inner
              pure (foldl' (flip mkLet) whole acc, bodyTy)
            Nothing -> do
              -- irrefutable destructuring: elaborate as single-case
              -- match by rewriting `let pat = rhs; rest` to
              -- `match rhs case pat -> ...`
              (patC, ctx', _) <- elabPattern ctx pat rhsTy
              (bodyTm, bodyTy) <- goUnder ctx' rest
              checkIrrefutable ctx pat rhsTy sp
              let matchTm = CMatch rhsTm [CaseAlt patC Nothing bodyTm]
              pure (foldl' (flip mkLet) matchTm acc, bodyTy)
      where
        patVarName = \case
          PVar n -> Just (Just n)
          PWild _ -> Just Nothing
          _ -> Nothing
        recItemVar (False, f, mp) = case mp of
          Nothing -> Just (nameText f, Just f)
          Just (PVar n) -> Just (nameText f, Just n)
          Just (PWild _) -> Just (nameText f, Nothing)
          _ -> Nothing
        recItemVar _ = Nothing
        goUnder c rs = case rs of
          [] -> case mexpected of
            Just t -> (,t) <$> check c body t
            Nothing -> infer c body
          _ -> elabLet c rs body mexpected
elabBlock :: Ctx -> [Decl] -> Maybe Expr -> Span -> CheckM (Term, Value)
elabBlock ctx0 ds0 mfin sp = do
  -- §9.3.1.1 scoped effect declarations are elaborated first (their
  -- operation signatures are closed over the block in v1), each
  -- contributing a transparent local binding of its interface type
  (ctx, wrap, ds) <- hoistScopedEffects ctx0 ds0
  -- v1: block-local declarations support signatures and lets; other
  -- local declaration forms are reported.
  binds <- goDecls [] ds
  case mfin of
    Nothing -> do
      errAt sp "E_BLOCK_NO_RESULT" Nothing "a pure block must end with an expression (§9.3.1)"
      anyHole ctx
    Just fin -> do
      (tm, ty) <- elabLet ctx binds fin Nothing
      pure (wrap tm, ty)
  where
    goDecls _ [] = pure []
    goDecls sigs (d : rest) = case d of
      -- a local signature annotates the following definition (§9.3.1)
      DSig _ n tyE _ -> goDecls ((nameText n, tyE) : sigs) rest
      DLet _ (LetDef (Just n) _ Nothing _ [] mty Nothing rhs) _ ->
        (LetBind False emptyPrefix (PVar n) (annOf n mty sigs) rhs sp :) <$> goDecls sigs rest
      DLet _ (LetDef (Just n) _ Nothing _ bs mty _ rhs) dsp -> do
        -- local named function: elaborate as lambda
        let lam = ELambda Nothing bs (maybe rhs (\t -> EAscription rhs t dsp) mty) dsp
        (LetBind False emptyPrefix (PVar n) (lookup (nameText n) sigs) lam sp :) <$> goDecls sigs rest
      DLet _ (LetDef Nothing imp (Just p) prefix [] mty Nothing rhs) _ ->
        (LetBind imp prefix p mty rhs sp :) <$> goDecls sigs rest
      -- a local type alias is a type-level let binding (§9.3.1, §10.2)
      DTypeAlias _ n params _ (Just rhs) dsp ->
        let (body, ann) = case params of
              [] -> (rhs, Just (EVar (Name "Type" dsp)))
              bs -> (ELambda Nothing bs rhs dsp, Nothing)
         in (LetBind False emptyPrefix (PVar n) ann body sp :) <$> goDecls sigs rest
      _ -> do
        unsupportedAt (declSpan d)
          "this local declaration form is not supported inside block by this implementation"
        goDecls sigs rest
    annOf n mty sigs = case mty of
      Just t -> Just t
      Nothing -> lookup (nameText n) sigs

-- ── Algebraic effects (§9.3.1.1, §18.1.14–§18.1.22) ──────────────────
--
-- Runtime model (realized by 'Kappa.Eval.evalEffPrim'): an @Eff r a@
-- value is a tree — @__EffPure v@, or @__EffOp label op payload cont@
-- with @cont@ the captured continuation from the operation site
-- (§30.2.2.7 OpCall). Handlers elaborate to @__handleEff@ applications;
-- the continuation is an ordinary closure, so resumption is naturally
-- re-entrant (one-shot/multi-shot discipline is enforced statically by
-- 'Kappa.Usage').

-- | Elaborate the @scoped effect@ declarations of a block: mint the
-- interface-type and label identities, record operation metadata in the
-- context, and produce a wrapper that let-binds the interface name.
hoistScopedEffects :: Ctx -> [Decl] -> CheckM (Ctx, Term -> Term, [Decl])
hoistScopedEffects ctx0 ds0 = go ctx0 id ds0
  where
    go ctx wrap [] = pure (ctx, wrap, [])
    go ctx wrap (DEffect mods eff dsp : rest)
      | dmScoped mods && not (effIsLabelDecl eff) = do
          (ctx', wrap') <- elabScopedEffect ctx eff dsp
          go ctx' (wrap . wrap') rest
      | dmScoped mods && effIsLabelDecl eff = do
          ctx' <- elabScopedEffectLabel ctx eff dsp
          go ctx' wrap rest
    go ctx wrap (d : rest) = do
      (ctx', wrap', rest') <- go ctx wrap rest
      pure (ctx', wrap', d : rest')

-- | §9.3.1.1/§18.1.15: a local @scoped effect l : E@ introduces a fresh
-- effect label @l@ for the lexical scope that shares the operations and
-- interface of an effect @E@ already in scope (scoped or top-level).
elabScopedEffectLabel :: Ctx -> EffectDecl -> Span -> CheckM Ctx
elabScopedEffectLabel ctx eff dsp = do
  let lblName = nameText (effName eff)
  case effLabelType eff of
    Just (EVar en) -> do
      mbase <- lookupEffLabelM ctx (nameText en)
      case mbase of
        Nothing -> do
          errAt (nameSpan en) "E_NAME_UNRESOLVED" (Just "kappa.name.unresolved")
            ("scoped effect label '" <> lblName <> "' references unknown effect '"
               <> nameText en <> "' (§18.1.15)")
          pure ctx
        Just base -> do
          st0 <- get
          suffix <- freshNameM "#efflbl"
          let labelG = GName (csModule st0) (lblName <> suffix <> ".label")
          addGlobal labelG (GlobalDef (VGlobN (gPrel "EffLabel") []) Nothing False)
          recordCoreBody labelG (CLit (LitStr (effLabelKey labelG)))
          pure ctx {ctxEffLabels = Map.insert lblName (base {eliLabel = labelG}) (ctxEffLabels ctx)}
    _ -> do
      errAt dsp "E_EFFECT_LABEL_FORM" (Just "kappa-hs.effect.label")
        ("'scoped effect " <> lblName <> " : E' requires E to be a named effect in scope (§18.1.15)")
      pure ctx

-- | §18.1.15 effect type parameters (e.g. @effect State (s : Type)@): bind
-- each parameter as a local in @ctx@ (so later parameters and the operation
-- signatures may reference earlier ones) and collect the @(name, kind)@ pairs,
-- each kind being de Bruijn under the preceding parameters.
elabEffParams :: Ctx -> [Binder] -> CheckM (Ctx, [(Text, Term)])
elabEffParams ctx [] = pure (ctx, [])
elabEffParams ctx (b : bs) = do
  let nm = maybe "_" nameText (bName b)
  kT <- case binderTypeExpr b of
    Just e -> fst <$> inferType ctx e
    Nothing -> pure (CSort 0)
  kV <- evalIn ctx kT
  (ctxF, rest) <- elabEffParams (bindCtx nm False kV ctx) bs
  pure (ctxF, (nm, kT) : rest)

-- | Elaborate an effect interface's parameters and operations (§18.1.15),
-- shared by the top-level and scoped forms. Returns the parameter binders, the
-- interface kind term (@k0 -> … -> Type@, just @Type@ when unparameterized),
-- and the operation metadata (each operation's payload/result type quoted
-- under the parameter binders).
elabEffInterface :: Ctx -> EffectDecl -> CheckM ([(Text, Term)], Term, [EffOpInfo])
elabEffInterface ctx eff = do
  (ctxP, params) <- elabEffParams ctx (effParams eff)
  let ifaceKindTm = foldr (\(nm, kT) acc -> CPi Expl Q0 nm kT acc) (CSort 0) params
  ops <- fmap catMaybes . forM (effOps eff) $ \op -> do
    (tyTm, _) <- inferType ctxP (eoType op)
    tyV <- evalIn ctxP tyTm >>= forceM
    -- §18.1.15/§18.1.21: an operation signature is, after elaborating outer
    -- foralls, @forall (impl…). Π(x₁:A₁)…(xₙ:Aₙ). B@. Peel the leading IMPLICIT
    -- binders as the operation's own implicit parameters (bound in the local
    -- context so the argument/result types may reference them), then every
    -- explicit Pi as an argument, leaving @B@ as the final codomain.
    let peelImpl ctxC accI t = case t of
          VPi Impl _ inm dom clo -> do
            kT <- quoteIn ctxC dom
            let ctxC' = bindCtx inm False dom ctxC
            res <- clApp clo (VRigid (ctxLen ctxC) []) >>= forceM
            peelImpl ctxC' (accI ++ [(inm, kT)]) res
          _ -> pure (ctxC, accI, t)
        peelArgs ctxC accA t = case t of
          VPi Expl _ _ dom clo -> do
            argT <- quoteIn ctxC dom
            res <- clApp clo (VRigid (ctxLen ctxC) []) >>= forceM
            peelArgs ctxC (accA ++ [argT]) res
          _ -> do
            resT <- quoteIn ctxC t
            pure (accA, resT)
    (ctxI, implicits, afterImpl) <- peelImpl ctxP [] tyV
    (argsT, resT) <- peelArgs ctxI [] afterImpl
    if null argsT
      then do
        errAt (eoSpan op) "E_EFFECT_OP_SIGNATURE" (Just "kappa-hs.effect.operation")
          "an effect operation signature must elaborate to a function type (§18.1.15)"
        pure Nothing
      else
        pure
          ( Just
              EffOpInfo
                { eoiName = nameText (eoName op)
                , eoiQ = maybe Q1 (qOf . Just) (eoQuantity op) -- §18.1.17 one-shot default
                , eoiImplicits = implicits
                , eoiArgsT = argsT
                , eoiResT = resT
                }
          )
  pure (params, ifaceKindTm, ops)

elabScopedEffect :: Ctx -> EffectDecl -> Span -> CheckM (Ctx, Term -> Term)
elabScopedEffect ctx eff _dsp = do
  let nm = nameText (effName eff)
  st0 <- get
  suffix <- freshNameM "#eff"
  let ifaceG = GName (csModule st0) (nm <> suffix)
      labelG = GName (csModule st0) (nm <> suffix <> ".label")
  (params, ifaceKindTm, ops) <- elabEffInterface ctx eff
  ifaceKindV <- evalIn ctx ifaceKindTm
  -- the interface is a (possibly parameterized) local type constructor; the
  -- label is an opaque value of type EffLabel whose identity is its global
  -- name (§18.1.18 handler matching is by label identity)
  addGlobal ifaceG (GlobalDef ifaceKindV Nothing False)
  addGlobal labelG (GlobalDef (VGlobN (gPrel "EffLabel") []) Nothing False)
  -- §18.1.18: native string-token identity for the label (see elabTopEffect).
  recordCoreBody labelG (CLit (LitStr (effLabelKey labelG)))
  let info = EffLabelInfo {eliLabel = labelG, eliIface = ifaceG, eliParams = params, eliOps = ops}
      ctx' =
        (bindCtxLet nm False ifaceKindV (VGlobN ifaceG []) ctx)
          { ctxEffLabels = Map.insert nm info (ctxEffLabels ctx)
          }
      wrap = CLet QW nm ifaceKindTm (CGlob ifaceG)
  pure (ctx', wrap)

-- | Effect-label resolution (§18.1): a §9.3.1.1 lexically scoped effect in
-- 'ctxEffLabels' wins; otherwise a module-level (top-level) @effect@
-- declaration in 'csModEffLabels' is visible everywhere in the module.
-- | §18.1.18: the unique runtime identity string of an effect label (its
-- fully-qualified global name), used as the native label token.
effLabelKey :: GName -> Text
effLabelKey (GName (ModuleName segs) nm) = T.intercalate "." (segs ++ [nm])

lookupEffLabelM :: Ctx -> Text -> CheckM (Maybe EffLabelInfo)
lookupEffLabelM ctx nm = case Map.lookup nm (ctxEffLabels ctx) of
  Just e -> pure (Just e)
  Nothing -> gets (Map.lookup nm . csModEffLabels)

-- | The scoped (§9.3.1.1) and top-level (§18.1) effect labels visible here,
-- merged (scoped wins), for use in pure pattern guards.
effMerged :: Ctx -> CheckM (Map Text EffLabelInfo)
effMerged ctx = gets (\st -> Map.union (ctxEffLabels ctx) (csModEffLabels st))

-- | §18.1: elaborate a TOP-LEVEL @effect@ declaration. Like a scoped effect
-- it mints an opaque interface type + label value and computes the operation
-- signatures, but it registers them as module globals and records the
-- interface in 'csModEffLabels' (visible module-wide) and the type name in
-- the import scope, rather than as a lexically scoped local.
elabTopEffect :: EffectDecl -> Span -> CheckM ()
elabTopEffect eff _dsp = do
  let nm = nameText (effName eff)
  already <- gets (Map.member nm . csModEffLabels)
  unless already $ do
    st0 <- get
    let ifaceG = GName (csModule st0) nm
        labelG = GName (csModule st0) (nm <> ".label")
    (params, ifaceKindTm, ops) <- elabEffInterface emptyCtx eff
    ifaceKindV <- evalIn emptyCtx ifaceKindTm
    addGlobal ifaceG (GlobalDef ifaceKindV Nothing False)
    addGlobal labelG (GlobalDef (VGlobN (gPrel "EffLabel") []) Nothing False)
    -- §18.1.18: the label's runtime identity is its (unique) global name.
    -- The interpreter uses the neutral global; the native backend has no
    -- neutral globals, so record a string-token core body for it (label
    -- equality in the native effect runtime is string equality).
    recordCoreBody labelG (CLit (LitStr (effLabelKey labelG)))
    -- the effect type name resolves module-wide as its interface (type
    -- constructor when parameterized, §18.1.15)
    modify' $ \st -> st {csScope = Map.insert nm ifaceG (csScope st)}
    let info = EffLabelInfo {eliLabel = labelG, eliIface = ifaceG, eliParams = params, eliOps = ops}
    modify' $ \st -> st {csModEffLabels = Map.insert nm info (csModEffLabels st)}

-- | §18.1.15: a top-level @effect label l : E@ mints a fresh effect label
-- @l@ that shares the operations and interface of an existing effect @E@
-- (so several labels can name distinct instances of one effect). The new
-- label gets its own identity; its operations and interface are E's.
elabTopEffectLabel :: EffectDecl -> Span -> CheckM ()
elabTopEffectLabel eff sp = do
  let lblName = nameText (effName eff)
  unless (null (effParams eff)) $
    reportUnsupported sp "effect-label declaration parameters"
  case effLabelType eff of
    Just (EVar en) -> do
      mbase <- gets (Map.lookup (nameText en) . csModEffLabels)
      case mbase of
        Nothing ->
          errAt (nameSpan en) "E_NAME_UNRESOLVED" (Just "kappa.name.unresolved")
            ("effect label '" <> lblName <> "' references unknown effect '" <> nameText en
               <> "' (the interface must be a top-level 'effect' declaration in scope, §18.1.15)")
        Just base -> do
          already <- gets (Map.member lblName . csModEffLabels)
          unless already $ do
            st0 <- get
            let labelG = GName (csModule st0) (lblName <> ".label")
            addGlobal labelG (GlobalDef (VGlobN (gPrel "EffLabel") []) Nothing False)
            recordCoreBody labelG (CLit (LitStr (effLabelKey labelG)))
            -- same interface + operations as E, but a fresh label identity
            modify' $ \st ->
              st {csModEffLabels = Map.insert lblName (base {eliLabel = labelG}) (csModEffLabels st)}
    _ ->
      errAt sp "E_EFFECT_LABEL_FORM" (Just "kappa-hs.effect.label")
        ("'effect label " <> lblName <> " : E' requires E to be a named top-level effect (§18.1.15)")

-- | Effect-row syntax @<[l1 : E1, ... | tail]>@ (§18.1.14): rows are
-- neutral spines of @__effRowCons label iface rest@.
elabEffRow :: Ctx -> [(Name, Expr)] -> Maybe Expr -> Span -> CheckM (Term, Value)
elabEffRow ctx entries mtail _sp = do
  parts <- fmap catMaybes . forM entries $ \(ln, ifE) -> do
    meli <- lookupEffLabelM ctx (nameText ln)
    case meli of
      Just eli -> do
        ifTm <- check ctx ifE (VSort 0)
        pure (Just (CGlob (eliLabel eli), ifTm))
      Nothing -> do
        errAt (nameSpan ln) "E_NAME_UNRESOLVED" (Just "kappa.name.unresolved")
          ("unresolved effect label '" <> nameText ln <> "' (not a scoped (§9.3.1.1) or top-level (§18.1) effect)")
        pure Nothing
  tailTm <- case mtail of
    Nothing -> pure (CGlob (gPrel "__effRowNil"))
    Just te -> check ctx te (VGlobN (gPrel "EffRow") [])
  let row =
        foldr
          (\(l, t) acc -> CApp Expl (CApp Expl (CApp Expl (CGlob (gPrel "__effRowCons")) l) t) acc)
          tailTm
          parts
  pure (row, VGlobN (gPrel "EffRow") [])

-- | A non-dependent function-type value (level-safe: the codomain is
-- captured in the closure environment).
nonDepPiV :: Q -> Value -> Value -> Value
nonDepPiV q dom cod = VPi Expl q "_" dom (Closure [cod] (CVar 1))

effTyV :: Value -> Value -> Value
effTyV row a = VGlobN (gPrel "Eff") [(Expl, row), (Expl, a)]

-- | Instantiate an operation's payload and result types at concrete effect
-- parameter VALUES (outer-to-inner). The stored types are de Bruijn under the
-- parameter binders, so the eval environment lists the parameters
-- innermost-first.
instOpTypes :: EvalCtx -> [Value] -> EffOpInfo -> ([Value], Value)
instOpTypes ec ps op =
  let env = reverse ps
   in (map (eval ec env) (eoiArgsT op), eval ec env (eoiResT op))

-- | The field name of the @i@-th tuple component (§6.6 tuples are records with
-- @_1@, @_2@, … fields), used to bundle a multi-argument operation payload.
effTupleField :: Int -> Text
effTupleField i = "_" <> T.pack (show (i + 1))

-- | An operation selection @label.op@ (§18.1.15): a first-class value of type
-- @forall params. argTy -> Eff <[label : E params]> resTy@ that builds the
-- §30.2.2.7 OpCall tree node with the identity continuation. For an
-- unparameterized effect (@params = []@) this is just @argTy -> Eff <[label :
-- E]> resTy@.
effOpSelection :: EffLabelInfo -> EffOpInfo -> CheckM (Term, Value)
effOpSelection eli op = do
  let -- the implicit binders are the effect's type parameters followed by the
      -- operation's own forall-bound implicits; the interface in the row uses
      -- only the effect parameters (the first @ne@).
      allParams = eliParams eli ++ eoiImplicits op
      np = length allParams
      ne = length (eliParams eli)
      argsT = eoiArgsT op
      na = length argsT
      -- the interface applied to the effect-parameter variables; @extra@ counts
      -- binders introduced after the implicit binders.
      ifaceApp extra =
        foldl (\f i -> CApp Expl f (CVar (np - 1 - i + extra)))
          (CGlob (eliIface eli)) [0 .. ne - 1]
      rowT extra =
        CApp Expl
          (CApp Expl (CApp Expl (CGlob (gPrel "__effRowCons")) (CGlob (eliLabel eli))) (ifaceApp extra))
          (CGlob (gPrel "__effRowNil"))
      -- TYPE: forall params opImpls. A₁ -> … -> Aₙ -> Eff <[label : iface params]> B.
      -- Under the k-th argument binder, the implicit binders are shifted by k,
      -- and argument type Aₖ (de Bruijn under the implicit binders) by k.
      effCod = CApp Expl (CApp Expl (CGlob (gPrel "Eff")) (rowT na)) (shiftTerm na 0 (eoiResT op))
      argArrows = foldr (\(k, aT) acc -> CPi Expl QW "__x" (shiftTerm k 0 aT) acc) effCod (zip [0 ..] argsT)
      tyTerm = foldr (\(nm, kT) acc -> CPi Impl Q0 nm kT acc) argArrows allParams
      -- TERM: \@params @opImpls -> \x₁ … \xₙ -> __EffOp label op PAYLOAD k,
      -- where PAYLOAD is the single argument when n = 1, else the tuple.
      payload
        | na == 1 = CVar 0
        | otherwise = CRecordV [(effTupleField i, CVar (na - 1 - i)) | i <- [0 .. na - 1]]
      opCall =
        CCtor
          (gPrel "__EffOp")
          [ CGlob (eliLabel eli)
          , CLit (LitStr (eoiName op))
          , payload
          , CLam Expl Q1 "__r" (CCtor (gPrel "__EffPure") [CVar 0])
          ]
      opBody = foldr (\_ acc -> CLam Expl QW "__x" acc) opCall argsT
      tm = foldr (\(nm, _) acc -> CLam Impl Q0 nm acc) opBody allParams
  tyV <- evalIn emptyCtx tyTerm
  pure (tm, tyV)

-- | Split an effect-row value at a label: the matching interface and
-- the residual row (§18.1.21 SplitEff, by §18.1.18 label identity).
splitEffRow :: GName -> Value -> CheckM (Maybe (Value, Value))
splitEffRow labelG row0 = do
  row <- forceM row0
  case row of
    VGlobN (GName _ "__effRowCons") [(_, l), (_, e), (_, rest)] -> do
      lF <- forceM l
      case lF of
        VGlobN lg []
          | lg == labelG -> pure (Just (e, rest))
        _ -> do
          minner <- splitEffRow labelG rest
          pure $ case minner of
            Just (e', rest') ->
              Just (e', VGlobN (gPrel "__effRowCons") [(Expl, l), (Expl, e), (Expl, rest')])
            Nothing -> Nothing
    _ -> pure Nothing

-- | @[deep] handle label expr with case ...@ (§18.1.21–§18.1.22). The
-- target carrier is @Eff r@ for the residual row @r@ in v1.
elabHandle :: Ctx -> Bool -> Expr -> Expr -> [HandlerCase] -> Span -> Maybe Value -> CheckM (Term, Value)
elabHandle ctx deep lblE scrutE cases sp mexpected = do
  mEli <- case lblE of
    EVar ln -> lookupEffLabelM ctx (nameText ln)
    _ -> pure Nothing
  case mEli of
    Nothing -> do
      errAt (exprSpan lblE) "E_NAME_UNRESOLVED" (Just "kappa.name.unresolved")
        "'handle' requires an effect label in scope (a §9.3.1.1 scoped or §18.1 top-level effect)"
      anyHole ctx
    Just eli -> do
      (scrutTm0, scrutTy0) <- infer ctx scrutE
      (scrutTm, scrutTy1) <- insertAllImplicits ctx (exprSpan scrutE) scrutTm0 scrutTy0
      scrutTy <- forceM scrutTy1
      case scrutTy of
        VGlobN (GName _ "Eff") [(_, row), (_, aT)] -> do
          msplit <- splitEffRow (eliLabel eli) row
          -- the matched interface fixes the effect's type parameters (§18.1.15):
          -- @<[l : State Int]>@ gives @State Int@, so the parameters are @[Int]@.
          (residual, paramVs) <- case msplit of
            Just (ifaceV0, rest) -> do
              ifaceV <- forceM ifaceV0
              let ps = case ifaceV of
                    VGlobN g spn | g == eliIface eli -> map snd spn
                    _ -> []
              pure (rest, ps)
            Nothing -> do
              errAt (exprSpan scrutE) "E_EFFECT_LABEL_NOT_IN_ROW" (Just "kappa.effect.row-mismatch")
                "the handled computation's effect row does not contain the handled label (§18.1.21)"
              pure (VGlobN (gPrel "__effRowNil") [], [])
          ecH <- ec_
          -- bind an operation's own implicit (forall-bound) parameters as fresh
          -- skolem rigids for the clause's typing context. They are NOT runtime
          -- binders (erased; consumed at the call site, absent from the OpCall
          -- payload), so the clause term omits them — sound because the body
          -- references only the explicit args and the resumption, which sit
          -- ABOVE the skolems in the context (lower de Bruijn indices).
          let goBOI c accInOrder [] = pure (c, accInOrder)
              goBOI c accInOrder ((inm, kT) : rest) = do
                let kindV = eval ecH (reverse (paramVs ++ accInOrder)) kT
                    c' = bindCtx inm False kindV c
                goBOI c' (accInOrder ++ [VRigid (ctxLen c) []]) rest
              bindOpImplicits c0 = goBOI c0 []
          bT <- freshMetaV ctx
          -- §18.1.21: the handler eliminates into a target carrier `m`. By
          -- default (and for an `Eff r` expectation) that is `Eff residual`;
          -- when the surrounding context expects a NON-Eff carrier (e.g.
          -- `IO e`), use it directly — the §30.2.2.7 handler kernel is
          -- carrier-agnostic (it applies the clauses/return and threads the
          -- resumption, never imposing Eff).
          resultTy <- case mexpected of
            Just t -> do
              tf <- forceM t
              case tf of
                VGlobN (GName _ "Eff") _ -> pure (effTyV residual bT)
                _ -> pure tf
            Nothing -> pure (effTyV residual bT)
          -- exactly one return clause (§18.1.21)
          retLam <- case [(pat, body, csp) | HandlerReturn pat body csp <- cases] of
            [(pat, body, _)] ->
              handlerClauseLam ctx QW pat aT (\c' -> check c' body resultTy)
            [] -> do
              errAt sp "E_HANDLER_RETURN_MISSING" (Just "kappa-hs.effect.handler")
                "a handler requires exactly one 'case return x -> ...' clause (§18.1.21)"
              pure (CLam Expl QW "__x" (CCtor (gPrel "__EffPure") [CVar 0]))
            (_ : (_, _, csp2) : _) -> do
              errAt csp2 "E_HANDLER_RETURN_DUPLICATE" (Just "kappa-hs.effect.handler")
                "a handler permits only one 'case return x -> ...' clause (§18.1.21)"
              pure (CLam Expl QW "__x" (CCtor (gPrel "__EffPure") [CVar 0]))
          -- one operation clause per declared operation (§18.1.21)
          let opClauses =
                [(onm, argPats, kn, body, csp) | HandlerOp onm argPats kn body csp <- cases]
          forM_ (eliOps eli) $ \op ->
            unless (any (\(onm, _, _, _, _) -> nameText onm == eoiName op) opClauses) $
              errAt sp "E_HANDLER_OP_MISSING" (Just "kappa-hs.effect.handler")
                ("this handler has no clause for operation '" <> eoiName op <> "' (§18.1.21)")
          clauseTms <- fmap catMaybes . forM opClauses $ \(onm, argPats, kn, body, csp) ->
            case find ((== nameText onm) . eoiName) (eliOps eli) of
              Nothing -> do
                errAt (nameSpan onm) "E_HANDLER_OP_UNKNOWN" (Just "kappa-hs.effect.handler")
                  ("the handled effect declares no operation '" <> nameText onm <> "' (§18.1.21)")
                pure Nothing
              Just op -> do
                -- skolemize the operation's own implicit parameters, then take
                -- its argument/result types at the effect's actual type
                -- parameters plus those skolems (§18.1.15/§18.1.21)
                (ctxSk, skolemVs) <- bindOpImplicits ctx (eoiImplicits op)
                let (opArgVs, opResV) = instOpTypes ecH (paramVs ++ skolemVs) op
                    nArgs = length opArgVs
                when (length argPats /= nArgs) $
                  errAt csp "E_HANDLER_OP_ARITY" (Just "kappa-hs.effect.handler")
                    ( "operation '" <> nameText onm <> "' takes " <> T.pack (show nArgs)
                        <> " argument(s) but this clause binds " <> T.pack (show (length argPats)) <> " (§18.1.21)")
                -- shallow k resumes in the unhandled carrier; deep k is
                -- already re-handled (§18.1.21/§18.1.22)
                let kTy
                      | deep = nonDepPiV Q1 opResV resultTy
                      | otherwise = nonDepPiV Q1 opResV (effTyV row aT)
                    -- bind the resumption `k` (at its declared quantity) and
                    -- check the body in the target carrier
                    mkK cArgs = do
                      let cK = bindCtx (nameText kn) False kTy cArgs
                      inner <- check cK body resultTy
                      pure (CLam Expl (eoiQ op) (nameText kn) inner)
                lam <- case (argPats, opArgVs) of
                  -- single argument: the payload IS the value (§18.1.21)
                  ([p], [argV]) -> handlerClauseLam ctxSk QW p argV mkK
                  -- n ≥ 2 arguments: the payload is the tuple (x₁,…,xₙ);
                  -- destructure it positionally to bind the clause parameters
                  (ps, _) -> do
                    let tupTy = VRecordT [(effTupleField i, v) | (i, v) <- zip [0 ..] opArgVs]
                        c0 = bindCtx "__payload" False tupTy ctxSk
                    (patC, cArgs, _) <- elabPattern c0 (PTuple ps csp) tupTy
                    inner <- mkK cArgs
                    pure (CLam Expl QW "__payload" (CMatch (CVar 0) [CaseAlt patC Nothing inner]))
                pure (Just (eoiName op, lam))
          let opsRec = CRecordV (sortOn fst clauseTms)
              deepTm = CCtor (gPrel (if deep then "True" else "False")) []
              tm =
                foldl'
                  (CApp Expl)
                  (CGlob (gPrel "__handleEff"))
                  [deepTm, CGlob (eliLabel eli), retLam, opsRec, scrutTm]
          pure (tm, resultTy)
        _ -> do
          errAt (exprSpan scrutE) "E_TYPE_EQUALITY_MISMATCH" (Just "kappa.type.mismatch")
            "the handled computation of 'handle' must have an Eff type (§18.1.21)"
          anyHole ctx

-- | A one-argument clause lambda binding a surface pattern: simple
-- variable patterns bind directly; other patterns go through a match.
handlerClauseLam ::
  Ctx -> Q -> Pattern -> Value -> (Ctx -> CheckM Term) -> CheckM Term
handlerClauseLam ctx q pat ty mkBody = case pat of
  PVar n -> do
    let ctx' = bindCtx (nameText n) False ty ctx
    CLam Expl q (nameText n) <$> mkBody ctx'
  PWild _ -> do
    let ctx' = bindCtx "__w" False ty ctx
    CLam Expl q "__w" <$> mkBody ctx'
  _ -> do
    let ctx0 = bindCtx "__scrut" False ty ctx
    (patC, ctx', _) <- elabPattern ctx0 pat ty
    body <- mkBody ctx'
    pure (CLam Expl q "__scrut" (CMatch (CVar 0) [CaseAlt patC Nothing body]))

-- | A @do@ block in an @Eff row a@ position (§18.1.14: Eff is the
-- monadic carrier): items elaborate to @__effBind@ chains.
elabEffDo :: Ctx -> Value -> Value -> [DoItem] -> Span -> CheckM (Term, Value)
elabEffDo ctx0 row aT items0 sp = do
  tm <- go ctx0 items0
  pure (tm, effTyV row aT)
  where
    effT = effTyV row
    go _ [] = do
      errAt sp "E_DO_EMPTY" (Just "kappa-hs.do.empty")
        "a do block must end with an expression item (§18.2)"
      pure (CCtor (gPrel "__EffPure") [CCtor (gPrel "Unit") []])
    go c [DoExpr e] = do
      -- final item: an Eff computation of the result type, or (corpus
      -- accommodation, as in the IO kernel) a pure result value
      let eD = desugarBang e
      st0 <- get
      n0 <- gets (length . csDiags)
      tm0 <- check c eD (effT aT)
      n1 <- gets (length . csDiags)
      if n1 == n0
        then pure tm0
        else do
          put st0
          tm <- check c eD aT
          pure (CCtor (gPrel "__EffPure") [tm])
    -- a final statement-if is the result expression (§18.2)
    go c [DoIf alts mels isp] =
      let toExpr its = case its of
            [DoExpr e] -> e
            _ -> EDo Nothing its isp
          ifE = EIf [(cnd, toExpr body) | (cnd, body) <- alts] (toExpr <$> mels) isp
       in go c [DoExpr ifE]
    go c (item : rest) = case item of
      DoExpr e -> do
        bT <- freshMetaV c
        tm <- check c (desugarBang e) (effT bT)
        contTm <- CLam Expl QW "__u" <$> go (bindCtx "__u" False bT c) rest
        pure (effBindTm tm contTm)
      DoBind (LetBind _ _ pat mty rhs bsp) -> do
        bT <- case mty of
          Just tyE -> do
            (tyTm, _) <- inferType c tyE
            evalIn c tyTm
          Nothing -> freshMetaV c
        rhsTm <- check c (desugarBang rhs) (effT bT)
        checkIrrefutable c pat bT bsp
        contTm <- handlerClauseLam c Q1 pat bT (\c' -> go c' rest)
        pure (effBindTm rhsTm contTm)
      DoLet (LetBind _ _ pat mty rhs bsp) -> do
        -- §18.3.1: a `let` RHS inside a do block may contain `!`; desugar
        -- it like the DoBind branch above so it is not rejected as a bare
        -- splice (E_SPLICE_OUTSIDE_DO).
        let rhsD = desugarBang rhs
        (rhsTm, rhsTy) <- case mty of
          Just tyE -> do
            (tyTm, _) <- inferType c tyE
            tyV <- evalIn c tyTm
            tm <- check c rhsD tyV
            pure (tm, tyV)
          Nothing -> do
            (tm, ty) <- infer c rhsD
            insertAllImplicits c bsp tm ty
        checkIrrefutable c pat rhsTy bsp
        case pat of
          PVar n -> do
            rhsV <- evalIn c rhsTm
            tyTm <- quoteIn c rhsTy
            let c' = bindCtxLet (nameText n) False rhsTy rhsV c
            CLet QW (nameText n) tyTm rhsTm <$> go c' rest
          _ -> do
            tyTm <- quoteIn c rhsTy
            let c0 = bindCtx "__b" False rhsTy c
            (patC, c', _) <- elabPattern c0 pat rhsTy
            body <- go c' rest
            pure (CLet QW "__b" tyTm rhsTm (CMatch (CVar 0) [CaseAlt patC Nothing body]))
      other -> do
        unsupportedAt (doItemSpan other)
          "this do-item form is not supported in an Eff-typed do block by this implementation"
        go c rest
    effBindTm m f = CApp Expl (CApp Expl (CGlob (gPrel "__effBind")) m) f

-- | A @do@ block whose result type is a user monad @m@ (one with a
-- @Monad@ instance) that is not one of the kernel carriers IO\/STM\/Eff\/
-- Elab. §18.8 specifies @do@ over an arbitrary enclosing monad; for a
-- control-flow-free block this is exactly the classic monadic
-- desugaring, so the items are rewritten to surface @(>>=)@\/lambda
-- applications and elaborated through the ordinary trait-method path
-- (which inserts the @Monad m@ dictionary). The supported item set
-- mirrors 'elabEffDo' — bind\/let\/expression\/statement-if; abrupt
-- control-flow items (which would need the §18.8 completion protocol
-- realized over @m@) are rejected here, exactly as in an Eff-typed do.
elabMonadDo :: Ctx -> Value -> [DoItem] -> Span -> CheckM (Term, Value)
elabMonadDo ctx me items0 sp = do
  e <- desugar items0
  tm <- check ctx e me
  pure (tm, me)
  where
    bindOp = EVar (Name ">>=" sp)
    mkLam pat body = case pat of
      PVar n -> ELambda Nothing [simpleBinder n] body sp
      PWild _ -> ELambda Nothing [simpleBinder (Name "__u" sp)] body sp
      _ ->
        ELambda Nothing [simpleBinder (Name "__x" sp)]
          (EMatch (EVar (Name "__x" sp)) [MatchCase pat Nothing body sp] sp)
          sp
    mkBind pat act rest = EApp bindOp [ArgExplicit act, ArgExplicit (mkLam pat rest)]
    ifToExpr alts mels isp =
      let toExpr its = case its of
            [DoExpr e] -> e
            _ -> EDo Nothing its isp
       in EIf [(cnd, toExpr body) | (cnd, body) <- alts] (toExpr <$> mels) isp
    desugar [] = do
      errAt sp "E_DO_EMPTY" (Just "kappa-hs.do.empty")
        "a do block must end with an expression item (§18.2)"
      pure (EVar (Name "__u" sp))
    desugar [DoExpr e] = pure (desugarBang e)
    desugar [DoIf alts mels isp] = pure (ifToExpr alts mels isp)
    desugar (item : rest) = case item of
      DoExpr e -> mkBind (PWild sp) (desugarBang e) <$> desugar rest
      DoBind (LetBind _ _ pat _ rhs _) -> mkBind pat (desugarBang rhs) <$> desugar rest
      -- a bare `x <- act` (monadic flag True) is the same monadic bind as
      -- `let x <- act`; `x = e` (False) is an imperative reassignment with
      -- no meaning in a pure monad and is rejected below.
      DoAssign n True rhs _ -> mkBind (PVar n) (desugarBang rhs) <$> desugar rest
      DoLet lb@(LetBind _ _ _ _ _ bsp) -> (\r -> ELet [lb] r bsp) <$> desugar rest
      DoIf alts mels isp -> mkBind (PWild sp) (ifToExpr alts mels isp) <$> desugar rest
      other -> do
        unsupportedAt (doItemSpan other)
          "this do-item form is not supported in a user-monad do block by this implementation (§18.8)"
        desugar rest

doItemSpan :: DoItem -> Span
doItemSpan = \case
  DoBind lb -> lbSpan lb
  DoLet lb -> lbSpan lb
  DoLetQ _ _ _ s -> s
  DoVar _ _ s -> s
  DoAssign _ _ _ s -> s
  DoExpr e -> exprSpan e
  DoUsing _ _ _ s -> s
  DoDefer _ _ s -> s
  DoReturn _ _ s -> s
  DoBreak _ s -> s
  DoContinue _ s -> s
  DoWhile _ _ _ _ s -> s
  DoFor _ _ _ _ _ s -> s
  DoIf _ _ s -> s
  DoDecl d -> declSpan d

declSpan :: Decl -> Span
declSpan = \case
  DSig _ _ _ sp -> sp
  DLet _ _ sp -> sp
  DData _ _ sp -> sp
  DTypeAlias _ _ _ _ _ sp -> sp
  DTrait _ _ sp -> sp
  DInstance _ sp -> sp
  DDerive _ sp -> sp
  DEffect _ _ sp -> sp
  DFixity _ sp -> sp
  DImport _ sp -> sp
  DExport _ sp -> sp
  DExpect _ _ sp -> sp
  DPattern _ _ sp -> sp
  DProjection _ _ _ _ _ sp -> sp
  DTopSplice _ sp -> sp
  DUnsafeAssert _ _ sp -> sp

-- ── if / match ───────────────────────────────────────────────────────

checkIf :: Ctx -> [(Expr, Expr)] -> Maybe Expr -> Span -> Value -> CheckM Term
checkIf ctx alts mels sp resT = go ctx alts
  where
    boolT = VGlobN (gPrel "Bool") []
    go c [] = case mels of
      Just e -> check c e resT
      Nothing -> do
        errAt sp "E_IF_MISSING_ELSE" (Just "kappa-hs.control.if-missing-else")
          "if without else is only permitted as a do-block statement (§16.4, §18.4)"
        pure (CCtor (gPrel "Unit") [])
    go c ((cnd, t) : rest) = do
      -- §7.4.1 flow refinement: constructor tests in the condition
      -- refine their subjects in the condition's own conjuncts and in
      -- the then-branch
      refs <- condRefines c cnd
      let ctxR = refineCtx refs c
      cTm <- check ctxR cnd boolT
      -- §7.4.1/§16.1.8: a bare rigid Bool condition is branch-local
      -- equality evidence (b = True in then, b = False in else),
      -- consulted by conversion through the rigid-fact table
      let mLvl = case cnd of
            EVar n -> case lookupCtx (nameText n) c of
              Just (i, _) -> case drop i (ctxEnv c) of
                (VRigid l [] : _) -> Just l
                _ -> Nothing
              Nothing -> Nothing
            _ -> Nothing
          withFact ctorName act = do
            -- the condition's value is boolean branch-refinement
            -- evidence in the branch (a §3.2.3 proof source); rigid
            -- conditions additionally feed conversion's fact table
            cv <- evalIn ctxR cTm
            oldBool <- gets csBoolFacts
            modify' $ \st ->
              st {csBoolFacts = (cv, ctorName == ("True" :: Text)) : csBoolFacts st}
            r <- case mLvl of
              Nothing -> act
              Just l -> do
                oldFacts <- gets csFacts
                modify' $ \st ->
                  st {csFacts = Map.insert l (FactIs (VCtor (gPrel ctorName) [])) (csFacts st)}
                r0 <- act
                modify' $ \st -> st {csFacts = oldFacts}
                pure r0
            modify' $ \st -> st {csBoolFacts = oldBool}
            pure r
      tTm <- withFact "True" (check ctxR t resT)
      -- the negative side refines the subject to the complementary
      -- constructors of its data type (§7.4.1 lacks-refinement); only
      -- a bare `x is C` condition licenses the complement
      negs <- case cnd of
        EIs (EVar _) _ -> complementRefines refs
        _ -> pure []
      eTm <- withFact "False" (go (refineCtx negs c) rest)
      pure (CIf cTm tTm eTm)

-- | Only a whole-condition single `x is C` test yields a usable
-- complement (a failed conjunction proves nothing positive), and
-- only a UNIQUE residual constructor is a usable fact: a wider
-- residual would invent a positive fact the test never proved.
complementRefines :: [(Text, [GName])] -> CheckM [(Text, [GName])]
complementRefines refs = fmap concat . forM refs $ \(x, gs) -> do
  st <- get
  case nub [ciData ci | g <- gs, Just ci <- [Map.lookup g (csCtors st)]] of
    [dataG]
      | Just di <- Map.lookup dataG (csDatas st)
      , [residual] <- [cg | cg <- diCtors di, cg `notElem` gs] ->
          pure [(x, [residual])]
    _ -> pure []

-- | §7.4.1/§7.4.2 refinements induced by an if-condition: `x is C`
-- refines x to {C}; conjunction collects both sides; disjunction
-- refines a subject to the union of constructors when both sides
-- refine it.
condRefines :: Ctx -> Expr -> CheckM [(Text, [GName])]
condRefines _ctx = go
  where
    go = \case
      EIs (EVar n) cref -> do
        mg <- quietCtor cref
        pure [(nameText n, [g]) | Just g <- [mg]]
      EApp (EVar (Name op _)) [ArgExplicit l, ArgExplicit r]
        | op == "&&" -> (++) <$> go l <*> go r
        | op == "||" -> do
            ls <- go l
            rs <- go r
            pure [(x, gs ++ gs') | (x, gs) <- ls, (x', gs') <- rs, x == x']
      EThunk e _ -> go e
      _ -> pure []
    quietCtor (CtorRef mqual n) = do
      st <- get
      let inScope g@(GName m _) =
            m == csModule st || Map.lookup (gnameText g) (csScope st) == Just g || m == preludeModule
          cands = case mqual of
            Nothing ->
              [g | (g, _) <- Map.toList (csCtors st), gnameText g == nameText n, inScope g]
            Just q ->
              [ ctorG
              | (dg, di) <- Map.toList (csDatas st)
              , gnameText dg == nameText q
              , inScope dg
              , ctorG <- diCtors di
              , gnameText ctorG == nameText n
              ]
      pure (case cands of (g : _) -> Just g; [] -> Nothing)

checkMatch :: Ctx -> Expr -> [MatchCase] -> Span -> Value -> CheckM Term
checkMatch ctx scrut cases sp resT = do
  hasAp <- or <$> mapM caseUsesActive cases
  if hasAp
    then do
      lowered <- lowerActiveMatch ctx scrut cases sp
      check ctx lowered resT
    else checkMatchPlain ctx scrut cases sp resT
  where
    caseUsesActive = \case
      MatchCase pat _ _ _ -> patUsesActive pat
      MatchImpossible _ -> pure False
    patUsesActive pat = case pat of
      PCtor cref ps _ | not (null ps) -> do
        mc <- peekCtor ctx cref
        case mc of
          Just _ -> pure False
          Nothing -> do
            mAp <- lookupActivePattern cref
            case mAp of
              Just _ -> pure True
              Nothing -> isJust <$> lookupGlobalName (nameText (crName cref))
      PActive {} -> pure True
      _ -> pure False

-- | 'resolveCtor' without the unresolved-constructor diagnostic: used
-- while classifying possible active-pattern heads (§17.3.2).
peekCtor :: Ctx -> CtorRef -> CheckM (Maybe (GName, CtorInfo))
peekCtor ctx cref = do
  st0 <- get
  r <- resolveCtor ctx cref
  case r of
    Just _ -> pure r
    Nothing -> put st0 >> pure Nothing

-- | Find an active pattern by (unqualified) head name; same-module
-- definitions take precedence over imported ones (§17.3).
lookupActivePattern :: CtorRef -> CheckM (Maybe APInfo)
lookupActivePattern (CtorRef _ n) = do
  st <- get
  let nm = nameText n
      cands = [(g, i) | (g, i) <- Map.toList (csActive st), gnameText g == nm]
      own = [i | (GName m _, i) <- cands, m == csModule st]
  pure $ case own ++ map snd cands of
    (i : _) -> Just i
    [] -> Nothing

-- | Lower a match containing active-pattern cases (§17.3.2) into
-- nested matches over the pattern functions' results: Option results
-- test Some/None, Match results thread the Miss residue into the
-- remaining cases, and total view results match the view value
-- directly (consecutive cases with the same head share one view
-- match, preserving exhaustiveness over the view type).
lowerActiveMatch :: Ctx -> Expr -> [MatchCase] -> Span -> CheckM Expr
lowerActiveMatch ctx scrut cases sp = case scrut of
  EVar _ -> goCases scrut cases
  _ -> do
    sv <- freshNameM "__apscrut"
    let svn = Name sv sp
    inner <- goCases (EVar svn) cases
    pure (ELet [LetBind False emptyPrefix (PVar svn) Nothing scrut sp] inner sp)
  where
    goCases se cs = do
      classified <- mapM classify cs
      build se classified
    classify c@(MatchImpossible _) = pure (CPlain c)
    classify c@(MatchCase pat mguard body csp) = case pat of
      PCtor cref ps _ | not (null ps) -> do
        mc <- peekCtor ctx cref
        case mc of
          Just _ -> pure (CPlain c)
          Nothing -> do
            mAp <- lookupActivePattern cref
            case mAp of
              Just info -> case mapM activePatArgExpr (init ps) of
                Just args -> pure (CActive (crName cref) info args (last ps) mguard body csp)
                Nothing -> do
                  unsupportedAt csp "this active-pattern argument form is not supported by this implementation"
                  pure (CBad csp)
              Nothing -> do
                mg <- lookupGlobalName (nameText (crName cref))
                case mg of
                  Just _ -> do
                    errAt csp "E_PATTERN_HEAD_NOT_CONSTRUCTOR_OR_ACTIVE_PATTERN" (Just "kappa-hs.pattern.head")
                      ("'" <> nameText (crName cref)
                         <> "' is neither a constructor nor an active pattern, so it cannot head a pattern (§17.3.2)")
                    pure (CBad csp)
                  Nothing -> pure (CPlain c)
      PActive cref args vp psp -> do
        mAp <- lookupActivePattern cref
        case mAp of
          Just info -> pure (CActive (crName cref) info args vp mguard body psp)
          Nothing -> do
            errAt psp "E_PATTERN_HEAD_NOT_CONSTRUCTOR_OR_ACTIVE_PATTERN" (Just "kappa-hs.pattern.head")
              ("'" <> nameText (crName cref) <> "' is not an active pattern (§17.3.2)")
            pure (CBad psp)
      _ -> pure (CPlain c)
    apApp n args se = EApp (EVar n) (map ArgExplicit (args ++ [se]))
    pcon nm ps = PCtor (CtorRef Nothing (Name nm sp)) ps sp

    build se classified = case classified of
      [] -> pure (EMatch se [] sp)
      (CBad _ : rest) -> build se rest
      (CPlain _ : _) -> do
        let (plains, rest) = span isPlain classified
            plainCases = [c | CPlain c <- plains]
        if null rest
          then pure (EMatch se plainCases sp)
          else do
            r <- freshNameM "__apk"
            let rn = Name r sp
            inner <- build (EVar rn) rest
            pure (EMatch se (plainCases ++ [MatchCase (PVar rn) Nothing inner sp]) sp)
      (CActive n info args vp mguard body csp : rest) -> case apResult info of
        APOption -> do
          inner <- build se rest
          pure $
            EMatch (apApp n args se)
              [ MatchCase (pcon "Some" [vp]) mguard body csp
              , MatchCase (PWild sp) Nothing inner sp
              ]
              sp
        APMatch -> do
          r <- freshNameM "__apresid"
          let rn = Name r sp
          inner <- build (EVar rn) rest
          pure $
            EMatch (apApp n args se)
              [ MatchCase (pcon "Hit" [vp]) mguard body csp
              , MatchCase (pcon "Miss" [PVar rn]) Nothing inner sp
              ]
              sp
        APTotal -> do
          let sameHead = \case
                CActive n2 i2 _ _ _ _ _ -> nameText n2 == nameText n && apResult i2 == APTotal
                _ -> False
              (run, rest') = span sameHead (CActive n info args vp mguard body csp : rest)
              viewCases = [MatchCase vp' g' b' c' | CActive _ _ _ vp' g' b' c' <- run]
          extra <-
            if null rest'
              then pure []
              else do
                inner <- build se rest'
                pure [MatchCase (PWild sp) Nothing inner sp]
          pure (EMatch (apApp n args se) (viewCases ++ extra) sp)
      where
        isPlain = \case
          CPlain _ -> True
          _ -> False

-- | One classified match case during active-pattern lowering.
data CaseClass
  = CPlain !MatchCase
  | CActive !Name !APInfo ![Expr] !Pattern !(Maybe Expr) !Expr !Span
  | CBad !Span

-- | Rewrite @let? P args (vp) = e@ over an active pattern P into the
-- corresponding match on @P args e@ (§17.3.2). A Match-result pattern
-- threads a residue, which a plain @let?@ cannot receive.
rewriteActiveLetQ :: Ctx -> Pattern -> Expr -> Span -> CheckM (Pattern, Expr)
rewriteActiveLetQ ctx pat rhs dsp = case pat of
  PCtor cref ps psp | not (null ps) -> do
    mc <- peekCtor ctx cref
    case mc of
      Just _ -> pure (pat, rhs)
      Nothing -> do
        mAp <- lookupActivePattern cref
        case mAp of
          Nothing -> pure (pat, rhs)
          Just info -> case mapM activePatArgExpr (init ps) of
            Nothing -> pure (pat, rhs)
            Just args -> do
              let app = EApp (EVar (crName cref)) (map ArgExplicit (args ++ [rhs]))
                  vp = last ps
              case apResult info of
                APOption -> pure (PCtor (CtorRef Nothing (Name "Some" psp)) [vp] psp, app)
                APMatch -> do
                  errAt dsp "E_ACTIVE_PATTERN_MATCH_RESULT_NOT_ALLOWED_IN_PLAIN_LET_QUESTION"
                    (Just "kappa-hs.pattern.active")
                    "a Match-result active pattern threads a residue on a miss and may not be used in a plain 'let?'; use a match with a residue case instead (§17.3.2)"
                  pure (PCtor (CtorRef Nothing (Name "Hit" psp)) [vp] psp, app)
                APTotal -> pure (vp, app)
  _ -> pure (pat, rhs)

-- | Convert an active-pattern argument (written in pattern position)
-- to the expression it denotes (§17.3.2).
activePatArgExpr :: Pattern -> Maybe Expr
activePatArgExpr = \case
  PLit (LInt v msuf) psp -> Just (EIntLit v ((`Name` psp) <$> msuf) psp)
  PLit (LFloat v msuf) psp -> Just (EFloatLit v ((`Name` psp) <$> msuf) psp)
  PVar n -> Just (EVar n)
  _ -> Nothing

checkMatchPlain :: Ctx -> Expr -> [MatchCase] -> Span -> Value -> CheckM Term
checkMatchPlain ctx scrut cases sp resT = do
  (sTm, sTy) <- infer ctx scrut
  (sTm1, sTy1) <- insertAllImplicits ctx (exprSpan scrut) sTm sTy
  -- a variable scrutinee yields branch-local rigid facts: the matched
  -- nullary constructor on the success side, the lacks-set on later
  -- cases (dependent-match normalization, §7.4.1)
  let mLvl = case scrut of
        EVar n -> case lookupCtx (nameText n) ctx of
          Just (i, _) -> case drop i (ctxEnv ctx) of
            (VRigid l [] : _) -> Just l
            _ -> Nothing
          Nothing -> Nothing
        _ -> Nothing
      -- §13.1.4: in a variant match, a `(| ..rest |)` clause's binder has type
      -- `Variant r`, where r is the scrutinee's members MINUS those matched by
      -- earlier clauses. We thread the covered member tags through the fold and
      -- narrow the residual binder accordingly.
      variantResidual c = case c of
        PVariant Nothing Nothing _ (Just restN) _ -> Just restN
        _ -> Nothing
      goCase (accAlts, prior, covered) c = case c of
        MatchImpossible isp -> do
          empty <- scrutineeEmpty sTy1
          unless empty $
            errAt isp "E_INDEXED_IMPOSSIBLE_REACHABLE" (Just "kappa.proof.impossible-reachable")
              "'case impossible' requires the remaining scrutinee type to be uninhabited (§17.1.5)"
          pure (accAlts, prior, covered)
        MatchCase pat mguard body _ -> do
          sVarF <- forceM sTy1
          (patC, ctx') <- case (variantResidual pat, sVarF) of
            (Just restN, VVariantT members) -> do
              memberTags <- mapM (tagOf ctx) members
              let residual = [m | (m, t) <- zip members memberTags, t `notElem` covered]
              pure
                ( CPInjectRest covered
                , bindCtx (nameText restN) False (VVariantT residual) ctx
                )
            _ -> do
              (pc, cx, _) <- elabPattern ctx pat sTy1
              pure (pc, cx)
          let fact = case patC of
                CPCtor g [] -> Just (FactIs (VCtor g []))
                _ | not (null prior) -> Just (FactNot prior)
                _ -> Nothing
          oldFacts <- gets csFacts
          forM_ ((,) <$> mLvl <*> fact) $ \(l, f) ->
            modify' $ \st -> st {csFacts = Map.insert l f (csFacts st)}
          gTm <- traverse (\g -> check ctx' g (VGlobN (gPrel "Bool") [])) mguard
          bTm <- check ctx' body resT
          modify' $ \st -> st {csFacts = oldFacts}
          let prior' = prior ++ [g | CPCtor g _ <- [patC]]
              covered' = covered ++ [t | CPInject t _ <- [patC]]
          pure (accAlts ++ [CaseAlt patC gTm bTm], prior', covered')
  nErrsBefore <- gets (length . filter isError . csDiags)
  (alts, _, _) <- foldM goCase ([], [], []) cases
  nErrsAfter <- gets (length . filter isError . csDiags)
  -- §3.1: a match whose arms already failed to type against the
  -- scrutinee gets no piled-on exhaustiveness diagnostic
  when (nErrsAfter == nErrsBefore) $
    checkExhaustive ctx sp sTy1 [(p, g) | CaseAlt p g _ <- alts]
  pure (CMatch sTm1 alts)

scrutineeEmpty :: Value -> CheckM Bool
scrutineeEmpty ty = do
  t <- forceM ty
  case t of
    VGlobN g [] -> do
      st <- get
      pure $ case Map.lookup g (csDatas st) of
        Just di -> null (diCtors di)
        Nothing -> False
    _ -> pure False

-- exhaustiveness (§17.1): closed ADTs / Bool / variants / records /
-- tuples; literal scrutinees require a catch-all.
checkExhaustive :: Ctx -> Span -> Value -> [(CorePat, Maybe Term)] -> CheckM ()
checkExhaustive ctx sp ty alts = do
  t <- forceM ty
  let catchAll = any isCatchAll [p | (p, Nothing) <- alts]
  if catchAll
    then pure ()
    else case t of
      VGlobN g _ -> do
        st <- get
        case Map.lookup g (csDatas st) of
          Just di -> do
            let rows = [[p] | (p, Nothing) <- alts]
                missing =
                  [ c
                  | c <- diCtors di
                  , let a = ctorArity st c
                  , wildUseful st (specializeRows st (KCtor c) a rows) (a :: Int)
                  ]
            unless (null missing) $
              report $
                withNote ("missing cases: " <> T.intercalate ", " (map gnameText missing)) $
                  diag SevError StageElaborate "E_PATTERN_NON_EXHAUSTIVE" (Just "kappa.pattern.non-exhaustive") sp
                    "match is not exhaustive"
          Nothing -> requireCatchAll
      VVariantT members -> do
        tags <- mapM (tagOf ctx) members
        let covered = concat [coveredTags p | (p, Nothing) <- alts]
            hasRest = any hasRestPat [p | (p, Nothing) <- alts]
            missing = tags \\ covered
        unless (null missing || hasRest) $
          report $
            withNote ("missing member types: " <> T.intercalate ", " missing) $
              diag SevError StageElaborate "E_PATTERN_NON_EXHAUSTIVE" (Just "kappa.pattern.non-exhaustive") sp
                "variant match is not exhaustive"
      VRecordT _ -> unless (any isRecordIrrefutable [p | (p, Nothing) <- alts]) requireCatchAll
      _ -> requireCatchAll
  where
    requireCatchAll =
      report $
        diag SevError StageElaborate "E_PATTERN_NON_EXHAUSTIVE" (Just "kappa.pattern.non-exhaustive") sp
          "match requires a catch-all case for this scrutinee type (§17.1)"
    isCatchAll = \case
      CPWild -> True
      CPVar _ -> True
      CPAs _ p -> isCatchAll p
      CPOr ps _ -> any isCatchAll ps
      _ -> False
    irrefutableSub = \case
      CPWild -> True
      CPVar _ -> True
      CPAs _ p -> irrefutableSub p
      CPTuple ps -> all irrefutableSub ps
      CPRecord fs _ -> all (irrefutableSub . snd) fs
      _ -> False
    coveredTags = \case
      CPInject tag p | irrefutableSub p -> [tag]
      CPOr ps _ -> concatMap coveredTags ps
      _ -> []
    hasRestPat = \case
      CPInjectRest _ -> True
      _ -> False
    isRecordIrrefutable = \case
      CPRecord fs _ -> all (irrefutableSub . snd) fs
      CPTuple ps -> all irrefutableSub ps
      p -> isCatchAll p

-- §17.1 exhaustiveness for nested constructor patterns, via pattern-
-- matrix usefulness (Maranget-style, over-approximating coverage for
-- record, variant and as-patterns so positives never regress): a match
-- is non-exhaustive iff the all-wildcard row is useful w.r.t. the
-- unguarded rows.
data PatKey = KCtor !GName | KTup !Int | KLit !Literal
  deriving stock (Eq)

ctorArity :: CheckState -> GName -> Int
ctorArity st c = case Map.lookup c (csCtors st) of
  Just ci -> length (ciFields ci)
  Nothing -> 0

-- unwrap as/or patterns into plain alternatives for the first column
expandRow :: [CorePat] -> [[CorePat]]
expandRow [] = [[]]
expandRow (p : ps) = case p of
  CPAs _ q -> expandRow (q : ps)
  CPOr qs _ -> concat [expandRow (q : ps) | q <- qs]
  _ -> [p : ps]

-- a first-column pattern this analysis treats as matching anything
isWildLike :: CheckState -> CorePat -> Bool
isWildLike st = \case
  CPWild -> True
  CPVar _ -> True
  CPRecord {} -> True -- over-approximation
  CPInject {} -> True -- nested variant injections: over-approximation
  CPInjectRest _ -> True
  -- an arity-mismatched constructor pattern was already diagnosed;
  -- do not cascade a non-exhaustiveness report
  CPCtor c ps -> length ps /= ctorArity st c
  _ -> False

patKey :: CheckState -> CorePat -> Maybe (PatKey, Int)
patKey st = \case
  CPCtor c ps | length ps == ctorArity st c -> Just (KCtor c, length ps)
  CPTuple ps -> Just (KTup (length ps), length ps)
  CPLit l -> Just (KLit l, 0)
  _ -> Nothing

subPats :: CorePat -> [CorePat]
subPats = \case
  CPCtor _ ps -> ps
  CPTuple ps -> ps
  _ -> []

specializeRows :: CheckState -> PatKey -> Int -> [[CorePat]] -> [[CorePat]]
specializeRows st k a rows =
  [ row'
  | row0 <- rows
  , row <- expandRow row0
  , Just row' <- [spec row]
  ]
  where
    spec [] = Nothing
    spec (p : ps)
      | isWildLike st p = Just (replicate a CPWild ++ ps)
      | Just (k', _) <- patKey st p, k' == k = Just (subPats p ++ ps)
      | otherwise = Nothing

defaultRows :: CheckState -> [[CorePat]] -> [[CorePat]]
defaultRows st rows =
  [ ps
  | row0 <- rows
  , (p : ps) <- expandRow row0
  , isWildLike st p
  ]

-- is the all-wildcard row of width n useful w.r.t. the matrix?
wildUseful :: CheckState -> [[CorePat]] -> Int -> Bool
wildUseful _ rows 0 = null rows
wildUseful st rows n =
  let firsts = [p | row0 <- rows, (p : _) <- expandRow row0]
      keys = nub (mapMaybe (patKey st) firsts)
      complete = case keys of
        ((KTup _, _) : _) -> True
        ks@((KCtor c, _) : _) ->
          case Map.lookup c (csCtors st) >>= \ci -> Map.lookup (ciData ci) (csDatas st) of
            Just di -> all (\dc -> KCtor dc `elem` map fst ks) (diCtors di)
            Nothing -> False
        _ -> False -- literals: never a complete signature here
   in if complete
        then
          or
            [ wildUseful st (specializeRows st k a rows) (a + n - 1)
            | (k, a) <- keys
            ]
        else wildUseful st (defaultRows st rows) (n - 1)

checkIrrefutable :: Ctx -> Pattern -> Value -> Span -> CheckM ()
checkIrrefutable ctx pat ty sp = do
  ok <- irrefutableFor ctx pat ty
  unless ok $
    errAt sp "E_REFUTABLE_LET_PATTERN" (Just "kappa-hs.pattern.refutable-binding")
      "let bindings require an irrefutable pattern (§9.1.2); use match or let? instead"

irrefutableFor :: Ctx -> Pattern -> Value -> CheckM Bool
irrefutableFor ctx pat ty = case pat of
  PWild _ -> pure True
  PVar _ -> pure True
  PAs _ p -> irrefutableFor ctx p ty
  PTyped p _ _ -> irrefutableFor ctx p ty
  PTuple ps _ -> pure (all shallowIrrefutable ps)
  PUnit _ -> pure True
  PRecord fs _ _ -> pure (all (\(_, _, mp) -> maybe True shallowIrrefutable mp) fs)
  PCtor cref _ _ -> do
    t <- forceM ty
    case t of
      VGlobN g _ -> do
        st <- get
        case Map.lookup g (csDatas st) of
          Just di | [single] <- diCtors di -> do
            mr <- resolveCtor ctx cref
            pure (fmap fst mr == Just single)
          _ -> pure False
      _ -> pure False
  _ -> pure False
  where
    shallowIrrefutable = \case
      PWild _ -> True
      PVar _ -> True
      PAs _ p -> shallowIrrefutable p
      PTuple ps _ -> all shallowIrrefutable ps
      _ -> False

-- pattern elaboration: produce core pattern and extended context.
elabPattern :: Ctx -> Pattern -> Value -> CheckM (CorePat, Ctx, Bool)
elabPattern ctx0 pat0 ty0 = do
  (p, ctx) <- go ctx0 pat0 ty0
  forM_ (duplicatesOf (corePatNames p)) $ \n ->
    errAt (patternSpan pat0) "E_DUPLICATE_PATTERN_BINDER" (Just "kappa-hs.pattern.duplicate-binder")
      ("pattern binds '" <> n <> "' more than once (§17.2)")
  pure (p, ctx, True)
  where
    corePatNames :: CorePat -> [Text]
    corePatNames = \case
      CPVar n -> [n]
      CPAs n p -> n : corePatNames p
      CPCtor _ ps -> concatMap corePatNames ps
      CPTuple ps -> concatMap corePatNames ps
      CPRecord fs mr -> concatMap (corePatNames . snd) fs ++ [nm | Just nm <- [mr], not (T.null nm)]
      CPInject _ p -> corePatNames p
      -- or-pattern alternatives bind the same names; count one side
      CPOr (p : _) _ -> corePatNames p
      _ -> []
    go ctx pat tyIn = do
      ty <- forceM tyIn
      case pat of
        PWild _ -> pure (CPWild, ctx)
        PVar n
          -- a Var pattern naming an in-scope nullary constructor is a
          -- constructor pattern (lowercase ctors exist, e.g. ω-free code)
          | otherwise -> pure (CPVar (nameText n), bindCtx (nameText n) False ty ctx)
        PUnit _ -> pure (CPCtor (gPrel "Unit") [], ctx)
        PLit l _ -> do
          -- §17.2.1: a literal pattern's type must agree with a known
          -- concrete scrutinee type
          st0 <- get
          case ty of
            VGlobN h _
              | Map.member h (csDatas st0)
              , not (litHeadAgrees (coreLit l) h) -> do
                  hT <- quoteIn ctx ty
                  errOnce (patternSpan pat) "E_TYPE_EQUALITY_MISMATCH" (Just "kappa.type.mismatch")
                    ("a literal pattern cannot match a scrutinee of type '" <> renderTerm hT <> "' (§17.2.1)")
            _ -> pure ()
          pure (CPLit (coreLit l), ctx)
        PAs n p -> do
          let ctx1 = bindCtx (nameText n) False ty ctx
          (p', ctx2) <- go ctx1 p ty
          pure (CPAs (nameText n) p', ctx2)
        PTyped p tyE _ -> do
          (tyTm, _) <- inferType ctx tyE
          tyV <- evalIn ctx tyTm
          _ <- unify ctx tyV ty
          go ctx p tyV
        PTuple ps _ -> do
          fts <- case ty of
            VRecordT fs | length fs == length ps -> pure (map snd fs)
            _ -> mapM (const (freshMetaV ctx)) ps
          (ps', ctx') <- goList ctx (zip ps fts)
          pure (CPTuple ps', ctx')
        PRecord fs mrest _ -> do
          fields <- case ty of
            VRecordT fts -> pure fts
            _ -> pure []
          (ps', ctx') <-
            goList ctx [(fromMaybe (PVar n) mp, fromMaybe (VSort 0) (lookup (nameText n) fields)) | (_, n, mp) <- fs]
          let names = [nameText n | (_, n, _) <- fs]
          case mrest of
            Just (PatRestBind restN) -> do
              -- ..rest binds the remaining fields as a record (§17.2.5)
              let remaining = [(fn, ft) | (fn, ft) <- fields, fn `notElem` names]
                  ctx'' = bindCtx (nameText restN) False (VRecordT remaining) ctx'
              pure (CPRecord (zip names ps') (Just (nameText restN)), ctx'')
            Just PatRestDiscard -> pure (CPRecord (zip names ps') (Just ""), ctx')
            Nothing -> pure (CPRecord (zip names ps') Nothing, ctx')
        POr ps sp -> do
          rs <- mapM (\p -> go ctx p ty) ps
          let pats = map fst rs
          case rs of
            [] -> pure (CPWild, ctx)
            ((p1, ctx1) : _) -> do
              -- §17.2.3: every alternative must bind the SAME SET of names,
              -- with corresponding binders at definitionally-equal types. The
              -- body uses the first alternative's binder order (canonical); for
              -- each alternative we record the permutation from its own
              -- structural binder order to canonical, so a reordered binding
              -- (e.g. `A p q | B q p`) still resolves correctly at runtime.
              let canonical = corePatNames p1
                  n = length canonical
                  structNames (p, _) = corePatNames p
                  typesOf (_, c) =
                    [ (ceName e, ceType e)
                    | e <- take (ctxLen c - ctxLen ctx) (ctxEntries c)
                    ]
              ec <- ec_
              if not (all (\r -> sort (structNames r) == sort canonical) rs)
                then do
                  errAt sp "E_OR_PATTERN_BINDER_MISMATCH" (Just "kappa-hs.pattern.or-bindings")
                    "all alternatives of an or-pattern must bind the same set of names (§17.2.3)"
                  pure (CPOr pats (map (const [0 .. n - 1]) rs), ctx1)
                else do
                  -- §17.2.3 binder-type agreement (best-effort at the scrutinee
                  -- context depth; catches e.g. `I (n:Integer) | S (s:String)`)
                  let t1 = typesOf (p1, ctx1)
                  forM_ (drop 1 rs) $ \r -> do
                    let ti = typesOf r
                    forM_ canonical $ \nm ->
                      case (lookup nm t1, lookup nm ti) of
                        (Just a, Just b) ->
                          unless (convertible ec (ctxLen ctx) a b) $
                            errAt sp "E_OR_PATTERN_BINDER_MISMATCH" (Just "kappa-hs.pattern.or-bindings")
                              ( "or-pattern binder '" <> nm
                                  <> "' has incompatible types across alternatives (§17.2.3)")
                        _ -> pure ()
                  let perms =
                        [ [fromMaybe 0 (elemIndex (canonical !! j) (structNames r)) | j <- [0 .. n - 1]]
                        | r <- rs
                        ]
                  pure (CPOr pats perms, ctx1)
        PVariant mn mtyE isWild mrest _ -> case ty of
          VVariantT members -> case (mn, mtyE, mrest) of
            (_, Just tyE, Nothing) -> do
              (tyTm, _) <- inferType ctx tyE
              tyV <- evalIn ctx tyTm
              tag <- tagOf ctx tyV
              tags <- mapM (tagOf ctx) members
              unless (tag `elem` tags) $
                errAt (patternSpan pat) "E_VARIANT_MEMBER" (Just "kappa-hs.variant.unknown-member")
                  "variant pattern type is not a member of the scrutinee union"
              if isWild
                then pure (CPInject tag CPWild, ctx)
                else case mn of
                  Just n -> pure (CPInject tag (CPVar (nameText n)), bindCtx (nameText n) False tyV ctx)
                  Nothing -> pure (CPInject tag CPWild, ctx)
            (Just n, Nothing, Nothing)
              | [single] <- members -> do
                  tag <- tagOf ctx single
                  pure (CPInject tag (CPVar (nameText n)), bindCtx (nameText n) False single ctx)
              | otherwise -> do
                  errAt (nameSpan n) "E_VARIANT_AMBIGUOUS" (Just "kappa-hs.variant.ambiguous")
                    "untyped variant pattern requires a singleton union (§13.1.7)"
                  pure (CPWild, ctx)
            (Nothing, Nothing, Just restN) -> do
              pure (CPInjectRest [], bindCtx (nameText restN) False ty ctx)
            _ -> do
              errAt (patternSpan pat) "E_VARIANT_PATTERN" Nothing "malformed variant pattern"
              pure (CPWild, ctx)
          _ -> do
            errAt (patternSpan pat) "E_TYPE_EQUALITY_MISMATCH" (Just "kappa.type.mismatch")
              "variant pattern requires a union scrutinee"
            pure (CPWild, ctx)
        PCtorNamed cref fields sp -> do
          mr <- resolveCtor ctx cref
          case mr of
            Nothing -> pure (CPWild, ctx)
            Just (_, ci) -> do
              let fieldNames = mapMaybe fst (ciFields ci)
              forM_ fields $ \(n, _) ->
                unless (nameText n `elem` fieldNames) $
                  errAt (nameSpan n) "E_PATTERN_FIELD_UNKNOWN" (Just "kappa.pattern.constructor-arity")
                    ("constructor has no named field '" <> nameText n <> "'")
              let posPats =
                    [ case lookup fn [(nameText n, fromMaybe (PVar n) mp) | (n, mp) <- fields] of
                        Just p -> p
                        Nothing -> PWild sp
                    | Just fn <- map fst (ciFields ci)
                    ]
              go ctx (PCtor cref posPats sp) tyIn
        PCtor cref ps sp -> do
          mr <- resolveCtor ctx cref
          case mr of
            Nothing -> pure (CPWild, ctx)
            Just (g, ci) -> do
              -- §17.1: the cases' constructor patterns must belong to
              -- the (known) scrutinee type
              case ty of
                VGlobN h _ | h /= ciData ci -> do
                  hT <- quoteIn ctx ty
                  errOnce sp "E_TYPE_EQUALITY_MISMATCH" (Just "kappa.type.mismatch")
                    ("constructor pattern of type '" <> gnameText (ciData ci)
                       <> "' cannot match a scrutinee of type '" <> renderTerm hT <> "' (§17.1)")
                _ -> pure ()
              fieldTys <- ctorFieldTypes ctx g ci ty sp
              when (length ps /= length fieldTys) $
                errAt sp "E_PATTERN_CONSTRUCTOR_ARITY_MISMATCH" (Just "kappa.pattern.constructor-arity")
                  ("constructor pattern arity mismatch: expected "
                     <> T.pack (show (length fieldTys))
                     <> ", got "
                     <> T.pack (show (length ps)))
              -- Surplus binders get fresh metas, not Type: after the
              -- arity diagnostic the bodies must not cascade (§3.1).
              padTys <- mapM (const (freshMetaV ctx)) (drop (length fieldTys) ps)
              (ps', ctx') <- goList ctx (zip ps (fieldTys ++ padTys))
              pure (CPCtor g ps', ctx')
        PActive _ _ _ sp -> do
          unsupportedAt sp "active patterns are not supported by this implementation"
          pure (CPWild, ctx)
        POpChain {} -> do
          errAt (patternSpan pat) "E_INTERNAL" Nothing "operator pattern not re-associated"
          pure (CPWild, ctx)

    goList ctx [] = pure ([], ctx)
    goList ctx ((p, t) : rest) = do
      (p', ctx') <- go ctx p t
      (ps, ctx'') <- goList ctx' rest
      pure (p' : ps, ctx'')

    coreLit = \case
      LInt v _ -> LitInt v
      LFloat v _ -> LitDouble v
      LString s -> LitStr s
      LScalar c -> LitScalar c
    -- conservatively: only flag literal/data disagreements where the
    -- data type is plainly not the literal's family
    litHeadAgrees lit h = case lit of
      LitInt _ -> gnameText h `elem` ["Int", "Nat", "Integer"]
      LitDouble _ -> gnameText h `elem` ["Float", "Double"]
      LitStr _ -> gnameText h == "String"
      LitScalar _ -> gnameText h `elem` ["UnicodeScalar", "Char"]
      -- byte/bytes/grapheme literals have no surface pattern form
      -- (coreLit never produces them); never flag
      LitByte _ -> True
      LitBytes _ -> True
      LitGrapheme _ -> True

-- instantiate the constructor's field types against the scrutinee type
-- (GADT-lite: unify the constructor's result with the scrutinee type).
ctorFieldTypes :: Ctx -> GName -> CtorInfo -> Value -> Span -> CheckM [Value]
ctorFieldTypes ctx _ ci scrutTy _ = do
  ctype <- evalIn emptyCtx (ciType ci)
  peel ctype []
  where
    peel t acc = do
      t' <- forceM t
      case t' of
        VPi Impl _ _ _ clo -> do
          m <- freshMetaV ctx
          r <- clApp clo m
          peel r acc
        VPi Expl _ _ dom clo -> do
          m <- freshMetaV ctx
          r <- clApp clo m
          peel r (acc ++ [dom])
        result -> do
          _ <- unify ctx result scrutTy
          pure acc

-- ── try / do ─────────────────────────────────────────────────────────

ioType :: Value -> Value -> Value
ioType e a = VGlobN (gPrel "IO") [(Expl, e), (Expl, a)]

elabTry :: Ctx -> Expr -> [ExceptCase] -> Maybe Expr -> Span -> CheckM (Term, Value)
elabTry ctx body excepts mfin sp = do
  errT <- freshMetaV ctx
  resT <- freshMetaV ctx
  bodyTm <- check ctx body (ioType errT resT)
  errT' <- forceM errT
  -- handlers discharge the body's error type; the try expression's own
  -- error type is whatever the handlers / finalizer may still raise
  outErr <- if null excepts then pure errT' else freshMetaV ctx
  caught <-
    if null excepts
      then pure bodyTm
      else do
        -- \err -> match err cases
        let nm = "__err"
            ctx' = bindCtx nm False errT' ctx
        alts <- forM excepts $ \(ExceptCase pat mguard hbody _) -> do
          (patC, ctx'', _) <- elabPattern ctx' pat errT'
          gTm <- traverse (\g -> check ctx'' g (VGlobN (gPrel "Bool") [])) mguard
          hTm <- check ctx'' hbody (ioType outErr resT)
          pure (CaseAlt patC gTm hTm)
        checkExhaustive ctx sp errT' [(p, g) | CaseAlt p g _ <- alts]
        let handlerTm = CLam Expl QW nm (CMatch (CVar 0) alts)
        pure (CApp Expl (CApp Expl (CGlob (gPrel "catchIO")) bodyTm) handlerTm)
  final <- case mfin of
    Nothing -> pure caught
    Just finE -> do
      finTm <- check ctx finE (ioType outErr (VGlobN (gPrel "Unit") []))
      pure (CApp Expl (CApp Expl (CGlob (gPrel "finallyIO")) caught) finTm)
  pure (final, ioType outErr resT)

-- do blocks (§18.2): the carrier is IO in this implementation.
--
-- @loops@ tracks the enclosing loops of this do-scope (one entry per
-- loop, @Just label@ when labeled) so @break@\/@continue@ are resolved
-- at compile time: a labeled form must name an enclosing labeled loop
-- (§18.2.5) and an unlabeled form must occur inside some loop body
-- (§18.6 "Using them outside a loop body is a compile-time error").
-- The loop's @else@ suite runs after normal completion, so the loop
-- itself is not in scope as a target there. Each do-expression starts a
-- fresh scope: targets never cross a first-class do-value boundary.
elabDo :: Ctx -> Maybe Name -> [DoItem] -> Span -> Maybe Value -> CheckM (Term, Value)
elabDo ctx0 mlabel items _sp mexpected = do
  -- §18.9.3: '~' inout markers are admissible within this do elaboration
  let ctx = ctx0 {ctxInDo = True}
  me <- traverse forceM mexpected
  case me of
    -- an Eff-typed do sequences algebraic-effect computations
    -- (§18.1.14); it elaborates to __effBind chains, not the IO kernel
    Just (VGlobN (GName _ "Eff") [(_, row), (_, a)]) ->
      elabEffDo ctx row a items _sp
    -- an Elab-typed do sequences elaboration-time actions (§21.9); it
    -- elaborates to __elabBind chains run by the Elab evaluator
    Just (VGlobN (GName pm "Elab") [(_, a)])
      | pm == preludeModule ->
          elabElabDo ctx a items _sp
    -- §18.8: a do-block whose result is a user monad `m a` (m has a
    -- Monad instance) and is not a kernel carrier (IO/STM handled by
    -- elabDoIO; Eff/Elab above) elaborates by the classic monadic
    -- desugaring to (>>=)/pure.
    Just t@(VGlobN g@(GName _ gn) spine)
      | not (null spine)
      , gn `notElem` ["IO", "STM", "Eff", "Elab"] -> do
          let mV = VGlobN g (init spine)
          hasMonad <- isJust <$> instanceSearch ctx _sp (VGlobN (gPrel "Monad") [(Expl, mV)])
          if hasMonad then elabMonadDo ctx t items _sp else elabDoIO ctx me items
    _ -> elabDoIO ctx me items
  where
    elabDoIO = elabDoIOItems (nameText <$> mlabel) _sp

elabDoIOItems :: Maybe Text -> Span -> Ctx -> Maybe Value -> [DoItem] -> CheckM (Term, Value)
elabDoIOItems mlabel _sp ctx mexp items = do
  (errT, resT, doTy) <- case mexp of
    Just (VGlobN (GName _ "IO") [(_, e), (_, a)]) ->
      pure (e, a, Nothing)
    -- an STM-typed do sequences IO-shaped items (§18.1.13); the kernel
    -- runs it as the underlying action
    Just expd@(VGlobN (GName _ "STM") [(_, a)]) -> do
      e <- freshMetaV ctx
      pure (e, a, Just expd)
    -- pure-result do (corpus): a do block in a position expecting a
    -- known non-IO type sequences pure statements; the §18.8 kernel
    -- passes pure statement values through, so it runs unchanged
    Just expd | not (isFlexHead expd) -> do
      e <- freshMetaV ctx
      pure (e, expd, Just expd)
    _ -> do
      e <- freshMetaV ctx
      a <- freshMetaV ctx
      pure (e, a, Nothing)
  kitems <- goItems [] ctx errT resT items
  pure (CDo mlabel kitems, fromMaybe (ioType errT resT) doTy)
  where
    -- §18.1.13: the monad an item of this do-scope is checked at. For an
    -- STM-typed block, items are STM actions (the kernel still runs them as
    -- the underlying IO at runtime); otherwise IO of the scope's error type.
    wrapTy :: Value -> Value -> Value
    wrapTy errT x = case mexp of
      Just (VGlobN (GName _ "STM") _) -> VGlobN (gPrel "STM") [(Expl, x)]
      _ -> ioType errT x
    -- whether this do-scope is STM-typed (its items are STM actions, not
    -- IO) — the transparent nested-do path applies only to IO-shaped scopes
    isStmExpected :: Maybe Value -> Bool
    isStmExpected (Just (VGlobN (GName _ "STM") _)) = True
    isStmExpected _ = False
    goItems :: [Maybe Text] -> Ctx -> Value -> Value -> [DoItem] -> CheckM [KItem]
    goItems _ _ _ _ [] = pure []
    goItems loops c errT resT (item : rest) = do
      let lastItem = null rest
      case item of
        -- §18.8.3.1: a nested `do` block in statement position is a child
        -- scope that is TRANSPARENT to abrupt completion. Its items are
        -- elaborated under the SAME lexical completion context (enclosing
        -- `loops` and `ctxReturnTarget`), so a `break`/`continue`/`return@L`
        -- inside it that targets an enclosing loop or function resolves and
        -- propagates outward. (A first-class do VALUE — `let x = do …`, or a
        -- spliced `!doVal` — stays opaque: it is elaborated through the
        -- ordinary value path, which resets the completion context.) STM-typed
        -- do-scopes keep the generic path.
        DoExpr (EDo innerLbl innerItems _)
          | not (isStmExpected mexp) -> do
              aT <- if lastItem then pure resT else freshMetaV c
              subItems <- goItems loops c errT aT innerItems
              ks <- goItems loops c errT resT rest
              pure (KSubDo (nameText <$> innerLbl) subItems : ks)
        DoExpr e -> do
          aT <- if lastItem then pure resT else freshMetaV c
          let eD = desugarBang e
              ioT = wrapTy errT aT
          -- statements are IO actions (§18.2); the corpus also
          -- sequences pure expressions as statements, and the §18.8
          -- kernel passes pure statement values through unchanged, so
          -- an inferable statement may also check at the bare type
          tm <- case eD of
            _ | statementInferable eD -> do
                  (tm0, ty0) <- infer c eD
                  (tm1, ty1) <- insertAllImplicits c (exprSpan eD) tm0 ty0
                  okIO <- unify c ty1 ioT
                  if okIO
                    then pure tm1
                    else do
                      okPure <- unify c ty1 aT
                      okDiscard <-
                        if okPure
                          then pure True
                          else do
                            -- a final action of unit-result do-scopes
                            -- may have a non-unit result; it is
                            -- discarded (corpus accommodation)
                            isUnit <-
                              forceM aT >>= \case
                                VGlobN (GName _ "Unit") [] -> pure True
                                _ -> pure False
                            if isUnit
                              then do
                                b <- freshMetaV c
                                unify c ty1 (ioType errT b)
                              else pure False
                      unless okDiscard $ expectType c (exprSpan eD) ty1 ioT
                      pure tm1
            _ -> check c eD ioT
          (KExpr tm :) <$> goItems loops c errT resT rest
        DoBind (LetBind implocal prefix pat mty rhs bsp) -> do
          aT <- case mty of
            Just tyE -> do
              (tyTm, _) <- inferType c tyE
              evalIn c tyTm
            Nothing -> freshMetaV c
          let rhsD = desugarBang rhs
          st0 <- get
          n0 <- gets (length . csDiags)
          rhsTm0 <- check c rhsD (wrapTy errT aT)
          n1 <- gets (length . csDiags)
          rhsTm <-
            if n1 == n0
              then pure rhsTm0
              else do
                -- container bind (§18.3 accommodation): a do block in a
                -- non-IO container position binds through that container
                put st0
                (tm0, ty0) <- infer c rhsD
                (tm1, ty1) <- insertAllImplicits c bsp tm0 ty0
                ty1F <- forceM ty1
                case ty1F of
                  VGlobN (GName _ h) args
                    | h /= "IO"
                    , ((_, lastArg) : _) <- reverse args -> do
                        expectType c bsp lastArg aT
                        pure tm1
                  _ -> do
                    -- not container-shaped: restore the IO/STM diagnosis
                    put st0
                    check c rhsD (wrapTy errT aT)
          checkIrrefutable c pat aT bsp
          (patC, cBound, _) <- elabPattern c pat aT
          let c' = markImplicitLocal bsp implocal prefix c cBound
          ks <- goItems loops c' errT resT rest
          pure (KBind (qOf (bpQuantity prefix)) patC rhsTm : ks)
        DoLet (LetBind implocal prefix pat mty rhs bsp) -> do
          -- §18.3.1: `let pat = expr` inside `do` may contain `!`. The
          -- spliced computation is sequenced first and `pat` is then bound
          -- to its value; desugar `!` here exactly as the bind/expr items
          -- do, so it does not reach `infer`/`check` as a bare splice
          -- (E_SPLICE_OUTSIDE_DO). The KLet runtime runs splices via evalK.
          let rhsD = desugarBang rhs
          (rhsTm, rhsTy) <- case mty of
            Just tyE -> do
              (tyTm, _) <- inferType c tyE
              tyV <- evalIn c tyTm
              tm <- check c rhsD tyV
              pure (tm, tyV)
            Nothing -> do
              (tm, ty) <- infer c rhsD
              insertAllImplicits c bsp tm ty
          checkIrrefutable c pat rhsTy bsp
          (patC, cBound, _) <- elabPattern c pat rhsTy
          let cBound' = case (pat, rhs) of
                -- §7.4.3 stable alias: `let q = p` transports refinement
                (PVar qn, EVar pn)
                  | Just _ <- lookupCtx (nameText pn) c ->
                      addCtxAlias (nameText qn) (nameText pn) cBound
                _ -> cBound
          let c' = markImplicitLocal bsp implocal prefix c cBound'
          ks <- goItems loops c' errT resT rest
          pure (KLet (qOf (bpQuantity prefix)) patC rhsTm : ks)
        DoLetQ pat0 rhs0 mElse dsp -> do
          (pat, rhs) <- rewriteActiveLetQ c pat0 rhs0 dsp
          (rhsTm, rhsTy) <- infer c rhs
          (patC, c', _) <- elabPattern c pat rhsTy
          mElse' <- forM mElse $ \(rp, fe) -> do
            (rpC, c2, _) <- elabPattern c rp rhsTy
            feTm <- check c2 fe (ioType errT resT)
            pure (rpC, feTm)
          ks <- goItems loops c' errT resT rest
          pure (KLetQ patC rhsTm mElse' : ks)
        DoVar n rhs _ -> do
          (rhsTm, rhsTy) <- infer c rhs
          (rhsTm1, rhsTy1) <- insertAllImplicits c (nameSpan n) rhsTm rhsTy
          let refTy = VGlobN (gPrel "Ref") [(Expl, rhsTy1)]
              c' = bindCtxVar (nameText n) refTy c
          ks <- goItems loops c' errT resT rest
          pure (KVarItem (nameText n) rhsTm1 : ks)
        DoAssign n monadic rhs asp -> do
          mref <- pure (lookupCtx (nameText n) c)
          case mref of
            Just (i, entry) -> do
              et <- forceM (ceType entry)
              case et of
                VGlobN (GName _ "Ref") [(_, a)] -> do
                  rhsTm <-
                    if monadic
                      then check c (desugarBang rhs) (ioType errT a)
                      else check c (desugarBang rhs) a
                  ks <- goItems loops c errT resT rest
                  pure (KAssign (CVar i) monadic rhsTm : ks)
                _ -> do
                  errAt asp "E_ASSIGN_NOT_VAR" (Just "kappa-hs.do.assign-non-var")
                    ("'" <> nameText n <> "' is not a mutable var binding (§18.6.1)")
                  goItems loops c errT resT rest
            Nothing
              -- corpus accommodation: `x <- e` where `x` is not a var
              -- binding in scope is an Idris-style monadic bind of a
              -- fresh immutable binding (the §18.6.1 var-assign reading
              -- requires an enclosing `var x`, which does not exist)
              | monadic ->
                  goItems loops c errT resT
                    (DoBind (LetBind False emptyPrefix (PVar n) Nothing rhs asp) : rest)
              | otherwise -> do
                  errAt asp "E_NAME_UNRESOLVED" (Just "kappa.name.unresolved")
                    ("unresolved name '" <> nameText n <> "'")
                  goItems loops c errT resT rest
        DoReturn ml me rsp -> do
          -- §18.5/§18.5.1: `return@L` targets the enclosing named function
          -- or labeled lambda L. Resolution is confined to the current
          -- function/lambda body and does not cross a user-written lambda
          -- boundary, so the only reachable target is the innermost
          -- enclosing one (`ctxReturnTarget`). When L names it, the abrupt
          -- Return targets exactly the construct that bare `return` does
          -- here (the current body's completion), so it lowers to the same
          -- KReturn; a label naming anything else is a compile-time error.
          forM_ ml $ \l ->
            unless (Just (nameText l) == ctxReturnTarget c) $
              errAt (nameSpan l) "E_LABEL_UNRESOLVED" (Just "kappa-hs.do.label-unresolved")
                ("return@" <> nameText l
                   <> " does not target the enclosing named function or labeled lambda; return resolution is confined to the current function/lambda body and does not cross a lambda boundary (§18.5/§18.5.1)")
          tm <- case me of
            Just e -> do
              -- a `return` payload ordinarily carries this do-scope's
              -- result type; per the §18.8 completion kernel an abrupt
              -- Return targets the enclosing function instead, so a
              -- payload typed for the outer return context is also
              -- accepted (e.g. `if c then pure () else do return 0`)
              st0 <- get
              n0 <- gets (length . csDiags)
              tm0 <- check c (desugarBang e) resT
              n1 <- gets (length . csDiags)
              if n1 == n0
                then pure tm0
                else do
                  put st0
                  retT <- freshMetaV c
                  check c (desugarBang e) retT
            Nothing -> do
              expectType c rsp (VGlobN (gPrel "Unit") []) resT
              pure (CCtor (gPrel "Unit") [])
          ks <- goItems loops c errT resT rest
          pure (KReturn tm : ks)
        DoBreak ml bsp -> do
          checkLoopTarget "break" ml bsp
          (KBreak (nameText <$> ml) :) <$> goItems loops c errT resT rest
        DoContinue ml csp -> do
          checkLoopTarget "continue" ml csp
          (KContinue (nameText <$> ml) :) <$> goItems loops c errT resT rest
        DoWhile ml cond body mels _ -> do
          -- §18.6: a `while` condition may have type `Bool` or type
          -- `m Bool` where `m` is the enclosing do-block's monad (here
          -- `IO errT`). A pure `Bool` is used directly (and is a
          -- flow-sensitive condition position per §18.6 line 20478); a
          -- monadic `IO errT Bool` is re-run each iteration, so it is
          -- wrapped in a `__runIO` splice whose evaluation executes the
          -- action and yields the `Bool` the kernel loop tests. The pure
          -- form is attempted first; only if it produces a type error is
          -- the monadic form tried, which keeps the common pure path and
          -- its refinement facts unchanged.
          let condD = desugarBang cond
          st0 <- get
          n0 <- gets (length . csDiags)
          pureTm <- check c condD (VGlobN (gPrel "Bool") [])
          n1 <- gets (length . csDiags)
          condTm <-
            if n1 == n0
              then pure pureTm
              else do
                put st0
                actTm <- check c condD (ioType errT (VGlobN (gPrel "Bool") []))
                errTm <- quoteIn c errT
                boolTm <- quoteIn c (VGlobN (gPrel "Bool") [])
                pure
                  ( CApp
                      Expl
                      (CApp Impl (CApp Impl (CGlob (gPrel "__runIO")) errTm) boolTm)
                      actTm
                  )
          bodyKs <- goItems (withLoop ml) c errT (VGlobN (gPrel "Unit") []) body
          elsKs <- traverse (goItems loops c errT (VGlobN (gPrel "Unit") [])) mels
          ks <- goItems loops c errT resT rest
          pure (KWhile (nameText <$> ml) condTm bodyKs elsKs : ks)
        DoFor ml pat src body mels fsp -> do
          -- §18.6/§20.2: a 'for' generator iterates any source the
          -- comprehension as-if list model understands. The common case
          -- is a List source, which is checked directly against
          -- 'List elemT' exactly as before (no double elaboration, so
          -- the §12 usage analysis on 'src' is unaffected). Non-List
          -- sources (Array/Set/Map/Option/Query/range) are detected by a
          -- side-effect-free probe of the inferred source type and
          -- materialized to the element list via the matching prelude
          -- conversion.
          let src' = desugarBang src
          elemT <- freshMetaV c
          srcKind <- probeForSrcKind c src'
          let listSrc = case srcKind of
                SKArray -> prelApp1 fsp "__arrayToList" [src']
                SKSet -> prelApp1 fsp "__setToList" [src']
                SKMap -> prelApp1 fsp "__mapToList" [src']
                SKOption -> prelApp1 fsp "__optionToList" [src']
                SKQuery -> prelApp1 fsp "__queryToList" [src']
                SKRange -> prelApp1 fsp "rangeToList" [src']
                _ -> src'
          srcTm <- check c listSrc (VGlobN (gPrel "List") [(Expl, elemT)])
          checkIrrefutable c pat elemT fsp
          (patC, c', _) <- elabPattern c pat elemT
          bodyKs <- goItems (withLoop ml) c' errT (VGlobN (gPrel "Unit") []) body
          elsKs <- traverse (goItems loops c errT (VGlobN (gPrel "Unit") [])) mels
          ks <- goItems loops c errT resT rest
          pure (KFor (nameText <$> ml) patC srcTm bodyKs elsKs : ks)
        DoIf alts mels _ -> do
          -- §7.4.1: `x is C` conditions refine their subject inside the
          -- guarded suite
          alts' <- forM alts $ \(cond, body) -> do
            refs <- condRefines c cond
            let cR = refineCtx refs c
            condTm <- check cR (desugarBang cond) (VGlobN (gPrel "Bool") [])
            bodyKs <- goItems loops cR errT (VGlobN (gPrel "Unit") []) body
            pure (condTm, bodyKs)
          elsKs <- traverse (goItems loops c errT (VGlobN (gPrel "Unit") [])) mels
          -- §8.2.2A postdominating refinement: when every branch except
          -- one completes abruptly, the surviving branch's facts hold
          -- for the rest of this do-scope
          cAfter <- case (alts, mels) of
            ([(cond, thenB)], Just elseB)
              | abruptSuite elseB -> do
                  refs <- condRefines c cond
                  pure (refineCtx refs c)
              | abruptSuite thenB -> do
                  refs <- condRefines c cond
                  negs <- case cond of
                    EIs (EVar _) _ -> complementRefines refs
                    _ -> pure []
                  pure (refineCtx negs c)
            _ -> pure c
          ks <- goItems loops cAfter errT resT rest
          pure (KIf alts' elsKs : ks)
        DoDefer ml e _ -> do
          -- §18.7: `defer e` schedules onto the current do-scope;
          -- `defer@L e` schedules onto the enclosing do-scope labeled L
          -- (which may be outer, so the action stays pending across inner
          -- scope exits and runs only when L itself exits). The labeled
          -- do-scopes enclosing this point are this do-block (mlabel) and
          -- every enclosing labeled loop body (loops); a label naming
          -- none of them is a compile-time error rather than a defer that
          -- never fires.
          forM_ ml $ \l ->
            unless (Just (nameText l) == mlabel || Just (nameText l) `elem` loops) $
              errAt (nameSpan l) "E_LABEL_UNRESOLVED" (Just "kappa-hs.do.label-unresolved")
                ("defer@" <> nameText l
                   <> " does not target an enclosing labeled do-scope (explicit 'do' or loop) of this do-scope (§18.7)")
          eTm <- check c (desugarBang e) (ioType errT (VGlobN (gPrel "Unit") []))
          ks <- goItems loops c errT resT rest
          pure (KDefer (nameText <$> ml) eTm : ks)
        DoUsing mq pat rhs usp -> do
          -- §9.3: using always binds its pattern with borrowed access at
          -- the default quantity ω; an explicit prefix is rejected
          forM_ mq $ \qsp ->
            errAt qsp "E_QTT_USING_EXPLICIT_QUANTITY" (Just "kappa-hs.qtt.using-quantity")
              "a 'using' item always binds with borrowed access at the default quantity ω; explicit quantity or borrow markers are not permitted (§9.3, §18.2)"
          -- §19.5/§18.8.5 resource-scoped bind: `acquire` yields an owned
          -- resource of type `m A`; `pat` is bound (borrowed) for the rest
          -- of the scope, and the resource's `release` (resolved from the
          -- required `Releasable m A` instance) is attached to scope exit,
          -- running on EVERY exit path (normal/return/break/continue/error)
          -- in LIFO order with any `defer`s — realized by the protected
          -- exit machinery (KUsing), not a source rewrite to `defer` (which
          -- would move the resource before the borrowed use, §19.5).
          aT <- freshMetaV c
          acquireTm <- check c (desugarBang rhs) (ioType errT aT)
          -- Releasable (m := IO errT) (a := aT); `release : a -> m Unit`
          let mTyV = VGlobN (gPrel "IO") [(Expl, errT)]
          dictTm <- resolveImplicit c usp (VGlobN (gPrel "Releasable") [(Expl, mTyV), (Expl, aT)])
          let releaseTm = CProj dictTm "release"
          checkIrrefutable c pat aT usp
          (patC, cBound, _) <- elabPattern c pat aT
          ks <- goItems loops cBound errT resT rest
          pure (KUsing patC acquireTm releaseTm : ks)
        DoDecl d -> do
          case d of
            DLet _ (LetDef (Just n) _ Nothing _ [] mty Nothing rhs) dsp ->
              goItems loops c errT resT (DoLet (LetBind False emptyPrefix (PVar n) mty rhs dsp) : rest)
            _ -> do
              unsupportedAt (declSpan d)
                "this local declaration form inside do is not supported by this implementation"
              goItems loops c errT resT rest
      where
        withLoop ml = (nameText <$> ml) : loops
        checkLoopTarget what ml sp = case ml of
          Just l ->
            unless (Just (nameText l) `elem` loops) $
              errAt (nameSpan l) "E_LABEL_UNRESOLVED" (Just "kappa-hs.do.label-unresolved")
                (what <> "@" <> nameText l
                   <> " does not target an enclosing labeled loop of this do-scope (§18.2.5)")
          Nothing ->
            when (null loops) $
              errAt sp "E_BREAK_OUTSIDE_LOOP" (Just "kappa-hs.do.break-outside-loop")
                ("'" <> what
                   <> "' is valid only within the body of a loop of this do-scope (§18.6)")

-- | Does this do-suite always complete abruptly (its final item is a
-- return\/break\/continue)? Used for §8.2.2A postdominating refinement.
abruptSuite :: [DoItem] -> Bool
abruptSuite items = case reverse items of
  (DoReturn {} : _) -> True
  (DoBreak {} : _) -> True
  (DoContinue {} : _) -> True
  (DoExpr (EDo _ inner _) : _) -> abruptSuite inner
  _ -> False

-- | Is the (forced) value headed by an unsolved metavariable?
isFlexHead :: Value -> Bool
isFlexHead = \case
  VFlex {} -> True
  _ -> False

-- | Statement shapes that elaborate soundly by inference, allowing the
-- pure-statement accommodation in 'elabDo' (variants, literals and other
-- expected-type-directed forms keep the plain IO checking path).
statementInferable :: Expr -> Bool
statementInferable = \case
  EApp f _ -> statementInferable f
  EVar {} -> True
  EDot {} -> True
  EQDot {} -> True
  EOpChain {} -> True
  EIf {} -> True
  EMatch {} -> True
  EUnit {} -> True
  ETuple {} -> True
  EIntLit {} -> True
  EFloatLit {} -> True
  EStringLit {} -> True
  _ -> False

-- | §16.3.3: an implicit do-binding @let (\@x : T) = e@ joins the local
-- implicit context for the remaining items. @before@ is the context the
-- pattern was elaborated in; the entries added on top of it are marked.
-- @binderSp@ is the do-binding's source span; for a @\@&@-borrowed
-- implicit local it is recorded as the §3.1.1A introduction origin so a
-- later borrow-escape diagnostic can cite where the candidate was
-- borrowed.
markImplicitLocal :: Span -> Bool -> BinderPrefix -> Ctx -> Ctx -> Ctx
markImplicitLocal _ False _ _ after = after
markImplicitLocal binderSp True (BinderPrefix mq mb) before after =
  let es = ctxEntries after
      (new, old) = splitAt (length es - ctxLen before) es
      mark e =
        e
          { ceImplicitLocal = True
          , ceQ = mq
          , ceBorrow = isJust mb
          , ceOrigin = if isJust mb then binderSp else ceOrigin e
          }
   in after {ctxEntries = map mark new ++ old}

-- `!e` splicing inside do items (§18.3): rewritten to runIO marker the
-- interpreter understands; typing treats !e : a where e : IO err a.
desugarBang :: Expr -> Expr
desugarBang = \case
  EBang _ e sp -> EApp (EVar (Name "__runIO" sp)) [ArgExplicit (desugarBang e)]
  -- §18.3.1 immediate-application splice: an /open/ `!f x y` is sugar for
  -- `!(f x y)`, i.e. the entire maximal application spine is the splice
  -- operand. The parser produces `EApp (EBang False f) [x, y]`, so when
  -- the head of an application is an open bang, the whole application is
  -- the spliced computation rather than `(!f) x y`. A /closed/ bang
  -- `(!f) x` (explicitly parenthesised) splices `f` first and then applies
  -- the result to `x`, so it falls through to the ordinary EApp rule.
  EApp (EBang False f bsp) args ->
    EApp (EVar (Name "__runIO" bsp))
      [ArgExplicit (EApp (desugarBang f) (map mapArg args))]
  EApp f args -> EApp (desugarBang f) (map mapArg args)
  EIf alts mels sp ->
    EIf [(desugarBang c, desugarBang t) | (c, t) <- alts] (fmap desugarBang mels) sp
  EMatch scrut cases sp ->
    EMatch (desugarBang scrut)
      [case mc of
         MatchCase p g b csp -> MatchCase p (fmap desugarBang g) (desugarBang b) csp
         other -> other
      | mc <- cases]
      sp
  EAscription e t sp -> EAscription (desugarBang e) t sp
  ETuple es sp -> ETuple (map desugarBang es) sp
  EDot e m -> EDot (desugarBang e) m
  e -> e
  where
    mapArg = \case
      ArgExplicit e -> ArgExplicit (desugarBang e)
      ArgImplicit e -> ArgImplicit (desugarBang e)
      a -> a

-- ── §21 Syntax, macros, and Elab ─────────────────────────────────────
--
-- Design (Spec §21, §22, §6.3.4.3–5, §20.9):
--
--   * 'Syntax t' is compile-time-only. A quote @'{ e }@ elaborates to
--     'CQuote': the SURFACE payload (with @${...}@ sub-splices replaced
--     by numbered 'EQuoteHole' grafting slots), §21.4 hygiene metadata,
--     and one elaborated term of type @Syntax _@ per slot. Quotation
--     type-checks the payload to assign the Syntax index (and to
--     surface malformed-payload diagnostics) but discharges no final
--     object-level obligations; the payload TERM is discarded and the
--     surface syntax kept (§21.1).
--   * Hygiene (§21.4): every payload occurrence of a quote-site LOCAL
--     binder (not rebound inside the payload) is renamed to a fresh
--     hygienic spelling and recorded as a 'QuoteCapture' with its
--     context LEVEL. Splicing validates each capture against the
--     splice-site context (binder still present at that level, same
--     spelling) — one rule covering local-binder escape and
--     borrow-scope escape — then resolves capture occurrences by level
--     through 'ctxHyg', immune to later shadowing.
--   * @$(m)@ (§21.2) admits @m : Elab (Syntax t)@ or the bare-Syntax
--     sugar @m : Syntax t@ (treated as @pure m@). The elaborated
--     argument is EVALUATED at elaboration time (runtime-mode NbE over
--     compile-time values) and the resulting action is run by
--     'runElab', a CheckM interpreter over stuck @__elab*@ primitive
--     applications: pure/bind, the §21.5 reflection queries, the
--     §21.9 diagnostics, and §22 shape reflection. The produced
--     Syntax is grafted ('substQuoteHoles') and re-elaborated at the
--     splice site exactly as if written there (§30.1); the grafted
--     expansion is recorded in 'csExpansions' so the §12.2 usage
--     analysis charges the expanded object-level uses at each splice.
--   * Elab-typed @do@ blocks lower to @__elabBind@ chains; @pure@
--     into an Elab position lifts via @__elabPure@ (§21.9).
--   * Prefixed strings (§6.3.4.3–5) resolve their handler term at type
--     @Elab (InterpolatedMacro t)@, run @buildInterpolated@ over the
--     §6.3.4.4 fragment list at elaboration time, and splice the
--     result; bare object-phase 'InterpolatedMacro' values are
--     rejected. Comprehension carriers with 'FromComprehensionRaw' /
--     'FromComprehensionPlan' instances run the sink hook the same
--     way (§20.9), raw preferred, after checking the instance's
--     'Item' member against the yielded item type.
--
-- §21.8 restrictions: package mode provides no IO capability to the
-- evaluator by construction (no IO primitive reduces outside the
-- §18.8 kernel). Termination of macro execution is bounded by the
-- evaluator's fuel; see SPEC_COVERAGE.md for the provided subset.

-- | The runtime-mode evaluation context for elaboration-time
-- execution (§21.8, §30.2.4): every global unfolds.
ecRT_ :: CheckM EvalCtx
ecRT_ = gets (\st -> EvalCtx (Globals (csGlobals st)) (csMetas st) True (csFacts st))

evalRT :: Ctx -> Term -> CheckM Value
evalRT ctx t = do
  ec <- ecRT_
  pure (eval ec (ctxEnv ctx) t)

forceRT :: Value -> CheckM Value
forceRT v = do
  ec <- ecRT_
  pure (force ec v)

vappRT :: Value -> [Value] -> CheckM Value
vappRT f as = do
  ec <- ecRT_
  pure (foldl' (\g a -> vapp ec g Expl a) f as)

-- | Run an elaboration speculatively: keep its result only when it
-- reported no new diagnostics; otherwise restore the full state.
trySpec :: CheckM a -> CheckM (Maybe a)
trySpec act = do
  st0 <- get
  n0 <- gets (length . csDiags)
  r <- act
  n1 <- gets (length . csDiags)
  if n1 == n0 then pure (Just r) else put st0 >> pure Nothing

synTV :: Value -> Value
synTV t = VGlobN (gPrel "Syntax") [(Expl, t)]

elabTV :: Value -> Value
elabTV t = VGlobN (gPrel "Elab") [(Expl, t)]

elabPureTm :: Term -> Term
elabPureTm = CApp Expl (CGlob (GName primModule "__elabPure"))

-- | Elaborate a syntax quote @'{ payload }@ (§21.1).
elabQuote :: Ctx -> Expr -> Span -> Maybe Value -> CheckM (Term, Value)
elabQuote ctx payload0 sp mexp = do
  let spliceList = collectSplices payload0
      slotIdx = Map.fromList [(ssp, i) | (i, (ssp, _)) <- zip [0 ..] spliceList]
      payload = replaceSplices slotIdx payload0
  -- the sub-splice slots: each must be a meta-phase Syntax value (an
  -- Elab action is not run implicitly inside a quote, §21.1)
  slots <- forM spliceList $ \(ssp, se) -> do
    (tm0, ty0) <- infer ctx se
    (tm1, ty1) <- insertAllImplicits ctx ssp tm0 ty0
    ty1F <- forceM ty1
    case ty1F of
      VGlobN (GName pm "Syntax") [(_, t)]
        | pm == preludeModule -> pure (tm1, t)
      VGlobN (GName pm "Elab") _
        | pm == preludeModule -> do
            errAt ssp "E_QUOTE_SPLICE_ELAB" (Just "kappa.syntax.quotation")
              "an 'Elab (Syntax _)' action is not run implicitly inside a quote; bind it in the surrounding Elab computation first and splice the resulting 'Syntax' value (§21.1)"
            (tm1,) <$> freshMetaV ctx
      _ -> do
        tT <- quoteIn ctx ty1F
        errAt ssp "E_QUOTE_SPLICE_TYPE" (Just "kappa.syntax.quotation")
          ("a '${...}' splice inside a quote requires a 'Syntax' value; this expression has type " <> renderTerm tT <> " (§21.1)")
        (tm1,) <$> freshMetaV ctx
  -- type-directed payload checking sufficient to assign the Syntax
  -- index; the elaborated term is discarded (§21.1: quotation records
  -- syntax, final obligations are discharged at splice sites)
  let ctxQ = ctx {ctxQuoteSlots = Map.fromList (zip [0 ..] (map snd slots))}
  tV <- case mexp of
    Just t -> do
      _ <- check ctxQ payload t
      pure t
    Nothing -> do
      (tm0, ty0) <- infer ctxQ payload
      (_, ty1) <- insertAllImplicits ctxQ sp tm0 ty0
      pure ty1
  qs <- mkQuotedSyntax ctx payload sp
  pure (CQuote qs (map fst slots), synTV tV)

-- | Elaborate a §23.2 staged-code quotation @.< e >.@: if @e : t@ the
-- quote has type @Code t@. The interpreter models generative code by
-- its present-stage value ('__codeQuote'); captured present-stage
-- variables follow the §23.3 lift-based cross-stage persistence of a
-- simple variable occurrence (the value environment is captured, so
-- §23.7 scope safety holds by construction). The §12.3.2 escape rules
-- treat the quote like a closure over its payload ('Kappa.Usage').
elabCodeQuote :: Ctx -> Expr -> Span -> Maybe Value -> CheckM (Term, Value)
elabCodeQuote ctx e _sp mexp = do
  tV <- maybe (freshMetaV ctx) pure mexp
  tm <- check ctx {ctxCodeDepth = ctxCodeDepth ctx + 1} e tV
  pure (CApp Expl (CGlob (gPrel "__codeQuote")) tm, codeTV tV)

-- | Elaborate a §23.2 escape @.~c@: requires @c : Code t@ and an
-- enclosing code quote.
elabCodeEscape :: Ctx -> Expr -> Span -> CheckM (Term, Value)
elabCodeEscape ctx e sp = do
  when (ctxCodeDepth ctx == 0) $
    errAt sp "E_CODE_ESCAPE_OUTSIDE_QUOTE" (Just "kappa-hs.staging.escape")
      "the escape '.~c' splices a staged subterm and is only meaningful inside a '.< ... >.' code quote (§23.2)"
  tV <- freshMetaV ctx
  tm <- check ctx {ctxCodeDepth = max 0 (ctxCodeDepth ctx - 1)} e (codeTV tV)
  pure (CApp Expl (CGlob (gPrel "__codeEscape")) tm, tV)

codeTV :: Value -> Value
codeTV t = VGlobN (gPrel "Code") [(Expl, t)]

-- | §21.4 hygiene metadata: rename quote-site local references to
-- fresh hygienic spellings and record (spelling, original, level).
mkQuotedSyntax :: Ctx -> Expr -> Span -> CheckM QuotedSyntax
mkQuotedSyntax ctx payload sp = do
  let bound = boundNamesIn payload
      occ = nub [nameText n | n <- freeVarOccurrences payload]
      capturable =
        [ (nm, i)
        | nm <- occ
        , nm `notElem` bound
        , Just (i, _) <- [lookupCtx nm ctx]
        ]
  caps <- forM capturable $ \(nm, i) -> do
    h <- freshNameM (nm <> "__hyg")
    pure (QuoteCapture h nm (ctxLen ctx - 1 - i))
  let ren = Map.fromList [(qcOrig c, qcHyg c) | c <- caps]
  pure (QuotedSyntax (renameVarOccurrences ren payload) caps sp)

-- | Elaborate a splice @$(m)@ (§21.2): execute the elaboration-time
-- action and elaborate the produced syntax at the splice site.
elabSplice :: Ctx -> Expr -> Span -> Maybe Value -> CheckM (Term, Value)
elabSplice ctx me sp mexp = do
  tV <- maybe (freshMetaV ctx) forceM mexp
  let bail = (\t -> (t, tV)) <$> freshMeta
  phaseOk <- splicePhaseCheck ctx me
  if not phaseOk
    then bail
    else do
      rA <- trySpec (check ctx me (elabTV (synTV tV)))
      mtm <- case rA of
        Just tm -> pure (Just tm)
        Nothing -> do
          rB <- trySpec (check ctx me (synTV tV))
          case rB of
            Just tm -> pure (Just (elabPureTm tm))
            Nothing -> do
              r <- trySpec $ do
                (tm0, ty0) <- infer ctx me
                insertAllImplicits ctx sp tm0 ty0
              tyDesc <- case r of
                Just (_, ty) -> do
                  tT <- quoteIn ctx ty
                  pure ("; this expression has type " <> renderTerm tT)
                Nothing -> pure ""
              errAt sp "E_SPLICE_REQUIRES_SYNTAX" (Just "kappa-hs.syntax.splice")
                ("a splice '$(...)' requires an 'Elab (Syntax t)' action or a meta-phase 'Syntax t' value"
                   <> tyDesc <> " (§21.2)")
              pure Nothing
      case mtm of
        Nothing -> bail
        Just tm -> do
          v <- evalRT ctx tm
          res <- runElab ctx sp v
          case res of
            Left () -> bail
            Right sv -> do
              mtmS <- spliceSyntaxValue ctx sp tV sv
              case mtmS of
                Nothing -> bail
                Just tmS -> pure (tmS, tV)

-- | Elaborate a produced 'Syntax' value at a splice site (§21.2):
-- graft, validate hygiene, record the expansion, re-elaborate.
spliceSyntaxValue :: Ctx -> Span -> Value -> Value -> CheckM (Maybe Term)
spliceSyntaxValue ctx sp tV sv = do
  mq <- graftQuoteV ctx sp sv
  case mq of
    Nothing -> pure Nothing
    Just qs -> do
      ok <- validateCaptures ctx sp (qsCaptures qs)
      if not ok
        then pure Nothing
        else do
          let ctx' = extendHyg ctx (qsCaptures qs)
              back = Map.fromList [(qcHyg c, qcOrig c) | c <- qsCaptures qs]
          modify' $ \st ->
            st {csExpansions = Map.insert sp (renameVarOccurrences back (qsExpr qs)) (csExpansions st)}
          Just <$> check ctx' (qsExpr qs) tV

-- | The §21.6 convenience reflection queries that may be run directly
-- by the elaborator in ordinary term positions.
reflQueryNames :: [Text]
reflQueryNames = ["defEqSyntax", "headSymbolSyntax", "typeOfSyntax"]

-- | §21.6: delaborate a first-order TYPE term back to surface syntax (for
-- 'typeOfSyntax'). Covers the type-expression forms — universes, type
-- constructors/names, type application (implicit args inferred away),
-- saturated type-level constructors, and de Bruijn variables (resolved
-- through the binder stack, then the context). A form that is not a
-- first-order type expression yields Nothing, so the query fails gracefully
-- rather than fabricating syntax.
delaborateType :: Ctx -> Span -> Term -> Maybe Expr
delaborateType ctx dsp = go []
  where
    nm t = Name t dsp
    go env tm = case tm of
      CSort _ -> Just (EVar (nm "Type"))
      CGlob g -> Just (EVar (nm (gnameText g)))
      CVar i
        | i < length env -> Just (EVar (nm (env !! i)))
        | otherwise -> case drop (i - length env) (ctxEntries ctx) of
            (e : _) -> Just (EVar (nm (ceName e)))
            [] -> Nothing
      CApp Impl f _ -> go env f
      CApp Expl f a -> do
        fE <- go env f
        aE <- go env a
        pure (EApp fE [ArgExplicit aE])
      CCtor g args -> do
        argEs <- mapM (go env) args
        pure (foldl (\acc e -> EApp acc [ArgExplicit e]) (EVar (nm (gnameText g))) argEs)
      _ -> Nothing

-- | §21.6: the convenience reflection operations are elaboration-time
-- queries. In an 'Elab'-typed position an application is an ordinary
-- 'Elab' action; in any other position the elaborator runs the query
-- at the call site and residualizes its result (the standardized
-- queries consume only meta-phase 'Syntax' operands and answer with
-- portable first-order results, so no §21.2 generic coercion arises).
elabReflQuery :: Ctx -> Name -> [Arg] -> Maybe Value -> CheckM (Term, Value)
elabReflQuery ctx qn args mexp = do
  (fTm, fTy) <- infer ctx (EVar qn)
  (tm0, ty0) <- elabSpine ctx (nameSpan qn) fTm fTy args
  (tm1, ty1) <- insertAllImplicits ctx (nameSpan qn) tm0 ty0
  ty1F <- forceM ty1
  expElab <- case mexp of
    Nothing -> pure False
    Just e -> isElabHeaded <$> forceM e
  case ty1F of
    VGlobN (GName pm "Elab") [(_, rT)]
      | pm == preludeModule
      , CGlob (GName fm _) <- fTm
      , fm == preludeModule
      , not expElab -> do
          v <- evalRT ctx tm1
          res <- runElab ctx (nameSpan qn) v
          case res of
            Left () -> (,rT) <$> freshMeta
            Right rv -> do
              rTm <- quoteIn ctx rv
              pure (rTm, rT)
    _ -> pure (tm1, ty1F)
  where
    isElabHeaded = \case
      VGlobN (GName pm "Elab") _ | pm == preludeModule -> True
      _ -> False

-- | §21.6: elaborate a reflected syntax value at the current call site
-- (shared by the convenience reflection queries). Ill-scoped or
-- ill-typed payloads fail with ordinary structured diagnostics
-- (§21.6.1).
elabReflPayload :: Ctx -> Span -> Value -> CheckM (Maybe (Term, Ctx))
elabReflPayload ctx sp sv = do
  mq <- graftQuoteV ctx sp sv
  case mq of
    Nothing -> pure Nothing
    Just qs -> do
      ok <- validateCaptures ctx sp (qsCaptures qs)
      if not ok
        then pure Nothing
        else do
          let ctx' = extendHyg ctx (qsCaptures qs)
          -- a payload that elaborates as a type is reflected as the
          -- type expression (so 'defEqSyntax' relates a same-spelling
          -- data family's type facet to its rebound static object,
          -- §7.6); other payloads elaborate as ordinary terms
          mty <- trySpec (fst <$> inferType ctx' (qsExpr qs))
          case mty of
            Just tyTm -> pure (Just (tyTm, ctx'))
            Nothing -> do
              (tm0, ty0) <- infer ctx' (qsExpr qs)
              (tm1, _) <- insertAllImplicits ctx' sp tm0 ty0
              pure (Just (tm1, ctx'))

-- | The global declaration head of an elaborated core term, if any
-- (§21.6 'headSymbol': None for variables, binders, locals, and
-- literals).
headGlobalOf :: Term -> Maybe GName
headGlobalOf = \case
  CApp _ f _ -> headGlobalOf f
  CGlob g@(GName m _) | m /= primModule -> Just g
  CCtor g _ -> Just g
  _ -> Nothing

-- | A §21.6 'Symbol' value: resolved declaration identity.
symbolValue :: GName -> Value
symbolValue (GName (ModuleName segs) n) =
  VPrim "__symbolV" [VLit (LitStr (T.intercalate "." segs <> "::" <> n))]

-- | §21.9 phase check: object-phase runtime locals cannot enter an
-- elaboration-time splice argument (only meta-phase carriers may).
splicePhaseCheck :: Ctx -> Expr -> CheckM Bool
splicePhaseCheck ctx me = do
  let bound = boundNamesIn me
      occs =
        [ (n, i)
        | n <- freeVarOccurrences me
        , nameText n `notElem` bound
        , not (Map.member (nameText n) (ctxHyg ctx))
        , Just (i, _) <- [lookupCtx (nameText n) ctx]
        ]
  bad <- filterM (\(_, i) -> not <$> metaPhaseType (ceType (ctxEntries ctx !! i))) occs
  case bad of
    [] -> pure True
    ((n, _) : _) -> do
      errAt (nameSpan n) "E_ELAB_PHASE" (Just "kappa-hs.macro.phase")
        ("the object-phase runtime binding '" <> nameText n
           <> "' cannot be captured by an elaboration-time splice; object-phase terms enter 'Elab' only through meta-phase carriers such as 'Syntax' (§21.9)")
      pure False

-- | Is a local's type a meta-phase carrier admissible inside 'Elab'?
metaPhaseType :: Value -> CheckM Bool
metaPhaseType v = do
  t <- forceM v
  case t of
    -- type, row, quantity, and region parameters are erased
    -- classifier-level entities; mentioning them does not smuggle an
    -- object-phase runtime value into Elab (§21.9)
    VSort _ -> pure True
    VGlobN (GName pm g) args
      | pm == preludeModule
      , g `elem`
          [ "Syntax", "Elab", "SyntaxOrigin", "SyntaxFragment"
          , "RawComprehension", "ComprehensionPlan"
          , "RecRow", "EffRow", "Quantity", "Region", "EffLabel"
          ] ->
          pure True
      | pm == preludeModule
      , g `elem` ["List", "Option"]
      , ((_, a) : _) <- args ->
          metaPhaseType a
    VGlobN (GName m _) _ | m == shapeModule -> pure True
    _ -> pure False

-- | Graft a syntax value: force the slot values to quotes and
-- substitute them into the payload's grafting holes (§21.2).
graftQuoteV :: Ctx -> Span -> Value -> CheckM (Maybe QuotedSyntax)
graftQuoteV ctx sp v0 = do
  v <- forceRT v0
  case v of
    VQuote qs slots -> do
      subs <- mapM (graftQuoteV ctx sp) slots
      case sequence subs of
        Nothing -> pure Nothing
        Just qss ->
          pure $
            Just
              QuotedSyntax
                { qsExpr = substQuoteHoles (Map.fromList (zip [0 ..] (map qsExpr qss))) (qsExpr qs)
                , qsCaptures = qsCaptures qs ++ concatMap qsCaptures qss
                , qsSpan = qsSpan qs
                }
    _ -> do
      errAt sp "E_SPLICE_REQUIRES_SYNTAX" (Just "kappa-hs.syntax.splice")
        "the elaboration-time action did not produce a 'Syntax' value this implementation can splice (§21.2)"
      pure Nothing

-- | §21.4: every free hygienic binder of spliced syntax must still be
-- valid at the splice site.
validateCaptures :: Ctx -> Span -> [QuoteCapture] -> CheckM Bool
validateCaptures ctx sp caps = do
  let n = ctxLen ctx
      entryOk c =
        let i = n - 1 - qcLevel c
         in i >= 0 && i < n && ceName (ctxEntries ctx !! i) == qcOrig c
      bad = [c | c <- caps, not (entryOk c)]
  forM_ (take 1 bad) $ \c ->
    errAt sp "E_SYNTAX_SCOPE_ESCAPE" (Just "kappa-hs.syntax.scope-escape")
      ("this Syntax value mentions the local binder '" <> qcOrig c
         <> "' (or its borrow region) whose scope has ended; a Syntax value may escape a lexical scope only while every free hygienic binder it references remains valid, and splicing requires those binders at the splice site (§21.4)")
  pure (null bad)

extendHyg :: Ctx -> [QuoteCapture] -> Ctx
extendHyg ctx caps = ctx {ctxHyg = foldr ins (ctxHyg ctx) caps}
  where
    n = ctxLen ctx
    ins c m = case drop (n - 1 - qcLevel c) (ctxEntries ctx) of
      e : _ -> Map.insert (qcHyg c) (qcLevel c, ceType e) m
      [] -> m

-- | Run an elaboration-time action value (§21.9, §30.2.4): interpret
-- the stuck @__elab*@ primitive applications under CheckM.
runElab :: Ctx -> Span -> Value -> CheckM (Either () Value)
runElab ctx sp v0 = do
  v <- forceRT v0
  case v of
    VPrim "__elabPure" [x] -> pure (Right x)
    VPrim "__elabBind" [m, k] -> do
      r <- runElab ctx sp m
      case r of
        Left e -> pure (Left e)
        Right x -> runElab ctx sp =<< vappRT k [x]
    VPrim "renderSyntax" [s] -> do
      mq <- graftQuoteV ctx sp s
      pure $ case mq of
        Just qs -> Right (VLit (LitStr (renderExprSrc (qsExpr qs))))
        Nothing -> Left ()
    VPrim "syntaxOrigin" [s] -> do
      sV <- forceRT s
      let osp = case sV of
            VQuote qs _ -> qsSpan qs
            _ -> sp
      pure (Right (VPrim "__syntaxOriginV" [VLit (LitStr (T.pack (show osp)))]))
    VPrim "normalizeSyntax" [s] -> pure (Right s)
    VPrim "whnfSyntax" [s] -> pure (Right s)
    -- §21.6 'typeOfSyntax': elaborate the payload at the current call site,
    -- infer its type, and reify that type back to a 'Syntax Type' by
    -- delaborating the inferred type term to surface syntax. The query
    -- commits no constraints (state restored).
    VPrim "typeOfSyntax" [s] -> do
      mq <- graftQuoteV ctx sp s
      case mq of
        Nothing -> pure (Left ())
        Just qs -> do
          ok <- validateCaptures ctx sp (qsCaptures qs)
          if not ok
            then pure (Left ())
            else do
              let ctx' = extendHyg ctx (qsCaptures qs)
              st0 <- get
              mr <- trySpec (infer ctx' (qsExpr qs))
              put st0
              case mr of
                Nothing -> pure (Left ())
                Just (_, tyV) -> do
                  tyTm <- quoteIn ctx' tyV
                  case delaborateType ctx' (qsSpan qs) tyTm of
                    Just tyE -> pure (Right (VQuote (QuotedSyntax tyE [] (qsSpan qs)) []))
                    Nothing -> pure (Left ())
    -- §21.6 'defEqSyntax': elaborate both syntax values at the current
    -- call site and answer the same Boolean that 'defEq' would for the
    -- resulting cores; the query commits no constraints
    VPrim "defEqSyntax" [s1, s2] -> do
      m1 <- elabReflPayload ctx sp s1
      m2 <- elabReflPayload ctx sp s2
      case (m1, m2) of
        (Just (tm1, ctx1), Just (tm2, ctx2)) -> do
          st0 <- get
          v1 <- evalRT ctx1 tm1
          v2 <- evalRT ctx2 tm2
          eq <- unify ctx v1 v2
          put st0
          pure (Right (VCtor (gPrel (if eq then "True" else "False")) []))
        _ -> pure (Left ())
    -- §21.6 'headSymbolSyntax': Some s only when the elaborated core
    -- has a global declaration head ('sameSymbol' then compares
    -- resolved declaration identity, not spelling — a module alias
    -- path resolves to the same symbol)
    VPrim "headSymbolSyntax" [s] -> do
      m <- elabReflPayload ctx sp s
      pure $ case m of
        Nothing -> Left ()
        Just (tm, _) -> Right $ case headGlobalOf tm of
          Just g -> VCtor (gPrel "Some") [symbolValue g]
          Nothing -> VCtor (gPrel "None") []
    VPrim "withSyntaxOrigin" [_, s] -> pure (Right s)
    VPrim "warnElab" [m] -> do
      msg <- strValue m
      report (diag SevWarning StageElaborate "W_MACRO_DIAGNOSTIC" (Just "kappa.macro.failure") sp msg)
      pure (Right unitValue)
    VPrim "warnElabWith" [c, m, _] -> do
      code <- strValue c
      msg <- strValue m
      report (diag SevWarning StageElaborate code (Just "kappa.macro.failure") sp msg)
      pure (Right unitValue)
    VPrim "failElab" [m] -> do
      msg <- strValue m
      errAt sp "E_MACRO_FAILURE" (Just "kappa.macro.failure") msg
      pure (Left ())
    VPrim "failElabWith" [c, m, _] -> do
      code <- strValue c
      msg <- strValue m
      errAt sp code (Just "kappa.macro.failure") msg
      pure (Left ())
    VPrim "__stringSyntax" [s] -> do
      txt <- strValue s
      pure (Right (literalQuote (EStringLit (StringLit Nothing 0 False [FragLit txt]) [] sp)))
    VPrim "__natSyntax" [n] -> do
      nF <- forceRT n
      pure $ case nF of
        VLit (LitInt i) -> Right (literalQuote (EIntLit i Nothing sp))
        _ -> Right (literalQuote (EIntLit 0 Nothing sp))
    VPrim "__boolSyntax" [b] -> do
      bF <- forceRT b
      let nm = case bF of
            VCtor (GName _ "True") [] -> "True"
            _ -> "False"
      pure (Right (literalQuote (EVar (Name nm sp))))
    VPrim "__unitSyntax" [] -> pure (Right (literalQuote (EUnit sp)))
    VPrim "__shapeInspectAdt" [tyV, _] -> shapeInspectAdtOp ctx sp tyV
    VPrim "__shapeInspectRecord" [tyV, target] -> shapeInspectRecordOp ctx sp tyV target
    VPrim "__shapeRequireFieldInstances" [tcV, tyV, _] -> shapeRequireFieldsOp ctx sp tcV tyV
    VPrim "__shapeMatchAdt" [shapeV, scrutV, cb] -> shapeMatchAdtOp ctx sp shapeV scrutV cb
    VPrim "__shapeMatchAdt2" [shapeV, lV, rV, cbS, cbD] -> shapeMatchAdt2Op ctx sp shapeV lV rV cbS cbD
    _ -> do
      errAt sp "E_ELAB_STUCK" (Just "kappa.macro.failure")
        "this elaboration-time action could not be executed by the Elab evaluator (§21.9; see SPEC_COVERAGE.md for the provided subset)"
      pure (Left ())
  where
    literalQuote e = VQuote (QuotedSyntax e [] sp) []
    unitValue = VCtor (gPrel "Unit") []
    strValue x = do
      xF <- forceRT x
      pure $ case xF of
        VLit (LitStr s) -> s
        _ -> ""

-- | Elab-typed do blocks (§21.9): lower to '__elabBind' chains.
elabElabDo :: Ctx -> Value -> [DoItem] -> Span -> CheckM (Term, Value)
elabElabDo ctx0 aTy items0 sp = do
  tm <- go ctx0 items0
  pure (tm, elabTV aTy)
  where
    bindPrim m k = CApp Expl (CApp Expl (CGlob (GName primModule "__elabBind")) m) k
    badForm ctx isp rest = do
      errAt isp "E_ELAB_DO_FORM" (Just "kappa-hs.do.elab")
        "this do item form is not available in an 'Elab' do block (§21.9)"
      go ctx rest
    go ctx = \case
      [] -> do
        errAt sp "E_ELAB_DO_FORM" (Just "kappa-hs.do.elab")
          "an 'Elab' do block must end with an expression of the block's Elab type (§21.9)"
        freshMeta
      [DoExpr e] -> check ctx (desugarBang e) (elabTV aTy)
      [item] -> badForm ctx (doItemSpan item) []
      (item : rest) -> case item of
        DoExpr e -> do
          bTy <- freshMetaV ctx
          mTm <- check ctx (desugarBang e) (elabTV bTy)
          restTm <- go (bindCtx "_" False bTy ctx) rest
          pure (bindPrim mTm (CLam Expl QW "_" restTm))
        DoBind (LetBind _ _ pat mty rhs bsp) -> bindItem ctx pat mty rhs bsp rest
        DoAssign n True rhs asp -> bindItem ctx (PVar n) Nothing rhs asp rest
        DoAssign n False rhs asp -> letItem ctx (PVar n) Nothing rhs asp rest
        DoLet (LetBind _ _ pat mty rhs bsp) -> letItem ctx pat mty rhs bsp rest
        other -> badForm ctx (doItemSpan other) rest
    patBinder bsp = \case
      PVar n -> pure (nameText n)
      PWild _ -> pure "_"
      _ -> do
        errAt bsp "E_ELAB_DO_FORM" (Just "kappa-hs.do.elab")
          "only variable and wildcard binders are supported in 'Elab' do binds (§21.9)"
        pure "_"
    bindItem ctx pat mty rhs bsp rest = do
      bTy <- case mty of
        Just tyE -> do
          (tyTm, _) <- inferType ctx tyE
          evalIn ctx tyTm
        Nothing -> freshMetaV ctx
      rhsTm <- check ctx (desugarBang rhs) (elabTV bTy)
      nm <- patBinder bsp pat
      restTm <- go (bindCtx nm False bTy ctx) rest
      pure (bindPrim rhsTm (CLam Expl QW nm restTm))
    letItem ctx pat mty rhs bsp rest = do
      -- §18.3.1: a `let` RHS inside a do block may contain `!`; desugar it
      -- like bindItem so it is not rejected as a bare splice.
      let rhsD = desugarBang rhs
      (rhsTm, rhsTy) <- case mty of
        Just tyE -> do
          (tyTm, _) <- inferType ctx tyE
          tyV <- evalIn ctx tyTm
          tm <- check ctx rhsD tyV
          pure (tm, tyV)
        Nothing -> do
          (tm0, ty0) <- infer ctx rhsD
          insertAllImplicits ctx bsp tm0 ty0
      nm <- patBinder bsp pat
      rhsV <- evalIn ctx rhsTm
      restTm <- go (bindCtxLet nm False rhsTy rhsV ctx) rest
      tyTm' <- quoteIn ctx rhsTy
      pure (CLet QW nm tyTm' rhsTm restTm)

-- ── §22 Derivation-shape reflection ──────────────────────────────────

gShape :: Text -> GName
gShape = GName shapeModule

shapeFamily :: Maybe DiagnosticFamily
shapeFamily = Just "kappa.deriving.shape"

listValue :: [Value] -> Value
listValue = foldr (\x t -> VCtor (gPrel "::") [x, t]) (VCtor (gPrel "Nil") [])

valueList :: Value -> CheckM [Value]
valueList v = do
  vF <- forceRT v
  case vF of
    VCtor (GName _ "::") [h, t] -> (h :) <$> valueList t
    _ -> pure []

shapeFieldValue :: Maybe Text -> Int -> Value
shapeFieldValue mname i =
  VCtor
    (gShape "ShapeField")
    [ maybe (VCtor (gPrel "None") []) (\n -> VCtor (gPrel "Some") [VLit (LitStr n)]) mname
    , VLit (LitStr renderName)
    ]
  where
    renderName = fromMaybe ("_" <> T.pack (show (i + 1))) mname

-- | The §22.1 constructor summaries of a data type.
shapeCtorValues :: GName -> CheckM [Value]
shapeCtorValues g = do
  st <- get
  let ctorGs = maybe [] diCtors (Map.lookup g (csDatas st))
  pure
    [ VCtor
        (gShape "ShapeConstructor")
        [ VLit (LitStr (gnameText cg))
        , VLit (LitStr (gnameText cg))
        , VLit (LitInt (fromIntegral tag))
        , listValue
            [ shapeFieldValue mname i
            | (i, (mname, _)) <- zip [0 ..] (maybe [] ciFields (Map.lookup cg (csCtors st)))
            ]
        ]
    | (tag, cg) <- zip [0 :: Int ..] ctorGs
    ]

-- | §22.1 'inspectAdt': the inspected head must be a data type whose
-- representation is visible at this elaboration site.
shapeInspectAdtOp :: Ctx -> Span -> Value -> CheckM (Either () Value)
shapeInspectAdtOp _ctx sp tyV = do
  t <- forceRT tyV
  st <- get
  case t of
    VGlobN g _
      | Just di <- Map.lookup g (csDatas st) -> do
          let GName declMod _ = g
              opaque = Map.member g (csOpaqueDatas st)
          if opaque && declMod /= csModule st
            then do
              errAt sp "KAPPA_DERIVING_SHAPE_OPAQUE_REPRESENTATION" shapeFamily
                ("the representation of '" <> gnameText g
                   <> "' is opaque outside its defining module; shape inspection requires a representation ordinary code at this site could match on (§22.1)")
              pure (Left ())
            else do
              ctorVs <- shapeCtorValues g
              st' <- get
              let ctorGs = diCtors di
                  fieldCounts =
                    [maybe 0 (length . ciFields) (Map.lookup cg (csCtors st')) | cg <- ctorGs]
                  kindName
                    | length ctorGs == 1 = "ProductAdt"
                    | all (== 0) fieldCounts = "EnumAdt"
                    | otherwise = "SumAdt"
              pure $
                Right $
                  VCtor
                    (gShape "AdtShape")
                    [ VLit (LitStr (gnameText g))
                    , VLit (LitStr (gnameText g))
                    , VCtor (gShape "ShapeRepresentationVisible") []
                    , VCtor (gShape kindName) []
                    , listValue ctorVs
                    ]
    _ -> do
      tT <- quoteIn emptyCtx t
      errAt sp "KAPPA_DERIVING_SHAPE_NOT_DATA" shapeFamily
        ("shape inspection requires a data type; '" <> renderTerm tT <> "' is not one (§22.1)")
      pure (Left ())

-- | §22.1 'inspectRecord': closed records only; field order follows
-- the written order of the inspected alias when known (§22.2).
shapeInspectRecordOp :: Ctx -> Span -> Value -> Value -> CheckM (Either () Value)
shapeInspectRecordOp _ctx sp tyV target = do
  t <- forceRT tyV
  case t of
    VRecordT fs -> do
      written <- targetFieldOrder target
      let names = map fst fs
          ordered = case written of
            Just ws | sort ws == sort names -> ws
            _ -> names
      pure $
        Right $
          VCtor
            (gShape "RecordShape")
            [listValue [shapeFieldValue (Just nm) i | (i, nm) <- zip [0 ..] ordered]]
    VGlobN (GName pm "__openRec") _
      | pm == preludeModule -> do
          errAt sp "KAPPA_DERIVING_SHAPE_NOT_CLOSED_RECORD" shapeFamily
            "Phase 0 record shape inspection requires a closed record type; open record types are reserved for a later phase (§22.1)"
          pure (Left ())
    _ -> do
      tT <- quoteIn emptyCtx t
      errAt sp "KAPPA_DERIVING_SHAPE_NOT_CLOSED_RECORD" shapeFamily
        ("record shape inspection requires a closed record type; '" <> renderTerm tT <> "' is not one (§22.1)")
      pure (Left ())
  where
    targetFieldOrder tv = do
      tvF <- forceRT tv
      case tvF of
        VQuote qs _
          | EVar n <- qsExpr qs -> do
              mg <- lookupGlobalName (nameText n)
              case mg of
                Just g -> gets (Map.lookup g . csRecordOrders)
                Nothing -> pure Nothing
        _ -> pure Nothing

-- | §22.4 'requireRuntimeFieldInstances': probe ordinary implicit
-- resolution for @tc F@ at every constructor field type @F@.
shapeRequireFieldsOp :: Ctx -> Span -> Value -> Value -> CheckM (Either () Value)
shapeRequireFieldsOp ctx sp tcV tyV = do
  t <- forceRT tyV
  st <- get
  case t of
    VGlobN g _
      | Just di <- Map.lookup g (csDatas st) -> do
          fieldTys <- concat <$> mapM (ctorFieldTypesOf t) (diCtors di)
          missing <- filterM (fmap not . satisfiable) fieldTys
          case missing of
            [] -> pure (Right (VCtor (gPrel "Unit") []))
            ((cg, mname, fTy) : _) -> do
              fT <- quoteIn ctx fTy
              errAt sp "KAPPA_DERIVING_SHAPE_MISSING_RUNTIME_FIELD_INSTANCE" shapeFamily
                ("no instance satisfies the required trait obligation for field '"
                   <> fromMaybe "_" mname <> "' of constructor '" <> gnameText cg
                   <> "' (field type " <> renderTerm fT <> ") of data type '" <> gnameText g <> "' (§22.4)")
              pure (Left ())
    _ -> do
      errAt sp "KAPPA_DERIVING_SHAPE_NOT_DATA" shapeFamily
        "field-instance checking requires a data type shape (§22.4)"
      pure (Left ())
  where
    ctorFieldTypesOf tV cg = do
      st <- get
      case Map.lookup cg (csCtors st) of
        Nothing -> pure []
        Just ci -> do
          doms <- ctorFieldTypes ctx cg ci tV sp
          pure [(cg, mname, fTy) | ((mname, _), fTy) <- zip (ciFields ci) doms]
    satisfiable (_, _, fTy) = do
      ec <- ecRT_
      goal <- forceM (vapp ec tcV Expl fTy)
      r <- trySpec $ do
        mLoc <- localCandidate ctx sp Q0 goal
        case mLoc of
          Just _ -> pure True
          Nothing -> isJust <$> instanceSearch ctx sp goal
      pure (fromMaybe False r)

-- | Field arity of a shape-constructor summary value.
shapeCtorInfo :: Value -> CheckM (Text, Int, [Value])
shapeCtorInfo cv = do
  cvF <- forceRT cv
  case cvF of
    VCtor (GName _ "ShapeConstructor") [nmV, _, _, fieldsV] -> do
      nmF <- forceRT nmV
      let nm = case nmF of
            VLit (LitStr s) -> s
            _ -> "?"
      fields <- valueList fieldsV
      pure (nm, length fields, fields)
    _ -> pure ("?", 0, [])

-- | §22.5 'matchAdt': construct an exhaustive match over the
-- scrutinee syntax, one branch per constructor, branch bodies
-- produced by the elaboration-time callback.
shapeMatchAdtOp :: Ctx -> Span -> Value -> Value -> Value -> CheckM (Either () Value)
shapeMatchAdtOp ctx sp shapeV scrutV cb = do
  mscrut <- graftQuoteV ctx sp scrutV
  shapeF <- forceRT shapeV
  case (mscrut, shapeF) of
    (Just scrutQ, VCtor (GName _ "AdtShape") [_, _, _, _, ctorsV]) -> do
      ctorVs <- valueList ctorsV
      branches <- runBranches ctorVs scrutQ
      pure $ case branches of
        Nothing -> Left ()
        Just (cases, caps) ->
          Right $
            VQuote
              (QuotedSyntax (EMatch (qsExpr scrutQ) cases sp) (qsCaptures scrutQ ++ caps) sp)
              []
    _ -> do
      errAt sp "KAPPA_DERIVING_SHAPE_NOT_DATA" shapeFamily
        "matchAdt requires an inspected data shape (§22.5)"
      pure (Left ())
  where
    runBranches [] _ = pure (Just ([], []))
    runBranches (cv : rest) scrutQ = do
      (nm, arity, fields) <- shapeCtorInfo cv
      let boundFields = listValue [VCtor (gShape "BoundField") [f] | f <- fields]
      r <- runElab ctx sp =<< vappRT cb [cv, boundFields]
      case r of
        Left () -> pure Nothing
        Right bodyV -> do
          mbody <- graftQuoteV ctx sp bodyV
          case mbody of
            Nothing -> pure Nothing
            Just bodyQ -> do
              more <- runBranches rest scrutQ
              pure $ do
                (cases, caps) <- more
                let pat = PCtor (CtorRef Nothing (Name nm sp)) (replicate arity (PWild sp)) sp
                pure
                  ( MatchCase pat Nothing (qsExpr bodyQ) sp : cases
                  , qsCaptures bodyQ ++ caps
                  )

-- | §22.5 'matchAdt2': a tupled match comparing two values of the
-- same data type, same-constructor and different-constructor branches.
shapeMatchAdt2Op :: Ctx -> Span -> Value -> Value -> Value -> Value -> Value -> CheckM (Either () Value)
shapeMatchAdt2Op ctx sp shapeV lV rV cbSame cbDiff = do
  ml <- graftQuoteV ctx sp lV
  mr <- graftQuoteV ctx sp rV
  shapeF <- forceRT shapeV
  case (ml, mr, shapeF) of
    (Just lQ, Just rQ, VCtor (GName _ "AdtShape") [_, _, _, _, ctorsV]) -> do
      ctorVs <- valueList ctorsV
      let pairs = [(c1, c2) | c1 <- ctorVs, c2 <- ctorVs]
      branches <- runPairs pairs
      pure $ case branches of
        Nothing -> Left ()
        Just (cases, caps) ->
          -- close the tupled match with a catch-all duplicating the
          -- last different-constructor body, so exhaustiveness over
          -- the tuple scrutinee is syntactically evident (§22.5)
          let diffBodies =
                [ body
                | MatchCase (PTuple [PCtor c1 _ _, PCtor c2 _ _] _) _ body _ <- cases
                , nameText (crName c1) /= nameText (crName c2)
                ]
              catchAll = [MatchCase (PWild sp) Nothing b sp | b <- take 1 (reverse diffBodies)]
           in Right $
                VQuote
                  ( QuotedSyntax
                      (EMatch (ETuple [qsExpr lQ, qsExpr rQ] sp) (cases ++ catchAll) sp)
                      (qsCaptures lQ ++ qsCaptures rQ ++ caps)
                      sp
                  )
                  []
    _ -> do
      errAt sp "KAPPA_DERIVING_SHAPE_NOT_DATA" shapeFamily
        "matchAdt2 requires an inspected data shape (§22.5)"
      pure (Left ())
  where
    runPairs [] = pure (Just ([], []))
    runPairs ((c1, c2) : rest) = do
      (nm1, ar1, fields1) <- shapeCtorInfo c1
      (nm2, ar2, _) <- shapeCtorInfo c2
      r <-
        if nm1 == nm2
          then do
            let fieldPairs = listValue [VCtor (gShape "BoundFieldPair") [f] | f <- fields1]
            runElab ctx sp =<< vappRT cbSame [c1, fieldPairs]
          else runElab ctx sp =<< vappRT cbDiff [c1, c2]
      case r of
        Left () -> pure Nothing
        Right bodyV -> do
          mbody <- graftQuoteV ctx sp bodyV
          case mbody of
            Nothing -> pure Nothing
            Just bodyQ -> do
              more <- runPairs rest
              pure $ do
                (cases, caps) <- more
                let pat =
                      PTuple
                        [ PCtor (CtorRef Nothing (Name nm1 sp)) (replicate ar1 (PWild sp)) sp
                        , PCtor (CtorRef Nothing (Name nm2 sp)) (replicate ar2 (PWild sp)) sp
                        ]
                        sp
                pure
                  ( MatchCase pat Nothing (qsExpr bodyQ) sp : cases
                  , qsCaptures bodyQ ++ caps
                  )

-- ── Comprehensions (§20) ─────────────────────────────────────────────
--
-- Lowered per the §20.10 normative algebra, realized directly over
-- lists (the §20.10.11 as-if rule). A first pass infers the plan
-- (source kinds, use mode, cardinality, orderedness, row-entry
-- quantities) against a state snapshot; a second pass desugars to
-- surface syntax and elaborates once.

-- | How a generator source is iterated (§20.10.2 built-in obligations).
data SrcKind = SKList | SKArray | SKSet | SKMap | SKOption | SKQuery | SKRange | SKUnknown
  deriving stock (Eq, Show)

-- | Cardinality approximation (§20.10.1).
data QCard = CZero | COne | CZeroOrOne | COneOrMore | CZeroOrMore
  deriving stock (Eq, Show)

cardName :: QCard -> Text
cardName = \case
  CZero -> "QZero"
  COne -> "QOne"
  CZeroOrOne -> "QZeroOrOne"
  COneOrMore -> "QOneOrMore"
  CZeroOrMore -> "QZeroOrMore"

cardIv :: QCard -> (Int, Maybe Int)
cardIv = \case
  CZero -> (0, Just 0)
  COne -> (1, Just 1)
  CZeroOrOne -> (0, Just 1)
  COneOrMore -> (1, Nothing)
  CZeroOrMore -> (0, Nothing)

cardOf :: (Int, Maybe Int) -> QCard
cardOf = \case
  (0, Just 0) -> CZero
  (1, Just 1) -> COne
  (0, Just 1) -> CZeroOrOne
  (1, Nothing) -> COneOrMore
  _ -> CZeroOrMore

mulCard :: QCard -> QCard -> QCard
mulCard a b =
  let (al, ah) = cardIv a
      (bl, bh) = cardIv b
      hi = case (ah, bh) of
        (Just x, Just y) -> Just (min 1 (x * y))
        (Just 0, _) -> Just 0
        (_, Just 0) -> Just 0
        _ -> Nothing
   in cardOf (min 1 (al * bl), hi)

filterCard :: QCard -> QCard
filterCard c = let (_, h) = cardIv c in cardOf (0, h)

-- | May the inferred cardinality be checked against the demanded one
-- (interval subset, §20.10.1)?
cardSub :: QCard -> QCard -> Bool
cardSub a b =
  let (al, ah) = cardIv a
      (bl, bh) = cardIv b
      hiOk = case (ah, bh) of
        (_, Nothing) -> True
        (Just x, Just y) -> x <= y
        (Nothing, Just _) -> False
   in al >= bl && hiOk

cardManyHi :: QCard -> Bool
cardManyHi c = case snd (cardIv c) of
  Nothing -> True
  Just h -> h > 1

cardZeroLo :: QCard -> Bool
cardZeroLo c = fst (cardIv c) == 0

-- | What pass 1 learned about one generator source.
data SrcInfo = SrcInfo
  { siKind :: !SrcKind
  , siItem :: !Value
  , siOrdered :: !Bool
  , siOneShot :: !Bool
  , siCard :: !QCard
  , siItemLinear :: !Bool
  }

-- | Classify a do-block 'for' generator source by its inferred type,
-- rolling back ALL elaboration side effects (diagnostics, metavariables,
-- usage). The real elaboration of the source happens once afterwards, so
-- this probe must leave no trace (§12 usage analysis in particular must
-- see the source exactly once). A source whose type does not resolve to
-- a known collection carrier is reported as 'SKUnknown' and handled by
-- the ordinary 'List elemT' check, preserving the prior behaviour.
probeForSrcKind :: Ctx -> Expr -> CheckM SrcKind
probeForSrcKind ctx src = do
  st0 <- get
  n0 <- gets (length . csDiags)
  (_, srcTy) <- infer ctx src
  n1 <- gets (length . csDiags)
  k <-
    if n1 /= n0
      then pure SKUnknown -- inference failed; let the real check report it
      else siKind <$> sourceInfo ctx srcTy
  put st0 -- discard every side effect of the probe
  pure k

sourceInfo :: Ctx -> Value -> CheckM SrcInfo
sourceInfo ctx ty = do
  t <- forceM ty
  case t of
    VGlobN (GName _ "List") [(_, a)] -> pure (SrcInfo SKList a True False CZeroOrMore False)
    VGlobN (GName _ "Array") [(_, a)] -> pure (SrcInfo SKArray a True False CZeroOrMore False)
    VGlobN (GName _ "Set") [(_, a)] -> pure (SrcInfo SKSet a False False CZeroOrMore False)
    VGlobN (GName _ "Map") [(_, k), (_, v)] ->
      pure (SrcInfo SKMap (VRecordT [("key", k), ("value", v)]) False False CZeroOrMore False)
    VGlobN (GName _ "Option") [(_, a)] -> pure (SrcInfo SKOption a True False CZeroOrOne False)
    -- §20.2 range generator: a NumericRange iterates its ascending
    -- element stream (Reusable QZeroOrMore per the §23.7 IntoQuery
    -- instance for the canonical range type)
    VGlobN (GName _ "NumericRange") [(_, a)] -> pure (SrcInfo SKRange a True False CZeroOrMore False)
    VGlobN (GName _ "QueryCore") [(_, m), (_, q), (_, a)] -> do
      (oneShot, card) <- decodeQueryMode m
      lin <- decodeLinearQuantity q
      pure (SrcInfo SKQuery a True oneShot card lin)
    _ -> do
      item <- freshMetaV ctx
      pure (SrcInfo SKUnknown item True False CZeroOrMore False)

decodeQueryMode :: Value -> CheckM (Bool, QCard)
decodeQueryMode m0 = do
  m <- forceM m0
  case m of
    VCtor (GName _ "QueryMode") [u0, c0] -> do
      u <- forceM u0
      c <- forceM c0
      let oneShot = case u of
            VCtor (GName _ "OneShot") _ -> True
            _ -> False
          card = case c of
            VCtor (GName _ "QZero") _ -> CZero
            VCtor (GName _ "QOne") _ -> COne
            VCtor (GName _ "QZeroOrOne") _ -> CZeroOrOne
            VCtor (GName _ "QOneOrMore") _ -> COneOrMore
            _ -> CZeroOrMore
      pure (oneShot, card)
    _ -> pure (False, CZeroOrMore)

-- | Is the quantity value the linear quantity @1@?
decodeLinearQuantity :: Value -> CheckM Bool
decodeLinearQuantity q0 = do
  q <- forceM q0
  pure $ case q of
    VPrim "__quantityOfNat" [VLit (LitInt 1)] -> True
    _ -> False

-- | Does the variable occur (syntactically) in the expression?
occursVar :: Text -> Expr -> Bool
occursVar v = go
  where
    go = \case
      EVar (Name n _) -> n == v
      EApp f as -> go f || any goA as
      EDot b _ -> go b
      EQDot b _ -> go b
      EOpChain els -> or [go x | ChainOperand x <- els]
      ETuple es _ -> any go es
      ERecordLit is _ -> or [go e | RecItem _ _ (Just e) <- is]
      ERecordPatch b items _ ->
        go b
          || or
            [ case it of
                PatchUpdate _ (PatchValue e) -> go e
                PatchExtend _ e -> go e
                PatchSection a e -> go a || go e
                PatchPun _ -> False
            | it <- items
            ]
      EListLit es _ -> any go es
      ESetLit es _ -> any go es
      EMapLit kvs _ -> any (\(k, w) -> go k || go w) kvs
      EIf alts mels _ -> any (\(c, t) -> go c || go t) alts || maybe False go mels
      EMatch s cs _ -> go s || or [maybe False go g || go b | MatchCase _ g b _ <- cs]
      ELambda _ _ b _ -> go b
      ELet bs b _ -> any (go . lbExpr) bs || go b
      EAscription e _ _ -> go e
      ESectionLeft e _ _ -> go e
      ESectionRight _ e _ -> go e
      EElvis a b _ -> go a || go b
      EIs e _ -> go e
      EThunk e _ -> go e
      ELazy e _ -> go e
      EForce e _ -> go e
      EBang _ e _ -> go e
      EStringLit _ parts _ -> any (go . ipExpr) parts
      EDo _ items _ -> any goItem items
      EComprehension _ cls yy _ ->
        any goClause cls || any go (yieldExprsOf yy)
      _ -> False
    goA = \case
      ArgExplicit e -> go e
      ArgImplicit e -> go e
      ArgInout e _ -> go e
      ArgNamedBlock fs _ -> or [maybe False go me | (_, me) <- fs]
    goItem = \case
      DoBind lb -> go (lbExpr lb)
      DoLet lb -> go (lbExpr lb)
      DoLetQ _ e mfb _ -> go e || maybe False (go . snd) mfb
      DoExpr e -> go e
      _ -> True -- conservative for loops/var/defer items
    goClause = \case
      S.CFor _ _ _ src _ -> go src
      S.CLet _ _ _ rhs _ -> go rhs
      S.CIf e -> go e
      S.COrderBy ks _ -> any (go . snd) ks
      S.CSkip e _ -> go e
      S.CTake e _ -> go e
      S.CDistinct me _ -> maybe False go me
      S.CGroupBy k aggs _ _ -> go k || or [go e || maybe False go mu | (_, e, mu) <- aggs]
      S.CJoin _ _ src cond _ _ -> go src || go cond

yieldExprsOf :: CompYield -> [Expr]
yieldExprsOf = \case
  YieldExpr e -> [e]
  YieldPair k v -> [k, v]

-- | Surface pattern variables, in binding order.
surfPatVars :: Pattern -> [Name]
surfPatVars = \case
  PWild _ -> []
  PVar n -> [n]
  PLit _ _ -> []
  PAs n p -> n : surfPatVars p
  PCtor _ ps _ -> concatMap surfPatVars ps
  PCtorNamed _ fs _ -> concatMap surfPatVars [p | (_, Just p) <- fs]
  PActive _ _ p _ -> surfPatVars p
  PTuple ps _ -> concatMap surfPatVars ps
  PUnit _ -> []
  PRecord fs mrest _ ->
    concatMap (\(_, n, mp) -> maybe [n] surfPatVars mp) fs
      ++ [n | Just (PatRestBind n) <- [mrest]]
  PTyped p _ _ -> surfPatVars p
  POr ps _ -> case ps of
    (p : _) -> surfPatVars p
    [] -> []
  POpChain p chain _ -> surfPatVars p ++ concatMap (surfPatVars . snd) chain
  PVariant mb _ _ mrest _ -> maybe [] pure mb ++ maybe [] pure mrest

-- | Per-clause pass-1 annotation consumed by the desugaring pass.
data CAnn = CAnn
  { caKind :: !SrcKind -- ^ generator/join source kind
  , caForceRefut :: !Bool -- ^ desugar with a wildcard fallback case
  }

defaultAnn :: CAnn
defaultAnn = CAnn SKUnknown False

-- | Pass-1 result: plan metadata plus pending diagnostics.
data CompPlan = CompPlan
  { cpAnns :: ![CAnn]
  , cpOneShot :: !Bool
  , cpCard :: !QCard
  , cpItemLinear :: !Bool
  , cpDiags :: ![(Span, Text, Maybe Text, Text)]
  }

-- | Pass 1: infer the comprehension plan. Elaboration side effects
-- (diagnostics, metas) are rolled back; only the plan survives.
planComp :: Ctx -> [S.CompClause] -> CompYield -> Span -> CheckM CompPlan
planComp ctx0 clauses yld _sp = do
  st0 <- get
  plan <- go ctx0 [] True False COne [] [] clauses
  put st0
  pure plan
  where
    linsOf row = [v | (v, True) <- row]
    directComponent v = goD
      where
        goD = \case
          EVar (Name n _) -> n == v
          ETuple es _ -> any goD es
          ERecordLit is _ -> or [goD e | RecItem _ _ (Just e) <- is]
          EAscription e _ _ -> goD e
          _ -> False
    pend csp code fam msg = (csp, code, fam, msg)
    dropMsg what vs csp =
      pend csp "E_QUERY_ROW_NOT_DROPPABLE" (Just "kappa.quantity.unsatisfied")
        (what <> " may discard the current row, but linear row entry '"
           <> T.intercalate "', '" vs <> "' is not droppable (§20.10.4)")
    go _ctx row _ordered oneShot card anns diags [] = do
      -- the yielded item carries quantity 1 only when a linear row
      -- entry flows into it as a direct component (not when an
      -- application consumes the entry and yields its result)
      let lins = linsOf row
          itemLinear = not (null [v | v <- lins, any (directComponent v) (yieldExprsOf yld)])
      pure (CompPlan (reverse anns) oneShot card itemLinear (reverse diags))
    go ctx row ordered oneShot card anns diags (c : cs) = case c of
      S.CFor refut _ pat src csp -> do
        (_, srcTy) <- infer ctx src
        si <- sourceInfo ctx srcTy
        irr <- irrefutableFor ctx pat (siItem si)
        let lins = linsOf row
            refutD =
              [ pend csp "E_QUERY_FOR_REFUTABLE" (Just "kappa-hs.query.refutable-for")
                  "the pattern of a 'for' clause must be irrefutable for the element type; use the refutable form 'for?' instead (§20.4)"
              | not refut && not irr
              ]
            dropD = [dropMsg "the refutable generator 'for?'" lins csp | refut, not (null lins)]
            dupD =
              [ pend csp "E_QUERY_ROW_NOT_DUPLICABLE" (Just "kappa.quantity.unsatisfied")
                  ("a nested 'for' over a zero-or-many source may drop or duplicate the current row, but linear row entry '"
                     <> T.intercalate "', '" lins <> "' is neither droppable nor duplicable (§20.10.4)")
              | not refut
              , not (null lins)
              , cardManyHi (siCard si) || cardZeroLo (siCard si)
              ]
        (_, ctx', _) <- elabPattern ctx pat (siItem si)
        let row' = row ++ [(nameText n, siItemLinear si) | n <- surfPatVars pat]
        go ctx' row' (ordered && siOrdered si) (oneShot || siOneShot si)
          (mulCard card (siCard si))
          (CAnn (siKind si) (not irr) : anns)
          (reverse (refutD ++ dropD ++ dupD) ++ diags)
          cs
      S.CLet refut pat mty rhs csp -> do
        rhsTy <- case mty of
          Just tyE -> do
            (tyTm, _) <- inferType ctx tyE
            tyV <- evalIn ctx tyTm
            _ <- check ctx rhs tyV
            pure tyV
          Nothing -> snd <$> infer ctx rhs
        irr <- irrefutableFor ctx pat rhsTy
        let lins = linsOf row
            refutD =
              [ pend csp "E_REFUTABLE_LET_PATTERN" (Just "kappa-hs.pattern.refutable-binding")
                  "a 'let' comprehension clause requires an irrefutable pattern; use 'let?' instead (§20.4.1)"
              | not refut && not irr
              ]
            dropD = [dropMsg "the refutable binding 'let?'" lins csp | refut, not (null lins)]
        (_, ctx', _) <- elabPattern ctx pat rhsTy
        let row' = row ++ [(nameText n, False) | n <- surfPatVars pat]
        go ctx' row' ordered oneShot (if refut then filterCard card else card)
          (CAnn SKUnknown (not irr) : anns)
          (reverse (refutD ++ dropD) ++ diags)
          cs
      S.CIf cond -> do
        let lins = linsOf row
            dropD =
              [ pend (exprSpan cond) "E_QUERY_ROW_NOT_DROPPABLE" (Just "kappa.quantity.unsatisfied")
                  ("an 'if' filter may drop the current row, but linear row entry '"
                     <> T.intercalate "', '" lins <> "' is not droppable (§20.10.4)")
              | not (null lins)
              ]
        go ctx row ordered oneShot (filterCard card) (defaultAnn : anns) (dropD ++ diags) cs
      S.COrderBy keys csp -> do
        let lins = linsOf row
        consumed <- concat <$> mapM (consumesLin ctx lins . snd) keys
        let consD =
              [ pend csp "E_QUERY_ORDER_KEY_CONSUMES" (Just "kappa-hs.query.order-key")
                  ("an 'order by' key is checked in a non-consuming context, but this key consumes linear row entry '"
                     <> T.intercalate "', '" (nub consumed) <> "' (§20.6.1)")
              | not (null consumed)
              ]
        go ctx row True oneShot card (defaultAnn : anns) (consD ++ diags) cs
      S.CSkip _ csp -> pagingClause ctx row ordered oneShot card anns diags cs "skip" csp
      S.CTake _ csp -> pagingClause ctx row ordered oneShot card anns diags cs "take" csp
      S.CDistinct _ csp -> do
        let lins = linsOf row
            dropD = [dropMsg "'distinct' deduplication" lins csp | not (null lins)]
        go ctx row ordered oneShot (filterCard card) (defaultAnn : anns) (dropD ++ diags) cs
      S.CGroupBy key aggs n csp -> do
        (_, kTy) <- infer ctx key
        aggTys <- forM aggs $ \(an, ae, _) -> do
          (_, aTy) <- infer ctx ae
          pure (nameText an, aTy)
        let keyD =
              [ pend csp "E_QUERY_GROUP_KEY_FIELD" (Just "kappa-hs.query.group")
                  "the group record always contains the field 'key'; an aggregate may not be named 'key' (§20.7)"
              | any ((== "key") . fst) aggTys
              ]
            recTy = VRecordT (sortOn fst (("key", kTy) : aggTys))
            ctx' = bindCtx (nameText n) False recTy ctx
        go ctx' [(nameText n, False)] False oneShot CZeroOrMore (defaultAnn : anns) (keyD ++ diags) cs
      S.CJoin left pat src cond mInto csp -> do
        (_, srcTy) <- infer ctx src
        si <- sourceInfo ctx srcTy
        let lins = linsOf row
        case (left, mInto) of
          (True, Just into) -> do
            let captured = [v | v <- lins, occursVar v src || occursVar v cond]
                capD =
                  [ pend csp "E_QUERY_LEFT_JOIN_LINEAR_CAPTURE" (Just "kappa-hs.query.left-join")
                      ("the delayed inner query of a 'left join ... into' may not capture linear row entry '"
                         <> T.intercalate "', '" captured <> "' (§20.8)")
                  | not (null captured)
                  ]
                qTy =
                  VGlobN (gPrel "QueryCore")
                    [ (Expl, VCtor (gPrel "QueryMode") [VCtor (gPrel "Reusable") [], VCtor (gPrel "QZeroOrMore") []])
                    , (Expl, VPrim "__omegaQ" [])
                    , (Expl, siItem si)
                    ]
                ctx' = bindCtx (nameText into) False qTy ctx
                row' = row ++ [(nameText into, False)]
            go ctx' row' (ordered && siOrdered si) (oneShot || siOneShot si) card
              (CAnn (siKind si) False : anns) (capD ++ diags) cs
          _ -> do
            let dupD =
                  [ pend csp "E_QUERY_ROW_NOT_DUPLICABLE" (Just "kappa.quantity.unsatisfied")
                      ("a 'join' may drop or duplicate the current row, but linear row entry '"
                         <> T.intercalate "', '" lins <> "' is neither droppable nor duplicable (§20.10.4)")
                  | not (null lins)
                  ]
            (_, ctx', _) <- elabPattern ctx pat (siItem si)
            let row' = row ++ [(nameText nm, siItemLinear si) | nm <- surfPatVars pat]
            go ctx' row' (ordered && siOrdered si) (oneShot || siOneShot si)
              (mulCard card (filterCard (siCard si)))
              (CAnn (siKind si) False : anns) (dupD ++ diags) cs
    pagingClause ctx row ordered oneShot card anns diags cs what csp = do
      let lins = linsOf row
          ordD =
            [ pend csp "E_QUERY_UNORDERED_PAGING" (Just "kappa.query.orderedness")
                ("'" <> what <> "' requires an Ordered pipeline, but the pipeline is unordered here; insert an 'order by' before paging (§20.6.2)")
            | not ordered
            ]
          dropD = [dropMsg ("'" <> what <> "' paging") lins csp | not (null lins)]
      go ctx row ordered oneShot (filterCard card) (defaultAnn : anns) (ordD ++ dropD ++ diags) cs

-- | Which linear row entries does an ordering/distinct key expression
-- consume? Direct arguments at borrow-or-unrestricted callee binders
-- are non-consuming; quantity-1/>=1 binders and bare moves consume.
consumesLin :: Ctx -> [Text] -> Expr -> CheckM [Text]
consumesLin _ [] _ = pure []
consumesLin ctx lins e0 = case e0 of
  EVar (Name v _) -> pure [v | v `elem` lins]
  EDot b _ -> case b of
    EVar _ -> pure [] -- borrowed place read (§12.4 approximation)
    _ -> consumesLin ctx lins b
  EAscription e _ _ -> consumesLin ctx lins e
  EApp (EVar f) args -> do
    st0 <- get
    (_, fTy0) <- resolveName ctx f
    fTy <- forceM fTy0
    put st0
    let explQs = piExplQs fTy
        explArgs = [e | ArgExplicit e <- args]
        slot (mq, arg) = case arg of
          EVar (Name v _)
            | v `elem` lins ->
                pure [v | mq `elem` [Just Q1, Just QGe1, Nothing]]
          _ -> consumesLin ctx lins arg
    concat <$> mapM slot (zip (map Just explQs ++ repeat Nothing) explArgs)
  _ -> pure [v | v <- lins, occursVar v e0]
  where
    piExplQs ty = case ty of
      VPi Expl q _ _ clo -> q : piExplQs (peek clo)
      VPi Impl _ _ _ clo -> piExplQs (peek clo)
      _ -> []
    -- peeking under the binder with a dummy is enough for quantities
    peek (Closure env body) =
      eval (EvalCtx (Globals Map.empty) Map.empty False Map.empty) (VSort 0 : env) body

-- | The elaborated carrier prefix of a prefixed comprehension (§20.9):
-- the prefix term and its (forced) type.
type CarrierPrefix = (Term, Value)

elabComprehension :: Ctx -> CompKind -> [S.CompClause] -> CompYield -> Span -> CheckM (Term, Value)
elabComprehension ctx kind clauses yld sp = elabComprehensionC ctx kind clauses yld sp Nothing

elabComprehensionC :: Ctx -> CompKind -> [S.CompClause] -> CompYield -> Span -> Maybe CarrierPrefix -> CheckM (Term, Value)
elabComprehensionC ctx kind clauses yld sp mCarrier = do
  plan <- planComp ctx clauses yld sp
  forM_ (cpDiags plan) $ \(dsp, code, fam, msg) -> errAt dsp code fam msg
  lowered <- desugarComp ctx (zip clauses (cpAnns plan ++ repeat defaultAnn)) yld sp
  case mCarrier of
    Just prefix -> collectCarrier ctx kind plan lowered prefix sp
    Nothing -> case kind of
      CompList -> infer ctx lowered
      CompSet -> do
        eqLam <- pairEqLam sp
        infer ctx (prelApp1 sp "__setFromList" [prelApp1 sp "__distinctBy" [lowered, eqLam]])
      CompMap mconf -> do
        eqLam <- pairEqLam sp
        comb <- conflictLam ctx mconf sp
        infer ctx (prelApp1 sp "__mapFromEntries" [prelApp1 sp "__mapResolve" [lowered, eqLam, comb]])
      CompCarrier _ -> infer ctx lowered

prelApp1 :: Span -> Text -> [Expr] -> Expr
prelApp1 sp n es = EApp (EVar (Name n sp)) (map ArgExplicit es)

-- | @\\a b -> a == b@.
pairEqLam :: Span -> CheckM Expr
pairEqLam sp = do
  a <- freshNameM "__a"
  b <- freshNameM "__b"
  let an = Name a sp
      bn = Name b sp
  pure $
    ELambda Nothing [simpleBinder an, simpleBinder bn]
      (EApp (EOpRef Nothing (Name "==" sp) sp) [ArgExplicit (EVar an), ArgExplicit (EVar bn)])
      sp

-- | The map-conflict combine function (§20.5.1); default keep last.
conflictLam :: Ctx -> Maybe OnConflict -> Span -> CheckM Expr
conflictLam ctx mconf sp = case fromMaybe KeepLast mconf of
  KeepLast -> two (\_ b -> EVar b)
  KeepFirst -> two (\a _ -> EVar a)
  CombineWith f -> pure f
  CombineUsing w -> case ctorRefOfExpr w of
    Just cref -> do
      a <- freshNameM "__old"
      b <- freshNameM "__new"
      x <- freshNameM "__x"
      let an = Name a sp
          bn = Name b sp
          xn = Name x sp
          wrap e = EApp w [ArgExplicit e]
          appended = prelApp1 sp "append" [wrap (EVar an), wrap (EVar bn)]
      pure $
        ELambda Nothing [simpleBinder an, simpleBinder bn]
          (EMatch appended [MatchCase (PCtor cref [PVar xn] sp) Nothing (EVar xn) sp] sp)
          sp
    Nothing -> do
      _ <- unsupported ctx sp "this 'combine using' wrapper form"
      two (\_ b -> EVar b)
  where
    two f = do
      a <- freshNameM "__old"
      b <- freshNameM "__new"
      let an = Name a sp
          bn = Name b sp
      pure (ELambda Nothing [simpleBinder an, simpleBinder bn] (f an bn) sp)

ctorRefOfExpr :: Expr -> Maybe CtorRef
ctorRefOfExpr = \case
  EVar n -> Just (CtorRef Nothing n)
  EDot (EVar q) (DotName n) -> Just (CtorRef (Just q) n)
  _ -> Nothing

-- | Speculatively elaborate the head of a possible carrier-prefixed
-- comprehension (§20.9). 'Just' when the prefix is type-valued: either
-- a fully applied result type or a unary @Type -> Type@ sink head. The
-- caller restores elaboration state when this returns 'Nothing'.
carrierPrefix :: Ctx -> Expr -> [Arg] -> CheckM (Maybe CarrierPrefix)
carrierPrefix ctx f preArgs = do
  let headE = if null preArgs then f else EApp f preArgs
  case f of
    EVar _ -> goInfer headE
    EDot _ _ -> goInfer headE
    EApp _ _ -> goInfer headE
    _ -> pure Nothing
  where
    goInfer headE = do
      n0 <- gets (length . csDiags)
      -- §7.2: a carrier prefix is a type expression, so a same-spelling
      -- data family selects its TYPE facet (inferT), not the constructor
      (hTm, hTy) <- inferT ctx headE
      n1 <- gets (length . csDiags)
      hTy' <- forceM hTy
      if n1 /= n0
        then pure Nothing
        else case hTy' of
          VSort _ -> pure (Just (hTm, hTy'))
          VPi Expl _ _ dom _ -> do
            domF <- forceM dom
            case domF of
              VSort _ -> pure (Just (hTm, hTy'))
              _ -> pure Nothing
          _ -> pure Nothing

-- | Terminal collection through an explicit carrier prefix (§20.9).
collectCarrier :: Ctx -> CompKind -> CompPlan -> Expr -> CarrierPrefix -> Span -> CheckM (Term, Value)
collectCarrier ctx kind plan lowered (prefTm, prefTy) sp = do
  (listTm0, listTy) <- infer ctx lowered
  itemV <- elemOfList listTy
  candidate <- case prefTy of
    VSort _ -> evalIn ctx prefTm
    VPi Expl _ _ _ _ -> do
      itemTm <- quoteIn ctx itemV
      evalIn ctx (CApp Expl prefTm itemTm)
    _ -> freshMetaV ctx
  cand <- forceM candidate
  -- §20.9 custom sinks: a FromComprehensionRaw instance is preferred
  -- over FromComprehensionPlan; both run their Elab hook here
  mSink <- sinkHook cand itemV
  case mSink of
    Just r -> pure r
    Nothing -> builtinCarrier listTm0 listTy itemV candidate cand
  where
    sinkHook cand itemV = do
      mRaw <- trySpec (instanceSearch ctx sp (VGlobN (gPrel "FromComprehensionRaw") [(Expl, cand)]))
      mPlan <-
        case mRaw of
          Just (Just _) -> pure Nothing
          _ -> trySpec (instanceSearch ctx sp (VGlobN (gPrel "FromComprehensionPlan") [(Expl, cand)]))
      let chosen = case (mRaw, mPlan) of
            (Just (Just dict), _) -> Just (dict, "fromComprehensionRaw", "__rawComprehension")
            (_, Just (Just dict)) -> Just (dict, "fromComprehensionPlan", "__comprehensionPlan")
            _ -> Nothing
      case chosen of
        Nothing -> pure Nothing
        Just (dictTm, method, token) -> do
          ec <- ecRT_
          dictV <- evalRT ctx dictTm
          -- the associated Item must be definitionally equal to the
          -- normalized yielded item type (§20.9)
          let itemMember = vproj ec dictV "Item"
          okItem <- unify ctx itemMember itemV
          if not okItem
            then do
              iT <- quoteIn ctx =<< forceM itemMember
              yT <- quoteIn ctx =<< forceM itemV
              errAt sp "E_SINK_ITEM_MISMATCH" (Just "kappa-hs.query.sink")
                ("the selected sink's associated 'Item' type '" <> renderTerm iT
                   <> "' is not definitionally equal to the yielded item type '" <> renderTerm yT <> "' (§20.9)")
              Just <$> anyHole ctx
            else do
              action <- vappRT (vproj ec dictV method) [VPrim token []]
              res <- runElab ctx sp action
              case res of
                Left () -> Just <$> anyHole ctx
                Right sv -> do
                  mtm <- spliceSyntaxValue ctx sp cand sv
                  case mtm of
                    Nothing -> Just <$> anyHole ctx
                    Just tm -> pure (Just (tm, cand))
    builtinCarrier listTm0 listTy _itemV candidate cand = case cand of
      VGlobN (GName _ "QueryCore") [(_, m), (_, q), (_, a)] -> do
        -- §20.9: the Query carriers cannot silently discard map/set
        -- collection metadata
        case kind of
          CompMap _ -> do
            errAt sp "E_QUERY_METADATA_LOSS" (Just "kappa-hs.query.sink")
              "a 'Query { ... }' map comprehension is ill-formed: the Query carrier would silently discard the map metadata (§20.9)"
          CompSet -> do
            errAt sp "E_QUERY_METADATA_LOSS" (Just "kappa-hs.query.sink")
              "a 'Query {| ... |}' set comprehension is ill-formed: the Query carrier would silently discard the set metadata (§20.9)"
          _ -> pure ()
        (expOneShot, expCard) <- decodeQueryMode m
        expLinear <- decodeLinearQuantity q
        when (cpOneShot plan && not expOneShot) $
          errAt sp "E_QUERY_MODE_MISMATCH" (Just "kappa-hs.query.mode")
            "this comprehension's plan is one-shot, but the carrier requires a reusable query; use 'OnceQuery [ ... ]' or an explicitly indexed 'QueryCore' carrier (§20.9)"
        unless (cardSub (cpCard plan) expCard) $
          errAt sp "E_QUERY_CARDINALITY_MISMATCH" (Just "kappa-hs.query.cardinality")
            ("the inferred plan cardinality " <> cardName (cpCard plan)
               <> " cannot be checked against the demanded cardinality " <> cardName expCard
               <> "; cardinality may only be widened (§20.10.1)")
        when (cpItemLinear plan && not expLinear) $
          errAt sp "E_QUERY_ITEM_QUANTITY_MISMATCH" (Just "kappa-hs.query.item-quantity")
            "the yielded item is available only at linear quantity 1, but the carrier demands unrestricted (ω) items (§20.9)"
        listTm <- checkAsList listTm0 listTy a
        pure (CApp Expl (CGlob (gPrel "__queryFromList")) listTm, candidate)
      VGlobN (GName _ "Array") [(_, a)] -> do
        listTm <- checkAsList listTm0 listTy a
        pure (CApp Expl (CGlob (gPrel "__arrayFromList")) listTm, candidate)
      VGlobN (GName _ "List") [(_, a)] -> do
        listTm <- checkAsList listTm0 listTy a
        pure (listTm, candidate)
      VGlobN (GName _ "Set") [(_, a)] -> do
        listTm <- checkAsList listTm0 listTy a
        pure (CApp Expl (CGlob (gPrel "__setFromList")) listTm, candidate)
      _ -> unsupported ctx sp "this comprehension carrier"
    elemOfList ty = do
      t <- forceM ty
      case t of
        VGlobN (GName _ "List") [(_, a)] -> pure a
        _ -> freshMetaV ctx
    checkAsList tm ty a = do
      expectType ctx sp ty (VGlobN (gPrel "List") [(Expl, a)])
      pure tm

-- | Pass 2: desugar the clause pipeline over lists (§20.10.11 as-if).
-- The pipeline expression has type @List Row@ where @Row@ is the tuple
-- of the variables bound so far.
desugarComp :: Ctx -> [(S.CompClause, CAnn)] -> CompYield -> Span -> CheckM Expr
desugarComp ctx clauses yld sp = do
  (vars, pipe) <- foldM step ([], EListLit [EUnit sp] sp) clauses
  yf <- perRow vars (yieldElem yld)
  pure (prelApp1 sp "__pipeMap" [pipe, yf])
  where
    yieldElem = \case
      YieldExpr e -> e
      YieldPair k v ->
        ERecordLit [RecItem False (Name "key" sp) (Just k), RecItem False (Name "value" sp) (Just v)] sp

    rowE vars = case vars of
      [] -> EUnit sp
      [v] -> EVar v
      vs -> ETuple (map EVar vs) sp
    rowP vars = case vars of
      [] -> PWild sp
      [v] -> PVar v
      vs -> PTuple (map PVar vs) sp

    perRow vars body = do
      r <- freshNameM "__row"
      let rn = Name r sp
      pure $
        ELambda Nothing [simpleBinder rn]
          (EMatch (EVar rn) [MatchCase (rowP vars) Nothing body sp] sp)
          sp

    cmap f l = prelApp1 sp "__pipeConcatMap" [l, f]

    wrapSrc k src = case k of
      SKQuery -> prelApp1 sp "__queryToList" [src]
      SKSet -> prelApp1 sp "__setToList" [src]
      SKMap -> prelApp1 sp "__mapToList" [src]
      SKOption -> prelApp1 sp "__optionToList" [src]
      SKArray -> prelApp1 sp "__arrayToList" [src]
      SKRange -> prelApp1 sp "rangeToList" [src]
      _ -> src

    -- element function: match one element against the pattern, emit
    -- the extended row on success (wildcard fallback when filtering)
    elemLam pat filtering successBody = do
      el <- freshNameM "__el"
      let en = Name el sp
          cases =
            MatchCase pat Nothing successBody sp
              : [MatchCase (PWild sp) Nothing (EListLit [] sp) sp | filtering]
      pure (ELambda Nothing [simpleBinder en] (EMatch (EVar en) cases sp) sp)

    step (vars, pipe) (clause, ann) = case clause of
      S.CFor refut _ pat src _ -> do
        let vars' = vars ++ surfPatVars pat
            filtering = refut || caForceRefut ann
        ef <- elemLam pat filtering (EListLit [rowE vars'] sp)
        f <- perRow vars (cmap ef (wrapSrc (caKind ann) src))
        pure (vars', cmap f pipe)
      S.CLet refut pat mty rhs _ -> do
        let vars' = vars ++ surfPatVars pat
            filtering = refut || caForceRefut ann
            rhs' = maybe rhs (\t -> EAscription rhs t sp) mty
            cases =
              MatchCase pat Nothing (EListLit [rowE vars'] sp) sp
                : [MatchCase (PWild sp) Nothing (EListLit [] sp) sp | filtering]
        f <- perRow vars (EMatch rhs' cases sp)
        pure (vars', cmap f pipe)
      S.CIf cond -> do
        f <- perRow vars (EIf [(cond, EListLit [rowE vars] sp)] (Just (EListLit [] sp)) sp)
        pure (vars, cmap f pipe)
      S.COrderBy keys _ -> do
        -- decorate-sort-undecorate: pair each row with its key tuple,
        -- stably sort on the keys, then drop the decoration (§20.6.1)
        let keyTuple = case keys of
              [(_, k)] -> k
              _ -> ETuple (map snd keys) sp
        deco <- perRow vars (ETuple [keyTuple, rowE vars] sp)
        cmp <- decoCmpLam keys
        und <- undecorateLam
        pure
          ( vars
          , prelApp1 sp "__pipeMap"
              [prelApp1 sp "__sortBy" [prelApp1 sp "__pipeMap" [pipe, deco], cmp], und]
          )
      S.CSkip n _ -> pure (vars, prelApp1 sp "__listDrop" [n, pipe])
      S.CTake n _ -> pure (vars, prelApp1 sp "__listTake" [n, pipe])
      S.CDistinct Nothing _ -> do
        eqLam <- rowEqLam vars
        pure (vars, prelApp1 sp "__distinctBy" [pipe, eqLam])
      S.CDistinct (Just k) _ -> do
        -- decorate with the key, dedupe on it via Eq, undecorate
        deco <- perRow vars (ETuple [k, rowE vars] sp)
        pure (vars, prelApp1 sp "__distinctOnFst" [prelApp1 sp "__pipeMap" [pipe, deco]])
      S.CGroupBy key aggs n _ -> do
        kf <- perRow vars key
        eqLam <- pairEqLam sp
        let groups = prelApp1 sp "__groupBy" [pipe, kf, eqLam]
        g <- freshNameM "__g"
        let gn = Name g sp
            gRows = EDot (EVar gn) (DotName (Name "rows" sp))
        aggItems <- forM aggs $ \(an, ae, mUsing) -> do
          valF <- perRow vars ae
          body <- case mUsing of
            Nothing -> pure (prelApp1 sp "__aggFold" [gRows, valF])
            Just w -> case ctorRefOfExpr w of
              Just cref -> do
                r <- freshNameM "__r"
                x <- freshNameM "__x"
                let rn = Name r sp
                    xn = Name x sp
                    wrapF =
                      ELambda Nothing [simpleBinder rn]
                        (EApp w [ArgExplicit (EApp valF [ArgExplicit (EVar rn)])])
                        sp
                    folded = prelApp1 sp "__aggFold" [gRows, wrapF]
                pure (EMatch folded [MatchCase (PCtor cref [PVar xn] sp) Nothing (EVar xn) sp] sp)
              Nothing -> do
                _ <- unsupported ctx (exprSpan w) "this aggregate 'using' wrapper form"
                pure (prelApp1 sp "__aggFold" [gRows, valF])
          pure (RecItem False an (Just body))
        let rec' =
              ERecordLit
                (RecItem False (Name "key" sp) (Just (EDot (EVar gn) (DotName (Name "key" sp)))) : aggItems)
                sp
            gLam = ELambda Nothing [simpleBinder gn] rec' sp
        pure ([n], prelApp1 sp "__pipeMap" [groups, gLam])
      S.CJoin True pat src cond (Just into) _ -> do
        let vars' = vars ++ [into]
        ef <- elemLamKeep pat cond
        let matches = cmap ef (wrapSrc (caKind ann) src)
            qVal = prelApp1 sp "__queryOfMatches" [matches]
            inner = ELet [LetBind False emptyPrefix (PVar into) Nothing qVal sp] (EListLit [rowE vars'] sp) sp
        f <- perRow vars inner
        pure (vars', cmap f pipe)
      S.CJoin _ pat src cond _ _ -> do
        let vars' = vars ++ surfPatVars pat
        ef <- elemLam pat True (EIf [(cond, EListLit [rowE vars'] sp)] (Just (EListLit [] sp)) sp)
        f <- perRow vars (cmap ef (wrapSrc (caKind ann) src))
        pure (vars', cmap f pipe)

    -- left join: keep the matching element itself (§20.8)
    elemLamKeep pat cond = do
      el <- freshNameM "__el"
      let en = Name el sp
          succBody = EIf [(cond, EListLit [EVar en] sp)] (Just (EListLit [] sp)) sp
          cases =
            [ MatchCase pat Nothing succBody sp
            , MatchCase (PWild sp) Nothing (EListLit [] sp) sp
            ]
      pure (ELambda Nothing [simpleBinder en] (EMatch (EVar en) cases sp) sp)

    -- row equality: componentwise (==) over the row tuple (§20.6.3)
    rowEqLam vars = do
      ra <- freshNameM "__ra"
      rb <- freshNameM "__rb"
      asV <- mapM (const (freshNameM "__qa")) vars
      bsV <- mapM (const (freshNameM "__qb")) vars
      let ran = Name ra sp
          rbn = Name rb sp
          aNames = map (`Name` sp) asV
          bNames = map (`Name` sp) bsV
          eqOne a b = EApp (EOpRef Nothing (Name "==" sp) sp) [ArgExplicit (EVar a), ArgExplicit (EVar b)]
          trueE = EVar (Name "True" sp)
          falseE = EVar (Name "False" sp)
          conj = foldr (\(a, b) acc -> EIf [(eqOne a b, acc)] (Just falseE) sp) trueE (zip aNames bNames)
          body =
            EMatch (EVar ran)
              [MatchCase (rowP aNames) Nothing (EMatch (EVar rbn) [MatchCase (rowP bNames) Nothing conj sp] sp) sp]
              sp
      pure (ELambda Nothing [simpleBinder ran, simpleBinder rbn] body sp)

    -- lexicographic stable comparator over decorated (keys, row)
    -- pairs (§20.6.1); 'desc' swaps the comparison operands
    decoCmpLam keys = do
      ra <- freshNameM "__pa"
      rb <- freshNameM "__pb"
      asV <- mapM (const (freshNameM "__ka")) keys
      bsV <- mapM (const (freshNameM "__kb")) keys
      let ran = Name ra sp
          rbn = Name rb sp
          aNames = map (`Name` sp) asV
          bNames = map (`Name` sp) bsV
          keyP ns = case ns of
            [v] -> PVar v
            vs -> PTuple (map PVar vs) sp
          pairP ns = PTuple [keyP ns, PWild sp] sp
          cmpOne desc a b =
            let (x, y) = if desc then (b, a) else (a, b)
             in prelApp1 sp "compare" [EVar x, EVar y]
          chain [] = prelApp1 sp "compare" [EIntLit 0 Nothing sp, EIntLit 0 Nothing sp]
          chain [(desc, a, b)] = cmpOne desc a b
          chain ((desc, a, b) : restK) =
            EMatch (cmpOne desc a b)
              [ MatchCase (PCtor (CtorRef Nothing (Name "EQ" sp)) [] sp) Nothing (chain restK) sp
              , MatchCase (PVar (Name "__o" sp)) Nothing (EVar (Name "__o" sp)) sp
              ]
              sp
          keyed = [(desc, a, b) | ((desc, _), (a, b)) <- zip keys (zip aNames bNames)]
          body =
            EMatch (EVar ran)
              [ MatchCase (pairP aNames) Nothing
                  (EMatch (EVar rbn) [MatchCase (pairP bNames) Nothing (chain keyed) sp] sp)
                  sp
              ]
              sp
      pure (ELambda Nothing [simpleBinder ran, simpleBinder rbn] body sp)

    -- drop the (keys, row) decoration after sorting
    undecorateLam = do
      p <- freshNameM "__p"
      r <- freshNameM "__r"
      let pn = Name p sp
          rn = Name r sp
      pure $
        ELambda Nothing [simpleBinder pn]
          (EMatch (EVar pn) [MatchCase (PTuple [PWild sp, PVar rn] sp) Nothing (EVar rn) sp] sp)
          sp

-- ── Declarations ─────────────────────────────────────────────────────

-- | Check a resolved module: two passes (headers then bodies), per the
-- preceding-signature recursion rule (§15.16, §9.2).
checkModule :: CheckState -> Module -> (CheckState, Diagnostics)
checkModule st0 m =
  -- Sets, not lists: every let consults sigNames and every signature
  -- consults siglessLets, so list membership made large modules
  -- quadratic (measured ~4x time per size doubling at 16k+ decls)
  let sigNames = Set.fromList [nameText n | DSig _ n _ _ <- modDecls m]
      siglessLets =
        Set.fromList
          [ nameText n
          | DLet _ (LetDef (Just n) _ _ _ _ _ _ _) _ <- modDecls m
          , not (nameText n `Set.member` sigNames)
          ]
      passes = do
        mapM_ predeclarePass (modDecls m)
        mapM_ (headerPassIn siglessLets) (modDecls m)
        -- §10.4: once every data type's constructor types are
        -- elaborated, check strict positivity over the whole module's
        -- data group by fixed-point iteration and record each accepted
        -- type's parameter-positivity signature
        positivityPass (modDecls m)
        -- §14.3: register every top-level instance head before any
        -- body is checked, so instance visibility within the module
        -- does not depend on declaration order
        mapM_ instanceHeadPass (modDecls m)
        mapM_ (bodyPassIn siglessLets) (modDecls m)
        flushPendingFinal
        sigSatisfactionPass
      (_, st1) = runState passes (st0 {csSigPending = Map.empty, csPreInstances = Map.empty})
   in -- 'report' prepends; restore emission (source) order here
      (st1 {csDiags = []}, reverse (csDiags st1))

-- §9.1: a non-expect top-level term signature must be satisfied by
-- exactly one matching definition in the same source file.
sigSatisfactionPass :: CheckM ()
sigSatisfactionPass = do
  st <- get
  unless (csModule st == preludeModule) $
    forM_ (Map.toList (csSigPending st)) $ \(g, sp) ->
      errAt sp "E_SIGNATURE_UNSATISFIED" (Just "kappa-hs.signature.unsatisfied")
        ("top-level signature '" <> gnameText g
           <> "' has no definition in this source file (Spec §9.1); use 'expect term' for external requirements (§9.4)")

-- Pre-register data type-constructor names so declarations in one file
-- may refer to data types declared later (§10.1: declaration order
-- within a module is immaterial for type references).
predeclarePass :: Decl -> CheckM ()
predeclarePass = \case
  DData _ (DataDecl n params _ _) _ -> do
    g <- ownName n
    exists <- gets (Map.member g . csGlobals)
    unless exists $ do
      paramTele <- elabTele emptyCtx params
      let tyTm = foldr (\(ic, q, nm, t) acc -> CPi ic q nm t acc) (CSort 0) paramTele
      tyV <- evalIn emptyCtx tyTm
      addGlobal g (GlobalDef tyV Nothing False)
  _ -> pure ()

-- | Header pass, knowing which module-level lets have no signature: a
-- signature whose type mentions such a name (a reified static object,
-- §2.8.3) is deferred to the body pass, where the binding's value is
-- available in declaration order.
headerPassIn :: Set Text -> Decl -> CheckM ()
headerPassIn siglessLets = \case
  DSig _ _ tyE _
    | any (`Set.member` siglessLets) (sigHeadNames tyE) ->
        -- deferred to 'bodyPassIn' (the let's value is needed first)
        pure ()
  DSig _ n tyE sp -> do
    -- §11.3.3 (approximation): free ASCII-lowercase heads in the
    -- signature that resolve to no global are implicitly universalized
    -- as erased implicit binders; the kind is inferred from use (a
    -- fresh meta, defaulted to Type when unconstrained).
    fvs <- filterM (fmap isNothing . lookupGlobalName) (nub (freeLower tyE))
    kvs <- mapM (const (freshMetaV emptyCtx)) fvs
    let ctx0 = foldl (\c (v, k) -> bindCtx v False k c) emptyCtx (zip fvs kvs)
    (tyTm0, _) <- inferType ctx0 tyE
    kTms <- forM kvs $ \kv -> do
      kv' <- forceM kv
      case kv' of
        VFlex m [] -> solveMeta m (VSort 0) >> pure (CSort 0)
        _ -> quoteIn emptyCtx kv'
    let tyTm = foldr (\(v, kT) acc -> CPi Impl Q0 v kT acc) tyTm0 (zip fvs kTms)
    tyV <- evalIn emptyCtx tyTm
    g <- ownName n
    exists <- gets (Map.member g . csGlobals)
    isExpected <- gets (Map.member g . csExpects)
    when (exists && not isExpected) $ do
      enrich <- duplicateRelated (nameText n) g sp
      report $ enrich $
        diag SevError StageElaborate "E_DUPLICATE_DECLARATION" (Just "kappa-hs.name.duplicate") sp
          ("duplicate declaration of '" <> nameText n <> "'")
    recordDeclSite g sp
    addGlobal g (GlobalDef tyV Nothing False)
    -- §9.1: the signature awaits its same-file definition (an expected
    -- name is governed by §9.4 satisfaction instead)
    unless isExpected $
      modify' $ \st -> st {csSigPending = Map.insert g sp (csSigPending st)}
  DData mods dd sp -> do
    -- §22.1: an 'opaque data' representation is inspectable only in
    -- its defining module
    when (dmOpaque mods) $ do
      g <- ownName (ddName dd)
      modify' $ \st -> st {csOpaqueDatas = Map.insert g () (csOpaqueDatas st)}
    headerData dd sp
  DTypeAlias _ n params _ (Just rhs) sp
    | nameText n `elem` allNamesIn rhs -> do
        -- §15.16 admits recursive type-alias groups only "when
        -- admitted"; this implementation does not admit them (aliases
        -- are transparent definitions, §11.3) — recursion needs a data
        -- declaration. The alias is salvaged as a fresh metavariable
        -- so downstream uses do not cascade.
        errAt sp "E_RECURSIVE_TYPE_ALIAS" (Just "kappa-hs.type.recursive-alias")
          ("type alias '" <> nameText n
             <> "' refers to itself; recursive type aliases are not admitted (§15.16) — use a data declaration")
        g <- ownName n
        noteDefinition g sp
        tyV <- aliasKind params
        mv <- freshMetaV emptyCtx
        addGlobal g (GlobalDef tyV (Just mv) True)
  DTypeAlias _ n params _ (Just rhs) sp -> do
    -- alias: a definition at a universe type
    (tm, ty) <- elabAliasBody params rhs
    g <- ownName n
    noteDefinition g sp
    -- §22.2: remember the written field order of a record alias for
    -- derivation-shape reflection (core records are canonicalized)
    case rhs of
      ERecordType rfs Nothing _ ->
        modify' $ \st ->
          st {csRecordOrders = Map.insert g [nameText (rtfName f) | f <- rfs] (csRecordOrders st)}
      _ -> pure ()
    tmV <- evalIn emptyCtx tm
    addGlobal g (GlobalDef ty (Just tmV) True)
  DTypeAlias _ n params _ Nothing _ -> do
    g <- ownName n
    tyV <- aliasKind params
    addGlobal g (GlobalDef tyV Nothing False)
  DTrait _ td sp -> headerTrait td sp
  -- §18.1: a top-level (non-scoped) effect declaration registers a
  -- module-wide effect interface; a `scoped effect` is handled lexically by
  -- hoistScopedEffects in the block where it appears (so it is skipped here).
  DEffect mods eff sp
    | dmScoped mods -> pure ()
    | effIsLabelDecl eff -> elabTopEffectLabel eff sp
    | otherwise -> elabTopEffect eff sp
  DExpect _ form sp -> headerExpect form sp
  -- §4.4: register the wrapped definition's header like any other; the
  -- assertion prefix only affects termination checking and gating, which
  -- happen in the body pass.
  DUnsafeAssert _ inner _ -> headerPassIn siglessLets inner
  _ -> pure ()

ownName :: Name -> CheckM GName
ownName n = do
  st <- get
  pure (GName (csModule st) (nameText n))

-- | Every identifier spelled anywhere inside a piece of surface syntax
-- (generic over-approximation; binder shadowing is ignored). Used for
-- the recursive-type-alias check.
allNamesIn :: Expr -> [Text]
allNamesIn = go
  where
    go :: Data a => a -> [Text]
    go x = case cast x :: Maybe Name of
      Just n -> [nameText n]
      Nothing -> concat (gmapQ go x)

aliasKind :: [Binder] -> CheckM Value
aliasKind params = do
  -- (p1 : K1) -> ... -> Type
  let go [] = CSort 0
      go (b : rest) = CPi (if bImplicit b then Impl else Expl) Q0 (maybe "_" nameText (bName b)) (CSort 0) (go rest)
  evalIn emptyCtx (go params)

elabAliasBody :: [Binder] -> Expr -> CheckM (Term, Value)
elabAliasBody params rhs = do
  (tm0, kindTm0) <- go emptyCtx params
  -- §11.3.3: unannotated alias parameters whose kind the body does not
  -- constrain generalize to implicit kind binders ('type Dep x = Nat'
  -- accepts any-typed x: Dep : (@__k : Type) -> __k -> Type)
  tm1 <- zonkTermM 0 tm0
  kindTm1 <- zonkTermM 0 kindTm0
  st <- get
  let unsolved = unsolvedMetasOf st kindTm1
      k = length unsolved
      offsets = Map.fromList (zip unsolved [0 :: Int ..])
      replaceMetas d t = case t of
        CMeta m | Just i <- Map.lookup m offsets -> CVar (d + (k - 1 - i))
        CPi ic q nm a b -> CPi ic q nm (replaceMetas d a) (replaceMetas (d + 1) b)
        CLam ic q nm b -> CLam ic q nm (replaceMetas (d + 1) b)
        CApp ic f a -> CApp ic (replaceMetas d f) (replaceMetas d a)
        other -> other
      (tm, kindTm) =
        if k == 0
          then (tm1, kindTm1)
          else
            ( foldr (\_ b -> CLam Impl Q0 "__k" b) (replaceMetas 0 tm1) unsolved
            , foldr (\_ b -> CPi Impl Q0 "__k" (CSort 0) b) (replaceMetas 0 kindTm1) unsolved
            )
  tyV <- evalIn emptyCtx kindTm
  pure (tm, tyV)
  where
    go ctx [] = do
      -- an eta-reduced alias body may itself be a (partially applied)
      -- type former of higher kind ('type Equal (@0 a) = (=) a', §3.5.1)
      (tm0, ty0) <- inferT ctx rhs
      tyF <- forceM ty0
      former <- finalIsSort ctx tyF
      case tyF of
        VSort _ -> pure (tm0, CSort 0)
        VFlex m [] -> solveMeta m (VSort 0) >> pure (tm0, CSort 0)
        -- the §18.1 'IO a' accommodation of inferType
        VPi Expl _ _ _ _
          | CApp Expl (CGlob g) argTm <- tm0
          , g == gPrel "IO" -> do
              m <- freshMeta
              pure (CApp Expl (CApp Expl (CGlob g) m) argTm, CSort 0)
        VPi {} | former -> do
          kTm <- quoteIn ctx tyF
          pure (tm0, kTm)
        other -> do
          oT <- quoteIn ctx other
          errAt (exprSpan rhs) "E_NOT_A_TYPE" (Just "kappa.type.mismatch")
            ("expected a type; this expression has type " <> renderTerm oT)
          pure (tm0, CSort 0)
    go ctx (b : rest) = do
      domTm <- case bType b of
        Just t -> fst <$> inferType ctx t
        Nothing -> freshMeta
      domV <- evalIn ctx domTm
      let nm = maybe "_" nameText (bName b)
          ic = if bImplicit b then Impl else Expl
          ctx' = bindCtx nm False domV ctx
      (tm, innerK) <- go ctx' rest
      pure (CLam ic Q0 nm tm, CPi ic Q0 nm domTm innerK)

headerData :: DataDecl -> Span -> CheckM ()
headerData (DataDecl n params _mkind ctors) sp = do
  -- the optional kind annotation is not validated: every data type
  -- lives at 'Type' in this implementation (see SPEC_COVERAGE.md)
  g <- ownName n
  noteDefinition g sp
  forM_ (duplicatesOf [nameText cn | CtorDecl cn _ _ _ <- ctors]) $ \dn ->
    errAt sp "E_DUPLICATE_DECLARATION" (Just "kappa-hs.name.duplicate")
      ("duplicate constructor '" <> dn <> "' in data declaration")
  -- data type constructor type: params -> Type
  paramTele <- elabTele emptyCtx params
  let sortT = CSort 0
  let tyTm = foldr (\(ic, q, nm, t) acc -> CPi ic q nm t acc) sortT paramTele
  tyV <- evalIn emptyCtx tyTm
  addGlobal g (GlobalDef tyV Nothing False)
  ctorGs <- forM ctors $ \(CtorDecl cn binders mgadt _) -> do
    cg <- ownName cn
    cty <- case mgadt of
      Just sig -> do
        -- GADT signature: elaborate under data params implicitly bound
        (tm, _) <- elabUnderParams paramTele sig
        pure tm
      Nothing -> do
        -- ordinary ctor: params implicit, fields explicit, result = data applied
        fieldsTele <- elabTele' paramTele binders
        -- §10.1.1: a field default is checked at declaration against
        -- the field's type, with only the EARLIER fields in scope
        checkFieldDefaults paramTele fieldsTele binders
        let resultT =
              foldl
                (\f i -> CApp Expl f (CVar i))
                (CGlob g)
                (reverse [length fieldsTele .. length fieldsTele + length paramTele - 1])
            full =
              foldr (\(ic, q, nm, t) acc -> CPi ic q nm t acc) resultT
                ([(Impl, Q0, nm, t) | (_, _, nm, t) <- paramTele] ++ fieldsTele)
        pure full
    let fields = ctorFieldsOf binders mgadt
    modify' $ \st -> st {csCtors = Map.insert cg (CtorInfo g cty fields) (csCtors st)}
    pure cg
  modify' $ \st -> st {csDatas = Map.insert g (DataInfo ctorGs (length params)) (csDatas st)}
  where
    ctorFieldsOf binders mgadt = case mgadt of
      Just sig -> gadtFields sig
      Nothing -> [(nameText <$> bName b, bDefault b) | b <- binders, not (bImplicit b)]
    gadtFields = \case
      EArrow b rest | not (bImplicit b) -> (nameText <$> bName b, bDefault b) : gadtFields rest
      EArrow _ rest -> gadtFields rest
      EForall _ rest _ -> gadtFields rest
      ETraitArrow _ rest -> gadtFields rest
      _ -> []

-- ── §10.4 strict positivity ──────────────────────────────────────────
--
-- "Every 'data' declaration MUST satisfy strict positivity." After the
-- header pass has elaborated every constructor type, this pass treats
-- all 'data' declarations of the module as one mutually recursive group
-- (declaration order within a module is immaterial, §10.1), computes a
-- parameter-positivity signature for every group member by fixed-point
-- iteration (§10.4), and then rejects the group if, under the converged
-- signatures, any group type still occurs non-strictly-positively in any
-- constructor argument type.

-- | The constructor argument (field) types of a data type, as core
-- terms, each closed over the data parameters as the OUTERMOST de Bruijn
-- binders. 'tdParamCount' leading 'CPi' binders of the elaborated
-- constructor type are the (implicit) parameters; every remaining 'CPi'
-- domain up to the result head is a field type. The returned 'pfDepth'
-- is the number of binders in scope at the field domain (parameters plus
-- the earlier fields of the same constructor), so that parameter @j@
-- (0-based, first parameter) sits at de Bruijn index @pfDepth - 1 - j@.
data PosField = PosField
  { pfDepth :: !Int
  , pfType :: !Term
  }

-- | Per-data-type positivity input gathered from the elaborated state.
data PosData = PosData
  { pdName :: !GName
  , pdParamCount :: !Int
  , pdFields :: ![PosField] -- ^ across all constructors of this type
  , pdSpan :: !Span
  }

positivityPass :: [Decl] -> CheckM ()
positivityPass decls = do
  st <- get
  let dataDecls = [(dd, sp) | DData _ dd sp <- decls]
  group <- catMaybes <$> mapM (gatherPosData st) dataDecls
  unless (null group) $ do
    let groupNames = Set.fromList (map pdName group)
        -- prior (non-group) signatures: accepted data types and the
        -- strictly-positive built-in/imported carriers
        priorSig = csPositivity st
        -- fixed-point over the group for the parameter-positivity
        -- signatures (§10.4). The recompute operator is monotone in the
        -- "more positive" direction (a parameter known positive lets a
        -- recursive index recurse strictly-positively instead of
        -- demanding the parameter be absent), so the signature we want is
        -- its GREATEST fixed point: start every parameter positive and
        -- iterate downward until stable. (A least fixed point from
        -- all-non-positive degenerates — e.g. it would mark 'a' in
        -- 'data Tree a = ... Branch (Tree a) a (Tree a)' as non-positive,
        -- wrongly. The rejection judgement below is computed afterwards
        -- against the converged signatures, per §10.4.)
        sig0 = Map.fromList [(pdName d, replicate (pdParamCount d) True) | d <- group]
        converged = fixpoint groupNames priorSig group sig0
        fullSig = Map.union converged priorSig
    -- record the converged group signatures for later declarations
    modify' $ \s -> s {csPositivity = Map.union converged (csPositivity s)}
    -- reject any group member with a non-strictly-positive occurrence
    forM_ group $ \d ->
      forM_ (pdFields d) $ \fld ->
        unless (spPositive groupNames fullSig (pfType fld)) $
          errOncePerSpan (pdSpan d) "E_DATA_NOT_STRICTLY_POSITIVE" (Just "kappa.termination.failure")
            ( "data type '" <> gnameText (pdName d)
                <> "' is not strictly positive: it occurs in a negative or non-admissible position"
                <> " in a constructor argument type (Spec §10.4)"
            )

-- | Collect the field types of one data declaration from the elaborated
-- 'CtorInfo' types. Returns 'Nothing' for a type with no recorded data
-- info (should not happen for a 'DData' that elaborated).
gatherPosData :: CheckState -> (DataDecl, Span) -> CheckM (Maybe PosData)
gatherPosData st (DataDecl n _ _ _, sp) = do
  g <- ownName n
  case Map.lookup g (csDatas st) of
    Nothing -> pure Nothing
    Just di -> do
      let pc = diParamCount di
          ctorTys = [ciType ci | cg <- diCtors di, Just ci <- [Map.lookup cg (csCtors st)]]
          flds = concatMap (posCtorFieldTypes pc) ctorTys
      pure (Just (PosData g pc flds sp))

-- | Peel 'pc' leading parameter binders, then collect each remaining
-- 'CPi' domain (a constructor field type) together with the binder depth
-- in scope at that domain.
posCtorFieldTypes :: Int -> Term -> [PosField]
posCtorFieldTypes pc = peelParams pc
  where
    peelParams 0 t = peelFields pc t
    peelParams k (CPi _ _ _ _ b) = peelParams (k - 1) b
    peelParams _ _ = [] -- malformed; nothing to check
    peelFields depth = \case
      CPi _ _ _ a b -> PosField depth a : peelFields (depth + 1) b
      _ -> [] -- the result head 'T params' carries no fields

-- | Fixed-point iteration of the group's parameter-positivity signatures
-- (§10.4): recompute every member's signature from the current
-- signatures until nothing changes.
fixpoint :: Set GName -> Map GName [Bool] -> [PosData] -> Map GName [Bool] -> Map GName [Bool]
fixpoint groupNames priorSig group = go
  where
    go sig =
      let sig' = Map.fromList [(pdName d, recomputeSig groupNames (Map.union sig priorSig) d) | d <- group]
       in if sig' == sig then sig else go sig'

-- | Recompute one data type's parameter-positivity signature: parameter
-- @j@ is positive iff every occurrence of the corresponding de Bruijn
-- variable in every field type is in a strictly positive position
-- (§10.4).
recomputeSig :: Set GName -> Map GName [Bool] -> PosData -> [Bool]
recomputeSig groupNames sig d =
  [ all (\fld -> varPositive groupNames sig (pfDepth fld - 1 - j) (pfType fld)) (pdFields d)
  | j <- [0 .. pdParamCount d - 1]
  ]

-- | Is the parameter-positivity signature of an applied head 'F' known
-- and is 'F' admissible in a strictly positive position? Returns the
-- per-argument positivity flags when admissible (§10.4 admissibility).
admissibleSig :: Set GName -> Map GName [Bool] -> Term -> Maybe [Bool]
admissibleSig groupNames sig = \case
  CGlob g
    | g `Set.member` groupNames -> Map.lookup g sig -- a group member (its evolving signature)
    | otherwise -> Map.lookup g sig -- a prior data type / built-in carrier with a recorded signature
  _ -> Nothing

-- | Split a term into its head and argument spine.
posSpine :: Term -> (Term, [Term])
posSpine = go []
  where
    go acc (CApp _ f a) = go (a : acc) f
    go acc t = (t, acc)

-- | §10.4 strict positivity of a constructor field type with respect to
-- a /target/ supplied as the predicate @hits@ (does this exact subterm
-- mention the target as its head?) plus @occurs@ (does the target occur
-- anywhere in this subterm?). The walk implements: the argument type
-- itself; @X -> U@ / @(x : X) -> U@ with the target absent from @X@ and
-- strictly positive in @U@; and an admissible application @F A1 .. An@
-- in which the target occurs strictly positively only in the @Ai@ whose
-- parameter is marked positive (and not at all in the others).
posWalk
  :: Set GName
  -> Map GName [Bool]
  -> (Int -> Term -> Bool) -- ^ @occurs shift t@: does the target occur in @t@ (shift = extra binders since the top)?
  -> (Int -> Term -> Bool) -- ^ @isBareTarget shift t@: is @t@ exactly a bare occurrence of the target (the "argument type itself")?
  -> Int -- ^ binders entered since the top (de Bruijn shift)
  -> Term
  -> Bool
posWalk groupNames sig occurs isBareTarget = go
  where
    go shift t
      -- the argument type itself (possibly with parameters/indices):
      -- a bare occurrence of the target is a strictly positive position
      | isBareTarget shift t = True
      -- the target does not occur at all: trivially strictly positive
      | not (occurs shift t) = True
      | otherwise = case posSpine t of
          -- function/dependent-function type 'X -> U' / '(x : X) -> U':
          -- target absent from the domain and strictly positive in 'U'
          (CPi _ _ _ a b, []) ->
            not (occurs shift a) && go (shift + 1) b
          -- application 'F A1 .. An'
          (hd, args@(_ : _)) ->
            case admissibleSig groupNames sig hd of
              Just flags ->
                -- 'F' is admissible (a prior/built-in carrier, or the
                -- defined type applied to parameters/indices, which is
                -- itself a strictly positive position): the target may
                -- occur strictly positively only in those 'Ai' whose
                -- parameter is marked positive in F's signature, and not
                -- at all in the others
                and
                  [ if positiveFlag
                      then go shift arg
                      else not (occurs shift arg)
                  | (arg, positiveFlag) <- zip args (flags ++ repeat False)
                  ]
              Nothing ->
                -- 'F' is not admissible (a bare variable, an opaque type
                -- without a positivity signature, …): the target must
                -- not occur anywhere in the application
                False
          -- covariant suspension wrappers: the target stays strictly
          -- positive under Thunk/Memo/Force in type position
          (CThunkE e, []) -> go shift e
          (CLazyE e, []) -> go shift e
          (CForceE e, []) -> go shift e
          -- record / variant type formers: every component is covariant
          (CRecordT fs, []) -> all (go shift . snd) fs
          (CVariantT ms, []) -> all (go shift) ms
          -- any other shape carrying an occurrence is not a strictly
          -- positive position
          _ -> False

-- | §10.4 strict positivity of a field type with respect to the group
-- types (the reject condition target). A group type may occur, but only
-- in strictly positive positions.
spPositive :: Set GName -> Map GName [Bool] -> Term -> Bool
spPositive groupNames sig =
  posWalk groupNames sig (\_shift t -> mentionsGroup groupNames t) bareGroup 0
  where
    bareGroup _shift = \case
      CGlob g -> g `Set.member` groupNames
      _ -> False

-- | §10.4 strict positivity of a field type with respect to one data
-- parameter (the de Bruijn variable @v@ at the field-domain depth). Used
-- to compute the parameter-positivity signature.
varPositive :: Set GName -> Map GName [Bool] -> Int -> Term -> Bool
varPositive groupNames sig v0 =
  posWalk groupNames sig (\shift t -> mentionsVar (v0 + shift) t) bareVar 0
  where
    bareVar shift = \case
      CVar i -> i == v0 + shift
      _ -> False

-- | Does any group type constructor occur anywhere in a term?
mentionsGroup :: Set GName -> Term -> Bool
mentionsGroup groupNames = go
  where
    go = \case
      CGlob g -> g `Set.member` groupNames
      CVar _ -> False
      CLam _ _ _ b -> go b
      CPi _ _ _ a b -> go a || go b
      CApp _ f a -> go f || go a
      CSort _ -> False
      CLit _ -> False
      CCtor _ as -> any go as
      CMatch s alts -> go s || any (\(CaseAlt _ gd b) -> maybe False go gd || go b) alts
      CRecordT fs -> any (go . snd) fs
      CRecordV fs -> any (go . snd) fs
      CProj e _ -> go e
      CProjAt e _ _ -> go e
      CVariantT ms -> any go ms
      CInject _ e -> go e
      CLet _ _ a b c -> go a || go b || go c
      CLetRec _ _ a b c -> go a || go b || go c
      CMeta _ -> False
      CDo _ _ -> False
      CSealE _ e -> go e
      CSigT _ e -> go e
      CThunkE e -> go e
      CLazyE e -> go e
      CForceE e -> go e
      CIf a b c -> go a || go b || go c
      CQuote _ slots -> any go slots

-- | Does the de Bruijn variable @v@ occur anywhere in a term (accounting
-- for binders that shift it)?
mentionsVar :: Int -> Term -> Bool
mentionsVar = go
  where
    go v = \case
      CVar i -> i == v
      CGlob _ -> False
      CLam _ _ _ b -> go (v + 1) b
      CPi _ _ _ a b -> go v a || go (v + 1) b
      CApp _ f a -> go v f || go v a
      CSort _ -> False
      CLit _ -> False
      CCtor _ as -> any (go v) as
      CMatch s alts -> go v s || any (\(CaseAlt p gd b) -> let n = patBindersC p in maybe False (go (v + n)) gd || go (v + n) b) alts
      CRecordT fs -> any (go v . snd) fs
      CRecordV fs -> any (go v . snd) fs
      CProj e _ -> go v e
      CProjAt e _ _ -> go v e
      CVariantT ms -> any (go v) ms
      CInject _ e -> go v e
      CLet _ _ a b c -> go v a || go v b || go (v + 1) c
      CLetRec _ _ a b c -> go v a || go (v + 1) b || go (v + 1) c
      CMeta _ -> False
      CDo _ _ -> False
      CSealE _ e -> go v e
      CSigT _ e -> go v e
      CThunkE e -> go v e
      CLazyE e -> go v e
      CForceE e -> go v e
      CIf a b c -> go v a || go v b || go v c
      CQuote _ slots -> any (go v) slots

-- §10.1.1 declaration-time validation of constructor field defaults:
-- each default must elaborate, with the preceding fields in scope, at
-- the field's declared type (later fields and the field itself are not
-- in scope).
checkFieldDefaults :: Telescope -> Telescope -> [Binder] -> CheckM ()
checkFieldDefaults paramTele fieldsTele binders = do
  pctx <- teleCtx paramTele
  let explicitBs = [b | b <- binders, not (bImplicit b)]
  _ <-
    foldM
      ( \(ctx, tele) b -> case tele of
          ((_, _, nm, domTm) : rest) -> do
            domV <- evalIn ctx domTm
            forM_ (bDefault b) $ \d -> do
              (dTm, dTy) <- infer ctx d
              eq <- unify ctx dTy domV
              unless eq $ do
                domR <- quoteIn ctx domV
                dTyR <- quoteIn ctx dTy
                errAt (exprSpan d) "E_TYPE_EQUALITY_MISMATCH" (Just "kappa.type.mismatch")
                  ( "constructor field default for '" <> nm
                      <> "' has type " <> renderTerm dTyR
                      <> ", but the field's type is " <> renderTerm domR <> " (Spec §10.1.1)"
                  )
              _ <- pure dTm
              pure ()
            pure (bindCtx nm False domV ctx, rest)
          [] -> pure (ctx, tele)
      )
      (pctx, fieldsTele)
      explicitBs
  pure ()

-- bind each telescope entry at its elaborated domain type (the domain
-- term is closed over the preceding entries)
teleCtx :: Telescope -> CheckM Ctx
teleCtx = foldM step emptyCtx
  where
    step c (_, _, nm, domTm) = do
      domV <- evalIn c domTm
      pure (bindCtx nm False domV c)

elabTele' :: Telescope -> [Binder] -> CheckM Telescope
elabTele' tele bs = do
  ctx <- teleCtx tele
  elabTele ctx bs

-- elaborate binders to a telescope (left to right).
elabTele :: Ctx -> [Binder] -> CheckM Telescope
elabTele _ [] = pure []
elabTele ctx (b : rest) = do
  domTm <- case binderTypeExpr b of
    Just t -> fst <$> inferType ctx t
    -- an unannotated param's kind is inferred from its uses (a fresh
    -- meta; unconstrained params still default to Type, §11.3.3)
    Nothing -> freshMeta
  domV <- evalIn ctx domTm
  let nm = maybe "_" nameText (bName b)
      ic = if bImplicit b then Impl else Expl
      ctx' = bindCtx nm False domV ctx
  restT <- elabTele ctx' rest
  pure ((ic, binderQ b, nm, domTm) : restT)

elabUnderParams :: Telescope -> Expr -> CheckM (Term, Value)
elabUnderParams tele e = do
  ctx <- teleCtx tele
  (tm, _) <- inferType ctx e
  -- close over params as implicit Pi
  let closed = foldr (\(_, _, nm, t) acc -> CPi Impl Q0 nm t acc) tm tele
  pure (closed, VSort 0)

headerTrait :: TraitDecl -> Span -> CheckM ()
headerTrait (TraitDecl supers n params members) sp = do
  g <- ownName n
  noteDefinition g sp
  paramTele <- elabTele emptyCtx params
  -- trait constructor: params -> Type
  let tyTm = foldr (\(_, _, nm, t) acc -> CPi Expl Q0 nm t acc) (CSort 0) paramTele
  tyV <- evalIn emptyCtx tyTm
  pctx <- teleCtx paramTele
  -- supertrait premises (§14.1.4): their evidence is carried as
  -- dictionary fields, projected by the compiler as ordinary evidence
  -- projections (§14.2.1); a parenthesized premise list (C1 a, C2 a)
  -- is several premises
  let superList = concatMap (\sx -> case sx of ETuple es _ -> es; _ -> [sx]) supers
  supPairs <- forM (zip [(0 :: Int) ..] superList) $ \(i, s) -> do
    (sTm, _) <- inferType pctx s
    pure (superFieldName i, sTm)
  -- member declarations in source order; earlier members are in scope
  -- for later member signatures as §13.2.1 siblings of the evidence
  -- record ("Inside the trait body, Item refers to the associated
  -- static member of the current trait evidence", §14.2.1), and free
  -- lowercase identifiers are implicitly universalized (§14.2/§11.3.3)
  let paramNames = [nm | (_, _, nm, _) <- paramTele]
      memberNames =
        nub $
          [nameText mn | TraitSig mn _ _ <- members]
            ++ [nameText mn | TraitDefault (LetDef (Just mn) _ _ _ _ _ _ _) _ <- members]
      elabMemberTy acc mtyE = do
        fvs <-
          filterM
            (\v -> if v `elem` (paramNames ++ memberNames) then pure False else isNothing <$> lookupGlobalName v)
            (nub (freeLower mtyE))
        kvs <- mapM (const (freshMetaV pctx)) fvs
        let mctx = foldl (\c (v, k) -> bindCtx v False k c) pctx (zip fvs kvs)
        (mtyTm0, _) <- withThis (Just (ThisTraitSibs (sortOn fst acc))) (inferType mctx mtyE)
        kTms <- forM kvs $ \kv -> do
          kv' <- forceM kv
          case kv' of
            VFlex m [] -> solveMeta m (VSort 0) >> pure (CSort 0)
            _ -> quoteIn pctx kv'
        let mtyTm = foldr (\(v, kT) b -> CPi Impl Q0 v kT b) mtyTm0 (zip fvs kTms)
        mtyV <- evalIn pctx mtyTm
        pure (mtyTm, mtyV)
      goMembers _acc done [] = pure (reverse done)
      goMembers acc done (m : rest) = case m of
        TraitSig mn mtyE _ -> do
          (mtyTm, mtyV) <- elabMemberTy acc mtyE
          goMembers (acc ++ [(nameText mn, mtyV)]) ((nameText mn, mtyTm) : done) rest
        TraitDefault (LetDef (Just mn) _ _ _ _ mty _ _) _
          -- a default for an already-declared member supplies its
          -- definition only; the declaration owns the dictionary
          -- field (§14.2: declaration vs definition forms)
          | nameText mn `elem` map fst done -> goMembers acc done rest
          | otherwise -> do
              (mtyTm, mtyV) <- case mty of
                Just t -> elabMemberTy acc t
                Nothing -> do
                  mTm <- freshMeta
                  mV <- evalIn pctx mTm
                  pure (mTm, mV)
              goMembers (acc ++ [(nameText mn, mtyV)]) ((nameText mn, mtyTm) : done) rest
        TraitDefault {} -> goMembers acc done rest
  ms <- goMembers [] [] members
  let dictBody = CRecordT (sortOn fst (supPairs ++ ms))
      dictTm = foldr (\(_, _, nm, _) acc -> CLam Expl Q0 nm acc) dictBody paramTele
  dictV <- evalIn emptyCtx dictTm
  -- the trait constructor is abstract (§14.1.1): not conversion-reducible
  addGlobal g (GlobalDef tyV (Just dictV) False)
  let defaults = Map.fromList [(nameText dn, ld) | TraitDefault ld@(LetDef (Just dn) _ _ _ _ _ _ _) _ <- members]
      supTms = [(fn, foldr (\(_, _, nm, _) acc -> CLam Expl Q0 nm acc) sTm paramTele) | (fn, sTm) <- supPairs]
  modify' $ \st -> st {csTraits = Map.insert g (TraitInfo (length paramTele) (map fst ms) defaults supTms) (csTraits st)}
  -- member projection globals: m : forall params. (@d : Tr params) -> τ
  -- (occurrences of sibling members in τ become projections from the
  -- dict binder)
  forM_ ms $ \(mn, mtyTm) -> do
    let dictTy =
          foldl
            (\f i -> CApp Expl f (CVar i))
            (CGlob g)
            (reverse [0 .. length paramTele - 1])
        projTy =
          foldr
            (\(_, _, nm, t) acc -> CPi Impl Q0 nm t acc)
            (CPi Impl QW "__d" dictTy (substThisTm (CVar 0) (shiftTerm 1 0 mtyTm)))
            paramTele
        projTm =
          foldr
            (\(_, _, nm, _) acc -> CLam Impl Q0 nm acc)
            (CLam Impl QW "__d" (CProj (CVar 0) mn))
            paramTele
    projTyV <- evalIn emptyCtx projTy
    projV <- evalIn emptyCtx projTm
    mg <- ownName (Name mn sp)
    -- both the bare member name and the qualified projection global.
    -- Capture the KCore body for the native backend (§14.2.1 member
    -- projection): a CLam chain projecting the member field from the dict.
    addGlobal mg (GlobalDef projTyV (Just projV) True)
    recordCoreBody mg projTm
    addGlobal (memberGlobal g mn) (GlobalDef projTyV (Just projV) True)
    recordCoreBody (memberGlobal g mn) projTm

-- | The dictionary field carrying the i-th supertrait premise's
-- evidence (§14.1.4/§14.3.3).
superFieldName :: Int -> Text
superFieldName i = "__super" <> T.pack (show i)

-- | Does a Pi/Lam closure body reference its own bound variable
-- (de Bruijn index 0, relative to the body)? Used to detect
-- non-dependent function arrows: when the codomain does not mention the
-- argument, elaborating an application slot need not evaluate the
-- argument value and unify it into the result type (the fresh
-- placeholder meta never appears in the codomain), which collapses the
-- per-slot cost of a deep application/operator chain from O(size) to
-- O(1) — restoring linear scaling for the (overwhelmingly common)
-- non-dependent case while leaving dependent elaboration unchanged.
--
-- Conservative: returns 'True' for the few constructs whose binder
-- structure is not traversed here ('CDo', 'CQuote'), so a body that
-- might reference index 0 is never mis-reported as independent.
coreUsesVar0 :: Term -> Bool
coreUsesVar0 = go 0
  where
    -- @d@ counts binders crossed; the body's index 0 appears as @CVar d@.
    go d = \case
      CVar i -> i == d
      CGlob _ -> False
      CLam _ _ _ b -> go (d + 1) b
      CPi _ _ _ a b -> go d a || go (d + 1) b
      CApp _ f a -> go d f || go d a
      CSort _ -> False
      CLit _ -> False
      CCtor _ as -> any (go d) as
      CMatch s alts ->
        go d s || any (\(CaseAlt p gd b) -> let d' = d + patBindersC p in maybe False (go d') gd || go d' b) alts
      CRecordT fs -> any (go d . snd) fs
      CRecordV fs -> any (go d . snd) fs
      CProj e _ -> go d e
      CProjAt e _ _ -> go d e
      CVariantT ms -> any (go d) ms
      CInject _ e -> go d e
      CLet _ _ a b c -> go d a || go d b || go (d + 1) c
      CLetRec _ _ a b c -> go d a || go (d + 1) b || go (d + 1) c
      CMeta _ -> False
      CDo _ _ -> True
      CSealE _ e -> go d e
      CSigT _ e -> go d e
      CThunkE e -> go d e
      CLazyE e -> go d e
      CForceE e -> go d e
      CIf a b c -> go d a || go d b || go d c
      CQuote _ _ -> True

shiftTerm :: Int -> Int -> Term -> Term
shiftTerm by = go
  where
    go d = \case
      CVar i
        | i >= d -> CVar (i + by)
        | otherwise -> CVar i
      CGlob g -> CGlob g
      CLam ic q n b -> CLam ic q n (go (d + 1) b)
      CPi ic q n a b -> CPi ic q n (go d a) (go (d + 1) b)
      CApp ic f a -> CApp ic (go d f) (go d a)
      CSort s -> CSort s
      CLit l -> CLit l
      CCtor g as -> CCtor g (map (go d) as)
      CMatch s alts ->
        CMatch (go d s) [CaseAlt p (fmap (go (d + nb p)) gd) (go (d + nb p) b) | CaseAlt p gd b <- alts]
        where
          nb = patBindersC
      CRecordT fs -> CRecordT [(n, go d t) | (n, t) <- fs]
      CRecordV fs -> CRecordV [(n, go d t) | (n, t) <- fs]
      CProj e f -> CProj (go d e) f
      CProjAt e f i -> CProjAt (go d e) f i
      CVariantT ms -> CVariantT (map (go d) ms)
      CInject t e -> CInject t (go d e)
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

patBindersC :: CorePat -> Int
patBindersC = \case
  CPWild -> 0
  CPVar _ -> 1
  CPLit _ -> 0
  CPCtor _ ps -> sum (map patBindersC ps)
  CPTuple ps -> sum (map patBindersC ps)
  CPRecord fs mr -> sum (map (patBindersC . snd) fs) + (case mr of Just nm | not (T.null nm) -> 1; _ -> 0)
  CPInject _ p -> patBindersC p
  CPInjectRest _ -> 1
  CPOr ps _ -> case ps of
    (p : _) -> patBindersC p
    [] -> 0
  CPAs _ p -> 1 + patBindersC p

headerExpect :: ExpectForm -> Span -> CheckM ()
headerExpect form sp = case form of
  ExpectTerm n tyE -> do
    g <- ownName n
    st0 <- get
    let alreadyDef = case Map.lookup g (csGlobals st0) of
          Just gd -> isJust (gdValue gd)
          Nothing -> False
    -- Elaborate the declared signature up front: it is needed both to
    -- register the abstract global (name resolution) and to check a
    -- backend-intrinsic satisfier against it up to definitional equality.
    (tyTm, _) <- inferType emptyCtx tyE
    tyV <- evalIn emptyCtx tyTm
    unless alreadyDef $ addGlobal g (GlobalDef tyV Nothing False)
    -- §34.5/§9.4: a matching backend intrinsic of the selected profile
    -- satisfies this expectation when its signature matches.
    byIntrinsic <- backendIntrinsicSatisfies g tyV sp
    let count = if alreadyDef || byIntrinsic then 1 else 0
    modify' $ \st -> st {csExpects = Map.insert g (sp, count) (csExpects st)}
  ExpectType n params _ -> abstractType n params
  ExpectData n params _ -> do
    abstractType n params
    g <- ownName n
    modify' $ \st -> st {csDatas = Map.insertWith (\_ old -> old) g (DataInfo [] (length params)) (csDatas st)}
  ExpectTrait n params _ -> abstractType n params
  where
    abstractType n params = do
      g <- ownName n
      fresh <- registerExpect g
      when fresh $ do
        tyV <- aliasKind params
        addGlobal g (GlobalDef tyV Nothing False)
    -- Record the §9.4 expectation. When the name is already defined
    -- earlier in the unit, that definition is its (single) satisfier and
    -- the existing global is kept. Returns True when the expect should
    -- introduce the declaration into the global table itself.
    registerExpect g = do
      st <- get
      let satisfied = case Map.lookup g (csGlobals st) of
            Just gd -> isJust (gdValue gd)
            Nothing -> Map.member g (csDatas st) || Map.member g (csTraits st)
          count = if satisfied then 1 else 0
      put st {csExpects = Map.insert g (sp, count) (csExpects st)}
      pure (not satisfied)

-- | §34.5/§9.4: decide whether a backend intrinsic of the selected profile
-- satisfies the expectation @g@ with declared type @tyV@. An intrinsic is
-- keyed by its Kappa spelling ('csBackendIntrinsics', empty unless a native
-- profile is selected); its expected signature MUST match @tyV@ up to
-- definitional equality. A name match with a type mismatch is reported as
-- 'E_BACKEND_INTRINSIC_SIGNATURE_MISMATCH' and still counts as "claimed by
-- the backend" so the precise mismatch is the sole diagnostic (not also a
-- spurious unsatisfied-expectation error).
backendIntrinsicSatisfies :: GName -> Value -> Span -> CheckM Bool
backendIntrinsicSatisfies g tyV sp = do
  st <- get
  case Map.lookup (gnameText g) (csBackendIntrinsics st) of
    Nothing -> pure False
    Just expectedTm -> do
      expectedV <- evalIn emptyCtx expectedTm
      ec <- ec_
      if convertible ec 0 tyV expectedV
        then pure True
        else do
          errAt sp "E_BACKEND_INTRINSIC_SIGNATURE_MISMATCH" (Just "kappa-hs.backend.intrinsic")
            ( "the declared type of '" <> gnameText g
                <> "' does not match the signature of the backend intrinsic that satisfies it (Spec §9.4, §34.5)"
            )
          pure True

-- | Note a top-level definition of @g@: it satisfies a pending same-file
-- signature (§9.1) and counts toward §9.4 expect satisfaction (a second
-- satisfier is ambiguous).
noteDefinition :: GName -> Span -> CheckM ()
noteDefinition g sp = do
  recordDeclSite g sp
  st <- get
  put st {csSigPending = Map.delete g (csSigPending st)}
  case Map.lookup g (csExpects st) of
    Nothing -> pure ()
    Just (esp, cnt) -> do
      modify' $ \st' -> st' {csExpects = Map.insert g (esp, cnt + 1) (csExpects st')}
      when (cnt + 1 == 2) $
        errAt sp "E_EXPECT_AMBIGUOUS" (Just "kappa-hs.expect.ambiguous")
          ("more than one definition satisfies expected declaration '" <> gnameText g <> "' (Spec §9.4)")

-- | §9.4: expects with no satisfier at the end of the compilation unit.
expectUnsatisfiedDiags :: CheckState -> Diagnostics
expectUnsatisfiedDiags st =
  [ diag SevError StageElaborate "E_EXPECT_UNSATISFIED" (Just "kappa-hs.expect.unsatisfied") sp
      ("expected declaration '" <> gnameText g
         <> "' is not satisfied by any definition, backend intrinsic, or imported artifact in this compilation unit (Spec §9.4)")
  | (g, (sp, n)) <- Map.toList (csExpects st)
  , n == 0
  ]

-- | Body pass: elaborates definitions, plus any signatures the header
-- pass deferred because they mention signature-less module lets.
bodyPassIn :: Set Text -> Decl -> CheckM ()
bodyPassIn siglessLets d = case d of
  DSig _ _ tyE _
    | any (`Set.member` siglessLets) (sigHeadNames tyE) -> headerPassIn Set.empty d
  _ -> bodyPass d

-- names a signature's type may resolve through (heads of applications,
-- dotted bases, binder domains)
sigHeadNames :: Expr -> [Text]
sigHeadNames = go
  where
    go = \case
      EVar (Name t _) -> [t]
      EApp f args -> go f ++ concatMap goArg args
      EDot e _ -> go e
      EQDot e _ -> go e
      EArrow b e -> maybe [] go (bType b) ++ go e
      EForall bs e _ -> concatMap (maybe [] go . bType) bs ++ go e
      EExists bs e _ -> concatMap (maybe [] go . bType) bs ++ go e
      ETuple es _ -> concatMap go es
      EOptionSugar e _ -> go e
      ETraitArrow a b -> go a ++ go b
      EOpChain els -> concat [go x | ChainOperand x <- els]
      _ -> []
    goArg = \case
      ArgExplicit e -> go e
      ArgImplicit e -> go e
      _ -> []

bodyPass :: Decl -> CheckM ()
bodyPass = \case
  DLet mods ld sp -> elabLetDecl mods ld sp
  DInstance inst sp -> elabInstance inst sp
  DPattern mods ld sp -> elabActivePatternDecl mods ld sp
  DProjection mods n bs ty body sp -> elabProjectionDecl mods n bs ty body sp
  DDerive _ sp ->
    unsupportedAt sp "derive declarations are not supported by this implementation"
  DTopSplice _ sp ->
    unsupportedAt sp "top-level splices are not supported by this implementation"
  DUnsafeAssert akind inner sp -> elabUnsafeAssert akind inner sp
  _ -> pure ()

-- | §4.4 termination-assertion escape. The assertion is gated by the
-- §4.2 build configuration: rejected by default (kappa.feature.gated)
-- with a diagnostic naming both the offending form and the build setting
-- that disallows it. When permitted, the use is recorded in the §4.7
-- audit ledger and the wrapped definition is elaborated normally — these
-- forms never change runtime semantics (§4.4), and this implementation
-- does not run a termination checker, so suppression is accept-only.
elabUnsafeAssert :: UnsafeAssertKind -> Decl -> Span -> CheckM ()
elabUnsafeAssert akind inner sp = do
  cfg <- gets csUnsafe
  let (facility, setting, allowed) = case akind of
        AssertTerminates -> ("assertTerminates", "allow_assert_terminates", allowAssertTerminates cfg)
        AssertTotal -> ("assertTotal", "allow_assert_terminates", allowAssertTerminates cfg)
        AssertReducible -> ("assertReducible", "allow_assert_reducible", allowAssertReducible cfg)
      affected = case inner of
        DLet _ ld _ -> maybe "<anonymous>" nameText (ldName ld)
        _ -> "<definition>"
  if allowed
    then recordAudit facility affected setting sp Nothing
    else gateUnsafe facility setting sp affected
  -- Elaborate the wrapped definition regardless of gating: these forms
  -- never change runtime semantics (§4.4) and registering the binding
  -- avoids a spurious §9.1 signature-unsatisfied cascade on top of the
  -- gate error. This implementation runs no termination checker, so the
  -- assertion's only effect here is gating + the §4.7 audit record.
  bodyPass inner

-- | §4.2: reject an unsafe/debug facility that the build configuration
-- disallows, citing both the offending form and the disabling setting.
gateUnsafe :: Text -> Text -> Span -> Text -> CheckM ()
gateUnsafe facility setting sp affected =
  report $
    withPayload (featureGatedPayload ("unsafe-debug-facility:" <> facility) setting) $
    withRelated (related RoleFeatureGateSite sp ("build setting '" <> setting <> "' is disabled")) $
      diag SevError StageElaborate "E_FEATURE_INACTIVE" (Just "kappa.feature.gated") sp
        ( "use of unsafe/debug facility '" <> facility <> "'"
            <> (if T.null affected || affected == "<definition>" then "" else " (on '" <> affected <> "')")
            <> " requires the build setting '" <> setting
            <> "', which is disabled (Spec §4.2)"
        )

-- | §4.7: append one audit-ledger entry for an accepted unsafe/debug use.
recordAudit :: Text -> Text -> Text -> Span -> Maybe Text -> CheckM ()
recordAudit facility affected setting sp reason = do
  mn <- gets csModule
  let rec' = AuditRecord facility mn sp affected setting reason
  modify' $ \st -> st {csAuditLedger = csAuditLedger st ++ [rec']}

-- | §4.5: gate a reference to the unchecked-proof escape
-- @unsafeAssertProof@ (and its primitive @__unsafeAssertProof@). It is a
-- compile-time error unless the build enables @allow_unsafe_assert_proof@.
-- The prelude itself defines these names, so a reference from inside the
-- prelude module is not gated. Each accepted use is recorded in the §4.7
-- ledger.
gateUnsafeAssertProof :: GName -> Span -> CheckM ()
gateUnsafeAssertProof (GName gm nm) sp
  | nm `elem` ["unsafeAssertProof", "__unsafeAssertProof"] = do
      cur <- gets csModule
      when (gm == preludeModule && cur /= preludeModule) $ do
        cfg <- gets csUnsafe
        if allowUnsafeAssertProof cfg
          then recordAudit "unsafeAssertProof" nm "allow_unsafe_assert_proof" sp Nothing
          else gateUnsafe "unsafeAssertProof" "allow_unsafe_assert_proof" sp ""
  | otherwise = pure ()

-- | An active-pattern declaration (§17.3.1) elaborates as an ordinary
-- function definition (the pattern name is also a first-class value)
-- and registers pattern metadata: its result classification and the
-- number of pattern arguments before the scrutinee.
elabActivePatternDecl :: DeclMods -> LetDef -> Span -> CheckM ()
elabActivePatternDecl mods ld sp = do
  elabLetDecl mods ld sp
  case ldName ld of
    Nothing -> pure ()
    Just n -> do
      g <- ownName n
      mgd <- gets (Map.lookup g . csGlobals)
      forM_ mgd $ \gd -> do
        (_argc, res) <- unrollExplicit 0 (gdType gd)
        resF <- forceM res
        let kind = case resF of
              VGlobN (GName _ "Option") _ -> Right APOption
              VGlobN (GName _ "Match") _ -> Right APMatch
              VGlobN (GName _ h) _ | h `elem` ["IO", "STM", "Elab"] -> Left h
              _ -> Right APTotal
        case kind of
          Left h ->
            errAt sp "E_ACTIVE_PATTERN_MONADIC_RESULT" (Just "kappa-hs.pattern.active")
              ("an active pattern's result type may not be the monadic type '" <> h
                 <> "'; return Option, Match, or a total view type (§17.3.1)")
          Right k -> do
            -- an Option/total-view pattern cannot return a residue, so
            -- a linear scrutinee would be lost on the miss path
            let explBinders = [b | b <- ldBinders ld, not (bImplicit b)]
                scrutLinear = case reverse explBinders of
                  (b : _) ->
                    bpQuantity (bPrefix b) `elem` [Just S.QOne, Just S.QAtLeastOne]
                      && isNothing (bpBorrow (bPrefix b))
                  [] -> False
            when (scrutLinear && k /= APMatch) $
              errAt sp "E_ACTIVE_PATTERN_LINEARITY_VIOLATION" (Just "kappa-hs.pattern.active")
                "this active pattern consumes a linear scrutinee but cannot thread a residue back on a miss; return 'Match item residue' instead (§17.3)"
            modify' $ \st -> st {csActive = Map.insert g (APInfo k) (csActive st)}
  where
    unrollExplicit :: Int -> Value -> CheckM (Int, Value)
    unrollExplicit = goU 0
      where
        goU expl lvl v = do
          vf <- forceM v
          case vf of
            VPi ic _ _ _ clo -> do
              inner <- clApp clo (VRigid lvl [])
              goU (if ic == Expl then expl + 1 else expl) (lvl + 1) inner
            _ -> pure (expl, vf)

-- | A projection definition (§9.1.1). Both forms register a term facet
-- global (a first-class descriptor) plus 'csProjections' metadata used
-- by the application-site elaborators of §16.1.5/§16.1.6.
--
--   * selector form: term facet @Δ -> Projector Roots T@; the runtime
--     value is @λΔ. λplaces. body@ with each @yield p@ reading @p@.
--   * expanded form: term facet @Δ -> Bundle@, a structural record of
--     @Getter/Opener/Setter/Sinker@ accessor closures with the §9.1.1
--     descriptor-field synthesis (get+set ⇒ open, inout ⇒ set).
--
-- Place lambdas/applications use the canonical (lexicographic) order of
-- the @Roots@ record so descriptor applications can be elaborated from
-- the roots record type alone.
elabProjectionDecl :: DeclMods -> Name -> [Binder] -> Expr -> ProjBody -> Span -> CheckM ()
elabProjectionDecl _mods n binders resTyE body sp = do
  flushPending
  g <- ownName n
  let groups = projBinderGroups binders
      placeBs = [b | (True, b) <- groups]
      ordBs = [b | (False, b) <- groups]
  when (null placeBs) $
    errAt sp "E_PROJECTION_MISSING_PLACE_BINDER" (Just "kappa-hs.projection.place-binder")
      "a projection definition must contain at least one 'place' binder (§9.1.1)"
  -- Δ context: ordinary binders, declaration order
  (ctxD, ordTele) <- elabOrdBinders emptyCtx ordBs
  -- place binder types and the focus, under the full Δ
  places0 <- forM placeBs $ \b -> do
    tyTm <- case binderTypeExpr b of
      Just tyE -> fst <$> inferType ctxD tyE
      Nothing -> freshMeta
    tyV <- evalIn ctxD tyTm
    pure (maybe "_" nameText (bName b), tyTm, tyV)
  let placesLex = sortOn (\(nm, _, _) -> nm) places0
      ctxPl = foldl (\c (nm, _, tv) -> bindCtx nm False tv c) ctxD placesLex
      nPl = length placesLex
  -- the declared focus may depend on the place binders (e.g.
  -- 'Array this.len Byte'); in the descriptor type a unique root is
  -- represented by the §13.2.1 'this' neutral
  (focusTmP, _) <- inferType ctxPl resTyE
  focusV <- evalIn ctxPl focusTmP
  let focusTm = placesToThis nPl focusTmP
      rootsTm = CRecordT [(nm, t) | (nm, t, _) <- placesLex]
      placeNames = [nm | (nm, _, _) <- places0]
      lamsOrd t = foldr (\(q, nm, _) acc -> CLam Expl q nm acc) t ordTele
      pisOrd t = foldr (\(q, nm, ty) acc -> CPi Expl q nm ty acc) t ordTele
      app2 h a b = CApp Expl (CApp Expl (CGlob (gPrel h)) a) b
  case body of
    ProjSelector bodyE0 -> do
      let yields0 = projYieldPlaces bodyE0
      yields <- fmap catMaybes . forM yields0 $ \case
        Right (root, path)
          -- with no place binders at all the declaration-level
          -- diagnostic already covers every yield
          | root `elem` placeNames || null placeNames -> pure (Just (root, path))
        Right (_, _) -> do
          errAt sp "E_PROJECTION_YIELD_INVALID" (Just "kappa-hs.projection.yield")
            "each 'yield' operand must be a stable place rooted in a 'place' binder of this projection (§9.1.1)"
          pure Nothing
        Left ysp -> do
          errAt ysp "E_PROJECTION_YIELD_INVALID" (Just "kappa-hs.projection.yield")
            "each 'yield' operand must be a stable place rooted in a 'place' binder of this projection (§9.1.1)"
          pure Nothing
      let bodyE = stripYields bodyE0
      bodyTm <- check ctxPl bodyE focusV
      let coreTy = pisOrd (app2 "Projector" rootsTm focusTm)
          defTm = lamsOrd (foldr (\(nm, _, _) acc -> CLam Expl QW nm acc) bodyTm placesLex)
      registerProjection g coreTy defTm $
        ProjInfo [isP | (isP, _) <- groups] placeNames True yields
    ProjAccessors clauses -> do
      forM_ (duplicatesOf [k | (k, _, _) <- clauses]) $ \k ->
        errAt sp "E_PROJECTION_ACCESSOR_CLAUSE_DUPLICATE" (Just "kappa-hs.projection.accessor")
          ("the accessor clause '" <> k <> "' appears more than once (§9.1.1)")
      when (length placeBs /= 1) $
        errAt sp "E_PROJECTION_EXPANDED_ACCESSOR_PLACE_BINDER_MISMATCH" (Just "kappa-hs.projection.accessor")
          "an expanded-form projection must have exactly one 'place' binder (§9.1.1)"
      case places0 of
        [] -> pure ()
        ((pName, pTyTm, pTyV) : _) -> do
          let ctxP = bindCtx pName False pTyV ctxD
              zipperTm = CApp Expl (CApp Expl (CApp Expl (CGlob (gPrel "Zipper")) pTyTm) focusTm) focusTm
          zipperV <- evalIn ctxD zipperTm
          let clauseOf k = [(mb, e) | (k', mb, e) <- clauses, k' == k]
              getC = clauseOf "get"
              setC = clauseOf "set"
              inoutC = clauseOf "inout"
              sinkC = clauseOf "sink"
          -- direct clause bodies
          getTm <- forM (take 1 getC) $ \(_, e) -> check ctxP e focusV
          sinkTm <- forM (take 1 sinkC) $ \(_, e) -> check ctxP e focusV
          inoutTm <- forM (take 1 inoutC) $ \(_, e) -> check ctxP e zipperV
          setTm <- forM (take 1 setC) $ \(mb, e) -> do
            let nv = fromMaybe "new_value" (mb >>= fmap nameText . bName)
            nvV <- case mb >>= bType of
              Just tyE -> do
                (t, _) <- inferType ctxD tyE
                evalIn ctxD t
              Nothing -> pure focusV
            tm <- check (bindCtx nv False nvV ctxP) e pTyV
            pure (nv, tm)
          -- synthesized descriptors (§9.1.1)
          synthOpen <-
            case (inoutTm, getC, setC) of
              ([], ((_, getE) : _), ((mb, setE) : _)) -> do
                let nvB = fromMaybe (simpleBinder (Name "new_value" sp)) mb
                    openE =
                      EApp (EVar (Name "Zipper" sp))
                        [ ArgExplicit getE
                        , ArgExplicit (ELambda Nothing [nvB] setE sp)
                        ]
                tm <- check ctxP openE zipperV
                pure [tm]
              _ -> pure []
          synthSet <-
            case (setTm, inoutC) of
              ([], ((_, inoutE) : _)) -> do
                let newE = EVar (Name "__new" sp)
                    fillE = EApp (EDot inoutE (DotName (Name "fill" sp))) [ArgExplicit newE]
                tm <- check (bindCtx "__new" False focusV ctxP) fillE pTyV
                pure [("__new", tm)]
              _ -> pure []
          let lamP t = CLam Expl QW pName t
              caps =
                [ ("get", app2 "Getter" rootsTm focusTm, lamP t) | t <- take 1 getTm ]
                  ++ [ ("open", app2 "Opener" rootsTm focusTm, lamP t)
                     | t <- take 1 (inoutTm ++ synthOpen)
                     ]
                  ++ [ ("set", app2 "Setter" rootsTm focusTm, lamP (CLam Expl Q1 nv t))
                     | (nv, t) <- take 1 (setTm ++ synthSet)
                     ]
                  ++ [ ("sink", app2 "Sinker" rootsTm focusTm, lamP t) | t <- take 1 sinkTm ]
              capsSorted = sortOn (\(nm, _, _) -> nm) caps
              coreTy = pisOrd (CRecordT [(nm, t) | (nm, t, _) <- capsSorted])
              defTm = lamsOrd (CRecordV [(nm, t) | (nm, _, t) <- capsSorted])
          registerProjection g coreTy defTm $
            ProjInfo [isP | (isP, _) <- groups] placeNames False []
  where
    stripYields e0 = case e0 of
      EApp (EVar y) [ArgExplicit e] | nameText y == "yield" -> e
      EIf alts mels isp ->
        EIf [(c, stripYields b) | (c, b) <- alts] (stripYields <$> mels) isp
      EMatch scrut cases msp ->
        EMatch scrut
          [ case c of
              MatchCase p mg b csp -> MatchCase p mg (stripYields b) csp
              other -> other
          | c <- cases
          ]
          msp
      EBlock ds (Just fin) bsp -> EBlock ds (Just (stripYields fin)) bsp
      EAscription e tyE asp -> EAscription (stripYields e) tyE asp
      e -> e

-- | Rewrite references to the innermost @n@ binders (a projection's
-- place binders) into the §13.2.1 @this@ neutral, dropping the binders.
-- Used to express a root-dependent focus type under Δ alone.
placesToThis :: Int -> Term -> Term
placesToThis n = go 0
  where
    go d t = case t of
      CVar i
        | i >= d ->
            if i - d < n then CGlob thisG else CVar (i - n)
        | otherwise -> t
      CGlob _ -> t
      CLam ic q nm b -> CLam ic q nm (go (d + 1) b)
      CPi ic q nm a b -> CPi ic q nm (go d a) (go (d + 1) b)
      CApp ic f a -> CApp ic (go d f) (go d a)
      CSort _ -> t
      CLit _ -> t
      CCtor g as -> CCtor g (map (go d) as)
      CMatch s alts ->
        CMatch (go d s)
          [CaseAlt p (fmap (go (d + patBindersC p)) g) (go (d + patBindersC p) b) | CaseAlt p g b <- alts]
      CRecordT fs -> CRecordT [(nm, go d x) | (nm, x) <- fs]
      CRecordV fs -> CRecordV [(nm, go d x) | (nm, x) <- fs]
      CProj e f -> CProj (go d e) f
      CProjAt e f i -> CProjAt (go d e) f i
      CVariantT ms -> CVariantT (map (go d) ms)
      CInject tag e -> CInject tag (go d e)
      CLet q nm a b c -> CLet q nm (go d a) (go d b) (go (d + 1) c)
      CLetRec q nm a b c -> CLetRec q nm (go d a) (go (d + 1) b) (go (d + 1) c)
      CMeta _ -> t
      CDo _ _ -> t
      CSealE ls e -> CSealE ls (go d e)
      CSigT ls e -> CSigT ls (go d e)
      CThunkE e -> CThunkE (go d e)
      CLazyE e -> CLazyE (go d e)
      CForceE e -> CForceE (go d e)
      CIf a b c -> CIf (go d a) (go d b) (go d c)
      CQuote qs slots -> CQuote qs (map (go d) slots)

-- | Elaborate the ordinary (non-place) binders of a projection in
-- declaration order, returning the extended context and the telescope.
elabOrdBinders :: Ctx -> [Binder] -> CheckM (Ctx, [(Q, Text, Term)])
elabOrdBinders ctx0 [] = pure (ctx0, [])
elabOrdBinders ctx0 (b : bs) = do
  tyTm <- case binderTypeExpr b of
    Just tyE -> fst <$> inferType ctx0 tyE
    Nothing -> freshMeta
  tyV <- evalIn ctx0 tyTm
  let nm = maybe "_" nameText (bName b)
      ctx1 = bindCtx nm (bImplicit b) tyV ctx0
  (ctx2, rest) <- elabOrdBinders ctx1 bs
  pure (ctx2, (binderQ b, nm, tyTm) : rest)

-- | Register a projection's term facet and projection-facet metadata.
registerProjection :: GName -> Term -> Term -> ProjInfo -> CheckM ()
registerProjection g coreTy defTm pj = do
  flushPending
  coreTy' <- zonkTermM 0 coreTy
  defTm' <- zonkTermM 0 defTm
  tyV <- evalIn emptyCtx coreTy'
  tmV <- evalIn emptyCtx defTm'
  addGlobal g (GlobalDef tyV (Just tmV) False)
  -- Record the projection's core definition so the native backend lowers the
  -- real selector (a CLam chain); without it the global has no recorded body
  -- and would be erased to the unit placeholder — a silent miscompile.
  recordCoreBody g defTm'
  modify' $ \st -> st {csProjections = Map.insert g pj (csProjections st)}

elabLetDecl :: DeclMods -> LetDef -> Span -> CheckM ()
-- the parsed decreases clause is not consulted: termination is verified
-- by the structural analysis below (see IMPLEMENTATION_NOTES.md)
elabLetDecl _ (LetDef (Just n) _ Nothing _ binders mResTy _mdec body) sp = do
  -- resolve any goals postponed from signature elaboration first, so the
  -- signature's value is canonical while checking the body
  flushPending
  g <- ownName n
  noteDefinition g sp
  -- §7.4: record receiver-marked explicit binder positions (method
  -- sugar inserts the receiver at the unique such binder)
  let recvIdxs =
        [ i
        | (i, rb) <- zip [(0 :: Int) ..] [rb | rb <- binders, not (bImplicit rb)]
        , bReceiver rb /= NoReceiver
        ]
  unless (null recvIdxs) $
    modify' $ \stM -> stM {csReceivers = Map.insert g recvIdxs (csReceivers stM)}
  st <- get
  msig <- pure (Map.lookup g (csGlobals st))
  case msig of
    Just gd | Nothing <- gdValue gd -> pure ()
    _ ->
      -- no governing signature: the binding is manifest (§2.8.4)
      modify' $ \stM -> stM {csManifest = Map.insert g () (csManifest stM)}
  -- §13.2.10/§2.8: a signature-governed binding whose definiens is an
  -- identity-preserving form (record/seal/projection chain, not a
  -- function result) still preserves static-object identity
  let markManifestIfShaped tm =
        when (manifestShaped tm) $
          modify' $ \stM -> stM {csManifest = Map.insert g () (csManifest stM)}
      manifestShaped = \case
        CGlob _ -> True
        CRecordV _ -> True
        CSealE _ x -> manifestShaped x
        CProj x _ -> manifestShaped x
        CProjAt x _ _ -> manifestShaped x
        _ -> False
  case msig of
    Just gd | Nothing <- gdValue gd -> do
      -- Pending goals raised inside the signature may have been solved
      -- to the signature's own binder rigids; re-quote the type so the
      -- solutions are baked in as proper de Bruijn variables.
      sigTy <- do
        ec <- ec_
        evalIn emptyCtx (quote ec 0 (gdType gd))
      addGlobal g gd {gdType = sigTy}
      -- signature first: check the definition against it (recursion OK)
      -- §7.1/§7.2: a definition body is a term-expression position, so
      -- the same-spelling constructor facet wins there even under a
      -- sort-typed signature (reaching the reified type facet requires
      -- the explicit `type T` selector, §7.1.1)
      ctorFacetWins <- case body of
        EVar bn | null binders -> do
          sigF <- forceM sigTy
          case sigF of
            VSort _ -> do
              mg <- lookupGlobalName (nameText bn)
              case mg of
                Just bg -> gets (Map.member bg . csCtors)
                Nothing -> pure False
            _ -> pure False
        _ -> pure False
      tm0 <-
        if ctorFacetWins
          then case body of
            EVar bn -> do
              (tm', ty') <- infer emptyCtx (EVar bn)
              expectType emptyCtx (nameSpan bn) ty' sigTy
              pure tm'
            _ -> checkAgainstSig (Just (nameText n)) sigTy binders body sp
          else checkAgainstSig (Just (nameText n)) sigTy binders body sp
      flushPending
      tm <- zonkTermM 0 tm0
      tmV <- evalIn emptyCtx tm
      let recursive = occursGlobal g tm
          isFunction = case tm of
            CLam {} -> True
            _ -> not (null binders)
      reducible <-
        if recursive && not isFunction
          then do
            -- a self-referential value (no intervening function
            -- abstraction) is a definitional cycle (§15.3, §16.4)
            errAt sp "E_RECURSIVE_VALUE_CYCLE" (Just "kappa.termination.failure")
              ("recursive value cycle: '" <> nameText n
                 <> "' refers to itself without an intervening function abstraction, so its evaluation cannot terminate (§15.3)")
            pure False
          else if recursive
            then do
              let okStructural = structuralOK g binders tm
              unless okStructural $
                report $
                  withNote "the definition is accepted but not conversion-reducible (§15.1)" $
                    diag SevWarning StageElaborate "W_TERMINATION_UNVERIFIED" (Just "kappa.termination.failure") sp
                      ("could not verify structural termination of '" <> nameText n <> "' (§15.3)")
              pure okStructural
            else pure True
      markManifestIfShaped tm
      recordCoreBody g tm
      addGlobal g gd {gdType = sigTy, gdValue = Just tmV, gdReducible = reducible}
    _ -> do
      -- a previous definition with a value: duplicate declaration (§9.2)
      case msig of
        Just gd' | isJust (gdValue gd') -> do
          enrich <- duplicateRelated (nameText n) g sp
          report $ enrich $
            diag SevError StageElaborate "E_DUPLICATE_DECLARATION" (Just "kappa-hs.name.duplicate") sp
              ("duplicate declaration of '" <> nameText n <> "'")
        _ -> pure ()
      -- no preceding signature: pre-register the name so self-references
      -- resolve and are reported as recursion-without-signature (§9.2)
      placeholderTy <- freshMetaV emptyCtx
      addGlobal g (GlobalDef placeholderTy Nothing False)
      (tm0, ty) <- elabFunction binders mResTy body sp
      flushPending
      tm <- zonkTermM 0 tm0
      when (occursGlobal g tm) $
        errAt sp "E_RECURSION_REQUIRES_SIGNATURE" (Just "kappa.type.missing-signature")
          "recursive definitions require a preceding signature declaration (§15, §9.2)"
      tmV <- evalIn emptyCtx tm
      recordCoreBody g tm
      addGlobal g (GlobalDef ty (Just tmV) True)
elabLetDecl _ (LetDef Nothing _ (Just pat) _ [] mty Nothing body) sp = do
  -- top-level pattern binding: bind each variable to a projection
  (bodyTm, bodyTy) <- case mty of
    Just tyE -> do
      (tyTm, _) <- inferType emptyCtx tyE
      tyV <- evalIn emptyCtx tyTm
      tm <- check emptyCtx body tyV
      pure (tm, tyV)
    Nothing -> infer emptyCtx body
  checkIrrefutable emptyCtx pat bodyTy sp
  case pat of
    PVar n -> do
      g <- ownName n
      tmV <- evalIn emptyCtx bodyTm
      addGlobal g (GlobalDef bodyTy (Just tmV) True)
      -- Record the elaborated core body so the native backend lowers the
      -- real value (a top-level prefixed binding `let 1 x = e` / `let &x = e`
      -- reaches here as a PVar pattern); without this it has no recorded body
      -- and would be erased to the unit placeholder — a silent miscompile.
      recordCoreBody g bodyTm
    _ -> do
      (patC, ctxP, _) <- elabPattern emptyCtx pat bodyTy
      let names = ctxEntries ctxP
      forM_ (zip [0 ..] names) $ \(i, entry) -> do
        let proj = CMatch bodyTm [CaseAlt patC Nothing (CVar i)]
        g <- ownName (Name (ceName entry) sp)
        projV <- evalIn emptyCtx proj
        addGlobal g (GlobalDef (ceType entry) (Just projV) True)
        recordCoreBody g proj
elabLetDecl _ _ sp =
  unsupportedAt sp "this let-definition form is not supported at top level"

occursGlobal :: GName -> Term -> Bool
occursGlobal g = go
  where
    go = \case
      CGlob g' -> g == g'
      CApp _ f a -> go f || go a
      CLam _ _ _ b -> go b
      CPi _ _ _ a b -> go a || go b
      CCtor _ as -> any go as
      CMatch s alts -> go s || any (\(CaseAlt _ gd b) -> maybe False go gd || go b) alts
      CRecordT fs -> any (go . snd) fs
      CRecordV fs -> any (go . snd) fs
      CProj e _ -> go e
      CProjAt e _ _ -> go e
      CVariantT ms -> any go ms
      CInject _ e -> go e
      CLet _ _ a b c -> go a || go b || go c
      CLetRec _ _ a b c -> go a || go b || go c
      CIf a b c -> go a || go b || go c
      CThunkE e -> go e
      CLazyE e -> go e
      CForceE e -> go e
      CDo _ items -> any goK items
      _ -> False
    goK = \case
      KBind _ _ t -> go t
      KLet _ _ t -> go t
      KLetQ _ t m -> go t || maybe False (go . snd) m
      KExpr t -> go t
      KVarItem _ t -> go t
      KAssign _ _ t -> go t
      KReturn t -> go t
      KWhile _ c b e -> go c || any goK b || maybe False (any goK) e
      KFor _ _ s b e -> go s || any goK b || maybe False (any goK) e
      KIf alts e -> any (\(c, b) -> go c || any goK b) alts || maybe False (any goK) e
      KDefer _ t -> go t
      KUsing _ a r -> go a || go r
      KSubDo _ b -> any goK b
      _ -> False

-- Structural-descent verification (§15.3 minimum, direct recursion):
-- accepted iff some explicit parameter position strictly decreases at
-- every direct self-call, where "decreases" means the argument is a
-- variable bound by a constructor sub-pattern of a match on that
-- parameter (or a variable transitively below it).
structuralOK :: GName -> [Binder] -> Term -> Bool
structuralOK g _ tm0 =
  let (params, body, depth0) = peel [] tm0 0
   in case params of
        [] -> False
        _ ->
          let calls = collect depth0 Map.empty body
           in case calls of
                Nothing -> False -- a self-call escaped spine position
                Just cs ->
                  any
                    (\i -> all (decreasingAt i) cs)
                    [0 .. length params - 1]
  where
    -- peel leading lambdas; record levels of explicit params
    peel acc (CLam ic _ _ b) d = peel (acc ++ [(ic, d)]) b (d + 1)
    peel acc t d = ([lvl | (Expl, lvl) <- acc], t, d)
      where
        _params = acc

    paramLevels = let (ps, _, _) = peel [] tm0 0 in ps

    -- collect self-calls: depth and per-call explicit args as
    -- (argIndex, Maybe boundLevelSubOfParam)
    -- subMap: level -> root param level it descends from
    collect :: Int -> Map.Map Int Int -> Term -> Maybe [[(Int, Maybe Int)]]
    collect d sub t = case t of
      CApp {} ->
        case spineOf t of
          (CGlob g', args) | g' == g ->
              Just [zipWith (\i a -> (i, argRoot d sub a)) [0 ..] [a | (Expl, a) <- args]]
          (f, args) -> do
            rs <- mapM (collect d sub . snd) args
            r0 <- collect d sub f
            pure (r0 ++ concat rs)
      CGlob g' | g' == g -> Nothing -- bare self-reference (escapes analysis)
      CLam _ _ _ b -> collect (d + 1) sub b
      CPi _ _ _ a b -> (++) <$> collect d sub a <*> collect (d + 1) sub b
      CLet _ _ a b c -> do
        ra <- collect d sub a
        rb <- collect d sub b
        rc <- collect (d + 1) sub c
        pure (ra ++ rb ++ rc)
      CLetRec _ _ a b c -> do
        ra <- collect d sub a
        rb <- collect (d + 1) sub b
        rc <- collect (d + 1) sub c
        pure (ra ++ rb ++ rc)
      CIf a b c -> concat3 <$> collect d sub a <*> collect d sub b <*> collect d sub c
      CMatch scrut alts -> do
        rs <- collect d sub scrut
        let scrutLvl = case scrut of
              CVar i -> rootOf (d - 1 - i)
              _ -> Nothing
            rootOf lvl
              | lvl `elem` paramLevels = Just lvl
              | otherwise = Map.lookup lvl sub
        ralts <- forM alts $ \(CaseAlt pat gd b) -> do
          let nb = patBindersC pat
              newLvls = [d .. d + nb - 1]
              sub' = case scrutLvl of
                Just root | ctorBinds pat -> foldr (\l m -> Map.insert l root m) sub newLvls
                _ -> sub
          rg <- maybe (Just []) (collect (d + nb) sub') gd
          rb <- collect (d + nb) sub' b
          pure (rg ++ rb)
        pure (rs ++ concat ralts)
      CCtor _ as -> concat <$> mapM (collect d sub) as
      CRecordT fs -> concat <$> mapM (collect d sub . snd) fs
      CRecordV fs -> concat <$> mapM (collect d sub . snd) fs
      CProj e _ -> collect d sub e
      CProjAt e _ _ -> collect d sub e
      CVariantT ms -> concat <$> mapM (collect d sub) ms
      CInject _ e -> collect d sub e
      CThunkE e -> collect d sub e
      CLazyE e -> collect d sub e
      CForceE e -> collect d sub e
      CDo _ _ -> Just [] -- loops handle their own progress; no self-calls expected
      _ -> Just []
      where
        concat3 a b c = a ++ b ++ c

    ctorBinds = \case
      CPCtor _ _ -> True
      CPInject _ _ -> True
      CPOr ps _ -> all ctorBinds ps
      CPAs _ p -> ctorBinds p
      _ -> False

    spineOf :: Term -> (Term, [(Icit, Term)])
    spineOf = go []
      where
        go acc (CApp ic f a) = go ((ic, a) : acc) f
        go acc f = (f, acc)

    -- the root param level an argument descends from, if any
    argRoot d sub = \case
      CVar i ->
        let lvl = d - 1 - i
         in Map.lookup lvl sub
      _ -> Nothing

    decreasingAt i call =
      case lookup i call of
        Just (Just root) -> root `elem` take (i + 1) paramLevels || root `elem` paramLevels
        _ -> False

checkAgainstSig :: Maybe Text -> Value -> [Binder] -> Expr -> Span -> CheckM Term
checkAgainstSig retName sigTy binders body sp = do
  -- consume binders against the signature's Pi telescope. §18.5: the body
  -- is the named function's body, so a `return@<name>` inside it resolves.
  go (emptyCtx {ctxReturnTarget = retName}) sigTy binders
  where
    -- §9.1: `let name = \binders -> body` is a named function `name`; the
    -- RHS lambda inherits the name as its return target. Inject it as the
    -- lambda's label so `return@name` inside the body resolves (an explicit
    -- label on the lambda is kept).
    body' = case (binders, body, retName) of
      ([], ELambda Nothing lbs lbody lsp, Just nm) -> ELambda (Just (Name nm lsp)) lbs lbody lsp
      _ -> body
    -- The function body do IS the return target's completion boundary, so
    -- elaborate it directly with ctxReturnTarget preserved (the generic
    -- EDo path would reset it, treating it as a nested do). §18.5.
    go ctx ty [] = case body' of
      EDo mlbl items isp -> do
        (tm, ty') <- elabDo ctx mlbl items isp (Just ty)
        expectType ctx isp ty' ty
        pure tm
      _ -> check ctx body' ty
    go ctx ty0 (b : rest) = do
      ty <- forceM ty0
      case ty of
        VPi Impl q nm dom clo
          | not (bImplicit b)
          , (nameText <$> bName b) /= Just nm ->
              -- skip implicit binder: bind it for the body (an explicit
              -- definition binder with the SAME name instead claims the
              -- implicit parameter, e.g. `let f r = …` against
              -- `f : forall (r : T). …`)
              skipImplicit ctx q nm dom clo (b : rest)
        VPi Impl q nm dom clo
          | bImplicit b
          , nm /= "_"
          , (nameText <$> bName b) /= Just nm
          , Just tyE <- binderTypeExpr b -> do
              -- an annotated implicit definition binder claims this Pi
              -- only when its annotation matches the domain; otherwise
              -- it claims a later implicit (e.g. a `(@d : Trait a)`
              -- evidence binder against `forall a. (@_ : Trait a) -> …`
              -- where the §11.3.3 synthesized `a` stays auto-bound)
              st0 <- get
              nBefore <- gets (length . csDiags)
              ok <- do
                (tyTm, _) <- inferType ctx tyE
                tyV <- evalIn ctx tyTm
                unify ctx dom tyV
              nAfter <- gets (length . csDiags)
              put st0
              if ok && nAfter == nBefore
                then claim ctx Impl q nm dom clo b rest
                else skipImplicit ctx q nm dom clo (b : rest)
        VPi ic q nm dom clo -> claim ctx ic q nm dom clo b rest
        _ -> do
          errAt sp "E_SIGNATURE_ARITY" (Just "kappa-hs.type.signature-arity")
            "definition has more parameters than its signature type"
          check ctx body ty
    skipImplicit ctx q nm dom clo bs = do
      let ctx' = bindCtx nm True dom ctx
      cod <- clApp clo (VRigid (ctxLen ctx) [])
      CLam Impl q nm <$> go ctx' cod bs
    claim ctx ic q nm dom clo b rest = do
      let bn = fromMaybe nm (nameText <$> bName b)
      forM_ (binderTypeExpr b) $ \tyE -> do
        (tyTm, _) <- inferType ctx tyE
        tyV <- evalIn ctx tyTm
        expectType ctx (bSpan b) dom tyV
      unless (ic == (if bImplicit b then Impl else Expl) || ic == Impl) $
        errAt (bSpan b) "E_BINDER_MISMATCH" (Just "kappa-hs.type.binder")
          "binder implicitness does not match the signature"
      let ctx' = bindCtx bn (bImplicit b) dom ctx
      cod <- clApp clo (VRigid (ctxLen ctx) [])
      CLam ic q bn <$> go ctx' cod rest

elabFunction :: [Binder] -> Maybe Expr -> Expr -> Span -> CheckM (Term, Value)
elabFunction [] mResTy body _ = case mResTy of
  Just tyE -> do
    (tyTm, _) <- inferType emptyCtx tyE
    tyV <- evalIn emptyCtx tyTm
    tm <- check emptyCtx body tyV
    pure (tm, tyV)
  Nothing -> do
    (tm, ty) <- infer emptyCtx body
    insertAllImplicits emptyCtx (exprSpan body) tm ty
elabFunction binders mResTy body sp = do
  let bodyE = case mResTy of
        Just tyE -> EAscription body tyE sp
        Nothing -> body
  elabLambda emptyCtx binders bodyE sp Nothing

-- | §14.3 instance pre-pass: elaborate and register the head of every
-- top-level instance declaration (instance-set entry plus the
-- dictionary global's type) before any declaration body is checked,
-- so instance visibility within the module does not depend on
-- declaration order. Instance heads depend only on header-pass
-- artifacts (traits, data types, aliases; lowercase head names are
-- implicitly universalized per §11.3.3), so this is sound ahead of
-- the body pass. Member bodies are still checked in source order by
-- 'elabInstance'.
instanceHeadPass :: Decl -> CheckM ()
instanceHeadPass = \case
  DInstance (InstanceDecl premises hd _) sp -> do
    mpi <- registerInstanceHead premises hd sp
    modify' $ \st -> st {csPreInstances = Map.insert sp mpi (csPreInstances st)}
  _ -> pure ()

-- | Elaborate an instance head and register the dictionary global
-- (type only — 'elabInstance' fills the value) and the instance-set
-- entry consulted by §14.3.1 search.
registerInstanceHead :: [Expr] -> Expr -> Span -> CheckM (Maybe PreInstance)
registerInstanceHead premises hd sp = do
  -- head must be Trait args...
  (traitG, argEs) <- instSplitHead hd
  st <- get
  case traitG >>= \g -> g <$ Map.lookup g (csTraits st) of
    Nothing -> do
      errAt sp "E_INSTANCE_HEAD" (Just "kappa-hs.trait.bad-instance-head")
        "instance head must be a trait applied to type arguments"
      pure Nothing
    Just g -> do
      -- collect implicitly-universalized lowercase variables (§11.3.3)
      let fvs = nub (concatMap freeLower (hd : premises))
      -- telescope: fvs as Type params, then premise dicts
      let teleLen = length fvs + length premises
      -- elaborate under fvs bound
      let ctx0 = foldl (\c v -> bindCtx v False (VSort 0) c) emptyCtx fvs
      premTms <- forM premises $ \p -> fst <$> inferType ctx0 p
      ctxP' <- instBindPremises ctx0 premTms
      -- head arguments check against the trait constructor's parameter
      -- types (so type constructors are valid arguments of
      -- higher-kinded traits, §14.1.2)
      traitTy <- gets (fmap gdType . Map.lookup g . csGlobals)
      argTms <- case traitTy of
        Just tt -> instCheckHeadArgs ctxP' tt argEs
        Nothing -> mapM (\e -> fst <$> inferType ctxP' e) argEs
      -- register the instance before checking members so member bodies
      -- can use the instance being defined (recursive instances, §14.3)
      dictName <- freshNameM ("__inst_" <> gnameText g <> "_")
      dictG <- gets (\s -> GName (csModule s) dictName)
      dictTy <- instDictTy g fvs premTms argTms
      addGlobal dictG (GlobalDef dictTy Nothing False)
      modify' $ \s ->
        s
          { csInstances =
              InstanceEntry g teleLen (map (shiftTerm (length premises) 0) premTms) argTms dictG
                : csInstances s
          }
      pure (Just (PreInstance g fvs premTms argTms dictG))

instSplitHead :: Expr -> CheckM (Maybe GName, [Expr])
instSplitHead e = case e of
  EApp f args -> do
    (g, es) <- instSplitHead f
    pure (g, es ++ [a | ArgExplicit a <- args])
  EVar n -> do
    mg <- lookupGlobalName (nameText n)
    pure (mg, [])
  _ -> pure (Nothing, [])

-- | Bind the instance's premise dictionaries as implicit-local candidates.
-- Each premise term was elaborated under the fv binders only, so the k-th
-- premise sits under k earlier premise binders and must be shifted by k. Each
-- dictionary also gets a DISTINCT name: 'localCandidate' dedups candidates by
-- name, so premises sharing a name (e.g. two @Eq@ premises @Eq e@, @Eq a@)
-- would shadow each other and the second goal would never resolve locally.
instBindPremises :: Ctx -> [Term] -> CheckM Ctx
instBindPremises ctx0 = go (0 :: Int) ctx0
  where
    go _ c [] = pure c
    go i c (p : rest) = do
      pv <- evalIn c (shiftTerm i 0 p)
      go (i + 1) (bindCtx ("__prem" <> T.pack (show i)) True pv c) rest

instCheckHeadArgs :: Ctx -> Value -> [Expr] -> CheckM [Term]
instCheckHeadArgs _ _ [] = pure []
instCheckHeadArgs ctx ty (e : es) = do
  t <- forceM ty
  case t of
    VPi Expl _ _ dom clo -> do
      tm <- check ctx e dom
      v <- evalIn ctx tm
      rest <- clApp clo v >>= \cod -> instCheckHeadArgs ctx cod es
      pure (tm : rest)
    _ -> do
      tm <- fst <$> inferType ctx e
      rest <- instCheckHeadArgs ctx t es
      pure (tm : rest)

instDictTy :: GName -> [Text] -> [Term] -> [Term] -> CheckM Value
instDictTy traitG fvs premTms argTms = do
  -- premises were elaborated under the fv binders only; the k-th
  -- premise domain sits under k earlier premise binders, so shift by
  -- k. The head ('argTms') was elaborated under fvs + all premises
  -- and is already correctly indexed.
  let dictHead = foldl (\f a -> CApp Expl f a) (CGlob traitG) argTms
      withPrems = go (0 :: Int) premTms
      go _ [] = dictHead
      go k (p : ps) = CPi Impl QW "__p" (shiftTerm k 0 p) (go (k + 1) ps)
      nest [] = withPrems
      nest (v : vs) = CPi Impl Q0 v (CSort 0) (nest vs)
  evalIn emptyCtx (nest fvs)

elabInstance :: InstanceDecl -> Span -> CheckM ()
elabInstance (InstanceDecl premises hd members) sp = do
  flushPending
  stash <- gets (Map.lookup sp . csPreInstances)
  mpi <- case stash of
    -- head already elaborated (or already rejected) by the pre-pass
    Just mpi -> pure mpi
    Nothing -> registerInstanceHead premises hd sp
  mpti <- case mpi of
    Nothing -> pure Nothing
    Just pinst -> gets (fmap ((,) pinst) . Map.lookup (piTrait pinst) . csTraits)
  forM_ mpti $ \(pinst, ti) -> do
    let g = piTrait pinst
        fvs = piFvs pinst
        premTms = piPremTms pinst
        argTms = piArgTms pinst
        dictG = piDictG pinst
        ctx0 = foldl (\c v -> bindCtx v False (VSort 0) c) emptyCtx fvs
    ctxP' <- instBindPremises ctx0 premTms
    do
      -- §14.1.4/§14.3.3: every supertrait premise of the trait must be
      -- satisfiable at the instance head (from the instance's own
      -- premises — including their transitive supertrait conformance
      -- paths — or the global instance set); the evidence found is
      -- stored in the dictionary's supertrait field
      superFields <- forM (tiSupers ti) $ \(fn, supClosed) -> do
        ec <- ec_
        argVs <- mapM (evalIn ctxP') argTms
        supF <- evalIn ctxP' supClosed
        supGoal <- forceM (evalApp ec supF [(Expl, a) | a <- argVs])
        mEv <- traitEvidence ctxP' sp supGoal
        case mEv of
          Just tm -> pure (Just (fn, tm))
          Nothing -> do
            gT <- quoteIn ctxP' supGoal
            errAt sp "E_TRAIT_SUPERTRAIT_UNSATISFIED" (Just "kappa-hs.trait.supertrait-unsatisfied")
              ("instance does not satisfy the supertrait premise '" <> renderTerm gT <> "' of trait '" <> gnameText g <> "' (§14.1.4)")
            pure Nothing
      -- member definitions checked against member types, in declaration
      -- order; already-checked members (associated static members in
      -- particular) instantiate the dict binder of later member types
      -- (§14.3.4)
      let goFields done [] = pure (reverse done)
          goFields done (mn : rest) = do
            mfield <- case findMember mn members of
              Just (LetDef _ _ _ _ mbinders mResTy _ mbody, msp) -> do
                memberTyV <- memberSigInstance g mn argTms ctxP' (catMaybes superFields ++ reverse done)
                tm <- checkMemberAgainst ctxP' memberTyV mbinders mResTy mbody msp
                pure (Just (mn, tm))
              Nothing -> case Map.lookup mn (tiDefaults ti) of
                -- the trait's default definition fills the member (§14.2.3)
                -- the default's own annotation mentions trait parameters
                -- and is superseded by the instantiated member type
                Just (LetDef _ _ _ _ dbinders _ _ dbody) -> do
                  memberTyV <- memberSigInstance g mn argTms ctxP' (catMaybes superFields ++ reverse done)
                  tm <- checkMemberAgainst ctxP' memberTyV dbinders Nothing dbody sp
                  pure (Just (mn, tm))
                Nothing -> do
                  errAt sp "E_INSTANCE_MEMBER_MISSING" (Just "kappa-hs.trait.member-missing")
                    ("instance does not define member '" <> mn <> "'")
                  pure Nothing
            goFields (maybe done (: done) mfield) rest
      dictFields <- goFields [] (tiMembers ti)
      flushPending
      let fields = sortOn fst (catMaybes superFields ++ dictFields)
          dictBody = CRecordV fields
          -- order: fvs outermost, then premises
          wrapped =
            foldr (\v acc -> CLam Impl Q0 v acc) (foldr (\_ acc -> CLam Impl QW "__p" acc) dictBody premises) fvs
      wrapped' <- zonkTermM 0 wrapped
      dictV <- evalIn emptyCtx wrapped'
      dictTy <- gets (maybe (VSort 0) gdType . Map.lookup dictG . csGlobals)
      addGlobal dictG (GlobalDef dictTy (Just dictV) True)
      -- §14.1.1: trait evidence lowers to a runtime record of the member
      -- implementations; capture its KCore body for the native backend.
      recordCoreBody dictG wrapped'
      -- §14.3/§33.2.1: program-level coherence — an overlapping pair of
      -- instances is rejected at declaration unless the instantiated
      -- evidence artifacts are equivalent (structural coherence mode),
      -- whether or not any use site resolves through them. Only
      -- already-elaborated instances (registered before this one) are
      -- compared here: the later member of a pair judges the overlap
      -- when its own dictionary value is complete.
      stPost <- get
      case dropWhile ((/= dictG) . ieDict) (csInstances stPost) of
        (newIe : priors) ->
          forM_ [ie | ie <- priors, ieTrait ie == g] $ \prior ->
            checkInstanceOverlap sp g newIe prior
        [] -> pure ()
  where
    findMember mn ms =
      case [ (ld, dsp) | DLet _ ld@(LetDef (Just dn) _ _ _ _ _ _ _) dsp <- ms, nameText dn == mn
           ] of
        (x : _) -> Just x
        [] -> Nothing

    memberSigInstance traitG mn argTms ctx doneFields = do
      mt <- globalTerm (memberGlobal traitG mn)
      case mt of
        Just (_, projTy) -> do
          argVs <- mapM (evalIn ctx) argTms
          peelArgs projTy argVs
        Nothing -> pure (VSort 0)
      where
        peelArgs ty [] = do
          t <- forceM ty
          case t of
            VPi Impl _ _ _ clo -> do
              -- the dict binder: instantiate with the partial dictionary
              -- being defined, so member types that project earlier
              -- members — associated static members above all — see the
              -- instance's definitions (§14.3.4)
              fvs <- forM doneFields $ \(fn, ftm) -> (,) fn <$> evalIn ctx ftm
              clApp clo (VRecordV (sortOn fst fvs))
            _ -> pure t
        peelArgs ty (a : as) = do
          t <- forceM ty
          case t of
            VPi Impl _ _ _ clo -> do
              r <- clApp clo a
              peelArgs r as
            _ -> pure t

    checkMemberAgainst ctx memberTy mbinders mResTy mbody msp =
      case mbinders of
        [] -> check ctx (maybe mbody (\t -> EAscription mbody t msp) mResTy) memberTy
        _ -> checkLambdaAgainst ctx memberTy mbinders mbody msp

    checkLambdaAgainst ctx ty binders body msp = do
      t <- forceM ty
      case (binders, t) of
        ([], _) -> check ctx body t
        (b : rest, VPi Impl q nm dom clo)
          | not (bImplicit b) -> do
              let ctx' = bindCtx nm True dom ctx
              cod <- clApp clo (VRigid (ctxLen ctx) [])
              CLam Impl q nm <$> checkLambdaAgainst ctx' cod (b : rest) body msp
        (b : rest, VPi ic q nm dom clo) -> do
          let bn = fromMaybe nm (nameText <$> bName b)
              ctx' = bindCtx bn (bImplicit b) dom ctx
          cod <- clApp clo (VRigid (ctxLen ctx) [])
          CLam ic q bn <$> checkLambdaAgainst ctx' cod rest body msp
        (_ : _, _) -> do
          errAt msp "E_SIGNATURE_ARITY" (Just "kappa-hs.type.signature-arity")
            "instance member has more parameters than the trait member type"
          check ctx body t

-- | Evidence for a trait goal: the local implicit context first
-- (§16.3.3), then the instance set (§14.3.1), then §14.3.3 supertrait
-- conformance paths projected from local evidence.
traitEvidence :: Ctx -> Span -> Value -> CheckM (Maybe Term)
traitEvidence ctx sp goal = do
  mLoc <- localCandidate ctx sp Q0 goal
  case mLoc of
    Just tm -> pure (Just tm)
    Nothing -> do
      mInst <- instanceSearch ctx sp goal
      case mInst of
        Just tm -> pure (Just tm)
        Nothing -> superCandidate ctx goal

-- | §14.3.3 conformance-path selection: project the goal's evidence
-- out of an in-scope implicit binder through declared-supertrait
-- dictionary fields.
superCandidate :: Ctx -> Value -> CheckM (Maybe Term)
superCandidate ctx goal = go 0 (ctxEntries ctx)
  where
    go _ [] = pure Nothing
    go i (e : rest)
      | ceImplicitLocal e = do
          m <- supertraitProject ctx 4 (CVar i) (ceType e) goal
          case m of
            Just tm -> pure (Just tm)
            Nothing -> go (i + 1) rest
      | otherwise = go (i + 1) rest

-- §14.3.3 conformance paths (depth-bounded): evidence 'evTm' of type
-- 'evTy' (a trait application) yields the trait goal 'goal' through
-- the evidence trait's transitive supertrait premises, as a chain of
-- supertrait-field projections.
supertraitProject :: Ctx -> Int -> Term -> Value -> Value -> CheckM (Maybe Term)
supertraitProject _ 0 _ _ _ = pure Nothing
supertraitProject ctx depth evTm evTy goal = do
  ev <- forceM evTy
  case ev of
    VGlobN tg args -> do
      mti <- gets (Map.lookup tg . csTraits)
      case mti of
        Just ti -> anyPath (tiSupers ti)
          where
            anyPath [] = pure Nothing
            anyPath ((fn, supClosed) : rest) = do
              ec <- ec_
              supF <- evalIn ctx supClosed
              supV <- forceM (evalApp ec supF [(Expl, a) | (_, a) <- args])
              st0 <- get
              ok <- unify ctx supV goal
              if ok
                then pure (Just (CProj evTm fn))
                else do
                  put st0
                  found <- supertraitProject ctx (depth - 1) (CProj evTm fn) supV goal
                  case found of
                    Just tm -> pure (Just tm)
                    Nothing -> anyPath rest
        Nothing -> pure Nothing
    _ -> pure Nothing

-- free lowercase identifiers (implicit universalization, §11.3.3
-- approximation: ASCII lowercase heads not resolving to globals).
freeLower :: Expr -> [Text]
freeLower = go
  where
    go = \case
      EVar (Name n _)
        | isLowerHead n -> [n]
        | otherwise -> []
      -- the label argument of a row constraint is not a type variable
      -- (§11.3.1: 'LacksRec r age')
      EApp f@(EVar hd) [rowA, ArgExplicit (EVar _)]
        | nameText hd == "LacksRec" -> go f ++ goArg rowA
      EApp f args -> go f ++ concatMap goArg args
      EArrow b e -> maybe [] go (bType b) ++ withoutBinders [b] (go e)
      EForall bs e _ -> concatMap (maybe [] go . bType) bs ++ withoutBinders bs (go e)
      ETraitArrow a b -> go a ++ go b
      EOptionSugar e _ -> go e
      ETuple es _ -> concatMap go es
      -- a dotted head (module path / projection, e.g. `main.Big`) is
      -- never an implicitly-universalized type variable
      EDot {} -> []
      _ -> []
    withoutBinders bs fvs =
      let bound = [nameText n | b <- bs, Just n <- [bName b]]
       in filter (`notElem` bound) fvs
    goArg = \case
      ArgExplicit e -> go e
      ArgImplicit e -> go e
      _ -> []
    isLowerHead n = case T.uncons n of
      Just (c, _) -> c >= 'a' && c <= 'z'
      Nothing -> False
