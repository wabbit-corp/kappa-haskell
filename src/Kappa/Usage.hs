-- | Quantity-and-borrow usage analysis (Spec §12.2–§12.4).
--
-- A post-elaboration pass over the resolved surface module. Each named
-- definition body is walked once, computing for every tracked binding a
-- usage interval [lo, hi] (sequential composition adds, branch joins
-- take min\/max, §12.2.2) plus borrow\/escape facts:
--
--   * @1@ / @>=1@ bindings unused on some completion path
--     (§12.2.5)                                   → E_QTT_LINEAR_DROP
--   * a consuming open-record receiver forgetting its
--     abstract residual tail (§13.2.7)            → E_ROW_TAIL_QUANTITY_UNSATISFIED
--   * @1@ / @<=1@ bindings used more than once    → E_QTT_LINEAR_OVERUSE
--   * @0@ bindings referenced at runtime          → E_QTT_ERASED_RUNTIME_USE
--   * borrowed bindings moved into a consuming
--     (quantity @1@\/@>=1@) parameter             → E_QTT_BORROW_CONSUME
--   * closures\/thunks capturing borrowed bindings
--     escaping through the definition's result    → E_QTT_BORROW_ESCAPE
--   * consuming a place while a live borrow of an
--     overlapping path exists (§12.4)             → E_QTT_BORROW_OVERLAP
--   * call-site @~place@ markers against the
--     callee's @inout@ parameters (§18.9.3)       → E_QTT_INOUT_MARKER_*
--   * @inout@ parameters whose declared result
--     does not thread the place back as a field   → E_QTT_INOUT_THREADED_FIELD_MISSING
--   * abrupt control flow escaping a deferred
--     action (§18.7)                              → E_DEFER_ABRUPT_CONTROL
--
-- Demand scaling (§12.2.1–§12.2.2): an argument occurrence is counted at
-- the callee parameter's demand interval, so a relevant binding passed
-- to an affine or unrestricted parameter fails its positive lower bound
-- and a linear binding passed to an unrestricted parameter fails its
-- upper bound. Closure-shaped values (lambdas, thunks, @lazy@,
-- operator\/receiver sections) carry their captured usage as a /latent/
-- multiset that is multiplied by the consumer's demand (§16.2.1):
-- exactly-once for an immediate call or a quantity-1 slot, zero-or-more
-- for an unrestricted slot, zero for an unused binding.
--
-- Record paths (§12.4): projecting a quantity-1 field out of a tracked
-- record consumes that path; the path can be restored by a record patch,
-- while a patch consumes the residue (and any moved-but-unpatched linear
-- path counts as reused). A @let &@ borrow of a path locks every
-- overlapping path for the binder's lexical scope.
--
-- The analysis is deliberately conservative: only bindings with explicit
-- quantity prefixes (or parameters claiming erased signature binders, or
-- projections of quantity-1 fields) are counted, parameter demand comes
-- from same-module signatures, and a definition containing constructs
-- outside the modelled subset is skipped entirely rather than misjudged.
--
-- Reading guide. The core data types are 'UseCount' (one binding's usage
-- interval @[lo, hi]@ plus borrow\/move metadata), 'Usage' (= @Map@ from a
-- binding key to its 'UseCount'), 'VInfo' (a tracked binding), 'PInfo' (a
-- parameter's demand: quantity plus borrow\/escape flags), and 'WalkResult'
-- (the result of walking one expression). The walk runs in the monad
-- 'Analysis' (= @State AnalysisState@). Background on quantities:
-- docs/CONCEPTS.md.
module Kappa.Usage
  ( PInfo
  , CtorParamInfo (..)
  , FieldShape (..)
  , RecordShape (..)
  , ProjUse (..)
  , RefOp (..)
  , coreFnParams
  , moduleUsageCtors
  , moduleUsageProjections
  , moduleUsageRecordAliases
  , moduleUsageRecordDeps
  , moduleUsageRecordShapes
  , moduleUsageInoutResults
  , moduleUsageInoutResultsWith
  , moduleUsageResultTypes
  , moduleUsageResultTypesWith
  , moduleUsageValueResultTypes
  , moduleUsageSignatures
  , usageDiagnostics
  , tailResumptiveClause
  ) where

import Control.Applicative ((<|>))
import Control.Monad (foldM, forM, forM_, unless, when)
import Control.Monad.State.Strict (State, execState, gets, modify')
import Data.List (find, isPrefixOf, tails)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes, fromMaybe, isJust, isNothing, listToMaybe, mapMaybe, maybeToList)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import Kappa.Core (Term)
import qualified Kappa.Core as Core
import Kappa.Diagnostic
import Kappa.Source (Span)
import Kappa.Syntax
import Kappa.SyntaxOps (renderExprSrc)

-- ── Tables ───────────────────────────────────────────────────────────

-- | Demand a callee places on one explicit argument position.
data PInfo = PInfo
  { pName :: !(Maybe Text)
  , pQuantity :: !(Maybe Quantity)
  , pBorrow :: !Bool
  , pInout :: !Bool
  , pKnown :: !Bool -- ^ from a same-module signature (vs. assumed)
  , pEscapingParam :: !Bool -- ^ unrestricted argument position may retain the value beyond the call
  , pReceiver :: !Bool -- ^ §7.4 receiver-marked binder
  , pCaptureBound :: !CaptureBound
  , pEscapeKind :: !EscapeKind
  }

data CaptureBound = CapAny | CapClosed
  deriving (Eq)

data EscapeKind = EscapeOrdinaryParam | EscapeFork | EscapeForkDaemon | EscapeForkIn
  deriving (Eq)

defaultP :: PInfo
defaultP = PInfo Nothing Nothing False False False True False CapAny EscapeOrdinaryParam

data CtorParamInfo = CtorParamInfo
  { cpiName :: !(Maybe Text)
  , cpiQuantity :: !(Maybe Quantity)
  , cpiType :: !(Maybe Expr)
  , cpiDataParams :: ![Text]
  }

data FieldShape = FieldShape
  { fsName :: !Text
  , fsQuantity :: !(Maybe Quantity)
  , fsType :: !(Maybe Expr)
  }

data RecordShape = RecordShape
  { rsParams :: ![Text]
  , rsFields :: ![FieldShape]
  }

type FieldPath = [Text]

-- | Demand interval of a parameter (§12.2.1); 'Nothing' upper = ω.
pDemand :: PInfo -> (Int, Maybe Int)
pDemand p = case pQuantity p of
  Just QOne -> (1, Just 1)
  Just QAtMostOne -> (0, Just 1)
  Just QAtLeastOne -> (1, Nothing)
  Just QZero -> (0, Just 0)
  Just QOmega
    | pKnown p -> (0, Nothing)
    | otherwise -> (1, Just 1)
  Just (QTerm _) -> (1, Just 1) -- symbolic: assume exactly-once
  Nothing
    | pKnown p -> (0, Nothing) -- known unrestricted parameter
    | otherwise -> (1, Just 1) -- unknown callee: assume exactly-once

-- | One tracked binding in scope.
data VInfo = VInfo
  { vKey :: !Text -- ^ unique usage-map key (shadowing-safe)
  , vQ :: !(Maybe Quantity) -- ^ counted quantity (@1@, @<=1@, @>=1@, @0@)
  , vBorrowed :: !Bool
  , vAnonBorrow :: !Bool -- ^ anonymous @&@ borrow: capture may not escape
  , vUsing :: !Bool -- ^ @using@-scoped resource: may not escape itself (§19.5)
  , vTaint :: !(Maybe Span) -- ^ closure capturing a borrow, formed here
  , vLatent :: !Usage -- ^ per-call captured usage (closure-valued bindings)
  , vFields :: ![(Text, Maybe Quantity)] -- ^ top-level record fields, when known
  , vPathFields :: ![(FieldPath, Maybe Quantity)]
  -- ^ quantity-bearing visible field paths, including nested record paths.
  , vNonDupValue :: !Bool
  -- ^ The value may hide a non-duplicable component not represented as a
  -- visible field path (for example a constructor payload).
  , vNonDupFields :: ![FieldPath]
  -- ^ Visible field paths that are non-duplicable but not necessarily
  -- quantity-1 droppable obligations (notably <=1 affine fields).
  , vMutable :: !Bool
  -- ^ Surface @var@ binding: ordinary value occurrences are current-value
  -- reads, not stable-place moves.
  , vStoredTypeText :: !(Maybe Text)
  -- ^ Source-rendered stored type when Usage can derive it from an explicit
  -- annotation/ascription. Used only for structured diagnostics; Usage does not
  -- invent type text for inferred mutable cells.
  , vStoredTypeExpr :: !(Maybe Expr)
  -- ^ Source type expression for the mutable cell's stored value, when known.
  -- Monadic assignment writes an action result, not the action expression, so
  -- usage needs the cell/result type to derive conservative storage facts.
  , vMutableDiagFields :: ![(Text, Text)]
  -- ^ Checker-captured §18.6.1 mutable-binding payload fields, including the
  -- selected MonadRef evidence, for usage-origin storage diagnostics.
  , vDeps :: ![(Text, [Text])] -- ^ §13.2.1 field dependencies (field ↦ siblings its type mentions)
  , vPathDeps :: ![(FieldPath, [FieldPath])]
  -- ^ §13.2.1 dependencies at their full visible field path.  A nested
  -- record field such as @outer.sized.buffer : Array this.len Byte@ locks
  -- @outer.sized.len@, not just top-level siblings.
  , vOpenTail :: !(Maybe (Text, Span))
  -- ^ §13.2.7: a linear (1\/>=1) receiver of an open record type
  -- @(... | r)@ owns the abstract residual tail @r@. Without a
  -- @RecTailSatisfies r 0@ premise (not expressible in v1), forgetting
  -- the tail is unsound, so the tail must be transferred whole (root
  -- move) or restored\/extended through a patch (residue consume). The
  -- payload carries the residual row variable spelling (for the §3.2.4
  -- @RecTailSatisfies r q@ obligation) and the binding site span.
  , vSpan :: !Span -- ^ binding site (drop reports)
  }

plainV :: Text -> Span -> VInfo
plainV k sp = VInfo k Nothing False False False Nothing Map.empty [] [] False [] False Nothing Nothing [] [] [] Nothing sp

-- | Expand a borrow lock over a field path with the §12.4 dependency
-- rule: borrowing a dependent field also locks the fields its type
-- mentions ("dependent fields are not disjoint merely because their
-- labels differ").
lockWithDeps :: VInfo -> [Text] -> [[Text]]
lockWithDeps vi path =
  dedupPaths $
    path
      : topLevelDeps
        ++ [ dep
           | (src, deps) <- vPathDeps vi
           , src `isPrefixOf` path
           , dep <- deps
           ]
  where
    topLevelDeps = case path of
      (f : _) -> [[d] | d <- fromMaybe [] (lookup f (vDeps vi))]
      [] -> []

-- | The taint a bare occurrence of the binding carries: a closure that
-- captured a borrow, or a @using@-scoped resource escaping itself.
vEscape :: VInfo -> Span -> Maybe Span
vEscape vi sp
  | Just t <- vTaint vi = Just t
  | vUsing vi = Just sp
  | otherwise = Nothing

linTopFields :: VInfo -> [Text]
linTopFields vi = foldr add [] (linPaths vi)
  where
    add (f : _) acc
      | f `elem` acc = acc
      | otherwise = f : acc
    add [] acc = acc

linPaths :: VInfo -> [FieldPath]
linPaths vi =
  dedupPaths $
    [ [f]
    | (f, q) <- vFields vi
    , positiveLowerQuantity q
    ]
      ++ [p | (p, q) <- vPathFields vi, positiveLowerQuantity q]

sliceVInfo :: VInfo -> FieldPath -> VInfo
sliceVInfo vi path =
  vi
    { vQ = pathPositiveQuantity vi path <|> if anyLinearBelow then Just QOne else Nothing
    , vFields = mergeFieldQuantities rebasedTop (topFieldsFromPaths rebasedPaths)
    , vPathFields = rebasedPaths
    , vNonDupValue = vNonDupValue vi && null path
    , vNonDupFields = rebasePaths path (vNonDupFields vi)
    , vDeps = [(f, ds) | ([f], deps) <- rebasedPathDeps, let ds = [d | [d] <- deps], not (null ds)]
    , vPathDeps = rebasedPathDeps
    , vOpenTail = Nothing
    }
  where
    rebasedPaths = rebasePathFields path (vPathFields vi)
    rebasedTop = if null path then vFields vi else []
    rebasedPathDeps =
      [ (src', deps')
      | (src, deps) <- vPathDeps vi
      , path `isPrefixOf` src
      , let src' = drop (length path) src
      , not (null src')
      , let deps' =
              [ drop (length path) dep
              | dep <- deps
              , path `isPrefixOf` dep
              , not (null (drop (length path) dep))
              ]
      , not (null deps')
      ]
    anyLinearBelow =
      any
        ( \p ->
            path `isPrefixOf` p
              && length p > length path
        )
        (linPaths vi)

fieldPatternQuantity :: VInfo -> FieldPath -> Maybe Quantity
fieldPatternQuantity vi path =
  pathPositiveQuantity vi path
    <|> if any (\p -> path `isPrefixOf` p && length p > length path) (linPaths vi)
      then Just QOne
      else Nothing

nonDupQuantity :: Maybe Quantity -> Bool
nonDupQuantity q = q `elem` [Just QOne, Just QAtMostOne]

positiveLowerQuantity :: Maybe Quantity -> Bool
positiveLowerQuantity q = q `elem` [Just QOne, Just QAtLeastOne]

-- | Field names that cannot be duplicated. This intentionally includes affine
-- fields; 'linPaths' tracks the separate positive-lower "must consume" axis.
nonDupFields :: VInfo -> [FieldPath]
nonDupFields vi =
  dedupPaths $
    [ [f]
    | (f, q) <- vFields vi
    , nonDupQuantity q
    ]
    ++ [p | (p, q) <- vPathFields vi, nonDupQuantity q]
    ++ vNonDupFields vi

-- | One chronological place event on a tracked root binding: a
-- definite consume of a path, or a borrow\/re-projection read of a
-- path (§12.4 path-sensitive consumption).
data PEv = PMove ![Text] !Span | PBorrow ![Text] !Span
  deriving (Eq)

-- | Usage interval of one binding plus the metadata its diagnostics need.
data UseCount = UseCount
  { ucLo :: !Int
  -- ^ move lower bound: fewest definite consumes on any completion path
  , ucHi :: !Int
  -- ^ move upper bound: most consumes on any completion path
  , ucMoves :: ![Span]
  -- ^ the consume occurrences (for "used more than once" reports)
  , ucTouches :: !Int
  -- ^ touch lower bound; borrow-uses count as touches, so a binding is
  -- dropped iff some path never touches it
  , ucEvents :: ![PEv]
  -- ^ chronological place events on the root ('PMove'\/'PBorrow'), for
  -- path-sensitive §12.4 reasoning
  , ucViolations :: ![([Text], Span)]
  -- ^ detected §12.4 borrow-after-consume violations (borrowed path, borrow site)
  }
  deriving (Eq)

-- | Whether the binding is touched (used or borrowed) on some path.
ucTouched :: UseCount -> Bool
ucTouched uc = ucTouches uc > 0

zeroUC :: UseCount
zeroUC = UseCount 0 0 [] 0 [] []

oneUC :: Span -> UseCount
oneUC sp = UseCount 1 1 [sp] 1 [] []

touchUC :: UseCount
touchUC = UseCount 0 0 [] 1 [] []

refEscapeUC :: Span -> UseCount
-- Escaping `ref x` marks the cell lifetime as no longer locally owned, but
-- copying the Ref value is not a second move of the stored payload.
refEscapeUC sp = (oneUC sp) {ucHi = 0, ucMoves = []}

-- | A root-key occurrence carrying a §12.4 place event.
evUC :: PEv -> UseCount -> UseCount
evUC ev uc = uc {ucEvents = ucEvents uc ++ [ev]}

-- | Sequential composition; a borrow of a path after an overlapping
-- definite consume (with no restoring update in between — a patch
-- rebinds through a fresh root) is a §12.4 violation.
seqUC :: UseCount -> UseCount -> UseCount
seqUC x y =
  UseCount
    { ucLo = ucLo x + ucLo y
    , ucHi = ucHi x + ucHi y
    , ucMoves = ucMoves x ++ ucMoves y
    , ucTouches = ucTouches x + ucTouches y
    , ucEvents = ucEvents x ++ ucEvents y
    , ucViolations = ucViolations x ++ ucViolations y ++ new
    }
  where
    new =
      [ (bp, sp)
      | PBorrow bp sp <- ucEvents y
      , any (\case PMove mp _ -> pathsOverlap mp bp; _ -> False) (ucEvents x)
      ]

altUC :: UseCount -> UseCount -> UseCount
altUC x y =
  UseCount
    { ucLo = min (ucLo x) (ucLo y)
    , ucHi = max (ucHi x) (ucHi y)
    , ucMoves = if ucHi y > ucHi x then ucMoves y else ucMoves x
    , ucTouches = min (ucTouches x) (ucTouches y)
    , ucEvents = ucEvents x ++ ucEvents y
    , ucViolations = ucViolations x ++ ucViolations y
    }

-- | Upper bound standing in for ω in scaled intervals.
omegaBound :: Int
omegaBound = 1000000

-- | Multiply a usage interval by a demand interval (§12.2.2, §16.2.1).
scaleUC :: (Int, Maybe Int) -> UseCount -> UseCount
scaleUC (lo, hi) uc =
  UseCount
    { ucLo = min omegaBound (lo * ucLo uc)
    , ucHi = hi'
    , ucMoves = if hi' > ucHi uc then ucMoves uc ++ ucMoves uc else ucMoves uc
    , ucTouches = if lo == 0 then 0 else ucTouches uc
    , ucEvents = if lo == 0 then [] else ucEvents uc
    , ucViolations = if hi' == 0 then [] else ucViolations uc
    }
  where
    hi' = case hi of
      Nothing -> if ucHi uc > 0 then omegaBound else 0
      Just h -> min omegaBound (h * ucHi uc)

type Usage = Map Text UseCount

scaleU :: (Int, Maybe Int) -> Usage -> Usage
scaleU d = Map.map (scaleUC d)

seqU :: Usage -> Usage -> Usage
seqU = Map.unionWith seqUC

altU :: Usage -> Usage -> Usage
altU u1 u2 =
  Map.mergeWithKey (\_ a b -> Just (altUC a b)) (Map.map (altUC zeroUC)) (Map.map (altUC zeroUC)) u1 u2

altUs :: [Usage] -> Usage
altUs [] = Map.empty
altUs us = foldr1 altU us

-- mark every binding as possibly-unused (loops may run zero times)
loopU :: Usage -> Usage
loopU = Map.map (\uc -> uc {ucLo = 0, ucTouches = 0})

-- ── Analysis monad ───────────────────────────────────────────────────

-- | Mutable state of the analysis walk: accumulated diagnostics, a bail
-- flag (set when an unmodelled construct is hit, so the definition is
-- skipped rather than misjudged), and a counter for fresh binding keys.
data AnalysisState = AnalysisState
  { sDiags :: ![Diagnostic]
  , sBail :: !Bool
  , sFresh :: !Int
  }

-- | The analysis monad: just 'State' over 'AnalysisState'. (No reader env —
-- the lexical 'Env' is threaded explicitly as a function argument instead.)
type Analysis = State AnalysisState

emit :: DiagnosticCode -> DiagnosticFamily -> Span -> Text -> Analysis ()
emit code fam sp msg =
  modify' $ \s ->
    s {sDiags = diag SevError StageElaborate code (Just fam) sp msg : sDiags s}

emitPayload :: DiagnosticCode -> DiagnosticFamily -> Payload -> Span -> Text -> Analysis ()
emitPayload code fam payload sp msg =
  modify' $ \s ->
    s {sDiags = withPayload payload (diag SevError StageElaborate code (Just fam) sp msg) : sDiags s}

-- | Like 'emit' but attaches §3.1.1A related origins — used by the
-- borrow/path/ownership diagnostics, which MUST include the borrow or
-- consume introduction site and the failing later use or escape site.
emitRel :: DiagnosticCode -> DiagnosticFamily -> Span -> [RelatedOrigin] -> Text -> Analysis ()
emitRel code fam sp rels msg =
  modify' $ \s ->
    s
      { sDiags =
          withRelateds rels (diag SevError StageElaborate code (Just fam) sp msg)
            : sDiags s
      }

bailOut :: Analysis ()
bailOut = modify' $ \s -> s {sBail = True}

-- | Shadowing-safe usage key for a new binding of @nm@.
freshKey :: Text -> Analysis Text
freshKey nm = do
  n <- gets sFresh
  modify' $ \s -> s {sFresh = n + 1}
  pure (nm <> "#" <> T.pack (show n))

-- | The lexical environment threaded through the walk: what's in scope and
-- the facts the analysis needs about it — tracked variables, callee
-- parameter demands, live borrows, constructor/field/projection shapes, and
-- assorted §-specific side tables. Extended with 'bindVars'\/'addBorrows'.
data Env = Env
  { eVars :: !(Map Text VInfo)
  , eFns :: !(Map Text [PInfo])
  , eInoutResults :: !(Map Text [FieldShape])
  , eResultTypes :: !(Map Text Expr)
  , eValueResultTypes :: !(Map Text Expr)
  , eResultStorage :: !(Map Text VInfo)
  , eRecognizedRefOps :: !(Map Span RefOp)
  , eRecognizedMultishotOps :: !(Map Span Text)
  , eHandlerOpQuantities :: !(Map Span Quantity)
  , eBorrows :: ![(Text, [Text], Span)]
  -- ^ live lexical borrows: root key, path, and the §3.1.1A
  -- borrow-introduction site (the @let &@ binding span) so the
  -- borrow/path/ownership diagnostics can relate the introduction site.
  , eAliases :: !(Map Text [(Text, Maybe Quantity)])
  , eRecordShapes :: !(Map Text RecordShape)
  , eCtors :: !(Map Text [(Text, [CtorParamInfo])])
  -- ^ ctor name → all sibling ctors of its data type with field quantities
  , eProjs :: !(Map Text ProjUse)
  -- ^ §9.1.1 projection definitions of the module
  , eDescs :: !(Map Text ProjUse)
  -- ^ local bindings holding a (partially applied) projection descriptor
  , eBorrowAliases :: !(Map Text (Text, [Text]))
  -- ^ borrowed place-alias bindings: binder key ↦ root key + path (§12.4)
  , eFieldDeps :: !(Map Text [(Text, [Text])])
  -- ^ record type alias ↦ §13.2.1 field dependencies
  , eEffOps :: !(Map Text [(Text, Quantity)])
  -- ^ scoped effect label ↦ operations with declared resumption
  -- quantities (§9.3.1.1, §18.1.16)
  , eExpansions :: !(Map Span Expr)
  -- ^ §21.2 splice expansions recorded by the elaborator (keyed by the
  -- splice span): the object-level uses charged at each splice site
  , ePendingSig :: ![Binder]
  -- ^ §12.2.5: signature Pi binders not yet consumed by equation-head
  -- params, to be aligned with a leading lambda chain in the body so
  -- their quantity obligations bind the lambda binders. Cleared once a
  -- lambda has claimed them (or on any non-lambda step).
  , eMutableBindingFields :: !(Map Span [(Text, Text)])
  -- ^ Checker-captured mutable-binding payloads keyed by source binding span.
  , eMonadicResultHeads :: !(Set.Set Text)
  -- ^ Source type heads that import resolution / instance registration proved
  -- denote monadic action carriers. Usage may unwrap action result types only
  -- for these heads plus the built-in carriers.
  , eDuplicableStorageHeads :: !(Set.Set Text)
  -- ^ Source heads that import resolution proved denote primitive duplicable
  -- storage types. Same-spelling local types are removed before the Env is built.
  , eLatentCurrentReadEscape :: !Bool
  -- ^ While walking the body of a user-written closure/thunk/code quote,
  -- a generated current-value read captures the hidden cell. Keep ordinary
  -- straight-line reads non-consuming, but record the hidden-cell escape in
  -- the latent usage of the closure-shaped value.
  }

-- | §9.1.1 projection shape for the §12.4 footprint analysis.
data ProjUse = ProjUse
  { puIsPlace :: ![Bool] -- ^ per explicit binder, declaration order
  , puPlaceNames :: ![Text] -- ^ place binder names, declaration order
  , puYields :: ![(Text, [Text])] -- ^ yield leaves: place name, path suffix
  }

data MutableCloseContext = MutableCloseContext
  { mccSelectedFacet :: !Text
  , mccSourceOperation :: !Text
  }

bindVars :: [(Text, VInfo)] -> Env -> Env
bindVars bs env =
  env
    { eVars = foldr (uncurry Map.insert) (eVars env) bs
    , eDescs = foldr (Map.delete . fst) (eDescs env) bs
    }

addBorrows :: [(Text, [Text], Span)] -> Env -> Env
addBorrows bs env = env {eBorrows = bs ++ eBorrows env}

-- | Walk result: immediate usage, escape taint, latent per-call usage.
data WalkResult = WalkResult
  { wrUsage :: !Usage
  , wrTaint :: !(Maybe Span)
  , wrLatent :: !Usage
  }

rPlain :: Usage -> WalkResult
rPlain u = WalkResult u Nothing Map.empty

rNone :: WalkResult
rNone = rPlain Map.empty

-- | Fold latent usage in at exactly-once consumption.
flatR :: WalkResult -> (Usage, Maybe Span)
flatR r = (wrUsage r `seqU` wrLatent r, wrTaint r)

-- ── Entry point ──────────────────────────────────────────────────────

-- | Analyze a resolved module; returns the §12.2–§12.4 usage
-- diagnostics for its named definitions. The first argument carries the
-- elaborator's §21.2 splice expansions (splice span ↦ expanded syntax).
-- The second argument carries checked callable types imported into this
-- module; without it a qualified imported call such as @m.borrow x@ would
-- be treated as an unknown consuming call even when its interface says the
-- parameter is unrestricted or affine.
usageDiagnostics ::
  Map Span Expr ->
  Map Span [(Text, Text)] ->
  Map Text [PInfo] ->
  Map Text [FieldShape] ->
  Map Text Expr ->
  Map Text Expr ->
  Map Text [(Text, Maybe Quantity)] ->
  Map Text RecordShape ->
  Map Text [(Text, [Text])] ->
  Map Text [(Text, [CtorParamInfo])] ->
  Map Span RefOp ->
  Map Span Text ->
  Map Span Quantity ->
  Set.Set Text ->
  Set.Set Text ->
  Map Text ProjUse ->
  Set.Set Text ->
  Module ->
  [Diagnostic]
usageDiagnostics expansions mutableBindingFields importedFnParams importedInoutResults importedResultTypes importedValueResultTypes importedAliases importedRecordShapes importedRecordDeps importedCtors recognizedRefOps recognizedMultishotOps handlerOpQuantities importedBorrowViewHeads visibleMonadicResultHeads importedProjs importedDuplicableStorageHeads m = concatMap analyzeDecl lets
  where
    decls = modDecls m
    sigs = Map.fromList [(nameText n, ty) | DSig _ n ty _ <- decls]
    lets = [ld | DLet _ ld _ <- decls, Just _ <- [ldName ld]]
    -- §18.1: top-level effect declarations are visible module-wide, so seed
    -- the resumption-quantity map with them (a scoped effect adds to it via
    -- addEffDecls in its block); without this a `return@/k` in a handler of
    -- a top-level ω-operation would be miscounted as one-shot.
    topEffOps =
      Map.fromList
        [ ( nameText (effName ed)
          , [(nameText (eoName o), fromMaybe QOne (eoQuantity o)) | o <- effOps ed]
          )
        | DEffect _ ed _ <- decls
        , not (effIsLabelDecl ed)
        ]
    projs = moduleUsageProjections m `Map.union` importedProjs
    aliases = moduleUsageRecordAliases m `Map.union` importedAliases
    recordShapes = moduleUsageRecordShapes m `Map.union` importedRecordShapes
    aliasDeps = moduleUsageRecordDeps m `Map.union` importedRecordDeps
    localFns = moduleUsageSignatures m
    inoutResults = moduleUsageInoutResultsWith monadicResultHeads m `Map.union` importedInoutResults
    resultTypes = moduleUsageResultTypesWith monadicResultHeads m `Map.union` importedResultTypes
    valueResultTypes = moduleUsageValueResultTypes m `Map.union` importedValueResultTypes
    localCtors = moduleUsageCtors m
    baseCtors = localCtors `Map.union` importedCtors
    ctors = baseCtors
    borrowViewHeads = importedBorrowViewHeads Set.\\ localTypeHeads
    resultStorage =
      moduleUsageResultStorage
        fns
        inoutResults
        resultTypes
        valueResultTypes
        recognizedRefOps
        recognizedMultishotOps
        aliases
        recordShapes
        aliasDeps
        ctors
        projs
        topEffOps
        mutableBindingFields
        borrowViewHeads
        monadicResultHeads
        duplicableStorageHeads
        m
    duplicableStorageHeads = importedDuplicableStorageHeads Set.\\ localTypeHeads
    fns = localFns `Map.union` builtinFns `Map.union` importedFnParams
    monadicResultHeads = visibleMonadicResultHeads
    analyzeDecl ld =
      let nm = maybe "" nameText (ldName ld)
          sigTy = Map.lookup nm sigs
          final = execState (analyzeLet expansions mutableBindingFields fns inoutResults resultTypes valueResultTypes resultStorage recognizedRefOps recognizedMultishotOps handlerOpQuantities aliases recordShapes aliasDeps ctors projs topEffOps borrowViewHeads monadicResultHeads duplicableStorageHeads sigTy ld) (AnalysisState [] False 0)
       in if sBail final then [] else reverse (sDiags final)
    localTypeHeads =
      Set.fromList $
        [nameText (ddName dd) | DData _ dd _ <- decls]
          ++ [nameText n | DTypeAlias _ n _ _ _ _ <- decls]

data BuiltinUsage = BuiltinUsage
  { buParams :: [PInfo]
  , buEscape :: EscapeKind
  , buLiftLike :: Bool
  }

data RefOp = RefRead | RefWrite
  deriving (Eq, Show)

builtinUsage :: Map Text BuiltinUsage
builtinUsage =
  Map.fromList
    [ ("unsafeConsume", BuiltinUsage [defaultP {pQuantity = Just QOne, pKnown = True}] EscapeOrdinaryParam False)
    , ("pure", BuiltinUsage [defaultP {pQuantity = Just QOne, pKnown = True, pEscapingParam = False}] EscapeOrdinaryParam True)
    , ("ioPure", BuiltinUsage [defaultP {pQuantity = Just QOne, pKnown = True, pEscapingParam = False}] EscapeOrdinaryParam True)
    , ("return", BuiltinUsage [] EscapeOrdinaryParam True)
    , ("summon", BuiltinUsage [defaultP {pQuantity = Just QZero, pKnown = True}] EscapeOrdinaryParam False)
    , ("fork", BuiltinUsage [defaultP {pKnown = True, pCaptureBound = CapClosed, pEscapeKind = EscapeFork}] EscapeFork False)
    , ("forkDaemon", BuiltinUsage [defaultP {pKnown = True, pCaptureBound = CapClosed, pEscapeKind = EscapeForkDaemon}] EscapeForkDaemon False)
    , ( "forkIn"
      , BuiltinUsage
          [ defaultP {pKnown = True}
          , defaultP {pKnown = True, pCaptureBound = CapClosed, pEscapeKind = EscapeForkIn}
          ]
          EscapeForkIn
          False
      )
    ]

-- Callee demand for prelude helpers the fixtures rely on.
builtinFns :: Map Text [PInfo]
builtinFns = Map.mapMaybe (\bu -> if null (buParams bu) then Nothing else Just (buParams bu)) builtinUsage

moduleUsageSignatures :: Module -> Map Text [PInfo]
moduleUsageSignatures m =
  Map.fromList
    [ (nameText n, fnParams (Map.lookup (nameText n) sigs) ld)
    | ld <- lets
    , Just n <- [ldName ld]
    ]
  where
    decls = modDecls m
    sigs = Map.fromList [(nameText n, ty) | DSig _ n ty _ <- decls]
    lets = [ld | DLet _ ld _ <- decls, Just _ <- [ldName ld]]

moduleUsageInoutResults :: Module -> Map Text [FieldShape]
moduleUsageInoutResults = moduleUsageInoutResultsWith Set.empty

moduleUsageInoutResultsWith :: Set.Set Text -> Module -> Map Text [FieldShape]
moduleUsageInoutResultsWith monadicResultHeads m =
  Map.fromList
    [ (nameText n, inoutShapes)
    | ld <- lets
    , Just n <- [ldName ld]
    , let inoutShapes = resultShapes (ldResultType ld `orElseE` Map.lookup (nameText n) sigs)
    , not (null inoutShapes)
    ]
  where
    decls = modDecls m
    sigs = Map.fromList [(nameText n, ty) | DSig _ n ty _ <- decls]
    lets = [ld | DLet _ ld _ <- decls, Just _ <- [ldName ld]]
    resultShapes mty =
      maybe [] (recordShapeFieldsWith shapes . unwrapActionType monadicResultHeads . dropBinders) mty
    shapes = moduleUsageRecordShapes m
    orElseE (Just x) _ = Just x
    orElseE Nothing y = y

moduleUsageResultTypes :: Module -> Map Text Expr
moduleUsageResultTypes = moduleUsageResultTypesWith Set.empty

moduleUsageResultTypesWith :: Set.Set Text -> Module -> Map Text Expr
moduleUsageResultTypesWith monadicResultHeads m =
  Map.fromList
    [ (nameText n, unwrapActionType monadicResultHeads (dropBinders ty))
    | ld <- lets
    , Just n <- [ldName ld]
    , Just ty <- [ldResultType ld `orElseE` Map.lookup (nameText n) sigs]
    ]
  where
    decls = modDecls m
    sigs = Map.fromList [(nameText n, ty) | DSig _ n ty _ <- decls]
    lets = [ld | DLet _ ld _ <- decls, Just _ <- [ldName ld]]
    orElseE (Just x) _ = Just x
    orElseE Nothing y = y

moduleUsageValueResultTypes :: Module -> Map Text Expr
moduleUsageValueResultTypes m =
  Map.fromList
    [ (nameText n, dropBinders ty)
    | ld <- lets
    , Just n <- [ldName ld]
    , Just ty <- [ldResultType ld `orElseE` Map.lookup (nameText n) sigs]
    ]
  where
    decls = modDecls m
    sigs = Map.fromList [(nameText n, ty) | DSig _ n ty _ <- decls]
    lets = [ld | DLet _ ld _ <- decls, Just _ <- [ldName ld]]
    orElseE (Just x) _ = Just x
    orElseE Nothing y = y

moduleUsageProjections :: Module -> Map Text ProjUse
moduleUsageProjections m =
  Map.fromList
    [ (nameText n, ProjUse isPlace placeNames yields)
    | DProjection _ n bs _ body _ <- modDecls m
    , let groups = projBinderGroups bs
          isPlace = map fst groups
          placeNames = [maybe "_" nameText (bName b) | (True, b) <- groups]
          yields = case body of
            ProjSelector e ->
              [ (root, path)
              | Right (root, path) <- projYieldPlaces e
              , root `elem` placeNames
              ]
            -- an accessor bundle's footprint is its whole root.
            ProjAccessors _ -> [(p, []) | p <- placeNames]
    ]

moduleUsageResultStorage ::
  Map Text [PInfo] ->
  Map Text [FieldShape] ->
  Map Text Expr ->
  Map Text Expr ->
  Map Span RefOp ->
  Map Span Text ->
  Map Text [(Text, Maybe Quantity)] ->
  Map Text RecordShape ->
  Map Text [(Text, [Text])] ->
  Map Text [(Text, [CtorParamInfo])] ->
  Map Text ProjUse ->
  Map Text [(Text, Quantity)] ->
  Map Span [(Text, Text)] ->
  Set.Set Text ->
  Set.Set Text ->
  Set.Set Text ->
  Module ->
  Map Text VInfo
moduleUsageResultStorage fns inoutResults resultTypes valueResultTypes recognizedRefOps recognizedMultishotOps aliases recordShapes aliasDeps ctors projs effs mutableBindingFields borrowViewHeads monadicResultHeads duplicableStorageHeads m =
  fixedPoint (length lets + 1) Map.empty
  where
    decls = modDecls m
    sigs = Map.fromList [(nameText n, ty) | DSig _ n ty _ <- decls]
    lets = [ld | DLet _ ld _ <- decls, Just _ <- [ldName ld]]

    fixedPoint fuel prev
      | fuel <= 0 = prev
      | storageSummariesStable next prev = next
      | otherwise = fixedPoint (fuel - 1) next
      where
        next = summaryMap prev

    summaryMap resultStorage =
      Map.fromList
        [ (nameText n, summaryFor resultStorage n sigTy ld)
        | ld <- lets
        , Just n <- [ldName ld]
        , let sigTy = Map.lookup (nameText n) sigs
        ]

    summaryFor resultStorage n sigTy ld =
      let binds = mapMaybe paramBindPure (alignParams (ldBinders ld) (maybe [] sigBinders sigTy))
          env =
            Env
              (Map.fromList binds)
              fns
              inoutResults
              resultTypes
              valueResultTypes
              resultStorage
              recognizedRefOps
              recognizedMultishotOps
              Map.empty
              []
              aliases
              recordShapes
              ctors
              projs
              Map.empty
              Map.empty
              aliasDeps
              effs
              Map.empty
              []
              mutableBindingFields
              monadicResultHeads
              duplicableStorageHeads
              False
       in storedValueInfo env ("$result:" <> nameText n) (exprSpan (ldBody ld)) (ldBody ld)

    storageSummariesStable a b =
      Map.map storageSummaryKey a == Map.map storageSummaryKey b

    storageSummaryKey vi =
      ( vQ vi
      , vFields vi
      , vPathFields vi
      , vNonDupValue vi
      , vNonDupFields vi
      , vDeps vi
      , vPathDeps vi
      , vStoredTypeText vi
      , renderExprSrc <$> vStoredTypeExpr vi
      )

    paramBindPure (b, ms) = do
      n <- bName b
      let BinderPrefix mq mb = bPrefix b
          BinderPrefix sq sb = maybe emptyPrefix bPrefix ms
          q = mq `orElse` sq
          mark = mb `orElse` sb
          ty = bType b `orElse` (bType =<< ms)
          borrowViewed = maybe False (isBorrowViewTy borrowViewHeads) ty
          anon = mark == Just (BorrowMark Nothing) || borrowViewed
          pathFields = maybe [] (recordPathFieldsWith recordShapes ctors) ty
          fields = mergeFieldQuantities (maybe [] (resolveFields aliases) ty) (topFieldsFromPaths pathFields)
          deps = maybe [] (resolveDeps aliasDeps) ty
          pathDeps = maybe [] (recordPathDepsWith recordShapes) ty
          openTail
            | isNothing mark
            , q `elem` [Just QOne, Just QAtLeastOne]
            , Just rowVar <- (hasAbstractTail aliases =<< ty) =
                Just (rowVar, bSpan b)
            | otherwise = Nothing
      pure
        ( nameText n
        , (plainV ("$param:" <> nameText n) (bSpan b))
            { vQ = q
            , vBorrowed = isJust mark || borrowViewed
            , vAnonBorrow = anon
            , vFields = fields
            , vPathFields = pathFields
            , vDeps = deps
            , vPathDeps = pathDeps
            , vOpenTail = openTail
            }
        )

    orElse (Just x) _ = Just x
    orElse Nothing y = y

moduleUsageCtors :: Module -> Map Text [(Text, [CtorParamInfo])]
moduleUsageCtors m =
  dataCtors
  where
    dataCtors = Map.fromList (concatMap dataCtorEntries [dd | DData _ dd _ <- modDecls m])
    dataCtorEntries dd =
      let typeName = nameText (ddName dd)
          dataParams = binderParamNames (ddParams dd)
          ctorParams c = [CtorParamInfo (nameText <$> bName b) (bpQuantity (bPrefix b)) (bType b) dataParams | b <- cdBinders c]
          siblings = [(nameText (cdName c), ctorParams c) | c <- ddCtors dd]
          qualifiedSiblings = [(typeName <> "." <> nameText (cdName c), ctorParams c) | c <- ddCtors dd]
       in concat
            [ [ (nameText (cdName c), siblings)
              , (typeName <> "." <> nameText (cdName c), qualifiedSiblings)
              ]
            | c <- ddCtors dd
            ]

moduleUsageRecordAliases :: Module -> Map Text [(Text, Maybe Quantity)]
moduleUsageRecordAliases m =
  Map.fromList
    [ (nameText n, fieldsOf fs)
    | DTypeAlias _ n _ _ (Just rhs) _ <- decls
    , Just fs <- [recordTypeFieldsOf rhs]
    ]
    <> dataRecordFields
  where
    decls = modDecls m
    fieldsOf fs =
      [(nameText (rtfName f), bpQuantity (rtfPrefix f)) | f <- fs]
    -- §12.4.3: a single-constructor data type with named fields (the
    -- prelude Zipper, or a user type) resolves to its real field
    -- quantities, so usage checking reads them from the declaration
    -- instead of a hardcoded table keyed on the type name.
    dataRecordFields =
      Map.fromList
        [ (nameText (ddName dd), fields)
        | DData _ dd _ <- decls
        , [c] <- [ddCtors dd]
        , let fields =
                [ (nameText nm, bpQuantity (bPrefix b))
                | b <- cdBinders c
                , Just nm <- [bName b]
                ]
        , not (null fields)
        ]

moduleUsageRecordDeps :: Module -> Map Text [(Text, [Text])]
moduleUsageRecordDeps m =
  Map.fromList
    [ (nameText n, fieldDepsOf fs)
    | DTypeAlias _ n _ _ (Just rhs) _ <- decls
    , Just fs <- [recordTypeFieldsOf rhs]
    ]
  where
    decls = modDecls m

moduleUsageRecordShapes :: Module -> Map Text RecordShape
moduleUsageRecordShapes m =
  Map.fromList
    [ (nameText n, RecordShape (binderParamNames params) (shapesOfRecordType fs))
    | DTypeAlias _ n params _ (Just rhs) _ <- decls
    , Just fs <- [recordTypeFieldsOf rhs]
    ]
    <> dataRecordShapes
  where
    decls = modDecls m
    shapesOfRecordType fs =
      [FieldShape (nameText (rtfName f)) (bpQuantity (rtfPrefix f)) (Just (rtfType f)) | f <- fs]
    dataRecordShapes =
      Map.fromList
        [ (nameText (ddName dd), shapes)
        | DData _ dd _ <- decls
        , [c] <- [ddCtors dd]
        , let fields =
                [ FieldShape (nameText nm) (bpQuantity (bPrefix b)) (bType b)
                | b <- cdBinders c
                , Just nm <- [bName b]
                ]
              shapes = RecordShape (binderParamNames (ddParams dd)) fields
        , not (null fields)
        ]

binderParamNames :: [Binder] -> [Text]
binderParamNames =
  mapMaybe (fmap nameText . bName)

-- | Surface @(field : T)@ is ambiguous with expression ascription in the
-- parser, but in type position the checker treats a lower-case field as a
-- singleton record type (§13.1). Usage consumes declaration/type shapes after
-- parsing, so it must preserve the same interpretation.
recordTypeFieldsOf :: Expr -> Maybe [RecTypeField]
recordTypeFieldsOf = \case
  ERecordType fs _ _ -> Just fs
  EAscription (EVar n) ty _
    | isLowerName (nameText n) ->
        Just [RecTypeField False False emptyPrefix Nothing n ty]
  ECaptures e _ _ -> recordTypeFieldsOf e
  _ -> Nothing

isLowerName :: Text -> Bool
isLowerName t = case T.uncons t of
  Just (c, _) -> c >= 'a' && c <= 'z'
  Nothing -> False

-- | Resolve a (possibly aliased) record type to its field list.
resolveFields :: Map Text [(Text, Maybe Quantity)] -> Expr -> [(Text, Maybe Quantity)]
resolveFields aliases = go
  where
    go = \case
      ERecordType fs _ _ ->
        [(nameText (rtfName f), bpQuantity (rtfPrefix f)) | f <- fs]
      EAscription (EVar n) _ _
        | isLowerName (nameText n) -> [(nameText n, Nothing)]
      e
        | Just hd <- typePathHead e
        , Just fs <- Map.lookup hd aliases -> fs
      EAscription e _ _ -> go e
      ECaptures e _ _ -> go e
      _ -> []

typePathHead :: Expr -> Maybe Text
typePathHead = \case
  EVar n -> Just (nameText n)
  EDot base (DotName n) -> (<> "." <> nameText n) <$> typePathHead base
  EApp f _ -> typePathHead f
  EAscription e _ _ -> typePathHead e
  ECaptures e _ _ -> typePathHead e
  _ -> Nothing

recordPathFields :: Env -> Expr -> [(FieldPath, Maybe Quantity)]
recordPathFields env = recordPathFieldsWith (eRecordShapes env) (eCtors env)

recordPathFieldsWith :: Map Text RecordShape -> Map Text [(Text, [CtorParamInfo])] -> Expr -> [(FieldPath, Maybe Quantity)]
recordPathFieldsWith shapesByName ctorsByName = go (0 :: Int) Set.empty
  where
    go depth seen e
      | depth > 32 = []
      | otherwise = case e of
          ERecordType fs _ _ ->
            shapePaths depth seen [FieldShape (nameText (rtfName f)) (bpQuantity (rtfPrefix f)) (Just (rtfType f)) | f <- fs]
          EAscription (EVar n) ty _
            | isLowerName (nameText n) ->
                shapePaths depth seen [FieldShape (nameText n) Nothing (Just ty)]
          EAscription e' _ _ -> go depth seen e'
          ECaptures e' _ _ -> go depth seen e'
          e'
            | Just hd <- typePathHead e' ->
                if Set.member hd seen
                  then []
                  else case shapeFieldsForType shapesByName e' of
                    Just shapes -> shapePaths depth (Set.insert hd seen) shapes
                    Nothing -> []
          _ -> []
    shapePaths depth seen shapes =
      mergePathQuantities direct nested
      where
        childPaths =
          [ (s, maybe [] (go (depth + 1) seen) (fsType s))
          | s <- shapes
          ]
        direct =
          [ ([fsName s], Just q)
          | (s, children) <- childPaths
          , Just q <- [fieldStorageQuantity depth s children]
          , nonDupQuantity (Just q) || positiveLowerQuantity (Just q)
          ]
        nested =
          concat
            [ [ (fsName s : p, q) | (p, q) <- children ]
            | (s, children) <- childPaths
            ]
    fieldStorageQuantity depth s childPaths =
      joinFieldQuantities
        [ fsQuantity s
        , if null childPaths
            then fsType s >>= typeStorageQuantityWithDepth shapesByName ctorsByName (depth + 1)
            else Nothing
        ]

typeStorageQuantityWith :: Map Text RecordShape -> Map Text [(Text, [CtorParamInfo])] -> Expr -> Maybe Quantity
typeStorageQuantityWith shapesByName ctorsByName = typeStorageQuantityWithDepth shapesByName ctorsByName 0

typeStorageQuantityWithDepth :: Map Text RecordShape -> Map Text [(Text, [CtorParamInfo])] -> Int -> Expr -> Maybe Quantity
typeStorageQuantityWithDepth shapesByName ctorsByName startDepth = go startDepth Set.empty
  where
    go depth seen ty
      | depth > 32 = Nothing
      | otherwise =
          joinFieldQuantities $
            case ty of
              ERecordType fs _ _ ->
                shapeQuantities depth seen [FieldShape (nameText (rtfName f)) (bpQuantity (rtfPrefix f)) (Just (rtfType f)) | f <- fs]
              EAscription (EVar n) fieldTy _
                | isLowerName (nameText n) ->
                    shapeQuantities depth seen [FieldShape (nameText n) Nothing (Just fieldTy)]
              EAscription e _ _ -> [go depth seen e]
              ECaptures e _ _ -> [go depth seen e]
              e
                | Just hd <- typePathHead e ->
                    if Set.member hd seen
                      then []
                      else
                        let seen' = Set.insert hd seen
                         in maybe [] (shapeQuantities depth seen') (shapeFieldsForType shapesByName e)
                              ++ ctorQuantities depth seen' e hd
              EApp f _ -> [go depth seen f]
              _ -> []
    shapeQuantities depth seen shapes =
      [ fsQuantity s
      | s <- shapes
      , nonDupQuantity (fsQuantity s) || positiveLowerQuantity (fsQuantity s)
      ]
        ++ [ go (depth + 1) seen ty
           | s <- shapes
           , ty <- maybeToList (fsType s)
           ]
    ctorQuantities depth seen ty hd =
      [ ctorParamStorageQuantity depth seen p
      | siblings <- ctorsForType hd
      , (_, params) <- siblings
      , p <- map (substCtorParamInfoForType ty) params
      ]
    ctorsForType hd =
      dedupCtorGroups
        [ siblings
        | (k, siblings) <- Map.toList ctorsByName
        , (hd <> ".") `T.isPrefixOf` k
        ]
    dedupCtorGroups = goGroups Set.empty
      where
        goGroups _ [] = []
        goGroups seenKeys (siblings : rest)
          | key `Set.member` seenKeys = goGroups seenKeys rest
          | otherwise = siblings : goGroups (Set.insert key seenKeys) rest
          where
            key = map fst siblings
    ctorParamStorageQuantity depth seen p =
      joinFieldQuantities
        [ cpiQuantity p
        , cpiType p >>= go (depth + 1) seen
        ]

substCtorParamInfoForType :: Expr -> CtorParamInfo -> CtorParamInfo
substCtorParamInfoForType ty p =
  let subst = Map.fromList (zip (cpiDataParams p) (typeAppArgs ty))
   in p {cpiType = substExpr subst <$> cpiType p}

recordPathDeps :: Env -> Expr -> [(FieldPath, [FieldPath])]
recordPathDeps env = recordPathDepsWith (eRecordShapes env)

recordPathDepsWith :: Map Text RecordShape -> Expr -> [(FieldPath, [FieldPath])]
recordPathDepsWith shapesByName = go (0 :: Int) []
  where
    go depth prefix e
      | depth > 32 = []
      | otherwise = case recordShapeFieldsWith shapesByName e of
          [] -> []
          shapes ->
            mergePathDeps direct nested
            where
              names = map fsName shapes
              direct =
                [ (prefix ++ [fsName s], [prefix ++ [d] | d <- deps])
                | s <- shapes
                , ty <- maybeToList (fsType s)
                , let deps = [d | d <- surfaceThisRefs ty, d `elem` names]
                , not (null deps)
                ]
              nested =
                foldr
                  mergePathDeps
                  []
                  [ go (depth + 1) (prefix ++ [fsName s]) ty
                  | s <- shapes
                  , ty <- maybeToList (fsType s)
                  ]

recordShapeFieldsWith :: Map Text RecordShape -> Expr -> [FieldShape]
recordShapeFieldsWith shapesByName = \case
  ERecordType fs _ _ ->
    [FieldShape (nameText (rtfName f)) (bpQuantity (rtfPrefix f)) (Just (rtfType f)) | f <- fs]
  EAscription (EVar n) ty _
    | isLowerName (nameText n) ->
        [FieldShape (nameText n) Nothing (Just ty)]
  EAscription e _ _ -> recordShapeFieldsWith shapesByName e
  ECaptures e _ _ -> recordShapeFieldsWith shapesByName e
  e -> fromMaybe [] (shapeFieldsForType shapesByName e)

shapeFieldsForType :: Map Text RecordShape -> Expr -> Maybe [FieldShape]
shapeFieldsForType shapesByName ty = do
  hd <- typePathHead ty
  RecordShape params fields <- Map.lookup hd shapesByName
  let subst = Map.fromList (zip params (typeAppArgs ty))
  pure (map (substFieldShape subst) fields)

typeAppArgs :: Expr -> [Expr]
typeAppArgs = \case
  EApp f args -> typeAppArgs f ++ explicitArgs args
  EAscription e _ _ -> typeAppArgs e
  ECaptures e _ _ -> typeAppArgs e
  _ -> []
  where
    explicitArgs = mapMaybe $ \case
      ArgExplicit e -> Just e
      ArgImplicit e -> Just e
      _ -> Nothing

substFieldShape :: Map Text Expr -> FieldShape -> FieldShape
substFieldShape subst s =
  s {fsType = substExpr subst <$> fsType s}

substExpr :: Map Text Expr -> Expr -> Expr
substExpr subst expr = case expr of
  EVar n -> Map.findWithDefault expr (nameText n) subst
  ETuple es sp -> ETuple (map go es) sp
  ERecordType fs mtail sp ->
    ERecordType [f {rtfType = go (rtfType f)} | f <- fs] (go <$> mtail) sp
  EApp f args -> EApp (go f) (map substArg args)
  EDot e m -> EDot (go e) m
  EQDot e m -> EQDot (go e) m
  EArrow b body ->
    EArrow (substBinder subst b) (substExpr (dropBinder b subst) body)
  EForall bs body sp ->
    let subst' = foldr dropBinder subst bs
     in EForall (map (substBinder subst) bs) (substExpr subst' body) sp
  EExists bs body sp ->
    let subst' = foldr dropBinder subst bs
     in EExists (map (substBinder subst) bs) (substExpr subst' body) sp
  ETraitArrow c body -> ETraitArrow (go c) (go body)
  EEffRow fields mtail sp -> EEffRow [(n, go e) | (n, e) <- fields] (go <$> mtail) sp
  EVariant arms mtail sp -> EVariant (map substVariant arms) (go <$> mtail) sp
  EAscription e ty sp -> EAscription (go e) (go ty) sp
  ECaptures e caps sp -> ECaptures (go e) caps sp
  EOptionSugar e sp -> EOptionSugar (go e) sp
  other -> other
  where
    go = substExpr subst
    substArg = \case
      ArgExplicit e -> ArgExplicit (go e)
      ArgImplicit e -> ArgImplicit (go e)
      ArgInout e sp -> ArgInout (go e) sp
      ArgNamedBlock items sp -> ArgNamedBlock [(n, go <$> me) | (n, me) <- items] sp
    substBinder sub b = b {bType = substExpr sub <$> bType b, bDefault = substExpr sub <$> bDefault b}
    substVariant (VariantArm e ty) = VariantArm (go e) (go <$> ty)
    dropBinder b sub = maybe sub (\n -> Map.delete (nameText n) sub) (bName b)

topFieldsFromPaths :: [(FieldPath, Maybe Quantity)] -> [(Text, Maybe Quantity)]
topFieldsFromPaths paths =
  [ (f, joinFieldQuantities qs)
  | f <- fields
  , let qs = [q | ([f'], q) <- paths, f' == f]
  ]
  where
    fields = foldr (\p acc -> case p of [f] | f `notElem` acc -> f : acc; _ -> acc) [] (map fst paths)

-- | Combine field-quantity lists, preserving the two independent linear
-- axes: @>=1@ is a drop obligation, @<=1@ is a duplication limit, and their
-- join is @1@. An annotation never weakens an inferred obligation and vice
-- versa.
mergeFieldQuantities ::
  [(Text, Maybe Quantity)] -> [(Text, Maybe Quantity)] -> [(Text, Maybe Quantity)]
mergeFieldQuantities annotated inferred =
  [(f, joinFieldQuantities (lookupAll f annotated ++ lookupAll f inferred)) | f <- fields]
  where
    fields = map fst annotated ++ [f | (f, _) <- inferred, f `notElem` map fst annotated]

lookupAll :: Eq a => a -> [(a, b)] -> [b]
lookupAll k = map snd . filter ((== k) . fst)

mergePathQuantities ::
  [(FieldPath, Maybe Quantity)] -> [(FieldPath, Maybe Quantity)] -> [(FieldPath, Maybe Quantity)]
mergePathQuantities annotated inferred =
  [(p, joinFieldQuantities (lookupAll p annotated ++ lookupAll p inferred)) | p <- paths]
  where
    paths = dedupPaths (map fst annotated ++ map fst inferred)

dedupPaths :: [FieldPath] -> [FieldPath]
dedupPaths = foldr (\p ps -> if p `elem` ps then ps else p : ps) []

mergePathDeps :: [(FieldPath, [FieldPath])] -> [(FieldPath, [FieldPath])] -> [(FieldPath, [FieldPath])]
mergePathDeps a b =
  [ (p, dedupPaths (concat (lookupAll p a ++ lookupAll p b)))
  | p <- dedupPaths (map fst a ++ map fst b)
  ]

pathText :: FieldPath -> Text
pathText = T.intercalate "."

pathKey :: VInfo -> FieldPath -> Text
pathKey vi p = vKey vi <> "." <> pathText p

refEscapeKey :: VInfo -> Text
refEscapeKey vi = vKey vi <> "$refescape"

usagePathOf :: VInfo -> Text -> Maybe FieldPath
usagePathOf vi k
  | k == vKey vi = Just []
  | Just rest <- T.stripPrefix (vKey vi <> ".") k
  , rest /= "~" =
      Just (T.splitOn "." rest)
  | otherwise = Nothing

pathUsage :: VInfo -> FieldPath -> Usage -> UseCount
pathUsage vi p u =
  foldr seqUC zeroUC
    [ c
    | (k, c) <- Map.toList u
    , Just q <- [usagePathOf vi k]
    , not (null q)
    , pathsOverlap p q
    ]

joinFieldQuantities :: [Maybe Quantity] -> Maybe Quantity
joinFieldQuantities qs
  | Just QOne `elem` qs = Just QOne
  | Just QAtMostOne `elem` qs && Just QAtLeastOne `elem` qs = Just QOne
  | Just QAtLeastOne `elem` qs = Just QAtLeastOne
  | Just QAtMostOne `elem` qs = Just QAtMostOne
  | Just QZero `elem` qs = Just QZero
  | Just QOmega `elem` qs = Just QOmega
  | otherwise = case [q | q@(Just (QTerm _)) <- qs] of
      (q : _) -> q
      [] -> Nothing

joinVInfo :: VInfo -> VInfo -> VInfo
joinVInfo a b =
  a
    { vQ = joinFieldQuantities [vQ a, vQ b]
    , vFields = mergeFieldQuantities (vFields a) (vFields b)
    , vPathFields = mergePathQuantities (vPathFields a) (vPathFields b)
    , vNonDupValue = vNonDupValue a || vNonDupValue b
    , vNonDupFields = dedupPaths (vNonDupFields a ++ vNonDupFields b)
    , vMutable = vMutable a || vMutable b
    , vStoredTypeExpr = vStoredTypeExpr a `orElse` vStoredTypeExpr b
    , vMutableDiagFields = if null (vMutableDiagFields a) then vMutableDiagFields b else vMutableDiagFields a
    , vDeps = vDeps a ++ [d | d <- vDeps b, d `notElem` vDeps a]
    , vPathDeps = mergePathDeps (vPathDeps a) (vPathDeps b)
    , vOpenTail = vOpenTail a `orElse` vOpenTail b
    }
  where
    orElse (Just x) _ = Just x
    orElse Nothing y = y

-- | §13.2.1: the fields a record literal makes linear because their
-- initializer transfers a quantity-1 value (a linear binding or a
-- quantity-1 field path of a tracked record). The resulting record value
-- owns those resources, so the whole record is linear for whole-record
-- use until they are consumed.
litLinearFields :: Env -> Expr -> [(Text, Maybe Quantity)]
litLinearFields env = \case
  ERecordLit items _ ->
    [ (nameText (riName it), Just (fromMaybe QOne (positiveTransferQuantity env v)))
    | it <- items
    , Just v <- [riValue it]
    , transfersLinear env v
    ]
  EAscription e _ _ -> litLinearFields env e
  ECaptures e _ _ -> litLinearFields env e
  _ -> []

litPathFields :: Env -> Expr -> [(FieldPath, Maybe Quantity)]
litPathFields env = \case
  ERecordLit items _ ->
    mergePathQuantities direct nested
    where
      direct =
        [ ([nameText (riName it)], Just (fromMaybe QOne (positiveTransferQuantity env v)))
        | it <- items
        , Just v <- [riValue it]
        , transfersLinear env v
        ]
      nested =
        concat
          [ [ (nameText (riName it) : p, q)
            | (p, q) <- storedPathFields env v
            ]
          | it <- items
          , Just v <- [riValue it]
          ]
  EAscription e _ _ -> litPathFields env e
  ECaptures e _ _ -> litPathFields env e
  _ -> []

litNonDuplicableFields :: Env -> Expr -> [FieldPath]
litNonDuplicableFields env = \case
  ERecordLit items _ ->
    dedupPaths $
      [ [nameText (riName it)]
      | it <- items
      , Just v <- [riValue it]
      , transfersNonDuplicable env v
      ]
      ++ concat
        [ [nameText (riName it) : p | p <- storedNonDupFields env v]
        | it <- items
        , Just v <- [riValue it]
        ]
  EAscription e _ _ -> litNonDuplicableFields env e
  ECaptures e _ _ -> litNonDuplicableFields env e
  _ -> []

storedPathFields :: Env -> Expr -> [(FieldPath, Maybe Quantity)]
storedPathFields env e = case e of
  ERecordLit {} -> litPathFields env e
  EAscription e' ty _ -> mergePathQuantities (recordPathFields env ty) (storedPathFields env e')
  ECaptures e' _ _ -> storedPathFields env e'
  EApp f args ->
    mergePathQuantities
      (ctorPathFields env f args)
      (maybe [] vPathFields (calleeStorageInfo env f))
  _
    | Just (vi, path, _) <- placeOf env e ->
        rebasePathFields path (vPathFields vi)
  _ -> []

storedNonDupFields :: Env -> Expr -> [FieldPath]
storedNonDupFields env e = case e of
  ERecordLit {} -> litNonDuplicableFields env e
  EAscription e' ty _ ->
    let annotated = [p | (p, q) <- recordPathFields env ty, nonDupQuantity q]
        inferred = storedNonDupFields env e'
     in dedupPaths (annotated ++ inferred)
  ECaptures e' _ _ -> storedNonDupFields env e'
  EApp f args ->
    dedupPaths $
      [p | (p, q) <- ctorPathFields env f args, nonDupQuantity q]
        ++ maybe [] vNonDupFields (calleeStorageInfo env f)
  _
    | Just (vi, path, _) <- placeOf env e ->
        rebasePaths path (nonDupFields vi)
  _ -> []

rebasePathFields :: FieldPath -> [(FieldPath, Maybe Quantity)] -> [(FieldPath, Maybe Quantity)]
rebasePathFields base fields =
  [ (rest, q)
  | (p, q) <- fields
  , base `isPrefixOf` p
  , let rest = drop (length base) p
  , not (null rest)
  ]

rebasePaths :: FieldPath -> [FieldPath] -> [FieldPath]
rebasePaths base fields =
  dedupPaths
    [ rest
    | p <- fields
    , base `isPrefixOf` p
    , let rest = drop (length base) p
    , not (null rest)
    ]

ctorPathFields :: Env -> Expr -> [Arg] -> [(FieldPath, Maybe Quantity)]
ctorPathFields env f args =
  case appHeadVar env f of
    Just cn
      | not (Map.member cn (eVars env))
      , Just params <- lookup cn (Map.findWithDefault [] cn (eCtors env)) ->
          mergePathQuantities (direct params args) (nested params args)
    _ -> []
  where
    direct params args0 =
      [ ([n], q)
      | p <- ctorParamArgs params args0
      , Just n <- [cpiName p]
      , let q = cpiQuantity p
      , nonDupQuantity q || positiveLowerQuantity q
      ]
    nested params args0 =
      concat
        [ [ (n : p, q)
          | Just n <- [cpiName pinfo]
          , (p, q) <- maybe [] (recordPathFields env) (cpiType pinfo)
          ]
        | pinfo <- ctorParamArgs params args0
        ]
    ctorParamArgs params0 = snd . foldl step (0 :: Int, [])
      where
        step (i, acc) = \case
          ArgExplicit _ -> (i + 1, acc ++ maybeToList (atMay i params0))
          ArgInout _ _ -> (i + 1, acc ++ maybeToList (atMay i params0))
          ArgNamedBlock items _ ->
            ( i
            , acc
                ++ [ p
                   | (n, _) <- items
                   , Just p <- [find ((== Just (nameText n)) . cpiName) params0]
                   ]
            )
          ArgImplicit _ -> (i, acc)
        atMay i xs
          | i >= 0 = listToMaybe (drop i xs)
          | otherwise = Nothing

storedLinearFields :: Env -> Expr -> [(Text, Maybe Quantity)]
storedLinearFields env e =
  mergeFieldQuantities top (topFieldsFromPaths (storedPathFields env e))
  where
    top = case e of
      ERecordLit {} -> mergeFieldQuantities (resolveFields (eAliases env) e) (litLinearFields env e)
      EVar n
        | Just vi <- Map.lookup (nameText n) (eVars env) ->
            [(f, q) | (f, q) <- vFields vi, positiveLowerQuantity q]
      EAscription e' ty _ -> mergeFieldQuantities (resolveFields (eAliases env) ty) (storedLinearFields env e')
      ECaptures e' _ _ -> storedLinearFields env e'
      _ -> []

storedRootQuantity :: Env -> Expr -> Maybe Quantity
storedRootQuantity env e = case placeOf env e of
  Just (vi, [], _)
    | positiveLowerQuantity (vQ vi) -> vQ vi
    | not (null (linPaths vi)) -> Just QOne
    | otherwise -> Nothing
  Just (vi, path, _) -> pathPositiveQuantity vi path
  Nothing -> case e of
    ERecordLit {} -> Nothing
    EAscription e' _ _ -> storedRootQuantity env e'
    ECaptures e' _ _ -> storedRootQuantity env e'
    EApp f args ->
      joinFieldQuantities $
        ctorStoresQuantityWith positiveLowerQuantity env f args
          : [q | Just vi <- [calleeStorageInfo env f], let q = vQ vi, positiveLowerQuantity q]
    _ -> if transfersLinear env e then Just QOne else Nothing

storedValueInfo :: Env -> Text -> Span -> Expr -> VInfo
storedValueInfo env key sp rhs =
  let storedTyExpr = storedValueTypeExpr env rhs
      typeInfo =
        if storedValueHasCompleteStorageShape env rhs
          then Nothing
          else storedValueInfoFromType env key sp <$> storedTyExpr
      linearFields = mergeFieldQuantities (storedLinearFields env rhs) (maybe [] vFields typeInfo)
      pathFields = mergePathQuantities (storedPathFields env rhs) (maybe [] vPathFields typeInfo)
      deps = maybe [] vDeps typeInfo
      pathDeps = maybe [] vPathDeps typeInfo
      nonDupFieldNames = dedupPaths (storedNonDupFields env rhs ++ maybe [] vNonDupFields typeInfo)
      rootQuantity = joinFieldQuantities [storedRootQuantity env rhs, typeInfo >>= vQ]
      diagFields = Map.findWithDefault [] sp (eMutableBindingFields env)
      storedTyText = case lookup "storedValueType" diagFields of
        Just t -> Just t
        Nothing -> case rhs of
          EAscription _ ty _ -> Just (renderExprSrc ty)
          _ -> Nothing
      nonDupHidden =
        ( transfersNonDuplicable env rhs
            && not (maybe False (nonDupQuantity . Just) rootQuantity)
            && null (storedNonDupFields env rhs)
        )
          || maybe False vNonDupValue typeInfo
   in (plainV key sp)
        { vMutable = True
        , vQ = rootQuantity
        , vFields = linearFields
        , vPathFields = pathFields
        , vDeps = deps
        , vPathDeps = pathDeps
        , vNonDupValue = nonDupHidden
        , vNonDupFields = nonDupFieldNames
        , vStoredTypeText = storedTyText
        , vStoredTypeExpr = storedTyExpr
        , vMutableDiagFields = diagFields
        }

storedValueHasConcreteShape :: Env -> Expr -> Bool
storedValueHasConcreteShape env = \case
  ERecordLit {} -> True
  EAscription e _ _ -> storedValueHasConcreteShape env e
  ECaptures e _ _ -> storedValueHasConcreteShape env e
  EVar n ->
    let cn = nameText n
     in not (Map.member cn (eVars env)) && Map.member cn (eCtors env)
  EApp f _
    | Just cn <- appHeadVar env f ->
        not (Map.member cn (eVars env)) && Map.member cn (eCtors env)
  e
    | Just _ <- placeOf env e -> True
  _ -> False

-- | True only when the value shape is precise enough to own the mutable-cell
-- storage facts without consulting the declared/ascribed cell type.  An
-- ascription on mutable storage is the cell's type, not just an initializer
-- check; it can contain hidden variant payload obligations even when the
-- immediate initializer is a concrete droppable constructor.
storedValueHasCompleteStorageShape :: Env -> Expr -> Bool
storedValueHasCompleteStorageShape env = \case
  EAscription {} -> False
  ECaptures e _ _ -> storedValueHasCompleteStorageShape env e
  e -> storedValueHasConcreteShape env e

storedValueTypeExpr :: Env -> Expr -> Maybe Expr
storedValueTypeExpr env = \case
  EAscription _ ty _ -> Just ty
  ECaptures e _ _ -> storedValueTypeExpr env e
  EApp f _ -> calleeDemandName env f >>= (`Map.lookup` eValueResultTypes env)
  _ -> Nothing

storedValueInfoFromType :: Env -> Text -> Span -> Expr -> VInfo
storedValueInfoFromType env key sp ty =
  let pathFields = recordPathFields env ty
      pathDeps = recordPathDeps env ty
      fields = mergeFieldQuantities (resolveFields (eAliases env) ty) (topFieldsFromPaths pathFields)
      nonDupFieldNames = [p | (p, q) <- pathFields, nonDupQuantity q]
      hiddenPositive = typeMayContainPositive env ty && null [() | (_, q) <- pathFields, positiveLowerQuantity q]
      hiddenNonDup =
        typeMayContainNonDuplicable env ty
          && null nonDupFieldNames
          && not hiddenPositive
      diagFields = Map.findWithDefault [] sp (eMutableBindingFields env)
   in (plainV key sp)
        { vMutable = True
        , vQ = if hiddenPositive then Just QOne else Nothing
        , vFields = fields
        , vPathFields = pathFields
        , vDeps = resolveDeps (eFieldDeps env) ty
        , vPathDeps = pathDeps
        , vNonDupValue = hiddenNonDup
        , vNonDupFields = nonDupFieldNames
        , vStoredTypeText = Just (renderExprSrc ty)
        , vStoredTypeExpr = Just ty
        , vMutableDiagFields = diagFields
        }

storedActionResultInfo :: Env -> VInfo -> Expr -> VInfo
storedActionResultInfo env oldInfo action =
  case actionResultValueExpr env action of
    Just valueExpr ->
      inheritStoredCellType env oldInfo False (storedValueInfo env key sp valueExpr)
    Nothing -> case actionResultType env action <|> vStoredTypeExpr oldInfo of
      Just ty -> storedValueInfoFromType env key sp ty
      Nothing ->
        (plainV key sp)
            { vMutable = True
            , vStoredTypeText = vStoredTypeText oldInfo
            , vStoredTypeExpr = vStoredTypeExpr oldInfo
            , vMutableDiagFields = vMutableDiagFields oldInfo
            }
  where
    key = vKey oldInfo
    sp = vSpan oldInfo

storedValueInfoForWrite :: Env -> VInfo -> Expr -> VInfo
storedValueInfoForWrite env oldInfo rhs =
  inheritStoredCellType env oldInfo False (storedValueInfo env (vKey oldInfo) (vSpan oldInfo) rhs)

inheritStoredCellType :: Env -> VInfo -> Bool -> VInfo -> VInfo
inheritStoredCellType env oldInfo mergeFallback vi =
  let fallback = storedValueInfoFromType env (vKey oldInfo) (vSpan oldInfo) <$> vStoredTypeExpr oldInfo
      mergeFacts base extra =
        base
          { vQ = joinFieldQuantities [vQ base, vQ extra]
          , vFields = mergeFieldQuantities (vFields base) (vFields extra)
          , vPathFields = mergePathQuantities (vPathFields base) (vPathFields extra)
          , vDeps = vDeps base ++ [d | d <- vDeps extra, d `notElem` vDeps base]
          , vPathDeps = mergePathDeps (vPathDeps base) (vPathDeps extra)
          , vNonDupValue = vNonDupValue base || vNonDupValue extra
          , vNonDupFields = dedupPaths (vNonDupFields base ++ vNonDupFields extra)
          }
      vi' =
        if mergeFallback
          then maybe vi (mergeFacts vi) fallback
          else vi
   in vi'
        { vStoredTypeText = vStoredTypeText vi' <|> vStoredTypeText oldInfo
        , vStoredTypeExpr = vStoredTypeExpr vi' <|> vStoredTypeExpr oldInfo
        , vMutableDiagFields =
            if null (vMutableDiagFields vi')
              then vMutableDiagFields oldInfo
              else vMutableDiagFields vi'
        }

actionResultValueExpr :: Env -> Expr -> Maybe Expr
actionResultValueExpr env = \case
  EAscription e _ _ -> actionResultValueExpr env e
  ECaptures e _ _ -> actionResultValueExpr env e
  EApp f args
    | Just n <- appHeadVar env f
    , maybe False buLiftLike (Map.lookup n builtinUsage)
    , (valueExpr : _) <- reverse (explicitExprs args) ->
        Just valueExpr
  _ -> Nothing

actionResultType :: Env -> Expr -> Maybe Expr
actionResultType env = \case
  EAscription _ ty _ -> Just (unwrapActionType (eMonadicResultHeads env) ty)
  ECaptures e _ _ -> actionResultType env e
  EApp f _ -> calleeDemandName env f >>= (`Map.lookup` eResultTypes env)
  e -> calleeDemandName env e >>= (`Map.lookup` eResultTypes env)

-- | Does this expression transfer ownership of a quantity-1 value? True
-- for a place that is a linear binding or a quantity-1 field path of a
-- tracked record (§12.4).
transfersLinear :: Env -> Expr -> Bool
transfersLinear env e = case placeOf env e of
  Just (vi, [], _) ->
    positiveLowerQuantity (vQ vi) || not (null (linPaths vi))
  Just (vi, path, _) -> isLinearPath vi path
  Nothing -> case e of
    ERecordLit items _ -> any (maybe False (transfersLinear env) . riValue) items
    EAscription e' _ _ -> transfersLinear env e'
    ECaptures e' _ _ -> transfersLinear env e'
    EApp f args ->
      ctorStoresWith positiveLowerQuantity env f args
        || maybe False summaryHasPositive (calleeStorageInfo env f)
        || anyArg (transfersLinear env) args
    _ -> False

transfersNonDuplicable :: Env -> Expr -> Bool
transfersNonDuplicable env e = case placeOf env e of
  Just (vi, [], _) -> vQ vi `elem` [Just QOne, Just QAtMostOne] || vNonDupValue vi || not (null (nonDupFields vi))
  Just (vi, path, _) -> isNonDupPath vi path
  Nothing -> case e of
    ERecordLit items _ -> any (maybe False (transfersNonDuplicable env) . riValue) items
    EAscription e' _ _ -> transfersNonDuplicable env e'
    ECaptures e' _ _ -> transfersNonDuplicable env e'
    EApp f args ->
      ctorStoresWith nonDupQuantity env f args
        || maybe False valueMayContainNonDuplicable (calleeStorageInfo env f)
        || anyArg (transfersNonDuplicable env) args
    _ -> False

valueMayContainNonDuplicable :: VInfo -> Bool
valueMayContainNonDuplicable vi =
  vQ vi `elem` [Just QOne, Just QAtMostOne] || vNonDupValue vi || not (null (nonDupFields vi))

summaryHasPositive :: VInfo -> Bool
summaryHasPositive vi =
  positiveLowerQuantity (vQ vi) || not (null (linPaths vi))

pathPositiveQuantity :: VInfo -> [Text] -> Maybe Quantity
pathPositiveQuantity vi path =
  joinFieldQuantities [q | (p, q) <- vPathFields vi, pathsOverlap p path, positiveLowerQuantity q]

isNonDupPath :: VInfo -> [Text] -> Bool
isNonDupPath vi path = any (pathsOverlap path) (nonDupFields vi)

anyArg :: (Expr -> Bool) -> [Arg] -> Bool
anyArg p = any $ \case
  ArgExplicit e -> p e
  ArgInout e _ -> p e
  ArgNamedBlock items _ -> any (maybe False p . snd) items
  _ -> False

ctorStoresWith :: (Maybe Quantity -> Bool) -> Env -> Expr -> [Arg] -> Bool
ctorStoresWith qPred env f args = maybe False (const True) (ctorStoresQuantityWith qPred env f args)

ctorStoresQuantityWith :: (Maybe Quantity -> Bool) -> Env -> Expr -> [Arg] -> Maybe Quantity
ctorStoresQuantityWith qPred env f args =
  case appHeadVar env f of
    Just cn
      | not (Map.member cn (eVars env))
      , Just params <- lookup cn (Map.findWithDefault [] cn (eCtors env)) ->
          let stored = filter qPred (ctorArgQuantities params args)
           in if null stored then Nothing else Just (fromMaybe QOne (joinFieldQuantities stored))
    _ -> Nothing
  where
    ctorArgQuantities params0 = snd . foldl step (0 :: Int, [])
      where
        step (i, qs) = \case
          ArgExplicit _ -> (i + 1, qs ++ maybeToList (cpiQuantity <$> atMay i params0))
          ArgInout _ _ -> (i + 1, qs ++ maybeToList (cpiQuantity <$> atMay i params0))
          ArgNamedBlock items _ ->
            ( i
            , qs
                ++ [ cpiQuantity p
                   | (n, _) <- items
                   , Just p <- [find ((== Just (nameText n)) . cpiName) params0]
                   ]
            )
          ArgImplicit _ -> (i, qs)
        atMay i xs
          | i >= 0 = listToMaybe (drop i xs)
          | otherwise = Nothing

positiveTransferQuantity :: Env -> Expr -> Maybe Quantity
positiveTransferQuantity env e = case placeOf env e of
  Just (vi, [], _)
    | positiveLowerQuantity (vQ vi) -> vQ vi
    | not (null (linPaths vi)) -> Just QOne
    | otherwise -> Nothing
  Just (vi, path, _) -> pathPositiveQuantity vi path
  Nothing -> case e of
    EAscription e' _ _ -> positiveTransferQuantity env e'
    ECaptures e' _ _ -> positiveTransferQuantity env e'
    EApp f args ->
      joinFieldQuantities $
        ctorStoresQuantityWith positiveLowerQuantity env f args
          : [q | Just vi <- [calleeStorageInfo env f], let q = vQ vi, positiveLowerQuantity q]
    _ -> if transfersLinear env e then Just QOne else Nothing

-- | Does this record type carry an abstract residual row tail @(... |
-- r)@ where @r@ is a row variable (§11.3.1A, §13.2.7)? A tail that is a
-- row variable (any non-record expression) is abstract; an explicit
-- closed extension @(... | (more fields))@ is followed structurally. A
-- bare type-alias spelling whose row tail is not visible here is treated
-- conservatively as having no abstract tail (no false positive).
-- | The abstract residual row variable of an open record type, if any
-- (§13.2.7). Returns the row-variable spelling so a §3.2.4
-- @kappa.row.tail-quantity@ diagnostic can name the residual row variable
-- @r@ in its @RecTailSatisfies r q@ obligation. An anonymous (unnamed)
-- abstract tail yields @"_"@.
hasAbstractTail :: Map Text [(Text, Maybe Quantity)] -> Expr -> Maybe Text
hasAbstractTail aliases = go (0 :: Int)
  where
    go n e
      | n > 32 = Nothing -- guard against accidental deep nesting
      | otherwise = case e of
          ERecordType _ (Just tailE) _ -> tailAbstract n tailE
          ERecordType _ Nothing _ -> Nothing
          EAscription e' _ _ -> go n e'
          ECaptures e' _ _ -> go n e'
          _ -> Nothing
    tailAbstract n tailE = case tailE of
      -- a row-variable spelling that is not a known record alias is an
      -- abstract residual tail; a record alias is conservatively closed
      EVar v
        | Map.member (nameText v) aliases -> Nothing
        | otherwise -> Just (nameText v)
      ERecordType {} -> go (n + 1) tailE
      EAscription e' _ _ -> tailAbstract n e'
      ECaptures e' _ _ -> tailAbstract n e'
      _ -> Just "_"

-- | Resolve a (possibly aliased) record type to its §13.2.1 field
-- dependencies: field ↦ sibling labels its type mentions via 'this'.
resolveDeps :: Map Text [(Text, [Text])] -> Expr -> [(Text, [Text])]
resolveDeps depAliases = go
  where
    go = \case
      ERecordType fs _ _ -> fieldDepsOf fs
      EAscription (EVar n) ty _
        | isLowerName (nameText n) ->
            fieldDepsOf [RecTypeField False False emptyPrefix Nothing n ty]
      e
        | Just hd <- typePathHead e -> Map.findWithDefault [] hd depAliases
      EAscription e _ _ -> go e
      ECaptures e _ _ -> go e
      _ -> []

-- | §13.2.1 field dependencies of a surface record type.
fieldDepsOf :: [RecTypeField] -> [(Text, [Text])]
fieldDepsOf fs =
  [ (nameText (rtfName f), deps)
  | f <- fs
  , let deps = [l | l <- surfaceThisRefs (rtfType f), l `elem` names]
  , not (null deps)
  ]
  where
    names = [nameText (rtfName f) | f <- fs]

-- ── Signature alignment ──────────────────────────────────────────────

-- | The signature's binder chain, implicits included (forall binders
-- and trait obligations are erased\/implicit slots, §11.3).
sigBinders :: Expr -> [Binder]
sigBinders = \case
  EForall bs body _ ->
    -- §11.3: forall (x : S). T ≡ (@0 x : S) -> T
    map
      ( \b ->
          b
            { bImplicit = True
            , bPrefix =
                (bPrefix b)
                  { bpQuantity = Just (fromMaybe QZero (bpQuantity (bPrefix b)))
                  }
            }
      )
      bs
      ++ sigBinders body
  ETraitArrow _ body -> sigBinders body
  EArrow b body -> b : sigBinders body
  ECaptures e _ _ -> sigBinders e
  _ -> []

dropBinders :: Expr -> Expr
dropBinders = \case
  EForall _ body _ -> dropBinders body
  ETraitArrow _ body -> dropBinders body
  EArrow _ body -> dropBinders body
  e -> e

isBorrowViewTy :: Set.Set Text -> Expr -> Bool
isBorrowViewTy heads ty =
  maybe False (`Set.member` heads) (typePathHead ty)

unwrapActionType :: Set.Set Text -> Expr -> Expr
unwrapActionType monadicResultHeads = \case
  EApp (EVar hd) args
    | isActionHead (nameText hd)
    , (a : _) <- reverse [e | ArgExplicit e <- args] ->
        a
  EApp f args
    | Just hd <- typePathHead f
    , isActionHead hd
    , (a : _) <- reverse [e | ArgExplicit e <- args] ->
        a
  EAscription e _ _ -> unwrapActionType monadicResultHeads e
  ECaptures e _ _ -> unwrapActionType monadicResultHeads e
  e -> e
  where
    isActionHead hd =
      hd `Set.member` builtinActionHeads || hd `Set.member` monadicResultHeads
    builtinActionHeads =
      Set.fromList
        [ "IO"
        , "UIO"
        , "STM"
        , "std.prelude.IO"
        , "std.prelude.UIO"
        , "std.prelude.STM"
        ]

-- | Align definition binders with signature binders: an explicit
-- definition binder claims a leading implicit signature binder of the
-- same name (§9.2); otherwise implicits are skipped.
alignParams :: [Binder] -> [Binder] -> [(Binder, Maybe Binder)]
alignParams [] _ = []
alignParams (b : bs) sbs = case sbs of
  (s : ss)
    | bImplicit s && not (bImplicit b) && not (sameName b s) ->
        alignParams (b : bs) ss
    | otherwise -> (b, Just s) : alignParams bs ss
  [] -> (b, Nothing) : alignParams bs []
  where
    sameName x y = case (bName x, bName y) of
      (Just nx, Just ny) -> nameText nx == nameText ny
      _ -> False

-- | The signature binders left after the definition binders consume
-- their share, mirroring 'alignParams' consumption (§12.2.5). Used to
-- carry the remaining quantity obligations onto a leading lambda chain.
remainingSig :: [Binder] -> [Binder] -> [Binder]
remainingSig [] sbs = sbs
remainingSig (b : bs) sbs = case sbs of
  (s : ss)
    | bImplicit s && not (bImplicit b) && not (sameName b s) ->
        remainingSig (b : bs) ss
    | otherwise -> remainingSig bs ss
  [] -> []
  where
    sameName x y = case (bName x, bName y) of
      (Just nx, Just ny) -> nameText nx == nameText ny
      _ -> False

-- | Explicit-argument demand of a definition, signature preferred.
fnParams :: Maybe Expr -> LetDef -> [PInfo]
fnParams msig ld =
  let sigPs = maybe [] sigBinders msig
      fromSig = [binderP b | b <- sigPs, not (bImplicit b)]
      aligned = alignParams (ldBinders ld) sigPs
      fromLet =
        [ mergeP (binderP b) (maybe defaultP binderP ms)
        | (b, ms) <- aligned
        , not (bImplicit b)
        , maybe True (not . bImplicit) ms
        ]
   in if null (ldBinders ld) then fromSig else fromLet
  where
    binderP b =
      let BinderPrefix mq mb = bPrefix b
       in defaultP
            { pName = nameText <$> bName b
            , pQuantity = if bInout b then Just QOne else mq
            , pBorrow = isJust mb
            , pInout = bInout b
            , pKnown = True
            , pEscapingParam = True
            , pReceiver = bReceiver b /= NoReceiver
            , pCaptureBound = captureBoundOf (bType b)
            , pEscapeKind = escapeKindFor (nameText <$> ldName ld)
            }
    mergeP p1 p2 =
      defaultP
        { pName = pName p1 `orElse` pName p2
        , pQuantity = pQuantity p1 `orElse` pQuantity p2
        , pBorrow = pBorrow p1 || pBorrow p2
        , pInout = pInout p1 || pInout p2
        , pKnown = pKnown p1 || pKnown p2
        , pEscapingParam = pEscapingParam p1 || pEscapingParam p2
        , pReceiver = pReceiver p1 || pReceiver p2
        , pCaptureBound = mergeCaptureBound (pCaptureBound p1) (pCaptureBound p2)
        , pEscapeKind = mergeEscapeKind (pEscapeKind p1) (pEscapeKind p2)
        }
    captureBoundOf = \case
      Just (ECaptures _ [] _) -> CapClosed
      Just (EAscription e _ _) -> captureBoundOf (Just e)
      _ -> CapAny
    mergeCaptureBound CapClosed _ = CapClosed
    mergeCaptureBound _ CapClosed = CapClosed
    mergeCaptureBound _ _ = CapAny
    escapeKindFor = \case
      Just nm -> maybe EscapeOrdinaryParam buEscape (Map.lookup nm builtinUsage)
      Nothing -> EscapeOrdinaryParam
    mergeEscapeKind EscapeOrdinaryParam k = k
    mergeEscapeKind k EscapeOrdinaryParam = k
    mergeEscapeKind k _ = k
    orElse (Just x) _ = Just x
    orElse Nothing y = y

-- ── Definition analysis ──────────────────────────────────────────────

analyzeLet ::
  Map Span Expr ->
  Map Span [(Text, Text)] ->
  Map Text [PInfo] ->
  Map Text [FieldShape] ->
  Map Text Expr ->
  Map Text Expr ->
  Map Text VInfo ->
  Map Span RefOp ->
  Map Span Text ->
  Map Span Quantity ->
  Map Text [(Text, Maybe Quantity)] ->
  Map Text RecordShape ->
  Map Text [(Text, [Text])] ->
  Map Text [(Text, [CtorParamInfo])] ->
  Map Text ProjUse ->
  Map Text [(Text, Quantity)] ->
  Set.Set Text ->
  Set.Set Text ->
  Set.Set Text ->
  Maybe Expr ->
  LetDef ->
  Analysis ()
analyzeLet expansions mutableBindingFields fns inoutResults resultTypes valueResultTypes resultStorage recognizedRefOps recognizedMultishotOps handlerOpQuantities aliases recordShapes aliasDeps ctors projs effs borrowViewHeads monadicResultHeads duplicableStorageHeads msig ld = do
  let sigPs = maybe [] sigBinders msig
      aligned = alignParams (ldBinders ld) sigPs
      -- §12.2.5: signature binders the equation-head params did not
      -- consume. When the body is a leading lambda chain, these carry
      -- the quantity obligations onto the lambda binders just as
      -- 'paramBind' does for equation-head params. Only the directly
      -- leading lambda may claim them: a lambda nested under any other
      -- form is a distinct closure, not this definition's binder chain.
      pendingSig = case ldBody ld of
        ELambda {} -> remainingSig (ldBinders ld) sigPs
        _ -> []
  binds <- catMaybes <$> mapM paramBind aligned
  let env =
          (Env (Map.fromList binds) fns inoutResults resultTypes valueResultTypes resultStorage recognizedRefOps recognizedMultishotOps handlerOpQuantities [] aliases recordShapes ctors projs Map.empty Map.empty aliasDeps effs expansions [] mutableBindingFields monadicResultHeads duplicableStorageHeads False)
          {ePendingSig = pendingSig}
  checkInoutResult aliases monadicResultHeads msig ld
  r <- walkE env (ldBody ld)
  let (u, taint) = flatR r
  forM_ binds $ \(_, vi) -> closeVar vi u
  -- §12.3.1: an explicit captures annotation on the declared result
  -- type licenses the closure's borrow captures
  let resCaptures = maybe False capturesAnnotated resultTy
      resultTy = ldResultType ld `orElseE` (sigResultOf =<< msig)
  unless resCaptures $
    forM_ taint $ \sp ->
      -- §3.1.1A (line 602-603): cite BOTH the borrow introduction site —
      -- the borrow-capturing closure formation site carried by the taint
      -- (RoleBorrowStart) — and the failing escape site, the definition
      -- body's result expression the closure flows out through
      -- (RoleBorrowEscapeSite).
      emitRel "E_QTT_BORROW_ESCAPE" "kappa.borrow.escape" sp
        [ related RoleBorrowStart sp "borrow-capturing closure formed here"
        , related RoleBorrowEscapeSite (exprSpan (ldBody ld)) "escapes through the result here"
        ]
        "a closure capturing a borrowed binding escapes through the result (§12.3.2)"
  where
    paramBind (b, ms) = case bName b of
      Nothing -> pure Nothing
      Just n -> do
        let BinderPrefix mq mb = bPrefix b
            BinderPrefix sq sb = maybe emptyPrefix bPrefix ms
            q = mq `orElse` sq
            mark = mb `orElse` sb
            ty = bType b `orElse` (bType =<< ms)
            -- §12.4.3: a BorrowView value is a reified borrow of its
            -- region — capturing it in a result-escaping closure is the
            -- same escape as capturing an anonymous borrowed binding
            borrowViewed = maybe False (isBorrowViewTy borrowViewHeads) ty
            anon = mark == Just (BorrowMark Nothing) || borrowViewed
            pathFields = maybe [] (recordPathFieldsWith recordShapes ctors) ty
            fields = mergeFieldQuantities (maybe [] (resolveFields aliases) ty) (topFieldsFromPaths pathFields)
            deps = maybe [] (resolveDeps aliasDeps) ty
            pathDeps = maybe [] (recordPathDepsWith recordShapes) ty
            -- §13.2.7: a linear (consuming) receiver of an open record
            -- type owns its abstract residual tail; track it so a body
            -- that forgets the tail without transferring or restoring it
            -- is rejected
            openTail
              | isNothing mark
              , q `elem` [Just QOne, Just QAtLeastOne]
              , Just rowVar <- (hasAbstractTail aliases =<< ty) =
                  Just (rowVar, bSpan b)
              | otherwise = Nothing
        k <- freshKey (nameText n)
        pure
            ( Just
                ( nameText n
                , (plainV k (bSpan b))
                    { vQ = q
                    , vBorrowed = isJust mark || borrowViewed
                    , vAnonBorrow = anon
                    , vFields = fields
                    , vPathFields = pathFields
                    , vDeps = deps
                    , vPathDeps = pathDeps
                    , vOpenTail = openTail
                    }
                )
            )
    orElseE (Just x) _ = Just x
    orElseE Nothing y = y
    sigResultOf e = case sigBinders e of
      [] -> Just e
      bs -> bType (last bs) `orElseE` Just e
    capturesAnnotated = \case
      ECaptures {} -> True
      EArrow _ r -> capturesAnnotated r
      _ -> False
    orElse (Just x) _ = Just x
    orElse Nothing y = y

-- | §18.9.3: an @inout@ parameter must be threaded back through the
-- declared result as a record field of the same name.
checkInoutResult :: Map Text [(Text, Maybe Quantity)] -> Set.Set Text -> Maybe Expr -> LetDef -> Analysis ()
checkInoutResult aliases monadicResultHeads msig ld =
  forM_ inouts $ \(nm, bsp) -> do
    let resTy = ldResultType ld `orElse` (sigResult <$> msig)
    forM_ resTy $ \ty ->
      unless (threadsField nm (unwrapActionType monadicResultHeads ty)) $
        emit "E_QTT_INOUT_THREADED_FIELD_MISSING" "kappa.inout.restoration" bsp
          ("the result type does not thread the inout place '" <> nm <> "' back as a field (§18.9.3)")
  where
    -- a definition binder claims its signature binder's inout marker
    aligned = alignParams (ldBinders ld) (maybe [] sigBinders msig)
    inouts
      | null (ldBinders ld) =
          [ (nameText n, bSpan b)
          | b <- maybe [] sigBinders msig
          , bInout b
          , Just n <- [bName b]
          ]
      | otherwise =
          [ (nameText n, bSpan b)
          | (b, ms) <- aligned
          , bInout b || maybe False bInout ms
          , Just n <- [bName b `orElse` (bName =<< ms)]
          ]
    orElse (Just x) _ = Just x
    orElse Nothing y = y
    sigResult = dropBinders
    threadsField nm ty =
      any (\(field, q) -> field == nm && q == Just QOne) (resolveFields aliases ty)

-- | Close one binding's scope: enforce its quantity interval, including
-- per-path consumption of its quantity-1 record fields (§12.4).
closeVar :: VInfo -> Usage -> Analysis ()
closeVar = closeVarWith Nothing

closeVarWith :: Maybe MutableCloseContext -> VInfo -> Usage -> Analysis ()
closeVarWith mctx vi u = do
  let UseCount {ucLo = rLo, ucHi = rHi, ucMoves = rOccs, ucTouches = rTlo, ucViolations = viols} =
        Map.findWithDefault zeroUC (vKey vi) u
      res@(UseCount {ucMoves = resOccs, ucTouches = resTlo}) =
        Map.findWithDefault zeroUC (vKey vi <> ".~") u
      refEsc =
        Map.findWithDefault zeroUC (refEscapeKey vi) u
      rootHi = rHi + ucHi res
      rootLo = rLo + ucLo res + ucLo refEsc
      rootTlo = rTlo + resTlo + ucTouches refEsc
  -- §12.4: borrowing or re-projecting a path after an overlapping
  -- definite consume (no intervening restore — a restoring patch
  -- rebinds through a fresh root) is a compile-time error
  -- A borrow-after-consume is a violation only when the prior consume was
  -- DEFINITE: the binding (or the borrowed path) must actually be
  -- consumable. Moving an unrestricted (ω) value is a copy, not a consume,
  -- so re-reading the value afterwards is sound — e.g. `let q = p` then
  -- `p.value` for a plain (ω) record `p` (§12.4, §16.4.3 stable alias).
  let definiteConsume bp =
        vQ vi `elem` [Just QOne, Just QAtMostOne, Just QAtLeastOne]
          || isLinearPath vi bp
  forM_ (dedupViols viols) $ \(bp, bsp) ->
    when (definiteConsume bp) $
      -- §3.1.1A: cite the consume/borrow introduction site (the binding's
      -- declaration) and the failing later use site.
      emitRel "E_QTT_PATH_CONSUMED" "kappa.path.consumed" bsp
        [ related RoleConsumedHere (vSpan vi) ("'" <> nm <> "' introduced here")
        , related RoleUsedAfterConsume bsp "borrowed here after the path was consumed"
        ]
        ("'" <> nm <> T.concat (map ("." <>) bp)
           <> "' is borrowed after the path was consumed (§12.4); restore it by record update first")
  -- per-path overuse: a whole-record use re-consumes every moved path
  -- (a patch consumes the residue only, not the paths it replaces).
  -- §13.2.1: a record carrying a quantity-1 field is a linear resource
  -- for that field path regardless of the record binding's own quantity
  -- — a record literal that places a linear value into a field
  -- (vQ == Nothing, fields inferred) is just as much a linear resource as
  -- an annotated `1 r` binding. The drop check below keys on `linPaths`
  -- independent of `vQ vi`; the upper-bound check must do the same, or a
  -- linear field consumed twice (`free r.buf; free r.buf`) escapes.
  pathOver <- fmap or . forM (linPaths vi) $ \p -> do
    let pc@(UseCount {ucHi = pHi, ucMoves = pOccs}) = pathUsage vi p u
    if ucHi pc > 0 && rHi + pHi > 1
      then do
        -- the path is in linPaths, i.e. quantity-1 (linear/relevant)
        overuse "linear" (nm <> "." <> pathText p) (pOccs ++ rOccs)
        pure True
      else pure False
  -- §13.2.1: a record value carrying a quantity-1 field is a linear
  -- resource for whole-record use until those linear paths are consumed
  -- or restored. Consuming the whole record (or transferring it as a
  -- result/argument) moves every field; otherwise each linear field path
  -- must itself be consumed on every completion path, or its owned
  -- resource is silently dropped (§12.2.5). A whole-record consume sets
  -- the root move lower bound; a patch re-consumes unpatched linear paths
  -- (walkPatch), so this check sees restored records as consumed.
  let droppedFields
        -- a borrowed receiver carries no consumption obligation, and a
        -- whole-record transfer (root move/patch residue) moves every
        -- field with it
        | vBorrowed vi || rootLo >= 1 = []
        | otherwise =
            [ p
            | p <- linPaths vi
            , let fc = pathUsage vi p u
              -- a linear field is dropped when neither consumed (moved)
              -- nor borrowed (touched) on this completion path; a borrow
              -- discharges the obligation for its scope under §12.2.5
            , ucLo fc < 1 && not (ucTouched fc)
            ]
  forM_ droppedFields $ \p ->
    linearDrop (Just p) (vSpan vi)
      ("the quantity-1 field '" <> nm <> "." <> pathText p
         <> "' may be dropped without being consumed (§13.2.1, §12.2.5)")
  -- §13.2.7: a consuming open-record receiver must transfer (root move)
  -- or restore/extend (patch, which consumes the residue) its abstract
  -- residual tail; otherwise the tail — which may carry a linear
  -- resource — is forgotten without the required RecTailSatisfies r 0
  -- evidence. The whole-record drop below covers the case where the
  -- receiver is wholly unused, so the tail report is gated on the root
  -- being touched (the receiver was used, just not tail-transferred).
  -- §3.1.4/§3.2.4: this is an abstract residual row tail demanded at a
  -- structural quantity (0, the discard demand) with the required
  -- RecTailSatisfies evidence unavailable, so the diagnostic uses the
  -- dedicated row family kappa.row.tail-quantity and its portable alias
  -- E_ROW_TAIL_QUANTITY_UNSATISFIED (Spec.md:955-957, 3097-3128), naming
  -- the residual row variable r and the generated RecTailSatisfies r 0
  -- obligation.
  let tailDropped = case vOpenTail vi of
        Just (rowVar, _)
          | rootLo < 1 && rootTlo >= 1 && null droppedFields -> Just rowVar
        _ -> Nothing
  forM_ tailDropped $ \rowVar ->
    emit "E_ROW_TAIL_QUANTITY_UNSATISFIED" "kappa.row.tail-quantity" (vSpan vi)
      ("the abstract residual row tail '" <> rowVar <> "' of '" <> nm
         <> "' is dropped without transferring or restoring it; a "
         <> "consuming open-record receiver requires 'RecTailSatisfies "
         <> rowVar <> " 0' to forget a tail that may hold a linear resource "
         <> "(§13.2.7)")
  let tailWasDropped = isJust tailDropped
  case vQ vi of
    Just QOne -> do
      when (rootHi > 1) (overuse "linear" nm (rOccs ++ resOccs))
      -- the whole-record drop is reported only when no linear field or
      -- residual tail already carried the leak (otherwise those reports
      -- are the precise diagnostics for the same untransferred resource)
      when
        (rootTlo < 1 && rootHi <= 1 && not pathOver && null droppedFields && not tailWasDropped)
        (dropErr "linear")
    Just QAtLeastOne -> when (rootTlo < 1 && not tailWasDropped) (dropErr "relevant")
    Just QAtMostOne -> when (rootHi > 1) (overuse "affine" nm (rOccs ++ resOccs))
    _ -> pure ()
  where
    nm = T.takeWhile (/= '#') (vKey vi)
    overuse kind what occs =
      emit "E_QTT_LINEAR_OVERUSE" "kappa.quantity.unsatisfied"
        (occAt occs)
        ("'" <> what <> "' is consumed more often than its "
           <> kind
           <> " quantity permits (§12.2)")
    occAt occs = case drop 1 occs of
      (sp : _) -> sp
      [] -> vSpan vi
    dropErr kind =
      linearDrop Nothing (vSpan vi)
        ("'" <> nm <> "' (" <> kind <> ") may be dropped without being consumed (§12.2.5)")
    linearDrop path sp msg =
      case mctx of
        Just ctx | vMutable vi ->
          emitPayload "E_QTT_LINEAR_DROP" "kappa.var.mutable-binding" (mutableStoredDropPayload ctx vi path) sp msg
        _ ->
          emit "E_QTT_LINEAR_DROP" "kappa.quantity.positive-lower-bound" sp msg
    dedupViols = foldr (\v vs -> if v `elem` vs then vs else v : vs) []

mutableStoredDropPayload :: MutableCloseContext -> VInfo -> Maybe FieldPath -> Payload
mutableStoredDropPayload ctx vi mpath =
  foldl
    (\p (k, v) -> withPayloadField k v p)
    ( withPayloadField "quantityFact" "stored-value" $
        withPayloadField "sourceOperation" (mccSourceOperation ctx) $
          withPayloadField "occurrence" "user-written" $
            withPayloadField "selectedFacet" (mccSelectedFacet ctx) $
              withPayloadField "binding" binding $
                payloadKind "mutable-binding"
    )
    fields
  where
    binding = T.takeWhile (/= '#') (vKey vi)
    fields =
      vMutableDiagFields vi
        ++ missingTypeFields
        ++ [("storedValuePath", pathText p) | Just p <- [mpath], not (null p)]
    hasField k = any ((== k) . fst) (vMutableDiagFields vi)
    missingTypeFields =
      maybe
        []
        ( \t ->
            [ ("storedValueType", t) | not (hasField "storedValueType") ]
              ++ [ ("hiddenReferenceType", "Ref " <> t) | not (hasField "hiddenReferenceType") ]
        )
        (vStoredTypeText vi)

-- ── Place helpers (§12.4) ────────────────────────────────────────────

-- | A stable place rooted at a tracked binding: root info plus path.
-- | Whether a let-binder pattern is a wildcard discard — an explicit @_@ or a
-- @_@-spelled variable binder (the surface @let _ = …@ parses as the latter).
isWildBinder :: Pattern -> Bool
isWildBinder = \case
  PWild _ -> True
  PVar n -> nameText n == "_"
  PTyped p _ _ -> isWildBinder p
  _ -> False

refFacetValue :: Expr -> Bool
refFacetValue = \case
  ERefFacet {} -> True
  EAscription e _ _ -> refFacetValue e
  ECaptures e _ _ -> refFacetValue e
  _ -> False

placeOf :: Env -> Expr -> Maybe (VInfo, [Text], Span)
placeOf env = \case
  EVar n -> do
    vi <- Map.lookup (nameText n) (eVars env)
    if vMutable vi then Nothing else pure ()
    pure (vi, [], nameSpan n)
  EDot b (DotName f) -> do
    (vi, path, _) <- placeOf env b
    pure (vi, path ++ [nameText f], nameSpan f)
  EAscription e _ _ -> placeOf env e
  ECaptures e _ _ -> placeOf env e
  _ -> Nothing

varPlaceOf :: Env -> Expr -> Maybe (VInfo, [Text], Span)
varPlaceOf env = \case
  EVar n -> do
    vi <- Map.lookup (nameText n) (eVars env)
    if vMutable vi then pure () else Nothing
    pure (vi, [], nameSpan n)
  EDot b (DotName f) -> do
    (vi, path, _) <- varPlaceOf env b
    pure (vi, path ++ [nameText f], nameSpan f)
  EAscription e _ _ -> varPlaceOf env e
  _ -> Nothing

varInoutPlaceOf :: Env -> Expr -> Maybe (VInfo, [Text], Span)
varInoutPlaceOf env e =
  varPlaceOf env e <|> case projVarPlacesOf env e of
    Just ([place], _) -> Just place
    _ -> Nothing

-- | Resolve a place through any §12.4 borrowed place-alias binding:
-- @let & x = root.path@ makes @x.f@ an alias of @root.path.f@ for
-- borrow-lock purposes.
resolveBorrowAlias :: Env -> (VInfo, [Text], Span) -> (Text, [Text], Span)
resolveBorrowAlias env (vi, path, sp) =
  case Map.lookup (vKey vi) (eBorrowAliases env) of
    Just (rootK, rootPath) -> (rootK, rootPath ++ path, sp)
    Nothing -> (vKey vi, path, sp)

-- | The lock set a lexical borrow of a place opens: the path itself
-- (rebased through borrow aliases) plus, for a §13.2.1 dependent
-- record, the sibling fields the borrowed field's type mentions.
-- The borrow-introduction span @bsp@ (the @let &@ binding site, §3.1.1A)
-- is carried on every lock entry so 'checkBorrowOverlap' can relate it.
borrowLocks :: Env -> (VInfo, [Text], Span) -> [(Text, [Text], Span)]
borrowLocks env pl@(vi, path, bsp) =
  let (rootK, fullPath, _) = resolveBorrowAlias env pl
      depLocks
        | rootK == vKey vi = drop 1 (lockWithDeps vi path)
        | otherwise = []
   in (rootK, fullPath, bsp) : [(rootK, p, bsp) | p <- depLocks]

-- | Same-call static footprint facts use the same dependency-expanded place
-- model as lexical borrows, but keep the operation span of the call argument
-- for diagnostics.
placeFootprintLocks :: Env -> (VInfo, [Text], Span) -> Span -> [(Text, [Text], Span)]
placeFootprintLocks env pl opSp =
  [(rootK, path, opSp) | (rootK, path, _) <- borrowLocks env pl]

-- | A fully applied §9.1.1 projection (or local descriptor binding)
-- call: the stable places its yield leaves touch, plus the auxiliary
-- expressions (ordinary arguments, descriptor head) to walk normally.
projPlacesOf :: Env -> Expr -> Maybe ([(VInfo, [Text], Span)], [Expr])
projPlacesOf env e0 = case e0 of
  EApp f args
    | Just headKey <- staticPathHead env f
    , Just pu <- Map.lookup headKey (eProjs env)
    , length args == length (puIsPlace pu)
    , or (puIsPlace pu) -> do
        let split = zip (puIsPlace pu) args
            placeArgs =
              [ (nm, e)
              | ((True, ArgExplicit e), nm) <-
                  zip [p | p@(True, _) <- split] (puPlaceNames pu)
              ]
            ordArgs = [e | (False, ArgExplicit e) <- split]
        (places, aux) <- packPlaces pu placeArgs
        pure (places, ordArgs ++ aux)
  EApp (EVar f) args
    | Just du <- Map.lookup (nameText f) (eDescs env)
    , [arg] <- args -> do
        e <- case arg of
          ArgExplicit e -> Just e
          ArgInout e _ -> Just e
          _ -> Nothing
        (places, aux) <- case (puPlaceNames du, e) of
          (_, ERecordLit items _) ->
            packPlaces du
              [(nameText fn, fe) | RecItem _ fn (Just fe) <- items]
          ([pn], _) -> packPlaces du [(pn, e)]
          _ -> Nothing
        pure (places, EVar f : aux)
  _ -> Nothing
  where
    -- map each yield leaf through the supplied place arguments; place
    -- arguments that are not stable places are walked normally
    packPlaces pu pairs = do
      let leaves =
            [ (root, suffix, lookup root pairs)
            | (root, suffix) <- puYields pu
            ]
      resolved <- Just (mapMaybe leafPlace leaves)
      let aux = [e | (_, e) <- pairs, Nothing <- [placeOf env e]]
      pure (resolved, aux)
    leafPlace (_, suffix, Just argE) = do
      (vi, path, sp) <- placeOf env argE
      pure (vi, path ++ suffix, sp)
    leafPlace _ = Nothing

projVarPlacesOf :: Env -> Expr -> Maybe ([(VInfo, [Text], Span)], [Expr])
projVarPlacesOf env e0 = case e0 of
  EApp f args
    | Just headKey <- staticPathHead env f
    , Just pu <- Map.lookup headKey (eProjs env)
    , length args == length (puIsPlace pu)
    , or (puIsPlace pu) -> do
        let split = zip (puIsPlace pu) args
            placeArgs =
              [ (nm, e)
              | ((True, ArgExplicit e), nm) <-
                  zip [p | p@(True, _) <- split] (puPlaceNames pu)
              ]
            ordArgs = [e | (False, ArgExplicit e) <- split]
        (places, aux) <- packPlaces pu placeArgs
        pure (places, ordArgs ++ aux)
  EApp (EVar f) args
    | Just du <- Map.lookup (nameText f) (eDescs env)
    , [arg] <- args -> do
        e <- case arg of
          ArgExplicit e -> Just e
          ArgInout e _ -> Just e
          _ -> Nothing
        (places, aux) <- case (puPlaceNames du, e) of
          (_, ERecordLit items _) ->
            packPlaces du
              [(nameText fn, fe) | RecItem _ fn (Just fe) <- items]
          ([pn], _) -> packPlaces du [(pn, e)]
          _ -> Nothing
        pure (places, EVar f : aux)
  EAscription e _ _ -> projVarPlacesOf env e
  _ -> Nothing
  where
    packPlaces pu pairs = do
      let leaves =
            [ (root, suffix, lookup root pairs)
            | (root, suffix) <- puYields pu
            ]
      resolved <- Just (mapMaybe leafPlace leaves)
      let aux = [e | (_, e) <- pairs, Nothing <- [placeOf env e <|> varPlaceOf env e]]
      pure (resolved, aux)
    leafPlace (_, suffix, Just argE) = do
      (vi, path, sp) <- varPlaceOf env argE
      pure (vi, path ++ suffix, sp)
    leafPlace _ = Nothing

-- | Does this expression denote a (partially applied) projection
-- descriptor value (§16.1.5)?
descOf :: Env -> Expr -> Maybe ProjUse
descOf env = \case
  e
    | Just headKey <- staticPathHead env e
    , Just pu <- Map.lookup headKey (eProjs env) ->
        Just pu
  EVar f
    | Just du <- Map.lookup (nameText f) (eDescs env) -> Just du
  EApp f args
    | Just headKey <- staticPathHead env f
    , Just pu <- Map.lookup headKey (eProjs env)
    , length args == length (filter not (puIsPlace pu)) ->
        Just pu
  EAscription e _ _ -> descOf env e
  _ -> Nothing

pathsOverlap :: [Text] -> [Text] -> Bool
pathsOverlap a b = a `isPrefixOf` b || b `isPrefixOf` a

-- | Report a consuming use of @path@ under @vi@ while an overlapping
-- borrow is live (§12.4).
checkBorrowOverlap :: Env -> VInfo -> [Text] -> Span -> Analysis ()
checkBorrowOverlap env vi path sp =
  case filter conflict (eBorrows env) of
    [] -> pure ()
    -- §3.1.1A line 602: a borrow/path/ownership diagnostic MUST include
    -- the borrow-introduction site and the failing later use. The live
    -- borrow that this consume conflicts with carries its @let &@
    -- introduction span; the consuming occurrence is @sp@.
    ((_, _, bsp) : _) ->
      emitRel "E_QTT_BORROW_OVERLAP" "kappa.borrow.overlap" sp
        [ related RoleBorrowStart bsp "overlapping borrow introduced here"
        , related RoleConsumedHere sp "consumed here while the borrow is live"
        ]
        ("'" <> T.takeWhile (/= '#') (vKey vi)
           <> T.concat (map ("." <>) path)
           <> "' is consumed while a live borrow of an overlapping path exists (§12.4)")
  where
    conflict (root, bpath, _) = root == vKey vi && pathsOverlap bpath path

-- | Usage of a consuming occurrence of a place (whole binding or a
-- quantity-1 field path), checked against live borrows.
movePlace :: Env -> VInfo -> [Text] -> Span -> Analysis Usage
movePlace env vi path sp = do
  when (vQ vi == Just QZero) $
    emit "E_QTT_ERASED_RUNTIME_USE" "kappa.quantity.unsatisfied" sp
      ("erased (quantity 0) binding '" <> T.takeWhile (/= '#') (vKey vi) <> "' is used at runtime (§12.2.1)")
  checkBorrowOverlap env vi path sp
  pure $ case path of
    [] -> Map.singleton (vKey vi) (evUC (PMove [] sp) (oneUC sp))
    fs ->
      Map.fromList
        [ (vKey vi <> "." <> T.intercalate "." fs, oneUC sp)
        , (vKey vi, evUC (PMove fs sp) touchUC)
        ]

-- | Is the one-segment path a quantity-1 field of the binding?
isLinearPath :: VInfo -> [Text] -> Bool
isLinearPath vi path = any (pathsOverlap path) (linPaths vi)

-- | Non-consuming touch usage for a borrowed/read place: the root is
-- touched and, for a field path, that field path too. Touching a linear
-- field path discharges its §13.2.1 consumption obligation for the
-- borrow's scope (a borrow is non-consuming but does demand the field).
placeTouch :: VInfo -> [Text] -> Usage
placeTouch vi path =
  Map.fromListWith seqUC $
    (vKey vi, touchUC)
      : [ (vKey vi <> "." <> T.intercalate "." path, touchUC)
        | not (null path)
        ]

-- | 'placeTouch' over a list of resolved places (e.g. a projection's
-- yield leaves).
placesTouch :: [(VInfo, [Text], Span)] -> Usage
placesTouch places =
  Map.unionsWith seqUC [placeTouch vi path | (vi, path, _) <- places]

-- | Like 'placeTouch', but the root touch carries a §12.4 'PBorrow'
-- place event (for borrow-after-consume tracking) at the borrow span.
placeBorrow :: VInfo -> [Text] -> Span -> Usage
placeBorrow vi path sp =
  Map.fromListWith seqUC $
    (vKey vi, evUC (PBorrow path sp) touchUC)
      : [ (vKey vi <> "." <> T.intercalate "." path, touchUC)
        | not (null path)
        ]

mutableReadUsage :: VInfo -> [Text] -> Span -> Analysis Usage
mutableReadUsage vi path sp = do
  -- §18.6.1 current-value facet: even `x.f` first reads the current value
  -- stored in the hidden cell, then projects from the read result. The read is
  -- therefore a duplication position for the whole stored value, including
  -- sibling fields and hidden constructor payloads.
  when (valueMayContainNonDuplicable vi) $
    emitPayload "E_VAR_READ_DUPLICATES_LINEAR_VALUE" "kappa.var.mutable-binding" (mutableReadPayload vi path) sp
      ("a current-value read of mutable variable '" <> T.takeWhile (/= '#') (vKey vi)
         <> "' would duplicate a non-duplicable value stored in the cell (§12.2.6, §18.6.1)")
  -- A mutable current read is a duplication position: it produces an additional
  -- value but the cell retains the stored value.  It therefore must not count as
  -- a touch/consume that can satisfy the stored value's final drop obligation.
  pure Map.empty

currentReadUsage :: Env -> VInfo -> [Text] -> Span -> Analysis Usage
currentReadUsage env vi path sp = do
  u <- mutableReadUsage vi path sp
  pure $
    if eLatentCurrentReadEscape env
      then u `seqU` Map.singleton (refEscapeKey vi) (refEscapeUC sp)
      else u

mutableReadPayload :: VInfo -> [Text] -> Payload
mutableReadPayload vi path =
  foldl
    (\p (k, v) -> withPayloadField k v p)
    ( withPayloadField "sourceOperation" "current read" $
        withPayloadField "occurrence" "user-written" $
          withPayloadField "selectedFacet" "current-value" $
            withPayloadField "binding" binding $
              payloadKind "mutable-binding"
    )
    fields
  where
    binding = T.takeWhile (/= '#') (vKey vi)
    factPathText = if null path then "stored-value" else T.intercalate "." path
    fields =
      vMutableDiagFields vi
        ++ missingTypeFields
        ++ [ ("nonDuplicableFact", factPathText)
           , ("quantityFact", if null path then "non-duplicable stored value" else "non-duplicable path")
           ]
    hasField k = any ((== k) . fst) (vMutableDiagFields vi)
    missingTypeFields =
      maybe
        []
        ( \t ->
            [ ("storedValueType", t) | not (hasField "storedValueType") ]
              ++ [ ("hiddenReferenceType", "Ref " <> t) | not (hasField "hiddenReferenceType") ]
        )
        (vStoredTypeText vi)

-- ── Expression walk ──────────────────────────────────────────────────

walkE :: Env -> Expr -> Analysis WalkResult
walkE env e0 = case e0 of
  EVar n -> case Map.lookup (nameText n) (eVars env) of
    Just vi | vMutable vi -> mutableRead vi [] (nameSpan n)
    Just vi -> do
      u <- movePlace env vi [] (nameSpan n)
      pure (WalkResult u (vEscape vi (nameSpan n)) (vLatent vi))
    Nothing -> pure rNone
  EHole {} -> pure rNone
  EIntLit {} -> pure rNone
  EFloatLit {} -> pure rNone
  EStringLit _ parts _ -> walks [ipExpr p | p <- parts]
  EUnit {} -> pure rNone
  ETuple es _ -> walks es
  ERecordLit items _ -> walks [v | RecItem _ _ (Just v) <- items]
  EApp f args -> walkApp env f args
  EDot {}
    | Just (vi, path, sp) <- varPlaceOf env e0 ->
        mutableRead vi path sp
    | Just (vi, path, sp) <- placeOf env e0 ->
        if isLinearPath vi path
          then rPlain <$> movePlace env vi path sp
          else
            -- a non-linear field projection touches a disjoint path of
            -- the root, not the whole binding (§12.4)
            pure (rPlain (Map.singleton (vKey vi) touchUC))
  EDot b _ -> walkE env b
  EQDot b _ -> walkE env b
  ERecordPatch b items _ -> walkPatch env b items (exprSpan e0)
  ESectionLeft l _ sp -> latentOf env l sp
  ESectionRight _ r sp -> latentOf env r sp
  EOpRef {} -> pure rNone
  EElvis l r _ -> walks [l, r]
  ELambda _ bs body sp -> do
    -- §12.2.5: a leading lambda chain in a definition body claims the
    -- signature binders the equation head did not consume, so a binder
    -- written as `\x ->` still inherits the Pi quantity obligation.
    let aligned = alignParams bs (ePendingSig env)
    bound <- catMaybes <$> mapM (lamBind env) aligned
    -- only a directly-nested lambda (a curried `\x -> \y -> ...`)
    -- continues this definition's binder chain; any other body form
    -- ends it, so the remaining signature binders are dropped
    let restSig = case body of
          ELambda {} -> remainingSig bs (ePendingSig env)
          _ -> []
        env' = bindVars bound env {ePendingSig = restSig}
    r <- walkE env' {eLatentCurrentReadEscape = True} body
    let (u, t) = flatR r
    forM_ bound $ \(_, vi) -> closeVar vi u
    let u' = foldr (Map.delete . vKey . snd) u bound
    taintLatent env u' t sp
  ELet binds body _ -> do
    (segs, env') <- walkBinds env binds
    WalkResult u2 t l2 <- walkE env' body
    let bodyU = u2 `seqU` l2
        sufs = drop 1 (scanr seqU bodyU [u | (u, _, _) <- segs])
    -- each binding is checked against everything sequenced after it
    forM_ (zip segs sufs) $ \((_, bound, _), suf) ->
      forM_ bound $ \(_, vi) -> closeVar vi suf
    let allBound = concat [bound | (_, bound, _) <- segs]
        del u = foldr (Map.delete . vKey . snd) u allBound
        u1 = foldr (\(u, _, _) acc -> u `seqU` acc) Map.empty segs
    pure (WalkResult (u1 `seqU` del u2) t (del l2))
  EBlock decls mres _ -> do
    -- §9.3.1.1: collect scoped effect declarations (label ↦ op
    -- quantities) for the handler checks before walking the lets
    let env' = addEffDecls env decls
    binds <- declsToBinds [d | d <- decls, not (isEffDecl d)]
    walkE env' (ELet binds (fromMaybe (EUnit (exprSpan e0)) mres) (exprSpan e0))
  EDo _ items _ -> do
    fl <- walkItems env items
    let paths = flowPaths fl
        computeTaint = firstJust (maybeToList (fT fl) ++ mapMaybe (usageAnonBorrowIntro env) paths)
    pure (WalkResult (altUs paths) computeTaint Map.empty)
  EIf alts mels _ -> do
    condsU <- mapM (fmap (fst . flatR) . walkE env . fst) alts
    branches <- mapM (fmap flatR . walkE env . snd) alts
    melsR <- traverse (fmap flatR . walkE env) mels
    let bs = map fst branches ++ [maybe Map.empty fst melsR]
        taints = mapMaybe snd branches ++ catMaybes [snd =<< melsR]
    pure ((rPlain (foldr seqU (altUs bs) condsU)) {wrTaint = firstJust taints})
  EMatch scrut cases _ -> walkMatch env scrut cases
  ETry {} -> bailOut >> pure rNone
  ETryMatch {} -> bailOut >> pure rNone
  -- §18.1.21/.22 handler: the scrutinee is used once; each clause is an
  -- alternative path. The clause's resumption binder `k` is counted at
  -- the operation's declared resumption quantity (§18.1.16).
  EHandle _ _ scrut cases _ -> do
    r0 <- walkE env scrut
    let bindPats sp nms = mapM (\nm -> (\k -> (nm, plainV k sp)) <$> freshKey nm) nms
    crs <- forM cases $ \case
      HandlerReturn pat body sp -> do
        shadow <- bindPats sp (patVars pat)
        fst . flatR <$> walkE (bindVars shadow env) body
      HandlerOp _ argPats kN body sp -> do
        shadow <- bindPats sp (concatMap patVars argPats)
        kKey <- freshKey (nameText kN)
        let q = Map.findWithDefault QOne (nameSpan kN) (eHandlerOpQuantities env)
            kvi = (plainV kKey (nameSpan kN)) {vQ = countedQ q}
            env' = bindVars (shadow ++ [(nameText kN, kvi)]) env
        u <- fst . flatR <$> walkE env' body
        closeVar kvi u
        pure u
    pure (rPlain (fst (flatR r0) `seqU` altUs crs))
  EIs b _ -> walkE env b
  EThunk b sp -> suspend env b sp
  ELazy b sp -> suspend env b sp
  EForce b _ -> do
    r <- walkE env b
    let (u, t) = flatR r
    pure (WalkResult u t Map.empty)
  ESeal b _ _ -> walkE env b -- §13.2.10: hiding is not a consuming destructor
  EOpenExists {} -> bailOut >> pure rNone
  ESealExists {} -> bailOut >> pure rNone
  EListLit es _ -> walks es
  ESetLit es _ -> walks es
  EMapLit kvs _ -> walks (concatMap (\(k, v) -> [k, v]) kvs)
  EComprehension _ cls y _ -> walkComp env cls y (exprSpan e0)
  EArrow {} -> pure rNone -- type position: erased
  ERecordType {} -> pure rNone
  EForall {} -> pure rNone
  EExists {} -> pure rNone
  ETraitArrow {} -> pure rNone
  EEffRow {} -> pure rNone
  EVariant arms _ _ -> walks (map vaExpr arms)
  EOptionSugar {} -> pure rNone
  EAscription b _ _ -> walkE env b
  ECaptures b _ _ -> walkE env b
  ERefFacet n sp ->
    case Map.lookup (nameText n) (eVars env) of
      Just vi | vMutable vi ->
        -- The reference facet exposes the hidden cell. Direct recognized
        -- readRef/writeRef calls are handled before walking arguments. For
        -- other positions the produced Ref value carries a latent cell-lifetime
        -- escape: returning, storing, or passing it spends the latent usage, but
        -- a wildcard/discard does not.
        pure (WalkResult Map.empty Nothing (Map.singleton (refEscapeKey vi) (refEscapeUC sp)))
      _ -> pure rNone
  EVarRead n sp -> case Map.lookup (nameText n) (eVars env) of
    Just vi | vMutable vi -> rPlain <$> currentReadUsage env vi [] sp
    _ -> pure rNone
  EBang _ b _ -> walkE env b
  -- §21.2: a quote's object-level uses are charged when (and where) it
  -- is spliced, through the recorded expansion; the quote itself only
  -- captures meta-level syntax data
  EQuote {} -> pure rNone
  -- §23.2/§12.3.2: a code quote captures its payload's environment
  -- like a closure, so a borrowed capture escaping through the result
  -- is a borrow escape; '.~' operands are ordinary uses
  ECodeQuote body sp -> latentOf env body sp
  ECodeEscape body _ -> walkE env body
  ESpliceInQuote {} -> pure rNone
  EQuoteHole {} -> pure rNone
  ESplice _ sp -> case Map.lookup sp (eExpansions env) of
    Just ex -> walkE env ex
    Nothing -> bailOut >> pure rNone
  EImpossible {} -> pure rNone
  EKindQualified {} -> pure rNone
  EModuleSig {} -> pure rNone
  EQuotedLit {} -> pure rNone
  EReceiverSection _ args sp -> do
    rs <- mapM (walkE env) [e | ArgExplicit e <- args]
    let (u, t) = foldr (\r (au, at) -> let (u', t') = flatR r in (u' `seqU` au, firstJust (catMaybes [t', at]))) (Map.empty, Nothing) rs
    taintLatent env u t sp
  EOpChain {} -> bailOut >> pure rNone -- resolver output should not contain chains
  where
    mutableRead vi path sp = rPlain <$> currentReadUsage env vi path sp
    walks es = do
      rs <- mapM (walkE env) es
      let parts = map flatR rs
      pure ((rPlain (foldr (seqU . fst) Map.empty parts)) {wrTaint = firstJust (mapMaybe snd parts)})
    -- a delayed computation: its body usage becomes latent, and it is
    -- tainted when it captures an anonymous borrow (§12.3.2)
    suspend envS b sp = do
      r <- walkE envS {eLatentCurrentReadEscape = True} b
      let (u, t) = flatR r
      taintLatent envS u t sp
    -- shared by lambda/thunk/lazy/section formation
    taintLatent envS u t sp = do
      let anonKeys = [vKey vi | vi <- Map.elems (eVars envS), vAnonBorrow vi]
          captured = or [ucTouched c | (k, c) <- Map.toList u, k `elem` anonKeys]
      pure (WalkResult Map.empty (if captured || isJust t then Just sp else Nothing) u)
    latentOf envS operand sp = do
      r <- walkE envS {eLatentCurrentReadEscape = True} operand
      let (u, t) = flatR r
      taintLatent envS u t sp

firstJust :: [Span] -> Maybe Span
firstJust (s : _) = Just s
firstJust [] = Nothing

-- | The leftmost head variable of a (possibly nested/curried)
-- application head, used to classify application heads (e.g. a
-- data-constructor application). Skips intermediate application spines.
appHeadVar :: Env -> Expr -> Maybe Text
appHeadVar env = \case
  EVar n -> Just (nameText n)
  EDot base (DotName n)
    | Just prefix <- staticPathHead env base ->
        Just (prefix <> "." <> nameText n)
  EApp g _ -> appHeadVar env g
  EAscription e _ _ -> appHeadVar env e
  _ -> Nothing

staticPathHead :: Env -> Expr -> Maybe Text
staticPathHead env = \case
  EVar n
    | not (Map.member (nameText n) (eVars env)) -> Just (nameText n)
  EDot base (DotName n) -> (<> "." <> nameText n) <$> staticPathHead env base
  EAscription e _ _ -> staticPathHead env e
  _ -> Nothing

recognizedRefRead :: Env -> Expr -> [Arg] -> Maybe (Name, Span)
recognizedRefRead env _ args = do
  (n, sp) <- refReadFacetArg args
  if Map.lookup sp (eRecognizedRefOps env) == Just RefRead
    then Just (n, sp)
    else Nothing

recognizedRefWrite :: Env -> Expr -> [Arg] -> Maybe (Name, Expr, Span)
recognizedRefWrite env _ args = do
  (n, rhs, sp) <- refWriteFacetArgs args
  if Map.lookup sp (eRecognizedRefOps env) == Just RefWrite
    then Just (n, rhs, sp)
    else Nothing

recognizedRefReadExpr :: Env -> Expr -> Maybe (Name, Span)
recognizedRefReadExpr env = \case
  EApp f args -> recognizedRefRead env f args
  EAscription e _ _ -> recognizedRefReadExpr env e
  _ -> Nothing

walkExecutedExpr :: Env -> Expr -> Analysis WalkResult
walkExecutedExpr env e
  | Just (n, sp) <- recognizedRefReadExpr env e
  , Just vi <- Map.lookup (nameText n) (eVars env)
  , vMutable vi =
      rPlain <$> currentReadUsage env vi [] sp
walkExecutedExpr env e = walkE env e

refReadFacetArg :: [Arg] -> Maybe (Name, Span)
refReadFacetArg args =
  case explicitExprs args of
    [ERefFacet n sp] -> Just (n, sp)
    [EAscription (ERefFacet n sp) _ _] -> Just (n, sp)
    _ -> Nothing

refWriteFacetArgs :: [Arg] -> Maybe (Name, Expr, Span)
refWriteFacetArgs args =
  case explicitExprs args of
    [ERefFacet n sp, rhs] -> Just (n, rhs, sp)
    [EAscription (ERefFacet n sp) _ _, rhs] -> Just (n, rhs, sp)
    _ -> Nothing

explicitExprs :: [Arg] -> [Expr]
explicitExprs = mapMaybe $ \case
  ArgExplicit e -> Just e
  _ -> Nothing

-- | Comprehension usage (§20.10.5): each generator/join source is
-- evaluated exactly once for the pipeline, so a one-shot source place
-- is consumed once per comprehension. All other clause expressions run
-- once per row; demands on outer variables are scaled by the pipeline
-- cardinality, approximated as [0, ω]. Row binders introduced by
-- clause patterns are tracked separately by elaboration (§20.10.4) and
-- enter this analysis untracked.
walkComp :: Env -> [CompClause] -> CompYield -> Span -> Analysis WalkResult
walkComp env0 cls0 y sp = go env0 cls0 []
  where
    go env [] acc = do
      yu <- scaled env (case y of YieldExpr e -> [e]; YieldPair k v -> [k, v])
      pure (rPlain (foldr seqU yu acc))
    go env (c : rest) acc = case c of
      CFor _ _ pat src _ -> do
        su <- once env src
        env' <- bindPat env pat
        go env' rest (su : acc)
      CLet _ pat _ rhs _ -> do
        u <- scaled env [rhs]
        env' <- bindPat env pat
        go env' rest (u : acc)
      CIf e -> withScaled env rest acc [e]
      COrderBy ks _ -> withScaled env rest acc (map snd ks)
      CSkip e _ -> withScaled env rest acc [e]
      CTake e _ -> withScaled env rest acc [e]
      CDistinct me _ -> withScaled env rest acc (maybeToList me)
      CGroupBy k aggs n _ -> do
        u <- scaled env (k : concatMap (\(_, e, mu) -> e : maybeToList mu) aggs)
        env' <- bindName env n
        go env' rest (u : acc)
      CJoin _ pat src cond mInto _ -> do
        su <- once env src
        envP <- bindPat env pat
        cu <- scaled envP [cond]
        env' <- case mInto of
          Just n -> bindName env n
          Nothing -> pure envP
        go env' rest (su : cu : acc)
    withScaled env rest acc es = do
      u <- scaled env es
      go env rest (u : acc)
    once env src = fst . flatR <$> walkE env src
    scaled env es = do
      rs <- mapM (walkE env) es
      pure (scaleU (0, Nothing) (foldr (seqU . fst . flatR) Map.empty rs))
    bindPat env pat = do
      shadow <- forM (patVars pat) $ \nm -> do
        k <- freshKey nm
        pure (nm, plainV k sp)
      pure (bindVars shadow env)
    bindName env n = do
      k <- freshKey (nameText n)
      pure (bindVars [(nameText n, plainV k sp)] env)

-- ── Lambda binders and matches ───────────────────────────────────────

-- | Bind a lambda binder, merging in the quantity, borrow mark, and
-- type carried by an aligned signature Pi binder (§12.2.5) when the
-- lambda binder leaves them unstated. The lambda binder's own prefix
-- wins, exactly as 'paramBind' merges equation-head params.
lamBind :: Env -> (Binder, Maybe Binder) -> Analysis (Maybe (Text, VInfo))
lamBind env (b, ms) = case bName b of
  Nothing -> pure Nothing
  Just n -> do
    let BinderPrefix mq mb = bPrefix b
        BinderPrefix sq sb = maybe emptyPrefix bPrefix ms
        q = mq `orElse` sq
        mark = mb `orElse` sb
        ty = bType b `orElse` (bType =<< ms)
        pathFields = maybe [] (recordPathFields env) ty
        pathDeps = maybe [] (recordPathDeps env) ty
        fields = mergeFieldQuantities (maybe [] (resolveFields (eAliases env)) ty) (topFieldsFromPaths pathFields)
        deps = maybe [] (resolveDeps (eFieldDeps env)) ty
        -- §13.2.7: a consuming open-record lambda receiver owns its
        -- abstract residual tail, exactly as an equation-head receiver
        openTail
          | isNothing mark
          , q `elem` [Just QOne, Just QAtLeastOne]
          , Just rowVar <- (hasAbstractTail (eAliases env) =<< ty) =
              Just (rowVar, bSpan b)
          | otherwise = Nothing
    k <- freshKey (nameText n)
    pure
      ( Just
          ( nameText n
              , (plainV k (bSpan b))
                  { vQ = q
                  , vBorrowed = isJust mark
                  , vAnonBorrow = mark == Just (BorrowMark Nothing)
                  , vFields = fields
                  , vPathFields = pathFields
                  , vDeps = deps
                  , vPathDeps = pathDeps
                  , vOpenTail = openTail
                  }
          )
      )
  where
    orElse (Just x) _ = Just x
    orElse Nothing y = y

walkMatch :: Env -> Expr -> [MatchCase] -> Analysis WalkResult
walkMatch env scrut cases = do
  su <- fst . flatR <$> walkE env scrut
  let scrutV = case scrut of
        EVar n -> Map.lookup (nameText n) (eVars env)
        _ -> Nothing
  rs <- mapM (walkCase scrutV) [c | c@MatchCase {} <- cases]
  pure ((rPlain (su `seqU` altUs (map fst rs))) {wrTaint = firstJust (mapMaybe snd rs)})
  where
    walkCase scrutV (MatchCase pat mguard body csp) = do
      when (hasActive pat) bailOut
      checkRecordRest scrutV pat csp
      shadow <- forM (patBindings scrutV pat) $ \(nm, mq) -> do
        k <- freshKey nm
        pure (nm, (plainV k csp) {vQ = mq})
      let envC = bindVars shadow env
      gu <- maybe (pure Map.empty) (fmap (fst . flatR) . walkE envC) mguard
      r <- walkE envC body
      let (bu, t) = flatR r
      forM_ shadow $ \(_, vi) -> closeVar vi bu
      pure (gu `seqU` bu, t)
    walkCase _ (MatchImpossible _) = pure (Map.empty, Nothing)
    hasActive = \case
      PActive {} -> True
      PAs _ p -> hasActive p
      PCtor _ ps _ -> any hasActive ps
      PCtorNamed _ fs _ -> any hasActive [p | (_, Just p) <- fs]
      PTuple ps _ -> any hasActive ps
      PRecord fs _ _ -> any hasActive [p | (_, _, Just p) <- fs]
      PTyped p _ _ -> hasActive p
      POr ps _ -> any hasActive ps
      POpChain p chain _ -> hasActive p || any (hasActive . snd) chain
      _ -> False

-- | Pattern-bound names, with quantity-1 fields of a tracked record
-- scrutinee inherited by the bindings that receive them (§12.4).
patBindings :: Maybe VInfo -> Pattern -> [(Text, Maybe Quantity)]
patBindings scrutV pat = case (scrutV, pat) of
  (Just vi, PRecord fs rest _) ->
    concat
      [ case mp of
          Nothing -> [(fld, fieldPatternQuantity vi [fld])]
          Just (PVar x) -> [(nameText x, fieldPatternQuantity vi [fld])]
          Just p -> patBindings (Just (sliceVInfo vi [fld])) p
      | (_, f, mp) <- fs
      , let fld = nameText f
      ]
      ++ [ (nameText n, if any (`notElem` named fs) (linTopFields vi) then Just QOne else Nothing)
         | Just (PatRestBind n) <- [rest]
         ]
  _ -> map (\nm -> (nm, Nothing)) (patVars pat)
  where
    named fs = [nameText f | (_, f, _) <- fs]

patVars :: Pattern -> [Text]
patVars = \case
  PVar n -> [nameText n]
  PAs n p -> nameText n : patVars p
  PCtor _ ps _ -> concatMap patVars ps
  PCtorNamed _ fs _ -> concatMap patVars [p | (_, Just p) <- fs]
  PTuple ps _ -> concatMap patVars ps
  PRecord fs rest _ ->
    concatMap patVars [p | (_, _, Just p) <- fs]
      ++ [nameText f | (_, f, Nothing) <- fs]
      ++ [nameText n | Just (PatRestBind n) <- [rest]]
  PTyped p _ _ -> patVars p
  POr ps _ -> concatMap patVars ps
  POpChain p chain _ -> patVars p ++ concatMap (patVars . snd) chain
  PVariant mb _ _ mrest _ ->
    [nameText n | Just n <- [mb]] ++ [nameText n | Just n <- [mrest]]
  _ -> []

-- | A @..@ rest that silently discards a quantity-1 field of a tracked
-- record is a drop (§12.2.6, §12.4).
checkRecordRest :: Maybe VInfo -> Pattern -> Span -> Analysis ()
checkRecordRest (Just vi) (PRecord fs (Just PatRestDiscard) _) csp = do
  let named = [nameText f | (_, f, _) <- fs]
      missing = [f | f <- linTopFields vi, f `notElem` named]
  forM_ missing $ \f ->
    emit "E_QTT_LINEAR_DROP" "kappa.quantity.positive-lower-bound" csp
      ("the '..' rest pattern drops the quantity-1 field '" <> f <> "' (§12.2.6)")
  forM_ fs $ \(_, f, mp) ->
    forM_ mp $ \p ->
      checkRecordRest (Just (sliceVInfo vi [nameText f])) p csp
checkRecordRest (Just vi) (PRecord fs _ _) csp =
  forM_ fs $ \(_, f, mp) ->
    forM_ mp $ \p ->
      checkRecordRest (Just (sliceVInfo vi [nameText f])) p csp
checkRecordRest Nothing (PRecord fs _ _) csp =
  forM_ fs $ \(_, _, mp) ->
    forM_ mp $ \p ->
      checkRecordRest Nothing p csp
checkRecordRest _ _ _ = pure ()

-- ── Record patches (§12.4) ───────────────────────────────────────────

walkPatch :: Env -> Expr -> [PatchItem] -> Span -> Analysis WalkResult
walkPatch env base items sp = do
  vu <- walks (concatMap patchExprs items)
  bu <- case base of
    EVar n
      | Just vi <- Map.lookup (nameText n) (eVars env) -> do
          -- replacing patched paths conflicts with any live borrow of
            -- the record; the residue (and every moved-but-unpatched
            -- quantity-1 path) is consumed by the patch
            checkBorrowOverlap env vi [] sp
            pure $ patchRootUsage vi (concatMap patchPaths items) sp
    _ -> fst . flatR <$> walkE env base
  pure (rPlain (bu `seqU` vu))
  where
    patchExprs = \case
      PatchUpdate _ (PatchValue v) -> [v]
      PatchExtend _ v -> [v]
      PatchSection _ v -> [v]
      PatchPun _ -> []
    patchPaths = \case
      PatchUpdate path _ -> [[nameText n | (_, n) <- path] | not (null path)]
      PatchExtend n _ -> [[nameText n]]
      PatchSection {} -> []
      PatchPun n -> [[nameText n]]
    walks es = do
      rs <- mapM (walkE env) es
      pure (foldr (seqU . fst . flatR) Map.empty rs)

patchRootUsage :: VInfo -> [FieldPath] -> Span -> Usage
patchRootUsage vi patched sp =
  Map.fromList ((vKey vi <> ".~", oneUC sp) : (vKey vi, touchUC) : reconsumed)
  where
    reconsumed =
      [ (pathKey vi p, oneUC sp)
      | p <- linPaths vi
      , not (any (pathsOverlap p) patched)
      ]

-- ── Applications ─────────────────────────────────────────────────────

-- | Same-call facts for §12.4 disjointness: borrowed and consumed places.
data Fact
  = FBorrow !Text ![Text] !Span
  -- ^ a borrowed place footprint; the span is the §3.1.1A
  -- borrow-introduction site (the borrowing argument occurrence)
  | FMove !Text ![Text] !Span
  | FInout !Text ![Text] !Span
  -- ^ a '~'-marked inout argument's place footprint (§18.9.3)

applyExprVarInoutWrites :: Env -> Expr -> Env
applyExprVarInoutWrites env = \case
  EAscription e _ _ -> applyExprVarInoutWrites env e
  ECaptures e _ _ -> applyExprVarInoutWrites env e
  EApp f args ->
    foldl applyOne env (varInoutWriteBacks env f args)
  _ -> env
  where
    applyOne envc (nm, vi) = envc {eVars = Map.insert nm vi (eVars envc)}

applyStableExprVarInoutWrites :: Env -> Expr -> Analysis (Usage, [(Text, VInfo)], Env)
applyStableExprVarInoutWrites env = \case
  EAscription e _ _ -> applyStableExprVarInoutWrites env e
  ECaptures e _ _ -> applyStableExprVarInoutWrites env e
  EApp f args -> do
    foldM applyGroup (Map.empty, [], env) (stableInoutWriteBackGroups env f args)
  _ -> pure (Map.empty, [], env)
  where
    applyGroup (u, bound, envc) (nm, vi, targets) = do
      k <- freshKey nm
      let patched = [path | (path, _, _) <- targets]
          sp = case targets of
            ((_, _, targetSp) : _) -> targetSp
            [] -> vSpan vi
          refreshed =
            foldl
              (\acc (path, shape, targetSp) -> updateStableStoredShape envc acc path shape targetSp)
              vi
              targets
          newVi = refreshed {vKey = k, vSpan = sp}
          env' = envc {eVars = Map.insert nm newVi (eVars envc)}
      pure (u `seqU` patchRootUsage vi patched sp, bound ++ [(nm, newVi)], env')

varInoutWriteBacks :: Env -> Expr -> [Arg] -> [(Text, VInfo)]
varInoutWriteBacks env f args =
  case calleeDemandName env f of
    Nothing -> []
    Just callee ->
      let params = Map.findWithDefault [] callee (eFns env)
          resultShapes = Map.findWithDefault [] callee (eInoutResults env)
       in mapMaybe (writeBack resultShapes) (alignArgParams params args)
  where
    writeBack resultShapes = \case
      (ArgInout e sp, p)
        | pInout p
        , Just formal <- pName p
        , Just shape <- find ((== formal) . fsName) resultShapes
        , Just (vi, path, _) <- varInoutPlaceOf env e
        , Just (nm, _) <- find ((== vKey vi) . vKey . snd) (Map.toList (eVars env)) ->
            Just (nm, updateMutableStoredShape env vi path shape sp)
      _ -> Nothing

stableInoutWriteBackGroups :: Env -> Expr -> [Arg] -> [(Text, VInfo, [(FieldPath, FieldShape, Span)])]
stableInoutWriteBackGroups env f args =
  foldr insertGroup [] (stableInoutWriteBacks env f args)
  where
    insertGroup (nm, vi, path, shape, sp) [] = [(nm, vi, [(path, shape, sp)])]
    insertGroup wb@(nm, _vi, path, shape, sp) ((gnm, gvi, targets) : rest)
      | nm == gnm = (gnm, gvi, targets ++ [(path, shape, sp)]) : rest
      | otherwise = (gnm, gvi, targets) : insertGroup wb rest

stableInoutWriteBacks :: Env -> Expr -> [Arg] -> [(Text, VInfo, FieldPath, FieldShape, Span)]
stableInoutWriteBacks env f args =
  case calleeDemandName env f of
    Nothing -> []
    Just callee ->
      let params = Map.findWithDefault [] callee (eFns env)
          resultShapes = Map.findWithDefault [] callee (eInoutResults env)
       in mapMaybe (writeBack resultShapes) (alignArgParams params args)
  where
    writeBack resultShapes = \case
      (ArgInout e sp, p)
        | pInout p
        , Just formal <- pName p
        , Just shape <- find ((== formal) . fsName) resultShapes
        , Just (vi, path, _) <- stableInoutPlaceOf env e
        , Just (nm, _) <- find ((== vKey vi) . vKey . snd) (Map.toList (eVars env)) ->
            Just (nm, vi, path, shape, sp)
      _ -> Nothing

stableInoutPlaceOf :: Env -> Expr -> Maybe (VInfo, FieldPath, Span)
stableInoutPlaceOf env e =
  placeOf env e <|> case projPlacesOf env e of
    Just ([place], _) -> Just place
    _ -> Nothing

updateMutableStoredShape :: Env -> VInfo -> [Text] -> FieldShape -> Span -> VInfo
updateMutableStoredShape env vi path shape sp =
  vi
    { vQ = if null path then successorRootQ else vQ vi
    , vFields = if null path then fieldsFromType else vFields vi
    , vPathFields = mergePathQuantities keptPathFields newPathFields
    , vDeps =
        if null path
          then maybe [] (resolveDeps (eFieldDeps env)) (fsType shape)
          else vDeps vi
    , vPathDeps =
        if null path
          then tyPathDeps
          else mergePathDeps (vPathDeps vi) [(path ++ p, [path ++ d | d <- deps]) | (p, deps) <- tyPathDeps]
    , vNonDupFields = dedupPaths (keptNonDupFields ++ newNonDupFields)
    , vNonDupValue =
        if null path
          then successorNonDup && isNothing successorRootQ && null newNonDupFields && null newPathFields
          else vNonDupValue vi
    , vStoredTypeText =
        if null path
          then renderExprSrc <$> fsType shape
          else vStoredTypeText vi
    , vStoredTypeExpr =
        if null path
          then fsType shape
          else vStoredTypeExpr vi
    , vSpan = sp
    }
  where
    successorRootQ =
      if maybe False successorHasHiddenPositive (fsType shape)
        then Just QOne
        else Nothing
    successorNonDup =
      maybe False typeHasHiddenNonDuplicable (fsType shape)
    tyPathFields = maybe [] (recordPathFields env) (fsType shape)
    tyPathDeps = maybe [] (recordPathDeps env) (fsType shape)
    successorHasHiddenPositive ty =
      typeMayContainPositive env ty
        && not (any (positiveLowerQuantity . snd) tyPathFields)
    typeHasHiddenNonDuplicable ty =
      typeMayContainNonDuplicable env ty
        && not (any (nonDupQuantity . snd) tyPathFields)
    directPathFields =
      [ (path, q)
      | not (null path)
      , let q = successorRootQ
      , maybe False (\qv -> positiveLowerQuantity (Just qv) || nonDupQuantity (Just qv)) q
      ]
    fieldsFromType =
      mergeFieldQuantities
        (maybe [] (resolveFields (eAliases env)) (fsType shape))
        (topFieldsFromPaths tyPathFields)
    newPathFields =
      if null path
        then tyPathFields
        else mergePathQuantities directPathFields [(path ++ p, q) | (p, q) <- tyPathFields]
    newNonDupFields =
      dedupPaths $
        [path | not (null path), successorNonDup]
          ++ [path ++ p | (p, q) <- tyPathFields, nonDupQuantity q]
    keptPathFields =
      if null path
        then []
        else [(p, q) | (p, q) <- vPathFields vi, not (pathsOverlap p path)]
    keptNonDupFields =
      if null path
        then []
        else [p | p <- vNonDupFields vi, not (pathsOverlap p path)]

updateStableStoredShape :: Env -> VInfo -> [Text] -> FieldShape -> Span -> VInfo
updateStableStoredShape env vi path shape sp =
  let updated = updateMutableStoredShape env vi path shape sp
   in if null path
        then updated
        else updated {vQ = Nothing}

typeMayContainPositive :: Env -> Expr -> Bool
typeMayContainPositive = typeMayContainQuantity positiveLowerQuantity

typeMayContainNonDuplicable :: Env -> Expr -> Bool
typeMayContainNonDuplicable = typeMayContainQuantity nonDupQuantity

typeMayContainQuantity :: (Maybe Quantity -> Bool) -> Env -> Expr -> Bool
typeMayContainQuantity qPred env ty =
  case typeStorageQuantityWith (eRecordShapes env) (eCtors env) ty of
    Just q -> qPred (Just q)
    Nothing ->
      typeStorageFactsUnknown env ty
        && (qPred (Just QOne) || qPred (Just QAtMostOne))

typeStorageFactsUnknown :: Env -> Expr -> Bool
typeStorageFactsUnknown env = \case
  ERecordType {} -> False
  EAscription (EVar n) _ _
    | isLowerName (nameText n) -> False
  EAscription e _ _ -> typeStorageFactsUnknown env e
  ECaptures e _ _ -> typeStorageFactsUnknown env e
  EApp f _ -> typeStorageFactsUnknown env f
  ty
    | Just hd <- typePathHead ty ->
        not (knownDuplicableStorageHead env hd)
          && isNothing (shapeFieldsForType (eRecordShapes env) ty)
          && null
              [ ()
              | (k, _) <- Map.toList (eCtors env)
              , (hd <> ".") `T.isPrefixOf` k
              ]
  _ -> False

knownDuplicableStorageHead :: Env -> Text -> Bool
knownDuplicableStorageHead env hd =
  hd `Set.member` eDuplicableStorageHeads env || builtinSortHead hd
  where
    -- Universe spellings are parser/kernel syntax, not user-definable storage
    -- type constructors imported through a module scope.
    builtinSortHead t = t `elem` ["Type", "Type0", "Type1"]

walkApp :: Env -> Expr -> [Arg] -> Analysis WalkResult
walkApp env (EDot recv (DotName m)) args
  -- §7.4 method-call sugar: the receiver is one ordinary argument of
  -- the callee, demanded at its receiver-marked binder position
  | not (Map.member (nameText m) (eVars env))
  , Just params <- Map.lookup (nameText m) (eFns env)
  , (i : _) <- [ix | (ix, pp) <- zip [0 ..] params, pReceiver pp] =
      walkApp env (EVar m) (take i args ++ [ArgExplicit recv] ++ drop i args)
walkApp env f args
  -- a projection call in an ordinary value position is a non-consuming
  -- read of its yield leaves (§30.2.2.3 ReadProjector)
  | Just (places, aux) <- projPlacesOf env (EApp f args) = do
      rs <- mapM (walkE env) aux
      let u = foldr (seqU . fst . flatR) Map.empty rs
          touch = placesTouch places
      pure (rPlain (u `seqU` touch))
walkApp env f args = do
  hr <- walkE env f
  let (hu, _ht) = flatR hr -- an application calls its head exactly once
      params = maybe [] (\n -> Map.findWithDefault [] n (eFns env)) (calleeDemandName env f)
      liftLike = case appHeadVar env f of
        Just n -> maybe False buLiftLike (Map.lookup n builtinUsage)
        Nothing -> False
  rs <- forM (alignArgParams params args) $ \(arg, p) -> walkArg env params liftLike arg p
  -- §12.4: places borrowed and consumed by the same call must be disjoint
  let facts = concatMap snd rs
      borrowFacts = [(k, p, bsp) | FBorrow k p bsp <- facts]
      inouts = [(k, p, isp) | FInout k p isp <- facts]
      borrows = borrowFacts ++ inouts
  forM_ facts $ \case
    FMove k p msp
      | ((_, _, bsp) : _) <-
          [b | b@(bk, bp, _) <- borrows, bk == k, pathsOverlap bp p] ->
          -- §3.1.1A line 602: relate the same-call borrow-introduction
          -- site and the consuming occurrence.
          emitRel "E_QTT_BORROW_OVERLAP" "kappa.borrow.overlap" msp
            [ related RoleBorrowStart bsp "overlapping place borrowed by the same call here"
            , related RoleConsumedHere msp "consumed by the same call here"
            ]
            "a place is consumed by the same call that borrows an overlapping place (§12.4)"
    _ -> pure ()
  -- §18.9.3 / §3.3.4: a '~' footprint is an update footprint. It must be
  -- disjoint both from other '~' update footprints and from borrowed
  -- footprints in the same call, using dependency-expanded static footprints.
  let inoutBorrowPairs =
        [ (bsp, isp)
        | (k1, p1, isp) <- inouts
        , (k2, p2, bsp) <- borrowFacts
        , k1 == k2
        , pathsOverlap p1 p2
        ]
      overlapPairs =
        [ (isp1, isp2)
        | ((k1, p1, isp1), rest') <- zip inouts (drop 1 (tails inouts))
        , (k2, p2, isp2) <- rest'
        , k1 == k2
        , pathsOverlap p1 p2
        ]
  case inoutBorrowPairs of
    ((bsp, isp) : _) ->
      emitRel "E_QTT_BORROW_OVERLAP" "kappa.borrow.overlap" isp
        [ related RoleBorrowStart bsp "overlapping place borrowed by the same call here"
        , related RoleBorrowConflict isp "overlapping inout argument here"
        ]
        "an inout argument overlaps a borrowed place in the same call (§18.9.3, §12.4)"
    [] -> pure ()
  case overlapPairs of
    ((isp1, osp) : _) ->
      -- §3.1.1A line 602: both overlapping '~' footprints are
      -- borrow-introduction sites; relate the earlier one and the later.
      emitRel "E_QTT_BORROW_OVERLAP" "kappa.borrow.overlap" osp
        [ related RoleBorrowStart isp1 "place first borrowed by an inout argument here"
        , related RoleBorrowConflict osp "overlapping inout argument here"
        ]
        "two '~' inout arguments of the same call have overlapping place footprints (§18.9.3, §12.4)"
    [] -> pure ()
  -- A general callee neither stores nor returns its tainted
  -- callees/arguments, so the taint does not flow to its result.
  -- Two head families do carry an argument's taint into the result and
  -- so are taint-preserving:
  --   * result-carrying lifts (pure/ioPure/return), and
  --   * data-constructor application — the §12.3 escape rule lists
  --     "storing the value inside another data structure ... that would
  --     outlive rho" (Spec.md:11402) and §12.3.1 (Spec.md:11464-11470)
  --     notes a non-function value "may hide closures ... inside records,
  --     packages, or abstract data", with the anonymous-borrow region
  --     rejected by skolem escape. A constructor wraps its arguments into
  --     a value, so a borrow-capturing closure argument keeps its taint,
  --     exactly like the tuple/record-literal construction handled by
  --     'walks'. (Tuples and records already propagate via 'walks'.)
  let -- the head names a data constructor (looked up by ctor name, not a
      -- locally-bound variable shadowing it) — its application builds a
      -- value that holds the argument
      ctorLike = case appHeadVar env f of
        Just n -> not (Map.member n (eVars env)) && Map.member n (eCtors env)
        Nothing -> False
      taint
        | liftLike || ctorLike = firstJust (mapMaybe (wrTaint . fst) rs)
        | otherwise = Nothing
  pure ((rPlain (foldr (seqU . wrUsage . fst) hu rs)) {wrTaint = taint})

walkArg :: Env -> [PInfo] -> Bool -> Arg -> PInfo -> Analysis (WalkResult, [Fact])
walkArg env params resultCarried arg p = case arg of
  ArgImplicit _ -> pure (rNone, []) -- erased position (§12.2.1)
  ArgNamedBlock items _ -> do
    rs <- forM items $ \(n, me) -> do
      let np = fromMaybe defaultP (find ((== Just (nameText n)) . pName) params)
      walkArg env params resultCarried (ArgExplicit (fromMaybe (EVar n) me)) np
    let r = (rPlain (foldr (seqU . wrUsage . fst) Map.empty rs)) {wrTaint = firstJust (mapMaybe (wrTaint . fst) rs)}
    pure (r, concatMap snd rs)
  ArgInout e sp
    | pInout p -> inoutish e sp
    | otherwise -> do
        emit "E_QTT_INOUT_MARKER_UNEXPECTED" "kappa-hs.qtt.inout-marker" sp
          "call-site '~' marker on an argument whose parameter is not declared inout (§18.9.3)"
        (,[]) <$> walkE env e
  ArgExplicit e
    | pInout p -> do
        emit "E_QTT_INOUT_MARKER_REQUIRED" "kappa-hs.qtt.inout-marker" (exprSpan e)
          "this argument flows into an inout parameter and must be marked '~place' (§18.9.3)"
        (,[]) <$> walkE env e
    | pQuantity p == Just QZero -> pure (rNone, []) -- erased argument
    | pBorrow p -> borrowish e
    -- a projection call argument touches its yield leaves: a move per
    -- leaf under a consuming parameter (§30.2.2.3 MoveProjector), a
    -- call-scoped borrow otherwise (ReadProjector)
    | consuming
    , Just (places, aux) <- projPlacesOf env e -> do
        rs <- mapM (walkE env) aux
        us <- mapM (\(vi, path, psp) -> movePlace env vi path psp) places
        let u = foldr seqU (foldr (seqU . fst . flatR) Map.empty rs) us
        pure
          ( rPlain u
          , [ FMove k fp fsp
            | pl@(_, _, psp) <- places
            , (k, fp, fsp) <- placeFootprintLocks env pl psp
            ]
          )
    | Just (places, aux) <- projPlacesOf env e -> do
        rs <- mapM (walkE env) aux
        let u = foldr (seqU . fst . flatR) Map.empty rs
            touch = placesTouch places
        pure
          ( rPlain (u `seqU` touch)
          , [ FBorrow k fp fsp
            | pl@(_, _, psp) <- places
            , (k, fp, fsp) <- placeFootprintLocks env pl psp
            ]
          )
    | consuming
    , Just (vi, [], sp) <- placeOf env e
    , vBorrowed vi -> do
        case vEscape vi sp of
          Just tsp | resultCarried ->
            pure (WalkResult (Map.singleton (vKey vi) touchUC) (Just tsp) Map.empty, [])
          _ -> do
            -- §3.1.1A line 602: relate the borrow-introduction site (the
            -- borrowed binding's binder) and the failing consuming use.
            emitRel "E_QTT_BORROW_CONSUME" "kappa.quantity.unsatisfied" sp
              [ related RoleBorrowStart (vSpan vi) "borrowed binding introduced here"
              , related RoleConsumedHere sp "consumed by a quantity-1 parameter here"
              ]
              ("borrowed binding '" <> T.takeWhile (/= '#') (vKey vi) <> "' cannot be consumed by a quantity-1 parameter (§12.3.1)")
            pure (rPlain (Map.singleton (vKey vi) touchUC), [])
    -- a direct place argument is counted at the parameter's demand
    -- interval (§12.2.2); a definite consume is a move fact (§12.4)
    | Just (vi, path, sp) <- placeOf env e
    , null path || isLinearPath vi path -> do
        let d = pDemand p
            escapeT = vEscape vi sp
        u <-
          if fst d >= 1
            then movePlace env vi path sp
            else pure (placeUse vi path sp)
        let latent = scaleU d (vLatent vi)
        checkCaptureBound p escapeT sp
        -- a tainted closure binding may flow only into an at-most-once
        -- consuming position, like a directly written closure (§12.3.2)
        case escapeT of
          Just tsp
            | pKnown p
            , pEscapingParam p
            , pCaptureBound p == CapAny
            , pQuantity p `notElem` [Just QOne, Just QAtMostOne] ->
                -- §3.1.1A: cite the borrow-capturing closure formation
                -- site (primary) and the escape site where it flows out.
                emitRel "E_QTT_BORROW_ESCAPE" "kappa.borrow.escape" tsp
                  [ related RoleBorrowStart tsp "borrow-capturing closure formed here"
                  , related RoleBorrowEscapeSite sp "escapes into an unrestricted parameter here"
                  ]
                  "a closure capturing a borrowed binding flows into an unrestricted parameter (§12.3.2)"
          _ -> pure ()
        pure
          ( WalkResult (scaleU d u `seqU` latent) escapeT Map.empty
          , [ FMove k fp msp
            | fst d >= 1
            , (k, fp, msp) <- placeFootprintLocks env (vi, path, sp) sp
            ]
          )
    -- a definite consume of a deeper (non-linear) path still conflicts
    -- with a live borrow of an overlapping path (§12.4)
    | consuming
    , Just (vi, path, sp) <- placeOf env e -> do
        checkBorrowOverlap env vi path sp
        pure
          ( rPlain (Map.singleton (vKey vi) touchUC)
          , [FMove k fp msp | (k, fp, msp) <- placeFootprintLocks env (vi, path, sp) sp]
          )
    | otherwise -> do
        WalkResult u t l <- walkE env e
        checkCaptureBound p t (exprSpan e)
        let d = pDemand p
            -- §16.2.1/§13.2.7: a composite argument value (e.g. a record
            -- literal carrying a linear field) is demanded at the
            -- parameter's interval, so any linear value embedded in its
            -- construction is counted that many times — passing a record
            -- holding a linear field to an unrestricted receiver then
            -- fails the linear upper bound, exactly as a direct place
            -- argument already does.
            u' = scaleU d u
            l' = if refFacetValue e then l else scaleU d l
        -- a borrow-capturing closure may flow only into an
        -- at-most-once consuming position (§12.3.2); an unrestricted
        -- parameter may retain it beyond the borrow's scope
        case t of
          Just tsp
            | pKnown p
            , pEscapingParam p
            , pCaptureBound p == CapAny
            , pQuantity p `notElem` [Just QOne, Just QAtMostOne] -> do
                -- §3.1.1A (line 602-603): cite the borrow-capturing
                -- closure formation site carried by the composite value's
                -- taint (RoleBorrowStart) and the escape site where that
                -- composite argument flows into the unrestricted parameter
                -- (RoleBorrowEscapeSite).
                emitRel "E_QTT_BORROW_ESCAPE" "kappa.borrow.escape" tsp
                  [ related RoleBorrowStart tsp "borrow-capturing closure formed here"
                  , related RoleBorrowEscapeSite (exprSpan e) "flows into an unrestricted parameter here"
                  ]
                  "a closure capturing a borrowed binding flows into an unrestricted parameter (§12.3.2)"
                pure (rPlain (u' `seqU` l'), [])
          _ -> pure (WalkResult (u' `seqU` l') t Map.empty, [])
  where
    consuming = pQuantity p `elem` [Just QOne, Just QAtLeastOne]
    placeUse vi path sp =
      case path of
        [] -> Map.singleton (vKey vi) (oneUC sp)
        fs ->
          Map.fromList
            [ (vKey vi <> "." <> T.intercalate "." fs, oneUC sp)
            , (vKey vi, touchUC)
            ]
    borrowish e = case placeOf env e of
      Just (vi, path, sp) ->
          pure
            ( rPlain (placeBorrow vi path sp)
            , [FBorrow k fp bsp | (k, fp, bsp) <- placeFootprintLocks env (vi, path, sp) sp]
            )
      Nothing
        -- a projection call in borrow demand borrows every yield leaf
        -- for the call (§30.2.2.3 BorrowProjector)
        | Just (places, aux) <- projPlacesOf env e -> do
            rs <- mapM (walkE env) aux
            let u = foldr (seqU . fst . flatR) Map.empty rs
                touch = placesTouch places
            pure
              ( rPlain (u `seqU` touch)
              , [ FBorrow k fp bsp
                | pl@(_, _, psp) <- places
                , (k, fp, bsp) <- placeFootprintLocks env pl psp
                ]
              )
        | otherwise -> (,[]) <$> walkE env e
    -- like 'borrowish', but the facts carry the marker span for the
    -- §18.9.3 pairwise-disjointness check of one call's '~' arguments
    inoutish e isp =
      case placeOf env e of
        Just (vi, path, sp) -> do
          checkBorrowOverlap env vi path isp
          pure
            ( rPlain (placeBorrow vi path sp)
            , [FInout k fp isp | (k, fp, _) <- placeFootprintLocks env (vi, path, sp) isp]
            )
        Nothing -> case varPlaceOf env e of
          Just (vi, path, _) -> do
            checkBorrowOverlap env vi path isp
            pure
              ( rPlain Map.empty
              , [FInout k fp isp | (k, fp, _) <- placeFootprintLocks env (vi, path, isp) isp]
              )
          Nothing -> case projPlacesOf env e of
            Just (places, aux) -> do
              forM_ places $ \(vi, path, _) -> checkBorrowOverlap env vi path isp
              rs <- mapM (walkE env) aux
              let u = foldr (seqU . fst . flatR) (placesTouch places) rs
              pure
                ( rPlain u
                , [ FInout k fp isp
                  | pl <- places
                  , (k, fp, _) <- placeFootprintLocks env pl isp
                  ]
                )
            Nothing -> case projVarPlacesOf env e of
              Just (places, aux) -> do
                forM_ places $ \(vi, path, _) -> checkBorrowOverlap env vi path isp
                rs <- mapM (walkE env) aux
                let u = foldr (seqU . fst . flatR) Map.empty rs
                pure
                  ( rPlain u
                  , [ FInout k fp isp
                    | pl <- places
                    , (k, fp, _) <- placeFootprintLocks env pl isp
                    ]
                  )
              Nothing -> do
                (r, fs) <- borrowish e
                pure (r, [FInout k path isp | FBorrow k path _ <- fs])

alignArgParams :: [PInfo] -> [Arg] -> [(Arg, PInfo)]
alignArgParams params0 = go params0
  where
    go _ [] = []
    go ps (arg : rest) = case arg of
      ArgImplicit _ -> (arg, defaultP) : go ps rest
      ArgNamedBlock {} -> (arg, defaultP) : go ps rest
      ArgExplicit {} -> consume arg ps rest
      ArgInout {} -> consume arg ps rest
    consume arg ps rest = case ps of
      p : ps' -> (arg, p) : go ps' rest
      [] -> (arg, defaultP) : go [] rest

checkCaptureBound :: PInfo -> Maybe Span -> Span -> Analysis ()
checkCaptureBound p mt escapeSp =
  case (pCaptureBound p, mt) of
    (CapClosed, Just introSp) ->
      emitRel "E_QTT_BORROW_ESCAPE" "kappa.borrow.escape" escapeSp
        [ related RoleBorrowStart introSp "borrowed region captured here"
        , related RoleBorrowEscapeSite escapeSp (escapeSiteLabel (pEscapeKind p))
        ]
        (escapeMessage (pEscapeKind p))
    _ -> pure ()

escapeSiteLabel :: EscapeKind -> Text
escapeSiteLabel = \case
  EscapeFork -> "captured by a forked computation here"
  EscapeForkDaemon -> "captured by a daemon fiber computation here"
  EscapeForkIn -> "captured by a scoped fiber computation here"
  EscapeOrdinaryParam -> "flows into a closed-capture parameter here"

escapeMessage :: EscapeKind -> Text
escapeMessage = \case
  EscapeFork -> "a forked computation must be closed over local borrow regions (§18.1.4)"
  EscapeForkDaemon -> "a daemon fiber computation must be closed over local borrow regions (§18.1.4)"
  EscapeForkIn -> "a scoped fiber computation must be closed over local borrow regions unless the scope is region-indexed (§18.1.4)"
  EscapeOrdinaryParam -> "this argument's hidden capture environment is not allowed by a closed captures() parameter (§12.3.1)"

usageAnonBorrowIntro :: Env -> Usage -> Maybe Span
usageAnonBorrowIntro env u =
  firstJust
    [ vSpan vi
    | vi <- Map.elems (eVars env)
    , vAnonBorrow vi
    , any (touches vi) (Map.toList u)
    ]
  where
    touches vi (k, c) = ucTouched c && (k == vKey vi || (vKey vi <> ".") `T.isPrefixOf` k)

calleeDemandName :: Env -> Expr -> Maybe Text
calleeDemandName env = \case
  e | Just headKey <- staticPathHead env e -> Just headKey
  EApp f _ -> calleeDemandName env f
  EAscription e _ _ -> calleeDemandName env e
  _ -> Nothing

calleeStorageInfo :: Env -> Expr -> Maybe VInfo
calleeStorageInfo env f = do
  n <- appHeadVar env f
  guardNotLocal n
  Map.lookup n (eResultStorage env)
  where
    guardNotLocal n =
      if Map.member n (eVars env)
        then Nothing
        else Just ()

coreFnParams :: Term -> [PInfo]
coreFnParams = \case
  Core.CPi Core.Expl q brw nm _ body -> coreP nm q brw : coreFnParams body
  Core.CPi Core.Impl _ _ _ _ body -> coreFnParams body
  _ -> []
  where
    coreP nm q brw = defaultP {pName = Just nm, pQuantity = coreQuantity q, pBorrow = brw, pKnown = True}
    coreQuantity = \case
      Core.Q0 -> Just QZero
      Core.Q1 -> Just QOne
      Core.QW -> Just QOmega
      Core.QLe1 -> Just QAtMostOne
      Core.QGe1 -> Just QAtLeastOne

-- ── Bindings and do items ────────────────────────────────────────────

-- | Walk a let-group's right-hand sides; returns one segment per
-- binding (its RHS usage, the tracked bindings it introduces, and the
-- borrows it opens) plus the fully-extended environment.
walkBinds :: Env -> [LetBind] -> Analysis ([(Usage, [(Text, VInfo)], [(Text, [Text], Span)])], Env)
walkBinds = walkBindsWith walkE

walkBindsWith :: (Env -> Expr -> Analysis WalkResult) -> Env -> [LetBind] -> Analysis ([(Usage, [(Text, VInfo)], [(Text, [Text], Span)])], Env)
walkBindsWith walkRhs env binds = go env binds
  where
    bindsWholeRhs = \case
      PVar {} -> True
      PTyped p _ _ -> bindsWholeRhs p
      _ -> False
    go envc [] = pure ([], envc)
    go envc (LetBind _ prefix pat mty rhs bsp : rest) = do
      let BinderPrefix mq mb = prefix
          borrowed = isJust mb
          anon = mb == Just (BorrowMark Nothing)
          place = placeOf envc rhs
      (u, taint, latent, brs) <-
        if borrowed
          then case place of
            -- `let & v = p.f` opens a lexical borrow of the place: a
            -- non-consuming read that locks overlapping paths (§12.4,
            -- §13.2.1: plus the fields a dependent field's type
            -- mentions); borrowing through a borrowed alias locks the
            -- original
            Just pl@(vi, plPath, plSp) ->
              pure
                ( placeBorrow vi plPath plSp
                , Nothing
                , Map.empty
                , -- §3.1.1A: the borrow-introduction site is the @let &@
                  -- binding span; carry it on every lock this borrow opens
                  [(rk, fp, bsp) | (rk, fp, _) <- borrowLocks envc pl]
                )
            -- `let & v = proj places` locks every yield leaf for the
            -- binder's scope (§30.2.2.3 BorrowProjector)
            Nothing
              | Just (places, aux) <- projPlacesOf envc rhs -> do
                  rs <- mapM (walkE envc) aux
                  -- borrowing a place touches the root and, for a linear
                  -- field path, that field path too, so the §13.2.1
                  -- field obligation is discharged for the borrow's scope
                  let u' = foldr (seqU . fst . flatR) (placesTouch places) rs
                  pure
                    ( u'
                    , Nothing
                    , Map.empty
                    , -- §3.1.1A: introduction site is this @let &@ binding
                      [ (rk, fp, bsp)
                      | (rk, fp, _) <- concatMap (borrowLocks envc) places
                      ]
                    )
            Nothing -> do
              r <- walkRhs envc rhs
              let (u', t') = flatR r
              pure (u', t', Map.empty, [])
          else case (pat, rhs) of
            -- §12.2.6: a wildcard discard of a bare binding (`let _ = t`, also
            -- the surface `let _ = t` which parses as a `_`-named binder) is
            -- NOT a use and never discharges a positive lower bound — accepting
            -- it would be a generic discard for all linear values, so the bound
            -- value is left unconsumed and reported dropped.
            (p, EVar n)
              | isWildBinder p, Map.member (nameText n) (eVars envc) ->
                  pure (Map.empty, Nothing, Map.empty, [])
            _ -> do
              WalkResult u' t' l' <- walkRhs envc rhs
              let forceRefEscape =
                    bindsWholeRhs pat
                      && not (isWildBinder pat)
                      && refFacetValue rhs
              pure
                ( if forceRefEscape then u' `seqU` l' else u'
                , t'
                , if forceRefEscape then Map.empty else l'
                , []
                )
      let names = patVars pat
          single = length names == 1
          -- a binding receiving a quantity-1 field projection inherits the
          -- field's linearity (§12.4); a binding that ALIASES a bare must-use
          -- binding (`let x = t` with `t` of quantity `1`/`>=1`) inherits that
          -- quantity, so dropping the alias is caught (§12.2.6 — otherwise the
          -- move would silently launder the obligation).
          inherited = case place of
            Just (vi, path, _)
              | not borrowed, isLinearPath vi path -> Just QOne
              | not borrowed, null path, not (isWildBinder pat)
              , Just inheritedQ <- vQ vi, inheritedQ `elem` [QOne, QAtLeastOne] -> Just inheritedQ
            _ -> Nothing
          q = if single then mq `orElse` inherited else Nothing
          -- §13.2.1: a record literal that places a linear value into a
          -- field makes that field a linear path of the resulting record,
          -- whether or not the binding is annotated. The whole record is
          -- then a linear resource until those paths are consumed
          -- (enforced in 'closeVar').
          litFields
            | borrowed = []
            | otherwise = litLinearFields envc rhs
          fields =
            mergeFieldQuantities
              (maybe [] (resolveFields (eAliases envc)) mty)
              litFields
          annotatedPathFields = maybe [] (recordPathFields envc) mty
          fdeps = maybe [] (resolveDeps (eFieldDeps envc)) mty
          annotatedPathDeps = maybe [] (recordPathDeps envc) mty
          wholeRhsBinder = bindsWholeRhs pat
          mk nm = do
            k <- freshKey nm
            let storedInfo
                  | wholeRhsBinder, not borrowed, not (isWildBinder pat) = Just (storedValueInfo envc k bsp rhs)
                  | otherwise = Nothing
                q' = q `orElse` (storedInfo >>= vQ)
                pathFields' = maybe annotatedPathFields (mergePathQuantities annotatedPathFields . vPathFields) storedInfo
                pathDeps' = maybe annotatedPathDeps (mergePathDeps annotatedPathDeps . vPathDeps) storedInfo
                fields' =
                  maybe
                    (mergeFieldQuantities fields (topFieldsFromPaths pathFields'))
                    (mergeFieldQuantities fields . vFields)
                    storedInfo
                nonDupValue' = maybe False vNonDupValue storedInfo
                nonDupFields' = maybe [] vNonDupFields storedInfo
                openTail' = storedInfo >>= vOpenTail
            pure
              ( nm
              , (plainV k bsp)
                  { vQ = q'
                  , vBorrowed = borrowed
                  , vAnonBorrow = anon
                  , vTaint = if single then taint else Nothing
                  , vLatent = if single then latent else Map.empty
                  , vFields = fields'
                  , vPathFields = pathFields'
                  , vPathDeps = pathDeps'
                  , vNonDupValue = nonDupValue'
                  , vNonDupFields = nonDupFields'
                  , vDeps = fdeps
                  , vOpenTail = openTail'
                  }
              )
      -- every pattern name is bound (untracked entries still shadow
      -- outer bindings); only prefixed/tainted ones carry checks
      bound <- mapM mk names
      -- a borrowed binding of a place is a place alias for §12.4 locks;
      -- a binding of a (partial) projection application is a descriptor
      let aliasEntries =
            [ (vKey vi, (rk, fp))
            | borrowed
            , Just pl <- [place]
            , let (rk, fp, _) = resolveBorrowAlias envc pl
            , (_, vi) <- bound
            ]
          descEntries =
            [ (nm, du)
            | not borrowed
            , [nm] <- [names]
            , Just du <- [descOf envc rhs]
            ]
      (restoreU, restored, envStable) <- applyStableExprVarInoutWrites envc rhs
      let envAfterRhs = applyExprVarInoutWrites envStable rhs
          envb0 = bindVars bound envAfterRhs
          envb =
            envb0
              { eDescs = foldr (uncurry Map.insert) (eDescs envb0) descEntries
              , eBorrowAliases = foldr (uncurry Map.insert) (eBorrowAliases envb0) aliasEntries
              }
      (segs, env') <- go (addBorrows brs envb) rest
      pure ((u `seqU` restoreU, restored ++ bound, brs) : segs, env')
    orElse (Just x) _ = Just x
    orElse Nothing y = y

-- | Record a block's scoped effect declarations: label spelling ↦
-- operation names with declared resumption quantities (default 1,
-- §18.1.17).
addEffDecls :: Env -> [Decl] -> Env
addEffDecls env decls =
  env {eEffOps = foldr (uncurry Map.insert) (eEffOps env) effs}
  where
    effs =
      [ ( nameText (effName ed)
        , [(nameText (eoName o), fromMaybe QOne (eoQuantity o)) | o <- effOps ed]
        )
      | DEffect _ ed _ <- decls
      , not (effIsLabelDecl ed)
      ]

isEffDecl :: Decl -> Bool
isEffDecl = \case
  DEffect {} -> True
  _ -> False

-- | The counted quantity of a resumption binder: ω resumption values
-- are unrestricted (their soundness is the §18.1.20 capture rule), and
-- a one-shot resumption may be abandoned without use — the clause then
-- abandons the captured segment (§18.1.21, §32.2.20) — so the declared
-- quantity 1 counts as at-most-once.
countedQ :: Quantity -> Maybe Quantity
countedQ = \case
  QOmega -> Nothing
  QTerm {} -> Nothing
  QOne -> Just QAtMostOne
  q -> Just q

-- | Is this right-hand side an invocation of a resolved effect operation whose
-- checker-selected operation metadata permits multi-shot resumption
-- (§18.1.17)? Returns the operation's span and name for diagnostics.
multishotOpCall :: Env -> Expr -> Maybe (Span, Text)
multishotOpCall env = listToMaybe . multishotOpsInExecutedExpr env

multishotOpsInExecutedExpr :: Env -> Expr -> [(Span, Text)]
multishotOpsInExecutedExpr env = go
  where
    hit sp = [(sp, op) | Just op <- [Map.lookup sp (eRecognizedMultishotOps env)]]
    hitMember = \case
      DotName op -> hit (nameSpan op)
      DotOperator op -> hit (nameSpan op)
    goArg = \case
      ArgExplicit e -> go e
      ArgImplicit e -> go e
      ArgInout e _ -> go e
      ArgNamedBlock fields _ -> concatMap (maybe [] go . snd) fields
    goLet (LetBind _ _ _ _ rhs _) = go rhs
    goCase = \case
      MatchCase _ mg body _ -> maybe [] go mg ++ go body
      MatchImpossible {} -> []
    goExcept (ExceptCase _ mg body _) = maybe [] go mg ++ go body
    goHandler = \case
      HandlerReturn _ body _ -> go body
      HandlerOp _ _ _ body _ -> go body
    goDecl = \case
      DLet _ ld _ -> go (ldBody ld)
      DTopSplice e _ -> go e
      DUnsafeAssert _ inner _ -> goDecl inner
      _ -> []
    goDo = \case
      DoBind lb -> go (lbExpr lb)
      DoLet lb -> go (lbExpr lb)
      DoLetQ _ rhs mElse _ -> go rhs ++ maybe [] (go . snd) mElse
      DoVar _ mty rhs _ -> maybe [] go mty ++ go rhs
      DoAssign _ True rhs _ -> go rhs
      DoAssign _ False rhs _ -> go rhs
      DoExpr e -> go e
      DoUsing _ _ rhs _ -> go rhs
      DoDefer {} -> []
      DoReturn _ me _ -> maybe [] go me
      DoBreak {} -> []
      DoContinue {} -> []
      DoWhile _ cond body mels _ -> go cond ++ concatMap goDo body ++ maybe [] (concatMap goDo) mels
      DoFor _ _ src body mels _ -> go src ++ concatMap goDo body ++ maybe [] (concatMap goDo) mels
      DoIf alts mels _ ->
        concatMap (\(cond, body) -> go cond ++ concatMap goDo body) alts
          ++ maybe [] (concatMap goDo) mels
      DoDecl d -> goDecl d
    goCompClause = \case
      CFor _ _ _ src _ -> go src
      CLet _ _ mty rhs _ -> maybe [] go mty ++ go rhs
      CIf e -> go e
      COrderBy keys _ -> concatMap (go . snd) keys
      CSkip e _ -> go e
      CTake e _ -> go e
      CDistinct me _ -> maybe [] go me
      CGroupBy key aggs _ _ -> go key ++ concatMap (\(_, e, mu) -> go e ++ maybe [] go mu) aggs
      CJoin _ _ src on _ _ -> go src ++ go on
    goYield = \case
      YieldExpr e -> go e
      YieldPair k v -> go k ++ go v
    go = \case
      EVar {} -> []
      ERefFacet {} -> []
      EVarRead {} -> []
      EHole {} -> []
      EIntLit {} -> []
      EFloatLit {} -> []
      EStringLit _ parts _ -> concatMap (go . ipExpr) parts
      EQuotedLit {} -> []
      EUnit {} -> []
      ETuple es _ -> concatMap go es
      ERecordLit items _ -> concatMap (\(RecItem _ _ mv) -> maybe [] go mv) items
      ERecordType {} -> []
      eApp@(EApp f args) -> hit (exprSpan eApp) ++ go f ++ concatMap goArg args
      EDot recv member -> hitMember member ++ go recv
      EQDot recv member -> hitMember member ++ go recv
      ERecordPatch recv items _ -> go recv ++ concatMap goPatch items
      EReceiverSection _ args _ -> concatMap goArg args
      ESectionLeft e _ _ -> go e
      ESectionRight _ e _ -> go e
      EOpRef {} -> []
      EOpChain elems -> concatMap goOpElem elems
      EElvis a b _ -> go a ++ go b
      ELambda {} -> []
      ELet binds body _ -> concatMap goLet binds ++ go body
      EBlock decls mres _ -> concatMap goDecl decls ++ maybe [] go mres
      EDo _ items _ -> concatMap goDo items
      EIf alts mels _ -> concatMap (\(c, b) -> go c ++ go b) alts ++ maybe [] go mels
      EMatch scrut cases _ -> go scrut ++ concatMap goCase cases
      ETry scrut excepts mfin _ -> go scrut ++ concatMap goExcept excepts ++ maybe [] go mfin
      ETryMatch scrut cases excepts mfin _ ->
        go scrut ++ concatMap goCase cases ++ concatMap goExcept excepts ++ maybe [] go mfin
      EHandle _ lbl scrut cases _ -> go lbl ++ go scrut ++ concatMap goHandler cases
      EIs e _ -> go e
      EThunk {} -> []
      ELazy {} -> []
      EForce e _ -> go e
      ESeal a b _ -> go a ++ go b
      EOpenExists e _ _ body _ -> go e ++ go body
      ESealExists bs a b _ -> concatMap (go . snd) bs ++ go a ++ go b
      EListLit es _ -> concatMap go es
      ESetLit es _ -> concatMap go es
      EMapLit kvs _ -> concatMap (\(k, v) -> go k ++ go v) kvs
      EComprehension _ clauses yield _ -> concatMap goCompClause clauses ++ goYield yield
      EArrow {} -> []
      EForall {} -> []
      EExists {} -> []
      ETraitArrow {} -> []
      EEffRow {} -> []
      EVariant arms mtail _ -> concatMap (\(VariantArm e mty) -> go e ++ maybe [] go mty) arms ++ maybe [] go mtail
      EOptionSugar {} -> []
      EAscription e _ _ -> go e
      ECaptures e _ _ -> go e
      EBang _ e _ -> go e
      EQuote {} -> []
      ECodeQuote {} -> []
      ECodeEscape e _ -> go e
      ESplice e _ -> go e
      ESpliceInQuote {} -> []
      EQuoteHole {} -> []
      EImpossible {} -> []
      EKindQualified {} -> []
      EModuleSig {} -> []
    goPatch = \case
      PatchUpdate _ (PatchValue e) -> go e
      PatchExtend _ e -> go e
      PatchSection a b -> go a ++ go b
      PatchPun {} -> []
    goOpElem = \case
      ChainOperand e -> go e
      ChainOp {} -> []

-- | §4b tail-resumptive detector — the dual of 'multishotOpCall'.
--
-- A handler operation clause @case op x₁ … xₙ k -> body@ is
-- /tail-resumptive/ (§32.2.15, Koka's overwhelmingly common handler
-- shape) iff its resumption binder @k@ is invoked exactly once, in tail
-- position, applied to a single explicit value — i.e. the clause's tail
-- is @resume v@ (surface @k v@) and @k@ occurs nowhere else. For such a
-- clause the op-site→handler segment is never abandoned and is resumed
-- in place, so the runtime may skip severing the @Cont@ sub-chain,
-- heap-boxing the resumption, and re-pushing the handler on resume — the
-- whole point of Stage 4b (constant @Cont@ depth over an effectful loop).
--
-- HONESTY / soundness (the §34.3.9 invariant: never optimize merely
-- because local control is a jump): this is deliberately conservative —
-- a clause is reported tail-resumptive ONLY when it is provably so by
-- this structural check. Any of these forces the general 4a path
-- (correctness over speed):
--
--   * @k@ used more than once anywhere (multi-shot or duplicated use);
--   * @k@ stored, partially applied, or passed as a non-tail argument
--     (it escapes — the segment may outlive the clause);
--   * @k@ NOT in tail position (work happens after the resume);
--   * @k@ applied to ≠ 1 explicit argument (resume is quantity-1);
--   * a clause whose tail we cannot statically resolve to @k v@
--     (e.g. through an unmodelled construct) — left non-tail.
--
-- Crucially @k@ is allowed to occur in NON-tail positions of branches
-- the tail does not take only if it does not occur at all elsewhere:
-- the occurrence count is global over @body@, so a @k@ inside one arm of
-- an @if@ whose other arm is the tail @k v@ counts as two occurrences and
-- correctly forces the general path. Pre-resume work in the clause (e.g.
-- @let s' = f s in k s'@, @State.put@-style transforms) is fine — only
-- @k@'s own usage shape is constrained.
tailResumptiveClause :: Name -> Expr -> Bool
tailResumptiveClause k body =
  occursK body == 1 && tailIsResume body
  where
    kt = nameText k
    -- A reference to the resumption binder by name. (Shadowing by an
    -- inner lambda/let binding the same spelling is conservatively
    -- treated as a use too — counting it only risks a false NEGATIVE,
    -- never a false positive, so soundness holds.)
    isK = \case
      EVar n -> nameText n == kt
      _ -> False

    -- Total syntactic occurrences of @k@ anywhere in the clause body.
    -- One — and only one — is permitted, and it must be the tail
    -- application's head; any other occurrence (a second resume, a
    -- capture into a closure, a store) makes the count ≥ 2.
    occursK :: Expr -> Int
    occursK e
      | isK e = 1
      | otherwise = sum (map occursK (subExprs e))

    -- Is the clause's tail exactly @k v@ for a single explicit @v@?
    -- We follow the tail through the value-position constructs that
    -- preserve "the last thing evaluated": let/in, both arms of an if,
    -- match arms, ascriptions, and the final item of a do-block.
    tailIsResume :: Expr -> Bool
    tailIsResume = \case
      EApp h args
        | isK h -> length (explicitArgs args) == 1
        -- a deeper application head (currying) means k is applied to
        -- ≠1 explicit arg here, or the head is not k → not a tail resume
        | otherwise -> False
      ELet _ b _ -> tailIsResume b
      EAscription e _ _ -> tailIsResume e
      EIf alts mels _ ->
        not (null alts)
          && all (tailIsResume . snd) alts
          && maybe False tailIsResume mels
      EMatch _ cases _ ->
        let bodies = [e | MatchCase _ _ e _ <- cases]
         in not (null bodies) && all tailIsResume bodies
      EDo _ items _ -> doTailIsResume items
      _ -> False

    -- The tail of a do-block is its final item; only a trailing
    -- expression item (or a trailing statement-if whose suites all tail
    -- to a resume) qualifies. A trailing bind/let/loop/return etc. means
    -- the resume is not the block's tail value.
    doTailIsResume :: [DoItem] -> Bool
    doTailIsResume items = case reverse items of
      DoExpr e : _ -> tailIsResume e
      DoIf alts mels _ : _ ->
        not (null alts)
          && all (doTailIsResume . snd) alts
          && maybe False doTailIsResume mels
      _ -> False

    explicitArgs = filter isExplicitArg
    isExplicitArg = \case
      ArgExplicit _ -> True
      ArgInout _ _ -> True
      _ -> False

-- | The expressions of a match arm (its body and any guard); an
-- @impossible@ arm is unreachable and contributes none.
matchCaseExprs :: MatchCase -> [Expr]
matchCaseExprs = \case
  MatchCase _ mg e _ -> maybeToList mg ++ [e]
  MatchImpossible _ -> []

-- | The immediate sub-expressions of an expression, for the structural
-- occurrence count in 'tailResumptiveClause'. Deliberately total over
-- the surface 'Expr': anything not enumerated contributes its children
-- via the catch-all, so an unmodelled construct cannot hide a @k@.
subExprs :: Expr -> [Expr]
subExprs e0 = case e0 of
  EApp h args -> h : concatMap argExprs args
  EDot e _ -> [e]
  EQDot e _ -> [e]
  ERecordPatch e items _ -> e : concatMap patchExprs items
  EReceiverSection _ args _ -> concatMap argExprs args
  ESectionLeft e _ _ -> [e]
  ESectionRight _ e _ -> [e]
  EOpChain elems -> [x | ChainOperand x <- elems]
  EElvis a b _ -> [a, b]
  ELambda _ _ b _ -> [b]
  ELet bs b _ -> map lbExpr bs ++ [b]
  EBlock _ me _ -> maybeToList me
  EDo _ items _ -> concatMap doItemExprs items
  EIf alts mels _ -> concatMap (\(c, t) -> [c, t]) alts ++ maybeToList mels
  EMatch s cases _ -> s : concatMap matchCaseExprs cases
  ETry s cases mels _ -> s : concatMap exceptCaseBody cases ++ maybeToList mels
  ETryMatch s ms cs mels _ ->
    s : concatMap matchCaseExprs ms ++ concatMap exceptCaseBody cs ++ maybeToList mels
  EHandle _ lbl scrut cases _ ->
    lbl : scrut : concatMap handlerCaseExprs cases
  EIs e _ -> [e]
  EThunk e _ -> [e]
  ELazy e _ -> [e]
  EForce e _ -> [e]
  ESeal a b _ -> [a, b]
  EOpenExists e _ _ b _ -> [e, b]
  ESealExists bs a b _ -> map snd bs ++ [a, b]
  ETuple es _ -> es
  ERecordLit items _ -> concatMap recItemExprs items
  EListLit es _ -> es
  ESetLit es _ -> es
  EMapLit kvs _ -> concatMap (\(a, b) -> [a, b]) kvs
  EAscription e _ _ -> [e]
  ECaptures e _ _ -> [e]
  ERefFacet {} -> []
  EVarRead {} -> []
  EBang _ e _ -> [e]
  EQuote e _ -> [e]
  ESplice e _ -> [e]
  EStringLit _ parts _ -> map ipExpr parts
  _ -> []
  where
    argExprs = \case
      ArgExplicit e -> [e]
      ArgImplicit e -> [e]
      ArgInout e _ -> [e]
      ArgNamedBlock fs _ -> [x | (_, Just x) <- fs]
    patchExprs = \case
      PatchUpdate _ (PatchValue e) -> [e]
      PatchExtend _ e -> [e]
      PatchSection a b -> [a, b]
      PatchPun _ -> []
    recItemExprs (RecItem _ _ mv) = maybeToList mv
    exceptCaseBody (ExceptCase _ mg b _) = maybeToList mg ++ [b]
    handlerCaseExprs = \case
      HandlerReturn _ b _ -> [b]
      HandlerOp _ _ _ b _ -> [b]

-- | The expressions buried in a 'DoItem', for the occurrence count.
doItemExprs :: DoItem -> [Expr]
doItemExprs = \case
  DoBind lb -> [lbExpr lb]
  DoLet lb -> [lbExpr lb]
  DoLetQ _ e mels _ -> e : maybe [] (\(_, fe) -> [fe]) mels
  DoVar _ _ e _ -> [e]
  DoAssign _ _ e _ -> [e]
  DoExpr e -> [e]
  DoUsing _ _ e _ -> [e]
  DoDefer _ e _ -> [e]
  DoReturn _ me _ -> maybeToList me
  DoBreak {} -> []
  DoContinue {} -> []
  DoWhile _ c body mels _ -> c : concatMap doItemExprs body ++ maybe [] (concatMap doItemExprs) mels
  DoFor _ _ src body mels _ -> src : concatMap doItemExprs body ++ maybe [] (concatMap doItemExprs) mels
  DoIf alts mels _ ->
    concatMap (\(c, its) -> c : concatMap doItemExprs its) alts
      ++ maybe [] (concatMap doItemExprs) mels
  DoDecl _ -> []

declsToBinds :: [Decl] -> Analysis [LetBind]
declsToBinds [] = pure []
declsToBinds (d : ds) = case d of
  DLet _ (LetDef (Just n) _ Nothing prefix [] _ Nothing body) sp ->
    (LetBind False prefix (PVar n) Nothing body sp :) <$> declsToBinds ds
  DLet _ (LetDef Nothing imp (Just pat) prefix [] mty Nothing body) sp ->
    (LetBind imp prefix pat mty body sp :) <$> declsToBinds ds
  DSig {} -> declsToBinds ds
  _ -> bailOut >> pure []

-- | Control-flow result of a do-scope segment: fall-through usage
-- ('Nothing' when unreachable), result taint, and the usage of each
-- early-exit path (§12.2.5: positive lower bounds hold on every
-- completion path; break\/continue stop at the enclosing loop, returns
-- exit the do-scope).
data Flow = Flow
  { fU :: !(Maybe PathState)
  , fT :: !(Maybe Span)
  , fBC :: ![PathState]
  , fRet :: ![PathState]
  }

data PathState = PathState
  { psU :: !Usage
  , psVars :: !(Map Text VInfo)
  }

-- | Sequence a prefix usage before a segment's flow.
prefixFlow :: Usage -> Flow -> Flow
prefixFlow u (Flow mu t bc ret) =
  Flow (prefixPathState u <$> mu) t (map (prefixPathState u) bc) (map (prefixPathState u) ret)

prefixPathState :: Usage -> PathState -> PathState
prefixPathState u ps = ps {psU = u `seqU` psU ps}

-- | All paths of a segment (fall-through plus early exits).
flowPaths :: Flow -> [Usage]
flowPaths fl = map psU (flowPathStates fl)

flowPathStates :: Flow -> [PathState]
flowPathStates fl = maybeToList (fU fl) ++ fBC fl ++ fRet fl

scopeFlowVars :: Env -> [Text] -> Flow -> Flow
scopeFlowVars env names fl =
  fl
    { fU = scopePath <$> fU fl
    , fBC = map scopePath (fBC fl)
    , fRet = map scopePath (fRet fl)
    }
  where
    scopePath ps = ps {psVars = foldr restore (psVars ps) names}
    restore nm vars = case Map.lookup nm (eVars env) of
      Just vi -> Map.insert nm vi vars
      Nothing -> Map.delete nm vars

joinPathVars :: Env -> [PathState] -> Map Text VInfo
joinPathVars env paths =
  Map.mapWithKey joinOne (eVars env)
  where
    joinOne nm baseVi =
      foldl
        joinVInfo
        baseVi
        [vi | ps <- paths, Just vi <- [Map.lookup nm (psVars ps)]]

-- | Walk a do-scope; sequential items, branch joins for statement-ifs,
-- loop bodies may run zero times and every break\/continue\/return path
-- is a completion path of the bindings in scope. The returned taint is
-- the do result's (its final expression or any @return@), used for
-- escape detection.
walkItems :: Env -> [DoItem] -> Analysis Flow
walkItems env0 items0 = go env0 items0
  where
    go env [] = pure (Flow (Just (PathState Map.empty (eVars env))) Nothing [] [])
    go env (item : rest) = case item of
      DoExpr e -> do
        (u, t, envAction) <- walkExecutedAction env e
        (restoreU, restored, envStable) <- applyStableExprVarInoutWrites envAction e
        let env' = applyExprVarInoutWrites envStable e
        fl <- go env' rest
        forM_ restored $ \(_, vi) -> closeVar vi (altUs (flowPaths fl))
        let flScoped = scopeFlowVars envAction (map fst restored) fl
            fl' = prefixFlow (u `seqU` restoreU) flScoped
        -- the final statement's value escapes the do-scope: report the
        -- escape at that statement, not at the closure formation
        pure fl' {fT = if null rest then (exprSpan e <$ t) else fT fl'}
      DoLet lb -> bindLike env lb rest
      DoBind lb
        | Just (n, rhs, sp) <- recognizedWriteRef env (lbExpr lb) ->
            mutableWriteBind env n rhs sp lb rest
      DoBind lb
        | otherwise -> do
            (fl, suffixFl) <- bindLikeAction' env lb rest
            -- §18.1.20 call-site capture rule: the suffix from a multi-shot
            -- operation site to the handler boundary is captured by a
            -- reusable resumption, so every runtime-relevant captured value
            -- must be duplicable and free of borrow obligations
            forM_ (multishotOpCall env (lbExpr lb)) $ \(osp, opn) ->
              checkMultishotCapture env osp opn (flowPaths suffixFl)
            pure fl
      DoUsing _ pat rhs sp -> do
        -- §19.5: the bound resource is borrowed for the rest of scope
        -- and may not itself escape the do-scope
        (rhsU, _, envAction) <- walkExecutedAction env rhs
        (segs, env') <- walkBindsWith (\_ _ -> pure rNone) envAction [LetBind False (BinderPrefix Nothing (Just (BorrowMark Nothing))) pat Nothing rhs sp]
        let bound = concat [b | (_, b, _) <- segs]
            u = rhsU `seqU` foldr (\(su, _, _) acc -> su `seqU` acc) Map.empty segs
            markUsing = foldr (\(nm, _) -> Map.adjust (\vi -> vi {vUsing = True}) nm) (eVars env') bound
        fl <- go env' {eVars = markUsing} rest
        forM_ bound $ \(_, vi) -> closeVar vi (altUs (flowPaths fl))
        pure (prefixFlow u (scopeFlowVars envAction (map fst bound) fl))
      DoLetQ pat rhs mElse sp -> do
        u <- fst . flatR <$> walkE env rhs
        -- the else handler is an alternative completion path (§18.2)
        eu <- case mElse of
          Just (rp, fe) -> do
            shadow <- shadowVars (patVars rp) sp
            Just . fst . flatR <$> walkE (bindVars shadow env) fe
          Nothing -> do
            -- a plain let? silently discards the residual alternatives;
            -- a residue carrying a positive-lower-bound field may not be
            -- dropped that way (§12.2.5, §18.2)
            forM_ (residueLinear env pat) $ \cn ->
              emit "E_QTT_LINEAR_DROP" "kappa.quantity.positive-lower-bound" sp
                ("the residual constructor '" <> cn <> "' carries a quantity-1 or relevant field; a plain let? may not discard it (§12.2.5)")
            pure Nothing
        shadow <- shadowVars (patVars pat) sp
        fl <- go (bindVars shadow env) rest
        let flScoped = scopeFlowVars env (map fst shadow) fl
            fl' = prefixFlow u flScoped
            elseRet = [PathState e (eVars env) | e <- maybeToList eu]
        pure fl' {fRet = elseRet ++ fRet fl'}
      DoVar n mty rhs _ -> do
        u <- fst . flatR <$> walkE env rhs
        shadowK <- freshKey (nameText n)
        let factRhs = maybe rhs (\ty -> EAscription rhs ty (exprSpan rhs)) mty
            mutInfo = storedValueInfo env shadowK (nameSpan n) factRhs
            env' = bindVars [(nameText n, mutInfo)] env
        fl <- go env' rest
        forM_ (flowPathStates fl) $ \ps ->
          closeVarWith
            (Just (MutableCloseContext "current-value" "scope exit"))
            (Map.findWithDefault mutInfo (nameText n) (psVars ps))
            (psU ps)
        pure (prefixFlow u (scopeFlowVars env [nameText n] fl))
      DoAssign n monadic rhs sp
        | Just vi <- Map.lookup (nameText n) (eVars env)
        , vMutable vi ->
            if monadic
              then mutableWriteAction env n rhs sp rest
              else mutableWrite (MutableCloseContext "assignment-target" "assignment") env n rhs sp rest
        | otherwise -> do
            u <- fst . flatR <$> walkE env rhs
            prefixFlow u <$> go env rest
      DoReturn _ me _ -> do
        -- a return ends this path; items after it are unreachable
        (u, t) <- maybe (pure (Map.empty, Nothing)) (fmap flatR . walkE env) me
        pure (Flow Nothing t [] [PathState u (eVars env)])
      DoBreak {} -> pure (Flow Nothing Nothing [PathState Map.empty (eVars env)] [])
      DoContinue {} -> pure (Flow Nothing Nothing [PathState Map.empty (eVars env)] [])
      DoWhile _ cond body mels _ -> do
        (cu, _, envCond) <- walkExecutedAction env cond
        bodyFl <- go envCond body
        -- per-iteration paths: fall-through and break/continue exits;
        -- the loop may run zero times (§18.2.4)
        let iter = loopU (altUs (map psU (maybeToList (fU bodyFl) ++ fBC bodyFl)))
            loopExitVars = joinPathVars envCond (PathState Map.empty (eVars envCond) : flowPathStates bodyFl)
            loopEnv = envCond {eVars = loopExitVars}
        elseFl <- traverse (go loopEnv) mels
        let eu = maybe Map.empty (altUs . flowPaths) elseFl
            elseRet = maybe [] fRet elseFl
            afterLoopVars =
              case elseFl of
                Just ef | not (null (maybeToList (fU ef))) -> joinPathVars loopEnv (maybeToList (fU ef) ++ fBC bodyFl)
                _ -> joinPathVars envCond (PathState Map.empty (eVars envCond) : fBC bodyFl)
            restEnv = envCond {eVars = afterLoopVars}
        fl <- go restEnv rest
        let fl' = prefixFlow (cu `seqU` iter `seqU` eu) fl
            loopRet = map (prefixPathState cu) (fRet bodyFl ++ elseRet)
        pure fl' {fRet = loopRet ++ fRet fl'}
      DoFor _ pat src body mels sp -> do
        (su, _, envSrc) <- walkExecutedAction env src
        shadow <- shadowVars (patVars pat) sp
        bodyFl0 <- go (bindVars shadow envSrc) body
        let bodyFl = scopeFlowVars envSrc (map fst shadow) bodyFl0
            iter = loopU (altUs (map psU (maybeToList (fU bodyFl) ++ fBC bodyFl)))
            loopExitVars = joinPathVars envSrc (PathState Map.empty (eVars envSrc) : flowPathStates bodyFl)
            loopEnv = envSrc {eVars = loopExitVars}
        elseFl <- traverse (go loopEnv) mels
        let eu = maybe Map.empty (altUs . flowPaths) elseFl
            elseRet = maybe [] fRet elseFl
            afterLoopVars =
              case elseFl of
                Just ef | not (null (maybeToList (fU ef))) -> joinPathVars loopEnv (maybeToList (fU ef) ++ fBC bodyFl)
                _ -> joinPathVars envSrc (PathState Map.empty (eVars envSrc) : fBC bodyFl)
            restEnv = envSrc {eVars = afterLoopVars}
        fl <- go restEnv rest
        let fl' = prefixFlow (su `seqU` iter `seqU` eu) fl
            loopRet = map (prefixPathState su) (fRet bodyFl ++ elseRet)
        pure fl' {fRet = loopRet ++ fRet fl'}
      DoIf alts mels _ -> do
        (bfs, elsePrefix, elseEnv) <- walkIfAlts Map.empty env alts
        mef0 <- traverse (go elseEnv) mels
        let mef = prefixFlow elsePrefix <$> mef0
            branchFls = bfs ++ maybeToList mef
            -- with no else there is an implicit empty fall-through path
            fallts =
              mapMaybe fU branchFls
                ++ [PathState elsePrefix (eVars elseEnv) | case mef of Nothing -> True; Just _ -> False]
            branchFall
              | null fallts = Nothing
              | otherwise = Just (altUs (map psU fallts))
            joinedEnv = env {eVars = joinPathVars env fallts}
        fl <- go joinedEnv rest
        let fl' = case branchFall of
              Nothing -> Flow Nothing (fT fl) [] []
              Just bu -> prefixFlow bu fl
            exitsB = concatMap fBC branchFls
            exitsR = concatMap fRet branchFls
        pure fl' {fBC = exitsB ++ fBC fl', fRet = exitsR ++ fRet fl'}
      DoDefer _ e sp -> do
        u <- fst . flatR <$> walkE env e
        when (deferAbrupt e) $
          emit "E_DEFER_ABRUPT_CONTROL" "kappa-hs.do.defer" sp
            "a deferred action must not return, break, or continue out of itself (§18.7)"
        prefixFlow u <$> go env rest
      DoDecl d | isEffDecl d -> go (addEffDecls env [d]) rest
      DoDecl d -> do
        lbs <- declsToBinds [d]
        case lbs of
          [lb] -> bindLike env lb rest
          _ -> go env rest
      where
        shadowVars nms sp =
          mapM (\nm -> (\k -> (nm, plainV k sp)) <$> freshKey nm) nms
        bindLike envc lb restItems = fst <$> bindLike' envc lb restItems
        bindLike' = bindLikeWith walkE
        bindLikeAction' envc lb@(LetBind {}) restItems = do
          (actU, _, envAction) <- walkExecutedAction envc (lbExpr lb)
          (segs, env') <- walkBindsWith (\_ _ -> pure rNone) envAction [lb]
          let u = actU `seqU` foldr (\(su, _, _) acc -> su `seqU` acc) Map.empty segs
              bound = concat [b | (_, b, _) <- segs]
          fl <- go env' restItems
          -- every path leaving the binding's scope must satisfy it
          forM_ bound $ \(_, vi) -> closeVar vi (altUs (flowPaths fl))
          let flScoped = scopeFlowVars envAction (map fst bound) fl
          pure (prefixFlow u flScoped, flScoped)
        bindLikeWith walkRhs envc lb@(LetBind {}) restItems = do
          (segs, env') <- walkBindsWith walkRhs envc [lb]
          let u = foldr (\(su, _, _) acc -> su `seqU` acc) Map.empty segs
              bound = concat [b | (_, b, _) <- segs]
          fl <- go env' restItems
          -- every path leaving the binding's scope must satisfy it
          forM_ bound $ \(_, vi) -> closeVar vi (altUs (flowPaths fl))
          let flScoped = scopeFlowVars envc (map fst bound) fl
          pure (prefixFlow u flScoped, flScoped)
        walkExecutedAction envc = \case
          EAscription e _ _ -> walkExecutedAction envc e
          EBang _ e _ -> walkExecutedAction envc e
          EDo _ items _ -> do
            fl <- walkItems envc items
            let paths = flowPathStates fl
                usages = map psU paths
                u = altUs usages
                t = firstJust (maybeToList (fT fl) ++ mapMaybe (usageAnonBorrowIntro envc) usages)
                env' =
                  case paths of
                    [] -> envc
                    _ -> envc {eVars = joinPathVars envc paths}
            pure (u, t, env')
          EIf alts mels _ -> do
            (branchFls, elsePrefix, elseEnv) <- walkIfAlts Map.empty envc [(cond, [DoExpr body]) | (cond, body) <- alts]
            mef0 <- traverse (walkExecutedAction elseEnv) mels
            let mef = (\(u, t, envElse) -> Flow (Just (PathState (elsePrefix `seqU` u) (eVars envElse))) t [] []) <$> mef0
                paths =
                  mapMaybe fU (branchFls ++ maybeToList mef)
                    ++ [PathState elsePrefix (eVars elseEnv) | isNothing mef0]
                u = altUs (map psU paths)
                t = firstJust (mapMaybe fT (branchFls ++ maybeToList mef))
                env' =
                  case paths of
                    [] -> envc
                    _ -> envc {eVars = joinPathVars envc paths}
            pure (u, t, env')
          EMatch scrut cases _ -> do
            (su, st, envScrut) <- walkExecutedAction envc scrut
            caseRuns <- forM cases $ \case
              MatchCase _ mg body _ -> do
                (gu, _, envGuard) <- maybe (pure (Map.empty, Nothing, envScrut)) (walkExecutedAction envScrut) mg
                (bu, bt, envBody) <- walkExecutedAction envGuard body
                pure (gu `seqU` bu, bt, envBody)
              MatchImpossible _ -> pure (Map.empty, Nothing, envScrut)
            let paths = [PathState u (eVars envCase) | (u, _, envCase) <- caseRuns]
                branchU = altUs (map psU paths)
                env' =
                  case paths of
                    [] -> envScrut
                    _ -> envScrut {eVars = joinPathVars envScrut paths}
            pure (su `seqU` branchU, firstJust (maybeToList st ++ mapMaybe (\(_, t, _) -> t) caseRuns), env')
          ETry scrut excepts mfin _ -> do
            (su, st, envScrut) <- walkExecutedAction envc scrut
            exceptRuns <- forM excepts $ \(ExceptCase pat mg body sp) -> do
              shadow <- shadowVars (patVars pat) sp
              (gu, _, envGuard) <- maybe (pure (Map.empty, Nothing, envScrut)) (walkExecutedAction envScrut) mg
              (bu, bt, envBody0) <- walkExecutedAction (bindVars shadow envGuard) body
              let envBody = restoreScopedEnv envGuard (map fst shadow) envBody0
              forM_ shadow $ \(_, vi) -> closeVar vi bu
              pure (gu `seqU` bu, bt, envBody)
            let paths0 = PathState Map.empty (eVars envScrut) : [PathState u (eVars envCase) | (u, _, envCase) <- exceptRuns]
                joined0 = envScrut {eVars = joinPathVars envScrut paths0}
                branchU = altUs (map psU paths0)
                branchT = firstJust (maybeToList st ++ mapMaybe (\(_, t, _) -> t) exceptRuns)
            case mfin of
              Nothing -> pure (su `seqU` branchU, branchT, joined0)
              Just fin -> do
                (fu, ft, envFin) <- walkExecutedAction joined0 fin
                pure (su `seqU` branchU `seqU` fu, firstJust (catMaybes [branchT, ft]), envFin)
          ETryMatch scrut cases excepts mfin _ -> do
            (mu, mt, envMatched) <- walkExecutedAction envc (EMatch scrut cases (exprSpan scrut))
            (tu, tt, envTry) <- walkExecutedAction envMatched (ETry (EUnit (exprSpan scrut)) excepts mfin (exprSpan scrut))
            pure (mu `seqU` tu, firstJust (catMaybes [mt, tt]), envTry)
          EHandle _ _ scrut cases _ -> do
            (su, st, envScrut) <- walkExecutedAction envc scrut
            caseRuns <- forM cases $ \case
              HandlerReturn pat body sp -> do
                shadow <- shadowVars (patVars pat) sp
                (bu, bt, envBody0) <- walkExecutedAction (bindVars shadow envScrut) body
                let envBody = restoreScopedEnv envScrut (map fst shadow) envBody0
                forM_ shadow $ \(_, vi) -> closeVar vi bu
                pure (bu, bt, envBody)
              HandlerOp _ argPats kN body sp -> do
                shadow <- shadowVars (concatMap patVars argPats) sp
                kKey <- freshKey (nameText kN)
                let q = Map.findWithDefault QOne (nameSpan kN) (eHandlerOpQuantities envc)
                    kvi = (plainV kKey (nameSpan kN)) {vQ = countedQ q}
                    envBody0 = bindVars (shadow ++ [(nameText kN, kvi)]) envScrut
                (bu, bt, envBody1) <- walkExecutedAction envBody0 body
                closeVar kvi bu
                forM_ shadow $ \(_, vi) -> closeVar vi bu
                let envBody = restoreScopedEnv envScrut (map fst shadow ++ [nameText kN]) envBody1
                pure (bu, bt, envBody)
            let paths = PathState Map.empty (eVars envScrut) : [PathState u (eVars envCase) | (u, _, envCase) <- caseRuns]
                env' = envScrut {eVars = joinPathVars envScrut paths}
            pure (su `seqU` altUs (map psU paths), firstJust (maybeToList st ++ mapMaybe (\(_, t, _) -> t) caseRuns), env')
          EBlock decls mres _ -> do
            let envBlock = addEffDecls envc decls
            binds <- declsToBinds [d | d <- decls, not (isEffDecl d)]
            (segs, envBound) <- walkBinds envBlock binds
            let bindU = foldr (\(u, _, _) acc -> u `seqU` acc) Map.empty segs
                bound = concat [b | (_, b, _) <- segs]
            (ru, rt, envRes0) <- maybe (pure (Map.empty, Nothing, envBound)) (walkExecutedAction envBound) mres
            forM_ bound $ \(_, vi) -> closeVar vi ru
            let envRes = restoreScopedEnv envBlock (map fst bound) envRes0
            pure (bindU `seqU` ru, rt, envRes)
          e
            | Just (n, rhs, sp) <- recognizedWriteRef envc e -> do
              (u, env') <- recognizedWriteEffect (MutableCloseContext "reference" "writeRef") envc n rhs sp
              pure (u, Nothing, env')
            | otherwise -> do
              r <- walkExecutedExpr envc e
              let (u, t) = flatR r
              pure (u, t, envc)
        restoreScopedEnv base names envAfter =
          envAfter {eVars = foldr restore (eVars envAfter) names}
          where
            restore nm vars = case Map.lookup nm (eVars base) of
              Just vi -> Map.insert nm vi vars
              Nothing -> Map.delete nm vars
        walkIfAlts prefixU envc [] =
          pure ([], prefixU, envc)
        walkIfAlts prefixU envc ((cond, body) : more) = do
          (cu, _, envCond) <- walkExecutedAction envc cond
          let prefixU' = prefixU `seqU` cu
          bodyFl <- prefixFlow prefixU' <$> go envCond body
          (restFls, elsePrefix, elseEnv) <- walkIfAlts prefixU' envCond more
          pure (bodyFl : restFls, elsePrefix, elseEnv)
        recognizedWriteEffect closeCtx envc n rhs wsp =
          case Map.lookup (nameText n) (eVars envc) of
            Just oldInfo | vMutable oldInfo -> do
              closeVarWith
                (Just closeCtx)
                (oldInfo {vSpan = wsp})
                Map.empty
              u <- fst . flatR <$> walkE envc rhs
              let newInfo = (storedValueInfoForWrite envc oldInfo rhs) {vMutable = True}
                  env' = envc {eVars = Map.insert (nameText n) newInfo (eVars envc)}
              pure (u, env')
            _ -> do
              u <- fst . flatR <$> walkE envc rhs
              pure (u, envc)
        mutableWrite closeCtx envc n rhs wsp restItems = do
          (u, env') <- recognizedWriteEffect closeCtx envc n rhs wsp
          fl <- go env' restItems
          pure (prefixFlow u fl)
        mutableWriteAction envc n action wsp restItems = do
          (u, _, envAction) <- walkExecutedAction envc action
          case Map.lookup (nameText n) (eVars envAction) of
            Just oldInfo | vMutable oldInfo -> do
              closeVarWith
                (Just (MutableCloseContext "assignment-target" "assignment"))
                (oldInfo {vSpan = wsp})
                Map.empty
              let newInfo = storedActionResultInfo envAction oldInfo action
                  env' = envAction {eVars = Map.insert (nameText n) newInfo (eVars envAction)}
              fl <- go env' restItems
              pure (prefixFlow u fl)
            _ -> do
              prefixFlow u <$> go envAction restItems
        mutableWriteBind envc n rhs wsp lb restItems = do
          case Map.lookup (nameText n) (eVars envc) of
            Just oldInfo | vMutable oldInfo -> do
              closeVarWith
                (Just (MutableCloseContext "reference" "writeRef"))
                (oldInfo {vSpan = wsp})
                Map.empty
              u <- fst . flatR <$> walkE envc rhs
              let newInfo = (storedValueInfoForWrite envc oldInfo rhs) {vMutable = True}
                  envWritten = envc {eVars = Map.insert (nameText n) newInfo (eVars envc)}
              shadow <- shadowVars (patVars (lbPattern lb)) (lbSpan lb)
              fl <- go (bindVars shadow envWritten) restItems
              forM_ shadow $ \(_, vi) -> closeVar vi (altUs (flowPaths fl))
              pure (prefixFlow u (scopeFlowVars envWritten (map fst shadow) fl))
            _ -> bindLike envc lb restItems
        recognizedWriteRef envc = \case
          EApp f args
            | Just (n, rhs, sp) <- recognizedRefWrite envc f args
            , Just vi <- Map.lookup (nameText n) (eVars envc)
            , vMutable vi ->
                Just (n, rhs, sp)
          EAscription e _ _ -> recognizedWriteRef envc e
          _ -> Nothing
        -- a use of any outer non-duplicable binding in the captured
        -- suffix of a multi-shot operation (§18.1.20.2)
        checkMultishotCapture envc osp opn paths = do
          let usesVar vi u =
                any
                  (\(k, c) -> ucTouched c && (k == vKey vi || (vKey vi <> ".") `T.isPrefixOf` k))
                  (Map.toList u)
              offenders =
                [ (vi, kind)
                | vi <- Map.elems (eVars envc)
                , Just kind <- [captureKind vi]
                , any (usesVar vi) paths
                ]
          case offenders of
            ((vi, kind) : _) ->
              emit "E_QTT_CONTINUATION_CAPTURE" "kappa-hs.qtt.continuation-capture" osp
                ( "the multi-shot operation '" <> opn <> "' would capture '"
                    <> T.takeWhile (/= '#') (vKey vi) <> "' (" <> kind
                    <> ") in its resumption; every value captured by a multi-shot resumption must be duplicable and free of borrow obligations (§18.1.20)"
                )
            [] -> pure ()
        captureKind vi
          | vBorrowed vi = Just "a borrowed binding"
          | vQ vi `elem` [Just QOne, Just QAtMostOne] || vNonDupValue vi || not (null (nonDupFields vi)) =
              Just "a non-duplicable binding"
          | otherwise = Nothing

-- | Residual constructors of a plain @let?@ pattern that carry a
-- positive-lower-bound (quantity @1@\/@>=1@) field (§12.2.5).
residueLinear :: Env -> Pattern -> [Text]
residueLinear env pat = case headCtor pat of
  Just cn ->
    [ cn'
    | (cn', ps) <- Map.findWithDefault [] cn (eCtors env)
    , cn' /= cn
    , any (\p -> cpiQuantity p `elem` [Just QOne, Just QAtLeastOne]) ps
    ]
  Nothing -> []
  where
    headCtor = \case
      PCtor cr _ _ -> Just (nameText (crName cr))
      PCtorNamed cr _ _ -> Just (nameText (crName cr))
      PTyped p _ _ -> headCtor p
      PAs _ p -> headCtor p
      _ -> Nothing

-- | Abrupt control flow escaping a deferred action (§18.7): any
-- @return@, or a @break@\/@continue@ not enclosed by a loop inside the
-- deferred expression itself; nested lambdas are separate targets.
deferAbrupt :: Expr -> Bool
deferAbrupt = goE
  where
    goE = \case
      EDo _ items _ -> any (goI False) items
      EBlock {} -> False
      ELambda {} -> False
      EIf alts mels _ -> any (goE . snd) alts || maybe False goE mels
      ELet _ body _ -> goE body
      _ -> False
    goI inLoop = \case
      DoReturn {} -> True
      DoBreak {} -> not inLoop
      DoContinue {} -> not inLoop
      DoWhile _ _ body mels _ -> any (goI True) body || maybe False (any (goI inLoop)) mels
      DoFor _ _ _ body mels _ -> any (goI True) body || maybe False (any (goI inLoop)) mels
      DoIf alts mels _ -> any (any (goI inLoop) . snd) alts || maybe False (any (goI inLoop)) mels
      DoExpr e -> goE e
      DoLet lb -> goE (lbExpr lb)
      DoBind lb -> goE (lbExpr lb)
      _ -> False
