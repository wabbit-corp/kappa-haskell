{-# LANGUAGE OverloadedRecordDot #-}

-- | Native backend: lower elaborated KCore ('Kappa.Core.Term') to C that
-- links against the @kappart@ runtime (see @runtime/kappart.h@ and
-- docs/NATIVE_BACKEND.md).
--
-- The lowering is a structural recursion over 'Term' that mirrors
-- 'Kappa.Eval.eval' / 'Kappa.Interp' but emits C rather than stepping an
-- interpreter, so the two stay semantically aligned for the supported
-- subset.  Any 'Term' or do-kernel item the backend does not support is a
-- compile-time 'E_BACKEND_UNSUPPORTED' error naming the construct (and the
-- definition it appears in) — never a silent fallback to interpreter
-- behaviour.
--
-- Representation contract with the runtime:
--
--   * all functions are curried arity-1 closures; application is a chain
--     of @kapp@ (explicit) / @kappi@ (implicit) calls;
--   * implicit arguments are erased for primitives and constructors, and
--     type-level implicit arguments to ordinary functions are passed as an
--     unused @kunit()@ placeholder (types are computationally erased);
--   * the de Bruijn environment is the runtime @KEnv@ linked list, head =
--     index 0; entering a binder conses onto it.
module Kappa.Backend.C
  ( generateC
  , BackendError (..)
  , backendDiagnostics
  , basePrims
    -- * Shared primitive registry (consumed by "Kappa.Backend.LLVM")
  , PrimEntry (..)
  , primEntries
  , primDirect
  , primRegistryDiagnostics
    -- * Shared Q0 spine erasure (consumed by "Kappa.Backend.LLVM")
  , eraseQ0ArgsP
  ) where

import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import Data.Char (isAscii, isAsciiLower, isAsciiUpper, isDigit, ord)
import Data.List (sort)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import Control.Monad (foldM, forM, forM_, unless, void, when)
import Control.Monad.State.Strict
import Kappa.Backend.NativeFfi
  ( ResolvedNativeSymbol (..)
  , externPrototype
  , rnsCollectCtors
  , wrapperCName
  , wrapperDefinition
  )
import qualified Kappa.Backend.Repr as Repr
import qualified Kappa.Builtins as Builtins
import Kappa.Check (CheckState (..), CtorInfo (..))
import Kappa.Core
import Kappa.Diagnostic
import Kappa.Eval (EvalCtx (..), GlobalDef (..), Globals (..), eval, force, quote)
import Kappa.Source (ModuleName (..), Span, noSpan)
import Numeric (showHex, showOct)

-- | One reason the native backend cannot compile a definition: the global
-- it occurred in, the unsupported construct, and a human detail.
data BackendError = BackendError
  { beGlobal :: !GName
  , beSpan :: !Span
  , beConstruct :: !Text
  , beDetail :: !Text
  }
  deriving stock (Eq, Show)

-- | Render backend errors as structured diagnostics (§3.1): one
-- @E_BACKEND_UNSUPPORTED@ per unsupported construct, citing the offending
-- definition's declaration site.
backendDiagnostics :: [BackendError] -> Diagnostics
backendDiagnostics = map one
  where
    one be =
      diag SevError StageElaborate "E_BACKEND_UNSUPPORTED" (Just "kappa-hs.backend.unsupported")
        (beSpan be)
        ( "the native backend cannot compile definition '"
            <> gnameText (beGlobal be)
            <> "': " <> beDetail be
            <> " (" <> beConstruct be <> ")"
        )

-- ── Code-generation monad ────────────────────────────────────────────

data GenState = GenState
  { gsFresh :: !Int
  , gsStmts :: ![Text] -- ^ current function body, reversed
  , gsEnv :: !Text -- ^ C expression for the current KEnv*
  , gsParamLvals :: ![Text] -- ^ R2.3: in a FLAT (capture-free) first-order worker, the C lvalue for each de Bruijn index — the params (index @i@ = source param @n-1-i@) plus any @let@/@match@-bound locals prepended at index 0 (R2.3-rest); a 'CVar' reads the C local directly instead of walking @kvar(kw_env,i)@. Empty outside a flat worker body (then 'CVar' uses @kvar@).
  , gsTop :: ![Text] -- ^ completed top-level C functions, reversed
  , gsProtos :: ![Text] -- ^ forward declarations, reversed
  , gsEmitted :: !(Set GName) -- ^ globals already emitted or enqueued
  , gsQueue :: ![GName] -- ^ globals still to emit
  , gsErrs :: ![BackendError] -- ^ unsupported-construct findings
  , gsCur :: !GName -- ^ definition currently being compiled (for diagnostics)
  , gsGlobals :: !(Map GName GlobalDef)
  , gsEvalCtx :: !EvalCtx -- ^ R2.2: a non-runtime EvalCtx (built from the CheckState) used only to 'quote' a global's 'gdType' to a Term so the per-parameter scalar kinds can be read from its Pi telescope.
  , gsBodies :: !(Map GName Term)
  , gsSuspenders :: !(Set GName) -- ^ §3.3: globals that TRANSITIVELY reach a suspending primitive (fork/await/…); computed once from gsBodies. A do-bind whose action's spine head is in here may suspend, so its do-block is CPS-lowered.
  , gsCtors :: !(Map GName CtorInfo)
  , gsDatas :: !(Set GName)
  , gsTraits :: !(Set GName)
  , gsDeclSites :: !(Map GName Span)
  , gsPrims :: !(Set Text) -- ^ primitive names the linked runtime implements
  , gsPrimUsed :: !(Set Text) -- ^ §34.5.3: builtin primitives actually referenced; 'assemble' emits an @extern@ decl for each direct entry point (@kp_*@/@kpf_*@) so the optimized output calls it DIRECTLY — never a by-name string dispatch.
  , gsHostSyms :: !(Map GName ResolvedNativeSymbol) -- ^ §27.1.1/§36.28: each provided @host.native.*@ member (an abstract global) ↦ its resolved native symbol (C symbol + ABI signature), built per build from the manifest's native bindings (never a hardcoded catalog). A reference to such a member lowers to a DIRECT typed call ('knative'), not a runtime primitive.
  , gsHostUsed :: !(Set GName) -- ^ §27.1.1: host members actually referenced; 'assemble' emits one extern prototype + marshalling wrapper per used member.
  , gsBounceMemo :: !(Map (GName, Int) (Maybe Bool)) -- ^ Native lowering cache: whether a boxed worker of this arity may return K_BOUNCE. 'Nothing' marks an in-progress analysis; recursive cycles conservatively read as may-bounce. The analysis is pure in the stable codegen environment, so caching prevents large game targets from re-walking the same bodies at every call site.
  , gsLoops :: ![LoopCtx] -- ^ enclosing loops, innermost first (§18.2.5 labels)
  , gsDefer :: ![(Text, Text)] -- ^ §18.7 TAIL-scope defer frames (do-block + tail-if-branch), innermost first; flushed after the tail IO action via kio_finally
  , gsScopeDefers :: ![(Text, Text)] -- ^ §18.7 NESTED-scope defer frames (loop body / non-tail if branch), innermost first; flushed inline at scope exit + break/continue/return crossings
  , gsDeferLabels :: ![(Text, (Text, Text))] -- ^ §18.7 label ↦ (arr,cnt) frame of each enclosing LABELED do-scope (explicit `do`/loop), innermost first; a `defer@L` registers onto the frame of the scope labeled L (which may be outer) instead of the current scope.
  , gsScalars :: !(Map Int (Text, Text)) -- ^ P0.2: in a scalarized var loop, the de-Bruijn index (relative to the push-free loop body) of each scalarized Int var -> (int64 C local, retained ref C-name). Consulted by the read/write peephole only while 'gsScalarRegion'.
  , gsScalarRegion :: !Bool -- ^ P0.2: true only while emitting the SCALAR copy of a var loop, so the readRef/writeRef/KAssign peephole reads/writes the int64 local instead of kref_get/kref_set.
  , gsCpsRefRegion :: !Bool -- ^ CPS loop family (§4 R7): true while building the @cond@/@body@ action trees of a SUSPENDING @while@ (or any CPS re-run scope). A @readRef@ then lowers to the @OP_READ_REF@ action NODE (a RUN-TIME cell access the CK-machine performs each iteration) rather than a build-time @kref_get@ captured once — so a re-run body never reads a stale snapshot, and read-after-write within an iteration is preserved.
  , gsI64Escape :: !Text -- ^ the C statement spliced by scalarArith on int overflow / INT64_MIN: @*kovf = 1; return 0;@ for an unboxed scalar worker, or @flush all scalars; goto <boxed>;@ for a scalar var loop.
  , gsCollectCtors :: !(Set Text) -- ^ LR2: gKeys of USER constructors referenced (constructed or matched); builtins use the fixed @KCT_*@ ids so they are NOT collected. After codegen, @assemble@ assigns each a @KCT_USER_BASE+i@ id (sorted, deterministic) and emits a @KT_<mangle>@ enum.
  , gsCollectVars :: !(Set Text) -- ^ LR2: §13 variant member-identity tags referenced (injected or matched); @assemble@ emits a 0-based @KVT_<mangle>@ enum (variants are never runtime-built, so no fixed-id constraint).
  }

-- | A loop's labelled control targets: its source label (if any), the C
-- goto label a @continue@ jumps to, the one a @break@ jumps to, and the
-- 'gsScopeDefers' depth at loop-body entry (so a @break@/@continue@ flushes
-- exactly the defer frames it unwinds, §18.7).
data LoopCtx = LoopCtx
  { lcLabel :: !(Maybe Text)
  , lcContinue :: !Text
  , lcBreak :: !Text
  , lcScopeDepth :: !Int
  }

type Gen = State GenState

freshN :: Text -> Gen Text
freshN base = do
  n <- gets gsFresh
  modify' $ \g -> g {gsFresh = n + 1}
  pure (base <> T.pack (show n))

-- | A fresh name for a generated top-level helper FUNCTION (lambda, closure,
-- do-block, thunk, defer), derived from the enclosing source global so the
-- generated C carries source intent — e.g. @kfn_main_2e_len_9@ for a lambda
-- inside @main.len@ — rather than an opaque @kfn_9@ (QW3, review note §6).
-- The global counter is kept only as a uniqueness suffix.  Temporaries
-- (@pa_@, @env_@, @scrut_@, …) keep the plain 'freshN' form.
freshFn :: Text -> Gen Text
freshFn base = do
  g <- gets gsCur
  n <- gets gsFresh
  modify' $ \st -> st {gsFresh = n + 1}
  pure (base <> mangle (gKey g) <> "_" <> T.pack (show n))

emit :: Text -> Gen ()
emit s = modify' $ \g -> g {gsStmts = s : gsStmts g}

-- | Run an action with a fresh (empty) statement buffer and the given
-- current-env expression, returning the produced statements in order plus
-- the action's result; restores the caller's buffer and env afterwards.
captured :: Text -> Gen a -> Gen ([Text], a)
captured env act = do
  saved <- gets gsStmts
  savedEnv <- gets gsEnv
  -- R2.3-rest: a flat worker binds let/match vars by prepending C locals to
  -- gsParamLvals; restoring it here scopes those bindings to this block (an
  -- if-branch / match-alt), exactly as the KEnv tail did for the boxed path.
  -- A no-op for the boxed path (gsParamLvals is empty there).
  savedLvals <- gets gsParamLvals
  modify' $ \g -> g {gsStmts = [], gsEnv = env}
  r <- act
  produced <- gets gsStmts
  modify' $ \g -> g {gsStmts = saved, gsEnv = savedEnv, gsParamLvals = savedLvals}
  pure (reverse produced, r)

-- | Record an unsupported-construct finding and return a placeholder C
-- expression so error collection can continue.
unsupported :: Text -> Text -> Gen Text
unsupported construct detail = do
  g <- gets gsCur
  sites <- gets gsDeclSites
  let sp = Map.findWithDefault noSpan g sites
  modify' $ \st -> st {gsErrs = BackendError g sp construct detail : gsErrs st}
  pure "kunit()"

-- | A construct that is provably NOT a runtime value of an accepted,
-- erased program (a type-level term, an elaboration invariant, or an
-- elaboration-time/staging value). Reaching it in value position is an
-- internal-invariant violation reported (never silently miscompiled) per
-- §27.7; see docs/NATIVE_ESCALATIONS.md. Same diagnostic channel as
-- 'unsupported' — the detail carries the spec citation.
escalated :: Text -> Text -> Gen Text
escalated = unsupported

-- | Enqueue a global for emission (idempotent).
enqueue :: GName -> Gen ()
enqueue g = do
  seen <- gets gsEmitted
  unless (g `Set.member` seen) $
    modify' $ \st -> st {gsEmitted = Set.insert g (gsEmitted st), gsQueue = g : gsQueue st}

-- ── Names ────────────────────────────────────────────────────────────

-- | A unique, valid C identifier for a global's accessor function.
cGlobIdent :: GName -> Text
cGlobIdent g = "kg_" <> mangle (gKey g)

mangle :: Text -> Text
mangle = T.concatMap esc
  where
    esc c
      | isAsciiLower c || isAsciiUpper c || isDigit c = T.singleton c
      | otherwise = "_" <> T.pack (showHex (ord c) "") <> "_"

-- | A C string literal (quoted, escaped) for arbitrary UTF-8 text.
cStr :: Text -> Text
cStr t = "\"" <> T.concatMap esc t <> "\""
  where
    esc c = case c of
      '"' -> "\\\""
      '\\' -> "\\\\"
      '\n' -> "\\n"
      '\t' -> "\\t"
      '\r' -> "\\r"
      _
        | isAscii c && c >= ' ' -> T.singleton c
        -- Emit non-ASCII / control bytes via their UTF-8 octets in OCTAL.
        -- A C octal escape consumes at most three digits, so \NNN cannot be
        -- extended by a following ASCII digit (unlike \xNN, which greedily
        -- absorbs subsequent hex digits — e.g. "café2" would mis-escape).
        | otherwise -> T.concat [octet b | b <- utf8Bytes c]
    octet b = "\\" <> T.pack (pad3 (showOct b ""))
    pad3 s = replicate (3 - length s) '0' ++ s

-- | A C @kstr@ literal carrying the exact UTF-8 byte length.  A String
-- literal may contain an embedded NUL (@\\u{0}@), so it must NOT be built
-- with @kstr0@ (which derives the length via @strlen@ and would truncate
-- at the NUL — corrupting both I/O and String equality).  @cStr@ escapes
-- the NUL as an octal byte, and this length is the UTF-8 byte count.
cStrL :: Text -> Text
cStrL s = "kstr(" <> cStr s <> ", " <> T.pack (show (utf8Len s)) <> ")"

-- ── LR2: numeric constructor / variant tags ─────────────────────────
--
-- A constructor/variant value carries a small integer `tagid` so pattern
-- matching dispatches on an int compare (kctor_tagid/kvariant_tagid) instead
-- of a kctor_is/kvariant_is strcmp.  The id must be IDENTICAL at every
-- construction site and every match site for a given name; codegen guarantees
-- this with one rule:
--
--   * the runtime builds 8 builtins (Unit/True/False/::/Nil/Some/None/__rat)
--     so those share a FIXED enum with the runtime — codegen spells them with
--     the kappart.h `KCT_*` names (`builtinCtorTag`);
--   * every other (user) constructor is referenced by a `KT_<mangle gKey>`
--     name, collected into `gsCollectCtors`, and given a `KCT_USER_BASE + i`
--     id by `assemble` (the value is irrelevant to correctness — both sides
--     use the same symbolic name — only its disjointness from the builtins,
--     guaranteed by KCT_USER_BASE, and from other user ctors, guaranteed by
--     `mangle` being injective, matter);
--   * variants are never runtime-built, so all variant tags are user ids:
--     a `KVT_<mangle tag>` name, collected into `gsCollectVars`, 0-based.

-- | The fixed kappart.h @KCT_*@ id for a runtime-built builtin constructor,
-- or @Nothing@ for a user constructor (which gets a @KT_*@ id). A thin
-- re-export of the single source of truth in "Kappa.Builtins"
-- ('Builtins.runtimeCtors'); the emitted symbolic @KCT_*@ name is resolved to
-- its numeric value by the C compiler against the included @kappart.h@.
--
-- §11 Ordering (LT\/EQ\/GT) is deliberately NOT here: @durationCompare@ and
-- the @Ord@ instances are @.kp@ definitions, so Ordering is a USER constructor
-- codegen builds (id @KCT_USER_BASE+i@) — the runtime never delivers it.
builtinCtorTag :: Text -> Maybe Text
builtinCtorTag = Builtins.builtinCtorCName

-- | The C tag constant for a constructor, recording a user constructor's use
-- so @assemble@ emits its @KT_*@ enum entry.
ctorTagConst :: GName -> Gen Text
ctorTagConst g = case builtinCtorTag (gKey g) of
  Just kc -> pure kc
  Nothing -> do
    modify' $ \st -> st {gsCollectCtors = Set.insert (gKey g) (gsCollectCtors st)}
    pure ("KT_" <> mangle (gKey g))

-- | The C tag constant for a §13 variant member tag, recording its use so
-- @assemble@ emits its @KVT_*@ enum entry.
variantTagConst :: Text -> Gen Text
variantTagConst tag = do
  modify' $ \st -> st {gsCollectVars = Set.insert tag (gsCollectVars st)}
  pure ("KVT_" <> mangle tag)

-- | The @enum { KT_… = …, … }@ blocks for every collected user constructor
-- and variant tag, emitted by @assemble@ after @#include "kappart.h"@ so the
-- symbolic names referenced in generated constructions/matches are defined.
tagEnumBlock :: GenState -> [Text]
tagEnumBlock st =
  ctorBlock (Set.toList (gsCollectCtors st))
    ++ block "KVT_" "" (Set.toList (gsCollectVars st))
  where
    -- KBackendIR Stage 2: the user-ctor numbering (sort gKeys, assign
    -- @KCT_USER_BASE + i@) is the single authority 'Repr.assignUserCtorTags',
    -- shared with the LLVM backend so the two agree on every id by
    -- construction.  We still EMIT the symbolic @KCT_USER_BASE + i@ offset
    -- (byte-identical to before — the C compiler resolves it against the
    -- included kappart.h), but derive @i@ from the shared id map rather than a
    -- second open-coded @sort@ + @zip@.
    ctorBlock names = case sort names of
      [] -> []
      sorted ->
        let ids = Repr.assignUserCtorTags names
         in ["enum {"]
              ++ [ "  KT_" <> mangle n <> " = KCT_USER_BASE + "
                     <> T.pack (show (Map.findWithDefault 0 n ids - Builtins.kctUserBase)) <> ","
                 | n <- sorted
                 ]
              ++ ["};"]
    -- §13 variant member tags are never runtime-built (no shared id authority);
    -- they keep their own 0-based per-program numbering.
    block prefix base names = case sort names of
      [] -> []
      sorted ->
        ["enum {"]
          ++ [ "  " <> prefix <> mangle n <> " = " <> base <> T.pack (show i) <> ","
             | (i, n) <- zip [(0 :: Int) ..] sorted
             ]
          ++ ["};"]

-- | The number of UTF-8 bytes a 'Text' encodes to (the C string length).
utf8Len :: Text -> Int
utf8Len = T.foldl' (\acc c -> acc + length (utf8Bytes c)) 0

-- | UTF-8 encode a single character to bytes.
utf8Bytes :: Char -> [Int]
utf8Bytes c =
  let n = ord c
   in if n < 0x80
        then [n]
        else if n < 0x800
          then [0xC0 + (n `div` 0x40), 0x80 + (n `mod` 0x40)]
          else if n < 0x10000
            then [0xE0 + (n `div` 0x1000), 0x80 + ((n `div` 0x40) `mod` 0x40), 0x80 + (n `mod` 0x40)]
            else
              [ 0xF0 + (n `div` 0x40000)
              , 0x80 + ((n `div` 0x1000) `mod` 0x40)
              , 0x80 + ((n `div` 0x40) `mod` 0x40)
              , 0x80 + (n `mod` 0x40)
              ]

-- ── Top-level driver ─────────────────────────────────────────────────

-- | The primitive names implemented by the base @kappart@ runtime
-- (kappart.c).  Kept in lock-step with that file: emitting a primitive
-- outside this set (plus any FFI extension) is a compile-time
-- 'E_BACKEND_UNSUPPORTED'.
basePrims :: Set Text
basePrims =
  Set.fromList
    [ -- integer
      "addInt", "subInt", "mulInt", "divInt", "modInt", "negInt"
    , "eqInt", "ltInt", "leInt"
      -- §18.1.6 Duration/Instant constructors, compare, arithmetic, clock
    , "__nowNanos" -- §18.1 clock prim (raw ns); Duration/Instant ops are the std.time .kp fragment
      -- double
    , "addDouble", "subDouble", "mulDouble", "divDouble", "negDouble"
    , "eqDouble", "ltDouble", "floatEq"
      -- string / scalar
    , "stringAppend", "eqStr", "ltStr", "eqScalar", "ltScalar"
    , "showInt", "showDouble", "showScalar", "showStringLit"
      -- §28.2 Rational
    , "__ratOfInt", "__ratNum", "__ratDen", "addRat", "subRat", "mulRat"
    , "divRat", "negRat", "eqRat", "ltRat", "showRat", "ratOfDouble"
      -- §6.1 numeric conversions
    , "natToInt", "natOfInt", "intToNat", "intToDouble", "primitiveIntToString"
      -- §6.5/§29.5 byte / bytes / grapheme atoms
    , "eqByte", "ltByte", "showByte", "eqBytes", "ltBytes", "showBytes"
    , "eqGrapheme", "showGrapheme"
      -- §29.5 std.bytes portable operations over the exact byte sequence
    , "__bytesEmpty", "__bytesSingleton", "__bytesLength", "__bytesIsEmpty"
    , "__bytesGet", "__bytesIndexUnsafe", "__bytesAppend", "__bytesSlice"
    , "__bytesTake", "__bytesDrop", "__bytesStartsWith", "__bytesEndsWith"
    , "__bytesContains", "__bytesFind", "__bytesBreakIndex", "__bytesToList"
    , "__bytesFromList", "__bytesCompact"
      -- §29.5 linear BytesBuilder
    , "__newBytesBuilder", "__bytesBuilderByte", "__bytesBuilderBytes"
    , "__finishBytesBuilder"
      -- §29.4 std.unicode (table-free): UTF-8 codec, scalars, byte/nat
    , "__utf8Bytes", "__utf8Valid", "__decodeUtf8Lossy", "__byteLength"
    , "__uniScalarValue", "__scalarInRange", "__scalarOfValue", "__scalarToString"
    , "__stringScalars", "__scalarCount", "__byteToNat", "__natToByte"
    , "__graphemeToString"
      -- §29.4 StringBuilder + string cursors + incremental UTF-8 decoder
    , "__newStringBuilder", "__stringBuilderString", "__stringBuilderScalar"
    , "__stringBuilderGrapheme", "__finishStringBuilder"
    , "__stringStart", "__stringEnd", "__stringCursorOffset", "__stringNextScalar"
    , "__stringPrevScalar", "__stringSpan", "__stringCompact"
    , "__newUtf8Decoder", "__decodeUtf8Chunk", "__finishUtf8Decoder"
      -- §29.4 table-driven Unicode (UAX#15 normalization, UAX#29 segmentation)
    , "__normalize", "__caseFold", "__stringGraphemes", "__graphemeCount"
    , "__graphemeValid", "__graphemeOfString", "__stringNextGrapheme"
    , "__stringWords", "__stringSentences"
      -- §29.1 std.atomic bitwise + repr-equality + §29.3 std.hash FNV-1a
    , "__intAnd", "__intOr", "__intXor", "__atomicRepEq"
    , "__hashMixInt", "__hashMixDouble", "__hashMixString", "__hashMixBytes"
      -- §20 collection carriers / §28.2 transport / range enumeration
    , "__queryFromList", "__queryToList", "__setFromList", "__setToList"
    , "__arrayFromList", "__arrayToList", "__mapFromEntries", "__mapToList"
    , "__transport", "__arrayIndexUnsafe", "__rangeEnum", "unsafeConsume"
      -- §28.2 proof helper
    , "__absurd"
      -- IO
    , "printString", "printlnString", "ioPure", "ioBind", "ioThen", "throwIO", "catchIO", "finallyIO"
    , "__reraiseCause" -- §18.1.4 re-raise a full Cause; lowered to a krt2_reraise node (compileAppGlob), no primEntry
    , "__race", "__timeout" -- §18.1.6 lowered to krt2_race/krt2_timeout nodes (compileAppGlob), no primEntry
    , "withScope", "__interruptWait", "__interruptNoWait" -- §19.5/§18.1.4 lowered to krt2_* nodes (compileAppGlob)
    , "uninterruptible", "__mask", "poll" -- §18.1.12 masking; lowered to krt2_uninterruptible/krt2_mask/krt2_poll nodes (compileAppGlob)
    , "demonitor" -- §18.1.8 no-op; kpf_demonitor shim (primEntries)
    , "newRef", "readRef", "writeRef"
      -- §18.1.13 STM (single-agent: TVar = cell, `atomically` runs the action)
    , "newTVar", "readTVar", "writeTVar", "atomically", "retry", "stmBind", "stmPure"
      -- §18.1.4/.6/.9 concurrency node builders (CPS do-kernel)
    , "__forkRun", "__forkDaemon", "__awaitFiber", "cede", "__sleepForNanos"
    , "newPromise", "completePromise", "awaitPromiseExit"
      -- §18.1.8 structured scopes + monitors (CPS do-kernel, Stage 3)
    , "newScope", "forkIn", "shutdownScope", "monitor", "awaitMonitor"
    ]

-- | Compile the reachable closure of @main@ to a C translation unit.
-- @ffiPrims@ are the additional primitive names the linked FFI runtime
-- implements (empty for the no-FFI build).  Returns @Left errs@ when any
-- reachable definition uses an unsupported construct (the caller renders
-- these as 'E_BACKEND_UNSUPPORTED'), or @Right csource@ on success.
generateC :: CheckState -> GName -> Set Text -> Map GName ResolvedNativeSymbol -> Either [BackendError] Text
generateC cs mainG ffiPrims hostSyms =
  let st0 =
        GenState
          { gsFresh = 0
          , gsStmts = []
          , gsEnv = "0"
          , gsParamLvals = []
          , gsTop = []
          , gsProtos = []
          , gsEmitted = Set.singleton mainG
          , gsQueue = [mainG]
          , gsErrs = []
          , gsCur = mainG
          , gsGlobals = csGlobals cs
          , gsEvalCtx = EvalCtx (Globals (csGlobals cs)) (csMetas cs) False (csFacts cs)
          , gsBodies = csCoreBodies cs
          , gsSuspenders = suspenderGlobals (csCoreBodies cs)
          , gsCtors = csCtors cs
          , gsDatas = Map.keysSet (csDatas cs)
          , gsTraits = Map.keysSet (csTraits cs)
          , gsDeclSites = csDeclSites cs
          , gsPrims = Set.union basePrims ffiPrims
          , gsPrimUsed = Set.empty
          , gsHostSyms = hostSyms
          , gsHostUsed = Set.empty
          , gsBounceMemo = Map.empty
          , gsLoops = []
          , gsDefer = []
          , gsScopeDefers = []
          , gsDeferLabels = []
          , gsScalars = Map.empty
          , gsScalarRegion = False
          , gsCpsRefRegion = False
          , gsI64Escape = "*kovf = 1; return 0;"
          , gsCollectCtors = Set.empty
          , gsCollectVars = Set.empty
          }
      final = execState (drainQueue >> emitMain mainG) st0
   in case reverse (gsErrs final) of
        [] -> Right (assemble final)
        errs -> Left errs

-- | Emit globals until the work queue is empty.
drainQueue :: Gen ()
drainQueue = do
  q <- gets gsQueue
  case q of
    [] -> pure ()
    (g : rest) -> do
      modify' $ \st -> st {gsQueue = rest}
      emitGlobal g
      drainQueue

-- | Emit one global's accessor function (memoised so recursion and CAF
-- sharing terminate and are evaluated once).
emitGlobal :: GName -> Gen ()
emitGlobal g = do
  modify' $ \st -> st {gsCur = g}
  bodies <- gets gsBodies
  let ident = cGlobIdent g
  modify' $ \st -> st {gsProtos = ("static KValue *" <> ident <> "(void);") : gsProtos st}
  -- A global reaches here only after compileGlob has ruled out a primitive,
  -- a host intrinsic, and a constructor, so a missing core body means a
  -- type-level / opaque / type-alias reference (e.g. `type Int = Integer`,
  -- or an opaque builtin type used as a value).  These are computationally
  -- erased (§12.2, §31.2) — their accessor yields the unit placeholder, the
  -- same inert value the interpreter never inspects — so an accepted program
  -- that mentions such a name compiles rather than being refused.  (Trait
  -- dictionaries and derived projections DO have recorded core bodies via
  -- recordCoreBody, so they take the Just branch below.)
  case Map.lookup g bodies of
    Nothing -> do
      -- Erase to the unit placeholder ONLY for a genuinely type-level / opaque
      -- global (a data\/trait name or a sort-typed builtin like @Integer@).  A
      -- real value-typed global with no recorded core body is NOT erasable —
      -- silently substituting unit would miscompile it (e.g. a top-level
      -- prefixed binding before recordCoreBody covered it).  Such a case is a
      -- backend gap, surfaced honestly rather than mis-lowered.
      typeLevel <- isTypeGlob g
      placeholder <-
        if typeLevel
          then pure "kunit()"
          else
            unsupported "definition"
              ( "'" <> gKey g <> "' has no recorded core body and is not a "
                  <> "type-level global, so it cannot be lowered (no-core-body)"
              )
      (stmts, _) <- captured "0" (pure ())
      finishGlobal ident stmts placeholder
    Just tm -> do
      -- A global whose body is a type-level / staging term (a `Type`-typed
      -- or `Syntax`-typed definition) is computationally erased (§12.2,
      -- §31.2): its accessor yields the unit placeholder, exactly as the
      -- interpreter's value for it is never inspected at runtime.  This is
      -- the by-name counterpart of the erasure that 'compileErasableArg'
      -- applies to inline type-level/quote arguments.
      erasable <- isErasableArg tm
      if erasable
        then do
          (stmts, _) <- captured "0" (pure ())
          finishGlobal ident stmts "kunit()"
        else case funcArity tm of
          -- A function global is lowered to a worker (a loop, so a tail
          -- self-call runs in constant C stack) plus a curried closure for
          -- partial application and first-class use.
          (n, inner) | n >= 1 -> compileFunctionGlobal g n inner
          _ -> do
            (stmts, e) <- captured "0" (compile tm)
            finishGlobal ident stmts e

-- | The leading-lambda arity of a term and the body beneath those binders.
funcArity :: Term -> (Int, Term)
funcArity = go 0
  where
    go !n (CLam _ _ _ b) = go (n + 1) b
    go !n t = (n, t)

-- | Does this worker body create a heap value that captures the enclosing
-- environment BY REFERENCE (a closure\/thunk\/do-action\/recursive let)?  If
-- so, the QW2 in-place parameter-cell update is UNSAFE: such a value can
-- escape one loop iteration (returned, consed into a list, deferred, …) and a
-- later @cell->val =@ mutation would overwrite the snapshot it must observe,
-- diverging from the interpreter (which evaluates each recursive call in a
-- fresh environment).  When this holds the worker rebuilds the parameter env
-- each iteration instead (the pre-QW2 behaviour, correct for escaping
-- closures).  Conservative: ANY such construct anywhere in the body disables
-- the in-place loop, even if that particular closure does not actually escape.
bodyCapturesEnv :: Term -> Bool
bodyCapturesEnv = go
  where
    go t = case t of
      CLam {} -> True -- kclo(fn, env)
      CLetRec {} -> True -- recursive closure captures the binder cell
      CDo {} -> True -- kio(fn, env)
      CThunkE {} -> True -- kthunk(fn, env, 0)  (Delay)
      CLazyE {} -> True -- kthunk(fn, env, 1)  (Memo)
      CQuote {} -> True -- conservative (erased, but never in a hot worker)
      -- P0-B: a saturated eta-expanded constructor application lowers to a
      -- direct 'kctor' (no 'kclo' over the env — see 'etaCtorApp'), so it
      -- captures its field VALUES, not the env, exactly like a 'CCtor'.
      -- Look through the eta lambdas to the real fields so this no longer
      -- forces the per-iteration env rebuild.
      CApp {} | Just (_, ctorArgs) <- etaCtorApp t -> any go ctorArgs
      CApp _ f a -> go f || go a
      CCtor _ _ args -> any go args
      CMatch s _ alts -> go s || any goAlt alts
      CProj e _ -> go e
      CProjAt e _ _ -> go e
      CInject _ e -> go e
      CForceE e -> go e
      CSealE _ e -> go e
      CLet _ _ ty rhs body -> go ty || go rhs || go body
      CIf c th el -> go c || go th || go el
      CRecordV fs -> any (go . snd) fs
      CRecordT fs -> any (go . snd) fs
      CVariantT ts -> any go ts
      CSigT _ e -> go e
      CPi _ _ _ _ a b -> go a || go b
      CVar {} -> False
      CGlob {} -> False
      CSort {} -> False
      CLit {} -> False
      CMeta {} -> False
    goAlt (CaseAlt _ mg body) = maybe False go mg || go body

-- | Lower a function global to: a worker @kw_…(p0,…,p{n-1})@ whose body is
-- a @while(1)@ loop (so a tail self-call reassigns the C parameters and
-- @continue@s instead of recursing in C — bounded C stack for tail
-- recursion), plus a curried arity-1 closure chain that collects the
-- arguments and calls the worker, returned by the accessor @kg_…()@.
--
-- Two modes (R2.3): when the body is capture-free ('bodyCapturesEnv' is
-- 'False'), the worker is FLAT — parameters are the C parameters read directly
-- (via 'gsParamLvals'), and @let@/@match@-bound locals are plain C locals
-- (R2.3-rest), so NO @KEnv@ is built at all.  When the body captures the env by
-- reference (a closure\/thunk\/do that can escape an iteration), the env is
-- REBUILT at the loop top from the reassigned C params (so each iteration's
-- escaping closures capture a distinct env, matching the interpreter) and
-- variables are read via @kvar@.
compileFunctionGlobal :: GName -> Int -> Term -> Gen ()
compileFunctionGlobal g n inner = do
  let ident = cGlobIdent g
      worker = "kw_" <> mangle (gKey g)
      ps = ["p" <> T.pack (show i) | i <- [0 .. n - 1]]
      inPlace = not (bodyCapturesEnv inner)
      -- R2.3 FLAT frame: a CAPTURE-FREE body reads parameters directly from the
      -- C parameters (no KEnv node, no kvar chain walk); a tail self-call
      -- reassigns the C params in place (like rebuild mode, but with no env to
      -- rebuild).  Strict subset of the QW2 in-place case.  A capture-free body
      -- can only bind via `let`/`match` (CLetRec/CDo/CLam are env-capturing, so
      -- excluded) — those push C locals onto 'gsParamLvals' (R2.3-rest), so no
      -- KEnv is needed for binder-bearing bodies either.
      flat = inPlace
      -- Two worker modes: FLAT (capture-free) reads params as direct C locals
      -- (gsParamLvals) with NO KEnv; REBUILD (capturing) rebuilds kw_env at the
      -- loop top each iteration and reads via kvar.  Both reassign the C params
      -- on a tail self-call (slots=ps) — so the in-place QW2 KEnv-cell mode is
      -- subsumed by FLAT (which keeps no KEnv at all).
      ti = TailInfo g n ps
      -- rebuild mode: rebuild kw_env at the loop top from the C params.
      envExpr = foldl (\acc p -> "kpush(" <> p <> ", " <> acc <> ")") "0" ps
      loopTopEnv
        | flat = [] -- FLAT: params are direct C locals, no KEnv
        | otherwise = ["    KEnv *kw_env = " <> envExpr <> "; (void)kw_env;"]
      paramDecls = T.intercalate ", " ["KValue *" <> p | p <- ps]
  -- In a flat worker, a CVar resolves to its C parameter (gsParamLvals), and a
  -- let/match binding prepends a C local; the mapping is reset for a capturing
  -- worker so CVar/binders fall back to kvar/kpush.  (A flat body has no
  -- env-capturing form, so a lifted closure can never read it.)
  saved <- gets gsParamLvals
  modify' $ \st -> st {gsParamLvals = if flat then reverse ps else []}
  (bodyStmts, ()) <- captured "kw_env" (consume (SinkTail ti) inner)
  modify' $ \st -> st {gsParamLvals = saved}
  let workerFn =
        T.unlines $
          ["static KValue *" <> worker <> "(" <> paramDecls <> ") {"]
            ++ ["  while (1) {"]
            ++ loopTopEnv
            ++ map ("    " <>) bodyStmts
            ++ [ "  }"
               , "}"
               ]
  emitTop ("static KValue *" <> worker <> "(" <> paramDecls <> ");") workerFn
  -- curried closure chain clo_0 … clo_{n-1}; clo_{n-1} calls the worker.
  cloNames <- mapM (\i -> freshFn ("kclo" <> T.pack (show i) <> "_")) [0 .. n - 1]
  forM_ (zip [0 ..] cloNames) $ \(i, nm) -> do
    let body
          | i < n - 1 =
              "  return kclo(" <> (cloNames !! (i + 1)) <> ", kpush(arg, cenv));"
          | otherwise =
              -- saturating call: p{n-1} = arg; p_j = kvar(cenv, n-2-j)
              let collected = [ "kvar(cenv, " <> T.pack (show (n - 2 - j)) <> ")" | j <- [0 .. n - 2] ]
                  callArgs = T.intercalate ", " (collected ++ ["arg"])
               in "  return " <> worker <> "(" <> callArgs <> ");"
        fn =
          T.unlines
            [ "static KValue *" <> nm <> "(KEnv *cenv, KValue *arg) {"
            , "  (void)cenv; (void)arg;"
            , body
            , "}"
            ]
    emitTop ("static KValue *" <> nm <> "(KEnv *, KValue *);") fn
  -- accessor: the memoised curried closure value (its forward declaration
  -- was already emitted by 'emitGlobal').
  let accessor =
        T.unlines
          [ "static KValue *" <> ident <> "(void) {"
          , "  static KValue *cache = 0; if (cache) return cache;"
          , "  cache = kclo(" <> head cloNames <> ", 0);"
          , "  return cache;"
          , "}"
          ]
  modify' $ \st -> st {gsTop = accessor : gsTop st}
  -- LR1/R2.2: if g is a monomorphic first-order scalar function (Int and/or
  -- Double params + scalar result) with a scalar-expressible body, ALSO emit
  -- the typed unboxed worker beside the boxed kw_g.
  mplan <- scalarPlan g
  case mplan of
    Just (pks, ret) -> compileScalarWorker g pks ret inner
    Nothing -> pure ()

-- ── LR1/R2.2: typed unboxed scalar workers (int64 / double) ──────────────
-- A first-order monomorphic SCALAR function — parameters and result each
-- Int/Nat/Integer (→ @int64_t@) or Float/Double (→ @double@), read from
-- @gdType@ — with a scalar-EXPRESSIBLE body gets an auxiliary unboxed worker
-- beside the boxed @kw_g@: typed scalar params + a while-loop for tail
-- self-calls (no @KEnv@/@kvar@/box per iteration).  A saturated direct call
-- (compileScalarCall) unboxes each arg BY ITS KIND and, on a wrong-tag arg
-- (kunbox_i64/kunbox_dbl escape) OR an int64 overflow, sets @kovf@ and re-runs
-- the BOXED worker from the ORIGINAL boxed args — so the boxed/GMP path is
-- always the reference result (the unbox tag-check is the soundness net: even
-- a mis-derived kind escapes to boxed, never miscompiles).  @kw_g@, the
-- closure chain, and the accessor are unchanged; the unboxed worker is reached
-- only from the saturated fast path.  Body grammar (conservative allowlist;
-- else ⇒ boxed-only): a scalar literal, a param/var, the int arith prims
-- (add/sub/mul/div/mod/neg)Int (overflow-escaped), the double arith prims
-- (add/sub/mul/div/neg)Double (plain IEEE, no escape — wraps to ±inf/NaN like
-- the boxed prim), @intToDouble@ (an int→double cast), the safe compares
-- (eq/lt/le)Int and ltDouble/floatEq ONLY as an @if@ condition, @if@ in tail
-- position, and SATURATED self-calls.  (CLet and @if@ in value position are
-- deferred — they make a body ineligible, never miscompiled.  @eqDouble@ is
-- EXCLUDED: it is §6.1.3 raw-bit equality, not C @==@; @leDouble@ has no
-- runtime prim.)

-- | The scalar kind of a worker parameter / result: an unboxed @int64_t@ or
-- @double@.
data ScalarKind = KInt64 | KDouble deriving (Eq)

-- | The C type for a scalar kind.
cScalarTy :: ScalarKind -> Text
cScalarTy KInt64 = "int64_t"
cScalarTy KDouble = "double"

-- | Box a raw scalar C value back into a @KValue@ by its kind.
boxScalar :: ScalarKind -> Text -> Text
boxScalar KInt64 e = "kint(" <> e <> ")"
boxScalar KDouble e = "kdbl(" <> e <> ")"

-- | Unbox a @KValue@ argument to a raw scalar by its kind, escaping (setting
-- @ovf@) on a wrong tag — the soundness net for the typed worker.
unboxScalar :: ScalarKind -> Text -> Text -> Text
unboxScalar KInt64 box ovf = "kunbox_i64(" <> box <> ", &" <> ovf <> ")"
unboxScalar KDouble box ovf = "kunbox_dbl(" <> box <> ", &" <> ovf <> ")"

-- | R2.4: a worker parameter slot is either an unboxed scalar (int64/double) or
-- a boxed @KValue *@ passed through verbatim (a record/ADT/etc. param that is
-- not scalar but whose scalar FIELDS may be read+coerced).  An all-@PScalar@
-- worker is the LR1/R2.2 case (byte-identical @kwi_@/@kwd_@ output); a worker
-- with any @PBoxed@ slot is a MIXED worker (@kwm_@).
data ParamKind = PScalar !ScalarKind | PBoxed deriving (Eq)

-- | The C type for a parameter slot.
cParamTy :: ParamKind -> Text
cParamTy (PScalar k) = cScalarTy k
cParamTy PBoxed = "KValue *"

-- | The scalar kind of a slot, or 'Nothing' for a boxed slot.
paramSK :: ParamKind -> Maybe ScalarKind
paramSK (PScalar k) = Just k
paramSK PBoxed = Nothing

-- | A scalar arith prim, with its (result kind, argument kinds).  @intToDouble@
-- is the one cross-kind coercion (int → double, emitted as a C cast).
arithPrim :: Text -> Maybe (ScalarKind, [ScalarKind])
arithPrim = \case
  "addInt" -> Just (KInt64, [KInt64, KInt64])
  "subInt" -> Just (KInt64, [KInt64, KInt64])
  "mulInt" -> Just (KInt64, [KInt64, KInt64])
  "divInt" -> Just (KInt64, [KInt64, KInt64])
  "modInt" -> Just (KInt64, [KInt64, KInt64])
  "negInt" -> Just (KInt64, [KInt64])
  "addDouble" -> Just (KDouble, [KDouble, KDouble])
  "subDouble" -> Just (KDouble, [KDouble, KDouble])
  "mulDouble" -> Just (KDouble, [KDouble, KDouble])
  "divDouble" -> Just (KDouble, [KDouble, KDouble])
  "negDouble" -> Just (KDouble, [KDouble])
  "intToDouble" -> Just (KDouble, [KInt64])
  _ -> Nothing

-- | A scalar comparison usable as an @if@ condition: (C operator, operand
-- kind).  ONLY comparisons whose C operator EXACTLY matches the runtime prim:
-- the int compares, @ltDouble@ (IEEE @<@) and @floatEq@ (IEEE @==@).
-- @eqDouble@ is excluded — §6.1.3 raw-bit equality differs from C @==@ on NaN
-- and signed zero; @leDouble@ has no runtime prim to mirror.
cmpPrim :: Text -> Maybe (Text, ScalarKind)
cmpPrim = \case
  "eqInt" -> Just ("==", KInt64)
  "ltInt" -> Just ("<", KInt64)
  "leInt" -> Just ("<=", KInt64)
  "ltDouble" -> Just ("<", KDouble)
  "floatEq" -> Just ("==", KDouble)
  _ -> Nothing

-- | A saturated self-call: spine head is the worker's own global @self@ with
-- exactly @n@ explicit args (FULL GName equality, like 'selfTailArgs').
lr1SelfArgs :: GName -> Int -> Term -> Maybe [Term]
lr1SelfArgs self n term = case spineOf term of
  (CGlob g, sargs)
    | g == self, expl <- [a | (Expl, a) <- sargs], length expl == n -> Just expl
  _ -> Nothing

andM :: [Gen Bool] -> Gen Bool
andM = foldr (\m acc -> do b <- m; if b then acc else pure False) (pure True)

orM :: [Gen Bool] -> Gen Bool
orM = foldr (\m acc -> do b <- m; if b then pure True else acc) (pure False)

-- | Strip leading lambdas, recording each binder's (icity, quantity).
stripLamsQ :: Term -> ([(Icit, Q)], Term)
stripLamsQ = go []
  where
    go acc (CLam ic q _ b) = go ((ic, q) : acc) b
    go acc t = (reverse acc, t)

-- | The per-parameter scalar kinds and result kind of @g@ IF it is eligible
-- for an unboxed worker: a recorded body of @n@ explicit relevant binders, a
-- scalar type telescope of exactly @n@ runtime params + a scalar result, and a
-- scalar-expressible body.  @Nothing@ ⇒ boxed-only (never a miscompile).
-- | §6/§7 Stage 1.5 — the SUSPENDABILITY WITNESS that gates the unboxed scalar
-- worker.  A scalar worker keeps its values in raw C locals (@double@/@int64_t@);
-- those locals are absent from the @KEnv@ chain and the continuation @f->k@, so a
-- fiber park (await/fork/race/timeout/atomically/STM retry) at any point where a
-- raw scalar is live would LOSE it on resume (CPS-DESIGN R5) — a silent
-- miscompile, no crash.  So a worker may be emitted ONLY for a body that PROVABLY
-- does not may-suspend.  Returns @True@ if the body MAY suspend; the witness
-- ERRS TOWARD may-suspend (unknown ⇒ True ⇒ refuse the worker ⇒ stay boxed):
--
--   * a spine head that is a suspending primitive ('isSuspendingPrim') or a
--     global in the transitive §3.3 suspender closure ('gsSuspenders');
--   * an opaque higher-order call whose spine head is a local/param 'CVar'
--     (may suspend depending on the value passed — §6 "effect-polymorphic /
--     opaque-higher-order ⇒ may-suspend");
--
-- Today the arithmetic-only body grammar ('scalarEligTail'/'scalarKindOf')
-- already makes a scalar body suspension-free *implicitly* (no admitted form
-- is an IO/suspending op, and a non-scalar result kind already rejects every
-- @UIO a@ function).  This witness makes that property EXPLICIT and INDEPENDENT
-- so it survives the Stage-2a-pre widening to @let@/@match@ (which CAN carry a
-- suspending sub-term) and is the named soundness gate of §7 Stage 1.5 — not an
-- emergent accident of the allowlist.  It walks the WHOLE body (not just the
-- tail spine), recursing into @if@ branches and every prim/self-call argument,
-- because a suspension anywhere a raw scalar is live is unsound — not only in
-- tail position.
scalarBodyMaySuspend :: Set GName -> Term -> Bool
scalarBodyMaySuspend susp = go
  where
    -- a call's spine head decides suspendability for this node; the arguments
    -- are then walked too (a suspending op can hide in an argument position).
    -- Only an APPLICATION counts as a call here — a bare 'CVar'/'CGlob' LEAF
    -- (a value read, not an invocation) cannot itself park, so it is never
    -- flagged (else every scalar var read would falsely read as may-suspend).
    headSusp t = case t of
      CApp {} -> case fst (spineOf t) of
        CGlob h -> isSuspendingPrim h || h `Set.member` susp
        CVar _ -> True -- opaque higher-order call: may suspend (conservative)
        _ -> False
      _ -> False
    go t =
      headSusp t || case t of
        CIf c th el -> go c || go th || go el
        CApp _ a b -> go a || go b
        CMatch s _ alts -> go s || any (\a -> maybe False go (caGuard a) || go (caBody a)) alts
        CLet _ _ _ rhs body -> go rhs || go body
        CLetRec _ _ _ rhs body -> go rhs || go body
        CDo _ _ -> True -- a do-block is an IO action: conservatively may-suspend
        CCtor _ _ as -> any go as
        CSealE _ e -> go e
        CSigT _ e -> go e
        CForceE e -> go e
        CThunkE e -> go e
        CLazyE e -> go e
        CInject _ e -> go e
        CProj e _ -> go e
        CProjAt e _ _ -> go e
        _ -> False

scalarPlan :: GName -> Gen (Maybe ([ParamKind], ScalarKind))
scalarPlan g = do
  bodies <- gets gsBodies
  susp <- gets gsSuspenders
  case Map.lookup g bodies of
    Nothing -> pure Nothing
    Just body -> do
      let (binders, inner) = stripLamsQ body
          n = length binders
      -- all binders explicit + relevant: an implicit/erased binder is passed
      -- kunit() (compileErasableArg), which a scalar worker must never read.
      if n >= 1 && all (\(ic, q) -> ic == Expl && q /= Q0) binders
        then do
          mkinds <- typeScalarKinds g n
          case mkinds of
            -- require at least one unboxed scalar param (else there is nothing
            -- to win — an all-boxed body stays on the boxed/flat path).
            Just (pks, ret) | any (/= PBoxed) pks -> do
              -- §7 Stage 1.5 SOUNDNESS GATE (before the body grammar check): a
              -- worker whose body may suspend would lose its raw-scalar C locals
              -- across a park (§6).  Refuse it (→ boxed) — never miscompile.
              -- Gates on BOTH the global's own transitive suspender membership
              -- (g ∈ gsSuspenders) and a per-body walk for an inlined/opaque
              -- suspending sub-term, so it stays sound once locals widen.
              ok <- scalarEligTail g pks ret inner
              let mayParK = g `Set.member` susp || scalarBodyMaySuspend susp inner
              pure (if ok && not mayParK then Just (pks, ret) else Nothing)
            _ -> pure Nothing
        else pure Nothing

-- | Read @g@'s per-parameter kinds (unboxed scalar or boxed) and its (scalar)
-- result kind from its elaborated type (quoted to a Term Pi telescope).  A
-- non-scalar param domain is 'PBoxed' (R2.4 mixed worker — kept boxed,
-- passed through); the RESULT must be scalar (a boxed-result worker is not
-- eligible in this slice).  The count-match against @n@ (the body's structural
-- binder count) is a HARD guard: a disagreement (point-free style, an
-- unfoldable type alias, a function-typed result) yields @Nothing@, so a kind
-- is never assigned to the wrong binder.
typeScalarKinds :: GName -> Int -> Gen (Maybe ([ParamKind], ScalarKind))
typeScalarKinds g n = do
  globals <- gets gsGlobals
  ctx <- gets gsEvalCtx
  pure $ case Map.lookup g globals of
    Nothing -> Nothing
    Just gd -> do
      -- KBackendIR Stage 3: rep selection is 'Repr.repSelect' — the single
      -- authority that walks the type telescope and classifies every relevant
      -- explicit param + the result as int/double/boxed.  This backend's
      -- @ParamKind@/@ScalarKind@ are just the projection of that 'Rep' plan:
      -- the per-param 'Rep' becomes a 'PScalar'/'PBoxed' slot, and the RESULT
      -- 'Rep' must be a scalar (a boxed-result worker is not eligible in this
      -- slice — so a non-scalar result rep yields @Nothing@).
      (paramReps, retRep) <- Repr.repSelect ctx (gdType gd)
      ret <- repScalarKind retRep
      let pks = map paramRepKind paramReps
      if length pks == n then Just (pks, ret) else Nothing
  where
    -- A param slot is an unboxed scalar (int/double) or a boxed pass-through
    -- (R2.4 mixed worker) for any non-scalar rep.
    paramRepKind r = maybe PBoxed PScalar (repScalarKind r)

-- | The unboxed scalar kind of a 'Repr.Rep', or 'Nothing' for a rep that has no
-- unboxed scalar representation (boxed / immediate-ctor).  This is the
-- backend-local projection of the shared rep classification onto this backend's
-- two-element @ScalarKind@ (the only reps it unboxes today).
repScalarKind :: Repr.Rep -> Maybe ScalarKind
repScalarKind = \case
  Repr.RepInt -> Just KInt64
  Repr.RepDouble -> Just KDouble
  _ -> Nothing

-- | For a global head @g@, the per-spine-position erasure flags read from its
-- elaborated type's Pi telescope: @True@ at a binder whose quantity is 'Q0'
-- (computationally erased, §31.2), @False@ otherwise.  The list runs in
-- telescope order, which 'spineOf' lists arguments in (binder @k@ ↔ spine
-- position @k@); spine positions past the telescope (a result that is itself a
-- function value, applied further) get @False@.
--
-- This is the FIX for the interp-vs-native divergence on @sequence@ /
-- @sequence_@ / @for_@ / @traverse@ over IO: an ERASED type argument that is a
-- type-level APPLICATION @f a@ (a 'CApp' whose head is a type VARIABLE) is
-- otherwise lowered as a real runtime @kapp(kvar f, kvar a)@ over two
-- unit-valued (erased) slots, because the purely SYNTACTIC 'isErasableArg'
-- only inspects the spine head ('CVar' → @False@).  The interpreter keeps type
-- arguments as applicable values so it never crashes; the C/LLVM backends
-- crash with @kapp: applying a non-function value@.  Erasing by the binder's
-- 'Q0' QUANTITY — the elaborator's own irrelevance verdict — is syntax-blind
-- and so erases the application form too.  Unlike 'typeScalarKinds' (explicit
-- value binders only), this walks the WHOLE telescope, since an erased
-- argument can sit at an implicit OR explicit position.
-- The pure core ('erasedSpinePositionsP' / 'eraseQ0ArgsP') is exported so the
-- LLVM backend ("Kappa.Backend.LLVM") shares the SAME erasure verdict (its 'Gen'
-- monad is a distinct type, so it cannot call the monadic wrappers — but it has
-- the same 'gsGlobals' / 'gsEvalCtx' to feed the pure version).
erasedSpinePositions :: GName -> Gen [Bool]
erasedSpinePositions g = do
  globals <- gets gsGlobals
  ctx <- gets gsEvalCtx
  pure (erasedSpinePositionsP globals ctx g)

-- | The pure spine-erasure analysis (see 'erasedSpinePositions').
-- FAIL-SAFE: an unknown global, or a 'gdType' that does not 'force' to a 'VPi'
-- telescope (an unsolved-meta/thunk head), yields @[]@ — i.e. nothing is flagged.
-- That can only UNDER-erase (miss a position), never over-erase: a missed
-- type-application position reverts to the original @kapp(unit,unit)@ crash, but
-- a dictionary or runtime value is never wrongly dropped.
erasedSpinePositionsP :: Map GName GlobalDef -> EvalCtx -> GName -> [Bool]
erasedSpinePositionsP globals ctx g =
  case Map.lookup g globals of
    Nothing -> []
    Just gd -> walk 0 (gdType gd)
  where
    walk lvl ty =
      case force ctx ty of
        VPi _ q _ _ dom clo ->
          (q == Q0 || isKindDomain lvl dom) : walk (lvl + 1) (closApply lvl clo)
        _ -> []
    closApply lvl (Closure env body) = eval ctx (VRigid lvl [] : env) body
    -- A parameter whose DOMAIN is a kind (@Type@, or @A -> … -> Type@) is a type
    -- or type constructor: it is RuntimeErased (Spec §1.1.1 — types carry no
    -- runtime representation; §11.4 — there is no typecase), so it is erasable
    -- REGARDLESS of its quantity (a type argument need not be 'Q0').  This is the
    -- broader half of the verdict: 'Q0' alone caught the type args that happened
    -- to be quantity-zero, but a non-'Q0' type *application* @f a@ would still
    -- crash as @kapp(unit,unit)@.  Crucially this NEVER erases a dictionary: a
    -- dict's domain is a trait type @C a : Type@ — an inhabitant of a kind, not a
    -- kind — so 'isKindDomain' is False for it (Spec §14.4: @IsTrait@ does not
    -- imply @RuntimeErased@; a method projection is runtime-relevant).  Proofs of
    -- a 'RuntimeErased'/'IsProp' proposition are likewise erasable, but at a
    -- non-'Q0' position that needs the elaborator's IsProp evidence (not re-derived
    -- here); the common Q0 proof position is already covered above.  Mirrors
    -- 'Kappa.Check.isKindLike'.
    isKindDomain lvl v =
      case force ctx v of
        VSort _ -> True
        VPi _ _ _ _ _ clo -> isKindDomain (lvl + 1) (closApply lvl clo)
        _ -> False

-- | Rewrite a global-headed application @g a0 a1 …@ so each argument at an
-- ERASED (Q0 OR type-level/kind-domain) telescope position becomes a 'CSort'
-- placeholder — see
-- 'erasedSpinePositions' for the why.  The icities are preserved (an erased arg
-- can be implicit or explicit); the placeholder is then erased to @kunit()@ by
-- the existing 'compileErasableArg' path, with no new threading.  Positions past
-- the telescope keep their original term.
eraseQ0Args :: GName -> Term -> Gen Term
eraseQ0Args g term = do
  globals <- gets gsGlobals
  ctx <- gets gsEvalCtx
  pure (eraseQ0ArgsP globals ctx g term)

-- | The pure spine rewrite (see 'eraseQ0Args').
eraseQ0ArgsP :: Map GName GlobalDef -> EvalCtx -> GName -> Term -> Term
eraseQ0ArgsP globals ctx g term =
  let flags = erasedSpinePositionsP globals ctx g
      (hd, sargs) = spineOf term
      go _ [] = []
      go (er : ers) ((ic, a) : rest) = (ic, if er then CSort 0 else a) : go ers rest
      go [] rest = rest -- spine longer than the telescope: leave the tail as-is
      sargs' = go flags sargs
   in foldl (\f (ic, a) -> CApp ic f a) hd sargs'

-- KBackendIR Stage 3: the head-type → scalar-representation discriminator is
-- 'Repr.scalarRep' / 'Repr.repSelect' (the shared rep table); this backend's
-- @ScalarKind@ is the @RepInt@/@RepDouble@ projection of it ('repScalarKind').
-- 'typeScalarKinds' consumes 'Repr.repSelect' directly, so the standalone
-- head-discriminator wrapper that used to live here is gone — its only caller
-- was the param/result classification now derived from the shared rep plan.

-- | Eligibility of a tail-position term against the worker's return kind: an
-- @if@ (safe-compare condition, eligible branches), a saturated self-call
-- (each arg checks against the corresponding PARAM kind), or a leaf value
-- whose kind equals the return kind.
scalarEligTail :: GName -> [ParamKind] -> ScalarKind -> Term -> Gen Bool
scalarEligTail g pks ret term = case term of
  CIf c t e -> andM [scalarEligCond g pks ret c, scalarEligTail g pks ret t, scalarEligTail g pks ret e]
  _
    | Just args <- lr1SelfArgs g (length pks) term -> andM (zipWith (selfArgElig g pks ret) pks args)
    | otherwise -> scalarHasKind g pks ret ret term

-- | A self-call argument is eligible iff: for a scalar param slot, the arg is a
-- value of that scalar kind; for a boxed param slot, the arg is a PASS-THROUGH
-- of a boxed param (a bare @CVar@ of a boxed slot) — the only boxed value the
-- mixed worker can supply without unboxing/rebuilding (R2.4 slice).
selfArgElig :: GName -> [ParamKind] -> ScalarKind -> ParamKind -> Term -> Gen Bool
selfArgElig g pks ret pk arg = case pk of
  PScalar k -> scalarHasKind g pks ret k arg
  -- any boxed CVar into a boxed slot is fine: source type-checking already
  -- guarantees the self-call arg's type matches the param, and the runtime
  -- representation of every boxed slot is the uniform @KValue *@.
  PBoxed -> pure $ case arg of
    CVar j -> varParamKind pks j == Just PBoxed
    _ -> False

-- | Is @term@ a FIXED-OFFSET projection of a BOXED param (@krec_at(boxed,i)@)?
-- Its boxed field value can be coerced to any scalar kind by a tag-checked
-- unbox (R2.4), so it is admissible in any scalar position.  ONLY 'CProjAt'
-- (the P0.4 closed-record fixed-offset form, which codegen lowers to
-- @krec_at@) qualifies; a name-based 'CProj' (open/sealed record, dict member,
-- tuple ≥10) is NOT handled by the coercion codegen, so it must stay
-- ineligible here (→ boxed worker) rather than reach the worker and escalate
-- on a valid program.
isBoxedProj :: [ParamKind] -> Term -> Bool
isBoxedProj pks term = case term of
  CProjAt (CVar j) _ _ -> varParamKind pks j == Just PBoxed
  _ -> False

-- | Does the value-position @term@ have scalar kind @k@?  A projection of a
-- boxed param is coercible to any @k@ (a tag-checked unbox at codegen).
scalarHasKind :: GName -> [ParamKind] -> ScalarKind -> ScalarKind -> Term -> Gen Bool
scalarHasKind g pks ret k term
  | isBoxedProj pks term = pure True
  | otherwise = do
      mk <- scalarKindOf g pks ret term
      pure (mk == Just k)

-- | The scalar kind of a value-position expression, or @Nothing@ if it is not
-- scalar-expressible (every prim arg must match the prim's expected kind, so a
-- mixed-kind misuse such as @addInt acc n@ with @acc:Double@ is rejected, never
-- miscompiled).  A self-call's result is the worker's return kind.  A bare
-- @CVar@ of a BOXED param is NOT a scalar value (it is only usable as a
-- projection base — see 'isBoxedProj'), so it is @Nothing@ here.
scalarKindOf :: GName -> [ParamKind] -> ScalarKind -> Term -> Gen (Maybe ScalarKind)
scalarKindOf g pks ret term = case term of
  CLit (LitInt m)
    | m >= toInteger (minBound :: Int) && m <= toInteger (maxBound :: Int) -> pure (Just KInt64)
    | otherwise -> pure Nothing
  CLit (LitDouble _) -> pure (Just KDouble)
  CVar i -> pure (varParamKind pks i >>= paramSK)
  _ -> case spineOf term of
    (CGlob h, sargs) -> do
      let expl = [a | (Expl, a) <- sargs]
      mp <- globPrimName h
      case mp of
        Just p | Just (rk, argks) <- arithPrim p, length expl == length argks -> do
          oks <- sequence (zipWith (scalarHasKind g pks ret) argks expl)
          pure (if and oks then Just rk else Nothing)
        _
          | Just args <- lr1SelfArgs g (length pks) term -> do
              oks <- sequence (zipWith (selfArgElig g pks ret) pks args)
              pure (if and oks then Just ret else Nothing)
          | otherwise -> pure Nothing
    _ -> pure Nothing

-- | The kind of de Bruijn variable @i@ (env order: 0 = innermost = LAST
-- param), i.e. source param @n-1-i@; out of range ⇒ Nothing.
varParamKind :: [ParamKind] -> Int -> Maybe ParamKind
varParamKind pks i =
  let n = length pks
   in if i >= 0 && i < n then Just (pks !! (n - 1 - i)) else Nothing

-- | Eligibility of an @if@ condition: a saturated SAFE scalar compare whose
-- operands have the comparison's operand kind.
scalarEligCond :: GName -> [ParamKind] -> ScalarKind -> Term -> Gen Bool
scalarEligCond g pks ret term = case spineOf term of
  (CGlob h, sargs) -> do
    let expl = [a | (Expl, a) <- sargs]
    mp <- globPrimName h
    case (mp >>= cmpPrim, expl) of
      (Just (_, opk), [a, b]) -> andM [scalarHasKind g pks ret opk a, scalarHasKind g pks ret opk b]
      _ -> pure False
  _ -> pure False

-- | The unboxed worker name: keep @kwi_@ for an all-@int64@ worker (so existing
-- golden C is byte-stable); a worker with any @double@ param/result uses
-- @kwd_@.
scalarWorkerName :: GName -> [ParamKind] -> ScalarKind -> Text
scalarWorkerName g pks ret
  | any (== PBoxed) pks = "kwm_" <> mangle (gKey g) -- mixed boxed/unboxed (R2.4)
  | all (== PScalar KInt64) pks && ret == KInt64 = "kwi_" <> mangle (gKey g)
  | otherwise = "kwd_" <> mangle (gKey g)

-- | Emit the unboxed worker with per-slot param types + (scalar) return type,
-- e.g. @double kwd_g(double, int64_t, int *kovf)@ or, with a boxed slot,
-- @KValue *kwm_g(int64_t, KValue *, int64_t, int *kovf)@.
compileScalarWorker :: GName -> [ParamKind] -> ScalarKind -> Term -> Gen ()
compileScalarWorker g pks ret inner = do
  let n = length pks
      worker = scalarWorkerName g pks ret
      ps = ["p" <> T.pack (show i) | i <- [0 .. n - 1]]
      env = reverse ps -- de Bruijn 0 = innermost binder = the LAST param
      paramDecls = T.intercalate ", " (zipWith (\k p -> cParamTy k <> " " <> p) pks ps ++ ["int *kovf"])
  (bodyStmts, ()) <- captured "0" (scalarTail g pks ret ps env inner)
  let fn =
        T.unlines $
          [ "static " <> cScalarTy ret <> " " <> worker <> "(" <> paramDecls <> ") {"
          , "  while (1) {"
          ]
            ++ map ("    " <>) bodyStmts
            ++ [ "  }"
               , "}"
               ]
  emitTop ("static " <> cScalarTy ret <> " " <> worker <> "(" <> paramDecls <> ");") fn

-- | The C expression and type for one self-call argument: a scalar slot is
-- compiled to its scalar kind; a boxed slot is a pass-through of the boxed C
-- param (eligibility guarantees the arg is a bare @CVar@ of a boxed slot).
scalarSelfArg :: GName -> [ParamKind] -> ScalarKind -> [Text] -> ParamKind -> Term -> Gen (Text, Text)
scalarSelfArg g pks ret env pk a = case pk of
  PScalar k -> do e <- scalarExpr g pks ret env k a; pure (cScalarTy k, e)
  PBoxed -> case a of
    CVar j -> pure ("KValue *", env !! j)
    _ -> do e <- lr1Unreachable; pure ("KValue *", e)

-- | Compile the body in TAIL position: @if@ branches recurse in tail; a
-- saturated self-call reassigns the params (each temp typed by its slot kind)
-- and @continue@s (an in-place loop — no @KEnv@); any other (leaf, scalar)
-- expr is returned.
scalarTail :: GName -> [ParamKind] -> ScalarKind -> [Text] -> [Text] -> Term -> Gen ()
scalarTail g pks ret ps env term = case term of
  CIf c t e -> do
    cond <- scalarCond g pks ret env c
    (tb, ()) <- captured "0" (scalarTail g pks ret ps env t)
    (eb, ()) <- captured "0" (scalarTail g pks ret ps env e)
    emit ("if (" <> cond <> ") {")
    forM_ tb (emit . ("  " <>))
    emit "} else {"
    forM_ eb (emit . ("  " <>))
    emit "}"
  _
    | Just args <- lr1SelfArgs g (length pks) term -> do
        -- tail self-call: evaluate new args into typed temps FIRST (they may
        -- read current params), then reassign params and loop.
        temps <- forM (zip pks args) $ \(pk, a) -> do
          (cty, ae) <- scalarSelfArg g pks ret env pk a
          t <- freshN "ti_"
          emit (cty <> " " <> t <> " = " <> ae <> ";")
          pure t
        forM_ (zip ps temps) $ \(p, t) -> emit (p <> " = " <> t <> ";")
        emit "continue;"
    | otherwise -> do
        e <- scalarExpr g pks ret env ret term
        emit ("return " <> e <> ";")

-- | P0.2: if @term@ is a read of a scalarized var (@__runIO (readRef <var>)@,
-- the elaborator's auto-deref) while emitting the scalar loop region, the
-- int64 C local that shadows it; else 'Nothing'.  (For an unboxed scalar
-- worker 'gsScalarRegion' is false, so this never fires there.)
scalarReadOf :: Term -> Gen (Maybe Text)
scalarReadOf term = do
  region <- gets gsScalarRegion
  if not region
    then pure Nothing
    else case runIOSplice term of
      Just action -> case spineOf action of
        (CGlob h, sargs) -> do
          mp <- globPrimName h
          case (mp, [a | (Expl, a) <- sargs]) of
            (Just "readRef", [CVar idx]) -> do
              sc <- gets gsScalars
              pure (fst <$> Map.lookup idx sc)
            _ -> pure Nothing
        _ -> pure Nothing
      Nothing -> pure Nothing

-- | Compile a scalar-expressible value: a scalarized var read (P0.2), a
-- literal, a var, an arith op (int ops overflow-escaped, double ops plain
-- IEEE, @intToDouble@ a cast), or a (non-tail) self-call (whose @kovf@ is
-- propagated immediately).  Each int op that overflows sets @*kovf@ (or runs
-- 'gsI64Escape') and bails at once — never a wrapped value.
-- | Worker-side unbox of a boxed value to a scalar: the worker's escape flag is
-- the @int *kovf@ parameter (already a pointer), so pass it directly (unlike
-- 'unboxScalar' at a call site, which takes @&@ of a local int).
unboxWorker :: ScalarKind -> Text -> Text
unboxWorker KInt64 fb = "kunbox_i64(" <> fb <> ", kovf)"
unboxWorker KDouble fb = "kunbox_dbl(" <> fb <> ", kovf)"

-- | Compile a scalar-expressible value for the demanded scalar kind @dk@: a
-- scalarized var read (P0.2), a boxed-param field read coerced to @dk@ (R2.4),
-- a literal, a (scalar) param var, an arith op, or a (non-tail) self-call.
-- @dk@ is only consulted for the boxed-field coercion; everything else is
-- determined bottom-up (so all-scalar output is unaffected).
scalarExpr :: GName -> [ParamKind] -> ScalarKind -> [Text] -> ScalarKind -> Term -> Gen Text
scalarExpr g pks ret env dk term = do
  msc <- scalarReadOf term
  case msc of
    Just sloc -> pure sloc
    Nothing -> scalarExprBody g pks ret env dk term

scalarExprBody :: GName -> [ParamKind] -> ScalarKind -> [Text] -> ScalarKind -> Term -> Gen Text
scalarExprBody g pks ret env dk term
  -- R2.4: a record-field read of a BOXED param yields a boxed value; coerce it
  -- to the demanded scalar kind with a tag-checked unbox that escapes to the
  -- boxed worker on a wrong tag (so a non-Int/Double field never miscompiles).
  | CProjAt (CVar j) _ off <- term, isBoxedProj pks term = do
      fb <- freshN "fb_"
      emit ("KValue *" <> fb <> " = krec_at(" <> (env !! j) <> ", " <> T.pack (show off) <> ");")
      t <- freshN "ti_"
      emit (cScalarTy dk <> " " <> t <> " = " <> unboxWorker dk fb <> ";")
      emit "if (*kovf) return 0;"
      pure t
  | otherwise = case term of
      CLit (LitInt m) -> pure (cIntLit m)
      CLit (LitDouble d) -> pure (cDblLit d)
      CVar i -> pure (env !! i)
      _ -> case spineOf term of
        (CGlob h, sargs) -> do
          let expl = [a | (Expl, a) <- sargs]
          mp <- globPrimName h
          case mp of
            Just p | Just (_, argks) <- arithPrim p, length expl == length argks -> scalarArith g pks ret env p expl
            _
              | Just args <- lr1SelfArgs g (length pks) term -> do
                  aes <- mapM (\(pk, a) -> snd <$> scalarSelfArg g pks ret env pk a) (zip pks args)
                  t <- freshN "ti_"
                  emit (cScalarTy ret <> " " <> t <> " = " <> scalarWorkerName g pks ret <> "(" <> T.intercalate ", " (aes ++ ["kovf"]) <> ");")
                  emit "if (*kovf) return 0;"
                  pure t
              | otherwise -> lr1Unreachable
        _ -> lr1Unreachable

-- | Lower one scalar arith op.  Int ops mirror the @kp_*Int@ runtime helpers
-- exactly (§6 unbounded Integer promotes to GMP via the boxed escape; div/mod
-- by zero traps; INT64_MIN edges escape).  Double ops are plain IEEE (no
-- overflow/zero trap — they wrap to ±inf/NaN exactly like @kp_*Double@) and
-- match the boxed path's per-operation rounding: each op is emitted into its
-- own statement/temp, and the driver compiles with @-ffp-contract=off@
-- (Driver.hs), so the compiler cannot fuse a @mul@-then-@add@ into a
-- single-rounding FMA at any @-O@ level.  @intToDouble@ is a C cast (== the
-- prim's @(double)i@).
scalarArith :: GName -> [ParamKind] -> ScalarKind -> [Text] -> Text -> [Term] -> Gen Text
scalarArith g pks ret env p expl = do
  -- each arg is compiled for the prim's expected kind (so a boxed-field arg is
  -- coerced to the right scalar kind); arithPrim p is Just by the caller.
  let argks = maybe [] snd (arithPrim p)
  aes <- sequence (zipWith (\k a -> scalarExpr g pks ret env k a) argks expl)
  t <- freshN "ti_"
  esc <- gets gsI64Escape -- worker: `*kovf=1; return 0;`; scalar loop: flush+goto boxed
  case (p, aes) of
    ("addInt", [a, b]) -> emit ("int64_t " <> t <> "; if (__builtin_add_overflow(" <> a <> ", " <> b <> ", &" <> t <> ")) { " <> esc <> " }")
    ("subInt", [a, b]) -> emit ("int64_t " <> t <> "; if (__builtin_sub_overflow(" <> a <> ", " <> b <> ", &" <> t <> ")) { " <> esc <> " }")
    ("mulInt", [a, b]) -> emit ("int64_t " <> t <> "; if (__builtin_mul_overflow(" <> a <> ", " <> b <> ", &" <> t <> ")) { " <> esc <> " }")
    ("negInt", [a]) -> emit ("int64_t " <> t <> "; if (" <> a <> " == INT64_MIN) { " <> esc <> " } else " <> t <> " = -" <> a <> ";")
    ("divInt", [a, b]) -> emit ("if (" <> b <> " == 0) krt_fail(\"divInt: division by zero\"); int64_t " <> t <> "; if (" <> a <> " == INT64_MIN && " <> b <> " == -1) { " <> esc <> " } else " <> t <> " = " <> a <> " / " <> b <> ";")
    ("modInt", [a, b]) -> emit ("if (" <> b <> " == 0) krt_fail(\"modInt: division by zero\"); int64_t " <> t <> "; if (" <> a <> " == INT64_MIN && " <> b <> " == -1) " <> t <> " = 0; else " <> t <> " = " <> a <> " % " <> b <> ";")
    ("addDouble", [a, b]) -> emit ("double " <> t <> " = " <> a <> " + " <> b <> ";")
    ("subDouble", [a, b]) -> emit ("double " <> t <> " = " <> a <> " - " <> b <> ";")
    ("mulDouble", [a, b]) -> emit ("double " <> t <> " = " <> a <> " * " <> b <> ";")
    ("divDouble", [a, b]) -> emit ("double " <> t <> " = " <> a <> " / " <> b <> ";")
    ("negDouble", [a]) -> emit ("double " <> t <> " = -" <> a <> ";")
    ("intToDouble", [a]) -> emit ("double " <> t <> " = (double)" <> a <> ";")
    _ -> lr1UnreachableStmt
  pure t

-- | Compile an @if@ condition (a saturated safe scalar compare) to a C boolean
-- expr.  The C operator comes from 'cmpPrim', which admits only comparisons
-- whose C operator matches the runtime prim exactly.
scalarCond :: GName -> [ParamKind] -> ScalarKind -> [Text] -> Term -> Gen Text
scalarCond g pks ret env term = case spineOf term of
  (CGlob h, sargs) -> do
    let expl = [a | (Expl, a) <- sargs]
    mp <- globPrimName h
    case (mp >>= cmpPrim, expl) of
      (Just (op, opk), [a, b]) -> do
        ae <- scalarExpr g pks ret env opk a
        be <- scalarExpr g pks ret env opk b
        pure ("(" <> ae <> " " <> op <> " " <> be <> ")")
      _ -> lr1Unreachable
  _ -> lr1Unreachable

-- These are unreachable when 'scalarPlan' classified the body as eligible;
-- they record a backend error (never a silent miscompile) if an invariant
-- breaks.
lr1Unreachable :: Gen Text
lr1Unreachable = escalated "LR1-i64" "an int64-ineligible term reached the unboxed worker (LR1 eligibility invariant violated)"

lr1UnreachableStmt :: Gen ()
lr1UnreachableStmt = lr1Unreachable >> pure ()

-- | The saturated fast path at a call site: unbox each arg by its scalar kind,
-- call the unboxed worker, and escape to the boxed @kw_g@ (from the ORIGINAL
-- boxed args) on a wrong-tag arg or an int64 overflow.
compileScalarCall :: GName -> [ParamKind] -> ScalarKind -> [(Icit, Term)] -> Gen Text
compileScalarCall g pks ret sargs = do
  let worker = scalarWorkerName g pks ret
      kw = "kw_" <> mangle (gKey g)
  aes <- mapM (compileErasableArg . snd) sargs
  ts <- forM aes $ \ae -> do
    t <- freshN "la_"
    emit ("KValue *" <> t <> " = " <> ae <> ";")
    pure t
  ovf <- freshN "kovf_"
  emit ("int " <> ovf <> " = 0;")
  -- scalar slots unbox (tag-checked → escape); boxed slots pass through.
  avs <- forM (zip pks ts) $ \(pk, t) -> case pk of
    PScalar k -> do
      av <- freshN "lu_"
      emit (cScalarTy k <> " " <> av <> " = " <> unboxScalar k t ovf <> ";")
      pure av
    PBoxed -> pure t
  r <- freshN "lr_"
  res <- freshN "lres_"
  let boxed = "ktrampoline(" <> kw <> "(" <> T.intercalate ", " ts <> "))"
  emit ("KValue *" <> res <> ";")
  -- a wrong-tag arg short-circuits to boxed WITHOUT calling the unboxed worker
  -- (so it never runs on garbage 0-args, e.g. a spurious /0 trap).
  emit ("if (" <> ovf <> ") { " <> res <> " = " <> boxed <> "; }")
  emit "else {"
  emit ("  " <> cScalarTy ret <> " " <> r <> " = " <> worker <> "(" <> T.intercalate ", " (avs ++ ["&" <> ovf]) <> ");")
  emit ("  " <> res <> " = " <> ovf <> " ? " <> boxed <> " : " <> boxScalar ret r <> ";")
  emit "}"
  pure res

-- | Append a forward declaration + a completed top-level C function.
emitTop :: Text -> Text -> Gen ()
emitTop proto fn = modify' $ \st -> st {gsTop = fn : gsTop st, gsProtos = proto : gsProtos st}

finishGlobal :: Text -> [Text] -> Text -> Gen ()
finishGlobal ident stmts e =
  let fn =
        T.unlines $
          [ "static KValue *" <> ident <> "(void) {"
          , "  static KValue *cache = 0; if (cache) return cache;"
          , "  KEnv *env = 0; (void)env;"
          ]
            ++ map ("  " <>) stmts
            ++ [ "  cache = " <> e <> ";"
               , "  return cache;"
               , "}"
               ]
   in modify' $ \st -> st {gsTop = fn : gsTop st}

-- | The C @main@: initialise the GC and run @main@'s IO action.
-- | The kappart2 runtime owns the scheduler: @main@ runs as the root fiber and
-- returns its terminal Exit (Success a | Failure cause); the process exit code
-- is 0 on Success, 1 on Failure.
emitMain :: GName -> Gen ()
emitMain g =
  let ident = cGlobIdent g
      fn =
        T.unlines
          [ "int main(void) {"
          , "  krt2_new(0);"
          , "  KValue *kexit = krt2_run_main(" <> ident <> "());"
          , "  return krt2_exit_is_success(kexit) ? 0 : 1;"
          , "}"
          ]
   in modify' $ \st -> st {gsTop = fn : gsTop st}

assemble :: GenState -> Text
assemble st =
  T.unlines $
    [ "/* Generated by the Kappa native backend (Kappa.Backend.C). */"
    , "#include \"kappart2.h\"" -- the kappart2 runtime; pulls in kappart.h too
    , ""
    ]
      -- LR2: per-program numeric constructor/variant tag ids (KT_/KVT_),
      -- referenced by the generated constructions and pattern-match tests.
      ++ tagEnumBlock st
      ++ [""]
      -- §34.5.3: extern decls for each used builtin primitive's direct C
      -- entry point, so the optimized output calls it directly (no by-name dispatch).
      ++ primExternBlock st
      -- §27.1.1: direct extern prototypes + typed marshalling wrappers for
      -- each used host-binding member — the manifest-declared C symbols are
      -- called DIRECTLY (no name table, no strcmp dispatch).
      ++ hostNativeBlock st
      ++ reverse (gsProtos st)
      ++ [""]
      ++ reverse (gsTop st)

-- | Extern declarations for the direct C entry point of each used builtin
-- primitive (@kpf_*@). The optimized output calls these directly; the runtime
-- defines them. There is no by-name firing path in the runtime — every prim is
-- reached by a direct call or a curried @knative@ function pointer.
primExternBlock :: GenState -> [Text]
primExternBlock st
  | null cfns = []
  | otherwise =
      ["/* §34.5.3 builtin primitives: direct entry points (no string dispatch). */"]
        ++ ["extern KValue *" <> cfn <> "(KValue **);" | cfn <- cfns]
        ++ [""]
  where
    -- distinct entry-point names (several prims share one kpf_*)
    cfns =
      Set.toList . Set.fromList $
        [cfn | n <- Set.toList (gsPrimUsed st), Just (PrimEntry cfn _ _) <- [Map.lookup n primEntries]]

-- | The native host-binding block: one @extern@ prototype per distinct C
-- symbol used, followed by one marshalling wrapper per used member
-- ('Kappa.Backend.NativeFfi'). Empty when no host.native member is used.
hostNativeBlock :: GenState -> [Text]
hostNativeBlock st
  | null used = []
  | otherwise =
      [ "/* §27.1.1 native host bindings: direct extern prototypes + typed wrappers. */" ]
        ++ dedupKeep (map externPrototype used)
        ++ [""]
        ++ map wrapperDefinition used
        ++ [""]
  where
    used = [rns | g <- Set.toList (gsHostUsed st), Just rns <- [Map.lookup g (gsHostSyms st)]]
    dedupKeep = go Set.empty
      where
        go _ [] = []
        go seen (x : xs)
          | x `Set.member` seen = go seen xs
          | otherwise = x : go (Set.insert x seen) xs

-- ── Term lowering ────────────────────────────────────────────────────

-- | Compile a term: emit any needed statements into the current buffer and
-- return a C expression (of type @KValue *@) for its value.
compile :: Term -> Gen Text
compile term
  -- §18.3 monadic splice: `__runIO e` runs the embedded IO action inline
  -- and yields its result as an ordinary value (matches runSplices).
  | Just action <- runIOSplice term = compileRunIO action
compile term = case term of
  CVar i -> do
    -- R2.3: in a flat worker, read the C local for de Bruijn index @i@ directly
    -- (no kvar chain walk) — a parameter or a let/match-bound local prepended
    -- onto gsParamLvals (R2.3-rest).  gsParamLvals is empty outside a flat
    -- body; the kvar fallback is the general (boxed-KEnv) path.
    lvals <- gets gsParamLvals
    if not (null lvals) && i >= 0 && i < length lvals
      then pure (lvals !! i)
      else do
        -- R3.2: in a FLAT CLOSURE the flat prefix (the param + any let/match
        -- locals, 'gsParamLvals') covers the innermost de Bruijn indices and
        -- the captured env @cenv@ covers the rest, so a captured-var index is
        -- shifted PAST the flat prefix.  For a worker this branch is never
        -- taken (all indices are flat); for the boxed path @lvals@ is empty so
        -- the shift is 0 (unchanged @kvar(env,i)@).
        env <- gets gsEnv
        pure ("kvar(" <> env <> ", " <> T.pack (show (i - length lvals)) <> ")")
  CGlob g -> compileGlob g
  CLit l -> compileLit l
  CApp {} -> compileApp term
  CLam _ _ _ body -> compileLam body
  CCtor g _ args -> compileCtor g args
  CIf {} -> sinkToExpr term
  CMatch {} -> sinkToExpr term
  CLet {} -> sinkToExpr term
  CLetRec {} -> sinkToExpr term
  CRecordV fs -> compileRecord fs
  CProj e f -> do
    ee <- compile e
    pure ("kproj(" <> ee <> ", " <> cStr f <> ")")
  -- P0.4: a projection of a statically-known CLOSED record reads the field at
  -- its fixed lexicographic offset (krec_at, the tuple fast path) instead of a
  -- kproj-by-name strcmp scan.  Open/sealed/dynamic records keep plain CProj.
  CProjAt e _ i -> do
    ee <- compile e
    pure (recAtExpr ee i)
  CDo lbl items -> compileDo lbl items
  -- §13 closed/open variants: injection is a tagged payload.
  CInject tag e -> do
    ee <- compile e
    tc <- variantTagConst tag
    pure ("kinject(" <> tc <> ", " <> cStr tag <> ", " <> ee <> ")")
  -- §13.2.10: `seal` is pure and non-generative (seal e as S ≡ e), so a
  -- sealed package's runtime value is exactly its underlying record/value.
  CSealE _ e -> compile e
  -- §19 suspensions: Delay re-evaluates on force; Memo caches.
  CThunkE e -> compileSuspension 0 e
  CLazyE e -> compileSuspension 1 e
  CForceE t -> do
    te <- compile t
    pure ("kforce(" <> te <> ")")
  -- ── Escalated: NOT runtime values in an accepted, erased program ──
  -- A type-level / staging term (sort, function/record/variant/signature
  -- type, unsolved-dictionary meta, syntax quote) is computationally erased
  -- (§12.2 quantity-0 erasure, §31.2; §30.2.4 for staging): its runtime
  -- value is the unit placeholder, which the interpreter likewise never
  -- inspects.  Erasing it here (rather than rejecting) means a type/Syntax
  -- value reached through ANY position — an argument, a field, a global
  -- body, a local `let` binding — compiles and runs, so no accepted program
  -- is refused over an erased term (compileErasableArg handles the common
  -- argument/field sites directly; this is the catch-all).
  CSort _ -> pure "kunit()"
  CPi {} -> pure "kunit()"
  CRecordT _ -> pure "kunit()"
  CVariantT _ -> pure "kunit()"
  CSigT {} -> pure "kunit()"
  CMeta _ -> pure "kunit()"
  CQuote {} -> pure "kunit()"

-- | Head global of an application spine, if any.
headGlob :: Term -> Maybe GName
headGlob = \case
  CApp _ f _ -> headGlob f
  CGlob g -> Just g
  CCtor g _ _ -> Just g
  _ -> Nothing

-- | An application spine: head term plus its arguments with icities.
spineOf :: Term -> (Term, [(Icit, Term)])
spineOf = go []
  where
    go acc (CApp ic f a) = go ((ic, a) : acc) f
    go acc t = (t, acc)

-- | Recognise a fully-saturated application of an eta-expanded constructor
-- and beta-reduce it to a direct constructor (gap P0-A).
--
-- §10.1 'etaCtor' elaborates a constructor value of @k@ Pi binders into @k@
-- nested lambdas whose innermost body is a saturated @CCtor g [CVar …]@
-- selecting only the runtime-field binders (erased implicit/type binders are
-- dropped from the payload).  An applied occurrence keeps that
-- @CApp (… (CLam … (CCtor g …))) a@ shape, so without this it lowers through a
-- @k@-deep curried @kclo@/@kapp@ chain (one cons cell costs ~3 closures + 3
-- @kpush@ + 2 @kapp@ — the cost that dominates @listfold@/@adtbuild@).
--
-- When the spine applies exactly one argument per lambda the redex
-- beta-reduces: each body @CVar j@ names the binder at de Bruijn index @j@,
-- i.e. spine position @k-1-j@ (the spine lists arguments outermost-first),
-- supplied by the applied argument there.  Because every field var is a bare
-- binder reference (never a compound term or a free variable), the reduction
-- is a simultaneous substitution that just selects applied arguments — no
-- index shifting on open terms.  The result is @CCtor g [selected args]@,
-- compiled by 'compileCtor' as a direct @kctor@.
--
-- 'Nothing' for a partial application (still a closure), an over-application
-- (impossible for a well-typed ctor, but rejected for safety), or any head
-- that is not an eta-expanded constructor — all of which keep the general
-- curried lowering.
etaCtorApp :: Term -> Maybe (GName, [Term])
etaCtorApp term =
  case spineOf term of
    (hd, sargs)
      | (k, body) <- funcArity hd -- count the leading eta lambdas
      , k >= 1
      , k == length sargs
      , CCtor g _ fieldVars <- body ->
          (,) g <$> traverse (pick (map snd sargs) k) fieldVars
    _ -> Nothing
  where
    -- a field var must be a bare in-range binder reference; anything else
    -- (a compound subterm, or a free variable at index >= k) bails to the
    -- general lowering rather than misreading the payload.
    pick args k = \case
      CVar j | j >= 0, j < k -> Just (args !! (k - 1 - j))
      _ -> Nothing

-- | If @term@ is a saturated call to the worker's own global (a tail
-- self-call), return its arguments (with icities); the worker then loops
-- instead of recursing in C.
selfTailArgs :: TailInfo -> Term -> Maybe [(Icit, Term)]
selfTailArgs ti term = case spineOf term of
  (CGlob g, args) | g == tiName ti && length args == tiArity ti -> Just args
  _ -> Nothing

-- | Lower a self-tail-call to a loop step: recompute the arguments into
-- fresh temporaries (they may read the current parameters), rebind the
-- worker's parameter variables, and @continue@.
emitTailLoop :: TailInfo -> [(Icit, Term)] -> Gen ()
emitTailLoop ti args = do
  -- Evaluate every new argument into a temp FIRST (an arg may read a current
  -- parameter via @kvar@), THEN update the parameter cells in place — so the
  -- loop reuses the cells built once in 'compileFunctionGlobal' rather than
  -- allocating a fresh env each iteration (QW2).
  temps <- forM args $ \(_ic, a) -> do
    e <- compileErasableArg a -- erase type-level/staging args (§31.2), any icity
    t <- freshN "tc_"
    emit ("KValue *" <> t <> " = " <> e <> ";")
    pure t
  -- reassign the C parameters (FLAT: read directly; REBUILD: the loop top
  -- rebuilds kw_env from them).  Temps first, so an arg may read a current param.
  forM_ (zip (tiSlots ti) temps) $ \(slot, t) -> emit (slot <> " = " <> t <> ";")
  emit "continue;"

-- | Emit a tail-position application.  A call whose spine head is a
-- primitive cannot recurse, so it is computed directly and returned (the
-- saturated-prim fast path, no needless partial-application box or bounce).
-- A call to anything else (a function value / closure that could recurse)
-- becomes a trampoline @kbounce(f,a)@, returned so the driving
-- @kapp@/@krun_io@ performs the deferred application in constant C stack.
-- NOTE: this is the AUTHORITY on when a worker returns a @K_BOUNCE@;
-- 'workerMayBounce' mirrors the @kbounce@ condition below and must be kept in
-- lock-step (a new @kbounce@ arm here without updating it would make R3.1's
-- trampoline elision unsound).
emitTailApp :: Term -> Gen ()
emitTailApp term
  -- P0-A: a saturated eta-expanded constructor in tail position is a final
  -- data value (it cannot bounce or recurse), so build it directly and
  -- return it rather than trampolining through the closure chain.
  | Just (g, ctorArgs) <- etaCtorApp term = do
      e <- compileCtor g ctorArgs
      emit ("return " <> e <> ";")
emitTailApp term = do
  let (hd, _) = spineOf term
  mp <- case hd of CGlob g -> globPrimName g; _ -> pure Nothing
  case (mp, term) of
    (Just _, _) -> do
      e <- compile term -- prim spine: direct helper / entry-point call, computed here, no trampoline
      emit ("return " <> e <> ";")
    (Nothing, CApp Expl f a) -> do
      fe <- compile f
      ae <- compileErasableArg a
      emit ("return kbounce(" <> fe <> ", " <> ae <> ");")
    _ -> do
      e <- compile term
      emit ("return " <> e <> ";")

-- | Recognise a @__runIO e@ monadic-splice application (§18.3); returns
-- the single explicit IO-action argument.  Implicit type arguments are
-- ignored (erased).
runIOSplice :: Term -> Maybe Term
runIOSplice t = case spineOf t of
  (hd, args)
    | Just g <- headOf hd
    , g == Builtins.prelRunIO -- §1.2: declaration-symbol identity, not the "__runIO" spelling
    , [a] <- [x | (Expl, x) <- args] ->
        Just a
  _ -> Nothing
  where
    headOf (CGlob g) = Just g
    headOf _ = Nothing

-- | Is the implicit argument to this head erased at runtime? Primitive
-- and constructor heads erase implicit arguments (§31.2).  Primitives are
-- the @__prim@ module globals and the prelude globals whose value is a
-- bare 'VPrim' (the @prim@ registrations in "Kappa.Prelude").
isErasedHead :: Term -> Gen Bool
isErasedHead t = case headGlob t of
  Just g@(GName m _)
    | m == primModule -> pure True
    | otherwise -> do
        globals <- gets gsGlobals
        ctors <- gets gsCtors
        case Map.lookup g globals of
          Just gd | isVPrimValue (gdValue gd) -> pure True
          _ -> pure (Map.member g ctors)
  Nothing -> pure False

isVPrimValue :: Maybe Value -> Bool
isVPrimValue (Just (VPrim _ _)) = True
isVPrimValue _ = False

-- | Is this implicit argument purely type-level (computationally erased),
-- so an erased binder receiving it can be passed an unused placeholder?
-- Type-level forms and references to type/trait globals are erasable;
-- everything else (dictionaries, runtime values) is compiled for real.
isErasableArg :: Term -> Gen Bool
isErasableArg = \case
  CSort _ -> pure True
  CPi {} -> pure True
  CVariantT _ -> pure True
  CRecordT _ -> pure True
  CSigT {} -> pure True -- §13.2.10 signature type, erased (§12.2, §31.2)
  CMeta _ -> pure True
  CQuote {} -> pure True -- §21/§23 syntax quote: elaboration-time, erased
  CApp _ f _ -> isErasableArg f -- the spine head decides (e.g. @(List a))
  CGlob g -> isTypeGlob g
  _ -> pure False

-- | Compile a value-position argument, erasing it to the unit placeholder
-- when it is a type-level / staging term (§12.2, §31.2): an explicit
-- @(t : Type)@ / @(s : Syntax _)@ argument or constructor field is a
-- compile-time/static-object position (§11.1.6.1, §11.1.6.2) the spec
-- mandates be erased.  The interpreter stores the evaluated type/quote
-- value but never inspects it at runtime; emitting @kunit()@ keeps the
-- arity (so positional field projection stays aligned) while avoiding the
-- type-level guards in 'compile'.
compileErasableArg :: Term -> Gen Text
compileErasableArg a = do
  er <- isErasableArg a
  if er then pure "kunit()" else compile a

-- | A global that denotes a type or trait (so a reference to it in
-- argument position is computationally erased): a declared data type or
-- trait, or a global whose kind is a sort (e.g. the builtin @Integer@).
isTypeGlob :: GName -> Gen Bool
isTypeGlob g = do
  datas <- gets gsDatas
  traits <- gets gsTraits
  globals <- gets gsGlobals
  ctx <- gets gsEvalCtx
  let sortish = case Map.lookup g globals of
        Just gd -> isTypeKindTerm (quote ctx 0 (gdType gd))
        Nothing -> False
  pure (g `Set.member` datas || g `Set.member` traits || sortish)

isTypeKindTerm :: Term -> Bool
isTypeKindTerm = \case
  CSort _ -> True
  CPi _ _ _ _ _ body -> isTypeKindTerm body
  _ -> False

-- | Emit a reference to a runtime primitive, after confirming the linked
-- runtime implements it; an unimplemented primitive is a compile-time
-- 'E_BACKEND_UNSUPPORTED' (never a silent runtime failure).
-- | §34.5.3: a bare reference to a builtin primitive lowers to a DIRECT call
-- on its runtime entry point. A nullary pure builtin is a value, fired
-- immediately (@kpf_x(0)@); any other builtin becomes a curried native
-- action carrying the function pointer (@knative@, pure fires on saturation,
-- IO suspends). There is NO by-name string dispatch. An unknown primitive is a
-- compile-time 'E_BACKEND_UNSUPPORTED'.
emitPrim :: Text -> Gen Text
-- §18.1.12 `poll` is a 0-arity IO action that IS the OP_POLL node: a bare
-- reference (e.g. `ioBind poll k`, where `poll` is the action operand) lowers to
-- the node builder directly, exactly as the saturated `poll` case in
-- 'compileAppGlob'.  There is no curried `kpf_poll` wrapper in the runtime.
emitPrim "poll" = pure "krt2_poll()"
emitPrim name = case Map.lookup name primEntries of
  Just (PrimEntry cfn ar isio) -> do
    markPrimUsed name
    pure $
      if ar == 0 && not isio
        then cfn <> "((KValue **)0)"
        else "knative(" <> cfn <> ", " <> T.pack (show ar) <> ", " <> cStr name <> ", " <> ioFlag isio <> ")"
  Nothing ->
    unsupported "primitive"
      ("the primitive '" <> name <> "' is not implemented by the native runtime")

ioFlag :: Bool -> Text
ioFlag b = if b then "1" else "0"

-- | Record a builtin primitive as referenced so 'assemble' emits its extern.
markPrimUsed :: Text -> Gen ()
markPrimUsed n = modify' (\st -> st {gsPrimUsed = Set.insert n (gsPrimUsed st)})

-- | §27.1.1: a bare reference to a host-binding member lowers to a curried
-- native action carrying the codegen-emitted wrapper pointer ('knative').
-- Native bindings are conservatively typed in UIO, so the action is IO
-- (suspended). 'assemble' emits the wrapper + extern prototype per used member.
emitHostNative :: GName -> ResolvedNativeSymbol -> Gen Text
emitHostNative g rns = do
  markHostUsed g
  collectHostCtors rns
  pure
    ( "knative(" <> wrapperCName rns <> ", "
        <> T.pack (show (length (rns.params))) <> ", "
        <> cStr (rns.cSymbol) <> ", 1)"
    )

-- | Record a host member as referenced so 'assemble' emits its wrapper.
markHostUsed :: GName -> Gen ()
markHostUsed g = modify' (\st -> st {gsHostUsed = Set.insert g (gsHostUsed st)})

-- | Register the std.ffi wrapper constructors a host symbol's marshalling
-- builds (MkI64/MkU32/MkRawPtr/…) so 'assemble' emits their KT_ tag ids
-- (shared with any in-program match on the same ctor).
collectHostCtors :: ResolvedNativeSymbol -> Gen ()
collectHostCtors rns =
  modify' (\st -> st {gsCollectCtors = foldr Set.insert (gsCollectCtors st) (rnsCollectCtors rns)})

-- | The runtime primitive name a global resolves to, if it is one (a
-- @primModule@ name, a prelude @prim@ registration, or a §34.5 host
-- intrinsic that satisfied an @expect@), and that name is implemented by
-- the linked runtime.  Mirrors the prim-resolving arms of 'compileGlob'.
globPrimName :: GName -> Gen (Maybe Text)
globPrimName g@(GName m nm) = do
  prims <- gets gsPrims
  let known n = if n `Set.member` prims then Just n else Nothing
  if m == primModule
    then pure (known nm)
    else do
      globals <- gets gsGlobals
      pure $ case Map.lookup g globals of
        Just gd | Just (VPrim pname _) <- gdValue gd -> known pname
        _ -> Nothing

-- | §34.5.3: the complete builtin-primitive table — each primitive maps to
-- its DIRECT C entry point (@kp_*@/@kpf_*@ in the runtime: pure builtins, and
-- the effectful @kpf_io_*@ ones the do-kernel sequences), its arity, and
-- whether it is an IO action. Codegen emits a direct call to the entry point
-- (saturated) or a curried @knative@ value (partial) — never a by-name string
-- dispatch. This table is the single source of truth for each prim's arity and
-- IO-ness; the native suite catches any drift from the runtime's helpers.
data PrimEntry = PrimEntry !Text !Int !Bool -- ^ C entry point, arity, isIO

primEntries :: Map Text PrimEntry
primEntries = Map.fromList
  [ ("__arrayFromList", PrimEntry "kpf___queryFromList" 1 False)
  , ("__arrayIndexUnsafe", PrimEntry "kpf___arrayIndexUnsafe" 2 False)
  , ("__arrayToList", PrimEntry "kpf___queryFromList" 1 False)
  , ("__absurd", PrimEntry "kpf___absurd" 1 False)
  , ("__atomicRepEq", PrimEntry "kpf___atomicRepEq" 2 False)
  , ("__byteLength", PrimEntry "kpf___byteLength" 1 False)
  , ("__byteToNat", PrimEntry "kpf___byteToNat" 1 False)
  , ("__bytesAppend", PrimEntry "kpf___bytesAppend" 2 False)
  , ("__bytesBreakIndex", PrimEntry "kpf___bytesBreakIndex" 2 False)
  , ("__bytesBuilderByte", PrimEntry "kpf___bytesBuilderByte" 2 False)
  , ("__bytesBuilderBytes", PrimEntry "kpf___bytesBuilderBytes" 2 False)
  , ("__bytesCompact", PrimEntry "kpf___bytesCompact" 1 False)
  , ("__bytesContains", PrimEntry "kpf___bytesContains" 2 False)
  , ("__bytesDrop", PrimEntry "kpf___bytesDrop" 2 False)
  , ("__bytesEmpty", PrimEntry "kpf___bytesEmpty" 0 False)
  , ("__bytesEndsWith", PrimEntry "kpf___bytesEndsWith" 2 False)
  , ("__bytesFind", PrimEntry "kpf___bytesFind" 2 False)
  , ("__bytesFromList", PrimEntry "kpf___bytesFromList" 1 False)
  , ("__bytesGet", PrimEntry "kpf___bytesGet" 2 False)
  , ("__bytesIndexUnsafe", PrimEntry "kpf___bytesIndexUnsafe" 2 False)
  , ("__bytesIsEmpty", PrimEntry "kpf___bytesIsEmpty" 1 False)
  , ("__bytesLength", PrimEntry "kpf___bytesLength" 1 False)
  , ("__bytesSingleton", PrimEntry "kpf___bytesSingleton" 1 False)
  , ("__bytesSlice", PrimEntry "kpf___bytesSlice" 3 False)
  , ("__bytesStartsWith", PrimEntry "kpf___bytesStartsWith" 2 False)
  , ("__bytesTake", PrimEntry "kpf___bytesTake" 2 False)
  , ("__bytesToList", PrimEntry "kpf___bytesToList" 1 False)
  , ("__caseFold", PrimEntry "kpf___caseFold" 1 False)
  , ("__decodeUtf8Chunk", PrimEntry "kpf___decodeUtf8Chunk" 2 False)
  , ("__decodeUtf8Lossy", PrimEntry "kpf___decodeUtf8Lossy" 1 False)
  , ("__finishBytesBuilder", PrimEntry "kpf___finishBytesBuilder" 1 False)
  , ("__finishStringBuilder", PrimEntry "kpf___finishStringBuilder" 1 False)
  , ("__finishUtf8Decoder", PrimEntry "kpf___finishUtf8Decoder" 1 False)
  , ("__graphemeCount", PrimEntry "kpf___graphemeCount" 1 False)
  , ("__graphemeOfString", PrimEntry "kpf___graphemeOfString" 1 False)
  , ("__graphemeToString", PrimEntry "kpf___graphemeToString" 1 False)
  , ("__graphemeValid", PrimEntry "kpf___graphemeValid" 1 False)
  , ("__hashMixBytes", PrimEntry "kpf___hashMixBytes" 2 False)
  , ("__hashMixDouble", PrimEntry "kpf___hashMixDouble" 2 False)
  , ("__hashMixInt", PrimEntry "kpf___hashMixInt" 2 False)
  , ("__hashMixString", PrimEntry "kpf___hashMixString" 2 False)
  , ("__intAnd", PrimEntry "kpf___intAnd" 2 False)
  , ("__intOr", PrimEntry "kpf___intOr" 2 False)
  , ("__intXor", PrimEntry "kpf___intXor" 2 False)
  , ("__mapFromEntries", PrimEntry "kpf___queryFromList" 1 False)
  , ("__mapToList", PrimEntry "kpf___queryFromList" 1 False)
  , ("__natToByte", PrimEntry "kpf___natToByte" 1 False)
  , ("__newBytesBuilder", PrimEntry "kpf___newBytesBuilder" 0 False)
  , ("__newStringBuilder", PrimEntry "kpf___newStringBuilder" 0 False)
  , ("__newUtf8Decoder", PrimEntry "kpf___newUtf8Decoder" 0 False)
  , ("__normalize", PrimEntry "kpf___normalize" 2 False)
  , ("__queryFromList", PrimEntry "kpf___queryFromList" 1 False)
  , ("__queryToList", PrimEntry "kpf___queryFromList" 1 False)
  , ("__rangeEnum", PrimEntry "kpf___rangeEnum" 3 False)
  , ("__ratDen", PrimEntry "kpf___ratDen" 1 False)
  , ("__ratNum", PrimEntry "kpf___ratNum" 1 False)
  , ("__ratOfInt", PrimEntry "kpf___ratOfInt" 1 False)
  , ("__scalarCount", PrimEntry "kpf___scalarCount" 1 False)
  , ("__scalarInRange", PrimEntry "kpf___scalarInRange" 1 False)
  , ("__scalarOfValue", PrimEntry "kpf___scalarOfValue" 1 False)
  , ("__scalarToString", PrimEntry "kpf___scalarToString" 1 False)
  , ("__setFromList", PrimEntry "kpf___queryFromList" 1 False)
  , ("__setToList", PrimEntry "kpf___queryFromList" 1 False)
  , ("__stringBuilderGrapheme", PrimEntry "kpf___stringBuilderGrapheme" 2 False)
  , ("__stringBuilderScalar", PrimEntry "kpf___stringBuilderScalar" 2 False)
  , ("__stringBuilderString", PrimEntry "kpf___stringBuilderString" 2 False)
  , ("__stringCompact", PrimEntry "kpf___queryFromList" 1 False)
  , ("__stringCursorOffset", PrimEntry "kpf___stringCursorOffset" 2 False)
  , ("__stringEnd", PrimEntry "kpf___stringEnd" 1 False)
  , ("__stringGraphemes", PrimEntry "kpf___stringGraphemes" 1 False)
  , ("__stringNextGrapheme", PrimEntry "kpf___stringNextGrapheme" 2 False)
  , ("__stringNextScalar", PrimEntry "kpf___stringNextScalar" 2 False)
  , ("__stringPrevScalar", PrimEntry "kpf___stringPrevScalar" 2 False)
  , ("__stringScalars", PrimEntry "kpf___stringScalars" 1 False)
  , ("__stringSentences", PrimEntry "kpf___stringSentences" 1 False)
  , ("__stringSpan", PrimEntry "kpf___stringSpan" 3 False)
  , ("__stringStart", PrimEntry "kpf___stringStart" 1 False)
  , ("__stringWords", PrimEntry "kpf___stringWords" 1 False)
  , ("__transport", PrimEntry "kpf___queryFromList" 1 False)
  , ("__uniScalarValue", PrimEntry "kpf___uniScalarValue" 1 False)
  , ("__utf8Bytes", PrimEntry "kpf___utf8Bytes" 1 False)
  , ("__utf8Valid", PrimEntry "kpf___utf8Valid" 1 False)
  , ("addDouble", PrimEntry "kpf_addDouble" 2 False)
  , ("addInt", PrimEntry "kpf_addInt" 2 False)
  , ("addRat", PrimEntry "kpf_addRat" 2 False)
  , ("divDouble", PrimEntry "kpf_divDouble" 2 False)
  , ("divInt", PrimEntry "kpf_divInt" 2 False)
  , ("divRat", PrimEntry "kpf_divRat" 2 False)
  , ("eqByte", PrimEntry "kpf_eqByte" 2 False)
  , ("eqBytes", PrimEntry "kpf_eqBytes" 2 False)
  , ("eqDouble", PrimEntry "kpf_eqDouble" 2 False)
  , ("eqGrapheme", PrimEntry "kpf_eqGrapheme" 2 False)
  , ("eqInt", PrimEntry "kpf_eqInt" 2 False)
  , ("eqRat", PrimEntry "kpf_eqRat" 2 False)
  , ("eqScalar", PrimEntry "kpf_eqScalar" 2 False)
  , ("eqStr", PrimEntry "kpf_eqStr" 2 False)
  , ("floatEq", PrimEntry "kpf_floatEq" 2 False)
  , ("intToDouble", PrimEntry "kpf_intToDouble" 1 False)
  , ("intToNat", PrimEntry "kpf_intToNat" 1 False)
  , ("ioBind", PrimEntry "kpf_io_ioBind" 2 True)
  , ("ioPure", PrimEntry "kpf_io_ioPure" 1 True)
  , ("ioThen", PrimEntry "kpf_io_ioThen" 2 True)
  , ("throwIO", PrimEntry "kpf_io_throwIO" 1 True)
  , ("catchIO", PrimEntry "kpf_io_catchIO" 2 True)
  , ("finallyIO", PrimEntry "kpf_io_finallyIO" 2 True)
  -- §12.4.3 first-class borrowed views (runtime borrow = value)
  , ("captureBorrow", PrimEntry "kpf_captureBorrow" 1 False)
  , ("withBorrowView", PrimEntry "kpf_withBorrowView" 2 False)
  -- §18.1 algebraic-effect tree primitives (pure tree transformations)
  , ("runPure", PrimEntry "kpf_runPure" 1 False)
  , ("__effBind", PrimEntry "kpf___effBind" 2 False)
  , ("__handleEff", PrimEntry "kpf___handleEff" 5 False)
  , ("leInt", PrimEntry "kpf_leInt" 2 False)
  , ("ltByte", PrimEntry "kpf_ltByte" 2 False)
  , ("ltBytes", PrimEntry "kpf_ltBytes" 2 False)
  , ("ltDouble", PrimEntry "kpf_ltDouble" 2 False)
  , ("ltInt", PrimEntry "kpf_ltInt" 2 False)
  , ("ltRat", PrimEntry "kpf_ltRat" 2 False)
  , ("ltScalar", PrimEntry "kpf_ltScalar" 2 False)
  , ("ltStr", PrimEntry "kpf_ltStr" 2 False)
  , ("modInt", PrimEntry "kpf_modInt" 2 False)
  , ("mulDouble", PrimEntry "kpf_mulDouble" 2 False)
  , ("mulInt", PrimEntry "kpf_mulInt" 2 False)
  , ("mulRat", PrimEntry "kpf_mulRat" 2 False)
  , ("natOfInt", PrimEntry "kpf_natToInt" 1 False)
  , ("natToInt", PrimEntry "kpf_natToInt" 1 False)
  , ("negDouble", PrimEntry "kpf_negDouble" 1 False)
  , ("negInt", PrimEntry "kpf_negInt" 1 False)
  -- §18.1.6 Duration constructors (pure Int -> nanosecond Int)
    -- §18.1 Duration/Instant arithmetic = signed-ns Int add/sub (reuse kp_addInt/subInt)
  , ("__nowNanos", PrimEntry "kpf_now" 0 True) -- UIO Instant: reads the monotonic clock
  , ("negRat", PrimEntry "kpf_negRat" 1 False)
  , ("newRef", PrimEntry "kpf_io_newRef" 1 True)
  , ("primitiveIntToString", PrimEntry "kpf_primitiveIntToString" 1 False)
  , ("printString", PrimEntry "kpf_io_printString" 1 True)
  , ("printlnString", PrimEntry "kpf_io_printlnString" 1 True)
  , ("ratOfDouble", PrimEntry "kpf_ratOfDouble" 1 False)
  , ("readRef", PrimEntry "kpf_io_readRef" 1 True)
  , ("showByte", PrimEntry "kpf_showByte" 1 False)
  , ("showBytes", PrimEntry "kpf_showBytes" 1 False)
  , ("showDouble", PrimEntry "kpf_showDouble" 1 False)
  , ("showGrapheme", PrimEntry "kpf_showGrapheme" 1 False)
  , ("showInt", PrimEntry "kpf_showInt" 1 False)
  , ("showRat", PrimEntry "kpf_showRat" 1 False)
  , ("showScalar", PrimEntry "kpf_showScalar" 1 False)
  , ("showStringLit", PrimEntry "kpf_showStringLit" 1 False)
  , ("stringAppend", PrimEntry "kpf_stringAppend" 2 False)
  , ("subDouble", PrimEntry "kpf_subDouble" 2 False)
  , ("subInt", PrimEntry "kpf_subInt" 2 False)
  , ("subRat", PrimEntry "kpf_subRat" 2 False)
  , ("unsafeConsume", PrimEntry "kpf_unsafeConsume" 1 False)
  , ("writeRef", PrimEntry "kpf_io_writeRef" 2 True)
  -- §18.1.4/§18.1.6/§18.1.9 concurrency node builders (CPS do-kernel): each
  -- lowers to its krt2_* OP_* node so the CK-machine can park on it.  isIO=False
  -- because building the node is pure construction; the node IS the suspended
  -- action the CPS-lowered do-block sequences via krt2_bind.
  , ("__forkRun", PrimEntry "kpf_fork" 1 False)
  , ("__forkDaemon", PrimEntry "kpf_fork_daemon" 1 False)
  , ("__awaitFiber", PrimEntry "kpf_await" 1 False)
  , ("cede", PrimEntry "kpf_cede" 0 False)
  , ("__sleepForNanos", PrimEntry "kpf_sleep_for" 1 False)
  , ("newPromise", PrimEntry "kpf_new_promise" 0 False)
  , ("completePromise", PrimEntry "kpf_complete_promise" 2 False)
  , ("awaitPromiseExit", PrimEntry "kpf_await_promise_exit" 1 False)
  -- §18.1.8 structured scopes + monitors (Stage 3)
  , ("newScope", PrimEntry "kpf_new_scope" 0 False)
  , ("forkIn", PrimEntry "kpf_fork_in" 2 False)
  , ("shutdownScope", PrimEntry "kpf_shutdown_scope" 1 False)
  , ("monitor", PrimEntry "kpf_monitor" 1 False)
  , ("awaitMonitor", PrimEntry "kpf_await_monitor" 1 False)
  , ("demonitor", PrimEntry "kpf_demonitor" 1 True) -- §18.1.8 no-op -> Unit

  -- §18.1.13 STM (journaled): newTVar/readTVar/writeTVar/atomically/stmBind/
  -- stmPure are STM_* / OP_ATOMICALLY node-builders (compileAppGlob); check is a
  -- .kp def. Only `retry` keeps a primEntry — it is nullary (no explicit args, so
  -- it never reaches the compileAppGlob spine), and fires kpf_retry immediately
  -- to yield the STM_RETRY node.
  , ("retry", PrimEntry "kpf_retry" 0 False)
  ]

-- | Internal-consistency problems between the two primitive tables. The
-- saturated fast-path table 'primDirect' (@kp_*@ helpers) must be a subset of
-- the full registry 'primEntries' (@kpf_*@ wrappers, arity, IO-ness): every
-- prim with a direct lowering must also have a registry entry, and the two
-- must agree on arity — otherwise a saturated call and a partial/by-value
-- reference to the same prim would disagree on how many arguments it takes.
-- Reports any 'primDirect' entry missing from the registry, or whose arity
-- disagrees. An empty result means the tables are consistent. Surfaced by the
-- pipeline's §28 contract pass, so a drift becomes a reported diagnostic rather
-- than a silent miscompile.
primRegistryDiagnostics :: [Text]
primRegistryDiagnostics =
  [ msg
  | (name, (_, dArity)) <- Map.toList primDirectTable
  , Just msg <- [checkOne name dArity]
  ]
  where
    checkOne name dArity = case Map.lookup name primEntries of
      Nothing ->
        Just ("primDirect '" <> name <> "' has no primEntries registry entry")
      Just (PrimEntry _ eArity _)
        | eArity /= dArity ->
            Just
              ( "primDirect '" <> name <> "' has arity " <> tShow dArity
                  <> " but primEntries records arity " <> tShow eArity
              )
        | otherwise -> Nothing
    tShow :: Show a => a -> Text
    tShow = T.pack . show

-- | QW1: the statically-known saturated pure primitives that have a direct C
-- helper (`kp_…` in the runtime).  A saturated call to one of these is
-- lowered to a direct helper call — no string dispatch, no `prim_arity` /
-- `prim_is_io` check, no per-call argument array.  Maps the primitive name to
-- (helper C name, explicit arity).  These `kp_…` helpers are the runtime's
-- single source of truth for each prim's semantics; the native suite catches
-- any drift between this table and the runtime.  IO / partial / unlisted prims
-- lower to a curried `knative` value instead.
primDirect :: Text -> Maybe (Text, Int)
primDirect = (`Map.lookup` primDirectTable)

-- | The backing table for 'primDirect', kept enumerable so the §28 prim-registry
-- contract check ('primRegistryDiagnostics') can cross-validate every direct
-- entry against the full 'primEntries' registry.
primDirectTable :: Map Text (Text, Int)
primDirectTable = Map.fromList
  [ ("addInt", ("kp_addInt", 2))
  , ("subInt", ("kp_subInt", 2))
  , ("mulInt", ("kp_mulInt", 2))
  , ("divInt", ("kp_divInt", 2))
  , ("modInt", ("kp_modInt", 2))
  , ("negInt", ("kp_negInt", 1))
  , ("eqInt", ("kp_eqInt", 2))
  , ("ltInt", ("kp_ltInt", 2))
  , ("leInt", ("kp_leInt", 2))
  , ("addDouble", ("kp_addDouble", 2))
  , ("subDouble", ("kp_subDouble", 2))
  , ("mulDouble", ("kp_mulDouble", 2))
  , ("divDouble", ("kp_divDouble", 2))
  , ("negDouble", ("kp_negDouble", 1))
  , ("ltDouble", ("kp_ltDouble", 2))
  , ("floatEq", ("kp_floatEq", 2))
  , ("eqDouble", ("kp_eqDouble", 2))
  , ("stringAppend", ("kp_stringAppend", 2))
  , ("eqStr", ("kp_eqStr", 2))
  , ("ltStr", ("kp_ltStr", 2))
  , ("eqScalar", ("kp_eqScalar", 2))
  , ("ltScalar", ("kp_ltScalar", 2))
  , ("showInt", ("kp_showInt", 1))
  , ("showDouble", ("kp_showDouble", 1))
  , ("showScalar", ("kp_showScalar", 1))
  , ("showStringLit", ("kp_showStringLit", 1))
  , ("intToDouble", ("kp_intToDouble", 1))
  , ("eqByte", ("kp_eqByte", 2))
  , ("ltByte", ("kp_ltByte", 2))
  , ("__intAnd", ("kp_intAnd", 2))
  , ("__intOr", ("kp_intOr", 2))
  , ("__intXor", ("kp_intXor", 2))
  ]

-- | Compile an application spine.  When the spine head is a known runtime
-- primitive, emit a direct helper call ('primDirect') for a saturated pure
-- prim, else a direct call on its C entry point over a stack argument array —
-- the saturated case fires in one call with no intermediate curried
-- partial-application boxes or per-argument allocation (the dominant cost in
-- hot numeric loops).
-- Otherwise fall back to per-argument 'kapp'/'kappi'.
compileApp :: Term -> Gen Text
compileApp term
  -- P0-A: a saturated eta-expanded constructor application is a direct
  -- 'kctor', not a curried closure chain (see 'etaCtorApp').
  | Just (g, ctorArgs) <- etaCtorApp term = compileCtor g ctorArgs
compileApp term0 = do
  -- FIX (interp-vs-native): at an ORDINARY-function-global spine, replace each
  -- argument sitting at a 'Q0' (computationally erased, §31.2) telescope position
  -- with a 'CSort' placeholder.  'compileErasableArg' already lowers a 'CSort' to
  -- @kunit()@, so this erases the argument WHOLESALE — regardless of its syntax.
  -- Without it, an erased type-level APPLICATION @f a@ (a 'CApp' over type
  -- variables) survives the purely-syntactic 'isErasableArg' (which only looks
  -- at the spine head) and lowers to a real @kapp(kvar f, kvar a)@ over two
  -- unit-valued slots — the @sequence@/@sequence_@/@for_@/@traverse@-over-IO
  -- crash (@kapp: applying a non-function value@).  Rewriting the term here keeps
  -- EVERY downstream path consistent ('compileAppGlob', 'compileDirectCall' +
  -- 'applyExtra', the prim special-cases, and the 'compileAppDefault' curried
  -- fallback all re-derive from this term / its spine).
  --
  -- ONLY for a NON-erased head (an ordinary defined function global).  For an
  -- erased head — a primitive or a constructor ('isErasedHead') — elaboration
  -- has ALREADY dropped the implicit arguments from the spine, so spine position
  -- k no longer aligns with telescope binder k; erasing by telescope index there
  -- would wrongly unit-out a real EXPLICIT value argument (e.g. the @Eff@ value
  -- and continuation of the @__effBind@ prim, whose @~>@ value binders sit at
  -- telescope positions 3/4 while the spine holds only those two args).  Those
  -- heads never exhibit the type-application bug anyway (their implicit args are
  -- dropped, not lowered), and keep the existing per-arg erasure.
  erasedHd <- isErasedHead term0
  term <-
    if erasedHd
      then pure term0
      else case fst (spineOf term0) of
        CGlob g -> eraseQ0Args g term0
        _ -> pure term0
  let (hd, sargs) = spineOf term
  case hd of
    CGlob g -> do
      hostSyms <- gets gsHostSyms
      case Map.lookup g hostSyms of
        -- §27.1.1: a saturated host-member application is a DIRECT native
        -- action — collect the args and build a saturated 'knative_sat'
        -- (the suspended UIO action krun_io fires by calling the emitted
        -- wrapper). A partial application falls through to the curried
        -- bare-reference path (compileGlob → knative + kapp).
        Just rns
          | let arity = length (rns.params)
                explArgs = [a | (Expl, a) <- sargs]
          , length explArgs >= arity
          , arity > 0 -> do
              markHostUsed g
              collectHostCtors rns
              aes <- mapM compileErasableArg (take arity explArgs)
              arr <- freshN "na_"
              emit ("KValue *" <> arr <> "[] = {" <> T.intercalate ", " aes <> "};")
              pure
                ( "knative_sat(" <> wrapperCName rns <> ", "
                    <> T.pack (show arity) <> ", " <> arr <> ", 1)"
                )
        _ -> compileAppGlob g sargs term
    _ -> compileAppDefault term

-- | The non-host global application spine (primitive / direct-call / default).
compileAppGlob :: GName -> [(Icit, Term)] -> Term -> Gen Text
compileAppGlob g sargs term = do
      mp <- globPrimName g
      susp <- gets gsSuspenders
      case mp of
        -- §3.1 general CPS: an @ioBind@/@ioThen@ EXPRESSION (not a do-block —
        -- e.g. the prelude @join@/@race@/@timeout@ bodies) whose FIRST action may
        -- suspend becomes a CK-machine bind/then node, so the head action can
        -- park.  The synchronous @kpf_io_ioBind@ bridge cannot park, so a
        -- suspending head there would mis-run; the CDo path is already CPS, this
        -- is the same lowering for the raw @ioBind@ spine.  Gated on §3.3
        -- ('gsSuspenders') — a sequential @ioBind@ stays on the cheap bridge.
        Just "ioBind"
          | [m, k] <- [a | (Expl, a) <- sargs]
          , mayActSuspend susp m -> do
              mc <- compileErasableArg m
              kc <- compileErasableArg k
              pure ("krt2_bind(" <> mc <> ", " <> kc <> ")")
        Just "ioThen"
          | [m, n] <- [a | (Expl, a) <- sargs]
          , mayActSuspend susp m -> do
              mc <- compileErasableArg m
              nc <- compileErasableArg n
              pure ("krt2_then(" <> mc <> ", " <> nc <> ")")
        -- catchIO/finallyIO over a may-suspend body must be the CK-machine
        -- node, not the kpf_io_* bridge — the bridge runs the body via the
        -- synchronous krun_io, which cannot drive a krt2_bind/await tree (so
        -- `catchIO (join f) h` would mis-run the join).  Same §3.3 gate.
        Just "catchIO"
          | [body, h] <- [a | (Expl, a) <- sargs]
          , mayActSuspend susp body -> do
              bc <- compileErasableArg body
              hc <- compileErasableArg h
              pure ("krt2_catch(" <> bc <> ", " <> hc <> ")")
        Just "finallyIO"
          | [body, fin] <- [a | (Expl, a) <- sargs]
          , mayActSuspend susp body -> do
              bc <- compileErasableArg body
              fc <- compileErasableArg fin
              pure ("krt2_finally(" <> bc <> ", " <> fc <> ")")
        -- §18.1.4 __reraiseCause: re-raise a captured Cause as-is (the
        -- join/race/timeout failure arms).  A CK-machine OP_RERAISE node (not the
        -- typed-only kfail bridge): catchable iff the cause is a Fail, else it
        -- propagates to the fiber's Failure(cause) outcome (mirrors
        -- Interp.reraiseCauseValue).  These bodies are already CPS (they await),
        -- so the node is always CK-machine-driven.
        Just "__reraiseCause"
          | [c] <- [a | (Expl, a) <- sargs] -> do
              cc <- compileErasableArg c
              pure ("krt2_reraise(" <> cc <> ")")
        -- §18.1.6 race/timeout: the krt2_race/krt2_timeout node builders (a
        -- krt2_bind tree the CK-machine drives — forks both, awaits the first
        -- signal, interrupts the loser).  The prelude race/timeout bodies are
        -- `ioBind (__race l r) (\o -> match o …)`, so the surrounding ioBind
        -- lowers to krt2_bind (§3.3 has __race/__timeout as suspending).
        Just "__race"
          | [l, r] <- [a | (Expl, a) <- sargs] -> do
              lc <- compileErasableArg l
              rc <- compileErasableArg r
              pure ("krt2_race(" <> lc <> ", " <> rc <> ")")
        Just "__timeout"
          | [d, io] <- [a | (Expl, a) <- sargs] -> do
              dc <- compileErasableArg d
              ic <- compileErasableArg io
              pure ("krt2_timeout(" <> dc <> ", " <> ic <> ")")
        -- §19.5 withScope: run a body with a fresh structured scope, shutting it
        -- down on exit (krt2_with_scope is a krt2_bind tree the CK-machine drives).
        Just "withScope"
          | [use] <- [a | (Expl, a) <- sargs] -> do
              uc <- compileErasableArg use
              pure ("krt2_with_scope(" <> uc <> ")")
        -- §18.1.12 masking: the OP_UNINTERRUPTIBLE/OP_MASK/OP_POLL node builders.
        -- `uninterruptible body` raises mask_depth for the body (krt2_uninterruptible);
        -- `mask`'s surface wrapper forwards to `__mask f`, which the runtime applies
        -- to its `restore` closure (krt2_mask); `poll` is the explicit checkpoint
        -- (krt2_poll). All are CK-machine nodes driven by the do-kernel.
        Just "uninterruptible"
          | [body] <- [a | (Expl, a) <- sargs] -> do
              bc <- compileErasableArg body
              pure ("krt2_uninterruptible(" <> bc <> ")")
        Just "__mask"
          | [f] <- [a | (Expl, a) <- sargs] -> do
              fc <- compileErasableArg f
              pure ("krt2_mask(" <> fc <> ")")
        Just "poll"
          | null [a | (Expl, a) <- sargs] -> pure "krt2_poll()"
        -- §18.1.4 interruption: __interruptWait (request + await termination) and
        -- __interruptNoWait (request, return at once) — OP_INTERRUPT[_FORK] nodes.
        Just "__interruptWait"
          | [cause, fib] <- [a | (Expl, a) <- sargs] -> do
              cc <- compileErasableArg cause
              fc <- compileErasableArg fib
              pure ("krt2_interrupt_as(" <> cc <> ", " <> fc <> ")")
        Just "__interruptNoWait"
          | [cause, fib] <- [a | (Expl, a) <- sargs] -> do
              cc <- compileErasableArg cause
              fc <- compileErasableArg fib
              pure ("krt2_interrupt_fork_as(" <> cc <> ", " <> fc <> ")")
        -- §18.1.13 STM: the journaled monad (stm.c).  The STM do-notation
        -- desugars (via Monad STM) to stmBind/stmPure; the TVar ops + retry are
        -- STM_* tree leaves; `atomically` runs the tree in a transaction
        -- (OP_ATOMICALLY) that journals reads/writes, commits, and retry-parks
        -- the fiber on its read TVars (woken on write).  stmBind/atomically are
        -- ALWAYS nodes (STM is never on the synchronous bridge).
        Just "stmBind"
          | [m, k] <- [a | (Expl, a) <- sargs] -> do
              mc <- compileErasableArg m
              kc <- compileErasableArg k
              pure ("krt2_stm_bind(" <> mc <> ", " <> kc <> ")")
        Just "stmPure"
          | [v] <- [a | (Expl, a) <- sargs] -> do
              vc <- compileErasableArg v
              pure ("krt2_stm_pure(" <> vc <> ")")
        Just "newTVar"
          | [v] <- [a | (Expl, a) <- sargs] -> do
              vc <- compileErasableArg v
              pure ("krt2_new_tvar(" <> vc <> ")")
        Just "readTVar"
          | [tv] <- [a | (Expl, a) <- sargs] -> do
              tc <- compileErasableArg tv
              pure ("krt2_read_tvar(" <> tc <> ")")
        Just "writeTVar"
          | [tv, v] <- [a | (Expl, a) <- sargs] -> do
              tc <- compileErasableArg tv
              vc <- compileErasableArg v
              pure ("krt2_write_tvar(" <> tc <> ", " <> vc <> ")")
        Just "atomically"
          | [s] <- [a | (Expl, a) <- sargs] -> do
              sc <- compileErasableArg s
              pure ("krt2_atomically(" <> sc <> ")")
        Just pname | explArgs@(_ : _) <- [a | (Expl, a) <- sargs] ->
          case Map.lookup pname primEntries of
            -- §34.5.3: a saturated builtin lowers to a DIRECT call on its C
            -- entry point — no string dispatch. A pure builtin: the QW1
            -- positional fast path ('primDirect', no argument array) when
            -- available, else a direct @kpf_x(arr)@. An IO builtin: a
            -- saturated @knative_sat@ (the suspended action krun_io fires by
            -- calling the entry point). Partial / over-application falls
            -- through to the curried bare-reference path (emitPrim → knative).
            Just (PrimEntry cfn ar isio) | length explArgs == ar -> do
              markPrimUsed pname
              aes <- mapM compileErasableArg explArgs
              if isio
                then do
                  arr <- freshN "na_"
                  emit ("KValue *" <> arr <> "[] = {" <> T.intercalate ", " aes <> "};")
                  pure ("knative_sat(" <> cfn <> ", " <> T.pack (show ar) <> ", " <> arr <> ", 1)")
                else case primDirect pname of
                  Just (helper, har) | har == ar ->
                    pure (helper <> "(" <> T.intercalate ", " aes <> ")")
                  _ -> do
                    arr <- freshN "pa_"
                    emit ("KValue *" <> arr <> "[] = {" <> T.intercalate ", " aes <> "};")
                    pure (cfn <> "(" <> arr <> ")")
            _ -> compileAppDefault term -- partial / over-applied: curried path
        Just _ -> compileAppDefault term -- prim with no explicit args yet
        Nothing -> do
          ar <- globFuncArity g
          case ar of
            Just n | length sargs >= n -> compileDirectCall g n sargs
            _ -> compileAppDefault term

-- | Compile @__runIO action@.  A mutable-reference action (@readRef@ /
-- @writeRef@ / @newRef@, §18.6.1) run inline is lowered directly to the
-- @kref_*@ operation, skipping the suspend-as-action-then-krun_io path —
-- a mutable @var@ read/write in a loop is then a single cell access, not a
-- per-step primitive allocation + dispatch.  Any other action keeps the
-- general @krun_io@ lowering.
compileRunIO :: Term -> Gen Text
compileRunIO action = do
  let (hd, sargs) = spineOf action
      expl = [a | (Expl, a) <- sargs]
  mp <- case hd of CGlob g -> globPrimName g; _ -> pure Nothing
  case (mp, expl) of
    (Just "readRef", [r]) -> do
      re <- compile r
      pure ("kref_get(" <> re <> ")")
    (Just "writeRef", [r, v]) -> do
      re <- compile r
      ve <- compile v
      pure ("kref_set(" <> re <> ", " <> ve <> ")")
    (Just "newRef", [v]) -> do
      ve <- compile v
      pure ("kref_new(" <> ve <> ")")
    _ -> do
      ae <- compile action
      pure ("krun_io_checked(" <> ae <> ")")

-- | The worker arity of a function global @g@ — its leading-lambda count,
-- if @g@ has a recorded core body that is lowered to a worker (≥ 1 binder
-- via 'compileFunctionGlobal').  'Nothing' for CAFs, primitives, and
-- constructors (which have no worker to call directly).
globFuncArity :: GName -> Gen (Maybe Int)
globFuncArity g = do
  bodies <- gets gsBodies
  pure $ case Map.lookup g bodies of
    Just tm | (n, _) <- funcArity tm, n >= 1 -> Just n
    _ -> Nothing

-- | Can the boxed worker for @g@ (arity @n@, recorded body @body@) EVER return
-- a @K_BOUNCE@?  A worker returns a bounce only from a tail-position general
-- application ('emitTailApp's @kbounce@) — a tail @CApp Expl@ whose head is not
-- a prim, not a saturated self-call (which loops in place), and not an
-- eta-expanded constructor (which builds a value, R1.1).  Self-loops, leaf
-- values, prim/ctor results, the IO do-kernel (which returns @K_IOTAIL@
-- markers, NOT bounces), and @if@/@match@/@let@ over those never bounce.
-- Conservative: anything not provably bounce-free counts as may-bounce.  When
-- 'False', a saturated call can drop the 'ktrampoline' wrapper, since
-- @ktrampoline@ drains only @K_BOUNCE@ and passes every other value through
-- untouched — so @ktrampoline(kw_g(…)) ≡ kw_g(…)@ for a non-bouncing worker
-- (P1-E / R3.1).
--
-- This is the dual of 'emitTailApp': it must classify a tail position as
-- "bounces" exactly when 'emitTailApp' would emit @return kbounce(…)@ for it.
-- The two are coupled — if 'emitTailApp' grows a new @kbounce@ arm, this
-- analysis must grow with it or it becomes UNSOUND (a dropped trampoline is a
-- stack overflow at scale).  'consume' reaches a worker's tail positions
-- through @if@/@match@/@let@; only a tail @CApp Expl@ that is not a saturated
-- self-call (loops), a prim spine, or an eta-ctor (a value) actually bounces.
--
-- Lowered-IR implication: a function carries a "tail-call/bounce effect" bit;
-- a call to a callee with no such effect needs no trampoline drain (it lowers
-- to a direct call), realizing the §7 "trampolines → loop/musttail/direct vs
-- boxed-trampoline fallback" requirement for the non-bouncing case.
--
-- Cache invariant: during one 'generateC' run, 'gsBodies' is immutable and
-- each @(GName, arity)@ denotes a single worker body.  The cache key can
-- therefore omit the 'body' argument; it is still passed explicitly so callers
-- that have already looked up the body do not repeat that lookup.
workerMayBounce :: GName -> Int -> Term -> Gen Bool
workerMayBounce g n body = do
  memo <- gets gsBounceMemo
  case Map.lookup (g, n) memo of
    Just (Just b) -> pure b
    Just Nothing -> pure True
    Nothing -> do
      modify' $ \st -> st {gsBounceMemo = Map.insert (g, n) Nothing (gsBounceMemo st)}
      b <- workerMayBounceUncached g n body
      modify' $ \st -> st {gsBounceMemo = Map.insert (g, n) (Just b) (gsBounceMemo st)}
      pure b

workerMayBounceUncached :: GName -> Int -> Term -> Gen Bool
workerMayBounceUncached g n = tailMay
  where
    tailMay term = case term of
      CIf _ t e -> orM [tailMay t, tailMay e]
      CMatch _ _ alts -> orM [tailMay b | CaseAlt _ _ b <- alts]
      CLet _ _ _ _ body -> tailMay body
      CLetRec _ _ _ _ body -> tailMay body
      _
        -- a saturated self-call loops in place; 'lr1SelfArgs' is the shared
        -- recognizer (explicit-arg count == n) — intentionally stricter than
        -- 'selfTailArgs' (full-spine count), which only ever makes this MORE
        -- conservative (keeps a trampoline), never unsound.
        | Just _ <- lr1SelfArgs g n term -> pure False
        | CApp Expl _ _ <- term -> do
            let (hd, _) = spineOf term
            prim <- case hd of CGlob h -> globPrimName h; _ -> pure Nothing
            pure $ case (prim, etaCtorApp term) of
              (Nothing, Nothing) -> True -- a general tail call → kbounce
              _ -> False -- prim spine / eta-ctor → returns a value
        | otherwise -> pure False -- a leaf value / IO action (no bounce)

-- | A saturated (or over-saturated) call to a known function global: call
-- its worker @kw_…@ directly with the leading @n@ arguments instead of
-- building and draining a curried arity-1 closure chain.  The worker's result
-- is driven through 'ktrampoline' ONLY when its body can return a tail-call
-- bounce ('workerMayBounce'); a provably non-bouncing worker is called
-- directly (R3.1).  Any surplus arguments are then applied normally.
-- Type-level/staging arguments are erased (§31.2).
compileDirectCall :: GName -> Int -> [(Icit, Term)] -> Gen Text
compileDirectCall g n sargs = do
  enqueue g
  mplan <- scalarPlan g
  case mplan of
    -- LR1/R2.2: an exactly-saturated call to a scalar-eligible worker takes the
    -- unboxed fast path (with a boxed escape).  Surplus args / partial calls
    -- keep the boxed worker.
    Just (pks, ret) | length pks == n, length sargs == n -> compileScalarCall g pks ret sargs
    _ -> do
      let (callArgs, extra) = splitAt n sargs
          worker = "kw_" <> mangle (gKey g)
      aes <- mapM (compileErasableArg . snd) callArgs
      bodies <- gets gsBodies
      mayBounce <- case Map.lookup g bodies of
        Just body | (_, inner) <- funcArity body -> workerMayBounce g n inner
        Nothing -> pure True -- no recorded body → keep the trampoline
      let call = worker <> "(" <> T.intercalate ", " aes <> ")"
          base = if mayBounce then "ktrampoline(" <> call <> ")" else call
      foldM applyExtra base extra
  where
    applyExtra acc (Expl, a) = do
      ae <- compileErasableArg a
      pure ("kapp(" <> acc <> ", " <> ae <> ")")
    applyExtra acc (Impl, a) = do
      ae <- compileErasableArg a
      pure ("kappi(" <> acc <> ", " <> ae <> ")")

-- | The general curried application lowering (one 'kapp'/'kappi' per arg).
compileAppDefault :: Term -> Gen Text
compileAppDefault = \case
  CApp Expl f a -> do
    fe <- compile f
    ae <- compileErasableArg a -- §31.2: an explicit type-level/staging arg is erased
    pure ("kapp(" <> fe <> ", " <> ae <> ")")
  CApp Impl f a -> do
    erased <- isErasedHead f
    if erased
      then compile f -- implicit arg to a prim/constructor: erased (§31.2)
      else do
        fe <- compile f
        ae <- compileErasableArg a
        pure ("kappi(" <> fe <> ", " <> ae <> ")")
  t -> compile t

compileGlob :: GName -> Gen Text
compileGlob g@(GName m nm)
  | m == primModule = emitPrim nm
  | otherwise = do
      globals <- gets gsGlobals
      ctors <- gets gsCtors
      hostSyms <- gets gsHostSyms
      case Map.lookup g globals of
        -- A prelude `prim` registration: its value is a bare VPrim, so it
        -- maps directly to the runtime primitive of the same name.
        Just gd | Just (VPrim pname _) <- gdValue gd ->
          emitPrim pname
        -- §27.1.1: a provided host-binding member (an abstract global of a
        -- manifest-selected `host.native.*` module) lowers to a curried
        -- native action carrying the codegen-emitted wrapper pointer — a
        -- DIRECT typed call, no runtime name dispatch. The wrapper + extern
        -- prototype are emitted by 'assemble' for each used member. The
        -- gname→symbol map is built per build from the manifest's native
        -- bindings (never a hardcoded catalog).
        Just gd
          | Nothing <- gdValue gd
          , Just rns <- Map.lookup g hostSyms ->
              emitHostNative g rns
        _ -> case Map.lookup g ctors of
          Just ci ->
            -- A nullary constructor used as a value builds directly (the
            -- 'Repr.LayoutImmediate' / @b010@ case). A positive-arity
            -- constructor reference is eta-expanded to a saturated CCtor under
            -- lambdas by elaboration (§10.1 etaCtor), so a bare positive-arity
            -- ctor never reaches codegen for an accepted program; treat it as
            -- an internal invariant.
            case Repr.ctorLayoutByArity (length (ciFields ci)) of
              Repr.LayoutImmediate -> do
                tc <- ctorTagConst g
                pure ("kctor0(" <> tc <> ", " <> cStr (gKey g) <> ")")
              _ -> escalated "bare-ctor"
                ("constructor '" <> nm <> "' is referenced un-eta-expanded; \
                 \accepted programs eta-expand constructor values (§10.1)")
          Nothing -> do
            enqueue g
            pure (cGlobIdent g <> "()")

compileLit :: Literal -> Gen Text
compileLit = \case
  LitInt n
    | n >= toInteger (minBound :: Int) && n <= toInteger (maxBound :: Int) ->
        pure ("kint(" <> intLit n <> ")")
    -- §6: Integer is unbounded; a literal beyond int64 is a runtime bignum.
    | otherwise -> pure ("kbigint_str(" <> cStr (T.pack (show n)) <> ")")
  LitDouble d -> pure ("kdbl(" <> T.pack (show d) <> ")")
  LitStr s -> pure (cStrL s)
  LitScalar c -> pure ("kchr(" <> T.pack (show (ord c)) <> ")")
  -- §6.5 byte literal: a single octet.
  LitByte w -> pure ("kbyte(" <> T.pack (show (fromIntegral w :: Int)) <> ")")
  -- §29.5 byte-sequence literal: the exact byte content.  kbytes copies the
  -- bytes into GC memory, so a block-scoped compound literal is safe.
  LitBytes bs -> pure (cBytesLit bs)
  -- §6.5 grapheme literal: an exact scalar sequence rendered as UTF-8 text.
  LitGrapheme g -> pure (cStrL g)
  where
    intLit = cIntLit

-- | A C @int64_t@ literal for an in-range integer.  @INT64_MIN@ has no
-- positive counterpart in C (its magnitude overflows @long long@), so it
-- is emitted via the @<stdint.h>@ macro rather than @(-9223372036854775808LL)@.
cIntLit :: Integer -> Text
cIntLit n
  | n == toInteger (minBound :: Int) = "INT64_MIN"
  | n < 0 = "(-" <> T.pack (show (abs n)) <> "LL)"
  | otherwise = T.pack (show n) <> "LL"

-- | A C @double@ literal, using the SAME shortest round-trippable text as the
-- boxed @kdbl@ path (so the unboxed and boxed paths parse to the identical
-- double).  A source @LitDouble@ is finite, so 'show' never yields
-- Infinity/NaN, and Haskell's @Double@ 'show' always includes a @.@ or @e@, so
-- the text is always a valid C floating (double) literal.
cDblLit :: Double -> Text
cDblLit = T.pack . show

-- | A §29.5 byte-sequence literal.  @kbytes@ copies its input into GC
-- memory, so a block-scoped compound literal of @unsigned char@ is safe;
-- the empty sequence avoids a zero-length array (ill-formed in ISO C).
cBytesLit :: ByteString -> Text
cBytesLit bs
  | BS.null bs = "kbytes((const unsigned char *)\"\", 0)"
  | otherwise =
      "kbytes((const unsigned char[]){"
        <> T.intercalate "," [T.pack (show (fromIntegral w :: Int)) | w <- BS.unpack bs]
        <> "}, "
        <> T.pack (show (BS.length bs))
        <> ")"

-- | A lambda: lift its body into a fresh top-level closure function and
-- return a @kclo@ capturing the current environment.
compileLam :: Term -> Gen Text
compileLam body = do
  fnName <- freshFn "kfn_"
  env <- gets gsEnv -- the captured environment at closure creation
  -- The body is compiled in the 'SinkBounce' tail sink so a tail-position
  -- application (e.g. the recursive call of a local @let rec@ lambda) defers to
  -- the driving trampoline (§27.5A.3) rather than recursing in the C stack.
  --
  -- R3.2 FLAT CLOSURE: when the body is capture-free (no nested closure/thunk/do
  -- captures the parameter by reference), the parameter is read DIRECTLY as the
  -- C argument @arg@ (de Bruijn 0, via 'gsParamLvals') and let/match locals are
  -- flat C locals — NO per-application @kpush(arg, cenv)@.  Captured free vars
  -- (de Bruijn ≥ 1) are read from @cenv@ via the shifted 'CVar' fallback.  When
  -- the body captures the env, the parameter must live in a real @KEnv@ (a
  -- nested closure captures it by reference), so build @kpush(arg, cenv)@ as
  -- before and read everything via it (gsParamLvals empty).
  let flat = not (bodyCapturesEnv body)
  saved <- gets gsParamLvals
  bodyEnv <- if flat then pure "cenv" else freshN "lenv_"
  modify' $ \st -> st {gsParamLvals = if flat then ["arg"] else []}
  (stmts, ()) <- captured bodyEnv (consume SinkBounce body)
  modify' $ \st -> st {gsParamLvals = saved}
  -- non-flat: materialise kpush(arg, cenv) only when a variable is read (a
  -- constant lambda references neither — keeps the C -Wall clean).
  let usesEnv = (not flat) && any (T.isInfixOf bodyEnv) stmts
      envDecl = ["  KEnv *" <> bodyEnv <> " = kpush(arg, cenv);" | usesEnv]
      fn =
        T.unlines $
          [ "static KValue *" <> fnName <> "(KEnv *cenv, KValue *arg) {"
          , "  (void)cenv; (void)arg;"
          ]
            ++ envDecl
            ++ map ("  " <>) stmts
            ++ [ "}"
               ]
  modify' $ \st ->
    st
      { gsTop = fn : gsTop st
      , gsProtos = ("static KValue *" <> fnName <> "(KEnv *, KValue *);") : gsProtos st
      }
  pure ("kclo(" <> fnName <> ", " <> env <> ")")

compileCtor :: GName -> [Term] -> Gen Text
compileCtor g args = do
  -- §31.2: erase type-level / staging fields to a unit placeholder so the
  -- constructor's runtime arity (and positional projection) is preserved
  -- without compiling a type/quote value (which the interpreter stores but
  -- never inspects).
  argEs <- mapM compileErasableArg args
  tc <- ctorTagConst g
  -- KBackendIR Stage 2: the nullary ⇒ canonical @b010@ immediate decision is
  -- 'Repr.ctorLayoutByArity' (shared with the LLVM backend); 'Repr.LayoutImmediate'
  -- lowers to @kctor0@, anything else builds a boxed @kctor@ over its fields.
  case Repr.ctorLayoutByArity (length argEs) of
    Repr.LayoutImmediate -> pure ("kctor0(" <> tc <> ", " <> cStr (gKey g) <> ")")
    _ -> do
      arr <- freshN "args_"
      emit ("KValue *" <> arr <> "[] = {" <> T.intercalate ", " argEs <> "};")
      pure ("kctor(" <> tc <> ", " <> cStr (gKey g) <> ", " <> T.pack (show (length argEs)) <> ", " <> arr <> ")")

compileRecord :: [(Text, Term)] -> Gen Text
compileRecord fs = do
  valEs <- mapM (compileErasableArg . snd) fs
  namesArr <- freshN "rnames_"
  valsArr <- freshN "rvals_"
  let names = T.intercalate ", " [cStr n | (n, _) <- fs]
  -- The names array must outlive this C stack frame: krec stores the
  -- pointer without copying (the field labels are compile-time string
  -- literals), so a record built in a CAF accessor / closure and projected
  -- later would otherwise read a dangling stack array.  Emit it as static.
  emit ("static const char *" <> namesArr <> "[] = {" <> names <> "};")
  emit ("KValue *" <> valsArr <> "[] = {" <> T.intercalate ", " valEs <> "};")
  pure ("krec(" <> T.pack (show (length fs)) <> ", " <> namesArr <> ", " <> valsArr <> ")")

withEnv :: Text -> Gen a -> Gen a
withEnv e act = do
  saved <- gets gsEnv
  modify' $ \g -> g {gsEnv = e}
  r <- act
  modify' $ \g -> g {gsEnv = saved}
  pure r

-- ── Result sinks (shared by if/match/let in both expression and
-- function-body-tail position) ──────────────────────────────────────

-- | The self-recursion context of the function currently being compiled
-- as a worker: a saturated tail call to it becomes a loop instead of a C
-- call (see 'compileFunctionGlobal').
data TailInfo = TailInfo
  { tiName :: !GName -- ^ the worker's own global
  , tiArity :: !Int -- ^ number of leading binders
  , tiSlots :: ![Text] -- ^ the per-parameter update targets, in binder order: the mutable C parameter variables @p0@…@p{n-1}@.  A tail self-call evaluates its new args into temps then reassigns these (FLAT: params are direct C locals; REBUILD: the loop top rebuilds @kw_env@ from the reassigned params)
  }

-- | Where a computed value flows: into a C variable (expression context),
-- out of a worker as its tail result (a top-level function's tail position,
-- where a saturated self-call becomes a loop), or out of a closure/local
-- let-rec lambda body in tail position (where a tail application becomes a
-- trampoline 'kbounce' so local/mutual tail recursion runs in constant C
-- stack, §27.5A.3 — there are no worker params to loop on).
data Sink = SinkVar !Text | SinkTail !TailInfo | SinkBounce

sinkResult :: Sink -> Text -> Gen ()
sinkResult (SinkVar r) e = emit (r <> " = " <> e <> ";")
sinkResult (SinkTail _) e = emit ("return " <> e <> ";")
sinkResult SinkBounce e = emit ("return " <> e <> ";")

-- | Does @term@ compile to a CK-machine action NODE (krt2_bind/then/reraise) via
-- 'compileAppGlob's special cases?  In tail position such a node must be RETURNED
-- so the CK-machine drives it next — NOT handed to 'emitTailApp's per-argument
-- trampoline, which compiles the prim head as a bare reference ('emitPrim') and
-- loses the lowering (and rejects @__reraiseCause@, which has no @primEntry@).
cpsNodeApp :: Term -> Gen Bool
cpsNodeApp term = do
  let (hd, sargs) = spineOf term
  case hd of
    CGlob g -> do
      mp <- globPrimName g
      susp <- gets gsSuspenders
      pure $ case (mp, [a | (Expl, a) <- sargs]) of
        (Just "ioBind", [m, _]) -> mayActSuspend susp m
        (Just "ioThen", [m, _]) -> mayActSuspend susp m
        (Just "catchIO", [body, _]) -> mayActSuspend susp body
        (Just "finallyIO", [body, _]) -> mayActSuspend susp body
        (Just "__reraiseCause", [_]) -> True
        (Just "__race", [_, _]) -> True
        (Just "__timeout", [_, _]) -> True
        (Just "withScope", [_]) -> True
        (Just "uninterruptible", [_]) -> True
        (Just "__mask", [_]) -> True
        (Just "poll", []) -> True
        (Just "__interruptWait", [_, _]) -> True
        (Just "__interruptNoWait", [_, _]) -> True
        (Just "atomically", [_]) -> True
        (Just "stmBind", [_, _]) -> True
        _ -> False
    _ -> pure False

-- | Compile @term@ so its value flows to @sink@, recursing through the
-- control forms (if/match/let) so that a self-tail-call deep inside a
-- branch is lowered to a loop rather than a recursive C call.  This single
-- traversal serves both expression context ('SinkVar') and the worker's
-- tail position ('SinkTail'), so the two can never drift.
consume :: Sink -> Term -> Gen ()
consume sink term = case term of
  CIf c t e -> consumeIf sink c t e
  CMatch scrut _ alts -> consumeMatch sink scrut alts
  CLet _ _ _ rhs body -> do
    -- erase a type-level / staging binding (e.g. `let t = Int`) to the unit
    -- placeholder (§31.2) rather than compiling it as a value.
    re <- compileErasableArg rhs
    lvals <- gets gsParamLvals
    if null lvals
      then do
        -- boxed worker: push the binding onto the KEnv chain.
        env <- gets gsEnv
        e2 <- freshN "env_"
        emit ("KEnv *" <> e2 <> " = kpush(" <> re <> ", " <> env <> ");")
        withEnv e2 (consume sink body)
      else do
        -- R2.3-rest FLAT worker: bind a C local (no KEnv); 'bindFlatLocal'
        -- prepends it as de Bruijn index 0 and the enclosing 'captured' block
        -- (or the worker-body reset) restores the scope.
        _ <- bindFlatLocal "let_" re
        consume sink body
  -- A local recursive let: allocate the binder cell, evaluate the rhs
  -- (a function whose closure captures the cell but does not read it until
  -- applied), then back-patch (docs/NATIVE_BACKEND.md §5).
  CLetRec _ _ _ rhs body -> do
    env <- gets gsEnv
    e2 <- freshN "env_"
    emit ("KEnv *" <> e2 <> " = kpush(kunit(), " <> env <> ");")
    re <- withEnv e2 (compile rhs)
    emit (e2 <> "->val = " <> re <> ";")
    withEnv e2 (consume sink body)
  _ -> do
    isCps <- cpsNodeApp term
    case sink of
      -- Direct saturated self-call: loop in the worker (no allocation).
      SinkTail ti | Just args <- selfTailArgs ti term -> emitTailLoop ti args
      -- A suspending ioBind/ioThen or __reraiseCause in tail position lowers to a
      -- CK-machine NODE (compileAppGlob): RETURN it so the machine drives it, not
      -- emitTailApp (which would lose the lowering — see 'cpsNodeApp').
      SinkTail _ | CApp Expl _ _ <- term, isCps -> compile term >>= sinkResult sink
      -- Any other tail-position explicit application: return a trampoline
      -- bounce so the chain (mutual recursion, calls through a value, local
      -- let-rec) runs in constant C stack (§27.5A.3); the driving trampoline
      -- is the kapp/kappi at the non-tail site that demanded the value.
      SinkTail _ | CApp Expl _ _ <- term -> emitTailApp term
      -- A closure / local let-rec lambda body in tail position: the same bounce,
      -- so a tail self-call defers to the driving trampoline (constant C stack).
      SinkBounce | CApp Expl _ _ <- term, isCps -> compile term >>= sinkResult sink
      SinkBounce | CApp Expl _ _ <- term -> emitTailApp term
      _ -> do
        e <- compile term
        sinkResult sink e

-- | Compile an if/match/let in expression context: declare a fresh result
-- variable and consume into it.
sinkToExpr :: Term -> Gen Text
sinkToExpr term = do
  r <- freshN "r_"
  emit ("KValue *" <> r <> " = 0;")
  consume (SinkVar r) term
  pure r

consumeIf :: Sink -> Term -> Term -> Term -> Gen ()
consumeIf sink c t e = do
  ce <- compile c
  env <- gets gsEnv
  (tStmts, ()) <- captured env (consume sink t)
  (eStmts, ()) <- captured env (consume sink e)
  emit ("if (kas_bool(" <> ce <> ")) {")
  forM_ tStmts (emit . ("  " <>))
  emit "} else {"
  forM_ eStmts (emit . ("  " <>))
  emit "}"

-- ── Pattern matching ─────────────────────────────────────────────────

consumeMatch :: Sink -> Term -> [CaseAlt] -> Gen ()
consumeMatch sink scrut alts = do
  se <- compile scrut
  sv <- freshN "scrut_"
  emit ("KValue *" <> sv <> " = " <> se <> ";")
  env <- gets gsEnv
  done <- freshN "matched_"
  emit ("int " <> done <> " = 0;")
  -- §17.2.3: an or-pattern whose alternatives list the shared binders in a
  -- different order than the first needs a per-alternative de-Bruijn body
  -- permutation; the native backend distributes alternatives over a shared
  -- body and does not perform it, so refuse rather than miscompile. (The
  -- interpreter — the §27 conformance engine — handles this case.)
  forM_ alts $ \(CaseAlt pat _ _) ->
    when (orReordered pat) $
      void $
        unsupported "or-pattern-reordered-binders"
          "an or-pattern alternative that binds the shared names in a different order than the first alternative is not supported by the native backend (use a consistent binder order across alternatives)"
  forM_ (concatMap expandTopOr alts) $ \alt -> consumeAlt sink sv env done alt
  emit ("if (!" <> done <> ") krt_fail(\"non-exhaustive match\");")

-- | Whether a pattern contains an or-pattern whose alternatives bind the shared
-- names in a non-canonical order (a non-identity permutation on some
-- alternative) — see 'consumeMatch'.
orReordered :: CorePat -> Bool
orReordered = \case
  CPOr ps perms -> any (\pm -> pm /= [0 .. length pm - 1]) perms || any orReordered ps
  CPCtor _ _ ps -> any orReordered ps
  CPTuple ps -> any orReordered ps
  CPRecord fs _ -> any (orReordered . snd) fs
  CPInject _ p -> orReordered p
  CPAs _ p -> orReordered p
  _ -> False

-- | §17.2.3: a top-level or-pattern alternative is equivalent to one
-- alternative per branch (matchPat's firstJust, in order), with the same
-- guard and body. Splitting here lets each branch's variable bindings be
-- handled by the ordinary single-pattern path, so or-patterns that bind
-- variables work without decision-tree compilation.
expandTopOr :: CaseAlt -> [CaseAlt]
expandTopOr (CaseAlt pat g body) = [CaseAlt p g body | p <- distributePat pat]

-- | §17.2.3: expand a pattern into the list of or-free patterns it denotes,
-- distributing every nested 'CPOr' as the Cartesian product over its
-- positions (left-to-right, matching the interpreter's first-match order).
-- Each or-branch binds the same variables, so all expansions share the
-- alternative's guard and body; the resulting or-free patterns are then
-- handled by the ordinary single-pattern test/binding path.
distributePat :: CorePat -> [CorePat]
distributePat = \case
  CPOr ps _ -> concatMap distributePat ps
  CPCtor g nEx ps -> [CPCtor g nEx qs | qs <- mapM distributePat ps]
  CPTuple ps -> [CPTuple qs | qs <- mapM distributePat ps]
  CPRecord fs rest ->
    let (names, pats) = unzip fs
     in [CPRecord (zip names qs) rest | qs <- mapM distributePat pats]
  CPInject t p -> [CPInject t q | q <- distributePat p]
  CPAs n p -> [CPAs n q | q <- distributePat p]
  p -> [p] -- CPWild / CPVar / CPLit / CPInjectRest: no nested or

consumeAlt :: Sink -> Text -> Text -> Text -> CaseAlt -> Gen ()
consumeAlt sink sv env done (CaseAlt pat mguard body) = do
  emit ("if (!" <> done <> ") {")
  -- pattern test + bindings produced as a nested block
  (blk, ()) <- captured env $ do
    mtest <- patTest sv pat
    case mtest of
      Nothing -> consumeAltBody sink sv env done pat mguard body
      Just test -> do
        emit ("if (" <> test <> ") {")
        consumeAltBody sink sv env done pat mguard body
        emit "}"
  forM_ blk (emit . ("  " <>))
  emit "}"

-- | Bind the pattern variables, evaluate the optional guard, and on a full
-- match consume the body into the sink (and mark @done@; for a 'SinkTail'
-- body the @done@ store is dead — the body has returned/looped — but
-- harmless).
consumeAltBody :: Sink -> Text -> Text -> Text -> CorePat -> Maybe Term -> Term -> Gen ()
consumeAltBody sink sv env done pat mguard body = do
  -- patTest already verified the constructor/shape; bindings just project.
  env' <- bindPatScrut sv env pat
  case mguard of
    Nothing -> do
      withEnv env' (consume sink body)
      emit (done <> " = 1;")
    Just gd -> do
      ge <- withEnv env' (compile gd)
      emit ("if (kas_bool(" <> ge <> ")) {")
      withEnv env' (consume sink body)
      emit ("  " <> done <> " = 1;")
      emit "}"

-- | A C boolean expression that is true iff @pat@ matches the value @v@
-- (a pure expression; no side effects, no bindings).  'Nothing' means the
-- pattern always matches (e.g. a variable or wildcard).
patTest :: Text -> CorePat -> Gen (Maybe Text)
patTest v = \case
  CPWild -> pure Nothing
  CPVar _ -> pure Nothing
  CPAs _ p -> patTest v p
  CPLit l -> do
    le <- litValue l
    case le of
      Just lv -> pure (Just ("klit_eq(" <> v <> ", " <> lv <> ")"))
      Nothing -> pure (Just "0") -- unsupported literal: never matches (error already recorded)
  CPCtor g _ ps -> do
    let nps = length ps
    subs <- forM (zip [0 ..] ps) $ \(i, p) ->
      patTest (ctorArgExpr v nps i) p
    -- LR2: dispatch on the numeric ctor identity (int compare) rather than a
    -- kctor_is strcmp.  kctor_tagid returns -1 for a non-ctor scrutinee, so
    -- this preserves the `v->tag == K_CTOR &&` type guard kctor_is carried.
    tc <- ctorTagConst g
    let here = "kctor_tagid(" <> v <> ") == " <> tc
    pure (Just (conj (here : [t | Just t <- subs])))
  CPTuple ps -> do
    let n = length ps
    subs <- forM (zip [0 ..] ps) $ \(i, p) ->
      patTest (recAtExpr v i) p
    let szTest = "krec_size(" <> v <> ") == " <> T.pack (show n)
    pure (Just (conj (szTest : [t | Just t <- subs])))
  -- §17.2.5: a record pattern's rest binder always matches; the named
  -- fields determine the test (with or without a rest binder).
  CPRecord pfs _ -> recordTests v pfs
  CPOr ps _ -> do
    -- Top-level binding or-patterns are split into separate alternatives
    -- before reaching here (see consumeMatch), so any CPOr that arrives is
    -- nested. Non-binding nested ors disjoin their tests; a nested or that
    -- binds variables would need decision-tree compilation.
    if all bindsNothing ps
      then do
        subs <- mapM (patTest v) ps
        pure (Just (disj [maybe "1" id t | t <- subs]))
      else do
        _ <- unsupported "CPOr-nested-binding"
          "a nested or-pattern that binds variables is not supported (lift it to top-level alternatives)"
        pure (Just "0")
  -- §13 variant patterns: tag match + payload sub-test.
  CPInject tag p -> do
    sub <- patTest ("kvariant_payload(" <> v <> ")") p
    -- LR2: numeric variant dispatch (kvariant_tagid -> -1 for a non-variant).
    tc <- variantTagConst tag
    let here = "kvariant_tagid(" <> v <> ") == " <> tc
    pure (Just (conj (here : [t | Just t <- [sub]])))
  -- §13 residual-row pattern: a variant whose tag is none of the excluded.
  CPInjectRest excl -> do
    tcs <- mapM variantTagConst excl
    pure (Just (conj ("kis_variant(" <> v <> ")" : ["kvariant_tagid(" <> v <> ") != " <> tc | tc <- tcs])))
  where
    recordTests rv pfs = do
      subs <- forM pfs $ \(n, p) -> patTest ("kproj(" <> rv <> ", " <> cStr n <> ")") p
      case [t | Just t <- subs] of
        [] -> pure Nothing
        ts -> pure (Just (conj ts))

-- | The C expression for the i-th bound argument of a constructor value
-- @v@ whose pattern binds @nps@ trailing arguments (matchPat drops the
-- leading non-bound arguments).
ctorArgExpr :: Text -> Int -> Int -> Text
ctorArgExpr v nps i =
  "kctor_arg(" <> v <> ", kctor_argc(" <> v <> ") - " <> T.pack (show nps) <> " + " <> T.pack (show i) <> ")"

recAtExpr :: Text -> Int -> Text
recAtExpr v i = "krec_at(" <> v <> ", " <> T.pack (show i) <> ")"

-- | C expression for a §17.2.5 record rest binder: @rec@ minus the named
-- fields, passing the excluded names via a C99 compound literal.
recWithoutExpr :: Text -> [Text] -> Text
recWithoutExpr v names
  | null names = "krec_without(" <> v <> ", 0, 0)"
  | otherwise =
      "krec_without(" <> v <> ", " <> T.pack (show (length names))
        <> ", (const char*[]){" <> T.intercalate ", " (map cStr names) <> "})"

conj :: [Text] -> Text
conj [] = "1"
conj [x] = x
conj xs = "(" <> T.intercalate " && " xs <> ")"

disj :: [Text] -> Text
disj [] = "0"
disj [x] = x
disj xs = "(" <> T.intercalate " || " xs <> ")"

bindsNothing :: CorePat -> Bool
bindsNothing = \case
  CPWild -> True
  CPLit _ -> True
  -- @nEx@ skolem placeholder slots ARE bindings, so a ctor pattern with
  -- existentials does not "bind nothing".
  CPCtor _ nEx ps -> nEx == 0 && all bindsNothing ps
  CPTuple ps -> all bindsNothing ps
  CPOr ps _ -> all bindsNothing ps
  CPInjectRest _ -> True
  _ -> False

-- | The values a pattern binds, as C expressions over the scrutinee
-- expression @sv@, in matchPat's left-to-right binding order (rightmost
-- binder ends up at de Bruijn index 0).
patBindings :: Text -> CorePat -> [Text]
patBindings = go
  where
    go v = \case
      CPWild -> []
      CPLit _ -> []
      CPVar _ -> [v]
      CPAs _ p -> v : go v p
      CPCtor _ nEx ps ->
        -- §17.1: the @nEx@ existential-skolem slots come FIRST, so after the
        -- match path reverses the binding list they land BELOW the field binders
        -- — exactly where 'ctorFieldTypesCtx' bound the skolems. They are erased
        -- types never read at runtime; @kunit()@ is the placeholder (mirrors the
        -- interpreter's 'VRecordV []' and the LLVM backend's unit placeholder).
        let nps = length ps
         in replicate nEx "kunit()"
              ++ concat [go (ctorArgExpr v nps i) p | (i, p) <- zip [0 ..] ps]
      CPTuple ps -> concat [go (recAtExpr v i) p | (i, p) <- zip [0 ..] ps]
      -- §17.2.5: named-field bindings, then (if a non-discard rest binder)
      -- the remaining fields as a narrower record — matchPat's order.
      CPRecord pfs mrest ->
        concat [go ("kproj(" <> v <> ", " <> cStr n <> ")") p | (n, p) <- pfs]
          ++ case mrest of
            Just nm | not (T.null nm) -> [recWithoutExpr v (map fst pfs)]
            _ -> []
      CPOr _ _ -> [] -- only non-binding or-patterns reach here
      -- §13 variant payload / whole-value bindings (matchPat semantics).
      CPInject _ p -> go ("kvariant_payload(" <> v <> ")") p
      CPInjectRest _ -> [v]

litValue :: Literal -> Gen (Maybe Text)
litValue = \case
  LitInt n
    | n >= toInteger (minBound :: Int) && n <= toInteger (maxBound :: Int) ->
        pure (Just ("kint(" <> cIntLit n <> ")"))
    -- §6: an out-of-int64 integer literal pattern is a bignum (klit_eq
    -- compares K_BIGINT via mpz).
    | otherwise -> pure (Just ("kbigint_str(" <> cStr (T.pack (show n)) <> ")"))
  LitStr s -> pure (Just (cStrL s))
  LitScalar c -> pure (Just ("kchr(" <> T.pack (show (ord c)) <> ")"))
  LitDouble d -> pure (Just ("kdbl(" <> T.pack (show d) <> ")"))
  -- §6.5/§29.5 byte/bytes/grapheme literal patterns (klit_eq compares
  -- K_BYTE by octet, K_BYTES by content, grapheme as K_STR by bytes).
  LitByte w -> pure (Just ("kbyte(" <> T.pack (show (fromIntegral w :: Int)) <> ")"))
  LitBytes bs -> pure (Just (cBytesLit bs))
  LitGrapheme g -> pure (Just (cStrL g))

-- ── do-kernel ────────────────────────────────────────────────────────

-- | §18.1 CPS do-kernel (Stage 1).  A do-block whose binds reach a SUSPENDING
-- operation (fork/await/sleepFor/cede/awaitPromiseExit/…) cannot run on the
-- synchronous @krun_io@ bridge — the fiber must be able to park.  Such a block
-- is lowered to a @krt2_*@ action TREE the CK-machine drives node-by-node
-- (parking at OP_FORK/OP_AWAIT/…), instead of a @kio@ do-fn.
--
-- Detection is the CPS-DESIGN §3.3 suspendability analysis: a bind whose action
-- reaches a suspending primitive — directly OR transitively through the call
-- graph ('suspenderGlobals') — may suspend, so the block is CPS-lowered.  This
-- catches a user helper that forks/awaits, not only a literal @fork@/@await@.
-- A suspending op inside a defer/loop/if/var/return block is Stage-2 work and is
-- not yet CPS-lowered ('cpsEligible' is False); such a block is DIAGNOSED
-- (fail-closed in 'compileDo'), not mis-run on the bridge.
-- The wired-and-tested suspending operations, by name.  Only the surface
-- (preludeModule) and prim (primModule) globals are matched — a user global
-- named e.g. @join@/@race@/@timeout@ in another module never triggers CPS.
-- (Stage-3 ops — forkIn/shutdownScope/awaitMonitor — and the derived
-- join/race/timeout are added here as each is wired and tested.)
suspendingNames :: Set Text
suspendingNames =
  Set.fromList
    [ "fork", "forkDaemon", "await", "awaitPromise" -- surface (std.prelude)
    , "__forkRun", "__forkDaemon", "__awaitFiber" -- prims (__prim)
    , "cede", "__sleepForNanos", "newPromise", "completePromise", "awaitPromiseExit"
    , "__race", "__timeout" -- §18.1.6 race/timeout (compile to krt2_race/krt2_timeout nodes)
    , "withScope", "__interruptWait", "__interruptNoWait" -- §19.5/§18.1.4 scope + interruption nodes
    , "uninterruptible", "__mask", "poll" -- §18.1.12 masking: OP_UNINTERRUPTIBLE/OP_MASK/OP_POLL nodes
      -- §18.1.8 structured scopes/monitors: not all "suspend" (newScope/forkIn/
      -- monitor build a node; shutdownScope/awaitMonitor park) but all are
      -- CK-machine OP_* nodes, so a block using them must be CPS-lowered.
    , "newScope", "forkIn", "shutdownScope", "monitor", "awaitMonitor"
    , "atomically", "stmBind" -- §18.1.13 STM: atomically retry-parks; stmBind builds the STM tree
    ]

-- | Is g one of the suspending / CK-machine primitive ops, by module + name?
-- Only the prelude / __prim globals match — a user global named join/race never does.
isSuspendingPrim :: GName -> Bool
isSuspendingPrim (GName m nm) =
  (m == primModule || m == ModuleName ["std", "prelude"]) && nm `Set.member` suspendingNames

-- | Every global referenced anywhere in a term — the call-graph out-edges used by
-- the §3.3 transitive-suspender closure.
termGlobals :: Term -> Set GName
termGlobals = goT
  where
    goT t = case t of
      CVar {} -> Set.empty
      CGlob g -> Set.singleton g
      CLam _ _ _ b -> goT b
      CPi _ _ _ _ ty b -> goT ty <> goT b
      CApp _ a b -> goT a <> goT b
      CSort {} -> Set.empty
      CLit {} -> Set.empty
      CCtor g _ args -> Set.insert g (goAll args)
      CMatch s _ alts -> goT s <> mconcat [maybe Set.empty goT (caGuard a) <> goT (caBody a) | a <- alts]
      CRecordT fs -> goAll (map snd fs)
      CRecordV fs -> goAll (map snd fs)
      CProj e _ -> goT e
      CProjAt e _ _ -> goT e
      CVariantT ts -> goAll ts
      CInject _ e -> goT e
      CLet _ _ ty rhs body -> goT ty <> goT rhs <> goT body
      CLetRec _ _ ty rhs body -> goT ty <> goT rhs <> goT body
      CMeta {} -> Set.empty
      CDo _ items -> goItems items
      CSealE _ e -> goT e
      CSigT _ e -> goT e
      CThunkE e -> goT e
      CLazyE e -> goT e
      CForceE e -> goT e
      CIf c th el -> goT c <> goT th <> goT el
      CQuote _ ts -> goAll ts
    goAll = mconcat . map goT
    goItems = mconcat . map goItem
    goItem it = case it of
      KBind _ _ e -> goT e
      KLet _ _ e -> goT e
      KLetQ _ e me -> goT e <> maybe Set.empty (goT . snd) me
      KExpr e -> goT e
      KVarItem _ e -> goT e
      KAssign r _ v -> goT r <> goT v
      KReturn e -> goT e
      KBreak _ -> Set.empty
      KContinue _ -> Set.empty
      KWhile _ c b me -> goT c <> goItems b <> maybe Set.empty goItems me
      KFor _ _ s b me -> goT s <> goItems b <> maybe Set.empty goItems me
      KIf alts me -> mconcat [goT c <> goItems b | (c, b) <- alts] <> maybe Set.empty goItems me
      KDefer _ e -> goT e
      KUsing _ a r -> goT a <> goT r
      KSubDo _ items -> goItems items

-- | §3.3 suspendability analysis: the least set of globals that TRANSITIVELY
-- reach a suspending primitive — a global whose body references one directly, or
-- that calls another such global (closed under the call graph).  Computed once
-- over all recorded core bodies.  This is the SOUND replacement for the old
-- syntactic spine-head check: it catches a user helper that forks/awaits, not
-- just a literal @fork@/@await@.  (Higher-order suspension through a value-passed
-- action is not modelled — a known limitation; such a head is treated as
-- non-suspending, never miscompiled silently since it falls to the diagnostic.)
suspenderGlobals :: Map GName Term -> Set GName
suspenderGlobals bodies = fixpoint seed
  where
    refs = Map.map termGlobals bodies
    seed = Map.keysSet (Map.filter (any isSuspendingPrim) refs)
    fixpoint s =
      let s' = s <> Map.keysSet (Map.filter (any (`Set.member` s)) refs)
       in if s' == s then s else fixpoint s'

-- | Does this action (its spine head) reach a suspending op?  A suspending prim,
-- or a global in the §3.3 transitive-suspender set.
spineHeadSuspends :: Set GName -> Term -> Bool
spineHeadSuspends susp t = case fst (spineOf t) of
  CGlob g -> isSuspendingPrim g || g `Set.member` susp
  _ -> False

-- | §3.3 higher-order: is this action's spine head a local/parameter (a @CVar@)?
-- Then the action MAY suspend depending on the caller (e.g. @bracketM@'s @use r@,
-- where @use@ is an IO-action parameter).  A combinator over it is CPS-lowered
-- conservatively: the CK-machine drives a sequential local action just fine, and
-- only it can drive a suspending one — whereas the synchronous bridge cannot.
spineHeadIsLocal :: Term -> Bool
spineHeadIsLocal t = case fst (spineOf t) of
  CVar _ -> True
  _ -> False

-- | An action that an IO combinator (ioBind/catchIO/…) must drive through the
-- CK-machine: it either reaches a suspending op (§3.3) or is parameter-headed
-- (higher-order, may-suspend).
mayActSuspend :: Set GName -> Term -> Bool
mayActSuspend susp t = spineHeadSuspends susp t || spineHeadIsLocal t

-- | Does any action in the block (recursively, including loop/if bodies) reach a
-- suspending operation?  Gates CPS lowering and — when the block is NOT CPS-able
-- — DIAGNOSES it (a hard error, not a silent fall-through to the bridge).
blockSuspends :: Set GName -> [KItem] -> Bool
blockSuspends susp = any itemSuspends
  where
    s = spineHeadSuspends susp
    itemSuspends (KBind _ _ t) = s t
    itemSuspends (KExpr t) = s t
    itemSuspends (KAssign _ True t) = s t
    itemSuspends (KReturn t) = s t
    itemSuspends (KVarItem _ t) = s t
    itemSuspends (KWhile _ _ b me) = blockSuspends susp b || maybe False (blockSuspends susp) me
    itemSuspends (KFor _ _ _ b me) = blockSuspends susp b || maybe False (blockSuspends susp) me
    itemSuspends (KIf alts me) = any (blockSuspends susp . snd) alts || maybe False (blockSuspends susp) me
    itemSuspends (KUsing _ a _) = s a
    -- a transparent sub-do runs in THIS block's continuation chain, so a
    -- suspending op inside it makes this block suspend too (CPS LOOP FAMILY §4).
    itemSuspends (KSubDo _ b) = blockSuspends susp b
    itemSuspends _ = False

cpsEligible :: Set GName -> [KItem] -> Bool
cpsEligible susp items = blockSuspends susp items && all simpleLinear items
  where
    -- Stage 1: binds/lets/effects.  Stage 2: plus plain `defer` (lowered through
    -- the runtime's OP_DOSCOPE/OP_DEFER).  Stage 2.5 — the CPS LOOP FAMILY (§4):
    -- var / := / while / break / continue / return now lower through the
    -- CK-machine's OP_WHILE/KK_LOOP + OP_NEW_REF/OP_READ_REF/OP_WRITE_REF + the
    -- abrupt-control nodes, so a may-suspend block containing them is no longer
    -- fail-closed.  Scope discipline: the WELL-SCOPED CORE handles the unlabeled
    -- `while` (no else), `var`/`:=` (assign to a `var` cell), unlabeled
    -- `break`/`continue`, `return`, plain `defer`, statement-`if`, and a
    -- transparent unlabeled sub-do.  Labeled loops, `for`, loop `else`, `using`,
    -- and `let?` remain fail-closed (DIAGNOSED in 'compileDo', not mis-lowered).
    simpleLinear KBind {} = True
    simpleLinear KLet {} = True
    simpleLinear KExpr {} = True
    simpleLinear (KDefer Nothing _) = True
    simpleLinear KVarItem {} = True
    simpleLinear (KAssign (CVar _) _ _) = True
    simpleLinear KReturn {} = True
    simpleLinear (KBreak Nothing) = True
    simpleLinear (KContinue Nothing) = True
    simpleLinear (KWhile Nothing _ body Nothing) = all simpleLinear body
    simpleLinear (KIf alts mels) =
      all (all simpleLinear . snd) alts && maybe True (all simpleLinear) mels
    simpleLinear (KSubDo Nothing body) = all simpleLinear body
    simpleLinear _ = False

-- | Lower a CPS-eligible do-block: build its @krt2_*@ action tree, wrapping it
-- in a @krt2_doscope@ when the block carries §18.7 defers (so they run LIFO and
-- masked on every exit, via OP_DOSCOPE/KK_DOSCOPE).  With no defers there is no
-- scope frame — just the bind tree.
compileDoCps :: [KItem] -> Gen Text
compileDoCps items = do
  -- §4 R7: once any `var` cell exists in the block, EVERY read of it must be a
  -- RUN-TIME OP_READ_REF, not a build-time kref_get — not only inside the loop
  -- but for the rest of the block, since a loop body mutates the cell and a
  -- later read (e.g. `printlnString (showInt total)` after the loop) would
  -- otherwise capture the cell's value at build time (before the loop ran).  So
  -- the ref region spans the whole block whenever it declares a `var`.  A block
  -- with no `var` keeps the build-time read fast path.
  tree <- (if any hasVar items then withCpsRefRegion else id) (cpsItems items)
  -- §18.8: a `return` exits THIS do-block (yielding its value), not the fiber.
  -- When CPS-lowered the block is inlined into a larger continuation chain, so a
  -- bare OP_RETURN would unwind past the block to the fiber's KK_DONE.  Wrap the
  -- block in krt2_retscope (KK_RETSCOPE), which catches the RK_RETURN and
  -- delivers the value as the block's result — restoring do-block-scoped return.
  let scoped = if any itemReturns items then "krt2_retscope(" <> tree <> ")" else tree
  pure $ if any hasScope items then "krt2_doscope(" <> scoped <> ")" else scoped
  where
    hasScope (KDefer _ _) = True
    hasScope _ = False
    -- a `var` declared anywhere in THIS block (recursing into its own loop/if/
    -- subdo bodies, but NOT into a nested do VALUE).
    hasVar (KVarItem _ _) = True
    hasVar (KWhile _ _ b mels) = any hasVar b || maybe False (any hasVar) mels
    hasVar (KIf alts mels) = any (any hasVar . snd) alts || maybe False (any hasVar) mels
    hasVar (KSubDo _ b) = any hasVar b
    hasVar _ = False
    -- a `return` anywhere in THIS block (recursing into its own loop/if/subdo
    -- bodies, which return from this block, but NOT into a nested do VALUE).
    itemReturns (KReturn _) = True
    itemReturns (KWhile _ _ b mels) = any itemReturns b || maybe False (any itemReturns) mels
    itemReturns (KIf alts mels) = any (any itemReturns . snd) alts || maybe False (any itemReturns) mels
    itemReturns (KSubDo _ b) = any itemReturns b
    itemReturns _ = False

-- | Lower a CPS-eligible do-block to its @krt2_bind@/@krt2_then@ action tree.
-- Each non-tail bind becomes @krt2_bind(action, kclo(kdok_N, env))@ with the
-- continuation emitted as a sibling function; a discarded effect becomes
-- @krt2_then@; the tail action is returned directly (tail position — the
-- CK-machine, not a nested bind, so the spine stays bounded).
cpsItems :: [KItem] -> Gen Text
cpsItems items = case items of
  [] -> pure "krt2_pure(kunit())"
  [KExpr t] -> cpsActionTerm t
  [KBind _ _ t] -> cpsActionTerm t
  (KExpr t : rest) -> seqThen t rest
  (KBind _ CPWild t : rest) -> seqThen t rest
  (KBind _ pat t : rest) -> do
    m <- cpsActionTerm t
    contFn <- emitCpsCont pat rest
    env <- gets gsEnv
    pure ("krt2_bind(" <> m <> ", kclo(" <> contFn <> ", " <> env <> "))")
  (KLet _ CPWild t : rest) -> compile t >> cpsItems rest
  (KLet _ pat t : rest) -> do
    -- a `let` binds a PURE value; its reads (if any, inside a ref region)
    -- normalize to run-time OP_READ_REF so a re-run body re-reads the live cell,
    -- exactly as a monadic bind does.  Outside the region this is plain krt2_pure.
    bindA <- cpsActionOfPure t
    contFn <- emitCpsCont pat rest
    env <- gets gsEnv
    pure ("krt2_bind(" <> bindA <> ", kclo(" <> contFn <> ", " <> env <> "))")
  -- ── CPS LOOP FAMILY (CPS-DESIGN §4) ──────────────────────────────────
  -- @var x = init@: allocate a cell via OP_NEW_REF and push it onto the captured
  -- env (de Bruijn 0) for the continuation.  The cell lives in the KEnv, so it
  -- survives a park (the "free liveness via KEnv" of §4) and every later read/
  -- write addresses the SAME cell across iterations and across suspension.
  (KVarItem _ t : rest) -> do
    -- the initializer is normalized through the ref region too: a `var y = …`
    -- whose initializer reads an enclosing var must read it at run time.  Bind
    -- the (action) value, then OP_NEW_REF it and push the cell as de Bruijn 0.
    initA <- withCpsRefRegion (cpsActionOfPure t)
    contFn <- emitCpsNewRefCont rest
    env <- gets gsEnv
    pure ("krt2_bind(" <> initA <> ", kclo(" <> contFn <> ", " <> env <> "))")
  -- @x := rhs@ / @x <- rhs@ (a var assignment): write the cell at RUN TIME via
  -- OP_WRITE_REF so a re-run loop body re-writes the live cell, then continue.
  -- The rhs value is normalized to run-time reads (§4 R7), bound, then written.
  -- A monadic rhs additionally runs the rhs ACTION before the write.
  (KAssign (CVar idx) monadic rhsT : rest) -> do
    env <- gets gsEnv
    rhsA <-
      if monadic
        -- a monadic rhs (`x <- m`) is an IO ACTION; its var reads must still be
        -- hoisted to run-time OP_READ_REF (§4 R7) when in a ref region, exactly
        -- as a discarded effect or bind is — `cpsActionTerm` normalizes iff the
        -- ref region is on and the term reads a var, else plain compile.
        then cpsActionTerm rhsT
        else withCpsRefRegion (cpsActionOfPure rhsT)
    contFn <- emitCpsAssignCont idx rest
    pure ("krt2_bind(" <> rhsA <> ", kclo(" <> contFn <> ", " <> env <> "))")
  -- @return v@: exit THIS do-block (OP_RETURN -> RK_RETURN, caught by the
  -- enclosing KK_RETSCOPE — compileDoCps), running every crossed do-scope's
  -- defers en route.  The value is normalized to run-time reads, bound, then
  -- returned.  Tail (anything following `return` is dead, never reached).
  (KReturn t : _) -> do
    rv <- withCpsRefRegion (cpsActionOfPure t)
    contFn <- emitCpsReturnCont
    env <- gets gsEnv
    pure ("krt2_bind(" <> rv <> ", kclo(" <> contFn <> ", " <> env <> "))")
  -- @break@ / @continue@ (unlabeled): target the innermost OP_WHILE's KK_LOOP.
  (KBreak Nothing : _) -> pure "krt2_break()"
  (KContinue Nothing : _) -> pure "krt2_continue()"
  -- @while c { body }@ (unlabeled, no else): OP_WHILE[condIO, bodyIO] -> KK_LOOP.
  -- @cond@ is built as an ACTION that reads the loop vars at step time (so each
  -- iteration re-tests the live cells — §4 R7), and @body@ is a CPS action tree
  -- the runtime re-runs as a fresh per-iteration do-scope.
  (KWhile Nothing cond body Nothing : rest) -> do
    condA <- cpsCondAction cond
    bodyA <- withCpsRefRegion (cpsItems body)
    r <- cpsItems rest
    pure ("krt2_then(krt2_while(" <> condA <> ", " <> bodyA <> "), " <> r <> ")")
  -- a statement-`if` in a CPS block: each branch is a CPS action tree; the if's
  -- normal completion is Unit (matching the interpreter's KIf), so a non-tail if
  -- sequences its (Unit) result before the rest via krt2_then.
  (KIf alts mels : rest) -> do
    br <- cpsIf alts mels
    if null rest
      then pure br
      else do
        r <- cpsItems rest
        pure ("krt2_then(" <> br <> ", " <> r <> ")")
  -- a transparent nested do-statement (§18.8.3.1): its own bindings are SCOPED
  -- to the sub-block (they do not leak into @rest@, matching the legacy Nested
  -- handling), but abrupt control (break/continue/return) propagates outward —
  -- automatically, since those lower to unwind NODES the CK-machine routes
  -- through any scope nesting.  Build the sub-block as its own tree; if it
  -- registers its own §18.7 defers, wrap it in krt2_doscope so those finalizers
  -- run when the SUB-block exits (before @rest@), not the outer block's exit.
  (KSubDo Nothing body : rest) -> do
    sub0 <- cpsItems body
    let sub = if any subDefers body then "krt2_doscope(" <> sub0 <> ")" else sub0
    if null rest
      then pure sub
      else do
        r <- cpsItems rest
        pure ("krt2_then(" <> sub <> ", " <> r <> ")")
  -- §18.7 plain defer: register the action on the enclosing do-scope's ExitStack
  -- (OP_DEFER), then continue.  The whole block is wrapped in krt2_doscope
  -- (compileDoCps), so cur_exits is this scope's stack — even in a continuation
  -- that runs after a park, since OP_DOSCOPE set cur_exits and no suspending op
  -- changes it.  Finalizers run LIFO, masked, on every exit (R1).
  (KDefer Nothing t : rest) -> do
    de <- compileDeferAction t
    r <- cpsItems rest
    pure ("krt2_then(krt2_defer(" <> de <> "), " <> r <> ")")
  (item : _) ->
    unsupported "do-kernel (CPS)" ("unexpected item in a CPS do-block: " <> T.pack (show item))
  where
    seqThen t rest = do
      m <- cpsActionTerm t
      r <- cpsItems rest
      pure ("krt2_then(" <> m <> ", " <> r <> ")")
    -- a §18.7 defer registered DIRECTLY in a sub-block (not in its own nested
    -- loop/if/subdo, which carry their own per-iteration scope): such a defer
    -- needs the sub-block wrapped in krt2_doscope so it runs at the sub-block's
    -- exit, LIFO and masked (R1), rather than the enclosing block's.
    subDefers (KDefer _ _) = True
    subDefers _ = False

-- | Emit a CPS continuation function @kdok_N(KEnv *cenv, KValue *karg)@: bind
-- the delivered value @karg@ to @pat@ (extending the captured @cenv@), then
-- build the rest of the block as a tree.
emitCpsCont :: CorePat -> [KItem] -> Gen Text
emitCpsCont pat rest = do
  fnName <- freshFn "kdok_"
  (stmts, tree) <- captured "cenv" $ do
    e2 <- bindPatScrut "karg" "cenv" pat
    withEnv e2 (cpsItems rest)
  let fn =
        T.unlines $
          ["static KValue *" <> fnName <> "(KEnv *cenv, KValue *karg) {", "  (void)cenv; (void)karg;"]
            ++ map ("  " <>) stmts
            ++ ["  return " <> tree <> ";", "}"]
  modify' $ \st ->
    st
      { gsTop = fn : gsTop st
      , gsProtos = ("static KValue *" <> fnName <> "(KEnv *, KValue *);") : gsProtos st
      }
  pure fnName

-- ── CPS LOOP FAMILY helpers (CPS-DESIGN §4) ──────────────────────────────

-- | Run a build action with the §4 R7 ref-region flag set: while it is on, a
-- var read inside a value/action is normalized to a RUN-TIME OP_READ_REF
-- ('cpsNormalizeReads'), so a re-run loop body re-reads the live cell.
withCpsRefRegion :: Gen a -> Gen a
withCpsRefRegion act = do
  saved <- gets gsCpsRefRegion
  modify' $ \g -> g {gsCpsRefRegion = True}
  r <- act
  modify' $ \g -> g {gsCpsRefRegion = saved}
  pure r

-- | Compile an IO ACTION term in a CPS block.  In a §4 R7 ref region (a
-- suspending loop body) its var reads are hoisted to run-time OP_READ_REF so a
-- re-run observes the live cell; outside the region this is plain 'compile'.
cpsActionTerm :: Term -> Gen Text
cpsActionTerm = cpsNormalizeReads False

-- | §4 R7 var-read normalization (PURE result).  Build an ACTION node whose
-- stepped result is the VALUE of @term@, hoisting every var read to a RUN-TIME
-- OP_READ_REF bind so a re-run loop body re-reads the live cell.  Outside the
-- ref region (or for a read-free term) this is just @krt2_pure(<value>)@.
cpsActionOfPure :: Term -> Gen Text
cpsActionOfPure = cpsNormalizeReads True

-- | A var read @__runIO (readRef (CVar i))@ (the elaborator's auto-deref of a
-- surface @var@ read), if @term@ is exactly that shape; the de Bruijn index of
-- the cell otherwise 'Nothing'.
varReadIdx :: Term -> Gen (Maybe Int)
varReadIdx term = case runIOSplice term of
  Just action -> case spineOf action of
    (CGlob h, sargs) -> do
      mp <- globPrimName h
      pure $ case (mp, [a | (Expl, a) <- sargs]) of
        (Just "readRef", [CVar i]) -> Just i
        _ -> Nothing
    _ -> pure Nothing
  Nothing -> pure Nothing

-- | Does @term@ contain a var read (@__runIO (readRef …)@) anywhere?  Used to
-- decide whether a value must be hoisted into OP_READ_REF binds (§4 R7) — a
-- read-free value is built once and is safe to re-run as a @krt2_pure@ leaf.
termHasVarRead :: Term -> Gen Bool
termHasVarRead term = do
  mi <- varReadIdx term
  case mi of
    Just _ -> pure True
    Nothing -> case term of
      CApp _ f a -> (||) <$> termHasVarRead f <*> termHasVarRead a
      CCtor _ _ args -> orM (map termHasVarRead args)
      CProj e _ -> termHasVarRead e
      CProjAt e _ _ -> termHasVarRead e
      CRecordV fs -> orM (map (termHasVarRead . snd) fs)
      _ -> pure False
  where
    orM = foldr (\m acc -> do b <- m; if b then pure True else acc) (pure False)

-- | The shared §4 R7 normalizer.  Collect every var read in @term@ (left to
-- right), bind each via a RUN-TIME @krt2_read_ref(cell)@ onto a fresh KEnv slot,
-- then build the residual — @term@ with each read replaced by its bound slot and
-- all other free vars shifted past the pushes — wrapping it in @krt2_pure@ iff
-- @pureResult@.  A read-free term (or outside the ref region) short-circuits to
-- a plain @compile@ — no binds, preserving the build-time fast path.
cpsNormalizeReads :: Bool -> Term -> Gen Text
cpsNormalizeReads pureResult term = do
  region <- gets gsCpsRefRegion
  has <- if region then termHasVarRead term else pure False
  if not has
    then do
      v <- compile term
      pure (if pureResult then "krt2_pure(" <> v <> ")" else v)
    else do
      reads' <- collectReads term -- the original cell indices, in occurrence order
      let n = length reads'
      bindChain n reads' 0
  where
    -- bindChain n remaining done: bind each remaining read (its cell shifted past
    -- the @done@ prior pushes), pushing the value as the next KEnv slot; once all
    -- @n@ are bound, compile the rewritten residual under the extended env.
    bindChain n [] _ = do
      residual <- rewriteReads n term
      v <- compile residual
      pure (if pureResult then "krt2_pure(" <> v <> ")" else v)
    bindChain n (cellIdx : more) done = do
      -- the cell lives at original index @cellIdx@; @done@ pushes happened since,
      -- so it is now at @cellIdx + done@.
      cell <- compile (CVar (cellIdx + done))
      contFn <- emitReadHoistCont $ bindChain n more (done + 1)
      env <- gets gsEnv
      pure ("krt2_bind(krt2_read_ref(" <> cell <> "), kclo(" <> contFn <> ", " <> env <> "))")

-- | Emit a read-hoist continuation @kdok_N(KEnv*, KValue *karg)@ that pushes the
-- delivered read value as de Bruijn 0, then runs @build@ under the extended env.
emitReadHoistCont :: Gen Text -> Gen Text
emitReadHoistCont build = do
  fnName <- freshFn "kdok_"
  (stmts, tree) <- captured "cenv" $ do
    e2 <- pushEnv "karg" "cenv"
    withEnv e2 build
  let fn =
        T.unlines $
          ["static KValue *" <> fnName <> "(KEnv *cenv, KValue *karg) {", "  (void)cenv; (void)karg;"]
            ++ map ("  " <>) stmts
            ++ ["  return " <> tree <> ";", "}"]
  modify' $ \st ->
    st
      { gsTop = fn : gsTop st
      , gsProtos = ("static KValue *" <> fnName <> "(KEnv *, KValue *);") : gsProtos st
      }
  pure fnName

-- | Collect the cell de Bruijn indices of every var read in @term@, in
-- left-to-right occurrence order (with duplicates — each read site is bound
-- independently; a common-subexpression eliminator is a later refinement).
collectReads :: Term -> Gen [Int]
collectReads term = do
  mi <- varReadIdx term
  case mi of
    Just i -> pure [i]
    Nothing -> case term of
      CApp _ f a -> (++) <$> collectReads f <*> collectReads a
      CCtor _ _ args -> concat <$> mapM collectReads args
      CProj e _ -> collectReads e
      CProjAt e _ _ -> collectReads e
      CRecordV fs -> concat <$> mapM (collectReads . snd) fs
      _ -> pure []

-- | Rewrite @term@ for the residual of a read hoist: each var read at occurrence
-- @j@ (0-based, left to right, @n@ total) becomes @CVar (n-1-j)@ (its bound
-- slot), and every OTHER free var is shifted up by @n@ (past the @n@ pushes).
-- Stateful over the running occurrence counter so duplicate reads map to their
-- own slots in order.  Mirrors 'collectReads' exactly so slots line up.
rewriteReads :: Int -> Term -> Gen Term
rewriteReads n t0 = fst <$> runRW 0 t0
  where
    -- runRW j t = (rewritten t, next occurrence index after t's reads)
    runRW :: Int -> Term -> Gen (Term, Int)
    runRW j t = do
      mi <- varReadIdx t
      case mi of
        Just _ -> pure (CVar (n - 1 - j), j + 1)
        Nothing -> case t of
          CVar i -> pure (CVar (i + n), j) -- a non-read free var shifts past the pushes
          CApp ic f a -> do
            (f', j') <- runRW j f
            (a', j'') <- runRW j' a
            pure (CApp ic f' a', j'')
          CCtor g ann args -> do
            (args', j') <- runList j args
            pure (CCtor g ann args', j')
          CProj e f -> do (e', j') <- runRW j e; pure (CProj e' f, j')
          CProjAt e f i -> do (e', j') <- runRW j e; pure (CProjAt e' f i, j')
          CRecordV fs -> do
            (vs', j') <- runList j (map snd fs)
            pure (CRecordV (zip (map fst fs) vs'), j')
          _ -> pure (t, j) -- literals, globals, etc.: no reads, no free vars to shift
    runList j [] = pure ([], j)
    runList j (x : xs) = do
      (x', j') <- runRW j x
      (xs', j'') <- runList j' xs
      pure (x' : xs', j'')

-- | Push a single value onto the current KEnv expression, returning the new env
-- C-name (a @kpush(val, env)@ local).
pushEnv :: Text -> Text -> Gen Text
pushEnv val env = do
  n <- freshN "env_"
  emit ("KEnv *" <> n <> " = kpush(" <> val <> ", " <> env <> ");")
  pure n

-- | Build the @cond@ action of a CPS @while@: an action whose stepped result is
-- the loop's Bool condition, with var reads normalized to run-time OP_READ_REF
-- (§4 R7) so each iteration re-tests the LIVE cells.
cpsCondAction :: Term -> Gen Text
cpsCondAction = withCpsRefRegion . cpsActionOfPure

-- | The @var x = init@ continuation: the delivered initializer value @karg@ is
-- placed into a fresh cell via run-time OP_NEW_REF, and the cell is pushed as de
-- Bruijn 0 for the rest of the block (so it lives in the KEnv — captured across
-- a park, §4 — and every read/write addresses the same cell).
emitCpsNewRefCont :: [KItem] -> Gen Text
emitCpsNewRefCont rest = do
  fnName <- freshFn "kdok_"
  (stmts, tree) <- captured "cenv" $ do
    ref <- freshN "var_"
    emit ("KValue *" <> ref <> " = kref_new(karg);")
    e2 <- pushEnv ref "cenv"
    withEnv e2 (cpsItems rest)
  let fn =
        T.unlines $
          ["static KValue *" <> fnName <> "(KEnv *cenv, KValue *karg) {", "  (void)cenv; (void)karg;"]
            ++ map ("  " <>) stmts
            ++ ["  return " <> tree <> ";", "}"]
  modify' $ \st ->
    st
      { gsTop = fn : gsTop st
      , gsProtos = ("static KValue *" <> fnName <> "(KEnv *, KValue *);") : gsProtos st
      }
  pure fnName

-- | The @return v@ continuation: the delivered value @karg@ exits the do-block
-- via OP_RETURN (the abrupt-control node unwinds crossed do-scopes, running
-- their defers, then is caught by the block's KK_RETSCOPE — §18.8).
emitCpsReturnCont :: Gen Text
emitCpsReturnCont = do
  fnName <- freshFn "kdok_"
  let body =
        [ "static KValue *" <> fnName <> "(KEnv *cenv, KValue *karg) {"
        , "  (void)cenv;"
        , "  return krt2_return(karg);"
        , "}"
        ]
  modify' $ \st ->
    st
      { gsTop = T.unlines body : gsTop st
      , gsProtos = ("static KValue *" <> fnName <> "(KEnv *, KValue *);") : gsProtos st
      }
  pure fnName

-- | A continuation for a MONADIC var assignment @x <- rhs@ (or pure @x := rhs@):
-- the delivered rhs result @karg@ is written to the cell at de Bruijn @idx@ via
-- run-time OP_WRITE_REF, then the rest of the block runs.  @karg@ is NOT pushed
-- (the assignment introduces no binder), so indices in @rest@ are unchanged.
emitCpsAssignCont :: Int -> [KItem] -> Gen Text
emitCpsAssignCont idx rest = do
  fnName <- freshFn "kdok_"
  (stmts, tree) <- captured "cenv" $ do
    cell <- compile (CVar idx)
    r <- cpsItems rest
    pure ("krt2_then(krt2_write_ref(" <> cell <> ", karg), " <> r <> ")")
  let fn =
        T.unlines $
          ["static KValue *" <> fnName <> "(KEnv *cenv, KValue *karg) {", "  (void)cenv; (void)karg;"]
            ++ map ("  " <>) stmts
            ++ ["  return " <> tree <> ";", "}"]
  modify' $ \st ->
    st
      { gsTop = fn : gsTop st
      , gsProtos = ("static KValue *" <> fnName <> "(KEnv *, KValue *);") : gsProtos st
      }
  pure fnName

-- | A statement-@if@ in a CPS block: each branch is a CPS action tree.  The
-- condition is a pure Bool (R7-normalized if it reads a var); the runtime picks
-- the branch.  Built as @krt2_bind(<condAction>, kclo(select))@ where @select@
-- dispatches in C on the delivered Bool to the chosen branch's tree.
cpsIf :: [(Term, [KItem])] -> Maybe [KItem] -> Gen Text
cpsIf alts mels = goAlts alts
  where
    goAlts [] = case mels of
      Just els -> cpsItems els
      Nothing -> pure "krt2_pure(kunit())" -- no/exhausted else: Unit (§18.8)
    goAlts ((c, body) : more) = do
      condA <- cpsActionOfPure c
      thenFn <- emitCpsBranchCont (cpsItems body)
      elseFn <- emitCpsBranchCont (goAlts more)
      env <- gets gsEnv
      sel <- emitCpsIfSelect thenFn elseFn
      pure ("krt2_bind(" <> condA <> ", kclo(" <> sel <> ", " <> env <> "))")

-- | Emit a branch builder @kdok_N(KEnv *cenv, KValue *karg)@ ignoring @karg@,
-- returning the branch's CPS tree (built under the captured env, unextended).
emitCpsBranchCont :: Gen Text -> Gen Text
emitCpsBranchCont build = do
  fnName <- freshFn "kdok_"
  (stmts, tree) <- captured "cenv" build
  let fn =
        T.unlines $
          ["static KValue *" <> fnName <> "(KEnv *cenv, KValue *karg) {", "  (void)cenv; (void)karg;"]
            ++ map ("  " <>) stmts
            ++ ["  return " <> tree <> ";", "}"]
  modify' $ \st ->
    st
      { gsTop = fn : gsTop st
      , gsProtos = ("static KValue *" <> fnName <> "(KEnv *, KValue *);") : gsProtos st
      }
  pure fnName

-- | Emit the if-selector @kdok_N(KEnv *cenv, KValue *karg)@: on the delivered
-- Bool @karg@, return the then-branch tree or the else-branch tree (each built
-- by applying its closure to the captured env + Unit).
emitCpsIfSelect :: Text -> Text -> Gen Text
emitCpsIfSelect thenFn elseFn = do
  fnName <- freshFn "kdok_"
  let body =
        [ "static KValue *" <> fnName <> "(KEnv *cenv, KValue *karg) {"
        , "  return kas_bool(karg)"
        , "    ? " <> thenFn <> "(cenv, kunit())"
        , "    : " <> elseFn <> "(cenv, kunit());"
        , "}"
        ]
  modify' $ \st ->
    st
      { gsTop = T.unlines body : gsTop st
      , gsProtos = ("static KValue *" <> fnName <> "(KEnv *, KValue *);") : gsProtos st
      }
  pure fnName

-- | Compile a do-block to a suspended IO action (@kio@) whose body runs
-- the scope.  The captured environment is the current one.  A block reaching a
-- suspending operation is CPS-lowered instead (see 'cpsEligible').
compileDo :: Maybe Text -> [KItem] -> Gen Text
compileDo lbl items = do
  susp <- gets gsSuspenders
  if cpsEligible susp items
    then compileDoCps items
    -- A block that reaches a suspending op but is not a CPS-able shape would be
    -- mis-run on the synchronous bridge (fork/await never park) — fail closed
    -- with a clear diagnostic instead, until the relevant CPS stage lands.
    else
      if blockSuspends susp items
        then
          unsupported
            "do-kernel"
            ( "a suspending operation (fork/await/sleepFor/…) appears in a do-block shape the "
                <> "native backend does not yet CPS-lower (a loop, if, using, labeled defer, "
                <> "monadic assignment, or return); see runtime/docs/CPS-DESIGN.md (Stage 2+)"
            )
        else compileDoLegacy lbl items

compileDoLegacy :: Maybe Text -> [KItem] -> Gen Text
compileDoLegacy lbl items = do
  fnName <- freshFn "kdo_"
  env <- gets gsEnv
  -- A do-block is a fresh scope in its own C function: its defer frames,
  -- labeled-scope map and enclosing loops do not extend into it (control
  -- cannot break out of, nor defer@L into, a do-block VALUE's outer scope),
  -- so reset those for the do-fn body. compileItems sets up this scope's
  -- §18.7 defer frame (tagged with `lbl` for defer@label routing).
  saved <- gets $ \g -> (gsDefer g, gsScopeDefers g, gsLoops g, gsDeferLabels g)
  modify' $ \g -> g {gsDefer = [], gsScopeDefers = [], gsLoops = [], gsDeferLabels = []}
  (stmts, ()) <- captured "cenv" (compileItems lbl Tail items)
  modify' $ \g -> let (d, s, l, dl) = saved in g {gsDefer = d, gsScopeDefers = s, gsLoops = l, gsDeferLabels = dl}
  let fn =
        T.unlines $
          [ "static KValue *" <> fnName <> "(KEnv *cenv) {"
          , "  (void)cenv;"
          ]
            ++ map ("  " <>) stmts
            ++ ["}"]
  modify' $ \st ->
    st
      { gsTop = fn : gsTop st
      , gsProtos = ("static KValue *" <> fnName <> "(KEnv *);") : gsProtos st
      }
  pure ("kio(" <> fnName <> ", " <> env <> ")")

-- | §18.7 @defer t@: lift the deferred IO action into a suspended @kio@
-- thunk that is /evaluated and run lazily at scope exit/, not eagerly at the
-- registration site.  The interpreter registers @evalK env t@ as an exit
-- thunk and runs it from the LIFO exit list, so @t@'s sub-expressions observe
-- any state mutated between here and the flush.  The thunk captures the
-- current environment (the @var@ cells, not their snapshots), so the body's
-- @kref_get@ reads — and any faulting sub-expression — happen at flush time,
-- matching the interpreter exactly.  @krun_finish@/@flushFramesInline@ pop the
-- registered @kio@ and @krun_io@ it; the thunk body itself drives @krun_io@ on
-- the freshly-evaluated action so the action actually executes (a returned
-- action value would otherwise not be run).
compileDeferAction :: Term -> Gen Text
compileDeferAction t = do
  fnName <- freshFn "kdefer_"
  env <- gets gsEnv
  (stmts, e) <- captured "cenv" (compile t)
  let fn =
        T.unlines $
          [ "static KValue *" <> fnName <> "(KEnv *cenv) {"
          , "  (void)cenv;"
          ]
            ++ map ("  " <>) stmts
            ++ [ "  return krun_io(" <> e <> ");"
               , "}"
               ]
  emitTop ("static KValue *" <> fnName <> "(KEnv *);") fn
  pure ("kio(" <> fnName <> ", " <> env <> ")")

-- | A §19 suspension: lift the delayed expression into a fresh thunk
-- function capturing the current environment; @memo@ is 1 for Memo (cache
-- on first force) and 0 for Delay (re-evaluate each force).
compileSuspension :: Int -> Term -> Gen Text
compileSuspension memo e = do
  fnName <- freshFn "kth_"
  env <- gets gsEnv
  (stmts, ve) <- captured "cenv" (compile e)
  let fn =
        T.unlines $
          [ "static KValue *" <> fnName <> "(KEnv *cenv) {"
          , "  (void)cenv;"
          ]
            ++ map ("  " <>) stmts
            ++ [ "  return " <> ve <> ";"
               , "}"
               ]
  emitTop ("static KValue *" <> fnName <> "(KEnv *);") fn
  pure ("kthunk(" <> fnName <> ", " <> env <> ", " <> T.pack (show memo) <> ")")

-- | Whether a scope is in tail position (the do-block body, whose final
-- value is the block's result) or nested (a loop\/if body, run for effect
-- with control flow propagating via C statements).  Both share the same
-- item handling and environment threading — the only differences are the
-- result of a trailing 'KExpr' and the empty-scope fall-through.
-- | 'Tail': the do-block result is this scope's last value (a trailing
-- 'KExpr' propagates its IO action's result).  'Nested': run for effect,
-- control flow via C statements (a loop / non-tail @if@ body).
-- 'TailEffect': a tail statement-@if@ branch (§18.8) — still tail position
-- for stack-safety (the trailing IO action defers via @kio_effect@), but
-- its normal completion is discarded so the do-block yields Unit (matching
-- the interpreter's @KIf@ completion); a @return@ still propagates its
-- value as a non-local early return.
data ScopeMode = Tail | Nested | TailEffect
  deriving stock (Eq)

-- | Compile a sequence of do-kernel items, threading the environment
-- through bindings.  Mirrors 'Kappa.Interp.runScope' completion: in 'Tail'
-- position the scope @return@s the last 'KExpr' value (or Unit); in
-- 'Nested' position items run for effect and break\/continue\/return
-- propagate via C statements.  A single traversal serves both modes so the
-- two can never drift (the previous split caused real divergences).
-- | §18.7: count the @defer@L@ actions in a kernel subtree that target the
-- scope labeled @L@. Recurses into nested loop/if bodies (which route their
-- @defer@L@ to this scope) but never into a 'KDefer' action term (a nested
-- @do@ VALUE there is a fresh scope with its own label map).
countLabeledDefers :: Text -> [KItem] -> Int
countLabeledDefers s = sum . map go
  where
    go (KDefer (Just l) _) | l == s = 1
    go (KWhile _ _ body mels) = countLabeledDefers s body + maybe 0 (countLabeledDefers s) mels
    go (KFor _ _ _ body mels) = countLabeledDefers s body + maybe 0 (countLabeledDefers s) mels
    go (KIf alts mels) = sum [countLabeledDefers s b | (_, b) <- alts] + maybe 0 (countLabeledDefers s) mels
    -- a transparent nested do-statement routes its @defer@s@ to this scope,
    -- unless it is itself labeled @s@ (then it owns those defers)
    go (KSubDo subL body) | subL == Just s = 0
                          | otherwise = countLabeledDefers s body
    go _ = 0

compileItems :: Maybe Text -> ScopeMode -> [KItem] -> Gen ()
compileItems selfLabel mode items0 = do
  -- A scope that registers §18.7 defers gets a frame (a GC-heap array +
  -- count, declared at scope entry — for a loop body that means a fresh
  -- frame per iteration).  A Tail/TailEffect scope's frame is pushed on
  -- gsDefer and flushed after the tail IO action (kio_finally, via
  -- emitTailIO/emitTailReturn); a Nested scope's frame is pushed on
  -- gsScopeDefers and flushed INLINE at normal completion here (and at any
  -- break/continue/return that unwinds it — see gotoLoop / KReturn).
  --
  -- The frame must be sized for every action that lands on it: the
  -- unlabeled `defer`s written DIRECTLY in this scope, plus any
  -- `defer@selfLabel` written anywhere in this scope's kernel subtree
  -- (nested loop/if bodies route to it). A `defer@other` written here
  -- routes to an enclosing frame, so it is NOT counted at this scope.
  -- §19.5 `using` also attaches a release to this scope's exit frame.
  let ndirect = length [() | KDefer Nothing _ <- items0] + length [() | KUsing {} <- items0]
      nlabeled = case selfLabel of
        Just s -> countLabeledDefers s items0
        Nothing -> 0
      ndefer = ndirect + nlabeled
  if ndefer == 0
    then go items0
    else do
      arr <- freshN "kdef_"
      cnt <- freshN "kdc_"
      emit ("KValue **" <> arr <> " = (KValue **)kgc_alloc(sizeof(KValue *) * " <> T.pack (show ndefer) <> "); (void)" <> arr <> ";")
      emit ("int " <> cnt <> " = 0; (void)" <> cnt <> ";")
      let frame = (arr, cnt)
      case mode of
        Nested -> modify' $ \g -> g {gsScopeDefers = frame : gsScopeDefers g}
        _ -> modify' $ \g -> g {gsDefer = frame : gsDefer g}
      forM_ selfLabel $ \l -> modify' $ \g -> g {gsDeferLabels = (l, frame) : gsDeferLabels g}
      go items0
      forM_ selfLabel $ \_ -> modify' $ \g -> g {gsDeferLabels = drop 1 (gsDeferLabels g)}
      case mode of
        Nested -> do flushFramesInline [frame]; modify' $ \g -> g {gsScopeDefers = drop 1 (gsScopeDefers g)}
        _ -> modify' $ \g -> g {gsDefer = drop 1 (gsDefer g)}
  where
    go [] = case mode of
      -- both Tail and a discarded tail if-branch yield Unit here; route
      -- through emitTailReturn so any §18.7 defers are still flushed.
      Tail -> emitTailReturn "kunit()"
      TailEffect -> emitTailReturn "kunit()"
      Nested -> pure ()
    go (item : rest) = case item of
      KExpr t
        | null rest -> do
            te <- compile t
            case mode of
              -- The do-block's tail IO action is its result: defer it to the
              -- driving krun_io (constant C stack, §27.5A.3), carrying any
              -- §18.7 finalizers along (emitTailIO).
              Tail -> emitTailIO False te
              -- A tail statement-if branch: same, but the result is
              -- discarded (the do-block yields Unit).
              TailEffect -> emitTailIO True te
              Nested -> emitRunIODiscard te
      KExpr t -> do
        te <- compile t
        emitRunIODiscard te >> go rest
      -- A wildcard binding introduces no name: emit the right-hand side
      -- for its effect (a bind runs the IO action; a let just evaluates)
      -- without an unused C variable (keeps the generated C -Wall clean).
      KLet _ CPWild t -> do
        te <- compile t
        emit ("(void)(" <> te <> ");")
        go rest
      KLet _ pat t -> do
        te <- compile t
        sv <- freshN "let_"
        emit ("KValue *" <> sv <> " = " <> te <> ";")
        bindAndContinue sv pat
      KBind _ CPWild t -> do
        te <- compile t
        emitRunIODiscard te
        go rest
      KBind _ pat t -> do
        te <- compile t
        sv <- emitRunIOValue "bind_" te
        bindAndContinue sv pat
      -- §18 early non-local return: unwind every enclosing Nested scope
      -- (loop/if bodies) running their defers first, then return the value
      -- through emitTailReturn (which flushes the Tail-scope defer frames).
      KReturn t -> do
        te <- compile t
        scopeFrames <- gets gsScopeDefers
        flushFramesInline scopeFrames
        emitTailReturn te
      KVarItem _ t -> do
        -- P0.2: if this var begins an eligible scalarizable var+while pattern,
        -- lower the whole group to int64 C locals; else the boxed `var` cell.
        mplan <- scalarLoopPlan (item : rest)
        case mplan of
          Just plan -> emitScalarLoop plan
          Nothing -> do
            te <- compile t
            ref <- freshN "var_"
            emit ("KValue *" <> ref <> " = kref_new(" <> te <> ");")
            env <- gets gsEnv
            e2 <- freshN "env_"
            emit ("KEnv *" <> e2 <> " = kpush(" <> ref <> ", " <> env <> ");")
            withEnv e2 (go rest)
      KAssign refT monadic rhsT -> do
        rhs <- compile rhsT
        rhsv <-
          if monadic
            then emitRunIOValue "rhs_" rhs
            else pure rhs
        re <- compile refT
        emit ("kref_set(" <> re <> ", " <> rhsv <> ");")
        go rest
      -- A statement-`if` that is the do-block's tail: its branches are in
      -- tail position, so a recursive IO call in a branch must defer (not
      -- recurse through krun_io).  Compile the branches in 'TailEffect'
      -- (each path returns); the if's normal completion is discarded so the
      -- do-block yields Unit (§18.8).  A non-tail `if` runs for effect.
      KIf alts mels
        -- A statement-`if` that is the do-block's tail: its branches are in
        -- tail position, so compile them in 'TailEffect' (each path returns,
        -- deferring its tail IO action + finalizers via emitTailIO — stack
        -- safe and defer-correct).  A non-tail `if` runs for effect.
        | null rest && (mode == Tail || mode == TailEffect) -> compileKIfTail mode alts mels
        | otherwise -> compileKIf alts mels >> go rest
      KWhile ml cond bdy mels -> compileLoop ml (LoopWhile cond) bdy mels >> go rest
      KFor ml pat src bdy mels -> compileLoop ml (LoopFor pat src) bdy mels >> go rest
      -- §18.8.3.1: a transparent nested do-statement compiles as a child scope
      -- (its own §18.7 defer frame and label) that inherits the enclosing
      -- loop/return targets.  If it is itself the tail item of a value-returning
      -- do-block, preserve the enclosing tail mode: `else do ...` in a tail
      -- branch must return the sub-do's final value, not discard it as an
      -- effect-only nested statement.
      KSubDo subLbl subItems
        | null rest && (mode == Tail || mode == TailEffect) -> compileItems subLbl mode subItems
        | otherwise -> compileItems subLbl Nested subItems >> go rest
      KBreak ml -> gotoLoop ml lcBreak
      KContinue ml -> gotoLoop ml lcContinue
      -- §18 let? : bind the pattern and continue, or run the else block
      -- (which replaces the rest of this scope).
      KLetQ pat t mElse -> do
        te <- compile t
        sv <- freshN "letq_"
        emit ("KValue *" <> sv <> " = " <> te <> ";")
        env <- gets gsEnv
        let onElse = compileLetQElse mode sv mElse
        case distributePat pat of
          -- Common case: a single (or-free) pattern.  Preserves the
          -- irrefutable fast path and the simple if\/else lowering.
          [single] -> do
            mtest <- patTest sv single
            let onMatch = do env' <- bindPatScrut sv env single; withEnv env' (go rest)
            case mtest of
              Nothing -> onMatch -- irrefutable: always binds
              Just test -> do
                (mblk, ()) <- captured env onMatch
                (eblk, ()) <- captured env onElse
                emit ("if (" <> test <> ") {")
                forM_ mblk (emit . ("  " <>))
                emit "} else {"
                forM_ eblk (emit . ("  " <>))
                emit "}"
          -- §17.2.3 binding or-pattern in let? position: try each or-free
          -- alternative in source order; the first whose runtime test passes
          -- binds its variables and continues with the rest of the scope,
          -- otherwise the else block runs (matching the interpreter, which
          -- tries the alternatives in order before falling to the else).
          alts -> do
            done <- freshN "letqm_"
            emit ("int " <> done <> " = 0;")
            forM_ alts $ \alt -> do
              emit ("if (!" <> done <> ") {")
              (blk, ()) <- captured env $ do
                mtest <- patTest sv alt
                let bindAndGo = do
                      env' <- bindPatScrut sv env alt
                      withEnv env' (go rest)
                case mtest of
                  Nothing -> bindAndGo >> emit (done <> " = 1;")
                  Just test -> do
                    emit ("if (" <> test <> ") {")
                    bindAndGo
                    emit ("  " <> done <> " = 1;")
                    emit "}"
              forM_ blk (emit . ("  " <>))
              emit "}"
            (eblk, ()) <- captured env onElse
            emit ("if (!" <> done <> ") {")
            forM_ eblk (emit . ("  " <>))
            emit "}"
      -- §18.7: register a do-block-scope exit action (run LIFO at exit).
      -- A defer nested in a loop/if body is a distinct per-iteration scope
      -- whose timing this do-block-level model would change, so it is
      -- rejected rather than run at the wrong time.
      -- §18.7: register onto THIS scope's defer frame (the head of the
      -- relevant stack — gsDefer for a Tail/TailEffect scope, gsScopeDefers
      -- for a Nested loop/if body).  ndefer>0 guarantees the frame exists.
      -- The deferred action is a SUSPENDED thunk evaluated at scope exit
      -- (not eagerly at registration), so it observes state mutated between
      -- here and the flush — matching the interpreter (`evalK ... t` is run
      -- lazily from the exit list).
      KDefer ml t -> do
        de <- compileDeferAction t
        -- §18.7: `defer@L` registers onto the frame of the enclosing scope
        -- labeled L (which may be outer; its C arr/cnt locals are lexically
        -- in scope here). Plain `defer` uses the current scope's frame.
        frame <- gets $ \g -> case ml of
          Just l | Just fr <- lookup l (gsDeferLabels g) -> fr
          _ -> case mode of
            Nested -> head (gsScopeDefers g)
            _ -> head (gsDefer g)
        registerDefer frame de
        go rest
      -- §19.5: acquire the owned resource, attach `release resource` to this
      -- scope's exit frame (run LIFO with defers via krun_io at exit, on every
      -- exit path), then bind `pat` (borrowed) for the rest of the scope.
      KUsing pat acquireT releaseT -> do
        ae <- compile acquireT
        rv <- emitRunIOValue "ures_" ae
        re <- compile releaseT
        frame <- gets $ \g -> case mode of
          Nested -> head (gsScopeDefers g)
          _ -> head (gsDefer g)
        registerDefer frame ("kapp(" <> re <> ", " <> rv <> ")")
        bindAndContinue rv pat
      where
        -- bind an irrefutable do-pattern (with a runtime check for any
        -- refutable shape) and continue with the rest of this scope (the
        -- `rest` closed over from the enclosing `go (item : rest)` clause)
        bindAndContinue sv pat = do
          env <- gets gsEnv
          mtest <- patTest sv pat
          case mtest of
            Just test ->
              emit ("if (!(" <> test <> ")) krt_fail(\"irrefutable binding failed at runtime\");")
            Nothing -> pure ()
          env' <- bindPatScrut sv env pat
          withEnv env' (go rest)
        -- P0.2: emit the scalarized var group: each var keeps its retained
        -- heap ref (boxed fallback layout) AND gets an int64 shadow local;
        -- gsScalars maps each var's de Bruijn index (at the push-free loop
        -- body) to (local, ref); then the scalar+boxed loop, then the
        -- continuation (reads the flushed refs, region off).
        emitScalarLoop plan = goVars [] (slInits plan)
          where
            k = length (slInits plan)
            goVars acc [] = do
              let declOrder = reverse acc -- [(s0,ref0), (s1,ref1), …] in decl order
                  scs = Map.fromList [(k - 1 - j, sr) | (j, sr) <- zip [0 ..] declOrder]
              saved <- gets gsScalars
              modify' $ \g -> g {gsScalars = scs}
              compileScalarWhile (slLabel plan) (slCond plan) (slBody plan)
              modify' $ \g -> g {gsScalars = saved}
              go (slRest plan)
            goVars acc (initLit : more) = do
              ref <- freshN "var_"
              emit ("KValue *" <> ref <> " = kref_new(kint(" <> cIntLit initLit <> "));")
              env <- gets gsEnv
              e2 <- freshN "env_"
              emit ("KEnv *" <> e2 <> " = kpush(" <> ref <> ", " <> env <> ");")
              s <- freshN "sv_"
              emit ("int64_t " <> s <> " = " <> cIntLit initLit <> ";")
              withEnv e2 (goVars ((s, ref) : acc) more)

-- | §18.2.5: jump to a loop's continue\/break target. @ml@ selects the
-- loop: 'Nothing' is the innermost; @Just l@ the enclosing loop labelled
-- @l@ (the elaborator already verified the label resolves).
gotoLoop :: Maybe Text -> (LoopCtx -> Text) -> Gen ()
gotoLoop ml proj = do
  loops <- gets gsLoops
  let target = case ml of
        Nothing -> case loops of (lc : _) -> Just lc; [] -> Nothing
        Just l -> lookupLoop l loops
  case target of
    Just lc -> do
      -- §18.7: a break/continue unwinds every Nested defer scope from here
      -- down to (and including) the target loop's body, running their
      -- defers LIFO before the jump.  lcScopeDepth is gsScopeDefers' length
      -- at the target loop's body entry, so the crossed frames are the ones
      -- above it.
      depth <- gets (length . gsScopeDefers)
      frames <- gets (take (depth - lcScopeDepth lc) . gsScopeDefers)
      flushFramesInline frames
      emit ("goto " <> proj lc <> ";")
    Nothing -> emit "break;" -- defensive: rejected upstream (§18.2.5)
  where
    lookupLoop l = foldr (\lc acc -> if lcLabel lc == Just l then Just lc else acc) Nothing

-- | Return a pure value from a Tail scope, first running its §18.7 defer
-- frames LIFO (innermost frame first) inline — the value is not a tail IO
-- action, so there is no recursion to keep off the C stack.
emitTailReturn :: Text -> Gen ()
emitTailReturn e = do
  frames <- gets gsDefer
  case frames of
    [] -> emit ("return " <> e <> ";")
    _ -> do
      r <- freshN "ret_"
      emit ("KValue *" <> r <> " = " <> e <> ";")
      flushFramesInline frames
      emit ("return " <> r <> ";")

-- | Run defer frames LIFO inline (innermost frame first; within a frame,
-- last-registered first).  Each `cnt` is drained so a later flush on a
-- different control path is a no-op.
flushFramesInline :: [(Text, Text)] -> Gen ()
flushFramesInline frames =
  forM_ frames $ \(arr, cnt) -> do
    result <- freshN "defer_result"
    emit ("while (" <> cnt <> " > 0) {")
    emit ("  KValue *" <> result <> " = krun_io(" <> arr <> "[--" <> cnt <> "]);")
    emit ("  if (kis_fail(" <> result <> ")) return " <> result <> ";")
    emit "}"

-- | Run an IO action in generated do-kernel code and propagate typed native
-- failures immediately.  A failure exits the current generated scope after
-- draining every active §18.7 defer frame, mirroring the interpreter's
-- exception unwinding instead of binding the failure sentinel as an ordinary
-- value.
emitRunIOValue :: Text -> Text -> Gen Text
emitRunIOValue prefix action = do
  v <- freshN prefix
  emit ("KValue *" <> v <> " = krun_io(" <> action <> ");")
  emitPropagateFailure v
  pure v

emitRunIODiscard :: Text -> Gen ()
emitRunIODiscard action = do
  v <- emitRunIOValue "io_" action
  emit ("(void)" <> v <> ";")

emitPropagateFailure :: Text -> Gen ()
emitPropagateFailure v = do
  frames <- gets $ \g -> gsScopeDefers g ++ gsDefer g
  emit ("if (kis_fail(" <> v <> ")) {")
  forM_ frames $ \(arr, cnt) ->
    emit ("  while (" <> cnt <> " > 0) krun_io(" <> arr <> "[--" <> cnt <> "]);")
  emit ("  return " <> v <> ";")
  emit "}"

-- | Return a do-block's tail IO action, deferring its execution to the
-- driving @krun_io@ loop so a sequenced IO tail-recursion runs in constant
-- C stack (§27.5A.3).  @discard@ marks a tail statement-@if@ branch whose
-- result is dropped (the do-block yields Unit).  The active Tail-scope
-- defer frames (innermost first) are handed over with the action via nested
-- @kio_finally@ (finalizers run after the action completes, accumulated on
-- the krun_io heap stack rather than the C stack — order: innermost first).
emitTailIO :: Bool -> Text -> Gen ()
emitTailIO discard action = do
  frames <- gets gsDefer
  case frames of
    [] -> emit ("return " <> (if discard then "kio_effect(" else "kio_tail(") <> action <> ");")
    _ ->
      let core = if discard then "kio_effect(" <> action <> ")" else action
          wrapped = foldl (\acc (arr, cnt) -> "kio_finally(" <> acc <> ", " <> arr <> ", " <> cnt <> ")") core frames
       in emit ("return " <> wrapped <> ";")

-- | Register a §18.7 deferred action into the given (arr, cnt) frame.
registerDefer :: (Text, Text) -> Text -> Gen ()
registerDefer (arr, cnt) te = emit (arr <> "[" <> cnt <> "++] = " <> te <> ";")

-- | Like 'bindPat' but threads the concrete scrutinee C-expression
-- through the binding projections.
bindPatScrut :: Text -> Text -> CorePat -> Gen Text
bindPatScrut sv env pat = do
  lvals <- gets gsParamLvals
  if null lvals
    then foldM push env (patBindings sv pat) -- boxed: kpush each onto the KEnv
    else do
      -- R2.3-rest FLAT worker: bind each pattern variable to a C local via
      -- 'bindFlatLocal' (the LAST binding becomes de Bruijn index 0, matching
      -- the kpush order); the scope is restored by the enclosing 'captured'.
      forM_ (patBindings sv pat) (bindFlatLocal "pat_")
      gets gsEnv -- unchanged (flat reads via gsParamLvals, not the KEnv)
  where
    push e valExpr = do
      n <- freshN "env_"
      emit ("KEnv *" <> n <> " = kpush(" <> valExpr <> ", " <> e <> ");")
      pure n

-- | R2.3-rest: bind @valExpr@ to a fresh C local in a flat worker and prepend
-- it to 'gsParamLvals' as de Bruijn index 0 (params and earlier binders shift
-- up); the enclosing 'captured' block restores the scope.  Returns the C name.
bindFlatLocal :: Text -> Text -> Gen Text
bindFlatLocal prefix valExpr = do
  v <- freshN prefix
  emit ("KValue *" <> v <> " = " <> valExpr <> ";")
  modify' $ \st -> st {gsParamLvals = v : gsParamLvals st}
  pure v

compileKIf :: [(Term, [KItem])] -> Maybe [KItem] -> Gen ()
compileKIf alts mels = go alts
  where
    go [] = case mels of
      Just els -> emitBlock els
      Nothing -> pure ()
    go ((c, body) : more) = do
      ce <- compile c
      emit ("if (kas_bool(" <> ce <> ")) {")
      env <- gets gsEnv
      (blk, ()) <- captured env (compileItems Nothing Nested body)
      forM_ blk (emit . ("  " <>))
      emit "}"
      unless (null more && mels == Nothing) $ do
        emit "else {"
        go more
        emit "}"
    emitBlock items = do
      env <- gets gsEnv
      (blk, ()) <- captured env (compileItems Nothing Nested items)
      emit "{"
      forM_ blk (emit . ("  " <>))
      emit "}"

-- | Compile a do-block's TAIL statement-`if`: every branch is compiled in
-- 'TailEffect' (so each path ends in a @return@ — a recursive IO call in a
-- branch defers via @kio_effect@ rather than recursing through @krun_io@,
-- §27.5A.3), and a missing/exhausted else yields Unit (§18.8 — the if's
-- normal completion is discarded).
compileKIfTail :: ScopeMode -> [(Term, [KItem])] -> Maybe [KItem] -> Gen ()
compileKIfTail tailMode alts mels = goAlts alts
  where
    goAlts [] = case mels of
      Just els -> emitBranch els
      Nothing -> emitTailReturn "kunit()" -- no/exhausted else: yield Unit, flush defers
    goAlts ((c, body) : more) = do
      ce <- compile c
      emit ("if (kas_bool(" <> ce <> ")) {")
      emitBranch body
      emit "} else {"
      goAlts more
      emit "}"
    emitBranch items = do
      env <- gets gsEnv
      (blk, ()) <- captured env (compileItems Nothing tailMode items)
      forM_ blk (emit . ("  " <>))

data LoopKind = LoopWhile !Term | LoopFor !CorePat !Term

-- | Compile a @while@\/@for@ loop using explicit @goto@ labels, so §18.2.5
-- labelled @break@\/@continue@ targeting an outer loop work uniformly and
-- the §18.8 @else@ (run only on normal completion, not after a @break@) is
-- placed past the body and before the break label.
compileLoop :: Maybe Text -> LoopKind -> [KItem] -> Maybe [KItem] -> Gen ()
compileLoop mlabel kind body mels = do
  env <- gets gsEnv
  n <- freshN "lp_"
  let contL = "kcont_" <> n -- continue target (re-test)
      advL = "kadv_" <> n -- for-loop advance (continue lands here)
      normL = "knorm_" <> n -- normal completion (run else)
      endL = "kend_" <> n -- break target (skip else)
      -- continue re-tests; for a `for` it must advance the cursor first.
      contTarget = case kind of LoopWhile _ -> contL; LoopFor _ _ -> advL
  -- the Nested defer-frame depth OUTSIDE this loop's body; a break/continue
  -- to this loop unwinds the frames pushed since (§18.7, see gotoLoop).
  scopeDepth <- gets (length . gsScopeDefers)
  let ctx = LoopCtx mlabel contTarget endL scopeDepth
  -- A label is emitted only when something jumps to it (continue → advL,
  -- break → endL), so the generated loop has no unused goto labels under
  -- -Wall; contL/normL are always part of the loop's own control flow.
  let usesLabel l = any (T.isInfixOf ("goto " <> l))
  bodyBlk <- case kind of
    LoopWhile cond -> do
      (condBlk, ce) <- captured env (compile cond)
      (bb, ()) <- withLoop ctx (captured env (compileItems mlabel Nested body))
      emit (contL <> ": ;")
      forM_ condBlk (emit . ("  " <>))
      emit ("if (!kas_bool(" <> ce <> ")) goto " <> normL <> ";")
      forM_ bb emit
      emit ("goto " <> contL <> ";")
      pure bb
    LoopFor pat src -> do
      se <- compile src
      it <- freshN "it_"
      emit ("KValue *" <> it <> " = " <> se <> ";")
      (bb, ()) <- withLoop ctx $ captured env $ case pat of
        -- a wildcard element binds nothing: skip the unused element var
        CPWild -> compileItems mlabel Nested body
        _ -> do
          elemV <- freshN "elem_"
          emit ("KValue *" <> elemV <> " = kctor_arg(" <> it <> ", 0);")
          e' <- bindPatScrut elemV env pat
          withEnv e' (compileItems mlabel Nested body)
      emit (contL <> ": ;")
      emit ("if (!kis_cons(" <> it <> ")) goto " <> normL <> ";")
      forM_ bb emit
      when (usesLabel advL bb) $ emit (advL <> ": ;")
      emit (it <> " = kctor_arg(" <> it <> ", 1);")
      emit ("goto " <> contL <> ";")
      pure bb
  emit (normL <> ": ;")
  elsBlk <- case mels of
    Just els -> do
      (eb, ()) <- captured env (compileItems Nothing Nested els)
      emit "{"
      forM_ eb (emit . ("  " <>))
      emit "}"
      pure eb
    Nothing -> pure []
  when (usesLabel endL bodyBlk || usesLabel endL elsBlk) $ emit (endL <> ": ;")

-- | Run an action with @ctx@ pushed as the innermost enclosing loop.
withLoop :: LoopCtx -> Gen a -> Gen a
withLoop ctx act = do
  saved <- gets gsLoops
  modify' $ \g -> g {gsLoops = ctx : saved}
  r <- act
  modify' $ \g -> g {gsLoops = saved}
  pure r

-- ── P0.2: scalarize a non-escaping Int `var` loop to int64 C locals ──────
-- (raw-C review P0.2).  A run of @var x = <in-range Int literal>@ declarations
-- IMMEDIATELY followed by a @while <int compare> do <flat int assignments>@,
-- where every such var is a non-escaping Int and the loop body / continuation
-- contain no closure-creating form, lowers to int64 C locals + a scalar while
-- loop with NO kref/kvar/kint per iteration.  On overflow / INT64_MIN the
-- scalar loop flushes EVERY var to its retained heap ref and jumps into the
-- EXISTING boxed loop, which continues with GMP promotion (§6) — bit-identical
-- to the interpreter.  Anything outside this exact shape keeps the (correct)
-- boxed lowering, so no deferral can regress.

i64InRange :: Integer -> Bool
i64InRange m = m >= toInteger (minBound :: Int) && m <= toInteger (maxBound :: Int)

-- | The de Bruijn index of a scalarized-var READ — @__runIO (readRef (CVar i))@
-- with @0 <= i < k@ (the elaborator auto-derefs a surface var read).
scalarVarReadIdx :: Int -> Term -> Gen (Maybe Int)
scalarVarReadIdx k term = case runIOSplice term of
  Just action -> case spineOf action of
    (CGlob h, sargs) -> do
      mp <- globPrimName h
      case (mp, [a | (Expl, a) <- sargs]) of
        (Just "readRef", [CVar i]) | i >= 0 && i < k -> pure (Just i)
        _ -> pure Nothing
    _ -> pure Nothing
  Nothing -> pure Nothing

-- | int64-expressible over scalar-var reads (idx<k), in-range Int literals,
-- and the int arith prims — and NOTHING else (an outer-var read, a non-listed
-- prim, a ctor, etc. fails, keeping the loop boxed).
i64LoopExpr :: Int -> Term -> Gen Bool
i64LoopExpr k term = do
  sv <- scalarVarReadIdx k term
  case sv of
    Just _ -> pure True
    Nothing -> case term of
      CLit (LitInt m) -> pure (i64InRange m)
      _ -> case spineOf term of
        (CGlob h, sargs) -> do
          let expl = [a | (Expl, a) <- sargs]
          mp <- globPrimName h
          case mp of
            -- INT arith only (KInt64 result): a scalar var loop scalarizes Int
            -- vars to int64 locals, so a double op must keep it boxed.
            Just p | Just (KInt64, argks) <- arithPrim p, length expl == length argks -> andM (map (i64LoopExpr k) expl)
            _ -> pure False
        _ -> pure False

-- | A loop condition: a saturated INT compare over loop-expressible operands.
i64LoopCond :: Int -> Term -> Gen Bool
i64LoopCond k term = case spineOf term of
  (CGlob h, sargs) -> do
    let expl = [a | (Expl, a) <- sargs]
    mp <- globPrimName h
    case (mp >>= cmpPrim, expl) of
      (Just (_, KInt64), [_, _]) -> andM (map (i64LoopExpr k) expl)
      _ -> pure False
  _ -> pure False

data ScalarLoop = ScalarLoop
  { slInits :: ![Integer] -- the k var initial literals, declaration order
  , slLabel :: !(Maybe Text)
  , slCond :: !Term
  , slBody :: ![KItem] -- flat non-monadic @KAssign (CVar idx<k) _ rhs@
  , slRest :: ![KItem] -- continuation after the loop
  }

-- | Does any Term in this item (recursively) build a closure/thunk/do that
-- could capture an enclosing var by reference? (Reuses 'bodyCapturesEnv'.)
itemHasClosure :: KItem -> Bool
itemHasClosure item = case item of
  KExpr t -> bodyCapturesEnv t
  KBind _ _ t -> bodyCapturesEnv t
  KLet _ _ t -> bodyCapturesEnv t
  KLetQ _ t mels -> bodyCapturesEnv t || maybe False (bodyCapturesEnv . snd) mels
  KVarItem _ t -> bodyCapturesEnv t
  KAssign r _ t -> bodyCapturesEnv r || bodyCapturesEnv t
  KReturn t -> bodyCapturesEnv t
  KWhile _ c b mels -> bodyCapturesEnv c || any itemHasClosure b || maybe False (any itemHasClosure) mels
  KFor _ _ s b mels -> bodyCapturesEnv s || any itemHasClosure b || maybe False (any itemHasClosure) mels
  KIf alts mels -> any (\(c, b) -> bodyCapturesEnv c || any itemHasClosure b) alts || maybe False (any itemHasClosure) mels
  KDefer _ t -> bodyCapturesEnv t
  KUsing _ a r -> bodyCapturesEnv a || bodyCapturesEnv r
  KSubDo _ b -> any itemHasClosure b
  KBreak _ -> False
  KContinue _ -> False

-- | Recognize the eligible scalarizable shape at the head of an item list.
scalarLoopPlan :: [KItem] -> Gen (Maybe ScalarLoop)
scalarLoopPlan items =
  case span isKVar items of
    (varRun@(_ : _), KWhile ml cond body Nothing : rest2)
      | Just inits <- traverse initLit varRun ->
          do
            let k = length inits
            okCond <- i64LoopCond k cond
            okBody <- andM (map (bodyItemOk k) body)
            -- v1: non-empty flat body, no closure anywhere in the loop or the
            -- continuation (escape gate), no else (deferred).
            let noClosure = not (any itemHasClosure (KWhile ml cond body Nothing : rest2))
            pure $
              if okCond && okBody && not (null body) && noClosure
                then Just (ScalarLoop inits ml cond body rest2)
                else Nothing
    _ -> pure Nothing
  where
    isKVar (KVarItem _ _) = True
    isKVar _ = False
    initLit (KVarItem _ (CLit (LitInt m))) | i64InRange m = Just m
    initLit _ = Nothing
    bodyItemOk k (KAssign (CVar idx) False rhs) | idx >= 0 && idx < k = i64LoopExpr k rhs
    bodyItemOk _ _ = pure False

-- | Emit a scalarized var loop: an int64 scalar fast-path loop, then the
-- EXISTING boxed loop as the overflow continuation.  Requires 'gsScalars' to
-- map each var's de Bruijn index (at the loop body) to its (int64 local, ref).
compileScalarWhile :: Maybe Text -> Term -> [KItem] -> Gen ()
compileScalarWhile mlabel cond body = do
  scs <- gets gsScalars
  cur <- gets gsCur
  n <- freshN "sl_"
  let scontL = "kscont_" <> n
      sflushL = "ksflush_" <> n
      boxedL = "ksbox_" <> n
      afterL = "ksaft_" <> n
  -- A SNAPSHOT int64 local per scalar var holds the var's value at the TOP of
  -- the current iteration (pre-condition, pre-body).  The body commits each
  -- assignment in place (so a later read in the same iteration sees the new
  -- value — sequential semantics), but on overflow we flush the SNAPSHOTS, not
  -- the partially-mutated scalars, then re-run the iteration boxed from the
  -- top — so an earlier-committed assignment is NOT applied twice.  The
  -- snapshots are register copies (no per-iteration allocation).
  snaps <- forM (Map.elems scs) $ \(s, ref) -> do
    snap <- freshN "snap_"
    emit ("int64_t " <> snap <> ";")
    pure (s, ref, snap)
  let flushScalars = ["kref_set(" <> ref <> ", kint(" <> s <> "));" | (s, ref, _) <- snaps]
      flushSnaps = ["kref_set(" <> ref <> ", kint(" <> snap <> "));" | (_, ref, snap) <- snaps]
  savedEsc <- gets gsI64Escape
  -- the scalar copy: gsScalarRegion on; an overflow flushes the PRE-iteration
  -- snapshots and jumps to the boxed loop, which re-runs this iteration with
  -- GMP promotion (§6) — no double application of earlier assignments.
  modify' $ \g ->
    g
      { gsScalarRegion = True
      , gsI64Escape = T.concat (map (<> " ") flushSnaps) <> "goto " <> boxedL <> ";"
      }
  emit (scontL <> ": ;")
  -- snapshot BEFORE the condition test (so even a condition-overflow flushes a
  -- valid pre-iteration state, never an uninitialized snapshot).
  forM_ snaps $ \(s, _, snap) -> emit (snap <> " = " <> s <> ";")
  ce <- scalarCond cur [] KInt64 [] cond
  emit ("if (!" <> ce <> ") goto " <> sflushL <> ";")
  forM_ body $ \item -> case item of
    KAssign (CVar idx) False rhs -> do
      rhse <- scalarExpr cur [] KInt64 [] KInt64 rhs
      case Map.lookup idx scs of
        Just (s, _) -> emit (s <> " = " <> rhse <> ";")
        Nothing -> lr1UnreachableStmt
    _ -> lr1UnreachableStmt
  emit ("goto " <> scontL <> ";")
  -- normal scalar completion: flush every scalar var's FINAL value, skip boxed.
  emit (sflushL <> ": ;")
  forM_ flushScalars emit
  emit ("goto " <> afterL <> ";")
  -- boxed continuation (overflow target): the EXISTING boxed lowering, region
  -- off, reading the just-flushed (snapshot) refs and promoting to GMP (§6).
  emit (boxedL <> ": ;")
  modify' $ \g -> g {gsScalarRegion = False}
  compileLoop mlabel (LoopWhile cond) body Nothing
  emit (afterL <> ": ;")
  modify' $ \g -> g {gsI64Escape = savedEsc}

-- | §18 let? else branch: bind the residue pattern and run the else action
-- as the scope's result (it replaces the rest of the scope).  With no
-- @else@, a failed let? is a runtime defect (no Alternative available).
compileLetQElse :: ScopeMode -> Text -> Maybe (CorePat, Term) -> Gen ()
compileLetQElse mode sv mElse = case mElse of
  Nothing -> emit "krt_fail(\"let? pattern failed and no Alternative is available\");"
  Just (rp, fe) -> do
    env <- gets gsEnv
    -- §18.2.1: the else residue pattern is matched against the SCRUTINEE; a
    -- refutable residue that does not match is a runtime error — mirroring the
    -- interpreter (`matchPat ec rp x` -> Nothing -> "let? else: residue
    -- pattern failed").  Without this test the backend would bind the wrong
    -- constructor's fields and run the else body, silently diverging.
    mtest <- patTest sv rp
    case mtest of
      Just test -> emit ("if (!(" <> test <> ")) krt_fail(\"let? else: residue pattern failed\");")
      Nothing -> pure ()
    env' <- bindPatScrut sv env rp
    fee <- withEnv env' (compile fe)
    -- the else action replaces the rest of the scope, so it is the tail:
    -- defer it (stack-safe, §27.5A.3, with finalizers) the same way a
    -- trailing KExpr is.
    case mode of
      Tail -> emitTailIO False fee
      TailEffect -> emitTailIO True fee
      Nested -> emitRunIODiscard fee
