{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE NoFieldSelectors #-}
{-# LANGUAGE OverloadedRecordDot #-}

-- | Haskell mirror of the increment-1 @std.build@ schema (§29.8). These
-- records hold the *semantic* build configuration only: they carry no
-- source spans or value provenance, so structural equality is the
-- semantic build identity of §36.2.1 by construction (provenance is
-- tracked separately by the loader and never participates in this
-- identity). A value of 'BuildConfig' is the reified normal form of a
-- manifest's @buildConfig@ binding (see "Kappa.Build.Reify").
--
-- Records here use the dot-syntax house style: fields are /unprefixed/ and
-- read as @bc.name@ \/ @target.spec@ ('OverloadedRecordDot' +
-- 'NoFieldSelectors'). 'Target' is a product (@name@ + a 'TargetSpec' sum
-- whose variants each carry a single-constructor spec record), so every
-- field is total — there are no partial fields to dot-access unsafely.
module Kappa.Build.Types
  ( BuildConfig (..)
  , PackageVersion (..)
  , SourceRoot (..)
  , FragmentAxis (..)
  , Dependency (..)
  , ModuleSelector (..)
  , BackendProfile (..)
  , CType (..)
  , FfiClass (..)
  , SymbolDecl (..)
  , NativeSurface (..)
  , NativeInput (..)
  , NativeAbi (..)
  , NativeLinkSpec (..)
  , NativeLoadSpec (..)
  , HostBinding (..)
  , Target (..)
  , TargetSpec (..)
  , ExecutableSpec (..)
  , LibrarySpec (..)
  , TestSpec (..)
  , AggregateSpec (..)
  , AliasSpec (..)
  , BenchmarkSpec (..)
  ) where

import Data.Text (Text)

data BuildConfig = BuildConfig
  { name :: !Text
  , version :: !PackageVersion
  , sourceRoots :: ![SourceRoot]
  , fragmentAxes :: ![FragmentAxis]
  , dependencies :: ![Dependency]
  , hostBindings :: ![HostBinding]
  , targets :: ![Target]
  }
  deriving stock (Eq, Show)

newtype PackageVersion = PackageVersion {raw :: Text}
  deriving stock (Eq, Show)

newtype SourceRoot = SourceRoot {path :: Text}
  deriving stock (Eq, Show)

data FragmentAxis = FragmentAxis
  { name :: !Text
  , tags :: ![Text]
  }
  deriving stock (Eq, Show)

data Dependency
  = RegistryDep !Text !Text -- ^ name, version requirement
  | GitDep !Text !Text !Text -- ^ name, url, rev
  | PathDep !Text !Text -- ^ name, path
  | UrlDep !Text !Text -- ^ name, archive url
  deriving stock (Eq, Show)

data ModuleSelector
  = SelModule !Text
  | SelModulesUnder !Text
  deriving stock (Eq, Show)

data BackendProfile
  = NativeBackend !Text !Text -- ^ toolchain, target triple
  | JvmBackend
  | DotNetBackend
  deriving stock (Eq, Show)

-- | §26.1.1/§26.1.4 conservative ABI type vocabulary admitted in a native
-- binding's symbol signatures. Each maps to a documented Kappa surface type
-- and a C ABI type (see "Kappa.Backend.NativeFfi").
data CType
  = CtUnit
  | CtInt -- ^ C @int@ (the ergonomic default; surfaces as Integer)
  | CtInt64 -- ^ C @int64_t@
  | CtBool
  | CtDouble -- ^ C @double@ (= F64)
  | CtString
  | CtHandle
  | CtRawPtr
  -- §26.1.1 exact-width / pointer-width / float scalars (std.ffi). The C ABI
  -- spelling carries the exact width + signedness; the Kappa surface stays
  -- Integer/Double (the conservative integer/float class, §26.1.4).
  | CtI8 | CtI16 | CtI32 | CtI64
  | CtU8 | CtU16 | CtU32 | CtU64
  | CtIsize | CtUsize
  | CtF32 | CtF64
  deriving stock (Eq, Show)

-- | §26.1.4/§27.6: the foreign-call classification metadata every raw foreign
-- declaration MUST carry. It determines invocation routing — @nonblocking@ uses
-- ordinary runtime execution; @blocking@/@blocking-cancellable@ require backend
-- capability @rt-blocking@ and route through the blocking-work bridge.
data FfiClass
  = FfiNonblocking
  | FfiBlocking
  | FfiBlockingCancellable
  deriving stock (Eq, Show)

-- | §36.28: one exported native symbol — the Kappa member spelling, the C
-- symbol it calls, and its ABI signature (parameter types + result type).
data SymbolDecl = SymbolDecl
  { member :: !Text
  , symbol :: !Text
  , params :: ![CType]
  , result :: !CType
  }
  deriving stock (Eq, Show)

-- | §27.1.1: the binding's raw @host.native@ surface.
data NativeSurface
  = SymbolListSurface [SymbolDecl]
  -- ^ an explicit binding description (a symbol list with ABI signatures).
  | GeneratedSurface !Text ![Text]
  -- ^ §27.1.1/§36.28: a surface MECHANICALLY DERIVED by preprocessing + parsing
  -- a real header — there is NO hand-authored 'SymbolDecl'. @gsHeader@ names the
  -- header to parse (resolved on the binding's include path / pkg-config cflags);
  -- @gsSymbols@ are the C function names to extract. Build-plan resolution
  -- preprocesses the header with the binding's pkg-config\/define\/include
  -- inputs and the target ABI, parses each named function's declaration, and
  -- maps its C parameter\/result types to the conservative std.ffi\/opaque\/
  -- Option 'CType' vocabulary. A symbol whose declaration cannot be located or
  -- whose types are not conservatively mappable is a fail-closed build error.
  -- (The explicit-list form is appropriate for a small curated surface such as
  -- a shim's public API.)
  | GeneratedPrefixSurface !Text !Text
  -- ^ §26.1.2/§27.1.1: a BROAD raw surface derived by parsing EVERY function
  -- declaration in @gpHeader@ (first field) whose C name begins with @gpPrefix@
  -- (second field). This is the general header-derived binding path: the build
  -- plan extracts all matching declarations and maps each conservatively;
  -- declarations requiring features the conservative ABI cannot represent
  -- soundly (callbacks\/function pointers, by-value structs\/unions\/enums,
  -- variadics) are SKIPPED — i.e. rejected from the surface, never guessed
  -- (§26.1.2) — and the skipped set is reported (no silent omission). The
  -- generated set is pinned in the lockfile, so a header change repins.
  deriving stock (Eq, Show)

-- | §36.28 binding sources: realization inputs naming WHERE/HOW the declared
-- C symbols are provided and located. These are inert config data (§35.13);
-- discovery (pkg-config, header digesting) happens later, in build-plan
-- resolution, never during manifest evaluation.
data NativeInput
  = HeadersInput ![Text] -- ^ header files (also adds their dirs to -I)
  | IncludeDirInput !Text -- ^ an explicit -I include directory
  | DefineInput !Text !Text -- ^ a -D preprocessor definition (name, value)
  | PkgConfigInput !Text !(Maybe Text) -- ^ pkg-config package, optional minVersion
  | ShimInput ![Text] -- ^ user-authored C shim translation units to compile+link
  | ModuleMapInput ![Text] -- ^ native module-map files (digested; surface still from symbolList)
  | PrebuiltInput !Text !(Maybe Text) -- ^ prebuilt artifact path, optional expected identity
  | CStringSymbolsInput ![Text]
  -- ^ §26.1.4: the C symbols whose @char *@ parameters/results the binding
  -- PROVES are NUL-terminated C strings (the "binding description proves string
  -- semantics" path). Header-derived generation maps a @char *@ to @CtString@
  -- ONLY for a symbol in this set; otherwise a @char *@ is conservatively an
  -- @Option RawPtr@ like any other pointer (a raw @char *@ is not provably a
  -- readable NUL-terminated string of a known encoding). Recorded in identity.
  | ClassifyInput !FfiClass
  -- ^ §26.1.4/§27.6: the foreign-call classification carried by the binding's
  -- raw declarations. Default (when absent) is @nonblocking@ — the conservative
  -- choice for a direct native call that returns to the caller. A binding whose
  -- calls genuinely wait on I/O declares @blocking@. Recorded in the binding's
  -- native provenance + host-source identity (it affects runtime semantics).
  | VerifyInput ![Text]
  -- ^ §26.1.5/§27.1.1: real C declarations (verbatim prototypes / type
  -- aliases) that the binding's @symbolList@ / shim depends on. Build-plan
  -- resolution VERIFIES each against the located real headers by compiling
  -- a probe TU that @#include@s the headers and redeclares each — a
  -- mismatch with the actual header declaration fails the build (fail-closed,
  -- §36.28). This turns the otherwise author-controlled symbol surface into
  -- one checked against the real ABI, and the verified decls + header digests
  -- are recorded in the build's native provenance.
  deriving stock (Eq, Show)

data NativeAbi = CAbi
  deriving stock (Eq, Show)

data NativeLinkSpec
  = DynamicLink ![Text]
  | StaticLink ![Text]
  | NoLink
  deriving stock (Eq, Show)

data NativeLoadSpec
  = SystemLoader
  | BundledLoader
  | RuntimeLoad
  | ProvidedByHost
  deriving stock (Eq, Show)

data HostBinding = NativeBinding
  { name :: !Text
  , provides :: ![ModuleSelector]
  , surface :: !NativeSurface
  , abi :: !NativeAbi
  , inputs :: ![NativeInput]
  , link :: !NativeLinkSpec
  , load :: !NativeLoadSpec
  }
  deriving stock (Eq, Show)

-- | A build target: a name plus its kind-specific configuration. Splitting
-- the common @name@ from the per-kind 'TargetSpec' keeps every record
-- single-constructor, so every field is total and @target.name@ \/
-- @spec.backend@ dot access is always sound (no partial fields).
data Target = Target
  { name :: !Text
  , spec :: !TargetSpec
  }
  deriving stock (Eq, Show)

-- | The kind-specific half of a 'Target'. Each variant wraps a
-- single-constructor spec record.
data TargetSpec
  = Executable !ExecutableSpec
  | Library !LibrarySpec
  | Test !TestSpec
  | Aggregate !AggregateSpec
  | Alias !AliasSpec
  | Benchmark !BenchmarkSpec
  deriving stock (Eq, Show)

data ExecutableSpec = ExecutableSpec
  { backend :: !BackendProfile
  , fragments :: ![Text]
  , main :: !ModuleSelector
  , modules :: !ModuleSelector
  , dependencies :: ![Text]
  , hostBindings :: ![Text]
  }
  deriving stock (Eq, Show)

data LibrarySpec = LibrarySpec
  { backend :: !BackendProfile
  , fragments :: ![Text]
  , modules :: !ModuleSelector
  , dependencies :: ![Text]
  }
  deriving stock (Eq, Show)

newtype TestSpec = TestSpec {modules :: ModuleSelector}
  deriving stock (Eq, Show)

newtype AggregateSpec = AggregateSpec {members :: [Text]} -- ^ names of the member targets it groups
  deriving stock (Eq, Show)

newtype AliasSpec = AliasSpec {alias :: Text} -- ^ the name of the target this aliases
  deriving stock (Eq, Show)

data BenchmarkSpec = BenchmarkSpec
  { backend :: !BackendProfile
  , fragments :: ![Text]
  , main :: !ModuleSelector
  , modules :: !ModuleSelector
  , dependencies :: ![Text]
  }
  deriving stock (Eq, Show)
