-- @Target@ shares some field labels across its two constructors (the
-- accessors are only ever reached by constructor pattern match, never as
-- partial functions), so the partial-field warning is not meaningful here.
{-# OPTIONS_GHC -Wno-partial-fields #-}

-- | Haskell mirror of the increment-1 @std.build@ schema (§29.8). These
-- records hold the *semantic* build configuration only: they carry no
-- source spans or value provenance, so structural equality is the
-- semantic build identity of §36.2.1 by construction (provenance is
-- tracked separately by the loader and never participates in this
-- identity). A value of 'BuildConfig' is the reified normal form of a
-- manifest's @buildConfig@ binding (see "Kappa.Build.Reify").
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
  ) where

import Data.Text (Text)

data BuildConfig = BuildConfig
  { bcName :: !Text
  , bcVersion :: !PackageVersion
  , bcSourceRoots :: ![SourceRoot]
  , bcFragmentAxes :: ![FragmentAxis]
  , bcDependencies :: ![Dependency]
  , bcHostBindings :: ![HostBinding]
  , bcTargets :: ![Target]
  }
  deriving stock (Eq, Show)

newtype PackageVersion = PackageVersion {pvRaw :: Text}
  deriving stock (Eq, Show)

newtype SourceRoot = SourceRoot {srPath :: Text}
  deriving stock (Eq, Show)

data FragmentAxis = FragmentAxis
  { faName :: !Text
  , faTags :: ![Text]
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
  { sdMember :: !Text
  , sdSymbol :: !Text
  , sdParams :: ![CType]
  , sdResult :: !CType
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
  { nbName :: !Text
  , nbProvides :: ![ModuleSelector]
  , nbSurface :: !NativeSurface
  , nbAbi :: !NativeAbi
  , nbInputs :: ![NativeInput]
  , nbLink :: !NativeLinkSpec
  , nbLoad :: !NativeLoadSpec
  }
  deriving stock (Eq, Show)

data Target
  = ExecutableTarget
      { tName :: !Text
      , tBackend :: !BackendProfile
      , tFragments :: ![Text]
      , tMain :: !ModuleSelector
      , tModules :: !ModuleSelector
      , tDependencies :: ![Text]
      , tHostBindings :: ![Text]
      }
  | LibraryTarget
      { tName :: !Text
      , tBackend :: !BackendProfile
      , tFragments :: ![Text]
      , tModules :: !ModuleSelector
      , tDependencies :: ![Text]
      }
  | TestTarget
      { tName :: !Text
      , tModules :: !ModuleSelector
      }
  | AggregateTarget
      { tName :: !Text
      , tMembers :: ![Text] -- ^ names of the member targets it groups
      }
  | AliasTarget
      { tName :: !Text
      , tAlias :: !Text -- ^ the name of the target this aliases
      }
  | BenchmarkTarget
      { tName :: !Text
      , tBackend :: !BackendProfile
      , tFragments :: ![Text]
      , tMain :: !ModuleSelector
      , tModules :: !ModuleSelector
      , tDependencies :: ![Text]
      }
  deriving stock (Eq, Show)
