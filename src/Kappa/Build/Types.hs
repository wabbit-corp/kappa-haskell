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
  , NativeBindingSource (..)
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

data NativeBindingSource
  = PkgConfigSource !Text !(Maybe Text) -- ^ package, minVersion
  | HeadersSource ![Text]
  | SymbolListSource ![Text]
  | ShimSource !Text
  | PrebuiltNativeSource !Text
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
  , nbSource :: !NativeBindingSource
  , nbAbi :: !NativeAbi
  , nbHeaders :: ![NativeBindingSource]
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
  deriving stock (Eq, Show)
