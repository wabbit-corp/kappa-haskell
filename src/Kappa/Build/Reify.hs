-- | Reify a checked manifest's @buildConfig@ binding into a Haskell
-- 'BuildConfig' (§35.6 deterministic normalization + decoding). The
-- builder functions of @std.build@ are total transparent definitions,
-- so evaluating the binding to normal form unfolds them to saturated
-- data constructors; this module decodes that normal form.
--
-- Reification is pure over the evaluated value and performs no discovery
-- (§35.13): it reads neither the filesystem, environment, nor any
-- dependency. Decoding failures (a stuck value, a partial application, a
-- shape the schema does not define) surface as §35.11 config
-- diagnostics rather than a crash.
module Kappa.Build.Reify
  ( reifyBuildConfig
  ) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Kappa.Build.Types
import Kappa.Check (CheckState (..))
import Kappa.Config (configFamily)
import Kappa.Core (GName (..), Literal (..), Value (..), gnameText)
import Kappa.Diagnostic
import Kappa.Eval (EvalCtx (..), Globals (..), eval, force)
import Kappa.Source

-- | Reify the @buildConfig@ binding of a checked manifest module. The
-- 'Span' locates diagnostics on the manifest file. Returns the semantic
-- 'BuildConfig' or the §35.11 diagnostics describing why it could not be
-- reified.
reifyBuildConfig :: Span -> CheckState -> ModuleName -> Either Diagnostics BuildConfig
reifyBuildConfig sp st mn =
  case Map.lookup (GName mn "buildConfig") (csCoreBodies st) of
    Nothing ->
      Left
        [ cfg "E_CONFIG_EXPECTED_VALUE"
            ( "the manifest defines no 'buildConfig' binding; a build manifest must define exactly "
                <> "one 'let buildConfig : BuildConfig = ...' (Spec §35.13)"
            )
        ]
    Just body ->
      let ctx = EvalCtx (Globals (csGlobals st)) (csMetas st) True (csFacts st)
          v = force ctx (eval ctx [] body)
       in case decBuildConfig ctx v of
            Right bc -> Right bc
            Left (code, msg) -> Left [cfg code msg]
  where
    cfg code = diag SevError StageElaborate code (Just (configFamily code)) sp

-- ── Decoder monad ────────────────────────────────────────────────────

-- A decode failure carries the §35.11 code to emit and a message.
type Dec a = Either (Text, Text) a

decFail :: Text -> Dec a
decFail msg = Left ("E_CONFIG_EVAL", msg)

decPartial :: Text -> Dec a
decPartial msg = Left ("E_CONFIG_PARTIAL_APPLICATION", msg)

-- ── Value decoders ───────────────────────────────────────────────────

asCtor :: EvalCtx -> Value -> Dec (Text, [Value])
asCtor ctx v = case force ctx v of
  VCtor g args -> Right (gnameText g, args)
  VLam {} -> decPartial "expected a build value but found a function (a builder applied to too few arguments?) (Spec §35.2.2)"
  VPrim {} -> decFail "config value did not reduce to a build constructor (stuck primitive) (Spec §35.6)"
  VGlobN g _ -> decFail ("config value did not reduce: '" <> gnameText g <> "' is opaque or unsaturated (Spec §35.6)")
  _ -> decFail "expected a build constructor (Spec §35.6)"

asStr :: EvalCtx -> Value -> Dec Text
asStr ctx v = case force ctx v of
  VLit (LitStr s) -> Right s
  _ -> decFail "expected a String literal in the manifest (Spec §35.6)"

asList :: EvalCtx -> Value -> Dec [Value]
asList ctx v = case force ctx v of
  VCtor g args
    | gnameText g == "Nil" -> Right []
    | gnameText g == "::" -> case args of
        (h : t : _) -> (h :) <$> asList ctx t
        _ -> decFail "malformed list value (Spec §35.6)"
  _ -> decFail "expected a list value (Spec §35.6)"

asStrList :: EvalCtx -> Value -> Dec [Text]
asStrList ctx v = asList ctx v >>= mapM (asStr ctx)

asOption :: EvalCtx -> Value -> Dec (Maybe Value)
asOption ctx v = do
  (c, args) <- asCtor ctx v
  case (c, args) of
    ("None", _) -> Right Nothing
    ("Some", (x : _)) -> Right (Just x)
    _ -> decFail "expected an Option value (Spec §35.6)"

-- ── Schema decoders ──────────────────────────────────────────────────

decBuildConfig :: EvalCtx -> Value -> Dec BuildConfig
decBuildConfig ctx v = do
  (c, args) <- asCtor ctx v
  case (c, args) of
    ("MkBuildConfig", [nm, ver, roots, axes, deps, hbs, tgts]) ->
      BuildConfig
        <$> asStr ctx nm
        <*> decVersion ctx ver
        <*> (asList ctx roots >>= mapM (decSourceRoot ctx))
        <*> (asList ctx axes >>= mapM (decAxis ctx))
        <*> (asList ctx deps >>= mapM (decDependency ctx))
        <*> (asList ctx hbs >>= mapM (decHostBinding ctx))
        <*> (asList ctx tgts >>= mapM (decTarget ctx))
    _ -> decFail "the manifest's 'buildConfig' is not a 'package(...)' value (Spec §36.3)"

decVersion :: EvalCtx -> Value -> Dec PackageVersion
decVersion ctx v = do
  (c, args) <- asCtor ctx v
  case (c, args) of
    ("MkPackageVersion", (s : _)) -> PackageVersion <$> asStr ctx s
    _ -> decFail "expected a 'semver' value (Spec §29.8)"

decSourceRoot :: EvalCtx -> Value -> Dec SourceRoot
decSourceRoot ctx v = do
  (c, args) <- asCtor ctx v
  case (c, args) of
    ("MkSourceRoot", (p : _)) -> SourceRoot <$> asStr ctx p
    _ -> decFail "expected a 'sourceRoot' value (Spec §29.8)"

decAxis :: EvalCtx -> Value -> Dec FragmentAxis
decAxis ctx v = do
  (c, args) <- asCtor ctx v
  case (c, args) of
    ("MkFragmentAxis", [nm, ts]) ->
      FragmentAxis <$> asStr ctx nm <*> (asList ctx ts >>= mapM (decTag ctx))
    _ -> decFail "expected an 'axis' value (Spec §29.8)"

decTag :: EvalCtx -> Value -> Dec Text
decTag ctx v = do
  (c, args) <- asCtor ctx v
  case (c, args) of
    ("MkFragmentTag", (s : _)) -> asStr ctx s
    _ -> decFail "expected a 'tag' value (Spec §29.8)"

decFragments :: EvalCtx -> Value -> Dec [Text]
decFragments ctx v = do
  (c, args) <- asCtor ctx v
  case (c, args) of
    ("MkFragmentSelection", (ts : _)) -> asStrList ctx ts
    _ -> decFail "expected a 'tags' selection value (Spec §29.8)"

decDependency :: EvalCtx -> Value -> Dec Dependency
decDependency ctx v = do
  (c, args) <- asCtor ctx v
  case (c, args) of
    ("RegistryDep", [nm, ver]) -> RegistryDep <$> asStr ctx nm <*> asStr ctx ver
    ("GitDep", [nm, url, rev]) -> GitDep <$> asStr ctx nm <*> asStr ctx url <*> asStr ctx rev
    ("PathDep", [nm, p]) -> PathDep <$> asStr ctx nm <*> asStr ctx p
    _ -> decFail "expected a dependency value ('registry'/'git'/'pathDependency') (Spec §36.23)"

decModuleSelector :: EvalCtx -> Value -> Dec ModuleSelector
decModuleSelector ctx v = do
  (c, args) <- asCtor ctx v
  case (c, args) of
    ("SelModule", (s : _)) -> SelModule <$> asStr ctx s
    ("SelModulesUnder", (s : _)) -> SelModulesUnder <$> asStr ctx s
    _ -> decFail "expected a module selector ('module'/'modulesUnder') (Spec §29.8)"

decBackend :: EvalCtx -> Value -> Dec BackendProfile
decBackend ctx v = do
  (c, args) <- asCtor ctx v
  case (c, args) of
    ("NativeBackend", [tc, tt]) -> NativeBackend <$> asStr ctx tc <*> asStr ctx tt
    ("JvmBackend", _) -> Right JvmBackend
    ("DotNetBackend", _) -> Right DotNetBackend
    _ -> decFail "expected a backend profile ('native'/'jvm'/'dotnet') (Spec §29.8)"

decNativeSource :: EvalCtx -> Value -> Dec NativeBindingSource
decNativeSource ctx v = do
  (c, args) <- asCtor ctx v
  case (c, args) of
    ("PkgConfigSource", [pkg, mv]) -> do
      pkg' <- asStr ctx pkg
      mv' <- asOption ctx mv
      mvTxt <- traverse (asStr ctx) mv'
      Right (PkgConfigSource pkg' mvTxt)
    ("HeadersSource", (ps : _)) -> HeadersSource <$> asStrList ctx ps
    ("SymbolListSource", (ss : _)) -> SymbolListSource <$> asStrList ctx ss
    ("ShimSource", (p : _)) -> ShimSource <$> asStr ctx p
    ("PrebuiltNativeSource", (p : _)) -> PrebuiltNativeSource <$> asStr ctx p
    _ -> decFail "expected a native binding source (Spec §36.28)"

decAbi :: EvalCtx -> Value -> Dec NativeAbi
decAbi ctx v = do
  (c, _) <- asCtor ctx v
  case c of
    "CAbi" -> Right CAbi
    _ -> decFail "expected a native ABI ('cAbi') (Spec §36.28)"

decLink :: EvalCtx -> Value -> Dec NativeLinkSpec
decLink ctx v = do
  (c, args) <- asCtor ctx v
  case (c, args) of
    ("DynamicLink", (ls : _)) -> DynamicLink <$> asStrList ctx ls
    ("StaticLink", (ls : _)) -> StaticLink <$> asStrList ctx ls
    ("NoLink", _) -> Right NoLink
    _ -> decFail "expected a link spec ('dynamicLink'/'staticLink'/'noLink') (Spec §36.28)"

decLoad :: EvalCtx -> Value -> Dec NativeLoadSpec
decLoad ctx v = do
  (c, _) <- asCtor ctx v
  case c of
    "SystemLoader" -> Right SystemLoader
    "BundledLoader" -> Right BundledLoader
    "RuntimeLoad" -> Right RuntimeLoad
    "ProvidedByHost" -> Right ProvidedByHost
    _ -> decFail "expected a load spec (Spec §36.28)"

decHostBinding :: EvalCtx -> Value -> Dec HostBinding
decHostBinding ctx v = do
  (c, args) <- asCtor ctx v
  case (c, args) of
    ("MkNativeBinding", [nm, provides, source, abi, hdrs, link, load]) ->
      NativeBinding
        <$> asStr ctx nm
        <*> (asList ctx provides >>= mapM (decModuleSelector ctx))
        <*> decNativeSource ctx source
        <*> decAbi ctx abi
        <*> (asList ctx hdrs >>= mapM (decNativeSource ctx))
        <*> decLink ctx link
        <*> decLoad ctx load
    _ -> decFail "expected a host binding ('nativeBinding') (Spec §36.28)"

decTarget :: EvalCtx -> Value -> Dec Target
decTarget ctx v = do
  (c, args) <- asCtor ctx v
  case (c, args) of
    ("ExecutableTarget", [nm, be, fr, mn, mods, deps, hbs]) ->
      ExecutableTarget
        <$> asStr ctx nm
        <*> decBackend ctx be
        <*> decFragments ctx fr
        <*> decModuleSelector ctx mn
        <*> decModuleSelector ctx mods
        <*> asStrList ctx deps
        <*> asStrList ctx hbs
    ("LibraryTarget", [nm, be, fr, mods, deps]) ->
      LibraryTarget
        <$> asStr ctx nm
        <*> decBackend ctx be
        <*> decFragments ctx fr
        <*> decModuleSelector ctx mods
        <*> asStrList ctx deps
    _ -> decFail "expected a target ('executable'/'library') (Spec §29.8)"
