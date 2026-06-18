-- | The native host-binding catalog (§8.3.5, §27.1.1, §34.5.3): the
-- @zig@ profile's curated @host.native.*@ module surfaces. Each catalog
-- module is a host-binding module whose exported declarations are
-- realized by backend intrinsics (§34.5.3) — the runtime FFI primitives
-- of @runtime/kappart_ffi.c@. A @host.native.*@ module is supplied from
-- this catalog (an implementation-documented ABI description, §8.3.5)
-- and is made importable by a program ONLY when the build manifest
-- declares a @nativeBinding@ that provides it (§36.28); the manifest's
-- @link@/@load@ then drives the C toolchain. This replaces the former
-- bare-name @--ffi-full@ intrinsic table: native bindings are now
-- selected through the package/build/native mechanism, never a global
-- hardcoded list.
--
-- These host bindings are runtime-only (§34.5.1): they are registered as
-- abstract globals (no value), so the elaboration-time evaluator never
-- demands them.
module Kappa.Backend.NativeCatalog
  ( CatalogMember (..)
  , CatalogModule (..)
  , nativeCatalog
  , catalogModule
  ) where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Kappa.Core
import Kappa.Source (ModuleName (..))

-- | One exported member of a @host.native.*@ module: its Kappa surface
-- spelling, its expected Kappa type (Core; checked at use sites and
-- evaluated to the global's type), and the runtime FFI primitive that
-- realizes it under @native.direct@.
data CatalogMember = CatalogMember
  { cmName :: !Text
  , cmType :: !Term
  , cmPrim :: !Text
  }

-- | One curated @host.native.*@ module surface.
data CatalogModule = CatalogModule
  { cmoName :: !ModuleName
  , cmoMembers :: ![CatalogMember]
  }

-- ── type vocabulary (canonical Core; δ-unfolds match an `expect`'s
-- defeq, and these are evaluated to the global's 'Value' type) ─────────

gp :: Text -> Term
gp = CGlob . GName (ModuleName ["std", "prelude"])

ffiOpaque :: Term
ffiOpaque = CGlob (GName (ModuleName ["std", "ffi"]) "OpaqueHandle")

infixr 5 ~>
(~>) :: Term -> Term -> Term
a ~> b = CPi Expl QW "_" a b

-- | @IO Void a@ — the normal form of the prelude's @UIO a@ alias.
uio :: Term -> Term
uio a = CApp Expl (CApp Expl (gp "IO") (gp "Void")) a

tInteger, tString, tUnit :: Term
tInteger = gp "Integer"
tString = gp "String"
tUnit = gp "Unit"

-- ── the catalog ──────────────────────────────────────────────────────

hostNative :: [Text] -> ModuleName
hostNative segs = ModuleName (["host", "native"] ++ segs)

-- | The @zig@-profile native host-binding catalog, keyed by module name.
nativeCatalog :: Map ModuleName CatalogModule
nativeCatalog =
  Map.fromList
    [ entry
        (hostNative ["sqlite3"])
        [ m "sqliteOpen" (tString ~> uio ffiOpaque) "__sqliteOpen"
        , m "sqliteExec" (ffiOpaque ~> tString ~> uio tUnit) "__sqliteExec"
        , m "sqliteQueryInt" (ffiOpaque ~> tString ~> uio tInteger) "__sqliteQueryInt"
        , m "sqliteQueryText" (ffiOpaque ~> tString ~> uio tString) "__sqliteQueryText"
        , m "sqliteClose" (ffiOpaque ~> uio tUnit) "__sqliteClose"
        ]
    , entry
        (hostNative ["posix", "net"])
        [ m "tcpListen" (tInteger ~> uio ffiOpaque) "__tcpListen"
        , m "tcpAccept" (ffiOpaque ~> uio ffiOpaque) "__tcpAccept"
        , m "connRead" (ffiOpaque ~> uio tString) "__connRead"
        , m "connWrite" (ffiOpaque ~> tString ~> uio tUnit) "__connWrite"
        , m "connClose" (ffiOpaque ~> uio tUnit) "__connClose"
        , m "listenClose" (ffiOpaque ~> uio tUnit) "__listenClose"
        ]
    ]
  where
    m = CatalogMember
    entry mn ms = (mn, CatalogModule mn ms)

-- | Look up a catalog module by name.
catalogModule :: ModuleName -> Maybe CatalogModule
catalogModule mn = Map.lookup mn nativeCatalog
