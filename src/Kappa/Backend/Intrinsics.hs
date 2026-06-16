-- | Native-backend host-binding intrinsics (§34.5.3): the foreign
-- operations the @zig@ profile (§27.1) supplies to satisfy a source
-- program's @expect term@ declarations (§9.4).  This module is the single
-- source of truth shared by:
--
--   * the elaborator, which (only when the native FFI capability is
--     selected) seeds these names + expected types into
--     'Kappa.Check.csBackendIntrinsics' so a matching @expect@ is
--     satisfied by a backend intrinsic after a definitional-equality
--     check; and
--   * the code generator, which lowers a reference to a satisfied
--     intrinsic to the corresponding runtime FFI primitive
--     (@runtime/kappart_ffi.c@).
--
-- The expected types are spelled with @std.ffi@ types (§26.2): foreign
-- handles are bare @std.ffi.OpaqueHandle@ (a raw host-binding surface,
-- §26.1.1/§26.2), whose backend-specific runtime representation is the
-- runtime's @K_FGN@ wrapper.  See docs/NATIVE_FFI_DESIGN.md.
module Kappa.Backend.Intrinsics
  ( NativeIntrinsic (..)
  , nativeIntrinsics
  , intrinsicTypes
  , intrinsicPrim
  ) where

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Kappa.Core
import Kappa.Source (ModuleName (..))

-- | One native host-binding intrinsic: its expected Kappa type (Core) and
-- the runtime FFI primitive that realizes it under @native.direct@.
data NativeIntrinsic = NativeIntrinsic
  { niType :: !Term -- ^ expected signature, checked up to defeq (§9.4, §34.5)
  , niPrim :: !Text -- ^ runtime FFI primitive name (Kappa.Backend.Ffi / kappart_ffi.c)
  }

-- ── type vocabulary (canonical forms; aliases like Int/UIO δ-unfold to
-- these under conversion, so an `expect` may spell either) ───────────────

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

-- ── the intrinsic table ──────────────────────────────────────────────

-- | Every native host-binding intrinsic, keyed by the Kappa spelling a
-- source program uses in its @expect term@ declaration.
nativeIntrinsics :: Map Text NativeIntrinsic
nativeIntrinsics =
  Map.fromList
    [ -- POSIX TCP sockets
      i "tcpListen" (tInteger ~> uio ffiOpaque) "__tcpListen"
    , i "tcpAccept" (ffiOpaque ~> uio ffiOpaque) "__tcpAccept"
    , i "connRead" (ffiOpaque ~> uio tString) "__connRead"
    , i "connWrite" (ffiOpaque ~> tString ~> uio tUnit) "__connWrite"
    , i "connClose" (ffiOpaque ~> uio tUnit) "__connClose"
    , i "listenClose" (ffiOpaque ~> uio tUnit) "__listenClose"
      -- sqlite3
    , i "sqliteOpen" (tString ~> uio ffiOpaque) "__sqliteOpen"
    , i "sqliteExec" (ffiOpaque ~> tString ~> uio tUnit) "__sqliteExec"
    , i "sqliteQueryInt" (ffiOpaque ~> tString ~> uio tInteger) "__sqliteQueryInt"
    , i "sqliteQueryText" (ffiOpaque ~> tString ~> uio tString) "__sqliteQueryText"
    , i "sqliteClose" (ffiOpaque ~> uio tUnit) "__sqliteClose"
    ]
  where
    i name ty prim = (name, NativeIntrinsic ty prim)

-- | The intrinsic name → expected-type map seeded into the elaborator
-- ('Kappa.Check.csBackendIntrinsics') when the native FFI capability is on.
intrinsicTypes :: Map Text Term
intrinsicTypes = Map.map niType nativeIntrinsics

-- | The runtime FFI primitive realizing an intrinsic, if any.
intrinsicPrim :: Text -> Maybe Text
intrinsicPrim name = niPrim <$> Map.lookup name nativeIntrinsics
