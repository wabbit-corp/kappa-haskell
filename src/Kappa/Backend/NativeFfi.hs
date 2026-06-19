-- | The native foreign-ABI lowering vocabulary (§26.1.1/§26.1.4, §27.1.1).
--
-- A native host binding is described ENTIRELY by the build manifest's
-- @nativeBinding@ (a symbol list with ABI signatures, plus realization
-- inputs and link/load specs — see "Kappa.Build.Types"). The build plan
-- resolves each declared symbol into a 'ResolvedNativeSymbol'; codegen then
-- emits, per symbol, a DIRECT C prototype + a statically-typed marshalling
-- wrapper + a direct typed call site (a 'knative' action). There is NO
-- hardcoded native catalog, NO runtime primitive table, and NO string- or
-- KValue-dispatched primitive firing in the generated native output.
--
-- This module is the single place that maps the conservative ABI type
-- vocabulary ('CType', §26.1.1) to (a) its C ABI spelling, (b) its Kappa
-- surface type, and (c) the unbox/box marshalling around a direct call.
module Kappa.Backend.NativeFfi
  ( ResolvedNativeSymbol (..)
  , nativeMemberType
  , wrapperCName
  , externPrototype
  , wrapperDefinition
  , cAbiType
  ) where

import Data.Char (isAlphaNum)
import Data.Text (Text)
import qualified Data.Text as T
import Kappa.Build.Types (CType (..))
import Kappa.Core (GName (..), Icit (..), Q (..), Term (..))
import Kappa.Source (ModuleName (..))

-- | A native symbol resolved from the manifest, ready for direct-call
-- codegen (§27.1.1/§36.28): which @host.native.*@ member it backs, the C
-- symbol the generated wrapper calls directly, and its ABI signature.
data ResolvedNativeSymbol = ResolvedNativeSymbol
  { rnsModule :: !ModuleName
  , rnsMember :: !Text
  -- ^ the Kappa member name within @rnsModule@
  , rnsCSymbol :: !Text
  -- ^ the C symbol the wrapper calls directly (no name dispatch)
  , rnsParams :: ![CType]
  , rnsResult :: !CType
  }
  deriving stock (Eq, Show)

-- ── ABI type vocabulary (§26.1.1/§26.1.4) ─────────────────────────────

-- | The C ABI spelling of a 'CType', used in the extern prototype and the
-- wrapper's direct call. @CtUnit@ is only valid as a result (a @void@ C
-- function).
cAbiType :: CType -> Text
cAbiType = \case
  CtUnit -> "void"
  CtInt -> "int"
  CtInt64 -> "int64_t"
  CtBool -> "int"
  CtDouble -> "double"
  CtString -> "const char *"
  CtHandle -> "void *"
  CtRawPtr -> "void *"
  CtI8 -> "int8_t"
  CtI16 -> "int16_t"
  CtI32 -> "int32_t"
  CtI64 -> "int64_t"
  CtU8 -> "uint8_t"
  CtU16 -> "uint16_t"
  CtU32 -> "uint32_t"
  CtU64 -> "uint64_t"
  CtIsize -> "intptr_t"
  CtUsize -> "size_t"
  CtF32 -> "float"

-- | The Kappa surface type a 'CType' is presented as (conservative typing,
-- §26.1.4). Integer-class C scalars surface as @Integer@; handles/pointers
-- as the abstract @std.ffi@ types (the runtime boxes them as opaque K_FGN).
ctypeKappaTerm :: CType -> Term
ctypeKappaTerm = \case
  CtUnit -> gp "Unit"
  CtBool -> gp "Bool"
  CtDouble -> gp "Double"
  CtString -> gp "String"
  CtHandle -> ffi "OpaqueHandle"
  CtRawPtr -> ffi "RawPtr"
  CtF32 -> gp "Double"
  -- the integer class (exact-width + word-width) surfaces as Integer (§26.1.4
  -- conservative typing; the ABI width is carried by 'cAbiType'/marshalling).
  t | isIntClass t -> gp "Integer"
  _ -> gp "Integer"
  where
    isIntClass t = t `elem` [CtInt, CtInt64, CtI8, CtI16, CtI32, CtI64, CtU8, CtU16, CtU32, CtU64, CtIsize, CtUsize]

-- | The Kappa type of a native member: @p1 -> … -> pn -> UIO result@.
-- Native bindings are effectful, so the result is in @UIO@ (= @IO Void@),
-- the conservative §26.1.4 framing (no host effect escapes into a pure
-- value). The normal form matches "Kappa.Backend.NativeCatalog"'s former
-- hand-written surface but is now DERIVED from the manifest's ABI signature.
nativeMemberType :: [CType] -> CType -> Term
nativeMemberType ps r =
  foldr (\p acc -> ctypeKappaTerm p ~> acc) (uio (ctypeKappaTerm r)) ps

-- ── direct-call codegen (§27.1.1) ─────────────────────────────────────

-- | The C name of the generated marshalling wrapper for a symbol. Keyed by
-- the member's module+name so distinct members are distinct wrappers even
-- if they share a C symbol.
wrapperCName :: ResolvedNativeSymbol -> Text
wrapperCName rns =
  "kw_" <> mangle (renderMod (rnsModule rns) <> "." <> rnsMember rns)

-- | @extern <ret> <sym>(<params>);@ — the direct prototype of the C symbol
-- the wrapper calls. Emitted once per distinct C symbol.
externPrototype :: ResolvedNativeSymbol -> Text
externPrototype rns =
  "extern " <> cAbiType (rnsResult rns) <> " " <> rnsCSymbol rns
    <> "(" <> paramList (rnsParams rns) <> ");"
  where
    paramList [] = "void"
    paramList ps = T.intercalate ", " (map cAbiType ps)

-- | The generated marshalling wrapper: unbox each @KValue*@ arg to its C
-- ABI type, call the C symbol DIRECTLY, box the result. Signature matches
-- 'KNativeFn' (@KValue *(*)(KValue **)@), so 'krun_io' fires it without any
-- name lookup.
wrapperDefinition :: ResolvedNativeSymbol -> Text
wrapperDefinition rns =
  T.unlines
    [ "static KValue *" <> wrapperCName rns <> "(KValue **a) {"
    , "  " <> body
    , "}"
    ]
  where
    args = T.intercalate ", " [unbox p ("a[" <> T.pack (show i) <> "]") | (i, p) <- zip [0 :: Int ..] (rnsParams rns)]
    call = rnsCSymbol rns <> "(" <> args <> ")"
    body = case rnsResult rns of
      CtUnit -> call <> "; return kunit();"
      r -> "return " <> box r call <> ";"

-- | Unbox a @KValue*@ expression to a C value of the parameter's ABI type.
--
-- NOTE (§26.1.1 String ABI convention): @CtString@ marshals a Kappa @String@
-- to/from a NUL-terminated @const char *@ (@kas_str@/@kstr0@). A Kappa String
-- may contain embedded U+0000; such a string is truncated at the first NUL
-- across this boundary, and a C result is read up to its NUL terminator. This
-- is the documented conservative C-FFI string convention (no length channel);
-- a binding needing byte-exact NUL-bearing data should use @CtRawPtr@ + an
-- explicit length parameter.
unbox :: CType -> Text -> Text
unbox ty e = case ty of
  CtUnit -> "(void)" <> e -- a unit param carries no C argument; never emitted in practice
  CtInt64 -> "kas_int(" <> e <> ")"
  CtBool -> "kas_bool(" <> e <> ")"
  CtDouble -> "kas_dbl(" <> e <> ")"
  CtString -> "kas_str(" <> e <> ")"
  CtHandle -> "kas_fgn(" <> e <> ")"
  CtRawPtr -> "kas_fgn(" <> e <> ")"
  CtF32 -> "(float)kas_dbl(" <> e <> ")"
  -- integer class: unbox to int64 then narrow to the declared C width.
  _ -> "(" <> cAbiType ty <> ")kas_int(" <> e <> ")"

-- | Box a C call expression of the result's ABI type back to a @KValue*@.
box :: CType -> Text -> Text
box ty call = case ty of
  CtUnit -> "(" <> call <> ", kunit())"
  CtInt64 -> "kint(" <> call <> ")"
  CtBool -> "kbool(" <> call <> ")"
  CtDouble -> "kdbl(" <> call <> ")"
  CtString -> "kstr0(" <> call <> ")"
  CtHandle -> "kfgn((void *)(" <> call <> "), \"native\")"
  CtRawPtr -> "kfgn((void *)(" <> call <> "), \"native\")"
  CtF32 -> "kdbl((double)(" <> call <> "))"
  CtU64 -> "kint((int64_t)(uint64_t)(" <> call <> "))" -- values > INT64_MAX wrap (Integer surface; documented)
  -- other integer-class results: the C call already returns the exact width;
  -- widen to int64 (sign/zero extension follows from the C return type).
  _ -> "kint((int64_t)(" <> call <> "))"

-- ── small Core helpers (canonical, δ-unfold to an `expect`'s defeq) ────

gp :: Text -> Term
gp = CGlob . GName (ModuleName ["std", "prelude"])

ffi :: Text -> Term
ffi = CGlob . GName (ModuleName ["std", "ffi"])

infixr 5 ~>
(~>) :: Term -> Term -> Term
a ~> b = CPi Expl QW "_" a b

-- | @IO Void a@ — the normal form of the prelude's @UIO a@ alias.
uio :: Term -> Term
uio a = CApp Expl (CApp Expl (gp "IO") (gp "Void")) a

renderMod :: ModuleName -> Text
renderMod (ModuleName segs) = T.intercalate "." segs

-- | Mangle an arbitrary dotted name into a C identifier fragment.
mangle :: Text -> Text
mangle = T.concatMap esc
  where
    esc c
      | isAlphaNum c = T.singleton c
      | otherwise = "_"
