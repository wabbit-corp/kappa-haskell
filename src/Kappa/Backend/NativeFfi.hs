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
  , rnsCollectCtors
  , scalarOnly
  ) where

import Data.Char (isAlphaNum, isAsciiLower, isAsciiUpper, isDigit, ord)
import Data.Text (Text)
import qualified Data.Text as T
import Numeric (showHex)
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
  , rnsShimProvided :: !Bool
  -- ^ True iff this symbol is DEFINED by one of the binding's shim translation
  -- units (the binding has a @shim@ input). Only shim-provided symbols get a
  -- force-included conservative prototype for shim-ABI checking (§27.1.1): a
  -- real LIBRARY symbol is declared by its own header, so asserting our
  -- conservative @void *@ prototype for it would falsely conflict with the real
  -- pointer type when that header is in scope.
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
  CtF64 -> "double"

-- | The Kappa surface type a 'CType' is presented as (conservative typing,
-- §26.1.4). Integer-class C scalars surface as @Integer@; handles/pointers
-- as the abstract @std.ffi@ types (the runtime boxes them as opaque K_FGN).
ctypeKappaTerm :: CType -> Term
ctypeKappaTerm ty = case ty of
  CtUnit -> gp "Unit"
  CtBool -> gp "Bool"
  CtDouble -> gp "Double" -- = std.ffi.F64 (§26.2: F64 MAY be Double)
  CtString -> gp "String"
  CtInt -> gp "Integer" -- C `int` (not exact-width); ergonomic Integer surface
  -- §26.1.1:27307-27309: a RawPtr we cannot prove non-null MUST surface as
  -- `Option RawPtr`.
  CtRawPtr -> CApp Expl (gp "Option") (ffi "RawPtr")
  -- §27.1.1:27316: a raw host.native binding MAY expose bare OpaqueHandle for
  -- a resource whose release is supplied out of band (the binding's close op).
  CtHandle -> ffi "OpaqueHandle"
  -- §26.1.2:26114: exact-width / pointer-width / float scalars MUST surface as
  -- the corresponding std.ffi nominal types.
  _ -> case ffiScalar ty of
    Just (tyName, _) -> ffi tyName
    Nothing -> gp "Integer"

-- | The std.ffi nominal scalar a CType surfaces as (type name, ctor gKey), for
-- the exact-width / pointer-width / float classes (§26.1.2). 'Nothing' for the
-- ergonomic/builtin-typed CTypes (Int/Bool/Double/String/Handle/RawPtr/Unit).
ffiScalar :: CType -> Maybe (Text, Text)
ffiScalar = \case
  CtInt64 -> Just ("I64", "std.ffi.MkI64") -- int64_t is exact-width
  CtI8 -> Just ("I8", "std.ffi.MkI8")
  CtI16 -> Just ("I16", "std.ffi.MkI16")
  CtI32 -> Just ("I32", "std.ffi.MkI32")
  CtI64 -> Just ("I64", "std.ffi.MkI64")
  CtU8 -> Just ("U8", "std.ffi.MkU8")
  CtU16 -> Just ("U16", "std.ffi.MkU16")
  CtU32 -> Just ("U32", "std.ffi.MkU32")
  CtU64 -> Just ("U64", "std.ffi.MkU64")
  CtIsize -> Just ("Isize", "std.ffi.MkIsize")
  CtUsize -> Just ("Usize", "std.ffi.MkUsize")
  CtF32 -> Just ("F32", "std.ffi.MkF32")
  CtF64 -> Just ("F64", "std.ffi.MkF64")
  _ -> Nothing

-- | True iff every param/result is a non-pointer scalar (no RawPtr / Handle /
-- String) — only such a symbol's CONSERVATIVE C prototype can be soundly
-- checked against the real header (a pointer maps to @void *@, intentionally
-- not the real pointer type, so its prototype would falsely conflict).
scalarOnly :: ResolvedNativeSymbol -> Bool
scalarOnly rns = all isScalar (rnsResult rns : rnsParams rns)
  where
    isScalar t = t `notElem` [CtRawPtr, CtHandle, CtString]

-- | The std.ffi/std.prelude constructor gKeys a CType's marshalling
-- constructs (so codegen collects their KT_ tag ids). @Some@/@None@ are
-- builtin (fixed KCT_ ids) and are not collected.
rnsCollectCtors :: ResolvedNativeSymbol -> [Text]
rnsCollectCtors rns =
  concatMap ctorsOf (rnsResult rns : rnsParams rns)
  where
    ctorsOf t = case t of
      CtRawPtr -> ["std.ffi.MkRawPtr"]
      _ -> maybe [] (\(_, g) -> [g]) (ffiScalar t)

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
    ( ["static KValue *" <> wrapperCName rns <> "(KValue **a) {"]
        ++ map ("  " <>) bodyLines
        ++ ["}"]
    )
  where
    args = T.intercalate ", " [unbox p ("a[" <> T.pack (show i) <> "]") | (i, p) <- zip [0 :: Int ..] (rnsParams rns)]
    call = rnsCSymbol rns <> "(" <> args <> ")"
    bodyLines = case rnsResult rns of
      CtUnit -> [call <> "; return kunit();"]
      r ->
        -- capture the C result in a typed temp, then box it (the box for a
        -- nominal/Option result references it more than once).
        [ cAbiType r <> " r = " <> call <> ";"
        , "return " <> box r "r" <> ";"
        ]

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
  CtBool -> "kas_bool(" <> e <> ")"
  CtDouble -> "kas_dbl(" <> e <> ")"
  CtString -> "kas_str(" <> e <> ")"
  CtHandle -> "kas_fgn(" <> e <> ")"
  CtInt -> "(int)kas_int(" <> e <> ")"
  -- §26.1.1: Option RawPtr — None ↦ NULL, Some (MkRawPtr a) ↦ (void*)a.
  CtRawPtr ->
    "(kctor_tagid(" <> e <> ") == KCT_NONE ? (void *)0 : (void *)(intptr_t)kas_int("
      <> "kctor_arg(kctor_arg(" <> e <> ", 0), 0)))"
  CtF32 -> "(float)kas_dbl(kctor_arg(" <> e <> ", 0))"
  CtF64 -> "kas_dbl(kctor_arg(" <> e <> ", 0))"
  -- §26.1.1: the full unsigned 64-bit / pointer-width range (incl. ≥ 2^63).
  CtU64 -> "(uint64_t)kas_u64(kctor_arg(" <> e <> ", 0))"
  CtUsize -> "(size_t)kas_u64(kctor_arg(" <> e <> ", 0))"
  -- nominal exact-width scalar (MkXxx rep): unbox the rep Integer, narrow to
  -- the declared C width.
  _ -> case ffiScalar ty of
    Just _ -> "(" <> cAbiType ty <> ")kas_int(kctor_arg(" <> e <> ", 0))"
    Nothing -> "(" <> cAbiType ty <> ")kas_int(" <> e <> ")"

-- | Box a C value (the temp @r@) of the result's ABI type back to a @KValue*@.
box :: CType -> Text -> Text
box ty r = case ty of
  CtUnit -> "kunit()"
  CtBool -> "kbool(" <> r <> ")"
  CtDouble -> "kdbl(" <> r <> ")"
  CtString -> "kstr0(" <> r <> ")"
  CtHandle -> "kfgn((void *)(" <> r <> "), \"native\")"
  CtInt -> "kint((int64_t)(" <> r <> "))"
  -- §26.1.1: Option RawPtr — NULL ↦ None, else Some (MkRawPtr addr).
  CtRawPtr ->
    "((" <> r <> ") == (void *)0 ? kctor0(KCT_NONE, \"std.prelude.None\")"
      <> " : kctor(KCT_SOME, \"std.prelude.Some\", 1, (KValue *[]){"
      <> ctorExpr "std.ffi.MkRawPtr" "kint((int64_t)(intptr_t)(" "))" r
      <> "}))"
  CtF32 -> ctorExpr "std.ffi.MkF32" "kdbl((double)(" "))" r
  CtF64 -> ctorExpr "std.ffi.MkF64" "kdbl(" ")" r
  -- §26.1.1: unsigned 64-bit / pointer-width box the FULL range (bignum ≥ 2^63).
  CtU64 -> ctorExpr "std.ffi.MkU64" "ku64((uint64_t)(" "))" r
  CtUsize -> ctorExpr "std.ffi.MkUsize" "ku64((uint64_t)(" "))" r
  -- nominal exact-width scalar: wrap the (widened) rep in its MkXxx ctor.
  _ -> case ffiScalar ty of
    Just (_, g) -> ctorExpr g "kint((int64_t)(" "))" r
    Nothing -> "kint((int64_t)(" <> r <> "))"

-- | @kctor(KT_<g>, "<g>", 1, (KValue*[]){<pre><r><post>})@ — construct a
-- single-field std.ffi wrapper ctor around the (converted) C value.
ctorExpr :: Text -> Text -> Text -> Text -> Text
ctorExpr gkey pre post r =
  "kctor(" <> ktag gkey <> ", " <> cStrLit gkey <> ", 1, (KValue *[]){"
    <> pre <> r <> post <> "})"

-- | The C tag-id macro name for a constructor gKey — matches
-- "Kappa.Backend.C"'s @KT_<mangle gKey>@ (the ctor is registered for emission
-- via 'rnsCollectCtors').
ktag :: Text -> Text
ktag g = "KT_" <> cMangle g

-- | A C string literal (the ctor gKey, used as the runtime ctor name).
cStrLit :: Text -> Text
cStrLit s = "\"" <> s <> "\""

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

-- | Mangle an arbitrary dotted name into a C identifier fragment (for the
-- wrapper name; need only be injective within the host-symbol set).
mangle :: Text -> Text
mangle = T.concatMap esc
  where
    esc c
      | isAlphaNum c = T.singleton c
      | otherwise = "_"

-- | The EXACT mangle "Kappa.Backend.C" uses for @KT_<name>@ tag-id macros
-- (alphanumerics kept; every other char becomes @_<hex>_@). Must match so a
-- ctor constructed here and matched in compiled Kappa share the same KT_ id.
cMangle :: Text -> Text
cMangle = T.concatMap esc
  where
    esc c
      | isAsciiLower c || isAsciiUpper c || isDigit c = T.singleton c
      | otherwise = "_" <> T.pack (showHex (ord c) "") <> "_"
