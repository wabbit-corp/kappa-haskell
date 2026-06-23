-- | The single source of truth for every name the compiler wires in by
-- hand: prelude globals/constructors, standard-library module paths, and
-- the small hardcoded lists the checker and pipeline consult (literal
-- defaulting domains, implicitly-visible constructors, config-safe names).
--
-- Nothing outside this module should spell a prelude/stdlib name as a bare
-- string literal. Centralizing them here turns ~250 scattered literals into
-- one auditable inventory and lets 'wiredInPreludeNames' drive a load-time
-- check that the prelude actually defines everything the compiler assumes
-- (see "Kappa.Pipeline"). A drift that used to miscompile silently now
-- surfaces as a single diagnostic.
--
-- Naming convention:
--
--   * @prel*@   — a 'GName' in the @std.prelude@ module (type, constructor,
--                 trait, or wired-in helper/intrinsic).
--   * @mod*@    — a standard-library 'ModuleName'.
--   * @trait*@  — a trait spelling consulted by name (e.g. literal witnesses).
--   * @ident*@  — a magic surface identifier matched by 'nameText'.
module Kappa.Builtins
  ( -- * Prelude module + name builder
    preludeModule
  , gPrel
  , primModule

    -- * Prelude types
  , prelUnit
  , prelBool
  , prelString
  , prelNat
  , prelInt
  , prelInteger
  , prelDouble
  , prelByte
  , prelGrapheme
  , prelUnicodeScalar
  , prelList
  , prelArray
  , prelOption
  , prelThunk
  , prelNeed
  , prelZipper
  , prelRef
  , prelRegion
  , prelEff
  , prelEffRow
  , prelEffLabel
  , prelIO
  , prelSTM
  , prelElab
  , prelSyntax
  , prelLit
  , prelCode
  , prelInterp
  , prelInterpFmt
  , prelRecRow
  , prelLacksRec
  , prelQueryMode
  , prelQueryCore
  , prelQZeroOrMore
  , prelReusable

    -- * Prelude constructors
  , prelTrue
  , prelFalse
  , prelSome
  , prelNone
  , prelNil
  , prelCons
  , prelLT
  , prelEQ
  , prelGT
  , prelRefl
  , prelEqType
  , prelBoolV
  , prelOrdering

    -- * Effect-runtime constructors (Exit/Cause/Interrupt, §18)
  , prelSuccess
  , prelFailure
  , prelFail
  , prelInterrupt
  , prelDefect
  , prelMkDefectInfo
  , prelMkInterruptCause
  , prelTimedOut

    -- * Timeout/race result constructors (§18.1.6)
  , prelTOTimedOut
  , prelTOExit
  , prelROLeft
  , prelRORight

    -- * Prelude traits
  , prelShow
  , prelOrd
  , prelMonad
  , prelReleasable
  , prelFromComprehensionRaw
  , prelFromComprehensionPlan
  , prelIsTraitWitness

    -- * Prelude functions/helpers consulted by name
  , prelNot
  , prelCompare
  , prelReadRef
  , prelCatchIO
  , prelFinallyIO
  , prelStringAppend

    -- * Wired-in intrinsics (compiler-synthesized prelude globals)
  , prelRunIO
  , prelThis
  , prelCaptures
  , prelSizedOf
  , prelEffPure
  , prelEffOp
  , prelEffBind
  , prelHandleEff
  , prelEffRowNil
  , prelEffRowCons
  , prelOpenRec
  , prelClosedRow
  , prelRowExtend
  , prelRowEvidence
  , prelSetFromList
  , prelArrayFromList
  , prelQueryFromList
  , prelCodeQuote
  , prelCodeEscape

    -- * Standard-library module paths
  , modPrelude
  , modDebug
  , modBytes
  , modUnicode
  , modHash
  , modDerivingShape
  , modFfi
  , modFfiC
  , modAtomic
  , modGradual
  , modBridge
  , modSupervisor
  , modConfig
  , modBuild
  , modTesting
  , modMain
  , modManifest

    -- * Reserved host module roots (§8.3.5)
  , reservedHostRoots

    -- * Trait spellings used for literal-witness resolution
  , traitFromInteger
  , traitFromFloat

    -- * Hardcoded name lists consulted by the checker/pipeline
  , kernelMonadCarriers
  , numericLitDomains
  , floatLitDomains
  , implicitPreludeCtorNames
  , configSafeTypeNames
  , configSafeCtorNames

    -- * Load-time validation registry
  , BuiltinKind (..)
  , WiredIn (..)
  , wiredInPreludeNames
  ) where

import Data.Text (Text)
import Kappa.Core (GName (..), primModule)
import Kappa.Source (ModuleName (..))

-- | The module owning every built-in type, constructor, trait and helper
-- the compiler references (§28.1). All @prel*@ names live here.
preludeModule :: ModuleName
preludeModule = ModuleName ["std", "prelude"]

-- | Build a prelude global name from its spelling. Prefer a named @prel*@
-- constant; this is for the few sites that resolve a spelling dynamically.
gPrel :: Text -> GName
gPrel = GName preludeModule

-- ── Prelude types ────────────────────────────────────────────────────

prelUnit, prelBool, prelString, prelNat, prelInt, prelInteger, prelDouble :: GName
prelUnit = gPrel "Unit"
prelBool = gPrel "Bool"
prelString = gPrel "String"
prelNat = gPrel "Nat"
prelInt = gPrel "Int"
prelInteger = gPrel "Integer"
prelDouble = gPrel "Double"

prelByte, prelGrapheme, prelUnicodeScalar :: GName
prelByte = gPrel "Byte"
prelGrapheme = gPrel "Grapheme"
prelUnicodeScalar = gPrel "UnicodeScalar"

prelList, prelArray, prelOption :: GName
prelList = gPrel "List"
prelArray = gPrel "Array"
prelOption = gPrel "Option"

prelThunk, prelNeed, prelZipper, prelRef, prelRegion :: GName
prelThunk = gPrel "Thunk"
prelNeed = gPrel "Need"
prelZipper = gPrel "Zipper"
prelRef = gPrel "Ref"
prelRegion = gPrel "Region"

prelEff, prelEffRow, prelEffLabel, prelIO, prelSTM, prelElab :: GName
prelEff = gPrel "Eff"
prelEffRow = gPrel "EffRow"
prelEffLabel = gPrel "EffLabel"
prelIO = gPrel "IO"
prelSTM = gPrel "STM"
prelElab = gPrel "Elab"

prelSyntax, prelLit, prelCode, prelInterp, prelInterpFmt :: GName
prelSyntax = gPrel "Syntax"
prelLit = gPrel "Lit"
prelCode = gPrel "Code"
prelInterp = gPrel "Interp"
prelInterpFmt = gPrel "InterpFmt"

prelRecRow, prelLacksRec :: GName
prelRecRow = gPrel "RecRow"
prelLacksRec = gPrel "LacksRec"

prelQueryMode, prelQueryCore, prelQZeroOrMore, prelReusable :: GName
prelQueryMode = gPrel "QueryMode"
prelQueryCore = gPrel "QueryCore"
prelQZeroOrMore = gPrel "QZeroOrMore"
prelReusable = gPrel "Reusable"

-- ── Prelude constructors ─────────────────────────────────────────────

prelTrue, prelFalse, prelSome, prelNone, prelNil, prelCons :: GName
prelTrue = gPrel "True"
prelFalse = gPrel "False"
prelSome = gPrel "Some"
prelNone = gPrel "None"
prelNil = gPrel "Nil"
prelCons = gPrel "::"

prelLT, prelEQ, prelGT :: GName
prelLT = gPrel "LT"
prelEQ = gPrel "EQ"
prelGT = gPrel "GT"

-- | The reflexivity proof constructor (§14) and the propositional
-- equality type head @=@ (§14).
prelRefl, prelEqType :: GName
prelRefl = gPrel "refl"
prelEqType = gPrel "="

-- | The boolean constructor matching a Haskell 'Bool', for the few sites
-- that pick @True@/@False@ at runtime.
prelBoolV :: Bool -> GName
prelBoolV b = if b then prelTrue else prelFalse

-- | The ordering constructor matching a Haskell 'Ordering', for sites that
-- build a comparison result at runtime.
prelOrdering :: Ordering -> GName
prelOrdering o = case o of
  LT -> prelLT
  EQ -> prelEQ
  GT -> prelGT

-- ── Effect-runtime constructors (Exit/Cause/Interrupt, §18) ──────────

-- | The §18 @Exit@ outcome constructors used by the interpreter's
-- completion kernel.
prelSuccess, prelFailure :: GName
prelSuccess = gPrel "Success"
prelFailure = gPrel "Failure"

-- | The §18 @Cause@ constructors (a failed/interrupted/defected outcome)
-- and their payload builders.
prelFail, prelInterrupt, prelDefect, prelMkDefectInfo :: GName
prelFail = gPrel "Fail"
prelInterrupt = gPrel "Interrupt"
prelDefect = gPrel "Defect"
prelMkDefectInfo = gPrel "MkDefectInfo"

-- | The §18.1.8 interrupt-cause record builder and its @TimedOut@ tag.
prelMkInterruptCause, prelTimedOut :: GName
prelMkInterruptCause = gPrel "MkInterruptCause"
prelTimedOut = gPrel "TimedOut"

-- | The §18.1.6 @timeout@ / @race@ result constructors.
prelTOTimedOut, prelTOExit, prelROLeft, prelRORight :: GName
prelTOTimedOut = gPrel "TOTimedOut"
prelTOExit = gPrel "TOExit"
prelROLeft = gPrel "ROLeft"
prelRORight = gPrel "RORight"

-- ── Prelude traits ───────────────────────────────────────────────────

prelShow, prelOrd, prelMonad, prelReleasable :: GName
prelShow = gPrel "Show"
prelOrd = gPrel "Ord"
prelMonad = gPrel "Monad"
prelReleasable = gPrel "Releasable"

prelFromComprehensionRaw, prelFromComprehensionPlan, prelIsTraitWitness :: GName
prelFromComprehensionRaw = gPrel "FromComprehensionRaw"
prelFromComprehensionPlan = gPrel "FromComprehensionPlan"
prelIsTraitWitness = gPrel "__isTraitWitness"

-- ── Prelude functions consulted by name ──────────────────────────────

prelNot, prelCompare, prelReadRef, prelCatchIO, prelFinallyIO, prelStringAppend :: GName
prelNot = gPrel "not"
prelCompare = gPrel "compare"
prelReadRef = gPrel "readRef"
prelCatchIO = gPrel "catchIO"
prelFinallyIO = gPrel "finallyIO"
prelStringAppend = gPrel "stringAppend"

-- ── Wired-in intrinsics (compiler-synthesized prelude globals) ───────

prelRunIO, prelThis, prelCaptures, prelSizedOf :: GName
prelRunIO = gPrel "__runIO"
prelThis = gPrel "__this"
prelCaptures = gPrel "__captures"
prelSizedOf = gPrel "__sizedOf"

prelEffPure, prelEffOp, prelEffBind, prelHandleEff :: GName
prelEffPure = gPrel "__EffPure"
prelEffOp = gPrel "__EffOp"
prelEffBind = gPrel "__effBind"
prelHandleEff = gPrel "__handleEff"

prelEffRowNil, prelEffRowCons :: GName
prelEffRowNil = gPrel "__effRowNil"
prelEffRowCons = gPrel "__effRowCons"

prelOpenRec, prelClosedRow, prelRowExtend, prelRowEvidence :: GName
prelOpenRec = gPrel "__openRec"
prelClosedRow = gPrel "__closedRow"
prelRowExtend = gPrel "__rowExtend"
prelRowEvidence = gPrel "__rowEvidence"

prelSetFromList, prelArrayFromList, prelQueryFromList :: GName
prelSetFromList = gPrel "__setFromList"
prelArrayFromList = gPrel "__arrayFromList"
prelQueryFromList = gPrel "__queryFromList"

prelCodeQuote, prelCodeEscape :: GName
prelCodeQuote = gPrel "__codeQuote"
prelCodeEscape = gPrel "__codeEscape"

-- ── Standard-library module paths ────────────────────────────────────

-- | Alias for 'preludeModule', for symmetry with the other @mod*@ names.
modPrelude :: ModuleName
modPrelude = preludeModule

modDebug, modBytes, modUnicode, modHash, modDerivingShape :: ModuleName
modDebug = ModuleName ["std", "debug"]
modBytes = ModuleName ["std", "bytes"]
modUnicode = ModuleName ["std", "unicode"]
modHash = ModuleName ["std", "hash"]
modDerivingShape = ModuleName ["std", "deriving", "shape"]

modFfi, modFfiC, modAtomic, modGradual, modBridge, modSupervisor :: ModuleName
modFfi = ModuleName ["std", "ffi"]
modFfiC = ModuleName ["std", "ffi", "c"]
modAtomic = ModuleName ["std", "atomic"]
modGradual = ModuleName ["std", "gradual"]
modBridge = ModuleName ["std", "bridge"]
modSupervisor = ModuleName ["std", "supervisor"]

modConfig, modBuild, modTesting :: ModuleName
modConfig = ModuleName ["std", "config"]
modBuild = ModuleName ["std", "build"]
modTesting = ModuleName ["std", "testing"]

-- | The implicit module name for a headerless source file (§8.1).
modMain :: ModuleName
modMain = ModuleName ["main"]

-- | The synthetic module owning a build manifest's reified config unit.
modManifest :: ModuleName
modManifest = ModuleName ["__manifest"]

-- | Module-path roots reserved for host-supplied binding modules; user
-- source may not define a module at or under these (§8.3.5).
reservedHostRoots :: [[Text]]
reservedHostRoots =
  [ ["host", "jvm", "jni"]
  , ["host", "jvm"]
  , ["host", "dotnet"]
  , ["host", "native"]
  , ["host", "python"]
  ]

-- ── Trait spellings for literal-witness resolution ───────────────────

traitFromInteger, traitFromFloat :: Text
traitFromInteger = "FromInteger"
traitFromFloat = "FromFloat"

-- ── Hardcoded name lists ─────────────────────────────────────────────

-- | The kernel effect carriers that get dedicated do-block elaboration
-- (§18.8) and may not be an active pattern's result type (§17.3.1). These
-- are NOT "any type with a Monad instance" — pure monads like @Option@ /
-- @List@ / @Result@ are valid total views; only these effectful carriers
-- are special. One list shared by the do-block dispatcher and the
-- active-pattern check so the two cannot drift.
kernelMonadCarriers :: [Text]
kernelMonadCarriers = ["IO", "STM", "Eff", "Elab"]

-- | Domains an integer literal defaults into / is admitted by directly,
-- before falling back to @FromInteger@ witness resolution (§6.1.5).
numericLitDomains :: [Text]
numericLitDomains = ["Int", "Nat", "Integer"]

-- | Domains a floating literal is admitted by directly (§6.1.6).
floatLitDomains :: [Text]
floatLitDomains = ["Float", "Double"]

-- | The fixed constructor subset visible unqualified without an explicit
-- @import std.prelude.*@ (§28.1).
implicitPreludeCtorNames :: [Text]
implicitPreludeCtorNames =
  ["True", "False", "None", "Some", "Ok", "Err", "Nil", "::", "LT", "EQ", "GT", "refl"]

-- | Prelude type names admissible in a build-manifest config unit (§35.3).
configSafeTypeNames :: [Text]
configSafeTypeNames =
  [ "Unit", "Bool", "Byte", "Bytes", "UnicodeScalar", "Grapheme", "String"
  , "Int", "Nat", "Integer", "Float", "Double", "Ordering", "Option"
  , "Result", "List", "Char"
  ]

-- | Prelude constructor names admissible in a build-manifest config unit (§35.3).
configSafeCtorNames :: [Text]
configSafeCtorNames =
  ["True", "False", "Some", "None", "Ok", "Err", "Nil", "::", "LT", "EQ", "GT"]

-- ── Load-time validation registry ────────────────────────────────────

-- | What kind of prelude entity a wired-in name is expected to resolve to.
data BuiltinKind
  = BKType -- ^ a type/trait head (lives among globals)
  | BKCtor -- ^ a data constructor (lives among constructors)
  | BKValue -- ^ a term-level global (function/helper)
  | BKIntrinsic -- ^ a compiler-synthesized global; may be provided by the runtime
  deriving stock (Eq, Show)

-- | A wired-in prelude name plus the kind it should resolve to.
data WiredIn = WiredIn
  { wiName :: !GName
  , wiKind :: !BuiltinKind
  }
  deriving stock (Eq, Show)

-- | Every prelude name the compiler depends on existing. Consumed by the
-- pipeline's post-prelude validation pass; if any entry fails to resolve,
-- the compiler reports it rather than miscompiling downstream.
--
-- Deliberately excluded (compiler-synthesized, NOT registered as
-- @std.prelude@ globals/constructors, so they would always "fail" to
-- resolve): 'prelThis' (the implicit record-sibling binding, bound in local
-- context) and 'prelEffPure'/'prelEffOp' (the effect-tree constructors,
-- built and matched structurally via 'Kappa.Core.VCtor' rather than declared
-- in the prelude). They have @prel*@ constants because the checker spells
-- them, but they are not part of the prelude name contract.
wiredInPreludeNames :: [WiredIn]
wiredInPreludeNames =
  map (uncurry WiredIn)
    [ (prelUnit, BKType)
    , (prelBool, BKType)
    , (prelString, BKType)
    , (prelNat, BKType)
    , (prelInt, BKType)
    , (prelInteger, BKType)
    , (prelDouble, BKType)
    , (prelByte, BKType)
    , (prelGrapheme, BKType)
    , (prelUnicodeScalar, BKType)
    , (prelList, BKType)
    , (prelArray, BKType)
    , (prelOption, BKType)
    , (prelThunk, BKType)
    , (prelNeed, BKType)
    , (prelZipper, BKType)
    , (prelRef, BKType)
    , (prelRegion, BKType)
    , (prelEff, BKType)
    , (prelEffRow, BKType)
    , (prelEffLabel, BKType)
    , (prelIO, BKType)
    , (prelSTM, BKType)
    , (prelElab, BKType)
    , (prelSyntax, BKType)
    , (prelLit, BKType)
    , (prelCode, BKType)
    , (prelInterp, BKType)
    , (prelInterpFmt, BKType)
    , (prelRecRow, BKType)
    , (prelLacksRec, BKType)
    , (prelQueryMode, BKType)
    , (prelQueryCore, BKType)
    , (prelQZeroOrMore, BKType)
    , (prelReusable, BKType)
    , (prelTrue, BKCtor)
    , (prelFalse, BKCtor)
    , (prelSome, BKCtor)
    , (prelNone, BKCtor)
    , (prelNil, BKCtor)
    , (prelCons, BKCtor)
    , (prelLT, BKCtor)
    , (prelEQ, BKCtor)
    , (prelGT, BKCtor)
    , (prelSuccess, BKCtor)
    , (prelFailure, BKCtor)
    , (prelFail, BKCtor)
    , (prelInterrupt, BKCtor)
    , (prelDefect, BKCtor)
    , (prelMkDefectInfo, BKCtor)
    , (prelMkInterruptCause, BKCtor)
    , (prelTimedOut, BKCtor)
    , (prelTOTimedOut, BKCtor)
    , (prelTOExit, BKCtor)
    , (prelROLeft, BKCtor)
    , (prelRORight, BKCtor)
    , (prelRefl, BKCtor)
    , (prelEqType, BKType)
    , (prelShow, BKType)
    , (prelOrd, BKType)
    , (prelMonad, BKType)
    , (prelReleasable, BKType)
    , (prelFromComprehensionRaw, BKType)
    , (prelFromComprehensionPlan, BKType)
    , (prelNot, BKValue)
    , (prelCompare, BKValue)
    , (prelReadRef, BKValue)
    , (prelCatchIO, BKValue)
    , (prelFinallyIO, BKValue)
    , (prelStringAppend, BKValue)
    , (prelRunIO, BKIntrinsic)
    , (prelCaptures, BKIntrinsic)
    , (prelSizedOf, BKIntrinsic)
    , (prelEffBind, BKIntrinsic)
    , (prelHandleEff, BKIntrinsic)
    , (prelEffRowNil, BKIntrinsic)
    , (prelEffRowCons, BKIntrinsic)
    , (prelOpenRec, BKIntrinsic)
    , (prelClosedRow, BKIntrinsic)
    , (prelRowExtend, BKIntrinsic)
    , (prelRowEvidence, BKIntrinsic)
    , (prelSetFromList, BKIntrinsic)
    , (prelArrayFromList, BKIntrinsic)
    , (prelQueryFromList, BKIntrinsic)
    , (prelIsTraitWitness, BKIntrinsic)
    , (prelCodeQuote, BKIntrinsic)
    , (prelCodeEscape, BKIntrinsic)
    ]
