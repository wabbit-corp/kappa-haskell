-- | The implicit prelude (Spec §28): builtin types and primitives
-- registered directly, plus an embedded @std.prelude@ source compiled
-- through the ordinary pipeline. SPEC_COMPLIANCE.md documents which parts
-- of the §28.2 normative minimum are provided.
module Kappa.Prelude
  ( builtinState
  , preludeSource
  , stdTypeLevelBootstrapSource
  , stdTypeLevelSource
  , stdTypeLevelPackagesSource
  , stdDerivingShapeSource
  , stdHashSource
  , stdDebugSource
  , stdBytesSource
  , stdUnicodeSource
  , stdFfiSource
  , stdFfiCSource
  , stdAtomicSource
  , stdArrayMutableSource
  , stdGradualSource
  , stdBridgeSource
  , stdSupervisorSource
  , stdConfigSource
  , stdBuildSource
  , evalPurePrim
  ) where

import Control.Monad.State.Strict (State, evalState, get, put)
import Control.Monad (replicateM)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as T
import Kappa.Builtins
  ( prelBorrowRegionOf
  , prelNat
  , prelNatSucc
  , prelNatZero
  , prelTypeLevel
  )
import Kappa.Check
import Kappa.Core
import Kappa.CoreOps (levelParamsOfTerm)
import Kappa.Eval
  ( EvalCtx (..)
  , GlobalDef (gdType)
  , Globals (..)
  , emptyMetas
  , evalPurePrim
  , globalDefWithUniverses
  , lookupEnv
  , quote
  )
import Kappa.Source (ModuleName (..))

prel :: Text -> GName
prel = GName preludeModule

-- small Pi-type builders (closed terms, evaluated lazily by the checker)
piM :: ObservationMode -> Icit -> Q -> Bool -> Text -> Term -> Term -> Term
piM mode ic q borrowed name domain codomain =
  CPiEvidenceM mode formation ic q borrowed name Nothing BinderSourceWritten domain codomain
  where
    formation
      | mode == Parametric && paramKind domain = FormationParametric
      | otherwise = FormationOrdinary

infixr 5 ~>
(~>) :: Term -> Term -> Term
a ~> b = piM Ordinary Expl QW False "_" a b

piI :: Q -> Text -> Term -> Term -> Term
piI q nm a b = piM (defaultMode a) Impl q False nm a b

pi0 :: Text -> Term -> Term -> Term
pi0 nm a b = piM (defaultMode a) Expl Q0 False nm a b

-- The embedded prelude has already-elaborated Core domains, so apply the same
-- structural §11.1.2.3B defaulting judgment directly.  This is independent of
-- the requested quantity: only the elaborated parametric-kind shape selects
-- the observation mode.
defaultMode :: Term -> ObservationMode
defaultMode domain
  | paramKind domain = Parametric
  | otherwise = Ordinary

paramKind :: Term -> Bool
paramKind = \case
  CSort _ -> True
  CPiEvidenceM Parametric FormationParametric _ Q0 False _ _ _ dom cod ->
    paramKind dom && paramKind cod
  _ -> False

tcon :: Text -> Term
tcon = CGlob . prel

-- | Hidden-universe arities of source-defined type constructors referenced by
-- the hand-built builtin signatures below. A bare 'tcon' is the seeded
-- counterpart of an ordinary source reference: 'floatBuiltinUniverses'
-- assigns a fresh declaration-universe instance to each occurrence. Explicit
-- 'CGlobI' occurrences keep their written instance. Keeping this table on
-- resolved identities makes the seeded KCore as explicit as source-elaborated
-- KCore; the finalized checkpoint rejects any arity drift.
seededTypeUniverseArities :: Map.Map GName Int
seededTypeUniverseArities =
  Map.fromList
    [ (prel "Array", 1)
    , (prel "BorrowView", 1)
    , (prel "Cause", 1)
    , (prel "ClosedCode", 1)
    , (prel "Code", 1)
    , (prel "Core", 1)
    , (prel "CoreEq", 2)
    , (prel "Eff", 1)
    , (prel "Elab", 1)
    , (prel "Eq", 1)
    , (prel "Exit", 2)
    , (prel "Fiber", 2)
    , (prel "FiberRef", 1)
    , (prel "IO", 2)
    , (prel "IsSubsingleton", 1)
    , (prel "IsTrait", 1)
    , (prel "List", 1)
    , (prel "Map", 2)
    , (prel "Monitor", 2)
    , (prel "Option", 1)
    , (prel "Ord", 1)
    , (prel "Projector", 2)
    , (prel "Promise", 2)
    , (prel "QueryCore", 1)
    , (prel "RaceOutcome", 4)
    , (prel "Ref", 1)
    , (prel "Set", 1)
    , (prel "STM", 1)
    , (prel "Syntax", 1)
    , (prel "TVar", 1)
    , (prel "TimeoutOutcome", 2)
    , (prel "__ArrayBuf", 1)
    , (prel "__AtomicCell", 1)
    ]

-- | Initial state: builtin types and primitives under @std.prelude@.
builtinState :: CheckState
builtinState =
  case certifyClosedBuiltinData prelNat seededState of
    Left message ->
      error ("invalid compiler-seeded Nat interface: " <> T.unpack message)
    Right certified -> certified
  where
    seededState =
      initCheckState
        { csModule = preludeModule
    , -- §4.5 soundness escape: the genuine embedded prelude and the embedded
      -- standard-library modules built on top of it (std.debug etc.) admit the
      -- proof helpers (cong/sym/trans/subst/…) and wrap the debug introspection
      -- prims via the raw-admit intrinsics. The exemption is THIS flag alone
      -- (see 'gateUnsafeIntrinsic'): set it here, on the genuine embedded load,
      -- so those modules are permitted. A user file merely NAMED 'module
      -- std.prelude' never goes through this loader, so it does not get the
      -- flag and is gated like any other module. 'stdModule' inherits this flag
      -- (it does not reset it), so the embedded std-lib is covered too; the
      -- user-module pipeline (Kappa.Pipeline) sets it explicitly per module
      -- from the @AllowUnsafeIntrinsics attribute, overriding this base value.
      csAllowUnsafeIntrinsics = True
    , -- §4.7 audit hygiene: mark this as the genuine embedded load so the
      -- prelude's internal proof admits and the std-lib's debug-prim wrappers
      -- are NOT written to the audit ledger (they would otherwise carry into
      -- every user module's ledger). The pipeline clears this for user modules.
      csEmbeddedLoad = True
    , csGlobals = Map.fromList (types ++ prims ++ testingPrims)
    , csCtors = Map.fromList ctors
    , csDatas = Map.fromList datas
    , csPositivity = Map.fromList positivity
        , csModuleExports =
            Map.fromList [(testingModule, [nm | (GName _ nm, _) <- testingPrims])]
        }
    opaqueTy t = inferDeclarationUniverses (GlobalDef t Nothing False)
    prim name t = (prel name, inferDeclarationUniverses (GlobalDef t (Just (VPrim name [])) False))
    internalPrim name t =
      ( GName primModule name
      , inferDeclarationUniverses (GlobalDef t (Just (VPrim name [])) False)
      )
    compilerOpaque identity t =
      ( identity
      , inferDeclarationUniverses (GlobalDef t Nothing False)
      )
    inferDeclarationUniverses def =
      let params = levelParamsOfTerm (quote closedEvalCtx 0 (gdType def))
          count = case params of
            [] -> 0
            _ -> maximum params + 1
       in globalDefWithUniverses (DeclarationUniverseTelescope count False) def
    closedEvalCtx = EvalCtx (Globals Map.empty) emptyMetas False Map.empty
    testingModule = ModuleName ["std", "testing"]
    -- @std.testing@ (§T.6 support library): @failNow@ aborts evaluation
    -- with a message; it reduces to a stuck primitive that the harness
    -- and runtime report as a runtime failure.
    testingPrims =
      [ ( GName testingModule "failNow"
        , inferDeclarationUniverses (GlobalDef (tyV (piI Q0 "a" tType (tStr ~> CVar 1))) (Just (VPrim "failNow" [])) False)
        )
      ]

    tType = CSort LZero
    tTypeAt i = CSort (LParam i)
    -- Parametric carrier arguments generalize, while the carrier's result
    -- classifier is minimized independently (§11.1.3). These compiler-seeded
    -- declarations therefore have one hidden universe per type argument and a
    -- principal Type0 result, exactly like equivalent source declarations.
    typeToType = piM Parametric Expl Q0 False "A" (tTypeAt 0) tType
    typeToTypeToType =
      piM Parametric Expl Q0 False "A" (tTypeAt 0) $
        piM Parametric Expl Q0 False "B" (tTypeAt 1) tType
    capturesType =
      piM Parametric Expl Q0 False "A" (tTypeAt 0) $
        piM Parametric Expl Q0 False "region" (tcon "Region") (tTypeAt 0)
    tyV t = evalClosed (floatBuiltinUniverses t)
    types =
      [ (prel "Integer", opaqueTy (tyV tType))
      , (prel "Nat", opaqueTy (tyV tType))
      , (prel "Rational", opaqueTy (tyV tType)) -- §28.2 exact ratio type
      , (prel "Double", opaqueTy (tyV tType))
      , (prel "String", opaqueTy (tyV tType))
      , (prel "UnicodeScalar", opaqueTy (tyV tType))
      , (prel "Grapheme", opaqueTy (tyV tType)) -- §28.2 user-perceived text atom
      , (prel "Byte", opaqueTy (tyV tType)) -- §28.2 single byte (§6.5 'b' handler)
      , (prel "Bytes", opaqueTy (tyV tType))
      , (prel "BytesBuilder", opaqueTy (tyV tType)) -- §29.5 linear builder accumulator
      , (prel "BytesDecodeError", opaqueTy (tyV tType)) -- §29.5
      , (prel "StringBuilder", opaqueTy (tyV tType)) -- §29.4 linear text builder
      , (prel "Utf8Decoder", opaqueTy (tyV tType)) -- §29.4 incremental decoder
      , (prel "StringCursor", opaqueTy (tyV tType)) -- §29.4 string cursor
      , (prel "StringSpan", opaqueTy (tyV tType)) -- §29.4 string span
      , (prel "Region", opaqueTy (tyV tType)) -- §12.3 explicit region variables
      , -- §12.3.1 capture-annotated type former: part of type identity (§31.1)
        (prel "__captures", opaqueTy (tyV capturesType))
      , -- §18.1 Duration/Instant are ordinary opaque data over Int (the std.time
        -- fragment in the prelude library below), NOT compiler-opaque builtins.
        (prel "STM", opaqueTy (tyV typeToType)) -- §18.1.13
      , (prel "TVar", opaqueTy (tyV typeToType)) -- §18.1.13
      , (prel "Promise", opaqueTy (tyV typeToTypeToType)) -- §18.11 one-shot promise
      , (prel "Scope", opaqueTy (tyV tType)) -- §18.1.8 explicit supervision scope
      , (prel "Monitor", opaqueTy (tyV typeToTypeToType)) -- §18.1.8 fiber monitor
      , (prel "FiberRef", opaqueTy (tyV typeToType)) -- §18.1.7 fiber-local cell
      , (prel "Thunk", opaqueTy (tyV typeToType))
      , (prel "Need", opaqueTy (tyV typeToType))
      , (prel "IO", opaqueTy (tyV typeToTypeToType))
      , (prel "Ref", opaqueTy (tyV typeToType))
      , -- §29.1 the opaque atomic cell wrapped by AtomicRef. NOT a
        -- Ref/TVar: it has no readRef/writeRef surface, so atomicity cannot be
        -- bypassed. Built by __newAtomicRef; consumed by the other __atomic* ops.
        (prel "__AtomicCell", opaqueTy (tyV typeToType))
      , -- MUTABLE-ARRAY-DESIGN §4.1: the opaque mutable-array buffer wrapped by
        -- MutArray. The element type is a Q0-erased parameter that never reaches
        -- the runtime. Built by __newArray; consumed by __arrayRead/Write/Len.
        (prel "__ArrayBuf", opaqueTy (tyV typeToType))
      , -- §18.1.14 algebraic effects: the Eff carrier, effect rows and
        -- labels; rows are encoded as neutral spines
        -- '__effRowCons label iface rest' ending in '__effRowNil'
        (prel "EffRow", opaqueTy (tyV tType))
      , (prel "EffLabel", opaqueTy (tyV tType))
      , (prel "Eff", opaqueTy (tyV (piM Ordinary Expl Q0 False "row" (tcon "EffRow") typeToType)))
      , (prel "__effRowNil", opaqueTy (tyV (tcon "EffRow")))
      , (prel "__effRowCons", opaqueTy (tyV
          (tcon "EffLabel" ~> piM Parametric Expl Q0 False "interface" tType
            (tcon "EffRow" ~> tcon "EffRow"))))
      , -- §20 collection carriers and the §20.10 query core
        (prel "Set", opaqueTy (tyV typeToType))
      , (prel "Map", opaqueTy (tyV typeToTypeToType))
      , (prel "Array", opaqueTy (tyV typeToType))
      , (prel "Quantity", opaqueTy (tyV tType)) -- §12.1.1 reified quantities
      , -- phantom carrier for the corpus 'Array n elem' accommodation
        -- (see inferT in Kappa.Check)
        (prel "__sizedOf", opaqueTy (tyV (piM Ordinary Expl QW False "n" (tcon "Nat") typeToType)))
      , -- §11.3.1 record rows: row kind, the lacks constraint (labels
        -- are elaborated to string literals), and the open-record
        -- encoding '__openRec r (explicit-prefix record type)'
        (prel "RecRow", opaqueTy (tyV tType))
      , (prel "LacksRec", opaqueTy (tyV (tcon "RecRow" ~> tStr ~> tType)))
      , (prel "__openRec", opaqueTy (tyV (tcon "RecRow" ~> tType ~> tType)))
      , (prel "__rowExtend", inferDeclarationUniverses (GlobalDef (tyV (piI Q0 "a" tType (piI Q0 "b" tType (CVar 1 ~> tStr ~> CVar 2 ~> CVar 4)))) (Just (VPrim "__rowExtend" [])) False))
      , -- a closed residual row tail '__closedRow (fields record type)':
        -- solving an open record against a closed record instantiates
        -- the row tail with the leftover closed fields (§11.3.1A)
        (prel "__closedRow", opaqueTy (tyV (tType ~> tcon "RecRow")))
      , -- compiler-owned introduction-rule witness for the §11.3.1A
        -- intrinsic row traits (the evidence carries no information)
        (prel "__rowEvidence", opaqueTy (tyV (piI Q0 "r" (tcon "RecRow") (piI Q0 "l" tStr (CApp Expl (CApp Expl (tcon "LacksRec") (CVar 1)) (CVar 0))))))
      , (prel "ω", GlobalDef (tyV (tcon "Quantity")) (Just (VPrim "__omegaQ" [])) False)
      , (prel "QueryCore", opaqueTy (tyV (tcon "QueryMode" ~> tcon "Quantity" ~> typeToType)))
      , (prel "BorrowView", opaqueTy (tyV (tcon "Region" ~> typeToType))) -- §20.10.2
      , -- §12.4.3 first-class projector and accessor descriptors
        (prel "Projector", opaqueTy (tyV typeToTypeToType))
      , (prel "Getter", opaqueTy (tyV typeToTypeToType))
      , (prel "Opener", opaqueTy (tyV typeToTypeToType))
      , (prel "Setter", opaqueTy (tyV typeToTypeToType))
      , (prel "Sinker", opaqueTy (tyV typeToTypeToType))
      , (prel "composeProjector", inferDeclarationUniverses (GlobalDef composeProjectorTy (Just (VPrim "composeProjector" [])) False))
      , (prel "captureBorrow", inferDeclarationUniverses (GlobalDef captureBorrowTy (Just (VPrim "captureBorrow" [])) False))
      , (prel "withBorrowView", inferDeclarationUniverses (GlobalDef withBorrowViewTy (Just (VPrim "withBorrowView" [])) False))
      , -- §21 metaprogramming: hidden declaration universes let Syntax/Elab
        -- index values from any universe without a term-level TypeLevel Pi.
        (prel "Syntax", opaqueTy (tyV (piM Parametric Expl Q0 False "A" (CSort (LParam 0)) tType)))
      , (prel "Elab", opaqueTy (tyV (piM Parametric Expl Q0 False "A" (CSort (LParam 0)) tType)))
      , (prel "SyntaxOrigin", opaqueTy (tyV tType))
      , -- §21.6 semantic-reflection symbol identity (compile-time only)
        (prel "Symbol", opaqueTy (tyV tType))
      , -- §21.6 semantic-reflection tier (compile-time only, erased): an
        -- elaborated well-scoped core term `Core Γ t` in context `Γ`, with
        -- the witness-bearing exact equality `CoreEq`.
        (prel "CoreCtx", opaqueTy (tyV tType))
      , (prel "Core", globalDefWithUniverses coreUniverses (opaqueTy (tyV coreKind)))
      , (prel "CoreEq", globalDefWithUniverses coreEqUniverses (opaqueTy coreEqKind))
      , -- §23.1 generative staged code (not inspectable as Syntax)
        (prel "Code", opaqueTy (tyV typeToType))
      , (prel "ClosedCode", opaqueTy (tyV typeToType))
      , -- §20.9 opaque carriers passed to comprehension sink hooks
        (prel "RawComprehension", opaqueTy (tyV typeToType))
      , (prel "ComprehensionPlan", opaqueTy (tyV typeToType))
      , -- §22.4 trait-constructor classifier (witnesses synthesized by
        -- implicit resolution when the head is a declared trait)
        (prel "IsTrait", opaqueTy (tyV (pi0 "t" tType tType)))
      , (prel "__isTraitWitness", opaqueTy (tyV (piI Q0 "t" tType (CApp Expl (tcon "IsTrait") (CVar 0)))))
      , ( prel "__traitSubsingletonWitness"
        , opaqueTy
            ( tyV
                ( piI Q0 "t" tType
                    ( piI Q0 "_trait"
                        (CApp Expl (tcon "IsTrait") (CVar 0))
                        (CApp Expl (tcon "IsSubsingleton") (CVar 1))
                    )
                )
            )
        )
      ]
    coreUniverses = DeclarationUniverseTelescope 1 False
    coreEqUniverses = DeclarationUniverseTelescope 2 False
    -- §21.6 Core/CoreEq carry the universes of their reflected object types
    -- as declaration parameters. They are not fixed to Type0 and do not
    -- expose term-level TypeLevel binders.
    coreKind =
      pi0 "G" (tcon "CoreCtx") $
        piM Parametric Expl Q0 False "A" (CSort (LParam 0)) tType
    coreAt universe context objectType =
      CApp Expl
        (CApp Expl (CGlobI (prel "Core") [universe]) context)
        objectType
    -- §21.6 CoreEq kind: forall (@0 Γ : CoreCtx) (@0 a b : Type).
    -- Core Γ a -> Core Γ b -> Type
    coreEqKind =
      tyV $
        piI Q0 "G" (tcon "CoreCtx") $
          piM Parametric Impl Q0 False "a" (CSort (LParam 0)) $
            piM Parametric Impl Q0 False "b" (CSort (LParam 1)) $
              coreAt (LParam 0) (CVar 2) (CVar 1)
                ~> coreAt (LParam 1) (CVar 3) (CVar 1) ~> tType
    projT r f = CApp Expl (CApp Expl (tcon "Projector") r) f
    -- §12.4.3 composeProjector (one-field root packs of the middle
    -- projector are admitted structurally, hence the extra parameter)
    composeProjectorTy =
      tyV $
        piI Q0 "roots" tType $
          piI Q0 "mid" tType $
            piI Q0 "midRoots" tType $
              piI Q0 "focus" tType $
                piM Ordinary Expl QW False "_" (projT (CVar 3) (CVar 2)) $
                  piM Ordinary Expl QW False "_" (projT (CVar 2) (CVar 1)) $
                    projT (CVar 5) (CVar 2)
    captureBorrowTy =
      tyV $
        piI Q0 "ρ" (tcon "Region") $
          piI Q0 "a" tType $
            piM Ordinary Expl QW False "_" (CVar 0) $
              CApp Expl (CApp Expl (tcon "BorrowView") (CVar 2)) (CVar 1)
    borrowRegionOfTy =
      tyV $
        piI Q0 "a" tType $
          piM Ordinary Expl QW True "value" (CVar 0) (tcon "Region")
    withBorrowViewTy =
      tyV $
        piI Q0 "ρ" (tcon "Region") $
          piI Q0 "a" tType $
            piI Q0 "r" tType $
              piM Ordinary Expl QW False "_" (CApp Expl (CApp Expl (tcon "BorrowView") (CVar 2)) (CVar 1)) $
                piM Ordinary Expl QW False "_" (piM Ordinary Expl QW False "_" (CVar 2) (CVar 2)) $
                  CVar 2
    -- Nat is logically an ordinary inductive family even though its runtime
    -- representation is the exact compact Integer carrier.  Seed the same
    -- constructor interfaces an equivalent source data declaration would
    -- publish; evaluator and KBackendIR lowering provide the representation
    -- bridge without replacing these logical identities.
    ctors =
      [ (prelNatZero, CtorInfo prelNat emptyDeclarationUniverseTelescope tNat [] [])
      , (prelNatSucc, CtorInfo prelNat emptyDeclarationUniverseTelescope (tNat ~> tNat)
            [(Just "predecessor", Nothing)] [(Expl, Just "predecessor")])
      ]
    datas =
      [ (prelNat, DataInfo [prelNatZero, prelNatSucc] 0 LZero)
      ]
    -- §10.4 built-in parameter-positivity signatures for the opaque
    -- carriers that are "declared as strictly positive together with a
    -- parameter-positivity signature" (the spec names List/Option/Array
    -- specifically; List/Option/Result and propositional equality are
    -- source-defined data types whose signatures the positivity pass
    -- computes, so only the opaque carriers are seeded here).
    positivity =
      [ (prel "Array", [True]) -- §10.4 names Array explicitly
      , (prel "Set", [True])
      , (prel "Map", [True, True])
      , (prel "Ref", [True])
      , (prel "IO", [True, True])
      , (prel "Code", [True])
      , (prel "ClosedCode", [True])
      ]
    tInt = tcon "Integer"
    tNat = tcon "Nat"
    tLevel = CGlob prelTypeLevel
    synT a = CApp Expl (tcon "Syntax") a
    elabT a = CApp Expl (tcon "Elab") a
    elabTAt level a = CApp Expl (CGlobI (prel "Elab") [level]) a
    tOrigin = tcon "SyntaxOrigin"
    tconShapeAt name universes = CGlobI (GName shapeModule name) universes
    tDouble = tcon "Double"
    tRat = tcon "Rational"
    tStr = tcon "String"
    tBool = tcon "Bool" -- defined by prelude source; fine as neutral
    tScalar = tcon "UnicodeScalar"
    tGrapheme = tcon "Grapheme"
    tByte = tcon "Byte"
    tBytes = tcon "Bytes"
    tUnit = tcon "Unit"
    io e a = CApp Expl (CApp Expl (tcon "IO") e) a
    optionT a = CApp Expl (tcon "Option") a
    codeT a = CApp Expl (tcon "Code") a
    closedCodeT a = CApp Expl (tcon "ClosedCode") a
    effT r a = CApp Expl (CApp Expl (tcon "Eff") r) a
    refT a = CApp Expl (tcon "Ref") a
    atomicCellT a = CApp Expl (tcon "__AtomicCell") a -- §29.1 opaque atomic cell
    arrayBufT a = CApp Expl (tcon "__ArrayBuf") a -- MUTABLE-ARRAY-DESIGN §4.1 buffer
    listT a = CApp Expl (tcon "List") a
    setT a = CApp Expl (tcon "Set") a
    arrayT a = CApp Expl (tcon "Array") a
    mapT k v = CApp Expl (CApp Expl (tcon "Map") k) v
    queryT m q a = CApp Expl (CApp Expl (CApp Expl (tcon "QueryCore") m) q) a
    entryT k v = CRecordT [("key", k), ("value", v)]
    forallE body = piM Parametric Impl Q0 False "e" (tTypeAt 0) body
    forallEA body =
      piM Parametric Impl Q0 False "e" (tTypeAt 0) $
        piM Parametric Impl Q0 False "a" (tTypeAt 1) body
    forallEFA body =
      piM Parametric Impl Q0 False "e" (tTypeAt 0) $
        piM Parametric Impl Q0 False "f" (tTypeAt 1) $
          piM Parametric Impl Q0 False "a" (tTypeAt 2) body

    prims =
      [ compilerOpaque prelBorrowRegionOf borrowRegionOfTy
      , internalPrim "__typeLevelZero" (tyV tLevel)
      , internalPrim "__typeLevelOmega" (tyV tLevel)
      , internalPrim "__typeLevelSucc" (tyV (tLevel ~> tLevel))
      , internalPrim "__typeLevelAdd" (tyV (tLevel ~> tLevel ~> tLevel))
      , internalPrim "__typeLevelMax" (tyV (tLevel ~> tLevel ~> tLevel))
      , internalPrim "__typeLevelFromNat" (tyV (tNat ~> tLevel))
      , internalPrim "__elabPure"
          (tyV
            (piI Q0 "a" (CSort (LParam 0))
              (CVar 0 ~> elabTAt (LParam 0) (CVar 1))))
      , internalPrim "__elabBind"
          (tyV
            (piI Q0 "a" (CSort (LParam 0))
              (piI Q0 "b" (CSort (LParam 1))
                ( elabTAt (LParam 0) (CVar 1)
                    ~> (CVar 2 ~> elabTAt (LParam 1) (CVar 2))
                    ~> elabTAt (LParam 1) (CVar 2)
                ))))
      , prim "__compareTypeLevel" (tyV (tLevel ~> tLevel ~> tcon "Ordering"))
      , prim "__eqTypeLevel" (tyV (tLevel ~> tLevel ~> tBool))
      , prim "addInt" (tyV (tInt ~> tInt ~> tInt))
      , prim "subInt" (tyV (tInt ~> tInt ~> tInt))
      , prim "mulInt" (tyV (tInt ~> tInt ~> tInt))
      , prim "divInt" (tyV (tInt ~> tInt ~> tInt))
      , prim "modInt" (tyV (tInt ~> tInt ~> tInt))
      , prim "negInt" (tyV (tInt ~> tInt))
      , prim "eqInt" (tyV (tInt ~> tInt ~> tBool))
      , prim "ltInt" (tyV (tInt ~> tInt ~> tBool))
      , prim "leInt" (tyV (tInt ~> tInt ~> tBool))
      , prim "addDouble" (tyV (tDouble ~> tDouble ~> tDouble))
      , prim "subDouble" (tyV (tDouble ~> tDouble ~> tDouble))
      , prim "mulDouble" (tyV (tDouble ~> tDouble ~> tDouble))
      , prim "divDouble" (tyV (tDouble ~> tDouble ~> tDouble))
      , prim "negDouble" (tyV (tDouble ~> tDouble))
      , prim "eqDouble" (tyV (tDouble ~> tDouble ~> tBool)) -- raw-bit equality (§6.1.3)
      , prim "ltDouble" (tyV (tDouble ~> tDouble ~> tBool))
      , prim "floatEq" (tyV (tDouble ~> tDouble ~> tBool)) -- IEEE numeric equality
      , -- §6.1.7 libm floating-point / transcendental math (TOTAL Double ops,
        -- IEEE-754 semantics — sqrt of a negative is NaN; no partiality)
        prim "sqrt" (tyV (tDouble ~> tDouble))
      , prim "sin" (tyV (tDouble ~> tDouble))
      , prim "cos" (tyV (tDouble ~> tDouble))
      , prim "tan" (tyV (tDouble ~> tDouble))
      , prim "asin" (tyV (tDouble ~> tDouble))
      , prim "acos" (tyV (tDouble ~> tDouble))
      , prim "atan" (tyV (tDouble ~> tDouble))
      , prim "atan2" (tyV (tDouble ~> tDouble ~> tDouble))
      , prim "exp" (tyV (tDouble ~> tDouble))
      , prim "log" (tyV (tDouble ~> tDouble))
      , prim "pow" (tyV (tDouble ~> tDouble ~> tDouble))
      , prim "floor" (tyV (tDouble ~> tDouble))
      , prim "ceil" (tyV (tDouble ~> tDouble))
      , prim "fabs" (tyV (tDouble ~> tDouble))
      , prim "showFixed" (tyV (tNat ~> tDouble ~> tStr)) -- §6.1.7 "%.*f" formatter
      , -- §28.2 Rational exact-ratio arithmetic prims (the surface
        -- instances below delegate to these); '__ratOfInt' builds n/1
        prim "__ratOfInt" (tyV (tInt ~> tRat))
      , prim "addRat" (tyV (tRat ~> tRat ~> tRat))
      , prim "subRat" (tyV (tRat ~> tRat ~> tRat))
      , prim "mulRat" (tyV (tRat ~> tRat ~> tRat))
      , prim "divRat" (tyV (tRat ~> tRat ~> tRat))
      , prim "negRat" (tyV (tRat ~> tRat))
      , prim "eqRat" (tyV (tRat ~> tRat ~> tBool))
      , prim "ltRat" (tyV (tRat ~> tRat ~> tBool))
      , prim "showRat" (tyV (tRat ~> tStr))
      , prim "ratOfDouble" (tyV (tDouble ~> tRat)) -- §6.1.6 exact dyadic decode
      , prim "eqStr" (tyV (tStr ~> tStr ~> tBool))
      , prim "ltStr" (tyV (tStr ~> tStr ~> tBool))
      , prim "eqScalar" (tyV (tScalar ~> tScalar ~> tBool))
      , prim "ltScalar" (tyV (tScalar ~> tScalar ~> tBool))
      , -- §6.5/§29.5 text-atom comparison and rendering primitives
        prim "eqByte" (tyV (tByte ~> tByte ~> tBool))
      , prim "ltByte" (tyV (tByte ~> tByte ~> tBool))
      , prim "showByte" (tyV (tByte ~> tStr))
      , prim "eqBytes" (tyV (tBytes ~> tBytes ~> tBool))
      , prim "ltBytes" (tyV (tBytes ~> tBytes ~> tBool))
      , prim "showBytes" (tyV (tBytes ~> tStr))
      , prim "eqGrapheme" (tyV (tGrapheme ~> tGrapheme ~> tBool)) -- exact scalar sequence (§6.5)
      , prim "showGrapheme" (tyV (tGrapheme ~> tStr))
      , -- §29.4 std.unicode internals (wrapped by the embedded module
        -- source; double-underscore prims are implementation-internal)
        prim "__utf8Bytes" (tyV (tStr ~> tBytes))
      , prim "__utf8Valid" (tyV (tBytes ~> tBool))
      , prim "__decodeUtf8Lossy" (tyV (tBytes ~> tStr))
      , prim "__byteLength" (tyV (tStr ~> tNat))
      , prim "__uniScalarValue" (tyV (tScalar ~> tNat))
      , prim "__scalarInRange" (tyV (tNat ~> tBool))
      , prim "__scalarOfValue" (tyV (tNat ~> tScalar))
      , prim "__scalarToString" (tyV (tScalar ~> tStr))
      , prim "__stringScalars" (tyV (tStr ~> listT tScalar))
      , prim "__scalarCount" (tyV (tStr ~> tNat))
      , prim "__graphemeToString" (tyV (tGrapheme ~> tStr))
      , prim "__graphemeValid" (tyV (tStr ~> tBool))
      , prim "__graphemeOfString" (tyV (tStr ~> tGrapheme))
      , prim "__stringGraphemes" (tyV (tStr ~> listT tGrapheme))
      , prim "__graphemeCount" (tyV (tStr ~> tNat))
      , prim "__normalize" (tyV (tInt ~> tStr ~> tStr)) -- 0=NFC 1=NFD 2=NFKC 3=NFKD
      , prim "__caseFold" (tyV (tStr ~> tStr))
      , prim "__stringWords" (tyV (tStr ~> listT tStr))
      , prim "__stringSentences" (tyV (tStr ~> listT tStr))
      , -- §29.4 StringBuilder (linear text accumulator)
        prim "__newStringBuilder" (tyV (tcon "StringBuilder"))
      , prim "__stringBuilderString" (tyV (tStr ~> piM Ordinary Expl Q1 False "b" (tcon "StringBuilder") (tcon "StringBuilder")))
      , prim "__stringBuilderScalar" (tyV (tScalar ~> piM Ordinary Expl Q1 False "b" (tcon "StringBuilder") (tcon "StringBuilder")))
      , prim "__stringBuilderGrapheme" (tyV (tGrapheme ~> piM Ordinary Expl Q1 False "b" (tcon "StringBuilder") (tcon "StringBuilder")))
      , prim "__finishStringBuilder" (tyV (piM Ordinary Expl Q1 False "b" (tcon "StringBuilder") tStr))
      , -- §29.4 string cursors (StringCursor is a scalar offset; the
        -- byte offset is reported by __stringCursorOffset)
        prim "__stringStart" (tyV (tStr ~> tcon "StringCursor"))
      , prim "__stringEnd" (tyV (tStr ~> tcon "StringCursor"))
      , prim "__stringCursorOffset" (tyV (tStr ~> tcon "StringCursor" ~> tNat))
      , prim "__stringNextScalar"
          (tyV (tStr ~> tcon "StringCursor" ~> optionT (CRecordT [("next", tcon "StringCursor"), ("scalar", tScalar)])))
      , prim "__stringPrevScalar"
          (tyV (tStr ~> tcon "StringCursor" ~> optionT (CRecordT [("prev", tcon "StringCursor"), ("scalar", tScalar)])))
      , prim "__stringNextGrapheme"
          (tyV (tStr ~> tcon "StringCursor" ~> optionT (CRecordT [("grapheme", tGrapheme), ("next", tcon "StringCursor")])))
      , prim "__stringSpan" (tyV (tStr ~> tcon "StringCursor" ~> tcon "StringCursor" ~> optionT tStr))
      , prim "__stringCompact" (tyV (tStr ~> tStr))
      , -- §29.4 incremental UTF-8 decoder. The prims report malformed
        -- input as 'None'; the std.unicode wrappers map None to
        -- 'Err MkUnicodeDecodeError' and Some to 'Ok'.
        prim "__newUtf8Decoder" (tyV (tcon "Utf8Decoder"))
      , prim "__decodeUtf8Chunk"
          (tyV (tBytes ~> piM Ordinary Expl Q1 False "d" (tcon "Utf8Decoder")
                  (optionT (CRecordT [("decoder", tcon "Utf8Decoder"), ("text", tStr)]))))
      , prim "__finishUtf8Decoder"
          (tyV (piM Ordinary Expl Q1 False "d" (tcon "Utf8Decoder") (optionT tStr)))
      , prim "__byteToNat" (tyV (tByte ~> tNat))
      , prim "__natToByte" (tyV (tNat ~> tByte)) -- §29.5 builder/byte construction
      , -- §29.5 std.bytes internals (wrapped by the std.bytes module)
        prim "__bytesEmpty" (tyV tBytes)
      , prim "__bytesSingleton" (tyV (tByte ~> tBytes))
      , prim "__bytesLength" (tyV (tBytes ~> tNat))
      , prim "__bytesIsEmpty" (tyV (tBytes ~> tBool))
      , prim "__bytesGet" (tyV (tBytes ~> tNat ~> optionT tByte))
      , prim "__bytesIndexUnsafe" (tyV (tBytes ~> tNat ~> tByte))
      , prim "__bytesAppend" (tyV (tBytes ~> tBytes ~> tBytes))
      , prim "__bytesSlice" (tyV (tBytes ~> tNat ~> tNat ~> tBytes))
      , prim "__bytesTake" (tyV (tNat ~> tBytes ~> tBytes))
      , prim "__bytesDrop" (tyV (tNat ~> tBytes ~> tBytes))
      , prim "__bytesStartsWith" (tyV (tBytes ~> tBytes ~> tBool))
      , prim "__bytesEndsWith" (tyV (tBytes ~> tBytes ~> tBool))
      , prim "__bytesContains" (tyV (tBytes ~> tBytes ~> tBool))
      , prim "__bytesFind" (tyV (tByte ~> tBytes ~> optionT tNat))
      , prim "__bytesBreakIndex" (tyV (tBytes ~> tBytes ~> optionT tNat))
      , prim "__bytesToList" (tyV (tBytes ~> listT tByte))
      , prim "__bytesFromList" (tyV (listT tByte ~> tBytes))
      , prim "__bytesCompact" (tyV (tBytes ~> tBytes))
      , prim "__newBytesBuilder" (tyV (tcon "BytesBuilder"))
      , prim "__bytesBuilderByte" (tyV (tByte ~> piM Ordinary Expl Q1 False "b" (tcon "BytesBuilder") (tcon "BytesBuilder")))
      , prim "__bytesBuilderBytes" (tyV (tBytes ~> piM Ordinary Expl Q1 False "b" (tcon "BytesBuilder") (tcon "BytesBuilder")))
      , prim "__finishBytesBuilder" (tyV (piM Ordinary Expl Q1 False "b" (tcon "BytesBuilder") tBytes))
      , -- §29.1 std.atomic bitwise read-modify-write internals
        prim "__intAnd" (tyV (tInt ~> tInt ~> tInt))
      , prim "__intOr" (tyV (tInt ~> tInt ~> tInt))
      , prim "__intXor" (tyV (tInt ~> tInt ~> tInt))
      , -- §29.1 representation equality for atomicCompareExchange
        prim "__atomicRepEq" (tyV (piI Q0 "a" tType (CVar 0 ~> CVar 1 ~> tcon "Bool")))
      , -- §29.1 std.atomic primitive surface — the opaque atomic cell.
        -- Native (C/LLVM): each lowers to a @krt2_atomic_*@ operation on one boxed
        -- @KValue *@ cell protected by the runtime's atomic-cell discipline, so a
        -- concurrent fetch-add / CAS across the nproc worker pool conserves every
        -- update without narrowing §6 @Integer@ values.  Interpreter: fibers run
        -- cooperatively on one OS thread, so an @IORef@ cell models the SAME
        -- sequential semantics; it is the oracle for single-fiber use, not a test
        -- of the multi-worker race (which only the native runtime can run).
        --
        -- The atomic CELL type @__AtomicCell a@ IS a prelude tcon, so it is named
        -- concretely here (this pins inference — a fully-erased cell var would be
        -- ambiguous).  The memory order arrives as a small Integer CODE (the
        -- §29.1 canonical declaration-order index of the order constructor),
        -- computed by the std.atomic wrappers — NOT the constructor's tag id,
        -- which codegen assigns globally and the runtime cannot interpret.  The
        -- §29.1 CAS does NOT build its CompareExchangeResult here (that type lives
        -- in source): @__atomicCompareExchange@ returns the WITNESSED old value
        -- and the wrapper reconstructs Exchanged/NotExchanged in source.
        -- NOTE De Bruijn: each explicit @~>@ is itself a Pi binder, so every index
        -- to its RIGHT shifts up by one (see 'newRef' for the same accounting).
        prim "__newAtomicRef" (tyV (forallEA          -- forall e a.
          (CVar 0 ~> io (CVar 2) (atomicCellT (CVar 1)))))  -- a -> IO e (__AtomicCell a)
      , prim "__atomicLoad" (tyV (forallEA            -- forall e a.
          (tInt ~> atomicCellT (CVar 1) ~> io (CVar 3) (CVar 2))))  -- Int -> __AtomicCell a -> IO e a
      , prim "__atomicStore" (tyV (forallEA           -- forall e a.
          (tInt ~> atomicCellT (CVar 1) ~> CVar 2 ~> io (CVar 4) tUnit)))  -- Int -> __AtomicCell a -> a -> IO e Unit
      , prim "__atomicExchange" (tyV (forallEA        -- forall e a.
          (tInt ~> atomicCellT (CVar 1) ~> CVar 2 ~> io (CVar 4) (CVar 3))))  -- Int -> __AtomicCell a -> a -> IO e a
      , prim "__atomicCompareExchange" (tyV (forallEA -- forall e a.  (returns the witnessed old value)
          -- succCode -> failCode -> __AtomicCell a -> expected -> desired -> IO e a
          (tInt ~> tInt ~> atomicCellT (CVar 2) ~> CVar 3 ~> CVar 4 ~> io (CVar 6) (CVar 5))))
      , -- fetch-* are gated to integer cells by the AtomicInteger surface, so the
        -- cell payload + result are concrete Integer.
        -- forall e. Int -> __AtomicCell Integer -> Integer -> IO e Integer
        prim "__atomicFetchAdd" (tyV (forallE
          (tInt ~> atomicCellT tInt ~> tInt ~> io (CVar 3) tInt)))
      , prim "__atomicFetchSub" (tyV (forallE
          (tInt ~> atomicCellT tInt ~> tInt ~> io (CVar 3) tInt)))
      , prim "__atomicFetchAnd" (tyV (forallE
          (tInt ~> atomicCellT tInt ~> tInt ~> io (CVar 3) tInt)))
      , prim "__atomicFetchOr" (tyV (forallE
          (tInt ~> atomicCellT tInt ~> tInt ~> io (CVar 3) tInt)))
      , prim "__atomicFetchXor" (tyV (forallE
          (tInt ~> atomicCellT tInt ~> tInt ~> io (CVar 3) tInt)))
      , -- §29.3 std.hash mixing internals (deterministic within a run)
        prim "__hashMixInt" (tyV (tInt ~> tInt ~> tInt))
      , prim "__hashMixDouble" (tyV (tInt ~> tDouble ~> tInt))
      , prim "__hashMixString" (tyV (tInt ~> tStr ~> tInt))
      , prim "__hashMixBytes" (tyV (tInt ~> tBytes ~> tInt))
      , -- §29.6 std.debug introspection internals: result type is fixed by
        -- the std.debug wrappers (DebugTree / DebugEq), which live one
        -- module up, so the prim result is an unconstrained `r` pinned at
        -- the call site. The runtime builds the std.debug constructors.
        prim "__debugInspect" (tyV (piI Q0 "a" tType (piI Q0 "r" tType (CVar 1 ~> CVar 1))))
      , prim "__debugRender" (tyV (piI Q0 "a" tType (CVar 0 ~> tStr)))
      , prim "__debugCompare" (tyV (piI Q0 "a" tType (piI Q0 "r" tType (CVar 1 ~> CVar 2 ~> CVar 2))))
      , prim "stringAppend" (tyV (tStr ~> tStr ~> tStr))
      , prim "showInt" (tyV (tInt ~> tStr))
      , prim "primitiveIntToString" (tyV (tInt ~> tStr))
      , prim "showDouble" (tyV (tDouble ~> tStr))
      , prim "showStringLit" (tyV (tStr ~> tStr))
      , prim "showScalar" (tyV (tScalar ~> tStr))
      , prim "intToDouble" (tyV (tInt ~> tDouble))
      , prim "natOfInt" (tyV (tInt ~> tNat)) -- internal: Nat and Integer share representation
      , prim "natToInt" (tyV (tNat ~> tInt))
      , -- partial Int -> Nat conversion: negative values trap at runtime
        prim "intToNat" (tyV (tInt ~> tNat))
      , -- linear sink used by the external corpus behind its
        -- 'allow_unsafe_consume' directive: discards a linear value
        prim "unsafeConsume" (tyV (piI Q0 "a" tType (piM Ordinary Expl Q1 False "x" (CVar 0) tUnit)))
      , prim "printString" (tyV (forallE (tStr ~> io (CVar 1) tUnit)))
      , prim "printlnString" (tyV (forallE (tStr ~> io (CVar 1) tUnit)))
      , prim "ioPure" (tyV (forallEA (CVar 0 ~> io (CVar 2) (CVar 1))))
      , -- §18.1.4/§32.2: run a forked fiber to completion on the single
        -- runtime agent, capturing its Exit; the result is retrievable by
        -- __awaitFiber. (forall e a r. IO e a -> IO r (Fiber e a))
        prim "__forkRun"
          (tyV (piI Q0 "e" tType (piI Q0 "a" tType (piI Q0 "r" tType
            (io (CVar 2) (CVar 1) ~> io (CVar 1) (CApp Expl (CApp Expl (tcon "Fiber") (CVar 3)) (CVar 2)))))))
      , -- forall e a r. Fiber e a -> IO r (Exit e a)
        prim "__awaitFiber"
          (tyV (piI Q0 "e" tType (piI Q0 "a" tType (piI Q0 "r" tType
            (CApp Expl (CApp Expl (tcon "Fiber") (CVar 2)) (CVar 1) ~> io (CVar 1) (CApp Expl (CApp Expl (tcon "Exit") (CVar 3)) (CVar 2)))))))
      , -- §18.1.4 forkDaemon: like fork but unattached to the structured scope.
        -- forall e a r. IO e a -> IO r (Fiber e a)
        prim "__forkDaemon"
          (tyV (piI Q0 "e" tType (piI Q0 "a" tType (piI Q0 "r" tType
            (io (CVar 2) (CVar 1) ~> io (CVar 1) (CApp Expl (CApp Expl (tcon "Fiber") (CVar 3)) (CVar 2)))))))
      , -- §18.1.4 interruption. __interruptWait blocks until the target fiber
        -- has terminated and all finalizers have run; __interruptNoWait does
        -- not. forall e a. InterruptCause -> Fiber e a -> UIO Unit
        prim "__interruptWait"
          (tyV (piI Q0 "e" tType (piI Q0 "a" tType
            (tcon "InterruptCause" ~> CApp Expl (CApp Expl (tcon "Fiber") (CVar 2)) (CVar 1) ~> io (tcon "Void") tUnit))))
      , prim "__interruptNoWait"
          (tyV (piI Q0 "e" tType (piI Q0 "a" tType
            (tcon "InterruptCause" ~> CApp Expl (CApp Expl (tcon "Fiber") (CVar 2)) (CVar 1) ~> io (tcon "Void") tUnit))))
      , -- Same OP_INTERRUPT_FORK node as `__interruptNoWait`, but with a FREE
        -- result error channel `g` (the no-wait interrupt cannot itself fail, so
        -- its result channel is unconstrained — cf. `__reraiseCause`/`__timeout`).
        -- Used only by `disconnect` so its `onInterrupt` finalizer, which must be
        -- `IO e Unit` for the body's polymorphic `e`, type-checks without forcing a
        -- `IO Void -> IO e` transport.  forall e a g. InterruptCause -> Fiber e a -> IO g Unit
        prim "__interruptForkAny"
          (tyV (piI Q0 "e" tType (piI Q0 "a" tType (piI Q0 "g" tType
            (tcon "InterruptCause" ~> CApp Expl (CApp Expl (tcon "Fiber") (CVar 3)) (CVar 2) ~> io (CVar 2) tUnit)))))
      , -- §18.1.5 scheduler yield / interruption point.
        prim "cede" (tyV (io (tcon "Void") tUnit))
      , -- §18.1.2 sandbox/unsandbox: expose / re-hide the full terminal Cause.
        prim "sandbox" (tyV (forallEA
          (io (CVar 1) (CVar 0) ~> io (CApp Expl (tcon "Cause") (CVar 2)) (CVar 1))))
      , prim "unsandbox" (tyV (forallEA
          (io (CApp Expl (tcon "Cause") (CVar 1)) (CVar 0) ~> io (CVar 2) (CVar 1))))
      , -- §18.1.6 re-raise a non-typed runtime cause (interrupt/defect) in any
        -- error context. forall e g a. Cause e -> IO g a
        prim "__reraiseCause"
          (tyV (piI Q0 "e" tType (piI Q0 "g" tType (piI Q0 "a" tType
            (CApp Expl (tcon "Cause") (CVar 2) ~> io (CVar 2) (CVar 1))))))
      , -- §18.1.6 timeout/race kernels. The typed-error injection is done in
        -- the Kappa wrappers (below); these return a structured outcome in any
        -- error context (the outcome is pure data, so the result error is free).
        -- forall e a g. Int(ns) -> IO e a -> IO g (TimeoutOutcome e a). Takes raw
        -- nanoseconds; the `timeout` wrapper unwraps the Duration (std.time below).
        prim "__timeout"
          (tyV (piI Q0 "e" tType (piI Q0 "a" tType (piI Q0 "g" tType
            (tInt ~> io (CVar 3) (CVar 2)
              ~> io (CVar 2) (CApp Expl (CApp Expl (tcon "TimeoutOutcome") (CVar 4)) (CVar 3)))))))
      , -- forall e f a b g. IO e a -> IO f b -> IO g (RaceOutcome e f a b)
        prim "__race"
          (tyV (piI Q0 "e" tType (piI Q0 "f" tType (piI Q0 "a" tType (piI Q0 "b" tType (piI Q0 "g" tType
            (io (CVar 4) (CVar 2) ~> io (CVar 4) (CVar 2)
              ~> io (CVar 2)
                   (CApp Expl (CApp Expl (CApp Expl (CApp Expl (tcon "RaceOutcome") (CVar 6)) (CVar 5)) (CVar 4)) (CVar 3)))))))))
      , -- §18.1.8 explicit supervision scopes.
        prim "newScope" (tyV (io (tcon "Void") (tcon "Scope")))
      , -- forall e a. Scope -> IO e a -> UIO (Fiber e a). The source
        -- usage pass applies the §18.1.4 closed-capture bound to the action.
        prim "forkIn"
          (tyV (piI Q0 "e" tType (piI Q0 "a" tType
            (tcon "Scope" ~> io (CVar 2) (CVar 1)
              ~> io (tcon "Void") (CApp Expl (CApp Expl (tcon "Fiber") (CVar 3)) (CVar 2))))))
      , prim "shutdownScope" (tyV (tcon "Scope" ~> io (tcon "Void") tUnit))
      , -- forall e a. (Scope -> IO e a) -> IO e a
        prim "withScope"
          (tyV (forallEA
            ((tcon "Scope" ~> io (CVar 2) (CVar 1)) ~> io (CVar 2) (CVar 1))))
      , -- §18.1.12 interruption masking surface. `uninterruptible body` runs
        -- `body` with interruption delivery suppressed; a pending interrupt is
        -- re-checked when the region is left. The native backend lowers this to
        -- the OP_UNINTERRUPTIBLE node (krt2_uninterruptible), which raises the
        -- fiber's mask_depth for the body's duration.
        -- forall e a. IO e a -> IO e a
        prim "uninterruptible"
          (tyV (forallEA (io (CVar 1) (CVar 0) ~> io (CVar 2) (CVar 1))))
      , -- §18.1.11 source-level blocking bridge. The native backends lower this
        -- to OP_BLOCKING (krt2_blocking): the fiber parks while the body runs on
        -- the rt-blocking lane. The build DSL's `std.build.blocking` value is a
        -- separate schema-scoped FFI classification token.
        -- forall e a. IO e a -> IO e a
        prim "blocking"
          (tyV (forallEA (io (CVar 1) (CVar 0) ~> io (CVar 2) (CVar 1))))
      , -- §18.1.12 `poll`: an explicit interruption checkpoint that delivers a
        -- pending interrupt even inside a masked region (otherwise returns Unit).
        -- Lowered to the OP_POLL node (krt2_poll). UIO Unit.
        prim "poll" (tyV (io (tcon "Void") tUnit))
      , -- §18.1.12 `mask f`: run `f` with interruption masked, handing it a
        -- `restore` that re-enables interruption for a selected subcomputation.
        -- Lowered to the OP_MASK node (krt2_mask), which applies `f` to the
        -- runtime `restore` closure (rt.c). That closure is a single 1-arg
        -- function, but `restore` is typed RANK-2 — exactly as §18.1.12 mandates
        -- (Spec.md:19063-19066):
        --   restore : forall (x : Type). IO e x -> IO e x
        -- so one captured masking capability applies to sub-actions of arbitrary,
        -- caller-chosen result types within a mask block (the canonical
        -- bracket/withLock idiom; rank-1 instantiated at the mask result `a` could
        -- only restore sub-actions whose type equals `a`). The `x` binder is
        -- RuntimeErased (a type at quantity 0, §1.1.1/§31.2 — types carry no
        -- runtime representation). The conformance fix is NOT a monomorphisation
        -- and NOT a closure-ABI change: the runtime restore stays a single
        -- uniformly-boxed 1-arg function. The surface `mask` (below) wraps that
        -- raw closure as `\act -> __restoreAt raw act` — a worker-backed rank-2
        -- value WITH an erased type slot — so a use-site `restore @x act` lands
        -- its erased type-app on that slot, and the `__restoreAt` PRIM (whose own
        -- type-arg is dropped, §31.2) lowers to a bare `kapp(raw, act)` onto the
        -- 1-arg runtime restore. (Interp: the same adapter, peeling restore's
        -- erased binder before forwarding the action — see Eval.hs vapp / the
        -- `__restoreAt` case in Interp.hs.)
        -- forall e a. ((forall (x : Type). IO e x -> IO e x) -> IO e a) -> IO e a
        prim "__mask"
          (tyV (forallEA
            ( ( piI Q0 "x" tType                                  -- restore : forall (x : Type).
                  (io (CVar 2) (CVar 0) ~> io (CVar 3) (CVar 1))  --   IO e x -> IO e x
                ~> io (CVar 2) (CVar 1) )                         -- -> IO e a  (the body f)
              ~> io (CVar 2) (CVar 1) )))                         -- -> IO e a  (mask's result)
      , -- §18.1.12 internal: the action transformer `mask` hands to its body.
        -- `__restore act` runs `act` at the interruptibility level that held at
        -- the enclosing `mask`'s entry (OP_RESTORE in the runtime). Not a source
        -- name — `mask` supplies it; typed monomorphically here (the rank-2
        -- `restore` binder above is the source-visible polymorphic facet).
        -- forall e a. IO e a -> IO e a
        prim "__restore"
          (tyV (forallEA (io (CVar 1) (CVar 0) ~> io (CVar 2) (CVar 1))))
      , -- §18.1.12 RANK-2 conformance adapter (the CONFORMANCE-FIX core).
        -- The runtime `restore` that `krt2_mask` hands the body is a single
        -- type-erased, uniformly-boxed 1-ARGUMENT closure (rt.c restore_fn): it
        -- has NO runtime slot for a `forall (x:Type).` type binder. But §18.1.12
        -- types `restore` rank-2 so it applies at arbitrary result types. The
        -- surface `mask` therefore does NOT hand its body that raw closure
        -- directly; it wraps it as `\act -> __restoreAt raw act`, a worker-backed
        -- rank-2 value WITH a (kunit-filled) type slot, so the use-site type-app
        -- `kappi(restore, ⟨x⟩)` lands on a real slot rather than the 1-arg
        -- closure (the old "non-function value" crash). `__restoreAt` is a PRIM,
        -- so its own erased implicit type-arg `x` is dropped at the spine (the
        -- §31.2 prim-head erasure); the backends lower `__restoreAt raw act` to a
        -- bare `kapp(raw, act)` (NO `kappi`), reuniting with the 1-arg runtime
        -- closure. This is the whole erasure boundary: no monomorphisation, no
        -- closure-ABI change, no runtime change. (Interp: `raw` is the
        -- `VPrim "__restore"` head, which already erases its implicit args, so
        -- the adapter just forwards `act` to it — interp == C == LLVM.)
        -- forall e x. (forall y. IO e y -> IO e y) -> IO e x -> IO e x
        prim "__restoreAt"
          (tyV (forallEA
            ( piI Q0 "y" tType (io (CVar 2) (CVar 0) ~> io (CVar 3) (CVar 1)) -- raw : forall y. IO e y -> IO e y
              ~> io (CVar 2) (CVar 1)                                          -- act : IO e x
              ~> io (CVar 3) (CVar 2) )))                                      -- -> IO e x
      , -- §18.1.8 monitors. forall e a. Fiber e a -> UIO (Monitor e a)
        prim "monitor"
          (tyV (forallEA
            (CApp Expl (CApp Expl (tcon "Fiber") (CVar 1)) (CVar 0)
              ~> io (tcon "Void") (CApp Expl (CApp Expl (tcon "Monitor") (CVar 2)) (CVar 1)))))
      , prim "awaitMonitor"
          (tyV (forallEA
            (CApp Expl (CApp Expl (tcon "Monitor") (CVar 1)) (CVar 0)
              ~> io (tcon "Void") (CApp Expl (CApp Expl (tcon "Exit") (CVar 2)) (CVar 1)))))
      , prim "demonitor"
          (tyV (forallEA
            (CApp Expl (CApp Expl (tcon "Monitor") (CVar 1)) (CVar 0) ~> io (tcon "Void") tUnit)))
      , -- §18.1.7 fiber-local state. forall a. a -> UIO (FiberRef a)
        prim "newFiberRef"
          (tyV (piI Q0 "a" tType (CVar 0 ~> io (tcon "Void") (CApp Expl (tcon "FiberRef") (CVar 1)))))
      , prim "getFiberRef"
          (tyV (piI Q0 "a" tType (CApp Expl (tcon "FiberRef") (CVar 0) ~> io (tcon "Void") (CVar 1))))
      , prim "setFiberRef"
          (tyV (piI Q0 "a" tType
            (CApp Expl (tcon "FiberRef") (CVar 0) ~> CVar 1 ~> io (tcon "Void") tUnit)))
      , -- forall e a b. FiberRef a -> a -> IO e b -> IO e b
        prim "locallyFiberRef"
          (tyV (piI Q0 "e" tType (piI Q0 "a" tType (piI Q0 "b" tType
            (CApp Expl (tcon "FiberRef") (CVar 1) ~> CVar 2
              ~> io (CVar 4) (CVar 2) ~> io (CVar 5) (CVar 3))))))
      , -- §18.1.7 modifyFiberRef: atomic get-apply-set on the current fiber's
        -- cell (per-fiber, so the read-modify-write is trivially atomic), then
        -- return the NEW value. forall a. FiberRef a -> (a -> a) -> UIO a
        prim "modifyFiberRef"
          (tyV (piI Q0 "a" tType
            (CApp Expl (tcon "FiberRef") (CVar 0) ~> (CVar 1 ~> CVar 2)
              ~> io (tcon "Void") (CVar 2))))
      , prim "throwIO" (tyV (forallEA (CVar 1 ~> io (CVar 2) (CVar 1))))
      , prim "catchIO"
          (tyV (forallEFA
            (io (CVar 2) (CVar 0)
              ~> (CVar 3 ~> io (CVar 3) (CVar 2))
              ~> io (CVar 3) (CVar 2))))
      , prim "finallyIO" (tyV (forallEA (io (CVar 1) (CVar 0) ~> io (CVar 2) tUnit ~> io (CVar 3) (CVar 2))))
      , -- §18.1.4 onExit: run the body, then on EVERY exit run the handler with
        -- the body's reconstructed terminal Exit (a masked finalizer); the body's
        -- result is preserved.  forall e a. IO e a -> (Exit e a -> IO e Unit) -> IO e a
        prim "onExit"
          (tyV (forallEA
            (io (CVar 1) (CVar 0)                                            -- IO e a (body)
              ~> ( CApp Expl (CApp Expl (tcon "Exit") (CVar 2)) (CVar 1)     -- Exit e a
                     ~> io (CVar 3) tUnit )                                  -- -> IO e Unit (handler)
              ~> io (CVar 3) (CVar 2))))                                     -- -> IO e a
      , -- §18.1.4 onInterrupt: like onExit but the handler runs ONLY when the
        -- body exits via interrupt, receiving the InterruptCause.
        -- forall e a. IO e a -> (InterruptCause -> IO e Unit) -> IO e a
        prim "onInterrupt"
          (tyV (forallEA
            (io (CVar 1) (CVar 0)                                            -- IO e a (body)
              ~> ( tcon "InterruptCause" ~> io (CVar 3) tUnit )             -- InterruptCause -> IO e Unit
              ~> io (CVar 3) (CVar 2))))                                     -- -> IO e a
      , -- §28 IO carrier instances delegate to this bind primitive
        prim "ioBind"
          (tyV (piI Q0 "e" tType (piI Q0 "a" tType (piI Q0 "b" tType
            (io (CVar 2) (CVar 1) ~> (CVar 2 ~> io (CVar 4) (CVar 2)) ~> io (CVar 4) (CVar 2))))))
      , -- §18.1.14 'runPure' eliminates a fully handled Eff computation
        prim "runPure" (tyV (piI Q0 "a" tType (effT (CGlob (prel "__effRowNil")) (CVar 0) ~> CVar 1)))
      , -- internal Eff plumbing: monadic bind over the §30.2.2.7 OpCall
        -- tree and the shallow-handler driver (deep reinstalls itself);
        -- their reductions live in 'Kappa.Eval.evalEffPrim'
        prim "__effBind"
          (tyV (piI Q0 "r" (tcon "EffRow") (piI Q0 "a" tType (piI Q0 "b" tType
            (effT (CVar 2) (CVar 1) ~> (CVar 2 ~> effT (CVar 4) (CVar 2)) ~> effT (CVar 4) (CVar 2))))))
      , -- internal: not source-typeable (its applications are built and
        -- typed directly by the elaborator, like a KCore form)
        prim "__handleEff" (tyV (piI Q0 "a" tType (CVar 0)))
      , -- §18.7/§32.2.19 Stage-4a: exit-action frames for Eff do-blocks, so the
        -- §32.2.20 abandonment guarantee (a handler clause that does not resume
        -- runs the captured segment's defers exactly once, masked-LIFO) has
        -- frames to unwind.  `__effDoscope` delimits a do-scope; `__effDefer`
        -- registers an exit action.  They lower (Backend/C) to the runtime's
        -- krt2_doscope / krt2_defer nodes (the same OP_DOSCOPE/OP_DEFER machinery
        -- the IO do-kernel uses); their interpreter reductions are in
        -- 'Kappa.Eval.evalEffPrim'.
        prim "__effDoscope"
          (tyV (piI Q0 "r" (tcon "EffRow") (piI Q0 "a" tType
            (effT (CVar 1) (CVar 0) ~> effT (CVar 2) (CVar 1)))))
      , prim "__effDefer"
          (tyV (piI Q0 "r" (tcon "EffRow")
            (effT (CVar 0) tUnit ~> effT (CVar 1) tUnit)))
      , -- §18.1.13: aborted STM alternative (the `empty` action)
        prim "stmAbort" (tyV (forallEA (io (CVar 1) (CVar 0))))
      , -- §18.1.13 STM transactional state. Single-agent semantics: TVars
        -- are mutable cells and `atomically` runs the transaction directly
        -- (transactions are trivially serializable with no concurrent agent).
        prim "newTVar" (tyV (piI Q0 "a" tType (CVar 0 ~> CApp Expl (tcon "STM") (CApp Expl (tcon "TVar") (CVar 1)))))
      , prim "readTVar" (tyV (piI Q0 "a" tType (CApp Expl (tcon "TVar") (CVar 0) ~> CApp Expl (tcon "STM") (CVar 1))))
      , prim "writeTVar" (tyV (piI Q0 "a" tType (CApp Expl (tcon "TVar") (CVar 0) ~> CVar 1 ~> CApp Expl (tcon "STM") tUnit)))
      , prim "retry" (tyV (piI Q0 "a" tType (CApp Expl (tcon "STM") (CVar 0))))
      , prim "atomically" (tyV (piI Q0 "a" tType (CApp Expl (tcon "STM") (CVar 0) ~> io (tcon "Void") (CVar 1))))
      , -- §18.1.13 STM monad bind/pure: the STM do-notation desugars through the
        -- Monad STM instance (below) into these, which the native backend lowers
        -- to journaled STM_BIND/STM_PURE nodes (stm.c). `check` is a .kp def.
        prim "stmPure" (tyV (piI Q0 "a" tType (CVar 0 ~> CApp Expl (tcon "STM") (CVar 1))))
      , prim "stmBind" (tyV (piI Q0 "a" tType (piI Q0 "b" tType
          (CApp Expl (tcon "STM") (CVar 1)
            ~> (CVar 2 ~> CApp Expl (tcon "STM") (CVar 2))
            ~> CApp Expl (tcon "STM") (CVar 2)))))
      , -- §18.11 one-shot promises. newPromise : forall e a. UIO (Promise e a)
        prim "newPromise" (tyV (piI Q0 "e" tType (piI Q0 "a" tType
          (io (tcon "Void") (CApp Expl (CApp Expl (tcon "Promise") (CVar 1)) (CVar 0))))))
      , -- awaitPromiseExit : forall e a. Promise e a -> UIO (Exit e a)
        -- forall e a r. Promise e a -> IO r (Exit e a) — never fails (the Exit
        -- captures the outcome), so the error channel is free, like __awaitFiber;
        -- this lets `awaitPromise` re-raise into the caller's channel (below).
        prim "awaitPromiseExit" (tyV (piI Q0 "e" tType (piI Q0 "a" tType (piI Q0 "r" tType
          (CApp Expl (CApp Expl (tcon "Promise") (CVar 2)) (CVar 1)
            ~> io (CVar 1) (CApp Expl (CApp Expl (tcon "Exit") (CVar 3)) (CVar 2)))))))
      , -- awaitPromise (Promise e a -> IO e a) is a .kp def over awaitPromiseExit
        -- (see the prelude library below), mirroring `join` for fibers.
        -- completePromise : forall e a. Promise e a -> Exit e a -> UIO Bool
        prim "completePromise" (tyV (piI Q0 "e" tType (piI Q0 "a" tType
          (CApp Expl (CApp Expl (tcon "Promise") (CVar 1)) (CVar 0)
            ~> CApp Expl (CApp Expl (tcon "Exit") (CVar 2)) (CVar 1) ~> io (tcon "Void") tBool))))
      , -- §18.11 non-blocking peek: poll returns Some Exit iff the promise is
        -- completed (None otherwise) WITHOUT parking; isDone returns the Bool.
        -- pollPromise : forall e a. Promise e a -> UIO (Option (Exit e a))
        prim "pollPromise" (tyV (piI Q0 "e" tType (piI Q0 "a" tType
          (CApp Expl (CApp Expl (tcon "Promise") (CVar 1)) (CVar 0)
            ~> io (tcon "Void")
                 (CApp Expl (tcon "Option")
                   (CApp Expl (CApp Expl (tcon "Exit") (CVar 2)) (CVar 1)))))))
      , -- isDonePromise : forall e a. Promise e a -> UIO Bool
        prim "isDonePromise" (tyV (piI Q0 "e" tType (piI Q0 "a" tType
          (CApp Expl (CApp Expl (tcon "Promise") (CVar 1)) (CVar 0) ~> io (tcon "Void") tBool))))
      , -- §18.1 monotonic time: the ONLY irreducible time primitives — read the
        -- agent clock + sleep — both over raw nanosecond Ints. Duration/Instant
        -- construction + arithmetic + the typed wrappers live in the std.time
        -- prelude fragment below (ordinary Kappa over Int). sleepUntil is derived.
        prim "__nowNanos" (tyV (io (tcon "Void") tInt))
      , prim "__sleepForNanos" (tyV (tInt ~> io (tcon "Void") tUnit))
      , -- §18.1.10 fiber identity: the runtime delivers the fiber's stable
        -- integer id; the FiberId wrapper (MkFiberId) is applied in the
        -- std.prelude fragment below, exactly as Instant wraps __nowNanos.
        -- __currentFiberId : UIO Integer. __fiberId : forall e a. Fiber e a -> UIO Integer.
        prim "__currentFiberId" (tyV (io (tcon "Void") tInt))
      , prim "__fiberId"
          (tyV (piI Q0 "e" tType (piI Q0 "a" tType
            (CApp Expl (CApp Expl (tcon "Fiber") (CVar 1)) (CVar 0) ~> io (tcon "Void") tInt))))
      , -- §20.2 range enumeration: '__rangeEnum lo hi exclusive' lists the
        -- elements of a range in ascending order (empty when lo > hi).
        -- Reduces for the §28.2.3 Rangeable element types whose runtime
        -- values are Int/Nat literals or Unicode scalars.
        prim "__rangeEnum" (tyV (piI Q0 "v" tType (CVar 0 ~> CVar 1 ~> tBool ~> listT (CVar 3))))
      , -- §20 collection/query plumbing (the §20.10.11 as-if list model)
        prim "__quantityOfNat" (tyV (tNat ~> tcon "Quantity"))
      , prim "__queryFromList"
          (tyV (piI Q0 "m" (tcon "QueryMode") (piI Q0 "q" (tcon "Quantity") (piI Q0 "a" tType (listT (CVar 0) ~> queryT (CVar 3) (CVar 2) (CVar 1))))))
      , prim "__queryToList"
          (tyV (piI Q0 "m" (tcon "QueryMode") (piI Q0 "q" (tcon "Quantity") (piI Q0 "a" tType (queryT (CVar 2) (CVar 1) (CVar 0) ~> listT (CVar 1))))))
      , prim "__setFromList" (tyV (piI Q0 "a" tType (listT (CVar 0) ~> setT (CVar 1))))
      , prim "__setToList" (tyV (piI Q0 "a" tType (setT (CVar 0) ~> listT (CVar 1))))
      , prim "__arrayFromList" (tyV (piI Q0 "a" tType (listT (CVar 0) ~> arrayT (CVar 1))))
      , prim "__arrayToList" (tyV (piI Q0 "a" tType (arrayT (CVar 0) ~> listT (CVar 1))))
      , -- §28.2 total in-bounds index: traps at runtime if out of bounds.
        -- Codomain 'CVar 2' = the element type 'a': the two '~>' arrows (Array a,
        -- Int) each introduce a binder, so 'a' (bound by 'piI') sits at index 2 in
        -- the codomain — 'CVar 1' would wrongly name the Int-argument binder.
        prim "__arrayIndexUnsafe" (tyV (piI Q0 "a" tType (arrayT (CVar 0) ~> tInt ~> CVar 2)))
      , -- §28.2 unsafeAssertProof escape hatch: an opaque inhabitant of
        -- the asserted proposition (erased; never inspected at runtime)
        prim "__unsafeAssertProof" (tyV (piI Q0 "p" tType (CVar 0)))
      , -- §28.2 proof-helper internals. '__absurd' eliminates Void (it is
        -- never applied to a real value). '__transport' is the identity
        -- on a proof-irrelevantly equal value: 'subst'/'pathInd' carry
        -- the runtime payload through unchanged. '__eqProof' inhabits an
        -- erased equality proposition.
        prim "__absurd" (tyV (piI Q0 "a" tType (tcon "Void" ~> CVar 1)))
      , prim "__transport" (tyV (piI Q0 "from" tType (piI Q0 "to" tType (CVar 1 ~> CVar 1))))
      , prim "__eqProof" (tyV (piI Q0 "t" tType (CVar 0)))
      , prim "__mapFromEntries"
          (tyV (piI Q0 "k" tType (piI Q0 "v" tType (listT (entryT (CVar 1) (CVar 0)) ~> mapT (CVar 2) (CVar 1)))))
      , prim "__mapToList"
          (tyV (piI Q0 "k" tType (piI Q0 "v" tType (mapT (CVar 1) (CVar 0) ~> listT (entryT (CVar 2) (CVar 1))))))
      , prim "__ioNewRef" (tyV (forallEA (CVar 0 ~> io (CVar 2) (refT (CVar 1)))))
      , prim "__ioReadRef" (tyV (forallEA (refT (CVar 0) ~> io (CVar 2) (CVar 1))))
      , prim "__ioWriteRef" (tyV (forallEA (refT (CVar 0) ~> CVar 1 ~> io (CVar 3) tUnit)))
      , -- MUTABLE-ARRAY-DESIGN §4.1: the boxed mutable-array primitives. The
        -- element type @a@ is a Q0-erased @forall@ slot, dropped before codegen,
        -- so it NEVER reaches the kpf_* symbol (the erasure-safety contract).
        -- The index is a plain Int (the surface passes @natToInt i@); the array
        -- carries its own length.  __arrayLen is PURE (no IO).
        prim "__newArray" (tyV (forallEA (tNat ~> CVar 1 ~> io (CVar 3) (arrayBufT (CVar 2)))))  -- Nat -> a -> IO e (__ArrayBuf a)
      , prim "__arrayRead" (tyV (forallEA (arrayBufT (CVar 0) ~> tInt ~> io (CVar 3) (CVar 2))))  -- __ArrayBuf a -> Int -> IO e a
      , prim "__arrayWrite" (tyV (forallEA (arrayBufT (CVar 0) ~> tInt ~> CVar 2 ~> io (CVar 4) tUnit)))  -- __ArrayBuf a -> Int -> a -> IO e Unit
      , prim "__arrayLen" (tyV (piI Q0 "a" tType (arrayBufT (CVar 0) ~> tNat)))  -- __ArrayBuf a -> Nat (pure)
      , -- §21.5/§21.9 elaboration-time reflection and diagnostics
        -- (interpreted by the elaborator's §21.8 Elab runner; stuck as
        -- values everywhere else)
        prim "renderSyntax" (tyV (piI Q0 "t" (tTypeAt 0) (synT (CVar 0) ~> elabT tStr)))
      , prim "syntaxOrigin" (tyV (piI Q0 "t" (tTypeAt 0) (synT (CVar 0) ~> elabT tOrigin)))
      , prim "normalizeSyntax" (tyV (piI Q0 "t" (tTypeAt 0) (synT (CVar 0) ~> elabT (synT (CVar 1)))))
      , prim "withSyntaxOrigin" (tyV (piI Q0 "t" (tTypeAt 0) (tOrigin ~> synT (CVar 1) ~> elabT (synT (CVar 2)))))
      , prim "whnfSyntax" (tyV (piI Q0 "t" (tTypeAt 0) (synT (CVar 0) ~> elabT (synT (CVar 1)))))
      , -- §21.6 'typeOfSyntax': the type of a quoted expression, reified as
        -- 'Syntax Type' (forall t. Syntax t -> Elab (Syntax Type))
        prim "typeOfSyntax" (tyV (piI Q0 "t" (tTypeAt 0) (synT (CVar 0) ~> elabT (synT tType))))
      , -- §21.6 semantic-reflection convenience queries (elaboration-time;
        -- interpreted by 'Kappa.Check.runElab')
        prim "defEqSyntax"
          (tyV (piI Q0 "a" (tTypeAt 0) (piI Q0 "b" (tTypeAt 1) (synT (CVar 1) ~> synT (CVar 1) ~> elabT tBool))))
      , prim "headSymbolSyntax"
          (tyV (piI Q0 "t" (tTypeAt 0) (synT (CVar 0) ~> elabT (optionT (tcon "Symbol")))))
      , -- §21.6 'sameSymbol' compares resolved declaration identity
        prim "sameSymbol" (tyV (tcon "Symbol" ~> tcon "Symbol" ~> tBool))
      , -- §23 staged code: '.< e >.' elaborates to '__codeQuote e' (the
        -- interpreter models generative code by its present-stage value,
        -- §23.3 lift-based cross-stage persistence) and '.~c' to
        -- '__codeEscape c'
        prim "__codeQuote" (tyV (piI Q0 "t" tType (CVar 0 ~> codeT (CVar 1))))
      , prim "__codeEscape" (tyV (piI Q0 "t" tType (codeT (CVar 0) ~> CVar 1)))
      , -- §23.4-§23.6 closing and running staged code (every Code value
        -- this interpreter constructs is scope-safe by construction)
        prim "closeCode"
          (tyV (piI Q0 "t" tType (codeT (CVar 0) ~> CApp Expl (tcon "Option") (closedCodeT (CVar 1)))))
      , prim "genlet" (tyV (piI Q0 "t" tType (codeT (CVar 0) ~> codeT (CVar 1))))
      , prim "runCode" (tyV (piI Q0 "t" tType (closedCodeT (CVar 0) ~> io (tcon "Void") (CVar 1))))
      , prim "warnElab" (tyV (tStr ~> elabT tUnit))
      , prim "failElab" (tyV (piI Q0 "a" tType (tStr ~> elabT (CVar 1))))
      , prim "failElabWith" (tyV (piI Q0 "a" tType (tStr ~> tStr ~> listT tOrigin ~> elabT (CVar 3))))
      , prim "warnElabWith" (tyV (tStr ~> tStr ~> listT tOrigin ~> elabT tUnit))
      , -- §22 derivation-shape internals (wrapped by std.deriving.shape;
        -- the type argument is passed explicitly so the elaboration-time
        -- evaluator can see it)
        prim "__shapeInspectAdt"
          (tyV (pi0 "a" (CSort (LParam 0)) (synT (CSort (LParam 1)) ~> elabT (CApp Expl (tconShapeAt "AdtShape" [LParam 0]) (CVar 1)))))
      , prim "__shapeInspectRecord"
          (tyV (pi0 "a" (CSort (LParam 0)) (synT (CSort (LParam 1)) ~> elabT (CApp Expl (tconShapeAt "RecordShape" [LParam 0]) (CVar 1)))))
      , prim "__shapeRequireFieldInstances"
          (tyV
             (pi0 "tc" (piM Parametric Expl Q0 False "x" (CSort (LParam 0)) (CSort (LParam 1)))
                (pi0 "a" (CSort (LParam 2))
                   (CApp Expl (tconShapeAt "AdtShape" [LParam 2]) (CVar 0) ~> elabT tUnit))))
      , prim "__shapeMatchAdt"
          (tyV
             (piI Q0 "a" tType (piI Q0 "r" tType
                (CApp Expl (tconShapeAt "AdtShape" [LParam 0]) (CVar 1)
                   ~> synT (CVar 2)
                   ~> ((tconShapeAt "ShapeConstructor" [] ~> listT (tconShapeAt "BoundField" []) ~> elabT (synT (CVar 4))) ~> elabT (synT (CVar 3)))))))
      , prim "__shapeMatchAdt2"
          (tyV
             (piI Q0 "a" tType (piI Q0 "r" tType
                (CApp Expl (tconShapeAt "AdtShape" [LParam 0]) (CVar 1)
                   ~> synT (CVar 2)
                   ~> synT (CVar 3)
                   ~> ((tconShapeAt "ShapeConstructor" [] ~> listT (tconShapeAt "BoundFieldPair" []) ~> elabT (synT (CVar 5)))
                         ~> ((tconShapeAt "ShapeConstructor" [] ~> tconShapeAt "ShapeConstructor" [] ~> elabT (synT (CVar 6)))
                               ~> elabT (synT (CVar 5))))))))
      , prim "__stringSyntax" (tyV (tStr ~> elabT (synT tStr)))
      , prim "__natSyntax" (tyV (tNat ~> elabT (synT tNat)))
      , prim "__boolSyntax" (tyV (tBool ~> elabT (synT tBool)))
      , prim "__unitSyntax" (tyV (elabT (synT tUnit)))
      ]

-- Evaluate a closed type term without globals (only built-in structure).
evalClosed :: Term -> Value
evalClosed = go []
  where
    go env = \case
      CVar i -> lookupEnv i env
      CGlobal g universes -> VGlobal g universes []
      CPiEvidenceM mode formation ic q brw n assumption origin a b ->
        VPiEvidenceM mode formation ic q brw n assumption origin (go env a) (Closure env b)
      CApp ic f a -> app (go env f) ic (go env a)
      CSort n -> VSort n
      CRecordT fs -> VRecordT [(n, go env t) | (n, t) <- fs]
      t -> VPrim (T.pack (show t)) []
    app (VGlobI g universes sp) ic a =
      VGlobI g universes (sp ++ [(ic, a)])
    app f _ _ = f

-- | Elaborate the compiler-seeded prelude's bare universe syntax to the current
-- §11.1.2.3A representation. Each parametric bare-@Type@ binder gets a hidden
-- level in deterministic telescope order. A saturated seeded type-constructor
-- reference reuses the structurally known classifier levels of its arguments,
-- exactly as ordinary source elaboration does; genuinely unknown or partial
-- references receive fresh levels. Explicit 'CGlobI' spines and explicit
-- source @Type0@ remain fixed.
floatBuiltinUniverses :: Term -> Term
floatBuiltinUniverses source = evalState (go [] source) nextParam
  where
    existing = levelParamsOfTerm source
    nextParam = case existing of
      [] -> 0
      _ -> maximum existing + 1

    freshSort :: State Int Term
    freshSort = CSort <$> freshLevel

    freshLevel :: State Int Level
    freshLevel = do
      index <- get
      put (index + 1)
      pure (LParam index)

    freshLevels :: Int -> State Int [Level]
    freshLevels count = replicateM count freshLevel

    go env = \case
      CGlobal global [] -> do
        universes <- freshLevels (Map.findWithDefault 0 global seededTypeUniverseArities)
        pure (CGlobal global universes)
      CGlobal global universes -> pure (CGlobal global universes)
      CPiEvidenceM mode formation ic q borrowed name assumption origin domain codomain -> do
        domain' <- case (mode, domain) of
          (Parametric, CSort LZero) -> freshSort
          _ -> go env domain
        let localClassifier = case domain' of
              CSort level -> Just level
              _ -> Nothing
        CPiEvidenceM mode formation ic q borrowed name assumption origin domain'
          <$> go (localClassifier : env) codomain
      CLamM mode ic q name body ->
        CLamM mode ic q name <$> go (Nothing : env) body
      application@CApp {} -> do
        let (headTerm, arguments) = collectApplications application
        convertedArguments <-
          mapM
            (\(icit, argument) -> (icit,) <$> go env argument)
            arguments
        convertedHead <- case headTerm of
          CGlobal global [] -> do
            let arity = Map.findWithDefault 0 global seededTypeUniverseArities
            known <-
              mapM
                (\(_, argument) ->
                   maybe freshLevel pure
                     (typeArgumentClassifier env argument))
                (take arity convertedArguments)
            missing <- freshLevels (arity - length known)
            pure (CGlobal global (known ++ missing))
          _ -> go env headTerm
        pure
          (foldl
             (\function (icit, argument) -> CApp icit function argument)
             convertedHead
             convertedArguments)
      CRecordTQ fields -> CRecordTQ <$> traverse (traverse (go env)) fields
      CRecordV fields -> CRecordV <$> traverse (traverse (go env)) fields
      CProjM mode inner field -> (\inner' -> CProjM mode inner' field) <$> go env inner
      CProjAtM mode inner field index -> (\inner' -> CProjAtM mode inner' field index) <$> go env inner
      CVariantT members -> CVariantT <$> traverse (go env) members
      CSealE fields inner -> CSealE fields <$> go env inner
      CSigT fields inner -> CSigT fields <$> go env inner
      CThunkE inner suspensionType ->
        CThunkE <$> go env inner <*> traverse (go env) suspensionType
      CLazyE inner suspensionType ->
        CLazyE <$> go env inner <*> traverse (go env) suspensionType
      CForceE inner resultType ->
        CForceE <$> go env inner <*> traverse (go env) resultType
      other -> pure other

    collectApplications = collect []
      where
        collect arguments (CApp icit function argument) =
          collect ((icit, argument) : arguments) function
        collect arguments headTerm = (headTerm, arguments)

    typeArgumentClassifier env = \case
      CVar index -> case drop index env of
        level : _ -> level
        [] -> Nothing
      -- A universe code is itself classified one level higher.
      CSort level -> Just (levelSucc level)
      -- A bare nominal appearing in an authenticated type-argument position
      -- of a compiler-seeded signature denotes its principal Type0 result.
      -- Higher sorts are represented explicitly by 'CSort'; this pass never
      -- classifies arbitrary user terms from a readable global name.
      CGlobal _ _ -> Just LZero
      application@CApp {} ->
        let (headTerm, _) = collectApplications application
         in case headTerm of
              CGlobal _ _ -> Just LZero
              _ -> Nothing
      CUniverseLift _ upper _ _ -> Just upper
      _ -> Nothing


-- | Bootstrap fragment for the canonical @std.typelevel@ module. It is
-- checked before @std.prelude@ because prelude signatures mention
-- 'TypeLevel'; the representation depends only on the compiler-seeded 'Nat'
-- carrier. The operations are checked later by 'stdTypeLevelSource' after the
-- ordinary prelude traits and constructors are available.
stdTypeLevelBootstrapSource :: Text
stdTypeLevelBootstrapSource =
  T.unlines
    [ "module std.typelevel"
    , ""
    , "opaque data TypeLevel : Type0 ="
    , "    Level"
    , "        (omegaCoefficient : Nat)"
    , "        (finiteRemainder : Nat)"
    ]

-- | The ordinary source implementation of the canonical TypeLevel algebra
-- (§11.1.2.2). These definitions are opaque only after this module is sealed;
-- while checking the module, their bodies and the hidden 'Level' constructor
-- are available through the same ordinary elaborator used for user code.
stdTypeLevelSource :: Text
stdTypeLevelSource =
  T.unlines
    [ "module std.typelevel"
    , ""
    , "typeLevelZero : TypeLevel"
    , "opaque let typeLevelZero = Level 0 0"
    , ""
    , "typeLevelOne : TypeLevel"
    , "opaque let typeLevelOne = Level 0 1"
    , ""
    , "typeLevelOmega : TypeLevel"
    , "opaque let typeLevelOmega = Level 1 0"
    , ""
    , "typeLevelFromInteger : Nat -> TypeLevel"
    , "opaque let typeLevelFromInteger n = Level 0 n"
    , ""
    , "typeLevelSucc : TypeLevel -> TypeLevel"
    , "opaque let typeLevelSucc x ="
    , "    match x"
    , "    case Level c n -> Level c (n + 1)"
    , ""
    , "typeLevelAdd : TypeLevel -> TypeLevel -> TypeLevel"
    , "opaque let typeLevelAdd x y ="
    , "    match (x, y)"
    , "    case (Level xc xn, Level yc yn) -> Level (xc + yc) (xn + yn)"
    , ""
    , "typeLevelCompare : TypeLevel -> TypeLevel -> Ordering"
    , "opaque let typeLevelCompare x y ="
    , "    match (x, y)"
    , "    case (Level xc xn, Level yc yn) ->"
    , "        match compare xc yc"
    , "        case LT -> LT"
    , "        case GT -> GT"
    , "        case EQ -> compare xn yn"
    , ""
    , "typeLevelMax : TypeLevel -> TypeLevel -> TypeLevel"
    , "opaque let typeLevelMax x y ="
    , "    match typeLevelCompare x y"
    , "    case LT -> y"
    , "    case EQ -> x"
    , "    case GT -> x"
    , ""
    , "omega : TypeLevel"
    , "let omega = typeLevelOmega"
    , ""
    , "omegaTypeLevel : TypeLevel"
    , "let omegaTypeLevel = typeLevelOmega"
    , ""
    , "instance Zero TypeLevel ="
    , "    let zero = typeLevelZero"
    , ""
    , "instance One TypeLevel ="
    , "    let one = typeLevelOne"
    , ""
    , "instance FromInteger TypeLevel ="
    , "    let fromInteger n = typeLevelFromInteger n"
    , ""
    , "instance Successor TypeLevel ="
    , "    let succ x = typeLevelSucc x"
    , ""
    , "instance Add TypeLevel ="
    , "    let add x y = typeLevelAdd x y"
    , ""
    , "instance Max TypeLevel ="
    , "    let max x y = typeLevelMax x y"
    , ""
    , "instance Eq TypeLevel ="
    , "    let (==) x y ="
    , "        match typeLevelCompare x y"
    , "        case EQ -> True"
    , "        case LT -> False"
    , "        case GT -> False"
    , ""
    , "instance Ord TypeLevel ="
    , "    let compare x y = typeLevelCompare x y"
    , ""
    , "instance IsSet TypeLevel"
    , ""
    , "trait Monotone (ordinary 0 f : TypeLevel -> TypeLevel) ="
    , "    monotone : (x : TypeLevel) -> (y : TypeLevel) -> (@ordinary 0 p : x <= y) -> (f x <= f y) = True"
    , ""
    , "typeLevelAddAssoc : forall (x : TypeLevel) (y : TypeLevel) (z : TypeLevel). add (add x y) z = add x (add y z)"
    , "let typeLevelAddAssoc x y z = refl"
    , "typeLevelAddComm : forall (x : TypeLevel) (y : TypeLevel). add x y = add y x"
    , "let typeLevelAddComm x y = refl"
    , "typeLevelAddZero : forall (x : TypeLevel). add x typeLevelZero = x"
    , "let typeLevelAddZero x = refl"
    , "typeLevelSuccIsAddOne : forall (x : TypeLevel). succ x = add x typeLevelOne"
    , "let typeLevelSuccIsAddOne x = refl"
    , "typeLevelSuccStrict : forall (x : TypeLevel). (x < succ x) = True"
    , "let typeLevelSuccStrict x = refl"
    , "typeLevelLtIffSuccLe : forall (x : TypeLevel) (y : TypeLevel). (x < y) = (succ x <= y)"
    , "let typeLevelLtIffSuccLe x y = refl"
    , "typeLevelAddMonotone : forall (x : TypeLevel) (y : TypeLevel) (z : TypeLevel). (ordinary 0 p : (x <= y) = True) -> (add z x <= add z y) = True"
    , "let typeLevelAddMonotone x y z p = refl"
    , "typeLevelAddStrictMonotone : forall (x : TypeLevel) (y : TypeLevel) (z : TypeLevel). (ordinary 0 p : (x < y) = True) -> (add z x < add z y) = True"
    , "let typeLevelAddStrictMonotone x y z p = refl"
    , "typeLevelMaxAssoc : forall (x : TypeLevel) (y : TypeLevel) (z : TypeLevel). max (max x y) z = max x (max y z)"
    , "let typeLevelMaxAssoc x y z = refl"
    , "typeLevelMaxComm : forall (x : TypeLevel) (y : TypeLevel). max x y = max y x"
    , "let typeLevelMaxComm x y = refl"
    , "typeLevelMaxIdempotent : forall (x : TypeLevel). max x x = x"
    , "let typeLevelMaxIdempotent x = refl"
    , "typeLevelFiniteBelowOmega : forall (n : Nat). (typeLevelFromInteger n < typeLevelOmega) = True"
    , "let typeLevelFiniteBelowOmega n = refl"
    , "typeLevelOmegaPlusOmega : (typeLevelOmega < add typeLevelOmega typeLevelOmega) = True"
    , "let typeLevelOmegaPlusOmega = refl"
    , "typeLevelOnePlusOmega : add typeLevelOne typeLevelOmega = add typeLevelOmega typeLevelOne"
    , "let typeLevelOnePlusOmega = refl"
    , "typeLevelAddLeftZero : forall (x : TypeLevel). add typeLevelZero x = x"
    , "let typeLevelAddLeftZero x = refl"
    , "typeLevelAddMonotoneRight : forall (x : TypeLevel) (y : TypeLevel) (z : TypeLevel). (ordinary 0 p : (x <= y) = True) -> (add x z <= add y z) = True"
    , "let typeLevelAddMonotoneRight x y z p = refl"
    , "addRightMonotone : forall (k : TypeLevel). (x : TypeLevel) -> (y : TypeLevel) -> (@ordinary 0 p : (x <= y) = True) -> (add k x <= add k y) = True"
    , "let addRightMonotone k x y p = typeLevelAddMonotone @x @y @k p"
    , "instance Monotone (add k) ="
    , "    let monotone = addRightMonotone"
    , ""
    , "instance AdditiveMonoid TypeLevel ="
    , "    let addAssoc = typeLevelAddAssoc"
    , "    let addLeftIdentity = typeLevelAddLeftZero"
    , "    let addRightIdentity = typeLevelAddZero"
    , "instance CommutativeAdditiveMonoid TypeLevel ="
    , "    let addCommutative = typeLevelAddComm"
    , "instance OrderedAdditive TypeLevel ="
    , "    let addMonotoneLeft = typeLevelAddMonotone"
    , "    let addMonotoneRight = typeLevelAddMonotoneRight"
    , "instance JoinSemilattice TypeLevel ="
    , "    let joinAssoc = typeLevelMaxAssoc"
    , "    let joinCommutative = typeLevelMaxComm"
    , "    let joinIdempotent = typeLevelMaxIdempotent"
    ]

-- | The bounded package families are checked after the ordinary TypeLevel
-- operations and their standard dictionaries have entered the same module's
-- export environment. Data headers are predeclared before term signatures in
-- a source fragment, so keeping this as a separate @std.typelevel@ fragment
-- makes the dependency explicit without changing any public identity.
stdTypeLevelPackagesSource :: Text
stdTypeLevelPackagesSource =
  T.unlines
    [ "module std.typelevel"
    , ""
    , "type LevelLe (lo : TypeLevel) (hi : TypeLevel) : Type ="
    , "    (lo <= hi) = True"
    , ""
    , "type LevelLt (lo : TypeLevel) (hi : TypeLevel) : Type ="
    , "    (lo < hi) = True"
    , ""
    , "data TypeBelow.{u} : Type u ="
    , "    PackTypeBelow"
    , "        (ordinary 0 level : TypeLevel)"
    , "        (@0 bound : level < u)"
    , "        (ordinary 0 T : Type level)"
    , ""
    , "data TypeAtMost.{u} : Type (typeLevelSucc u) ="
    , "    PackTypeAtMost"
    , "        (ordinary 0 level : TypeLevel)"
    , "        (@0 bound : level <= u)"
    , "        (ordinary 0 T : Type level)"
    ]

-- | Embedded @std.prelude@ source (§28.2 subset; see SPEC_COMPLIANCE.md).
preludeSource :: Text
preludeSource =
  T.unlines
    [ -- §11.4.1: standard equality is an ordinary source declaration. Its
      -- explicit schema and parametric endpoints follow the same elaboration
      -- path as every user-defined universe-polymorphic data family.
      "data (=).{u}"
    , "    (@parametric 0 A : Type u)"
    , "    (parametric 0 x : A)"
    , "    (parametric 0 y : A)"
    , "    : Type u ="
    , "    refl : (=) x x"
    , ""
    , "data Void : Type"
    , ""
    , "data Unit : Type ="
    , "    Unit"
    , ""
    , "data Bool : Type ="
    , "    True"
    , "    False"
    , ""
    , "data Ordering : Type ="
    , "    LT"
    , "    EQ"
    , "    GT"
    , ""
    , -- §18.1/§29 std.time fragment: Duration/Instant are ordinary opaque data
      -- over a signed-nanosecond Int; all construction/arithmetic/compare is
      -- plain Kappa. Only __nowNanos (clock) + __sleepForNanos (timer) are prims.
      "opaque data Duration : Type ="
    , "    Duration Integer"
    , ""
    , "opaque data Instant : Type ="
    , "    Instant Integer"
    , ""
    , "durationNanos : Duration -> Integer"
    , "let durationNanos d ="
    , "    match d"
    , "    case Duration a -> a"
    , ""
    , "instantNanos : Instant -> Integer"
    , "let instantNanos i ="
    , "    match i"
    , "    case Instant a -> a"
    , ""
    , "nanos : Integer -> Duration"
    , "let nanos n = Duration n"
    , "micros : Integer -> Duration"
    , "let micros n = Duration (mulInt n 1000)"
    , "millis : Integer -> Duration"
    , "let millis n = Duration (mulInt n 1000000)"
    , "seconds : Integer -> Duration"
    , "let seconds n = Duration (mulInt n 1000000000)"
    , "minutes : Integer -> Duration"
    , "let minutes n = Duration (mulInt n 60000000000)"
    , ""
    , "durationAdd : Duration -> Duration -> Duration"
    , "let durationAdd x y = Duration (addInt (durationNanos x) (durationNanos y))"
    , "durationSub : Duration -> Duration -> Duration"
    , "let durationSub x y = Duration (subInt (durationNanos x) (durationNanos y))"
    , "durationCompare : Duration -> Duration -> Ordering"
    , "let durationCompare x y ="
    , "    if ltInt (durationNanos x) (durationNanos y) then LT"
    , "    elif eqInt (durationNanos x) (durationNanos y) then EQ"
    , "    else GT"
    , ""
    , "instantAdd : Instant -> Duration -> Instant"
    , "let instantAdd i d = Instant (addInt (instantNanos i) (durationNanos d))"
    , "instantDiff : Instant -> Instant -> Duration"
    , "let instantDiff x y = Duration (subInt (instantNanos x) (instantNanos y))"
    , ""
    , -- typed timer wrappers over the raw-ns prims (sleepUntil is derived).
      "nowMonotonic : IO Void Instant"
    , "let nowMonotonic = ioBind __nowNanos (\\n -> ioPure (Instant n))"
    , "sleepFor : Duration -> IO Void Unit"
    , "let sleepFor d = __sleepForNanos (durationNanos d)"
    , "sleepUntil : Instant -> IO Void Unit"
    , "let sleepUntil i = ioBind nowMonotonic (\\now -> sleepFor (instantDiff i now))"
    , ""
    , "data Option (0 a : Type) : Type ="
    , "    None"
    , "    Some a"
    , ""
    , "data Result (0 e : Type) (0 a : Type) : Type ="
    , "    Ok a"
    , "    Err e"
    , ""
    , "data List (0 a : Type) : Type ="
    , "    Nil"
    , "    (::) (head : a) (tail : List a)"
    , ""
    , -- §29.5 length-indexed array. The 'Nat' index is a phantom length
      -- witness (the element sequence is the as-if-list model of §20.10.11);
      -- the index is fixed at construction (e.g. `bytesAsSizedArray` packs
      -- it to `bytesLength`), which is how the §29.5 propositional-length
      -- guarantee is carried.
      "data SizedArray (n : Nat) (0 a : Type) : Type ="
    , "    MkSizedArray (elements : List a)"
    , ""
    , -- §12.4.3 canonical zipper: an opened owned focus plus a linear
      -- filler back to the whole
      "data Zipper (0 whole : Type) (0 focus : Type) (0 replace : Type) : Type ="
    , "    Zipper (focus : focus) (1 fill : replace -> whole)"
    , ""
    , "type Int = Integer"
    , "type Float = Double"
    , "type Char = UnicodeScalar" -- sanctioned alias (§28.5)
    , "type UIO (0 a : Type) = IO Void a"
    , "type __IORef (0 a : Type) = Ref a"
    , ""
    , -- §28.2 canonical Nat eliminators.  Recursion is deliberately on the
      -- first argument, making the left equations definitional while the
      -- commuted/right equations require explicit algebraic evidence.
      "natAdd : Nat -> Nat -> Nat"
    , "let natAdd left right ="
    , "    match left"
    , "    case Nat.Zero -> right"
    , "    case Nat.Succ predecessor -> Nat.Succ (natAdd predecessor right)"
    , ""
    , "natMultiply : Nat -> Nat -> Nat"
    , "let natMultiply left right ="
    , "    match left"
    , "    case Nat.Zero -> Nat.Zero"
    , "    case Nat.Succ predecessor -> natAdd right (natMultiply predecessor right)"
    , ""
    , "natCompare : Nat -> Nat -> Ordering"
    , "let natCompare left right ="
    , "    match left"
    , "    case Nat.Zero ->"
    , "        match right"
    , "        case Nat.Zero -> EQ"
    , "        case Nat.Succ _ -> LT"
    , "    case Nat.Succ leftPredecessor ->"
    , "        match right"
    , "        case Nat.Zero -> GT"
    , "        case Nat.Succ rightPredecessor -> natCompare leftPredecessor rightPredecessor"
    , ""
    , "not : Bool -> Bool"
    , "let not b = if b then False else True"
    , ""
    , "(&&) : Bool -> Thunk Bool -> Bool"
    , "let (&&) lhs rhs = if lhs then force rhs else False"
    , ""
    , "(||) : Bool -> Thunk Bool -> Bool"
    , "let (||) lhs rhs = if lhs then True else force rhs"
    , ""
    , -- §28.2 n-ary boolean folds over a `List Bool`. `and` is the conjunction
      -- (True over the empty list), `or` the disjunction (False over empty);
      -- both short-circuit. Unlike `(&&)`/`(||)` these are nameable first-class
      -- terms (no Thunk in their signature), so `and`/`or` may be passed around.
      "and : List Bool -> Bool"
    , "let and xs ="
    , "    match xs"
    , "    case Nil -> True"
    , "    case b :: rest -> if b then and rest else False"
    , ""
    , "or : List Bool -> Bool"
    , "let or xs ="
    , "    match xs"
    , "    case Nil -> False"
    , "    case b :: rest -> if b then True else or rest"
    , ""
    , -- §28.2 `force` as a first-class term: the keyword `force e` evaluates a
      -- suspension in place, but the bare name `force` is also a nameable value
      -- (e.g. `map force thunks`). The body uses the keyword form (it is applied
      -- to the argument `t`), so this binds the NAME `force` to that function.
      "force : forall (a : Type). Thunk a -> a"
    , "let force t = force t"
    , ""
    , -- §11.4/§14.4 proof-classification traits.  These precede Eq because
      -- Eq's revised contract carries IsSet as an ordinary supertrait.
      "trait IsEmpty (0 t : Type) ="
    , "    absurdT : t -> Void"
    , ""
    , "trait IsContr (0 t : Type) ="
    , "    center : t"
    , "    contract : (x : t) -> center = x"
    , ""
    , "trait IsSubsingleton (0 t : Type) ="
    , "    allEqual : (x : t) -> (y : t) -> x = y"
    , ""
    , "trait IsSubsingleton p => IsProp (0 p : Type)"
    , ""
    , "trait IsSet (0 a : Type) ="
    , "    pathIsProp : forall (x : a) (y : a). IsProp (x = y)"
    , "    let pathIsProp @x @y = __eqProof"
    , ""
    , "trait IsGroupoid (0 a : Type) ="
    , "    pathIsSet : forall (x : a) (y : a). IsSet (x = y)"
    , "    let pathIsSet @x @y = __eqProof"
    , ""
    , "trait Show (0 a : Type) ="
    , "    show : a -> String"
    , ""
    , "trait IsSet a => Eq (0 a : Type) ="
    , "    (==) : a -> a -> Bool"
    , "    eqSound : (x : a) -> (y : a) -> (0 proof : (x == y) = True) -> x = y"
    , "    let eqSound x y proof = __eqProof"
    , "    eqComplete : (x : a) -> (y : a) -> (0 proof : x = y) -> (x == y) = True"
    , "    let eqComplete x y proof = __eqProof"
    , ""
    , -- §14.1.4 (Spec 13921): in std.prelude Ord refines Eq, and its
      -- equality classes MUST agree with (==).
      "trait Eq a => Ord (0 a : Type) ="
    , "    compare : a -> a -> Ordering"
    , ""
    , "trait Add (0 a : Type) ="
    , "    add : a -> a -> a"
    , ""
    , "trait Successor (0 a : Type) ="
    , "    succ : a -> a"
    , ""
    , "trait Max (0 a : Type) ="
    , "    max : a -> a -> a"
    , ""
    , "trait Mul (0 a : Type) ="
    , "    multiply : a -> a -> a"
    , ""
    , "trait Negatable (0 a : Type) ="
    , "    negate : a -> a"
    , ""
    , "trait Zero (0 a : Type) ="
    , "    zero : a"
    , ""
    , "trait One (0 a : Type) ="
    , "    one : a"
    , ""
    , "(/=) : forall (a : Type). (@_ : Eq a) -> a -> a -> Bool"
    , "let (/=) x y = not (x == y)"
    , ""
    , "(!=) : forall (a : Type). (@_ : Eq a) -> a -> a -> Bool"
    , "let (!=) x y = not (x == y)"
    , ""
    , "trait CheckedSub (0 a : Type) ="
    , "    subDefined : (& x : a) -> (& y : a) -> Bool"
    , "    subtract : (x : a) -> (y : a) -> (@_ : subDefined x y = True) -> a"
    , ""
    , "trait (Eq a, Zero a) => CheckedDiv (0 a : Type) ="
    , "    divDefined : (& x : a) -> (& y : a) -> Bool"
    , "    divide : (x : a) -> (y : a) -> (@_ : divDefined x y = True) -> a"
    , "    divDefinedOnlyNonZero : forall (x : a) (y : a). divDefined x y = True -> (y /= zero) = True"
    , "    divDefinedForNonZero : forall (x : a) (y : a). (y /= zero) = True -> divDefined x y = True"
    , ""
    , "trait (Eq a, Zero a) => CheckedMod (0 a : Type) ="
    , "    modDefined : (& x : a) -> (& y : a) -> Bool"
    , "    modulo : (x : a) -> (y : a) -> (@_ : modDefined x y = True) -> a"
    , "    modDefinedOnlyNonZero : forall (x : a) (y : a). modDefined x y = True -> (y /= zero) = True"
    , "    modDefinedForNonZero : forall (x : a) (y : a). (y /= zero) = True -> modDefined x y = True"
    , ""
    , "trait FromInteger (0 t : Type) ="
    , "    fromInteger : Nat -> t"
    , ""
    , "trait FromFloat (0 t : Type) ="
    , "    fromFloat : Double -> t"
    , ""
    , "trait FromString (0 t : Type) =" -- §28.2 (ordinary library trait)
    , "    fromString : String -> t"
    , ""
    , "instance FromString String ="
    , "    let fromString s = s"
    , ""
    , "trait PreservesParametricForall"
    , "    (parametric 0 G : (A : Type) -> Type) ="
    , "    pullForall :"
    , "        (parametric 0 F : (A : Type) -> Type) ->"
    , "        (forall (A : Type). G (F A)) ->"
    , "        G (forall (A : Type). F A)"
    , ""
    , "trait Applicative (0 f : (0 A : Type) -> Type) ="
    , "    pureA : forall (a : Type). a -> f a"
    , "    liftA2 : forall (a : Type) (b : Type) (c : Type). (a -> b -> c) -> f a -> f b -> f c"
    , ""
    , -- §14.1.4 (Spec 13923): in std.prelude Monad refines Applicative.
      "trait Applicative m => Monad (0 m : (0 A : Type) -> Type) =" -- §28.2.2 (operational subset)
    , "    (>>=) : forall (a : Type) (b : Type). m a -> (a -> m b) -> m b"
    , ""
    , "instance Applicative Option ="
    , "    let pureA x = Some x"
    , "    let liftA2 f oa ob ="
    , "        match oa"
    , "        case None -> None"
    , "        case Some a -> (match ob case None -> None case Some b -> Some (f a b))"
    , ""
    , "instance Monad Option ="
    , "    let (>>=) o f ="
    , "        match o"
    , "        case None -> None"
    , "        case Some x -> f x"
    , ""
    , "trait Releasable (0 m : (0 A : Type) -> Type) (0 a : Type) =" -- §29.x resources
    , "    release : a -> m Unit"
    , ""
    , "trait Shareable (0 a : Type)" -- §12.3 marker: shared-borrow-safe
    , ""
    , "trait Lift (0 a : Type) =" -- §23.3 lift-based cross-stage persistence
    , "    liftCode : a -> Code a"
    , ""
    , -- §18.1.13 Pointed: the minimal carrier of a distinguished 'empty'
      -- element, with NONE of the monoid laws. It is the supertrait of 'Monoid'
      -- (so every 'Monoid' supplies 'empty' through it), AND it is what the
      -- effect carriers 'IO e a' / 'STM a' carry on their OWN — their equality is
      -- not an h-prop, so they cannot be lawful 'Monoid's, but they still need an
      -- 'empty' for the §18.1.13 'let?'/STM 'empty' desugaring (the
      -- refutable-miss continuation, and STM's aborted alternative). The
      -- desugarer emits a bare 'empty' reference whose implicit dictionary
      -- resolves through 'Pointed'.
      --
      -- 'empty' lives in EXACTLY ONE trait. A second value member named 'empty'
      -- (e.g. duplicating it in 'Monoid') would overwrite this bare-name global
      -- and mis-route every 'empty' use to the wrong trait's dictionary; so
      -- 'Monoid' INHERITS 'empty' from 'Pointed' rather than re-declaring it.
      "trait Pointed (0 a : Type) ="
    , "    empty : a"
    , ""
    , -- §28.2.2 Monoid. The spec's 'Monoid' is LAWFUL BY DEFAULT: it carries
      -- 'append' AND the three monoid LAWS
      -- (appendAssoc/appendLeftIdentity/appendRightIdentity) as mandatory
      -- members, and inherits 'empty' from its 'Pointed' supertrait. Every
      -- 'Monoid' instance therefore DISCHARGES the laws — 'String' through the
      -- gated 'unsafeAssertProof' escape ('instance IsSet String' makes each law
      -- an h-prop), 'List a' through the HONEST structural induction lemmas
      -- ('listAppendAssoc'/'listAppendRightIdentity', sound for every element
      -- type). Each carrier provides its 'empty' via a sibling 'instance Pointed'.
      --
      -- The laws are written in prefix '(=)' form (an infix '(x = y)' in member
      -- position mis-parses as a binder group). 'append' comes from THIS trait
      -- and 'empty' from the 'Pointed' supertrait (NO explicit dict parameters):
      -- the elaborator threads the instance's own dictionary (and the supertrait
      -- 'this.__super0' field for 'empty'), so inside e.g. 'instance Monoid
      -- (List a)' they reduce to the concrete 'listAppend'/'Nil' and the proofs
      -- can COMPUTE. 'x y z' are implicit 'forall'-bound, so honest proofs
      -- reference top-level recursive lemmas (see
      -- 'listAppendRightIdentity'/'listAppendAssoc') that take the spine
      -- EXPLICITLY and recurse; an instance body does not re-bind 'x y z'.
      --
      -- SOUNDNESS / effect carriers: because the laws are MANDATORY, a type can
      -- be a 'Monoid' only if it can honestly discharge them. 'IO e a' / 'STM a'
      -- CANNOT — their propositional equality is not an h-prop (no 'IsSet (IO e
      -- a)'), and fabricating one is exactly the unsoundness this avoids. They
      -- are therefore 'Pointed' but NOT 'Monoid'.
      "trait Pointed a => Monoid (0 a : Type) =" -- §28.2.2
    , "    append : a -> a -> a"
    , "    appendAssoc : forall (x : a) (y : a) (z : a). (=) (append (append x y) z) (append x (append y z))"
    , "    appendLeftIdentity : forall (x : a). (=) (append empty x) x"
    , "    appendRightIdentity : forall (x : a). (=) (append x empty) x"
    , ""
    , "trait Functor (0 f : (0 A : Type) -> Type) =" -- §28.2.2 containers
    , "    map : forall (a : Type) (b : Type). (a -> b) -> f a -> f b"
    , ""
    , "trait Foldable (0 t : (0 A : Type) -> Type) ="
    , "    foldr : forall (a : Type) (b : Type). (a -> b -> b) -> b -> t a -> b"
    , "    foldl : forall (a : Type) (b : Type). (b -> a -> b) -> b -> t a -> b"
    , "    foldMap : forall (a : Type) (m : Type). (@_ : Monoid m) -> (a -> m) -> t a -> m"
    , ""
    , "trait Filterable (0 t : (0 A : Type) -> Type) ="
    , "    filter : forall (a : Type). (a -> Bool) -> t a -> t a"
    , ""
    , "trait FilterMap (0 t : (0 A : Type) -> Type) ="
    , "    filterMap : forall (a : Type) (b : Type). (a -> Option b) -> t a -> t b"
    , ""
    , "trait Traversable (0 t : (0 A : Type) -> Type) ="
    , "    traverse : forall (f : (0 A : Type) -> Type) (a : Type) (b : Type). (@_ : Applicative f) -> (a -> f b) -> t a -> f (t b)"
    , ""
    , -- Algebraic law signatures below use the standard order relation. These
      -- declarations precede the law-bearing traits so trait-header checking
      -- never depends on a later value declaration.
      "(<) : forall (a : Type). (@_ : Ord a) -> a -> a -> Bool"
    , "let (<) x y ="
    , "    match compare x y"
    , "    case LT -> True"
    , "    case EQ -> False"
    , "    case GT -> False"
    , ""
    , "(<=) : forall (a : Type). (@_ : Ord a) -> a -> a -> Bool"
    , "let (<=) x y ="
    , "    match compare x y"
    , "    case LT -> True"
    , "    case EQ -> True"
    , "    case GT -> False"
    , ""
    , -- §28.2 proof-carrying finite and refinement carriers. Their erased
      -- evidence is checked before later representation analysis may omit it.
      "data Refined.{u, v} (0 a : Type u) (parametric 0 predicate : a -> Type v) : Type (max u v) ="
    , "    Refined (value : a) (@0 predicateIsProp : IsProp (predicate value)) (@0 proof : predicate value)"
    , ""
    , "data Fin (n : Nat) : Type 0 ="
    , "    Fin (value : Nat) (@0 isLt : (value < n) = True)"
    , ""
    , -- §28.2.2 algebraic traits are law-bearing dictionaries. Their proof
      -- members participate in interface identity and semantic hashing even
      -- when runtime erasure later removes their values.
      "trait (Eq a, Zero a, Add a) => AdditiveMonoid (0 a : Type) ="
    , "    addAssoc : forall (x : a) (y : a) (z : a). add (add x y) z = add x (add y z)"
    , "    addLeftIdentity : forall (x : a). add zero x = x"
    , "    addRightIdentity : forall (x : a). add x zero = x"
    , ""
    , "trait AdditiveMonoid a => CommutativeAdditiveMonoid (0 a : Type) ="
    , "    addCommutative : forall (x : a) (y : a). add x y = add y x"
    , ""
    , "trait (Eq a, Max a) => JoinSemilattice (0 a : Type) ="
    , "    joinAssoc : forall (x : a) (y : a) (z : a). max (max x y) z = max x (max y z)"
    , "    joinCommutative : forall (x : a) (y : a). max x y = max y x"
    , "    joinIdempotent : forall (x : a). max x x = x"
    , ""
    , "trait (AdditiveMonoid a, Negatable a) => AdditiveGroup (0 a : Type) ="
    , "    addLeftInverse : forall (x : a). add (negate x) x = zero"
    , "    addRightInverse : forall (x : a). add x (negate x) = zero"
    , ""
    , "trait (Eq a, One a, Mul a) => MultiplicativeMonoid (0 a : Type) ="
    , "    mulAssoc : forall (x : a) (y : a) (z : a). multiply (multiply x y) z = multiply x (multiply y z)"
    , "    mulLeftIdentity : forall (x : a). multiply one x = x"
    , "    mulRightIdentity : forall (x : a). multiply x one = x"
    , ""
    , "trait (AdditiveMonoid a, MultiplicativeMonoid a) => AdditivelyNoncommutativeSemiring (0 a : Type) ="
    , "    mulLeftZero : forall (x : a). multiply zero x = zero"
    , "    mulRightZero : forall (x : a). multiply x zero = zero"
    , "    leftDistribute : forall (x : a) (y : a) (z : a). multiply x (add y z) = add (multiply x y) (multiply x z)"
    , "    rightDistribute : forall (x : a) (y : a) (z : a). multiply (add x y) z = add (multiply x z) (multiply y z)"
    , ""
    , "trait (CommutativeAdditiveMonoid a, AdditivelyNoncommutativeSemiring a) => Semiring (0 a : Type)"
    , ""
    , "trait (Semiring a, AdditiveGroup a, CheckedSub a) => Ring (0 a : Type) ="
    , "    subDefinedAlways : forall (x : a) (y : a). subDefined x y = True"
    , "    subtractAsAddInverse : forall (x : a) (y : a) (@p : subDefined x y = True). subtract x y @p = add x (negate y)"
    , ""
    , "trait (Semiring a, Ord a, CheckedDiv a, CheckedMod a) => EuclideanSemiring (0 a : Type) ="
    , "    divAndModSameDomain : forall (x : a) (y : a). divDefined x y = modDefined x y"
    , "    divModIdentity : forall (x : a) (y : a) (@pd : divDefined x y = True) (@pm : modDefined x y = True). add (multiply (divide x y @pd) y) (modulo x y @pm) = x"
    , ""
    , "trait (Ring a, CheckedDiv a) => FieldLike (0 a : Type) ="
    , "    divisionRightInverse : forall (x : a) (y : a) (@p : divDefined x y = True). multiply (divide x y @p) y = x"
    , ""
    , "trait (Ord a, AdditiveMonoid a) => OrderedAdditive (0 a : Type) ="
    , "    addMonotoneLeft : forall (x : a) (y : a) (z : a). (x <= y) = True -> (add z x <= add z y) = True"
    , "    addMonotoneRight : forall (x : a) (y : a) (z : a). (x <= y) = True -> (add x z <= add y z) = True"
    , ""
    , "trait (OrderedAdditive a, Semiring a) => OrderedSemiring (0 a : Type) ="
    , "    mulNonnegativeMonotone : forall (x : a) (y : a) (z : a). (zero <= z) = True -> (x <= y) = True -> (multiply z x <= multiply z y) = True"
    , ""
    , "trait RefinementView (0 t : Type) ="
    , "    Base : Type"
    , "    Predicate : Base -> Type"
    , "    refinementValue : t -> Base"
    , "    refinementPredicateIsProp : (x : t) -> IsProp (Predicate (refinementValue x))"
    , "    refinementProof : (x : t) -> Predicate (refinementValue x)"
    , "    refine : (x : Base) -> (@0 predicateIsProp : IsProp (Predicate x)) -> (@0 proof : Predicate x) -> t"
    , "    valueAfterRefine : forall (x : Base) (@0 predicateIsProp : IsProp (Predicate x)) (@0 proof : Predicate x). refinementValue (refine x @predicateIsProp @proof) = x"
    , "    refineAfterValue : forall (x : t). refine (refinementValue x) @(refinementPredicateIsProp x) @(refinementProof x) = x"
    , ""
    , -- §28.2 Equiv: the equivalence trait providing (~=). §28.2.3 fixes
      -- its precedence/associativity to match (==) (infix 40).
      "trait Equiv (0 a : Type) ="
    , "    (~=) : a -> a -> Bool"
    , ""
    , -- §14.1.1.3 / §28.2: every Eq is an Equiv (the prelude bridge
      -- instance), so (~=) resolves for any type with an Eq instance.
      "instance Eq a => Equiv a ="
    , "    let (~=) x y = x == y"
    , ""
    , -- §28.2 Alternative (the empty/orElse choice structure)
      "trait Alternative (0 f : (0 A : Type) -> Type) ="
    , "    emptyA : forall (a : Type). f a"
    , "    (<|>) : forall (a : Type). f a -> f a -> f a"
    , ""
    , -- §28.2 Iterator: the associated 'Item' type and the one-shot step
      -- 'next'. 'next' references the associated 'Item' in its own
      -- signature; §14.2.1 makes that a sibling-member projection of the
      -- current trait evidence, now that associated static members are
      -- supported (§14.3.4) — an instance defines both 'Item = …' and
      -- 'let next this = …'.
      "trait Iterator (0 it : Type) ="
    , "    Item : Type"
    , "    next : (1 this : it) -> Option (item : Item, rest : it)"
    , ""
    , -- §29.x runtime-effect / resource traits (§18.1.25, §18.6.1,
      -- §19.1-19.5). Operational subset: the IO carrier instances below
      -- and the prelude wrappers delegate to the IO primitives.
      "trait MonadFinally (0 m : (0 A : Type) -> Type) ="
    , "    finally : forall (a : Type). m a -> m Unit -> m a"
    , ""
    , "trait MonadError (0 m : (0 A : Type) -> Type) ="
    , "    Error : Type"
    , "    throwError : forall (a : Type). Error -> m a"
    , "    catchError : forall (a : Type). m a -> (Error -> m a) -> m a"
    , ""
    , "trait MonadResource (0 m : (0 A : Type) -> Type) ="
    , "    bracketM : forall (a : Type) (b : Type). m a -> (a -> m Unit) -> (a -> m b) -> m b"
    , ""
    , "trait MonadRef (0 m : (0 A : Type) -> Type) ="
    , "    Ref : (0 A : Type) -> Type"
    , "    newRef : forall (a : Type). a -> m (Ref a)"
    , "    readRef : forall (a : Type). Ref a -> m a"
    , "    writeRef : forall (a : Type). Ref a -> a -> m Unit"
    , ""
    , -- §11.1.4/§28.2 intrinsic classifiers. They are ordinary nameable
      -- trait goals; evidence introduction remains compiler-owned.
      "trait IsNType (level : Nat) (0 a : Type)"
    , ""
    , "trait RuntimeErased (0 t : Type)"
    , ""
    , -- §14.5.2/§28.2 compiler-owned representation marker. Source code may
      -- name the goal, but only the checked derive path introduces evidence.
      "trait ExactNaturalRepresentation (0 t : Type)"
    , ""
    , -- §28.2 source-level dense ordinal equivalence. This law bundle remains
      -- separate from the compiler-owned representation certificate of
      -- §30.2.7B; a handwritten instance never authorizes a backend layout.
      "trait IsSet t => OrdinalRepresentation (n : Nat) (0 t : Type) ="
    , "    rank : t -> Fin n"
    , "    unrank : Fin n -> t"
    , "    unrankRank : forall (x : t). unrank (rank x) = x"
    , "    rankUnrank : forall (i : Fin n). rank (unrank i) = i"
    , ""
    , -- §14.4 set-truncation witnesses. Primitive carriers have canonical
      -- equality, while recursive containers below require IsSet evidence for
      -- every element carrier; no unconditional container instance is sound.
      "instance IsSet String"
    , "instance IsSet Bool"
    , "instance IsSet Double"
    , "instance IsSet Unit"
    , "instance IsSet UnicodeScalar"
    , "instance IsSet Byte"
    , "instance IsSet Bytes"
    , "instance IsSet Grapheme"
    , "instance IsSet Ordering"
    , ""
    , -- §28.2/§15.11 termination: WellFounded/Acc carriers and the
      -- well-founded-relation trait.  The well-foundedness witness is an
      -- erased proof and is not modelled; see docs/notes/KNOWN_SPEC_ISSUES.md.
      "data WellFounded (0 a : Type) (rel : a -> a -> Type) : Type ="
    , "    MkWellFounded"
    , ""
    , "trait WellFoundedRelation (0 a : Type) ="
    , "    rel : a -> a -> Type"
    , ""
    , -- §28.2 (export item, Spec.md line 28648; normative signatures at
      -- the §15 `expect term` block, Spec.md line 29108-29119)
      -- well-founded-relation combinators. 'measureRelation' lifts a
      -- WellFoundedRelation on the codomain 'b' to a relation on 'a' via a
      -- measure function; its body is the natural pullback of 'rel'.
      -- 'lexRelation' is exported at the spec surface, but the current
      -- checker does not inspect arbitrary WellFoundedRelation dictionaries
      -- as termination evidence; see docs/notes/KNOWN_SPEC_ISSUES.md.
      "measureRelation : forall (ordinary 0 a b : Type). (@_ : WellFoundedRelation b) -> (a -> b) -> a -> a -> Type"
    , "let measureRelation f x y = rel (f x) (f y)"
    , ""
    , "lexRelation : forall (a b : Type). (@_ : WellFoundedRelation a) -> (@_ : WellFoundedRelation b) -> WellFoundedRelation (a, b)"
    , "let lexRelation = __eqProof"
    , ""
    , "(+) : forall (a : Type). (@_ : Add a) -> (& x : a) -> (& y : a) -> a"
    , "let (+) x y = add x y"
    , ""
    , "(*) : forall (a : Type). (@_ : Mul a) -> (& x : a) -> (& y : a) -> a"
    , "let (*) x y = multiply x y"
    , ""
    , "(-) : forall (a : Type). (@_ : CheckedSub a) -> (x : a) -> (y : a) -> (@_ : subDefined x y = True) -> a"
    , "let (-) x y @p = subtract x y @p"
    , ""
    , "(/) : forall (a : Type). (@_ : CheckedDiv a) -> (x : a) -> (y : a) -> (@_ : divDefined x y = True) -> a"
    , "let (/) x y @p = divide x y @p"
    , ""
    , "(%) : forall (a : Type). (@_ : CheckedMod a) -> (x : a) -> (y : a) -> (@_ : modDefined x y = True) -> a"
    , "let (%) x y @p = modulo x y @p"
    , ""
    , "(>) : forall (a : Type). (@_ : Ord a) -> a -> a -> Bool"
    , "let (>) x y = not (x <= y)"
    , ""
    , "(>=) : forall (a : Type). (@_ : Ord a) -> a -> a -> Bool"
    , "let (>=) x y = not (x < y)"
    , ""
    , "instance Eq Integer ="
    , "    let (==) x y = eqInt x y"
    , ""
    , "instance Ord Integer ="
    , "    let compare x y = if ltInt x y then LT elif eqInt x y then EQ else GT"
    , ""
    , "instance Show Integer ="
    , "    let show x = showInt x"
    , ""
    , "instance Add Integer ="
    , "    let add x y = addInt x y"
    , ""
    , "instance Mul Integer ="
    , "    let multiply x y = mulInt x y"
    , ""
    , "instance Negatable Integer ="
    , "    let negate x = negInt x"
    , ""
    , "instance CheckedSub Integer ="
    , "    let subDefined x y = True"
    , "    let subtract x y @p = subInt x y"
    , ""
    , "instance CheckedDiv Integer ="
    , "    let divDefined x y = not (eqInt y 0)"
    , "    let divide x y @p = divInt x y"
    , "    let divDefinedOnlyNonZero = unsafeAssertProof \"Integer division is defined only for nonzero divisors\""
    , "    let divDefinedForNonZero = unsafeAssertProof \"Integer division is defined for every nonzero divisor\""
    , ""
    , "instance CheckedMod Integer ="
    , "    let modDefined x y = not (eqInt y 0)"
    , "    let modulo x y @p = modInt x y"
    , "    let modDefinedOnlyNonZero = unsafeAssertProof \"Integer modulo is defined only for nonzero divisors\""
    , "    let modDefinedForNonZero = unsafeAssertProof \"Integer modulo is defined for every nonzero divisor\""
    , ""
    , "instance FromInteger Integer ="
    , "    let fromInteger n = natToInt n"
    , ""
    , -- compatibility extension (§T.1, documented in TESTING.md): the
      -- external corpus writes user FromInteger instances through an
      -- 'integerToInt' literal-payload conversion. §6.1.5 makes the
      -- payload a Nat; this is the corresponding Nat -> Int conversion
      -- (§28.2 permits exports beyond the normative minimum).
      "integerToInt : Nat -> Int"
    , "let integerToInt n = natToInt n"
    , ""
    , "instance FromInteger Double ="
    , "    let fromInteger n = intToDouble (natToInt n)"
    , ""
    , "instance Eq Double ="
    , "    let (==) x y = eqDouble x y"
    , ""
    , "instance Show Double ="
    , "    let show x = showDouble x"
    , ""
    , "instance Add Double ="
    , "    let add x y = addDouble x y"
    , ""
    , "instance Mul Double ="
    , "    let multiply x y = mulDouble x y"
    , ""
    , "instance Eq String ="
    , "    let (==) x y = eqStr x y"
    , ""
    , "instance Show String ="
    , "    let show x = x"
    , ""
    , "instance Add String ="
    , "    let add x y = stringAppend x y"
    , ""
    , "instance Eq Bool ="
    , "    let (==) x y = if x then y else not y"
    , ""
    , "instance Show Bool ="
    , "    let show b = if b then \"True\" else \"False\""
    , ""
    , "instance Ord Bool ="
    , "    let compare x y = if x then (if y then EQ else GT) else (if y then LT else EQ)"
    , ""
    , "instance Eq Unit ="
    , "    let (==) x y = True"
    , ""
    , "instance Show Unit ="
    , "    let show u = \"()\""
    , ""
    , "instance Ord String ="
    , "    let compare x y = if ltStr x y then LT elif eqStr x y then EQ else GT"
    , ""
    , "instance Ord Double ="
    , "    let compare x y = if ltDouble x y then LT elif ltDouble y x then GT else EQ"
    , ""
    , "instance Eq UnicodeScalar ="
    , "    let (==) x y = eqScalar x y"
    , ""
    , "instance Ord UnicodeScalar ="
    , "    let compare x y = if ltScalar x y then LT elif eqScalar x y then EQ else GT"
    , ""
    , "instance Show UnicodeScalar ="
    , "    let show c = showScalar c"
    , ""
    , -- §28.2 text atoms: Byte and Bytes have Eq/Ord/Show; Grapheme has
      -- Eq (exact scalar sequence, §6.5) and Show but deliberately NO
      -- Ord (§29.x: no portable grapheme ordering)
      "instance Eq Byte ="
    , "    let (==) x y = eqByte x y"
    , ""
    , "instance Ord Byte ="
    , "    let compare x y = if ltByte x y then LT elif eqByte x y then EQ else GT"
    , ""
    , "instance Show Byte ="
    , "    let show b = showByte b"
    , ""
    , "instance Eq Bytes ="
    , "    let (==) x y = eqBytes x y"
    , ""
    , "instance Ord Bytes ="
    , "    let compare x y = if ltBytes x y then LT elif eqBytes x y then EQ else GT"
    , ""
    , "instance Show Bytes ="
    , "    let show bs = showBytes bs"
    , ""
    , "instance Eq Grapheme ="
    , "    let (==) x y = eqGrapheme x y"
    , ""
    , "instance Show Grapheme ="
    , "    let show g = showGrapheme g"
    , ""
    , -- §20.2 range operators over the prelude Rangeable trait (the
      -- associated Range type is modelled as a concrete carrier; the
      -- reference prelude spells it NumericRange)
      "data NumericRange (0 v : Type) : Type ="
    , "    NumericRange (rangeFrom : v) (rangeTo : v) (rangeExclusive : Bool)"
    , ""
    , "trait Rangeable (0 v : Type) ="
    , "    Range : Type"
    , "    range : v -> v -> Bool -> Range"
    , ""
    , "(..) : forall (v : Type). (@_ : Rangeable v) -> v -> v -> Rangeable.Range v"
    , "let (..) lo hi = range lo hi False"
    , ""
    , "(..<) : forall (v : Type). (@_ : Rangeable v) -> v -> v -> Rangeable.Range v"
    , "let (..<) lo hi = range lo hi True"
    , ""
    , "instance Rangeable Integer ="
    , "    let Range = NumericRange Integer"
    , "    let range lo hi excl = NumericRange lo hi excl"
    , ""
    , "instance Rangeable Nat ="
    , "    let Range = NumericRange Nat"
    , "    let range lo hi excl = NumericRange lo hi excl"
    , ""
    , "instance Rangeable UnicodeScalar =" -- §6.4
    , "    let Range = NumericRange UnicodeScalar"
    , "    let range lo hi excl = NumericRange lo hi excl"
    , ""
    , "trait Contains (0 container : Type) (0 item : Type) ="
    , "    contains : (& container : container) -> (& item : item) -> Bool"
    , ""
    , "instance Contains (NumericRange Nat) Nat ="
    , "    let contains r x ="
    , "        match r"
    , "        case NumericRange lo hi exclusive -> if lo <= x then (if exclusive then x < hi else x <= hi) else False"
    , ""
    , "instance Contains (NumericRange Integer) Integer ="
    , "    let contains r x ="
    , "        match r"
    , "        case NumericRange lo hi exclusive -> if lo <= x then (if exclusive then x < hi else x <= hi) else False"
    , ""
    , -- §20.2: materialize a range into its ascending element list. Used
      -- by the comprehension/for lowering and by 'IntoQuery NumericRange'.
      "rangeToList : forall (v : Type). NumericRange v -> List v"
    , "let rangeToList r ="
    , "    match r"
    , "    case NumericRange lo hi excl -> __rangeEnum lo hi excl"
    , ""
    , "orderingCode : Ordering -> Integer"
    , "let orderingCode o ="
    , "    match o"
    , "    case LT -> 0"
    , "    case EQ -> 1"
    , "    case GT -> 2"
    , ""
    , "instance Eq Ordering ="
    , "    let (==) x y = eqInt (orderingCode x) (orderingCode y)"
    , ""
    , "instance Ord Ordering ="
    , "    let compare x y = if ltInt (orderingCode x) (orderingCode y) then LT elif eqInt (orderingCode x) (orderingCode y) then EQ else GT"
    , ""
    , "instance Show Ordering ="
    , "    let show o ="
    , "        match o"
    , "        case LT -> \"LT\""
    , "        case EQ -> \"EQ\""
    , "        case GT -> \"GT\""
    , ""
    , "instance Eq Nat ="
    , "    let (==) x y = eqInt (natToInt x) (natToInt y)"
    , ""
    , "instance Ord Nat ="
    , "    let compare x y = natCompare x y"
    , ""
    , "instance Show Nat ="
    , "    let show n = showInt (natToInt n)"
    , ""
    , -- §28.2 logical refinement API. The proof-producing members use the
      -- authenticated prelude equality kernel; their public types are ordinary
      -- KCore and are rechecked like handwritten evidence.
      "refinedValue : forall (a : Type) (predicate : a -> Type). Refined a predicate -> a"
    , "let refinedValue x = x.value"
    , ""
    , "refinedPredicateIsProp : forall (a : Type) (predicate : a -> Type). (x : Refined a predicate) -> IsProp (predicate x.value)"
    , "let refinedPredicateIsProp x = x.predicateIsProp"
    , ""
    , "refinedProof : forall (a : Type) (predicate : a -> Type). (x : Refined a predicate) -> predicate x.value"
    , "let refinedProof x = x.proof"
    , ""
    , "refinedExt : forall (a : Type) (predicate : a -> Type) (x : Refined a predicate) (y : Refined a predicate). x.value = y.value -> x = y"
    , "let refinedExt proof = __eqProof"
    , ""
    , "refinedIsSet : forall (a : Type) (predicate : a -> Type). IsSet a -> IsSet (Refined a predicate)"
    , "let refinedIsSet evidence = __eqProof"
    , ""
    , "instance IsSet a => IsSet (Refined a predicate)"
    , ""
    , "instance Eq a => Eq (Refined a predicate) ="
    , "    let (==) x y = x.value == y.value"
    , ""
    , "instance Ord a => Ord (Refined a predicate) ="
    , "    let compare x y = compare x.value y.value"
    , ""
    , "instance RefinementView (Refined a predicate) ="
    , "    let Base = a"
    , "    let Predicate = predicate"
    , "    let refinementValue x = x.value"
    , "    let refinementPredicateIsProp x = x.predicateIsProp"
    , "    let refinementProof x = x.proof"
    , "    let refine x @predicateIsProp @proof = Refined x @predicateIsProp @proof"
    , "    let valueAfterRefine = __eqProof"
    , "    let refineAfterValue = __eqProof"
    , ""
    , "tryRefine : forall (a : Type) (predicate : a -> Type). (@0 predicateIsProp : forall (x : a). IsProp (predicate x)) -> ((x : a) -> Dec (predicate x)) -> (x : a) -> Option (Refined a predicate)"
    , "let tryRefine @predicateIsProp decide x ="
    , "    match decide x"
    , "    case Dec.Yes proof -> Some (Refined x @(predicateIsProp @x) @proof)"
    , "    case Dec.No refute -> None"
    , ""
    , "finValue : forall (n : Nat). Fin n -> Nat"
    , "let finValue i = i.value"
    , ""
    , "finExt : forall (n : Nat) (x : Fin n) (y : Fin n). x.value = y.value -> x = y"
    , "let finExt proof = __eqProof"
    , ""
    , "finZero : forall (n : Nat). Fin (natAdd n 1)"
    , "let finZero = Fin 0 @(unsafeAssertProof \"zero is below every positive Fin bound\")"
    , ""
    , "finSucc : forall (n : Nat). Fin n -> Fin (natAdd n 1)"
    , "let finSucc i = Fin (natAdd i.value 1) @(unsafeAssertProof \"successor preserves a Fin bound\")"
    , ""
    , "finWeaken : forall (n : Nat). Fin n -> Fin (natAdd n 1)"
    , "let finWeaken i = Fin i.value @(unsafeAssertProof \"Fin weakening preserves the ordinal\")"
    , ""
    , "finLast : (n : Nat) -> Fin (natAdd n 1)"
    , "let finLast n = Fin n @(unsafeAssertProof \"the predecessor is below a positive Fin bound\")"
    , ""
    , "finCases : forall (n : Nat) (parametric 0 motive : Fin (natAdd n 1) -> Type). motive finZero -> ((i : Fin n) -> motive (finSucc i)) -> (i : Fin (natAdd n 1)) -> motive i"
    , "let finCases @n @motive zeroCase successorCase i ="
    , "    match i.value"
    , "    case Nat.Zero -> __transport zeroCase"
    , "    case Nat.Succ predecessor -> __transport (successorCase (Fin predecessor @(unsafeAssertProof \"Fin successor elimination preserves the bound\")))"
    , ""
    , -- The worker recurses on the retained ordinal, not on the erased bound.
      -- Its predecessor-bound changes are justified by the Fin proof and are
      -- transported only through erased indices; runtime computation is the
      -- ordinary zero/successor fold required by §28.2.
      "__finBoundPred : Nat -> Nat"
    , "let __finBoundPred n ="
    , "    match n"
    , "    case Nat.Zero -> Nat.Zero"
    , "    case Nat.Succ predecessor -> predecessor"
    , ""
    , "__finInductionByValue : forall (parametric 0 motive : (k : Nat) -> Fin k -> Type). (forall (k : Nat). motive (natAdd k 1) finZero) -> (forall (k : Nat) (i : Fin k). motive k i -> motive (natAdd k 1) (finSucc i)) -> forall (n : Nat). (value : Nat) -> (@0 isLt : (value < n) = True) -> motive n (Fin value @isLt)"
    , "let __finInductionByValue @motive zeroCase successorCase @n value @isLt ="
    , "    match value"
    , "    case Nat.Zero -> __transport (zeroCase @(__finBoundPred n))"
    , "    case Nat.Succ predecessor ->"
    , "        let predecessorIndex : Fin (__finBoundPred n) = Fin predecessor @(unsafeAssertProof \"Fin induction predecessor preserves the reduced bound\")"
    , "        let induction : motive (__finBoundPred n) predecessorIndex = __finInductionByValue zeroCase successorCase @(__finBoundPred n) predecessorIndex.value @predecessorIndex.isLt"
    , "        __transport (successorCase @(__finBoundPred n) @predecessorIndex induction)"
    , ""
    , "finInduction : forall (n : Nat) (parametric 0 motive : (k : Nat) -> Fin k -> Type). (forall (k : Nat). motive (natAdd k 1) finZero) -> (forall (k : Nat) (i : Fin k). motive k i -> motive (natAdd k 1) (finSucc i)) -> (i : Fin n) -> motive n i"
    , "let finInduction @n @motive zeroCase successorCase i ="
    , "    __transport (__finInductionByValue zeroCase successorCase @n i.value @i.isLt)"
    , ""
    , "instance IsSet (Fin n)"
    , ""
    , "instance Eq (Fin n) ="
    , "    let (==) x y = x.value == y.value"
    , ""
    , "instance Ord (Fin n) ="
    , "    let compare x y = compare x.value y.value"
    , ""
    , "instance Show (Fin n) ="
    , "    let show i = show i.value"
    , ""
    , "instance RefinementView (Fin n) ="
    , "    let Base = Nat"
    , "    let Predicate = \\value -> (value < n) = True"
    , "    let refinementValue i = i.value"
    , "    let refinementPredicateIsProp i = summon (IsProp ((i.value < n) = True))"
    , "    let refinementProof i = i.isLt"
    , "    let refine value @predicateIsProp @proof = Fin value @proof"
    , "    let valueAfterRefine = __eqProof"
    , "    let refineAfterValue = __eqProof"
    , ""
    , "instance OrdinalRepresentation n (Fin n) ="
    , "    let rank i = i"
    , "    let unrank i = i"
    , "    let unrankRank = __eqProof"
    , "    let rankUnrank = __eqProof"
    , ""
    , "instance FromInteger Nat ="
    , "    let fromInteger n = n"
    , ""
    , "instance FromFloat Double ="
    , "    let fromFloat d = d"
    , ""
    , "print : forall (a : Type). (@_ : Show a) -> a -> UIO Unit"
    , "let print value = printString (show value)"
    , ""
    , "println : forall (a : Type). (@_ : Show a) -> a -> UIO Unit"
    , "let println value = printlnString (show value)"
    , ""
    , -- external-corpus compatibility helper (decimal print of an Int)
      "printInt : forall (e : Type). Int -> IO e Unit"
    , "let printInt n = printlnString (showInt n)"
    , ""
    , "pure : forall (e : Type) (a : Type). a -> IO e a"
    , "let pure x = ioPure x"
    , ""
    , -- §28.2.2 computation-carrier helpers and the IO e instances
      "pureIO : forall (e : Type) (a : Type). a -> IO e a"
    , "let pureIO x = ioPure x"
    , ""
    , "bindIO : forall (e : Type) (a : Type) (b : Type). IO e a -> (a -> IO e b) -> IO e b"
    , "let bindIO m f = ioBind m f"
    , ""
    , "instance Functor (IO e) ="
    , "    let map f m = ioBind m (\\x -> ioPure (f x))"
    , ""
    , "instance Applicative (IO e) ="
    , "    let pureA x = ioPure x"
    , "    let liftA2 f a b = ioBind a (\\x -> ioBind b (\\y -> ioPure (f x y)))"
    , ""
    , "instance Monad (IO e) ="
    , "    let (>>=) m f = ioBind m f"
    , ""
    , -- §18.1.13 STM is its own monad (journaled transactions); its do-notation
      -- desugars through these instances into stmBind/stmPure.
      "instance Functor STM ="
    , "    let map f m = stmBind m (\\x -> stmPure (f x))"
    , ""
    , "instance Applicative STM ="
    , "    let pureA x = stmPure x"
    , "    let liftA2 f a b = stmBind a (\\x -> stmBind b (\\y -> stmPure (f x y)))"
    , ""
    , "instance Monad STM ="
    , "    let (>>=) m f = stmBind m f"
    , ""
    , -- §18.6.1: STM supports surface `var` through TVar-backed MonadRef.
      "instance MonadRef STM ="
    , "    let Ref = TVar"
    , "    let newRef x = newTVar x"
    , "    let readRef r = readTVar r"
    , "    let writeRef r x = writeTVar r x"
    , ""
    , -- check c: succeed if c, else retry the transaction (§18.1.13).
      "check : Bool -> STM Unit"
    , "let check c = if c then stmPure Unit else retry"
    , ""
    , -- §18.1.13: `empty` (the aborted alternative) resolves through the
      -- law-less `Pointed` trait (NOT `Monoid`, whose mandatory laws this
      -- carrier cannot honestly discharge — its equality is not an h-prop), so
      -- IO-shaped do-scopes can sequence it as an action.
      "instance Pointed (IO e a) ="
    , "    let empty = stmAbort"
    , ""
    , -- §18.1.13 STM alternative: `empty` retries the transaction. Lets
      -- `let?`/refutable forms desugar in STM. `Pointed`, not `Monoid`: STM
      -- equality is not an h-prop, so the monoid laws cannot be asserted.
      "instance Pointed (STM a) ="
    , "    let empty = retry"
    , ""
    , -- RC4 / §28: the mandated `IO e` error-handling instances.  Their
      -- members ARE the §18.1.25 / §19.1 surface operations, delegating to
      -- the IO primitives, so `finally`/`throwError`/`catchError` resolve via
      -- the IO dictionary (the free functions they replaced are gone).
      "instance MonadFinally (IO e) ="
    , "    let finally ma mf = finallyIO ma mf"
    , ""
    , "instance MonadError (IO e) ="
    , "    let Error = e"
    , "    let throwError err = throwIO err"
    , "    let catchError body handler = catchIO body handler"
    , ""
    , -- §18.1/§19.5/§28.2 MonadResource: a protected resource scope. The
      -- release runs exactly once on every exit path from `use` (normal
      -- completion, typed failure, interruption, defect), as the §18.8/§18.1
      -- finally kernel guarantees.
      "instance MonadResource (IO e) ="
    , -- §18.1.12: `bracket` masks the WHOLE acquire-and-register region, then
      -- runs `use` restored (interruptible). Masking `acquire` AND the
      -- `finallyIO` finalizer-registration as one unit closes the gap where a
      -- born-interrupted fiber would deliver its pending interrupt before the
      -- release is installed (skipping the finalizer). With this, the interrupt
      -- can only fire inside `restore (use r)`, by which point the release is
      -- registered, so the finalizer RUNS on interrupt (ZIO/bracket semantics).
      -- This mirrors the runtime's krt2_acquire_release (rt.c).
      "    let bracketM acquire release use ="
    , "        mask (\\restore -> ioBind acquire (\\r -> finallyIO (restore (use r)) (release r)))"
    , ""
    , -- §18.6.1 / §28.2: IO supports surface `var` through MonadRef.
      "instance MonadRef (IO e) ="
    , "    let Ref = __IORef"
    , "    let newRef x = __ioNewRef x"
    , "    let readRef r = __ioReadRef r"
    , "    let writeRef r x = __ioWriteRef r x"
    , ""
    , -- §28.2 `bracket` surface name (the MonadResource method for IO).
      "bracket : forall (e : Type) (a : Type) (b : Type). IO e a -> (a -> IO e Unit) -> (a -> IO e b) -> IO e b"
    , "let bracket acquire release use = bracketM acquire release use"
    , ""
    , -- §18.1.12 surface names over the same protected-scope machinery. `ensuring`
      -- is the named finalizer combinator; `acquireRelease` keeps the resource-facing
      -- signature from the spec and delegates to the IO MonadResource instance.
      "ensuring : forall (e : Type) (a : Type). IO e a -> IO e Unit -> IO e a"
    , "let ensuring body finalizer = finallyIO body finalizer"
    , ""
    , "acquireRelease : forall (e : Type) (r : Type) (a : Type). IO e r -> ((1 resource : r) -> IO e Unit) -> ((& resource : r) -> IO e a) -> IO e a"
    , "let acquireRelease acquire release use = bracket acquire release use"
    , ""
    , -- §18.1.4: structured-concurrency handles (check-mode support)
      "data Fiber (0 e : Type) (0 a : Type) : Type ="
    , "    MkFiberHandle"
    , ""
    , -- §18.1.2 structured interruption metadata: a tag classifying why the
      -- interruption occurred plus the initiating fiber when semantically known.
      "data InterruptTag : Type ="
    , "    Requested"
    , "    ScopeShutdown"
    , "    TimedOut"
    , "    RaceLost"
    , "    External"
    , "    Custom String"
    , ""
    , "data FiberId : Type ="
    , "    MkFiberId Integer"
    , ""
    , -- §28.2 constructor namespace: the InterruptCause type's single ctor is
      -- spelled `InterruptCause` (matching the type), not `MkInterruptCause`.
      -- The runtime builds this value by its pinned id (KCT_MK_INTERRUPT_CAUSE),
      -- so the rename is purely at the prelude surface; the id is unchanged.
      "data InterruptCause : Type ="
    , "    InterruptCause InterruptTag (Option FiberId)"
    , ""
    , -- §28.2 defect classification: a defect's structured tag, used to project
      -- a host/runtime failure into a known category. `OtherDefect` is the
      -- catch-all for an unclassified host exception.
      "data DefectTag : Type ="
    , "    Panic"
    , "    AssertionFailed"
    , "    ArithmeticFault"
    , "    StackOverflow"
    , "    OutOfMemory"
    , "    HostFailure"
    , "    ForeignContractViolation"
    , "    UnhandledChildFailure"
    , "    OtherDefect"
    , ""
    , -- §28.2: a defect carries a classifying tag plus an optional diagnostic
      -- message (None when no human-readable text is available).
      "data DefectInfo : Type ="
    , "    DefectInfo (tag : DefectTag) (message : Option String)"
    , ""
    , "data Cause (0 e : Type) : Type ="
    , "    Fail e"
    , "    Interrupt InterruptCause"
    , "    Defect DefectInfo"
    , "    Both (Cause e) (Cause e)"
    , "    Then (Cause e) (Cause e)"
    , ""
    , "data Exit (0 e : Type) (0 a : Type) : Type ="
    , "    Success a"
    , "    Failure (Cause e)"
    , ""
    , -- §11.6 decidability witness. The universe belongs to the declaration
      -- schema; it is not a runtime TypeLevel parameter.
      "data Dec.{u} (parametric 0 p : Type u) : Type u ="
    , "    Yes p"
    , "    No (p -> Void)"
    , ""
    , "fork : forall (e : Type) (a : Type) (r : Type). (IO e a captures ()) -> IO r (Fiber e a)"
    , "let fork action = __forkRun action"
    , ""
    , -- §18.1.4/§32.2: await a fiber's terminal result (its Exit).
      "await : forall (e : Type) (a : Type) (r : Type). Fiber e a -> IO r (Exit e a)"
    , "let await fib = __awaitFiber fib"
    , ""
    , -- §18.1.4 forkDaemon: an unattached child fiber.
      "forkDaemon : forall (e : Type) (a : Type). (IO e a captures ()) -> UIO (Fiber e a)"
    , "let forkDaemon action = __forkDaemon action"
    , ""
    , -- §18.1.10 fiber identity: every created fiber has a unique FiberId for one
      -- program execution. `currentFiberId` reports the running fiber's id;
      -- `fiberId fib` reports a given fiber's. The runtime delivers a raw integer;
      -- the MkFiberId wrapper is applied here (cf. nowMonotonic over __nowNanos).
      "currentFiberId : UIO FiberId"
    , "let currentFiberId = ioBind __currentFiberId (\\n -> ioPure (MkFiberId n))"
    , "fiberId : forall (e : Type) (a : Type). Fiber e a -> UIO FiberId"
    , "let fiberId fib = ioBind (__fiberId fib) (\\n -> ioPure (MkFiberId n))"
    , ""
    , -- §18.1.4 join: await a fiber and project its outcome into the caller —
      -- success returns the value, typed failure re-fails, and any non-typed
      -- runtime cause (interruption/defect) terminates the caller likewise.
      "join : forall (e : Type) (a : Type). Fiber e a -> IO e a"
    , "let join fib ="
    , "    ioBind (await fib) (\\ex ->"
    , "      match ex"
    , "      case Success v -> ioPure v"
    , "      case Failure (Fail e) -> throwIO e"
    , "      case Failure c -> __reraiseCause c)"
    , ""
    , -- §18.11 awaitPromise: await a promise and project its Exit into the
      -- caller, exactly as `join` does for a fiber (success returns the value,
      -- a typed Fail re-fails, any other cause is re-raised).
      "awaitPromise : forall (e : Type) (a : Type). Promise e a -> IO e a"
    , "let awaitPromise p ="
    , "    ioBind (awaitPromiseExit p) (\\ex ->"
    , "      match ex"
    , "      case Success v -> ioPure v"
    , "      case Failure (Fail e) -> throwIO e"
    , "      case Failure c -> __reraiseCause c)"
    , ""
    , -- §18.1.12 masking surface. `mask f` runs `f` with interruption masked,
      -- handing it a `restore` that re-enables interruption for a chosen
      -- subcomputation. `restore` is RANK-2 — `forall (x : Type). IO e x -> IO e x`
      -- — exactly as §18.1.12 mandates (Spec.md:19063-19066): the single captured
      -- masking capability is applied to sub-actions of arbitrary, caller-chosen
      -- types within one mask block (the canonical bracket/withLock idiom). The
      -- `x` binder is RuntimeErased (a type at quantity 0), so a `restore @x act`
      -- use site emits an erased implicit type-application that the lowering DROPS
      -- before the runtime's single 1-arg `restore` closure — see `__mask` below.
      -- The body forwards to the `__mask` prim (OP_MASK), lowered to `krt2_mask`.
      "mask : forall (e : Type) (a : Type). ((forall (x : Type). IO e x -> IO e x) -> IO e a) -> IO e a"
    , -- The body's rank-2 `restore` is NOT the raw 1-arg runtime closure (which
      -- carries no type slot — see `__restoreAt`); it is `\act -> __restoreAt raw
      -- act`, a worker-backed rank-2 wrapper whose erased type slot absorbs the
      -- use-site `kappi`, with the prim `__restoreAt` dropping its own type-arg
      -- and lowering to a bare `kapp(raw, act)` onto the 1-arg runtime restore.
      "let mask f = __mask (\\raw -> f (\\act -> __restoreAt raw act))"
    , ""
    , -- §18.1.4 interruption surface. interrupt/interruptFork use the Requested
      -- tag with no recorded initiator; the *As forms carry explicit metadata.
      "interruptAs : forall (e : Type) (a : Type). InterruptCause -> Fiber e a -> UIO Unit"
    , "let interruptAs cause fib = __interruptWait cause fib"
    , ""
    , "interruptForkAs : forall (e : Type) (a : Type). InterruptCause -> Fiber e a -> UIO Unit"
    , "let interruptForkAs cause fib = __interruptNoWait cause fib"
    , ""
    , "interrupt : forall (e : Type) (a : Type). Fiber e a -> UIO Unit"
    , "let interrupt fib = __interruptWait (InterruptCause Requested None) fib"
    , ""
    , "interruptFork : forall (e : Type) (a : Type). Fiber e a -> UIO Unit"
    , "let interruptFork fib = __interruptNoWait (InterruptCause Requested None) fib"
    , ""
    , -- §18.1.4 / PRIMITIVES #5 disconnect (ZIO): detached interruption. Run the
      -- action on its own forked fiber and `join` it, so success/failure pass
      -- through transparently; but if the *caller* of `disconnect action` is
      -- interrupted while it is joined, the `onInterrupt` finalizer issues a
      -- NON-waiting interrupt (`interruptFork`) to the child. The caller then
      -- unwinds IMMEDIATELY — it does not block on the child's finalizers — while
      -- the child finalizes in the background (the §18.1.4 fork-interrupt edge).
      -- This is the only difference from running `action` inline, where the
      -- caller's interrupt waits for the action's finalizers (the default
      -- structured "wait for finalizers"). It is a pure derivation over
      -- fork/join/onInterrupt/interruptFork — NOT a new runtime primitive
      -- (`forkDaemon` detaches scope ATTACHMENT, a different axis: it does not
      -- change the caller's interrupt-wait edge, so it does not subsume this).
      "disconnect : forall (e : Type) (a : Type). (IO e a captures ()) -> IO e a"
    , "let disconnect action ="
    , "    ioBind (fork action) (\\fib ->"
    , "      onInterrupt (join fib) (\\ic ->"
    , "        __interruptForkAny (InterruptCause Requested None) fib))"
    , ""
    , -- §18.1.6 race result + the typed timeout error.
      "data RaceResult (0 a : Type) (0 b : Type) : Type ="
    , "    LeftWins a"
    , "    RightWins b"
    , ""
    , "data TimeoutError : Type ="
    , "    Timeout"
    , ""
    , -- internal structured outcomes returned by the timeout/race kernels;
      -- the wrappers below perform the typed-error injection.
      "data TimeoutOutcome (0 e : Type) (0 a : Type) : Type ="
    , "    TOTimedOut"
    , "    TOExit (Exit e a)"
    , ""
    , "data RaceOutcome (0 e : Type) (0 f : Type) (0 a : Type) (0 b : Type) : Type ="
    , "    ROLeft (Exit e a)"
    , "    RORight (Exit f b)"
    , ""
    , -- typed re-throw helper for the timeout-timer case: a concrete
      -- combined-error signature so the `Timeout` member widens in direct
      -- checking position (member→variant widening does not fire through the
      -- `ioBind`/`match` inference path).
      "__failTimeout : forall (e : Type) (a : Type). IO (| TimeoutError | e |) a"
    , "let __failTimeout = throwIO Timeout"
    , ""
    , -- §18.1.6 timeout: when the timer fires first the result is the typed
      -- failure `Fail Timeout`; otherwise the computation's outcome passes
      -- through. A typed `Fail e` is re-raised by `__reraiseCause` (which throws
      -- the typed error directly), and any non-typed cause is re-raised too —
      -- so a single `Failure c` arm covers every cause, and its free result
      -- error unifies to the combined channel with no variant widening.
      "timeout : forall (e : Type) (a : Type). Duration -> IO e a -> IO (| TimeoutError | e |) a"
    , "let timeout d io ="
    , "    ioBind (__timeout (durationNanos d) io) (\\o ->"
    , "      match o"
    , "      case TOTimedOut -> __failTimeout"
    , "      case TOExit (Success v) -> ioPure v"
    , "      case TOExit (Failure c) -> __reraiseCause c)"
    , ""
    , -- §18.1.6 race: the first branch to complete wins; the loser is
      -- interrupted (RaceLost) and awaited. A winning typed failure re-fails in
      -- the combined channel and any non-typed cause is re-raised — both via
      -- `__reraiseCause`, whose free result-error type unifies to the combined
      -- channel directly (no two-variable-variant widening, which is ambiguous).
      "race : forall (e : Type) (a : Type) (f : Type) (b : Type). IO e a -> IO f b -> IO (| e | f |) (RaceResult a b)"
    , "let race left right ="
    , "    ioBind (__race left right) (\\o ->"
    , "      match o"
    , "      case ROLeft (Success v) -> ioPure (LeftWins v)"
    , "      case ROLeft (Failure c) -> __reraiseCause c"
    , "      case RORight (Success v) -> ioPure (RightWins v)"
    , "      case RORight (Failure c) -> __reraiseCause c)"
    , ""
    , -- RC4: `throwError`/`catchError` are the §19.1 `MonadError` members
      -- (resolved via the carrier's dictionary), NOT free IO-only functions.
      -- The `IO e` instance below provides them for IO; `raise` stays a
      -- distinct §28 surface name.  (Defining a free function of the same
      -- name as a trait member would be E_DUPLICATE_DECLARATION.)
      "raise : forall (e : Type) (a : Type). e -> IO e a"
    , "let raise err = throwIO err"
    , ""
    , "identity : forall (a : Type). a -> a"
    , "let identity x = x"
    , ""
    , "(|>) : forall (a : Type) (b : Type). a -> (a -> b) -> b"
    , "let (|>) x f = f x"
    , ""
    , "(<|) : forall (a : Type) (b : Type). (a -> b) -> a -> b"
    , "let (<|) f x = f x"
    , ""
    , "listAppend : forall (a : Type). List a -> List a -> List a"
    , "let listAppend xs ys ="
    , "    match xs"
    , "    case Nil -> ys"
    , "    case x :: rest -> x :: listAppend rest ys"
    , ""
    , "concatMap : forall (a : Type) (b : Type). (a -> List b) -> List a -> List b"
    , "let concatMap f xs ="
    , "    match xs"
    , "    case Nil -> Nil"
    , "    case x :: rest -> listAppend (f x) (concatMap f rest)"
    , ""
    , "listLength : forall (a : Type). List a -> Integer"
    , "let listLength xs ="
    , "    match xs"
    , "    case Nil -> 0"
    , "    case _ :: rest -> addInt 1 (listLength rest)"
    , ""
    , -- §28.2 collection-basics surface (§20.10.11 as-if list model). The
      -- Array/Set/Map carriers are list-backed at runtime; the '__*'
      -- conversion prims are the identity on the element stream, so these
      -- terms are defined over List operations. Set/Map identify elements
      -- and keys by Eq, deduplicating on the list model.
      "__listIndex : forall (a : Type). List a -> Integer -> Option a"
    , "let __listIndex xs i ="
    , "    match xs"
    , "    case Nil -> None"
    , "    case x :: rest -> if leInt i 0 then Some x else __listIndex rest (subInt i 1)"
    , ""
    , "arrayEmpty : forall (a : Type). Array a"
    , "let arrayEmpty = __arrayFromList Nil"
    , ""
    , "arraySingleton : forall (a : Type). a -> Array a"
    , "let arraySingleton x = __arrayFromList (x :: Nil)"
    , ""
    , "arrayFromList : forall (a : Type). List a -> Array a"
    , "let arrayFromList xs = __arrayFromList xs"
    , ""
    , "arrayToList : forall (a : Type). Array a -> List a"
    , "let arrayToList xs = __arrayToList xs"
    , ""
    , "arrayLength : forall (a : Type). Array a -> Nat"
    , "let arrayLength xs = natOfInt (listLength (__arrayToList xs))"
    , ""
    , "arrayGet : forall (a : Type). Array a -> Nat -> Option a"
    , "let arrayGet xs i = __listIndex (__arrayToList xs) (natToInt i)"
    , ""
    , -- the proof-carrying §28.2 'arrayIndex' (in-bounds total indexing);
      -- the in-bounds proof makes the lookup total, so it delegates to
      -- the trapping primitive '__arrayIndexUnsafe' (out-of-bounds is
      -- unreachable under the supplied proof).
      "arrayIndex : forall (a : Type). (xs : Array a) -> (i : Nat) -> (@_ : (i < arrayLength xs) = True) -> a"
    , "let arrayIndex xs i = __arrayIndexUnsafe xs (natToInt i)"
    , ""
    , "sizedArrayLength : forall (n : Nat) (a : Type). SizedArray n a -> Nat"
    , "let sizedArrayLength xs ="
    , "    match xs"
    , "    case MkSizedArray elements -> natOfInt (listLength elements)"
    , ""
    , "__sizedArrayIndexNat : forall (n : Nat) (a : Type). (xs : SizedArray n a) -> (i : Nat) -> (@_ : (i < n) = True) -> a"
    , "let __sizedArrayIndexNat xs i ="
    , "    match xs"
    , "    case MkSizedArray elements -> __arrayIndexUnsafe (__arrayFromList elements) (natToInt i)"
    , ""
    , "sizedArrayIndex : forall (n : Nat) (a : Type). SizedArray n a -> Fin n -> a"
    , "let sizedArrayIndex xs i = __sizedArrayIndexNat xs i.value @i.isLt"
    , ""
    , "sizedArrayToArray : forall (n : Nat) (a : Type). SizedArray n a -> Array a"
    , "let sizedArrayToArray xs ="
    , "    match xs"
    , "    case MkSizedArray elements -> __arrayFromList elements"
    , ""
    , "arrayAsSized : forall (a : Type). (xs : Array a) -> exists (n : Nat). SizedArray n a"
    , "let arrayAsSized xs = seal exists (n = arrayLength xs). MkSizedArray (__arrayToList xs) as exists (n : Nat). SizedArray n a"
    , ""
    , "setEmpty : forall (a : Type). (@_ : Eq a) -> Set a"
    , "let setEmpty = __setFromList Nil"
    , ""
    , "setSingleton : forall (a : Type). (@_ : Eq a) -> a -> Set a"
    , "let setSingleton x = __setFromList (x :: Nil)"
    , ""
    , "setMember : forall (a : Type). (@_ : Eq a) -> a -> Set a -> Bool"
    , "let setMember x s = __anyEq (\\p -> \\q -> p == q) x (__setToList s)"
    , ""
    , "setInsert : forall (a : Type). (@_ : Eq a) -> a -> Set a -> Set a"
    , "let setInsert x s = if setMember x s then s else __setFromList (x :: __setToList s)"
    , ""
    , "__deleteEq : forall (a : Type). (a -> a -> Bool) -> a -> List a -> List a"
    , "let __deleteEq eq x xs ="
    , "    match xs"
    , "    case Nil -> Nil"
    , "    case y :: rest -> if eq x y then __deleteEq eq x rest else y :: __deleteEq eq x rest"
    , ""
    , "setDelete : forall (a : Type). (@_ : Eq a) -> a -> Set a -> Set a"
    , "let setDelete x s = __setFromList (__deleteEq (\\p -> \\q -> p == q) x (__setToList s))"
    , ""
    , "setSize : forall (a : Type). Set a -> Nat"
    , "let setSize s = natOfInt (listLength (__setToList s))"
    , ""
    , "mapEmpty : forall (k : Type) (v : Type). (@_ : Eq k) -> Map k v"
    , "let mapEmpty = __mapFromEntries Nil"
    , ""
    , "mapSingleton : forall (k : Type) (v : Type). (@_ : Eq k) -> k -> v -> Map k v"
    , "let mapSingleton kx vx = __mapFromEntries ((key = kx, value = vx) :: Nil)"
    , ""
    , "__mapDeleteKey : forall (k : Type) (v : Type). (k -> k -> Bool) -> k -> List (key : k, value : v) -> List (key : k, value : v)"
    , "let __mapDeleteKey eq k0 es ="
    , "    match es"
    , "    case Nil -> Nil"
    , "    case e :: rest -> if eq k0 e.key then __mapDeleteKey eq k0 rest else e :: __mapDeleteKey eq k0 rest"
    , ""
    , "mapInsert : forall (k : Type) (v : Type). (@_ : Eq k) -> k -> v -> Map k v -> Map k v"
    , "let mapInsert kx vx m = __mapFromEntries ((key = kx, value = vx) :: __mapDeleteKey (\\p -> \\q -> p == q) kx (__mapToList m))"
    , ""
    , "mapDelete : forall (k : Type) (v : Type). (@_ : Eq k) -> k -> Map k v -> Map k v"
    , "let mapDelete kx m = __mapFromEntries (__mapDeleteKey (\\p -> \\q -> p == q) kx (__mapToList m))"
    , ""
    , "__mapLookupKey : forall (k : Type) (v : Type). (k -> k -> Bool) -> k -> List (key : k, value : v) -> Option v"
    , "let __mapLookupKey eq k0 es ="
    , "    match es"
    , "    case Nil -> None"
    , "    case e :: rest -> if eq k0 e.key then Some e.value else __mapLookupKey eq k0 rest"
    , ""
    , "mapLookup : forall (k : Type) (v : Type). (@_ : Eq k) -> k -> Map k v -> Option v"
    , "let mapLookup kx m = __mapLookupKey (\\p -> \\q -> p == q) kx (__mapToList m)"
    , ""
    , "mapMember : forall (k : Type) (v : Type). (@_ : Eq k) -> k -> Map k v -> Bool"
    , "let mapMember kx m ="
    , "    match mapLookup kx m"
    , "    case Some _ -> True"
    , "    case None -> False"
    , ""
    , "mapSize : forall (k : Type) (v : Type). Map k v -> Nat"
    , "let mapSize m = natOfInt (listLength (__mapToList m))"
    , ""
    , "orElse : forall (a : Type). Option a -> a -> a"
    , "let orElse o d ="
    , "    match o"
    , "    case Some x -> x"
    , "    case None -> d"
    , ""
    , "instance Zero Integer ="
    , "    let zero = 0"
    , ""
    , "instance One Integer ="
    , "    let one = 1"
    , ""
    , "instance Zero Double ="
    , "    let zero = 0.0"
    , ""
    , "instance One Double ="
    , "    let one = 1.0"
    , ""
    , "instance Zero Nat ="
    , "    let zero = natOfInt 0"
    , ""
    , "instance One Nat ="
    , "    let one = natOfInt 1"
    , ""
    , "instance Add Nat ="
    , "    let add x y = natAdd x y"
    , ""
    , "instance Mul Nat ="
    , "    let multiply x y = natMultiply x y"
    , ""
    , "instance Negatable Double ="
    , "    let negate x = negDouble x"
    , ""
    , -- §28.2.3 Nat partial subtraction: subDefined x y = (y <= x); the
      -- prelude MUST NOT define Nat subtraction as saturating.
      "instance CheckedSub Nat ="
    , "    let subDefined x y = leInt (natToInt y) (natToInt x)"
    , "    let subtract x y @p = natOfInt (subInt (natToInt x) (natToInt y))"
    , ""
    , -- §28.2.3 Float/Double subtraction is total (subDefined = True);
      -- it does NOT imply the algebraic FieldLike/Ring/Semiring laws.
      "instance CheckedSub Double ="
    , "    let subDefined x y = True"
    , "    let subtract x y @p = subDouble x y"
    , ""
    , "instance CheckedDiv Nat ="
    , "    let divDefined x y = not (eqInt (natToInt y) 0)"
    , "    let divide x y @p = natOfInt (divInt (natToInt x) (natToInt y))"
    , "    let divDefinedOnlyNonZero = unsafeAssertProof \"Nat division is defined only for nonzero divisors\""
    , "    let divDefinedForNonZero = unsafeAssertProof \"Nat division is defined for every nonzero divisor\""
    , ""
    , "instance CheckedMod Nat ="
    , "    let modDefined x y = not (eqInt (natToInt y) 0)"
    , "    let modulo x y @p = natOfInt (modInt (natToInt x) (natToInt y))"
    , "    let modDefinedOnlyNonZero = unsafeAssertProof \"Nat modulo is defined only for nonzero divisors\""
    , "    let modDefinedForNonZero = unsafeAssertProof \"Nat modulo is defined for every nonzero divisor\""
    , ""
    , "instance CheckedDiv Double ="
    , "    let divDefined x y = not (eqDouble y 0.0)"
    , "    let divide x y @p = divDouble x y"
    , "    let divDefinedOnlyNonZero = unsafeAssertProof \"Double division is defined only for nonzero divisors\""
    , "    let divDefinedForNonZero = unsafeAssertProof \"Double division is defined for every nonzero divisor\""
    , ""
    , "instance IsSet Nat"
    , "derive ExactNaturalRepresentation Nat"
    , "instance IsSet Integer"
    , -- §28.2.3 mandated algebraic instances. Nat has no
      -- Negatable/AdditiveGroup/Ring/FieldLike instance.
      "instance AdditiveMonoid Nat ="
    , "    let addAssoc = unsafeAssertProof \"Nat addition is associative\""
    , "    let addLeftIdentity = unsafeAssertProof \"Nat zero is a left additive identity\""
    , "    let addRightIdentity = unsafeAssertProof \"Nat zero is a right additive identity\""
    , "instance CommutativeAdditiveMonoid Nat ="
    , "    let addCommutative = unsafeAssertProof \"Nat addition is commutative\""
    , "instance MultiplicativeMonoid Nat ="
    , "    let mulAssoc = unsafeAssertProof \"Nat multiplication is associative\""
    , "    let mulLeftIdentity = unsafeAssertProof \"Nat one is a left multiplicative identity\""
    , "    let mulRightIdentity = unsafeAssertProof \"Nat one is a right multiplicative identity\""
    , "instance AdditivelyNoncommutativeSemiring Nat ="
    , "    let mulLeftZero = unsafeAssertProof \"Nat zero annihilates multiplication on the left\""
    , "    let mulRightZero = unsafeAssertProof \"Nat zero annihilates multiplication on the right\""
    , "    let leftDistribute = unsafeAssertProof \"Nat multiplication distributes on the left\""
    , "    let rightDistribute = unsafeAssertProof \"Nat multiplication distributes on the right\""
    , "instance Semiring Nat"
    , "instance OrderedAdditive Nat ="
    , "    let addMonotoneLeft = unsafeAssertProof \"Nat addition is monotone on the left\""
    , "    let addMonotoneRight = unsafeAssertProof \"Nat addition is monotone on the right\""
    , "instance OrderedSemiring Nat ="
    , "    let mulNonnegativeMonotone = unsafeAssertProof \"Nat multiplication by a nonnegative value is monotone\""
    , "instance EuclideanSemiring Nat ="
    , "    let divAndModSameDomain = unsafeAssertProof \"Nat division and modulo have the same domain\""
    , "    let divModIdentity = unsafeAssertProof \"Nat division and modulo satisfy the Euclidean identity\""
    , ""
    , -- Integer (and therefore Int, definitionally) get the full ring
      -- tower but NOT FieldLike (integer division is not a field op).
      "instance AdditiveMonoid Integer ="
    , "    let addAssoc = unsafeAssertProof \"Integer addition is associative\""
    , "    let addLeftIdentity = unsafeAssertProof \"Integer zero is a left additive identity\""
    , "    let addRightIdentity = unsafeAssertProof \"Integer zero is a right additive identity\""
    , "instance CommutativeAdditiveMonoid Integer ="
    , "    let addCommutative = unsafeAssertProof \"Integer addition is commutative\""
    , "instance AdditiveGroup Integer ="
    , "    let addLeftInverse = unsafeAssertProof \"Integer negation is a left additive inverse\""
    , "    let addRightInverse = unsafeAssertProof \"Integer negation is a right additive inverse\""
    , "instance MultiplicativeMonoid Integer ="
    , "    let mulAssoc = unsafeAssertProof \"Integer multiplication is associative\""
    , "    let mulLeftIdentity = unsafeAssertProof \"Integer one is a left multiplicative identity\""
    , "    let mulRightIdentity = unsafeAssertProof \"Integer one is a right multiplicative identity\""
    , "instance AdditivelyNoncommutativeSemiring Integer ="
    , "    let mulLeftZero = unsafeAssertProof \"Integer zero annihilates multiplication on the left\""
    , "    let mulRightZero = unsafeAssertProof \"Integer zero annihilates multiplication on the right\""
    , "    let leftDistribute = unsafeAssertProof \"Integer multiplication distributes on the left\""
    , "    let rightDistribute = unsafeAssertProof \"Integer multiplication distributes on the right\""
    , "instance Semiring Integer"
    , "instance Ring Integer ="
    , "    let subDefinedAlways = unsafeAssertProof \"Integer subtraction is total\""
    , "    let subtractAsAddInverse = unsafeAssertProof \"Integer subtraction is addition of the inverse\""
    , "instance OrderedAdditive Integer ="
    , "    let addMonotoneLeft = unsafeAssertProof \"Integer addition is monotone on the left\""
    , "    let addMonotoneRight = unsafeAssertProof \"Integer addition is monotone on the right\""
    , "instance OrderedSemiring Integer ="
    , "    let mulNonnegativeMonotone = unsafeAssertProof \"Integer multiplication by a nonnegative value is monotone\""
    , ""
    , -- §28.2 Rational: the exact ratio type. It gets the full operation
      -- trait set (Eq/Ord/Show/Zero/One/Add/Mul/Negatable/CheckedSub/
      -- CheckedDiv) and the full algebraic tower INCLUDING FieldLike
      -- (§28.2.2: "Rational MUST receive FieldLike"). subDefined = True;
      -- divDefined x y = (y /= zero).
      "instance Eq Rational ="
    , "    let (==) x y = eqRat x y"
    , ""
    , "instance Ord Rational ="
    , "    let compare x y = if ltRat x y then LT elif eqRat x y then EQ else GT"
    , ""
    , "instance Show Rational ="
    , "    let show x = showRat x"
    , ""
    , "instance Zero Rational ="
    , "    let zero = __ratOfInt 0"
    , ""
    , "instance One Rational ="
    , "    let one = __ratOfInt 1"
    , ""
    , "instance Add Rational ="
    , "    let add x y = addRat x y"
    , ""
    , "instance Mul Rational ="
    , "    let multiply x y = mulRat x y"
    , ""
    , "instance Negatable Rational ="
    , "    let negate x = negRat x"
    , ""
    , "instance CheckedSub Rational ="
    , "    let subDefined x y = True"
    , "    let subtract x y @p = subRat x y"
    , ""
    , "instance CheckedDiv Rational ="
    , "    let divDefined x y = not (eqRat y (__ratOfInt 0))"
    , "    let divide x y @p = divRat x y"
    , "    let divDefinedOnlyNonZero = unsafeAssertProof \"Rational division is defined only for nonzero divisors\""
    , "    let divDefinedForNonZero = unsafeAssertProof \"Rational division is defined for every nonzero divisor\""
    , ""
    , "instance FromInteger Rational ="
    , "    let fromInteger n = __ratOfInt (natToInt n)"
    , ""
    , "instance FromFloat Rational ="
    , "    let fromFloat d = ratOfDouble d"
    , ""
    , "instance IsSet Rational"
    , -- (FromFloat Float and FromFloat Double coincide: Float = Double.)
      "instance AdditiveMonoid Rational ="
    , "    let addAssoc = unsafeAssertProof \"Rational addition is associative\""
    , "    let addLeftIdentity = unsafeAssertProof \"Rational zero is a left additive identity\""
    , "    let addRightIdentity = unsafeAssertProof \"Rational zero is a right additive identity\""
    , "instance CommutativeAdditiveMonoid Rational ="
    , "    let addCommutative = unsafeAssertProof \"Rational addition is commutative\""
    , "instance AdditiveGroup Rational ="
    , "    let addLeftInverse = unsafeAssertProof \"Rational negation is a left additive inverse\""
    , "    let addRightInverse = unsafeAssertProof \"Rational negation is a right additive inverse\""
    , "instance MultiplicativeMonoid Rational ="
    , "    let mulAssoc = unsafeAssertProof \"Rational multiplication is associative\""
    , "    let mulLeftIdentity = unsafeAssertProof \"Rational one is a left multiplicative identity\""
    , "    let mulRightIdentity = unsafeAssertProof \"Rational one is a right multiplicative identity\""
    , "instance AdditivelyNoncommutativeSemiring Rational ="
    , "    let mulLeftZero = unsafeAssertProof \"Rational zero annihilates multiplication on the left\""
    , "    let mulRightZero = unsafeAssertProof \"Rational zero annihilates multiplication on the right\""
    , "    let leftDistribute = unsafeAssertProof \"Rational multiplication distributes on the left\""
    , "    let rightDistribute = unsafeAssertProof \"Rational multiplication distributes on the right\""
    , "instance Semiring Rational"
    , "instance Ring Rational ="
    , "    let subDefinedAlways = unsafeAssertProof \"Rational subtraction is total\""
    , "    let subtractAsAddInverse = unsafeAssertProof \"Rational subtraction is addition of the inverse\""
    , "instance OrderedAdditive Rational ="
    , "    let addMonotoneLeft = unsafeAssertProof \"Rational addition is monotone on the left\""
    , "    let addMonotoneRight = unsafeAssertProof \"Rational addition is monotone on the right\""
    , "instance OrderedSemiring Rational ="
    , "    let mulNonnegativeMonotone = unsafeAssertProof \"Rational multiplication by a nonnegative value is monotone\""
    , "instance FieldLike Rational ="
    , "    let divisionRightInverse = unsafeAssertProof \"Rational division has a right inverse on its domain\""
    , ""
    , -- §28.2.2: Float/Double MUST NOT receive Semiring/Ring/FieldLike
      -- under raw-bit Eq. They keep only the operation traits above.
      --
      -- The 'empty' element of each lawful 'Monoid' lives in its sibling
      -- 'Pointed' instance (the 'Monoid' supertrait), separate from the 'append'
      -- + laws below. 'String'/'List a' supply both halves here.
      "instance Pointed String ="
    , "    let empty = \"\""
    , ""
    , "instance Pointed (List a) ="
    , "    let empty = Nil"
    , ""
    , -- LAWFUL Monoid: 'String' is a set ('instance IsSet String'), so its
      -- equational laws are honestly h-props and discharge through the gated
      -- 'unsafeAssertProof' escape; the §11.4 IsProp-under-Pi solver resolves the
      -- 'IsProp (forall xs. l = r)' obligation by recovering the carrier 'String'
      -- and threading its 'IsSet'. 'empty' comes from the 'Pointed String'
      -- supertrait above.
      "instance Monoid String ="
    , "    let append x y = stringAppend x y"
    , "    let appendAssoc = unsafeAssertProof \"Monoid String: append is associative\""
    , "    let appendLeftIdentity = unsafeAssertProof \"Monoid String: empty is a left identity\""
    , "    let appendRightIdentity = unsafeAssertProof \"Monoid String: empty is a right identity\""
    , ""
    , -- LAWFUL Monoid: List's monoid laws are PROVEN by structural induction (the
      -- lemmas 'listAppendRightIdentity'/'listAppendAssoc' are defined further
      -- below, AFTER 'cong'/'subst', whose values they consume — a forward
      -- reference to 'cong' leaves its value unelaborated and mis-resolves the
      -- proof's implicit equality endpoints), so this instance holds for EVERY
      -- element type 'a' and needs no 'IsSet' and no 'unsafeAssertProof'. The
      -- law params are IMPLICIT ('forall (x y z : a).'), bound here with the
      -- '@'-implicit binder form; 'append' reduces to the concrete 'listAppend'
      -- and 'empty' to 'Nil' (from the 'Pointed (List a)' supertrait), so each
      -- proof typechecks. 'appendLeftIdentity' is definitional ('append empty x ≡
      -- listAppend Nil x ≡ x'), hence 'refl'.
      "instance Monoid (List a) ="
    , "    let append x y = listAppend x y"
    , "    let appendLeftIdentity @x = refl"
    , "    let appendRightIdentity @x = listAppendRightIdentity x"
    , "    let appendAssoc @x @y @z = listAppendAssoc x y z"
    , ""
    , "instance Functor List ="
    , "    let map f xs ="
    , "        match xs"
    , "        case Nil -> Nil"
    , "        case x :: rest -> f x :: map f rest"
    , ""
    , -- §28.2.2: List is the standard nondeterminism monad — `pureA` is the
      -- singleton list and bind is `concatMap` (Cartesian sequencing).
      "instance Applicative List ="
    , "    let pureA x = x :: Nil"
    , "    let liftA2 f xs ys = concatMap (\\x -> map (f x) ys) xs"
    , ""
    , "instance Monad List ="
    , "    let (>>=) xs f = concatMap f xs"
    , ""
    , "instance Functor Option ="
    , "    let map f o ="
    , "        match o"
    , "        case Some x -> Some (f x)"
    , "        case None -> None"
    , ""
    , "instance Foldable List ="
    , "    let foldr f z xs ="
    , "        match xs"
    , "        case Nil -> z"
    , "        case x :: rest -> f x (foldr f z rest)"
    , "    let foldl f acc xs ="
    , "        match xs"
    , "        case Nil -> acc"
    , "        case x :: rest -> foldl f (f acc x) rest"
    , "    let foldMap f xs ="
    , "        match xs"
    , "        case Nil -> empty"
    , "        case x :: rest -> append (f x) (foldMap f rest)"
    , ""
    , "instance Foldable Option ="
    , "    let foldr f z o ="
    , "        match o"
    , "        case None -> z"
    , "        case Some x -> f x z"
    , "    let foldl f acc o ="
    , "        match o"
    , "        case None -> acc"
    , "        case Some x -> f acc x"
    , "    let foldMap f o ="
    , "        match o"
    , "        case None -> empty"
    , "        case Some x -> f x"
    , ""
    , "instance Filterable List ="
    , "    let filter p xs ="
    , "        match xs"
    , "        case Nil -> Nil"
    , "        case x :: rest -> if p x then x :: filter p rest else filter p rest"
    , ""
    , "instance FilterMap List ="
    , "    let filterMap f xs ="
    , "        match xs"
    , "        case Nil -> Nil"
    , "        case x :: rest ->"
    , "            match f x"
    , "            case Some y -> y :: filterMap f rest"
    , "            case None -> filterMap f rest"
    , ""
    , "instance Traversable List ="
    , "    let traverse f xs ="
    , "        match xs"
    , "        case Nil -> pureA Nil"
    , "        case x :: rest -> liftA2 (\\h -> \\t -> h :: t) (f x) (traverse f rest)"
    , ""
    , "instance Traversable Option ="
    , "    let traverse f o ="
    , "        match o"
    , "        case None -> pureA None"
    , "        case Some x -> liftA2 (\\v -> \\u -> Some v) (f x) (pureA True)"
    , ""
    , "(++) : forall (a : Type). (@_ : Monoid a) -> a -> a -> a"
    , "let (++) x y = append x y"
    , ""
    , -- §28.2 Eq/Ord/Show for the mandated container types List/Option/Result.
      -- Each `match` keeps any nested `match` in its LAST arm (non-last arms use
      -- a parenthesized inline match) so the layout parser groups arms correctly.
      "__ordChain : Ordering -> Ordering -> Ordering"
    , "let __ordChain a b ="
    , "    match a"
    , "    case EQ -> b"
    , "    case LT -> LT"
    , "    case GT -> GT"
    , ""
    , "instance IsSet a => IsSet (List a)"
    , "instance IsSet a => IsSet (Array a)"
    , "instance IsSet a => IsSet (Option a)"
    , "instance (IsSet e, IsSet a) => IsSet (Result e a)"
    , ""
    , "instance Eq a => Eq (List a) ="
    , "    let (==) xs ys ="
    , "        match xs"
    , "        case Nil -> (match ys case Nil -> True case z :: zs -> False)"
    , "        case x :: xrest ->"
    , "          match ys"
    , "          case Nil -> False"
    , "          case y :: yrest -> if x == y then xrest == yrest else False"
    , ""
    , "instance Ord a => Ord (List a) ="
    , "    let compare xs ys ="
    , "        match xs"
    , "        case Nil -> (match ys case Nil -> EQ case z :: zs -> LT)"
    , "        case x :: xrest ->"
    , "          match ys"
    , "          case Nil -> GT"
    , "          case y :: yrest -> __ordChain (compare x y) (compare xrest yrest)"
    , ""
    , -- §10.4 Array equality/order are the elementwise (list) relations on
      -- the array's element sequence; this also discharges the Eq
      -- superclass of the §14.1.3 'Hashable (Array a)' instance.
      "instance Eq a => Eq (Array a) ="
    , "    let (==) xs ys = arrayToList xs == arrayToList ys"
    , ""
    , "instance Ord a => Ord (Array a) ="
    , "    let compare xs ys = compare (arrayToList xs) (arrayToList ys)"
    , ""
    , "__showListGo : forall (a : Type). (@_ : Show a) -> Bool -> List a -> String"
    , "let __showListGo first xs ="
    , "    match xs"
    , "    case Nil -> \"\""
    , "    case x :: rest -> (if first then show x else \", \" ++ show x) ++ __showListGo False rest"
    , ""
    , "instance Show a => Show (List a) ="
    , "    let show xs = \"[\" ++ __showListGo True xs ++ \"]\""
    , ""
    , "instance Eq a => Eq (Option a) ="
    , "    let (==) xo yo ="
    , "        match xo"
    , "        case None -> (match yo case None -> True case Some w -> False)"
    , "        case Some x ->"
    , "          match yo"
    , "          case None -> False"
    , "          case Some y -> x == y"
    , ""
    , "instance Ord a => Ord (Option a) ="
    , "    let compare xo yo ="
    , "        match xo"
    , "        case None -> (match yo case None -> EQ case Some w -> LT)"
    , "        case Some x ->"
    , "          match yo"
    , "          case None -> GT"
    , "          case Some y -> compare x y"
    , ""
    , "instance Show a => Show (Option a) ="
    , "    let show o ="
    , "        match o"
    , "        case None -> \"None\""
    , "        case Some x -> \"Some \" ++ show x"
    , ""
    , "instance (Eq e, Eq a) => Eq (Result e a) ="
    , "    let (==) xr yr ="
    , "        match xr"
    , "        case Ok x -> (match yr case Ok y -> x == y case Err w -> False)"
    , "        case Err x ->"
    , "          match yr"
    , "          case Ok y -> False"
    , "          case Err y -> x == y"
    , ""
    , -- §28.2 Ord for Result orders Err before Ok (the conventional
      -- error-channel-low order), then by the contained value.
      "instance (Ord e, Ord a) => Ord (Result e a) ="
    , "    let compare xr yr ="
    , "        match xr"
    , "        case Err x -> (match yr case Err y -> compare x y case Ok w -> LT)"
    , "        case Ok x ->"
    , "          match yr"
    , "          case Err y -> GT"
    , "          case Ok y -> compare x y"
    , ""
    , "instance (Show e, Show a) => Show (Result e a) ="
    , "    let show r ="
    , "        match r"
    , "        case Ok x -> \"Ok \" ++ show x"
    , "        case Err e -> \"Err \" ++ show e"
    , ""
    , -- §28.2.2: Result is the standard error-short-circuiting monad over
      -- a fixed error type; an Err halts the computation.
      "instance Applicative (Result e) ="
    , "    let pureA x = Ok x"
    , "    let liftA2 f ra rb ="
    , "        match ra"
    , "        case Err e -> Err e"
    , "        case Ok a -> (match rb case Err e2 -> Err e2 case Ok b -> Ok (f a b))"
    , ""
    , "instance Monad (Result e) ="
    , "    let (>>=) r f ="
    , "        match r"
    , "        case Err e -> Err e"
    , "        case Ok x -> f x"
    , ""
    , "sequence : forall (t : (0 A : Type) -> Type) (f : (0 A : Type) -> Type) (a : Type). (@_ : Traversable t) -> (@_ : Applicative f) -> t (f a) -> f (t a)"
    , "let sequence xs = traverse (\\v -> v) xs"
    , ""
    , -- §28.2: nonZero x = x /= zero
      "nonZero : forall (a : Type). (@_ : Eq a) -> (@_ : Zero a) -> a -> Bool"
    , "let nonZero x = not (x == zero)"
    , ""
    , -- §28.2 effectful traversal helpers over a Foldable source. 'for_'
      -- runs an applicative action for each element, discarding results;
      -- 'sequence_' runs a Foldable of actions for effect.
      "for_ : forall (t : (0 A : Type) -> Type) (f : (0 A : Type) -> Type) (a : Type) (b : Type). (@_ : Foldable t) -> (@_ : Applicative f) -> t a -> (a -> f b) -> f Unit"
    , "let for_ xs act = foldr (\\x -> \\acc -> liftA2 (\\u -> \\v -> Unit) (act x) acc) (pureA Unit) xs"
    , ""
    , "sequence_ : forall (t : (0 A : Type) -> Type) (f : (0 A : Type) -> Type) (a : Type). (@_ : Foldable t) -> (@_ : Applicative f) -> t (f a) -> f Unit"
    , "let sequence_ xs = foldr (\\m -> \\acc -> liftA2 (\\u -> \\v -> Unit) m acc) (pureA Unit) xs"
    , ""
    , "summon : (0 t : Type) -> (@_ : IsTrait t) -> (@evidence : t) -> t" -- §16.3.3.1
    , "let summon (0 t : Type) (@_ : IsTrait t) (@evidence : t) = evidence"
    , ""
    , -- §28.2 proof and equality helpers over propositional equality.
      -- This implementation does not yet propagate the branch-local endpoint
      -- equality forced by matching 'refl' (see docs/notes/KNOWN_SPEC_ISSUES.md), so
      -- these helpers cannot be defined by 'match eq case refl -> ...'. They
      -- are realized through primitives that respect the operational
      -- meaning of erased, proof-irrelevant equality: 'subst'/'pathInd'
      -- transport by the identity (the equality witness is erased), and
      -- sym/trans/cong produce the relevant erased proof. The spec
      -- signatures are exactly as in §28.2.
      "absurd : forall (@0 a : Type). Void -> a"
    , "let absurd v = __absurd v"
    , ""
    , "subst.{u, v} : forall (@parametric 0 a : Type u) (@parametric 0 p : (ordinary 0 z : a) -> Type v) (@ordinary 0 x : a) (@ordinary 0 y : a). x = y -> p x -> p y"
    , "let subst.{u, v} eq px = __transport px"
    , ""
    , "sym : forall (@0 a : Type) (@0 x : a) (@0 y : a). x = y -> y = x"
    , "let sym eq = __eqProof"
    , ""
    , "trans : forall (@0 a : Type) (@0 x : a) (@0 y : a) (@0 z : a). x = y -> y = z -> x = z"
    , "let trans p q = __eqProof"
    , ""
    , "cong : forall (@0 a : Type) (@0 b : Type) (@0 x : a) (@0 y : a). (f : a -> b) -> x = y -> f x = f y"
    , "let cong f eq = __eqProof"
    , ""
    , -- Canonical Nat right identity is proved structurally because natAdd
      -- recurses on its left argument. The erased provider argument records
      -- the coherent AdditiveMonoid instance selected by the arithmetic
      -- elaborator; the proof itself is stated over canonical natAdd so a
      -- portable KCore checker need not unfold an instance implementation.
      "natAddRightIdentity : (@0 provider : AdditiveMonoid Nat) -> (n : Nat) -> (=) (natAdd n Nat.Zero) n"
    , "let natAddRightIdentity @provider n ="
    , "    match n"
    , "    case Nat.Zero -> refl"
    , "    case Nat.Succ predecessor -> cong (\\value -> Nat.Succ value) (natAddRightIdentity @provider predecessor)"
    , ""
    , -- The two non-definitional List monoid laws, PROVEN by structural
      -- induction on the spine — sound for EVERY element type 'a', needing no
      -- 'IsSet' and no 'unsafeAssertProof' (they discharge the §28.2.2
      -- 'Monoid (List a)' laws above). Top-level recursive lemmas take
      -- the spine EXPLICITLY so the body may 'match' and recurse; the cons step
      -- lifts the inductive hypothesis through '(h ::)' via 'consCong' (its
      -- signature pins both list endpoints, so 'cong' resolves with no
      -- inference ambiguity). They sit here, AFTER 'cong'/'subst', because a
      -- proof that consumed those operations through a forward reference (their
      -- value still unelaborated) mis-resolves its implicit equality endpoints.
      -- Each 'h :: t' arm's dependent goal reduces because the §7.4.1
      -- dependent-match refinement substitutes the scrutinee by its cons.
      "consCong : forall (a : Type) (xs : List a) (ys : List a). (h : a) -> (=) xs ys -> (=) (h :: xs) (h :: ys)"
    , "let consCong h eq = cong (\\rest -> h :: rest) eq"
    , ""
    , "listAppendRightIdentity : forall (a : Type). (xs : List a) -> (=) (listAppend xs Nil) xs"
    , "let listAppendRightIdentity xs ="
    , "    match xs"
    , "    case Nil -> refl"
    , "    case h :: t -> consCong h (listAppendRightIdentity t)"
    , ""
    , "listAppendAssoc : forall (a : Type). (xs : List a) -> (ys : List a) -> (zs : List a) -> (=) (listAppend (listAppend xs ys) zs) (listAppend xs (listAppend ys zs))"
    , "let listAppendAssoc xs ys zs ="
    , "    match xs"
    , "    case Nil -> refl"
    , "    case h :: t -> consCong h (listAppendAssoc t ys zs)"
    , ""
    , -- §21.6 semantic-reflection witness algebra (compile-time/erased).
      -- Bodies use '__eqProof', the same magic-inhabitant mechanism as
      -- sym/trans/cong, so the elaborator builds the dependent signatures.
      -- 'transCoreEq'/'substCoreEq' are deferred: a signature sharing a
      -- variable across implicit type-former-argument positions (the
      -- middle 'y' of transitivity) currently mis-infers CoreEq's implicit
      -- indices at the application site; see SPEC_COMPLIANCE.md.
      "reflCoreEq : forall (@0 G : CoreCtx) (@0 a : Type) (@0 x : Core G a) . CoreEq x x"
    , "let reflCoreEq = __eqProof"
    , ""
    , "symCoreEq : forall (@0 G : CoreCtx) (@0 a : Type) (@0 b : Type) (@0 x : Core G a) (@0 y : Core G b) . CoreEq x y -> CoreEq y x"
    , "let symCoreEq p = __eqProof"
    , ""
    , -- §11.4: dependent path induction over the motive 'c'. The base
      -- case is transported to the (proof-irrelevantly identical) goal.
      "pathInd.{u, v} : forall (@parametric 0 a : Type u) (@ordinary 0 x : a) (@parametric 0 c : forall (@ordinary 0 y : a). (@parametric 0 pp : x = y) -> Type v). c @x @refl -> forall (@ordinary 0 y : a). (parametric 0 p : x = y) -> c @y @p"
    , "let pathInd.{u, v} base y p = __transport base"
    , ""
    , -- §10.2.1 standard Nat no-confusion projections. These are ordinary
      -- erased proof terms exported by the authenticated prelude; callers do
      -- not depend on checker-only constructor tags or source-name matching.
      "natSuccInjective : forall (m : Nat) (n : Nat). Nat.Succ m = Nat.Succ n -> m = n"
    , "let natSuccInjective proof = __eqProof"
    , ""
    , "natZeroNotSucc : forall (n : Nat). Nat.Zero = Nat.Succ n -> Void"
    , "let natZeroNotSucc proof = __eqProof"
    , ""
    , -- §11.4/§14.4 h-prop closure lemmas (admitted via '__eqProof', the same
      -- magic-inhabitant mechanism as sym/trans/cong). These are the TRUE
      -- HoTT closure facts, not derivable here without funext, so they are
      -- admitted as primitives; the compiler-owned IsProp-under-Pi solver
      -- (Kappa.Check) constructs evidence structurally out of these, so the
      -- derivation built on them stays auditable. The solver discharges
      -- 'IsProp (forall xs. l = r)' goals (e.g. a forall-quantified equational
      -- trait law) so they can be settled through the gated 'unsafeAssertProof'
      -- escape rather than raw '__eqProof'.
      --
      -- CRITICAL (Spec §14.4): Kappa v1 equality is INTENSIONAL and does NOT
      -- assume UIP. For arbitrary 'a', '(=) x y' is NOT an h-prop. It is one
      -- exactly when 'IsSet a' is available (that IS the content of
      -- 'IsSet.pathIsProp'). So 'isPropEq' DEMANDS an 'IsSet a' hypothesis; the
      -- solver must resolve that evidence and thread it, and FAIL when it is
      -- absent — never fabricate UIP. (Closure under Pi, by contrast, is
      -- unconditional, so 'isPropPi' needs no such hypothesis.)
      -- NB: the equality is written in prefix form '(=) x y'; the infix
      -- '(x = y)' inside an argument position mis-parses as a binder group.
      "isPropEq : forall (@0 a : Type) (@0 x : a) (@0 y : a). (@_ : IsSet a) -> IsProp ((=) x y)"
    , "let isPropEq = __eqProof"
    , ""
    , "isPropPi : forall (@0 a : Type) (@0 p : a -> Type). ((x : a) -> IsProp (p x)) -> IsProp (forall (@0 x : a). p x)"
    , "let isPropPi h = __eqProof"
    , ""
    , -- §28.2 escape hatch: an unchecked proof of a proposition.
      "unsafeAssertProof : forall (@0 p : Type). (@_ : IsProp p) -> (@0 reason : String) -> p"
    , "let unsafeAssertProof reason = __unsafeAssertProof"
    , ""
    , "witness : forall (a : Type). (@value : a) -> a"
    , "let witness @value = value"
    , ""
    , -- §17.3: partial active patterns that thread a residue on a miss
      "data Match (0 a : Type) (0 r : Type) : Type ="
    , "    Hit (value : a)"
    , "    Miss (residue : r)"
    , ""
    , -- §20.10.1: query modes, cardinality, and reified quantities
      "data QueryUse : Type ="
    , "    Reusable"
    , "    OneShot"
    , ""
    , "data QueryCard : Type ="
    , "    QZero"
    , "    QOne"
    , "    QZeroOrOne"
    , "    QOneOrMore"
    , "    QZeroOrMore"
    , ""
    , "data QueryMode : Type ="
    , "    QueryMode (use : QueryUse) (card : QueryCard)"
    , ""
    , "instance FromInteger Quantity ="
    , "    let fromInteger n = __quantityOfNat n"
    , ""
    , -- §20.9 standard first-class query aliases
      "type Query (0 a : Type) = QueryCore (QueryMode.QueryMode QueryUse.Reusable QueryCard.QZeroOrMore) ω a"
    , "type OnceQuery (0 a : Type) = QueryCore (QueryMode.QueryMode QueryUse.OneShot QueryCard.QZeroOrMore) ω a"
    , "type SingletonQuery (0 a : Type) = QueryCore (QueryMode.QueryMode QueryUse.Reusable QueryCard.QOne) ω a"
    , ""
    , -- §20 comprehension-lowering support library (internal). The
      -- pipeline argument comes first so the row type is solved before
      -- the generated per-row lambdas elaborate.
      "__pipeConcatMap : forall (a : Type) (b : Type). List a -> (a -> List b) -> List b"
    , "let __pipeConcatMap xs f = concatMap f xs"
    , ""
    , "__pipeMap : forall (a : Type) (b : Type). List a -> (a -> b) -> List b"
    , "let __pipeMap xs f = map f xs"
    , ""
    , "__listDrop : forall (a : Type). Integer -> List a -> List a"
    , "let __listDrop n xs ="
    , "    match xs"
    , "    case Nil -> Nil"
    , "    case x :: rest -> if leInt n 0 then xs else __listDrop (subInt n 1) rest"
    , ""
    , "__listTake : forall (a : Type). Integer -> List a -> List a"
    , "let __listTake n xs ="
    , "    match xs"
    , "    case Nil -> Nil"
    , "    case x :: rest -> if leInt n 0 then Nil else x :: __listTake (subInt n 1) rest"
    , ""
    , "__sortInsert : forall (a : Type). (a -> a -> Ordering) -> a -> List a -> List a"
    , "let __sortInsert cmp x ys ="
    , "    match ys"
    , "    case Nil -> x :: Nil"
    , "    case y :: rest ->"
    , "        match cmp x y"
    , "        case GT -> y :: __sortInsert cmp x rest"
    , "        case _ -> x :: y :: rest"
    , ""
    , "__sortBy : forall (a : Type). List a -> (a -> a -> Ordering) -> List a" -- stable (§20.6.1)
    , "let __sortBy xs cmp ="
    , "    match xs"
    , "    case Nil -> Nil"
    , "    case x :: rest -> __sortInsert cmp x (__sortBy rest cmp)"
    , ""
    , "__queryOfMatches : forall (a : Type). List a -> Query a" -- left-join inner query (§20.8)
    , "let __queryOfMatches xs = __queryFromList xs"
    , ""
    , "__distinctOnFstAcc : forall (k : Type) (r : Type). List k -> List (_1 : k, _2 : r) -> (@_ : Eq k) -> List r"
    , "let __distinctOnFstAcc seen xs ="
    , "    match xs"
    , "    case Nil -> Nil"
    , "    case p :: rest ->"
    , "        match p"
    , "        case (kx, rx) -> if __anyEq (\\a -> \\b -> a == b) kx seen then __distinctOnFstAcc seen rest else rx :: __distinctOnFstAcc (kx :: seen) rest"
    , ""
    , "__distinctOnFst : forall (k : Type) (r : Type). List (_1 : k, _2 : r) -> (@_ : Eq k) -> List r" -- keep first (§20.6.3)
    , "let __distinctOnFst xs = __distinctOnFstAcc Nil xs"
    , ""
    , "__anyEq : forall (a : Type). (a -> a -> Bool) -> a -> List a -> Bool"
    , "let __anyEq eq x ys ="
    , "    match ys"
    , "    case Nil -> False"
    , "    case y :: rest -> if eq x y then True else __anyEq eq x rest"
    , ""
    , "__distinctByAcc : forall (a : Type). (a -> a -> Bool) -> List a -> List a -> List a"
    , "let __distinctByAcc eq seen xs ="
    , "    match xs"
    , "    case Nil -> Nil"
    , "    case x :: rest -> if __anyEq eq x seen then __distinctByAcc eq seen rest else x :: __distinctByAcc eq (x :: seen) rest"
    , ""
    , "__distinctBy : forall (a : Type). List a -> (a -> a -> Bool) -> List a" -- keep first (§20.6.3)
    , "let __distinctBy xs eq = __distinctByAcc eq Nil xs"
    , ""
    , "__optionToList : forall (a : Type). Option a -> List a"
    , "let __optionToList o ="
    , "    match o"
    , "    case None -> Nil"
    , "    case Some x -> x :: Nil"
    , ""
    , -- §18.6/§20.2/§23.7 IntoQuery: the source-introduction trait for
      -- 'for'/comprehension generators. The spec declares associated
      -- members Mode/ItemQuantity/Item/SourceDemand used in toQuery's
      -- result type; this implementation cannot reference an associated
      -- type in an applied type position (cf. Iterator), so IntoQuery is
      -- surfaced with its associated 'IntoItem' type and a 'toQuery'
      -- member returning a reusable 'Query IntoItem'. The mandated §23.7
      -- instances (List/Array/Set/Option/range/QueryCore-identity) are
      -- provided. The for/comprehension lowering iterates these sources
      -- via the §20.10.11 as-if list model; toQuery is the first-class
      -- surface. See docs/notes/KNOWN_SPEC_ISSUES.md.
      "trait IntoQuery (0 src : Type) ="
    , "    IntoItem : Type"
    , "    toQuery : src -> Query IntoItem"
    , ""
    , "__intoQueryToListAs : forall (src : Type) (item : Type). (@into : IntoQuery src) -> (@0 _ : into.IntoItem = item) -> src -> List item"
    , "let __intoQueryToListAs @into source = __transport (__queryToList (into.toQuery source))"
    , ""
    , "instance IntoQuery (List a) ="
    , "    let IntoItem = a"
    , "    let toQuery xs = __queryFromList xs"
    , ""
    , "instance IntoQuery (Array a) ="
    , "    let IntoItem = a"
    , "    let toQuery xs = __queryFromList (__arrayToList xs)"
    , ""
    , "instance IntoQuery (Set a) ="
    , "    let IntoItem = a"
    , "    let toQuery s = __queryFromList (__setToList s)"
    , ""
    , "instance IntoQuery (Option a) ="
    , "    let IntoItem = a"
    , "    let toQuery o = __queryFromList (__optionToList o)"
    , ""
    , "instance IntoQuery (NumericRange v) ="
    , "    let IntoItem = v"
    , "    let toQuery r = __queryFromList (rangeToList r)"
    , ""
    , "__groupInsert : forall (k : Type) (r : Type). (k -> k -> Bool) -> k -> r -> List (key : k, rows : List r) -> List (key : k, rows : List r)"
    , "let __groupInsert eq k0 row gs ="
    , "    match gs"
    , "    case Nil -> (key = k0, rows = row :: Nil) :: Nil"
    , "    case g :: rest -> if eq g.key k0 then (key = g.key, rows = listAppend g.rows (row :: Nil)) :: rest else g :: __groupInsert eq k0 row rest"
    , ""
    , "__groupByAcc : forall (k : Type) (r : Type). (r -> k) -> (k -> k -> Bool) -> List (key : k, rows : List r) -> List r -> List (key : k, rows : List r)"
    , "let __groupByAcc keyOf eq acc xs ="
    , "    match xs"
    , "    case Nil -> acc"
    , "    case x :: rest -> __groupByAcc keyOf eq (__groupInsert eq (keyOf x) x acc) rest"
    , ""
    , "__groupBy : forall (k : Type) (r : Type). List r -> (r -> k) -> (k -> k -> Bool) -> List (key : k, rows : List r)"
    , "let __groupBy xs keyOf eq = __groupByAcc keyOf eq Nil xs" -- groups in first-encounter order (§20.7)
    , ""
    , "__aggFold : forall (r : Type) (w : Type). List r -> (r -> w) -> (@_ : Monoid w) -> w"
    , "let __aggFold rows f = foldl (\\acc x -> append acc (f x)) empty rows"
    , ""
    , "__mapEntryCombine : forall (k : Type) (v : Type). (k -> k -> Bool) -> (v -> v -> v) -> k -> v -> List (key : k, value : v) -> v"
    , "let __mapEntryCombine eq comb k0 acc rest ="
    , "    match rest"
    , "    case Nil -> acc"
    , "    case other :: more -> __mapEntryCombine eq comb k0 (if eq k0 other.key then comb acc other.value else acc) more"
    , ""
    , "__mapResolveAcc : forall (k : Type) (v : Type). (k -> k -> Bool) -> (v -> v -> v) -> List k -> List (key : k, value : v) -> List (key : k, value : v)"
    , "let __mapResolveAcc eq comb seen es ="
    , "    match es"
    , "    case Nil -> Nil"
    , "    case e :: rest -> if __anyEq eq e.key seen then __mapResolveAcc eq comb seen rest else (key = e.key, value = __mapEntryCombine eq comb e.key e.value rest) :: __mapResolveAcc eq comb (e.key :: seen) rest"
    , ""
    , "__mapResolve : forall (k : Type) (v : Type). List (key : k, value : v) -> (k -> k -> Bool) -> (v -> v -> v) -> List (key : k, value : v)"
    , "let __mapResolve es eq comb = __mapResolveAcc eq comb Nil es" -- first-occurrence key order (§20.5.1)
    , ""
    , -- §6.3.4.3 prefixed-string fragments and the handler trait
      "data SyntaxFragment : Type ="
    , "    Lit (s : String)"
    , "    Interp (@0 t : Type) (e : Syntax t)"
    , "    InterpFmt (@0 t : Type) (e : Syntax t) (fmt : String)"
    , ""
    , "trait InterpolatedMacro (0 t : Type) ="
    , "    buildInterpolated : List SyntaxFragment -> Elab (Syntax t)"
    , ""
    , -- §6.5 prefixed single-quoted literals: the decoded payload record
      -- and its handler trait (the conventional g/b handlers elaborate
      -- through this surface).
      "data QuotedLiteral : Type ="
    , "    QuotedLiteral (sourceBody : String) (text : Option String) (bytes : Option Bytes)"
    , ""
    , "trait QuotedLiteralMacro (0 t : Type) ="
    , "    buildQuotedLiteral : QuotedLiteral -> Elab (Syntax t)"
    , ""
    , -- §20.9/§20.10: borrowed comprehension sources. The associated
      -- result members reference Region/BorrowView in the spec; like
      -- IntoQuery (see above and docs/notes/KNOWN_SPEC_ISSUES.md) the names are
      -- surfaced with their associated item type plus a query-producing
      -- member, so 'for &'/'for? &' sources resolve.
      "trait BorrowSourceIntoQuery (0 src : Type) ="
    , "    BorrowSrcItem : Type"
    , "    toBorrowSourceQuery : src -> Query BorrowSrcItem"
    , ""
    , "trait BorrowItemsIntoQuery (0 src : Type) ="
    , "    BorrowItem : Type"
    , "    toBorrowItemsQuery : src -> Query BorrowItem"
    , ""
    , -- §20.9 custom comprehension sinks (the associated 'Item' type is
      -- an ordinary member of type 'Type'; the hook parameter is typed
      -- by the opaque carrier — the §21.8 elaboration-time evaluator
      -- passes an opaque token)
      "trait FromComprehensionRaw (0 c : Type) ="
    , "    Item : Type"
    , "    fromComprehensionRaw : RawComprehension c -> Elab (Syntax c)"
    , ""
    , "trait FromComprehensionPlan (0 c : Type) ="
    , "    Item : Type"
    , "    fromComprehensionPlan : ComprehensionPlan c -> Elab (Syntax c)"
    ]

-- | Embedded @std.deriving.shape@ source (§22): the Phase 0
-- derivation-shape reflection surface. The shape summaries carry the
-- subset of the §22 fields the reflection queries of this
-- implementation populate (names, tags, constructor field lists); the
-- reflective operations are elaborator primitives executed by the
-- §21.8 Elab runner. See SPEC_COMPLIANCE.md for the provided subset.
stdDerivingShapeSource :: Text
stdDerivingShapeSource =
  T.unlines
    [ "module std.deriving.shape"
    , ""
    , "data ShapeAdtKind : Type ="
    , "    ProductAdt"
    , "    SumAdt"
    , "    EnumAdt"
    , ""
    , "data ShapeVisibility : Type ="
    , "    ShapeRepresentationVisible"
    , "    ShapeRepresentationOpaque"
    , ""
    , "data ShapeField : Type ="
    , "    ShapeField (sourceName : Option String) (renderName : String)"
    , ""
    , "data ShapeConstructor : Type ="
    , "    ShapeConstructor (sourceName : String) (renderName : String) (tag : Nat) (fields : List ShapeField)"
    , ""
    , "data AdtShape (0 a : Type) : Type ="
    , "    AdtShape (sourceName : String) (renderName : String) (visibility : ShapeVisibility) (kind : ShapeAdtKind) (constructors : List ShapeConstructor)"
    , ""
    , "data RecordShape (0 a : Type) : Type ="
    , "    RecordShape (fields : List ShapeField)"
    , ""
    , "data BoundField : Type ="
    , "    BoundField (field : ShapeField)"
    , ""
    , "data BoundFieldPair : Type ="
    , "    BoundFieldPair (field : ShapeField)"
    , ""
    , "inspectAdt : forall (@0 a : Type). Syntax Type -> Elab (AdtShape a)"
    , "let inspectAdt @a target = __shapeInspectAdt a target"
    , ""
    , "inspectRecord : forall (@0 a : Type). Syntax Type -> Elab (RecordShape a)"
    , "let inspectRecord @a target = __shapeInspectRecord a target"
    , ""
    , "runtimeConstructorFields : ShapeConstructor -> List ShapeField"
    , "let runtimeConstructorFields ctor = ctor.fields"
    , ""
    , "runtimeRecordFields : forall (@0 a : Type). RecordShape a -> List ShapeField"
    , "let runtimeRecordFields shape = shape.fields"
    , ""
    , "requireRuntimeFieldInstances :"
    , "    forall (tc : (parametric 0 x : Type) -> Type) (@0 a : Type)."
    , "    (@witness : forall (x : Type). IsTrait (tc x)) ->"
    , "    AdtShape a -> Elab Unit"
    , "let requireRuntimeFieldInstances @tc @a @witness shape ="
    , "    __shapeRequireFieldInstances tc a shape"
    , ""
    , "matchAdt :"
    , "    forall (@0 a : Type) (@0 r : Type)."
    , "    AdtShape a ->"
    , "    Syntax a ->"
    , "    (ShapeConstructor -> List BoundField -> Elab (Syntax r)) ->"
    , "    Elab (Syntax r)"
    , "let matchAdt shape scrutinee onConstructor ="
    , "    __shapeMatchAdt shape scrutinee onConstructor"
    , ""
    , "matchAdt2 :"
    , "    forall (@0 a : Type) (@0 r : Type)."
    , "    AdtShape a ->"
    , "    Syntax a ->"
    , "    Syntax a ->"
    , "    (ShapeConstructor -> List BoundFieldPair -> Elab (Syntax r)) ->"
    , "    (ShapeConstructor -> ShapeConstructor -> Elab (Syntax r)) ->"
    , "    Elab (Syntax r)"
    , "let matchAdt2 shape left right onSame onDifferent ="
    , "    __shapeMatchAdt2 shape left right onSame onDifferent"
    , ""
    , "stringSyntax : String -> Elab (Syntax String)"
    , "let stringSyntax s = __stringSyntax s"
    , ""
    , "natSyntax : Nat -> Elab (Syntax Nat)"
    , "let natSyntax n = __natSyntax n"
    , ""
    , "boolSyntax : Bool -> Elab (Syntax Bool)"
    , "let boolSyntax b = __boolSyntax b"
    , ""
    , "unitSyntax : Elab (Syntax Unit)"
    , "let unitSyntax = __unitSyntax"
    ]

-- | Embedded @std.hash@ source (§29.3): a linear 'HashState'
-- accumulator with primitive mixing steps; hash codes are opaque
-- same-execution tokens with Eq/Ord comparison only — neither numeric
-- nor showable. The §29.3 @Eq a =>@ superclass on 'Hashable' and the
-- container instances (Option\/Result\/List\/Array) are not modelled;
-- see SPEC_COMPLIANCE.md.
stdHashSource :: Text
stdHashSource =
  T.unlines
    [ "module std.hash"
    , ""
    , "data HashSeed : Type ="
    , "    MkHashSeed (seedValue : Integer)"
    , ""
    , "defaultHashSeed : HashSeed"
    , "let defaultHashSeed = MkHashSeed 0"
    , ""
    , "data HashState : Type ="
    , "    MkHashState (stateValue : Integer)"
    , ""
    , "data HashCode : Type ="
    , "    MkHashCode (codeValue : Integer)"
    , ""
    , "instance IsSet HashCode"
    , ""
    , "newHashState : HashSeed -> HashState"
    , "let newHashState seed ="
    , "    match seed"
    , "    case MkHashSeed s -> MkHashState (__hashMixInt 14695981039346656037 s)"
    , ""
    , "finishHashState : (1 state : HashState) -> HashCode"
    , "let finishHashState state ="
    , "    match state"
    , "    case MkHashState s -> MkHashCode s"
    , ""
    , "__mix : forall (a : Type). (Integer -> a -> Integer) -> a -> (1 state : HashState) -> HashState"
    , "let __mix step value state ="
    , "    match state"
    , "    case MkHashState s -> MkHashState (step s value)"
    , ""
    , "hashUnit : (1 state : HashState) -> HashState"
    , "let hashUnit state = __mix __hashMixInt 0 state"
    , ""
    , "hashBool : Bool -> (1 state : HashState) -> HashState"
    , "let hashBool value state = __mix __hashMixInt (if value then 1 else 0) state"
    , ""
    , "hashUnicodeScalar : UnicodeScalar -> (1 state : HashState) -> HashState"
    , "let hashUnicodeScalar value state = __mix __hashMixInt (natToInt (__uniScalarValue value)) state"
    , ""
    , "hashGrapheme : Grapheme -> (1 state : HashState) -> HashState" -- exact scalars (§29.3)
    , "let hashGrapheme value state = __mix __hashMixString (__graphemeToString value) state"
    , ""
    , "hashString : String -> (1 state : HashState) -> HashState" -- exact UTF-8 (§29.3)
    , "let hashString value state = __mix __hashMixString value state"
    , ""
    , "hashBytes : Bytes -> (1 state : HashState) -> HashState"
    , "let hashBytes value state = __mix __hashMixBytes value state"
    , ""
    , "hashByte : Byte -> (1 state : HashState) -> HashState"
    , "let hashByte value state = __mix __hashMixInt (natToInt (__byteToNat value)) state"
    , ""
    , "hashInt : Int -> (1 state : HashState) -> HashState"
    , "let hashInt value state = __mix __hashMixInt value state"
    , ""
    , "hashInteger : Integer -> (1 state : HashState) -> HashState"
    , "let hashInteger value state = __mix __hashMixInt value state"
    , ""
    , "hashFloatRaw : Float -> (1 state : HashState) -> HashState" -- raw IEEE bits
    , "let hashFloatRaw value state = __mix __hashMixDouble value state"
    , ""
    , "hashDoubleRaw : Double -> (1 state : HashState) -> HashState"
    , "let hashDoubleRaw value state = __mix __hashMixDouble value state"
    , ""
    , "hashNatTag : Nat -> (1 state : HashState) -> HashState"
    , "let hashNatTag value state = __mix __hashMixInt (natToInt value) state"
    , ""
    , -- §28.2 Rational hashes its canonical reduced rendering, which is
      -- injective up to 'eqRat' (equal rationals share a reduced form, so
      -- equal renderings), hence Eq-consistent per §14.1.3.
      "hashRational : Rational -> (1 state : HashState) -> HashState"
    , "let hashRational value state = hashString (showRat value) state"
    , ""
    , -- §14.1.3: Hashable refines Eq — hash acceleration is meaningful
      -- only relative to equality classes (so Eq-equal values hash equal).
      "trait Eq a => Hashable (0 a : Type) ="
    , "    hashInto : (& value : a) -> (1 state : HashState) -> HashState"
    , ""
    , "hashField : forall (a : Type). (@_ : Hashable a) -> (& value : a) -> (1 state : HashState) -> HashState"
    , "let hashField value state = hashInto value state"
    , ""
    , "hashWith : forall (a : Type). (@_ : Hashable a) -> HashSeed -> (& value : a) -> HashCode"
    , "let hashWith seed value = finishHashState (hashInto value (newHashState seed))"
    , ""
    , "instance Hashable Unit ="
    , "    let hashInto value state = hashUnit state"
    , ""
    , "instance Hashable Bool ="
    , "    let hashInto value state = hashBool value state"
    , ""
    , "instance Hashable Integer ="
    , "    let hashInto value state = hashInteger value state"
    , ""
    , "instance Hashable Nat ="
    , "    let hashInto value state = hashNatTag value state"
    , ""
    , "instance Hashable Double ="
    , "    let hashInto value state = hashDoubleRaw value state"
    , ""
    , "instance Hashable String ="
    , "    let hashInto value state = hashString value state"
    , ""
    , "instance Hashable Bytes ="
    , "    let hashInto value state = hashBytes value state"
    , ""
    , "instance Hashable Byte ="
    , "    let hashInto value state = hashByte value state"
    , ""
    , "instance Hashable UnicodeScalar ="
    , "    let hashInto value state = hashUnicodeScalar value state"
    , ""
    , "instance Hashable Grapheme ="
    , "    let hashInto value state = hashGrapheme value state"
    , ""
    , "instance Hashable Ordering ="
    , "    let hashInto value state = hashInt (orderingCode value) state"
    , ""
    , "instance Hashable Rational ="
    , "    let hashInto value state = hashRational value state"
    , ""
    , -- §14.1.3 container instances. Each mixes a per-constructor tag
      -- before the payload so structurally distinct shapes (None vs
      -- Some, Nil vs ::) cannot collide, and recurses through the
      -- element 'Hashable'. The container's own Eq supertrait obligation
      -- (e.g. Eq (Option a)) is discharged by projecting Eq a from the
      -- Hashable a premise via §14.1.4 supertrait projection.
      "instance Hashable a => Hashable (Option a) ="
    , "    let hashInto value state ="
    , "        match value"
    , "        case None -> hashNatTag 0 state"
    , "        case Some x -> hashInto x (hashNatTag 1 state)"
    , ""
    , "instance Hashable a => Hashable (List a) ="
    , "    let hashInto value state ="
    , "        match value"
    , "        case Nil -> hashNatTag 0 state"
    , "        case x :: rest -> hashInto rest (hashInto x (hashNatTag 1 state))"
    , ""
    , "instance (Hashable e, Hashable a) => Hashable (Result e a) ="
    , "    let hashInto value state ="
    , "        match value"
    , "        case Ok x -> hashInto x (hashNatTag 0 state)"
    , "        case Err y -> hashInto y (hashNatTag 1 state)"
    , ""
    , "instance Hashable a => Hashable (Array a) ="
    , "    let hashInto value state = hashInto (arrayToList value) state"
    , ""
    , "instance Eq HashCode ="
    , "    let (==) a b ="
    , "        match a"
    , "        case MkHashCode x ->"
    , "            match b"
    , "            case MkHashCode y -> eqInt x y"
    , ""
    , "instance Ord HashCode ="
    , "    let compare a b ="
    , "        match a"
    , "        case MkHashCode x ->"
    , "            match b"
    , "            case MkHashCode y -> if ltInt x y then LT elif eqInt x y then EQ else GT"
    ]

-- | Embedded @std.debug@ source (§29.6). Provided only when the build
-- enables @allow_debug_introspection@ (the import is gated in
-- 'Kappa.Pipeline'). The structured 'DebugTree' view, its human
-- rendering, and the debug-only 'compare' delegate to the runtime
-- introspection primitives (@__debugInspect@\/@__debugRender@\/
-- @__debugCompare@), which build these very constructors by walking the
-- runtime value representation. None of these participate in implicit
-- resolution, equality reflection, or coherence (§29.6).
stdDebugSource :: Text
stdDebugSource =
  T.unlines
    [ "module std.debug"
    , ""
    , "data DebugReason : Type ="
    , "    Opaque"
    , "    FunctionValue"
    , "    ForeignValue"
    , "    Cyclic"
    , "    DepthLimit"
    , "    SizeLimit"
    , "    Unsupported"
    , "    Unavailable"
    , ""
    , "data DebugEq : Type ="
    , "    Equal"
    , "    Different"
    , "    Unknown (reason : DebugReason)"
    , ""
    , "data DebugTree : Type ="
    , "    Scalar (text : String)"
    , "    Node (tag : String) (fields : List DebugField)"
    , "    OpaqueValue (reason : DebugReason)"
    , ""
    , "data DebugField : Type ="
    , "    DebugField (label : Option String) (value : DebugTree)"
    , ""
    , "inspect : forall (a : Type). (& x : a) -> DebugTree"
    , "let inspect x = __debugInspect x"
    , ""
    , "render : forall (a : Type). (& x : a) -> String"
    , "let render x = __debugRender x"
    , ""
    , "compare : forall (a : Type). (& x : a) -> (& y : a) -> DebugEq"
    , "let compare x y = __debugCompare x y"
    ]

-- | Embedded @std.bytes@ source (§29.5, MUST). Portable operations over
-- the exact byte sequence denoted by a 'Bytes' value, plus the linear
-- 'BytesBuilder' accumulator. 'BytesBuilder'\/'BytesDecodeError' are
-- builtin opaque carriers (re-exported here). The proof-carrying
-- 'bytesIndex'\/'bytesSlice' delegate to trapping primitives (the
-- supplied bounds proofs make the access total). The dependent
-- 'SizedArray' views of §29.5 are not provided; see SPEC_COMPLIANCE.md.
stdBytesSource :: Text
stdBytesSource =
  T.unlines
    [ "module std.bytes"
    , ""
    , "emptyBytes : Bytes"
    , "let emptyBytes = __bytesEmpty"
    , ""
    , "singletonByte : Byte -> Bytes"
    , "let singletonByte b = __bytesSingleton b"
    , ""
    , "bytesLength : Bytes -> Nat"
    , "let bytesLength bs = __bytesLength bs"
    , ""
    , "bytesIsEmpty : Bytes -> Bool"
    , "let bytesIsEmpty bs = __bytesIsEmpty bs"
    , ""
    , "bytesGet : Bytes -> Nat -> Option Byte"
    , "let bytesGet bs i = __bytesGet bs i"
    , ""
    , -- §29.5 total in-bounds index (the proof makes it total)
      "bytesIndex : (bs : Bytes) -> (i : Nat) -> (@_ : (i < bytesLength bs) = True) -> Byte"
    , "let bytesIndex bs i = __bytesIndexUnsafe bs i"
    , ""
    , "bytesAppend : Bytes -> Bytes -> Bytes"
    , "let bytesAppend x y = __bytesAppend x y"
    , ""
    , "bytesConcat : List Bytes -> Bytes"
    , "let bytesConcat xs ="
    , "    match xs"
    , "    case Nil -> __bytesEmpty"
    , "    case b :: rest -> __bytesAppend b (bytesConcat rest)"
    , ""
    , -- §29.5 total slice (the start+len bound proof makes it total)
      "bytesSlice : (bs : Bytes) -> (start : Nat) -> (len : Nat) -> (@_ : ((start + len) <= bytesLength bs) = True) -> Bytes"
    , "let bytesSlice bs start len = __bytesSlice bs start len"
    , ""
    , "bytesTake : Nat -> Bytes -> Bytes"
    , "let bytesTake n bs = __bytesTake n bs"
    , ""
    , "bytesDrop : Nat -> Bytes -> Bytes"
    , "let bytesDrop n bs = __bytesDrop n bs"
    , ""
    , "bytesStartsWith : Bytes -> Bytes -> Bool"
    , "let bytesStartsWith pre bs = __bytesStartsWith pre bs"
    , ""
    , "bytesEndsWith : Bytes -> Bytes -> Bool"
    , "let bytesEndsWith suf bs = __bytesEndsWith suf bs"
    , ""
    , "bytesContains : Bytes -> Bytes -> Bool"
    , "let bytesContains needle hay = __bytesContains needle hay"
    , ""
    , "bytesFind : Byte -> Bytes -> Option Nat"
    , "let bytesFind b bs = __bytesFind b bs"
    , ""
    , "bytesBreakOn : Bytes -> Bytes -> Option (prefix : Bytes, suffix : Bytes)"
    , "let bytesBreakOn sep bs ="
    , "    match __bytesBreakIndex sep bs"
    , "    case None -> None"
    , "    case Some i -> Some (prefix = __bytesTake i bs, suffix = __bytesDrop i bs)"
    , ""
    , "bytesToList : Bytes -> List Byte"
    , "let bytesToList bs = __bytesToList bs"
    , ""
    , "bytesFromList : List Byte -> Bytes"
    , "let bytesFromList bs = __bytesFromList bs"
    , ""
    , "bytesCompact : Bytes -> Bytes"
    , "let bytesCompact bs = __bytesCompact bs"
    , ""
    , -- §29.5 linear builder
      "newBytesBuilder : BytesBuilder"
    , "let newBytesBuilder = __newBytesBuilder"
    , ""
    , "bytesBuilderByte : Byte -> (1 builder : BytesBuilder) -> BytesBuilder"
    , "let bytesBuilderByte b builder = __bytesBuilderByte b builder"
    , ""
    , "bytesBuilderBytes : Bytes -> (1 builder : BytesBuilder) -> BytesBuilder"
    , "let bytesBuilderBytes more builder = __bytesBuilderBytes more builder"
    , ""
    , "finishBytesBuilder : (1 builder : BytesBuilder) -> Bytes"
    , "let finishBytesBuilder builder = __finishBytesBuilder builder"
    , ""
    , -- §29.5 dependent SizedArray views. `bytesAsSizedArray` packs the
      -- existential with witness `bytesLength bs`, so the §29.5 guarantee
      -- (witness propositionally equal to `bytesLength bs`) holds by
      -- construction; `bytesFromSizedArray` recovers the same byte
      -- sequence and `bytesBuilderSizedArray` appends it.
      "bytesAsSizedArray : Bytes -> exists (n : Nat). SizedArray n Byte"
    , "let bytesAsSizedArray bs = seal exists (n = bytesLength bs). MkSizedArray (bytesToList bs) as exists (n : Nat). SizedArray n Byte"
    , ""
    , "bytesFromSizedArray : forall (n : Nat). SizedArray n Byte -> Bytes"
    , "let bytesFromSizedArray arr = match arr case MkSizedArray es -> bytesFromList es"
    , ""
    , "bytesBuilderSizedArray : forall (n : Nat). SizedArray n Byte -> (1 builder : BytesBuilder) -> BytesBuilder"
    , "let bytesBuilderSizedArray arr builder = bytesBuilderBytes (bytesFromSizedArray arr) builder"
    ]

-- | Embedded @std.unicode@ source (§29.4; see SPEC_COMPLIANCE.md).
-- Unicode data version: UCD 15.0.0 (Kappa.UnicodeData); normalization,
-- canonical equivalence and grapheme segmentation are full-fidelity for
-- that version, while word\/sentence segmentation and display-width are
-- documented approximations. The §29.4 MUST surface — byte\/text ops,
-- scalar\/grapheme ops, normalization\/equivalence, case folding, the
-- 'StringBuilder', string cursors\/spans, and the incremental
-- 'Utf8Decoder' — is provided. The SHOULD submodules
-- @std.unicode.collation@ and @std.unicode.security@ are not.
stdUnicodeSource :: Text
stdUnicodeSource =
  T.unlines
    [ "module std.unicode"
    , ""
    , "data UnicodeVersion : Type ="
    , "    MkUnicodeVersion (major : Integer) (minor : Integer) (patch : Integer)"
    , ""
    , "unicodeVersion : UnicodeVersion"
    , "let unicodeVersion = MkUnicodeVersion 15 0 0"
    , ""
    , "data UnicodeDecodeError : Type ="
    , "    MkUnicodeDecodeError"
    , ""
    , "data UnicodeTextError : Type ="
    , "    MkUnicodeTextError"
    , ""
    , "data NormalizationForm : Type ="
    , "    NFC"
    , "    NFD"
    , "    NFKC"
    , "    NFKD"
    , ""
    , "data CaseFoldMode : Type =" -- full case folding (Data-driven)
    , "    FullCaseFold"
    , ""
    , "data DisplayWidthMode : Type =" -- documented coarse policy below
    , "    GraphemeCellWidth"
    , ""
    , "utf8Bytes : String -> Bytes"
    , "let utf8Bytes s = __utf8Bytes s"
    , ""
    , "decodeUtf8 : Bytes -> Result UnicodeDecodeError String"
    , "let decodeUtf8 bs = if __utf8Valid bs then Ok (__decodeUtf8Lossy bs) else Err MkUnicodeDecodeError"
    , ""
    , "decodeUtf8Lossy : Bytes -> String" -- U+FFFD replacement policy
    , "let decodeUtf8Lossy bs = __decodeUtf8Lossy bs"
    , ""
    , "byteLength : String -> Nat"
    , "let byteLength s = __byteLength s"
    , ""
    , "scalarValue : UnicodeScalar -> Nat"
    , "let scalarValue c = __uniScalarValue c"
    , ""
    , "unicodeScalarFromValue : Nat -> Option UnicodeScalar"
    , "let unicodeScalarFromValue n = if __scalarInRange n then Some (__scalarOfValue n) else None"
    , ""
    , "scalarToString : UnicodeScalar -> String"
    , "let scalarToString c = __scalarToString c"
    , ""
    , "scalars : String -> Query UnicodeScalar"
    , "let scalars s = __queryFromList (__stringScalars s)"
    , ""
    , "scalarCount : String -> Nat"
    , "let scalarCount s = __scalarCount s"
    , ""
    , "graphemeToString : Grapheme -> String"
    , "let graphemeToString g = __graphemeToString g"
    , ""
    , "graphemeFromString : String -> Option Grapheme"
    , "let graphemeFromString s = if __graphemeValid s then Some (__graphemeOfString s) else None"
    , ""
    , "graphemes : String -> Query Grapheme"
    , "let graphemes s = __queryFromList (__stringGraphemes s)"
    , ""
    , "graphemeCount : String -> Nat"
    , "let graphemeCount s = __graphemeCount s"
    , ""
    , "normalize : NormalizationForm -> String -> String"
    , "let normalize form s ="
    , "    match form"
    , "    case NFC -> __normalize 0 s"
    , "    case NFD -> __normalize 1 s"
    , "    case NFKC -> __normalize 2 s"
    , "    case NFKD -> __normalize 3 s"
    , ""
    , "isNormalized : NormalizationForm -> String -> Bool"
    , "let isNormalized form s = eqStr (normalize form s) s"
    , ""
    , "canonicalEquivalent : String -> String -> Bool" -- NFC-compare (§29.4)
    , "let canonicalEquivalent x y = eqStr (__normalize 0 x) (__normalize 0 y)"
    , ""
    , "caseFold : CaseFoldMode -> String -> String"
    , "let caseFold mode s = __caseFold s"
    , ""
    , -- documented policy: counts extended grapheme clusters as one
      -- display cell each (combining marks zero extra; no wide/ambiguous
      -- distinction)
      "displayWidth : DisplayWidthMode -> String -> Nat"
    , "let displayWidth mode s = __graphemeCount s"
    , ""
    , "words : String -> Query String" -- whitespace approximation
    , "let words s = __queryFromList (__stringWords s)"
    , ""
    , "sentences : String -> Query String" -- terminator approximation
    , "let sentences s = __queryFromList (__stringSentences s)"
    , ""
    , -- §29.4 StringBuilder (linear text accumulator)
      "newStringBuilder : StringBuilder"
    , "let newStringBuilder = __newStringBuilder"
    , ""
    , "stringBuilderString : String -> (1 builder : StringBuilder) -> StringBuilder"
    , "let stringBuilderString s builder = __stringBuilderString s builder"
    , ""
    , "stringBuilderScalar : UnicodeScalar -> (1 builder : StringBuilder) -> StringBuilder"
    , "let stringBuilderScalar c builder = __stringBuilderScalar c builder"
    , ""
    , "stringBuilderGrapheme : Grapheme -> (1 builder : StringBuilder) -> StringBuilder"
    , "let stringBuilderGrapheme g builder = __stringBuilderGrapheme g builder"
    , ""
    , "finishStringBuilder : (1 builder : StringBuilder) -> String"
    , "let finishStringBuilder builder = __finishStringBuilder builder"
    , ""
    , -- §29.4 string cursors and spans
      "stringStart : String -> StringCursor"
    , "let stringStart s = __stringStart s"
    , ""
    , "stringEnd : String -> StringCursor"
    , "let stringEnd s = __stringEnd s"
    , ""
    , "stringCursorOffset : String -> StringCursor -> Nat"
    , "let stringCursorOffset s c = __stringCursorOffset s c"
    , ""
    , "stringNextScalar : String -> StringCursor -> Option (scalar : UnicodeScalar, next : StringCursor)"
    , "let stringNextScalar s c = __stringNextScalar s c"
    , ""
    , "stringPrevScalar : String -> StringCursor -> Option (prev : StringCursor, scalar : UnicodeScalar)"
    , "let stringPrevScalar s c = __stringPrevScalar s c"
    , ""
    , "stringNextGrapheme : String -> StringCursor -> Option (grapheme : Grapheme, next : StringCursor)"
    , "let stringNextGrapheme s c = __stringNextGrapheme s c"
    , ""
    , "stringSpan : String -> StringCursor -> StringCursor -> Option String"
    , "let stringSpan s a b = __stringSpan s a b"
    , ""
    , "stringCompact : String -> String"
    , "let stringCompact s = __stringCompact s"
    , ""
    , -- §29.4 incremental UTF-8 decoder. Malformed input is reported as"
      -- Err MkUnicodeDecodeError."
      "newUtf8Decoder : Utf8Decoder"
    , "let newUtf8Decoder = __newUtf8Decoder"
    , ""
    , "decodeUtf8Chunk : Bytes -> (1 decoder : Utf8Decoder) -> Result UnicodeDecodeError (text : String, decoder : Utf8Decoder)"
    , "let decodeUtf8Chunk chunk decoder ="
    , "    match __decodeUtf8Chunk chunk decoder"
    , "    case None -> Err MkUnicodeDecodeError"
    , "    case Some r -> Ok r"
    , ""
    , "finishUtf8Decoder : (1 decoder : Utf8Decoder) -> Result UnicodeDecodeError String"
    , "let finishUtf8Decoder decoder ="
    , "    match __finishUtf8Decoder decoder"
    , "    case None -> Err MkUnicodeDecodeError"
    , "    case Some s -> Ok s"
    ]

-- | Embedded @std.ffi@ source (§26.1.1 portable foreign-ABI scalar and
-- pointer vocabulary): nominal exact-width/pointer-width wrappers over
-- the portable numeric representations. No host bindings are provided;
-- this is the type vocabulary only.
stdFfiSource :: Text
stdFfiSource =
  T.unlines
    [ "module std.ffi"
    , ""
    , "data I8 : Type =    MkI8 (rep : Integer)"
    , "data I16 : Type =   MkI16 (rep : Integer)"
    , "data I32 : Type =   MkI32 (rep : Integer)"
    , "data I64 : Type =   MkI64 (rep : Integer)"
    , "data U8 : Type =    MkU8 (rep : Integer)"
    , "data U16 : Type =   MkU16 (rep : Integer)"
    , "data U32 : Type =   MkU32 (rep : Integer)"
    , "data U64 : Type =   MkU64 (rep : Integer)"
    , "data Isize : Type = MkIsize (rep : Integer)"
    , "data Usize : Type = MkUsize (rep : Integer)"
    , "data F32 : Type =   MkF32 (rep : Double)"
    , "data F64 : Type =   MkF64 (rep : Double)"
    , ""
    , "data RawPtr : Type ="
    , "    MkRawPtr (addr : Integer)"
    , ""
    , "data OpaqueHandle : Type ="
    , "    MkOpaqueHandle (token : Integer)"
    , ""
    , "-- §26.1.1 ergonomic constructors + accessors over the exact-width scalar"
    , "-- wrappers (the native raw surface exposes these nominal types; programs"
    , "-- wrap/unwrap the Integer/Double rep with these helpers)."
    , "let i8 n = MkI8 n"
    , "let i16 n = MkI16 n"
    , "let i32 n = MkI32 n"
    , "let i64 n = MkI64 n"
    , "let u8 n = MkU8 n"
    , "let u16 n = MkU16 n"
    , "let u32 n = MkU32 n"
    , "let u64 n = MkU64 n"
    , "let isize n = MkIsize n"
    , "let usize n = MkUsize n"
    , "let f32 d = MkF32 d"
    , "let f64 d = MkF64 d"
    , "let i8Value v = match v"
    , "    case MkI8 r -> r"
    , "let i16Value v = match v"
    , "    case MkI16 r -> r"
    , "let i32Value v = match v"
    , "    case MkI32 r -> r"
    , "let i64Value v = match v"
    , "    case MkI64 r -> r"
    , "let u8Value v = match v"
    , "    case MkU8 r -> r"
    , "let u16Value v = match v"
    , "    case MkU16 r -> r"
    , "let u32Value v = match v"
    , "    case MkU32 r -> r"
    , "let u64Value v = match v"
    , "    case MkU64 r -> r"
    , "let isizeValue v = match v"
    , "    case MkIsize r -> r"
    , "let usizeValue v = match v"
    , "    case MkUsize r -> r"
    , "let f32Value v = match v"
    , "    case MkF32 r -> r"
    , "let f64Value v = match v"
    , "    case MkF64 r -> r"
    , "let rawPtr addr = MkRawPtr addr"
    , "let rawPtrAddr p = match p"
    , "    case MkRawPtr a -> a"
    ]

-- | Embedded @std.ffi.c@ source (§26.1.1): C/native ABI spelling types.
stdFfiCSource :: Text
stdFfiCSource =
  T.unlines
    [ "module std.ffi.c"
    , ""
    , "data CChar : Type =      MkCChar (rep : Integer)"
    , "data CSChar : Type =     MkCSChar (rep : Integer)"
    , "data CUChar : Type =     MkCUChar (rep : Integer)"
    , "data CShort : Type =     MkCShort (rep : Integer)"
    , "data CUShort : Type =    MkCUShort (rep : Integer)"
    , "data CInt : Type =       MkCInt (rep : Integer)"
    , "data CUInt : Type =      MkCUInt (rep : Integer)"
    , "data CLong : Type =      MkCLong (rep : Integer)"
    , "data CULong : Type =     MkCULong (rep : Integer)"
    , "data CLongLong : Type =  MkCLongLong (rep : Integer)"
    , "data CULongLong : Type = MkCULongLong (rep : Integer)"
    , "data CSize : Type =      MkCSize (rep : Integer)"
    , "data CPtrdiff : Type =   MkCPtrdiff (rep : Integer)"
    , "data CBool : Type =      MkCBool (rep : Bool)"
    , "data CFloat : Type =     MkCFloat (rep : Double)"
    , "data CDouble : Type =    MkCDouble (rep : Double)"
    ]

-- | Embedded @std.atomic@ source (§29.1): the canonical surface over an opaque
-- atomic cell.  An @AtomicRef a@ wraps an opaque @__AtomicCell a@ —
-- NOT a 'Ref' (§29.1: "not an ordinary var, Ref, TVar, or MonadRef"), so the
-- cell cannot be 'readRef'/'writeRef'-ed to bypass atomicity.  Every operation
-- lowers to a @__atomic*@ primitive:
--
--   * Native (C/LLVM): a @krt2_atomic_*@ operation on one runtime AtomicRef cell.
--     The cell stores the source @KValue *@, so §6 arbitrary-precision @Integer@
--     values are not narrowed.  fetch-add / CAS are indivisible runtime
--     operations, so concurrent updates across the worker pool are conserved
--     exactly (no lost updates).
--   * Interpreter: the single agent runs fibers cooperatively on one OS thread,
--     so every memory order is trivially sequentially consistent and the cell
--     is modelled by a plain mutable IORef.  This is the correct SEQUENTIAL
--     oracle; it does NOT (and cannot) exercise the multi-worker race the native
--     runtime guards against.
--
-- The memory-order argument is passed through as a small declaration-order code,
-- not a codegen-assigned constructor tag, so each LoadOrder/StoreOrder/RmwOrder/
-- CasFailureOrder maps directly onto the corresponding runtime order check (see
-- "runtime/atomic.c").
stdAtomicSource :: Text
stdAtomicSource =
  T.unlines
    [ "module std.atomic"
    , ""
    , "data AtomicRef (0 a : Type) : Type ="
    , "    MkAtomicRef (cell : __AtomicCell a)"
    , ""
    , "data LoadOrder : Type ="
    , "    LoadRelaxed"
    , "    LoadAcquire"
    , "    LoadSeqCst"
    , ""
    , "data StoreOrder : Type ="
    , "    StoreRelaxed"
    , "    StoreRelease"
    , "    StoreSeqCst"
    , ""
    , "data RmwOrder : Type ="
    , "    RmwRelaxed"
    , "    RmwAcquire"
    , "    RmwRelease"
    , "    RmwAcqRel"
    , "    RmwSeqCst"
    , ""
    , "data CasFailureOrder : Type ="
    , "    CasFailRelaxed"
    , "    CasFailAcquire"
    , "    CasFailSeqCst"
    , ""
    , "data CompareExchangeResult (0 a : Type) : Type ="
    , "    Exchanged (old : a)"
    , "    NotExchanged (current : a)"
    , ""
    , "trait AtomicValue (0 a : Type)"
    , ""
    , "trait AtomicInteger (0 a : Type)"
    , ""
    , "instance AtomicValue Bool"
    , "instance AtomicValue Integer"
    , "instance AtomicInteger Integer"
    , ""
    , "-- The memory order is forwarded to the runtime as a small Integer CODE —"
    , "-- the §29.1 canonical declaration-order index of the order constructor."
    , "-- Codegen assigns user-constructor tag ids GLOBALLY, so the runtime cannot"
    , "-- read an order's tag id directly; these matches give it a stable code that"
    , "-- maps onto a C11 memory_order (see runtime/atomic.c).  Every order is"
    , "-- realised faithfully — there is no silent downgrade to a weaker order."
    , "loadOrderCode : LoadOrder -> Integer"
    , "let loadOrderCode order ="
    , "    match order"
    , "    case LoadRelaxed -> 0"
    , "    case LoadAcquire -> 1"
    , "    case LoadSeqCst -> 2"
    , ""
    , "storeOrderCode : StoreOrder -> Integer"
    , "let storeOrderCode order ="
    , "    match order"
    , "    case StoreRelaxed -> 0"
    , "    case StoreRelease -> 1"
    , "    case StoreSeqCst -> 2"
    , ""
    , "rmwOrderCode : RmwOrder -> Integer"
    , "let rmwOrderCode order ="
    , "    match order"
    , "    case RmwRelaxed -> 0"
    , "    case RmwAcquire -> 1"
    , "    case RmwRelease -> 2"
    , "    case RmwAcqRel -> 3"
    , "    case RmwSeqCst -> 4"
    , ""
    , "casFailureOrderCode : CasFailureOrder -> Integer"
    , "let casFailureOrderCode order ="
    , "    match order"
    , "    case CasFailRelaxed -> 0"
    , "    case CasFailAcquire -> 1"
    , "    case CasFailSeqCst -> 2"
    , ""
    , "-- Each surface op extracts the opaque cell from MkAtomicRef and forwards it"
    , "-- (with the order code) to the matching __atomic* primitive, which the"
    , "-- native backends lower to a krt2_atomic_* call and the interpreter models"
    , "-- with a sequential IORef cell."
    , "newAtomicRef : forall (a : Type). (@_ : AtomicValue a) -> a -> UIO (AtomicRef a)"
    , "let newAtomicRef initial = do"
    , "    let cell <- __newAtomicRef initial"
    , "    pure (MkAtomicRef cell)"
    , ""
    , "atomicLoad : forall (a : Type). (@_ : AtomicValue a) -> LoadOrder -> AtomicRef a -> UIO a"
    , "let atomicLoad order ref ="
    , "    match ref"
    , "    case MkAtomicRef cell -> __atomicLoad (loadOrderCode order) cell"
    , ""
    , "atomicStore : forall (a : Type). (@_ : AtomicValue a) -> StoreOrder -> AtomicRef a -> a -> UIO Unit"
    , "let atomicStore order ref value ="
    , "    match ref"
    , "    case MkAtomicRef cell -> __atomicStore (storeOrderCode order) cell value"
    , ""
    , "atomicExchange : forall (a : Type). (@_ : AtomicValue a) -> RmwOrder -> AtomicRef a -> a -> UIO a"
    , "let atomicExchange order ref value ="
    , "    match ref"
    , "    case MkAtomicRef cell -> __atomicExchange (rmwOrderCode order) cell value"
    , ""
    , "-- Strong CAS: the primitive performs the atomic swap and returns the"
    , "-- WITNESSED old value.  By the §29.1 strong-CAS contract the exchange"
    , "-- succeeded iff that witnessed value equals `expected`, so the result"
    , "-- constructor is rebuilt HERE (in source, where codegen tags it correctly)"
    , "-- rather than in the runtime.  __atomicRepEq is the same representation"
    , "-- equality the native CAS used on the scalar cell."
    , "atomicCompareExchange : forall (a : Type). (@_ : AtomicValue a) -> RmwOrder -> CasFailureOrder -> AtomicRef a -> a -> a -> UIO (CompareExchangeResult a)"
    , "let atomicCompareExchange success failure ref expected desired ="
    , "    match ref"
    , "    case MkAtomicRef cell -> ioBind (__atomicCompareExchange (rmwOrderCode success) (casFailureOrderCode failure) cell expected desired) (\\witnessed -> if __atomicRepEq witnessed expected then ioPure (Exchanged witnessed) else ioPure (NotExchanged witnessed))"
    , ""
    , "atomicFetchAdd : RmwOrder -> AtomicRef Integer -> Integer -> UIO Integer"
    , "let atomicFetchAdd order ref operand ="
    , "    match ref"
    , "    case MkAtomicRef cell -> __atomicFetchAdd (rmwOrderCode order) cell operand"
    , ""
    , "atomicFetchSub : RmwOrder -> AtomicRef Integer -> Integer -> UIO Integer"
    , "let atomicFetchSub order ref operand ="
    , "    match ref"
    , "    case MkAtomicRef cell -> __atomicFetchSub (rmwOrderCode order) cell operand"
    , ""
    , "atomicFetchAnd : RmwOrder -> AtomicRef Integer -> Integer -> UIO Integer"
    , "let atomicFetchAnd order ref operand ="
    , "    match ref"
    , "    case MkAtomicRef cell -> __atomicFetchAnd (rmwOrderCode order) cell operand"
    , ""
    , "atomicFetchOr : RmwOrder -> AtomicRef Integer -> Integer -> UIO Integer"
    , "let atomicFetchOr order ref operand ="
    , "    match ref"
    , "    case MkAtomicRef cell -> __atomicFetchOr (rmwOrderCode order) cell operand"
    , ""
    , "atomicFetchXor : RmwOrder -> AtomicRef Integer -> Integer -> UIO Integer"
    , "let atomicFetchXor order ref operand ="
    , "    match ref"
    , "    case MkAtomicRef cell -> __atomicFetchXor (rmwOrderCode order) cell operand"
    ]

-- | Embedded @std.array.mutable@ source (MUTABLE-ARRAY-DESIGN §4.2): the IO
-- @MutArray@ front-end — the design's FIRST front-end, boxed elements only.
--
-- A @MutArray a@ wraps an opaque @__ArrayBuf a@ exactly as @AtomicRef@ wraps an
-- @__AtomicCell a@ (the §4.1 AtomicRef precedent): each surface op @match@-
-- unwraps the buffer and forwards ONLY values to a @__array*@ primitive.  The
-- element type @a@ is a @forall@ = Q0-erased parameter that NEVER reaches the
-- prim (the erasure-safety contract; the same class of bug as the prior native
-- IO crash, avoided here because nothing type-shaped is emitted).
--
-- Three-tier TOTAL indexing (MUTABLE-ARRAY-DESIGN §6):
--   1. PROOF-CARRYING (primary): 'arrayRead'/'arrayWrite' take an ERASED
--      @(i < arrayLen arr) = True@ witness (the §28.2 'arrayIndex' shape).  The
--      proof erases to nothing, so the op lowers to a bare O(1) load/store with
--      no runtime bounds check — totality is proven, not paid for.
--   2. OPTION/BOOL (ergonomic, proof-free): 'arrayReadOpt' returns @None@ out of
--      bounds; 'arrayWriteOk' returns @False@.  Total because Option/Bool absorb
--      the partiality (the §29 'arrayGet' discipline).
--   3. IO FLOOR (runtime trap): the @__array*@ prim itself bounds-checks and
--      raises a Defect in the IO channel on OOB (krt_fail / a thrown KappaError
--      — a §18.1.2 IO effect, never pure partiality).  Reached only if a caller
--      bypasses tiers 1-2; the proof path and the Option path never hit it.
--
-- ELEMENT UNBOXING (the design's §5.3 scalar-slab path) is DEFERRED to a later
-- stage and is the clean seam left for the parallel scalar-rep rework: every
-- array is born BOXED today (elemkind == KARR_BOXED in the runtime); the
-- @element_size@/@elemkind@ field and the @__array*@ symbol family are shaped so
-- the INT64/DOUBLE slabs land as a NEW prim family + a new dispatch arm with no
-- @K_ARRAY@ redesign and no change to this surface.  ST 'STArray', the linear
-- 'LinArray', the concurrent 'TArray', and 'freeze'/'thaw' are likewise deferred.
stdArrayMutableSource :: Text
stdArrayMutableSource =
  T.unlines
    [ "module std.array.mutable"
    , ""
    , "-- The opaque handle: a one-field data wrapping the runtime buffer, exactly"
    , "-- as MkAtomicRef wraps an __AtomicCell.  The element type is erased."
    , "data MutArray (0 a : Type) : Type ="
    , "    MkMutArray (buf : __ArrayBuf a)"
    , ""
    , "-- Allocate an n-element array, every slot initialised to `init`.  Total for"
    , "-- all n: a Nat is non-negative, so the length is well-formed by construction."
    , "newArray : forall (a : Type). (n : Nat) -> a -> UIO (MutArray a)"
    , "let newArray n init ="
    , "    ioBind (__newArray n init) (\\buf -> ioPure (MkMutArray buf))"
    , ""
    , "-- O(1), PURE, total: the length is stored in the buffer header."
    , "arrayLen : forall (a : Type). MutArray a -> Nat"
    , "let arrayLen arr ="
    , "    match arr"
    , "    case MkMutArray buf -> __arrayLen buf"
    , ""
    , "-- TIER 1 — proof-carrying total read.  The (i < arrayLen arr) = True witness"
    , "-- is ERASED, so this lowers to a bare O(1) load with NO bounds check."
    , "arrayRead : forall (a : Type). (arr : MutArray a) -> (i : Nat) -> (@_ : (i < arrayLen arr) = True) -> UIO a"
    , "let arrayRead arr i ="
    , "    match arr"
    , "    case MkMutArray buf -> __arrayRead buf (natToInt i)"
    , ""
    , "-- TIER 1 — proof-carrying total write (mirror of arrayRead).  The erased"
    , "-- witness is the LAST argument (after the value) so the value binds cleanly,"
    , "-- matching the §28.2 arrayIndex convention of a tail proof obligation."
    , "arrayWrite : forall (a : Type). (arr : MutArray a) -> (i : Nat) -> a -> (@_ : (i < arrayLen arr) = True) -> UIO Unit"
    , "let arrayWrite arr i v ="
    , "    match arr"
    , "    case MkMutArray buf -> __arrayWrite buf (natToInt i) v"
    , ""
    , "-- TIER 2 — ergonomic, proof-free read: None out of bounds.  Total because"
    , "-- Option absorbs the partiality (the §29 arrayGet discipline)."
    , "arrayReadOpt : forall (a : Type). MutArray a -> Nat -> UIO (Option a)"
    , "let arrayReadOpt arr i ="
    , "    match arr"
    , "    case MkMutArray buf ->"
    , "        if ltInt (natToInt i) (natToInt (__arrayLen buf))"
    , "        then ioBind (__arrayRead buf (natToInt i)) (\\x -> ioPure (Some x))"
    , "        else ioPure None"
    , ""
    , "-- TIER 2 — ergonomic, proof-free write: False (no write) out of bounds,"
    , "-- True on success."
    , "arrayWriteOk : forall (a : Type). MutArray a -> Nat -> a -> UIO Bool"
    , "let arrayWriteOk arr i v ="
    , "    match arr"
    , "    case MkMutArray buf ->"
    , "        if ltInt (natToInt i) (natToInt (__arrayLen buf))"
    , "        then ioBind (__arrayWrite buf (natToInt i) v) (\\_ -> ioPure True)"
    , "        else ioPure False"
    ]

-- | Embedded @std.gradual@ source (§24.9): explicit dynamic values.
-- 'DynRep' is a nominal token; representation checking compares tokens.
stdGradualSource :: Text
stdGradualSource =
  T.unlines
    [ "module std.gradual"
    , ""
    , "data CastBlame : Type ="
    , "    MkCastBlame (message : String)"
    , ""
    , "opaque data DynRep (0 a : Type) : Type ="
    , "    MkDynRep (tag : String)"
    , ""
    , "data Dyn : Type ="
    , "    MkDyn (tag : String)"
    , ""
    , "trait DynamicType (0 a : Type) ="
    , "    dynRep : DynRep a"
    , ""
    , "toDynWith : forall (@0 a : Type). DynRep a -> a -> Dyn"
    , "let toDynWith rep value ="
    , "    match rep"
    , "    case MkDynRep tag -> MkDyn tag"
    , ""
    , "checkedCastWith : forall (@0 a : Type). DynRep a -> Dyn -> Result CastBlame a"
    , "let checkedCastWith rep value ="
    , "    Err (MkCastBlame \"std.gradual: dynamic payloads are not carried by this implementation\")"
    , ""
    , "sameDynRep : forall (parametric 0 a : Type) (parametric 0 b : Type). DynRep a -> DynRep b -> Dec ((=) a b)"
    , "let sameDynRep x y ="
    , "    match x"
    , "    case MkDynRep xTag ->"
    , "        match y"
    , "        case MkDynRep yTag ->"
    , "            if eqStr xTag yTag"
    , "            then Yes __unsafeAssertProof"
    , "            else No (\\_ -> __unsafeAssertProof)"
    , ""
    , "toDyn : forall (@0 a : Type). (@_ : DynamicType a) -> a -> Dyn"
    , "let toDyn value = toDynWith dynRep value"
    , ""
    , "checkedCast : forall (@0 a : Type). (@_ : DynamicType a) -> Dyn -> Result CastBlame a"
    , "let checkedCast value = checkedCastWith dynRep value"
    ]

-- | Embedded @std.bridge@ source (§25.1): the boundary/bridge type
-- vocabulary. Surfaces are region-indexed; no live bridge runtime is
-- provided, so the binding operations are typed stubs that fail with a
-- bridge-lifecycle failure.
stdBridgeSource :: Text
stdBridgeSource =
  T.unlines
    [ "module std.bridge"
    , ""
    , "import std.gradual.(type CastBlame, ctor MkCastBlame)"
    , ""
    , "data BridgeOrigin : Type ="
    , "    MkBridgeOrigin (description : String)"
    , ""
    , "data BridgeFailure : Type ="
    , "    MkBridgeFailure (message : String)"
    , ""
    , "data BoundaryDirection : Type ="
    , "    IntoKappa"
    , "    OutOfKappa"
    , "    LaterUse"
    , ""
    , "data BoundaryPrecision : Type ="
    , "    Exact"
    , "    Conservative"
    , "    Lossy"
    , ""
    , "data BridgeContract (surface : Region -> Type) : Type ="
    , "    MkBridgeContract (description : String)"
    , ""
    , "data BridgePackage (surface : Region -> Type) : Type ="
    , "    MkBridgePackage (origin : BridgeOrigin)"
    , ""
    , "trait BridgeBindable (surface : Region -> Type) ="
    , "    bridgeContract : BridgeContract surface"
    , ""
    , "trait BridgeHandle (0 h : Type) ="
    , "    bridgeOrigin : h -> UIO BridgeOrigin"
    , "    bridgeFailure : BridgeFailure -> String"
    , ""
    , "bindModule :"
    , "    forall (surface : Region -> Type) (h : Type) (r : Region)."
    , "    (@_ : BridgeBindable surface) ->"
    , "    (@_ : BridgeHandle h) ->"
    , "    h ->"
    , "    String ->"
    , "    IO BridgeFailure (surface r)"
    , "let bindModule handle name ="
    , "    throwIO (MkBridgeFailure \"std.bridge: no live bridge runtime is provided by this implementation\")"
    , ""
    , "bindModuleOwned :"
    , "    forall (surface : Region -> Type) (h : Type)."
    , "    (@_ : BridgeBindable surface) ->"
    , "    (@_ : BridgeHandle h) ->"
    , "    h ->"
    , "    String ->"
    , "    IO BridgeFailure (BridgePackage surface)"
    , "let bindModuleOwned handle name ="
    , "    throwIO (MkBridgeFailure \"std.bridge: no live bridge runtime is provided by this implementation\")"
    , ""
    , "bridgePackageValue :"
    , "    forall (surface : Region -> Type) (r : Region)."
    , "    BridgePackage surface ->"
    , "    IO BridgeFailure (surface r)"
    , "let bridgePackageValue package ="
    , "    throwIO (MkBridgeFailure \"std.bridge: no live bridge runtime is provided by this implementation\")"
    , ""
    , "bridgePackageOrigin :"
    , "    forall (surface : Region -> Type)."
    , "    BridgePackage surface -> UIO BridgeOrigin"
    , "let bridgePackageOrigin package ="
    , "    match package"
    , "    case MkBridgePackage origin -> pure origin"
    , ""
    , "bridgeFailureToCastBlame : BridgeFailure -> CastBlame"
    , "let bridgeFailureToCastBlame failure ="
    , "    match failure"
    , "    case MkBridgeFailure message -> MkCastBlame message"
    ]

-- | Embedded @std.supervisor@ source (§29.2): the OTP-style supervision
-- surface. This is currently a typechecking/import surface only; restart
-- strategies, child execution, restart intensity, and shutdown semantics remain
-- future-stage library/runtime work.
stdSupervisorSource :: Text
stdSupervisorSource =
  T.unlines
    [ "module std.supervisor"
    , ""
    , "data SupervisorStrategy : Type ="
    , "    OneForOne"
    , "    OneForAll"
    , "    RestForOne"
    , ""
    , "data RestartPolicy : Type ="
    , "    Permanent"
    , "    Transient"
    , "    Temporary"
    , ""
    , "data RestartIntensity : Type ="
    , "    RestartIntensity (maxRestarts : Nat) (within : Duration)"
    , ""
    , "data ChildSpec (0 e : Type) : Type ="
    , "    ChildSpec (label : String) (restart : RestartPolicy) (run : IO e Unit)"
    , ""
    , "data Supervisor (0 e : Type) : Type ="
    , "    MkSupervisor (children : List (ChildSpec e))"
    , ""
    , "childSpec : forall (e : Type). String -> RestartPolicy -> IO e Unit -> ChildSpec e"
    , "let childSpec label restart run = ChildSpec label restart run"
    , ""
    , "startSupervisor :"
    , "    forall (e : Type)."
    , "    SupervisorStrategy ->"
    , "    RestartIntensity ->"
    , "    List (ChildSpec e) ->"
    , "    UIO (Supervisor e)"
    , "let startSupervisor strategy intensity children = pure (MkSupervisor children)"
    , ""
    , "shutdownSupervisor : forall (e : Type). Supervisor e -> UIO Unit"
    , "let shutdownSupervisor supervisor = pure ()"
    , ""
    , "awaitSupervisor : forall (e : Type). Supervisor e -> UIO (Exit e Unit)"
    , "let awaitSupervisor supervisor = pure (Success ())"
    , ""
    , "withSupervisor : forall (e : Type) (a : Type). SupervisorStrategy -> RestartIntensity -> List (ChildSpec e) -> (Supervisor e -> IO e a) -> IO e a"
    , "let withSupervisor strategy intensity children use = use (MkSupervisor children)"
    ]

-- | Embedded @std.config@ source (§35.4): the portable config-mode
-- external-input API. A build-manifest loader makes these names available
-- through the config schema scope (§35.3); portable config units do not
-- import @std.config@. 'ConfigInputKey' is config-safe and 'configInput'
-- constructs a typed input key so config-input expressions are in scope and
-- typecheck. NOTE: loader-side resolution of an external input value, and
-- the §35.13 standard request keys (@requestedTarget@/@requestedBackend@/…),
-- are NOT yet wired — the key is constructed but its value is never read
-- (tracked in docs/BUILD_AND_NATIVE_BINDINGS.md). @--target@ selects among
-- the produced targets post-hoc, which §35.13 permits for selection-only
-- parameters.
stdConfigSource :: Text
stdConfigSource =
  T.unlines
    [ "module std.config"
    , ""
    , "data ConfigInputKey (0 a : Type) : Type = MkConfigInputKey (name : String)"
    , "configInput : forall (a : Type). String -> ConfigInputKey a"
    , "let configInput name = MkConfigInputKey name"
    ]

-- | Embedded @std.build@ source (§29.8): the config-safe schema module
-- supplying the portable build-manifest vocabulary. A build-manifest
-- loader makes these names available through the config schema scope of
-- §35.3; portable manifests do not import @std.build@ (§29.8). This is
-- the increment-1 subset of §29.8 (package/source-root/fragment/
-- dependency/native-binding/target vocabulary); the larger workspace,
-- test/codegen/bridge/benchmark/publish, JVM/.NET/Python-ecosystem, and
-- reproducibility-status surfaces are sequenced follow-ups (a build
-- manifest MUST NOT assign a resolved 'ReproducibilityStatus' — §29.8 —
-- so no such constructor is exposed). Every declaration is a config-safe
-- data type, data constructor, or total transparent builder (§35.5);
-- constructing a value performs no discovery (§29.8).
stdBuildSource :: Text
stdBuildSource =
  T.unlines
    [ "module std.build"
    , ""
    , "data PackageVersion : Type = MkPackageVersion (raw : String)"
    , "let semver raw = MkPackageVersion raw"
    , ""
    , "data SourceRoot : Type = MkSourceRoot (path : String)"
    , "let sourceRoot path = MkSourceRoot path"
    , ""
    , "data FragmentTag : Type = MkFragmentTag (name : String)"
    , "let tag name = MkFragmentTag name"
    , ""
    , "data FragmentAxis : Type = MkFragmentAxis (name : String) (tags : List FragmentTag)"
    , "let axis name tags = MkFragmentAxis name tags"
    , ""
    , "data FragmentSelection : Type = MkFragmentSelection (tags : List String)"
    , "let tags ts = MkFragmentSelection ts"
    , ""
    , "data ModuleSelector : Type ="
    , "    SelModule (name : String)"
    , "    SelModulesUnder (prefix : String)"
    , "let module name = SelModule name"
    , "let modulesUnder prefix = SelModulesUnder prefix"
    , ""
    , "data BackendProfile : Type ="
    , "    NativeBackend (toolchain : String) (targetTriple : String)"
    , "    JvmBackend"
    , "    DotNetBackend"
    , "let native toolchain targetTriple = NativeBackend toolchain targetTriple"
    , "let jvm = JvmBackend"
    , "let dotnet = DotNetBackend"
    , ""
    , "data Dependency : Type ="
    , "    RegistryDep (name : String) (version : String)"
    , "    GitDep (name : String) (url : String) (rev : String)"
    , "    PathDep (name : String) (path : String)"
    , "    UrlDep (name : String) (url : String)"
    , "let registry name version = RegistryDep name version"
    , "let git name url rev = GitDep name url rev"
    , "let pathDependency name path = PathDep name path"
    , "let urlDependency name url = UrlDep name url"
    , ""
    , "-- §26.1.1/§26.1.4: the conservative ABI type vocabulary admitted in a"
    , "-- native binding's symbol signatures. Each maps to a documented Kappa"
    , "-- surface type and a C ABI type (see Kappa.Backend.NativeFfi)."
    , "data CType : Type ="
    , "    CtUnit"
    , "    CtInt"
    , "    CtInt64"
    , "    CtBool"
    , "    CtDouble"
    , "    CtString"
    , "    CtHandle"
    , "    CtRawPtr"
    , "    CtI8"
    , "    CtI16"
    , "    CtI32"
    , "    CtI64"
    , "    CtU8"
    , "    CtU16"
    , "    CtU32"
    , "    CtU64"
    , "    CtIsize"
    , "    CtUsize"
    , "    CtF32"
    , "    CtF64"
    , "let ctUnit = CtUnit"
    , "let ctInt = CtInt"
    , "let ctInt64 = CtInt64"
    , "let ctBool = CtBool"
    , "let ctDouble = CtDouble"
    , "let ctString = CtString"
    , "let ctHandle = CtHandle"
    , "let ctRawPtr = CtRawPtr"
    , "let ctI8 = CtI8"
    , "let ctI16 = CtI16"
    , "let ctI32 = CtI32"
    , "let ctI64 = CtI64"
    , "let ctU8 = CtU8"
    , "let ctU16 = CtU16"
    , "let ctU32 = CtU32"
    , "let ctU64 = CtU64"
    , "let ctIsize = CtIsize"
    , "let ctUsize = CtUsize"
    , "let ctF32 = CtF32"
    , "let ctF64 = CtF64"
    , ""
    , "-- §36.28: one exported native symbol — the Kappa member spelling, the"
    , "-- C symbol it calls, and its ABI signature (params + result)."
    , "data SymbolDecl : Type ="
    , "    MkSymbolDecl (member : String) (symbol : String) (params : List CType) (result : CType)"
    , "let symbolDecl member symbol params result = MkSymbolDecl member symbol params result"
    , ""
    , "-- §27.1.1: the binding's raw host.native surface, derived from an"
    , "-- explicit binding description (a symbol list with ABI signatures)."
    , "data NativeSurface : Type ="
    , "    SymbolListSurface (symbols : List SymbolDecl)"
    , "    GeneratedSurface (header : String) (symbols : List String)"
    , "    GeneratedPrefixSurface (header : String) (prefix : String)"
    , "let symbolList symbols = SymbolListSurface symbols"
    , "-- §27.1.1/§36.28: derive the raw surface by preprocessing + parsing a real"
    , "-- header (no hand-authored symbolDecl); 'symbols' names the C functions to"
    , "-- extract (a small curated surface, e.g. a shim's public API). The build"
    , "-- plan maps their C types to conservative std.ffi types."
    , "let generateFromHeader header symbols = GeneratedSurface header symbols"
    , "-- §26.1.2: derive a BROAD raw surface from EVERY function in 'header' whose"
    , "-- C name begins with 'prefix'; declarations needing callbacks/structs/"
    , "-- variadics are skipped (rejected, never guessed) and reported."
    , "let generateAllFromHeader header prefix = GeneratedPrefixSurface header prefix"
    , ""
    , "-- §36.28 binding sources: realization inputs naming WHERE/HOW the"
    , "-- declared C symbols are provided and located (header digests, shim"
    , "-- sources, pkg-config packages, prebuilt artifacts, module maps)."
    , "data NativeInput : Type ="
    , "    HeadersInput (paths : List String)"
    , "    IncludeDirInput (dir : String)"
    , "    DefineInput (name : String) (value : String)"
    , "    PkgConfigInput (package : String) (minVersion : Option String)"
    , "    ShimInput (sources : List String)"
    , "    ModuleMapInput (files : List String)"
    , "    PrebuiltInput (artifact : String) (expectedIdentity : Option String)"
    , "    ClassifyInput (class : FfiClass)"
    , "    CStringSymbolsInput (symbols : List String)"
    , "    VerifyInput (decls : List String)"
    , "let headers paths = HeadersInput paths"
    , "let includeDir dir = IncludeDirInput dir"
    , "let define name value = DefineInput name value"
    , "let pkgConfig package minVersion = PkgConfigInput package minVersion"
    , "let shim sources = ShimInput sources"
    , "let moduleMap files = ModuleMapInput files"
    , "let prebuiltNative artifact expectedIdentity = PrebuiltInput artifact expectedIdentity"
    , "let verify decls = VerifyInput decls"
    , "-- §26.1.4: declare the C symbols whose char* params/results are proven"
    , "-- NUL-terminated C strings; generation maps their char* to String (others"
    , "-- conservatively to Option RawPtr)."
    , "let cstrings symbols = CStringSymbolsInput symbols"
    , "-- §26.1.4/§27.6: foreign-call classification carried by a binding's raw"
    , "-- declarations (nonblocking | blocking | blocking-cancellable)."
    , "data FfiClass : Type = FfiNonblocking | FfiBlocking | FfiBlockingCancellable"
    , "let nonblocking = FfiNonblocking"
    , "let blocking = FfiBlocking"
    , "let blockingCancellable = FfiBlockingCancellable"
    , "let classify c = ClassifyInput c"
    , ""
    , "data NativeAbi : Type = CAbi"
    , "let cAbi = CAbi"
    , ""
    , "data NativeLinkSpec : Type ="
    , "    DynamicLink (libs : List String)"
    , "    StaticLink (libs : List String)"
    , "    NoLink"
    , "let dynamicLink libs = DynamicLink libs"
    , "let staticLink libs = StaticLink libs"
    , "let noLink = NoLink"
    , ""
    , "data NativeLoadSpec : Type ="
    , "    SystemLoader"
    , "    BundledLoader"
    , "    RuntimeLoad"
    , "    ProvidedByHost"
    , "let systemLoader = SystemLoader"
    , "let bundledLoader = BundledLoader"
    , "let runtimeLoad = RuntimeLoad"
    , "let providedByHost = ProvidedByHost"
    , ""
    , "data HostBinding : Type = MkNativeBinding (name : String) (provides : List ModuleSelector) (surface : NativeSurface) (abi : NativeAbi) (inputs : List NativeInput) (link : NativeLinkSpec) (load : NativeLoadSpec)"
    , "let nativeBinding name provides surface abi inputs link load = MkNativeBinding name provides surface abi inputs link load"
    , ""
    , "data Target : Type ="
    , "    ExecutableTarget (name : String) (backend : BackendProfile) (fragments : FragmentSelection) (main : ModuleSelector) (modules : ModuleSelector) (dependencies : List String) (hostBindings : List String)"
    , "    LibraryTarget (name : String) (backend : BackendProfile) (fragments : FragmentSelection) (modules : ModuleSelector) (dependencies : List String)"
    , "    TestTarget (name : String) (modules : ModuleSelector)"
    , "    AggregateTarget (name : String) (members : List String)"
    , "    AliasTarget (name : String) (target : String)"
    , "    BenchmarkTarget (name : String) (backend : BackendProfile) (fragments : FragmentSelection) (main : ModuleSelector) (modules : ModuleSelector) (dependencies : List String)"
    , "let executable name backend fragments main modules dependencies hostBindings = ExecutableTarget name backend fragments main modules dependencies hostBindings"
    , "let library name backend fragments modules dependencies = LibraryTarget name backend fragments modules dependencies"
    , "let test name modules = TestTarget name modules"
    , "let aggregate name members = AggregateTarget name members"
    , "let aliasTarget name target = AliasTarget name target"
    , "let benchmark name backend fragments main modules dependencies = BenchmarkTarget name backend fragments main modules dependencies"
    , ""
    , "data BuildConfig : Type = MkBuildConfig (name : String) (version : PackageVersion) (sourceRoots : List SourceRoot) (fragmentAxes : List FragmentAxis) (dependencies : List Dependency) (hostBindings : List HostBinding) (targets : List Target)"
    , "let package name version sourceRoots fragmentAxes dependencies hostBindings targets = MkBuildConfig name version sourceRoots fragmentAxes dependencies hostBindings targets"
    ]
