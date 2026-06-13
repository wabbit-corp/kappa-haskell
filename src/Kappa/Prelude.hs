-- | The implicit prelude (Spec §28): builtin types and primitives
-- registered directly, plus an embedded @std.prelude@ source compiled
-- through the ordinary pipeline. SPEC_COVERAGE.md documents which parts
-- of the §28.2 normative minimum are provided.
module Kappa.Prelude
  ( builtinState
  , preludeSource
  , stdDerivingShapeSource
  , stdHashSource
  , stdUnicodeSource
  , stdFfiSource
  , stdFfiCSource
  , stdAtomicSource
  , stdGradualSource
  , stdBridgeSource
  , stdSupervisorSource
  , evalPurePrim
  ) where

import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as T
import Kappa.Check
import Kappa.Core
import Kappa.Eval (evalPurePrim, lookupEnv)
import Kappa.Source (ModuleName (..))

prel :: Text -> GName
prel = GName preludeModule

-- small Pi-type builders (closed terms, evaluated lazily by the checker)
infixr 5 ~>
(~>) :: Term -> Term -> Term
a ~> b = CPi Expl QW "_" a b

piI :: Q -> Text -> Term -> Term -> Term
piI = CPi Impl

tcon :: Text -> Term
tcon = CGlob . prel

-- | Initial state: builtin types and primitives under @std.prelude@.
builtinState :: CheckState
builtinState =
  initCheckState
    { csModule = preludeModule
    , csGlobals = Map.fromList (types ++ prims ++ testingPrims)
    , csCtors = Map.fromList ctors
    , csDatas = Map.fromList datas
    , csModuleExports =
        Map.fromList [(testingModule, [nm | (GName _ nm, _) <- testingPrims])]
    }
  where
    opaqueTy t = GlobalDef t Nothing False
    prim name t = (prel name, GlobalDef t (Just (VPrim name [])) False)
    testingModule = ModuleName ["std", "testing"]
    -- @std.testing@ (§T.6 support library): @failNow@ aborts evaluation
    -- with a message; it reduces to a stuck primitive that the harness
    -- and runtime report as a runtime failure.
    testingPrims =
      [ ( GName testingModule "failNow"
        , GlobalDef (tyV (piI Q0 "a" tType (tStr ~> CVar 1))) (Just (VPrim "failNow" [])) False
        )
      ]

    tType = CSort 0
    tyV t = evalClosed t
    types =
      [ (prel "Integer", opaqueTy (tyV tType))
      , (prel "Nat", opaqueTy (tyV tType))
      , (prel "Double", opaqueTy (tyV tType))
      , (prel "String", opaqueTy (tyV tType))
      , (prel "UnicodeScalar", opaqueTy (tyV tType))
      , (prel "Grapheme", opaqueTy (tyV tType)) -- §28.2 user-perceived text atom
      , (prel "Byte", opaqueTy (tyV tType)) -- §28.2 single byte (§6.5 'b' handler)
      , (prel "Bytes", opaqueTy (tyV tType))
      , (prel "Region", opaqueTy (tyV tType)) -- §12.3 explicit region variables
      , -- §12.3.1 capture-annotated type former: part of type identity (§31.1)
        (prel "__captures", opaqueTy (tyV (tType ~> tcon "Region" ~> tType)))
      , (prel "Duration", opaqueTy (tyV tType)) -- §18.1 monotonic time difference
      , (prel "Instant", opaqueTy (tyV tType)) -- §18.1 monotonic time value
      , (prel "STM", opaqueTy (tyV (tType ~> tType))) -- §18.1.13
      , (prel "TVar", opaqueTy (tyV (tType ~> tType))) -- §18.1.13
      , (prel "Thunk", opaqueTy (tyV (tType ~> tType)))
      , (prel "Need", opaqueTy (tyV (tType ~> tType)))
      , (prel "IO", opaqueTy (tyV (tType ~> tType ~> tType)))
      , (prel "Ref", opaqueTy (tyV (tType ~> tType)))
      , -- §18.1.14 algebraic effects: the Eff carrier, effect rows and
        -- labels; rows are encoded as neutral spines
        -- '__effRowCons label iface rest' ending in '__effRowNil'
        (prel "EffRow", opaqueTy (tyV tType))
      , (prel "EffLabel", opaqueTy (tyV tType))
      , (prel "Eff", opaqueTy (tyV (tcon "EffRow" ~> tType ~> tType)))
      , (prel "__effRowNil", opaqueTy (tyV (tcon "EffRow")))
      , (prel "__effRowCons", opaqueTy (tyV (tcon "EffLabel" ~> tType ~> tcon "EffRow" ~> tcon "EffRow")))
      , -- §20 collection carriers and the §20.10 query core
        (prel "Set", opaqueTy (tyV (tType ~> tType)))
      , (prel "Map", opaqueTy (tyV (tType ~> tType ~> tType)))
      , (prel "Array", opaqueTy (tyV (tType ~> tType)))
      , (prel "Quantity", opaqueTy (tyV tType)) -- §12.1.1 reified quantities
      , -- phantom carrier for the corpus 'Array n elem' accommodation
        -- (see inferT in Kappa.Check)
        (prel "__sizedOf", opaqueTy (tyV (tcon "Nat" ~> tType ~> tType)))
      , -- §11.3.1 record rows: row kind, the lacks constraint (labels
        -- are elaborated to string literals), and the open-record
        -- encoding '__openRec r (explicit-prefix record type)'
        (prel "RecRow", opaqueTy (tyV tType))
      , (prel "LacksRec", opaqueTy (tyV (tcon "RecRow" ~> tStr ~> tType)))
      , (prel "__openRec", opaqueTy (tyV (tcon "RecRow" ~> tType ~> tType)))
      , (prel "__rowExtend", GlobalDef (tyV (piI Q0 "a" tType (piI Q0 "b" tType (CVar 1 ~> tStr ~> CVar 2 ~> CVar 4)))) (Just (VPrim "__rowExtend" [])) False)
      , -- a closed residual row tail '__closedRow (fields record type)':
        -- solving an open record against a closed record instantiates
        -- the row tail with the leftover closed fields (§11.3.1A)
        (prel "__closedRow", opaqueTy (tyV (tType ~> tcon "RecRow")))
      , -- compiler-owned introduction-rule witness for the §11.3.1A
        -- intrinsic row traits (the evidence carries no information)
        (prel "__rowEvidence", opaqueTy (tyV (piI Q0 "r" (tcon "RecRow") (piI Q0 "l" tStr (CApp Expl (CApp Expl (tcon "LacksRec") (CVar 1)) (CVar 0))))))
      , (prel "ω", GlobalDef (tyV (tcon "Quantity")) (Just (VPrim "__omegaQ" [])) False)
      , (prel "QueryCore", opaqueTy (tyV (tcon "QueryMode" ~> tcon "Quantity" ~> tType ~> tType)))
      , (prel "BorrowView", opaqueTy (tyV (tcon "Region" ~> tType ~> tType))) -- §20.10.2
      , -- §12.4.3 first-class projector and accessor descriptors
        (prel "Projector", opaqueTy (tyV (tType ~> tType ~> tType)))
      , (prel "Getter", opaqueTy (tyV (tType ~> tType ~> tType)))
      , (prel "Opener", opaqueTy (tyV (tType ~> tType ~> tType)))
      , (prel "Setter", opaqueTy (tyV (tType ~> tType ~> tType)))
      , (prel "Sinker", opaqueTy (tyV (tType ~> tType ~> tType)))
      , (prel "composeProjector", GlobalDef composeProjectorTy (Just (VPrim "composeProjector" [])) False)
      , (prel "captureBorrow", GlobalDef captureBorrowTy (Just (VPrim "captureBorrow" [])) False)
      , (prel "withBorrowView", GlobalDef withBorrowViewTy (Just (VPrim "withBorrowView" [])) False)
      , -- propositional equality (§11.4.1): (=) (@0 a) (x : a) : a -> Type
        (prel "=", opaqueTy (tyV (piI Q0 "a" tType (CVar 0 ~> CVar 1 ~> tType))))
      , (prel "refl", GlobalDef reflTy Nothing False)
      , -- §21 metaprogramming: compile-time-only type families (the
        -- domains live one universe up so 'Syntax Type' is well-typed
        -- under §11.1.1 cumulativity)
        (prel "Syntax", opaqueTy (tyV (CSort 1 ~> tType)))
      , (prel "Elab", opaqueTy (tyV (CSort 1 ~> tType)))
      , (prel "SyntaxOrigin", opaqueTy (tyV tType))
      , -- §21.6 semantic-reflection symbol identity (compile-time only)
        (prel "Symbol", opaqueTy (tyV tType))
      , -- §23.1 generative staged code (not inspectable as Syntax)
        (prel "Code", opaqueTy (tyV (tType ~> tType)))
      , (prel "ClosedCode", opaqueTy (tyV (tType ~> tType)))
      , -- §20.9 opaque carriers passed to comprehension sink hooks
        (prel "RawComprehension", opaqueTy (tyV (tType ~> tType)))
      , (prel "ComprehensionPlan", opaqueTy (tyV (tType ~> tType)))
      , -- §22.4 trait-constructor classifier (witnesses synthesized by
        -- implicit resolution when the head is a declared trait)
        (prel "IsTrait", opaqueTy (tyV (tType ~> tType)))
      , (prel "__isTraitWitness", opaqueTy (tyV (piI Q0 "t" tType (CApp Expl (tcon "IsTrait") (CVar 0)))))
      ]
    reflTy =
      tyV $
        piI Q0 "a" tType $
          piI Q0 "x" (CVar 0) $
            CApp Expl (CApp Expl (CApp Impl (tcon "=") (CVar 1)) (CVar 0)) (CVar 0)
    projT r f = CApp Expl (CApp Expl (tcon "Projector") r) f
    -- §12.4.3 composeProjector (one-field root packs of the middle
    -- projector are admitted structurally, hence the extra parameter)
    composeProjectorTy =
      tyV $
        piI Q0 "roots" tType $
          piI Q0 "mid" tType $
            piI Q0 "midRoots" tType $
              piI Q0 "focus" tType $
                CPi Expl QW "_" (projT (CVar 3) (CVar 2)) $
                  CPi Expl QW "_" (projT (CVar 2) (CVar 1)) $
                    projT (CVar 5) (CVar 2)
    captureBorrowTy =
      tyV $
        piI Q0 "ρ" (tcon "Region") $
          piI Q0 "a" tType $
            CPi Expl QW "_" (CVar 0) $
              CApp Expl (CApp Expl (tcon "BorrowView") (CVar 2)) (CVar 1)
    withBorrowViewTy =
      tyV $
        piI Q0 "ρ" (tcon "Region") $
          piI Q0 "a" tType $
            piI Q0 "r" tType $
              CPi Expl QW "_" (CApp Expl (CApp Expl (tcon "BorrowView") (CVar 2)) (CVar 1)) $
                CPi Expl QW "_" (CPi Expl QW "_" (CVar 2) (CVar 2)) $
                  CVar 2
    ctors =
      [ (prel "refl", CtorInfo (prel "=") (quoteClosedTy reflTy) [])
      ]
    datas =
      [ (prel "=", DataInfo [prel "refl"] 3)
      ]
    quoteClosedTy _ = piI Q0 "a" tType (piI Q0 "x" (CVar 0) (CApp Expl (CApp Expl (CApp Impl (tcon "=") (CVar 1)) (CVar 0)) (CVar 0)))

    tInt = tcon "Integer"
    tNat = tcon "Nat"
    synT a = CApp Expl (tcon "Syntax") a
    elabT a = CApp Expl (tcon "Elab") a
    tOrigin = tcon "SyntaxOrigin"
    tconShape = CGlob . GName shapeModule
    tDouble = tcon "Double"
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
    listT a = CApp Expl (tcon "List") a
    setT a = CApp Expl (tcon "Set") a
    arrayT a = CApp Expl (tcon "Array") a
    mapT k v = CApp Expl (CApp Expl (tcon "Map") k) v
    queryT m q a = CApp Expl (CApp Expl (CApp Expl (tcon "QueryCore") m) q) a
    entryT k v = CRecordT [("key", k), ("value", v)]
    forallE body = piI Q0 "e" tType body -- erased error param
    forallEA body = piI Q0 "e" tType (piI Q0 "a" tType body)

    prims =
      [ prim "addInt" (tyV (tInt ~> tInt ~> tInt))
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
      , prim "__byteToNat" (tyV (tByte ~> tNat))
      , -- §29.1 std.atomic bitwise read-modify-write internals
        prim "__intAnd" (tyV (tInt ~> tInt ~> tInt))
      , prim "__intOr" (tyV (tInt ~> tInt ~> tInt))
      , prim "__intXor" (tyV (tInt ~> tInt ~> tInt))
      , -- §29.1 representation equality for atomicCompareExchange
        prim "__atomicRepEq" (tyV (piI Q0 "a" tType (CVar 0 ~> CVar 1 ~> tcon "Bool")))
      , -- §29.3 std.hash mixing internals (deterministic within a run)
        prim "__hashMixInt" (tyV (tInt ~> tInt ~> tInt))
      , prim "__hashMixDouble" (tyV (tInt ~> tDouble ~> tInt))
      , prim "__hashMixString" (tyV (tInt ~> tStr ~> tInt))
      , prim "__hashMixBytes" (tyV (tInt ~> tBytes ~> tInt))
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
        prim "unsafeConsume" (tyV (piI Q0 "a" tType (CPi Expl Q1 "x" (CVar 0) tUnit)))
      , prim "printString" (tyV (forallE (tStr ~> io (CVar 1) tUnit)))
      , prim "printlnString" (tyV (forallE (tStr ~> io (CVar 1) tUnit)))
      , prim "ioPure" (tyV (forallEA (CVar 0 ~> io (CVar 2) (CVar 1))))
      , prim "throwIO" (tyV (forallEA (CVar 1 ~> io (CVar 2) (CVar 1))))
      , prim "catchIO" (tyV (forallEA (io (CVar 1) (CVar 0) ~> (CVar 2 ~> io (CVar 3) (CVar 2)) ~> io (CVar 3) (CVar 2))))
      , prim "finallyIO" (tyV (forallEA (io (CVar 1) (CVar 0) ~> io (CVar 2) tUnit ~> io (CVar 3) (CVar 2))))
      , prim "__runIO" (tyV (forallEA (io (CVar 1) (CVar 0) ~> CVar 1)))
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
      , -- §18.1.13: aborted STM alternative (the `empty` action)
        prim "stmAbort" (tyV (forallEA (io (CVar 1) (CVar 0))))
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
      , prim "__mapFromEntries"
          (tyV (piI Q0 "k" tType (piI Q0 "v" tType (listT (entryT (CVar 1) (CVar 0)) ~> mapT (CVar 2) (CVar 1)))))
      , prim "__mapToList"
          (tyV (piI Q0 "k" tType (piI Q0 "v" tType (mapT (CVar 1) (CVar 0) ~> listT (entryT (CVar 2) (CVar 1))))))
      , prim "newRef" (tyV (forallEA (CVar 0 ~> io (CVar 2) (refT (CVar 1)))))
      , prim "readRef" (tyV (forallEA (refT (CVar 0) ~> io (CVar 2) (CVar 1))))
      , prim "writeRef" (tyV (forallEA (refT (CVar 0) ~> CVar 1 ~> io (CVar 3) tUnit)))
      , -- §21.5/§21.9 elaboration-time reflection and diagnostics
        -- (interpreted by the elaborator's §21.8 Elab runner; stuck as
        -- values everywhere else)
        prim "renderSyntax" (tyV (piI Q0 "t" tType (synT (CVar 0) ~> elabT tStr)))
      , prim "syntaxOrigin" (tyV (piI Q0 "t" tType (synT (CVar 0) ~> elabT tOrigin)))
      , prim "normalizeSyntax" (tyV (piI Q0 "t" tType (synT (CVar 0) ~> elabT (synT (CVar 1)))))
      , prim "withSyntaxOrigin" (tyV (piI Q0 "t" tType (tOrigin ~> synT (CVar 1) ~> elabT (synT (CVar 2)))))
      , prim "whnfSyntax" (tyV (piI Q0 "t" tType (synT (CVar 0) ~> elabT (synT (CVar 1)))))
      , -- §21.6 semantic-reflection convenience queries (elaboration-time;
        -- interpreted by 'Kappa.Check.runElab')
        prim "defEqSyntax"
          (tyV (piI Q0 "a" tType (piI Q0 "b" tType (synT (CVar 1) ~> synT (CVar 1) ~> elabT tBool))))
      , prim "headSymbolSyntax"
          (tyV (piI Q0 "t" tType (synT (CVar 0) ~> elabT (optionT (tcon "Symbol")))))
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
          (tyV (CPi Expl QW "a" tType (synT tType ~> elabT (CApp Expl (tconShape "AdtShape") (CVar 1)))))
      , prim "__shapeInspectRecord"
          (tyV (CPi Expl QW "a" tType (synT tType ~> elabT (CApp Expl (tconShape "RecordShape") (CVar 1)))))
      , prim "__shapeRequireFieldInstances"
          (tyV (CPi Expl QW "tc" (tType ~> tType) (CPi Expl QW "a" tType (CApp Expl (tconShape "AdtShape") (CVar 0) ~> elabT tUnit))))
      , prim "__shapeMatchAdt"
          (tyV
             (piI Q0 "a" tType (piI Q0 "r" tType
                (CApp Expl (tconShape "AdtShape") (CVar 1)
                   ~> synT (CVar 2)
                   ~> ((tconShape "ShapeConstructor" ~> listT (tconShape "BoundField") ~> elabT (synT (CVar 4))) ~> elabT (synT (CVar 3)))))))
      , prim "__shapeMatchAdt2"
          (tyV
             (piI Q0 "a" tType (piI Q0 "r" tType
                (CApp Expl (tconShape "AdtShape") (CVar 1)
                   ~> synT (CVar 2)
                   ~> synT (CVar 3)
                   ~> ((tconShape "ShapeConstructor" ~> listT (tconShape "BoundFieldPair") ~> elabT (synT (CVar 5)))
                         ~> ((tconShape "ShapeConstructor" ~> tconShape "ShapeConstructor" ~> elabT (synT (CVar 6)))
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
      CGlob g -> VGlobN g []
      CPi ic q n a b -> VPi ic q n (go env a) (Closure env b)
      CApp ic f a -> app (go env f) ic (go env a)
      CSort n -> VSort n
      CRecordT fs -> VRecordT [(n, go env t) | (n, t) <- fs]
      t -> VPrim (T.pack (show t)) []
    app (VGlobN g sp) ic a = VGlobN g (sp ++ [(ic, a)])
    app f _ _ = f


-- | Embedded @std.prelude@ source (§28.2 subset; see SPEC_COVERAGE.md).
preludeSource :: Text
preludeSource =
  T.unlines
    [ "data Void : Type"
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
    , "data Option (a : Type) : Type ="
    , "    None"
    , "    Some a"
    , ""
    , "data Result (e : Type) (a : Type) : Type ="
    , "    Ok a"
    , "    Err e"
    , ""
    , "data List (a : Type) : Type ="
    , "    Nil"
    , "    (::) (head : a) (tail : List a)"
    , ""
    , -- §12.4.3 canonical zipper: an opened owned focus plus a linear
      -- filler back to the whole
      "data Zipper (whole : Type) (focus : Type) (replace : Type) : Type ="
    , "    Zipper (focus : focus) (1 fill : replace -> whole)"
    , ""
    , "type Int = Integer"
    , "type Float = Double"
    , "type Char = UnicodeScalar" -- sanctioned alias (§28.5)
    , "type UIO (a : Type) = IO Void a"
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
    , "trait Show (a : Type) ="
    , "    show : a -> String"
    , ""
    , "trait Eq (a : Type) ="
    , "    (==) : a -> a -> Bool"
    , ""
    , "trait Ord (a : Type) ="
    , "    compare : a -> a -> Ordering"
    , ""
    , "trait Add (a : Type) ="
    , "    add : a -> a -> a"
    , ""
    , "trait Mul (a : Type) ="
    , "    multiply : a -> a -> a"
    , ""
    , "trait Negatable (a : Type) ="
    , "    negate : a -> a"
    , ""
    , "trait CheckedSub (a : Type) ="
    , "    subDefined : a -> a -> Bool"
    , "    subtractUnchecked : a -> a -> a"
    , ""
    , "trait CheckedDiv (a : Type) ="
    , "    divDefined : a -> a -> Bool"
    , "    divideUnchecked : a -> a -> a"
    , ""
    , "trait CheckedMod (a : Type) ="
    , "    modDefined : a -> a -> Bool"
    , "    moduloUnchecked : a -> a -> a"
    , ""
    , "trait FromInteger (t : Type) ="
    , "    fromInteger : Nat -> t"
    , ""
    , "trait FromFloat (t : Type) ="
    , "    fromFloat : Double -> t"
    , ""
    , "trait FromString (t : Type) =" -- §28.2 (ordinary library trait)
    , "    fromString : String -> t"
    , ""
    , "instance FromString String ="
    , "    let fromString s = s"
    , ""
    , "trait EuclideanSemiring (a : Type) =" -- §28.2.1 (Nat only)
    , "    euclideanDivMod : a -> a -> (a, a)"
    , ""
    , "instance EuclideanSemiring Nat ="
    , "    let euclideanDivMod x y = (natOfInt (divInt (natToInt x) (natToInt y)), natOfInt (modInt (natToInt x) (natToInt y)))"
    , ""
    , "trait Monad (m : Type -> Type) =" -- §28.2.2 (operational subset)
    , "    (>>=) : forall (a : Type) (b : Type). m a -> (a -> m b) -> m b"
    , ""
    , "instance Monad Option ="
    , "    let (>>=) o f ="
    , "        match o"
    , "        case None -> None"
    , "        case Some x -> f x"
    , ""
    , "trait Releasable (m : Type -> Type) (a : Type) =" -- §29.x resources
    , "    release : a -> m Unit"
    , ""
    , "trait Zero (a : Type) ="
    , "    zero : a"
    , ""
    , "trait One (a : Type) ="
    , "    one : a"
    , ""
    , "trait Shareable (a : Type)" -- §12.3 marker: shared-borrow-safe
    , ""
    , "trait Lift (a : Type) =" -- §23.3 lift-based cross-stage persistence
    , "    liftCode : a -> Code a"
    , ""
    , "trait Monoid (a : Type) =" -- §28.2.2
    , "    empty : a"
    , "    append : a -> a -> a"
    , ""
    , "trait Functor (f : Type -> Type) =" -- §28.2.2 containers
    , "    map : forall (a : Type) (b : Type). (a -> b) -> f a -> f b"
    , ""
    , "trait Foldable (t : Type -> Type) ="
    , "    foldr : forall (a : Type) (b : Type). (a -> b -> b) -> b -> t a -> b"
    , "    foldl : forall (a : Type) (b : Type). (b -> a -> b) -> b -> t a -> b"
    , "    foldMap : forall (a : Type) (m : Type). (@_ : Monoid m) -> (a -> m) -> t a -> m"
    , ""
    , "trait Filterable (t : Type -> Type) ="
    , "    filter : forall (a : Type). (a -> Bool) -> t a -> t a"
    , ""
    , "trait FilterMap (t : Type -> Type) ="
    , "    filterMap : forall (a : Type) (b : Type). (a -> Option b) -> t a -> t b"
    , ""
    , "trait Applicative (f : Type -> Type) ="
    , "    pureA : forall (a : Type). a -> f a"
    , "    liftA2 : forall (a : Type) (b : Type) (c : Type). (a -> b -> c) -> f a -> f b -> f c"
    , ""
    , "trait Traversable (t : Type -> Type) ="
    , "    traverse : forall (f : Type -> Type) (a : Type) (b : Type). (@_ : Applicative f) -> (a -> f b) -> t a -> f (t b)"
    , ""
    , "(+) : forall (a : Type). (@_ : Add a) -> a -> a -> a"
    , "let (+) x y = add x y"
    , ""
    , "(*) : forall (a : Type). (@_ : Mul a) -> a -> a -> a"
    , "let (*) x y = multiply x y"
    , ""
    , "(-) : forall (a : Type). (@_ : CheckedSub a) -> (x : a) -> (y : a) -> (@_ : subDefined x y = True) -> a"
    , "let (-) x y = subtractUnchecked x y"
    , ""
    , "(/) : forall (a : Type). (@_ : CheckedDiv a) -> (x : a) -> (y : a) -> (@_ : divDefined x y = True) -> a"
    , "let (/) x y = divideUnchecked x y"
    , ""
    , "(%) : forall (a : Type). (@_ : CheckedMod a) -> (x : a) -> (y : a) -> (@_ : modDefined x y = True) -> a"
    , "let (%) x y = moduloUnchecked x y"
    , ""
    , "(/=) : forall (a : Type). (@_ : Eq a) -> a -> a -> Bool"
    , "let (/=) x y = not (x == y)"
    , ""
    , "(!=) : forall (a : Type). (@_ : Eq a) -> a -> a -> Bool"
    , "let (!=) x y = not (x == y)"
    , ""
    , "(<) : forall (a : Type). (@_ : Ord a) -> a -> a -> Bool"
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
    , "    let subtractUnchecked x y = subInt x y"
    , ""
    , "instance CheckedDiv Integer ="
    , "    let divDefined x y = not (eqInt y 0)"
    , "    let divideUnchecked x y = divInt x y"
    , ""
    , "instance CheckedMod Integer ="
    , "    let modDefined x y = not (eqInt y 0)"
    , "    let moduloUnchecked x y = modInt x y"
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
      "data NumericRange (v : Type) : Type ="
    , "    NumericRange (rangeFrom : v) (rangeTo : v) (rangeExclusive : Bool)"
    , ""
    , "trait Rangeable (v : Type) ="
    , "    range : v -> v -> Bool -> NumericRange v"
    , ""
    , "(..) : forall (v : Type). (@_ : Rangeable v) -> v -> v -> NumericRange v"
    , "let (..) lo hi = range lo hi False"
    , ""
    , "(..<) : forall (v : Type). (@_ : Rangeable v) -> v -> v -> NumericRange v"
    , "let (..<) lo hi = range lo hi True"
    , ""
    , "instance Rangeable Integer ="
    , "    let range lo hi excl = NumericRange lo hi excl"
    , ""
    , "instance Rangeable Nat ="
    , "    let range lo hi excl = NumericRange lo hi excl"
    , ""
    , "instance Rangeable UnicodeScalar =" -- §6.4
    , "    let range lo hi excl = NumericRange lo hi excl"
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
    , "    let compare x y = if ltInt (natToInt x) (natToInt y) then LT elif eqInt (natToInt x) (natToInt y) then EQ else GT"
    , ""
    , "instance Show Nat ="
    , "    let show n = showInt (natToInt n)"
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
    , -- §18.1.13: `empty` (the aborted alternative) resolves through
      -- Monoid, so STM-shaped do-scopes can sequence it as an action
      "instance Monoid (IO e a) ="
    , "    let empty = stmAbort"
    , "    let append x y = catchIO x (\\err -> y)"
    , ""
    , -- §18.11: structured-concurrency handles (check-mode support)
      "data Fiber (e : Type) (a : Type) : Type ="
    , "    MkFiberHandle"
    , ""
    , -- §18.8.2 terminal results and causes (vocabulary subset)
      "data InterruptCause : Type ="
    , "    MkInterruptCause"
    , ""
    , "data DefectInfo : Type ="
    , "    MkDefectInfo (message : String)"
    , ""
    , "data Cause (e : Type) : Type ="
    , "    Fail e"
    , "    Interrupt InterruptCause"
    , "    Defect DefectInfo"
    , "    Both (Cause e) (Cause e)"
    , "    Then (Cause e) (Cause e)"
    , ""
    , "data Exit (e : Type) (a : Type) : Type ="
    , "    Success a"
    , "    Failure (Cause e)"
    , ""
    , -- §11.6 decidability witness
      "data Dec (p : Type) : Type ="
    , "    Yes p"
    , "    No (p -> Void)"
    , ""
    , "fork : forall (e : Type) (a : Type) (r : Type). IO e a -> IO r (Fiber e a)"
    , "let fork action = ioPure MkFiberHandle"
    , ""
    , "throwError : forall (e : Type) (a : Type). e -> IO e a"
    , "let throwError err = throwIO err"
    , ""
    , "raise : forall (e : Type) (a : Type). e -> IO e a"
    , "let raise err = throwIO err"
    , ""
    , "catchError : forall (e : Type) (a : Type). IO e a -> (e -> IO e a) -> IO e a"
    , "let catchError body handler = catchIO body handler"
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
    , "    let add x y = natOfInt (addInt (natToInt x) (natToInt y))"
    , ""
    , "instance Mul Nat ="
    , "    let multiply x y = natOfInt (mulInt (natToInt x) (natToInt y))"
    , ""
    , "instance Negatable Double ="
    , "    let negate x = negDouble x"
    , ""
    , "instance CheckedDiv Nat ="
    , "    let divDefined x y = not (eqInt (natToInt y) 0)"
    , "    let divideUnchecked x y = natOfInt (divInt (natToInt x) (natToInt y))"
    , ""
    , "instance CheckedMod Nat ="
    , "    let modDefined x y = not (eqInt (natToInt y) 0)"
    , "    let moduloUnchecked x y = natOfInt (modInt (natToInt x) (natToInt y))"
    , ""
    , "instance CheckedDiv Double ="
    , "    let divDefined x y = not (eqDouble y 0.0)"
    , "    let divideUnchecked x y = divDouble x y"
    , ""
    , "instance Monoid String ="
    , "    let empty = \"\""
    , "    let append x y = stringAppend x y"
    , ""
    , "instance Monoid (List a) ="
    , "    let empty = Nil"
    , "    let append x y = listAppend x y"
    , ""
    , "instance Functor List ="
    , "    let map f xs ="
    , "        match xs"
    , "        case Nil -> Nil"
    , "        case x :: rest -> f x :: map f rest"
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
    , "instance Applicative Option ="
    , "    let pureA x = Some x"
    , "    let liftA2 f a b ="
    , "        match a"
    , "        case None -> None"
    , "        case Some x ->"
    , "            match b"
    , "            case None -> None"
    , "            case Some y -> Some (f x y)"
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
    , "sequence : forall (t : Type -> Type) (f : Type -> Type) (a : Type). (@_ : Traversable t) -> (@_ : Applicative f) -> t (f a) -> f (t a)"
    , "let sequence xs = traverse (\\v -> v) xs"
    , ""
    , "subtract : forall (a : Type). (@_ : CheckedSub a) -> a -> a -> a"
    , "let subtract x y = subtractUnchecked x y"
    , ""
    , "divide : forall (a : Type). (@_ : CheckedDiv a) -> a -> a -> a"
    , "let divide x y = divideUnchecked x y"
    , ""
    , "modulo : forall (a : Type). (@_ : CheckedMod a) -> a -> a -> a"
    , "let modulo x y = moduloUnchecked x y"
    , ""
    , "summon : (goal : Type) -> (@ev : goal) -> goal" -- §14.3.2
    , "let summon goal @ev = ev"
    , ""
    , -- §17.3: partial active patterns that thread a residue on a miss
      "data Match (a : Type) (r : Type) : Type ="
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
      "type Query (a : Type) = QueryCore (QueryMode.QueryMode QueryUse.Reusable QueryCard.QZeroOrMore) ω a"
    , "type OnceQuery (a : Type) = QueryCore (QueryMode.QueryMode QueryUse.OneShot QueryCard.QZeroOrMore) ω a"
    , "type SingletonQuery (a : Type) = QueryCore (QueryMode.QueryMode QueryUse.Reusable QueryCard.QOne) ω a"
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
    , "trait InterpolatedMacro (t : Type) ="
    , "    buildInterpolated : List SyntaxFragment -> Elab (Syntax t)"
    , ""
    , -- §20.9 custom comprehension sinks (the associated 'Item' type is
      -- an ordinary member of type 'Type'; the hook parameter is typed
      -- by the opaque carrier — the §21.8 elaboration-time evaluator
      -- passes an opaque token)
      "trait FromComprehensionRaw (c : Type) ="
    , "    Item : Type"
    , "    fromComprehensionRaw : RawComprehension c -> Elab (Syntax c)"
    , ""
    , "trait FromComprehensionPlan (c : Type) ="
    , "    Item : Type"
    , "    fromComprehensionPlan : ComprehensionPlan c -> Elab (Syntax c)"
    ]

-- | Embedded @std.deriving.shape@ source (§22): the Phase 0
-- derivation-shape reflection surface. The shape summaries carry the
-- subset of the §22 fields the reflection queries of this
-- implementation populate (names, tags, constructor field lists); the
-- reflective operations are elaborator primitives executed by the
-- §21.8 Elab runner. See SPEC_COVERAGE.md for the provided subset.
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
    , "data AdtShape (a : Type) : Type ="
    , "    AdtShape (sourceName : String) (renderName : String) (visibility : ShapeVisibility) (kind : ShapeAdtKind) (constructors : List ShapeConstructor)"
    , ""
    , "data RecordShape (a : Type) : Type ="
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
    , "    forall (tc : Type -> Type) (@0 a : Type)."
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
-- see SPEC_COVERAGE.md.
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
    , "trait Hashable (a : Type) ="
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

-- | Embedded @std.unicode@ source (§29.4 subset; see SPEC_COVERAGE.md).
-- Unicode data version: UCD 15.0.0 (Kappa.UnicodeData); normalization,
-- canonical equivalence and grapheme segmentation are full-fidelity for
-- that version, word\/sentence segmentation are documented
-- approximations, and the incremental decoder\/builders\/cursors of
-- §29.4 are not provided.
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

-- | Embedded @std.atomic@ source (§29.1): the canonical surface over
-- 'Ref' cells. The interpreter runs fibers cooperatively on one
-- thread, so every memory order is trivially sequentially consistent.
stdAtomicSource :: Text
stdAtomicSource =
  T.unlines
    [ "module std.atomic"
    , ""
    , "data AtomicRef (a : Type) : Type ="
    , "    MkAtomicRef (cell : Ref a)"
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
    , "data CompareExchangeResult (a : Type) : Type ="
    , "    Exchanged (old : a)"
    , "    NotExchanged (current : a)"
    , ""
    , "trait AtomicValue (a : Type)"
    , ""
    , "trait AtomicInteger (a : Type)"
    , ""
    , "instance AtomicValue Bool"
    , "instance AtomicValue Integer"
    , "instance AtomicInteger Integer"
    , ""
    , "newAtomicRef : forall (a : Type). (@_ : AtomicValue a) -> a -> UIO (AtomicRef a)"
    , "let newAtomicRef initial = do"
    , "    cell <- newRef initial"
    , "    pure (MkAtomicRef cell)"
    , ""
    , "atomicLoad : forall (a : Type). (@_ : AtomicValue a) -> LoadOrder -> AtomicRef a -> UIO a"
    , "let atomicLoad order ref ="
    , "    match ref"
    , "    case MkAtomicRef cell -> readRef cell"
    , ""
    , "atomicStore : forall (a : Type). (@_ : AtomicValue a) -> StoreOrder -> AtomicRef a -> a -> UIO Unit"
    , "let atomicStore order ref value ="
    , "    match ref"
    , "    case MkAtomicRef cell -> writeRef cell value"
    , ""
    , "atomicExchange : forall (a : Type). (@_ : AtomicValue a) -> RmwOrder -> AtomicRef a -> a -> UIO a"
    , "let atomicExchange order ref value ="
    , "    match ref"
    , "    case MkAtomicRef cell -> do"
    , "        old <- readRef cell"
    , "        writeRef cell value"
    , "        pure old"
    , ""
    , "atomicCompareExchange : forall (a : Type). (@_ : AtomicValue a) -> RmwOrder -> CasFailureOrder -> AtomicRef a -> a -> a -> UIO (CompareExchangeResult a)"
    , "let atomicCompareExchange success failure ref expected desired ="
    , "    match ref"
    , "    case MkAtomicRef cell -> ioBind (readRef cell) (\\current -> if __atomicRepEq current expected then ioBind (writeRef cell desired) (\\ignored -> ioPure (Exchanged current)) else ioPure (NotExchanged current))"
    , ""
    , "__atomicRmw : forall (a : Type). (a -> a -> a) -> RmwOrder -> AtomicRef a -> a -> UIO a"
    , "let __atomicRmw op order ref operand ="
    , "    match ref"
    , "    case MkAtomicRef cell -> do"
    , "        old <- readRef cell"
    , "        writeRef cell (op old operand)"
    , "        pure old"
    , ""
    , "atomicFetchAdd : RmwOrder -> AtomicRef Integer -> Integer -> UIO Integer"
    , "let atomicFetchAdd order ref operand = __atomicRmw addInt order ref operand"
    , ""
    , "atomicFetchSub : RmwOrder -> AtomicRef Integer -> Integer -> UIO Integer"
    , "let atomicFetchSub order ref operand = __atomicRmw subInt order ref operand"
    , ""
    , "atomicFetchAnd : RmwOrder -> AtomicRef Integer -> Integer -> UIO Integer"
    , "let atomicFetchAnd order ref operand = __atomicRmw __intAnd order ref operand"
    , ""
    , "atomicFetchOr : RmwOrder -> AtomicRef Integer -> Integer -> UIO Integer"
    , "let atomicFetchOr order ref operand = __atomicRmw __intOr order ref operand"
    , ""
    , "atomicFetchXor : RmwOrder -> AtomicRef Integer -> Integer -> UIO Integer"
    , "let atomicFetchXor order ref operand = __atomicRmw __intXor order ref operand"
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
    , "data DynRep (a : Type) : Type ="
    , "    MkDynRep (tag : String)"
    , ""
    , "data Dyn : Type ="
    , "    MkDyn (tag : String)"
    , ""
    , "trait DynamicType (a : Type) ="
    , "    dynRep : DynRep a"
    , ""
    , "toDynWith : forall (a : Type). DynRep a -> a -> Dyn"
    , "let toDynWith rep value ="
    , "    match rep"
    , "    case MkDynRep tag -> MkDyn tag"
    , ""
    , "checkedCastWith : forall (a : Type). DynRep a -> Dyn -> Result CastBlame a"
    , "let checkedCastWith rep value ="
    , "    Err (MkCastBlame \"std.gradual: dynamic payloads are not carried by this implementation\")"
    , ""
    , "sameDynRep : forall (a : Type) (b : Type). DynRep a -> DynRep b -> Option (Dec ((=) a b))"
    , "let sameDynRep x y = None"
    , ""
    , "toDyn : forall (a : Type). (@_ : DynamicType a) -> a -> Dyn"
    , "let toDyn value = toDynWith dynRep value"
    , ""
    , "checkedCast : forall (a : Type). (@_ : DynamicType a) -> Dyn -> Result CastBlame a"
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
    , "trait BridgeHandle (h : Type) ="
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
-- surface. The interpreter has no preemptive fiber runtime; children
-- run to completion in list order at start (check-mode fidelity).
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
    , "data ChildSpec (e : Type) : Type ="
    , "    ChildSpec (label : String) (restart : RestartPolicy) (run : IO e Unit)"
    , ""
    , "data Supervisor (e : Type) : Type ="
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
