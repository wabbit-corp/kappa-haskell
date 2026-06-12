-- | The implicit prelude (Spec §28): builtin types and primitives
-- registered directly, plus an embedded @std.prelude@ source compiled
-- through the ordinary pipeline. SPEC_COVERAGE.md documents which parts
-- of the §28.2 normative minimum are provided.
module Kappa.Prelude
  ( builtinState
  , preludeSource
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
      , (prel "Bytes", opaqueTy (tyV tType))
      , (prel "Region", opaqueTy (tyV tType)) -- §12.3 explicit region variables
      , (prel "Duration", opaqueTy (tyV tType)) -- §18.1 monotonic time difference
      , (prel "Instant", opaqueTy (tyV tType)) -- §18.1 monotonic time value
      , (prel "STM", opaqueTy (tyV (tType ~> tType))) -- §18.1.13
      , (prel "TVar", opaqueTy (tyV (tType ~> tType))) -- §18.1.13
      , (prel "Thunk", opaqueTy (tyV (tType ~> tType)))
      , (prel "Need", opaqueTy (tyV (tType ~> tType)))
      , (prel "IO", opaqueTy (tyV (tType ~> tType ~> tType)))
      , (prel "Ref", opaqueTy (tyV (tType ~> tType)))
      , -- §20 collection carriers and the §20.10 query core
        (prel "Set", opaqueTy (tyV (tType ~> tType)))
      , (prel "Map", opaqueTy (tyV (tType ~> tType ~> tType)))
      , (prel "Array", opaqueTy (tyV (tType ~> tType)))
      , (prel "Quantity", opaqueTy (tyV tType)) -- §12.1.1 reified quantities
      , (prel "ω", GlobalDef (tyV (tcon "Quantity")) (Just (VPrim "__omegaQ" [])) False)
      , (prel "QueryCore", opaqueTy (tyV (tcon "QueryMode" ~> tcon "Quantity" ~> tType ~> tType)))
      , (prel "BorrowView", opaqueTy (tyV (tcon "Region" ~> tType ~> tType))) -- §20.10.2
      , -- propositional equality (§11.4.1): (=) (@0 a) (x : a) : a -> Type
        (prel "=", opaqueTy (tyV (piI Q0 "a" tType (CVar 0 ~> CVar 1 ~> tType))))
      , (prel "refl", GlobalDef reflTy Nothing False)
      ]
    reflTy =
      tyV $
        piI Q0 "a" tType $
          piI Q0 "x" (CVar 0) $
            CApp Expl (CApp Expl (CApp Impl (tcon "=") (CVar 1)) (CVar 0)) (CVar 0)
    ctors =
      [ (prel "refl", CtorInfo (prel "=") (quoteClosedTy reflTy) [])
      ]
    datas =
      [ (prel "=", DataInfo [prel "refl"] 3)
      ]
    quoteClosedTy _ = piI Q0 "a" tType (piI Q0 "x" (CVar 0) (CApp Expl (CApp Expl (CApp Impl (tcon "=") (CVar 1)) (CVar 0)) (CVar 0)))

    tInt = tcon "Integer"
    tNat = tcon "Nat"
    tDouble = tcon "Double"
    tStr = tcon "String"
    tBool = tcon "Bool" -- defined by prelude source; fine as neutral
    tScalar = tcon "UnicodeScalar"
    tUnit = tcon "Unit"
    io e a = CApp Expl (CApp Expl (tcon "IO") e) a
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
      , prim "stringAppend" (tyV (tStr ~> tStr ~> tStr))
      , prim "showInt" (tyV (tInt ~> tStr))
      , prim "primitiveIntToString" (tyV (tInt ~> tStr))
      , prim "showDouble" (tyV (tDouble ~> tStr))
      , prim "showStringLit" (tyV (tStr ~> tStr))
      , prim "showScalar" (tyV (tScalar ~> tStr))
      , prim "intToDouble" (tyV (tInt ~> tDouble))
      , prim "natOfInt" (tyV (tInt ~> tNat)) -- internal: Nat and Integer share representation
      , prim "natToInt" (tyV (tNat ~> tInt))
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
    ]
