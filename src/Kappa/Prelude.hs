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
      , (prel "Thunk", opaqueTy (tyV (tType ~> tType)))
      , (prel "Need", opaqueTy (tyV (tType ~> tType)))
      , (prel "IO", opaqueTy (tyV (tType ~> tType ~> tType)))
      , (prel "Ref", opaqueTy (tyV (tType ~> tType)))
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
      , prim "printString" (tyV (forallE (tStr ~> io (CVar 1) tUnit)))
      , prim "printlnString" (tyV (forallE (tStr ~> io (CVar 1) tUnit)))
      , prim "ioPure" (tyV (forallEA (CVar 0 ~> io (CVar 2) (CVar 1))))
      , prim "throwIO" (tyV (forallEA (CVar 1 ~> io (CVar 2) (CVar 1))))
      , prim "catchIO" (tyV (forallEA (io (CVar 1) (CVar 0) ~> (CVar 2 ~> io (CVar 3) (CVar 2)) ~> io (CVar 3) (CVar 2))))
      , prim "finallyIO" (tyV (forallEA (io (CVar 1) (CVar 0) ~> io (CVar 2) tUnit ~> io (CVar 3) (CVar 2))))
      , prim "__runIO" (tyV (forallEA (io (CVar 1) (CVar 0) ~> CVar 1)))
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
    , "trait Zero (a : Type) ="
    , "    zero : a"
    , ""
    , "trait One (a : Type) ="
    , "    one : a"
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
    , "pure : forall (e : Type) (a : Type). a -> IO e a"
    , "let pure x = ioPure x"
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
    ]
