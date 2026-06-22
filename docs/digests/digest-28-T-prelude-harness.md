# Kappa Spec Digest: §28 Prelude + Appendix T Test Harness

## §28.1 Implicit import
Every file behaves as if it begins `import std.prelude.*` (unconditional; no disable specified). Plus unqualified constructor import of exactly: `True, False, None, Some, Ok, Err, Nil, (::), LT, EQ, GT, refl`. std.prelude is an ordinary module.

## §28.2 Core types (full list)
Unit, Void, Bool, Byte, Bytes, UnicodeScalar, Grapheme, String, Int, Nat, Integer, Float, Double, Rational, Ordering, Variant r, Syntax a, SyntaxFragment, Elab a, Option a, Result e a, List a, Array a, SizedArray n a, Set a, Map k v, Res a r, Match a r, Dec p, Eff r a, IO e a, UIO a, Fiber/FiberId/Exit/Cause/InterruptTag/InterruptCause/DefectTag/DefectInfo, Scope, Monitor, FiberRef, Promise, STM, TVar, Duration, Instant, TimeoutError, RaceResult, Regex, (=), Thunk a, Need a, Query family, Code/ClosedCode.

Canonical declarations:
```kappa
data Unit : Type = Unit
data Void : Type
data Bool : Type = True | False
expect data Nat : Type
expect data Integer : Type
type Int = Integer
type Float = Double
expect data Double : Type
expect data Rational : Type
data Ordering : Type = LT | EQ | GT
data List (a : Type) : Type =
    Nil
    (::) (head : a) (tail : List a)
data Res (a : Type) (r : Type) : Type = (:&) (value : a) (1 resource : r)
data Match (a : Type) (r : Type) : Type = Hit a | Miss r
data Dec (p : Type) : Type = Yes p | No (p -> Void)
data Exit (e : Type) (a : Type) : Type = Success a | Failure (Cause e)
data Cause (e : Type) : Type = Fail e | Interrupt InterruptCause | Defect DefectInfo | Both (Cause e) (Cause e) | Then (Cause e) (Cause e)
data (=) (@0 a : Type) (x : a) (y : a) : Type = refl : x = x
```
Option/Result constructors: Option.None, Option.Some, Result.Ok, Result.Err (data blocks not spelled out in §28.2).

## Term inventory (grouped)
pure, (>>=), (>>), map, liftA2, (<*>), (|>), (<|); not, and, or, force, (&&), (||); (==), (/=), (~=), compare, (<), (<=), (>), (>=); zero, one, add, (+), multiply, (*), negate, subDefined, subtract, (-), divDefined, divide, (/), modDefined, modulo, (%), nonZero; empty, (<|>), orElse, append, (++), foldl, foldr, foldMap, traverse, for_, sequence, sequence_, filter, filterMap; fromInteger, fromFloat, fromString, buildInterpolated, f, re, b, type; next, toQuery, ...; absurd, pathInd, subst, sym, trans, cong, unsafeAssertProof, witness, summon; floatEq; runPure; sandbox, unsandbox, finally, throwError, catchError, raise, bracket, release; fork/await/join/interrupt/... (fibers); newRef, readRef, writeRef, atomically, newTVar, ...; range, (..), (..<); listLength, listAppend, arrayEmpty/Singleton/FromList/ToList/Length/Get/Index, setEmpty/Singleton/Insert/Delete/Member/Size, mapEmpty/Singleton/Insert/Delete/Lookup/Member/Size; nowMonotonic, nanos..minutes, sleepFor, timeout, race; show, printString, printlnString, print, println.

## Key trait declarations (verbatim essentials)
```kappa
trait Show (a : Type) = show : (& value : a) -> String
trait Monoid (m : Type) = empty : m; append : m -> m -> m (+ 3 laws)
trait Foldable (t : Type -> Type) =
    foldr : forall a b. (a -> b -> b) -> b -> t a -> b
    foldl : forall a b. (b -> a -> b) -> b -> t a -> b
    foldMap : forall a m. (@_ : Monoid m) -> (a -> m) -> t a -> m
trait (Functor t, Foldable t) => Traversable t = traverse : forall f a b. (@_ : Applicative f) -> (a -> f b) -> t a -> f (t b)
trait Filterable t = filter : forall a. (a -> Bool) -> t a -> t a
trait FilterMap t = filterMap : forall a b. (a -> Option b) -> t a -> t b
trait Alternative (f : Type -> Type) = empty : f a; (<|>) : f a -> f a -> f a; let orElse = (<|>)
trait Iterator (it : Type) = Item : Type; next : (1 this : it) -> Option (item : Item, rest : it)
trait FromString (t : Type) = fromString : String -> t
trait IsEmpty t = absurd : t -> Void
trait IsContr t = center : t; contract : (x : t) -> center = x
trait IsSubsingleton t = allEqual : (x : t) -> (y : t) -> x = y
trait IsSubsingleton p => IsProp (p : Type)
trait IsSet a = pathIsProp : forall (x y : a). IsProp (x = y)
intrinsic trait RuntimeErased (t : Type)
intrinsic trait IsSubsingleton t => IsTrait (t : Type)
intrinsic trait QuantitySatisfies (capability : Quantity) (demand : Quantity)
```

## Numeric traits (§28.2.1, verbatim essentials)
```kappa
trait Zero a = zero : a
trait One a = one : a
trait Add a = add : a -> a -> a
(+) : forall a. (@_ : Add a) -> a -> a -> a ; let (+) x y = add x y
trait Mul a = multiply : a -> a -> a
(*) similarly
trait Negatable a = negate : a -> a
trait CheckedSub a =
    subDefined : (& x : a) -> (& y : a) -> Bool
    subtract : (x : a) -> (y : a) -> (@_ : subDefined x y = True) -> a
(-) : forall a. (@_ : CheckedSub a) -> (x : a) -> (y : a) -> (@_ : subDefined x y = True) -> a
trait (Eq a, Zero a) => CheckedDiv a = divDefined, divide (+ 2 laws); (/) similar with proof
trait (Eq a, Zero a) => CheckedMod a = modDefined, modulo (+ laws); (%) similar
nonZero : forall a. (@_ : Eq a) -> (@_ : Zero a) -> (& x : a) -> Bool
```
Algebraic: AdditiveMonoid, AdditiveGroup, MultiplicativeMonoid, Semiring, Ring, EuclideanSemiring, FieldLike, OrderedAdditive, OrderedSemiring (law members only).
Float/Double MUST NOT get Semiring/Ring/FieldLike; Rational MUST get FieldLike; Nat MUST NOT get Negatable/AdditiveGroup/Ring.

## Required instances
Zero/One/Add/Mul/CheckedSub/CheckedDiv/CheckedMod: Nat (no Negatable); +Negatable: Integer, Int; Rational/Float/Double: no CheckedMod. Eq: Unit Bool Byte Bytes UnicodeScalar Grapheme String Int Nat Integer Float Double Rational Ordering Duration Instant. Ord: same minus Unit, Grapheme. Show: Eq list + Grapheme. Eq Float/Double = RAW BIT equality; floatEq = IEEE numeric. FromInteger: Nat/Int/Integer/Rational/Float/Double. FromFloat: Rational/Float/Double. FromString String. Functor/Foldable/Traversable Option; +Filterable/FilterMap/Monoid List, Array. Rangeable Nat/Int/Integer/UnicodeScalar. Functor/Applicative/Monad (IO e) + MonadFinally/MonadError/MonadResource/MonadRef. Nat partial domains: subDefined x y = (y <= x); div/mod defined iff y /= zero.

## IO output (verbatim)
```kappa
expect term printString   : String -> UIO Unit
expect term printlnString : String -> UIO Unit
print   : forall a. (@_ : Show a) -> (& value : a) -> UIO Unit
let print value = printString (show value)
println : forall a. (@_ : Show a) -> (& value : a) -> UIO Unit
let println value = printlnString (show value)
```

## Short-circuit (verbatim)
```kappa
(&&) : Bool -> Thunk Bool -> Bool
let (&&) lhs rhs = if lhs then force rhs else False
(||) : Bool -> Thunk Bool -> Bool
let (||) lhs rhs = if lhs then True else force rhs
```

## Fixity table (normative minimum)
```text
(==) (~=) (/=) (<) (<=) (>) (>=) : infix 40
(&&)                             : infix right 30
(||)                             : infix right 20
(..) (..<)                       : infix 45
(::) (++)                        : infix right 50
(+) (-)                          : infix left 60
(*) (/) (%)                      : infix left 70
(-)                              : prefix 80
(:&)                             : infix right 4
(|>)                             : infix left 1
(<|)                             : infix right 0
?.                               : left-assoc 100 (reserved)
?:                               : right-assoc 2 (reserved)
```

## Appendix T harness
Directive grammar:
```text
testDirectiveLine ::= ws? '--!' ws? testDirective
inlineDiagnosticMarker ::= sourceText ws? '--!!' ws diagnosticCode (ws diagnosticCode)*
testDirective ::= directiveName [ws directiveBody]?
extensionDirectiveName ::= 'x-' ident ('.' ident)*
```
Config: `mode analyze|check|compile|run`; `packageMode|scriptMode`; `backend <p>`; `entry <qualifiedName>`; `runArgs <str>...`; `stdinFile <path>`; `dumpFormat json|sexpr`; `requires backend <p>|mode package|mode script|capability <name>`. Defaults: mode check, packageMode, json. Unmet requires → unsupported.

Diagnostic assertions: `assertNoErrors`, `assertNoWarnings`, `assertErrorCount n`, `assertWarningCount n`, `assertDiagnostic <sev> <code>`, `assertDiagnosticNext <sev> <code>` (.kp only, next source line), `assertDiagnosticAt <path> <sev> <code> <line> [<col>]`, `assertDiagnosticMatch <regex>`, `assertDiagnosticFamily <sev> <family>`, `assertDiagnosticPayload ...`, `assertDiagnosticLabel/Related <sev> <code-or-family> <role>`, fix assertions, `assertDiagnosticExplainExists <code>`. Inline `--!! E001` = same-line assertDiagnosticNext. Code-vs-family: `kappa.` prefix = family.

Type/shape: `assertType <name> <typeExpr>` (definitional equality); `assertDeclKinds <kindList>` (kinds: import export fixity signature let data type trait instance derive effect pattern expect).
Run: `assertStdout <str>` (exact after LF normalization), `assertStdoutContains`, `assertStderrContains`, `assertStdoutFile <path>`, `assertExitCode <n>`.
Results: pass | fail | unsupported | harnessError.

T.11 example:
```kappa
module main

choose : Bool -> Int -> Int -> Int
let choose flag left right = if flag then left else right

message : String
let message = "hello"

--! assertNoErrors
--! assertType choose Bool -> Int -> Int -> Int
--! assertType message String
--! assertDeclKinds signature, let, signature, let
```

## T.10 stable codes (subset relevant)
E_SAFE_NAV_GENERIC_AMBIGUOUS, W_SAFE_NAV_REDUNDANT_RECEIVER_PRESENT, E_QUERY_UNORDERED_PAGING, E_APPLICATION_NON_CALLABLE, E_APPLICATION_ARGUMENT_MISMATCH, E_CONSTRUCTOR_ARITY_MISMATCH, E_PATTERN_CONSTRUCTOR_ARITY_MISMATCH, E_NUMERIC_LITERAL_DOMAIN_MISMATCH, E_MODULE_ALIAS_TYPE_COLLISION, E_INDEXED_IMPOSSIBLE_REACHABLE, E_QUOTE_MALFORMED_SYNTAX, E_UNICODE_NAME_NON_NORMALIZED, E_UNICODE_VISUAL_DUPLICATE_BINDING, W_UNICODE_VISUAL_ALIAS_REFERENCE, E_GENERATED_SYNTAX_INVALID, E_CHECKPOINT_VERIFICATION_FAILED, E_ERASURE_JUSTIFICATION_MISSING, E_SEMANTIC_DECISION_FROM_TOKEN.
