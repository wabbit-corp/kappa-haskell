Yes, but split the tests into **two different suites** or the whole thing will quietly become UIP-by-compiler-bug, which is a dreadful way to invent theology.

Kappa’s spec already says the right thing: ordinary proof-like types live in `Type`, Kappa v1 does **not** assume UIP/proof irrelevance/runtime erasure for arbitrary equality types, and `IsNType` solving must be deterministic and specified, not “let the solver have a spiritual experience.”  Equality matching that requires UIP must be rejected unless `IsSet A` or `IsProp (x = y)` is available.

The counting blog is useful for **inhabitance/cardinality** tests, especially products, sums, finite ADTs, and optional finite-function strengthening. It explicitly counts `Void ~ 0`, `() ~ 1`, `Bool ~ 2`, products by multiplication, sums by addition, and finite functions by exponentiation. ([Wabbit][1]) But its later polymorphic/Yoneda examples rely on parametricity, and the author notes that some witnesses rely on parametricity/purity rather than ordinary definable code. ([Wabbit][1]) So use those only for optional strengthening, not conformance, unless Kappa standardizes the required parametricity theorem.

## 1. Test harness shape

I’d use pseudo-directives like this, mapped onto whatever harness you actually have:

```text
-- %summary SourceReachability T == Empty | Subsingleton | Contractible | Finite n | Unknown
-- %summary Completion T == ...
-- %enumerate Completion T == [term1, term2, ...] | NotEnumerable
-- %synth Goal == pass | fail
-- %check == pass
-- %check-fails CODE
```

Keep **inhabitance queries** separate from **source-level evidence synthesis**. The spec says inhabitance summaries can use proof-classification evidence, but using evidence for a summary does not create new source-level evidence. Tiny distinction, large compiler bug if ignored.

## 2. Shared fixtures

```kappa
data Zero : Type

data One : Type =
    One

data Two : Type =
    TwoA
    TwoB

data Three : Type =
    ThreeA
    ThreeB
    ThreeC

data KMaybe (a : Type) : Type =
    KNone
    KSome a

data KEither (a : Type) (b : Type) : Type =
    KLeft a
    KRight b

data SmallFoo : Type =
    Foo0
    Foo1 Bool
    Foo2 Unit

data Switch : Type =
    Off
    On

data OnlyOn (s : Switch) : Type =
    MkOnlyOn : OnlyOn On
```

## 3. Required inhabitance-summary tests

These should be mandatory conformance tests because the spec requires exact summaries for the normalized first-order algebraic fragment: `Void`, `Unit`, `Bool`, finite nullary constructors, closed products/records, closed sums/variants, and GADT constructor-result refinement.

```text
-- Base
%summary SourceReachability Void == Empty
%summary SourceReachability Zero == Empty
%summary SourceReachability Unit == Contractible
%summary SourceReachability One == Contractible
%summary SourceReachability Bool == Finite 2
%summary SourceReachability Two == Finite 2
%summary SourceReachability Three == Finite 3

-- Products / records
%summary SourceReachability (b : Bool, u : Unit) == Finite 2
%summary SourceReachability (x : Bool, y : Bool) == Finite 4
%summary SourceReachability (v : Void, b : Bool) == Empty
%summary SourceReachability (o : One, u : Unit) == Contractible

-- Sums / ADTs with payloads
%summary SourceReachability (KMaybe Void) == Contractible
%summary SourceReachability (KMaybe Unit) == Finite 2
%summary SourceReachability (KMaybe Bool) == Finite 3

%summary SourceReachability (KEither Unit Bool) == Finite 3
%summary SourceReachability (KEither Bool Bool) == Finite 4
%summary SourceReachability SmallFoo == Finite 4

-- GADT-style family argument refinement
%summary SourceReachability (OnlyOn On) == Contractible
%summary SourceReachability (OnlyOn Off) == Empty
```

That gives you the simple algebraic tests from the blog without dragging in rank-1 polymorphism, function extensionality, or a swamp monster wearing a theorem-prover hat.

## 4. Completion/enumeration tests

Finite enumeration must be deterministic, but enumeration must not make invalid source valid. Hole suggestions are diagnostic/tooling aids only; a `Contractible` or `Finite n` summary does not automatically solve a hole.

```kappa
holeUnit : Unit
let holeUnit = ?u
-- %check-fails E_HOLE_UNSOLVED
-- %hole ?u.summary == Contractible
-- %hole ?u.candidates == [()]

holeBool : Bool
let holeBool = ?b
-- %check-fails E_HOLE_UNSOLVED
-- %hole ?b.summary == Finite 2
-- %hole ?b.candidates == [False, True]

holeMaybeBool : KMaybe Bool
let holeMaybeBool = ?m
-- %check-fails E_HOLE_UNSOLVED
-- %hole ?m.summary == Finite 3
-- %hole ?m.candidates == [KNone, KSome False, KSome True]
```

Also test constructor order:

```text
%enumerate Completion Three == [ThreeA, ThreeB, ThreeC]
%enumerate Completion Two == [TwoA, TwoB]
```

And threshold behavior:

```text
-- For a product larger than the configured finite-enumeration threshold:
%summary Completion BigFinite == Finite N
%enumerate Completion BigFinite == NotEnumerable
```

The exact `N` depends on your fixture; the important bit is that summary and enumeration are not the same query, because naturally humans would conflate them and then blame computers.

## 5. Source reachability and `impossible`

Only exact `Empty` should justify `impossible`, `case impossible`, or omitting unreachable branches. `Subsingleton`, `Contractible`, and `Finite n` are not “permission to pretend the branch went away.”

```kappa
onlyOnOffImpossible : OnlyOn Off -> Unit
let onlyOnOffImpossible x =
    match x
    case MkOnlyOn -> impossible
-- %check == pass
-- because OnlyOn Off is Empty by family-argument refinement
```

Negative test:

```kappa
badImpossibleBool : Bool -> Unit
let badImpossibleBool b =
    match b
    case False -> impossible
    case True  -> ()
-- %check-fails E_INDEXED_IMPOSSIBLE_REACHABLE
```

Negative test for “opaque is not empty”:

```kappa
-- Module A
opaque data HiddenTwo : Type =
    HiddenA
    HiddenB

-- Module B, without clarify:
-- %summary SourceReachability HiddenTwo == Unknown
-- not Empty, not Finite 0, not Contractible
```

This catches the especially rancid bug where hidden constructors are treated as no constructors. Opaque does not mean void. It means “none of your business.”

## 6. Equality inhabitance tests, the UIP tripwire

These are the most important tests.

The spec says equality summaries behave conservatively: for `x = y`, no-confusion can prove `Empty`; `IsProp (x = y)` or `IsSet A` can give `Subsingleton`; `x` definitionally equal to `y` plus that evidence gives `Contractible`; but `x = x` with no such evidence is `Unknown`.

```kappa
eqSelfUnknown :
    forall (@0 A : Type) (@0 x : A).
    Unit
let eqSelfUnknown = ()
-- %summary Completion (x = x) in context [A : Type, x : A] == Unknown
```

This is the “do not smuggle UIP in through inhabitance” test.

```kappa
eqSelfWithSet :
    forall (@0 A : Type) (@_ : IsSet A) (@0 x : A).
    Unit
let eqSelfWithSet = ()
-- %summary Completion (x = x) in context [A : Type, IsSet A, x : A] == Contractible
-- %enumerate Completion (x = x) == [refl]
```

No-confusion:

```text
%summary SourceReachability (False = True) == Empty
%summary SourceReachability (TwoA = TwoB) == Empty
```

Nominal type inequality must **not** imply empty equality of types:

```text
%summary SourceReachability (Unit = Bool) == Unknown
```

That last one matters because the spec explicitly refuses to conclude that two inhabitants of `Type` are unequal merely because their normalized heads are different nominal declarations, preserving room for future univalence/cubical paths.

## 7. Equality matching tests

Accepted path induction:

```kappa
transportByMatch :
    forall (@0 A : Type) (@0 P : A -> Type)
           (@0 x : A) (@0 y : A).
    (p : x = y) -> P x -> P y

let transportByMatch p px =
    match p
    case refl -> px
-- %check == pass
```

Rejected UIP/K:

```kappa
badK :
    forall (@0 A : Type) (@0 x : A).
    (p : x = x) -> p = refl

let badK p =
    match p
    case refl -> refl
-- %check-fails E_EQUALITY_MATCH_REQUIRES_ISSET
```

Accepted only with h-level evidence:

```kappa
goodKWithSet :
    forall (@0 A : Type) (@_ : IsSet A) (@0 x : A).
    (p : x = x) -> p = refl

let goodKWithSet p =
    match p
    case refl -> refl
-- %check == pass
```

That pair is the anti-UIP smoke alarm. If `badK` passes in portable v1, the compiler has become Coq with an unlicensed axiom in the basement.

## 8. H-level synthesis tests

These are source-level evidence tests, not just summary tests.

### Base h-levels

Assuming you add compiler-owned intrinsic rules for the usual prelude types:

```text
%synth IsEmpty Void == pass
%synth IsEmpty Zero == pass

%synth IsContr Unit == pass
%synth IsContr One == pass
%synth IsContr Void == fail
%synth IsContr Bool == fail

%synth IsSubsingleton Void == pass
%synth IsSubsingleton Unit == pass
%synth IsSubsingleton Bool == fail
%synth IsSubsingleton Two == fail

%synth IsProp Void == pass
%synth IsProp Unit == pass
%synth IsProp Bool == fail
%synth IsProp Two == fail

%synth IsSet Void == pass
%synth IsSet Unit == pass
%synth IsSet Bool == pass
%synth IsSet Two == pass
%synth IsSet Three == pass

%synth IsGroupoid Bool == pass
%synth IsGroupoid Three == pass
```

The failures are as important as the passes. `Bool` is finite and discrete, not a proposition. Apparently “two” still means “not at most one,” despite several thousand years of human committees.

### `IsNType`

```text
%synth IsNType 0 Unit == pass
%synth IsNType 0 Bool == fail

%synth IsNType 1 Void == pass
%synth IsNType 1 Unit == pass
%synth IsNType 1 Bool == fail

%synth IsNType 2 Bool == pass
%synth IsNType 2 Three == pass

%synth IsNType 3 Bool == pass
%synth IsNType 3 Three == pass
```

And the symbolic case:

```kappa
badArbitraryN :
    forall (n : Nat).
    IsNType n Bool

let badArbitraryN =
    summon
-- %check-fails kappa.implicit.unsolved
```

Reason: arbitrary `IsNType n A` must not be solved by unbounded proof search. The spec explicitly requires deterministic, terminating, specified intrinsic rules for compiler-owned h-level solving.

## 9. Trait evidence tests

The spec makes fully applied trait evidence types subsingletons through `IsTrait`, but `IsTrait T` does **not** imply `IsProp T` or `RuntimeErased T`; method-bearing traits are especially not automatically erased.

```text
%synth IsSubsingleton (Eq Bool) == pass
%synth IsProp (Eq Bool) == fail
%synth RuntimeErased (Eq Bool) == fail
```

For intrinsic proof-only traits:

```text
%synth IsProp (QuantitySatisfies 1 1) == pass
%synth RuntimeErased (QuantitySatisfies 1 1) == pass
%synth QuantitySatisfies 1 1 == pass

%synth IsProp (QuantitySatisfies 0 1) == pass
%synth RuntimeErased (QuantitySatisfies 0 1) == pass
%synth QuantitySatisfies 0 1 == fail
%summary SourceReachability (QuantitySatisfies 0 1) == Empty
```

That catches the difference between “this is a proposition” and “this proposition is true,” a distinction humans keep rediscovering and then naming departments after.

## 10. `IsSubsingleton` is not inhabitance

```kappa
badSubsingletonGivesValue :
    forall (@0 A : Type).
    IsSubsingleton A =>
    A

let badSubsingletonGivesValue =
    ?x
-- %check-fails E_HOLE_UNSOLVED
-- %hole ?x.summary == Subsingleton
```

But with an explicit inhabitant:

```kappa
subsingletonWithWitness :
    forall (@0 A : Type).
    IsSubsingleton A =>
    (x : A) ->
    A

let subsingletonWithWitness x =
    x
-- %check == pass
-- %summary Completion A in context [x : A, IsSubsingleton A] == Contractible
```

The inhabitance-summary rule permits `Contractible` when an explicit inhabitant exists alongside `IsSubsingleton`; it must not manufacture the inhabitant out of uniqueness alone.

## 11. Optional finite-function/cardinality strengthening

These should **not** be mandatory conformance tests, because your required fragment says unsupported shapes such as function types are `Unknown`; optional strengthening may summarize nondependent finite functions as `Finite (|B| ^ |A|)` if bounded and sound.  The blog’s corresponding examples are `Bool -> Bool ~ 4`, `Maybe Bool -> Bool ~ 8`, `Bool -> Maybe Bool ~ 9`, and `(Bool, Bool, Bool) -> () ~ 1`. ([Wabbit][1])

Baseline portable mode:

```text
%summary Completion (Bool -> Bool) == Unknown
%summary Completion (KMaybe Bool -> Bool) == Unknown
```

With `finite-function-inhabitance` or whatever you call the explicit optional strengthening mode:

```text
%summary Completion (Bool -> Bool) == Finite 4
%summary Completion (KMaybe Bool -> Bool) == Finite 8
%summary Completion (Bool -> KMaybe Bool) == Finite 9
%summary Completion ((b1 : Bool, b2 : Bool, b3 : Bool) -> Unit) == Contractible
```

But do **not** let that imply function h-levels unless you also specify function extensionality or a finite-function representation whose equality is source-level:

```text
-- Even with finite-function inhabitance enabled:
%synth IsSet (Bool -> Bool) == fail
```

This prevents the classic “we counted the functions, therefore equality of functions is fine” faceplant. Counting inhabitants is not the same as proving paths between functions are propositions.

## 12. Runtime-shape versus source-inhabitance tests

Proof erasure must not make impossible values appear inhabited. The spec says erased impossible proof fields still have to be source-inhabited before they can be ignored for runtime-shape multiplication.

```kappa
data BadErasedProof : Type =
    MkBadErasedProof (@0 p : False = True)

-- %summary SourceReachability BadErasedProof == Empty
-- %summary RuntimeShape BadErasedProof == Empty
```

```kappa
data UnknownErasedProof (@0 A : Type) (@0 x : A) : Type =
    MkUnknownErasedProof (@0 p : x = x)

-- In context [A : Type, x : A], without IsSet A:
-- %summary SourceReachability (UnknownErasedProof A x) == Unknown
-- %summary RuntimeShape (UnknownErasedProof A x) == Unknown
```

```kappa
data GoodErasedProof : Type =
    MkGoodErasedProof (@0 p : True = True)

-- assuming Bool has IsSet:
-- %summary SourceReachability GoodErasedProof == Contractible
-- %summary RuntimeShape GoodErasedProof == Contractible
```

## 13. What should be inferred automatically?

**Yes, automatically infer**:

* Required inhabitance summaries for first-order algebraic KCore: base types, finite nullary ADTs, closed products/records, closed sums/variants, and GADT family-argument refinement.
* Equality emptiness via supported no-confusion: distinct visible constructors, primitive distinct literals, and constructor family-argument contradictions.
* `IsSubsingleton (Tr args)` for trait evidence types via `IsTrait`.
* `RuntimeErased P` when `IsProp P` is available.
* Base/structural h-level facts only when you write down the compiler-owned intrinsic rules.

**Do not infer by default**:

* `IsProp (x = y)` for arbitrary `A`.
* `IsSet A` for arbitrary `A`.
* UIP/K.
* Function extensionality.
* `IsProp (Eq A)` just because `Eq A` is trait evidence.
* `RuntimeErased T` from `IsSubsingleton T`.
* Source-level evidence from an inhabitance-summary query unless a separate, specified evidence-construction rule exists.
* Anything from `RuntimeShape`/`Optimization` summaries back into source acceptance.

The core red-team invariant is this:

```text
x = x for x : A is Unknown without IsSet A or IsProp (x = x).
badK must fail.
goodKWithSet may pass.
```

Everything else is bookkeeping. Annoying bookkeeping, granted, but that is the sacred compost from which sound compilers occasionally grow.

[1]: https://wabbit.blog/posts/fp-counting-type-inhabitants.html "@wabbit.one - Counting type inhabitants"
