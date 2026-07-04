# Kappa `lazy data` Semantics Note

## Purpose

This note explains the proposed `lazy data` semantics for Kappa.

The goal is to add Haskell-like lazy datatype ergonomics locally, without making function arrows lazy, without adding strictness parameters to higher-order abstractions, and without rewriting constructor fields to `Thunk` or `Need`.

The central idea is:

```text
ordinary data  => ordinary strict constructor behavior
lazy data      => selected datatype has enterable-head semantics
```

A `lazy data` declaration is opt-in per data family.

## Surface form

Example:

```kappa
lazy data List (a : Type) : Type =
    Nil
    Cons a (List a)

lazy data StrictHeadList (a : Type) : Type =
    Nil
    Cons (!head : a) (tail : StrictHeadList a)
```

The `lazy` modifier belongs to the data family. It does not modify the function arrow and does not make every type in the language lazy.

The field strictness marker is `!`. In a `lazy data` constructor, an unmarked field is stored without WHNF-normalization; a `!` field is WHNF-normalized before storage.

## Hidden representation

For a declaration:

```kappa
lazy data T Δ : Type =
    C1 fields1...
    C2 fields2...
```

Kappa behaves as if there were a hidden head representation:

```text
T# Δ =
    C1# fields1...
    C2# fields2...
```

A source value of type `T Δ` is an enterable runtime cell producing exactly one `T# Δ` head.

Conceptually:

```text
T Δ = Enterable (T# Δ)
```

But `T#`, `C1#`, `C2#`, and `Enterable` are not source-visible declarations. They are explanatory names for the runtime and core behavior.

A lazy data value is in one of two states:

```text
evaluated head : T# Δ
delayed head   : memoized computation producing T# Δ
```

The delayed state produces a head representation `T# Δ`, not another source value `T Δ`. This avoids recursive chains like:

```text
Delay : Need (T Δ) -> T Δ
```

The intended representation is instead closer to:

```text
Delay : Need (T# Δ) -> T Δ
```

or, more accurately:

```text
T Δ = enterable cell producing T# Δ
```

## Entering

Each lazy data family has a hidden enter operation:

```text
enter_T : T Δ -> T# Δ
```

Entering performs one outer representation check.

If the cell already stores a head, entering returns that head.

If the cell stores a delayed head computation, entering evaluates that computation, updates the cell with the resulting head when sharing is used, and returns that head.

The delayed computation may do internal work before producing the head. It may call functions, allocate, enter other lazy values, or pattern match. The important invariant is that the current cell is updated with one constructor head, not with another delayed `T Δ` value.

## Pattern matching

Pattern matching on lazy data implicitly enters the scrutinee.

For example:

```kappa
match xs
case Nil -> e_nil
case Cons h t -> e_cons
```

behaves as if it first performed:

```text
enter_List xs
```

and then matched on the resulting hidden `List#` head.

The source-visible constructors are still only:

```kappa
Nil
Cons
```

There is no source pattern for the hidden delayed state. Exhaustiveness checking ignores the delayed state because it is not a constructor.

## Constructor types

Source constructors keep their ordinary source types.

For:

```kappa
lazy data List (a : Type) : Type =
    Nil
    Cons a (List a)
```

source constructor types are:

```kappa
Nil  : List a
Cons : a -> List a -> List a
```

They are not rewritten to:

```kappa
Cons : Need a -> Need (List a) -> List a
```

Fields are not wrapped in `Need`. There is no `LazyField` type.

## Constructor application and fields

Lazy data changes constructor evaluation, not field types.

When a constructor head is created for a lazy data family:

```kappa
Cons head tail
```

unmarked fields are stored without WHNF-normalization.

A strict field:

```kappa
Cons (!head : a) (tail : List a)
```

causes `head` to be WHNF-normalized before it is stored in the hidden `Cons#` head.

The `!` marker does not change the type of the field. It also does not force through explicit suspension types. For example, if a strict field has type `Need A`, the field value itself is normalized as a `Need A` value; the suspended `A` inside it is not forced merely because the field is strict.

## Why fields are not `Need`

The field itself is not the capture point.

Capture happens when the compiler forms a delayed constructor-head computation. Once a value is already available and is put into a field, the field slot simply stores that value.

So the semantic distinction is:

```text
non-strict field:
    do not WHNF-normalize the argument before storing it

strict field:
    WHNF-normalize the argument before storing it
```

not:

```text
non-strict field:
    store Need A

strict field:
    store A
```

This keeps the declared field type honest.

## `lazy expr` at lazy data types

The existing expression:

```kappa
lazy expr
```

continues to mean ordinary `Need` introduction when it synthesizes a type, or when the expected type is `Need A`.

But when `lazy expr` is checked against an expected type known to be a `lazy data` family application, it may elaborate to a hidden delayed head cell of that data type.

Example:

```kappa
ones : List Int
let ones =
    Cons 1 (lazy ones)
```

Here the expected type of `lazy ones` is `List Int`, and `List` is known to be `lazy data`. Therefore `lazy ones` may create a delayed `List Int` cell whose delayed computation produces one `List# Int` head when entered.

This rule is expected-type-directed. Without an expected lazy-data type, `lazy expr` keeps the ordinary `Need` meaning.

## Abstract lazy data

The compiler may form a lazy-data delayed cell only when it knows the expected type is lazy-enterable.

That knowledge can come from:

```text
1. a concrete `lazy data` declaration in the current module;
2. an imported interface that records the lazy-data capability;
3. an `expect lazy data` declaration satisfied by a compatible artifact;
4. future explicit evidence, if Kappa standardizes such evidence.
```

For abstract lazy data:

```kappa
opaque lazy data Stream a : Type =
    ...
```

or:

```kappa
expect lazy data Stream (a : Type) : Type
```

an importing module may know that `Stream a` supports lazy-data delay and enter behavior even when the constructors are hidden.

The compiler must not guess this from erased type arguments at runtime.

For a type variable:

```kappa
forall (a : Type). ...
```

`lazy expr : a` is rejected unless the interface carries explicit lazy-data capability evidence for `a`.

## Metadata preservation

Lazy-data constructor behavior is constructor metadata.

It is preserved by:

```text
1. direct constructor references;
2. transparent local aliases of a constructor;
3. record/package fields that store constructor metadata;
4. projection from such fields;
5. import/export through interfaces that record the metadata.
```

It is destroyed by:

```text
1. eta-expansion;
2. ordinary lambda wrapping;
3. sealing behind a signature that omits constructor metadata;
4. conversion to a plain function type with no constructor metadata;
5. storage through a field/interface that omits metadata.
```

Example preserving metadata:

```kappa
let MkCons = Cons
let xs = MkCons 1 Nil
```

Example losing metadata:

```kappa
let MkCons h t = Cons h t
```

The second form is an ordinary function wrapper. Unless its type or metadata explicitly preserves constructor behavior, application of `MkCons` is ordinary function application.

## Quantities and positive lower bounds

A delayed lazy-data head is a delayed use boundary.

Constructing the delayed head does not demand the variables captured by the delayed computation.

Therefore:

```kappa
bad : (>=1 x : Int) -> List Int
let bad x =
    lazy Cons x Nil
```

cannot discharge the `>=1 x` obligation merely by mentioning `x` inside the delayed head. The obligation is discharged only if the delayed cell is entered sufficiently before `x` leaves scope, or if `x` is demanded independently outside the delayed computation.

This is the same basic principle as ordinary closures and suspensions: delayed uses do not count as immediate demands.

The important distinction is that these obligations attach to the delayed constructor-head computation, not to fields as such.

## Captures and borrowed values

A delayed lazy-data head may capture variables. That delayed computation is the capture point.

It must obey the ordinary closure, borrow, region, and memoization safety rules.

In particular:

```text
1. borrowed views must not escape their region;
2. anonymous regions must not be hidden inside delayed data that outlives them;
3. linear or positive-lower-bound obligations must not be silently duplicated, dropped, or hidden;
4. memoized delayed heads must not retain or duplicate state in a way the quantity and borrow rules forbid.
```

Again, the field declaration itself does not create this capture. The delayed head closure does.

## Totality and productivity

`lazy data` does not add general recursion.

A definition like:

```kappa
bad : List Int
let bad = lazy bad
```

is rejected unless a future feature gives it a productive interpretation.

Productive infinite structures require guarded/productive recursion, for example a shape like:

```kappa
ones : List Int
let ones =
    Cons 1 (lazy ones)
```

subject to Kappa's productivity checker.

The key rule is: laziness may delay observation of a constructor head, but it must not smuggle nontermination into a total language.

## No source-level blackholes

The source semantics does not need a `Blackhole` state.

A backend may use update-in-progress markers, blackholes, indirections, pointer tags, or other runtime machinery to implement sharing safely. Those are implementation details, not source-level constructors or semantic cases.

## Relationship to `Thunk` and `Need`

`Thunk A` and `Need A` remain ordinary explicit suspension types.

They are still useful for non-strict function parameters, explicit suspensions, short-circuiting APIs, and ordinary delayed computations.

`lazy data` is separate. It says that a selected data family has enterable-head semantics.

Comparison:

```text
Thunk A / Need A:
    explicit suspension type
    eliminated by `force`
    visible in source types

lazy data T:
    selected datatype representation/evaluation strategy
    eliminated by pattern matching / constructor tests / projections
    hidden delayed state is not visible in source types
```

## Summary

The aligned model is:

```text
lazy data = selected datatype has enterable head semantics
not universal laziness
not lazy arrows
not field wrappers
not recursive Delay chains
```

More explicitly:

```text
T Δ = enterable cell producing T# Δ

T# Δ = C1# fields... | C2# fields... | ...

enter_T : T Δ -> T# Δ
```

Fields remain fields of their declared types.

Unmarked fields are not WHNF-normalized when stored in a lazy data head.

`!` fields are WHNF-normalized before storage.

Pattern matching enters the scrutinee and sees only declared source constructors.

Constructor metadata preserves lazy-data behavior across direct references, transparent aliases, and interfaces that record it.

Quantities, captures, regions, and productivity remain enforced at the delayed-head closure boundary.
