# Spec-coverage report: effect self labels, borrow/flow rules, and bridge universes

Date: 2026-07-28

Status: open specification decisions

This report expands three issues found while reviewing the staged
`tests/pending-import/spec-coverage` corpus against `docs/Spec.md`. In each
case, individually reasonable rules compose into either a contradiction or a
missing formation rule. The affected tests should not be treated as portable
conformance evidence until the corresponding decision is made.

## Executive summary

| Area | Current conflict | Recommended resolution |
| --- | --- | --- |
| Top-level effect labels | Only `effect label` and `scoped effect` introduce effect-label declarations, but examples and tests use a top-level `effect E` as both interface `E` and label `E`. | Give every top-level effect declaration a canonical self label, paired with its interface declaration and exported/imported with it. |
| Borrow/flow composition | Borrow introduction, record patching, and `impossible` each have two rule sets that disagree about the same program. | Separate ownership capability from demand accounting; define record patch as a non-mutating read/rebuild operation; explicitly admit active-refinement facts in reachability proofs. |
| Bridge surface universes | Bridge surfaces are fixed at `Region -> Type`, while the normative Numpy surface contains a field quantifying over `Type` and therefore lives above `Type`. | Make `BridgeContract`, `BridgePackage`, and `BridgeBindable` universe-polymorphic over `Region -> Type u`, with a single explicit rule for the runtime carrier's own universe. |

## 1. Bare top-level effect names as effect-row labels

### 1.1 Current written rules

The declaration-kind rules in §7 say that an `effect-label` declaration is
introduced only by:

1. an explicit `effect label` declaration; or
2. the canonical self label of a `scoped effect`.

Section 9.3.1.1 repeats the second rule and says that:

```kappa
scoped effect E =
    1 op : Unit -> Unit
```

introduces both:

- a type-kind effect-interface constructor `E`; and
- an effect-label declaration `E`.

Section 18.1.15 says an ordinary top-level `effect` introduces an interface
constructor and that effect labels are separate identifiers. It again mentions
the canonical self label only for `scoped effect`.

Under those rules, this top-level declaration:

```kappa
effect Exn =
    1 raise : String -> Void
```

introduces the interface `Exn`, but not an effect label named `Exn`.
Consequently the following historical surface is not derivable:

```kappa
boom : Eff <[Exn : Exn]> Int
let boom = Exn.raise "boom"
```

The first `Exn` in the row must resolve in effect-label position, while the
second resolves in type position. `Exn.raise` also requires the receiver to
resolve as an effect label or `EffLabel` value.

### 1.2 Corpus and compatibility evidence

The compiler and existing examples historically treat the bare top-level
effect spelling as a paired interface/label group. Eighteen staged tests rely
on that behavior:

- `diag-families-1/effect-row-mismatch-missing-label.kp`
- `diag-families-2/inout-restoration-under-effect-row.kp`
- `effects-handlers/GRANULE-exception-effect-row.kp`
- `effects-handlers/effect-label-rebinding-delegation.kp`
- `effects-handlers/effect-label-static-value-delegation.kp`
- `effects-handlers/effect-op-implicit-forall-param.kp`
- `effects-handlers/effect-op-param-own-label-positive.kp`
- `effects-handlers/effect-row-entry-formation-negative.kp`
- `effects-handlers/handler-completion-return-break.kp`
- `effects-handlers/handler-resumption-escape-pending-defer-negative.kp`
- `effects-handlers/multishot-defer-cloned-per-resume.kp`
- `effects-handlers/shallow-vs-deep-reinstall.kp`
- `errors-collections/eff-carrier-try-finally.kp`
- `rows-props/eff-row-spliteff-premise.kp`
- `rows-props/eff-row-unique-labels-rejected.kp`
- `runtime-hashing/abandonment-exit-actions-eff-order.kp`
- `runtime-hashing/abortive-defer-using-lifo-order.kp`
- `runtime-hashing/continuation-boundary-do-frames.kp`

This is not merely syntactic convenience. Requiring explicit label
declarations would change:

- what an ordinary effect declaration exports;
- whether importing an effect interface also imports its usable label;
- the declaration identity selected by `E.op`;
- which label a handler eliminates; and
- interface hashes and dependency edges for existing modules.

### 1.3 Resolution choices

#### Option A: canonical self labels for all effect declarations

Every top-level:

```kappa
effect E = ...
```

would introduce a binding group containing both:

- `type E`, the interface constructor; and
- `effect-label E`, the canonical self label for that interface declaration.

This matches `scoped effect`, historical source, and the current corpus.

The label must be a declaration-site identity. It must not become a
runtime-fresh prompt on each evaluation. For top-level declarations there is
only one module-level identity.

#### Option B: require explicit labels

Every use would instead need a separate declaration, conceptually:

```kappa
effect Exn = ...
effect label exn : Exn

boom : Eff <[exn : Exn]> Int
let boom = exn.raise "boom"
```

This follows the current literal wording but requires rewriting the Spec's
examples, existing conformance tests, the staged corpus, and likely user code.
It also needs a rule for whether an effect declaration exports any convenient
default label.

#### Option C: contextual fallback from interface to label

The resolver could reinterpret a top-level interface name as an implicit label
only when label lookup otherwise fails. This avoids adding a declaration but
creates a context-sensitive synthetic identity, complicates imports and
shadowing, and disagrees with the binding-group model.

### 1.4 Recommendation

Adopt Option A.

The Spec should add the following rules:

1. Every effect declaration introduces a canonical self label of the same
   spelling in declaration kind `effect-label`.
2. The interface and self label form one paired declaration group, like the
   paired type/constructor facets of a same-spelling data family.
3. Exporting or importing the unqualified effect spelling selects both facets
   unless a kind-qualified selector says otherwise.
4. `type E` selects the interface facet; `effectLabel E` selects the label
   facet.
5. `E.op` in ordinary direct-operation syntax selects the canonical self-label
   facet and the operation declared by the paired interface.
6. The self label has stable declaration-site identity and is not dynamically
   generative.
7. Explicit additional labels remain supported and may target the same
   interface.

With those rules, the eighteen tests are structurally valid. Their remaining
individual failures can then be judged independently.

## 2. Borrow and flow-sensitive rule conflicts

This area contains three distinct conflicts. They share a common pattern:
high-level semantic rules require information that a narrower acceptance rule
does not explicitly admit.

### 2.1 Borrow introduction and restored linear obligations

#### Conflicting clauses

Section 12.2.3 says that when a quantity-`1` root is supplied to a borrowed
parameter:

- the quantity-`1` obligation is suspended for the call; and
- the obligation is restored when the call returns.

Section 12.2.5 says:

- a borrowed demand is runtime-relevant;
- it is non-consuming; and
- it discharges the interval usage obligation of a borrowed binding.

For:

```kappa
peek : (& x : A) -> Int

f : (1 x : A) -> Int
let f x = peek x
```

two readings are possible.

**Consumption reading:** the call merely borrows `x`. After it returns, the
owned quantity-`1` obligation is restored and must still be consumed. `f`
therefore drops `x` and is rejected.

**Demand reading:** the borrowed call is a runtime-relevant demand of `x`, so
it satisfies the `[1,1]` lower bound even though ownership capability is
restored. `f` is accepted.

The test
`functions-quantities/borrow-intro-restores-linear-obligation.kp` chooses the
consumption reading. The compiler chooses the demand reading.

#### Recommendation

Separate two state components:

1. **ownership capability**, which is suspended and restored; and
2. **interval demand accounting**, which records runtime-relevant demand.

A temporary borrow should restore ownership capability without erasing the
fact that the root was demanded. Under the Spec's existing definition of a
positive lower bound as a must-*demand* obligation, the borrowed call should
discharge that lower bound.

If the language instead intends exactly-once *consumption*, it needs a separate
consumption obligation rather than overloading interval demand.

Recommended normative sentence:

> Restoring a quantity-`1` root after a temporary borrow restores the right and
> obligation to avoid a second consuming use; it does not erase the
> runtime-relevant demand already recorded for positive-lower-bound checking.

Under this recommendation,
`borrow-intro-restores-linear-obligation.kp` should be rewritten as a positive
test.

### 2.2 Record patching an unrestricted root under a live shared borrow

#### Conflicting clauses

The record-patch rules say that:

- the scrutinee is evaluated exactly once;
- right-hand sides are evaluated into temporaries;
- omitted fields are obtained by projections; and
- a fresh record is assembled by ordinary reconstruction.

That model is a non-mutating read/rebuild operation. For an unrestricted root,
projecting fields is an ordinary read and should coexist with a live shared
borrow.

Other wording describes evaluating the patch scrutinee and reconstructing the
whole record. An implementation can interpret that as consuming the source
record and reject any patch while a borrow of the source is live.

The disagreement is exercised by:

`borrows-places/record-patch-unrestricted-root-under-live-borrow.kp`.

#### Recommendation

Specify patching independently of in-place mutation:

1. A record patch never mutates the source record.
2. For an `omega` root, obtaining omitted fields is a non-consuming read.
3. A live shared borrow of the source does not conflict with construction of a
   patched copy.
4. Ordinary quantity rules still reject copying linear or otherwise
   non-copyable omitted fields.
5. Projection-section write-footprint checks concern conflicts among updates
   used to construct the new record; they do not turn the source read into a
   mutation.
6. A patch of a quantity-`1` source may consume that source when reconstruction
   actually transfers its fields; this is separate from the unrestricted
   case.

Under these rules, the unrestricted-root test is valid and its current
rejection is a compiler failure.

### 2.3 `impossible` and active refinement facts

#### Conflicting clauses

Sections 17.1.4 and 17.1.5 say `impossible` is accepted *only if*
unreachability follows from:

- definitional equality;
- family-argument unification;
- structural inhabitance;
- and the portable arithmetic/proof fragment.

The list does not explicitly name active flow-refinement facts.

Elsewhere:

- §30.2.2.11 requires every `impossible` check to run with an active
  refinement context;
- §31.1.2 makes definitional equality and normalization relative to that
  context;
- the context proves `HasCtor`, `LacksCtor`, and boolean facts; and
- a contradictory `HasCtor`/`LacksCtor` context is explicitly unreachable.

The following tests rely on those facts:

- `lambdas-implicits-flow/contradictory-and-evidence-unreachable.kp`
- `lambdas-implicits-flow/else-narrowing-impossible.kp`
- `lambdas-implicits-flow/gadt-ground-index-else-unreachable.kp`
- `patterns-active/impossible-ignores-is-evidence.kp`

A strict reading of §17 rejects them because flow facts are absent from the
closed list. A compositional reading accepts them because refinement-aware
definitional equality includes those facts.

#### Recommendation

Make the compositional reading explicit.

Replace the §17 acceptance list with wording equivalent to:

> `impossible` is accepted when the branch is unreachable under the current
> active refinement context, as established by refinement-aware definitional
> equality and normalization (§31.1.2), family-argument unification,
> structural inhabitance (§30.2.7), or the portable arithmetic/proof fragment
> (§15.8).

Also explicitly admit:

- `HasCtor`/`LacksCtor` contradictions;
- a residual branch whose visible constructors are all excluded;
- boolean true/false facts introduced by preceding control flow; and
- constructor-forced index equalities transported through stable aliases.

The existing restriction against proving arbitrary facts from a contradictory
context must remain: contradiction may justify the branch's unreachability,
not arbitrary equality in reachable code.

## 3. Bridge surface universe inconsistency

### 3.1 Current declarations

Section 26.1 specifies:

```kappa
A bridge surface has kind Region -> Type

expect data BridgeContract (@0 surface : Region -> Type) : Type
expect data BridgePackage  (@0 surface : Region -> Type) : Type

trait BridgeBindable (surface : Region -> Type) =
    bridgeContract : BridgeContract surface
```

The same chapter gives a normative Numpy-style surface:

```kappa
type Numpy (r : Region) : Type =
    (opaque NDArray : Type -> Nat -> Type,
     array :
        forall (@0 a : Type).
        (@_ : DynamicType a) ->
        List a -> IO PyError (exists (n : Nat). this.NDArray a n))
```

### 3.2 Why the example is not `Region -> Type`

Under predicative universe formation, `Type` is itself classified above
`Type`. A record field whose type quantifies over:

```kappa
forall (@0 a : Type). ...
```

has a type in at least `Type1` unless the Spec supplies a special
universe-irrelevance rule for this erased quantifier.

Consequently the record containing `array` also inhabits at least `Type1`.
The declared annotation:

```kappa
type Numpy (r : Region) : Type
```

is not justified, and `Numpy` cannot instantiate a parameter fixed at:

```kappa
Region -> Type
```

The staged test
`ffi-bridges/polymorphic-surface-member-numpy-shape.kp` exposes this mismatch.

This is a surface-formation problem, not a runtime bridge-representation
problem. Erasing the `surface` parameter from `BridgeContract` at runtime does
not by itself make the source type well-kinded.

### 3.3 Resolution choices

#### Option A: universe-polymorphic bridge surfaces

Generalize the complete API coherently:

```kappa
BridgeContract.{u} :
    (parametric 0 surface : Region -> Type u) -> Type ...

BridgePackage.{u} :
    (parametric 0 surface : Region -> Type u) -> Type ...

BridgeBindable.{u} (parametric 0 surface : Region -> Type u)
```

The Spec must choose and state the result universe of `BridgeContract` and
`BridgePackage`. If their erased surface parameter is intended not to raise
the runtime carrier's universe, that exception must be a general universe
formation rule, not an unstated bridge special case.

#### Option B: make erased `forall` universe-irrelevant

Declare that a field's erased quantification over `Type u` does not raise the
classifier of the containing function or record.

This is a far-reaching type-theory change. It affects much more than bridges,
including records, existential packages, trait members, static objects, and
representation proofs. It requires a soundness argument and corresponding
changes throughout the universe rules.

#### Option C: restrict bridge surfaces to `Type`

Keep `Region -> Type`, but rewrite Numpy and similar surfaces to avoid
quantification over arbitrary `Type`. This would require monomorphized members,
a `Dyn`-based boundary, or a small-universe restriction.

This loses the polymorphic typed bridge surface the chapter is trying to
specify.

### 3.4 Recommendation

Adopt Option A.

Bridge descriptions are compile-time indices over runtime contracts, so
universe polymorphism is the narrowest change and preserves the intended typed
surface.

The revision must update all of:

- `BridgeContract`;
- `BridgePackage`;
- `BridgeBindable`;
- `BridgeHandle.bindModuleWith`;
- `BridgeHandle.bindModuleOwnedWith`;
- `bindModule`;
- `bindModuleOwned`;
- `bridgePackageValue`;
- contract derivation and interface identity; and
- examples and required `std.bridge` declarations.

The interface identity for a contract must include the instantiated universe
schema where ordinary universe identity rules require it. Runtime contract
layout may remain universe-erased.

After that change, the Numpy surface should be annotated at its inferred
universe, and `polymorphic-surface-member-numpy-shape.kp` can be rewritten as a
positive formation test rather than a SPEC-ISSUE.

## 4. Proposed resolution order

1. Add top-level canonical effect self labels. This mostly codifies historical
   behavior and unblocks the largest number of tests.
2. Clarify that active refinement facts participate in `impossible`
   reachability. The necessary semantic machinery is already specified.
3. Separate borrow capability restoration from demand accounting, then settle
   unrestricted record-patch reads.
4. Introduce the bridge universe schema and update the full bridge telescope
   atomically; partial generalization will only move the mismatch to another
   member.

## 5. Conformance criteria after resolution

The issues are resolved when portable tests can establish all of the following
without implementation-private names:

- a top-level effect's same-spelling label survives direct use, import,
  qualification, re-export, rebinding, and interface serialization;
- explicit secondary labels for one interface remain distinct;
- temporary borrowing has one specified effect on both capability state and
  lower-bound demand accounting;
- patching an unrestricted record under a live shared borrow has one specified
  result independent of lowering strategy;
- every active-refinement fact named by the Spec can justify `impossible`
  exactly when its branch is unreachable;
- a `Region -> Type1` bridge surface can form a contract and package through
  the standard API; and
- bridge contract runtime layout remains stable and does not depend on a
  hidden compiler constructor.
