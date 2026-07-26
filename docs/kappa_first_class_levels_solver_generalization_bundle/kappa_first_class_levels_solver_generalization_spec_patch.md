# Kappa first-class level terms, principled generalization, certified level solving, recursive schemas, and monotonicity patch

**Patch base:** `Spec(100).md`

This patch closes the remaining gaps in Kappa's universe and `TypeLevel` design without introducing another privileged
mini-language for level expressions.

The patch makes these decisions normative:

```text
* any stable total term of type TypeLevel may index Type;
* standard level operations are decomposed by the solver, while opaque or neutral level terms become rigid atoms;
* expression lifting and `do` elaboration occur before level-index admissibility is checked;
* mutable current-value facets are not level-stable in v1, but immutable snapshots are;
* declaration generalization is parametric abstraction at semantic declaration boundaries;
* declaration generalization never commutes a universal quantifier through a type constructor;
* quantifier interchange requires ordinary first-class evidence;
* unbounded parametric packages use ordinary record, constructor, projection, and pattern rules only;
* generated declaration-universe constraints are ordinary erased proof binders;
* level constructor normalization, rigid entailment, and metavariable inference are separate normative layers;
* rigid level entailment is exact paired QF Presburger entailment;
* KCoreText arithmetic replay is complete for the rigid portable level theory;
* portable principal inference is guaranteed only for a precisely specified assignable fragment;
* recursive declaration-schema calls are same-or-lower in v1 and non-identity instantiations are explicit;
* first-class TypeLevel recursion remains ordinary dependent recursion;
* lift proof-object identity is excluded from semantic identity;
* schemaLift insertion is direct, fully saturated, and expected-type-directed;
* declaration schemas may be eta-reified into bounded first-class level functions only from an expected type;
* eta-reification never supplies an omitted explicit term-level TypeLevel argument;
* user monotonicity is ordinary `Monotone` trait evidence discovered by normal implicit resolution;
* reverse universe or schema conversions are independent checked lifts, never implicit "inverses".
```

The attached implementation audit found that the working tree already has three distinct mechanisms: a deterministic
AC/ACI constructor normalizer, exact paired-Presburger rigid entailment, and a separate incomplete lower-bound
metavariable solver. It also found that the existing KCoreText structural proof language is not complete for the rigid
solver. This patch makes that separation explicit instead of continuing the venerable compiler tradition of naming
three different things "normalization" and hoping they merge out of embarrassment.

---

## 1. Diagnostic additions and amendments

### 1.1 Portable aliases

Add to §3.1.4:

```text
E_UNIVERSE_INFERENCE_REQUIRES_ANNOTATION
E_UNIVERSE_RECURSIVE_SCHEMA_INCREASE
E_UNIVERSE_RECURSIVE_SCHEMA_IMPLICIT
E_GENERALIZATION_PARAMETRIC_ESCAPE
```

Add these meanings:

```text
* `E_UNIVERSE_INFERENCE_REQUIRES_ANNOTATION` is emitted when a minimizable universe metavariable remains outside the
  portable principal-inference fragment and cannot legally be generalized. The diagnostic does not claim that no
  semantic principal solution exists; it requires an explicit result universe, declaration schema, or other local
  annotation.

* `E_UNIVERSE_RECURSIVE_SCHEMA_INCREASE` is emitted when a recursive call inside one declaration SCC explicitly
  instantiates a declaration-universe parameter at a level not proved less than or equal to the current SCC instance.

* `E_UNIVERSE_RECURSIVE_SCHEMA_IMPLICIT` is emitted when a recursive call attempts a non-identity declaration-universe
  instantiation without an explicit `.{...}` instantiation, or when such a call occurs in an SCC without a complete
  explicit recursive signature.

* `E_GENERALIZATION_PARAMETRIC_ESCAPE` is emitted when a candidate declaration generalization fails rigid parametric
  rechecking because the candidate generalized variable would be observed, reified, returned, stored, or otherwise
  used ordinarily.
```

Amend the meaning of `E_UNIVERSE_LEVEL_EXPRESSION` to:

```text
* `E_UNIVERSE_LEVEL_EXPRESSION` is emitted when an expression used as a `Type` index or level-ordering operand:
  * does not have type `TypeLevel`;
  * is not total in the accepted KCore program;
  * is not stable for the lifetime of the dependent type containing it;
  * contains an unresolved universe metavariable at a checkpoint that requires rigid level terms;
  * contains an ill-scoped identity; or
  * cannot be represented as a well-scoped KCore level term.

  A stable opaque or neutral function application of type `TypeLevel` is not rejected merely because it does not reduce
  to `zero`, `omega`, `succ`, `+`, or `max`.
```

### 1.2 Diagnostic families

Insert in §3.2.3:

Family:

```text
kappa.universe.inference-requires-annotation
```

Used when a minimizable universe metavariable is outside the portable assignable fragment and cannot legally remain in a
generalized declaration schema.

Payload MUST include:

* declaration and SCC identities;
* selected metavariable identity;
* normalized constraints mentioning that metavariable;
* rigid assumptions in scope;
* which portable assignment rules were attempted;
* whether a semantic least solution is known not to exist, unknown, or merely outside the portable fragment;
* the smallest known explicit annotation or schema repair.

This family uses `E_UNIVERSE_INFERENCE_REQUIRES_ANNOTATION`.

Family:

```text
kappa.universe.recursive-schema
```

Used for invalid recursive declaration-schema instantiation.

Payload MUST include:

* recursive SCC identity;
* caller and callee declaration identities;
* current and requested universe instances;
* per-parameter normalized `<=` obligations;
* whether the instantiation was explicit or inferred;
* whether the SCC has a complete explicit recursive signature;
* the first failed inequality or missing explicit instantiation;
* the recursive call origin.

An upward or incomparable call uses `E_UNIVERSE_RECURSIVE_SCHEMA_INCREASE`.
A non-identity implicit call or non-identity call without a complete signature uses
`E_UNIVERSE_RECURSIVE_SCHEMA_IMPLICIT`.

Family:

```text
kappa.generalization.parametric-escape
```

Used when rigid parametric rechecking rejects a proposed generalized declaration.

Payload MUST include:

* declaration and SCC identities;
* candidate generalized metavariables and their classifiers;
* the rigid parametric binders introduced for rechecking;
* the first ordinary-observation dependency that escapes;
* whether the failed candidate was a type, universe, row, quantity, or extension-defined variable;
* the source origin of the ordinary use;
* the nearest explicit monomorphic annotation known to repair the declaration.

This family uses `E_GENERALIZATION_PARAMETRIC_ESCAPE`.

---

## 2. Replace the closed solver-expression restriction in §11.1.1

In §11.1.1, keep the actual opaque `TypeLevel` declaration and its runtime-capability rules.

Replace the text beginning with:

```text
Portable v1 solver-level expressions are canonical elaborated expressions, not source spellings.
```

through the end of the current **Universe operation identity** subsection with the following.

~~~~text
<!-- types.universes.level_terms -->
##### Level terms and universe-index admissibility

Kappa distinguishes ordinary typing of a level value from admissibility of that value as a universe index.

```text
Γ ⊢ t : TypeLevel
```

is the ordinary term-typing judgment.

```text
Γ ⊢level t : TypeLevel
```

is the universe-index admissibility judgment.

A term is level-admissible when all of the following hold:

1. `Γ ⊢ t : TypeLevel`;
2. `t` is total in the accepted KCore program;
3. `t` is stable for the lifetime of every dependent type containing that occurrence;
4. every free identity of `t` is in scope at the dependent type occurrence;
5. the occurrence can be serialized as a well-scoped KCore term;
6. no unresolved universe metavariable remains when rigid level checking is required.

`stable` means that the denotation of the term cannot change while the dependent type containing it remains in scope.
It does not mean that the term is known during compilation, closed, reducible, or built only from standard level
operations.

Accepted level terms include:

```kappa
u
record.level
chooseLevel b
f x
max (chooseLevel b) otherLevel
```

provided the terms satisfy the ordinary totality and stability rules.

Expression lifting and `do` elaboration occur before the level-admissibility judgment is checked.

For example, source syntax morally equivalent to:

```kappa
!readLevel
```

inside a larger lifted expression is first elaborated to an ordinary monadic bind:

```kappa
do
    let tmp <- readLevel
    ... tmp ...
```

A later type occurrence `Type tmp` is checked using the immutable binder `tmp`. There is no separate effectful
universe-index operation.

A mutable current-value facet is not stable in v1 and is not admitted directly in a universe index:

```kappa
do
    var u = 0
    pure (Type u)       -- rejected by the existing mutable-value static-position rule
```

An immutable snapshot may be admitted:

```kappa
do
    var u = 0
    let u0 = u
    pure (Type u0)
```

provided the snapshot is otherwise valid in the containing dependent type.

A future extension may admit flow-versioned mutable values such as `VarCurrent(cell, version)` as level terms. Kappa v1
does not.

The universe family uses the level-admissibility judgment:

```text
Γ ⊢level u : TypeLevel
────────────────────────────
Γ ⊢ Type u : Type (succ u)
```

A dependent Pi binder records whether its bound variable occurs in a universe-index or level-ordering position in the
codomain.

Application uses the following rule:

```text
Γ ⊢ f : (u : TypeLevel) -> B
Γ ⊢ a : TypeLevel
Γ ⊢level a : TypeLevel       when B contains a level dependency on u
────────────────────────────────────────────────────────────────────
Γ ⊢ f a : B[a/u]
```

No second source-level `TypeLevel` binder kind is introduced. The level dependency is a checked property of the
elaborated telescope.

KCore substitution MUST preserve level admissibility:

```text
Γ, u : TypeLevel ⊢level l : TypeLevel
Γ ⊢level a : TypeLevel
──────────────────────────────────────
Γ ⊢level l[a/u] : TypeLevel
```

The standard universe operations are ordinary `std.typelevel` declarations.

When a level term is translated into the solver view, the checker decomposes applications whose resolved semantic
identities are the canonical standard operations:

```kappa
zero
one
fromInteger
omega
succ
(+)
max
```

A stable total term that does not decompose through those operations becomes a rigid neutral atom rather than being
rejected.

The portable solver view is:

```text
LevelExpr ::=
    ClosedLevel(Nat omegaCoefficient, Nat finiteRemainder)
  | RigidAtom(LevelAtomId)
  | LevelMeta(LevelMetaId)
  | Add(LevelExpr, LevelExpr)
  | Max(LevelExpr, LevelExpr)

LevelAtomId ::=
    LocalLevelBinderId
  | DeclarationUniverseParameterId
  | DependentFieldLevelId
  | ProjectionLevelId
  | NeutralLevelTermId
```

`succ x` is represented as `Add(x, ClosedLevel(0, 1))` after constructor normalization.

A `NeutralLevelTermId` contains an alpha-normalized structural digest of the KCore term, resolved global identities, and
free-variable identities. The digest is computed independently of the enclosing type, the level constraint being solved,
and any proof object, so its definition is not circular. Two definitionally equal level terms denote the same rigid atom.
Equal source spelling alone is irrelevant.

Examples:

```kappa
opaque let chooseLevel
    (b : Bool)
    : TypeLevel =
    if b then 0 else omega

chooseLevel b
```

is a valid level term and, while opaque, is represented by one rigid neutral atom.

The solver does not automatically split every opaque term by unfolding its body. Transparent reduction and ordinary
branch refinement may expose more structure when the language's existing conversion rules permit it. A user may also
supply ordinary erased proof evidence about a neutral level term.

For example:

```kappa
chooseLevelBounded :
    (b : Bool) ->
    chooseLevel b < omega + 1
```

may discharge a bound required by a caller.

The compiler recognizes standard operations by resolved semantic identity, never by spelling. Shadowing `+`, `max`,
`succ`, or `omega` changes ordinary resolution, but an otherwise stable result of type `TypeLevel` remains a valid
neutral level term.

Explicit and inferred declaration-schema instantiations accept the same level-admissible terms. For example,
`f.{chooseLevel b}` is valid when `chooseLevel b` is stable and total. The instantiation is static and erased even when
its level term mentions an immutable runtime-originating value.

Thus this is valid even when `myMax` is opaque:

```kappa
Type (myMax u v)
```

The solver treats `myMax u v` as a rigid atom unless transparent reduction or selected evidence exposes additional
relations.

`E_UNIVERSE_LEVEL_EXPRESSION` is reserved for ill-typed, unstable, non-total, ill-scoped, meta-bearing, or otherwise
unrepresentable level terms. It is not emitted merely because a term is nonstandard or opaque.
~~~~

---

## 3. Amend §11.1.2.2 level assumptions

After the current substitution paragraph in §11.1.2.2, insert:

~~~~text
A recognized comparison proposition may mention any admissible level term, including a neutral atom.

For example:

```kappa
(@0 p : chooseLevel b < omega + 1)
```

introduces the ordinary local assumption:

```text
succ (chooseLevel b) <= omega + 1
```

where `chooseLevel b` is represented by its rigid neutral atom while opaque.

The solver may prove only consequences entailed for every assignment of unconstrained rigid atoms in the portable level
semantics. A satisfiable refutation means that the theorem is not entailed by the available level facts. For an opaque
neutral term, it does not claim that the source definition can realize the displayed abstract countermodel.
~~~~

---

## 4. Replace the canonical-grammar restrictions in §§11.1.2.4 and 11.1.2.5

In §11.1.2.4, replace the paragraphs beginning:

```text
Universe inference may use only canonical solver-level expressions.
```

through the `E_UNIVERSE_LEVEL_EXPRESSION` paragraph with:

~~~~text
Universe inference may use any term satisfying the level-admissibility judgment of §11.1.1.

Before solving, elaboration converts each admitted term into the solver view:

* canonical standard `zero`, `omega`, `succ`, `+`, and `max` applications are decomposed;
* closed standard operations are evaluated;
* transparent ordinary reduction may expose additional standard structure;
* every remaining stable total neutral term becomes a rigid atom;
* inference metavariables remain `LevelMeta` nodes until solved or generalized.

An opaque or user-defined term of type `TypeLevel` is not unfolded merely to improve solver precision.

Failure to prove a required relation involving a neutral atom is an unsolved universe constraint, not an invalid level
expression.
~~~~

In §11.1.2.5, replace:

```text
A value `i : TypeLevel` may index `Type` only when the expression used as the index is a solver-level expression ...
```

and the later paragraph beginning:

```text
However, a `TypeLevel` value is admissible as a `Type` index ...
```

with:

~~~~text
A value `i : TypeLevel` may index `Type` when the corresponding term satisfies the level-admissibility judgment of
§11.1.1.

The exact dependent result is retained.

For example:

```kappa
use :
    (u : TypeLevel) ->
    (@0 p : u < omega + 1) ->
    Type u ->
    Type u
```

may be applied to an opaque level term:

```kappa
use (chooseLevel b) proof x
```

with exact result type:

```kappa
Type (chooseLevel b)
```

The compiler does not widen this result merely because the index is opaque.

A cumulative common universe may be selected when an expected type or branch join intentionally forgets the exact
index. Such widening is expected-type-directed and is represented by explicit KCore lifts.
~~~~

---

## 5. Declaration generalization and parametric rechecking

### 5.1 Amend hidden and local generalization

Append to §11.1.2.3A and replace the body of the current **Local declaration universe generalization** subsection with
the following unified rules.

~~~~text
<!-- types.generalization.declaration_boundaries -->
##### Declaration generalization boundaries

Fresh implicit generalization occurs only at semantic declaration boundaries.

Declaration boundaries include:

* top-level term definitions and signatures;
* local `let` term declarations;
* local type declarations and aliases;
* trait, data, effect, projection, and instance declarations where their ordinary rules permit generalization;
* one complete top-level or local recursive declaration SCC.

The following binders are not declaration generalization boundaries:

* lambda parameters;
* constructor and pattern binders;
* match branch binders;
* record destructuring binders;
* monadic `<-` binders;
* handler clause binders;
* comprehension binders;
* ordinary function application.

A `<-` binder is introduced by ordinary elaboration of `bind`. The action is instantiated before the bound value exists.
No new outer quantifier is introduced around that value.

Existing polymorphism is preserved.

If:

```text
Γ ⊢ foo : forall a. F a
```

then:

```kappa
let boo = foo
```

may bind `boo` at the same polymorphic type. This does not invent or move a quantifier.

Fresh declaration generalization proceeds as follows:

1. Infer the declaration body at a type containing candidate metavariables.
2. Select candidates that:
   * are not free in the surrounding typing environment;
   * occur in a classifier admitted for declaration generalization;
   * are not fixed by an expected monomorphic signature;
   * are not blocked by an unsolved higher-priority obligation.
3. Replace selected candidates by fresh rigid variables with `parametric` observation mode.
4. Recheck the complete declaration body or declaration SCC under those rigid variables.
5. Require that no selected variable occurs in the body's ordinary-observation dependency set.
6. Abstract the selected variables only at the outer declaration boundary.
7. For universe candidates, create hidden or explicit declaration-universe parameters and generated erased constraint
   binders under §§11.1.2.3A and 11.1.2.3A.1.

Schematically:

```text
Γ, parametric a1, ..., an ⊢ rhs : T[a1, ..., an] ▷ D
{a1, ..., an} ∩ FV(Γ) = {}
{a1, ..., an} ∩ D = {}
────────────────────────────────────────────────────────
Γ ⊢ declaration x = rhs
    with x : forall a1 ... an. T[a1, ..., an]
```

Universe variables are abstracted in the declaration-universe telescope rather than as ordinary term-level `forall`
binders.

A candidate that fails rigid parametric rechecking is not silently widened to ordinary observation. The declaration is
kept monomorphic when an expected monomorphic type fixes it; otherwise it is rejected with
`E_GENERALIZATION_PARAMETRIC_ESCAPE`.

Local recursive declarations generalize once per local SCC. Outer rigid variables remain rigid and are not generalized
again. Every use outside the SCC freshly instantiates the local declaration telescope.

The generalization rule is independent of whether the declaration body syntactically looks like a value, constructor,
lambda, monadic action, lazy value, or foreign call. Soundness comes from the declaration boundary, the free-variable
condition, and rigid parametric rechecking, not from a blacklist of suspicious nouns.
~~~~

### 5.2 Generalization does not commute universal quantifiers

Insert immediately after the previous subsection:

~~~~text
<!-- types.generalization.no_quantifier_commutation -->
##### Generalization does not commute quantifiers through type constructors

Declaration generalization changes:

```text
T[?a]
```

into an outer abstraction:

```text
forall a. T[a]
```

It does not transform:

```text
forall a. G (F a)
```

into:

```text
G (forall a. F a)
```

and does not perform the reverse transformation.

Those types may be related only through explicit ordinary evidence supplied by the relevant type constructor.
~~~~

### 5.3 Add a standard first-class quantifier-interchange trait

Insert in the standard trait section, with cross-reference from the preceding subsection:

~~~~text
<!-- traits.preserves_parametric_forall -->
#### `PreservesParametricForall`

The standard prelude provides the ordinary trait:

```kappa
trait PreservesParametricForall.{u, v, w}
    (parametric 0 G : (A : Type v) -> Type w) =

    pullForall :
        (parametric 0 F : (A : Type u) -> Type v) ->
        (forall (A : Type u). G (F A)) ->
        G (forall (A : Type u). F A)
```

Evidence states that `G` lawfully moves one parametric universal quantifier from outside `G` into its argument.

The compiler may insert `pullForall` only:

* when an expected type requires this exact interchange;
* after normal implicit resolution selects unique coherent evidence;
* without supplying an omitted explicit source argument;
* with the selected evidence application represented explicitly in KCore.

This trait is not implied by `Functor`, `Applicative`, `Monad`, laziness, memoization, purity, or runtime representation
similarity alone.

A lawful `Need`-like type constructor may provide the evidence. A mutable `Ref`-like constructor ordinarily cannot.
~~~~

---

## 6. Remove the sealing-eliminator exception

In §30.2.0, replace the current case-analysis sentence:

```text
Dependencies of a parametric scrutinee also propagate unless the eliminator is a declared sealing eliminator whose
result mode is checked parametrically.
```

with:

~~~~text
Dependencies of a parametric scrutinee propagate through case analysis.

Kappa v1 has no generic user-declared or compiler-declared "sealing eliminator" that may discard observation
dependencies.

Construction into a declared parametric field is the sealing boundary. Projection or pattern binding restores a
parametric origin. Construction into an ordinary field propagates the dependency. An ordinary result is accepted only
when its computed ordinary-observation dependency set is empty.
~~~~

Add to the required metatheory:

```text
An expression checked with an empty ordinary-observation dependency set cannot reify a type code or static value that is
available only through parametric fields, constructor arguments, projections, pattern binders, aliases, or higher-kinded
applications.
```

---

## 7. Represent all declaration-universe constraints as erased proof binders

Amend §§11.1.2.3A and 11.1.2.3A.1 with:

~~~~text
<!-- types.universes.constraint_telescope -->
##### Declaration-universe constraint proof telescope

There is one source and core mechanism for declaration-universe constraints: erased proof binders.

A user may write a bound directly:

```kappa
expect let liftCode.{u, v}
    (@0 p : u <= v)
    (ordinary 0 A : Type u)
    : Type v
```

When elaboration infers a declaration-universe constraint not already represented by an equivalent user binder, it
inserts an anonymous implicit erased binder immediately after the declaration-universe telescope and before the
user-written term telescope:

```kappa
(@0 __universeConstraint0 : u <= v)
```

Generated constraint binders are ordered by deterministic first occurrence of their normalized propositions in the
fully elaborated declaration signature, with duplicate propositions removed by semantic level equality.

At a declaration reference:

* schema levels are instantiated first;
* generated and user-written implicit constraint binders are solved by ordinary level-proof insertion;
* explicit user-written term-level `TypeLevel` arguments are never supplied by schema instantiation;
* the resulting application spine records every proof argument explicitly in KCore.

The interface records:

* each normalized comparison proposition;
* its telescope position;
* its rigid dependencies;
* whether it was source-written or generated;
* the solver and algebra versions required to check it.

The proposition participates in interface and semantic identity. The arbitrary identity of one proof object does not.

For nominal families, constraint proof binders belong to the complete family telescope and therefore participate in full
saturation and schema-action alignment. They erase at runtime and do not alter representation.
~~~~

Replace the sentence:

```text
Constraints among schema parameters are inferred from the declaration signature and body and are retained in the
interface. Kappa v1 introduces no second surface syntax for declaration-schema constraints.
```

with:

```text
Constraints among schema parameters are ordinary erased proof binders. Source-written `@0` comparison binders and
compiler-generated anonymous comparison binders have the same KCore meaning. Kappa introduces no second constraint
language.
```


### 7.1 KCore and KCoreText constraint representation

Replace the authoritative KCore record:

```text
DeclarationUniverseTelescope =
    (parameters  : List UniverseParameter,
     constraints : List UniverseConstraint)
```

with:

```text
DeclarationUniverseTelescope =
    List UniverseParameter

DeclarationConstraintSummary =
    List NormalizedLevelProposition
```

`DeclarationConstraintSummary` is derived from the declaration's implicit erased proof binders. It is a checked cache
for interfaces, diagnostics, role comparison, and solver startup; it is not a second source of authority.

The authoritative KCore declaration type contains the generated or source-written proof binders in its ordinary term
telescope.

Amend KCoreText declaration grammar so `constraintBlock?` is removed from `defDecl`, `axiomDecl`, `dataDecl`,
`constructorDecl`, and `localDef`.

`constraintBlock` remains in `levelCertificateDecl` and schema-certificate declarations as the explicit assumption
context of the certificate being checked.

Canonical KCoreText prints generated declaration constraints as ordinary-observation, ordinary-formation, implicit
quantity-`0` binders in the declaration type or nominal family telescope.

For example, a generated constraint is printed schematically as:

```kcore
(ordinary ordinary 0 implicit value %__universeConstraint0#7 :
    term-node "boolean-proof" {
      term-value = term-value(apply @std.typelevel.le#... (...));
    })
```

using the actual canonical Boolean-to-proposition KCore node standardized by the surrounding specification.

Nominal family saturation includes these binders. Role checking aligns their normalized propositions and inserts the
corresponding erased proof evidence at the target instance.

---

## 8. Replace §11.1.2.4A with the normative level-solver architecture

Replace the current **Principal universe inference** subsection with the following two subsections.

~~~~text
<!-- types.universes.level_solver -->
##### 11.1.2.4A Level constructor normalization and rigid entailment

Kappa separates:

```text
1. deterministic constructor normalization;
2. exact rigid semantic entailment;
3. assignable universe-metavariable inference.
```

No one layer is claimed to be a complete replacement for either of the others.

###### Stored constructor normal form

After level-admissibility checking and translation to the solver view, constructor normalization produces:

```text
LevelNF ::=
    Closed(c : Nat, n : Nat)
  | Atom(LevelAtomId)
  | AddNF(nonempty sorted list LevelNF)
  | MaxNF(nonempty sorted duplicate-free list LevelNF)
  | Meta(LevelMetaId)
```

Normalization performs exactly these equations:

```text
succ x = x + 1

addition:
    associative
    commutative
    zero-eliminating
    closed-constant-folding
    multiplicity-preserving

maximum:
    associative
    commutative
    idempotent
    zero-eliminating
```

Nested additions and maxima are flattened and rebuilt left-associated from their canonical lists.

No distributivity, cancellation, absorption, semantic dominance, or general Presburger simplification is part of
constructor normalization.

A portable total ordering for constructor-normal forms is:

```text
Closed < Atom < AddNF < MaxNF < Meta
```

with:

* closed pairs compared lexicographically;
* atom kinds ordered as local binder, declaration parameter, field, projection, neutral term;
* atom payloads compared by canonical semantic-identity bytes;
* addition and maximum lists compared lexicographically by this same recursive order;
* metavariables compared by deterministic declaration-local metavariable identity.

The exact rank has no mathematical significance but is normative for canonical KCoreText and hashing.

The following expressions need not share constructor normal forms:

```text
max u (succ u)                  and succ u
u + max v w                     and max (u + v) (u + w)
max (u + 1) (u + omega)         and u + omega
```

They are semantically equal when rigid entailment proves both inequalities.

###### Rigid semantic domain

Every rigid level expression denotes a pair in:

```text
Nat × Nat
```

where `(c, n)` denotes `omega * c + n`.

```text
zero                = (0, 0)
finite k            = (0, k)
omega               = (1, 0)
succ(c, n)          = (c, n + 1)
(c, n) + (d, m)     = (c + d, n + m)
max                  = lexicographic maximum
```

Ordering is lexicographic:

```text
(c, n) <= (d, m)
iff
c < d or (c = d and n <= m)
```

Each rigid atom receives one independent pair of nonnegative integer variables unless ordinary definitional equality or
explicit assumptions identify it with another atom.

###### Rigid entailment

To decide whether a consistent rigid assumption context `A` entails `x <= y`:

1. normalize constructor syntax;
2. reject unresolved inference metavariables;
3. assign two nonnegative integer variables to every distinct rigid atom;
4. translate `succ`, addition, and lexicographic ordering to quantifier-free Presburger arithmetic;
5. translate `max a b` using a guarded conditional selecting the lexicographically greater pair;
6. decide satisfiability of:

   ```text
   nonnegative atom components
   and translation(A)
   and not translation(x <= y)
   ```

The theorem is entailed exactly when the refutation formula is unsatisfiable.

A conforming implementation may use any complete decision procedure for this exact QF Presburger translation.

Rigid semantic equality is mutual entailment:

```text
A entails x = y
iff
A entails x <= y
and
A entails y <= x
```

Constructor-normal equality is a sound fast path only.

For a neutral opaque atom, a satisfying refutation model proves only that the inequality is not entailed by the available
abstract facts. It does not assert that the source function can realize that model.

Solver results are classified as:

```text
Entailed
NotEntailed
BlockedByMetavariables
ContradictoryAssumptions
IndeterminateResourceLimit
```

`IndeterminateResourceLimit` never permits acceptance.

Recognized contradictory assumption contexts are rejected before they may justify any universe formation.

<!-- types.universes.principal_inference -->
##### 11.1.2.4B Portable principal universe-metavariable inference

Rigid entailment is complete for the portable rigid theory. Inference assignments are guaranteed only for the portable
assignable fragment defined here.

The solver receives:

```text
* a finite selected set of minimizable metas;
* a finite unselected set of residual or generalizable metas;
* normalized inequalities under consistent rigid assumption contexts.
```

The pointwise order on assignments is the rigid semantic `<=` relation after substitution.

The portable solver performs, in order:

1. constructor normalization;
2. cancellation of a common additive multiset on both sides;
3. cancellation of a common successor, since `succ x = x + 1`;
4. extraction of direct lower bounds `lower <= ?m`;
5. reduction of maximum-only self occurrences, including:
   * `max ?m lower <= ?m` to `lower <= ?m`;
   * internal SCC occurrences that appear only beneath `max`;
6. joining lower-bound contributions with `max`;
7. solving selected-meta SCCs together;
8. closed residuation for a selected meta in a closed additive right context;
9. selected single-meta maximum contexts of either form:
   * `max(?m, rigidArms...) <= ?m`, contributing every rigid arm as a lower bound;
   * `lower <= max(?m, rigidArms...)`, contributing `lower` exactly when rigid entailment proves that the rigid arms
     alone do not satisfy `lower`;
10. substitution, renormalization, and rigid rechecking of every resulting constraint.

Common additive cancellation validates, for example:

```text
p + 1 <= ?u + 1     becomes p <= ?u
succ p <= succ ?u   becomes p <= ?u
```

Closed residuation validates:

```text
5 <= ?u + 2         gives ?u := 3
```

For closed pairs `L = (lc, ln)` and `C = (cc, cn)`, the least `M` satisfying `L <= M + C` is:

```text
(0, 0)                              when lc < cc
(0, max(0, ln - cn))                when lc = cc
(lc - cc, max(0, ln - cn))          when lc > cc
```

The result is rechecked by rigid entailment before assignment.

The solver rejects recursive self-containment through positive addition or successor, including:

```text
succ ?u <= ?u
?u + 1 <= ?u
```

The solver does not claim a pointwise least assignment for:

```text
omega <= max ?u ?v
```

because the two metas admit incomparable minimal assignments.

Each minimizable meta receives one result:

```text
SolvedPrincipal(level)
Unsatisfiable
NoPointwiseLeastSolution
OutsidePortableInferenceFragment
BlockedByUnselectedMetas
```

`NoPointwiseLeastSolution` may be reported only when the solver has a checked certificate of non-principality, such as
incomparable minimal solutions.

`OutsidePortableInferenceFragment` does not claim that no semantic principal solution exists.

At a declaration boundary:

* remaining legal generalizable metas become declaration-universe parameters and erased constraint binders;
* a minimizable meta with `OutsidePortableInferenceFragment` is rejected with
  `E_UNIVERSE_INFERENCE_REQUIRES_ANNOTATION`;
* `NoPointwiseLeastSolution` uses `E_UNIVERSE_NO_PRINCIPAL_SOLUTION`;
* unsatisfiable constraints use the existing universe-constraint diagnostics.

A conforming portable implementation MUST NOT silently accept additional out-of-fragment inference merely because an
implementation-specific SMT solver can guess a useful assignment. A future standardized extension may enlarge this
fragment and must version the inference contract.
~~~~

---

## 9. KCoreText level terms and complete arithmetic replay

### 9.1 Amend level syntax

In §30.2.0A, retain:

```text
level-term(term)
```

and add:

```text
A `level-term(term)` is valid when `term` passes ordinary KCore typing, totality, stability, scoping, and the
level-admissibility judgment.

Canonical standard operations are printed structurally as `add`, `max`, and closed levels after constructor
normalization. A neutral term is printed as `level-term(canonicalTerm)`.
```

### 9.2 Replace `levelProof`

Replace the current `levelProof` grammar and following prose with:

```text
levelProof ::=
    'assumption' '(' integer ')' ';'
  | 'arithmetic' '[' integerList? ']' ';'
  | 'closed' ';'
  | 'zero-left' level ';'
  | 'refl' level ';'
  | 'trans' '{' levelProof levelProof '}'
  | 'succ-mono' '{' levelProof '}'
  | 'max-left' level level ';'
  | 'max-right' level level ';'
  | 'max-least' '{' levelProof levelProof '}'
  | 'add-mono-left' level '{' levelProof '}'
  | 'add-mono-right' level '{' levelProof '}'

integerList ::=
    integer (',' integer)*
```

`arithmetic [i1, ..., in]` is the complete portable replay form for rigid level entailment.

Its verifier:

1. selects exactly the listed normalized assumptions from the certificate's constraint block;
2. rejects duplicate, unavailable, out-of-range, ill-scoped, or meta-bearing assumptions;
3. checks that the selected assumption context is satisfiable;
4. converts strict propositions to `succ lhs <= rhs`;
5. constructor-normalizes every endpoint;
6. translates the selected assumptions and stated theorem to the normative paired QF Presburger semantics of
   §11.1.2.4A;
7. accepts exactly when the selected assumptions entail the theorem.

The structural forms are compact conveniences. They are not the completeness boundary.

After a structural or arithmetic proof is verified, KCore stores canonical level-entailment evidence containing:

```text
* normalized theorem;
* a deterministic irredundant ordered subset of normalized assumptions;
* TypeLevel algebra version;
* rigid-entailment verifier version.
```

The deterministic irredundant subset is computed by visiting assumptions in normalized order and removing an assumption
when the theorem remains entailed without it.

Canonical KCoreText prints verified level-entailment evidence as:

```text
arithmetic [canonical dependency indices];
```

regardless of whether the input used a structural proof.

Resource exhaustion rejects the certificate or reports an indeterminate verification failure. It never validates the
certificate.

### 9.3 Canonical level serialization and hashing

Add to KCoreText canonicalization:

```text
* every printed level is in the recursive AC/ACI constructor normal form of §11.1.2.4A;
* addition operands retain multiplicity and use the normative portable ordering;
* maximum operands are duplicate-free and use the same ordering;
* neutral level terms are represented by canonical KCore term syntax;
* semantic level equality is checked by mutual entailment, never by constructor-tree equality alone;
* proof syntax is not part of level-evidence semantic identity;
* two verified proofs of the same normalized theorem from the same canonical dependency set have the same semantic hash.
```

---

## 10. Recursive universe polymorphism

Insert after declaration-universe generalization and cross-reference from Chapter 15.

~~~~text
<!-- types.universes.recursive_schemas -->
##### Recursive declaration-universe schemas

Kappa distinguishes:

```text
first-class recursion over `(u : TypeLevel)`
```

from:

```text
polymorphic recursion through a declaration schema `f.{u}`.
```

A first-class `TypeLevel` parameter is an ordinary term parameter. Recursive calls may increase, decrease, or otherwise
change that parameter when the ordinary type checker and termination checker accept the call.

For a recursive declaration SCC with current rigid universe instance:

```text
.{u1, ..., un}
```

an internal recursive reference at:

```text
.{v1, ..., vn}
```

is valid in Kappa v1 only when the checker proves pointwise:

```text
v1 <= u1
...
vn <= un
```

Rules:

* an identity recursive instantiation may omit `.{...}`;
* every non-identity recursive instantiation must be written explicitly;
* every SCC containing a non-identity recursive instantiation must have complete explicit recursive signatures and
  explicit declaration-universe schemas;
* recursive schema instantiations are not inferred from an expected result type;
* required `universeLift` and `schemaLift` nodes remain explicit in KCore;
* an upward or incomparable recursive schema instance is rejected with `E_UNIVERSE_RECURSIVE_SCHEMA_INCREASE`;
* a non-identity implicit instance or non-identity call without complete signatures is rejected with
  `E_UNIVERSE_RECURSIVE_SCHEMA_IMPLICIT`.

The pointwise `<=` restriction is a typing rule, not a termination proof.

A call at the same schema instance still requires ordinary structural, size-change, sized, or well-founded descent.

A strict schema decrease:

```text
vi < ui
```

may contribute a static size-change `<` edge because the standard `TypeLevel` ordering is well founded on the admitted
level domain.

For a recursive SCC, the size-change graph may include declaration-universe parameters as static rows and columns.
Every accepted cycle must still contain an ordinary or static strict decrease under the existing termination rules.

Kappa v1 does not admit an upward recursive declaration-schema call even when another runtime argument decreases.
A future explicit polymorphic-recursion extension may do so only with complete signatures, explicit schema arguments,
and a separately checked well-founded measure. It is not inferred from ordinary `.{u}` syntax.
~~~~

Amend §15.4 so `TypeLevel` is an admitted portable measure type:

```text
For a `TypeLevel` component, the component order is the standard `<` relation of §11.1.2.2. The admitted level domain is
well founded, so no non-negativity side condition is required.
```

---

## 11. Lift semantic identity and direct expected-type-directed schema lifting

### 11.1 Replace the semantic-hash rule for `universeLift`

In §30.2.1A, replace:

```text
semantic hashes include canonical source level, target level, and evidence identity;
```

with:

~~~~text
semantic identity includes:

* canonical source level;
* canonical target level;
* the normalized theorem `source <= target`;
* the canonical dependency set of active level assumptions;
* the `TypeLevel` algebra and rigid-entailment versions.

The arbitrary identity or syntax of the proof object does not participate in semantic identity.

Original proof and certificate identities remain available as provenance and audit metadata.
~~~~

Add:

```text
A direct lift and a transitively composed lift with the same canonical source, target, theorem, and dependency set have
the same semantic hash.
```

### 11.2 Strengthen `schemaLift` insertion

Insert in §30.2.1B:

~~~~text
Surface elaboration considers a `schemaLift` only when both are already known:

```text
synthesized type = D.{a1, ..., an} x1 ... xm
expected type    = D.{b1, ..., bn} y1 ... ym
```

and both applications are fully saturated applications of the same resolved nominal family.

The elaborator attempts one direct source-to-target lift.

It does not:

* search a graph of intermediate universe instances;
* invent a target family instance to solve an unconstrained metavariable;
* use `irrelevant` roles to default unrelated levels;
* lift a partial family head or constructor constant;
* invoke user coercion or trait search;
* participate in instance-head candidate matching or overlap checking.
~~~~

Amend schema-certificate semantic identity:

~~~~text
A schema-action certificate's semantic identity is derived from:

* family semantic identity;
* normalized nominal signature-closure hash;
* effective role vector;
* certificate-checker version;
* `TypeLevel` algebra version.

Allocation identity and proof-object identity do not participate.
~~~~

---

## 12. Expected-type-directed schema reification

Insert after §11.1.2.3A.1:

~~~~text
<!-- types.universes.schema_reification -->
##### Reifying declaration schemas as bounded first-class functions

Declaration-universe polymorphism remains declaration-level when no single first-class type can classify every
instantiation.

When an expected type supplies a bounded first-class level telescope, elaboration may eta-expand a declaration schema.

For example, an expected type:

```kappa
(u : TypeLevel) ->
(@0 p : u < k) ->
Result u
```

may reify `f.{u}` as:

```kappa
\ (u : TypeLevel) (@0 p : u < k) ->
    f.{u}
```

provided every schema constraint is discharged by `p` or the surrounding context.

Rules:

* reification is triggered only by a known expected first-class polymorphic type;
* generated level lambdas and proof binders are explicit in KCore;
* hidden declaration-universe arguments may be instantiated;
* implicit erased proof arguments may be inserted;
* an omitted explicit term-level `TypeLevel` argument is never supplied;
* without an expected polymorphic type, a declaration-polymorphic value is instantiated once at the use site;
* the transformation preserves observation mode, quantity, and runtime representation.

Thus a source function:

```kappa
g : (u : TypeLevel) -> T u
```

is not applied merely by writing `g`. Explicit term arguments remain explicit.
~~~~

---

## 13. Standard monotonicity evidence and discovery

Replace §10.4.3.4 with:

~~~~text
<!-- data_types.nominal_signature_variance.level_monotonicity -->
##### 10.4.3.4 Level-expression monotonicity

Role inference uses ordinary checked evidence of the canonical trait:

```kappa
trait Monotone
    (ordinary 0 f : TypeLevel -> TypeLevel) =

    monotone :
        (x : TypeLevel) ->
        (y : TypeLevel) ->
        (@0 p : x <= y) ->
        (f x <= f y) = True
```

The authoritative trait identity is `std.typelevel.Monotone`. Recognition is by resolved semantic identity, never by
spelling.

The standard prelude provides checked `IsTrait`, `IsSubsingleton`, and `RuntimeErased` evidence for `Monotone f`. Its
only member is erased proof evidence; multiple coherent proofs therefore cannot produce runtime or semantic-identity
differences.

The standard prelude supplies coherent evidence for canonical standard operations and their supported partial
applications, including:

```text
succ
\x -> x + k
\x -> k + x
\x -> max x k
\x -> max k x
```

using the checked standard level theorems.

For a user-defined or opaque level function `f`, the compiler forms the ordinary goal:

```kappa
Monotone f
```

Evidence discovery uses normal implicit resolution:

1. explicit or implicit local evidence;
2. ordinary visible instances;
3. standard instances and instance combinators.

The compiler does not scan arbitrary declarations in the same module for a theorem whose type happens to resemble
monotonicity.

A theorem may be made discoverable by packaging it as an ordinary instance:

```kappa
fooMonotoneProof :
    (x y : TypeLevel) ->
    (@0 p : x <= y) ->
    foo x <= foo y

instance Monotone foo =
    monotone = fooMonotoneProof
```

or by passing local evidence:

```kappa
(@0 mono : Monotone foo)
```

For a compound occurrence, the role checker forms the normalized one-hole function whose argument is the schema
parameter and requests `Monotone` for that function.

Selected monotonicity evidence is resolved and frozen before the universe-role fixed point begins. The fixed-point
checker consumes selected evidence; it does not launch trait search during iteration.

Evidence whose typing depends on the not-yet-established role vector or schema-action certificate of the same nominal
signature block is cyclic and rejected.

If no evidence is selected, every affected schema parameter is conservatively forced to `invariant`. If the user wrote a
more permissive explicit role, the existing variance diagnostic identifies the unsolved `Monotone` goal.

The normalized `Monotone f` proposition and its dependencies participate in the nominal signature closure. The arbitrary
identity of one proof object does not participate in semantic hashing, though it remains audit provenance.

Monotonicity does not justify cancellation or order reflection.

The standard prelude may separately define:

```kappa
trait Monotone f => OrderEmbedding
    (ordinary 0 f : TypeLevel -> TypeLevel) =

    reflectLe :
        (x : TypeLevel) ->
        (y : TypeLevel) ->
        (@0 p : f x <= f y) ->
        x <= y
```

Only an `OrderEmbedding`-like fact may justify generic inverse-order reasoning. The principal solver's standard
successor and common-addition cancellation is justified by the corresponding checked standard theorems, not by
`Monotone` alone.
~~~~

---

## 14. Remove references to inverse lifts

In §30.2.0, replace:

```text
`universeLift`, `schemaLift`, and their inverses preserve dependencies.
```

with:

```text
`universeLift` and `schemaLift` preserve observation dependencies.

A reverse conversion is a separate checked lift requiring independently valid reverse level or schema evidence.
Covariant lifts have no implicit inverse.
```

Apply the same wording replacement anywhere else the specification refers to an inverse cumulative lift.

---

## 15. `TypeLevel` bootstrap and versioning

Insert after the standard `TypeLevel` operation definitions in §11.1.2.2:

~~~~text
<!-- types.universes.bootstrap_versions -->
##### `TypeLevel` bootstrap and semantic versions

The standard prelude declarations are the source-level authority for `TypeLevel` and its operations.

A compiler may predeclare their canonical semantic identities while bootstrapping the prelude, but it MUST:

1. check the actual source declarations against the required signatures;
2. check or verify the normative operation bodies and law evidence;
3. verify that its solver bridge is extensionally equivalent to those declarations;
4. reject a mismatching bootstrap prelude rather than silently replacing it.

Interfaces, KCoreText modules, caches, level certificates, schema certificates, and semantic hashes record:

```text
typeLevelAlgebraVersion
levelConstructorNormalizerVersion
levelRigidEntailmentVersion
levelPrincipalInferenceVersion
levelCertificateVersion
```

Changing the represented level domain, ordering, addition, maximum, successor, or certificate semantics requires a
corresponding version change and invalidates incompatible artifacts.
~~~~

Amend KCoreText required module metadata to include those five fields.

---

## 16. Interface and KCore amendments

Add to module-interface requirements:

```text
* canonical KCore terms and referenced semantic identities for neutral level terms used in exported types; opaque declaration bodies are included only when ordinary transparency rules require them;
* level-admissibility dependency summaries for term-level TypeLevel binders used in exported dependent types;
* generated declaration-universe proof binders and their normalized propositions;
* canonical level-evidence dependency sets, excluding proof-object identity;
* recursive SCC schema-instantiation policy and every non-identity recursive schema edge;
* selected `Monotone` goals and evidence dependencies used by exported role certificates;
* all five TypeLevel solver/algebra version fields.
```

Schema certificates serialize each selected monotonicity proof as a checked witness containing the affected parameter
index, canonical one-hole operator, exact resolved `Monotone` goal, selected evidence term, and the exact canonical
dependency closure of the goal and evidence. KCoreText verifies the evidence before replaying roles and treats the
neutral occurrence as invariant when no matching verified witness exists. The evidence term and evidence-only
dependencies remain audit provenance and are excluded from semantic hashing; the normalized goal and its dependencies
remain semantic.

Add to KCore checkpoint verification:

```text
* recheck the level-admissibility judgment for every `level-term`;
* recheck substitution closure for every dependent TypeLevel application spine;
* reject a mutable current-value facet embedded in a v1 universe index;
* replay every arithmetic level certificate with the normative rigid verifier;
* recompute canonical level-evidence dependencies;
* recheck same-or-lower recursive schema edges;
* reject non-identity implicit recursive schema instantiation;
* verify that schema reification inserted no omitted explicit term-level argument;
* verify selected `Monotone` evidence before role-certificate checking;
* reject any lift whose semantic identity depends on proof-object allocation identity.
```

---

## 17. Global normative replacements

Apply these global edits:

1. Replace claims that arbitrary user-defined `TypeLevel` terms are invalid universe indices with the level-admissibility
   judgment and neutral-atom rules of §11.1.1.
2. Replace claims that constructor-normal equality is complete semantic equality with mutual rigid entailment.
3. Replace claims that principal inference finds every expressible least solution with the portable assignable-fragment
   contract.
4. Replace KCoreText structural-proof completeness claims with arithmetic replay as the completeness boundary.
5. Replace generated universe-constraint side tables with generated erased proof binders in the declaration telescope.
6. Remove every generic sealing-eliminator exception.
7. Remove every reference to inverse cumulative lifts.
8. State that `schemaLift` is considered only against a known expected fully saturated same-family target.
9. State that schema eta-reification inserts hidden schemas and implicit evidence only, never explicit term arguments.
10. Replace unspecified monotonicity-certificate language with ordinary `std.typelevel.Monotone` trait evidence.

---

## 18. Required metatheory

Add to the universe and KCore metatheory obligations:

```text
* substitution closure of the level-admissibility judgment;
* subject reduction for dependent types indexed by opaque neutral TypeLevel terms;
* stability of neutral-atom identity under alpha-renaming and definitional equality;
* soundness and completeness of paired QF Presburger rigid entailment;
* soundness of the portable principal-assignment fragment;
* correctness of common-addition and successor cancellation;
* correctness and determinism of arithmetic-certificate replay;
* proof irrelevance of recognized erased level-ordering evidence for semantic identity;
* soundness of rigid parametric declaration generalization;
* separation of declaration generalization from quantifier interchange;
* noninterference for unbounded parametric package elimination without sealing exceptions;
* subject reduction for same-or-lower recursive schema instantiation;
* preservation of termination certificates when static schema-level rows participate in SCT;
* coherence of expected-type-directed schema eta-reification;
* soundness of role inference using selected Monotone evidence;
* cache and interface soundness across TypeLevel algebra and solver version changes.
```


---

## 19. Appendix T harness additions required by the companion suites

Add to §T.5.2:

```text
assertLevelNormalForm <levelExpr> equals <levelExpr>
assertLevelEntails <comparisonExpr>
assertLevelDoesNotEntail <comparisonExpr>
assertPrincipalUniverse <qualified-declaration> <levelExpr>
assertUniverseInferenceClass <qualified-declaration> <inference-class>
assertLevelSolve <selected-meta-list> where <constraint-list> gives <assignment-list>
assertLevelSolveClass <selected-meta-list> where <constraint-list> <inference-class>
assertSemanticHashEquals <artifact-or-target>
assertRecursiveSchemaEdge <caller> <callee> <relation>
assertSelectedEvidence <goalType> <qualified-evidence>
```

where:

```text
inference-class ::=
    SolvedPrincipal
  | Unsatisfiable
  | NoPointwiseLeastSolution
  | OutsidePortableInferenceFragment
  | BlockedByUnselectedMetas

relation ::= identity | lower-or-equal | strict-lower
```

Rules:

* `assertLevelNormalForm` elaborates both expressions as `TypeLevel`, translates them into the solver view, and compares
  their recursive AC/ACI constructor normal forms.
* `assertLevelEntails` succeeds iff the active test-level assumptions rigidly entail the comparison under
  §11.1.2.4A.
* `assertLevelDoesNotEntail` succeeds iff the rigid refutation formula is satisfiable. It does not claim that an opaque
  source function realizes the abstract countermodel.
* `assertPrincipalUniverse` checks the solved minimizable result universe of the named declaration before any expected
  cumulative lift.
* `assertUniverseInferenceClass` checks the portable principal-solver classification of the named declaration.
* `assertLevelSolve` invokes the portable principal solver directly over test-local rigid atoms and selected metavariables and checks the canonical assignment.
* `assertLevelSolveClass` checks the solver classification when no assignment is expected.
* `assertSemanticHashEquals` is the equality counterpart of `assertSemanticHashDiffersFrom` and compares canonical
  semantic identities, not raw file bytes.
* `assertRecursiveSchemaEdge` inspects verified KCore and checks the canonical recursive edge classification.
* `assertSelectedEvidence` checks the evidence selected by ordinary implicit resolution for the normalized goal. It does
  not perform a second search during assertion evaluation.

Add to §T.5.3:

```text
assertKCoreLevelEvidence <path> <certificate-ref> dependencies <integer-list>
assertKCoreSemanticHashEquals <path1> <path2>
```

This parses and verifies the KCoreText file, resolves the certificate, and checks its canonical irredundant dependency
set after arithmetic replay.

`assertKCoreSemanticHashEquals` parses and verifies both KCoreText files and compares their canonical KCore semantic
hashes. Raw source bytes and proof syntax are ignored.
