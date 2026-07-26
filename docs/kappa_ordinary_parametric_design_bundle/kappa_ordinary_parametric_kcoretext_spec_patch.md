# Kappa `ordinary` / `parametric` modality and KCoreText patch

**Patch base:** `Spec(96)(1).md`

This patch replaces the current Type-specific “parametric witness capability” mechanism with an explicit observation
modality, restores inferred universe polymorphism for bare `Type`, preserves proof-directed universe bounds, makes
`TypeLevel` an actual runtime-capable opaque prelude data type, makes equality universe-polymorphic, records cumulative
lifts in KCore, and standardizes a Kappa-like parseable KCore text format.

The core separation is:

```text
observation mode   controls whether a dependency may be reified as ordinary data
quantity           controls runtime demand and erasure
access mode        controls ordinary versus borrowed access
explicitness       controls explicit versus implicit application
universe level     controls classification
```

These dimensions are independent. In particular:

```text
quantity 0 does not imply parametric observation
parametric observation does not imply runtime erasure
an explicit universe such as Type0 does not imply ordinary observation
```

---

## 1. Diagnostics

### 1.1 Generalize `E_PARAMETRIC_TYPE_PROMOTION`

In §3.1.4, replace the current meaning of `E_PARAMETRIC_TYPE_PROMOTION` with:

```text
* `E_PARAMETRIC_TYPE_PROMOTION` is emitted when an expression carrying `parametric` observation mode is used where an
  `ordinary`-observable value of the same classifier is required.

  This includes:

  * returning a parametric type or type-former witness as an ordinary universe value;
  * storing it in an ordinary field;
  * passing it to an ordinary binder;
  * reifying it as an ordinary static object;
  * selecting ordinary static-object members through it;
  * reflecting or type-casing it without explicit evidence;
  * losing its observation mode through aliasing, projection, pattern matching, partial application, interface
    serialization, KCore transformation, or lowering.

  The diagnostic applies to base type witnesses and higher-kinded parametric witnesses.
```

In family `kappa.type.parametric-promotion`, replace the definition and payload requirements with:

```text
A **parametric static witness** is an expression whose KCore observation mode is `parametric`.

Payload MUST include:

* witness expression;
* witness classifier;
* witness origin;
* actual observation mode, always `parametric`;
* demanded observation mode, always `ordinary`;
* use site;
* operation that demanded ordinary observation;
* quantity, access mode, and explicitness of the relevant binder or field;
* application spine already supplied, when the witness is higher-kinded;
* residual parametric kind after partial application, when applicable;
* whether the failure arose in source, generated syntax, interface loading, KCore verification, or lowering.
```

### 1.2 Add `E_PARAMETRIC_BINDER_DOMAIN`

Add this portable alias in §3.1.4:

```text
E_PARAMETRIC_BINDER_DOMAIN
```

Meaning:

```text
* `E_PARAMETRIC_BINDER_DOMAIN` is emitted when source explicitly requests `parametric` observation for a binder whose
  elaborated domain is not a parametric kind admitted by §11.1.2.3B.
```

Add family:

```text
kappa.type.parametric-binder-domain
```

Payload MUST include:

```text
* binder origin;
* binder domain;
* normalized binder domain;
* inferred universe, when any;
* requested observation mode;
* reason the domain is not a parametric kind;
* nearest valid `ordinary` rendering.
```

### 1.3 Add textual-KCore diagnostics

Add these portable aliases:

```text
E_KCORE_TEXT_INVALID
E_KCORE_TEXT_UNSUPPORTED_VERSION
```

Meanings:

```text
* `E_KCORE_TEXT_INVALID` is emitted when a `.kcore` unit is lexically malformed, syntactically malformed, ill-scoped,
  ill-typed, references unavailable semantic identities, or fails KCore checkpoint verification.

* `E_KCORE_TEXT_UNSUPPORTED_VERSION` is emitted when a KCoreText schema version is well-formed but unsupported by the
  selected implementation.
```

Add families:

```text
kappa.kcore.text-invalid
kappa.kcore.unsupported-version
```

`kappa.kcore.text-invalid` payload MUST include:

```text
* KCoreText schema version, when readable;
* source path;
* source range;
* declaration or node being parsed or checked;
* whether the failure occurred during lexing, parsing, name resolution, scoping, typing, or checkpoint verification;
* violated KCore invariant;
* nearest semantic identity, when available.
```

---

## 2. Surface keywords and binder grammar

### 2.1 Add contextual keywords

In §5.2, add to the contextual-keyword list:

```text
ordinary, parametric
```

Add:

```text
`ordinary` and `parametric` are soft keywords only in binder and field prefixes.

Outside a position that admits a binder observation mode, they may be used as ordinary identifiers.
```

### 2.2 Replace §12.1.1 Shared binder prefixes

Replace the grammar and defaulting text of §12.1.1 with:

```text
<!-- types.functions.shared_binder_prefixes -->
#### 12.1.1 Shared binder prefixes

The following grammar is shared by function binders, lambda binders, record fields, constructor fields, local binders,
implicit binders, trait parameters, effect parameters, and every other source form that admits an explicit binder
prefix.

```text
observationMode ::=
    'ordinary'
  | 'parametric'

quantity ::=
    '0'
  | '1'
  | 'ω'
  | '<=1'
  | '>=1'
  | quantityExpr

borrowMarker ::=
    '&'
  | '&' '[' regionRef ']'

binderPrefix ::=
    observationMode? quantity? borrowMarker?

explicitBinderBody ::=
    binderPrefix? ident ':' type
  | binderPrefix? '_' ':' type
  | binderPrefix? 'this' ':' type
  | binderPrefix? 'this' ident ':' type

binderName ::= ident | '_'

implicitBinderBody ::=
    '@' binderPrefix? binderName ':' type
```

The canonical prefix order is:

```text
observation mode, quantity, borrow marker, binder name, annotation
```

Examples:

```kappa
(parametric 0 A : Type)
(ordinary 0 A : Type)
(ordinary ω A : Type)
(parametric 1 F : (A : Type) -> Type)
(ordinary 1 & x : Buffer)
(@parametric 0 A : Type)
(@ordinary 0 p : Proof)
```

The following are invalid prefix orders:

```kappa
(0 parametric A : Type)
(& ordinary x : A)
(@0 parametric A : Type)
```

`@` marks implicitness and is written before the ordinary binder prefix. It never denotes a quantity or observation mode.

`quantityExpr` is checked in a static-object expression position with expected classifier `Quantity`.

`regionRef` must resolve to a region variable already in scope.

Observation mode, quantity, access mode, and explicitness are independent:

* observation mode controls parametric versus ordinary static observability;
* quantity controls permitted runtime-relevant demand;
* a borrow marker controls borrowed access;
* `@` controls implicit application.

An explicit quantity does not select an observation mode.

An explicit universe such as `Type0` does not select an observation mode.

A `parametric` binder may not carry a borrow marker in Kappa v1. A source form combining `parametric` with `&` or
`&[ρ]` is rejected with `E_PARAMETRIC_BINDER_DOMAIN`.

Default observation mode and quantity:

1. If the binder domain elaborates to a parametric kind under §11.1.2.3B:

   * omitted observation mode defaults to `parametric`;
   * omitted quantity defaults to `0`;
   * an explicit quantity changes only the quantity;
   * an explicit `ordinary` changes only the observation mode.

2. If the binder domain does not elaborate to a parametric kind:

   * omitted observation mode defaults to `ordinary`;
   * an explicit explicit-binder quantity defaults to `ω` when omitted;
   * an implicit-binder quantity follows §16.3 when omitted;
   * explicit `parametric` is rejected in Kappa v1.

Consequently:

```kappa
(A : Type)
```

means approximately:

```kappa
(parametric 0 A : Type ?u)
```

while:

```kappa
(A : Type0)
```

means:

```kappa
(parametric 0 A : Type0)
```

and:

```kappa
(ordinary A : Type)
```

means approximately:

```kappa
(ordinary ω A : Type ?u)
```

The annotation `Type0` fixes a universe level. It does not grant ordinary observation.

A source-written binder whose default is parametric is not silently widened to ordinary observation. If its body requires
ordinary observation, elaboration rejects the use and SHOULD suggest adding `ordinary` at the binder.

A compiler-generated binder introduced by signature inference or implicit declaration-level universalization uses the
least permissive observation mode that typechecks:

* choose `parametric` when every use is parametric;
* choose `ordinary` only when an ordinary-observation use requires it.

The chosen mode is recorded explicitly in KCore and is not reinferred by later phases.

Non-dependent arrow remains sugar:

```kappa
A -> B == (_ : A) -> B
```

The anonymous binder of a non-dependent arrow has ordinary observation mode. Its quantity is the ordinary omitted
quantity for a value binder.
```

### 2.3 Patch local binder prose

Where §9.3 currently says that a quantity-only prefix introduces variables “with ordinary access,” retain the access
statement and add:

```text
Observation mode is selected independently by §12.1.1 from the elaborated annotation and any explicit `ordinary` or
`parametric` keyword.
```

---

## 3. Bare `Type` and hidden declaration universe parameters

### 3.1 Replace §11.1.2.3 Bare `Type`

Replace the subsection completely with:

```text
<!-- types.universes.bare_type -->
##### 11.1.2.3 Bare `Type`

Bare `Type` is universe-polymorphic surface syntax.

Each source occurrence of:

```kappa
Type
```

elaborates initially to:

```text
Type ?u
```

where `?u : TypeLevel` is a fresh universe metavariable unless an expected classifier or surrounding constraint already
determines the level.

The spelling `*` is sugar for the same floating bare-`Type` form.

Explicit universe spellings remain fixed:

```kappa
Type0
Type1
Type u
Type(max u v)
Typeω
```

`Type0` never introduces a universe metavariable.

Two independent bare-`Type` annotations introduce distinct universe metavariables unless ordinary elaboration constraints
equate them.

A grouped annotation shares one metavariable:

```kappa
(A B : Type)
```

Separate annotations are independent initially:

```kappa
(A : Type) (B : Type)
```

Universe typing remains predicative:

```text
Type u : Type (succ u)
```

A compact renderer may omit inferred universe levels. A verbose renderer MUST expose the solved or generalized levels.

Compact:

```kappa
id : (A : Type) -> A -> A
```

Verbose:

```text
id.{u} : (parametric 0 A : Type u) -> A -> A
```

A renderer MUST NOT interpret compact `Type : Type` as self-containment. Verbose output must reveal the distinct
predicative levels.
```

### 3.2 Insert hidden declaration universe parameters

Insert immediately after §11.1.2.3:

```text
<!-- types.universes.declaration_parameters -->
##### 11.1.2.3A Hidden declaration universe parameters

At a declaration generalization boundary, an unsolved universe metavariable that occurs in the declaration's
user-observable type is generalized into a hidden declaration universe parameter.

A hidden declaration universe parameter is part of the semantic declaration telescope.

It is not:

* an ordinary source binder;
* an ordinary Pi over `TypeLevel`;
* a quantity-`0` term argument;
* a runtime argument;
* a first-class value;
* a source-level universe-schema quantifier.

This specification renders hidden declaration universe parameters as:

```text
name.{u, v}
```

The notation is used by verbose diagnostics, interfaces, KCoreText, and tooling. Kappa v1 does not require source syntax
for writing it directly.

Generalization rules:

* Generalize every unsolved universe metavariable that occurs in an exported, stored, reified, interface-visible, or
  otherwise user-observable declaration type.
* Retain and normalize constraints among generalized universe parameters.
* Order parameters by deterministic first occurrence in the fully elaborated declaration type.
* Generalize once per semantic declaration SCC.
* Instantiate declaration universe parameters freshly at every declaration reference before ordinary unification and
  cumulativity.
* Different uses of one declaration may instantiate its universe parameters differently.
* Declaration universe parameters and constraints participate in interface identity, semantic hashing, instance-head
  identity, KCore identity, and tooling output.
* Generalization MUST NOT turn a declaration universe parameter into a term-level `(u : TypeLevel)` binder.

Examples:

```kappa
id : (A : Type) -> A -> A
let id A x = x
```

elaborates schematically to:

```text
id.{u} : (parametric 0 A : Type u) -> A -> A
```

```kappa
const : (A : Type) -> (B : Type) -> A -> B -> A
```

elaborates schematically to:

```text
const.{u, v} :
    (parametric 0 A : Type u) ->
    (parametric 0 B : Type v) ->
    A -> B -> A
```
```

### 3.3 Patch universe inference and defaulting

In §11.1.2.4, replace the bare-`Type` paragraphs with:

```text
Bare `Type` introduces fresh universe metavariables under §11.1.2.3.

Universe metavariables are solved by ordinary universe constraints and definitional equality of admitted level terms.

At a declaration generalization boundary, remaining universe metavariables in the generalized type become hidden
declaration universe parameters under §11.1.2.3A.

A declaration universe parameter is instantiated freshly at every declaration reference.

A first-class term-level binder:

```kappa
(u : TypeLevel) -> T
```

is not interchangeable with declaration universe polymorphism.

Erasing a term-level `TypeLevel` argument does not turn it into a declaration universe parameter and does not supply a
universe ceiling.
```

In §11.1.3, replace the `Universe variables` bullet block with:

```text
Universe variables:

* Every bare `Type` occurrence may introduce a universe metavariable.
* At a declaration generalization boundary, every unsolved universe metavariable appearing in the generalized type is
  generalized into the declaration universe telescope.
* Generalized universe constraints are retained and normalized.
* A universe metavariable not appearing in a user-observable type MAY be solved to the least level satisfying its
  constraints when that solution is deterministic.
* A universe metavariable MUST NOT be defaulted merely to avoid adding a declaration universe parameter.
* A hidden declaration universe parameter MUST NOT be emitted as an ordinary source or KCore term binder.
```

---

## 4. Parametric kinds and observation mode

Replace the current §11.1.2.3A “Parametric type witnesses” with the following subsection, renumbering it to
§11.1.2.3B after the new declaration-parameter subsection.

```text
<!-- types.universes.parametric_observation -->
##### 11.1.2.3B Parametric kinds and observation mode

Kappa tracks quantity and observation mode independently.

Observation modes are:

```text
ordinary
parametric
```

`ordinary` permits every observation otherwise allowed by the value's type, phase, access mode, and available evidence.

`parametric` permits the value to influence typing parametrically but forbids reifying, returning, storing, or passing it
as an ordinary-observable value of the same classifier.

There is one-way observation subsumption:

```text
ordinary -> parametric
```

An ordinary value may be used where a parametric value is expected.

There is no implicit reverse subsumption:

```text
parametric -/-> ordinary
```

Quantity and observation mode are distinct:

* quantity controls runtime demand, copying, dropping, and erasure;
* observation mode controls static observability and reification;
* a parametric value is not erased merely because it is parametric;
* a quantity-`0` value is not automatically parametric.

A **parametric kind** is generated by:

```text
paramKind ::=
    Type u
  | (parametric 0 x : paramKind) -> paramKind
```

Implicit parametric binders are admitted in the same grammar.

Examples:

```kappa
Type
Type3
(parametric 0 A : Type) -> Type
(parametric 0 A : Type) -> (parametric 0 B : Type) -> Type
(parametric 0 F : (parametric 0 A : Type) -> Type) -> Type
```

The following is not a parametric kind in Kappa v1:

```kappa
(n : Nat) -> Type
```

An explicit `parametric` binder whose domain is not a parametric kind is rejected with
`E_PARAMETRIC_BINDER_DOMAIN`.

A value bound parametrically at classifier `K` is a **parametric static witness at K**.

Base example:

```kappa
(parametric 0 A : Type u)
```

Higher-kinded example:

```kappa
(parametric 0 m : (parametric 0 A : Type u) -> Type v)
```

Parametric application propagates structurally.

If:

```text
f :parametric (parametric 0 x : K1) -> K2
```

and `a` validly instantiates `x`, then:

```text
f a :parametric K2[a/x]
```

Partial application preserves the residual parametric kind.

Parametric positions include:

* type expressions;
* arguments to parametric binders;
* parametric fields and constructor arguments;
* trait goals and associated types that preserve the dependency;
* dependent result types;
* aliases, projections, patterns, and applications whose result remains parametric;
* equality propositions whose carrier formation is independently well-formed;
* generated syntax checked under the same rules.

Ordinary-observation positions include:

* returning a type or type former as an ordinary universe value;
* storing it in an ordinary field;
* passing it to an ordinary binder;
* constructing an ordinary static-object facet from it;
* reflection, typecase, or ordinary static-object lookup not justified by explicit evidence.

Trait evidence may provide observations explicitly.

A declaration constrained by `Typeable A`, `Generic A`, or equivalent evidence is parametric in `A` relative to the
evidence it receives. The witness `A` alone does not provide those observations.

Examples:

```kappa
id : (A : Type) -> A -> A
```

uses the default `parametric 0` mode for `A`.

```kappa
bad : (A : Type) -> Type
let bad A = A
```

is rejected with `E_PARAMETRIC_TYPE_PROMOTION`.

```kappa
chooseType : Bool -> Type
let chooseType b = if b then Int else String
```

is accepted. It has no type binder; it returns an ordinary type-code value.

```kappa
arrowCode :
    (ordinary 0 A : Type) ->
    (ordinary 0 B : Type) ->
    Type

let arrowCode A B =
    A -> B
```

is accepted. `A` and `B` are erased at runtime but remain ordinary-observable type-code values statically.

```kappa
type Packed =
    (A : Type, value : A)
```

uses a default parametric field `A` and may project `A` only parametrically.

```kappa
type Structure =
    (ordinary 0 Carrier : Type,
     operation : Carrier -> Carrier)
```

stores an ordinary-observable carrier code.
```

---

## 5. Impredicative parametric formation

In §11.1.2.8, replace the current special-case `0 Type` formation text with:

```text
<!-- types.universes.observation_modal_formation -->
##### Observation-modal dependent products and sums

Kappa and KCore distinguish ordinary and parametric dependent products and sums.

Ordinary Pi formation is predicative:

```text
Γ ⊢ A : Type u
Γ, x :ordinary A ⊢ B : Type v
────────────────────────────────────────────
Γ ⊢ Π[ordinary,q] x : A. B : Type (max u v)
```

The existing universe-ceiling rule applies when `v` depends on `x`.

Parametric Pi formation is impredicative in its domain:

```text
Γ ⊢ A : Type u
Γ, x :parametric A ⊢ B : Type v
────────────────────────────────────────────
Γ ⊢ Π[parametric,q] x : A. B : Type v
```

The domain universe `u` does not raise the product universe.

The body's universe still contributes normally.

The parametric rule is an explicit trusted language rule. It is not derived from quantity zero or runtime erasure.

Examples:

```kappa
(parametric 0 A : Type3) -> Int
```

has classifier `Type` when `Int : Type`.

```kappa
(parametric 0 A : Type3) -> A -> A
```

has classifier `Type3`, because the body contains value types classified by `Type3`.

```kappa
(parametric 0 m : (A : Type) -> Type) ->
(A : Type) ->
m A -> m A
```

has the universe determined by `m A`, not by the classifier of the higher-kinded domain itself.

Ordinary Sigma, record, tuple, package, constructor, and existential fields use the predicative ceiling rule.

Parametric Sigma formation is impredicative in its field domain:

```text
Γ ⊢ A : Type u
Γ, x :parametric A ⊢ B : Type v
────────────────────────────────────────────
Γ ⊢ Σ[parametric,q] x : A. B : Type v
```

The field's own domain universe does not raise the enclosing telescope. Later field types and payloads still contribute
normally.

Examples:

```kappa
(parametric 0 T : Type3, foo : Int)
```

has classifier `Type`.

```kappa
(parametric 0 T : Type3, foo : T)
```

has classifier `Type3`.

Projection and pattern matching preserve observation mode.

The impredicative parametric Pi and Sigma rules are distinct KCore rules. A conforming implementation MUST NOT simulate
them by constructing ordinary Pi or Sigma nodes and omitting selected universe checks.
```

---

## 6. `forall`, implicit generalization, and inferred binders

### 6.1 Replace the opening of §11.3

```text
<!-- types.quantification -->
### 11.3 Universal quantification

`forall` is implicit quantity-`0` dependent-product sugar.

```kappa
forall a. T
```

elaborates as if written:

```kappa
(@parametric 0 a : Type ?u) -> T
```

where `?u` is a fresh bare-`Type` universe metavariable.

```kappa
forall (A : Type0). T
```

elaborates as:

```kappa
(@parametric 0 A : Type0) -> T
```

An explicit mode is respected:

```kappa
forall (ordinary A : Type). T
```

elaborates as:

```kappa
(@ordinary 0 A : Type ?u) -> T
```

For a domain that is not a parametric kind, omitted mode is ordinary:

```kappa
forall (n : Nat). T
```

elaborates as:

```kappa
(@ordinary 0 n : Nat) -> T
```

`forall` does not directly introduce declaration universe parameters. Bare-`Type` metavariables in the completed
declaration type are generalized at the declaration boundary.
```

### 6.2 Replace implicit type-variable generalization

In §11.3.3, replace the current parametric default block with:

```text
When implicit declaration-level universalization introduces a binder whose inferred domain is a parametric kind, the
binder is generalized with:

```text
observation mode = parametric
quantity         = 0
```

unless an ordinary-observation use requires an ordinary binder.

The compiler chooses the least permissive mode that typechecks.

Examples:

```kappa
let id A x = x
```

may infer:

```kappa
id : (A : Type) -> A -> A
```

with verbose elaboration:

```text
id.{u} : (parametric 0 A : Type u) -> A -> A
```

```kappa
trait Functor f =
    map : forall a b. (a -> b) -> f a -> f b
```

infers schematically:

```text
trait Functor.{u,v}
    (parametric 0 f :
        (parametric 0 A : Type u) -> Type v) =
    ...
```

A source-written binder that defaults to parametric is never silently widened. The compiler reports the first ordinary
use and suggests the `ordinary` keyword.
```

---

## 7. Structural mode propagation

### 7.1 Records, tuples, packages, and existentials

Replace procedural “preserve parametric capability” wording with:

```text
Every KCore field records an explicit observation mode.

Projection preserves the field's observation mode.

Repacking a parametric projection into another parametric field is permitted.

Using a parametric projection where an ordinary-observable value is required is rejected with
`E_PARAMETRIC_TYPE_PROMOTION`.

An omitted field mode follows §12.1.1 from the elaborated field annotation.
```

### 7.2 Data constructors and constructor-size checking

In §10.4.1, replace the narrow `0 Type ρ` exception with:

```text
A constructor-local field whose selected observation mode is `parametric` does not contribute the classifier of its own
domain merely by storing the parametric witness.

Every later constructor field is checked normally.

Generated constructor functions, accessors, projections, matchers, pattern binders, metadata, interfaces, and KCore
nodes preserve the field observation mode.

A generated operation that changes a parametric field to ordinary observation is rejected with
`E_PARAMETRIC_TYPE_PROMOTION`.

Examples:

```kappa
data Box : Type =
    Box (parametric 0 T : Type3) (foo : Int)
```

is accepted.

```kappa
data LargeBox : Type3 =
    LargeBox (parametric 0 T : Type3) (foo : T)
```

is accepted at `Type3` because the payload field `foo : T` contributes level `3`.

```kappa
data BadBox : Type =
    BadBox (parametric 0 T : Type3) (foo : T)
```

is rejected because the payload is too large for `Type`.
```

### 7.3 Pattern matching

Replace §17.1.7A with:

```text
#### 17.1.7A Observation modes in constructor patterns

A pattern binder inherits the observation mode of the constructor field it binds.

A parametric branch binder may be used in types and other parametric positions.

It may not be returned, stored, reflected, or passed as an ordinary-observable value.

Pattern matching does not require a special unpack form. It preserves the mode structurally.

Example:

```kappa
data Some : Type =
    Some (A : Type) (value : A)

repack : Some -> Some
let repack x =
    match x
    case Some A value ->
        Some A value
```

is accepted because the default mode of `A : Type` is parametric.

```kappa
bad : Some -> Type
let bad x =
    match x
    case Some A value ->
        A
```

is rejected with `E_PARAMETRIC_TYPE_PROMOTION`.
```

### 7.4 Static-object facets and aliases

In §7.6.1, replace Type-specific capability language with:

```text
A declaration may expose an ordinary static-object facet, a parametric static facet, or both when each is independently
well-typed.

A type alias depending on parametric inputs may expose a parametric higher-kinded facet suitable for another parametric
binder without exposing an ordinary type-code function.

Example:

```kappa
type Id A = A
```

may instantiate:

```kappa
(parametric 0 f : (A : Type) -> Type)
```

but does not thereby become an ordinary-observable function returning type codes.

Rebinding, projection, storage, imports, exports, and interface serialization preserve the facet observation mode.
```

### 7.5 Trait evidence

In §14, replace references to “parametric type-witness capability rules” with “parametric observation-mode rules.”

Add:

```text
Trait search may form goals mentioning parametric values.

Behavior may depend on explicit or implicit evidence such as `Typeable A`, `Generic A`, or `Show A`.

That dependence is ordinary dictionary passing. It does not convert the witness `A` itself to ordinary observation.
```

---

## 8. Higher-kinded parameters and `Monad`

Insert near the higher-kinded trait declarations:

```text
A higher-kinded binder whose domain is a parametric kind defaults to `parametric 0`.

Canonical examples:

```kappa
trait Functor
    (parametric 0 f : (A : Type) -> Type) =

    map :
        forall a b.
        (a -> b) ->
        f a ->
        f b

trait Applicative f => Monad
    (parametric 0 f : (A : Type) -> Type) =

    pure :
        forall a.
        a -> f a

    bind :
        forall a b.
        f a ->
        (a -> f b) ->
        f b
```

The inner binder `(A : Type)` also defaults to `parametric 0`.

A higher-kinded parametric argument may be:

* a named type constructor;
* a partial application;
* a transparent alias;
* a type lambda;
* a projected parametric type-former field.

Examples include:

```kappa
Option
List
Result Error
State Store
Id
```

A type former that demands an ordinary type-code argument does not match a parametric kind:

```kappa
G : (ordinary 0 A : Type) -> Type
```

Instance-head matching for higher-kinded arguments uses definitional equality after permitted transparent alias
unfolding, beta reduction, and canonical type-constructor normalization.

Instance resolution does not use function extensionality to compare arbitrary type-former arguments.
```

Apply the same parameter-mode correction to:

```text
Functor
Applicative
Monad
Alternative
MonadFinally
MonadError
MonadResource
MonadRef
Releasable
Foldable
Traversable
Filterable
FilterMap
```

and every analogous trait whose carrier domain is a parametric kind.

---

## 9. `TypeLevel` as an actual runtime-capable prelude type

### 9.1 Replace the opening of §11.1.1

```text
<!-- types.universes.typelevel_data -->
#### 11.1.1 `TypeLevel`

`TypeLevel` is an actual opaque algebraic data type declared by the standard prelude.

The canonical declaration is:

```kappa
opaque data TypeLevel : Type0 =
    private Level
        (omegaCoefficient : Nat)
        (finiteRemainder  : Nat)
```

The constructor is private to `std.typelevel`.

The value `Level c n` denotes the level `ω·c + n`.

Kappa v1 therefore represents levels below `ω²`.

The public representation is opaque. Programs outside `std.typelevel` cannot construct or pattern-match `Level`
directly.

`TypeLevel` is runtime-capable ordinary data:

* an ordinary `u : TypeLevel` may be stored, returned, captured, compared, or passed to runtime code;
* `0 u : TypeLevel` is erased by quantity;
* a meta-phase `TypeLevel` value is erased by phase;
* use of `u` as a universe index is static and does not itself require runtime representation;
* one source binder may have both static index uses and ordinary runtime uses.

Compiler universe metavariables and solver constraints are compiler metadata over `TypeLevel` terms. They are not
runtime inhabitants of `TypeLevel`.
```

### 9.2 Replace intrinsic-only operations

Replace the intrinsic-head semantics of §11.1.2.2 with:

```text
The canonical `std.typelevel` module defines actual ordinary opaque declarations:

```kappa
opaque let zero : TypeLevel = ...
opaque let one : TypeLevel = ...
opaque let omega : TypeLevel = ...
opaque let succ (x : TypeLevel) : TypeLevel = ...
opaque let add (x : TypeLevel) (y : TypeLevel) : TypeLevel = ...
opaque let compare (x : TypeLevel) (y : TypeLevel) : Ordering = ...
opaque let max (x : TypeLevel) (y : TypeLevel) : TypeLevel = ...
```

and actual standard instances:

```text
Eq TypeLevel
Ord TypeLevel
Zero TypeLevel
One TypeLevel
FromInteger TypeLevel
Successor TypeLevel
Add TypeLevel
Max TypeLevel
```

The public operations are opaque to ordinary delta reduction outside `std.typelevel`.

The universe solver has a certified normalization bridge for the resolved semantic identities of these exact
declarations and instances.

The bridge may normalize them while:

* checking an index of `Type`;
* comparing universe indices;
* solving universe inequalities;
* checking cumulativity;
* checking universe ceilings;
* checking constructor universe-size obligations.

Recognition is by resolved semantic identity, never by source spelling.

A compiler may lower a standard operation to an intrinsic, constant-fold it, or compile its ordinary body. Runtime,
compile-time, and solver behavior MUST be extensionally equivalent.

A runtime-reachable intrinsic application must have a backend lowering or be replaced by the ordinary implementation.
A solver-only intrinsic must not survive to KBackendIR.
```

### 9.3 Patch erasure and backend legality

Remove `TypeLevel` from every blanket list of intrinsically compile-time-only or always-runtime-erased types.

Insert in §11.1.6:

```text
`TypeLevel` is not intrinsically compile-time-only.

Erasure is justified by quantity, phase, erased-index status, ambient demand, or ordinary dead-code elimination.

Compiler ownership of a declaration or instance is not an erasure justification.
```

Insert in the trait evidence section:

```text
Compiler ownership, canonical instance identity, coherence, and intrinsic introduction do not imply runtime erasure.

A method-bearing dictionary may be erased only after every runtime-relevant observation has been specialized,
devirtualized, inlined, or otherwise discharged.

Different members of one dictionary may have different runtime relevance. For example, `Ord TypeLevel.compare` may be
runtime-relevant while law proofs are erased.
```

Replace blanket KBackendIR rejection of `TypeLevel` with:

```text
KBackendIR may contain runtime-relevant `TypeLevel` values and operations.

KBackendIR must not contain universe metavariables, solver constraints, solver proof state, erased quantity-`0`
occurrences, or `Type u` as a runtime universe object.
```

---

## 10. Proof-directed universe bounds

Keep ordinary erased evidence syntax:

```kappa
(i : TypeLevel) ->
(@0 p : i < κ) ->
Type i
```

No special bounded-binder syntax is added.

Add the following normative conditions to the universe solver section:

```text
A level-comparison proof may affect universe formation only through the designated universe-proof interface.

The active universe-assumption context used for classification must be satisfiable.

Logical explosion from an arbitrary inconsistent proposition context does not establish universe inequalities.

A strict cycle such as `i < i`, directly or transitively, may not justify self-containment.

Every KCore universe-ceiling derivation records the proof or solver certificate that supplied the bound.

Substitution replaces the level term and its bound evidence together.

Checkpoint verification rechecks the substituted universe derivation.

Subject reduction under local level evidence is a required metatheory obligation for Kappa's trusted core.
```

---

## 11. Universe-polymorphic equality and standard declarations

### 11.1 Replace propositional equality

Replace the standard equality declaration with:

```kappa
data (=)
    (@A : Type)
    (0 x : A)
    (0 y : A)
    : Type =

    refl : x = x
```

The carrier binder defaults to `@parametric 0 A : Type ?u`.

The endpoints are quantity-`0` ordinary value binders. They are erased but are not parametric-kind binders.

The declaration generalizes schematically to:

```text
(=).{u} :
    (@parametric 0 A : Type u) ->
    (ordinary 0 x : A) ->
    (ordinary 0 y : A) ->
    Type u
```

If `a,b : Type u`, then equality between the types instantiates the carrier with `Type u` and therefore lives in
`Type (succ u)` by ordinary predicative universe typing.

No equality-specific universe exception is permitted.
```

### 11.2 Generalize `Dec`, containers, effects, and eliminators

Replace fixed-universe declarations with universe-generalized declarations wherever their types permit it.

At minimum this applies to:

```text
Dec
Option
List
Result
IO
Eff
Eq
Ord
IsProp
IsSet
pathInd
subst
sameDynRep
checkedCastWith
```

`Dec` should be source-written as:

```kappa
data Dec (P : Type) : Type =
    Yes (proof : P)
    No  (refute : P -> False)
```

with hidden declaration universe parameters inferred.

The required dynamic representation signature remains ordinary equality:

```kappa
expect term sameDynRep :
    forall a b.
    DynRep a ->
    DynRep b ->
    Dec (a = b)
```

There is no special `TypeEq` family and no equality kind-check bypass.

A signature such as:

```kappa
compareTypes :
    (a b : Type) ->
    IO Error (a = b)
```

is well-formed by ordinary hidden universe generalization of equality and `IO`.
```

---

## 12. KCore modality, hidden universes, and lifts

### 12.1 Insert KCore observation modes

Insert near the opening of §30.2:

```text
<!-- compiler.kcore.observation_modes -->
#### 30.2.0 Observation modes

Every KCore binder and every dependent field records independently:

```text
observationMode : ObservationMode
quantity        : Quantity
accessMode      : AccessMode
explicitness    : BinderExplicitness
```

where:

```text
ObservationMode ::= ordinary | parametric
```

KCore uses distinct observation judgments:

```text
Γ ⊢ordinary   t : A
Γ ⊢parametric t : A
```

Every ordinary value is admissible parametrically.

A parametric value is not admissible ordinarily without an explicit language rule or explicit evidence that constructs
an ordinary value.

Variable, application, projection, pattern, alias, package, constructor, trait, and static-object rules propagate
observation mode structurally.

KCore does not use frontend side tables to reconstruct lost parametricity.

Pi and Sigma nodes carry mode explicitly:

```text
Pi   [mode, quantity, access, explicitness] x : A. B
Sigma[mode, quantity, access, explicitness] x : A. B
```

The impredicative formation rules apply only to nodes whose mode is `parametric`.

Observation mode participates in:

* KCore typing;
* interfaces;
* semantic hashing;
* normalized instance heads;
* KCoreText;
* stage dumps;
* checkpoint verification.

Observation mode is not itself a runtime field.

Erasure still requires an ordinary erasure justification.
```

Replace `ParamTypeWitness`, `ParamStaticWitness`, and capability-side-table language with explicit KCore observation
mode.

### 12.2 Hidden declaration universe telescopes

Add:

```text
A KCore declaration records a hidden universe telescope separately from its term telescope.

```text
DeclarationUniverseTelescope =
    (parameters  : List UniverseParameter,
     constraints : List UniverseConstraint)
```

Universe parameters are instantiated at global-reference sites.

They are not local variables, term binders, closure fields, or runtime arguments.
```

### 12.3 Explicit cumulative lifts

Insert after §30.2.1:

```text
<!-- compiler.kcore.universe_lifts -->
#### 30.2.1A Explicit universe lifts

Surface cumulativity is implicit.

KCore records every cumulative subsumption explicitly:

```text
universeLift [from = u, to = v, evidence = p] t
```

Typing rule:

```text
Γ ⊢ t : A
Γ ⊢ A : Type u
Γ ⊢ p : u <= v
────────────────────────────────────────────
Γ ⊢ universeLift[u,v,p] t : A at classifier Type v
```

The node changes only the classifier at which `A` is used.

Rules:

* identity lifts normalize away;
* nested lifts compose canonically;
* composition preserves evidence dependencies;
* lifts preserve observation mode;
* lifts are runtime representation identity and erase before KBackendIR;
* semantic hashes include canonical source level, target level, and evidence identity;
* checkpoint verification rejects missing, ill-scoped, or invalid lift evidence.
```

---

## 13. Canonical KCoreText

Insert after §30.2.0:

```text
<!-- compiler.kcore.text_format -->
#### 30.2.0A Canonical KCoreText

A conforming implementation MUST provide a canonical, parseable, human-readable KCore serialization named
`KCoreText`.

KCoreText is deliberately Kappa-like, but it is not Kappa source syntax.

It uses braces and semicolons. Indentation is ignored.

It performs no overload resolution, implicit insertion, universe inference, modality inference, quantity defaulting,
name lookup by source spelling, or cumulative-lift insertion.

Every such fact is explicit in the file.

A `.kcore` unit is accepted only after parsing and ordinary KCore checkpoint verification.

##### Header and modules

```text
kcoreFile ::=
    'kcore' integer ';'
    kcoreModule+

kcoreModule ::=
    'module' globalRef moduleMetadata? '{' kcoreDecl* '}'

moduleMetadata ::=
    '[' metadataEntry (',' metadataEntry)* ']'

metadataEntry ::=
    identifier '=' stringLiteral
```

Required metadata includes:

```text
languageVersion
compilerInterfaceVersion
sourceModuleIdentity
```

##### Identities

```text
globalRef   ::= '@' qualifiedName '#' stableId
localRef    ::= '%' identifier '#' integer
universeRef ::= '^' identifier '#' integer
stableId    ::= hexDigit+
```

The readable name is present for humans. The stable identity is authoritative.

Canonical output uses fully qualified global names and deterministic local numbering.

##### Declarations

```text
kcoreDecl ::=
    universeDecl
  | defDecl
  | axiomDecl
  | dataDecl
  | genericDecl

universeDecl ::=
    'universe' universeRef ';'

defDecl ::=
    'def' observationMode globalRef universeTelescope? ':' term constraintBlock? '{'
        'body' '=' term ';'
    '}'

axiomDecl ::=
    'axiom' observationMode globalRef universeTelescope? ':' term constraintBlock? ';'

dataDecl ::=
    'data' globalRef universeTelescope? binder* ':' term constraintBlock? '{'
        constructorDecl*
    '}'

constructorDecl ::=
    'constructor' globalRef ':' term ';'

universeTelescope ::=
    '.{' universeRef (',' universeRef)* '}'

constraintBlock ::=
    'where' '{' universeConstraint* '}'

universeConstraint ::=
    level '<=' level ';'
  | level '<' level ';'
```

##### Binders

```text
binder ::=
    '(' observationMode formationMode quantity explicitness accessMode localRef ':' term ')'

observationMode ::= 'ordinary' | 'parametric'
formationMode   ::= 'ordinary' | 'parametric'
explicitness    ::= 'explicit' | 'implicit'
accessMode      ::= 'value' | 'borrow' | 'borrow[' regionRef ']'
quantity        ::= '0' | '1' | 'omega' | 'affine' | 'relevant' | 'quantity-term(' term ')'
regionRef       ::= localRef | globalRef
fieldRef        ::= '@field:' qualifiedName '#' stableId
```

Every declaration observation mode and every binder attribute, including formation mode, is mandatory in canonical output.

##### Terms

```text
term ::=
    localRef
  | globalRef universeInstantiation?
  | 'Type' level
  | '(' binder '->' term ')'
  | 'sigma' binder '{' term '}'
  | 'lambda' binder '{' term '}'
  | 'apply' term '(' argumentList? ')'
  | 'block' '{' blockItem* term '}'
  | 'case' term ':' term '{' caseAlt* '}'
  | 'construct' globalRef '(' argumentList? ')'
  | 'project' fieldRef term
  | 'lift' '[' level '<=' level 'by' evidenceRef ']' term
  | 'ascribe' term ':' term
  | genericTerm

universeInstantiation ::=
    '.{' level (',' level)* '}'

argumentList ::=
    argument (',' argument)*

argument ::=
    'explicit' term
  | 'implicit' term

blockItem ::=
    'let' binder '=' term ';'
  | 'letrec' '{' localDef+ '}'

localDef ::=
    'def' observationMode localRef ':' term '{' 'body' '=' term ';' '}'

caseAlt ::=
    'case' globalRef binder* '{' term '}'
  | 'default' '{' term '}'
```

##### Generic extension nodes

Every KCore node without a standardized specialized spelling is represented by:

```text
genericDecl ::=
    'decl-node' stringLiteral '{' namedValue* '}'

genericTerm ::=
    'term-node' stringLiteral '{' namedValue* '}'

namedValue ::=
    identifier '=' coreValue ';'

coreValue ::=
    term
  | level
  | quantity
  | observationMode
  | explicitness
  | accessMode
  | globalRef
  | localRef
  | stringLiteral
  | integer
  | '[' (coreValue (',' coreValue)*)? ']'
```

Unknown portable node tags are rejected unless the file header declares a supported extension owning that tag.

##### Levels and evidence

```text
level ::=
    integer
  | globalRef
  | universeRef
  | 'succ' '(' level ')'
  | 'max' '(' level ',' level ')'
  | 'add' '(' level ',' level ')'
  | 'level-term' '(' term ')'

evidenceRef ::=
    localRef
  | globalRef
  | 'solver' '(' stableId ')'
```

##### Canonicalization

Canonical KCoreText obeys all of the following:

* braces, commas, colons, and semicolons are emitted exactly as prescribed;
* indentation is two spaces but is semantically irrelevant;
* declarations are ordered by semantic dependency, then canonical global identity;
* local binders are numbered deterministically in preorder;
* universe parameters are numbered independently and appear only in declaration universe telescopes;
* all quantities, modes, explicitness values, access modes, universe instantiations, and lifts are explicit;
* resolved references include semantic identities;
* aliases remain only where KCore itself retains them;
* opaque or unavailable bodies are represented by an explicit `body-unavailable` generic node;
* canonical output contains no comments;
* a parser MAY accept line comments in hand-authored test input;
* printing a parsed and verified canonical unit produces byte-identical canonical text modulo LF line endings.

##### Example

```kcore
kcore 1;

module @sample.identity#9af2 [
  languageVersion = "kappa-v1",
  compilerInterfaceVersion = "1",
  sourceModuleIdentity = "sample.identity"
] {
  def ordinary @sample.identity.id#31ce .{^u#0} :
    ((parametric parametric 0 explicit value %A#0 : Type ^u#0) ->
      ((ordinary ordinary omega explicit value %x#1 : %A#0) -> %A#0))
  {
    body =
      lambda (parametric parametric 0 explicit value %A#0 : Type ^u#0) {
        lambda (ordinary ordinary omega explicit value %x#1 : %A#0) {
          %x#1
        }
      };
  }
}
```

##### Verification and round trip

For every accepted KCore unit `C`:

```text
parse(printCanonical(C)) ≡α C
check(parse(printCanonical(C))) = accepted
semanticHash(parse(printCanonical(C))) = semanticHash(C)
printCanonical(parse(printCanonical(C))) = printCanonical(C)
```

Parsing does not trust the input. Checkpoint verification is mandatory.

Malformed syntax uses `E_KCORE_TEXT_INVALID`.

A well-formed but unsupported schema version uses `E_KCORE_TEXT_UNSUPPORTED_VERSION`.
```

---

## 14. Stage dumps and test harness integration

### 14.1 Chapter 34

Keep `json` and `sexpr` as general observability formats.

Add:

```text
The KCore checkpoint additionally MUST support canonical `kcore` format under §30.2.0A.

`kcore` is a round-trippable core language. `json` and `sexpr` remain general stage-dump schemas and are not required to
round-trip through the KCoreText parser.
```

### 14.2 Appendix T configuration

In §T.4 add:

```text
dumpFormat kcore
canonicalDumps
```

Rules:

```text
`dumpFormat kcore` is valid only for a KCore stage dump.

`canonicalDumps` requests deterministic alpha-renaming, semantic ordering, and omission of presentation-only unstable
identifiers without removing semantic information.
```

Add portable capability:

```text
kcoreText
```

### 14.3 Appendix T assertions

In the stage-dump assertion subsection, add:

```text
assertStageDumpRoundTrips <checkpoint>
assertKCoreParses <path>
assertKCoreRoundTrips <path>
assertKCoreRejects <path> <diagnostic-code>
```

Rules:

```text
* `assertStageDumpRoundTrips KCore` requests canonical textual KCore, parses it, verifies it, serializes it again, and
  succeeds iff the canonical serializations are equal.

* `assertKCoreParses path` succeeds iff the `.kcore` file parses and passes KCore checkpoint verification.

* `assertKCoreRoundTrips path` additionally requires canonical parse-print-parse stability and semantic-hash stability.

* `assertKCoreRejects path code` succeeds iff the file parses as KCoreText and checkpoint verification rejects it with
  the requested diagnostic code.

* A parser failure satisfies `assertKCoreRejects` only when `code` is `E_KCORE_TEXT_INVALID` or
  `E_KCORE_TEXT_UNSUPPORTED_VERSION` as appropriate.

* A `.kcore` suffix on `assertStageDump <checkpoint> equals <path>` selects KCoreText for the KCore checkpoint.
```

---

## 15. Required adversarial invariant

Insert near the end of §11.1 or in KCore verification:

```text
<!-- types.universes.hurkens_barrier -->
##### Hurkens/Girard barrier

The parametric modality permits impredicative abstraction and instantiation but forbids reifying a result that depends
parametrically on a universe argument as an ordinary universe value.

The ordinary route remains predicative.

Therefore a direct Hurkens/Girard encoding must fail in one of two places:

* the parametric encoding fails when it attempts parametric-to-ordinary promotion; or
* the ordinary encoding fails a predicative universe-formation or self-containment obligation.

The standard conformance suite includes both minimal barriers and a larger Hurkens-style attempted encoding.

A negative test is not a consistency proof. It is a required adversarial regression test identifying the intended
blocking obligation.
```

---

## 16. Global replacements

Apply these normative replacements across the specification.

### 16.1 Binder wording

Replace procedural phrases such as:

```text
preserves parametric type-witness capability
```

with:

```text
preserves KCore observation mode
```

Replace:

```text
ordinary type-code value / parametric type witness
```

with the generalized terms:

```text
ordinary static value / parametric static witness
```

when the rule applies to higher-kinded values as well as base types.

### 16.2 Standard trait parameters

Rewrite standard higher-kinded declarations to show `parametric` explicitly in normative canonical forms.

Compact source examples may omit the keyword when demonstrating the default.

### 16.3 Equality

Replace ordinary endpoint binders:

```kappa
(x : A) (y : A)
```

with quantity-`0` endpoints:

```kappa
(0 x : A) (0 y : A)
```

Do not mark value endpoints `parametric` merely because they erase.

### 16.4 TypeLevel

Remove statements that:

```text
TypeLevel is intrinsically compile-time-only
TypeLevel has no runtime representation
all TypeLevel evidence is erased because it is compiler-owned
```

Replace them with the runtime-capable and use-sensitive rules in §9 of this patch.

### 16.5 Tooling

Update refactoring and signature-rendering rules so they preserve and expose observation mode independently from
quantity.

Add `make parametric` and `make ordinary` to the standard binder refactorings.

---

## 17. Summary invariant

Insert this boxed summary after the modal formation rules:

```text
Kappa observation and universe invariant:

1. Bare `Type` introduces a fresh universe metavariable.

2. Remaining universe metavariables generalize into hidden declaration universe parameters, never ordinary term Pis.

3. Every KCore binder and dependent field records observation mode and quantity independently.

4. Omitted mode on a parametric-kind binder defaults to `parametric`; omitted quantity then defaults to `0`.

5. Omitted mode on any other binder defaults to `ordinary`.

6. `Type0` fixes the level but does not change the mode.

7. Ordinary values may instantiate parametric binders.

8. Parametric values do not implicitly become ordinary values.

9. Parametric Pi and Sigma formation is impredicative in the domain.

10. Ordinary Pi and Sigma formation remains predicative.

11. Equality is universe-polymorphic and has erased endpoints; it has no special universe exception.

12. Cumulative subsumption is explicit in KCore.

13. `TypeLevel` is real opaque runtime-capable prelude data; compiler normalization is a certified semantic bridge.

14. Proof-directed universe bounds remain explicit evidence and are rechecked after substitution.

15. KCoreText is parseable, round-trippable, independently checkable, and fully explicit.
```
