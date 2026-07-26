# Kappa parametric packages, universe schemas, principal universe inference, and KCore completion patch

**Patch base:** `Spec(97).md`

This patch resolves the remaining contradictions after introducing independent `ordinary` / `parametric` observation modes.
It makes the following decisions normative:

```text
* unbounded packages of parametric type witnesses are legal;
* unbounded packages or functions of ordinary type codes remain illegal;
* declaration universe schemas have explicit optional surface syntax;
* equality is an ordinary user-definable universe-schema declaration;
* universe inference computes a deterministic principal least solution where one exists;
* local declarations may universe-generalize and serialize their local universe telescopes;
* TypeLevel has a complete ordinary prelude algebra;
* inconsistent level assumptions are rejected deterministically;
* KCore observation checking is an independently checkable dependency calculus;
* KCoreText is completed so every global use, local schema, certificate, and extension is explicit.
```

The patch deliberately keeps observation mode and universe formation separate:

```text
ordinary / parametric
    controls whether a value may be observed or reified ordinarily

ordinary / parametric Pi or Sigma formation
    controls the universe contribution of the binder domain

quantity
    controls demand and erasure
```

A parametric type field may therefore be impredicatively packaged even when its universe level is an ordinary first-class
`TypeLevel` value. This is the intended semantic commitment of this revision.

---

## 1. Diagnostics

### 1.1 Remove `E_PARAMETRIC_BINDER_DOMAIN`

Delete portable alias:

```text
E_PARAMETRIC_BINDER_DOMAIN
```

Delete diagnostic family:

```text
kappa.type.parametric-binder-domain
```

Explicit `parametric` observation is legal for every well-formed binder domain. Parametric observation does not by itself
select impredicative formation. The latter is selected by the Pi or Sigma node's formation rule.

### 1.2 Add universe-schema and principal-inference diagnostics

Add portable aliases:

```text
E_UNIVERSE_SCHEMA_ARITY_MISMATCH
E_UNIVERSE_SCHEMA_SCOPE
E_UNIVERSE_NO_PRINCIPAL_SOLUTION
E_KCORE_LEVEL_CERTIFICATE_INVALID
```

Meanings:

```text
* `E_UNIVERSE_SCHEMA_ARITY_MISMATCH` is emitted when an explicit universe instantiation supplies the wrong number of
  arguments for a declaration universe schema.

* `E_UNIVERSE_SCHEMA_SCOPE` is emitted when a declaration-universe parameter is used in an ordinary runtime position,
  captured as a term value, or otherwise escapes the static universe-expression positions admitted by §11.1.2.3A.

* `E_UNIVERSE_NO_PRINCIPAL_SOLUTION` is emitted when declaration universe inference has valid solutions but no unique
  least normalized solution under §11.1.2.4A. The declaration requires an explicit universe schema or a more precise
  result-classifier annotation.

* `E_KCORE_LEVEL_CERTIFICATE_INVALID` is emitted when a KCoreText level certificate is malformed, references unavailable
  assumptions, proves a different constraint, or fails the independent certificate checker.
```

Add families:

```text
kappa.universe.schema-arity
kappa.universe.schema-scope
kappa.universe.no-principal-solution
kappa.kcore.level-certificate-invalid
```

The `kappa.universe.no-principal-solution` payload MUST include:

```text
* declaration identity;
* declaration SCC identity;
* unresolved universe metavariables;
* normalized lower and upper bounds for each metavariable;
* candidate incomparable minimal solutions;
* source origins that introduced the relevant metas and constraints;
* whether an explicit universe schema was present;
* a source rendering of the smallest explicit schema or result annotation known to repair the declaration.
```

### 1.3 Narrow `E_UNIVERSE_UNBOUNDED_TELESCOPE`

Replace its meaning with:

```text
* `E_UNIVERSE_UNBOUNDED_TELESCOPE` is emitted when an ordinary-observation Pi, Sigma, existential, record, tuple,
  package, constructor telescope, module signature, or equivalent dependent telescope contains an ordinary type-code
  component whose universe has no ceiling independent of the variables introduced by that telescope.

  A parametric type-witness field does not by itself trigger this diagnostic. Later ordinary payload fields whose types
  depend on that witness remain subject to the ordinary ceiling rule.
```

### 1.4 Deterministic inconsistent-level diagnostics

Replace every implementation-choice clause for inconsistent recognized level assumptions with:

```text
If adding a recognized level-comparison proof binder makes the active level-assumption context inconsistent, the binder
is rejected.

A direct or transitive strict cycle, including `i < i`, `i < j` with `j <= i`, or any normalized equivalent, is rejected
with:

    E_UNIVERSE_SELF_CONTAINMENT

Any other inconsistent recognized level-assumption set is rejected with:

    E_UNIVERSE_CONSTRAINT_UNSATISFIABLE

A conforming implementation MUST NOT retain an inconsistent recognized comparison merely as an ordinary proposition and
continue universe checking. This rule is deterministic across implementations.
```

---

## 2. Surface declaration universe schemas

Insert after §11.1.2.3A.

```text
<!-- types.universes.explicit_declaration_schemas -->
##### 11.1.2.3A.1 Explicit declaration universe schemas

A declaration may expose its declaration universe telescope explicitly.

Surface grammar:

```text
universeSchema ::=
    '.{' universeSchemaParam (',' universeSchemaParam)* '}'

universeSchemaParam ::=
    ident

universeInstantiation ::=
    '.{' levelExpr (',' levelExpr)* '}'
```

The declaration schema appears immediately after the declared name and before ordinary term parameters.

Examples:

```kappa
data Box.{u} (A : Type u) : Type u =
    Box (value : A)

data (=).{u}
    (@parametric 0 A : Type u)
    (parametric 0 x : A)
    (parametric 0 y : A)
    : Type u =

    refl : x = x

type Endo.{u} (A : Type u) : Type u =
    A -> A

trait Functor.{u, v}
    (parametric 0 F : (A : Type u) -> Type v) =
    ...
```

A declaration-universe parameter:

* is rigid within the declaration;
* is not an ordinary `TypeLevel` term binder;
* is not a runtime argument;
* is not captured by closures;
* may appear in `Type u`, `succ u`, `max u v`, standard `TypeLevel` arithmetic used in universe expressions, and
  recognized erased level-comparison propositions;
* may appear in explicit cumulative-lift evidence;
* participates in declaration interface identity, semantic hashing, KCore identity, and instance-head identity.

A declaration-universe parameter may not be:

* returned as a `TypeLevel` value;
* stored in an ordinary record or constructor field;
* passed to an ordinary runtime `TypeLevel` binder;
* pattern matched;
* reflected as runtime data.

Such a use is rejected with `E_UNIVERSE_SCHEMA_SCOPE`.

If a declaration has an explicit universe schema, the schema is complete. Every unsolved universe metavariable that
would otherwise need declaration-level generalization must be solved from the explicit schema and generated constraints.
The implementation MUST NOT silently append hidden parameters.

If a declaration omits the schema, hidden declaration universe inference remains available under §11.1.2.4A.

At a reference site, an explicit instantiation supplies one level expression per schema parameter:

```kappa
Box.{0} Int
Endo.{3} T
```

If the instantiation is omitted, elaboration creates fresh universe metavariables and solves them by ordinary expected
classifier, unification, and cumulativity constraints.

An explicit instantiation with the wrong arity is rejected with `E_UNIVERSE_SCHEMA_ARITY_MISMATCH`.

Declaration universe parameters are alpha-bound. Their source names do not affect interface or semantic identity; their
order and normalized constraints do.

Constraints among schema parameters are inferred from the declaration signature and body and are retained in the
interface. Kappa v1 introduces no second surface syntax for declaration-schema constraints.
```

### 2.1 Extend declaration grammar

Apply `universeSchema?` immediately after the declared name in every declaration form that may introduce a semantic
object:

```text
term signature
definition
type alias
data declaration
trait declaration
instance declaration when the instance itself generalizes levels
effect declaration
projection declaration
module-signature member
local function or local type declaration
```

At minimum, amend the relevant productions schematically to:

```text
dataDecl  ::= modifiers? 'data' dataName universeSchema? dataParam* ':' type ...
typeDecl  ::= modifiers? 'type' typeName universeSchema? typeParam* ...
traitDecl ::= modifiers? 'trait' traitName universeSchema? traitParam* ...
effectDecl ::= modifiers? 'effect' effectName universeSchema? effectParam* ...
termSig   ::= termName universeSchema? ':' type
termDef   ::= 'let' termName universeSchema? binder* ...
```

The signature and definition of one declaration MUST expose alpha-equivalent universe schemas.

---

## 3. Principal universe inference

Insert after §11.1.2.4.

```text
<!-- types.universes.principal_inference -->
##### 11.1.2.4A Principal universe inference

Universe inference computes the least normalized universe solution justified by generated constraints whenever such a
solution exists.

The algorithm is applied once per semantic declaration SCC, including a local declaration SCC.

Inputs:

```text
* rigid outer declaration-universe parameters;
* rigid explicit universe-schema parameters of the SCC;
* fresh universe metavariables introduced by bare `Type` and elaboration;
* generated equality and ordering constraints;
* explicit result-classifier annotations;
* active level assumptions whose contexts are satisfiable.
```

Universe metavariables have one of two inference roles:

```text
generalizable
    introduced in a parameter, field, associated member, or other user-observable polymorphic position;

minimizable
    introduced only as a result classifier, the classifier of a declaration itself, or another position whose least
    admissible universe is semantically preferred.
```

A metavariable that occurs in both roles is generalizable unless constraints uniquely determine it.

Procedure:

1. Normalize all level expressions through the certified standard `TypeLevel` bridge.
2. Compute lower and upper bounds for every metavariable.
3. Solve every minimizable metavariable to the unique least normalized expression satisfying its bounds.
4. Solve any generalizable metavariable uniquely determined by equality or matching lower and upper bounds.
5. Generalize every remaining generalizable metavariable into the declaration universe telescope, retaining normalized
   constraints among generalized parameters.
6. Reject any remaining metavariable that is neither solved nor legally generalizable.

A least solution is principal when every other valid solution is greater than or equal to it pointwise after
instantiation of generalized parameters.

If several incomparable minimal solutions exist, or if no least solution is expressible in the admitted level algebra,
elaboration fails with `E_UNIVERSE_NO_PRINCIPAL_SOLUTION`.

Cumulativity permits a declaration inferred at its principal universe to be used at any larger universe through an
explicit KCore lift. Inference MUST NOT raise a principal result universe merely because a larger solution also works.

Inference MUST NOT invent equality between otherwise independent universe metavariables.

Examples:

```kappa
data Phantom (A : Type) : Type =
    Phantom
```

The parameter level generalizes, while the result classifier has no lower bound and is minimized to `Type0`.

```kappa
data Box (A : Type) : Type =
    Box (value : A)
```

The constructor payload generates a lower bound from the universe of `A`; the principal result universe is that level.

```kappa
chooseType : Bool -> Type
let chooseType b =
    if b then Int else String
```

The principal result is `Type0`.

```kappa
data (=)
    (@parametric 0 A : Type)
    (parametric 0 x : A)
    (parametric 0 y : A)
    : Type =
    refl : x = x
```

No constraint forces the result universe to equal the carrier universe. Principal inference would minimize the result.
The standard equality declaration therefore uses the explicit schema `data (=).{u} ... : Type u` under §11.4.1.
```

---

## 4. Unbounded parametric witness packages

Replace §11.1.2.7 and the conflicting Sigma examples in §11.1.2.8 with:

```text
<!-- types.universes.no_ordinary_universe_of_all_codes -->
##### 11.1.2.7 No ordinary universe of all ordinary type codes

Kappa permits small packages containing parametric type witnesses from arbitrary first-class universe levels.

For example:

```kappa
type AnyTypeWitness : Type =
    (ordinary 0 level : TypeLevel,
     parametric 0 T : Type level)
```

The shorter form uses the default mode on the second field:

```kappa
type AnyTypeWitness : Type =
    (ordinary 0 level : TypeLevel,
     T : Type level)
```

This type is well formed. The field `T` is a parametric witness. It does not store an ordinary observable type code and
therefore contributes no `succ level` universe obligation to the enclosing Sigma.

Projection preserves the mode:

```text
p.T :parametric Type p.level
```

The projected witness may be used:

* as a type expression;
* as an argument to another parametric type or higher-kinded binder;
* in equality propositions whose endpoint binders are parametric;
* in another parametric field or constructor argument.

It may not be returned, stored, or passed as an ordinary value of `Type p.level`.

Therefore this remains rejected:

```kappa
reify :
    AnyTypeWitness ->
    Type 0

let reify p =
    p.T
```

The precise result annotation may differ by level; the rejection is mode-based, not merely a level mismatch.

An unbounded ordinary type-code package remains rejected:

```kappa
type AllOrdinaryCodes =
    (ordinary 0 level : TypeLevel,
     ordinary 0 T : Type level)
```

The ordinary field `T` has classifier `Type (succ level)`, for which no ceiling independent of `level` exists.

Likewise, an ordinary code-producing function remains rejected:

```kappa
(level : TypeLevel) -> Type level
```

because its result is an ordinary universe value, not a sealed parametric field.

A later ordinary payload field remains subject to its own universe:

```kappa
(ordinary 0 level : TypeLevel,
 parametric 0 T : Type level,
 value : T)
```

is unbounded unless an external ceiling is available, because the ordinary payload field `value : T` is classified at
`Type level`.

The accepted parametric witness package is not a universe of all ordinary type codes. It has no ordinary decoding
projection and cannot satisfy the ordinary code-production assumptions used by Girard/Hurkens constructions.
```

Replace the Sigma examples with:

```text
Accepted:

```kappa
(ordinary 0 i : TypeLevel,
 T : Type i)
```

The `T` field defaults to parametric and the package is small.

Rejected:

```kappa
(ordinary 0 i : TypeLevel,
 ordinary 0 T : Type i)
```

Accepted under an external schema ceiling:

```kappa
type OrdinaryCodesBelow.{u} : Type u =
    (ordinary 0 i : TypeLevel,
     @0 p : i < u,
     ordinary 0 T : Type i)
```
```

---

## 5. Standard bounded ordinary-code schemas

Replace the current term-indexed `TypeBelow` and `TypeAtMost` declarations with:

```text
**Standard bounded ordinary-code schemas.**

The standard prelude provides declaration-universe schemas:

```kappa
data TypeBelow.{u} : Type u =
    PackTypeBelow
        (ordinary 0 level : TypeLevel)
        (@0 bound : level < u)
        (ordinary 0 T : Type level)

data TypeAtMost.{u} : Type (succ u) =
    PackTypeAtMost
        (ordinary 0 level : TypeLevel)
        (@0 bound : level <= u)
        (ordinary 0 T : Type level)
```

`u` is a declaration-universe parameter, not a term-level `TypeLevel` binder.

`TypeBelow.{u}` packages an ordinary observable type code whose level is strictly below `u`.

`TypeAtMost.{u}` packages an ordinary observable type code whose level is at most `u`; the package itself lives in
`Type (succ u)`.

The proof binder supplies the constructor-size obligation for the ordinary `T` field.

A reference may infer or state the schema level:

```kappa
TypeBelow.{3}
TypeAtMost.{omega}
```

The earlier declarations:

```kappa
data TypeBelow (k : TypeLevel) : Type k = ...
data TypeAtMost (k : TypeLevel) : Type (succ k) = ...
```

are not Kappa v1 declarations and must be removed. Their type constructors would require unbounded ordinary Pis over a
first-class level.
```

---

## 6. Universe-polymorphic equality without exceptions

Replace §11.4.1's equality declaration and exact KCore interface with:

```text
<!-- types.propositions.equality -->
#### 11.4.1 Propositional equality

Equality is an ordinary user-definable universe-schema data family:

```kappa
data (=).{u}
    (@parametric 0 A : Type u)
    (parametric 0 x : A)
    (parametric 0 y : A)
    : Type u =

    refl : x = x
```

The normative elaborated interface is:

```text
(=).{u} :
    (@parametric 0 A : Type u) ->
    (parametric 0 x : A) ->
    (parametric 0 y : A) ->
    Type u
```

There is no equality-specific universe exception, endpoint marker bypass, resizing rule, or privileged kind-check path.
Any user declaration with the same legal schema and binder modes receives the same ordinary typing behavior.

Ordinary values may instantiate the parametric endpoint binders by ordinary-to-parametric observation subsumption.
Parametric endpoints may also instantiate them directly.

The endpoints have quantity `0`; they are explicit semantic arguments in `x = y` but do not contribute runtime demand.
The proof term itself is erased or retained independently according to its own quantity and proof-relevance rules.

The standard eliminators are universe-generalized declarations:

```kappa
pathInd.{u, v} :
    (@parametric 0 A : Type u) ->
    (@parametric 0 x : A) ->
    (parametric 0 motive : (parametric 0 y : A) -> x = y -> Type v) ->
    motive x refl ->
    (parametric 0 y : A) ->
    (parametric 0 p : x = y) ->
    motive y p

subst.{u, v} :
    (@parametric 0 A : Type u) ->
    (parametric 0 P : (parametric 0 z : A) -> Type v) ->
    (parametric 0 x : A) ->
    (parametric 0 y : A) ->
    x = y ->
    P x ->
    P y
```

`Dec` is similarly explicit:

```kappa
data Dec.{u}
    (parametric 0 P : Type u)
    : Type u =

    Yes (proof : P)
    No  (refute : P -> Void)
```

The required dynamic-representation signature remains:

```kappa
sameDynRep :
    forall a b.
    DynRep a ->
    DynRep b ->
    Dec (a = b)
```

It typechecks by the ordinary parametric endpoint binders of `(=).{u}` and the ordinary universe schema of `Dec`.
```

Add a conformance requirement:

```text
The standard prelude source declaration of equality MUST be accepted by the same surface elaborator and KCore checker
used for an equivalent user-written equality family. A compiler MUST NOT identify equality by source spelling in order
to bypass ordinary universe or observation checks.
```

---

## 7. Data and constructor grammar

Replace the relevant grammar fragments with:

```text
dataParam ::=
    ident
  | '(' explicitBinderBody ')'
  | '(' implicitBinderBody ')'

constructorDecl ::=
    ident constructorUniverseInstantiation? ctorBinder*

constructorUniverseInstantiation ::=
    universeInstantiation

ctorBinder ::=
    ctorPositionalField
  | '(' ctorParam ')'
  | '(' implicitBinderBody ')'
  | '{' fieldDecl (',' fieldDecl)* '}'

ctorParam ::=
    binderPrefix? ('thunk' | 'lazy')? ident ':' type defaultClause?

fieldDecl ::=
    binderPrefix? ('thunk' | 'lazy')? ident ':' type defaultClause?
```

Extend grouped explicit binders:

```text
explicitBinderBody ::=
    binderPrefix? binderName+ ':' type
```

Grouped binders share one elaborated annotation and, for bare `Type`, one universe metavariable.

### 7.1 Repair constructor-size examples

Replace rejected examples that omitted observation mode with:

```kappa
data U : Type0 =
    MkU (ordinary 0 T : Type0)

data U : Type0 =
    MkU (@ordinary 0 T : Type0)

data BadOmega : Type omega =
    MkBadOmega (ordinary 0 T : Type omega)

data G : Type0 =
    MkG : (ordinary 0 A : Type0) -> G
```

These remain rejected because quantity zero does not remove the ordinary universe-size obligation.

Add accepted controls:

```kappa
data PhantomCode : Type0 =
    PhantomCode (parametric 0 T : Type3)

data PhantomCodeDefault : Type0 =
    PhantomCodeDefault (T : Type3)
```

The second field defaults to parametric observation because its domain is a parametric kind.

Later payloads still count:

```kappa
data LargePayload : Type3 =
    LargePayload
        (parametric 0 T : Type3)
        (value : T)
```

The same declaration at `Type0` is rejected because `value : T` is an ordinary payload field classified at level `3`.
```

---

## 8. `TypeLevel` representation and complete algebra

Replace the opening declaration with:

```kappa
opaque data TypeLevel : Type0 =
    Level
        (omegaCoefficient : Nat)
        (finiteRemainder  : Nat)
```

The `opaque data` declaration hides `Level` outside `std.typelevel`; no per-constructor `private` syntax is used.

Replace the placeholder operation definitions with these normative bodies:

```kappa
opaque let typeLevelZero : TypeLevel =
    Level 0 0

opaque let typeLevelOne : TypeLevel =
    Level 0 1

opaque let typeLevelOmega : TypeLevel =
    Level 1 0

opaque let typeLevelFromInteger
    (n : Nat) : TypeLevel =
    Level 0 n

opaque let typeLevelSucc
    (x : TypeLevel) : TypeLevel =
    match x
    case Level c n ->
        Level c (n + 1)

opaque let typeLevelAdd
    (x : TypeLevel)
    (y : TypeLevel)
    : TypeLevel =
    match (x, y)
    case (Level xc xn, Level yc yn) ->
        Level (xc + yc) (xn + yn)

opaque let typeLevelCompare
    (x : TypeLevel)
    (y : TypeLevel)
    : Ordering =
    match (x, y)
    case (Level xc xn, Level yc yn) ->
        match compare xc yc
        case Less -> Less
        case Greater -> Greater
        case Equal -> compare xn yn

opaque let typeLevelMax
    (x : TypeLevel)
    (y : TypeLevel)
    : TypeLevel =
    match typeLevelCompare x y
    case Less -> y
    case Equal -> x
    case Greater -> x
```

The representation denotes:

```text
Level c n = omega * c + n
```

for levels below `omega^2`.

`typeLevelAdd` is the commutative natural/Hessenberg sum on this represented fragment:

```text
(omega * a + m) + (omega * b + n)
    = omega * (a + b) + (m + n)
```

Therefore:

```text
1 + omega = omega + 1
omega + omega = omega * 2
(omega + 1) + omega = omega * 2 + 1
```

The dot or multiplication sign in mathematical renderings is not the source `Mul TypeLevel` operation. Kappa v1 does
not provide `Mul TypeLevel`.

The standard instances delegate to these definitions:

```text
Zero TypeLevel
One TypeLevel
FromInteger TypeLevel
Successor TypeLevel
Add TypeLevel
Eq TypeLevel
Ord TypeLevel
Max TypeLevel
```

`FromInteger TypeLevel` accepts nonnegative integer literals only.

The prelude MUST also provide checked instances and laws for:

```text
AdditiveMonoid TypeLevel
CommutativeAdditiveMonoid TypeLevel
OrderedAdditive TypeLevel
JoinSemilattice TypeLevel
```

Required checked theorems include:

```kappa
typeLevelAddAssoc
typeLevelAddComm
typeLevelAddZero
typeLevelSuccIsAddOne
typeLevelSuccStrict
typeLevelLtIffSuccLe
typeLevelAddMonotone
typeLevelAddStrictMonotone
typeLevelMaxAssoc
typeLevelMaxComm
typeLevelMaxIdempotent
typeLevelFiniteBelowOmega
typeLevelOmegaPlusOmega
typeLevelOnePlusOmega
```

The operation bodies are opaque outside `std.typelevel` for ordinary delta reduction.

The universe solver may nevertheless normalize the resolved semantic identities of these standard declarations through
the certified universe bridge. The bridge MUST be extensionally equivalent to the checked source definitions. It does
not recognize source spelling alone.
```

---

## 9. KCore observation dependency calculus

Replace the prose-only observation section in §30.2 with:

```text
<!-- compiler.kcore.observation_calculus -->
#### 30.2.0 Observation dependency calculus

KCore checks observation mode with an independently defined dependency judgment:

```text
Gamma |- t : A ▷ D
```

`D` is a finite set of parametric origins on which ordinary observation of `t` depends.

A term is admissible in an `ordinary` position exactly when `D` is empty.

Every term is admissible in a `parametric` position.

This yields the one-way subsumption:

```text
ordinary -> parametric
```

and forbids the reverse.

Parametric origins include:

```text
* parametric binder identities;
* parametric field projections;
* parametric static facets;
* implementation-generated origins that preserve one of the above.
```

The checker computes `D`; KCoreText does not serialize a trusted precomputed dependency set.

##### Variables and globals

```text
ordinary binder x      => deps(x) = {}
parametric binder x    => deps(x) = {x}
ordinary global facet  => deps(g) = {}
parametric global facet => deps(g) = {g}
```

##### Checking against a binder or field

An argument or field value with dependency set `D` may instantiate:

```text
ordinary binder/field    only when D = {}
parametric binder/field  for any D
```

##### Application

Suppose:

```text
f : Pi[mode,q] x : A. B
```

with dependency sets `Df` and `Da` for `f` and argument `a`.

The argument must satisfy the binder mode.

The result dependency set is:

```text
Df union propagate(mode, x, B, Da)
```

where:

```text
propagate(ordinary,  x, B, Da) = {}

propagate(parametric, x, B, Da) =
    Da, when x occurs in B or B normalizes to a parametric kind;
    {}, otherwise.
```

This permits a genuinely constant value function such as `forall A. Int` to return an ordinary `Int`, while ensuring
that type-constructor application, dependent result formation, and higher-kinded partial application preserve
parametric dependencies.

##### Lambda

If the body has dependencies `D`, then:

```text
deps(lambda x { body }) = D minus {x}
```

Abstraction discharges dependence on its own binder but not on captured outer parametric origins.

##### Let and substitution

For:

```text
let x = rhs in body
```

let `Dr` be the dependencies of `rhs` and `Db` the dependencies of `body` with binder origin `x`.

```text
deps(let x = rhs in body) =
    (Db minus {x}) union (Dr when x is in Db, otherwise {})
```

KCore substitution MUST satisfy the same equation:

```text
deps(t[s/x]) =
    (deps(t) minus {x}) union
    (deps(s) when x is in deps(t), otherwise {})
```

##### Pi, Sigma, and other static code construction

Constructing an ordinary static code term does not seal dependencies.

For Pi, Sigma, type-family application, and other ordinary code constructors, dependencies of component code terms are
unioned after removing locally bound origins from dependent bodies.

Consequently, constructing `A -> A` from a parametric `A` yields a parametric type witness rather than an ordinary type
code.

##### Record, tuple, package, and data construction

A declared parametric field is a sealing boundary.

During construction:

```text
* dependencies supplied to ordinary fields propagate to the enclosing value;
* dependencies supplied to parametric fields are sealed and do not make the whole container parametric;
* every field argument is still checked against its declared observation mode.
```

Projection restores the declared field mode:

```text
ordinary field projection:
    dependencies are those of the scrutinee;

parametric field projection:
    dependencies are those of the scrutinee plus a fresh projection origin.
```

Constructor arguments and pattern binders use the same rules.

##### Case analysis

Pattern binders receive the observation modes declared by the selected constructor or field.

The result dependency set is the union of branch dependencies after branch-local binder substitution. Dependencies of a
parametric scrutinee also propagate unless the eliminator is a declared sealing eliminator whose result mode is checked
parametrically.

##### Aliases, conversion, and lifts

Transparent aliases preserve dependency sets.

Definitional conversion does not change dependencies.

`universeLift` and its inverse preserve dependencies.

##### Required metatheory

The KCore checker MUST validate:

```text
weakening
substitution
subject reduction
ordinary-to-parametric subsumption
absence of parametric-to-ordinary promotion
preservation through beta, iota, zeta, and projection reduction
```

A hand-authored KCoreText file is rejected if any node requires a nonempty dependency set in an ordinary position.
```

---

## 10. Local universe generalization

Insert into §11.1.2.3A and §30.2:

```text
<!-- types.universes.local_generalization -->
##### Local declaration universe generalization

Local term definitions, local type aliases, and local recursive declaration SCCs may generalize universe metavariables.

A local generalization boundary occurs after elaborating the complete local declaration SCC and before elaborating uses
outside that SCC.

Rules:

* apply the same principal-universe algorithm as for top-level declarations;
* outer declaration-universe parameters remain rigid and are not generalized again;
* universe metavariables fixed by an expected monomorphic local signature are not generalized;
* remaining generalizable metas become a local declaration universe telescope;
* local references instantiate that telescope freshly at each use;
* recursive local declarations generalize once per local SCC;
* generalized constraints are serialized in KCore, KCoreText, stage dumps, and semantic hashes;
* local universe generalization introduces no runtime argument or closure field.

A local declaration whose type refers to an ordinary local term may not generalize that term as a universe parameter.
Ordinary dependency and escape rules still apply.
```

---

## 11. Complete KCoreText

Replace and extend the KCoreText grammar as follows.

Every global definition and axiom records its finalized observation summary explicitly:

```text
defDecl   ::= 'def' observationMode globalRef universeTelescope? ':' term constraintBlock? '{' ... '}'
axiomDecl ::= 'axiom' observationMode globalRef universeTelescope? ':' term constraintBlock? ';'
```

This mode is independently recomputed for available bodies and is the interface fact used for opaque or imported
global facets. It is not inferred from quantity or from the declaration's classifier.

Every dependent binder also records its independently selected formation mode:

```text
binder ::=
    '(' observationMode formationMode quantity explicitness accessMode localRef ':' term ')'

formationMode ::= 'ordinary' | 'parametric'
```

The serialized formation mode is an untrusted claim. Verification checks it against §11.1.2.8; it is never reconstructed
from observation mode, quantity, or erasure after elaboration.

### 11.1 Remove free `universeDecl`

Remove:

```text
universeDecl ::= 'universe' universeRef ';'
```

Universe parameters occur only in global or local declaration telescopes.

### 11.2 Global uses and universe instantiation

```text
globalUse ::=
    globalRef universeInstantiation?

universeInstantiation ::=
    '.{' level (',' level)* '}'
```

Use `globalUse` in:

```text
global term references
constructors
case alternatives
static-object references
evidence references
associated-member references
```

Revised productions:

```text
term ::=
    ...
  | globalUse
  | 'construct' globalUse '(' argumentList? ')'
  | ...

caseAlt ::=
    'case' globalUse binder* '{' term '}'
  | 'default' '{' term '}'

evidenceRef ::=
    localRef
  | globalUse
  | 'constraint' '(' integer ')'
  | 'certificate' '(' certificateRef universeInstantiation? ')'
```

### 11.3 Local definitions

```text
localDef ::=
    'def' observationMode localRef universeTelescope? ':' term constraintBlock? '{'
        'body' '=' term ';'
    '}'
```

Local recursive groups are explicit:

```text
localRecGroup ::=
    'letrec' '{' localDef+ '}' 'in' term
```

### 11.4 Typed generic values

Replace ambiguous untagged generic values with:

```text
coreValue ::=
    'integer-value' '(' integer ')'
  | 'string-value' '(' stringLiteral ')'
  | 'level-value' '(' level ')'
  | 'quantity-value' '(' quantityExpr ')'
  | 'term-value' '(' term ')'
  | 'global-ref-value' '(' globalUse ')'
  | 'local-ref-value' '(' localRef ')'
```

The token `0` never relies on context to decide whether it is an integer, level, quantity, or term value inside a generic
extension payload.

### 11.5 Extension declarations

Add:

```text
extensionDecl ::=
    'extension' identifier integer ';'
```

A module using `genericDecl` or `genericTerm` from extension `x` MUST contain exactly one compatible declaration:

```text
extension x version;
```

Unknown undeclared extension tags are rejected with `E_KCORE_TEXT_INVALID`.

### 11.6 Level certificates

Add:

```text
certificateRef ::= '@certificate.' qualifiedName '#' stableId

levelCertificateDecl ::=
    'level-certificate' certificateRef universeTelescope? ':' universeConstraint constraintBlock? '{'
        levelProof
    '}'

levelProof ::=
    'assumption' '(' integer ')' ';'
  | 'closed' ';'
  | 'zero-left' level ';'
  | 'refl' level ';'
  | 'trans' '{' levelProof levelProof '}'
  | 'succ-mono' '{' levelProof '}'
  | 'max-left' level level ';'
  | 'max-right' level level ';'
  | 'add-mono-left' level '{' levelProof '}'
  | 'add-mono-right' level '{' levelProof '}'
```

`closed` is accepted only when both sides are closed standard `TypeLevel` expressions and the ordinary checked
`Ord TypeLevel` semantics validate the stated constraint.

`zero-left l` proves `0 <= l`; its level remains independently scope- and kind-checked.

`assumption(n)` refers to the `n`th normalized entry of the certificate declaration's own
`constraintBlock`. A certificate use supplies exactly the certificate telescope's universe
instantiation and must discharge that block in the use-site assumption context before the
specialized theorem can authorize a lift.

A certificate is identified by semantic identity but remains untrusted until the independent certificate checker
verifies the proof tree against the stated constraint.

Invalid or forged certificates are rejected with `E_KCORE_LEVEL_CERTIFICATE_INVALID`.

### 11.7 Canonical declaration ordering

Canonical output orders declaration SCCs topologically by semantic dependency.

Within one mutually recursive SCC, declarations are ordered lexicographically by their authoritative stable identity,
not by source spelling, allocation order, or hash-map iteration order.

Level certificate declarations precede the first declaration that references them and are ordered by certificate stable
identity when otherwise independent.

### 11.8 Canonicality

Add:

```text
Every global use includes an explicit universe instantiation when the referenced declaration has a nonempty universe
schema.

Every local use includes an explicit universe instantiation when the local declaration has a nonempty local universe
schema.

Every cumulative lift cites one of:

* a local proof reference;
* a normalized declaration constraint index;
* a verified level certificate reference.

A stable ID alone never constitutes proof.
```

---

## 12. Global normative replacements

Apply these replacements throughout the specification:

1. Replace every statement that `(i : TypeLevel, T : Type i)` is rejected with the explicit ordinary version:

   ```kappa
   (ordinary 0 i : TypeLevel, ordinary 0 T : Type i)
   ```

2. Replace every statement that `exists (i : TypeLevel). Type i` is categorically unsafe with the distinction:

   ```text
   parametric witness existential: accepted
   ordinary type-code existential: rejected without a ceiling
   ```

3. Replace old `TypeBelow (k : TypeLevel)` and `TypeAtMost (k : TypeLevel)` declarations with the schema declarations
   `TypeBelow.{u}` and `TypeAtMost.{u}`.

4. Replace `private Level` with `Level` inside `opaque data TypeLevel`.

5. Replace equality endpoint modes `ordinary 0` with `parametric 0`.

6. Remove every claim that equality receives a distinguished capability exception.

7. Add `universeSchema?` to constructor, data, type, trait, effect, projection, term, and local declaration grammar.

8. Remove `E_PARAMETRIC_BINDER_DOMAIN` from aliases, families, registries, and tests.

9. Replace implementation-optional inconsistent level handling with deterministic rejection.

10. Update interface artifacts to serialize:

    ```text
    explicit or inferred declaration universe schemas;
    local universe schemas when local artifacts are emitted;
    normalized schema constraints;
    observation mode on every binder and field;
    parametric-result dependency summaries needed by application checking;
    verified level-certificate identities.
    ```

---

## 13. Required adversarial properties

A conforming implementation MUST include separate tests demonstrating:

```text
* an unbounded parametric type-witness package is accepted;
* projecting its witness preserves parametric mode;
* ordinary reification of that projection is rejected;
* an unbounded ordinary type-code package is rejected;
* user-written equality with an explicit schema is accepted;
* sameDynRep uses ordinary equality without a compiler exception;
* principal inference minimizes Phantom and chooseType results;
* payload-bearing declarations infer the least required result universe;
* local declarations generalize and instantiate local universe schemas;
* direct and transitive inconsistent level assumptions reject deterministically;
* TypeLevel addition satisfies the specified closed equations;
* KCore dependency checking rejects alias, application, projection, pattern, and partial-application laundering;
* KCoreText global constructor, case, evidence, and local references carry explicit universe instantiations;
* forged level certificates are rejected;
* KCoreText round-trips local schemas and verified lifts.
```

The direct Hurkens/Girard regression must fail at one of the intended structural barriers:

```text
parametric code production -> E_PARAMETRIC_TYPE_PROMOTION
ordinary same-universe code production -> E_UNIVERSE_SELF_CONTAINMENT or E_UNIVERSE_CONSTRAINT_UNSATISFIABLE
```

A plain unrelated return-type mismatch is not a valid Hurkens barrier regression.
