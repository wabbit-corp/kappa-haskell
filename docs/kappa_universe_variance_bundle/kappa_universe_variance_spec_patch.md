# Kappa cumulative nominal-family universe variance patch

**Patch base:** `Spec(98).md`

This patch adds checked variance for declaration-universe parameters of nominal families. It is deliberately broader than
an ordinary-data-only rule: the core representation is a certified action on a normalized nominal signature, so future
higher inductive, higher inductive-recursive, quotient inductive, higher inductive-inductive, and quotient
inductive-inductive forms must pass through the same machinery rather than inventing mutually incompatible little
subtyping systems, as language features so often attempt when left unsupervised.

The patch makes these decisions normative:

```text
* universe-schema roles are `invariant`, `covariant`, and `irrelevant`;
* there is no contravariant universe-schema role;
* omitted roles are inferred deterministically;
* explicit roles may tighten inference but may not be more permissive;
* cross-instance cumulativity applies only to fully saturated nominal-family applications;
* every cross-instance use is an explicit, checked `schemaLift` in KCore;
* Kappa does not make role-related instances judgmentally equal merely because Rocq does;
* a verified nominal-signature action certificate is required;
* unsupported current or future signature clauses conservatively force affected roles to `invariant`;
* positivity, observation mode, quantity, universe formation, and universe-schema variance remain independent checks;
* future HIIT/HIRT/QIT/QIIT extensions must certify point constructors, higher/path constructors, equations,
  recursive operations, eliminators, and computation rules together.
```

---

## 1. Diagnostic additions

### 1.1 Portable aliases

Add to §3.1.4:

```text
E_UNIVERSE_VARIANCE_TOO_PERMISSIVE
E_UNIVERSE_VARIANCE_NOT_APPLICABLE
E_UNIVERSE_SCHEMA_LIFT_INVALID
E_KCORE_SCHEMA_CERTIFICATE_INVALID
```

Add these meanings:

```text
* `E_UNIVERSE_VARIANCE_TOO_PERMISSIVE` is emitted when an explicit declaration-universe variance annotation is more
  permissive than the role certified for that parameter.

* `E_UNIVERSE_VARIANCE_NOT_APPLICABLE` is emitted when a variance annotation is written on a declaration that does not
  introduce a nominal family or another standardized nominal-signature block.

* `E_UNIVERSE_SCHEMA_LIFT_INVALID` is emitted when an attempted cumulative use of one nominal-family universe instance
  at another instance fails role comparison, declaration constraints, saturation, family-argument alignment, or
  certificate verification.

* `E_KCORE_SCHEMA_CERTIFICATE_INVALID` is emitted when a KCore or KCoreText nominal-signature action certificate is
  missing, malformed, stale, forged, produced by an unsupported checker version, disagrees with the declaration's
  signature closure, or fails independent verification.
```

### 1.2 Diagnostic families

Insert in §3.2.3:

Family:

```text
kappa.universe.variance
```

Used for invalid explicit universe-variance annotations and failures while inferring or validating a nominal family's
role vector.

Payload MUST include:

* nominal declaration identity;
* nominal signature-block identity;
* universe-schema parameter index and source name, when available;
* explicit role, when present;
* inferred role;
* effective role;
* role-checker version;
* the normalized signature clause or generated obligation that forced the tighter role;
* source or synthetic origin of that clause;
* whether the declaration is current ordinary data, trait evidence, or an extension-defined nominal signature;
* the extension gate and clause kind when an extension is involved;
* the nearest stricter role that would be accepted.

An annotation that is too permissive uses `E_UNIVERSE_VARIANCE_TOO_PERMISSIVE`.

An annotation on a declaration for which roles have no semantics uses `E_UNIVERSE_VARIANCE_NOT_APPLICABLE`.

Family:

```text
kappa.universe.schema-lift
```

Used when cumulative nominal-family subsumption cannot be justified.

Payload MUST include:

* family identity;
* source and target universe instances;
* certified role vector;
* source and target normalized declaration constraints;
* saturation arity and supplied family-argument count;
* source and target aligned family arguments;
* per-role obligations and their evidence;
* certificate identity and checker version;
* first failed invariant equality, covariant inequality, family-argument alignment, or clause-action obligation;
* whether the attempted use originated in expected-type checking, constructor checking, pattern matching, trait search,
  an explicit source ascription, or hand-authored KCore.

This family uses `E_UNIVERSE_SCHEMA_LIFT_INVALID`.

Family:

```text
kappa.kcore.schema-certificate-invalid
```

Used when the independent KCore checker rejects a nominal-signature action certificate.

Payload MUST include:

* certificate identity;
* family or signature-block identity;
* recorded and recomputed signature-closure hashes;
* recorded and recomputed role vectors;
* checker format version;
* clause kind and clause identity of the first failed action or coherence obligation;
* whether the certificate came from the current unit or an imported interface artifact.

This family uses `E_KCORE_SCHEMA_CERTIFICATE_INVALID`.

---

## 2. Surface universe-schema roles

Amend §11.1.2.3A.1.

Replace:

```text
universeSchemaParam ::=
    ident
```

with:

```text
universeSchemaParam ::=
    universeVariance? ident

universeVariance ::=
    'invariant'
  | 'covariant'
  | 'irrelevant'
```

The three words are contextual keywords only inside declaration universe schemas and KCoreText universe-role positions.

Examples:

```kappa
data Phantom.{irrelevant u} : Type0 =
    Phantom

data StoredCode.{covariant u} : Type (succ u) =
    StoredCode (ordinary 0 T : Type u)

data Consumer.{invariant u} : Type (succ u) =
    Consumer (run : (ordinary 0 T : Type u) -> Int)
```

A schema parameter with no written role is inferred under §11.1.2.3A.2.

A role annotation is accepted only on a declaration that elaborates to a nominal signature block, including:

* `data` and `opaque data` declarations;
* nominal record or variant sugar elaborating to `data`;
* trait declarations when their evidence type is represented by a nominal signature block;
* future extension declarations that explicitly adopt the nominal-signature contract of §10.5.

A role annotation on an ordinary term, transparent type alias, effect declaration without a nominal evidence family,
projection, or other non-nominal declaration is rejected with `E_UNIVERSE_VARIANCE_NOT_APPLICABLE`.

Unannotated universe parameters remain valid on every declaration kind that already admits an explicit schema.

A role controls only cumulative comparison between instances of the same nominal family. It does not imply:

* runtime erasure;
* quantity `0`;
* parametric observation mode;
* proof irrelevance;
* term-parameter variance;
* representation polymorphism;
* positivity of recursive occurrences.

In particular, `irrelevant` means only that no relation between the corresponding source and target universe levels is
required by the family certificate. It does not mean that the universe parameter is absent from interface identity or
that values mentioning the parameter may be observed ordinarily.

---

## 3. Declaration-universe variance semantics

Insert after §11.1.2.3A.1.

<!-- types.universes.nominal_variance -->
##### 11.1.2.3A.2 Cumulative nominal families and declaration-universe variance

A declaration-universe parameter of a nominal family has one role:

```text
UniverseVariance ::= invariant | covariant | irrelevant
```

Roles are ordered from least to most permissive:

```text
invariant < covariant < irrelevant
```

For one schema parameter with source level `a` and target level `b`, define:

```text
a <=[invariant] b   iff   a ≡ b

a <=[covariant] b   iff   a <= b

a <=[irrelevant] b  always
```

Here `≡` is normalized definitional equality of universe-level expressions and `<=` is the checked universe ordering.

For a role vector `r̄` and equally sized universe instances `ā` and `b̄`:

```text
ā <=[r̄] b̄
```

holds pointwise.

Both `ā` and `b̄` must independently satisfy the declaration's normalized universe-schema constraints. An irrelevant
role does not waive those declaration constraints.

There is no contravariant universe role in Kappa v1. Any occurrence that would require reversal of a universe
inequality, contravariant function-domain subtyping, a wrapper function, a traversal, or another non-identity runtime
map forces the affected role to `invariant`.

A role annotation is a user-requested upper bound on permissiveness. Let `inferred` be the role certified by the checker
and `written` the explicit role:

```text
written is accepted iff written <= inferred
```

Thus an inferred `irrelevant` role may be tightened to `covariant` or `invariant`; an inferred `covariant` role may be
tightened to `invariant`; an inferred `invariant` role may not be loosened.

The effective role is the explicit accepted role when present, otherwise the inferred role.

Every nominal family has a checked effective role vector, including a family whose vector is entirely invariant.
All-invariant is the conservative fallback and requires no cross-instance cumulativity.

### 3.1 Fully saturated family applications

Add:

Cross-instance nominal-family cumulativity applies only to a fully saturated application of the family head.

A family application is fully saturated when every binder of the declared data-family or nominal-family term telescope
has been supplied, including explicit, implicit, erased, parametric, and ordinary binders.

Kappa has no parameter/index partition. Universe variance does not infer variance for family term arguments.

To relate:

```text
D.{ā} x̄
D.{b̄} ȳ
```

all of the following are required:

1. `D` is the same resolved nominal declaration in both types;
2. both applications are fully saturated;
3. `ā <=[roles(D)] b̄`;
4. the declaration constraints hold at both instances;
5. the family arguments align left-to-right under the family telescope;
6. the checked nominal-signature action certificate for `D` is available.

Family-argument alignment rechecks the same source argument term against the corresponding target binder after earlier
aligned arguments have been substituted. It may insert only:

* ordinary definitional conversion;
* classifier-only `universeLift` nodes;
* recursively certified `schemaLift` nodes for fully saturated nominal family arguments.

It does not invoke user coercions, trait search, function extensionality, propositional equality, arbitrary mapping,
container traversal, or general subtyping.

If alignment succeeds, the target family arguments are the canonical rechecked arguments produced by this process.

A partially applied family or constructor is never directly related by universe variance. Surface elaboration MAY
eta-expand a partial application and insert lifts only after the nominal result becomes fully saturated. Such
eta-expansion must be explicit in KCore and must preserve observation mode, quantity, and runtime behavior.

### 3.2 Cumulativity is not judgmental equality

Add:

```text
Different universe instances related by `covariant` or `irrelevant` roles are not made judgmentally equal merely by the
role declaration.

Surface Kappa may insert cumulative subsumption implicitly, but KCore represents it with `schemaLift` (§30.2.1B).

This applies even to `irrelevant` roles. `irrelevant` removes the cross-instance level obligation; it does not erase the
explicit lift from checked KCore.

This choice keeps Kappa conversion smaller than Rocq-style role-sensitive convertibility and ensures every nominal
cross-instance step remains auditable, hashable, and independently checkable.
```

---

## 4. Nominal signature closures and certificates

Insert after §10.4.2 as §10.4.3.

<!-- data_types.nominal_signature_variance -->
#### 10.4.3 Nominal signature closure and cumulative-action certification

After constructor universe-size checking and positivity checking succeed, every nominal declaration is elaborated to a
normalized **nominal signature closure**.

For ordinary `data`, the closure contains at least:

```text
* the nominal family head and complete term telescope;
* the declaration universe telescope and normalized constraints;
* every point constructor telescope and result;
* generated projections, recursors, inductors, and eliminators that are part of source or interface semantics;
* every definitional or propositional computation rule generated for those eliminators;
* observation modes, quantities, access modes, and explicitness of all binders and fields;
* the runtime representation summary required to establish representation-identity lifting.
```

A future nominal extension adds its extension-defined clauses under §10.5.

The closure excludes presentation-only syntax, source names after identity resolution, diagnostics, and backend-specific
layout choices.

A **nominal-signature action certificate** for a role vector proves that for every pair of well-formed universe instances
related by that role vector:

```text
1. each fully saturated family instance has a target instance;
2. every point constructor is preserved;
3. every higher/path constructor, quotient equation, recursive operation, recursive equation, and boundary clause is
   preserved when the extension provides such clauses;
4. every generated eliminator remains well typed;
5. every declared computation rule commutes with the lift;
6. the action is identity on equal universe instances;
7. action composition agrees with direct action;
8. the value-level lift is runtime representation identity;
9. observation dependencies, quantities, borrowing, and erasedness are preserved.
```

The certificate is checked by a standardized certificate checker. A compiler-generated certificate is not trusted merely
because the same compiler generated it.

If no valid non-invariant certificate can be generated for a parameter, that parameter is inferred `invariant`.
If an extension clause has no standardized action rule, every universe parameter occurring in or controlling that clause
is forced to `invariant`.

### 4.1 Ordinary-data action rules

Continue:

For ordinary data, a constructor action is synthesized left-to-right over the constructor telescope.

A source field value may be reused at the target only when the target field type is obtained by:

* definitional equality;
* a classifier-only `universeLift`;
* a recursively certified `schemaLift` on a fully saturated nominal field type;
* rebuilding an erased proof from checked level/equality evidence without changing runtime representation.

The action may not require:

* an eta-wrapper around a function field;
* mapping over a container;
* pattern matching on a runtime field;
* allocation of a replacement runtime value;
* invocation of user code;
* a contravariant type conversion;
* a change of constructor tag, field order, or retained runtime field representation.

If any runtime-relevant field would require such a transformation, every schema parameter responsible for that
transformation is forced to `invariant`.

A direct constructor-local field:

```kappa
(ordinary 0 T : Type u)
```

or:

```kappa
(parametric 0 T : Type u)
```

may be reused from a lower `u` at a higher `u` through a classifier-only lift, so such a field generally requires at
most `covariant` rather than `invariant`.

A universe parameter appearing only in the classifier of a fully supplied family argument does not by itself constrain
the role. Family arguments are fixed and rechecked at both instances.

A universe parameter in a function-field domain forces `invariant`; Kappa does not infer a contravariant role.

The result classifier of the nominal family alone does not constrain the role. An empty family may therefore infer an
`irrelevant` role even when its result is written `Type u`.

### 4.2 Deterministic role inference

Add:

Universe-role inference is performed after principal universe inference, constructor-size checking, positivity checking,
and normalization of the nominal signature closure.

The role lattice is pointwise:

```text
invariant < covariant < irrelevant
```

For an ordinary singleton family or a mutually checked nominal signature block, inference computes a greatest fixed
point.

Let `R` assign one tentative role to every pair of introduced nominal family and declaration-universe parameter.

```text
R0     = every role is irrelevant
Rk+1   = recomputeVariance(Rk)
```

`recomputeVariance` runs the standardized signature-action checker using symbolic source and target universe instances.
It returns the most permissive role requirements justified by all clauses, using tentative roles from `Rk` for recursive
references to families in the same block and recorded roles for external families.

The operator MUST be monotone in the role order and MUST only retain or tighten roles. Iteration stops at the first fixed
point.

The stable vector is the inferred vector.

For current ordinary data, the standardized action rules of §10.4.3 determine `recomputeVariance`.
For extension-defined clause kinds, the extension supplies standardized monotone transfer rules under §10.5.

If a generated requirement couples distinct schema parameters in a way not expressible by independent pointwise roles,
all parameters involved in that coupled requirement are tightened to `invariant`.

A conforming implementation MAY use constraint solving or another algorithm instead of literal iteration, but it MUST
produce the same fixed-point role vectors.

Roles are inferred jointly for all families in one mutually recursive or future inductive-inductive signature block.
The certificate records a separate role vector for each introduced nominal family head, even when the source extension
uses one shared block schema.

### 4.3 Relationship to positivity and observation

Add:

Universe variance is independent of strict positivity and parameter-positivity signatures.

```text
parameter positivity
    says whether a type-parameter position preserves recursive positivity;

universe variance
    says when two declaration-universe instances of the same fully saturated nominal family are cumulatively related;

observation mode
    says whether a value may be observed or reified ordinarily;

quantity
    says how often a value is demanded and whether it erases.
```

A role never makes a non-positive recursive occurrence acceptable.
A parametric field is not automatically universe-irrelevant.
An erased field is not automatically universe-irrelevant.
A universe-irrelevant parameter is not automatically erased or parametric.

The normative check order for ordinary data is:

```text
1. ordinary elaboration and principal universe inference;
2. constructor universe-size checking;
3. strict positivity and parameter-positivity fixed point;
4. nominal signature closure construction;
5. universe-role fixed point;
6. nominal-signature action certificate verification;
7. generated eliminator and computation-rule verification.
```

### 4.4 Level-expression monotonicity

Role inference may use only checked monotonicity facts for universe-level operations.

The standard `TypeLevel` theorems certify that `succ`, standard natural/Hessenberg addition, and `max` are monotone in
every argument. A classifier-only field or clause involving these operations may therefore generate pointwise covariant
requirements.

A transparent level expression that normalizes to the standard solver grammar inherits those facts.

An opaque, neutral, extension-defined, or user-defined `TypeLevel` operation has no variance property merely because its
result type is `TypeLevel`. Unless a checked monotonicity certificate recognized by the universe solver is available,
every schema parameter occurring under that operation is forced to `invariant`.

The variance checker never invokes arbitrary trait search to guess monotonicity.

---

## 5. Examples and required standard summaries

Insert after §10.4.3.

Examples:

```kappa
data Phantom.{u} : Type0 =
    Phantom
```

infers `irrelevant u`.

```kappa
data Box.{u}
    (A : Type u)
    : Type u =
    Box (value : A)
```

infers `irrelevant u`: the fully saturated argument `A` is fixed and rechecked at both instances, while the payload type
is the same aligned argument.

```kappa
data SomeWitness.{u} : Type0 =
    SomeWitness (parametric 0 A : Type u)
```

infers `covariant u`: increasing `u` admits reuse of the witness through a classifier-only lift, while decreasing `u`
is not generally valid.

```kappa
data SomeCode.{u} : Type (succ u) =
    SomeCode (ordinary 0 A : Type u)
```

infers `covariant u`.

```kappa
data Consumer.{u} : Type (succ u) =
    Consumer (run : (ordinary 0 A : Type u) -> Int)
```

infers `invariant u`: lifting would require widening a function domain, and Kappa has no contravariant role.

```kappa
data Empty.{covariant u} : Type u
```

is accepted even though the inferred role is `irrelevant`; `covariant` is a valid stricter annotation.

The standard prelude MUST publish verified role summaries for every universe-polymorphic nominal family.
At minimum, the expected summaries include:

```text
(=).{u}                 irrelevant u
TypeBelow.{u}           covariant u
TypeAtMost.{u}          covariant u
```

For equality, `u` classifies fully supplied parametric family arguments and endpoints; it is not stored as a
constructor-local code witness.

---

## 6. Standard bounded schemas

Amend the `TypeBelow` and `TypeAtMost` declarations to state their roles explicitly:

```kappa
data TypeBelow.{covariant u} : Type u =
    PackTypeBelow
        (ordinary 0 level : TypeLevel)
        (@0 bound : level < u)
        (ordinary 0 T : Type level)

data TypeAtMost.{covariant u} : Type (succ u) =
    PackTypeAtMost
        (ordinary 0 level : TypeLevel)
        (@0 bound : level <= u)
        (ordinary 0 T : Type level)
```

The certificate derives a target bound from the source bound and the covariant schema inequality. The ordinary type-code
field is reused under classifier cumulativity. Both proof reconstruction and code reclassification erase before runtime.

---

## 7. KCore `schemaLift`

Insert after §30.2.1A.

<!-- compiler.kcore.schema_lifts -->
#### 30.2.1B Explicit nominal-schema lifts

Surface cumulative use between universe instances of the same nominal family is implicit.

KCore records it explicitly:

```text
schemaLift [
    family      = D,
    from        = .{a1, ..., an},
    to          = .{b1, ..., bn},
    certificate = cert,
    roles       = [r1, ..., rn],
    targetArgs  = [y1, ..., ym]
] t
```

Each role entry is one of:

```text
invariant
irrelevant
covariant evidence
```

where `evidence` proves the corresponding source level is `<=` the target level.

Typing rule, schematically:

```text
Γ ⊢ t : D.{ā} x̄
D is fully saturated by x̄
roles(D) = r̄
Γ ⊢ ā <=[r̄] b̄
Γ ⊢ align_D(ā, x̄; b̄) = ȳ
Γ ⊢ cert : SchemaActionCertificate(D, r̄)
────────────────────────────────────────────────────────
Γ ⊢ schemaLift[D,ā,b̄,cert,ȳ] t : D.{b̄} ȳ
```

Rules:

* the family head and saturation arity are verified from semantic identity;
* invariant entries carry no proof and require normalized equality;
* irrelevant entries carry no proof and impose no cross-instance relation;
* covariant entries carry checked level evidence;
* source and target declaration constraints are rechecked;
* family arguments are aligned by the restricted process of §11.1.2.3A.2;
* the certificate is independently verified or imported from a verified interface artifact;
* the node preserves observation dependencies, quantities, access modes, and family-argument refinements;
* the node is runtime representation identity and erases before KBackendIR;
* identity schema lifts normalize away;
* nested schema lifts compose to one direct lift when certificate identity and argument alignment agree;
* a direct lift and a composed lift have the same semantic hash after canonicalization;
* no `schemaLift` is inserted during trait-instance candidate matching or overlap checking;
* checkpoint verification rejects a lift on an unsaturated family, a mismatched family head, mismatched family arguments,
  an invalid role relation, or an invalid certificate.

### 7.1 Constructor and eliminator coherence

Add:

For ordinary data, `schemaLift` satisfies constructor and eliminator coherence.

A lifted constructor value is observationally the corresponding target-instance constructor with aligned fields.
KCore may retain the outer `schemaLift` or normalize it through the constructor, but both representations must be
judgmentally coherent for iota reduction.

Case analysis on a lifted scrutinee uses the target family instance while binding fields with the modes and types
specified by the certified constructor action.

The following diagrams commute in checked KCore:

```text
constructor action followed by schemaLift
    = target constructor applied to aligned fields

case/induction after schemaLift
    = source case/induction with target motive and certified branch alignment
```

No branch-local equality or GADT family-argument fact may be invented by a schema lift. Existing family arguments must
align definitionally after explicit classifier and nominal lifts.

### 7.2 Partial applications

Add:

`schemaLift` is not defined on a bare or partially applied nominal family head or constructor constant.

When source ergonomics require a relation between first-class type formers, elaboration may generate an eta-expansion:

```text
lambda remainingArgs {
    schemaLift (sourceHead remainingArgs)
}
```

only when:

* the remaining telescope is known;
* every generated application becomes fully saturated before lifting;
* the expansion preserves observation mode and quantity;
* no runtime wrapper survives after specialization and erasure;
* the expanded KCore term independently typechecks.

---

## 8. Trait coherence and instance resolution

Insert in §14.3:

```text
<!-- traits.universe_schema_cumulativity -->
#### Universe-schema cumulativity and instance resolution

Universe-schema cumulativity does not participate in global instance-head overlap, orphan, or coherence comparison.

Instance heads are compared using exact normalized declaration universe instantiations after ordinary declaration-schema
instantiation. The resolver does not use one-way or irrelevant `schemaLift` edges to manufacture additional matching
instance heads.

A universe-polymorphic instance should generalize or explicitly declare its own universe schema.

After a unique candidate has been selected by ordinary coherence rules, its resulting evidence value may be subjected to
ordinary expected-type cumulativity, including a checked `schemaLift`, when the evidence type is a certified nominal
family.

This ordering prevents bidirectional irrelevant lifts from creating ambiguous or overlapping instances.
```

---

## 9. Interface artifacts and semantic identity

Amend §30.3.

Every exported nominal signature block MUST record:

```text
NominalCumulativitySummary =
    (blockIdentity          : NominalSignatureBlockId,
     familyIdentity         : SemanticObjectId,
     universeParameters     : List UniverseParameter,
     effectiveRoles         : List UniverseVariance,
     rolesWereExplicit      : List Bool,
     declarationConstraints : List UniverseConstraint,
     saturationArity        : Nat,
     signatureClosureHash   : Digest,
     certificateIdentity    : SchemaActionCertificateId,
     certificateVersion     : Nat,
     clauseKinds            : List NominalSignatureClauseKind,
     monotoneWitnesses       : List VerifiedMonotoneWitnessSummary,
     representationIdentity : Bool,
     extensionGate          : Option FeatureGateId)
```

Rules:

* `representationIdentity` MUST be true for any certificate used by Kappa's implicit cumulative subsumption;
* role vectors and certificate identity participate in interface and semantic identity;
* changing an effective role is an interface-semantic change even when source term signatures print identically;
* imported opaque families may be used cumulatively only through a supported verified summary;
* if the summary is absent, malformed, stale, or produced by an unsupported checker, all roles are treated as invariant
  and any attempted nontrivial schema lift is rejected;
* downstream compilation does not re-infer roles from opaque implementation bodies;
* a paranoid verification mode may recompute certificates when the complete normalized signature closure is available;
* instance-head metadata records exact schema instantiations independently from the cumulative summary.

The existing `DeclarationUniverseTelescope` is extended conceptually to keep ordinary schema parameters and nominal
roles separate:

```text
DeclarationUniverseTelescope =
    (parameters  : List UniverseParameter,
     constraints : List UniverseConstraint)

NominalUniverseRoles =
    List (UniverseParameterId, UniverseVariance)
```

Term and transparent type declarations have no `NominalUniverseRoles` unless they also introduce a nominal family.

---

## 10. KCoreText changes

Amend §30.2.0A.

### 10.1 Declarations and role syntax

Replace the KCoreText `dataDecl` and universe-telescope grammar with:

```text
dataDecl ::=
    'data' globalRef nominalUniverseTelescope? binder* ':' term constraintBlock?
        'certificate' schemaCertificateRef
        '{' constructorDecl* '}'

universeTelescope ::=
    '.{' universeRef (',' universeRef)* '}'

nominalUniverseTelescope ::=
    '.{' nominalUniverseBinder (',' nominalUniverseBinder)* '}'

nominalUniverseBinder ::=
    universeVariance universeRef

universeVariance ::=
    'invariant' | 'covariant' | 'irrelevant'
```

Future standardized nominal signature declarations use the same `nominalUniverseTelescope` and certificate reference.

### 10.2 Certificate declarations

Add:

```text
schemaCertificateRef ::=
    '@schema:' qualifiedName '#' stableId

schemaCertificateDecl ::=
    'schema-certificate' schemaCertificateRef
    'for' globalRef
    '['
        'checkerVersion' '=' integer ','
        'signatureHash' '=' schemaSignatureBinding ','
        'saturationArity' '=' integer
    ']'
    '{'
        'roles' '=' '[' universeVariance (',' universeVariance)* ']' ';'
        'clauseKinds' '=' '[' nominalClauseKind (',' nominalClauseKind)* ']' ';'
        'monotoneWitnesses' '='
            '[' monotoneWitness (',' monotoneWitness)* ']' ';'
    '}'

monotoneWitness ::=
    '{'
        'parameter' '=' integer ';'
        'operator' '=' term ';'
        'goal' '=' term ';'
        'evidence' '=' term ';'
        'dependencies' '=' '[' ref (',' ref)* ']' ';'
    '}'

schemaSignatureBinding ::=
    'local'
  | stringLiteral

nominalClauseKind ::=
    'sort_declaration'
  | 'point_constructor'
  | 'path_constructor'
  | 'higher_boundary'
  | 'quotient_equation'
  | 'recursive_operation'
  | 'recursive_equation'
  | 'eliminator'
  | 'computation_rule'
  | 'truncation_rule'
  | 'extension_clause'
```

Add `schemaCertificateDecl` to `kcoreDecl`.

A certificate declaration is not accepted merely because its recorded hash and roles are well formed. The independent
checker recomputes or verifies the certificate against the normalized local signature closure, or validates it against a
previously verified imported interface artifact.


`signatureHash = local` is valid only when the referenced nominal signature block is declared in the same KCoreText
unit. It instructs the independent checker to compute the closure hash from that local declaration; it is not a trusted
hash shortcut. Canonical local KCoreText retains the token `local`.

An imported certificate uses an exact digest string obtained from the verified interface artifact. The checker compares
that digest with the imported `NominalCumulativitySummary` before accepting any lift.

A stable identity alone never proves a schema action.

### 10.3 Schema-lift terms

Add to `term`:

```text
  | schemaLiftTerm
```

with:

```text
schemaLiftTerm ::=
    'schema-lift' '['
        'family' '=' globalRef ','
        'from' '=' universeInstantiation ','
        'to' '=' universeInstantiation ','
        'certificate' '=' schemaCertificateRef ','
        'roles' '=' '[' schemaRoleEvidence (',' schemaRoleEvidence)* ']' ','
        'targetArgs' '=' '(' argumentList? ')'
    ']' term

schemaRoleEvidence ::=
    'invariant'
  | 'irrelevant'
  | 'covariant' evidenceRef
```

Canonical KCoreText prints every role and every covariant proof explicitly.

### 10.4 Canonicalization

Add:

```text
* nominal universe roles appear in declaration-schema order;
* schema-certificate declarations precede the first declaration or lift that references them;
* a local certificate is ordered by authoritative certificate identity after its signature block;
* schema lifts are normalized by identity elimination and composition before canonical printing;
* irrelevant and invariant role entries never carry evidence;
* covariant role entries always carry evidence;
* `targetArgs` contains the canonical aligned full family telescope;
* no partial-family schema lift is printable as valid canonical KCoreText.
```

KCoreText rejection of a bad certificate uses `E_KCORE_SCHEMA_CERTIFICATE_INVALID`.
A well-formed certificate with an invalid lift use uses `E_UNIVERSE_SCHEMA_LIFT_INVALID`.

---

## 11. Principal universe inference interaction

Insert after §11.1.2.4A:

```text
Universe-role inference runs only after declaration universe inference has produced the final explicit or hidden schema
and normalized constraints.

Role inference:

* does not add or remove schema parameters;
* does not change a principal universe solution;
* does not equate independent universe metavariables;
* does not turn a first-class `TypeLevel` binder into a declaration universe parameter;
* may tighten only cumulative comparison semantics of already generalized schema parameters.

An explicit role annotation does not influence whether a universe metavariable is minimizable or generalizable.
If a user needs a specific relationship between result and parameter universes, that relationship must still be stated
through the declaration schema, result classifier, or ordinary generated constraints.
```

---

## 12. Future HIIT/HIRT/QIT/QIIT contract

Insert after §10.4.3 as a reserved extension contract.

<!-- data_types.future_nominal_signatures -->
### 10.5 Required nominal-signature contract for future inductive extensions

Any future feature that introduces one or more mutually defined nominal families and wants declaration-universe
cumulativity MUST elaborate to a checked nominal signature block.

This requirement applies at least to future:

```text
* higher inductive types;
* higher inductive-inductive types (HIITs);
* higher inductive-recursive or higher inductive-inductive-recursive types (HIRTs/HIIRTs);
* quotient inductive types (QITs);
* quotient inductive-inductive types (QIITs);
* quotient or higher inductive-recursive combinations;
* extension-defined nominal types with non-free constructors or equations.
```

A nominal signature block may contain standardized clause kinds:

```text
NominalSignatureClauseKind ::=
    sort-declaration
  | point-constructor
  | path-constructor
  | higher-boundary
  | quotient-equation
  | recursive-operation
  | recursive-equation
  | eliminator
  | computation-rule
  | truncation-rule
  | extension-defined-clause
```

The extension specification MUST define:

1. well-formedness and positivity/strict-positivity for every recursive occurrence;
2. the normalized signature closure contributed by every clause;
3. a monotone variance-transfer rule for every clause kind;
4. a checked action of schema lifts on every introduced sort;
5. action on every point constructor;
6. naturality of every path constructor, higher boundary, quotient equation, and recursive equation;
7. preservation of every generated eliminator and computation rule;
8. identity and composition coherence of the schema action;
9. the runtime representation argument establishing that the lift erases;
10. interface and KCoreText serialization of all clauses needed to recheck the certificate.

Path, quotient, and recursive equations participate even when their proof terms or witnesses erase. Runtime erasure is
not permission to omit an equation from variance certification.

For inductive-inductive blocks, roles are inferred jointly across all introduced sorts. The block certificate records a
separate effective role vector for every exported family head.

For inductive-recursive blocks, every recursively defined operation and every defining equation must commute with the
schema action. A recursive operation returning an ordinary universe code may force `covariant` or `invariant`; an
operation occurring in a negative or unsupported position forces `invariant`.

For higher or quotient constructors, the lifted endpoints, faces, boundaries, and equations must be accepted by the
extension's path/equality theory. Merely preserving point-constructor runtime tags is insufficient.

Large elimination, truncation restrictions, univalence, and cubical computation rules must be included in the
certificate whenever the extension exposes them.

If the extension cannot generate and independently verify all required action and coherence obligations for a schema
parameter, that parameter is `invariant`.

An implementation MUST NOT enable cumulative roles for an extension merely because its point constructors resemble an
ordinary data declaration.

### 12.1 Conservative v1 fallback

Add:

```text
Portable Kappa v1 contains no source syntax for HIIT, HIRT, QIT, or QIIT declarations unless a separately standardized
feature gate supplies it.

The interface and KCore structures introduced here are forward-compatible storage and verification contracts.
Unknown extension clause kinds do not inherit cumulative behavior automatically.
```

---

## 13. Metatheory obligations

Insert near the KCore required metatheory list:

Cumulative nominal-family support requires mechanized or otherwise independently checked proofs of:

```text
* reflexivity and transitivity of the role-indexed nominal cumulativity relation;
* preservation under substitution of declaration-universe parameters and family arguments;
* subject reduction for constructor, projection, iota, and schema-lift reduction;
* identity and composition coherence for schema actions;
* preservation of observation dependencies and quantities;
* representation identity and erasure of schema lifts;
* coherence between constructor actions and generated eliminators;
* stability under opacity and imported certificate use;
* consistency of role inference with mutual fixed points;
* extension-specific path/equation/recursive-operation naturality for every enabled future nominal extension.
```

A regression suite is not a substitute for these obligations, though it remains cheaper than discovering their absence
in a public consistency incident.

---

## 14. Appendix T harness additions

Add these portable test directives:

```text
--! assertUniverseRole <qualified-declaration> <parameter-index> <invariant|covariant|irrelevant>
--! assertSchemaLiftCount <integer>
--! assertSchemaLiftPresent <qualified-declaration>
--! assertSchemaCertificateValid <qualified-declaration>
--! assertInterfaceContainsUniverseRoles <qualified-declaration> <role-list>
--! assertSemanticHashDiffersFrom <artifact-or-target>
```

Meanings:

```text
assertUniverseRole
    checks the effective exported role after inference and explicit tightening.

assertSchemaLiftCount
    checks canonical verified KCore after identity/composition normalization.

assertSchemaLiftPresent
    checks that at least one verified lift of the named family is present.

assertSchemaCertificateValid
    independently verifies the family certificate.

assertInterfaceContainsUniverseRoles
    checks ordered interface metadata, not rendered prose.

assertSemanticHashDiffersFrom
    checks that changing a role or certificate-relevant signature fact changes semantic identity.
```

Future-extension test suites may use capability requirements:

```text
--! requires capability hiitUniverseVariance
--! requires capability hirtUniverseVariance
--! requires capability qitUniverseVariance
--! requires capability qiitUniverseVariance
```

A capability-gated suite is skipped only when the extension itself is unavailable. Once an implementation advertises the
capability, every such suite is mandatory.

---

## 15. Global mechanical edits

Apply these edits throughout normative prose, examples, interfaces, and dumps:

1. Render inferred nominal schemas with roles in verbose output:

   ```text
   List.{irrelevant u}
   TypeBelow.{covariant u}
   Consumer.{invariant u}
   ```

2. Do not add roles to ordinary term declaration schemas.

3. Extend every exported nominal declaration's interface metadata with effective roles and certificate identity.

4. Extend KCore family applications with enough resolved identity and saturation metadata for `schemaLift` checking.

5. State that `universeLift` changes only the classifier of one type/code term, whereas `schemaLift` changes the nominal
   family universe instance under a certified role vector. Neither subsumes the other.

6. Replace any claim that all same-family universe instances must match exactly with the role-indexed relation for fully
   saturated certified nominal applications.

7. Retain exact schema instantiations for instance-head coherence; do not role-normalize instance heads.

8. Keep the existing constructor universe-size and positivity checks. Variance is an additional phase, never a bypass.

9. Add role and certificate information to hover, verbose type display, interface dumps, KCoreText, semantic hashes,
   query keys, and reproducibility inputs.

10. When imported certificate support is unavailable, degrade to all-invariant; never infer permissive roles from an opaque
    declaration's printed type alone.
