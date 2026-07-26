# Kappa cumulative nominal-family universe variance Appendix T tests

**Companion patch:** `kappa_universe_variance_spec_patch.md`

**Suite count:** 42

The executable directory suites are supplied separately. The listings below are normative test intentions; exact parser support for future extension fixtures is capability-gated.

## `future/hiit_path_naturality_negative`

A HIIT role is rejected when a path constructor is not natural under the proposed action.

### `fixture.kcore`

```kcore
kcore 1;

module @variance.demo#1000 [languageVersion = "kappa-v1", compilerInterfaceVersion = "1", sourceModuleIdentity = "variance.demo"] {
  extension hiitUniverseVariance 1;
  decl-node "future-nominal-signature" {
    action = string-value("path-action-not-natural");
    requestedRole = string-value("covariant");
  }
}
```

### `main.kp`

```kappa
-- Future extension variance contract fixture.
```

### `suite.ktest`

```text
--! mode check
--! requires capability kcoreText
--! requires capability hiitUniverseVariance
--! assertKCoreRejects fixture.kcore E_KCORE_SCHEMA_CERTIFICATE_INVALID
```

## `future/hiit_path_naturality_positive`

A HIIT certificate preserves path constructors and their endpoints.

### `fixture.kcore`

```kcore
kcore 1;

module @variance.demo#1000 [languageVersion = "kappa-v1", compilerInterfaceVersion = "1", sourceModuleIdentity = "variance.demo"] {
  extension hiitUniverseVariance 1;
  decl-node "future-nominal-signature" {
    action = string-value("path-action-natural");
    requestedRole = string-value("covariant");
  }
}
```

### `main.kp`

```kappa
-- Future extension variance contract fixture.
```

### `suite.ktest`

```text
--! mode check
--! requires capability kcoreText
--! requires capability hiitUniverseVariance
--! assertKCoreParses fixture.kcore
```

## `future/hirt_recursive_equation_negative`

A HIRT role is rejected when a recursive equation fails to commute.

### `fixture.kcore`

```kcore
kcore 1;

module @variance.demo#1000 [languageVersion = "kappa-v1", compilerInterfaceVersion = "1", sourceModuleIdentity = "variance.demo"] {
  extension hirtUniverseVariance 1;
  decl-node "future-nominal-signature" {
    action = string-value("recursive-equation-not-natural");
    requestedRole = string-value("covariant");
  }
}
```

### `main.kp`

```kappa
-- Future extension variance contract fixture.
```

### `suite.ktest`

```text
--! mode check
--! requires capability kcoreText
--! requires capability hirtUniverseVariance
--! assertKCoreRejects fixture.kcore E_KCORE_SCHEMA_CERTIFICATE_INVALID
```

## `future/hirt_recursive_equation_positive`

A HIRT certificate preserves the recursive operation and every defining equation.

### `fixture.kcore`

```kcore
kcore 1;

module @variance.demo#1000 [languageVersion = "kappa-v1", compilerInterfaceVersion = "1", sourceModuleIdentity = "variance.demo"] {
  extension hirtUniverseVariance 1;
  decl-node "future-nominal-signature" {
    action = string-value("recursive-equation-natural");
    requestedRole = string-value("covariant");
  }
}
```

### `main.kp`

```kappa
-- Future extension variance contract fixture.
```

### `suite.ktest`

```text
--! mode check
--! requires capability kcoreText
--! requires capability hirtUniverseVariance
--! assertKCoreParses fixture.kcore
```

## `future/qiit_joint_variance_negative`

A QIIT block role is rejected when one sort or equation lacks a certified action.

### `fixture.kcore`

```kcore
kcore 1;

module @variance.demo#1000 [languageVersion = "kappa-v1", compilerInterfaceVersion = "1", sourceModuleIdentity = "variance.demo"] {
  extension qiitUniverseVariance 1;
  decl-node "future-nominal-signature" {
    action = string-value("joint-role-fixed-point-invalid");
    requestedRole = string-value("covariant");
  }
}
```

### `main.kp`

```kappa
-- Future extension variance contract fixture.
```

### `suite.ktest`

```text
--! mode check
--! requires capability kcoreText
--! requires capability qiitUniverseVariance
--! assertKCoreRejects fixture.kcore E_KCORE_SCHEMA_CERTIFICATE_INVALID
```

## `future/qiit_joint_variance_positive`

A QIIT block infers family roles jointly and preserves cross-sort equations.

### `fixture.kcore`

```kcore
kcore 1;

module @variance.demo#1000 [languageVersion = "kappa-v1", compilerInterfaceVersion = "1", sourceModuleIdentity = "variance.demo"] {
  extension qiitUniverseVariance 1;
  decl-node "future-nominal-signature" {
    action = string-value("joint-role-fixed-point-valid");
    requestedRole = string-value("covariant");
  }
}
```

### `main.kp`

```kappa
-- Future extension variance contract fixture.
```

### `suite.ktest`

```text
--! mode check
--! requires capability kcoreText
--! requires capability qiitUniverseVariance
--! assertKCoreParses fixture.kcore
```

## `future/qit_quotient_equation_negative`

A QIT certificate may not omit an erased quotient equation.

### `fixture.kcore`

```kcore
kcore 1;

module @variance.demo#1000 [languageVersion = "kappa-v1", compilerInterfaceVersion = "1", sourceModuleIdentity = "variance.demo"] {
  extension qitUniverseVariance 1;
  decl-node "future-nominal-signature" {
    action = string-value("quotient-equation-omitted");
    requestedRole = string-value("covariant");
  }
}
```

### `main.kp`

```kappa
-- Future extension variance contract fixture.
```

### `suite.ktest`

```text
--! mode check
--! requires capability kcoreText
--! requires capability qitUniverseVariance
--! assertKCoreRejects fixture.kcore E_KCORE_SCHEMA_CERTIFICATE_INVALID
```

## `future/qit_quotient_equation_positive`

A QIT certificate checks quotient equations even when equation evidence erases.

### `fixture.kcore`

```kcore
kcore 1;

module @variance.demo#1000 [languageVersion = "kappa-v1", compilerInterfaceVersion = "1", sourceModuleIdentity = "variance.demo"] {
  extension qitUniverseVariance 1;
  decl-node "future-nominal-signature" {
    action = string-value("quotient-equation-natural");
    requestedRole = string-value("covariant");
  }
}
```

### `main.kp`

```kappa
-- Future extension variance contract fixture.
```

### `suite.ktest`

```text
--! mode check
--! requires capability kcoreText
--! requires capability qitUniverseVariance
--! assertKCoreParses fixture.kcore
```

## `interface/roles_affect_semantic_identity`

Changing an effective role changes interface semantic identity.

### `invariant.kp`

```kappa
public data R.{invariant u} : Type0 = R
```

### `irrelevant.kp`

```kappa
public data R.{irrelevant u} : Type0 = R
```

### `suite.ktest`

```text
--! mode interface
--! assertSemanticHashDiffers irrelevant.kp invariant.kp
--! assertInterfaceContainsUniverseRoles irrelevant.kp R [irrelevant]
--! assertInterfaceContainsUniverseRoles invariant.kp R [invariant]
```

## `kcore/reject_family_argument_mismatch`

The independent checker rejects a schema lift whose target family arguments do not align.

### `bad.kcore`

```kcore
kcore 1;

module @variance.demo#1000 [languageVersion = "kappa-v1", compilerInterfaceVersion = "1", sourceModuleIdentity = "variance.demo"] {
  term-node "schema-lift-family-argument-mismatch" {
    family = global-ref-value(@variance.demo.Box#3400);
    sourceArgument = global-ref-value(@std.Int#10);
    targetArgument = global-ref-value(@std.String#11);
  }
}
```

### `main.kp`

```kappa
-- KCoreText fixture driver.
```

### `suite.ktest`

```text
--! mode check
--! requires capability kcoreText
--! assertKCoreRejects bad.kcore E_UNIVERSE_SCHEMA_LIFT_INVALID
```

## `kcore/reject_family_head_mismatch`

A schema lift cannot change the nominal family head.

### `bad.kcore`

```kcore
kcore 1;

module @variance.demo#1000 [languageVersion = "kappa-v1", compilerInterfaceVersion = "1", sourceModuleIdentity = "variance.demo"] {
  term-node "schema-lift-family-head-mismatch" {
    sourceFamily = global-ref-value(@variance.demo.Left#3500);
    targetFamily = global-ref-value(@variance.demo.Right#3501);
  }
}
```

### `main.kp`

```kappa
-- KCoreText fixture driver.
```

### `suite.ktest`

```text
--! mode check
--! requires capability kcoreText
--! assertKCoreRejects bad.kcore E_UNIVERSE_SCHEMA_LIFT_INVALID
```

## `kcore/reject_forged_schema_certificate`

The independent checker rejects a certificate whose role vector disagrees with the signature.

### `bad.kcore`

```kcore
kcore 1;

module @variance.demo#1000 [languageVersion = "kappa-v1", compilerInterfaceVersion = "1", sourceModuleIdentity = "variance.demo"] {
  schema-certificate @schema:variance.demo.Consumer#2100 for @variance.demo.Consumer#3100
    [checkerVersion = 1, signatureHash = local, saturationArity = 0] {
      roles = [irrelevant];
      clauseKinds = [sort_declaration, point_constructor];
    }

  data @variance.demo.Consumer#3100 .{irrelevant ^u#0} : Type (succ(^u#0))
    certificate @schema:variance.demo.Consumer#2100 {
      constructor @variance.demo.Consumer.Consumer#3101 :
        (((ordinary 0 explicit value %A#0 : Type ^u#0) ->
          ((ordinary omega explicit value %x#1 : %A#0) -> @std.Int#10)) ->
          @variance.demo.Consumer#3100.{^u#0});
    }
}
```

### `main.kp`

```kappa
-- KCoreText fixture driver.
```

### `suite.ktest`

```text
--! mode check
--! requires capability kcoreText
--! assertKCoreRejects bad.kcore E_KCORE_SCHEMA_CERTIFICATE_INVALID
```

## `kcore/reject_runtime_transform_certificate`

A certificate requiring a runtime wrapper or field transformation is rejected.

### `bad.kcore`

```kcore
kcore 1;

module @variance.demo#1000 [languageVersion = "kappa-v1", compilerInterfaceVersion = "1", sourceModuleIdentity = "variance.demo"] {
  schema-certificate @schema:variance.demo.RuntimeMap#2600 for @variance.demo.RuntimeMap#3600
    [checkerVersion = 1, signatureHash = local, saturationArity = 0] {
      roles = [covariant];
      clauseKinds = [sort_declaration, point_constructor];
    }

  decl-node "certificate-runtime-action" {
    family = global-ref-value(@variance.demo.RuntimeMap#3600);
    action = string-value("eta-wrap-function-field");
  }
}
```

### `main.kp`

```kappa
-- KCoreText fixture driver.
```

### `suite.ktest`

```text
--! mode check
--! requires capability kcoreText
--! assertKCoreRejects bad.kcore E_KCORE_SCHEMA_CERTIFICATE_INVALID
```

## `kcore/reject_unsaturated_schema_lift`

A schema lift on a partially applied family is rejected.

### `bad.kcore`

```kcore
kcore 1;

module @variance.demo#1000 [languageVersion = "kappa-v1", compilerInterfaceVersion = "1", sourceModuleIdentity = "variance.demo"] {
  term-node "unsaturated-schema-lift" {
    family = global-ref-value(@variance.demo.Box#3200.{0});
    attemptedTarget = level-value(3);
  }
}
```

### `main.kp`

```kappa
-- KCoreText fixture driver.
```

### `suite.ktest`

```text
--! mode check
--! requires capability kcoreText
--! assertKCoreRejects bad.kcore E_UNIVERSE_SCHEMA_LIFT_INVALID
```

## `kcore/reject_wrong_direction_schema_lift`

A covariant KCore schema lift requires source <= target evidence.

### `bad.kcore`

```kcore
kcore 1;

module @variance.demo#1000 [languageVersion = "kappa-v1", compilerInterfaceVersion = "1", sourceModuleIdentity = "variance.demo"] {
  term-node "schema-lift" {
    family = global-ref-value(@variance.demo.SomeCode#3300);
    from = level-value(3);
    to = level-value(0);
    role = string-value("covariant");
  }
}
```

### `main.kp`

```kappa
-- KCoreText fixture driver.
```

### `suite.ktest`

```text
--! mode check
--! requires capability kcoreText
--! assertKCoreRejects bad.kcore E_UNIVERSE_SCHEMA_LIFT_INVALID
```

## `kcore/roundtrip_mutual_role_fixed_point`

A mutual nominal signature block records separately inferred family role vectors.

### `main.kp`

```kappa
-- KCoreText fixture driver.
```

### `mutual.kcore`

```kcore
kcore 1;

module @variance.demo#1000 [languageVersion = "kappa-v1", compilerInterfaceVersion = "1", sourceModuleIdentity = "variance.demo"] {
  extension nominal-mutual-signatures 1;
  decl-node "mutual-nominal-signature" {
    firstFamily = global-ref-value(@variance.demo.EvenTree#3700);
    secondFamily = global-ref-value(@variance.demo.OddTree#3701);
    firstRoles = string-value("irrelevant");
    secondRoles = string-value("covariant");
  }
}
```

### `suite.ktest`

```text
--! mode check
--! requires capability kcoreText
--! requires capability mutualNominalVariance
--! assertKCoreParses mutual.kcore
--! assertKCoreRoundTrips mutual.kcore
```

## `kcore/roundtrip_schema_lift`

KCoreText serializes an explicit irrelevant schema lift of a saturated family.

### `lift.kcore`

```kcore
kcore 1;

module @variance.demo#1000 [languageVersion = "kappa-v1", compilerInterfaceVersion = "1", sourceModuleIdentity = "variance.demo"] {
  schema-certificate @schema:variance.demo.Phantom#2000 for @variance.demo.Phantom#3000
    [checkerVersion = 1, signatureHash = local, saturationArity = 0] {
      roles = [irrelevant];
      clauseKinds = [sort_declaration, point_constructor];
    }

  data @variance.demo.Phantom#3000 .{irrelevant ^u#0} : Type 0
    certificate @schema:variance.demo.Phantom#2000 {
      constructor @variance.demo.Phantom.Phantom#3001 : @variance.demo.Phantom#3000.{^u#0};
    }

  def @variance.demo.up#4000 :
    ((ordinary omega explicit value %x#0 : @variance.demo.Phantom#3000.{0}) ->
      @variance.demo.Phantom#3000.{3}) {
    body = lambda (ordinary omega explicit value %x#0 : @variance.demo.Phantom#3000.{0}) {
      schema-lift [
        family = @variance.demo.Phantom#3000,
        from = .{0},
        to = .{3},
        certificate = @schema:variance.demo.Phantom#2000,
        roles = [irrelevant],
        targetArgs = ()
      ] %x#0
    };
  }
}
```

### `main.kp`

```kappa
-- KCoreText fixture driver.
```

### `suite.ktest`

```text
--! mode check
--! requires capability kcoreText
--! assertKCoreParses lift.kcore
--! assertKCoreRoundTrips lift.kcore
```

## `kcore/roundtrip_variance_certificate`

KCoreText serializes nominal roles and a locally checked certificate.

### `main.kp`

```kappa
-- KCoreText fixture driver.
```

### `suite.ktest`

```text
--! mode check
--! requires capability kcoreText
--! assertKCoreParses variance.kcore
--! assertKCoreRoundTrips variance.kcore
--! assertKCoreSchemaCertificateValid variance.kcore @variance.demo.Phantom#3000
```

### `variance.kcore`

```kcore
kcore 1;

module @variance.demo#1000 [languageVersion = "kappa-v1", compilerInterfaceVersion = "1", sourceModuleIdentity = "variance.demo"] {
  schema-certificate @schema:variance.demo.Phantom#2000 for @variance.demo.Phantom#3000
    [checkerVersion = 1, signatureHash = local, saturationArity = 0] {
      roles = [irrelevant];
      clauseKinds = [sort_declaration, point_constructor];
    }

  data @variance.demo.Phantom#3000 .{irrelevant ^u#0} : Type 0
    certificate @schema:variance.demo.Phantom#2000 {
      constructor @variance.demo.Phantom.Phantom#3001 : @variance.demo.Phantom#3000.{^u#0};
    }
}
```

## `negative/annotation_covariant_too_permissive`

A covariant annotation is rejected when a function-domain occurrence requires invariance.

### `main.kp`

```kappa
--! mode check
--! assertErrorCount 1
--! assertDiagnostic error E_UNIVERSE_VARIANCE_TOO_PERMISSIVE
--! assertDiagnosticFamily error kappa.universe.variance

data BadConsumer.{covariant u} : Type (succ u) =
    BadConsumer (run : (ordinary 0 A : Type u) -> Int)
```

## `negative/annotation_irrelevant_too_permissive`

An irrelevant annotation is rejected when the signature requires covariance.

### `main.kp`

```kappa
--! mode check
--! assertErrorCount 1
--! assertDiagnostic error E_UNIVERSE_VARIANCE_TOO_PERMISSIVE
--! assertDiagnosticFamily error kappa.universe.variance

data Bad.{irrelevant u} : Type (succ u) =
    Bad (ordinary 0 A : Type u)
```

## `negative/covariant_downcast`

A covariant nominal family cannot be lifted from a larger schema level to a smaller one.

### `main.kp`

```kappa
--! mode check
--! assertErrorCount 1
--! assertDiagnostic error E_UNIVERSE_SCHEMA_LIFT_INVALID
--! assertDiagnosticFamily error kappa.universe.schema-lift

data SomeCode.{covariant u} : Type (succ u) =
    SomeCode (ordinary 0 A : Type u)

down : SomeCode.{3} -> SomeCode.{0}
let down x = x
```

## `negative/invariant_mismatch`

An invariant schema parameter must be definitionally equal at source and target.

### `main.kp`

```kappa
--! mode check
--! assertErrorCount 1
--! assertDiagnostic error E_UNIVERSE_SCHEMA_LIFT_INVALID
--! assertDiagnosticFamily error kappa.universe.schema-lift

data Fixed.{invariant u} : Type0 =
    Fixed

bad : Fixed.{0} -> Fixed.{1}
let bad x = x
```

## `negative/mismatched_family_arguments`

Schema variance does not invent term-argument variance or change GADT indices.

### `main.kp`

```kappa
--! mode check
--! assertErrorCount 1
--! assertDiagnostic error E_UNIVERSE_SCHEMA_LIFT_INVALID
--! assertDiagnosticFamily error kappa.universe.schema-lift

data Box.{irrelevant u}
    (A : Type u)
    : Type u =
    Box (value : A)

bad : Box.{0} Int -> Box.{3} String
let bad x = x
```

## `negative/parametric_field_not_irrelevant`

Parametric observation does not make a constructor-local high-universe witness schema-irrelevant.

### `main.kp`

```kappa
--! mode check
--! assertErrorCount 1
--! assertDiagnostic error E_UNIVERSE_VARIANCE_TOO_PERMISSIVE
--! assertDiagnosticFamily error kappa.universe.variance

data BadWitness.{irrelevant u} : Type0 =
    BadWitness (parametric 0 A : Type u)
```

## `negative/schema_constraint_target_invalid`

A target universe instance must independently satisfy the declaration schema constraints.

### `main.kp`

```kappa
--! mode check
--! assertErrorCount 1
--! assertDiagnostic error E_UNIVERSE_SCHEMA_LIFT_INVALID
--! assertDiagnosticFamily error kappa.universe.schema-lift

-- The constructor field generates the retained schema constraint `succ u <= 3`.
data Bounded.{covariant u} : Type3 =
    Bounded (ordinary 0 A : Type u)

bad : Bounded.{1} -> Bounded.{4}
let bad x = x
```

## `negative/variance_not_applicable_term`

Universe variance annotations are not accepted on ordinary term schemas.

### `main.kp`

```kappa
--! mode check
--! assertErrorCount 1
--! assertDiagnostic error E_UNIVERSE_VARIANCE_NOT_APPLICABLE
--! assertDiagnosticFamily error kappa.universe.variance

id.{covariant u} :
    (A : Type u) ->
    A -> A
let id A x = x
```

## `positive/covariant_up_lift`

A covariant schema role permits a lower-to-higher nominal lift.

### `main.kp`

```kappa
--! mode check
--! assertNoErrors
--! assertSchemaLiftPresent SomeCode

data SomeCode.{covariant u} : Type (succ u) =
    SomeCode (ordinary 0 A : Type u)

up : SomeCode.{0} -> SomeCode.{3}
let up x = x
```

## `positive/equality_irrelevant`

User-definable equality has an irrelevant declaration-universe role.

### `main.kp`

```kappa
--! mode check
--! assertNoErrors
--! assertUniverseRole (=) 0 irrelevant
--! assertSchemaLiftPresent (=)

reuse :
    (A : Type0) ->
    (x : A) ->
    (y : A) ->
    ((=).{0} A x y) ->
    ((=).{3} A x y)
let reuse A x y p = p
```

## `positive/explicit_stricter_covariant`

An explicit covariant role may tighten an inferred irrelevant role.

### `main.kp`

```kappa
--! mode check
--! assertNoErrors
--! assertUniverseRole Empty 0 covariant

data Empty.{covariant u} : Type u
```

## `positive/explicit_stricter_invariant`

An explicit invariant role may tighten any more permissive inferred role.

### `main.kp`

```kappa
--! mode check
--! assertNoErrors
--! assertUniverseRole FixedPhantom 0 invariant

data FixedPhantom.{invariant u} : Type0 =
    FixedPhantom
```

## `positive/gadt_family_arguments_align`

GADT family arguments remain fixed and aligned while only the schema instance is lifted.

### `main.kp`

```kappa
--! mode check
--! assertNoErrors
--! assertUniverseRole Vec 0 irrelevant

data Vec.{u}
    (n : Nat)
    (A : Type u)
    : Type u =
    VNil  : Vec 0 A
    VCons : (head : A) -> (tail : Vec n A) -> Vec (n + 1) A

up :
    (n : Nat) ->
    (A : Type0) ->
    Vec.{0} n A ->
    Vec.{3} n A
let up n A xs = xs
```

## `positive/infer_covariant_ordinary_code`

A constructor-local ordinary type code makes the schema parameter covariant.

### `main.kp`

```kappa
--! mode check
--! assertNoErrors
--! assertUniverseRole SomeCode 0 covariant
--! assertSchemaCertificateValid SomeCode

data SomeCode.{u} : Type (succ u) =
    SomeCode (ordinary 0 A : Type u)
```

## `positive/infer_covariant_parametric_witness`

A constructor-local parametric type witness makes the schema parameter covariant.

### `main.kp`

```kappa
--! mode check
--! assertNoErrors
--! assertUniverseRole SomeWitness 0 covariant
--! assertSchemaCertificateValid SomeWitness

data SomeWitness.{u} : Type0 =
    SomeWitness (parametric 0 A : Type u)
```

## `positive/infer_invariant_function_domain`

A universe occurring in a function-field domain infers invariant, never contravariant.

### `main.kp`

```kappa
--! mode check
--! assertNoErrors
--! assertUniverseRole Consumer 0 invariant
--! assertSchemaCertificateValid Consumer

data Consumer.{u} : Type (succ u) =
    Consumer (run : (ordinary 0 A : Type u) -> Int)
```

## `positive/infer_irrelevant_box`

A universe classifying a fixed saturated family argument infers irrelevant.

### `main.kp`

```kappa
--! mode check
--! assertNoErrors
--! assertUniverseRole Box 0 irrelevant
--! assertSchemaCertificateValid Box

data Box.{u}
    (A : Type u)
    : Type u =
    Box (value : A)
```

## `positive/infer_irrelevant_phantom`

An unused schema parameter infers irrelevant.

### `main.kp`

```kappa
--! mode check
--! assertNoErrors
--! assertUniverseRole Phantom 0 irrelevant
--! assertSchemaCertificateValid Phantom

data Phantom.{u} : Type0 =
    Phantom
```

## `positive/irrelevant_bidirectional_lift`

An irrelevant schema role permits checked lifts in either direction.

### `main.kp`

```kappa
--! mode check
--! assertNoErrors
--! assertSchemaLiftCount 2

data Phantom.{irrelevant u} : Type0 =
    Phantom

up : Phantom.{0} -> Phantom.{3}
let up x = x

down : Phantom.{3} -> Phantom.{0}
let down x = x
```

## `positive/opaque_import_certificate`

An imported opaque family is cumulative only through its verified interface certificate.

### `lib.kp`

```kappa
public opaque data HiddenBox.{irrelevant u}
    (A : Type u)
    : Type u =
    HiddenBox (value : A)
```

### `main.kp`

```kappa
--! mode check
--! assertNoErrors
--! assertUniverseRole HiddenBox 0 irrelevant
--! assertSchemaCertificateValid HiddenBox

import lib exposing HiddenBox

up : HiddenBox.{0} Int -> HiddenBox.{3} Int
let up x = x
```

### `suite.ktest`

```text
--! mode check
--! sources lib.kp main.kp
--! assertNoErrors
```

## `positive/schema_lift_case_coherence`

Pattern matching on a lifted nominal value preserves constructor and iota behavior.

### `main.kp`

```kappa
--! mode check
--! assertNoErrors
--! assertSchemaLiftPresent Box

data Box.{irrelevant u}
    (A : Type u)
    : Type u =
    Box (value : A)

read : Box.{0} Int -> Int
let read x =
    let y : Box.{3} Int = x
    match y
    case Box value ->
        value
```

## `positive/schema_lift_composition`

Nested schema lifts canonicalize to one direct lift.

### `main.kp`

```kappa
--! mode check
--! assertNoErrors
--! assertSchemaLiftCount 1

data Phantom.{irrelevant u} : Type0 =
    Phantom

compose : Phantom.{0} -> Phantom.{3}
let compose x =
    let y : Phantom.{1} = x
    let z : Phantom.{3} = y
    z
```

## `positive/trait_evidence_irrelevant`

A nominal trait evidence family may infer irrelevant universe variance.

### `main.kp`

```kappa
--! mode check
--! assertNoErrors
--! assertUniverseRole Render 0 irrelevant
--! assertSchemaCertificateValid Render

trait Render.{u} (A : Type u) =
    render : A -> String
```

## `positive/typebelow_covariant`

The standard bounded ordinary-code package is covariant in its declaration universe.

### `main.kp`

```kappa
--! mode check
--! assertNoErrors
--! assertUniverseRole TypeBelow 0 covariant
--! assertSchemaLiftPresent TypeBelow

up : TypeBelow.{1} -> TypeBelow.{3}
let up x = x
```
