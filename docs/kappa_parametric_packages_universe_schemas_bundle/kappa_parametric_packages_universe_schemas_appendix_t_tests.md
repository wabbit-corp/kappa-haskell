# Separate Appendix T conformance tests: parametric packages, universe schemas, and KCore completion

These suites are intentionally separate from the language specification. Each leaf directory is one independent Appendix T directory suite.

**Suite count:** 71

Every suite is expected to produce harness outcome **pass**. A negative suite passes when compilation or KCore verification is rejected with the asserted diagnostic.

## data

### `negative/constructor_ordinary_type_code_too_large`

An explicit ordinary type-code constructor field remains subject to constructor-size checking.

Source expectation: **reject**. Harness outcome: **pass**.

#### `main.kp`

```kappa
--! mode check
--! assertErrorCount 1
--! assertDiagnostic error E_DATA_CONSTRUCTOR_FIELD_UNIVERSE
--! assertDiagnosticFamily error kappa.universe.constructor-size

data BadCode : Type0 =
    BadCode (ordinary 0 T : Type3)
```

### `positive/constructor_parametric_default_small`

A constructor-local Type binder defaults parametric and does not enlarge a phantom data type.

Source expectation: **accept**. Harness outcome: **pass**.

#### `main.kp`

```kappa
--! mode check
--! assertNoErrors

data PhantomCode : Type0 =
    PhantomCode (T : Type3)
```

## equality

### `positive/explicit_universe_schema_equality`

A user-defined equality family uses ordinary explicit declaration universe-schema syntax.

Source expectation: **accept**. Harness outcome: **pass**.

#### `main.kp`

```kappa
--! mode check
--! assertNoErrors

data MyEq.{u}
    (@parametric 0 A : Type u)
    (parametric 0 x : A)
    (parametric 0 y : A)
    : Type u =

    MyRefl : MyEq x x

myRefl :
    forall A x.
    MyEq x x

let myRefl A x =
    MyRefl
```

### `positive/io_of_type_equality`

A universe-polymorphic effect/container may contain equality between types.

Source expectation: **accept**. Harness outcome: **pass**.

#### `main.kp`

```kappa
--! mode check
--! assertNoErrors

type EqualityAction =
    IO String (Type0 = Type0)
```

### `positive/same_dyn_rep_parametric_endpoints`

The required sameDynRep shape typechecks through ordinary parametric equality endpoints.

Source expectation: **accept**. Harness outcome: **pass**.

#### `main.kp`

```kappa
--! mode check
--! assertNoErrors

import std.gradual.(type DynRep, term sameDynRep)

sameDynRepShape :
    forall a b.
    DynRep a ->
    DynRep b ->
    Dec (a = b)

let sameDynRepShape a b =
    sameDynRep
```

### `positive/universe_polymorphic_equality`

Ordinary equality between type values is accepted through universe-polymorphic equality.

Source expectation: **accept**. Harness outcome: **pass**.

#### `main.kp`

```kappa
--! mode check
--! assertNoErrors

data Equal.{u}
    (@parametric 0 A : Type u)
    (parametric 0 x : A)
    (parametric 0 y : A)
    : Type u =

    EqualRefl : Equal x x

same :
    forall a.
    Equal a a

let same a =
    EqualRefl
```

## higher-kinded

### `positive/higher_kinded_functor_shape`

An inferred higher-kinded trait parameter defaults recursively to parametric mode.

Source expectation: **accept**. Harness outcome: **pass**.

#### `main.kp`

```kappa
--! mode check
--! assertNoErrors

trait MiniFunctor f =
    map :
        forall a b.
        (a -> b) ->
        f a ->
        f b
```

### `positive/higher_kinded_monad_shape`

Monad-style higher-kinded parametric application is accepted.

Source expectation: **accept**. Harness outcome: **pass**.

#### `main.kp`

```kappa
--! mode check
--! assertNoErrors

trait MiniMonad
    (m : (A : Type) -> Type) =

    pure :
        forall a.
        a -> m a

    bind :
        forall a b.
        m a ->
        (a -> m b) ->
        m b
```

### `positive/type_alias_identity_constructor`

A transparent alias whose body is a parametric witness exposes a parametric higher-kinded facet.

Source expectation: **accept**. Harness outcome: **pass**.

#### `main.kp`

```kappa
--! mode check
--! assertNoErrors

type Id A =
    A

useF :
    (F : (A : Type) -> Type) ->
    (A : Type) ->
    F A ->
    F A

let useF F A x =
    x

idInt :
    Id Int ->
    Id Int

let idInt x =
    useF Id Int x
```

### `positive/type_constructor_argument_option`

A named type constructor can instantiate a higher-kinded parametric binder.

Source expectation: **accept**. Harness outcome: **pass**.

#### `main.kp`

```kappa
--! mode check
--! assertNoErrors

useF :
    (F : (A : Type) -> Type) ->
    (A : Type) ->
    F A ->
    F A

let useF F A x =
    x

optionId :
    Option Int ->
    Option Int

let optionId x =
    useF Option Int x
```

### `positive/type_constructor_partial_application`

A partial type-constructor application can instantiate a parametric higher-kinded binder.

Source expectation: **accept**. Harness outcome: **pass**.

#### `main.kp`

```kappa
--! mode check
--! assertNoErrors

useF :
    (F : (A : Type) -> Type) ->
    (A : Type) ->
    F A ->
    F A

let useF F A x =
    x

resultId :
    Result String Int ->
    Result String Int

let resultId x =
    useF (Result String) Int x
```

## kcore

### `kcore/parse_and_roundtrip_constructor_instantiation`

Constructor declarations and construction sites carry explicit universe instantiations.

Source expectation: **accept**. Harness outcome: **pass**.

#### `constructor.kcore`

```kcore
kcore 1;

module @tests.kcore.constructor_instantiation#1101 [
  languageVersion = "kappa-v1",
  compilerInterfaceVersion = "1",
  sourceModuleIdentity = "tests.kcore.constructor_instantiation"
] {
  data @tests.kcore.constructor_instantiation.Box#2200 .{^u#0}
    (parametric parametric 0 explicit value %A#0 : Type ^u#0)
    : Type ^u#0
  {
    constructor @tests.kcore.constructor_instantiation.Box.Box#2201 .{^u#0} :
      ((ordinary ordinary omega explicit value %value#1 : %A#0) ->
        @tests.kcore.constructor_instantiation.Box#2200.{^u#0} %A#0);
  }

  axiom ordinary @tests.kcore.constructor_instantiation.one#2203 :
    @std.prelude.Int#baeedb0f51b49732;

  def ordinary @tests.kcore.constructor_instantiation.make#2202 :
    @tests.kcore.constructor_instantiation.Box#2200.{0} @std.prelude.Int#baeedb0f51b49732
  {
    body =
      construct @tests.kcore.constructor_instantiation.Box.Box#2201.{0}(
        @tests.kcore.constructor_instantiation.one#2203
      );
  }
}
```

#### `main.kp`

```kappa
-- fixture-only suite
```

#### `suite.ktest`

```text
--! mode check
--! requires capability kcoreText
--! assertKCoreParses constructor.kcore
--! assertKCoreRoundTrips constructor.kcore
```

### `kcore/parse_and_roundtrip_identity`

Canonical identity KCoreText parses, verifies, and round-trips.

Source expectation: **accept**. Harness outcome: **pass**.

#### `identity.kcore`

```kcore
kcore 1;

module @tests.kcore.identity#1001 [
  languageVersion = "kappa-v1",
  compilerInterfaceVersion = "1",
  sourceModuleIdentity = "tests.kcore.identity"
] {
  def ordinary @tests.kcore.identity.id#2001 .{^u#0} :
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

#### `main.kp`

```kappa
-- KCoreText suite root
```

#### `suite.ktest`

```text
--! mode check
--! requires capability kcoreText
--! assertKCoreParses identity.kcore
--! assertKCoreRoundTrips identity.kcore
```

### `kcore/parse_and_roundtrip_level_certificate`

A verified closed level certificate parses and round-trips.

Source expectation: **accept**. Harness outcome: **pass**.

#### `certificate.kcore`

```kcore
kcore 1;

module @tests.kcore.certificate#1102 [
  languageVersion = "kappa-v1",
  compilerInterfaceVersion = "1",
  sourceModuleIdentity = "tests.kcore.certificate"
] {
  level-certificate @certificate.tests.kcore.zero_le_omega#5001 :
    0 <= omega
  {
    closed;
  }

  def ordinary @tests.kcore.certificate.raise#2300 :
    Type omega
  {
    body =
      lift [0 <= omega by certificate(@certificate.tests.kcore.zero_le_omega#5001)]
        @std.prelude.Int#baeedb0f51b49732;
  }
}
```

#### `main.kp`

```kappa
-- fixture-only suite
```

#### `suite.ktest`

```text
--! mode check
--! requires capability kcoreText
--! assertKCoreParses certificate.kcore
--! assertKCoreRoundTrips certificate.kcore
```

### `kcore/parse_and_roundtrip_lift`

KCoreText with explicit universe lift parses, verifies, and round-trips.

Source expectation: **accept**. Harness outcome: **pass**.

#### `lift.kcore`

```kcore
kcore 1;

module @tests.kcore.lift#1002 [
  languageVersion = "kappa-v1",
  compilerInterfaceVersion = "1",
  sourceModuleIdentity = "tests.kcore.lift"
] {
  extension impl.kappa 1;

  axiom parametric @tests.kcore.lift.le#3001 .{^u#0, ^v#1} :
    apply @std.typelevel.LevelLe#baf08d09a165fea5
      (explicit term-node "impl.kappa.level-value" {
        level = level-value(^u#0);
      },
       explicit term-node "impl.kappa.level-value" {
        level = level-value(^v#1);
      });

  def ordinary @tests.kcore.lift.raise#2002 .{^u#0, ^v#1} :
    ((ordinary ordinary omega explicit value %A#0 : Type ^u#0) ->
      Type ^v#1)
  {
    body =
      lambda (ordinary ordinary omega explicit value %A#0 : Type ^u#0) {
        lift [^u#0 <= ^v#1 by @tests.kcore.lift.le#3001.{^u#0, ^v#1}] %A#0
      };
  }
}
```

#### `main.kp`

```kappa
-- KCoreText suite root
```

#### `suite.ktest`

```text
--! mode check
--! requires capability kcoreText
--! assertKCoreParses lift.kcore
--! assertKCoreRoundTrips lift.kcore
```

### `kcore/parse_and_roundtrip_local_universe`

KCoreText serializes and round-trips a local declaration universe telescope.

Source expectation: **accept**. Harness outcome: **pass**.

#### `local.kcore`

```kcore
kcore 1;

module @tests.kcore.local_universe#1100 [
  languageVersion = "kappa-v1",
  compilerInterfaceVersion = "1",
  sourceModuleIdentity = "tests.kcore.local_universe"
] {
  def ordinary @tests.kcore.local_universe.outer#2100 .{^u#0} :
    ((parametric parametric 0 explicit value %A#0 : Type ^u#0) ->
      ((ordinary ordinary omega explicit value %x#1 : %A#0) -> %A#0))
  {
    body =
      lambda (parametric parametric 0 explicit value %A#0 : Type ^u#0) {
        lambda (ordinary ordinary omega explicit value %x#1 : %A#0) {
          letrec {
            def ordinary %localId#2 .{^v#1} :
              ((parametric parametric 0 explicit value %B#3 : Type ^v#1) ->
                ((ordinary ordinary omega explicit value %y#4 : %B#3) -> %B#3))
            {
              body =
                lambda (parametric parametric 0 explicit value %B#3 : Type ^v#1) {
                  lambda (ordinary ordinary omega explicit value %y#4 : %B#3) {
                    %y#4
                  }
                };
            }
          } in
            apply
              (apply %localId#2.{^u#0} %A#0)
              %x#1
        }
      };
  }
}
```

#### `main.kp`

```kappa
-- fixture-only suite
```

#### `suite.ktest`

```text
--! mode check
--! requires capability kcoreText
--! assertKCoreParses local.kcore
--! assertKCoreRoundTrips local.kcore
```

### `kcore/reject_forged_level_certificate`

A false closed level certificate is rejected by the independent certificate checker.

Source expectation: **reject**. Harness outcome: **pass**.

#### `bad.kcore`

```kcore
kcore 1;

module @tests.kcore.bad_certificate#1103 [
  languageVersion = "kappa-v1",
  compilerInterfaceVersion = "1",
  sourceModuleIdentity = "tests.kcore.bad_certificate"
] {
  level-certificate @certificate.tests.kcore.bad#5002 :
    omega + 1 <= omega
  {
    closed;
  }
}
```

#### `main.kp`

```kappa
-- fixture-only suite
```

#### `suite.ktest`

```text
--! mode check
--! requires capability kcoreText
--! assertKCoreRejects bad.kcore E_KCORE_LEVEL_CERTIFICATE_INVALID
```

### `kcore/reject_invalid_lift`

The independent KCore checker rejects an invalid cumulative lift.

Source expectation: **reject**. Harness outcome: **pass**.

#### `bad.kcore`

```kcore
kcore 1;
module @tests.kcore.badlift#1005 [languageVersion = "kappa-v1", compilerInterfaceVersion = "1", sourceModuleIdentity = "tests.kcore.badlift"] {
  axiom ordinary @tests.kcore.badlift.notProof#2006 : Type 0;
  def ordinary @tests.kcore.badlift.bad#2005 : Type 0 {
    body = lift [1 <= 0 by @tests.kcore.badlift.notProof#2006] @std.prelude.Int#9001;
  }
}
```

#### `main.kp`

```kappa
-- KCoreText suite root
```

#### `suite.ktest`

```text
--! mode check
--! requires capability kcoreText
--! assertKCoreRejects bad.kcore E_KCORE_TEXT_INVALID
```

### `kcore/reject_missing_mode`

Canonical KCoreText requires an explicit observation mode on every binder.

Source expectation: **reject**. Harness outcome: **pass**.

#### `bad.kcore`

```kcore
kcore 1;
module @tests.kcore.bad#1003 [languageVersion = "kappa-v1", compilerInterfaceVersion = "1", sourceModuleIdentity = "tests.kcore.bad"] {
  axiom ordinary @tests.kcore.bad.f#2003 : ((0 explicit value %A#0 : Type 0) -> %A#0);
}
```

#### `main.kp`

```kappa
-- KCoreText suite root
```

#### `suite.ktest`

```text
--! mode check
--! requires capability kcoreText
--! assertKCoreRejects bad.kcore E_KCORE_TEXT_INVALID
```

### `kcore/reject_parametric_promotion`

The independent KCore checker rejects a hand-written parametric promotion.

Source expectation: **reject**. Harness outcome: **pass**.

#### `bad.kcore`

```kcore
kcore 1;
module @tests.kcore.badpromotion#1004 [languageVersion = "kappa-v1", compilerInterfaceVersion = "1", sourceModuleIdentity = "tests.kcore.badpromotion"] {
  def ordinary @tests.kcore.badpromotion.bad#2004 .{^u#0} :
    ((parametric parametric 0 explicit value %A#0 : Type ^u#0) -> Type ^u#0)
  {
    body =
      lambda (parametric parametric 0 explicit value %A#0 : Type ^u#0) {
        %A#0
      };
  }
}
```

#### `main.kp`

```kappa
-- KCoreText suite root
```

#### `suite.ktest`

```text
--! mode check
--! requires capability kcoreText
--! assertKCoreRejects bad.kcore E_PARAMETRIC_TYPE_PROMOTION
```

### `kcore/reject_unsupported_version`

KCoreText rejects unsupported schema versions deterministically.

Source expectation: **reject**. Harness outcome: **pass**.

#### `future.kcore`

```kcore
kcore 999;
module @tests.kcore.future#1006 [languageVersion = "kappa-v1", compilerInterfaceVersion = "999", sourceModuleIdentity = "tests.kcore.future"] {
}
```

#### `main.kp`

```kappa
-- KCoreText suite root
```

#### `suite.ktest`

```text
--! mode check
--! requires capability kcoreText
--! assertKCoreRejects future.kcore E_KCORE_TEXT_UNSUPPORTED_VERSION
```

### `positive/kcore_stage_roundtrip`

Generated KCoreText parses, verifies, prints canonically, and round-trips.

Source expectation: **accept**. Harness outcome: **pass**.

#### `main.kp`

```kappa
--! mode check
--! requires capability stageDumps
--! requires capability kcoreText
--! assertNoErrors
--! assertStageDumpRoundTrips KCore

id :
    (A : Type) ->
    A -> A

let id A x =
    x
```

## metatheory

### `negative/hurkens_fragment`

A larger Hurkens-shaped fragment must fail at a modal or universe obligation rather than being accepted.

Source expectation: **reject**. Harness outcome: **pass**.

#### `main.kp`

```kappa
--! mode check
--! assertErrorCount 1
--! assertDiagnostic error E_PARAMETRIC_TYPE_PROMOTION
--! assertDiagnosticFamily error kappa.type.parametric-promotion

-- A direct surface analogue of the code-producing Pi operation required by
-- Hurkens-style universe encodings.  The parametric inputs may form a type
-- expression, but that expression may not be returned as an ordinary code.
piCode :
    (parametric 0 A : Type) ->
    (parametric 0 B : A -> Type) ->
    Type

let piCode A B =
    (x : A) -> B x
```

### `negative/hurkens_ordinary_small_universe`

The ordinary route to a small universe of all small types is blocked by predicativity.

Source expectation: **reject**. Harness outcome: **pass**.

#### `main.kp`

```kappa
--! mode check
--! assertErrorCount 1
--! assertDiagnostic error E_DATA_CONSTRUCTOR_FIELD_UNIVERSE
--! assertDiagnosticFamily error kappa.universe.constructor-size

data SmallUniverse : Type0 =
    Code (ordinary 0 T : Type0)
```

### `negative/hurkens_parametric_code_escape`

The parametric route to a universe-code-producing Pi is blocked at promotion.

Source expectation: **reject**. Harness outcome: **pass**.

#### `main.kp`

```kappa
--! mode check
--! assertErrorCount 1
--! assertDiagnostic error E_PARAMETRIC_TYPE_PROMOTION
--! assertDiagnosticFamily error kappa.type.parametric-promotion

piCode :
    (A : Type) ->
    (A -> Type) ->
    Type

let piCode A B =
    (x : A) -> B x
```

## observation

### `negative/parametric_type_constructor_application_promotion`

A type constructor applied to a parametric type remains a parametric type code and cannot be returned ordinarily.

Source expectation: **reject**. Harness outcome: **pass**.

#### `main.kp`

```kappa
--! mode check
--! assertErrorCount 1
--! assertDiagnostic error E_PARAMETRIC_TYPE_PROMOTION
--! assertDiagnosticFamily error kappa.type.parametric-promotion

bad :
    (A : Type) ->
    Type

let bad A =
    Option A
```

### `positive/parametric_constant_application_ordinary_result`

A genuinely constant polymorphic value result need not inherit a parametric type-argument dependency.

Source expectation: **accept**. Harness outcome: **pass**.

#### `main.kp`

```kappa
--! mode check
--! assertNoErrors

constant :
    forall A.
    Int

let constant A =
    1

useConstant :
    (A : Type) ->
    Int

let useConstant A =
    constant @A
```

## parametricity

### `negative/parametric_alias_launder`

A local alias does not launder parametric observation into ordinary observation.

Source expectation: **reject**. Harness outcome: **pass**.

#### `main.kp`

```kappa
--! mode check
--! assertErrorCount 1
--! assertDiagnostic error E_PARAMETRIC_TYPE_PROMOTION
--! assertDiagnosticFamily error kappa.type.parametric-promotion

bad :
    (A : Type) ->
    Type

let bad A =
    type Alias = A
    Alias
```

### `negative/parametric_higher_kind_launder`

A higher-kinded parametric witness cannot be returned as an ordinary type-former value.

Source expectation: **reject**. Harness outcome: **pass**.

#### `main.kp`

```kappa
--! mode check
--! assertErrorCount 1
--! assertDiagnostic error E_PARAMETRIC_TYPE_PROMOTION
--! assertDiagnosticFamily error kappa.type.parametric-promotion

bad :
    (F : (A : Type) -> Type) ->
    ((A : Type) -> Type)

let bad F =
    F
```

### `negative/parametric_pattern_launder`

A constructor pattern preserves the field mode and cannot leak a type code.

Source expectation: **reject**. Harness outcome: **pass**.

#### `main.kp`

```kappa
--! mode check
--! assertErrorCount 1
--! assertDiagnostic error E_PARAMETRIC_TYPE_PROMOTION
--! assertDiagnosticFamily error kappa.type.parametric-promotion

data Some : Type =
    Some (A : Type) (value : A)

bad :
    Some -> Type

let bad x =
    match x
    case Some A value ->
        A
```

### `negative/parametric_record_projection_launder`

A projected parametric field cannot be returned as an ordinary type code.

Source expectation: **reject**. Harness outcome: **pass**.

#### `main.kp`

```kappa
--! mode check
--! assertErrorCount 1
--! assertDiagnostic error E_PARAMETRIC_TYPE_PROMOTION
--! assertDiagnosticFamily error kappa.type.parametric-promotion

type Sig : Type =
    (A : Type, value : A)

bad :
    Sig -> Type

let bad s =
    s.A
```

### `negative/parametric_return_as_type`

A default parametric Type binder cannot be returned as an ordinary universe value.

Source expectation: **reject**. Harness outcome: **pass**.

#### `main.kp`

```kappa
--! mode check
--! assertErrorCount 1
--! assertDiagnostic error E_PARAMETRIC_TYPE_PROMOTION
--! assertDiagnosticFamily error kappa.type.parametric-promotion

bad :
    (A : Type) ->
    Type

let bad A =
    A
```

### `negative/parametric_to_ordinary_consumer`

A parametric higher-kinded witness cannot instantiate an ordinary binder.

Source expectation: **reject**. Harness outcome: **pass**.

#### `main.kp`

```kappa
--! mode check
--! assertErrorCount 1
--! assertDiagnostic error E_PARAMETRIC_TYPE_PROMOTION
--! assertDiagnosticFamily error kappa.type.parametric-promotion

bad :
    (F : (A : Type) -> Type) ->
    ((ordinary 0 G : (A : Type) -> Type) -> Int) ->
    Int

let bad F consume =
    consume F
```

## patterns

### `positive/parametric_pattern_repack`

Constructor patterns preserve parametric observation mode and permit repacking.

Source expectation: **accept**. Harness outcome: **pass**.

#### `main.kp`

```kappa
--! mode check
--! assertNoErrors

data Some : Type =
    Some (A : Type) (value : A)

repack :
    Some -> Some

let repack x =
    match x
    case Some A value ->
        Some A value
```

## records

### `positive/high_universe_parametric_field_small`

A high-universe parametric field does not raise the record universe by itself.

Source expectation: **accept**. Harness outcome: **pass**.

#### `main.kp`

```kappa
--! mode check
--! assertNoErrors

type Tag : Type =
    (parametric 0 T : Type3,
     value : Int)
```

### `positive/high_universe_payload_is_large`

A payload whose type is the high-universe witness still raises the enclosing universe.

Source expectation: **accept**. Harness outcome: **pass**.

#### `main.kp`

```kappa
--! mode check
--! assertNoErrors

type LargePack : Type3 =
    (parametric 0 T : Type3,
     value : T)
```

### `positive/parametric_record_projection`

Projection exposes a parametric type witness that may remain in a dependent result type.

Source expectation: **accept**. Harness outcome: **pass**.

#### `main.kp`

```kappa
--! mode check
--! assertNoErrors

type Sig : Type =
    (A : Type, value : A)

get :
    (s : Sig) ->
    s.A

let get s =
    s.value
```

### `positive/parametric_record_repack`

A projected parametric type may be repackaged into another parametric field.

Source expectation: **accept**. Harness outcome: **pass**.

#### `main.kp`

```kappa
--! mode check
--! assertNoErrors

type Sig : Type =
    (A : Type, value : A)

copy :
    Sig -> Sig

let copy s =
    (A = s.A, value = s.value)
```

### `positive/polymorphic_record_is_small`

A record containing a polymorphic function remains in Type.

Source expectation: **accept**. Harness outcome: **pass**.

#### `main.kp`

```kappa
--! mode check
--! assertNoErrors

type Poly : Type =
    (A : Type) -> A -> A

type Box : Type =
    (f : Poly)

boxId :
    Box -> Box

let boxId b =
    b
```

### `positive/stored_polymorphic_function_on_box`

A stored polymorphic function may be instantiated at the record that stores it.

Source expectation: **accept**. Harness outcome: **pass**.

#### `main.kp`

```kappa
--! mode check
--! assertNoErrors

type Poly : Type =
    (A : Type) -> A -> A

type Box : Type =
    (f : Poly)

useStored :
    Box -> Box

let useStored b =
    b.f Box b
```

## surface

### `positive/default_type_binder_parametric`

A source-written Type binder defaults to parametric mode, quantity 0, and a hidden declaration universe.

Source expectation: **accept**. Harness outcome: **pass**.

#### `main.kp`

```kappa
--! mode check
--! assertNoErrors

id :
    (A : Type) ->
    A ->
    A

let id A x =
    x
```

### `positive/explicit_parametric_equivalent`

Explicit parametric syntax agrees with the default Type-binder elaboration.

Source expectation: **accept**. Harness outcome: **pass**.

#### `main.kp`

```kappa
--! mode check
--! assertNoErrors

id :
    (parametric 0 A : Type) ->
    A ->
    A

let id A x =
    x
```

### `positive/forall_defaults_parametric`

`forall A.` elaborates to an implicit parametric quantity-0 Type binder with a hidden universe.

Source expectation: **accept**. Harness outcome: **pass**.

#### `main.kp`

```kappa
--! mode check
--! assertNoErrors

polyId :
    forall A.
    A -> A

let polyId A x =
    x
```

### `positive/forall_explicit_ordinary`

`forall (ordinary A : Type)` expresses an erased but ordinary-observable type code.

Source expectation: **accept**. Harness outcome: **pass**.

#### `main.kp`

```kappa
--! mode check
--! assertNoErrors

returnCode :
    forall (ordinary A : Type).
    Type

let returnCode A =
    A
```

### `positive/ordinary_erased_type_codes`

An ordinary quantity-0 type-code binder is statically observable while remaining runtime-erased.

Source expectation: **accept**. Harness outcome: **pass**.

#### `main.kp`

```kappa
--! mode check
--! assertNoErrors

arrowCode :
    (ordinary 0 A : Type) ->
    (ordinary 0 B : Type) ->
    Type

let arrowCode A B =
    A -> B
```

### `positive/ordinary_unrestricted_type_codes`

Ordinary type-code production is legal and does not require typecase or reflection.

Source expectation: **accept**. Harness outcome: **pass**.

#### `main.kp`

```kappa
--! mode check
--! assertNoErrors

chooseCode :
    Bool ->
    Type

let chooseCode flag =
    if flag then Int else String

arrowCode :
    (ordinary A : Type) ->
    (ordinary B : Type) ->
    Type

let arrowCode A B =
    A -> B
```

### `positive/parametric_non_kind_domain_allowed`

Explicit parametric observation is legal for a non-kind domain when no impredicative formation claim is needed.

Source expectation: **accept**. Harness outcome: **pass**.

#### `main.kp`

```kappa
--! mode check
--! assertNoErrors

ignoreNat :
    (parametric 0 n : Nat) ->
    Int

let ignoreNat n =
    0
```

### `positive/type0_does_not_change_mode`

An explicit Type0 annotation fixes only the universe and remains parametric by default.

Source expectation: **accept**. Harness outcome: **pass**.

#### `main.kp`

```kappa
--! mode check
--! assertNoErrors

id0 :
    (A : Type0) ->
    A ->
    A

let id0 A x =
    x
```

## traits

### `positive/trait_evidence_relative_parametricity`

Behavior may depend on an explicit dictionary while the type parameter remains parametric.

Source expectation: **accept**. Harness outcome: **pass**.

#### `main.kp`

```kappa
--! mode check
--! assertNoErrors

trait Tagged A =
    tag : Int

readTag :
    (A : Type) ->
    (evidence : Tagged A) ->
    A ->
    Int

let readTag A evidence value =
    evidence.tag
```

## typelevel

### `positive/typelevel_algebra_laws`

Checked TypeLevel algebra laws expose the specified commutative addition behavior.

Source expectation: **accept**. Harness outcome: **pass**.

#### `main.kp`

```kappa
--! mode check
--! assertNoErrors

oneOmegaCommutes :
    one + omega = omega + one

let oneOmegaCommutes =
    typeLevelOnePlusOmega

omegaDoubles :
    omega + omega = omega + omega

let omegaDoubles =
    refl
```

### `positive/typelevel_erased_binder`

A quantity-0 TypeLevel binder erases by quantity rather than by its type name.

Source expectation: **accept**. Harness outcome: **pass**.

#### `main.kp`

```kappa
--! mode check
--! assertNoErrors

ignoreLevel :
    (0 level : TypeLevel) ->
    Int

let ignoreLevel level =
    0
```

### `positive/typelevel_mixed_static_runtime_use`

One TypeLevel binder may occur statically as an index and dynamically as a returned value.

Source expectation: **accept**. Harness outcome: **pass**.

#### `main.kp`

```kappa
--! mode check
--! assertNoErrors

rememberLevel :
    (level : TypeLevel) ->
    (parametric 0 T : Type level) ->
    TypeLevel

let rememberLevel level T =
    level
```

### `positive/typelevel_runtime_add`

Ordinary runtime TypeLevel addition is available through the standard Add instance.

Source expectation: **accept**. Harness outcome: **pass**.

#### `main.kp`

```kappa
--! mode check
--! assertNoErrors

addLevels :
    TypeLevel ->
    TypeLevel ->
    TypeLevel

let addLevels x y =
    x + y
```

### `positive/typelevel_runtime_compare`

An ordinary TypeLevel value and Ord TypeLevel operation may remain runtime-relevant.

Source expectation: **accept**. Harness outcome: **pass**.

#### `main.kp`

```kappa
--! mode check
--! assertNoErrors

compareLevels :
    TypeLevel ->
    TypeLevel ->
    Ordering

let compareLevels x y =
    compare x y
```

## universes

### `negative/inconsistent_level_bound`

A strict self-bound cannot justify a universe classifier.

Source expectation: **reject**. Harness outcome: **pass**.

#### `main.kp`

```kappa
--! mode check
--! assertErrorCount 1
--! assertDiagnostic error E_UNIVERSE_SELF_CONTAINMENT
--! assertDiagnosticFamily error kappa.universe.constraint

bad :
    (ordinary 0 level : TypeLevel) ->
    (@0 impossible : level < level) ->
    Type level
```

### `negative/inconsistent_level_transitive_cycle`

A transitive strict level cycle is deterministically rejected as self-containment.

Source expectation: **reject**. Harness outcome: **pass**.

#### `main.kp`

```kappa
--! mode check
--! assertErrorCount 1
--! assertDiagnostic error E_UNIVERSE_SELF_CONTAINMENT
--! assertDiagnosticFamily error kappa.universe.constraint

bad :
    (ordinary 0 i : TypeLevel) ->
    (ordinary 0 j : TypeLevel) ->
    (@0 p : i < j) ->
    (@0 q : j <= i) ->
    Int
```

### `negative/type0_self_containment`

Ordinary predicative universes still reject Type0 : Type0.

Source expectation: **reject**. Harness outcome: **pass**.

#### `main.kp`

```kappa
--! mode check
--! assertErrorCount 1
--! assertDiagnostic error E_UNIVERSE_SELF_CONTAINMENT
--! assertDiagnosticFamily error kappa.universe.constraint

bad : Type0
let bad = Type0
```

### `negative/unbounded_ordinary_type_package`

An unbounded package of ordinary type codes has no external universe ceiling.

Source expectation: **reject**. Harness outcome: **pass**.

#### `main.kp`

```kappa
--! mode check
--! assertErrorCount 1
--! assertDiagnostic error E_UNIVERSE_UNBOUNDED_TELESCOPE
--! assertDiagnosticFamily error kappa.universe.unbounded-telescope

type AllOrdinaryCodes =
    (ordinary 0 level : TypeLevel,
     ordinary 0 T : Type level)
```

### `negative/unbounded_parametric_projection_promotion`

A projected unbounded parametric witness cannot be returned as an ordinary type code.

Source expectation: **reject**. Harness outcome: **pass**.

#### `main.kp`

```kappa
--! mode check
--! assertErrorCount 1
--! assertDiagnostic error E_PARAMETRIC_TYPE_PROMOTION
--! assertDiagnosticFamily error kappa.type.parametric-promotion

type AnyTypeWitness : Type =
    (ordinary 0 level : TypeLevel,
     T : Type level)

bad :
    (p : AnyTypeWitness) ->
    Type p.level

let bad p =
    p.T
```

### `negative/unbounded_typelevel_telescope`

A first-class level-dependent telescope needs an external universe ceiling.

Source expectation: **reject**. Harness outcome: **pass**.

#### `main.kp`

```kappa
--! mode check
--! assertErrorCount 1
--! assertDiagnostic error E_UNIVERSE_UNBOUNDED_TELESCOPE
--! assertDiagnosticFamily error kappa.universe.unbounded-telescope

type AllTypes =
    (ordinary 0 level : TypeLevel,
     ordinary 0 T : Type level)
```

### `negative/universe_schema_arity`

Explicit universe instantiation with the wrong arity is rejected.

Source expectation: **reject**. Harness outcome: **pass**.

#### `main.kp`

```kappa
--! mode check
--! assertErrorCount 1
--! assertDiagnostic error E_UNIVERSE_SCHEMA_ARITY_MISMATCH
--! assertDiagnosticFamily error kappa.universe.schema-arity

data Box.{u}
    (A : Type u)
    : Type u =
    Box (value : A)

type Bad =
    Box.{0, 1} Int
```

### `positive/local_universe_generalization`

A local definition generalizes and freshly instantiates a local universe telescope.

Source expectation: **accept**. Harness outcome: **pass**.

#### `main.kp`

```kappa
--! mode check
--! assertNoErrors

useLocal :
    (A : Type) ->
    A -> A

let useLocal A x =
    let localId B y = y
    localId A x
```

### `positive/principal_universe_choose_type`

A code-producing function receives the least result universe justified by its branches.

Source expectation: **accept**. Harness outcome: **pass**.

#### `main.kp`

```kappa
--! mode check
--! assertNoErrors

chooseType :
    Bool -> Type

let chooseType b =
    if b then Int else String

type Chosen : Type0 =
    chooseType True
```

### `positive/principal_universe_payload`

A constructor payload supplies the lower bound for the principal result universe.

Source expectation: **accept**. Harness outcome: **pass**.

#### `main.kp`

```kappa
--! mode check
--! assertNoErrors

data PayloadBox
    (A : Type)
    : Type =
    PayloadBox (value : A)

-- Type2 : Type3, so the payload forces the principal result to Type3.
type HighBox : Type3 =
    PayloadBox Type2
```

### `positive/principal_universe_phantom`

Principal inference minimizes a phantom family result while generalizing its parameter level.

Source expectation: **accept**. Harness outcome: **pass**.

#### `main.kp`

```kappa
--! mode check
--! assertNoErrors

data Phantom
    (A : Type)
    : Type =
    Phantom

-- The high-level parameter is phantom; the result classifier is minimized.
type SmallPhantom : Type0 =
    Phantom Type3
```

### `positive/proof_bounded_type_package`

Ordinary erased level evidence supplies a universe ceiling without special bounded-binder syntax.

Source expectation: **accept**. Harness outcome: **pass**.

#### `main.kp`

```kappa
--! mode check
--! assertNoErrors

type LocalTypeBelow.{u} : Type u =
    (ordinary 0 level : TypeLevel,
     @0 proof : level < u,
     ordinary 0 T : Type level)
```

### `positive/standard_typebelow_schema`

A bounded ordinary-code package is defined as a declaration universe schema rather than an unbounded term-indexed family.

Source expectation: **accept**. Harness outcome: **pass**.

#### `main.kp`

```kappa
--! mode check
--! assertNoErrors

data LocalTypeBelow.{u} : Type u =
    LocalPackTypeBelow
        (ordinary 0 level : TypeLevel)
        (@0 bound : level < u)
        (ordinary 0 T : Type level)
```

### `positive/unbounded_parametric_projection`

Projection of an unbounded packaged type preserves parametric mode and may feed another parametric binder.

Source expectation: **accept**. Harness outcome: **pass**.

#### `main.kp`

```kappa
--! mode check
--! assertNoErrors

type AnyTypeWitness : Type =
    (ordinary 0 level : TypeLevel,
     T : Type level)

useWitness :
    (p : AnyTypeWitness) ->
    ((U : Type p.level) -> Int) ->
    Int

let useWitness p k =
    k p.T
```

### `positive/unbounded_parametric_type_package`

A small package may contain a parametric type witness from an arbitrary first-class universe level.

Source expectation: **accept**. Harness outcome: **pass**.

#### `main.kp`

```kappa
--! mode check
--! assertNoErrors

type AnyTypeWitness : Type =
    (ordinary 0 level : TypeLevel,
     T : Type level)
```

### `positive/universe_generalized_identity`

One declaration is instantiated at distinct hidden universe levels.

Source expectation: **accept**. Harness outcome: **pass**.

#### `main.kp`

```kappa
--! mode check
--! assertNoErrors

id :
    (A : Type) ->
    A ->
    A

let id A x =
    x

small :
    Int -> Int

let small x =
    id Int x

large :
    Type0 -> Type0

let large x =
    id Type0 x
```

### `positive/universe_schema_instantiation`

A declaration universe schema may be instantiated explicitly at references.

Source expectation: **accept**. Harness outcome: **pass**.

#### `main.kp`

```kappa
--! mode check
--! assertNoErrors

data Box.{u}
    (A : Type u)
    : Type u =

    Box (value : A)

type Box0 : Type0 =
    Box.{0} Int

type Box3 : Type3 =
    Box.{3} Type2
```
