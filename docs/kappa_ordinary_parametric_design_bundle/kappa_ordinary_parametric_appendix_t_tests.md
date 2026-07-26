# Separate Appendix T conformance tests: `ordinary` / `parametric` and KCoreText

These suites are intentionally separate from the language specification. Each leaf directory is one independent Appendix T directory suite.

**Suite count:** 47

Every suite is expected to produce harness outcome **pass**. A negative suite passes when compilation or KCore verification is rejected with the asserted diagnostic.

## equality

### `positive/universe_polymorphic_equality`

Ordinary equality between type values is accepted through universe-polymorphic equality.

Source expectation: **accept**. Harness outcome: **pass**.

#### `main.kp`

```kappa
--! mode check
--! assertNoErrors

sameUniverse :
    Type0 = Type0

let sameUniverse =
    refl

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

## kcore

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
  axiom ordinary @tests.kcore.lift.le#3001 .{^u#0, ^v#1} :
    @std.typelevel.LevelLe#4001.{^u#0, ^v#1};

  def ordinary @tests.kcore.lift.raise#2002 .{^u#0, ^v#1} :
    ((ordinary ordinary omega explicit value %A#0 : Type ^u#0) ->
      Type ^v#1)
    where {
      ^u#0 <= ^v#1;
    }
  {
    body =
      lambda (ordinary ordinary omega explicit value %A#0 : Type ^u#0) {
        lift [^u#0 <= ^v#1 by @tests.kcore.lift.le#3001] %A#0
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

### `kcore/reject_invalid_lift`

The independent KCore checker rejects an invalid cumulative lift.

Source expectation: **reject**. Harness outcome: **pass**.

#### `bad.kcore`

```kcore
kcore 1;
module @tests.kcore.badlift#1005 [languageVersion = "kappa-v1", compilerInterfaceVersion = "1", sourceModuleIdentity = "tests.kcore.badlift"] {
  def ordinary @tests.kcore.badlift.bad#2005 : Type 0 {
    body = lift [1 <= 0 by solver(deadbeef)] @std.prelude.Int#9001;
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
--! assertKCoreRejects bad.kcore E_UNIVERSE_CONSTRAINT_UNSATISFIABLE

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

## metatheory

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

### `negative/hurkens_fragment`

A larger Hurkens-shaped fragment must fail at a modal or universe obligation rather than being accepted.

Source expectation: **reject**. Harness outcome: **pass**.

#### `main.kp`

```kappa
--! mode check
--! assertErrorCount 1
--! assertDiagnostic error E_PARAMETRIC_TYPE_PROMOTION
--! assertDiagnosticFamily error kappa.type.parametric-promotion

type Pow A =
    A -> Type

type Pow2 A =
    Pow A -> Type

forallCode :
    (A : Type) ->
    (Pow2 A -> A) ->
    Pow2 A

let forallCode A intro predicate =
    A

```

## parametricity

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

### `positive/parametric_non_kind_domain_allowed`

Explicit parametric observation is legal on any well-formed domain; only formation uses the parametric-kind fragment.

Source expectation: **accept**. Harness outcome: **pass**.

#### `main.kp`

```kappa
--! mode check
--! assertNoErrors

accepted :
    (parametric 0 n : Nat) ->
    Nat

let accepted n =
    n

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
    Type level ->
    TypeLevel

let rememberLevel level value =
    level

```

## universes

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

### `positive/proof_bounded_type_package`

Ordinary erased level evidence supplies a universe ceiling without special bounded-binder syntax.

Source expectation: **accept**. Harness outcome: **pass**.

#### `main.kp`

```kappa
--! mode check
--! assertNoErrors

type TypeBelow
    (ordinary 0 bound : TypeLevel)
    : Type bound =

    (ordinary 0 level : TypeLevel,
     @0 proof : level < bound,
     ordinary 0 T : Type level)

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
