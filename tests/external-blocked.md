<!-- RECONCILIATION NOTE (2026-06-20): the upstream external corpus GREW from
959 to 1115 fixtures; a fresh `tools/run-external-fixtures.sh` reports 962 pass /
76 fail / 11 unsupported / 66 harness-error / 1115 total (see external-results.md).
The hand-maintained per-fixture classes below predate that growth and are NOT yet
a complete triage of the current 76 fail + 66 harness-error. An independent
adversarial spot-check of the fails found them to be, by frequency: (a)
NON-NORMATIVE diagnostic-code spelling divergences — the fixture pins one portable
spelling; this implementation emits a different but spec-valid code AND exposes
the §3.1.4 portable alias via `portableCode` (e.g. E_TYPE_EQUALITY_MISMATCH→
E_TYPE_MISMATCH; E_NUMERIC_LITERAL_DOMAIN_MISMATCH, itself a §3.1.4 required alias;
E_UNSOLVED_IMPLICIT, for which §3.1.4 defines no alias). The external harness
matches the raw `code`, so these are the other implementation's spelling choice,
not MUST violations. (b) build-DSL surface gaps (`BuildConfig` manifests outside
the documented manifest subset). (c) two genuine accept-clean under-rejections
(`for value in (Option a)` non-List source; a member-resolution-at-lowering case)
tracked in SPEC_COVERAGE §18.6/§22. The 66 harness-errors are predominantly in
the `build` category: fixtures assert another implementation's §36
build-resolution diagnostic spellings (`E_BUILD_DEP_UNRESOLVED`,
`E_BUILD_LOCK_MISMATCH`, `E_BUILD_PROVIDER_COLLISION`, …) that this
implementation either spells differently (`E_DEPENDENCY_LOCK_MISMATCH`,
`E_NATIVE_BINDING_UNPINNED`) or does not yet emit (dependency/registry/git
resolution + provider-collision detection not implemented); the asserted code
is outside this implementation's §3.1.2A registry, so the directive cannot be
type-checked and is classified harnessError per §T (NOT silently reconciled —
§3.1.4 forbids reusing a portable alias for a different meaning; see
KNOWN_SPEC_ISSUES.md #6). NOTE: the §18 scoped effect + handler mechanism IS
implemented and tested (`tests/conformance/effects/`); only top-level `effect`
declarations and `return@`/`defer@` are deterministic-unsupported. A full
per-fixture re-triage of the grown corpus remains outstanding. -->

## Blocked classifications

Hand-maintained (in `tests/external-blocked.md`, appended to this
report by `tools/run-external-fixtures.sh`). Every non-passing
fixture falls in exactly one class:

1. **Outside Spec.md** — `unsupported`/`harnessError` is the outcome
   Appendix T itself mandates for the fixture's directives; the entry
   cites the directive and the spec section that does *not* define it.
2. **Spec conflict** — the fixture's expectation contradicts a
   specific Spec.md requirement; both sides are cited.
3. **Tracked gap** — the feature or diagnostic-calibration behavior is
   spec-compatible but not implemented here; the failure is honest,
   retained as `fail`, and queued (cited to the governing section).

### Outside Spec.md: spec-mandated `unsupported` (2 fixtures)

Evidence for each fixture is the quoted directive reason in the
"Unsupported, by reason" breakdown above and the per-fixture line in
the raw log (`/tmp/external-raw.log`). §T.4: *"`requires ...`
directives are preconditions. If any required condition is not met,
the test result is **unsupported**, not failed."* §T.8 defines the
`unsupported` outcome accordingly.

(The 8 `fuzz.pending.kbackendir.*` fixtures were previously listed
here as `requires backend dotnet` preconditions. That was wrong on
the evidence: they carry the plain configuration directive
`--! backend dotnet`, not `requires backend dotnet`, and §T.4 says
`backend <profile>` "selects the backend profile for **compile and
run** tests" — these are default-mode `check` suites with pure
diagnostic assertions, so backend selection does not apply. The
harness now runs them as check suites: 6 pass; the 2 diagnostic-shape
differences are tracked in the gaps table below.)

- **`requires capability incremental`** (2:
  `patch.import_stability.reload_same_identity`,
  `static_objects.incremental_static_object_identity_body_change`):
  `incremental` is one of §T.4's portable capability names; §T.7
  incremental step suites presume Chapter 34 session/cache reuse
  ("the harness preserves any caches, query results, module
  interfaces, ... that the compiler may legally reuse under Chapter
  34"). This implementation keeps no session state and does not claim
  the capability → unsupported (§T.4/§T.8).

### Outside Spec.md: `harnessError` (0 fixtures)

§T.8: *"`harnessError` means the test itself was malformed, for
example because of an unknown standard directive ..."*. The corpus's
private, non-`x-`-prefixed directives appear nowhere in Appendix T
(§T.3 grammar, §T.4 configuration list, §T.5 assertion lists) nor
anywhere else in Spec.md. All of those actually used by the corpus
have an evident portable meaning, so this harness implements them as
documented compatibility extensions, as §T.1 permits (see TESTING.md):
`assertEval`, `assertDiagnosticCodes`, `allow_unsafe_consume`,
`assertParameterQuantities`, `assertExecute`, `assertRunStdout`,
`assertEvalErrorContains`, `assertDoItemDescriptors`,
`assertInoutParameters`, and `assertContainsTokenTexts` (plus the
`x-assertEval`/`x-assertEvalErrorContains`/`x-assertDeclDescriptors`/
`x-assertTraitMembers`/`x-assertContainsTokenTexts` extensions). Any
future private directive without an evident portable meaning remains
a harness error.

### Spec conflicts (fixture expectation contradicts Spec.md; 12 fixtures)

- `core_semantics.evaluation.positive`
  (`runtime_error_division_by_zero.kp`) asserts `let result = 1 / 0`
  elaborates with **no errors** and traps at runtime. §28.2.1 defines
  `(/) : ... (x : a) -> (y : a) -> (@_ : divDefined x y = True) -> a`
  ("`/` is checked division. It requires proof that the denominator is
  valid for the selected `CheckedDiv` instance"), and §28.2.3 fixes
  the Integer domain as `divDefined x y = (y /= zero)`. For literals
  `1`/`0` the obligation reduces definitionally to `False = True`,
  which is uninhabited; the §3.2.4 `kappa.implicit.unsolved` family
  ("an implicit argument cannot be synthesized") is an error, so
  `assertNoErrors` is unsatisfiable in a conforming implementation.
  §28.2.1 additionally forbids the escape hatch: "The portable prelude
  MUST NOT provide unchecked division-by-zero ... under these operator
  names."
- `data_types.constructors.positive_named_field_source_order_evaluation`
  contains `let boom = 1 / 0` under `assertNoErrors` — the same
  §28.2.1/§28.2.3 contradiction as above (the source-order behavior it
  pins is unreachable behind the ill-typed division).
- `core_semantics.evaluation.runtime_negative`
  (`user_defined_and_is_eager.kp`) redefines
  `(&&) : Int -> Int -> Int` in module scope (shadowing the prelude
  `(&&) : Bool -> Thunk Bool -> Bool` per §7.1 nearest-binding-group
  lookup and §28.1), then asserts `result : Bool` with
  `result = False && failNow "..."` elaborates with **no errors**:
  `False : Bool` flows into an `Int` parameter and the `Int` result is
  ascribed `Bool` — §16.1.7.1 application checking and §3.2.3
  `kappa.type.mismatch` make both rejections mandatory. (Were the
  prelude `&&` selected instead, the `Thunk` second operand would not
  be evaluated and the asserted runtime error could not occur either.)
- `modules.imports.item_kind_selectors.negative_wildcard_ctor` asserts
  that after `import foo.*` the program compiles clean but `Box 42`
  fails **at runtime** with "Name 'Box' is not in scope". §8.3.1:
  "`import M.*` imports all exported binding groups except
  distinct-spelling constructors" and "A same-spelling data family is
  imported as one binding group containing its type facet and its
  same-spelling constructor facet (§7.2)". `data Box a = Box a` is a
  same-spelling family, so the wildcard import brings the constructor
  facet; a conforming implementation accepts and evaluates `Box 42`,
  so the asserted runtime name failure cannot occur.
- `static_objects.kind_accept_effect_label_kind_qualified_inside_scoped_effect`
  asserts `let L = effect-label State` elaborates with no errors.
  §7.1 (declaration kinds): "The internal declaration kind for effect
  labels is written `effect-label` in this specification. Its
  source-level selector spelling is `effectLabel`, **because
  hyphenated words are not identifiers in Kappa source**." §7.1.1
  grammar: `kindQualifiedSelector ::= 'type' | 'trait' |
  'effectLabel' | 'module'`; §5 (keywords): "`effectLabel` is a soft
  keyword used only as a source-level kind-qualified selector".
  §3.2.2's `kappa.import.effect-label-selector` family even names the
  spelling `effect-label` an *invalid selector spelling*. The fixture
  text is therefore not a conforming program; `effect-label` lexes as
  `effect - label` and cannot elaborate.
- `static_objects.kind_reject_effect_label_selector_on_type` asserts
  **exactly one** error for `let bad = effect-label Token` — the count
  presumes `effect-label` is recognized as a single selector token and
  rejected once, which the same §7.1/§7.1.1/§5 spelling rules
  contradict (here the nonconforming spelling produces an unresolved
  `effect`/`label` cascade instead).
- `traits.members.negative_member_unresolved_at_lowering` asserts two
  `E_TYPE_MISMATCH` errors for ordinary uses of `traverse` at
  `Option (List Int)`. The §28.2 prelude term list includes
  `traverse` as a §14.2.1 overloaded member, and this implementation
  provides `Traversable List`, `Traversable Option`, and
  `Applicative Option` instances (§28.2 mandates *at least* the
  minimum; instances beyond it are permitted). Under §14.2.1 ("A bare
  occurrence of `m` elaborates to projection from synthesized implicit
  evidence") and the §14.3.1 instance-resolution algorithm both uses
  are well-typed, so a conforming implementation accepts; the
  fixture's `assertErrorCount 2` pins another implementation's
  member-lowering limitation, not a spec requirement.
- `traits.members.negative_opaque_member_operator_wrong_code` asserts
  exactly three `E_TYPE_MISMATCH` errors; one of the three probes,
  `apply1 (\o -> o >>= (\x -> Some (x + 41))) (Some 1) : Option Int`,
  is well-typed by §14.2.1 overloaded-member elaboration with the
  §28.2.2 `Monad Option` instance once `apply1`'s type arguments are
  solved (§16.3.3 postponed goals). The two genuinely ill-typed probes
  (no `Ord CI`/`Eq CI` instances) are rejected here with
  `kappa.implicit.unsolved` (§3.2.4). The fixture therefore fails on
  *count* alone (2 emitted vs 3 asserted): the well-typed first probe is
  correctly accepted, which contradicts the fixture's expectation of a
  third rejection — a §14.3.1 conflict that no diagnostic-code spelling
  rule can reconcile.
- `short_circuit_reject_rhs_wrong_unsuspended_type` asserts one
  `E_TYPE_EQUALITY_MISMATCH` for `True && 1` (prelude
  `(&&) : Bool -> Thunk Bool -> Bool`, §16.1.3, so the literal `1`
  appears where `Thunk Bool` is expected). This implementation rejects
  it once (the spec-mandated outcome) but with
  `E_NUMERIC_LITERAL_DOMAIN_MISMATCH` (family
  `kappa.type.literal-domain-mismatch`, §3.2.3). §3.1.4 (Spec.md:928)
  *mandates* this portable alias precisely "when literal elaboration
  fails because the surrounding expected type … is not compatible with
  the literal domain", and §3.1.4 (Spec.md:823) forbids reusing the
  `E_TYPE_MISMATCH` alias "for a materially different diagnostic
  meaning". The fixture pins `E_TYPE_MISMATCH` for a condition the spec
  reserves the literal-domain alias for, so its expectation contradicts
  §3.1.4.
- `types.literals.negative_numeric_literal_at_user_type` asserts two
  `E_TYPE_MISMATCH` for `MkB 5` / `MkB 3.14` where `MkB : W -> Box` and
  the user type `W` has no `FromInteger`/`FromFloat` instance. Both are
  correctly rejected (the spec-mandated outcome, §6.1.5) with
  `E_NUMERIC_LITERAL_DOMAIN_MISMATCH` — the §3.1.4-mandated portable
  alias for "no suitable literal witness is available" (§3.2.3). Same
  §3.1.4 reuse contradiction as above.
- `types.literals.negative_literal_in_parameterized_positions` asserts
  four `E_TYPE_MISMATCH`; all four ill-typed declarations are correctly
  rejected (count matches exactly). Three are string/None-at-`Color`
  mismatches reported with `E_TYPE_EQUALITY_MISMATCH` (→ portable
  `E_TYPE_MISMATCH`, matches). The fourth, `Some 5 : Option Color`, is a
  numeric literal at a `FromInteger`-less domain and is reported with
  `E_NUMERIC_LITERAL_DOMAIN_MISMATCH` — again the §3.1.4-mandated alias
  for that exact condition (§3.2.3/§6.1.5). The fixture pins
  `E_TYPE_MISMATCH` for the literal-domain probe too, contradicting
  §3.1.4's reuse rule.
- `expressions.conditionals.negative_if_condition_not_bool` asserts
  five `E_TYPE_MISMATCH` for five confidently-inferred non-`Bool`
  `if`/`while` conditions (§16.4: a condition MUST have type `Bool`).
  All five are correctly rejected statically (count matches exactly,
  the spec-mandated outcome — none traps only at runtime). Four
  (`if "yes"`, `if someOpt`, `if predicate`, `if n` where `n : Int`)
  are reported with `E_TYPE_EQUALITY_MISMATCH`, which §3.1.4 aliases to
  the pinned `E_TYPE_MISMATCH` (matches). The fifth, `if 5`, is a bare
  integer literal at the `Bool` domain, and `Bool` has no `FromInteger`
  witness (§6.1.5); this implementation reports it with
  `E_NUMERIC_LITERAL_DOMAIN_MISMATCH` (family
  `kappa.type.literal-domain-mismatch`, §3.2.3), which §3.1.4
  (Spec.md:928-929) *mandates* "when literal elaboration fails because
  the surrounding expected type … is not compatible with the literal
  domain" and which §3.1.4 (Spec.md:823) forbids folding back onto
  `E_TYPE_MISMATCH`. The fixture pins `E_TYPE_MISMATCH` for the
  literal-domain probe, the same §3.1.4 reuse contradiction as
  `short_circuit_reject_rhs_wrong_unsuspended_type` and the
  `types.literals.negative_*` entries above. (The companion positive
  fixture `expressions.conditionals.positive_bool_conditions`, which
  exercises a monadic `while readFlag do` condition with
  `readFlag : UIO Bool`, previously failed on a §18.6 defect — a
  monadic `m Bool` `while` condition was rejected — and now PASSES; see
  the §18.6 fix and its `tests/conformance/run/while-monadic-cond.kp`
  mirror.)
### Tracked gaps (spec-compatible behavior not implemented; honest `fail`s, 17 fixtures)

Diagnostic-spelling notes below: only the §3.1.4-listed portable
aliases are normative comparison keys; every other code spelling
(both implementations') is implementation-defined per §3.1. This
harness's `assertDiagnosticCodes` matches through those §3.1.4 aliases
in both directions and through nothing else: a code §3.1.4 does not
standardize (e.g. `kappa.implicit.unsolved` / `E_UNSOLVED_IMPLICIT`,
§3.2.4, for which §3.1.4 defines no portable alias) is compared
verbatim. The diagnostic count is always compared exactly, and there
are no implementation-defined spelling "tolerances", so a fixture that
pins a different *required* code than this implementation emits is
reported as an honest `fail` rather than reconciled.

| fixture | gap | spec |
|---|---|---|
| `app_reject_at_argument_to_explicit_binder` | `idInt @1` (an `@`-payload supplied to an *explicit* binder) reports `kappa.application.argument-mismatch` here; the corpus expects its `kappa.type.mismatch` spelling. Neither code is the §3.2 `kappa.application.explicit-implicit-classifier` family (portable `E_EXPLICIT_IMPLICIT_CLASSIFIER_MISMATCH`) that is closest to this condition; aligning to it is queued. | §3.2, §3.1.4, §16.1.7 |
| `app_reject_explicit_implicit_wrong_type` | `readEnv @1 7`: the literal `@`-payload `1` is supplied to the implicit `Env` binder, and `Env` has no `FromInteger` witness (§6.1.5), so the payload cannot be elaborated against the selected implicit binder's demanded type. This implementation now emits the §3.1.4-mandated portable code `E_EXPLICIT_IMPLICIT_CLASSIFIER_MISMATCH` (family `kappa.application.explicit-implicit-classifier`, §3.2 — §3.1.4 Spec.md:995-996, §16.1.7.2): the payload-elaboration failure is retagged to the classifier-mismatch code at the `ArgImplicit` spine case. The corpus pins `E_APPLICATION_ARGUMENT_MISMATCH`, which §3.1.4 does not standardize and which is therefore compared verbatim; the rejection is correct and the error count matches, only the spelling differs, so this stays an honest `fail`. The fixture's pinned code is not the §3.1.4-mandated one for this condition. | §3.2, §6.1.5, §3.1.4, §16.1.7.2 |
| `app_reject_too_many_arguments` | `idInt 1 2` reports `kappa-hs.application.non-callable` here (an implementation-defined family — §3.2 defines none for non-callable application: "the head of an application has a type that is not a function or callable value" — `idInt 1 : Int`), portable `E_APPLICATION_NON_CALLABLE` (§3.1.4); the corpus expects its generic type-mismatch spelling for over-application. | §3.1.4, §3.2 |
| `fuzz.pending.reject_dotted_value_root` | `let i0 = i0.right` is rejected here as a member access on an undetermined receiver (the own name resolves to the §9.2 pre-registration so sig-less recursion can be reported); the corpus's resolution model leaves the own name unresolved (`E_NAME_UNRESOLVED`, twice — the failed declaration also binds nothing). Spec fixes neither model's diagnostic spelling (§9.2/§15 only require rejection of sig-less recursion). | §9.2, §15, §7.1 |
| `fuzz.pending.kbackendir.reject_invalid_application_erased_type_argument` | the malformed `type I3 = (1 i0 : I3) : Int = i1` line yields a syntax error here in addition to the expected `E_APPLICATION_NONCALLABLE` (2 errors vs the corpus's 1); the corpus's recovery silently absorbs the malformed alias tail. Same §3.1.14A recovery-shape family as the entries above. | §3.1.14A, §5.2 |
| `fuzz.pending.kbackendir.reject_invalid_application_later_zero_arity` | `let i1 = i1 "s"` inside a do block, with sig-less top-level `let i1 = 1` declared *later* in the file: the non-recursive do-let RHS (§9.3.1) resolves the own name to the outer scope, where this implementation's in-order elaboration of sig-less top-level lets has not yet registered `i1` → `E_NAME_UNRESOLVED`; the corpus resolves the forward reference and reports `E_APPLICATION_NONCALLABLE` (`1 "s"`). Forward references to *sig-less* later top-level lets are the gap (signature-carrying forward references resolve fine here). | §7.1, §9.2, §15 |
| `traits.instances.negative_unresolved_name_in_instance_body` | an unresolved name inside an instance member body is rejected here with `E_NAME_UNRESOLVED` (§3.2.2 `kappa.name.unresolved`); the corpus expects the spelling `E_TYPE_MISMATCH`, pinning its own lowering (the fixture's own comment says the name previously "lowered as bare names and crashed at runtime" there). §3.1.4's portable aliases do not map an unresolved-name rejection to `E_TYPE_MISMATCH`; the static rejection itself is common ground. | §3.2.2, §3.1.4 |
| `fuzz.pending.reject_invalid_do_bind_indented_continuation` | a more-indented line after a complete do-bind RHS parses as a §5.2 continuation (application) here and fails as `E_APPLICATION_NONCALLABLE`; the corpus's layout rejects it as a syntax error. The §5.4 layout text does not decide do-item continuation lines explicitly. | §5.4, §18.4 |
| `fuzz.pending.reject_invalid_indented_expression_continuation` | same layout-continuation difference (our parse yields one downstream type error, the corpus's two). | §5.4 |
| `parser.recovery.negative_malformed_tuple_parameter_no_crash` | `let i1 (1 i1 :)3` — declaration-level recovery reports once here; the corpus's recovery yields two diagnostics. No crash either way (the §3.1.14A minimum contract is met); cascade-shape parity is queued. | §3.1.14A |
| `types.literals.negative_literal_in_nested_result_positions` | all three ill-typed declarations (record-field literal, do-tail, and `"a" ++ "b"` at user type `Color`) **are** correctly rejected — the spec-mandated outcome. The asserted count is 3 `E_TYPE_MISMATCH`; this implementation emits 5 because the `++` probe (`(++) : forall a. Monoid a => a -> a -> a`) surfaces both the unsatisfiable `Monoid Color` evidence goal (§6.1.5/§14.3.1, `E_UNSOLVED_IMPLICIT`) and a mismatch on each `String` operand, where the corpus collapses the binary-at-wrong-result to one mismatch. The two extra diagnostics are an honest cascade-count divergence (the §3.1.11 single-cause suppression does not fold the `Monoid` evidence failure into the operand mismatches here), not a missed rejection; cascade-shape parity for the evidence-bearing-operator case is queued. Pre-existing on committed HEAD (this fixture was added to the corpus after the prior ledger revision and fails identically on the unmodified baseline). | §6.1.5, §14.3.1, §3.1.11 |
| `app_reject_missing_implicit_argument` | `readEnv 7`, where `readEnv : (@ω env : Env) -> Int -> Int`: the explicit `7` fills the `Int` parameter and the runtime implicit `Env` binder is left with no candidate. This implementation rejects it once (the spec-mandated outcome) with `E_UNSOLVED_IMPLICIT` (`kappa.implicit.unsolved`, §3.2.4 — "an implicit argument cannot be synthesized", which is exactly a missing runtime implicit, as the fixture's own name says). The corpus pins `E_TYPE_EQUALITY_MISMATCH`. §3.1.4 defines no portable alias for `kappa.implicit.unsolved` and forbids reusing `E_TYPE_MISMATCH` for it, so neither spelling is normative; the rejection itself is common ground. | §16.3.3, §3.2.4, §3.1.4 |
| `traits.members.negative_container_wrapped_user_nominal_equality` | `o == Some Red` / `o == (Red :: Nil)` through an opaque lambda: `==` demands `Eq` evidence for a container of the user nominal `Color`, which has no `Eq Color` instance. Both uses are correctly rejected (count matches) with `E_UNSOLVED_IMPLICIT` (`kappa.implicit.unsolved`, §3.2.4 trait-evidence goal). The corpus pins `E_TYPE_MISMATCH`; §3.1.4 maps this missing-instance condition to no portable alias and forbids reusing `E_TYPE_MISMATCH`. Honest spelling divergence; no missed rejection. | §3.2.4, §3.1.4, §14.3.1 |
| `traits.members.negative_opaque_ordering_constructed_operands` | `x < (2 :: Nil)` / `x < Some 2`: `<` demands `Ord` evidence for a constructed (non-scalar) operand with no `Ord` instance. Both correctly rejected (count matches) with `E_UNSOLVED_IMPLICIT` (§3.2.4). Same §3.1.4 spelling divergence as the row above. | §3.2.4, §3.1.4, §14.3.1 |
| `traits.members.negative_tuple_arrow_operand_equality` | `p == (Red, 1)` (tuple wrapping a user nominal) / `f == inc` (arrow operand): `==` demands `Eq` evidence neither tuple-of-`Color` nor a function type provides. Both correctly rejected (count matches) with `E_UNSOLVED_IMPLICIT` (§3.2.4). Same §3.1.4 spelling divergence. | §3.2.4, §3.1.4, §14.3.1 |
| `traits.members.negative_value_position_member_reference` | bare value-position references to member names `empty` / `release` with no determinable owning instance: the residual member goal is an unsolved implicit. Both correctly rejected (count matches) with `E_UNSOLVED_IMPLICIT` (§3.2.4). The corpus pins `E_TYPE_MISMATCH`; §3.1.4 defines no alias for `kappa.implicit.unsolved`. Honest spelling divergence. (Earlier ledger revisions wrongly credited this fixture as cleared — that "clear" depended only on the removed `E_UNSOLVED_IMPLICIT → E_TYPE_MISMATCH` harness tolerance, not on any behavior change; it is reclassified here as the honest tracked-gap it always was.) | §3.2.4, §3.1.4, §14.2.1 |
| `traits.resolution.negative_unsolved_goal_no_defaulting` | four drivers (`Filterable (Box _)`, `EuclideanSemiring Int` at the wrong shape, `FromString Duration`, `Applicative (STM _)`) each demand evidence at a type that provably has no instance; all four must be rejected statically (the fixture's purpose: an unsolved goal must NOT default to a unique ground instance head). All four correctly rejected (count matches) with `E_UNSOLVED_IMPLICIT` — the precise `kappa.implicit.unsolved` condition (§3.2.4). The corpus pins `E_TYPE_MISMATCH`; §3.1.4 defines no alias for this family. Honest spelling divergence; the spec-critical no-defaulting behavior is satisfied. | §3.2.4, §3.1.4, §16.3.3 |

Reclassified in this revision: the
`E_UNSOLVED_IMPLICIT → E_TYPE_MISMATCH` harness "tolerance" has been
removed (it relaxed the test oracle without changing emitted codes,
contradicting §3.1.4's rule that a portable alias must not be reused
for a materially different meaning). Nine fixtures that previously
matched only through it are reclassified honestly above (three as
literal-domain spec-conflicts now reporting the §3.1.4-mandated
`E_NUMERIC_LITERAL_DOMAIN_MISMATCH`, six as `kappa.implicit.unsolved`
tracked-gaps). In particular `traits.members.negative_value_position_member_reference`,
previously credited as "cleared" by the §3.1.11 cascade-suppression
work, never changed emitted code: that clear was the tolerance, not a
behavior fix, so it returns to its honest tracked-gap classification.

Cleared in prior revisions (all PASS):
§16.1.7.1 function-argument quantity mismatch reported as
`E_APPLICATION_ARGUMENT_MISMATCH`
(`arrow_reject_unrestricted_argument_function_to_linear_expected`);
§3.1.11 single-cause cascade suppression at implicit-goal flush
(`fuzz.pending.reject_builtin_arithmetic_non_numeric_operand`,
`fuzz.pending.reject_compile_time_parameter_runtime_arithmetic`) — the
latter also relies on §6.6 `()` elaborating to the type `Unit` in
type position; §5.2/§3.1.14A in-bracket recovery surfacing the
unbalanced-bracket cause when an unclosed bracket swallows following
declarations (`fuzz.pending.reject_constructor_runtime_type_field`,
`fuzz.pending.reject_malformed_constructor_keyword`); §13.2.11
anonymous existential (`exists`) type sugar elaborating to the
§13.2.10 sealed-package machinery, so the §12.4.3 borrow-escape
rejection is reached
(`borrow_qtt.030_borrow.reject_borrow_view_escape_anonymous`).

Cleared in earlier revisions of this ledger (all now PASS):
the §14.2.1 associated-static-member lane (`traits.instances.*` 4),
trait defaults with parameters (2), §14.3.3 supertrait projection,
static-object kind selectors and rebound-identity (6 + export facade),
import `ctor` selectors / aliased re-exports / fixity imports /
URL-pin codes (5), §28.2.1 divDefined via boolean branch refinement
(`examples.expr_eval`), runtime recursion depth guard, deep-value
rendering, `integerToInt` (§T.1 compatibility export), bare operator
references (§5.5.1, 2), alias-parameter generalization, named-block
duplicate labels, misindented case body, recursive type aliases (2),
data-constructor salvage, instance-declaration recovery hygiene,
numeric-function application mismatches (3), literal-suffix mismatch,
fixity descriptor format, pattern/scrutinee agreement (2), BorrowView
closure escape.
