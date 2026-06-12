## Blocked classifications

Hand-maintained (in `tests/external-blocked.md`, appended to this
report by `tools/run-external-fixtures.sh`). Every non-passing
fixture falls in exactly one class:

1. **Outside Spec.md** — `unsupported`/`harnessError` is the outcome
   Appendix T itself mandates for the fixture's directives; the entry
   cites the directive and the spec section that does *not* define it.
2. **Spec conflict** — the fixture's expectation contradicts a
   specific Spec.md requirement; both sides are cited.
3. **Tracked gap** — the feature is spec-defined but not implemented
   here; the failure is honest, retained as `fail`, and queued (cited
   to the defining section).

### Outside Spec.md: spec-mandated `unsupported` (10 fixtures)

Evidence for each fixture is the quoted directive reason in the
"Unsupported, by reason" breakdown above and the per-fixture line in
the raw log (`/tmp/external-raw.log`).

- **`backend dotnet`** (8): `fuzz.pending.kbackendir.*`. §T.4:
  unmet `requires backend` → unsupported. No `dotnet` backend exists
  here (no §27 backend profiles are implemented; the only provided
  profile is `backend interpreter`).
- **`requires capability incremental`** (2:
  `patch.import_stability.reload_same_identity`,
  `static_objects.incremental_static_object_identity_body_change`):
  §T.7 incremental step suites presume Chapter 34 session reuse; this
  implementation keeps no session state and does not claim the
  capability → unsupported (§T.4/§T.8).

Previously listed here and since implemented (now run normally):
`mode compile` (the per-module Term→Value lowering into the
interpreter's runtime representation is recorded as the
`lowerKBackendIR`/`module` portable trace step, §T.5.5); `scriptMode`
(§T.4: compiles without §8.1 path-derived module names); and the
`x-assertContainsTokenKinds` / `x-assertDataConstructors` /
`x-assertModule` / `x-assertModuleAttributes` extension directives
(documented compatibility extensions per §T.1/§T.3).

### Outside Spec.md: `harnessError` (0 fixtures)

§T.3: *"Any unknown standard directive, malformed directive, or
ill-typed directive argument is a harness error."* The corpus's
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

### Spec conflicts (fixture expectation contradicts Spec.md)

- `core_semantics.evaluation.positive`
  (`runtime_error_division_by_zero.kp`) asserts `let result = 1 / 0`
  elaborates with **no errors**. §28.2.1 defines
  `(/) : … -> (@_ : divDefined x y = True) -> a` with
  `instance CheckedDiv Integer` computing `divDefined x y = not (y == 0)`,
  so the implicit obligation reduces to `False = True`, which is
  uninhabited — a conforming checker must reject. The fixture's
  `assertNoErrors` contradicts §28.2.1.
- `core_semantics.evaluation.runtime_negative`
  (`user_defined_and_is_eager.kp`) redefines
  `(&&) : Int -> Int -> Int` and applies it as `False && failNow "…"`
  under `result : Bool`, asserting **no errors**: `False : Bool` and
  `failNow … : a` flow into `Int` parameters and the `Int` result is
  ascribed `Bool`, which §16.1.7.1 application checking must reject.
  It additionally requires the *discarded* second argument to be
  evaluated, which §15.1 normalization does not mandate.
- `traits.members.negative_member_unresolved_at_lowering`,
  `traits.members.negative_value_position_member_reference`,
  `traits.members.negative_opaque_member_operator_wrong_code` expect
  `E_TYPE_MISMATCH` for conditions that include genuinely unresolved
  names; §7.1 name-resolution failures render here as
  `E_NAME_UNRESOLVED` under the §3.1.2A portable-alias rules (the
  spec fixes no `E_TYPE_MISMATCH` for unresolved references;
  unresolved *implicit obligations* are already matched through the
  documented `E_UNSOLVED_IMPLICIT ↔ E_TYPE_MISMATCH` §3.1.2A alias).

### Tracked gaps (spec-defined, not implemented; honest `fail`s)

The remaining 59 tracked-gap failures (64 fails minus the 5
spec-conflict fixtures above) group by feature, ranked by fixture
count (classification from the raw log; one fixture may exhibit
several gaps — it is counted under the dominant one). The §21–§23
metaprogramming lane (macros, `Elab`/`Syntax`, deriving-shape,
custom query sinks, the §21.6 convenience reflection queries, and
§23 staged code) is fully clear in the corpus: `macros.*` 32/32,
`deriving.*` 10/10, `queries.*` 54/54, plus the staging and
static-object reflection fixtures.

| rank | feature gap | spec | ~fixtures |
|---|---|---|---|
| 1 | Fuzz robustness: malformed-construct rejection with specific codes, recovery-cascade and indentation-diagnostic deltas (`fuzz.*` 14, `parser` 1) | §3.1.14A, §5.4, §9 | 15 |
| 2 | Static-object kind selectors and identity: effect-label kind selectors inside `scoped effect`, reified-static fallback ambiguity, kind-selector rejections, rebound type-object ctor patterns, package-member type objects, export-facade kind-qualified aliases (`static_objects.*` 9) | §2.8.3–§2.8.6, §7.1.1, §7.6, §17.3.2, §8.3 | 9 |
| 3 | Associated trait type members (`Out`, `Element`), trait-default members with parameters, use-site supertrait projection evidence (`traits.instances/.members` 6, `expressions.implicit_parameters` 1) | §14.2.1, §14.1.4, §14.3 | 7 |
| 4 | Application implicit-insertion diagnostic calibration: literal-defaulting and unsolved-implicit failures at argument positions report `E_APPLICATION_ARGUMENT_MISMATCH`/`E_TYPE_EQUALITY_MISMATCH`/`E_TYPE_MISMATCH` in the corpus where this implementation reports `E_UNSOLVED_IMPLICIT`/`E_APPLICATION_NONCALLABLE`/… (`app_reject_*` 4, `lexical.numbers` 1, `patterns…guard_and_literal` 1) | §16.1.7.1, §3.1.2A | 6 |
| 5 | Import item-kind selectors (ctor/type facet wildcards), symbolic-term imports, and URL-import pinning codes (`modules.imports.*` 6) | §8.3–§8.4 | 6 |
| 6 | Misc expression-level deltas: bare-minus/operator sections under checked application, dependent-case result types, named-application labels, misindentation code, short-circuit suspended-operand typing (`expressions.*` 5, `short` 1) | §16 | 6 |
| 7 | Runtime-model deltas: source-order named-constructor field evaluation with runtime-trapping division (§28.2.1 proof-carrying `(/)` rejects `1 / 0` statically here), recursion-depth guard, deep value `show`, `Result` propagation example (`data_types` 1, `runtime` 1, `interpreter` 1, `examples` 1) | §10.1.1, §32.1 | 4 |
| 8 | `BorrowView`/`captureBorrow` projection borrows and exists-type escapes (`borrow_qtt.*` 2) | §12.4.3, §12.2 | 2 |

The remainder (4) is a long tail of one fixture each:
linear-function argument-quantity subsumption (`arrow_reject_*`,
§12.2.1), scrutinee-vs-constructor pattern typing diagnostics
(`patterns…scrutinee_constructor`, §17.1), the operator-token
fixity surface (`lexical.operator_identifiers_fixity…`, §5.5.3),
and the corpus prelude term `integerToInt`
(`types.literals.positive_local_frominteger_instance`): Spec.md
defines no such conversion (§28.2 names `intToNat`/`natToInt`
etc., not `integerToInt`) — retained as an honest fail pending a
documented compatibility decision.
