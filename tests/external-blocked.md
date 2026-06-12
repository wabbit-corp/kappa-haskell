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

### Outside Spec.md: spec-mandated `unsupported` (33 fixtures)

Evidence for each fixture is the quoted directive reason in the
"Unsupported, by reason" breakdown above and the per-fixture line in
the raw log (`/tmp/external-raw.log`).

- **`mode compile`** (10): `static_objects.lowering_compile_erases_*`
  (`…kind_qualified_static_object_smoke`, `…module_object_rebinding_smoke`,
  `…nested_static_object_capture_smoke`, `…record_type_field_smoke`,
  `…trait_object_constraint_descriptor_smoke`,
  `…transparent_sealed_type_member_smoke`, `…type_alias_reification_smoke`,
  `…type_object_argument_smoke`, `…type_object_in_record_return_smoke`,
  `…type_object_through_named_application_smoke`). `mode compile`
  presumes a code-generating backend; this implementation provides
  only the `backend interpreter` profile (§T.4), and §T.8 classifies
  a test whose mode/backend precondition is unmet as unsupported.
- **`backend dotnet`** (8): `fuzz.pending.kbackendir.*`. §T.4:
  unmet `requires backend` → unsupported. No `dotnet` backend exists
  here (no §27 backend profiles are implemented).
- **Unsupported `x-` extension directives** (12): per §T.3 an
  `x-`-prefixed directive the harness does not support makes the test
  **unsupported**, never silently ignored; none of these names is
  defined by §T.4/§T.5, so implementing them is optional (§T.1).
  `x-assertContainsTokenKinds` (7: `lexical.identifiers.positive`,
  `lexical.operator_identifiers_fixity.operator_tokens.positive`,
  `literals.character_literals_char.positive`,
  `literals.numeric_literals.positive`,
  `literals.string_literals.interpolation.positive`,
  `literals.string_literals.positive_escapes`,
  `literals.unit_tuples.positive`); `x-assertDataConstructors` (3:
  `data_types.data_declarations.positive`,
  `lexical.whitespace_indentation_continuation.positive`,
  `modules.visibility_opacity_private_opaque.positive`);
  `x-assertModule` (2: `modules.files.negative_header_mismatch`,
  `modules.files.positive`).
  These assert raw token streams / constructor tables / module
  identity dumps this harness does not expose.
  (`x-assertContainsTokenTexts` is now implemented — token source
  texts are directly observable from the lexer — so its one fixture
  runs normally.)
- **`requires capability incremental`** (2:
  `patch.import_stability.reload_same_identity`,
  `static_objects.incremental_static_object_identity_body_change`):
  §T.7 incremental step suites presume Chapter 34 session reuse; this
  implementation keeps no session state and does not claim the
  capability → unsupported (§T.4/§T.8).
- **`scriptMode`** (1:
  `modules.imports.item_kind_selectors.unhide_clarify_import_items.positive`):
  not among the §T.4 configuration directives this implementation
  provides; script mode (and §4 `unhide`/`clarify`) is unimplemented.

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

The remaining 170 tracked-gap failures (175 fails minus the 5
spec-conflict fixtures above) group by feature, ranked by fixture
count (classification from the raw log; one fixture may exhibit
several gaps — it is counted under the dominant one):

| rank | feature gap | spec | ~fixtures |
|---|---|---|---|
| 1 | Macros/elaborator reflection: `Elab`/`Syntax`, quote literals `'{…}`, splices, prefixed-string interpolation handlers, `FromComprehensionRaw`/`Plan` custom sinks, `std.deriving.shape` (`macros.*` 30, `queries.appendix_t.realistic.*` 18, `deriving.shape.*` 10) | §21–§23, §22, §6.3.4–§6.3.5, §20.10.9 | 58 |
| 2 | Sealing/opacity and static-object facets: `seal` packages, opaque signature members, trait/effect-label facets, kind selectors (`modules.sealing.*` 13, `static_objects.*` 14) | §13.4–§13.5, §8.3, §7.5–§7.6, §7.1.1 | 27 |
| 3 | Fuzz robustness: malformed-construct rejection with specific codes, recovery-cascade and indentation-diagnostic deltas (`fuzz.pending.*`) | §3.1.14A, §5.4, §9 | 15 |
| 4 | `BorrowView`/`captureBorrow` projection borrows, code-quote capture, exists-type escapes (`borrow_qtt.*` 3 — the handler/resumption-QTT and `effects.*` fixtures are cleared) | §12.4.3, §12.2 | 3 |
| 5 | Associated trait type members; use-site supertrait conformance paths (`traits.*` 9, `app_reject_*` implicit-insertion diagnostics 5) | §14.2.1, §14.1.4, §16.1.7.1 | 14 |
| 6 | Required standard modules: `std.bridge`, `std.ffi`, `std.atomic`, `std.gradual`, `std.supervisor` (`bridge`/`ffi`/`atomic`/`gradual`/`supervisor` fixtures) | §29.1–§29.2, §25–§26 | 7 |
| 7 | Record/suspension `Need`/`Thunk`-typed lazy field insertion (`record_*` 5, `suspension_*` 2) | §11.2, §16.2.2 | 7 |
| 8 | Definitional-equality residue: record η, irrefutable tuple lets, optional-type sugar over parenthesized/tuple types, capture subsumption (`definitional_equality.*` 5, `this_nonfirst_*` 4) | §31.1, §13.1.9, §13.2.1 | 9 |
| 9 | Named-application preserved metadata and named-block diagnostics (`named_reject_*`) | §16.1.7 | 5 |
| 10 | Import item-kind selectors and URL-import pinning (`modules.imports.*`) | §8.3–§8.4 | 5 |
| 11 | Equality transport through branch evidence (`transport_*`) | §16.1.8, §16.4 | 4 |
| 12 | Union injection inference without expected type (`union_*`) | §13.3 | 3 |
| 13 | Misc expression-level deltas (`expressions.*`) | §16 | 5 |
| 14 | Runtime-model deltas surfaced by the newly implemented `assertEvalErrorContains`/`assertExecute` directives: source-order named-constructor field evaluation with runtime-trapping division (`data_types.constructors.positive_named_field_source_order_evaluation` — §28.2.1 proof-carrying `(/)` rejects `1 / 0` statically here), evaluation-time name-resolution failure for a wildcard-imported constructor (`modules.imports.item_kind_selectors.negative_wildcard_ctor` — resolution is static here), and a recursion-depth guard with a clean runtime error (`runtime.recursion.negative_divergent_recursion_depth_guard` — the pure evaluator diverges instead) | §10.1.1, §8.3, §32.1 | 3 |

The remainder (~10) is a long tail of one or two fixtures each:
boolean-proposition coercion (§11.4.2), deep value `show`/equality
(`interpreter`, `examples`), parser recovery without crash,
short-circuit suspended-operand typing (§16.1.3), linear-function
argument-quantity subsumption (`arrow_reject_*`, §12.2.1), patch
diagnostics payloads, and `core_semantics` evaluation deltas beyond
the spec conflicts above.
