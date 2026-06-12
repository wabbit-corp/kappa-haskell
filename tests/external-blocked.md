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

### Outside Spec.md: spec-mandated `unsupported` (40 fixtures)

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
- **Unsupported `x-` extension directives** (13): per §T.3 an
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
  `modules.files.positive`); `x-assertContainsTokenTexts` (1:
  `lexical.operator_identifiers_fixity.operator_tokens.operator_sections.positive`).
  These assert raw token streams / constructor tables / module
  identity dumps this harness does not expose.
- **`requires capability unicodeSourceWarnings`** (4:
  `unicode.text.appendix_t.901/902/903/905_optional_*_warning`) and
  **`legacyCharAlias`** (2: `unicode.text.appendix_t.900`, `…904`):
  neither name appears in the §T.4 portable capability list, so the
  precondition is unmet here → unsupported (§T.8). (The fixtures
  themselves mark these "optional".)
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

### Outside Spec.md: spec-mandated `harnessError` (41 fixtures)

§T.3: *"Any unknown standard directive, malformed directive, or
ill-typed directive argument is a harness error."* All 41 fixtures
(each enumerated with its offending line in "Harness errors" above)
use private, non-`x-`-prefixed directives of the corpus's own
implementation; none appears in Appendix T (§T.3 grammar, §T.4
configuration list, §T.5 assertion lists) nor anywhere else in
Spec.md, so harnessError is the mandated outcome — these can only
become passes if the corpus renames them `x-…` or Appendix T adopts
them. Directive occurrence counts across the 41:
`allow_unsafe_consume` (31), `assertParameterQuantities` (9),
`assertRunStdout` (4), `assertExecute` (3),
`assertEvalErrorContains` (3), `assertDoItemDescriptors` (3),
`assertInoutParameters` (1), `assertContainsTokenTexts` (1).
(`assertEval` and `assertDiagnosticCodes` are likewise nonstandard
but have an evident portable meaning; this harness implements them —
and the `x-assertEval`/`x-assertEvalErrorContains`/
`x-assertDeclDescriptors`/`x-assertTraitMembers` extensions — as
documented compatibility extensions, as §T.1 permits.)

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
  documented `E_IMPLICIT_UNSOLVED ↔ E_TYPE_MISMATCH` §3.1.2A alias).

### Tracked gaps (spec-defined, not implemented; honest `fail`s)

The remaining 525 failures group by feature, ranked by fixture count
(classification from the raw log; one fixture may exhibit several
gaps — it is counted under the dominant one):

| rank | feature gap | spec | ~fixtures |
|---|---|---|---|
| 1 | QTT usage/borrow enforcement: quantity counting, linear/affine/relevant violations, borrow escape/overlap/consume, `E_QTT_*` family | §12.2–§12.4, §16.2.1, §3.3 | 124 |
| 2 | Unicode text stack: `Byte`/`Grapheme`/`Bytes` types, `g"…"`/`b"…"` quoted-literal forms, `std.unicode`, `std.hash`, ranges over text | §6.4–§6.5, §20.2, §29.3–§29.5 | 88 |
| 3 | Query comprehensions and first-class queries: `group by`/`order`/`join`/`into` clauses, `Query`/`QueryCore` lowering | §20.3–§20.10 | 54 |
| 4 | Projection declarations and projector/accessor descriptors | §9.1.1, §16.1.5–§16.1.6 | 35 |
| 5 | Macros/elaborator reflection: `Elab`/`Syntax`, quote literals `'{…}`, splices | §21, §23 | 31 |
| 6 | `this`-dependent record signatures and dependent records | §13.2 (dependent fields), §16.1.5 (`this` binders) | 24+12 (`types.records.dependent.*`, `this_*`, residual `static_objects.*`) |
| 7 | Diagnostic-code selection at application boundaries: spec's `E_APPLICATION_ARGUMENT_MISMATCH` vs this implementation's `E_TYPE_EQUALITY_MISMATCH`/`E_NAMED_ARG_*`/`E_IMPLICIT_UNSOLVED` choices | §16.1.7.1, §3.1.2A | ~15 |
| 8 | Required standard modules: `std.hash`, `std.bridge`, `std.atomic`, `std.supervisor`, `std.gradual`, `std.ffi` | §29.1–§29.3, §25–§26 | 13 |
| 9 | `let NAME : TYPE = …` inline-ascription definitions (parse gap; also blocks fixtures whose real subject is elsewhere) | §9.2 | 11 |
| 10 | Open rows / record row extension `:=`, `E_ROW_*` | §13.1.5, §13.2 | 10 |
| 11 | `std.deriving.shape` derivation-shape reflection | §22 | 10 |
| 12 | Active patterns (view patterns) | §17.3 | 8 |
| 13 | Record patch: nested/grouped paths, patch-specific diagnostics, import-stability suite | §13.2.5 | 8 |
| 14 | Effect handlers / effect rows / `using` resource binds | §18.1, §19.5 | 6+ (plus handler-local declaration forms inside blocks, §18.2) |
| 15 | Sealing and existentials (`seal`/`exists`/`open`, `E_SEAL_*`) | §13.4–§13.5 | 6 |

The remainder (~70) is a long tail: record/suspension `Need`-typed
lazy field insertion (§11.2, §16.2.2), associated trait type members
and higher-kinded instance heads (§14), definitional-equality
residue — record η, irrefutable tuple lets, optional-type sugar over
parenthesized types (§31.1, §13.1.9) — equality transport through
branch evidence (§16.1.8, §16.4), implicit-candidate scoping rules
(§16.3), URL imports (§8), `expect` declarations (§9.4), and fuzz
fixtures compounding several of the gaps above.
