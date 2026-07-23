# Spec-coverage campaign — staged tests

Tests written 2026-07-19/20 by a systematic coverage campaign over `docs/Spec.md`:
every spec section was analyzed against the existing conformance corpus (871 sections;
525 had zero `§` citations), 617 undertested/untested normative requirements were
identified, and tests were authored for them — including cross-feature combination
tests. Staged here, OUTSIDE `tests/conformance`, so the gate ignores them until
imported. Tests found to pass have been progressively imported to
`tests/conformance/spec-coverage/` (541 files at the time of writing); what remains
here mostly documents **compiler gaps**: the expectation is spec-correct but the
compiler does not implement it yet.

Directory = spec area (chunk) from the campaign, e.g. `effects-handlers/` covers
§18.1.14–18.1.25. Multi-file suites are directories with a `suite.ktest`.

## STATUS lines

Every test ends with a comment recording its outcome against a clean compiler build:

    -- STATUS(<commit>): PASS
    -- STATUS(<commit>): FAIL — <what the compiler actually does>
    -- STATUS(<commit>): UNSUPPORTED — <missing capability>
    -- STATUS(<commit>): HARNESS-ERROR — <e.g. spec-implied family not registered>

Tally at `a0497523` (573 units): **203 PASS / 331 FAIL / 17 UNSUPPORTED / 22 harness
errors**. FAILs are writer-classified compiler gaps (see each file's note); harness
errors are mostly tests asserting a spec-implied diagnostic family the implementation
does not register (same situation as `../harness-error-unregistered-family/`);
UNSUPPORTED is mostly `configMode`.

`[was PASS in an earlier STATUS line]` marks a **regression between `a51e1bf` and
`a0497523`**: 15 files, 12 of them `E_NAME_UNRESOLVED` on prelude exit-type names
(`Success`, `Interrupt`) in `io-fibers-stm/` — likely fallout of the
TypeLevel/universes revision touching the prelude; triage before trusting either
STATUS.

## Spec issues

Contradictions/ambiguities discovered while writing these tests are consolidated in
`docs/SPEC_ISSUES.md` (§-keyed, with provenance). Several tests there are cited by
name where an issue made an expectation unpinnable.

## 2026-07-22 addenda

- `delta-2026-07-22/README.md` records the campaign for requirements added or
  materially changed by the first-class-level and solver/generalization
  revision. Its tests now live in the semantic area directories above.
- `whole-spec-missed-2026-07-22/README.md` records a second whole-spec pass
  focused on non-universe combinations missed by the original campaign,
  including prelude trait shape, error/control layout, handlers, queries, GADT
  positivity, and multi-fragment expectations. Its tests now live in the
  semantic area directories above.
- `../../dx-issues/` stages common-expectation and diagnostic-quality probes
  found during the same audits.

## 2026-07-23 addenda

- `combo-2026-07-23/README.md` records the 249-test round-3 probe-first
  campaign: deliberate cross-feature combinations (linearity x active
  patterns/guards, borrows x record update x inout, handlers x resources x
  masking, existentials x erasure x opacity, GADT refinement x flow typing,
  cross-module suites, queries x linearity, interpolation x macros, unions x
  transport, numerics x traits), plus spec-anchored findings from the
  DX/robustness lanes. The tests now live in the semantic area directories
  above. Notable: 12 soundness-class compiler gaps (guard/borrow/as-pattern
  linearity accounting, opaque-inhabitance leak, erased-payload matching,
  comprehension linearity laundering) and one evaluator crash (Rational
  literal pattern). Round-3 spec issues are the dated addenda section of
  `docs/SPEC_ISSUES.md`; the consolidated bug list remains in
  `combo-2026-07-23/FINDINGS.md`.
- `../../dx-issues/` gained ~60 round-3 probes (beginner-mistake diagnostics,
  fix-it quality, cascade suppression, warning hygiene, prelude ergonomics,
  layout/CRLF/BOM, runtime common-sense, diagnostic consistency, degenerate
  inputs).
