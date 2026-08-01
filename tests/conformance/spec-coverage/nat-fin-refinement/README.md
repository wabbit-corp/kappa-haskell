# Nat, Fin, refinement, and representation conformance contract

This package contains 103 directory suites: 22 imported from the original bundle derivation, plus 49 added 2026-07-26 by the catalog-gap pass (T.12 items previously uncovered) and the corpus-reconciliation pass (tests moved in from dx-issues/spec-coverage and green conformance tests re-based after the revision flipped their expectations). Original derivation sources:

* `docs/Kappa-Nat-Fin-Refinement-Patch-Bundle/Appendix-T-Nat-Fin-Refinement-Tests.md`;
* `docs/Kappa-Nat-Fin-Refinement-Patch-Bundle/Additional-Backend-and-Certificate-Pseudotests.md`; and
* the corresponding normative changes in `docs/Spec.md`.

The 103 manifest-owned suites are active. Logical `Nat`, checked derivation,
proof-producing arithmetic, `Fin`, `Refined`, symbolic cardinality, and
independently replayed arithmetic and representation certificates are
implemented. Exact non-unary `Nat` and proof erasure are required on every
runnable backend. The optional `rt-compact-finite-ordinal` profile is not
advertised, so its two layout-specific suites report `Unsupported` rather than
silently accepting a generic layout as compact.

The package is intentionally split by contract surface:

| Root | Suites | Primary coverage |
| --- | ---: | --- |
| `positive/` | 61 | Nat constructors/computation, proof-directed right-identity transport, no-confusion, derivation, provider selection, arithmetic transport, Fin, refinements, and range membership |
| `negative/` | 28 | unsupported derivation, noncommutative evidence, underconstrained solving, missing refinement proof, out-of-range literals, and forbidden `in` syntax |
| `analysis/` | 6 | inhabitance, symbolic cardinality, and ordinal representation |
| `backend/` | 4 | exact unbounded Nat, proof-field erasure, and capability-gated compact native layouts |
| `artifact/` | 4 | arithmetic certificates, representation certificates, provider determinism, and mutation rejection |

`manifest.json` is authoritative for paths, provenance, owner stages, and
capabilities. No suite may move to active conformance merely because it produces
an error: its declared source or artifact outcome and every required harness
assertion must pass.

The artifact suites use executable harness mutations. Each decisive
certificate field class is changed independently, canonically serialized, and
required to fail replay with the certificate-specific diagnostic.

The provider-determinism pair independently compiles variants separated by an
unrelated import and compares their canonical generated proof/certificate body
bytes through the production KCore checkpoint.

## Active gate

The active contract is run with:

```sh
kappa test tests/conformance/spec-coverage/nat-fin-refinement
```

The 2026-07-30 promotion result is 101 passed, zero failed, two explicitly
unsupported optional compact-layout suites, and zero harness errors.
