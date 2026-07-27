# Nat, Fin, refinement, and representation conformance contract

This package contains 103 directory suites: 22 imported from the original bundle derivation, plus 49 added 2026-07-26 by the catalog-gap pass (T.12 items previously uncovered) and the corpus-reconciliation pass (tests moved in from dx-issues/spec-coverage and green conformance tests re-based after the revision flipped their expectations). Original derivation sources:

* `docs/Kappa-Nat-Fin-Refinement-Patch-Bundle/Appendix-T-Nat-Fin-Refinement-Tests.md`;
* `docs/Kappa-Nat-Fin-Refinement-Patch-Bundle/Additional-Backend-and-Certificate-Pseudotests.md`; and
* the corresponding normative changes in `docs/Spec.md`.

The suites remain pending because the current compiler still treats `Nat` as a
compiler-opaque carrier sharing the integer primitive/representation path,
rejects every `derive` declaration, and lacks the required no-confusion,
arithmetic-certificate, `Fin`, `Refined`, symbolic-cardinality,
representation-certificate, and backend representation contracts. The runtime
already has an exact GMP fallback for large integer operations, but it does not
yet implement the logical `Nat` and verified representation contract. The
Appendix T analysis and representation directives are also not implemented by
`Kappa.TestHarness`.

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

The artifact mutation suites include explicit `MUTATION.md` procedures until the
harness gains deterministic artifact mutation support. Promotion requires those
procedures to become executable fixtures, not prose-only checks.

The provider-determinism pair currently checks accepted interface semantics
across an unrelated import. Before promotion, NFR-0 must also compare the
selected normalization-provider identity and generated proof or certificate
bytes. The current `assertSemanticHashEquals` implementation only covers a
narrow nominal-interface summary and is not sufficient by itself.

## Baseline

The 2026-07-25 baseline from:

```sh
kappa test tests/pending-import/spec-coverage/nat-fin-refinement
```

is 22 suites: 3 passed, 9 failed, 1 unsupported, and 9 harness errors.

The three apparent passes are not package-promotion candidates.
`arithmetic-underconstrained` exercises the pre-existing rule that explicit
holes remain unsolved but does not establish the new arithmetic solver;
`derive-isset-function-field` currently rejects because every `derive`
declaration is unsupported; and `in-membership-syntax` rejects because the
grammar has no `in` expression. The last must remain paired with a passing
`contains` test. The unsupported suite requires arithmetic-certificate
capability. The harness errors are intentional gates for the new Appendix T
analysis, certificate, erasure, and representation assertions. The remaining
failures require the source, elaboration, prelude, analysis, artifact, or
backend work assigned in `docs/NAT-FIN-REFINEMENT-PLAN.md`.
