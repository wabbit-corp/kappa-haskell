# Retargeted conformance fixtures — unified derive / canonical evidence

Conformance fixtures whose pinned outcomes the 2026-08-02 unified-`derive` /
canonical-evidence revision invalidated. Found by a five-lane sweep of the
conformance tree with independent adversarial verification (6 candidates,
6 confirmed), rewritten here to the new contract, staged pending
implementation. Each carries a provenance header and a `-- STATUS(3014a0d9)`
baseline (2 pass / 4 fail at 3014a0d9). They promote back at DA-9
(docs/DERIVE-AUTOMATION-PLAN.md). Two
came from the ACTIVE nat-fin-refinement contract, whose manifest now counts
102 suites.

| fixture | original path | class |
| --- | --- | --- |
| `CURRY-singleton-data-wrapper-deriving-wrapper-eq.kp` | `tests/conformance/spec-coverage/adts/CURRY-singleton-data-wrapper-deriving-wrapper-eq.kp` | flips-to-accept |
| `CURRY-do-refutable-pattern-monad-failure.kp` | `tests/conformance/spec-coverage/do-blocks/CURRY-do-refutable-pattern-monad-failure.kp` | flips-to-reject |
| `derive-isset-function-field` | `tests/conformance/spec-coverage/nat-fin-refinement/negative/derive-isset-function-field/main.kp` | flips-to-accept |
| `handwritten-eq-missing-laws` | `tests/conformance/spec-coverage/nat-fin-refinement/negative/handwritten-eq-missing-laws/main.kp` | flips-to-accept |
| `cubical-gate-inactive-refl-needs-definitional-equality.kp` (renamed from cubical-gate-inactive-no-funext.kp) | `tests/conformance/spec-coverage/rows-props/cubical-gate-inactive-no-funext.kp` | assertion-invalidated |
| `typelevel-source-instances-rejected.kp` | `tests/conformance/universes/typelevel-source-instances-rejected.kp` | diagnostic-changed |
