# Retargeted conformance fixtures — Spec 107 module-SCC / induction-recursion

Conformance fixtures whose pinned outcomes the 2026-08-01 Spec(106)->Spec(107)
revision invalidated. Each was found by an eight-lane sweep of the 4,130-fixture
conformance tree (1,407 fixtures examined in depth; 40 candidates), confirmed by
an independent adversarial verifier (36 confirmed, 4 refuted and left in place),
rewritten here to the Spec-107 contract, and staged pending implementation.
Each file carries a provenance header naming its original conformance path and a
`-- STATUS(f1e4161b)` baseline line. The 2026-08-01 baseline over the 36:
**12 PASS / 5 FAIL / 0 UNSUPPORTED / 19 HARNESS-ERROR** — the harness errors
pin the not-yet-registered Spec-107 codes and families
(`E_DATA_STRICT_POSITIVITY`; `E_RECURSIVE_VALUE_CYCLE` exists today but only
under the old `kappa.termination.failure` family, not the required
`kappa.declaration.recursive-group`), the fails are behavior gaps (top-level
forward references, group signature rules), and the 12 passes are
comment-only retargets whose unchanged directives are already green — those
twelve are immediately promotable back to conformance as soon as their
updated rationale text is accepted (MSI-0 may return them early rather than
waiting for MSI-8; until then their coverage is absent from the active
gate). They promote back to their original directories at MSI-8 at the
latest (see docs/MODULE-SCC-INDUCTION-RECURSION-PLAN.md).

Breakage classes: `diagnostic-changed` (20) — mostly positivity rejections
re-homed to `kappa.data.strict-positivity` / `E_DATA_STRICT_POSITIVITY`
(§10.4.2, §3.2.11A), strict value cycles re-homed to
`kappa.declaration.recursive-group` / `E_RECURSIVE_VALUE_CYCLE` (§9.5.6), and
unsigned recursion re-pointed to `E_MISSING_EXPLICIT_SIGNATURE` (§9.5.5);
`assertion-invalidated` (13) — premises about preceding signatures,
source-order grouping, or old hidden phases; `flips-to-accept` (3) — top-level
forward references and order-dependent rejections §7.1A now accepts.

| fixture | original path | class |
| --- | --- | --- |
| `positivity-converged-nonpositive-param-reject.kp` | `tests/conformance/data_types/positivity-converged-nonpositive-param-reject.kp` | diagnostic-changed |
| `positivity-mutual-reject.kp` | `tests/conformance/data_types/positivity-mutual-reject.kp` | diagnostic-changed |
| `positivity-recorded-nonpositive-param-reject` | `tests/conformance/data_types/positivity-recorded-nonpositive-param-reject/main.kp` | diagnostic-changed |
| `positivity-reject-negative.kp` | `tests/conformance/data_types/positivity-reject-negative.kp` | diagnostic-changed |
| `positivity-reject-rose.kp` | `tests/conformance/data_types/positivity-reject-rose.kp` | diagnostic-changed |
| `positivity-transparent-alias-reject.kp` | `tests/conformance/data_types/positivity-transparent-alias-reject.kp` | diagnostic-changed |
| `BQN-use-before-define-let-binding.kp` | `tests/conformance/imported-anon/BQN-use-before-define-let-binding.kp` | assertion-invalidated |
| `EGGLOG-mutually-recursive-datatypes.kp` | `tests/conformance/imported-anon/EGGLOG-mutually-recursive-datatypes.kp` | assertion-invalidated |
| `HYLO-name-unresolved.kp` | `tests/conformance/imported-anon/HYLO-name-unresolved.kp` | flips-to-accept |
| `METACOQ-data-strict-positivity.kp` | `tests/conformance/imported-anon/METACOQ-data-strict-positivity.kp` | assertion-invalidated |
| `METACOQ-mutual-fix-distinct-binders.kp` | `tests/conformance/imported-anon/METACOQ-mutual-fix-distinct-binders.kp` | assertion-invalidated |
| `NARYA-mutual-recursive-fns.kp` | `tests/conformance/imported-anon/NARYA-mutual-recursive-fns.kp` | assertion-invalidated |
| `SOUFFLE-adt-branch-type-undefined.kp` | `tests/conformance/imported-anon/SOUFFLE-adt-branch-type-undefined.kp` | flips-to-accept |
| `compiler_stress.gadt.strict_positivity_rejected.kp` | `tests/conformance/imported-anon/compiler_stress.gadt.strict_positivity_rejected.kp` | diagnostic-changed |
| `data_types.positivity.alias_unfolding.kp` | `tests/conformance/imported-anon/data_types.positivity.alias_unfolding.kp` | assertion-invalidated |
| `data_types.positivity.mutual_data_group_accepted.kp` | `tests/conformance/imported-anon/data_types.positivity.mutual_data_group_accepted.kp` | diagnostic-changed |
| `data_types.positivity.phantom_parameter_accepted.kp` | `tests/conformance/imported-anon/data_types.positivity.phantom_parameter_accepted.kp` | diagnostic-changed |
| `decreases-div-adversarial-reject.kp` | `tests/conformance/recursion/decreases-div-adversarial-reject.kp` | flips-to-accept |
| `decreases-transparent-helper-cycle-reject.kp` | `tests/conformance/recursion/decreases-transparent-helper-cycle-reject.kp` | diagnostic-changed |
| `no-signature.kp` | `tests/conformance/recursion/no-signature.kp` | diagnostic-changed |
| `ATS-lazy-stream-eval-positivity.kp` | `tests/conformance/spec-coverage/adts/ATS-lazy-stream-eval-positivity.kp` | diagnostic-changed |
| `RACKET-data-tree-mutual.kp` | `tests/conformance/spec-coverage/adts/RACKET-data-tree-mutual.kp` | assertion-invalidated |
| `data_types.positivity.negative_occurrence.kp` | `tests/conformance/spec-coverage/adts/data_types.positivity.negative_occurrence.kp` | diagnostic-changed |
| `positivity-abstract-alias-not-admissible` | `tests/conformance/spec-coverage/adts/positivity-abstract-alias-not-admissible/suite.ktest` | diagnostic-changed |
| `positivity-function-domain.kp` | `tests/conformance/spec-coverage/adts/positivity-function-domain.kp` | diagnostic-changed |
| `positivity-mutual-iteration-reject.kp` | `tests/conformance/spec-coverage/adts/positivity-mutual-iteration-reject.kp` | diagnostic-changed |
| `thunk-positivity-wrapper-propagation.kp` | `tests/conformance/spec-coverage/adts/thunk-positivity-wrapper-propagation.kp` | diagnostic-changed |
| `ELIXIR-guard-definition-without-body-rejected.kp` | `tests/conformance/spec-coverage/declarations/ELIXIR-guard-definition-without-body-rejected.kp` | assertion-invalidated |
| `RACKET-letrec-mutual-recursion-toplevel.kp` | `tests/conformance/spec-coverage/declarations/RACKET-letrec-mutual-recursion-toplevel.kp` | assertion-invalidated |
| `SOUFFLE-relation-no-rules-warning.kp` | `tests/conformance/spec-coverage/declarations/SOUFFLE-relation-no-rules-warning.kp` | assertion-invalidated |
| `NICKEL-forall-body-type-violation.kp` | `tests/conformance/spec-coverage/diag-families-1/NICKEL-forall-body-type-violation.kp` | assertion-invalidated |
| `CREUSOT-cycle-in-open-logic-rejected.kp` | `tests/conformance/spec-coverage/proofs-deriving-totality/CREUSOT-cycle-in-open-logic-rejected.kp` | diagnostic-changed |
| `CREUSOT-recursion-with-substitution-detected.kp` | `tests/conformance/spec-coverage/proofs-deriving-totality/CREUSOT-recursion-with-substitution-detected.kp` | diagnostic-changed |
| `CREUSOT-termination-direct-recursion-caught.kp` | `tests/conformance/spec-coverage/proofs-deriving-totality/CREUSOT-termination-direct-recursion-caught.kp` | diagnostic-changed |
| `mutual-recursion-ten-function-cycle-run.kp` | `tests/conformance/spec-coverage/proofs-deriving-totality/mutual-recursion-ten-function-cycle-run.kp` | assertion-invalidated |
| `HYLO-trait-circular-refinement.kp` | `tests/conformance/spec-coverage/traits-instances/HYLO-trait-circular-refinement.kp` | assertion-invalidated |
