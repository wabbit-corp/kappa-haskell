# Kappa unified `derive` and canonical-evidence patch

This package is a replacement for the earlier monolithic proposal. It contains:

* `READY_TO_INSERT_SPEC_CHANGES.md`, the normative patch against `Spec(108).md`;
* `APPENDIX_T_HARNESS_AMENDMENTS.md`, the added portable harness directives;
* `REVISION_NOTES.md`, a concise map from the previous proposal;
* `SOURCE_BASE.md`, the exact source-specification hash;
* `VALIDATION_REPORT.md`, the static audit result;
* `SHA256SUMS.txt`, checksums for every other file in the package;
* `TEST_MANIFEST.md`, a human-readable inventory of **109** independent suites;
* `tests/manifest.json`, the machine-readable inventory; and
* `tests/`, with one suite root per test rather than one enormous Markdown terrarium.

## Deliberate revisions from the previous proposal

* `reflectsDec`, `reflectsSound`, `reflectsComplete`, `happly`, `happlyForall`, `borrowHapply`, and `eqReflect` have ordinary implementations. Only the binder-aware extensionality projections `funExt`, `forallExt`, and `borrowFunExt` are genuine foundation `expect term` declarations supplied by the mandatory foundation provider.
* Every `forall` use was audited. Equality deciders and ordinary functions use ordinary arrows; theorem parameters remain implicit quantity-`0` Pis where intended.
* Trait evidence has two principled uniqueness modes: sealed-coherent and independently unique. Independent construction is justified by a checked `evidence uniqueness` certificate that cannot use `IsTrait` or coherence for its own goal.
* `Eq` and `Equiv` remain separate. The standard `Eq -> Equiv` bridge is a fallback instance, so a direct non-equality `Equiv` genuinely overrides it.
* `IsEquivalence`, `IsPreorder`, `IsPartialOrder`, and `IsTotalOrder` classify explicit relation values. `Preorder`, `PartialOrder`, and `Ord` select ambient structures.
* `Ord` now carries actual totality. The old `Dec ((x <= y) = True)` member proved decidability of a Boolean proposition, not totality.
* `Alternative` refines `Applicative` and carries left identity, right identity, and associativity, but no speculative distributivity or commutativity laws.
* Synthesized members use unambiguous prefix syntax, such as `derive eqComplete : ...`; ordinary expression bodies retain `= derive` and `derive (T)`.

## Test execution model

Each path named in `TEST_MANIFEST.md` is a separate Appendix T suite root. The package contains **122 Kappa source files**, including **3 incremental suites** and **5 non-incremental multi-file suites**.

The files were statically audited against the current specification grammar and the companion harness amendments. No Kappa compiler was available in the environment, so the fixtures were not executed. That limitation is recorded rather than concealed beneath a tasteful layer of confidence.
