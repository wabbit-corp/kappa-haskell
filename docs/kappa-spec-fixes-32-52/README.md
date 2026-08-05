# Kappa issues #32 and #52 patch bundle

Contents:

* `Spec(107)-issues-32-52.md` — full updated specification.
* `KNOWN_SPEC_ISSUES(4)-issues-32-52.md` — ledger with #32 and #52 moved to resolved; the coherent foreign-call edit also
  closes #76.
* `issues-32-52.patch` — cumulative git patch for the specification, ledger, and all conformance fixtures.
* `spec-only-issues-32-52.patch` — specification-only patch for `docs/Spec.md`.
* `ledger-only-issues-32-52.patch` — issue-ledger-only patch for `docs/KNOWN_SPEC_ISSUES.md`.
* `ready-to-insert-spec-changes.md` — insertion map and concise normative summary.
* `masking-comparison.md` — comparison with GHC, Cats Effect, ZIO, and Monix, plus the selected Kappa synthesis.
* `appendix-t-tests/issue-52-quantity-borrow/*.kp` — standalone issue #52 fixtures.
* `appendix-t-tests/issue-32-mask-restore/*.kp` — standalone issue #32 fixtures.
* `SHA256SUMS` — digests for all delivered files other than the checksum file itself.

Validation performed:

* the patch passes `git diff --check`;
* the patch applies cleanly to pristine copies of `Spec(107).md` and `KNOWN_SPEC_ISSUES(4).md`;
* the patched specification and ledger compare byte-for-byte with the bundled full updated files;
* Markdown fence balance, test directive shape, trailing whitespace, and basic delimiter balance were checked; and
* every fixture is a standalone single-file Appendix T suite; and
* the final red-team matrix contains 29 fixtures: 13 for issue #52 and 16 for issue #32.

No Kappa compiler executable was available in the working environment, so the `.kp` suites were structurally validated
but not executed.
