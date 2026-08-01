# Appendix T fixtures: module-wide declaration SCCs and induction-recursion

These fixtures accompany the Spec(106) amendment that makes top-level declaration order non-semantic, discovers
recursive groups from semantic declaration facets, and admits ordinary induction-induction, induction-recursion, and
family-indexed induction-recursion.

The archive is organized by coverage category. Every suite has a `README.md` recording its normative targets. Standard
suites contain `suite.ktest`; incremental suites contain contiguous `stepN` suite roots and `incremental.ktest`.

The fixtures use the Appendix T directives introduced by the amendment. They are conformance inputs, not a claim that
every conceivable Kappa program has been enumerated.
