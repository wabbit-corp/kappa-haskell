# Kappa first-class levels, solver, generalization, and recursive schema tests

This package contains 67 independent Appendix T directory suites accompanying
`kappa_first_class_levels_solver_generalization_spec_patch.md`.

The suites cover:

* arbitrary stable total `TypeLevel` terms as universe indices;
* opaque neutral level atoms and exact dependent result types;
* declaration-boundary parametric generalization;
* explicit quantifier-interchange evidence;
* ordinary elimination of unbounded parametric packages;
* erased proof binders for declaration-universe constraints;
* AC/ACI constructor normalization and paired-Presburger rigid entailment;
* portable principal inference, cancellation, and residual classifications;
* arithmetic KCoreText certificates and proof-irrelevant semantic hashing;
* same-or-lower recursive declaration schemas;
* expected-type-directed direct schema lifts and bounded schema reification;
* normal `Monotone` trait evidence discovery.

The package is a conformance specification. The repository integration imports this exact tree under
`tests/conformance/spec-coverage/first-class-levels-solver-generalization/`; all 67 suites pass the Appendix T harness.
