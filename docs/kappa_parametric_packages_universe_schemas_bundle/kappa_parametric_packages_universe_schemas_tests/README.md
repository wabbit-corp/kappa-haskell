# Kappa parametric packages, universe schemas, and completed KCoreText conformance tests

These are separate Appendix T-style suites accompanying the follow-up specification patch based on `Spec(97).md`.

Each leaf directory is one independent standard directory suite. The root is a catalog, not one aggregate suite.

The suites cover:

- unbounded parametric type-witness packages and ordinary-code rejection;
- explicit declaration universe schemas and explicit instantiation;
- principal least-universe inference;
- universe-polymorphic user-defined equality with parametric endpoints;
- constructor-size behavior after observation-mode defaulting;
- complete runtime and solver `TypeLevel` algebra;
- deterministic rejection of inconsistent level assumptions;
- local universe generalization;
- KCore observation-dependency barriers;
- completed KCoreText universe instantiation, local schemas, constraints, and certificates;
- focused Girard/Hurkens prerequisite failures.

Every suite is expected to produce harness outcome `pass`. Negative suites pass by observing the required rejection and diagnostic.
