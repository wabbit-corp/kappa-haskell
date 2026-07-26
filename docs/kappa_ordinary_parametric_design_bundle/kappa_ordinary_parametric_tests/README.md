# Kappa ordinary/parametric and KCoreText conformance tests

These are separate Appendix T-style suites accompanying the specification patch.

Run each leaf directory as one independent standard directory suite. The root is a catalog, not one aggregate suite.

The tests cover:

- default and explicit `ordinary` / `parametric` binder syntax;
- floating bare `Type` and hidden declaration universe generalization;
- higher-kinded parametricity and Monad/Functor shapes;
- records, constructors, projections, and pattern preservation;
- parametric-promotion rejection paths;
- universe-polymorphic equality;
- runtime-capable `TypeLevel` values;
- proof-directed universe bounds;
- Hurkens/Girard barrier regressions;
- canonical KCoreText parsing, verification, and round trips.

See `manifest.json` for a machine-readable catalog.

Every suite is expected to produce harness outcome `pass`. Negative suites pass by observing the required rejection and diagnostic.
