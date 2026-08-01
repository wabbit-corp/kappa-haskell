# Chapter 36 fragment-validation conformance fixtures

These suites exercise §36.12 through a real `kappa.build.kp` project build. The
Kappa source files use ordinary Appendix T assertions in `suite.ktest`; the
small `build-request.json` file records the surrounding test runner's build
request because Appendix T v1 does not standardize a project-manifest/target
selection directive.

For each case, the build-test driver must:

1. evaluate `kappa.build.kp` under Chapter 35;
2. resolve the target names in `build-request.json` under Chapter 36;
3. run the standard assertions in `suite.ktest` against the complete build
   diagnostic multiset; and
4. not fall back to Appendix T's raw "all `.kp` files under the suite root"
   source-selection rule.

The manifests use the standardized `jvm` backend family only to provide a
concrete artifact target. The tests stop after `mode check`; no JVM artifact is
executed. A runner may substitute any supported backend profile while
preserving the fragment axes, target names, source roots, and selected fragment
sets.

The generated-source and implementation-defined admission cases remain
normative T.10 obligations but are not encoded here because they require,
respectively, a repository-specific code-generator fixture and an
implementation-defined admission extension.
