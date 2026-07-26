# Kappa cumulative nominal-family universe variance conformance suites

These are separate Appendix T-style suites accompanying the universe-variance patch based on `Spec(98).md`.

Each leaf directory is one independent suite. Negative suites pass by observing the required rejection and diagnostic.
Capability-gated future suites become mandatory once an implementation advertises the corresponding HIIT, HIRT, QIT,
or QIIT universe-variance capability.

Coverage includes role inference, stricter explicit annotations, full saturation, family-argument alignment, explicit
KCore `schemaLift`, certificate verification, constructor/case coherence, interface identity, and future higher/quotient
signature naturality obligations.
