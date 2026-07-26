# Nat / Fin / Refined patch bundle

Files:

* `Spec-Nat-Fin-Refinement-v2.patch` — unified diff against the current `Spec(102).md`, labelled as `Spec.md` for easy application after copying the spec to that filename.
* `Appendix-T-Nat-Fin-Refinement-Tests.md` — Appendix T-style conformance tests to insert as a separate T.12 test section.
* `Additional-Backend-and-Certificate-Pseudotests.md` — non-source-only backend/certificate fixture tests.

Main changes:

* Makes `Nat` an ordinary `Zero`/`Succ` inductive source type while requiring exact non-unary runtime representation.
* Adds generated no-confusion packages for ordinary data declarations.
* Changes `Eq` to refine `IsSet` and adds checked `derive IsSet` / `derive Eq` rules.
* Fixes semiring hierarchy by requiring commutative additive evidence for ordinary `Semiring` and adding a separate additively noncommutative trait.
* Adds proof-producing arithmetic/index solving, normalization-provider artifacts, and compact arithmetic certificates without extending definitional equality.
* Defines proof-carrying `Fin n`, generic `Refined`, `RefinementView`, symbolic cardinality, ordinal representation certificates, exact-natural certificates, and refinement representation certificates.
* Keeps membership as an ordinary `contains` function through `Contains`; no hardcoded `in` membership syntax is introduced.
* Strengthens backend obligations in a tiered way: all runnable backends must support exact non-unary `Nat` and proof erasure; native full-layout profiles must support compact finite ordinal/packed field capabilities; managed backends may be more conservative unless they advertise those capabilities.

Application check performed:

```text
git apply --check Spec-Nat-Fin-Refinement-v2.patch
```

against the attached `Spec(102).md` copied to `Spec.md`.
