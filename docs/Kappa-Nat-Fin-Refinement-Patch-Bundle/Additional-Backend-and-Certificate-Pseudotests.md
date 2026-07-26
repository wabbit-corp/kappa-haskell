# Additional backend and certificate pseudotests

These tests are not meant to be source-only inline tests. They are directory-suite or compiler-fixture tests that mutate KCoreText, interface artifacts, or KBackendIR dumps. Tiny bit rude to ask source code to forge a certificate against itself.

## Arithmetic certificates

1. Build a source module that requires arithmetic transport for `Vec (m + n) A` to `Vec (n + m) A`.
2. Capture the generated KCoreText with a compact arithmetic certificate.
3. Verify that the unmodified certificate passes `assertArithmeticCertificatesValid`.
4. Mutate exactly one of: goal expression, assumption order, provider identity, provider version, domain version, context telescope, or canonical normal form payload.
5. Re-run KCore verification.
6. Expected result: rejection with `E_KCORE_ARITHMETIC_CERTIFICATE_INVALID` and no accepted KBackendIR.

## Representation certificates

1. Build a module containing `Fin n`, a closed enum, a finite product, and `NatBetween 2 30` expressed using `contains (2 .. 30)`.
2. Capture the representation certificates for ordinal, exact-natural, and refinement cases.
3. Verify that the unmodified artifacts pass `assertOrdinalRepresentation`, `assertExactNaturalRepresentation`, and `assertRefinementRepresentation`.
4. Mutate rank/unrank round-trip proof references, target type identity, erased-field summary, source-evidence identity, or backend-profile restrictions.
5. Expected result: rejection with `E_KCORE_REPRESENTATION_CERTIFICATE_INVALID`.

## Backend exactness

1. Compile a program computing values above native machine-word range, including addition, multiplication, division, modulo, successor, predecessor-on-positive, and comparison.
2. Run it on every runnable backend profile.
3. Expected result: exact mathematical results, no overflow, no wraparound, no unary successor storage in the runtime representation audit.

## Managed backend caution

1. Compile a certified finite ordinal type under native and managed profiles.
2. Native full-layout profiles must advertise and use compact ordinal/packing capabilities where eligible.
3. Managed JVM/CLR/Python profiles may preserve nominal wrappers or host values unless they explicitly advertise the compact/packed capability.
4. All profiles still erase quantity-`0` proof fields and preserve source behavior.
