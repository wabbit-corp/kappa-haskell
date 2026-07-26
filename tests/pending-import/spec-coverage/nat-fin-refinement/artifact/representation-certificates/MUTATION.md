# Representation-certificate mutation contract

1. Compile `main.kp` and capture its ordinal, exact-natural, and refinement
   representation certificates.
2. Independently verify each unmodified certificate.
3. Mutate one field at a time: rank/unrank round-trip evidence, target type
   identity, retained-field summary, source-evidence identity, constructor
   mapping, erased-field summary, or backend-profile restriction.
4. Each mutated artifact must be rejected with
   `E_KCORE_REPRESENTATION_CERTIFICATE_INVALID`.
5. A handwritten `OrdinalRepresentation` instance without a compiler
   certificate must not change layout.
