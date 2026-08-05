# IIR-017: Implicit non-identity recursive universe schema

A recursive operation called on the stored lower-level child has inferred schema instance `.{v}`. Because `v <= u`
does not make that instance identical to the current rigid `.{u}`, the call must spell `UEl.{v}` explicitly.

## Normative targets

* `§11.1.2.3A`
