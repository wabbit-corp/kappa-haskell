# DIAG-013: Alias-exposed strict value cycle

Transparent normalization exposes a body-facet cycle containing the non-function initializer `makeType`. The specific
strict-value-cycle rule takes precedence over the unsupported mixed-cycle fallback.

## Normative targets

* `§3.2.11A`
* `§9.5.6`
