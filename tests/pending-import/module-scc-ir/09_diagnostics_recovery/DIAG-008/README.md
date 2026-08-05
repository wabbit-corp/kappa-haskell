# DIAG-008: Undefined derive target remains unresolved

An implementation-defined test capability cannot invent source-language declarations or change name resolution.
Because `BadRecursiveOperation` is neither declared by the suite nor standardized by the spec, the derive target is an
ordinary unresolved name. A portable source-only fixture cannot manufacture the generated dependency cycle described by
the old version of this test.

## Normative targets

* `§7.1A`
* `§14.5`
