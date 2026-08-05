# DIAG-009: Incomplete recursive operation body

Recovery preserves the group header and reports the missing expression rather than an unresolved operation name.

The downstream inductive-recursion check may be blocked instead of materialized as a suppressed diagnostic, so only the
mandatory recovery root is asserted.

## Normative targets

* `§3.1.14A`
* `§9.5.7`
