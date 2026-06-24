# Pending import — staged ANON corpus failures

Converted from `anon-workspace/new-tests` (the reference cross-language conformance
corpus). These did **not** pass against the current Kappa compiler with a mechanical
convert (`mode analyze`→`check`, `anonlang.`→`kappa.`, `Anon`→`Kappa`). They are staged
here — OUTSIDE `tests/conformance`, so the gate ignores them — to fix & import later.

360 sibling tests DID import cleanly and live in `tests/conformance/imported-anon/`.

## Categories

### `syntax-dialect/` — 491
Parse/layout/operator error — the ANON surface syntax differs from Kappa's; needs rewriting or a parser feature.

### `different-family/` — 254
Kappa emits a different diagnostic family/code (often a more specific one, or a cascade). Some are importable by re-pointing the assertion to Kappa's family.

### `line-relaxable-cascade/` — 243
Right family emitted, but Kappa also emits many extra (cascade) errors — usually a partially-unsupported construct.

### `we-reject-positive/` — 177
Positive test (expected 0 errors) that Kappa REJECTS — potential gap/bug where we reject valid code.

### `harness-error-unregistered-family/` — 109
References a diagnostic family Kappa does not register (e.g. kappa.name.shadowing, kappa.quantity.satisfies, kappa.type.unsolved-metavariable). Needs a family decision.

### `we-accept-negative/` — 70
Negative test where Kappa emits NO diagnostic of the expected family — potential SOUNDNESS gap (we accept what should be rejected).

### `other/` — 17
Uncategorised failure.

### `multifile-other/` — 17
Other multi-file tests that did not pass.

### `cross-module/` — 11
Multi-file cross-module visibility/import/ambiguity tests; Kappa's cross-module name-resolution behavior differs. (Stored as proper multi-file dirs.)

### `unsupported/` — 3
Declared as requiring an unsupported capability.

### `hang/` — 1
Compiler does not terminate (or is very slow) — e.g. a Paterson-condition instance escaping the depth backstop (§14.3.5).

## Regeneration

Source: `anon-workspace/new-tests/<name>/*.lang`. Conversion + classification scripts
were run ad hoc; the per-category name lists are the directory contents here.
