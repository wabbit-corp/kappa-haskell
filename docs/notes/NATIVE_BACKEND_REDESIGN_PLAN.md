# Native backend redesign plan v2 — real ABI discovery/verification + broad string-dispatch elimination

Date: 2026-06-18. The v1 remediation (commit 21ac8b5) deleted the hardcoded catalog and the
runtime FFI string-dispatch, and made native members lower to direct typed call sites. That was
NECESSARY but NOT SUFFICIENT: per external manual audit it merely RELOCATED hardcoded host
knowledge from `NativeCatalog.hs` into a manifest `symbolList` + a hand-authored `native_shim.c`,
and did not discover/verify the real host ABI. See memory `kappa-native-abi-discovery-bar`.

## The bar (must ALL hold; do not claim completion otherwise)

1. **pkg-config is real discovery + identity.** Run `pkg-config --modversion --cflags --libs`;
   locate/read/HASH the actual `.pc` file(s); ENFORCE `Maybe minVersion`; record package + version
   + `.pc` identity in plan + lock + provenance.
2. **headers are located, hashed, preprocessed, and used to VERIFY signatures.** Locate real
   headers via the pkg-config include dirs; read/HASH; preprocess with the selected C driver +
   target + defines; verify each declared/used C symbol against the ACTUAL header declaration
   (compiler-checked typed-extern probe / static assert at minimum; libclang AST dump if available).
3. **No relocated hardcoding for sqlite (or any lib).** Bind REAL symbols where the ABI fits, or
   GENERATE the adapter wrapper from a trusted binding summary (§26.1.5) + verified header
   declarations — generated, reproducible, provenance-recorded source. A hand-written shim may
   exist only as a user-authored artifact, never as evidence of discovery/verification.
4. **No string primitive dispatch in optimized native output, broadly.** `kprim_call(const char*,…)`
   / `prim_fire_pure` must not appear in emitted optimized `.kappa.c` for ANY prim (incl.
   `printlnString`, intrinsics). Builtins lower to direct runtime functions / generated typed calls.
   The string-dispatch machinery may remain only in an interpreter/bootstrap path optimized native
   output never calls.
5. **Provenance/identity records everything affecting the generated interface/ABI** (§27.1.1/§36.6A
   /§36.28): selected headers/module-maps/symbol inputs, preprocessor defines, target ABI, adapter
   mode, pkg-config package/version/.pc identity, generated interface-artifact provenance — into
   plan + lock.

## Increments (each: implement → tests → broad adversarial review → remediate → commit)

- **I1 — string-dispatch elimination (#4).** Give every `basePrims` entry a direct C entry point;
  codegen emits a direct call (saturated) / generated curried fn-pointer value (partial); emitted
  `.kappa.c` has zero `kprim_call(`/`kprim(`. Quarantine `kprim_call`/`prim_fire_pure` to a
  bootstrap path optimized output never references (or delete if dead). Test asserts the property.
- **I2 — pkg-config real identity + minVersion + .pc/header hashing (#1,#2,#5).** Resolution-phase
  discovery records a `ResolvedNativeIdentity` (pkg version, `.pc` path+sha256, cflags/libs, header
  paths+sha256, defines, target, adapter mode) into provenance + lock; minVersion enforced
  (E_BUILD diagnostic on mismatch / missing).
- **I3 — header-verified signatures + generated adapter from trusted summary (#2,#3).** A trusted
  binding summary (read+hashed) names the REAL C symbols and adaptation per Kappa member; the build
  GENERATES an adapter TU that `#include`s the real headers and calls the real symbols (compiler-
  verified), content-hashed into provenance. The demo binds real `sqlite3_*` through a generated,
  verified adapter; `native_shim.c` is removed as "proof of support".
- **I4 — broad adversarial review** specifically asking whether real pkg-config/header/module-map
  ABI discovery, identity/provenance, signature verification, and string-dispatch elimination are
  COMPLETE; remediate; iterate.

Broad reviewers only (whole Spec.md + the bar above); never narrow them to deleted files.
