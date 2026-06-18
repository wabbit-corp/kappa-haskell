# Native backend redesign plan (Haskell reference) — reject the closed catalog / runtime string-dispatch design

Date: 2026-06-18. Goal: full Spec.md compliance for build/package/native, meeting or
exceeding the F# standing goal (`/opt/workspaces/kappa/KAPPA_BUILD_PACKAGE_NATIVE_LANE.md`).
No hardcoded native catalog, no runtime primitive dispatch as the native backend design.

## What is REJECTED (the old design, to be removed from the optimized native lane)

1. **`src/Kappa/Backend/NativeCatalog.hs`** — a closed, hardcoded table of
   `host.native.sqlite3` / `host.native.posix.net` module surfaces, each member mapped to a
   runtime FFI primitive name (`__sqliteOpen`, `__tcpListen`, …). This is the "hardcoded native
   catalog" the goal forbids. The set of native functions/dependencies must be **discovered and
   resolved from the manifest's `nativeBinding` configuration** (symbol list with ABI signatures,
   realization inputs, link/load specs, hashes/lockfile provenance), never a closed in-compiler list.

2. **`gsHostPrims :: Map GName Text`** in `Backend/C.hs` — maps each provided `host.native.*`
   member to a runtime FFI primitive **string name**; `compileGlob` lowers such a reference to
   `emitPrim prim`, i.e. a curried `kprim_call("__sqliteOpen", …)`. This is the rejected
   string/name-dispatched, KValue-dispatched primitive call path for native output.

3. **`runtime/kappart_ffi.c` string dispatch** — `prim_is_io(p)`, `prim_arity(p)`, `ffi_call(p, …)`
   implemented as `strcmp`/`IS("__sqliteOpen")` chains. This is the runtime primitive registration +
   dispatch table the goal forbids for the native design. `prim_fire_pure`/`kprim_call` over native
   symbols must disappear from optimized native codegen.

## What REPLACES it (direct typed C call sites, manifest-driven)

The manifest fully describes each native binding (work already started in the working tree —
`Build/Types.hs`, `Build/Reify.hs`, `Prelude.hs`):

- `nativeBinding name provides surface abi inputs link load`
- `surface = symbolList [ symbolDecl member cSymbol params result, … ]` where each
  `symbolDecl` carries the Kappa member spelling, the **C symbol name**, and the **ABI signature**
  (`params : List CType`, `result : CType`) — `CType ∈ {ctUnit,ctInt,ctInt64,ctBool,ctDouble,ctString,ctHandle,ctRawPtr}` (§26.1.1/§26.1.4 conservative vocabulary).
- `inputs = [ headers […], includeDir …, define …, pkgConfig …, shim […], moduleMap […], prebuiltNative … ]`
  — inert config (§35.13); discovery (pkg-config, header digest) happens in build-plan resolution, not config-eval.

**Build plan resolution** (`Build/Plan.hs`) turns these into a set of `ResolvedNativeSymbol`
records: `GName ↦ {cSymbol, [CType] params, CType result, link/load provenance, digests}`, with
pinning/lockfile provenance (§27.1.1/§36.6A) as the F# lane already does.

**Codegen** (`Backend/C.hs`) consumes the resolved symbols, NOT a catalog:
- emit one `extern <cret> <cSymbol>(<cparams>);` prototype per resolved symbol into `.kappa.c`;
- emit one **generated, statically-typed** marshalling wrapper per symbol that unboxes each
  `KValue*` arg to its declared C ABI type, calls `<cSymbol>(…)` **directly**, and boxes the result;
- at a saturated call site for a host.native member, emit a **direct typed call** to that wrapper —
  no `kprim_call`, no primitive name string, no runtime arity/IO lookup.
- The C toolchain invocation uses the resolved `inputs`/`link`/`load` (`-I`/`-D`/`-L`/`-l`,
  pkg-config flags, shim/translation units, header set).

**Quarantine**: the `__sqliteOpen`-style runtime FFI prims + `kappart_ffi.c` string dispatch are an
**interpreter-only** compatibility path (tree-walking `Eval.hs` / `kprim_call`). They are explicitly
**excluded from optimized native backend completion** and must not appear in optimized `.kappa.c`.
A test asserts optimized native output for a native-using program contains zero `kprim_call("__`/native
`prim_fire_pure`.

## Process (per goal)

1. This plan (rejecting the old design) — DONE.
2. Launch three independent, unconstrained adversarial reviewers (broad Spec.md compliance prompt).
3. Remediate every legitimate finding; rerun broad review.
4. Commit only coherent increments after tests + adversarial gates pass. No push/tag until told.
5. Keep `KAPPA_SELF_HOSTING_PORT_NOTES.md` as the live bug queue.

Completion is invalid if anything is marked unsupported/subset/future-work/manual/hardcoded-interim
without a precise Spec.md defect citation.
