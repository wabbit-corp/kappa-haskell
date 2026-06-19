# Kappa self-hosting port notes (Haskell reference)

Living log of lessons learned while building a Kappa-in-Kappa compiler
(`/opt/workspaces/kappa-self-hosting`), using this Haskell compiler as the
**runtime oracle** (and a cleaner modeling reference for several passes).
This file only records notes; the Haskell production code is not modified.

## How this compiler is used as an oracle
- It is the only available backend that *runs* programs which decompose strings
  (the self-host compiler's lexer needs this). See finding H-1.
- CLI: `cabal list-bin kappa` → `check | run [--json] | test | test --suite | audit | build`.
- The `test` command executes Appendix-T `--!` directive fixtures
  (`assertNoErrors`, `assertType`, `assertEval`, …) — used for Kappa-level fixtures.

## Actionable issue queue (prioritized — live, for the Haskell implementation team)

Severity: **HIGH** (perf/correctness bug or real-code friction) · **MED** · **LOW**.
Repros in the findings below. H-1 is an enabler (this is the runtime oracle), kept for context.

| ID | Sev | Area | Issue (expected → actual) | Fix direction |
|----|-----|------|---------------------------|---------------|
| H-4 | HIGH | elaborator perf (PERF BUG) | a single 26-term `\|\|`-chain of `String ==` (`c == "a" \|\| c == "b" \|\| …`) makes `kappa check` of the whole module take **>300s**; rewriting that one definition as an `if/elif` chain drops it to **~11s**. Super-linear in the size of a `\|\|`/`&&`-of-`String ==` expression. A 65-branch `if/elif` of `String ==` is fine; a 40-fn recursive SCC checks in 0.2s — so it is specific to deep `\|\|`/`&&` nests of `String ==`. | profile the elaborator on this shape; likely re-resolving the `Eq String` dictionary and/or re-normalizing the `\|\|` spine per term without memoization. Memoize/short-circuit. |
| H-5 | MED | CLI / build (`run`/`build` are single-file) | `kappa run FILE` / `build` compile only FILE+prelude; an `import kc.other` gives `E_MODULE_NAME_UNRESOLVED: imported module … is not part of this compilation unit`. No way to run a multi-module program from a source root (F# has `--source-root`). Forces concatenating modules or directory-suite workarounds for every run. | add multi-file `run`/`build`: discover & compile imported modules from a source root (like the directory-suite path already does for `test`). |
| H-2 | MED | IR-stage separation | the HS pipeline has a weaker IR split than F#'s `KFrontIR → KCore → KRuntimeIR → KBackendIR`; the self-host mirrors the F# stages. Not a bug, but if HS aims to be a reference it should expose comparable staged dumps. | optionally expose staged IR dumps comparable to F# `--dump-stage`. |
| H-1 | — | runtime intrinsics (ENABLER) | implements `__stringScalars`/`__bytesToList`/`__utf8Bytes`/… so it is the only backend that runs text-processing self-host code. | keep; this is what makes self-hosting testable. |

## Native backend redesign queue (2026-06-18 — consolidated from 3 independent adversarial reviews)

Design directive: native bindings discovered/resolved from the manifest `nativeBinding`
(symbol list + ABI signatures + inputs + link/load + digests), lowered to DIRECT C
prototypes + typed wrappers + direct typed call sites. NO hardcoded catalog, NO runtime
string/KValue primitive dispatch in optimized native output. See NATIVE_BACKEND_REDESIGN_PLAN.md.

| ID | Sev | Status | Issue | Fix |
|----|-----|--------|-------|-----|
| N-1 | CRIT | DONE | tree did not compile after the half-applied rename | finished rename; surface threaded forward |
| N-2 | CRIT | DONE | hardcoded `NativeCatalog.hs` was the live authority | **deleted** `NativeCatalog.hs`; surface + codegen derive from reified `SymbolDecl`s (`Plan.resolveBinding`, `Pipeline.applyNativeModules`/`nativeHostSymbols`) |
| N-3 | CRIT | DONE | decoded ABI surface was dead data | `[ResolvedNativeSymbol]` now threads plan → pipeline → codegen (`rxNativeSymbols`→`gsHostSyms`) |
| N-4 | CRIT | DONE | native calls lowered to `kprim_call("__…")` string dispatch | C.hs emits extern proto + typed wrapper (`kw_*`) + direct `knative`/`knative_sat` call site; verified zero `kprim_call("__` for natives in generated C |
| N-5 | CRIT | DONE | runtime `kappart_ffi.c` strcmp dispatch wired into core loop | **deleted** both FFI units; added `K_NATIVE` (codegen fn-pointer action) to runtime; removed `*_ffi` hooks |
| N-6 | CRIT | PARTIAL | native host-source identity now DISCOVERED + VERIFIED + recorded as provenance (`Kappa.Backend.NativeProbe`): pkg-config `--modversion`/`--atleast-version` (minVersion enforced fail-closed), `.pc` located+hashed, headers located+hashed, `verify` C decls compiled against the real headers (fail-closed `E_BUILD_NATIVE_ABI` on signature mismatch), composite identity written to `<base>.native.prov`. STILL OPEN: fold this identity into `kappa.lock` (verify-against-lock pinning) | add a `host-native` lock entry kind keyed per binding |
| N-15 | HIGH | PARTIAL | symbolList C-symbol names still author-named (the adapter/shim symbols); only the binding's declared REAL dependencies (`verify` decls) are checked against headers | bind directly to real symbols where the ABI fits + auto-derive/verify each symbolList entry |

## Broad adversarial review round 2 (post b59c759) — new findings (all spec-cited; deferrals are INCOMPLETENESS, not subset)

Confirmed DONE+correct by 3 independent reviewers: N-2..N-5, N-7, N-14 (zero kprim in emitted C, faithful extraction via compiled-probe arity check, K_NATIVE is_io correct, marshalling sound). H-3/H-4 elaborator pathology NOT reproducible (26-term ‖-chain checks in 0.27s; Eval.hs:162-174 already carries the fix) → resolved.

| ID | Sev | Status | Issue | Spec | Fix |
|----|-----|--------|-------|------|-----|
| N-16 | CRIT | DONE | native host-source identity now folded into `kappa.lock` as a `host-binding` entry kind (per binding); computed in the resolve/lock phase (`collectLockClosure`→`NativeProbe.hostBindingLockEntries`) so `--locked` verifies it and an unlocked build writes it. Identity composites pkg-config version+.pc digest, header digests, verified decls, defines, SHIM SOURCE DIGESTS (N-27), the SYMBOL SURFACE (N-19 partial), and the TARGET TRIPLE (N-22 partial) | §8.3.5:6918, §36.7 | done |
| N-17 | CRIT | DONE | `E_NATIVE_BINDING_UNPINNED` is now LIVE: `verifyLock` emits it (not the dep-mismatch code) when a `host-binding` entry is missing/changed under `--locked` (native suite: shim drift → E_NATIVE_BINDING_UNPINNED, fail-closed) | §8.3.5:6918 | done |
| N-18 | CRIT | open | reproducibility is opt-in (`--locked` off by default; unlocked build rewrites lock) — inverted vs F# verify-only default | §36.7, §3.2.15 | default package-mode to verify-only; explicit `--update` to write |
| N-19 | CRIT | open | symbolList C symbols themselves never ABI-verified (only the disjoint author-listed `verify` set); a bogus symbolList cSymbol builds unchecked; `inputs=[]` bindings have ZERO checking | §27.1.1:27367, §26.1.3 | require each symbolDecl carry a real C prototype compiled in the probe, or derive surface from headers; digest symbolList |
| N-20 | HIGH | DONE | `CType` widened to ctI8..ctU64/ctIsize/ctUsize/ctF32, each mapping to its exact C ABI spelling. UPDATED for §26.1.2:26114: the exact-width/pointer-width/float classes (incl. ctInt64) now surface as the std.ffi NOMINAL types (I8..U64/Isize/Usize/F32/I64) — the raw surface uses std.ffi scalar types as the spec MANDATES — with marshalling that constructs/destructures the MkXxx wrapper ctors (tag ids shared with in-program matches). ctInt (C `int`, not exact-width) stays Integer. std.ffi gained ergonomic iN/uN/f32/…+ accessors. Native suite: ctU32→U32 (htonl), ctI64→I64 (sqliteQueryInt, demo unwraps via i64Value) | §26.1.1, §26.1.2:26114 | done (std.ffi.c CChar..CBool spellings tracked) |
| N-21 | MED | PARTIAL | content identity is FNV-1a-64; §36.6A's MUST (a reproducibility artifact states its digest algorithm) is now satisfied — the lock header records `digest: fnv1a-64`. REMAINING: a cryptographic digest (sha256) for collision-resistant / cross-impl-byte-exact identity is not implemented (no crypto dep; FNV is the project's deliberate change-detection identity). Not a Spec MUST (cross-impl interop unmandated); revisit if a security/interop requirement lands | §36.6A:39557 | add sha256 (pure-Haskell or dep) if required |
| N-22 | HIGH | DONE | `targetTriple` now threaded to the cross-capable driver (`zig cc -target <triple>`) so a cross-compile targets the requested platform (a host gcc/clang leaves the host target — an explicit non-host triple there fails the link honestly), AND folded into the host-source identity (N-16). Calling convention / linked-library identity modeling still tracked | §36.21, §27.1.1:27366 | done (CC/data-layout/linked-lib identity tracked) |
| N-23 | — | N/A | `M.Raw`: §26.1.2's MUST is CONDITIONAL on "providing a refined surface for M". The backend exposes ONLY the raw conservative surface derived from `symbolList` (UIO results, scalar/handle vocabulary, no refinement overlay), so the condition is not met and M.Raw is not required. Becomes a real item only when a refined surface is added (with N-25) | §26.1.2 (conditional) | revisit with N-25 |
| N-24 | HIGH | DONE | RawPtr now surfaces as `Option RawPtr` (§26.1.1:27307-27309) — marshalling maps NULL↔None / non-null↔Some(MkRawPtr addr) (native suite: `getenv`→Some). Owning OpaqueHandle: §27.1.1:27316 EXPLICITLY PERMITS bare OpaqueHandle in a RAW host binding whose release is supplied out of band (the binding's close op) — the demo's host.native.* raw surface + sqliteClose qualifies, so this is compliant (documented in NativeFfi). The §26.1.2:26114 exact-width MUST is also satisfied (see N-20 redo) | §26.1.1:27303-27314, §26.1.4, §27.1.1:27316 | done |
| N-25 | HIGH | PARTIAL | adapter mode (`native.direct`, the only mode the zig profile realizes / the schema can select) is now recorded in the host-binding identity (§26.1.3). REMAINING: a selectable adapter-mode field (meaningful only once non-native profiles exist) + a trusted-summary input kind (§26.1.5) — pairs with the N-24 overlay subsystem | §26.1.1:26221, §26.1.3, §26.1.5 | add trusted-summary input + selectable adapter when non-native profiles land |
| N-26 | HIGH | DONE | `prebuiltNative` artifact now digested + expectedIdentity VERIFIED fail-closed (`NativeProbe.verifyPrebuilt`); digest folded into identity | §36.28, §36.6 | done |
| N-27 | MED | DONE | shim source content digested into the host-binding lock identity (`shimDigestLines`) | §27.1.1:27367 | done |
| N-28 | MED | DONE | `moduleMap` files now located+digested into the native identity (`digestRel`), fail-closed if missing; `needsDiscovery` triggers on it | §27.1.1:27370 | done |
| N-29 | MED | DONE | native shim/prebuilt/moduleMap paths routed through `safeWithinRoot` (rejects `..`-escape + symlink, §36.11) fail-closed | §36.11, §36.6A | done (headers stay system-path; shim/prebuilt/moduleMap within-root) |
| N-30 | MED | open | lock has no per-entry schema identity (§36.7:39603); space-separated fields unescaped; corrupt lock tolerated on unlocked (update) builds | §36.7:39603 | per-entry schema id; escape separators; reject corrupt lock |
| N-18 | CRIT | DONE | package-mode build is now LOCKED by default (§36.7:39662): the lock is verified up front and a missing/stale entry is fail-closed (`verifyLock` unless `--update`); only `--update`/`--lockfile-update` may write (§36.7:39664). Test harnesses pass `--update` for establishing builds; `--locked` is the explicit alias | §36.7:39662,:39664 | done |
| N-19 | CRIT | DONE | the Driver writes a generated header of the host extern prototypes (for shim-provided cSymbols — verify'd library symbols excluded to avoid system-header conflicts; header `#include`s stdint/stddef) and force-`-include`s it into the cc compile, so a shim defining a symbol with an ABI signature that disagrees with the manifest is a fail-closed compile error (native suite: `double probe_thing` declared `[ctI64] ctI64` → rejected) | §27.1.1:27366, §26.1.3 | done |
| N-36 | MED | DONE | (subsumed by N-18: a corrupt/missing lock is now fail-closed by default, not silently overwritten — writing requires `--update`) | §36.7 | done |
| N-33 | HIGH | DONE | canonical link/load text + resolved pkg-config `--libs` now folded into the host-binding identity (`Plan.linkText`/`loadText`, `pkgProvLines libs=`); a link-spec change repins → `E_NATIVE_BINDING_UNPINNED` under `--locked` (verified) | §27.1.1:27368, §36.21:41848,:41861 | done |
| N-34 | MED | DONE | added `ctF64`→`std.ffi.F64` (exact-ABI binary64 name, §26.2:27297); `ctDouble` kept as the documented ergonomic `Double` alias (like `ctInt`) | §26.1.2:26114, §26.2:27297 | done |
| N-35 | MED | DONE | U64/Usize now round-trip the FULL unsigned range incl. ≥ 2^63 via `kas_u64`/`ku64` (mpz import/export; bignum Integer) — native suite round-trips 2^64-1 exactly | §26.1.1:27293 | done |
| N-36 | MED | open | corrupt lock silently overwritten on a default (non-`--locked`) build (`lockWellFormed` checked only under `--locked`); subsumed once N-18 flips the default | §36.7 | gate updateLock on lockWellFormed |
| N-31 | LOW | DONE (native) | `unsafeConsume` native arity fixed to 1 (prim_arity + codegen table); interp arm `[_,_]` is correct (interp does not erase implicits) | — | done |
| N-32 | LOW | DONE | `CtString` NUL-truncation ABI convention now documented at the marshalling site (§26.1.1 String ABI; use CtRawPtr+length for byte-exact NUL-bearing data) | §26.1.1 | done |
| N-7 | HIGH | DONE | `nbInputs` decoded then ignored; FFI-unit picked by a Bool | Driver `resolveInputs` threads headers/includeDir/define/shim/prebuilt + runs pkg-config; `boRuntimeFfi`/stub removed; demo links real sqlite3 via pkgConfig |
| N-8 | HIGH | open | `M.Raw` mechanically-derived raw surface unimplemented (§26.1.2) | expose `host.native.X.Raw` from the binding description |
| N-9 | HIGH | DONE | `SelModulesUnder` prefix selector hard-rejected | both selector forms resolve to concrete host.native modules; root validated (non-host.native → E_NATIVE_BINDING_UNSUPPORTED) |
| N-10 | HIGH | open | no C-ABI export (§36.14); no toolchain/platform/calling-conv/data-layout model (§36.21) | artifact-identity record + structured toolchain model |
| N-11 | MED | PARTIAL | `CType` closed 8-enum, not full §26.1.1 exact-width scalars | created `Kappa.Backend.NativeFfi` (CType↔C-ABI↔Kappa-type↔marshalling); widening CType to exact-width (Int8/16/32, UInt*, Size) still open |
| N-12 | MED | open | adapter mode (§26.1.3) + trusted summaries (§26.1.5) not modeled | model adapter mode + trusted-summary types |
| N-13 | MED | open | `prebuiltNative` expectedIdentity decoded then never verified (§36.28) | verify + fold into identity (with N-6) |
| N-14 | HIGH | DONE | builtin prims (`printlnString`, intrinsics, etc.) string-dispatched via `kprim_call`/`prim_fire_pure` in optimized native output | `prim_fire_pure` branches extracted into 119 direct `kpf_*` C entry points; codegen emits a direct call (saturated pure → `kpf_x(arr)`/positional `kp_*`; IO → `knative_sat(kpf_io_x,…,1)`; partial → curried `knative`). Emitted `.kappa.c` has ZERO `kprim_call`/`kprim` (test asserts it). `kprim_call`/`prim_fire_pure` remain only as the never-emitted bootstrap K_PRIM path |

## Findings / lessons

### H-1 (decisive): Haskell evaluator implements string/byte decomposition
`src/Kappa/Eval.hs` implements `__stringScalars : String -> List Scalar`, `__bytesToList`,
`__bytesGet`, `__utf8Bytes`, `__uniScalarValue`; `src/Kappa/Prelude.hs` wires
`scalars s = __queryFromList (__stringScalars s)`, `bytesToList`, `scalarValue`, etc.
The F# interpreter implements none of these (see F# port notes F-1). Therefore the
self-hosting compiler is *executed* under this Haskell compiler.
Verified: `[ for c in scalars s yield natToInt (scalarValue c) ]` runs under `kappa run`.

### H-2: IR-split caveat (why F# is the architecture oracle, not this one)
Per the project direction, this Haskell compiler is used for modeling inspiration where
cleaner, but its IR-stage separation is weaker than the F# `KFrontIR → KCore → KRuntimeIR →
KBackendIR` split. The self-host mirrors the F# stage boundaries, not this pipeline's.
(Detailed comparison appended as the IR stages are ported.)

(more findings appended as stages progress)

### H-3 (MAJOR perf pathology): super-linear compile time on larger modules
`kappa check` time grows super-linearly in module size for the self-host compiler:
- lexer alone (~490 lines): ~10s CPU
- lexer+ast+parser merged (~1500 lines): >240s CPU (did not finish at 4min)
The F# oracle type-checks the identical source in ~1-2s. This is a Haskell-compiler
performance pathology (per-definition cost appears to grow with the size of the preceding
environment — likely re-elaboration/termination/conversion work scaling with module size),
NOT an infinite loop in the self-host code (smaller versions ran fine: 9/9 expr and 3/3
binding differential tests passed). A misdiagnosed "27-minute hang" during a diffast batch
was actually this slow compile under heavy machine load.
Consequence for self-hosting: compiling the *whole* growing self-host compiler under this
backend per runtime test is impractical. Validation strategy adopted: F# typecheck (fast)
gates the whole compiler; Haskell runtime tests run on isolated/smaller components (the
lexer alone compiles+runs in seconds) or single files with generous timeouts.
(Taught by: timed `kappa check` on incremental merges of the self-host compiler.)

### H-4 (ROOT CAUSE + FIX for H-3): `||`-chains of String `==` are pathologically slow
The super-linear blowup in H-3 was caused by ONE definition: a 26-term boolean expression
`c == "Left" || c == "Right" || ... (26x)` over `String`. With it present the whole parser
took >300s to `kappa check`; replacing that single function with an equivalent `if/elif`
chain dropped the whole-parser check to ~11s. (An `if/elif` chain of 65 String `==`
comparisons — the lexer's `kwCase` — was never slow.) So the trigger is specifically a deep
`||`-nest of `String` equality, not chain length, SCC size, or String `==` per se. A 40-fn
mutually-recursive SCC checks in 0.2s; a polymorphic `P a` is fine.
Workaround for self-host code (and a likely real perf bug in this compiler's elaborator,
worth profiling): never write long `||`/`&&` chains of `String ==`; use `if/elif` instead.
This MITIGATES H-3: whole-compiler runtime testing is practical again (~11s compile).
(Taught by: bisecting `kappa check` time by stubbing individual parser definitions.)
