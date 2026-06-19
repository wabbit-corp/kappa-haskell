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
| N-20 | HIGH | open | `CType` 8-enum lacks exact-width/unsigned/C-spelling scalars (no I8/16/32, U8..U64, Isize/Usize, F32, CChar..CBool) → unsigned/size_t APIs mis-declared | §26.1.1:27270-27288 | widen CType + cAbiType/ctypeKappaTerm/marshal + ctXxx builders |
| N-21 | HIGH | open | content identity is FNV-1a, not sha256 → cross-impl divergence + weak identity | §36.6A:39557 | add sha256 dep; switch contentId/native digests to sha256 |
| N-22 | HIGH | open | `targetTriple` decoded but IGNORED (cross-compile silently builds host); triple/CC/linked-lib absent from identity | §36.21, §27.1.1:27366 | thread `-target` to cc; model platform roles; fold triple/CC/lib into composite |
| N-23 | HIGH | open | `M.Raw` mechanically-derived raw surface unimplemented | §26.1.2 | expose `host.native.X.Raw` |
| N-24 | HIGH | open | RawPtr/OpaqueHandle nullability+ownership dropped (bare non-optional) | §26.1.1:27303-27314, §26.1.4 | default to `Option RawPtr`/wrapped handle unless trusted-summary/shim overrides |
| N-25 | HIGH | open | adapter modes (§26.1.3) + trusted summaries (§26.1.5) unmodeled; adapter mode absent from identity | §26.1.1:26221, §26.1.3, §26.1.5 | add adapterMode field + trusted-summary input; fold into identity |
| N-26 | HIGH | open | `prebuiltNative` expectedIdentity decoded then never verified (fail-OPEN) | §36.28, §36.6 | digest artifact; compare expectedIdentity fail-closed; fold into identity |
| N-27 | MED | open | shim source content not digested into identity (a shim edit is invisible) | §27.1.1:27367 | digest shim .c/.h into composite + lock |
| N-28 | MED | open | `moduleMap` input silently dropped (comment claims a digest that doesn't happen) | §27.1.1:27370 | digest moduleMap or fail-closed if unrealized |
| N-29 | MED | open | no §36.11 path-escape/symlink hardening on native header/shim/prebuilt paths | §36.11, §36.6A | reuse source-tree normalize+symlink guard; fail-closed on escape |
| N-30 | MED | open | lock parser drops malformed lines unless `--locked`; no per-entry schema identity; unescaped field separator | §36.7:39603 | per-entry schema id; escape separators; reject corrupt lock always |
| N-31 | LOW | open | `unsafeConsume` table arity 2 but only 1 explicit arg (implicit erased) → native leaves it an unsaturated function (masked: result always discarded) | — | arity 1 in prim_arity + table + interp arm |
| N-32 | LOW | open | `CtString` marshalling truncates embedded NUL (kstr0/kas_str), no length channel | §26.1.1 | document ABI constraint or thread length |
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
