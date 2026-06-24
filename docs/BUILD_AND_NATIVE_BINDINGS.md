# Kappa packages, build files, and native bindings

Authoritative notes for the build-manifest / package / native-binding
support in this Haskell implementation. Tracks what is implemented, the
spec grounding (§29.8, §35, §36), the deliberate increment boundaries,
and what remains sequenced (with the exact citation that each deferral
is spec-permitted, not a defect).

This complements `docs/NATIVE_BACKEND_OPTIMIZATION_GUIDE.md` (the native
codegen roadmap). Where build configuration eventually drives codegen or
the runtime ABI, that crossover is recorded here and cross-referenced
there.

## Model (Spec §35.13, §36.3)

A build manifest is the file `kappa.build.kp`. Per §35.13 it is an
ordinary Chapter-35 **config unit**: ordinary Kappa syntax, parsed by the
ordinary parser, but evaluated in the **config-expression** profile
(§35.2.2) under a **loader-supplied schema scope** (§35.3) containing the
config-safe names of `std.config` and `std.build`. It has no module
header, no imports/exports, no separate signatures, no user functions or
macros, no `IO`/`Elab`; it may use helper `let` bindings and must define
exactly one `let buildConfig : BuildConfig = ...`.

Crucially (§35.13): **manifest evaluation produces the `buildConfig`
value + diagnostics and does NOT perform build resolution** — no
dependency resolution, no source-root enumeration, no `pkg-config`, no
header scanning, no lockfile update. Those are build-plan resolution
(§36.4) and are a *separate phase*. Increment 1 stops exactly at this
spec boundary.

### Manifest surface syntax

The §36.3 example is **illustrative** and writes builders with
parenthesized named arguments (`package ( name = …, … )`, `jvm ()`). That
is not the literal Kappa surface: in Kappa, `( name = … )` is a record
literal (§13.2.3), and named application uses **braces** —
`package { name = …, version = … }` (§10.1.1 / §16.1.7). Portable
manifests for this implementation therefore use the brace form, which is
the spec's actual named-application syntax; nullary backends are written
bare (`backend = jvm`, not `jvm ()`). The fixtures in `tests/build/`
demonstrate the portable spelling. Because builders are functions (not
defaulted constructors), every field must be supplied (§16.1.7 forbids
partial application); a missing field is a type error, never a silent
default.

## What is implemented (increment 1)

End-to-end: `kappa build --manifest [PATH|DIR]` (and bare `kappa build`
with no positional path) discovers `kappa.build.kp` (walking up from the
working directory, or an explicit file/dir), config-checks it, evaluates
`buildConfig`, reifies it to a Haskell `BuildConfig`, and reports
diagnostics or a summary of the resolved configuration.

Components:

- **`std.config` + `std.build` schema modules** (`src/Kappa/Prelude.hs`,
  embedded and checked in `preludeState`). They are ordinary config-safe
  Kappa: data types and total transparent builder functions (§35.5). The
  increment-1 `std.build` subset covers the §36.3 vocabulary:
  `package`/`semver`/`sourceRoot`/`axis`/`tag`/`tags`/`module`/
  `modulesUnder`/`registry`/`git`/`pathDependency`/`nativeBinding`/
  `pkgConfig`/`headers`/`symbolList`/`shim`/`prebuiltNative`/`cAbi`/
  `dynamicLink`/`staticLink`/`noLink`/`systemLoader`/`bundledLoader`/
  `runtimeLoad`/`providedByHost`/`native`/`jvm`/`dotnet`/`executable`/
  `library`, plus their result types.

- **Config-mode checker** (`src/Kappa/Config.hs`). Per §35.1 the config
  restrictions are *additional restrictions on ordinary Kappa, not a
  separate parser*: we reuse `parseModule` and `checkModule`, and layer
  (a) a structural restriction pass (§35.1/§35.2.2) rejecting module
  headers, imports/exports, standalone signatures, `data`/traits/
  instances/`expect`, function definitions and pattern bindings; (b) an
  expression-admissibility walk (generic, via `queryExprs`) rejecting
  lambdas (no first-class function values, §35.2.2), `do`/IO, effect
  handlers/`try`, comprehensions, set/map literals, quotes/splices, and
  sealing; (c) the §35.3 schema scope, built from the `std.config` /
  `std.build` exports plus a fixed config-admissible prelude allowlist
  (the portable-minimum types and their data constructors — *not*
  ordinary prelude functions), installed without an ordinary import.

- **Reification** (`src/Kappa/Build/Reify.hs` → `src/Kappa/Build/Types.hs`).
  Builders are total transparent definitions, so evaluating `buildConfig`
  to normal form (runtime `EvalCtx`, full unfolding) reduces them to
  saturated data constructors, which the decoder walks into the Haskell
  `BuildConfig`. Reification is pure over the value and performs no
  discovery (§35.13). A stuck value or partial application surfaces as a
  §35.11 config diagnostic, not a crash.

- **Diagnostics** (`src/Kappa/Explain.hs`). All eleven §35.11 config
  classes are registered (`E_CONFIG_PARSE`, `E_CONFIG_RESTRICTED_FORM`,
  `E_CONFIG_IMPORT_NOT_SAFE`, `E_CONFIG_TYPE`, `E_CONFIG_UNRESOLVED_NAME`,
  `E_CONFIG_CALL_NOT_SAFE`, `E_CONFIG_PARTIAL_APPLICATION`,
  `E_CONFIG_EVAL`, `E_CONFIG_PROVENANCE_UNAVAILABLE`,
  `E_CONFIG_INTERPOLATION`, `E_CONFIG_EXPECTED_VALUE`) under the
  implementation family prefix `kappa-hs.config.*`. Build/provider codes
  are registered too: `E_BUILD_MANIFEST_NOT_FOUND`,
  `E_BUILD_TARGET_NOT_FOUND`, `E_PROVIDER_COLLISION`
  (`kappa.provider.collision`, §3.2.15), and
  `E_BACKEND_PROFILE_UNREALIZED` (`kappa-hs.backend.profile`, a target that
  selects a jvm/dotnet backend this implementation does not realize).
  `E_NATIVE_BINDING_UNPINNED` (`kappa.package.reproducibility`, §3.2.15) IS
  emitted: a package-mode build pins each binding's host-source identity (a
  `host-binding` lock entry over pkg-config version/.pc digest + resolved
  cflags/libs, located header digests, verified decls, shim-source digests, the
  symbol surface, target triple, classification, capabilities, and cstring
  declarations); a later `--locked` build VERIFIES it and any drift (e.g. an
  edited shim) is rejected fail-closed with `E_NATIVE_BINDING_UNPINNED` (covered
  by the native suite "host-source identity is pinned … drift is fail-closed").
  Newer native fail-closed codes: `E_NATIVE_BINDING_PATH_ESCAPE`
  (`kappa-hs.build.native-path`, §36.11 root-escaping/symlink input path),
  `E_NATIVE_BINDING_ABI_UNVERIFIED` (`kappa-hs.build.native-abi`, an explicit
  symbolList pointer/string/handle symbol with no shim/verify ABI proof), and
  `E_BACKEND_CAPABILITY_UNREALIZED` (`kappa-hs.backend.capability`).

- **Tests** (`tests/build/`, runner `run-build-tests.sh`): valid
  manifests (full §36.3 shape, minimal, symbol-list native binding),
  invalid manifests asserting the specific §35.11 code, a
  reproducibility pair, and the not-found path.

## Semantic vs provenance identity (§36.2.1)

`BuildConfig` (`Kappa.Build.Types`) is *pure semantic data*: it carries
no source spans or provenance, so structural equality (`deriving Eq`) is
the **semantic build identity** of §36.2.1 by construction. Two manifests
that compute the same configuration through different helper bindings /
`if`s reify to equal `BuildConfig` values — verified by
`tests/build/reproducibility/`. This guarantees a provenance-only source
edit can never change artifact/cache identity (the §36.2.1 requirement),
because provenance is simply not part of the value.

The complementary **value-provenance graph** (§35.7/§35.13) is produced
separately (`Kappa.Build.Provenance`), so it never affects the semantic
value/identity (§35.7: provenance is metadata). It is computed from the
manifest's span-bearing surface AST — §35.7's model is expression-oriented
(the origin of the binding name, the origin of the computing expression,
and an edge from a reference to the referenced value's provenance), which
the surface tree expresses directly. A `SourceProvenance` records a span
for a literal or schema name; `CompositeProvenance`/`SequenceProvenance`
carry per-field/per-element provenance for named applications, records,
and lists; `DerivedProvenance` records an operation (a call, a reference
edge through a `let`, or a conditional) together with its input
provenances; `UnknownProvenance` is used where the origin is not
recoverable. Per §35.7 it never fabricates precise provenance — a value
computed by `if`/`match` is recorded as *derived from* that operation,
not from a guessed branch. `kappa build --manifest --provenance` prints
the `buildConfig` provenance tree (the tool surface; `--provenance`
performs no build). (Per-slice string-interpolation provenance, §35.8, is
N/A while manifests use plain string literals; `E_CONFIG_PROVENANCE_UNAVAILABLE`
remains registered with its four §35.11 sub-causes.)

## Target kinds (§29.8, §36.30+)

The schema supports four target kinds, each with a build-pipeline action:

- **`executable`** — native build (lower `main`'s closure to C + link, §27.7).
- **`library`** — its modules are compiled into a dependent that path/git/
  registry/url-depends on the package (it is consumed, not built directly;
  named directly in an aggregate it is skipped with a note).
- **`test`** (§36.31) — `kappa build --manifest --target <name>` runs the
  target's modules through the Appendix-T test harness (each test file
  standalone, like `kappa test FILE`) and reports pass/fail / exit status.
- **`aggregate`** — groups member targets by name; building it runs each
  member's action (build/run), succeeding iff all do. Cyclic membership is
  rejected (`E_BUILD_TARGET_CYCLE`); an unknown member is
  `E_BUILD_TARGET_NOT_FOUND`.
- **`aliasTarget`** — an alias/rename of another target; building it builds
  the aliased target (cycle-detected, same diagnostics as aggregate).
- **`benchmark`** — a runnable benchmark program (executable shape, no host
  bindings); the build runs its `main` under the interpreter (toolchain-
  free) and reports completion / non-zero on a runtime failure. (Pure
  compute: a benchmark importing a `host.native.*` module fails honestly,
  since the interpreter supplies no foreign operations.)

`--target NAME` dispatches on the named target's kind (test → run suite;
executable → native build; benchmark → run under the interpreter;
aggregate → run each member; alias → run the aliased target); no `--target`
builds the default executable. Other §29.8 kinds (`codegen`, `bridge`,
`publish`, …) are not in the schema subset yet (§29.8's "equivalent to"
lets the implementation choose the subset; they are deferred-not-defective;
`codegen`/`bridge` also need generator/bridge backend infrastructure not
present here).

## Native bindings — driven by the manifest (increment 2, DONE)

Native bindings are obtained **only** through the package/build/native
mechanism. There is no hardcoded native list and no `--ffi-full`; the
former `Kappa.Backend.Intrinsics` table and `Kappa.Backend.Ffi` are
deleted.

The model (§8.3.5 / §27.1.1 / §34.5.3) — **there is no in-compiler catalog**;
the manifest binding is the sole authority for the surface:

- **A manifest `nativeBinding` fully describes** each `host.native.*` module
  it provides: `provides = [module "host.native.sqlite3"]` (§36.28) names the
  module, and `surface = symbolList [symbolDecl member cSymbol params result, …]`
  declares every exported member, the C symbol it calls, and its ABI
  signature (`CType` params/result — §26.1.1/§26.1.4). `inputs` name the
  realization (`shim`/`headers`/`includeDir`/`define`/`pkgConfig`/
  `prebuiltNative`); `link`/`load` drive the toolchain.
- **The plan resolves** (`Kappa.Build.Plan.resolveBinding`, a §36.4 slice)
  each binding's `provides × symbolList` into `ResolvedNativeSymbol` records
  (module ↦ member, C symbol, ABI signature), with collision + realizability
  + host-root checks. These are runtime-only (§34.5.1): registered as
  abstract globals (no value), so elaboration never demands them.
- **The program imports** the provided module
  (`import host.native.sqlite3 as sql`) and uses its members
  (`sql.sqliteOpen`). `Kappa.Pipeline.applyNativeModules` registers each
  resolved member as an abstract global whose Kappa type is DERIVED from its
  ABI signature (`Kappa.Backend.NativeFfi.nativeMemberType`), and returns a
  `GName → ResolvedNativeSymbol` map. Codegen (`Kappa.Backend.C`,
  `gsHostSyms`) lowers each member to a **direct typed C call site**: an
  `extern` prototype + a marshalling wrapper (`kw_*`) + a `knative` action.
  `Kappa.Backend.Driver` compiles the `shim` translation units, runs
  `pkg-config`, and threads `-I`/`-D`/`-l` from `inputs`/`link`. No
  `kappart_ffi.c`, no runtime primitive table, no string dispatch.
- **Source-defining** a `host.native.*` module (or any reserved host
  root) is rejected (`E_HOST_MODULE_SOURCE_DEFINED`, §8.3.5). With no
  manifest provider, importing `host.native.X` is unresolved
  (`E_MODULE_NAME_UNRESOLVED`) — the legacy single-file `kappa build
  FILE` therefore has no native bindings, by design.

Diagnostics (all registered in `Kappa.Explain`): `E_PROVIDER_COLLISION`
(two bindings provide one module), `E_NATIVE_BINDING_UNSUPPORTED`
(provider names a module not under the `host.native` root, or a binding
with an empty symbol surface),
`E_BUILD_BINDING_NOT_FOUND` (target names an undeclared binding),
`E_BACKEND_HOST_LINK_UNREALIZABLE` (any load mode other than
`systemLoader` — `bundledLoader`/`runtimeLoad`/`providedByHost` — which
the zig profile does not realize, §34.5.3), `E_BUILD_ENTRY_NOT_FOUND`,
`E_HOST_MODULE_SOURCE_DEFINED`.

A manifest build enumerates **every** `.kp` module under the package
source roots (`Kappa.Build.Plan`), keeps those whose §8.1 path-derived
module name matches the target's `modules` selector (or is its `main`),
and compiles them as one §8.1 **package-mode** unit — so the entry module
may import sibling package modules, and a `module` header that disagrees
with its path is rejected (`E_MODULE_PATH_MISMATCH`). Modules outside the
selector are not compiled into the target.

One CLI ergonomics note: under `--emit-c` the generated `.c` is written
next to the entry source (the `-o` path applies to the linked
executable, not the `.c`).

`kappa build --manifest [DIR] [--target NAME] [-o OUT] [--emit-c]` builds
the executable target; `--check` stops at the evaluated configuration
(the §35.13 boundary) and prints a summary. The demo
(`examples/native/http_sqlite/`) builds end-to-end via its
`kappa.build.kp` (sqlite3 + POSIX sockets).

### Generated raw surfaces + foreign-call classification (§26.1.2, §26.1.4, §27.1.1)

A binding's surface need not be hand-authored. Two header-derived forms
(`Kappa.Backend.HeaderGen`, resolved in `Kappa.Build.Plan.genThen`) generate
the `host.native.*.Raw` surface mechanically — there is no hand-written
`symbolDecl` on these paths:

- `surface = generateFromHeader "h" ["f", "g", …]` — preprocess `h` (`cc -E -P`
  with the binding's pkg-config cflags, `-D` defines, resolved `-I` path), parse
  the named functions, and map each conservatively. Use for a small curated
  surface (e.g. a shim's public API).
- `surface = generateAllFromHeader "h" "prefix"` — the **general** path: parse
  EVERY function in `h` whose C name begins with `prefix`. For the libuv example
  this derives the broad `host.native.libuv.Raw` (≈210 `uv_*` functions from
  `<uv.h>`), not a curated handful.

Conservative mapping (§26.1.4): a non-`char` pointer ⇒ `Option RawPtr`; a `char`
pointer ⇒ the C-string convention; integer/float scalars ⇒ their exact-width
`std.ffi` nominal; an array parameter decays to a pointer; `void` result ⇒
`Unit`. A declaration the conservative C-ABI cannot represent soundly — a
callback/function-pointer, a by-value struct/union/enum, a variadic, or
`long long`/`long double` — is **rejected, never guessed** (§26.1.2): the
explicit-list form fails closed (`E_BUILD_NATIVE_HEADER_GEN`); the broad form
skips it and reports the skipped count on stderr (no silent omission). The
generated symbol set is pinned in `kappa.lock`, so a header change repins and
regenerates (§27.1.1 host-source identity).

**Target ABI (§26.1.3).** The pinned target ABI description is the target triple
(in `kappa.lock`) plus the LP64 data model the integer-width mapping assumes.
For a cross-capable driver (`zig cc`) the header is preprocessed AND ABI-verified
*for the declared triple* (`-target` is threaded into the `cc -E` and verify
steps, matching the link step), so a cross-build derives the surface from the
target's headers — not the host's. A host `cc`/`gcc`/`clang` cannot retarget, so
it preprocesses for the host (the realized configurations keep the triple equal
to the host). A target triple whose data model is not LP64 (LLP64 Windows, ILP32
32-bit) is **rejected** (`E_BACKEND_CAPABILITY_UNREALIZED`) rather than have a
layout-sensitive surface inferred for an unmodelled ABI (§26.1.3:26245).

Shims are the spec-sanctioned escape hatch for exactly the rejected cases
(§26.1.2: callbacks/structs/variadics "MUST be rejected or require an explicit
shim … rather than guessed"; §27.1.1: "MAY require a user-provided shim …
rather than guessing"). libuv's event loop is callback-driven, so the broad raw
surface cannot expose `uv_listen`/`uv_read_start`/`uv_run`/`uv_close` (they take
callbacks); `examples/native/http_uv/native_uv_shim.c` is the minimal blocking
adapter over exactly those, and its surface is itself generated from
`native_uv_shim.h` — no hand-authored `symbolDecl`.

**Foreign-call classification (§26.1.4 MUST).** Every binding carries a
foreign-call classification — `classify nonblocking` (the default for a direct
native call), `classify blocking`, or `classify blockingCancellable`. It is
recorded in the binding's native provenance (`*.native.prov`,
`foreign-call-classification …`) and folded into the host-source identity
(`kappa.lock`), so it participates in reproducibility (§26.1.3). The libuv
adapter declares `blocking` (its `accept`/`read` wait on socket I/O); the raw
`libuv.Raw` value functions are `nonblocking`.

**Interface-artifact records (§26.1.2).** §26.1.2:26141 conditions the
record-keeping MUST on *generated overload spellings* ("For every generated
overload spelling, the module interface artifact MUST record …"). A C/native
surface has no overloading — each generated member's name is its C symbol
verbatim, the overload rule is trivially *unsuffixed-unique*, and the adapter
mode is constant (`native.direct`) — so no overload spellings are generated and
that per-overload MUST is vacuous. The unconditional §26.1.2:26193 diagnostic
MUST (report both the generated Kappa spelling and the original host identity)
holds because for a native binding the generated spelling *is* the host symbol
(member == C symbol). The substantive record fields the spec enumerates
(generated spelling, host spelling/identity, host signature, adapter mode) are
nonetheless recorded in the host-source identity pinned in `kappa.lock` (the
per-symbol `symbol <member> <cSymbol> <params>-><result>` lines + the
`adapter native.direct` line in the native provenance). A separate managed-host
overload-disambiguation/interface-artifact subsystem is only needed for a future
`host.jvm`/`host.dotnet` profile, which is not implemented.

**Capability profile + routing (§26.1.4 / §27.6).** §27.6 requires every backend
profile to declare a runtime capability set; the native profile's is declared in
`Kappa.Backend.Capabilities` (`nativeRuntimeCapabilities = rt-core, rt-blocking,
rt-atomics`) and recorded in each binding's native provenance
(`backend-capabilities …`). The classification→capability rule is enforced
fail-closed during plan resolution (`Kappa.Build.Plan.checkClassificationCapability`):
a binding whose classification needs a capability the profile does not advertise
is rejected with `E_BACKEND_CAPABILITY_UNREALIZED` (§26.1.4:26311, §27.6:28186) —
e.g. a `blocking-cancellable` binding (which needs a safe foreign-call
cancellation capability the native runtime lacks). A `blocking` binding is
accepted because `rt-blocking` *is* advertised; it is realized by **direct
execution** on the native runtime's single agent — the agent is itself the
blocking lane, so the §26.1.4:26304 "MUST NOT … starve unrelated runnable
fibers" rule holds vacuously (there is no concurrent fiber execution). A true
offloading blocking-work lane (needed only if the native runtime later gains a
concurrent scheduler) is a low-priority tracked item
(`docs/notes/KAPPA_SELF_HOSTING_PORT_NOTES.md`, H-7), not claimed as implemented.

### Lockfile + reproducibility (§36.4, §36.23.2, §3.2.15)

`Kappa.Build.Lock` records the resolved **path-dependency closure** in
`kappa.lock` (in the project directory): one entry per dependency package
— its path relative to the project (a portable key using `..`) and a
**content identity** (an FNV-1a digest over the package's manifest + all
its `.kp` source files, path-sorted, so it is location- and
enumeration-independent — an implementation-defined identity per §36.23.2,
a change-detection digest, not a cryptographic one).

`kappa build --manifest` creates/updates `kappa.lock` by default when the
closure is non-empty. `kappa build --manifest --locked` makes no changes
and fails with `E_DEPENDENCY_LOCK_MISMATCH` (family
`kappa.package.reproducibility`, §3.2.15) if the lock is missing or any
resolved content identity differs — i.e. the build is not reproducible
against the recorded lock. `--check` performs no resolution and touches no
lock.

### Dependency resolution (§36.23, increment 4)

A target's `dependencies` names are resolved against the manifest's
declared dependencies (`Kappa.Build.Plan.resolveDeps`):

- A **`pathDependency`** is resolved against the local filesystem and
  followed **transitively**: the dependency package's manifest (relative
  to the dependent's directory) is loaded + evaluated, its **library**
  modules (those matching its `library` targets' `modules` selectors, or
  all its package modules except executables' mains when it declares no
  library) are enumerated and compiled into the unit, and its own library
  dependencies are resolved the same way. The closure is deduplicated and
  cycle-detected by canonical package directory, so a diamond or a
  dependency cycle resolves once and terminates. Missing manifest →
  `E_DEPENDENCY_PATH_NOT_FOUND`; a dependent listing an undeclared
  dependency name → `E_DEPENDENCY_NOT_FOUND`; a module provided by more
  than one package in the closure → `E_DEPENDENCY_MODULE_COLLISION`.
- A **`git`** dependency is resolved via the `git` CLI: the URL is cloned
  into a project-local content-addressed cache (`<root>/.kappa/git/…`),
  the requested revision is checked out (detached), and its resolved
  commit SHA is recorded in `kappa.lock` as the immutable identity
  (§36.23). Its checkout is then treated as a transitive path dependency.
  git-unavailable / clone / checkout / rev-parse failures are honest
  `E_DEPENDENCY_GIT_FAILED`. Pin to a commit SHA for full reproducibility;
  a branch/tag is resolved best-effort and the lock pins whichever SHA
  resolved (so `--locked` detects a drifted branch).
- A **`registry`** dependency is resolved against a **vendored/offline
  registry** (§36.23.1 implementation-defined resolver profile): the
  registry root comes from `$KAPPA_REGISTRY`, laid out as
  `<root>/<name>/<version>/kappa.build.kp`. The resolver enumerates the
  version directories (non-version entries are skipped), keeps those whose
  version satisfies the constraint (`*`/empty = any; `^X[.Y[.Z]]` caret
  with npm semantics; a bare `X[.Y[.Z]]` = leading-component prefix;
  prereleases are excluded from ranges but may be pinned by an exact
  dirname), picks the highest, and resolves it as a transitive path
  dependency. The lock pins `version+content-digest` so `--locked` detects
  both a version change and content drift of a vendored package.
  Diagnostics: `$KAPPA_REGISTRY` unset → `E_DEPENDENCY_UNRESOLVED`; package
  absent → `E_DEPENDENCY_REGISTRY_NOT_FOUND`; no satisfying version →
  `E_DEPENDENCY_VERSION_UNSATISFIED`.
- A **`url`** dependency (`urlDependency { name, url }`) fetches an
  archive via `curl` (which handles `file://` and `http(s)://`) into a
  project-local content-addressed cache, unpacks it via `tar`
  (autodetecting compression), resolves the package root (the unpacked
  tree, or its sole manifest-bearing top-level directory) as a transitive
  path dependency, and pins its content digest in the lock. Honest
  `E_DEPENDENCY_URL_FAILED` when curl/tar are unavailable or the
  fetch/unpack fails or yields no manifest. (Remote `http(s)://` works
  when the network allows; `file://` is offline.)
- A **networked package registry** (vs the local vendored registry above)
  and `artifact`/target-artifact dependency builders are not provided.

### Tracked temporary residue

- **No cross-package module namespacing.** Module identity is the dotted
  name; packages are expected to choose distinct module prefixes by
  convention (§36.3 uses `acme.image.*`). A collision anywhere in the
  dependency closure is *rejected* (`E_DEPENDENCY_MODULE_COLLISION`), not
  silently merged — there is no spec mechanism that namespaces a module by
  its package, so rejection is the correct enforcement.
- **No networked registry** — registry dependencies resolve against a
  local vendored registry (`$KAPPA_REGISTRY`); a remote registry server/
  protocol, and `artifact`/target-artifact dependency builders, are not
  provided. Path, git, vendored-registry, and url (archive) dependencies
  are all resolved; the lockfile records each.
- **Root-as-cyclic-dependency asymmetry**: when a path dependency cycles
  back to the package being built, the root contributes the modules of the
  *executable* target being built (its `modules` selector), not its
  *library* modules. A cyclic dependency importing a root module outside
  that selector fails honestly with `E_MODULE_NAME_UNRESOLVED` (an
  unusual topology; the failure is honest, not silent-wrong).
- The general §9.4 `expect`→backend-intrinsic hook
  (`csBackendIntrinsics`/`backendIntrinsicSatisfies`) remains in the
  checker but is now **always seeded empty** — the conforming native
  surface is `host.native` imports, not bare-name `expect`s. A bare
  `expect term` therefore has no native provider and is honestly
  unsatisfied. (Inert hook, not a hardcoded list or bootstrap path.)
- `pkgConfig`/`headers`/`includeDir`/`define`/`shim` inputs ARE realized in
  the build phase (the driver runs `pkg-config`, adds `-I`/`-D`, and
  compiles+links shim translation units) — never at config-eval (§35.13
  forbids discovery there). The binding's surface comes from its own
  `symbolList` (§36.28 forbids inferring ABI from headers alone), not from
  any catalog. What is NOT yet done: digesting those inputs into a lockfile
  for reproducible PINNING (bug queue N-6).
- **Only the native (zig) backend profile is realized.** A target whose
  `backend` is `jvm`/`dotnet` is *rejected* at resolution with
  `E_BACKEND_PROFILE_UNREALIZED` (§34.5.3/§36.4) rather than silently built
  native. `--check`/`--provenance` still describe such a target (they
  perform no resolution).
- A native binding's `abi` field is reified but currently only `cAbi` is
  modeled; structured adapter-mode/calling-convention selection (§26.1.3,
  §36.21) and the `M.Raw` raw surface (§26.1.2) are later increments (bug
  queue N-8/N-10/N-12).
- **External config inputs (§35.4) and the §35.13 standard request keys**
  (`requestedTarget`/`requestedBackend`/…) are not implemented: `std.config`
  declares only `configInput name`, with no loader-supplied `input`
  resolution. `--target` selects post-hoc among the produced targets (which
  §35.13 permits for selection-only parameters); no request parameter is
  visible to the config evaluator.

## Increment sequencing (deferrals are spec-permitted, not defects)

1. **(done)** Build-manifest foundation: schema + config-mode check +
   reify + diagnostics + CLI discovery. Boundary: §35.13 (no resolution).
2. **(done)** Native bindings driven by the manifest (§8.3.5/§34.5.3/
   §36.28): manifest `symbolList` surface (no catalog) + provider selection
   + host.native imports + DIRECT typed-call codegen (extern proto + wrapper
   + `knative`, no runtime FFI table) + shim/pkg-config/`-I`/`-l` realization
   + diagnostics; a minimal §36.4 build-plan slice (target select + entry
   resolve). `--ffi-full`, the hardcoded catalog, and `kappart_ffi.c` retired.
3. **(done)** Multi-file build-plan resolution (§36.4): enumerate the
   package's modules under its source roots, filter by the target's
   `modules` selector, compile as one package-mode unit (header/path
   agreement). `kappa.lock` and incremental caching are later.
4. **(done)** Dependency resolution (§36.23): path dependencies resolved
   + their library modules compiled into the unit; registry/git honestly
   unresolved (§36.23.1).
5. **(done)** Transitive path-dependency closure (cycle-detected,
   deduplicated) + proper `staticLink` `-Wl,-Bstatic` grouping.
6. **(done)** `kappa.lock` + path-dep content identity (§36.23.2) +
   `--locked` reproducibility check (`E_DEPENDENCY_LOCK_MISMATCH`, §3.2.15).
7. **(done)** Git dependency resolution via the `git` CLI (clone/checkout
   to a project-local cache, resolved SHA pinned in `kappa.lock`,
   `E_DEPENDENCY_GIT_FAILED` on failure). Registry/url still unresolved.
8. **(done)** Vendored/offline registry resolver (`$KAPPA_REGISTRY`) with
   semver constraints + version+content lock pinning (§36.23.1).
9. **(done)** `url` (archive) dependency resolution via curl+tar, content
   pinned in the lock (`E_DEPENDENCY_URL_FAILED` on failure).
10. A networked registry server/protocol + `artifact`/target-artifact
    dependency builders (the remaining unresolvable sources).
11. **(done)** Value-provenance graph (§35.7) over the surface AST,
    surfaced via `kappa build --manifest --provenance`.
12. Canonical schema serialization + semantic-identity computation (§36.2)
    + per-slice string-interpolation provenance (§35.8).
13. **(partly done)** Target kinds: `executable`/`library`/`test`/
    `aggregate`/`aliasTarget`/`benchmark` are built/run/grouped/aliased;
    `codegen`/`bridge`/`publish` (generator/bridge/publish backends) and
    JVM/.NET/Python ecosystems + deployment/reproducibility status remain.

Spec-cited deferral grounds: §29.8 explicitly lists the larger type/
builder set as "equivalent to" a portable schema (signatures are
implementation-chosen) and forbids the manifest assigning a resolved
`ReproducibilityStatus` (so no such constructor is exposed); §35.13 puts
resolution outside manifest evaluation; §36.4/§36.23/§36.28 define the
resolution phases the later increments implement.
