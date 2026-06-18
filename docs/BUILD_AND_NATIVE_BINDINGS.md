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
  (`kappa.provider.collision`, §3.2.15), `E_NATIVE_BINDING_UNPINNED`
  (`kappa.package.reproducibility`, §3.2.15).

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

The complementary **value-provenance graph** (§35.7/§35.13: a source
range for `buildConfig` and every reachable subvalue) is the next
increment. The reify seam is built to accept it without reshaping
`BuildConfig`: provenance will live in a parallel `ValuePath →
Provenance` side-map keyed off the manifest's span-bearing AST, never in
the semantic value. Until then `E_CONFIG_PROVENANCE_UNAVAILABLE` is
registered with its four §35.11 sub-causes.

## Native bindings — driven by the manifest (increment 2, DONE)

Native bindings are obtained **only** through the package/build/native
mechanism. There is no hardcoded native list and no `--ffi-full`; the
former `Kappa.Backend.Intrinsics` table and `Kappa.Backend.Ffi` are
deleted.

The model (§8.3.5 / §27.1.1 / §34.5.3):

- **The catalog** (`src/Kappa/Backend/NativeCatalog.hs`) is the `zig`
  profile's curated set of `host.native.*` module surfaces — each an
  implementation-documented ABI description (§8.3.5): a list of typed
  members and the runtime FFI primitive (`runtime/kappart_ffi.c`) that
  realizes each (§34.5.3). Increment 2 supplies `host.native.sqlite3` and
  `host.native.posix.net` (the former bare intrinsics, re-keyed by
  module + member). These are runtime-only (§34.5.1): registered as
  abstract globals (no value), so elaboration never demands them.
- **A manifest `nativeBinding` selects** which `host.native.*` modules a
  build provides (`provides = [module "host.native.sqlite3"]`, §36.28)
  and supplies the link/load. `Kappa.Build.Plan.resolveExecutable` (a
  §36.4 build-plan slice) selects the target, resolves its
  `hostBindings` to catalog modules with collision + realizability
  checks, and locates the entry module under the source roots.
- **The program imports** the provided module
  (`import host.native.sqlite3 as sql`) and uses its members
  (`sql.sqliteOpen`). `Kappa.Pipeline.compileProgramWithNative` registers
  the selected catalog modules into the check state so the import
  resolves, and returns a `GName → prim` map. Codegen
  (`Kappa.Backend.C`, `gsHostPrims`) lowers each provided member to its
  runtime primitive — keyed on the full `GName`, never a bare name.
  `Kappa.Backend.Driver` links `kappart_ffi.c` and emits `-l` flags from
  the binding's `link` spec.
- **Source-defining** a `host.native.*` module (or any reserved host
  root) is rejected (`E_HOST_MODULE_SOURCE_DEFINED`, §8.3.5). With no
  manifest provider, importing `host.native.X` is unresolved
  (`E_MODULE_NAME_UNRESOLVED`) — the legacy single-file `kappa build
  FILE` therefore has no native bindings, by design.

Diagnostics (all registered in `Kappa.Explain`): `E_PROVIDER_COLLISION`
(two bindings provide one module), `E_NATIVE_BINDING_UNSUPPORTED`
(provider names a module the catalog lacks, a `modulesUnder` selector, or
a `symbolList` symbol that is not a member of the provided modules),
`E_BUILD_BINDING_NOT_FOUND` (target names an undeclared binding),
`E_BACKEND_HOST_LINK_UNREALIZABLE` (any load mode other than
`systemLoader` — `bundledLoader`/`runtimeLoad`/`providedByHost` — which
the zig profile does not realize, §34.5.3), `E_BUILD_ENTRY_NOT_FOUND`,
`E_HOST_MODULE_SOURCE_DEFINED`.

Two CLI ergonomics notes: under `--emit-c` the generated `.c` is written
next to the entry source (the `-o` path applies to the linked
executable, not the `.c`); and a manifest build resolves the target's
`main` module to a single entry file and compiles it standalone — the
entry's `module` header is not yet checked against the manifest selector,
and sibling program modules are not yet enumerated (full multi-file
source-root resolution is increment 4).

`kappa build --manifest [DIR] [--target NAME] [-o OUT] [--emit-c]` builds
the executable target; `--check` stops at the evaluated configuration
(the §35.13 boundary) and prints a summary. The demo
(`examples/native/http_sqlite/`) builds end-to-end via its
`kappa.build.kp` (sqlite3 + POSIX sockets).

### Tracked temporary residue

- **Static linkage** is emitted as a plain `-l` (linker default search
  order), without `-Wl,-Bstatic`/`-Bdynamic` grouping; a `staticLink`
  request is honored only if a static archive is what the linker finds.
  Proper static grouping is deferred (see `linkFlags` in
  `Kappa.Backend.Driver`). This is the one tracked native-link
  approximation.
- The general §9.4 `expect`→backend-intrinsic hook
  (`csBackendIntrinsics`/`backendIntrinsicSatisfies`) remains in the
  checker but is now **always seeded empty** — the conforming native
  surface is `host.native` imports, not bare-name `expect`s. A bare
  `expect term` therefore has no native provider and is honestly
  unsatisfied. (Inert hook, not a hardcoded list or bootstrap path.)
- `pkgConfig`/`headers` provider *discovery* (running `pkg-config`,
  scanning headers) is not performed: §35.13 forbids the manifest from
  doing it and §36.28 forbids inferring ABI from headers alone, so it is
  build-plan resolution for a later increment. A `symbolList`/`pkgConfig`
  provider selects a curated catalog module; its declared member names
  are the binding's surface.

## Increment sequencing (deferrals are spec-permitted, not defects)

1. **(done)** Build-manifest foundation: schema + config-mode check +
   reify + diagnostics + CLI discovery. Boundary: §35.13 (no resolution).
2. **(done)** Native bindings driven by the manifest (§8.3.5/§34.5.3/
   §36.28): catalog + provider selection + host.native imports + codegen
   + link + diagnostics; `--ffi-full` and the hardcoded table retired; a
   minimal §36.4 build-plan slice (target select + entry resolve).
3. Value-provenance graph + canonical serialization (§35.7, §36.2/§36.2.1).
4. Full build-plan resolution (§36.4): multi-file source-root
   enumeration, module derivation, `kappa.lock`.
5. Dependency resolution (§36.23, resolver profiles §36.23.1) + the
   `kappa.package.reproducibility` pinning diagnostics in full; remove the
   static-link approximation.
6. Remaining target kinds (test/codegen/bridge/benchmark/publish, §36.30+)
   and JVM/.NET/Python ecosystems; deployment/reproducibility status.

Spec-cited deferral grounds: §29.8 explicitly lists the larger type/
builder set as "equivalent to" a portable schema (signatures are
implementation-chosen) and forbids the manifest assigning a resolved
`ReproducibilityStatus` (so no such constructor is exposed); §35.13 puts
resolution outside manifest evaluation; §36.4/§36.23/§36.28 define the
resolution phases the later increments implement.
