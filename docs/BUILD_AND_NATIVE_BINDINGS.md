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

## Native bindings — status and the bootstrap to replace

Increment 1 lets a manifest *describe* native bindings (§36.28
providers: `pkgConfig`/`headers`/`symbolList`/`shim`/`prebuiltNative`;
link kinds `dynamicLink`/`staticLink`/`noLink`; load kinds
`systemLoader`/`bundledLoader`/`runtimeLoad`/`providedByHost`) and reifies
them. It does **not** yet route them to codegen/link.

The native-codegen path is still served by the **temporary hardcoded
bootstrap**: `src/Kappa/Backend/Intrinsics.hs` (a fixed name→type/prim
map for tcp/sqlite), seeded into the checker by `kappa build --ffi-full`
(`app/Main.hs` `cmdBuildNative`, `Kappa.Backend.Driver`). This bootstrap
is **explicitly interim** and is the thing increment 2 replaces.

Increment 2 (native bindings driven by the manifest), done the
spec-faithful way — *not* the bare-name interim that an early plan
considered and that adversarial review correctly rejected as
**non-conforming** against §8.3.5/§9.4/§27.1.1/§36.28:

- A native binding `provides` modules under the reserved root
  `host.native.*` (§8.3.5). Satisfaction of a program's `host.native.*`
  import / §9.4 `expect` must key on the **full `GName` under that host
  root**, derived from a manifest provider — never on a bare global name
  independent of any binding module. (§34.5.3 does permit a
  backend-intrinsic realization of `host.native.*` exports, so a
  provider-keyed catalog is allowed; only the bare-name keying is not.)
- The intrinsic surface becomes **derived per build from the manifest's
  selected providers**. The current `Intrinsics` map is demoted to a
  provider-keyed bootstrap catalog that activates only when a manifest
  `nativeBinding` selects it; with no `nativeBinding`, zero intrinsics
  are available (today's `FfiStub`). `--ffi-full` is then retired.
- `symbolList`/`shim` providers (explicit symbol/ABI surfaces) are the
  increment-2 entry path: §36.28 forbids inferring ownership/nullability
  from headers alone, and §35.13 forbids the manifest from scanning
  headers, so `pkgConfig`/`headers` discovery is build-plan resolution
  (§36.4) and lands with that phase.

## Increment sequencing (deferrals are spec-permitted, not defects)

1. **(done)** Build-manifest foundation: schema + config-mode check +
   reify + diagnostics + CLI discovery. Boundary: §35.13 (no resolution).
2. Value-provenance graph + canonical serialization (§35.7, §36.2/§36.2.1).
3. Build-plan resolution (§36.4): source-root enumeration, module
   derivation, provider-collision (`E_PROVIDER_COLLISION`), `kappa.lock`.
4. Dependency resolution (§36.23, resolver profiles §36.23.1) + the
   `kappa.package.reproducibility` pinning diagnostics in full.
5. Native bindings driven by the manifest (§36.28), replacing the
   `--ffi-full` bootstrap; link/load → `Kappa.Backend.Driver`.
6. Remaining target kinds (test/codegen/bridge/benchmark/publish, §36.30+)
   and JVM/.NET/Python ecosystems; deployment/reproducibility status.

Spec-cited deferral grounds: §29.8 explicitly lists the larger type/
builder set as "equivalent to" a portable schema (signatures are
implementation-chosen) and forbids the manifest assigning a resolved
`ReproducibilityStatus` (so no such constructor is exposed); §35.13 puts
resolution outside manifest evaluation; §36.4/§36.23/§36.28 define the
resolution phases the later increments implement.
