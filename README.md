# kappa-haskell

A Haskell implementation of the **Kappa** programming language — a small,
statically typed, **dependently typed** language with first-class effects,
quantitative (linear/affine) usage tracking, totality checking, and a
diagnostics-as-contract design.

This repository contains the full front end (lexer, parser, resolver,
elaborator/type checker, totality checker), a tree-walking interpreter, the
implicit prelude and standard modules, a native (C) backend, a package/build
manifest system, and an Appendix-T conformance test harness — all exposed
through a single `kappa` CLI.

It targets the **portable `kappa-v1` profile** of the language as specified in
[`docs/Spec.md`](docs/Spec.md). See [`SPEC_COMPLIANCE.md`](SPEC_COMPLIANCE.md)
for exactly what is and isn't implemented.

> **Status:** the in-tree conformance suite passes **349/349** (0 fail, 0
> unsupported, 0 harness error), verified 2026-06-23. The language spec is a
> draft and the implementation is research-grade.

---

## Table of contents

- [What is Kappa?](#what-is-kappa)
- [A taste of the language](#a-taste-of-the-language)
- [Building](#building)
- [The `kappa` CLI](#the-kappa-cli)
- [How a program is compiled](#how-a-program-is-compiled)
- [Native backend](#native-backend)
- [Packages and build manifests](#packages-and-build-manifests)
- [Testing and conformance](#testing-and-conformance)
- [Repository layout](#repository-layout)
- [Documentation map](#documentation-map)
- [The Delve example](#the-delve-example)
- [License](#license)

---

## What is Kappa?

Kappa is a dependently typed language whose design principles read like a
zen-of-Python for proof-carrying systems code (from [`docs/Spec.md`](docs/Spec.md) §1):

- **Explicit is better than implicit**, simple better than complex, readability
  counts, and *one obvious way to do it*.
- **Totality, purity, and parametricity** are the default stance — encouraged,
  not mandatory.
- **Non-strictness is explicit**: laziness is modeled by suspension *types* and
  suspension *terms*, not a separate family of arrow types.
- **Named semantic objects are first-class** — types, type constructors, traits,
  modules, effect labels, and projections can be passed, stored, sealed, opened,
  and projected like any other value.
- **Diagnostics are part of the language contract.** A compile error is a
  source-level explanation of which rule could not be satisfied, where the
  obligation came from, and (when evident) how to repair it. Every diagnostic
  has a stable code and exists in both a human rendering and a machine-readable
  (JSON) rendering of the *same* structured record — tools never parse prose.
- **Boundary honesty / progressive precision.** Crossings into dynamic values,
  foreign runtimes, and native ABIs are explicit. Erased compile-time
  information is never silently assumed to exist at runtime; runtime evidence is
  always carried by explicit values.

The type system combines:

- **Dependent types** — Π/Σ types, a universe hierarchy (`Type`, `Type1`, …),
  existentials via sealed packages (`exists`/`seal`/`open`), and type-level
  computation.
- **Quantitative type theory (QTT)** — every binder carries a usage quantity
  (`0` erased, `1` linear, `ω` unrestricted), so the checker enforces linear and
  affine resource discipline.
- **Effects** — effectful computations are typed (e.g. `UIO Unit` for a program
  that performs unrestricted I/O).
- **Totality / termination checking** — recursive definitions are checked for
  termination so that "total" really means total.
- **Traits and instances**, records with row-style fields and punning, closed
  and open unions, ranges, pattern matching with flow refinement, and named
  holes (`?h`).

## A taste of the language

A `.kp` source file is a module. Here is a complete program — note the explicit
type signature preceding each `let`, structural records, record update with
`.{ … }`, and the effectful `UIO Unit` main in `do` notation:

```kappa
module main

-- structural record types and values
person : (name : String, age : Integer)
let person = (name = "ada", age = 36)

-- functional record update
older : (name : String, age : Integer)
let older = person.{ age = 37 }

main : UIO Unit
let main = do
    printlnString person.name
    printlnString (showInt person.age)
    printlnString (showInt older.age)
```

Running it prints:

```
ada
36
37
```

Dependent and quantitative features look like this — universes are explicit, and
`exists` is sugar for the sealed-package machinery:

```kappa
module main

-- an existential package: a hidden witness type plus a payload
anonPkg : exists (a : Type). a
let anonPkg = seal 5 as exists (a : Type). a

-- explicit-witness introduction
explicitPkg : exists (a : Type). a
let explicitPkg = seal exists (a = Int). 7 as exists (a : Type). a
```

Browse [`tests/conformance/`](tests/conformance) for hundreds of small,
self-contained programs that double as executable documentation of every
language feature.

## Building

Requirements:

- **GHC 9.14.1** and **Cabal 3.10+** (CI pins these; the code targets
  `base >= 4.17`, so recent GHCs work).
- For the native backend only: a C compiler (`cc`/`clang`/`gcc`), `pkg-config`,
  and the Boehm GC + GMP development headers (`libgc-dev`, `libgmp-dev` on
  Debian/Ubuntu).

Build and test:

```sh
cabal build                 # builds the library + the `kappa` executable (zero warnings under -Wall)
cabal test                  # runs the conformance tree + the diagnostic-registry cross-check
cabal run -v0 kappa -- ...  # invoke the CLI (see below)
```

The project is plain Cabal — no Stack or Nix is required. The `kappa`
executable and the in-process test-suite both run under the threaded RTS pinned
to a single capability (`-N1`), which realizes the language's §18.1 single
runtime agent while still giving reliable cross-fiber wakeups and timers.

## The `kappa` CLI

The CLI ([`app/Main.hs`](app/Main.hs)) has the following subcommands:

| Command | What it does |
| --- | --- |
| `kappa check PATH` | Type-check a single `.kp` file; emit diagnostics; exit non-zero on error. |
| `kappa run PATH` | Check, then run the module's `main` under the interpreter. |
| `kappa test PATH` | Run the Appendix-T harness over a file or directory tree. |
| `kappa test --suite DIR` | Treat `DIR` as exactly one §T.2 suite. |
| `kappa explain CODE` | Print the registry explanation for a diagnostic code or family. |
| `kappa audit PATH` | Emit the unsafe/debug audit ledger (§4.7) as JSON. |
| `kappa build [FILE]` | Native build — single-file, or manifest/package mode (see below). |

Flags shared by `check`/`run`:

- `--json` — emit the whole diagnostic batch as a single JSON array on stdout
  (one object per diagnostic), so tools never parse interleaved prose (§3.1.1).
- `--no-implicit-prelude` — compile without the implicit prelude insertion.

Examples:

```sh
cabal run -v0 kappa -- check tests/conformance/records/basics.kp
cabal run -v0 kappa -- run   tests/conformance/records/basics.kp
cabal run -v0 kappa -- check --json path/to/file.kp
cabal run -v0 kappa -- explain E_TYPE_MISMATCH
cabal run -v0 kappa -- test  tests/conformance
```

## How a program is compiled

> **New to the codebase?** [`docs/CONCEPTS.md`](docs/CONCEPTS.md) is a primer
> on the vocabulary the source assumes (de Bruijn indices vs. levels,
> normalization by evaluation, bidirectional typing, quantities) plus a
> suggested file-by-file reading order. The source comments point back to it.

The pipeline lives under [`src/Kappa/`](src/Kappa) and is orchestrated by
[`Kappa.Pipeline`](src/Kappa/Pipeline.hs). Roughly in order:

| Stage | Module(s) | Responsibility |
| --- | --- | --- |
| Source | [`Source`](src/Kappa/Source.hs) | Positions, spans, module names. |
| Lex | [`Token`](src/Kappa/Token.hs), [`Lexer`](src/Kappa/Lexer.hs), [`Unicode`](src/Kappa/Unicode.hs)/[`UnicodeData`](src/Kappa/UnicodeData.hs) | Tokenize (Unicode-aware). |
| Parse | [`Parser`](src/Kappa/Parser.hs), [`Parser.Monad`](src/Kappa/Parser/Monad.hs), [`Syntax`](src/Kappa/Syntax.hs)/[`SyntaxOps`](src/Kappa/SyntaxOps.hs) | Build the surface AST (user fixity, sections, sugar). |
| Resolve | [`Resolve`](src/Kappa/Resolve.hs) | Name resolution, imports, module exports. |
| Elaborate / check | [`Check`](src/Kappa/Check.hs), [`Core`](src/Kappa/Core.hs)/[`CoreOps`](src/Kappa/CoreOps.hs), [`Usage`](src/Kappa/Usage.hs) | The dependently typed elaborator: inference, unification, universe checking, QTT usage, traits/instances. |
| Totality | [`Termination`](src/Kappa/Termination.hs) | Termination/totality checking. |
| Evaluate / run | [`Eval`](src/Kappa/Eval.hs), [`Interp`](src/Kappa/Interp.hs) | Normalization and the tree-walking interpreter that runs `main`. |
| Prelude | [`Prelude`](src/Kappa/Prelude.hs), [`Builtins`](src/Kappa/Builtins.hs) | Builtin types/primitives plus the embedded `std.*` source modules. |
| Diagnostics | [`Diagnostic`](src/Kappa/Diagnostic.hs), [`Explain`](src/Kappa/Explain.hs), [`Pretty`](src/Kappa/Pretty.hs) | Structured diagnostics, the code registry, and rendering. |

The implicit prelude and standard library (`std.prelude`, `std.bytes`,
`std.unicode`, `std.gradual`, `std.bridge`, `std.config`, `std.build`, and
more) are themselves written in Kappa and compiled through the ordinary
pipeline at startup.

## Native backend

In addition to the interpreter, `kappa build` lowers a checked program to C and
links a native executable.

- [`Kappa.Backend.C`](src/Kappa/Backend/C.hs) — code generation to C.
- [`Kappa.Backend.Driver`](src/Kappa/Backend/Driver.hs) — detects a C driver
  and links the runtime.
- [`Kappa.Backend.NativeFfi`](src/Kappa/Backend/NativeFfi.hs),
  [`HeaderGen`](src/Kappa/Backend/HeaderGen.hs),
  [`NativeProbe`](src/Kappa/Backend/NativeProbe.hs) — resolve `host.native.*`
  bindings, generate adapter headers, and probe/verify the host ABI.
- [`runtime/kappart.c`](runtime/kappart.c) — the C runtime the generated code
  links against.

Single-file mode compiles one program with no host bindings:

```sh
cabal run -v0 kappa -- build path/to/program.kp -o program
cabal run -v0 kappa -- build --emit-c path/to/program.kp   # stop after C generation
```

Native host bindings (FFI to C, etc.) are available **only** through the
manifest/package mechanism — there is no `--ffi-full` escape hatch. A program
that imports a `host.native.*` module without a manifest provider fails honestly.

See [`docs/NATIVE_BACKEND.md`](docs/NATIVE_BACKEND.md) and
[`docs/BUILD_AND_NATIVE_BINDINGS.md`](docs/BUILD_AND_NATIVE_BINDINGS.md) for the
details.

## Packages and build manifests

A package is described by a `kappa.build.kp` manifest — itself a checked Kappa
value of type `BuildConfig` (§35.13/§36), not an ad-hoc config format. The build
machinery lives under [`src/Kappa/Build/`](src/Kappa/Build).

```sh
# discover kappa.build.kp upward from the cwd, then build the default executable
cabal run -v0 kappa -- build --manifest

cabal run -v0 kappa -- build --manifest --check          # validate + summarize, no build
cabal run -v0 kappa -- build --manifest --provenance     # print buildConfig value provenance
cabal run -v0 kappa -- build --manifest --target NAME     # build/run a named target
cabal run -v0 kappa -- build --manifest --update          # refresh kappa.lock
```

Highlights:

- **Source roots, fragment axes** (e.g. `backend`/`os`/`role`), **dependencies**
  (registry/git/path/url), **native host bindings**, and **targets**
  (executable / test / benchmark / library / aggregate / alias).
- **Reproducible builds via `kappa.lock`.** The lockfile is a *package-wide*
  artifact pinning the union of every executable/benchmark target's dependency
  closure *and* the host-source identity of each native binding. Ordinary builds
  verify the lock fail-closed; only `--update` may rewrite it.
- Test targets run the Appendix-T harness; benchmark targets run under the
  interpreter.

A worked manifest is in
[`examples/packages/delve/kappa.build.kp`](examples/packages/delve/kappa.build.kp).

## Testing and conformance

Testing is driven by the built-in Appendix-T harness
([`Kappa.TestHarness`](src/Kappa/TestHarness.hs)), exposed as `kappa test`.

```sh
cabal build                                     # zero warnings under -Wall
cabal run -v0 kappa -- test tests/conformance   # the in-tree suite (349/349)
cabal run -v0 kappa -- test examples            # golden-output examples
cabal run -v0 kappa -- test path/to/file.kp     # one fixture
cabal run -v0 kappa -- test --suite path/to/dir # one §T.2 directory suite
```

Test fixtures are ordinary `.kp` files annotated with `--!` directive lines
(`mode check`/`mode run`, `assertNoErrors`, `assertStdout`, `assertEval`, …) and
inline `--!!  CODE` markers that assert a specific diagnostic on a line. Exit
code is non-zero if any test *fails* or the harness errors; `unsupported` never
fails a run (§T.8).

See [`TESTING.md`](TESTING.md) for the full directive subset and harness model.

## Repository layout

```
app/                 the `kappa` CLI (Main.hs)
src/Kappa/           the compiler library
  Backend/           C codegen, native FFI, build driver
  Build/             package manifest, lockfile, provenance, plan
  ...                lexer, parser, resolver, checker, interpreter, prelude, diagnostics
runtime/             C runtime (kappart.c) for the native backend
tests/conformance/   the in-tree conformance suite (.kp fixtures)
examples/            example packages (Delve, image-loader) and native demos
docs/                Spec.md and backend/design documentation
input/               upstream source bundles used as design references
```

## Documentation map

| File | Contents |
| --- | --- |
| [`docs/CONCEPTS.md`](docs/CONCEPTS.md) | Primer + reading order for understanding the compiler source. Start here. |
| [`docs/Spec.md`](docs/Spec.md) | The Kappa Language Specification (the normative source). |
| [`SPEC_COMPLIANCE.md`](SPEC_COMPLIANCE.md) | What's implemented vs. the spec; remaining gaps to 100%. |
| [`docs/notes/KNOWN_SPEC_ISSUES.md`](docs/notes/KNOWN_SPEC_ISSUES.md) | Known issues / ambiguities in the spec itself. |
| [`docs/notes/IMPLEMENTATION_NOTES.md`](docs/notes/IMPLEMENTATION_NOTES.md) | Deep notes on how the implementation works. |
| [`TESTING.md`](TESTING.md) | Test harness, directives, external corpus. |
| [`docs/notes/PERFORMANCE.md`](docs/notes/PERFORMANCE.md) | Performance notes and measurements. |
| [`docs/NATIVE_BACKEND.md`](docs/NATIVE_BACKEND.md) | The native (C) backend. |
| [`docs/BUILD_AND_NATIVE_BINDINGS.md`](docs/BUILD_AND_NATIVE_BINDINGS.md) | Build manifests and native bindings. |
| [`docs/WORKER_DISCOVERED_ISSUES.md`](docs/WORKER_DISCOVERED_ISSUES.md) | Bugs and pitfalls harvested from Claude worker transcripts. |
| [`CHANGELOG.md`](CHANGELOG.md) | Release history. |

## The Delve example

[`examples/packages/delve/`](examples/packages/delve) is a complete,
**config-driven native roguelike** written in Kappa. It exercises the whole
stack: a multi-target package manifest, native host bindings for a terminal
(and optional audio) via the C FFI, the `kappa.lock` reproducibility flow, JSON
save/load, and a tree of `.kp` modules.

Its defining trait is that gameplay content is **data-driven**: actors, items,
spawn tables, worldgen, systems, and lore all live in
`assets/delve/*.json`, are loaded and validated into a typed `ContentPack`, and
only then drive the engine — raw JSON never leaks into combat, rendering, or AI.
Build it with `kappa build --manifest` from that directory; see its
[README](examples/packages/delve/README.md) for controls and design notes.

## License

MIT — see [`LICENSE`](LICENSE).
