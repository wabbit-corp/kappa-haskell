# Native backend

This document describes the **native backend** for the Kappa
implementation: the path that compiles a Kappa program to a real
native executable (an ELF binary), the runtime it links against, the
garbage-collection model, the code-generation strategy, and the FFI
surface used by the HTTP + SQLite demo.

It complements the interpreter (`Kappa.Interp`), which remains the
reference executor for the full supported language subset. The native
backend reuses the **same** front end — lexer, parser, resolver,
elaborator — and lowers the elaborated KCore (`Kappa.Core.Term`) to C.
There is no second type checker, no second lowering, and no separate
semantic model: the backend is a code generator over the existing IR.

> Scope note (§27.7). Code generation / backends are a *profile-scoped*
> area of the spec. The portable `kappa-v1` conformance surface this
> implementation targets does not mandate a native backend, and the
> conformance suite does not exercise one. This backend is therefore an
> *additive* capability: it must never change the behaviour of `check`,
> `run`, or `test`, and a program the native backend cannot compile must
> fail honestly (`E_BACKEND_UNSUPPORTED`) rather than silently diverge
> from the interpreter.

## 1. Toolchain

| Concern        | Decision                                                                 |
| -------------- | ------------------------------------------------------------------------ |
| Native driver  | `zig cc` (bundles clang 21.x) when present; system `cc`/`gcc` otherwise. |
| GC             | Boehm–Demers–Weiser conservative collector (`-lgc`, `gc.h`).             |
| FFI demo deps  | POSIX TCP sockets (libc, no extra dep) and `sqlite3` (`-lsqlite3`).      |

> The demo uses blocking POSIX sockets (`sys/socket.h`) rather than
> libuv: the requirement permits "libuv or sockets", and a blocking
> accept loop keeps the demo a straightforward, unquestionably-real
> native server with one fewer external dependency. The only FFI library
> linked is sqlite3.

`zig cc` is preferred because it is hermetic and trivially installable
without root (a single tarball). The implementation auto-detects a
driver in this order:

1. `$KAPPA_CC` if set (explicit override).
2. A local `zig` under `.toolchain/` (or on `$PATH`) → `zig cc`.
3. `cc`, then `gcc`, then `clang` on `$PATH`.

If none is found, `kappa build` fails with a clear diagnostic naming the
drivers it looked for and how to install one. The generated C is plain
C11 and links the same way under either driver, so the choice of driver
does not affect semantics.

`zig` itself is **not** committed (it is ~50 MB); `.toolchain/` is
git-ignored. CI / reviewers install it with the documented one-liner in
`docs/NATIVE_BACKEND.md` §7 or set `$KAPPA_CC` to any C compiler.

## 2. Pipeline

```
source ──front end──▶ KCore (Term, per global)
                          │
                          ▼
                  Kappa.Backend.C        (lower Term → C source)
                          │
                          ▼
              <out>.c  +  runtime/kappart.c  +  runtime/kappart.h
                          │
                       zig cc / cc           (compile + link, -lgc …)
                          ▼
                   native executable
```

`kappa build FILE [-o OUT] [--emit-c] [--cc DRIVER] [--lib NAME]…`:

* runs the ordinary compilation pipeline (`compileSourceWithPrelude`)
  and refuses to proceed if the front end reports any error — the
  native backend never compiles code the checker rejected;
* requires a `main` definition (`E_NO_MAIN` otherwise), exactly like
  `kappa run`;
* lowers each reachable global's **elaborated** `Term` to C
  (`Kappa.Backend.C`), emitting one translation unit;
* writes the C next to the runtime, invokes the C driver, and produces
  `OUT` (default: the input basename without extension);
* `--emit-c` stops after writing the C source (useful for tests and
  inspection) and does not invoke the driver.

The elaborated `Term` for each top-level definition is captured during
elaboration (`CheckState.csCoreBodies`) — re-deriving it by `quote`-ing
the stored NbE `Value` is **unsound** for `do`-blocks and suspensions
that close over `let`/argument bindings (`quote` drops the captured
environment), so we keep the real elaborator output instead.

## 3. Value representation

Every Kappa value is a uniformly **boxed**, heap-allocated object
(`KValue*`), so the generated code and the runtime can treat values
uniformly (apply, match, project) without monomorphising. The header is
a tag; the body is a tagged union:

```
struct KValue {
  uint8_t tag;            // KValueTag
  union {
    int64_t   i;          // K_INT  (Nat/Int/Integer share this; see §5)
    double    d;          // K_DBL
    KStr      str;        // K_STR  (len + GC'd char buffer, not NUL-terminated)
    uint32_t  chr;        // K_CHR  (Unicode scalar value)
    KCtor     ctor;       // K_CTOR (tag-name + boxed args)
    KRecord   rec;        // K_REC  (sorted field-name + boxed value array)
    KClosure  clo;        // K_CLO  (fn pointer + captured-env array)
    KForeign  fgn;        // K_FGN  (opaque host pointer, e.g. socket fd / sqlite3*)
    KRef      ref;        // K_REF  (mutable cell: one boxed slot)
  } as;
};
```

* `K_INT` holds a 64-bit machine integer. The spec's `Integer` is
  unbounded; the native backend supports the 64-bit range and reports
  `E_BACKEND_UNSUPPORTED` if a literal does not fit (it never silently
  wraps). See §5.
* `K_CTOR` carries the constructor's **fully-qualified name** (interned
  C string) and its boxed arguments; matching compares the name. Unit,
  `True`/`False`, list `Nil`/`Cons`, etc. are ordinary constructors.
* `K_REC` keeps fields in the spec's canonical (lexicographic) order, so
  projection is a name lookup and equality is positional.
* `K_CLO` is a function pointer of fixed arity 1 (`KValue* (*)(KValue*
  env, KValue* arg)`) plus a captured-environment array. All Kappa
  functions are curried to arity-1 closures; multi-argument application
  is a chain of `kapp` calls. This keeps codegen uniform and makes
  partial application free.
* `K_FGN` wraps an opaque host pointer for FFI (a socket file descriptor,
  a `sqlite3*`, …). The GC scans it conservatively but never frees the
  underlying resource; explicit close/free primitives do that.
* `K_REF` is the runtime cell behind `var`/`MonadRef` (§18.6.1).

## 4. Garbage collection

The runtime uses the **Boehm–Demers–Weiser conservative garbage
collector** (`libgc`). Rationale, in the spirit of the requirement that
"leaks-as-a-strategy is not acceptable":

* **Model.** Mark-and-sweep, conservative on the C stack and registers,
  precise enough for our needs because every Kappa value is a single
  `KValue` box reached through ordinary C pointers. No value is
  manually freed; the collector reclaims unreachable boxes.
* **Allocation API.** `kgc_alloc(size)` → `GC_MALLOC` (scanned: may
  contain pointers, e.g. ctor args, env arrays). `kgc_alloc_atomic(size)`
  → `GC_MALLOC_ATOMIC` (pointer-free, e.g. string/byte buffers) so the
  collector does not scan large blobs for spurious pointers.
  `kgc_init()` calls `GC_INIT()` once at startup (`main`).
* **Object layout & scanning.** Every heap object is a `KValue` or a
  `KValue*[]` (env / ctor-arg / record-value arrays) or a `char[]`
  (string bytes, atomic). Because the collector is conservative it needs
  no per-type maps; because the arrays are real C pointer arrays it
  traces them precisely. There are no tagged/packed pointers that would
  hide a reference from the collector.
* **Ownership / lifetime.** Kappa is GC'd: values have no owner and no
  scope-bound destructor at the C level. `defer`/`using` (§18) run their
  bodies for *effect* ordering, not for memory reclamation; the memory
  is the GC's. FFI resources (`K_FGN`) are the one exception — their
  lifetime is managed explicitly by the FFI primitives that open/close
  them, and the GC only reclaims the small `KValue` wrapper.
* **Limitations.** (a) Conservative scanning can retain garbage that a
  precise collector would free (false roots from integer-shaped stack
  words); acceptable and bounded. (b) No finalizers are registered, so a
  Kappa program that opens FFI handles and drops them without closing
  leaks the *host* resource (not Kappa memory) — this matches manual FFI
  ownership and is documented, not hidden. (c) `libgc` must be present at
  link time; if absent, `kappa build` fails with a clear message.

## 5. Codegen and the supported subset

`Kappa.Backend.C` lowers `Term` to C. Each Kappa global becomes either a
C `KValue*`-returning thunk (CAF) or, when it is a function, a top-level
closure constructor. The lowering is a straightforward structural
recursion over `Term`, mirroring `Kappa.Eval.eval` but emitting C
instead of stepping an interpreter, so the two stay semantically aligned
by construction.

**Supported `Term` forms** (preserving spec semantics for the subset):

* `CVar`, `CGlob`, `CLam`, `CApp` — variables, globals, closures,
  curried application.
* `CLit` — `LitInt`/`LitDouble`/`LitStr`/`LitScalar` (and byte/grapheme
  where they reduce to the above).
* `CCtor`, `CMatch` (over `CPWild`/`CPVar`/`CPLit`/`CPCtor`/`CPTuple`/
  `CPRecord`/`CPInject`/`CPOr`/`CPAs`), `CIf`.
* `CLet`, `CLetRec` — including recursive functions (knot via the
  closure environment).
* `CRecordV`, `CProj` — record values and projection.
* `CDo` over the executable do-kernel: `KExpr`, `KBind`, `KLet`,
  `KReturn`, `KVarItem`, `KAssign`, `KWhile`, `KFor`, `KIf`, `KBreak`,
  `KContinue`. These compile to ordinary C control flow.
* Primitive globals (`__prim.*`): integer/float/string/char operations,
  comparison, `show*`, and the IO primitives backing the demo, each a
  C runtime function.

**Coverage.** The backend compiles the accepted **run-mode (`UIO`) surface**
exercised by the conformance suite and seven adversarial review rounds — no
spec-mandated *runtime* construct it touches is rejected or silently
miscompiled. Every do-kernel item (`defer`/`let?`/labelled `break`/`continue`,
loops, statement-`if`, `match`), every value form (variants, suspensions,
records, bignum, Rational, bytes/Unicode), and §9.1.1 `projection` selectors
lower and run equivalently to the interpreter. In particular:

* **`defer` (§18.7)** runs at **any** scope depth (do-block, loop body, `if`
  body — per-scope frames) and is evaluated **lazily at scope exit** (a
  suspended `kio` thunk capturing the environment, `compileDeferAction`), so a
  deferred body observes state mutated between registration and the flush —
  never a registration-time snapshot.
* **Binding or-patterns (§17.2.3)** are distributed into or-free alternatives
  (`distributePat`) in `match`, in `let?` (tried in source order, first match
  wins), and in a `let?` else residue.
* **`let?` (§18.2.1)** binds an else *residue* pattern only after testing it
  against the scrutinee (`krt_fail` on a refutable mismatch, like the
  interpreter), never binding the wrong constructor's fields.
* **Real value globals** — a top-level *prefixed* binding (`let 1 x`/`let &x`)
  and a `projection` — record their core body, so the backend lowers the real
  value rather than erasing it.

Type-level / staging terms (`CSort`/`CPi`/`CVariantT`/`CRecordT`/`CSigT`/
`CMeta`/`CQuote`, and a `Type`- or `Syntax`-typed definition referenced as
a value) are **erased** to a unit placeholder wherever they appear — an
argument, a field, a local `let` binding (§12.2, §31.2; §30.2.4 for staging).
A no-body global accessor erases to the unit placeholder **only** when the
global is genuinely type-level (a data/trait name or a sort-typed builtin); a
real value-typed global that reaches codegen without a recorded core body is a
fail-stop `E_BACKEND_UNSUPPORTED`, never a silent unit.

The `E_BACKEND_UNSUPPORTED` mechanism remains as a defensive backstop for
genuinely non-runtime forms (a bare un-eta-expanded constructor or a
`KUsing` kernel item — both elaboration invariants that accepted programs
do not produce, and a primitive name the linked runtime does not provide —
the §21/§23 *elaboration-time* reflection/staging prims, which live in the
`Elab` monad and so cannot appear in a `UIO` program). It is emitted at
build time with the construct's source span and **no** executable — never a
silent fallback to interpreter behaviour. See
[`NATIVE_ESCALATIONS.md`](NATIVE_ESCALATIONS.md).

### Properties of the supported subset

* **`Int`/`Integer` are unbounded.** Values within signed 64-bit stay
  inline (`K_INT`); an operation whose exact result overflows promotes to
  a GMP bignum (`K_BIGINT`) — never a wraparound or trap — matching the
  interpreter exactly (factorials, `2^128`, the 64-bit boundary, bignum
  div/mod/compare incl. negatives are all verified native ≡ interpreter).
* **All tail recursion is stack-safe (§27.5A.3).** A top-level function is
  a *worker* whose body is a `while(1)` loop: a direct tail self-call
  rebinds the parameters and `continue`s. Every *other* tail call —
  mutual recursion, a call through a function value, and a local `let rec`
  lambda's self-call — returns a trampoline `K_BOUNCE` that the driving
  `kapp`/`krun_io` drains in a single C frame (`SinkBounce`).
  **IO sequencing is also trampolined**: a do-block's tail IO action is
  handed to the `krun_io` loop instead of being run by a nested `krun_io`,
  via `kio_tail` (result propagated), `kio_effect` (a tail statement-`if`
  branch whose result is discarded, §18.8 → the do-block yields `Unit`), or
  `kio_finally` (carrying §18.7 `defer` finalizers, accumulated on a heap
  stack and run LIFO after the action). This covers tail IO recursion
  through a trailing expression, a statement-`if` branch (incl. nested,
  chained, and mutual), `let?`-else, a trailing `match`, a `while`/`for`
  body, and any of those with a top-level `defer` present. All forms run
  in **constant C stack** (verified to depth 5,000,000 under an 8 MB stack;
  the interpreter itself StackOverflows well before that), flat ~2.4 MB RSS.
  *Not* tail position, hence bounded by the C stack like any deep non-tail
  recursion (the interpreter is also O(n) stack here, and O(n²) time): the
  recursive call in the **bound/first leg** of `bindIO`/`ioThen`/`ioBind`
  (left-nested `>>=`), and a deeply-recursive `!`-splice (`__runIO`). These
  are fail-stop (never a wrong answer) and `ulimit -s` raises the bound.
* **`show` and the §29 text/Unicode surface are supported.** `showDouble`
  (shortest round-trip, Haskell format), `showStringLit`/`showScalar`
  (Haskell escaping), `Rational`, byte/bytes/grapheme literals + prims,
  the linear `BytesBuilder`, UTF-8 codec / scalar cursors / `StringBuilder`
  / incremental decoder, and table-driven UAX-15 normalization + UAX-29
  grapheme segmentation + case-fold (over the committed `Kappa.UnicodeData`
  tables, generated into `runtime/kappa_ucd.h` by `tools/gen-ucd-c.py`) all
  produce byte-identical output to the interpreter.

### Performance characteristics

The representation is uniformly boxed (every value a GC'd `KValue`), but
the hot paths avoid needless overhead:

* A saturated application whose spine head is a known primitive lowers to
  a single `kprim_call` over a stack argument array — no intermediate
  curried `K_PRIM` boxes or per-argument allocation; the hottest
  arithmetic/comparison ops are matched first in the arity dispatch.
* A saturated call to a known function global calls its worker `kw_…`
  directly (through the trampoline) instead of building a curried
  closure chain.
* Small integers (`-16..256`) and the two `Bool` constructors are cached;
  a closure binds its environment once (not per variable reference); a
  mutable-`var` read/write inside a loop lowers to a direct `kref_*` cell
  access rather than the suspended-IO path.

A tail-recursive `sum 1..10_000_000` runs in ~4.2 s and a
`var`-mutating `while` loop of 1,000,000 steps in ~0.4 s, both at flat
~2.4 MB RSS (≈16× / ≈10× faster than the first cut). Residual cost is the
inherent boxing/GC of the uniform representation and the by-name primitive
dispatch; integer unboxing and opcode dispatch remain available future
work (they would not change observable behaviour).

## 6. FFI and the HTTP + SQLite demo

The foreign boundary is spec-conformant and manifest-driven: a program
`import`s a `host.native.*` module (§8.3.5) that a build manifest's
`nativeBinding` provider (§36.28) supplies, realized by the `zig` profile
through the direct native adapter (`native.direct`, §27.1.1). The binding's
`symbolList` of `symbolDecl`s fully describes the surface (Kappa member, C
symbol, ABI signature); codegen lowers each member to a **direct typed C
call site** — an `extern` prototype + a marshalling wrapper + a `knative`
action whose function pointer `krun_io` calls directly. There is no hardcoded
native catalog, no runtime FFI primitive table, and no string/`KValue`
dispatch in generated native output. The C symbols come from the manifest's
`inputs` (a package `shim`, `pkgConfig`-resolved libraries, headers). The
full mechanism and rationale are in
[`NATIVE_FFI_DESIGN.md`](NATIVE_FFI_DESIGN.md) and
[`BUILD_AND_NATIVE_BINDINGS.md`](BUILD_AND_NATIVE_BINDINGS.md).

Honest failure modes (no silent fallback): under the interpreter
(`run`/`check`) or a build with no manifest provider for a module, an
`import host.native.X` is unresolved → `E_MODULE_NAME_UNRESOLVED`; a bare
`expect term` has no native provider → `E_EXPECT_UNSATISFIED` (§9.4);
source-defining a `host.native.*` module → `E_HOST_MODULE_SOURCE_DEFINED`
(§8.3.5).

`examples/native/http_sqlite/` contains the demo: `server.kp` imports
`host.native.sqlite3` and `host.native.posix.net`, and its
`kappa.build.kp` provides both via `nativeBinding`s. For each request it
performs a SQLite write (increment a persistent hit counter) and read,
then returns an HTTP/1.1 response reporting the count. `run.sh` builds it
with `kappa build --manifest examples/native/http_sqlite`, drives three
requests, and verifies both the responses (`hits=1/2/3`) and the
persisted database state (`counter.hits = 3`).

## 7. Building and testing

```sh
# one-time: fetch a hermetic C driver (no root); or set $KAPPA_CC=cc
ZIG=zig-x86_64-linux-0.16.0
curl -fsSL https://ziglang.org/builds/$ZIG.tar.xz | tar -xJ -C .toolchain
export KAPPA_CC="$PWD/.toolchain/$ZIG/zig cc"

# compile a Kappa program to a native executable
cabal run -v0 kappa -- build examples/native/hello.kp -o /tmp/hello
/tmp/hello

# inspect generated C without invoking the driver
cabal run -v0 kappa -- build examples/native/hello.kp --emit-c

# build + drive the HTTP + sqlite demo via its build manifest (needs -lsqlite3)
cabal run -v0 kappa -- build --manifest examples/native/http_sqlite -o /tmp/kserver
bash examples/native/http_sqlite/run.sh   # end-to-end smoke test
```

`kappa build FILE` flags: `--emit-c` (stop after writing the `.c`),
`-o OUT`, `--cc DRIVER` (override the C driver). A single-file build has
no native bindings (those come only through a manifest).

`kappa build --manifest [DIR]` flags (§35.13/§36): `--check` (validate +
summarize the configuration only, no build), `--target NAME` (select an
executable target), plus `-o OUT`, `--emit-c`, `--cc DRIVER`. Native
host bindings, codegen, and link flags are all driven by the manifest's
`nativeBinding` providers — see
[`BUILD_AND_NATIVE_BINDINGS.md`](BUILD_AND_NATIVE_BINDINGS.md).

Native backend tests live under `test/` (driven by the Haskell test
suite) and `examples/native/` (end-to-end build+run smoke tests with
timeouts). They are gated on a C driver being available and skip with a
clear message when it is not, so the core suite still runs in a minimal
environment.
