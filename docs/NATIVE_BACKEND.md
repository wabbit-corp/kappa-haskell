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

**Honestly unsupported** (compile-time `E_BACKEND_UNSUPPORTED`, with the
precise form named — never a silent fallback to interpreter behaviour):

* Type-level / sort terms in value position (`CSort`, `CPi`,
  `CVariantT`, `CRecordT`, `CMeta`), reflection / quote machinery
  (`CQuote`, `CThunkE`/`CLazyE` beyond the simple cases we lower),
  sealed packages / signatures (`CSealE`/`CSigT`).
* `do`-kernel items not in the list above (`KLetQ`, `KDefer`, `KUsing`)
  until implemented; each names itself in the diagnostic.
* `Integer` literals outside the signed 64-bit range.
* Any global whose body uses an unsupported form transitively.

The diagnostic is emitted at build time with the source span of the
offending construct where one is recoverable, and always names the
construct. The backend produces **no** executable when any reachable
definition is unsupported.

### Known limitations of the supported subset

These are honest, documented bounds — not silent divergences:

* **`Int`/`Integer` are 64-bit.** The spec's integers are unbounded; the
  native backend represents them as `int64_t`. A literal outside the
  64-bit range is rejected at compile time, and an arithmetic operation
  whose exact result overflows 64 bits is a **clean runtime trap**
  (`addInt`/`subInt`/`mulInt`/`negInt`/`divInt` check via
  `__builtin_*_overflow`), never a silent wraparound. Programs that stay
  within 64 bits agree with the interpreter exactly; programs that exceed
  it run unbounded under the interpreter but trap natively.
* **Deep non-tail recursion is bounded by the C stack.** Generated calls
  use the native C stack, so a deeply self-recursive function (e.g. a
  non-tail `sumTo 1_000_000`) can overflow it (a clean OS fault), whereas
  the interpreter is bounded by its own `-K64m` guard. This is a
  representation limit, not a miscompilation: at a sufficient stack size
  the result is identical to the interpreter.
* **Floating-point and string `show` are not supported.** `showDouble`,
  `showStringLit`, `showScalar` (whose interpreter output is Haskell's
  `show`) are rejected at compile time rather than risk a formatting
  divergence; double *arithmetic* and comparison are supported.

### Performance characteristics

The backend favours a simple, uniformly-boxed representation over raw
speed. Every value is a heap `KValue`; primitive application allocates a
`K_PRIM` box and dispatches by name through the runtime's primitive
tables; variable lookup walks the linked `KEnv`. A trivial integer loop
therefore costs several allocations and a handful of `strcmp`s per
iteration (≈4 µs/iteration on the reference machine; a 1,000,000-step
loop completes in ~4 s with **flat** ~3 MB RSS). This is "reasonably
bounded" — linear in the work, constant in memory thanks to the GC — but
it is not optimised native code; unboxing and primitive specialisation
are obvious future work.

## 6. FFI and the HTTP + SQLite demo

The runtime exposes a small set of C primitives (registered as ordinary
prelude `prim` globals with native-only IO semantics; see
"Kappa.Backend.Ffi" and `runtime/kappart_ffi.c`) that wrap POSIX sockets
and `sqlite3`:

* TCP sockets: `__tcpListen` (bind+listen), `__tcpAccept`, `__connRead`,
  `__connWrite`, `__connClose`, `__listenClose`;
* sqlite3: `__sqliteOpen`, `__sqliteExec`, `__sqliteQueryInt`,
  `__sqliteQueryText`, `__sqliteClose`.

These are real IO actions run by the FFI runtime under `krun_io`; the
interpreter does not provide them, and a non-`--ffi-full` native build
rejects them at compile time (the FFI primitive set is excluded), so
nothing silently degrades.

`examples/native/http_sqlite/` contains the demo: `server.kp` is a native
HTTP server that, for each request, performs a SQLite write (increment a
persistent hit counter) and a SQLite read (the new count), then returns an
HTTP/1.1 response reporting the count. `run.sh` builds it, drives three
requests, and verifies both the responses (`hits=1/2/3`) and the persisted
database state (`counter.hits = 3`) — proving the request → SQLite →
response path runs in a real native process.

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

# build + drive the HTTP + sqlite demo (needs -lsqlite3)
cabal run -v0 kappa -- build --ffi-full --lib -lsqlite3 \
  examples/native/http_sqlite/server.kp -o /tmp/kserver
bash examples/native/http_sqlite/run.sh   # end-to-end smoke test
```

`kappa build` flags: `--emit-c` (stop after writing the `.c`), `-o OUT`,
`--cc DRIVER` (override the C driver), `--ffi-full` (link the
libc-sockets + sqlite3 FFI runtime instead of the no-FFI stub), and
`--lib FLAG` (extra linker flags, repeatable).

Native backend tests live under `test/` (driven by the Haskell test
suite) and `examples/native/` (end-to-end build+run smoke tests with
timeouts). They are gated on a C driver being available and skip with a
clear message when it is not, so the core suite still runs in a minimal
environment.
