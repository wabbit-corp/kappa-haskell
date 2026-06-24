# v2 — wiring `kappart2` into `Kappa.Backend.C`

How real, already-written Kappa programs come to run on the fiber runtime. This
is the "make existing Kappa programs actually run on it" milestone (DESIGN.md
§17). It is grounded in the actual backend code, not a sketch:
`src/Kappa/Backend/C.hs` (`compileDo`, `compileItems`, `emitRunIOValue`,
`emitTailIO`, `emitMain`, `primEntries`) and `src/Kappa/Backend/Driver.hs`
(`linkExecutable`).

## The problem, precisely

`compileDo lbl items` emits a C function `kdo_N(KEnv *cenv)` and returns
`kio(kdo_N, env)` — a suspended `K_IO`. Inside `kdo_N`, `compileItems` lowers
the items as **straight-line C**: each non-tail `KBind`/`KExpr` becomes

```c
KValue *bind_x = krun_io(action);            // emitRunIOValue
if (kis_fail(bind_x)) { /* drain defers */ return bind_x; }
/* ...rest of the do-block, using bind_x... */
```

The continuation after `krun_io(action)` is *the following C statements* — a C
return address on `kdo_N`'s stack. So if `action` is `await child` (or `sleepFor`,
or an STM `retry`), the only way to "suspend" is to block the worker thread
inside `krun_io`, which defeats the scheduler. **The fix is to CPS-convert the
do-kernel** so the continuation becomes a heap closure the CK-machine can re-enter
on a different worker later.

## The key enabler: the de Bruijn `KEnv`

CPS-converting a do-block usually means a live-variable analysis to build the
continuation's captured environment. We get that **for free**: the backend
already threads an explicit de Bruijn `KEnv *` (`gsEnv`), and every binding
`kpush`es onto it. So a continuation is just `kclo(cont_fn, env)` where `env` is
the *current* `KEnv` — it already holds exactly the live locals — and `cont_fn`
pushes the bound value and runs the rest:

```c
/* before (straight-line, cannot suspend at `action`): */
KValue *bind_x = krun_io(action);
/* rest using kpush(bind_x, cenv) */

/* after (CPS — `action` may suspend; the rest is a heap continuation): */
return krt2_bind(action, kclo(kdo_N_k7, cenv));
/* and a generated function: */
static KValue *kdo_N_k7(KEnv *cenv, KValue *bind_x) {
  KEnv *e = kpush(bind_x, cenv);
  /* rest of the do-block, in CPS — itself ending in krt2_bind/krt2_then/tail */
}
```

A do-block thus compiles to a **pure constructor of an action tree**
(`krt2_bind`/`krt2_then`/…), not a function that drives `krun_io`. Each non-tail
bind splits the remaining items into a fresh `kdo_N_kM` continuation; the chain of
continuations *is* the CPS transform. Because `kclo`/`kpush`/`kapp` and the de
Bruijn discipline already exist, this is a re-targeting of `compileItems`, not new
machinery — but it is a real rewrite of a load-bearing function (REVIEW.md B1),
not a one-liner.

## Mapping the do-kernel to the runtime

| `KItem` / form                | v1 (kappart) lowering            | v2 (kappart2) lowering                                  |
|-------------------------------|----------------------------------|--------------------------------------------------------|
| `KExpr t` (tail)              | `emitTailIO` (`kio_tail`)        | the tail action expression (no bind needed)            |
| `KExpr t` (non-tail)          | `emitRunIODiscard`               | `krt2_then(t, <cont>)`                                  |
| `KBind pat t` (non-tail)      | `emitRunIOValue` + bind          | `krt2_bind(t, kclo(cont_fn, env))`, cont pushes+matches |
| `KLet pat t`                  | inline C local + `kpush`         | unchanged (pure; no suspension) — stays inline in cont  |
| `KVarItem` / `KAssign`        | `kref_new`/`kref_set`            | unchanged (refs are synchronous)                        |
| `KReturn t`                   | `emitTailReturn` + defer flush   | a `Return` completion node (needs the completion channel)|
| `KBreak`/`KContinue`          | `goto` + inline defer flush      | `Break`/`Continue` completion nodes (completion channel) |
| `KDefer` / `KUsing`           | GC array + `flushFramesInline`   | `krt2_defer` onto the enclosing `KK_DOSCOPE` exit stack |
| `KWhile`/`KFor`               | C `for`/`while` + `goto` labels  | a recursive IO loop over `krt2_bind`, `cede` at back-edge|
| `KIf`                         | C `if` + tail/nested branches    | `krt2_bind`/`krt2_then` per branch                      |

The prelude scheduler primitives lower to the `krt2_*` builders instead of the
`kpf_io_*` entries (a new column in `primEntries`, gated by the runtime flag):
`fork`→`krt2_fork`, `await`→`krt2_await`, `cede`→`krt2_cede`, `sleepFor`→
`krt2_sleep_for`, `newPromise`→`krt2_new_promise`, `atomically`→`krt2_atomically`,
`newScope`/`forkIn`/`shutdownScope`/`withScope`, `mask`/`uninterruptible`/`poll`,
`acquireRelease`, `blocking`, the `std.atomic` ops, etc. `ioPure`/`ioBind`/`ioThen`/
`throwIO`/`catchIO`/`finallyIO`/`newRef`/`readRef`/`writeRef` map to the
corresponding `krt2_*`.

## `main` and the Driver

- **`emitMain`** emits `krt2_run_main(<main>())` instead of `krun_io(<main>())`
  (`C.hs:1245`). The runtime owns the top-level loop and returns the terminal
  `Exit`; the process exit code is derived from it (Success → 0, Failure → 1 with
  a diagnostic).
- **`linkExecutable`** (`Driver.hs:232-243`) currently compiles `runtimeDir/
  kappart.c` and links `-lgc -lgmp`. For a kappart2 target it additionally:
  - adds `-I <kappart2>/include`,
  - compiles/links the kappart2 TUs (or links the prebuilt `libkappart2.a`),
  - adds libuv via `pkg-config --cflags/--libs libuv` (Driver-owned, like the
    binding pkg-config path),
  - adds `-D_GNU_SOURCE -DGC_THREADS -pthread` to **both** `kappart.c` and the kappart2 TUs
    (REVIEW.md M15 — a mismatch is undefined; enforce with a `_Static_assert`).
  The runtime cannot be a `hostBinding`/`pkgConfig` manifest entry (its symbols
  are codegen intrinsics, not FFI; REVIEW.md M14), so this is Driver-owned.

## Coexistence — do not break the existing backend

The kappart path backs every current native test/example. The kappart2 lowering
is **additive**, selected by a flag (e.g. `--runtime kappart2`, or a
`GenState.gsRuntime` field defaulting to `Kappart`). `compileItems` branches on it;
`primEntries` gains a kappart2 entry-point column; `emitMain`/`linkExecutable`
branch on it. With the flag off, output is byte-identical to today.

## Staging — each stage runs more programs, and is testable

1. **Linear core (no scopes/completion needed).** CPS-lower
   `KExpr`/`KBind`/`KLet`/`KVarItem`/`KAssign` + `ioPure`/`ioBind`/`ioThen`/
   `print`/`throwIO`/`catchIO` + `fork`/`await`/`cede`/`sleepFor`/promises/`now`.
   This already covers `do { f <- fork child; r <- await f; printlnString (show r) }`
   — a real concurrent program runs on the scheduler. *Depends only on the v1
   spine, which is done.* First target: a `fork`+`await`+`sleep` `.kp` compiled
   with `--runtime kappart2` producing the same stdout as the interpreter
   (`KAPPA_RT_WORKERS=1` for byte-exactness, REVIEW.md M13).
2. **Completion channel + finalizers.** `KReturn`/`KBreak`/`KContinue` + `KDefer`/
   `KUsing` + `finallyIO`. *Depends on the runtime increment (`KK_DOSCOPE`,
   `krt2_defer`).*
3. **Loops + `if` + sub-do.** `KWhile`/`KFor`/`KIf`/`KSubDo`, with `krt2_safepoint`
   at back-edges (REVIEW.md M5).
4. **Structured concurrency + the rest.** `newScope`/`forkIn`/`shutdownScope`/
   `withScope`, masking, STM, atomics, `std.supervisor`. *Depends on the runtime
   scopes/interruption increment.*
5. **Native conformance green, then flip `Capabilities.hs`** to the runtime's set
   (§3). `rt-multishot-effects` stays staged behind its escape-check gate.

## Why scopes/completion land in the runtime first

Stages 2–4 of the lowering emit *into* runtime primitives that must already exist:
the `KK_DOSCOPE` completion channel, `krt2_defer`, the `Scope` operations, and
interruption/masking. That is the runtime increment built alongside this doc.
Stage 1 needs none of them, so the first running concurrent program can land as
soon as the lowering branch + Driver wiring exist.
