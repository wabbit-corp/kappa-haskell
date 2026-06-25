# The LLVM backend

A second native backend (`src/Kappa/Backend/LLVM.hs`, entry point `generateLL`) that
emits **textual LLVM IR** (`.ll`). It exists so the value-representation/layout system,
Perceus precise reference counting, and coroutine-lowered CPS — none of which C can
express cheaply — eventually have a home (see [CPS-DESIGN.md](CPS-DESIGN.md) Stage 5 and
[UNBOXING-DESIGN.md](UNBOXING-DESIGN.md)). It is selected with the environment variable
`KAPPA_BACKEND=llvm`; the default remains the C backend (`Kappa.Backend.C`, `generateC`),
which is unchanged.

## Strategy: parity first, perf later

The buildout is in two phases:

- **Phase 1 — uniform-boxed parity (current).** Same ~40-byte boxed `KValue` model as
  the C backend, the **same kappart2 runtime**, the same `KEnv`/`kpush`/`kvar`
  discipline, the same `kctor`/`kapp`/`knative_sat` ABI. *Only the emitted source
  language differs.* The LLVM backend must match the C backend's observable behaviour
  bit-for-bit; that is the entire correctness contract of Phase 1. There is no perf
  advantage yet — the point is a correct end-to-end IR path to build the real work on.

- **Phase 2 — the perf endgame (later, CPS-DESIGN Stage 5).** The LLVM-native layout
  system (immediate-tagged ints, unboxed scalars, niche optimization, newtype erasure),
  Perceus precise RC (`dup`/`drop` + in-place reuse) **as the primary mechanism in a
  mixed/hybrid memory model** — *not* a wholesale GC replacement, since pure reference
  counting leaks cycles, so a tracing/cycle-collector (or region) backstop for cyclic
  data is still needed (exact scheme TBD) — and coroutine-lowered CPS (`llvm.coro.*`,
  with `CoroSplit` seeded by the live `KEnv` set). The *stable seam*
  CPS-DESIGN §5 mandates — the continuation signature and the `KEnv` de-Bruijn
  discipline — is preserved by building Phase 1 on the same runtime, so Phase 2 slots in
  without tearing anything out.

## Why textual `.ll` (not `llvm-hs`)

`clang` compiles a `.ll` file directly (`clang foo.ll runtime.c… -o exe`); no `llc`,
`opt`, or `zig` is required, and no heavy `llvm-hs`/C++ dependency is pulled in. This
mirrors the C backend, which already emits text and shells out to a toolchain — the IR
emitter is a near-mechanical port of the C string-builder. Conventions:

- **Opaque pointers** (`ptr`, not `i8*`) — modern LLVM. `KValue*`, `KEnv*`, `Rt*`, and
  every function pointer are all `ptr`.
- **Omit `target triple` / `datalayout`** — let clang infer host defaults (a cross
  build injects the triple from the existing `targetFlags`). The only effect is a benign
  `-Woverride-module` note.
- **Default C calling convention** (no `cc` keyword) — matches the runtime's
  System-V/AArch64 ABI.

## Architecture

`generateLL :: CheckState -> GName -> Set Text -> Map GName ResolvedNativeSymbol ->
Either [BackendError] Text` — the **same signature** as `generateC`, returning a complete
`.ll` translation unit. It mirrors the C backend's structure:

- A `GenState` + `State` emission monad. The defining difference from C: **`compile ::
  Term -> Gen Text` returns an SSA operand** (`%v7`, an `@global`, or `ptr null`), not a
  nestable expression string. LLVM is three-address, so every compound sub-result is
  materialized as an instruction (a `call`/`getelementptr`/…) emitted into the current
  basic block, and the operand naming it is returned. This is the single biggest
  mechanical change; everything else transliterates 1:1 from the named C.hs `compile*`
  functions.
- A **worklist** over `gsBodies` (`drainQueue`/`emitGlobal`/`enqueue`) identical in
  shape to the C backend's — representation-independent; only leaf emission differs.
- **String interning** with UTF-8 byte length (`@kstr(ptr, i64 byteLen)`, NUL-safe like
  the C backend — never `kstr0`+`strlen`), plus a separate NUL-terminated C-string pool
  for `kbigint_str`.
- The runtime is reused via **declared externs**: each runtime symbol the program calls
  gets a deduplicated `declare` line; the runtime `.c` files compile + link exactly as
  for the C backend (the Driver passes the `.ll` in the same argv slot a `.c` occupies).

`main` mirrors the C backend's `emitMain`: `krt2_new(i32 0)` → `kg_main()` →
`krt2_run_main` → `krt2_exit_is_success` → `select` (return 0 on success else 1). There
is **no `krt_init` call** — it runs inside `krt2_new`. Each global is a memoized arity-0
CAF accessor (`.cache` global + load/`icmp ne null`/`phi` guard) or, later, a
worker + closure-chain (Milestone D).

GC safety in Phase 1 is the C backend's: Boehm scans the C stack conservatively, and SSA
values / `alloca` slots are all visible to it — no precise stack maps. (Precise RC is
Phase 2.)

## Milestone roadmap

Each milestone extends `compile` to handle more Core forms, mirroring the named C.hs
function, and is gated by `test/native/llvm-parity.sh` (**interp == C == LLVM** on stdout
+ exit code; the interpreter is the conformance oracle, so three-way agreement on a
diverse corpus is the proof). The corpus lives in `tests/native/llvm/`.

| Milestone | Forms | Status |
|---|---|---|
| **M0** | `CLit` string, `printlnString`/`printString` (`knative_sat`), `CGlob` CAF refs, `main` | ✅ `c28797d` |
| **M1** | `CLit Int` (`kint`/`kbigint_str`), ten pure direct `kp_*` Int/show prims, prim-spine apps | ✅ `88f9e8f` |
| **M2** | CAF cross-references (enqueue + accessor) | ✅ `88f9e8f` |
| **B**  | `CVar`/`CLet` (uniform `kpush`/`kvar`), widen pure-direct prims to Integer/String/Bool | ✅ `ce30ca5` |
| **C**  | constructors + `CMatch` + `CIf` (tag ids as IR `i32`; `kctor`/`kctor_tagid`/`kctor_arg`) | ✅ `f4d443b` |
| **D**  | `CLam` + closures + general `kapp` + tail-call `kbounce` (curried model; worker chain is Phase 2) | ✅ `5848b85` |
| **E**  | `CDo` do-kernel (linear `bind`/`let`/`action`/`final` → `krt2_bind`/`krt2_pure` tree, lazy continuations — the §5 seam) | ✅ `3cab171` |
| **F–M** | do-kernel `KIf`/loops/cells/abrupt, records, recursive patterns, all literals + prim coverage, `letrec`/thunks, host FFI, exceptions, `KSubDo` — the delve-driven surface (see below) | ✅ → `0ec0078` |
| **Phase 2** | layout system · Perceus RC (+ GC/cycle backstop, mixed model) · coroutine CPS | future |

**Phase-1 core (M0–E) is complete** at interp == C == LLVM over 35 corpus programs:
strings, integers (incl. big-Integer), pure prims, CAF graphs, local bindings,
constructors/match/if, curried closures + general application + stack-safe tail
recursion, and IO do-blocks. Remaining Phase-1 *surface* (each a clean
`E_BACKEND_UNSUPPORTED` today, not a miscompile):

- **do-kernel control flow** — ✅ `KIf` (`ee9064f`); ✅ `KWhile` + mutable cells
  (`KVarItem`/`KAssign`) + abrupt control (`KBreak`/`KContinue`/`KReturn`) via
  `krt2_while`/`krt2_break`/`krt2_continue`/`krt2_return` + `newRef`/`readRef`/`writeRef`,
  with `var`-read splices hoisted to monadic-normal-form (`b4ba6fa`); remaining: `KFor`
  (list cursor), while-`else`, labeled loops, `KDefer`, `KUsing`, `KSubDo`, `KLetQ`, and
  function-scoped `return` (a runtime gap — `krt2_return` finishes the fiber).
- **records** — ✅ `CRecordV` + `CProjAt`/`CProj` via `krec`/`krec_at`/`kproj`
  (`1b3770d`); ✅ type-level-global erasure so trait instances on builtin types
  compile (`fb3c2bc`).
- **patterns** — ✅ literal patterns (`ee9064f`); ✅ recursive nested/tuple/record/variant
  + or-patterns with exact de-Bruijn binder order (`e600d61`).
- **literals + prims** — ✅ `Byte`/`Char`/`Double` literals + generalized prim-as-value
  coverage (`71003bc`); ✅ `letrec` + `delay`/`memo`/`force` thunks (`502188d`).
- **host FFI** — ✅ host-native members via a C-wrapper sidecar (lower like prims over
  `wrapperCName`; the Driver emits the marshalling `.c`) (`5ac0e21`).
- **exceptions + sub-do** — ✅ `catchIO`/`finallyIO`/`throwIO` as `krt2_catch`/`finally`/
  `throw` node-builders + `KSubDo` (`0ec0078`).
- **remaining (not needed by delve/voxelcraft)** — concurrency/STM (`fork`/`await`/STM),
  `KFor`/while-`else`/labeled loops, the worker/closure-chain + self-TCO perf path.

**Empirically driven by building the real packages — Phase 1 surface DONE:** both real
packages codegen fully LLVM-clean. voxelcraft was clean from the start; delve went from
**721 unsupported sites → 0**: records 368, curried prims + `Byte`/`Char`/`Double`
literals 124, `letrec`/`delay`/`force` 127, recursive patterns 90, host-native FFI 17,
exceptions + `KSubDo` 10, type-global erasure 6. `delve-macos-arm64` now codegens with
zero `E_BACKEND_UNSUPPORTED` on `KAPPA_BACKEND=llvm`. The corpus gate is 81/81
interp == C == LLVM, with zero miscompiles found across every milestone's adversarial
sweep. Phase 2 (the layout system · Perceus + GC backstop · coroutine CPS) is the next
chapter.

## Extending it

To add a Core form: find how `Kappa.Backend.C` lowers it (a `compile*` function), then
emit the equivalent IR three-address — compile each sub-term to an operand, then the
instruction that consumes them. Use the **uniform** realization (always correct, not
necessarily fastest): every binder pushes one `kpush` env slot and `CVar i` reads
`kvar(env, i)`; do *not* port the C backend's `gsParamLvals` flat-param fast path in
Phase 1. Add corpus programs under `tests/native/llvm/` that print an observable result
exercising the new form, and run the parity harness until interp == C == LLVM. A form not
yet handled must emit a clean `E_BACKEND_UNSUPPORTED` (the catch-all in `compile`) — never
a silent wrong answer.
