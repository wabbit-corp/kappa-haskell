# Prior-art research — what `kappart2` borrows, and from where

Five web-grounded research passes informed the runtime's design and the v2/v3
roadmap: stackless/CPS IO lowering, effect-handler abstract machines, structured
concurrency, work-stealing schedulers, and GC under green threads. The headline:
**the validated design needs no architectural change** — the literature
independently re-derives the choices already made (heap-reified continuations,
the `__EffOp` evidence-passing tree, the re-entrant scope-drain latch) — and it
gives a concrete, cited upgrade path for performance. Each section lists the load-
bearing sources and the "adopt now / v2 / v3" mapping onto our code.

---

## 1. Stackless / CPS lowering of the do-kernel (drives v2, INTEGRATION.md)

**Finding.** The canonical recipe is **CPS-convert then defunctionalize**: each
non-tail bind becomes one heap continuation frame
`krt2_bind(action, kclo(cont_fn, captured-env))`, and the defunctionalized
continuation *is* a frame-stack machine — exactly our `Cont` stack. The cut site
in our backend is `compileItems`/`bindAndContinue` (`C.hs ~2795`); the captured
env is the existing de Bruijn `KEnv` (so liveness is free — capture the whole env
first, project to live levels later). Keep `K_IOTAIL`/`emitTailIO` for the tail
(don't CPS the fast path).

- Appel, *Compiling with Continuations* (CUP 1992) — CPS as compiler IR.
- Ager, Biernacki, Danvy, Midtgaard, *A Functional Correspondence between
  Evaluators and Abstract Machines* (PPDP 2003) — defunctionalized CPS = frame
  machine.
- Reynolds, *Definitional Interpreters…* (1972) — defunctionalization.
- Rust async→state-machine (Mandry, *How Rust optimizes async/await*); C#/Roslyn
  async; Kotlin `ContinuationImpl` — only **live** locals are spilled into the
  resumption (the over-capture-leaks pitfall under our conservative GC).

**Adopt:** RANK-1 per-bind CPS-then-defunctionalize; hybrid tail via `K_IOTAIL`;
whole-env capture first then a liveness projection. **Prerequisite (done):**
explicit heap scope/finalizer frames so `defer`/`using` survive a cross-worker
resume — this is the completion channel (`KK_DOSCOPE`/`KK_FINSEQ`) now shipped.

## 2. Effect handlers → abstract machine (drives v2 `rt-multishot-effects`)

**Finding.** Two families: (A) **native stack-segment** (Multicore OCaml 5,
libmprompt, libhandler) — a resumption is a pointer to a suspended stack-segment
chain; O(1) one-shot, deep-clone for multi-shot; needs stack switching. (B)
**evidence-passing / yield-bubbling** (Xie & Leijen) — every effectful step returns
`Pure v` or `Yield(marker, op, k)`, `k` extended by each bind, handlers found by an
evidence vector. **We are family (B) already**: `KCT_EFFOP`/`KCT_EFFPURE` *is* the
`Yield`/`Pure` tree and `__effBind`/`__handleEff` are the bubbling — so effects stay
on that representation; the `Cont` stack carries only IO control (do **not** unify).

- Xie & Leijen, *Generalized Evidence Passing for Effect Handlers* (ICFP 2021,
  PACMPL 5:71) — the canonical model for compiling handlers to plain code.
- Sivaramakrishnan, Dolan, et al., *Retrofitting Effect Handlers onto OCaml*
  (PLDI 2021; arXiv:2104.00250) — the stack-segment runtime, one-shot default.
- Leijen, **libmprompt / libmpeff** (koka-lang) — multi-prompt delimited
  continuations in portable C; the reference for a C-runtime resumption.
- Hillerström & Lindley, *Liberating Effects with Rows and Handlers* — the CK/CEK
  machine treatment; `ocaml-multicont` (Hillerström) — explicit multi-shot.

**Adopt (v2):** a structured resumption `K_RESUME { Cont* suffix; DoScopeFrame*
scopes; MaskState mask; uint8_t shots }` retaining do-scope frames (the §32.2.13/
.19/.20 prerequisite); one-shot-as-move / multi-shot-as-clone; a tail-resumptive
in-place fast path (§32.2.15) so effectful loops stay constant-depth. This is the
gated `rt-multishot-effects` work.

## 3. Structured concurrency & supervision (validates the shipped scopes)

**Finding.** Trio, Kotlin, Loom, Swift, and Erlang/OTP **converge on one
invariant**: a scope must not exit until every attached child has terminated *and
run its finalizers*. They differ only on failure policy (all-or-nothing
cancel-siblings vs isolating/supervised). The recommended mechanism is precisely
ours: **one scope-exit code path; `KK_UNSCOPE` as a re-entrant park on a per-scope
`live_count` latch reusing the `await` Waiter/park/resume machinery**; finalizers
run under an interrupt mask (Trio "shield" / Kotlin `NonCancellable`); causes
aggregate via the §28 `Cause` tree (`Both`/`Then`).

- Smith, *Notes on structured concurrency, or: Go statement considered harmful*
  (2018) + Trio cancel-scopes — the nursery invariant.
- Kotlin structured concurrency (`coroutineScope` vs `supervisorScope`); JVM Loom
  `StructuredTaskScope` (`ShutdownOnFailure`/`OnSuccess`); Swift SE-0304 task trees.
- Erlang/OTP `supervisor` — one/all/rest-for-one, restart intensity; reversed-start
  termination, original-order restart.

**Status:** the shipped increment implements exactly this latch-drain model
(`shutdownScope`, `scope.c`). **Refinement noted:** run finalizers fully masked
(currently the unwind clears the pending interrupt; full Trio-shield masking is a
small follow-up). **std.supervisor** is a Kappa library over
`forkIn`/`interrupt`/`await`/`monitor`/`now_monotonic` (not runtime code).

## 4. Work-stealing scheduler (drives v3 perf — replace the mutex+condvar queue)

**Finding.** The state of the art is a **per-worker Chase–Lev deque** (owner
push/pop bottom, thieves steal top) + a shared global/injection queue for overflow
and reactor wakeups, with a throttled park/unpark protocol. Adopt the **C11
memory-ordering** version proven correct for weak memory models (the only seq_cst
sync is one fence in `pop`). Topology: bounded deque (256, pow2) + a `runnext`/LIFO
slot + a mutex-protected global queue used *only* for overflow and injection
(Go/Tokio). Throttle wakeups with an atomic spinning-worker count (Go
`nmspinning`); park with EMPTY/PARKED/NOTIFIED (Tokio `park.rs`). The reactor is an
**injector** (Go `injectglist`): it batches woken fibers to the global queue and
unparks at most one idle worker — never runs fibers itself.

- Le, Pop, Cohen & Zappa Nardelli, *Correct and Efficient Work-Stealing for Weak
  Memory Models* (PPoPP 2013) — the C11 Chase–Lev deque + exact memory orders.
- Taskflow `work-stealing-queue/wsq.hpp` — a standalone, copyable C++ extract.
- Lerche, *Making the Tokio scheduler 10× faster* + Tokio `park.rs`.
- Go runtime `proc.go` (`runqput`/`runqsteal`/`injectglist`/spinning) — Vyukov et al.
- Cilk work-first principle — keep all scheduling overhead off the common path.

**Adopt (v3):** replace `rt->rq_*` (the correct-but-coarse mutex+condvar FIFO) with
this topology. The v1 queue is deliberately the proven-correct shape first; this is
the throughput upgrade.

## 5. GC under M:N green threads (validates rt->all; one near-term tweak)

**Finding.** The invariant for any green-thread runtime over a stop-the-world GC:
**every suspended fiber's live state must be reachable from a root that does not
depend on a worker's C stack** (a parked fiber has no thread). We get this right by
heap-reifying the continuation into the `Fiber` and rooting every not-yet-DONE
fiber in `rt->all` — structurally the same choice as GHC (heap `TSO`/`STACK`
objects) and Go (per-`G` scanned stacks); the only difference is conservative vs
precise scanning. Second invariant: a thread blocked in a foreign call should tell
the collector via `GC_do_blocking` so STW need not wait on it.

- bdwgc `gc.h` (`GC_do_blocking`/`GC_call_with_gc_active`),
  `pthread_stop_world.c`; Boehm, *Conservative GC Algorithmic Overview* and
  *GC scalability* — parallel marking, thread-local alloc.
- GHC RTS scheduler commentary (capabilities, heap-allocated stacks); Go runtime
  (per-G stack scanning).

**Adopt now (low risk):** enable parallel marking (`GC_MARKERS=NPROC`) +
thread-local alloc in the Boehm build. **Adopt with care:** `GC_do_blocking`
around the reactor's `uv_run` *poll* — but the reactor's libuv callbacks
`GC_MALLOC` (run queue nodes), so the whole `uv_run` cannot be wrapped naively;
either wrap only the poll or make callbacks `GC_call_with_gc_active`. Currently
Boehm stops the reactor via Mach/signals even mid-`uv_run` (proven by the passing
timer tests), so this is a pause-latency optimization, not a correctness fix.
**Adopt (v3):** a real `krt2_safepoint` budget/poll so compute-bound non-allocating
fibers reach STW promptly — also the safepoint primitive for the future precise
collector (the eventual Perceus/bespoke-GC direction).

---

## One-line takeaways

| Area | Borrowed from | Status |
|------|---------------|--------|
| Do-kernel CPS lowering | Appel/Reynolds/Danvy; Rust/Kotlin/C# async | v2 (designed, INTEGRATION.md) |
| Effects = evidence passing | Xie & Leijen; OCaml 5; libmprompt | already the model; multishot = v2 |
| Scope-drain latch + masked finalizers | Trio/Kotlin/Loom/Swift/OTP | **shipped** (matches the literature) |
| Heap-reified suspendable finalizers | GHC heap stacks; the CPS pitfall | **shipped** (completion channel) |
| C11 Chase–Lev work-stealing | Le/Pop/Cohen/Nardelli; Go; Tokio; Cilk | v3 |
| Rooted parked fibers + `GC_do_blocking` | bdwgc; GHC; Go | rt->all shipped; reactor tweak pending |
