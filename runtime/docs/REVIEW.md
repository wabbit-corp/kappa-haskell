# Adversarial design review — findings and resolutions

An 8-lens adversarial review (conformance, GC/parallelism, CK-machine, libuv,
STM, structured+multishot, alternative-architecture, ABI/build) was run against
[`DESIGN.md`](DESIGN.md) and [`include/kappart2.h`](../kappart2.h) before any
core code was written. **Verdict: proceed with fixes.** The architecture
(stackless CK-machine + M:N work-stealing + single libuv reactor + Boehm GC) is
sound; no reviewer found a materially better alternative (the steelman of
stackful coroutines, per-worker loops, scheduler-as-effect, and GHC-RTS-reuse all
concluded *keep the design*). This file records every blocker/major and how the
design was changed to close it. Section numbers (§) are DESIGN.md sections.

## Scope decision: what v1 is, honestly

A reviewer verified (`C.hs:3043-3048`) that the backend's do-kernel lowers every
**non-tail** bind to inline straight-line C (`KValue *bind_x = krun_io(action);`),
so the continuation after a non-last `await`/`sleep`/STM-retry is a C return
address, not a heap object. Making *existing compiled programs* suspend at every
IO boundary therefore requires a **codegen rewrite** of `compileItems` /
`emitRunIOValue` (emit `krt2_bind(action, kclo(cont_fn, env))` per non-tail leg),
not a builder retarget. That rewrite is **v2** (backend integration, §17).

So the v1 boundary is:

- **v1 (this package):** the standalone runtime — the CK-machine, scheduler,
  reactor, blocking lane, and all primitives — is correct and proven by C
  harnesses that build `krt2_bind`/`krt2_then` action trees directly (exactly the
  shape the v2 codegen will emit). v1 does **not** make already-compiled
  do-blocks suspend; it proves the runtime mechanism that v2's codegen will feed.
- **v2:** the `C.hs` CPS rewrite + Driver wiring + the capability flip.

This is stated up front so the "fiber suspends at any IO boundary" claim is scoped
to "any IO boundary *expressed via the CK-machine builders*," which is what the
runtime controls.

## Capability staging (§3, §19)

v1 advertises **five** of six: `rt-core`, `rt-parallel`, `rt-shared-stm`,
`rt-blocking`, `rt-atomics`. **`rt-multishot-effects` is staged to v2** behind a
real gate, because (a) the static escape restriction it relies on (§32.2.20) is
**not implemented** — `Usage.hs:checkMultishotCapture` tracks only
borrowed/quantity-1 captures, with no notion of a `defer`/`using` obligation in
the captured suffix (finding M3/m1); and (b) coupling the common one-shot path to
multishot machinery risks regressing it. The pure `__EffOp` closure encoding
(already multishot-capable for *pure* effects) stays; the full §32.2.16
multishot-with-IO-segments contract is not claimed until the per-use-clone
protocol, the Eff/CK split, the §34.4.1 doc, and a native reachability gate
(`E_BACKEND_INCAPABLE`, currently missing at `C.hs:276`) all land. Each flag flips
only when its evidence exists (§27.6 forbids advertising an unbacked flag).

## Blockers

| # | Finding | Resolution |
|---|---------|------------|
| **B1** | Do-kernel not CPS-converted (`C.hs:3043-3048`): non-tail binds are inline `krun_io`, so only a do-block's last action can suspend. §17.4 mislabeled a multi-function codegen rewrite as a builder retarget. | Scoped to **v2** (above). §17 rewritten to name the three lowering surfaces (`krun_io` inline, `kpf_io_*`, the do-kernel `KItem` lowering) and state all three move to `Cont` frames; v1 runtime is proven by harness-built `krt2_bind` trees. |
| **B2** ✅ | Abrupt completion (`Break`/`Continue`/`Return[L]`, §18.8/§30.2.2.6) has no channel in the step loop (only VALUE/FAIL/BLOCK/CEDE), so `do { defer cleanup; break }` never runs `cleanup`. | **SHIPPED.** A unified `unwind(reason)` with `RK_NORMAL/FAIL/RETURN/BREAK/CONTINUE/INTERRUPT`; a **`KK_DOSCOPE`** frame whose exit-action stack runs LIFO via a suspendable **`KK_FINSEQ`** frame on *every* exit, then re-propagates the reason; `KK_LOOP` consumes break/continue; `KK_CATCH` consumes fail. Heap-reified so finalizers survive a cross-worker resume (RESEARCH.md §1 pitfall). `test/completion.c` green. |
| **B3** | Lost-wakeup family: worker-park, `uv_async` submission, STM-retry park, generic park/unpark — each an unspecified deadlock. | **One CAS park/unpark protocol** (§6.2), specified once and referenced everywhere: a fiber's `status` is the CAS arbiter; a *sticky wake-pending* flag a parker checks before sleeping. Worker idle uses a seq-counter futex (`inject; fetch_add(seq,release); wake` ‖ `load(seq,acq); try_work else futex_wait(seq,s)`). `uv_async` uses unconditional-send + drain-to-empty with an acquire recheck. STM retry **re-validates under the commit lock, then inserts onto watcher lists and parks, all under the lock**. (§6.2, §7.2, §11.) |
| **B4** | Parked/runnable fibers can be GC-collected mid-flight: the fiber table is weak, and the only holders are libuv-malloc memory (`uv_timer_t->data`, `IoReq`, `uv_work_t.data`) and the malloc-backed Chase–Lev array — none scanned by Boehm. | The runtime keeps an **explicit `Rt`-rooted strong set** of every parked/in-flight `Fiber*` (added at park, removed at wake). The deque backing array, global injection ring, `IoReq` pool, and reactor MPSC nodes are **`GC_MALLOC`'d** (scanned) or shadowed by a GC-rooted `Fiber*` array. §16 rewritten: suspended-fiber liveness is an explicit root set; **libuv memory is not a GC root**. |
| **B5** | KValue allocation on libuv threadpool threads is UB — libuv creates those threads; `GC_register_my_thread` is never called, so a collection won't scan their stacks. | §7.4 rewritten: **forbid KValue allocation on pool threads** — run the foreign call there, marshal *raw C* results back, box on the reactor/worker. For `blocking { arbitrary Kappa }`, `work_cb` **self-registers** via `GC_get_stack_base`/`GC_register_my_thread` (guarded for thread reuse, no unregister), relying on Boehm's documented foreign-thread self-registration. |
| **B6** | Timeout/race tie-break (§18.1.6/§32.2.8) has no mechanism; the timer wake and the io wake race onto the global queue with no io-wins/left-wins bias. | A **single-assignment resolution cell** with priority, resolved **on the reactor thread**: io/left claims first; timer/right claims only-if-unclaimed (CAS where the loser cannot overwrite). For `timeout`, convert to `Fail Timeout` only when the action's terminal `Exit` is itself the `TimedOut` interrupt (mirror `Interp.hs:exitTimedOut`). **All** libuv handle ops — start *and* `stop`/`close` — are reactor-confined; cancellation is an `IoReq` through the async path. (§7.4a.) |

## Selected majors (folded into the design / implementation)

- **M1/M2/D7 — Eff vs IO continuations.** Do **not** unify. The "immutable shared
  `Cont`" claim was false: `Cont.aux` points at a mutable shared `Scope*`/
  `ExitFrame*`, so a double-resume of `do { defer print D; op }` would print `D`
  *once*, violating §32.2.19. Keep the pure `__EffOp`/closure encoding for *effect*
  resumptions; `Cont` carries *only* IO control. Where a handler's carrier is IO,
  pure Eff reduction yields an IO action the CK-machine then drives — the two never
  share a continuation object. The §34.4.1 representation doc describes the
  **closure graph**, not `Cont` frames. (Enables the v2 multishot gate.)
- **M4 — scope-exit must park.** `KK_UNSCOPE` is a **re-entrant parking point**:
  send `ScopeShutdown`, register the parent on each child's waiter list, return
  `BLOCK`, re-enter the *same* frame on wake and recheck remaining children, run
  the scope's `KK_POPEXIT` actions only when all children are `F_DONE`; the wait
  is masked (§32.2.12). Busy-waiting would deadlock at `N=1`. (§9.1.)
- **M5 — pure stack-safety.** Deep non-tail pure recursion inside one IO step
  overflows the C stack and is an interruption blind spot. Stated explicitly:
  pure stack-safety is the `K_BOUNCE` trampoline (tail) + codegen `krt2_safepoint`
  at back-edges; non-tail-recursive pure SCCs exceeding the C stack must be
  lowered stack-safely or rejected (native analog of the §27.5A.4 safe-point
  obligation). (§6.4.)
- **M6/M7/M15/D10 — value-layer parallelism.** Singletons
  (`kint_cache`/`the_unit`/`the_true`/`the_false`) are **eagerly pre-populated in
  `krt2_new` before workers start** (closes the lazy-init store-store race —
  `kappart.c:99-103,247-289`). Ordinary `K_REF`/`var` slots are accessed via
  **relaxed atomics** (`_Atomic(KValue*)`), giving §32.2.10's "no ordering, no
  tearing" portably (not the "aligned 64-bit" hand-wave). `kappart` and `kappart2`
  **must** be compiled with identical `-DGC_THREADS -pthread`; a build-time
  `_Static_assert`/runtime `GC_get_parallel()` check fails closed on mismatch. The
  linked GMP must be the reentrant build. "Reuse the value layer *unchanged*" is
  downgraded to "reuse with startup pre-population + atomic ref accessors."
- **M16-M19/D8 — STM correctness.** `readTVar` samples `(value,version)`
  **atomically** (seqlock / single-pointer snapshot), not two independent loads.
  `orElse` **accumulates the left branch's read-set** (keep `l`'s reads, roll back
  `l`'s writes) so a later write to a TVar `l` read wakes the parked `orElse`.
  Commit is bracketed in an **implicit mask** (validate→install→bump→wake is
  uninterruptible, §32.2.9); a pre-commit interrupt is an attempt-abandon point.
  `newTVar`-in-txn is a **txn-local write-set cell** installed with a defined
  initial version on commit, dropped on abort. (§11.)
- **M8 — masked unwind.** The unwind machinery is masked, but each finalizer body
  may `restore`/`poll` and, if then interrupted, contributes its own `Interrupt`
  cleanup cause composed via `Then`. "Unwind is masked" ≠ "finalizer bodies cannot
  restore." (§8.)
- **M10/M20/M23/D16 — small correctness specs.** Each attached child carries an
  **acked** bit set by `await`/`join`/`awaitMonitor` (not by `monitor` creation);
  at `KK_UNSCOPE`, un-acked `Fail`/`Defect` children compose `Defect
  UnhandledChildFailure` with `Both` in creation order before finalizer `Then`
  causes (§32.2.4). `completePromise` **wakes every** waiter (release published
  before any resumed step). `FiberRefMap` is an **immutable copy-on-write** map so
  parent/child updates are independent after the fork snapshot (§18.1.7).
- **M11/M12/D6 — reactor confinement + shutdown order.** All libuv handle ops are
  reactor-confined (cancellation submitted as `IoReq`s; `uv_close` added to
  teardown). Shutdown order: drain scopes → await/drain the blocking lane (do
  **not** `uv_stop` while pool work is outstanding) → async-signal the reactor
  *from itself* to `uv_close` all handles and stop → join workers. (§7.5.)
- **M13/D13 — determinism vs the -N1 oracle.** `rt-parallel` breaks byte-exact
  `assertRunStdout` against the `-threaded -N1` `Interp.hs` oracle. A
  **deterministic test mode** (`KAPPA_RT_WORKERS=1` + documented cooperative order,
  or a single ordered output sink) is used for stdout assertions; true-parallel
  behavior is validated by order-insensitive/set assertions and TSan. (§1, §17.6.)
- **M14/D12 — build/driver.** The runtime is ~14 TUs; it cannot ride a
  `hostBinding`/`pkgConfig` entry (`krt2_*` are codegen intrinsics, not FFI
  symbols). Ship **`libkappart2.a`**; the Driver links it + `-luv` + threaded
  `-lgc` + `-pthread` **unconditionally** when targeting kappart2, with libuv
  discovered via `pkg-config` as a Driver-owned dependency. No `kappa.build.kp`
  entry exists for the runtime itself. (§17.1, §20.)
- **M22/D14 — action-node representation.** Scheduler ops are **reserved
  primitive names** the step loop recognizes (reusing the existing string-dispatch
  and matching the oracle's `__forkRun`/`__awaitFiber`), and runtime handles are
  **`K_FGN` boxes** — so **no new `KTag`** is added. The header's "no KTag change"
  stands; DESIGN.md §17's stray "new `K_FIBER` tag" line is removed. (§5.3.)
- **m3 — harness builder API.** A small continuation-builder API
  (`krt2_h_lam`/`krt2_h_bind`/`krt2_h_seq` + an env builder) is added so harnesses
  can express `fork;await;print` without hand-writing closures, making the
  "testable before integration" claim real.

## Majors deferred with the multishot capability (v2)

M3 (static escape check), M9 (interrupt mid-multishot-segment, KK_HANDLE in
unwind), and the per-use clone protocol travel with `rt-multishot-effects` and are
out of v1 scope. The pure-effect path remains correct; only the
multishot-with-IO-segments contract is deferred.
