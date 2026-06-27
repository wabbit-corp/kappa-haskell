# Runtime Efficiency Review (kappart2)

Five hot-path reviews of the native M:N runtime (`runtime/rt.c`, `reactor.c`,
`scope.c`, `stm.c`, `internal.h`, plus the CPS lowering in
`src/Kappa/Backend/C.hs`). The reviews were read-only; this document
consolidates them, leads with the one **correctness** bug that gets implemented
next, then ranks the genuine efficiency wins and honestly separates them from
premature optimization.

The grounding fact throughout: **the bench says allocation, not indirection, is
the dominant cost.** Fork is ~832 B/op and the fork/await ping-pong is ~704 B/op;
Go reaches the same workload at ~128 B/op because it *reuses* pooled `g` structs.
Nothing in this runtime is the wrong *size* — the problem is that almost nothing
is *recycled*. Every finding below is a variation on that theme.

---

## 1. Load-bearing: the repeated-`krt2_run_main` crash

### Symptom
Calling `krt2_run_main` repeatedly in one process deterministically crashes with
`kapp: applying a non-function value` around the **60th–80th** call. The
documented "`run_main` is reusable" contract (exercised only twice in
`tests/scope_drain.c`, well below the GC threshold) is broken at scale.

### Root cause: GC under-retention triggered by the shutdown→reinit cycle
This is **not** a logic bug in `deliver()` and **not** a single bad Boehm call.
It is a use-after-free of a still-live, root-reachable continuation chain,
introduced specifically by the teardown+reinit combination. Proven by bisection:

| Probe | Result | Conclusion |
|---|---|---|
| `GC_DONT_GC=1`, 6000 calls | clean | GC is necessary to trigger it |
| single `run_main`, 300k binds, aggressive GC | clean | steady-state rooting is correct |
| big run-1 then 2000 trivial runs | clean | run-1's heap is not the poison |
| run N+1 builds its own continuation chain after ≥1 prior shutdown | **crash** | the shutdown→reinit cycle is the trigger |

At the crash, `deliver()`'s `KK_BIND` arm reads `c->a` (the bind closure) as a
**freshly-reused** heap box — observed as `K_INT(0)`, `K_CTOR`, and `K_DBL`
across runs — while the owning fiber is still the head of `g_rt->all`. So a
live, rooted `Cont`/`KEnv`/`KClo` was reclaimed early. `GC_PRINT_STATS` shows
collections #3/#4 (in the run-2 region) freeing ~480 KB including the live
chain, immediately before the fault.

Crash site confirmed in source:
- `runtime/rt.c:866` — `f->k = c->next; f->cur = kapp(c->a, v);` (the `KK_BIND` deliver arm)
- `runtime/rt.c:1421` — `krt2_shutdown(rt)` at the end of every `run_main`
- `runtime/rt.c:1436` — `if (g_rt == rt) g_rt = NULL;` — clears the runtime so the next call rebuilds from scratch
- `runtime/rt.c:1395` — `Rt *rt = g_rt ? g_rt : krt2_new(0);` — the rebuild path

The un-reset state that makes teardown+reinit unsafe is concentrated in
`krt2_shutdown` / `krt2_new` + `krt_init`: re-`GC_INIT`,
re-`GC_set_all_interior_pointers(0)`, re-`atexit`, re-`GC_allow_register_threads`,
plus the never-destroyed pthread mutex/cond objects. Each of these was reproduced
*in isolation* and is clean — the fault is the specific combination.

### Recommended fix: make the runtime persistent across `run_main`
Do **not** clear `g_rt` and do **not** join+rebuild workers/reactor/`uv_loop`
each call. Init once (lazily on first `run_main`), keep the worker pool and
reactor alive, and per call only:
1. build the main fiber + root scope,
2. run it to completion,
3. drain the root scope —

leaving `g_rt`, `rt->all`, the loop, and the thread pool intact. The single
persistent-runtime probe (300k binds, one run) is provably crash-free, so reusing
one initialized `Rt` + worker pool + loop sidesteps the cross-run GC corruption
**by construction**. This is also strictly *cheaper* — it removes the per-run
thread create/join churn (finding S-5) and the repeated `krt_init` side effects
(finding S-4).

If a true teardown is ever required, it must add an explicit quiescence barrier
(force a full GC with no in-flight workers, `pthread_*_destroy` all
mutexes/condvars, verify the `GC_thread` table is empty) before rebuilding — but
persistence is strictly cheaper and re-entrant, so prefer it.

---

## 2. Ranked top inefficiencies (whole runtime)

Ranked by hot-path impact, grounded in the bench baseline that **allocation is
the dominant cost**. The top three are the ones worth doing; everything below is
real but second-order, and the bottom group is explicitly *not* worth touching
yet.

| # | Inefficiency | Where | Why it ranks here |
|---|---|---|---|
| 1 | **No fiber / Cont / KEnv pooling** — every fork is fresh GC traffic (208 B Fiber + 40 B Cont + KEnv cells + 24 B Waiter), nothing recycled | `rt.c` fork + CPS path | This *is* the 832 B/op fork cost. The single biggest lever; the pre-Perceus version of the deferred Stage-5 reuse. |
| 2 | **Per-enqueue `RQNode` (16 B) and per-park `Waiter` (24 B) allocations** on the scheduler hot path, each holding only a `Fiber*` already rooted in `rt->all` | `rt.c:359`, `rt.c:595/634` | ≥2 RQNode + 1 Waiter per fork/await round-trip. Removable to **zero** via an intrusive next-pointer / embedded Waiter in the Fiber. Cheapest high-leverage win. |
| 3 | **OP / STM / CPS action nodes never pack** — every node is a 48 B `K_CTOR` + a separate args array (64 B for a 2-arg bind), and loop/retry bodies rebuild the whole tree per iteration | `kappart.c:331`, `rt.c:59`, `stm.c`, `C.hs cpsItems` | OP tags ≥ `0x40000000` fail `kctor_tagid_packs`, so they *always* box. The big structural fix is global unboxing (Phase 2); the cheap-now win is a single inline `{tag,a,b}` OP node (1 malloc, not 2). |
| 4 | **Per-fiber/promise/scope `pthread_mutex_t` (64 B), init on the hot path, never destroyed** — guards only cold termination edges | `rt.c:421/607`, `scope.c:79` | 64 B of zero-payload weight per object (73% of a Promise) + an init syscall per fork; zero `pthread_mutex_destroy` anywhere. Replace with a 1-word spin/futex or CAS handshake. |
| 5 | **STM journal allocated fresh per transaction and re-run from scratch on every conflict** | `stm.c:69/177/215` | Bites exactly under the multi-writer contention STM exists for; the journal should live on the Fiber and reset, not realloc. |
| 6 | **One global mutex (`g_stm`) serializes all STM commits/parks/unparks**, with thundering-herd wake of every parked tx on a popular-TVar write | `stm.c:45/182/198` | Caps commit throughput at one core regardless of TVar disjointness. TL2-style striped version-locks are the standard fix. |
| 7 | **Single global FIFO run queue** (`rq_lock`) — all workers contend per push and per pop | `rt.c:361`, `internal.h:300` | Latent at the bench's 1-worker config; the next bottleneck once allocation is pooled. Chase-Lev per-worker deques are the documented upgrade. |
| 8 | **`krt2_pure(...)` re-box on every wake** (64 B) — the resume value round-trips through a fresh OP node the worker immediately decodes | `rt.c:486/621`, `scope.c:133` | Unit-resume paths can use a cached singleton; a one-liner. |
| 9 | **Reactor timer churn** — `uv_timer_init/start/close` + malloc per `sleepFor`, `io_lock` re-taken per drained node | `reactor.c:33/85/44` | Only the timer/IO path, not the core loop; hot for sleep/timeout-heavy code. |

### Honest scope notes
- **#1–#4 are the real wins.** They are on the actual fork/await hot path the
  bench measures, and #1/#2/#4 are removable to near-zero without touching the
  value representation.
- **#5–#7 do not bite at "one TVar / one worker / low contention"** — they bite
  precisely under the concurrency these subsystems exist to handle. Worth doing,
  but driven by a contended workload, not the current bench.
- **The cold findings below are premature optimization** at expected scale and
  are listed only so a future reader doesn't re-discover them as "bugs": the
  `kfgn` handle box (#S-3 in sync), the `shutdownScope` snapshot array, the
  `FinSeq`/kick node, the `stm_unpark` fast-path branch (which is *correct as
  written*), and lazy `ExitStack` allocation (the `C.hs hasScope` gate already
  keeps non-defer blocks off this path).

---

## 3. Per-subsystem findings

Severity is relative to the bench: **hot** = on the measured fork/await/commit
hot path; **warm** = real per-op heap traffic, secondary to value boxing;
**cold** = correct-and-fine at expected scale, listed for completeness.

### 3.1 Fork-lifecycle + run-main lifecycle (`rt.c`, `reactor.c`, `internal.h`)

| Finding | Location | Cost | Sev | Cheaper design |
|---|---|---|---|---|
| **run_main re-entrancy crash** — GC under-retention from shutdown→reinit; `deliver()` reads a reused box as the bind closure | `rt.c:1394-1437` (run_main/shutdown), `kappart.c:52-65` (krt_init); surfaces at `rt.c:866` | process crash after ~60-80 calls | **hot** | Persistent runtime: don't clear `g_rt`, keep workers/reactor/loop alive; per call only build+run+drain the main fiber. See §1. |
| No fiber/Cont/RQNode/Waiter free-list — every fork is fresh GC traffic | `rt.c:410` (fiber_new), `358-360`, `1020`, `595/634` | ~832 B/op fork | **warm** | Per-worker SLIST free-list of Fiber/Cont/RQNode, reset-and-reuse on finish/pop. Pre-Perceus Stage-5. |
| Per-fork `pthread_mutex` (64 B) init'd, never destroyed; needed only at await-wakeup | `rt.c:421/607/1368`, `scope.c:79` | 1 mutex init/fork + per-run accumulation | **warm** | Lazy-init only when first awaiter parks, or replace with CAS waiter-list; add `pthread_mutex_destroy` on teardown. |
| `krt_init` not once-guarded; re-runs `GC_INIT`/`GC_set_all_interior_pointers(0)`/`atexit` per `krt2_new` | `kappart.c:52-65`, called `rt.c:1361` | repeated global GC re-config + unbounded `atexit` | **warm** | `pthread_once` guard; with persistent runtime it runs exactly once. |
| Per-run worker+reactor create/join + fresh `uv_loop` per call | `rt.c:1411-1413/1431`, `reactor.c:65-76` | ~13 create/join + 1 loop setup/teardown per run | **warm** | Keep the pool + reactor + loop alive across runs (persistent runtime). |
| `rq_push` GC_MALLOCs a 16 B RQNode per enqueue; single global FIFO | `rt.c:358-366/387-405` | 16 B/op + one global-lock acquire per enqueue | **warm** | Intrusive `rq_next` on the Fiber (zero alloc — a fiber is in the queue at most once) + Chase-Lev deques. |

### 3.2 CPS / continuation / KEnv allocation (`rt.c` CK-machine, `C.hs cpsItems`)

| Finding | Location | Cost | Sev | Cheaper design |
|---|---|---|---|---|
| Action nodes are boxed `K_CTOR` + separate args array; OP tag never packs | `rt.c:59-64`, `kappart.c:331-367`, `kappart.h:343` | 64 B/bind node (2 mallocs) | **warm** | Dedicated inline `{tag,a,b}` OP-node struct: 1 malloc, no args-array indirection. Drop-in via existing accessors. |
| Per suspending bind: fresh `kclo` (48 B) + `KK_BIND` Cont (40 B) + KEnv cell (16 B), none reused | `C.hs:3392-3396/3533-3549/3716-3720`, `rt.c:865/1019-1022` | ~104 B/bind atop node cost | **warm** | Per-worker free-list for Cont + KEnv (each consumed once); Perceus in-place reuse later. One-shot, single-owner — not correctness-sensitive. |
| Loop body action-tree rebuilt every iteration (`kapp` re-runs the builder) | `rt.c:866/877-879/1166-1172`, `C.hs:3451-3455` | O(body-size) alloc per iteration where O(1) reuse is possible | **warm** | Cache the built body node on the `KK_LOOP` frame (`aux` is free) and re-deliver; only the carried KEnv cells change. |
| `rq_push` 16 B RQNode per enqueue + global FIFO (scheduler-side dup of 3.1) | `rt.c:358-366` | 16 B/enqueue + global mutex round-trip | **warm** | Free-list / intrusive link; Chase-Lev deques. |
| `do_await` GC_MALLOCs a 32 B Waiter per park (fiber parks on ≤1 list) | `rt.c:595-597/634-636` | ~32 B/park | **cold** | Embed one inline Waiter in the Fiber, link that onto the target's list. |
| `OP_DOSCOPE` eagerly allocs ExitStack + `KK_DOSCOPE` Cont even with zero defers | `rt.c:437-441/1137-1142/697-717`, `C.hs:3358-3361` | ExitStack + 40 B Cont per wrapped scope | **cold** | Mostly fine — `hasScope` gate already excludes non-defer blocks. Residual: lazy ExitStack on first `OP_DEFER`. |

### 3.3 Scheduler / reactor (`rt.c`, `reactor.c`, `internal.h`)

| Finding | Location | Cost | Sev | Cheaper design |
|---|---|---|---|---|
| Per-enqueue RQNode GC alloc; ≥2 enqueues per fork/await | `rt.c:358-366`; callers `576/486/621/1058` | 16 B/enqueue + GC scan | **hot** | Intrusive `_Atomic(Fiber*) rq_next` in the Fiber — zero-alloc enqueue (status CAS gates single-queue-membership). |
| Per-park Waiter GC alloc | `rt.c:595/634`, `internal.h:203` | 24 B/park + GC scan | **hot** | Embed Waiter intrusively in the Fiber (parks on ≤1 list on the fork/await path). |
| Single global FIFO run queue, one mutex, no work-stealing | `internal.h:300-304`, `rt.c:361-404` | one global lock acquire per push/pop (≥3 per op); caps multi-core scaling | **warm** | Per-worker Chase-Lev deques (lock-free owner side); or sharded FIFOs as an intermediate step. Latent at 1 worker. |
| Per-fiber `pthread_mutex_init` per fork, never destroyed | `rt.c:421/607`, `scope.c:79` | one init/fork; costlier on macOS where the bench runs | **warm** | Pool Fibers (reuse the initialized mutex) or replace the termination handshake with the existing CAS. |
| Reactor per-sleep churn: GC IoReq + malloc SleepTimer + `uv_timer_init/start/close` + `uv_async_send`; `io_lock` per drained node | `reactor.c:33-40/85-94/44-55` | timer registration + lock-per-node per sleepFor | **warm** | Pool `uv_timer_t` (stop+restart, not init/close); free-list IoReq; drain by swapping head/tail under one lock. |
| `cond_signal` issued while still holding `rq_lock` (hurry-up-and-wait) | `rt.c:361-365` | one redundant wake/re-block per cross-worker wakeup under contention | **cold** | Signal after `unlock`; enables wait-morphing on glibc. Do opportunistically when reworking the queue. |

### 3.4 STM (`stm.c`, OP_ATOMICALLY in `rt.c`)

| Finding | Location | Cost | Sev | Cheaper design |
|---|---|---|---|---|
| Per-transaction journal heap-allocated fresh and discarded on every retry | `stm.c:69-89/177/215-218` | ~2 GC_MALLOC/tx min + reallocs; ~320 B re-allocated per conflict on a 10R/10W tx | **hot** | Cache the Journal on the Fiber; reset `nr`/`nw` to 0, retain `capr`/`capw` across runs and retries. |
| Entire STM action tree is boxed `K_CTOR`, rebuilt per re-run (`kapp` materializes subtrees) | `stm.c:107-157/142/176-225`; `internal.h:135` vs `kappart.h:396` | 48 B/node re-allocated per retry; k conflicts pay k× | **hot** | Mostly the global-unboxing milestone. STM-specific: on a watcher wake, skip re-run if no read TVar's version changed; memoize the pure prefix. |
| One global mutex (`g_stm`) serializes all commits/parks/unparks across all TVars | `stm.c:45/182/201/208/223/164/170` | commit throughput ceilings at 1 core; lock held across `nw` GC_MALLOCs + watcher splice | **hot** | TL2-style striped per-TVar version-locks via `g_tick`; allocate new VBoxes *outside* the lock, lock only to swap pointers + splice. |
| Popular-TVar write wakes EVERY parked tx (thundering herd); each re-runs and most re-park | `stm.c:198-202/162-171/215-223` | O(parked) wakeups + O(parked) full re-runs + 2×O(parked) global-lock acquisitions per write | **hot** | Condition-narrow the wake (per-waiter TVar); keep the parked journal so re-run validates read-set first and re-parks without re-running; striped locks remove the global contention. |
| Journal is a linear-scan list: `j_read`/`j_newer_write`/validation are O(n), install O(nw²); duplicate reads stored k× | `stm.c:90-100/184-188/210-218` | O(n²) for a tx of size n | **warm** | Keep the list for small n (<8 — faster than a hash); switch to an open-addressed hash keyed by TVar address past a threshold. |
| `stm_unpark` called unconditionally at every `atomically` entry | `stm.c:162-175` | one predictable branch on the no-park fast path | **cold** | **No change** — the `stm_nreads==0` early-return is the right design. |

### 3.5 Sync / promise / scope (`rt.c`, `scope.c`)

| Finding | Location | Cost | Sev | Cheaper design |
|---|---|---|---|---|
| Every Fiber/Promise/Scope embeds a 64 B `pthread_mutex_t`, never destroyed; acquired only on cold edges | `internal.h:221/252/283`; init `rt.c:421/607`, `scope.c:79` | 64 B/object (73% of a Promise); undestroyed-mutex retention | **warm** | 4-byte spin/flag lock or a lock-free single-assignment Promise cell (CAS 0→1, Treiber waiter stack). Removes 60 B/object + the leak. |
| Wake/resume re-boxes the value in a fresh `krt2_pure(...)` OP node (64 B), immediately decoded and discarded | `rt.c:486/621`, `scope.c:133`; resume `rt.c:592/631` | 64 B/woken waiter; 64×N on broadcast | **warm** | (a) Cache one static `OP_PURE(unit)` singleton for the Unit-resume paths. (b) Have `krt2i_wake` inject the raw value into the continuation, eliding the node. |
| `OP_DOSCOPE` unconditionally allocs ExitStack (16 B) + `KK_DOSCOPE` Cont (40 B); all of finally/onExit/bracket/withScope lower through it | `rt.c:1137-1143/437-441`, lowered from `rt.c:140/158-177` | ~56 B/do-scope before any defer, +≥32 B on first defer | **warm** | Lazy ExitStack: store nullable on the Cont (`aux=NULL`), create on first `OP_DEFER`; `begin_finseq` already short-circuits an empty stack. |
| Non-empty finseq drain allocs `KK_POPMASK` Cont + FinSeq + a `krt2_pure(unit)` kick node | `rt.c:697-717/453/715` | ~144 B per finalizer-bearing exit, on the normal success path too | **cold** | Call `deliver(rt,f,unit())` directly instead of a kick node; reuse the cached Unit singleton; fold FinSeq fields into the `KK_FINSEQ` Cont slots. |
| `shutdownScope` GC_MALLOCs a `Fiber*[n]` snapshot under the scope lock | `scope.c:147-173` | 8×n B scratch per shutdown | **cold** | Fine at expected scale (handful of children). Stack buffer with heap fallback only if scopes ever hold thousands. Lock-discipline must be preserved. |
| Each foreign handle allocs the struct + a separate 48 B `kfgn` KValue box | `rt.c:608/1049/1052`, `scope.c:88/139`, `kappart.c:428` | 48 B/handle (35% of a 136 B newPromise) | **cold** | Inherent to the boxed-handle ABI; a tagged-pointer `K_FGN` is the UNBOXING Stage-1+ direction. Part of the boxing problem, not a separable bug. |

---

## 4. Bottom line

1. **Implement the persistent runtime first** (§1) — it fixes the `run_main`
   crash *and* deletes the per-run thread/loop churn and repeated `krt_init`.
2. **Then pool the hot-path allocations** — intrusive RQNode/Waiter links (zero
   alloc), Fiber/Cont/KEnv free-lists, and a 1-word lock replacing the 64 B
   per-object `pthread_mutex`. These attack the 832 B/op fork cost directly.
3. **The inline OP-node** (`{tag,a,b}`, one malloc) is a cheap real win available
   now, ahead of the larger global-unboxing milestone that the OP/STM node boxing
   ultimately depends on.
4. **STM striped locks + per-fiber journal reuse** are real but contention-driven;
   schedule them against a multi-writer workload, not the current bench.
5. **Leave the cold findings alone** — they are correct and fine at expected
   scale; touching them now is premature optimization.
