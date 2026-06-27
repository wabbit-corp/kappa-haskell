# kappart2 Runtime Spec-Coverage Map

Conformance of the native **kappart2** runtime (C backend primary, LLVM backend
secondary) to the spec's runtime requirements: §18.1 (fibers / structured
concurrency / STM / effect handlers), §29 (std runtime modules), §32.2 (runtime
state machine), §27.6 / §34.3.3 / §34.4 (capability profiles and lowering
obligations).

Status legend: **IMPLEMENTED** (realized + codegen-reachable), **PARTIAL**
(present but incomplete / unsound / over-claimed), **MISSING** (absent or dead /
unreachable). Severity: **MUST** / **SHOULD** / **MAY** are spec-normative;
**profile-scoped** is §27.6 latitude (a backend may legally withhold a capability
if it rejects programs needing it).

> Methodology note: presence and wiring were confirmed statically (file:line
> grep + read). Runtime *behavior* is exercised by the C tests under
> `runtime/tests/*.c` but those were not re-run for this map. Items marked
> "exists but untested at native level" are wired and plausibly correct yet have
> no native execution test — they are **not** counted as gaps.

---

## Executive Summary

### Normative-MUST runtime gaps: **11**

Counting distinct MISSING or PARTIAL items at MUST severity, after
de-duplicating the same root cause reported across multiple area audits.
(Several appear in 2–3 audits; the count below collapses them.)

| # | Gap (deduped) | Status | Areas reporting |
|---|---|---|---|
| 1 | **Handler abandonment cleanup** — a one-shot/abortive clause that completes without resuming never drains the captured do-scope's `defer`/`using` (§32.2.20/.21, §18 handlers) | MISSING | effects-stm, state-machine |
| 2 | **Safe-points** — `krt2_safepoint` is a no-op, no codegen emits it; pure loops / scalar fast-path are uninterruptible & unfair (§32.2.5/.6) | MISSING | state-machine, capabilities, std-scheduler |
| 3 | **std.atomic is non-atomic** — correct lock-free `atomic.c` is dead code; prelude lowers `AtomicRef` to a plain `Ref`, RMW/CAS race under parallel workers (§29.1) | MISSING | std-scheduler |
| 4 | **`blocking` is identity** — no offload lane; a blocking body monopolizes a scheduler worker yet `rt-blocking` is advertised (§18.1.11 / §18.1.5 / §29) | PARTIAL | fibers, effects-stm, capabilities, std-scheduler |
| 5 | **std.supervisor is a stub** — restart policies / strategies / intensity / cause semantics all absent (§29.2) | MISSING | std-scheduler |
| 6 | **`sandbox`/`unsandbox` no native lowering** — declared + in oracle, rejected `E_BACKEND_UNSUPPORTED` on native (§18.1.2) | MISSING | effects-stm |
| 7 | **`Alternative STM` / `orElse` unreachable** — runtime `STM_ORELSE` exists but no instance binds it; the `Monoid (STM a)` stub drops the right branch (§18.1.13) | MISSING | effects-stm |
| 8 | **`fiberId`/`currentFiberId` unreachable** — runtime ops exist, no prim, no codegen (§18.1.10) | MISSING | fibers |
| 9 | **Fiber labels** — `get/set/locallyFiberLabel` entirely absent (§18.1.10) | MISSING | fibers |
| 10 | **`sleepFor`/`sleepUntil` nonpositive duration** — signed→unsigned cast parks ~forever instead of returning immediately (§18.1.6) | MISSING | std-scheduler |
| 11 | **UnhandledChildFailure** — a forked-and-never-awaited child that fails silently vanishes; never aggregated into its scope's Exit (§18.1.3/.8) | MISSING | fibers |

Additional MUST items that are **PARTIAL refinements** of an otherwise-working
mechanism (not counted separately above, listed in area tables): §32.2.12 failing-finalizer `Then`-composition + mandatory-cleanup-wait masking; §32.2.13 mask-state restore on resume; the §27.6 capability-declaration inconsistency (C runtime vs Haskell profile disagree on `rt-parallel`/`rt-shared-stm`); std.atomic memory-order arguments ignored and missing fixed-width instances (same root as #3).

### Highest-priority gaps (ranked)

1. **Handler abandonment cleanup (#1)** — a genuine §32.2.21-MUST *correctness*
   violation hiding behind value-only tests. Resources acquired with
   `using`/`defer` inside a body whose effect is handled abortively are silently
   leaked on native. The conformance tests assert only the clause value (via the
   interpreter oracle), and the oracle reduces `__effDefer` to pure-Unit, so
   **neither side can observe the leak** — untested by construction.
2. **std.atomic non-atomic (#3)** — silent data races. Every `AtomicRef` op is a
   non-atomic `readRef`/`writeRef` pair on the multi-worker runtime; memory-order
   arguments are ignored. A correct implementation already exists and is compiled
   in — it is purely a backend-wiring gap.
3. **Safe-points (#2)** — a compute-bound pure loop ignores pending interruption
   and monopolizes a worker, violating weak fairness and the interruption-point
   obligation. The contract is documented (`kappart2.h`) but the stub is empty.
4. **`blocking` identity (#4)** — `rt-blocking` is advertised on an unsound
   premise (the Haskell justification claims a single-agent runtime, but the
   runtime spawns nproc workers). N concurrent blocking calls deadlock the
   scheduler.
5. **std.supervisor stub (#5)** — an entire normative §29.2 module returns
   constants. Large but self-contained (`.kp` library over the existing
   Scope/Fiber/Monitor/Promise primitives).
6. **`sandbox`/`unsandbox` (#6)** and **`Alternative STM` (#7)** — reachable
   surface features that hard-fail or silently misbehave on native; both have the
   runtime half already present.

### What is solidly done

The **core CK-machine is a faithful realization of §32.2 for the sequential,
one-shot profile**, and the §18.1 structured-concurrency surface is
**C-backend-complete**:

- §32.2.1 fiber-state schema, §32.2.13 captured-continuation boundary, §32.2.18
  store-sharing (no rollback), §32.2.17 abortive direct-escape, §32.2.22 deep
  re-installation — implemented, codegen-reachable, regression-tested.
- §18.1.4–.9 fork / await / join / interrupt (WAITING form so loser finalizers
  run before the combinator returns) / newScope / shutdownScope / monitor /
  Promise / FiberRef — all end-to-end on C, with real C tests
  (`cancel`, `scopes`, `scope_drain`, `race`, `fiberref_promise`, `finalizer_mask`).
- §18.1.6 race / timeout with correct tie-breaks and waiting-interrupt of the loser.
- §18.1.12 poll / uninterruptible / mask+restore / ensuring / acquireRelease;
  §32.2.5 masked-LIFO finalizer drain (interrupt mid-drain cannot drop remaining defers).
- §18.1.13 STM core: optimistic journal, read-version validation, real
  retry-parking with lost-wakeup closure, commit-uninterruptible.
- §18.1.21/.22 shallow & deep one-shot handlers; §18.1.16/.17/.20 multi-shot
  capability gating + the control-flow-linearity capture rule (static).
- §18.1.5/.6 scheduler/reactor spine: M:N (1 worker/CPU), libuv reactor thread,
  `uv_hrtime` monotonic clock, FIFO weak fairness.
- §34.4 cleanup/defer/using are first-class scheduler nodes, **not** host GC
  finalizers (fails closed if a defer escapes its do-scope).

### Profile-scoped latitude (NOT conformance gaps)

- **LLVM backend** blocklists `fork`/`scope`/`monitor`/`promise`/STM/`sleepFor`
  as a clean unsupported (`ckMachinePrims`, LLVM.hs:560-578). §18.1 concurrency
  is C-complete but LLVM-incomplete *by design* (uniform-boxed parity milestone).
  LLVM *does* support the masking/finalizer ops.
- **Multi-shot effects** correctly withheld; reachable multi-shot ops are
  statically rejected — the §32.2.14 ">1 use MUST be persistent" is satisfied
  vacuously by rejection, per the §32.2 cap-gating clause.
- §32.2.15 tail-resumptive join-point optimization absent — observationally
  equivalent (more allocation), a perf MAY.
- Single global FIFO run-queue (no work-stealing deques) — fair and conformant;
  stealing is a MAY/perf item.

### Not spec requirements (out of scope — recorded to prevent false gaps)

- `withInterruptStatus` / `getInterruptStatus` / `disconnect` as primitives —
  not in the spec; interrupt status is modeled purely via mask/uninterruptible/poll.
- §18.6.2 `VarCurrent` — an elaboration-time current-value representative, not a
  §32.2 runtime entity.
- Semaphores / queues / channels / Ref-over-TVar — §29's required modules are
  exactly atomic/supervisor/hash/unicode/bytes/debug/config/build; these are
  future `.kp` convenience libraries.
- `rt-timers` — not a real capability; monotonic timers fold into `rt-core`.
- MVar — not a spec entity (only Promise §18.1.9 is normative).

---

## Area 1 — Fibers, Scopes, Interruption (§18.1.2–§18.1.12, §18.11)

The §18.1 fiber/scope/interruption surface is implemented end-to-end on the C
backend (runtime OP-node + `krt2_*` ABI + prelude prim + C-codegen dispatch),
and the semantics are genuinely realized (WAITING interruption so loser
finalizers run before combinators return; attach/detach races serialized under
`sc->lock`). Gaps are at the edges: fiber identity/labels (unreachable),
unhandled-child-failure aggregation, and the no-op `blocking`.

| Requirement (§) | Status | Sev | Evidence (§ + file:line) | Effort |
|---|---|---|---|---|
| fork / forkDaemon — attached/detached child, inherits FiberRef snapshot (§18.1.4) | IMPLEMENTED | MUST | Spec.md:18654; Prelude.hs:427-438,1510-1519; rt.c:68-69 → OP_FORK/OP_FORK_DAEMON rt.c:1048-1052; attach scope.c:91-114; C.hs:432 | none |
| await → terminal Exit; join projects Success/Fail / re-raises (§18.1.4/§32.2) | IMPLEMENTED | MUST | Spec.md:18662; Prelude.hs:431,1514,1524-1530; krt2_await rt.c:70 → do_await rt.c:1054; awaiter woken in fiber_finish rt.c:481-486 | none |
| interrupt/interruptFork/As — WAITS for target termination + all finalizers; default InterruptCause; first-request-wins (§18.1.2/.4) | IMPLEMENTED | MUST | Spec.md:18670,19081; Prelude.hs:1553-1563; rt.c:83-86; OP_INTERRUPT rt.c:1083-1093; wait scope.c:58-73; first-wins scope.c:43-52 | none |
| newScope/withScope/forkIn/shutdownScope — interrupt+drain all children, idempotent, born-into-draining still interrupted (§18.1.8) | IMPLEMENTED | MUST | Spec.md:18877; Prelude.hs:476-486; shutdown scope.c:147-173; born-into-draining scope.c:108-114; withScope=ensuring rt.c:140-143 | none |
| monitor/awaitMonitor/demonitor — one-way obs; returns recorded Exit even post-termination; demonitor is sound no-op (§18.1.8) | IMPLEMENTED | MUST | Spec.md:18891; Prelude.hs:526-536; scope.c:177-199; demonitor no-op rt.c:125 | none |
| timeout — timer→interrupt(TimedOut), wait finalize, Fail Timeout; io-wins tie; nonpositive fires first (§18.1.6) | IMPLEMENTED | MUST | Spec.md:18804; race.c:80-97 (TimedOut via waiting interrupt_as); Prelude.hs:1596-1602; C.hs:2318. *nonpositive short-circuit & exact tie tested in race.c, not re-run* | none |
| race — winner result, loser interrupt(RaceLost)+finalize, left-wins tie (§18.1.6) | IMPLEMENTED | MUST | Spec.md:18820; race.c:40-62; Prelude.hs:1609+; tie order race.c:47-52 | none |
| Promise: new/complete(first-wins)/awaitExit/await/poll; interruptible waits, wake-all (§18.1.9/§18.11) | IMPLEMENTED | MUST | Spec.md:18943; Prelude.hs:631-649,1535-1541; rt.c:77-79,192-193; tested fiberref_promise.c | none |
| FiberRef new/get/set/modify/locally — per-fiber map, copy-on-fork, locally restores as masked finalizer (§18.1.7) | IMPLEMENTED | MUST | Spec.md:18837; Prelude.hs:538-563; deep-copy internal.h:208-243; ops rt.c:1193-1203; both backends C.hs:428 / LLVM.hs:3312 | none |
| poll/uninterruptible/mask+restore/ensuring/acquireRelease — finalizers masked, poll delivers under mask (§18.1.12) | IMPLEMENTED | MUST | Spec.md:19055; rt.c:1095-1121; begin_finseq rt.c:701-707; both backends C.hs:423 / LLVM.hs:3316; tested finalizer_mask.c, cancel.c | none |
| cede / nowMonotonic / sleepFor / sleepUntil — interruptible, non-agent-blocking (§18.1.5/.6) | IMPLEMENTED | MUST | Spec.md:18739; cede Prelude.hs:449 → rt.c:1056; sleep prims Prelude.hs:661-662; derived std.time Prelude.hs:843-848 | none |
| **fiberId / currentFiberId — source-visible unique identity (§18.1.10)** | **MISSING** | MUST | Spec.md:18984. Runtime HAS ops (rt.c:80-81, handlers rt.c:1074-1081) but **no prelude prim** (only the FiberId data decl Prelude.hs:1465) and **no codegen** (neither C.hs nor LLVM.hs). Unreachable from source. | S |
| **get/set/locallyFiberLabel — per-fiber diagnostic label (§18.1.10)** | **MISSING** | MUST | Spec.md:18992. No `Fiber.label` field (internal.h:214-246); header lists `krt2_*_fiber_label` as remaining (kappart2.h:185); no prim, no codegen. Entire sub-API absent. | M |
| **UnhandledChildFailure — attached child failing-unacknowledged at scope exit → Defect (§18.1.3/.8)** | **MISSING** | MUST | Spec.md:18629. fiber_finish only stores Exit + wakes awaiters; scope_detach unlinks + decrements live (rt.c:477-496, scope.c:119-134) — neither inspects the child's Exit; root-scope shutdown discards exits (rt.c:1394-1423). | L |
| **blocking : IO e a → IO e a — route through backend blocking bridge; gate on rt-blocking (§18.1.11)** | **PARTIAL** | MUST | Spec.md:19030. krt2_blocking is identity `{ return body; }` rt.c:97 — runs inline on a CK worker, no uv threadpool offload. No prelude prim, no dispatch, no rt-blocking gate. See cross-area #4. | M |
| fork/forkIn captures () borrow-escape → E_QTT_BORROW_ESCAPE (§18.1.4) | PARTIAL | MUST | Spec.md:18708. Signatures carry `captures ()` (Prelude.hs:479-482,1510,1518) so the obligation is expressed; the E_QTT_BORROW_ESCAPE-emitting check was not located — **elaboration/QTT concern, defer to that audit lane.** | unknown |
| LLVM backend parity for §18.1 concurrency | PARTIAL | profile-scoped | LLVM.hs:560-578 blocklists fork/scope/monitor/promise/STM/sleepFor; supports masking/finalizer ops (LLVM.hs:3310-3318). C-complete, LLVM-incomplete by design. | M-L/group |

---

## Area 2 — Effect Handlers & STM (§18 effects, §18.1.13 STM)

The algebraic-effect handler kernel (handle / deep handle / perform / resume,
one-shot) and STM with real optimistic-journal parking are genuinely implemented
and wired through both backends; multi-shot is capability-gated and the §18.1.20
capture rule is statically enforced. The headline gap is abandonment cleanup
(shared with Area 3); plus three reachable-but-broken surface features.

| Requirement (§) | Status | Sev | Evidence (§ + file:line) | Effort |
|---|---|---|---|---|
| Shallow & deep one-shot handlers — nearest-label capture, one return + one-per-op, k typed at quantity, deep auto-reinstall, other labels propagate (§18.1.21/.22) | IMPLEMENTED | MUST | Static: elabHandle Check.hs:7824-7948. Runtime: do_perform rt.c:761-817 (label walk eff_label_same rt.c:736), do_resume rt.c:822-855 (deep re-push rt.c:841-844). Both backends C.hs:2014-2017. *Native execution exists-but-untested — no krt2_handle test in runtime/tests.* | none |
| Resumption-quantity discipline — one-shot default; multi-shot gated; §18.1.20 capture rule (§18.1.16/.17/.20) | IMPLEMENTED | MUST | csMultishotOps Check.hs:7599-7603; multishotLegality C.hs:499-511; capture analysis Usage.hs:2149-2280 (E_QTT_CONTINUATION_CAPTURE); runtime one-shot backstop rt.c:826-832; conformance tests under tests/conformance/qtt/ | none |
| Exit/Cause vocabulary, throwError/catchError on Fail only, __reraiseCause, Promise single-assignment (§18.1.2/.4/.9) | IMPLEMENTED | MUST | Cause ctors rt.c:45-49; KK_CATCH rt.c:949-955; reraise C.hs:2308-2317 → rt.c:1034; Promise rt.c:602-656 | none |
| STM core — serializable atomically, consistent snapshot, commit-only writes, retry-park-on-change, commit-uninterruptible (§18.1.13/§32.2.9) | IMPLEMENTED | MUST | stm.c: journal stm.c:82-89, read-version validate stm.c:182-204, retry-park + revalidate stm.c:207-224; commit sync within OP_ATOMICALLY. Parked retry interruptible (scope.c:43-52 + rt.c:1010). Two self-documented SHOULD deviations (stm.c:25-37): RUN phase uninterruptible; possible torn read-snapshot. | none core / S for SHOULD |
| **Handler abandonment — clause completes WITHOUT resuming → drain captured do-scope `defer`/`using` masked-LIFO before clause result (§32.2.20/.21)** | **MISSING** | MUST | Spec.md:35380. do_perform severs [head..prev] into Resumption r->head (rt.c:795-803); if resume never called the slice is GC'd — defers never run. No path runs begin_finseq over r->head. Tests assert only value via assertEval (oracle); oracle reduces __effDefer to Unit (Eval.hs:1099-1106) → **uncovered by construction.** See Area 3 §32.2.20/.21. | M |
| **Alternative STM / orElse — right branch runs only on left-retry, rolling back left writes, keeping reads (§18.1.13)** | **MISSING** | MUST | Spec.md:19144. Runtime ready: krt2_or_else stm.c:60, STM_ORELSE rollback stm.c:130-153. But **no surface binding** — zero `instance Alternative` in Prelude.hs (only an unrelated `Option` `orElse` Prelude.hs:1749). The lone STM choice is `Monoid (STM a)` whose `append x y = x` (Prelude.hs:1417) **drops y**. STM_ORELSE is dead code. | low-med |
| **sandbox / unsandbox — expose/re-hide terminal Cause in typed channel (§18.1.2)** | **MISSING** | MUST | Spec.md:18599 normative expect-term. Declared Prelude.hs:451-454, in oracle Interp.hs:669-680, but **0 hits** in Backend/C.hs & LLVM.hs; krt2_sandbox only a doc comment (kappart2.h:188). emitPrim turns it into compile-time E_BACKEND_UNSUPPORTED → reachable use rejected on native. | M |
| §32.2.12 failing-finalizer cause composes `Then` + remaining finalizers still run (§32.2.12) | PARTIAL | MUST | Spec.md:35202. rt.c:973-981: a finalizer that itself fails abandons remaining finalizers and does NOT compose via `Then` (self-admitted refinement). Cause ctors exist (rt.c:48-49) but unused on this path. Normal body-then-cleanup composition IS structured. See Area 3. | M |
| Multi-shot rejection diagnostic code/family (§18.1.17) | PARTIAL | MUST | Spec.md:19337. Rejection correct (Capabilities.hs:30 omits cap, multishotLegality C.hs:499-511) but emits `E_BACKEND_UNSUPPORTED` / `kappa-hs.backend.unsupported` instead of the mandated `E_FEATURE_BACKEND_CAPABILITY_MISSING` / `kappa.feature.gated`. | low |
| var/loop family (var/:=/while/for/break/continue) inside Eff-typed do-block (§18.6/§32.2.19) | MISSING | SHOULD | Spec.md:20747. elabEffDo rejects them Check.hs:8120-8131 (`defer`/`using` ARE supported, Check.hs:8063-8119). Deliberate interp-vs-native parity guard; IO do-kernel does support the loop family. | high |

---

## Area 3 — Runtime State Machine (§32.2)

The CK-machine is a faithful §32.2 realization for the **sequential, one-shot**
case. The central gap is abandonment-cleanup (§32.2.20/.21, same root as Area 2);
the rest are PARTIAL refinements (mask-restore on resume, finalizer-cause
composition, cleanup-wait masking) and absent-by-design multi-shot/safe-point
machinery.

| Requirement (§) | Status | Sev | Evidence (§ + file:line) | Effort |
|---|---|---|---|---|
| §32.2.1 fiber-state schema + transition families | IMPLEMENTED | MUST | Spec.md:34864. Fiber struct internal.h:214-246 (cur/k, status, att/cur_scope, mask_depth, interrupt_pending/cause, cur_exits, locals, exit); step/deliver/unwind rt.c:859-1006. All families present except handler-ABANDON. | n/a |
| §32.2.13 captured-continuation boundary (suffix to nearest matching handler incl. loop/return/do-scope/other-handler frames) | IMPLEMENTED | MUST | Spec.md:35222. do_perform outward walk rt.c:766-803; cur_exits snapshot rt.c:786,796. | n/a |
| **§32.2.13 resume re-enters under capture-point mask state** | **PARTIAL** | MUST | Spec.md:35237. Resumption (rt.c:463-471) saves cur_exits but NOT mask_depth; do_resume rt.c:822-855 doesn't restore mask before splice → resumed body inherits the clause's mask. Correct only when captured slice contains the relevant KK_POPMASK/SETMASK frames. No perform-under-mask test. | S |
| §32.2.14 one-shot destructive / multi-shot persistent | PARTIAL | profile-scoped | Spec.md:35246. One-shot destructive impl (do_resume rt.c:826-833 with `used` backstop). Multi-shot not impl; rt-multishot-effects withheld; reachable multi-shot statically rejected (C.hs:499-516). ">1 MUST" satisfied vacuously by rejection. | L (v2) |
| §32.2.15 tail-resumptive join-point optimization | MISSING | MAY | Spec.md:35260. No detection; do_perform always allocates a Resumption (rt.c:795-814). Observationally equivalent — deferred optimization, not a gap. | M (optional) |
| §32.2.16 reclamation doesn't invalidate a live one-shot resumption | IMPLEMENTED | MUST | Spec.md:35284. Captured slice GC_MALLOC'd, held via Resumption.head/tail (rt.c:464-465), Boehm-traced. | n/a (one-shot) |
| §32.2.17 abortive direct-escape but still §32.2.13 boundary + §32.2.19/.20 unwind | PARTIAL | MUST | Spec.md:35310. Direct escape works (rt.c:913-918); the closing MUST (not dropping the captured segment without exit-action behavior) is VIOLATED — see §32.2.20. | M (shared) |
| §32.2.18 continuation reuse ≠ store rollback (heap stays shared) | IMPLEMENTED | MUST | Spec.md:35328. do_perform only severs Cont + cur_exits pointer (rt.c:801,786), never touches the heap; refs are ordinary GC cells (rt.c:1173-1182). | n/a (one-shot) |
| §32.2.19 do-scope exit-stacks copied with continuation; each resume unwinds its own | PARTIAL | profile-scoped | Spec.md:35341. cur_exits restored on resume (rt.c:849) so a single resume unwinds its own defers. Per-clone independence is multi-shot (moot). Abandon path covered under §32.2.20. | M / L (v2) |
| **§32.2.20 clause-without-resume abandons captured segment: unwind do-scope frames once, run exit actions masked-LIFO; + static escape check** | **MISSING** | MUST | Spec.md:35358. No abandonment drain; deliver flows clause value to KK_HANDLER (rt.c:913-918) and the slice is GC'd defers-unrun. Static escape check absent (kappart2.h:247-249). | M + M |
| **§32.2.21 worked example (using r + defer): both run once masked-LIFO before clause result, post-op code doesn't run** | **MISSING** | MUST | Spec.md:35380. Direct consequence of §32.2.20. Tests assert only value (assertEval); oracle reduces __effDefer to Unit (Eval.hs:1099-1106) → genuine MUST violation, untested-by-construction. | M + tests |
| §32.2.22 deep = shallow + recursive driver (reinstall around resumption) | IMPLEMENTED | MUST | Spec.md:35425. do_perform records deep handler on Resumption (rt.c:807-808); do_resume re-pushes fresh KK_HANDLER (rt.c:841-844). One-shot only. | n/a (one-shot) |
| **§32.2.12 cleanup-cause composition + masked mandatory-cleanup waits** | **PARTIAL** | MUST | Spec.md:35191. Masked-LIFO drain + normal Then-composition IMPLEMENTED (rt.c:697-911). GAP 1: failing-finalizer cause not `Then`-composed + abandons remaining finalizers (rt.c:973-981). GAP 2: interrupt-wait / shutdown-wait parks set F_PARKED WITHOUT raising mask_depth (scope.c:62-72,147-166) → waiting fiber interruptible during a spec-masked wait. | M |
| §32.2.5 finalizers run masked; pending request observed at next interruption point | IMPLEMENTED | MUST | Spec.md:34974. begin_finseq raises mask_depth + KK_POPMASK (rt.c:701-711); deliver only when mask_depth==0 (rt.c:1010). Tested finalizer_mask.c. | n/a |
| **§32.2.6 weak fairness — long-running pure execution behaves as if it has safe points** | **PARTIAL** | MUST | Spec.md:34996. IO-step granularity preemptible (rt.c:1010); cede re-enqueues. GAP: pure recursion never re-enters the check — krt2_safepoint is a no-op (rt.c:1322) and codegen emits **zero** safepoint calls. Tight pure loop monopolizes a worker. See cross-area #2. | M |
| §32.2.3 per-do-block nested supervision scope drained before that block's release actions | PARTIAL | MUST | Spec.md:34930. Exit-action machine ordered correctly, BUT per-do-block scopes NOT created — fork attaches to a flat per-fiber f->cur_scope (rt.c:569-578); internal.h:566-568 notes flat-nesting-in-v1. A block's defers aren't guaranteed to run after that block's forked children drain. | L |

---

## Area 4 — Capabilities & Lowering Obligations (§27.6, §34.3.3, §34.4)

The native profile's capability declaration is **internally inconsistent**: the C
runtime and the Haskell profile disagree, and the disagreement is unreconciled.
The multi-shot gate and the §34.4 cleanup-not-host-finalizer obligation are
solidly met; the safe-point and blocking obligations are not.

| Requirement (§) | Status | Sev | Evidence (§ + file:line) | Effort |
|---|---|---|---|---|
| §27.6 a backend MUST declare an authoritative, self-consistent capability set | PARTIAL | MUST | **TWO disagreeing decls:** rt.c:17-19 KRT2_CAPABILITIES = {rt-core, rt-parallel, rt-shared-stm, rt-blocking, rt-atomics}; Capabilities.hs:30 = {rt-core, rt-blocking, rt-atomics}. Disagree on rt-parallel & rt-shared-stm. The C list is never consumed (only its extern, kappart2.h:250); the Haskell list is the one used (NativeProbe.hs:126). **Verified this session.** | small |
| §32.2.5/.6 long-running pure execution MUST behave as if it has safe points (rt-core) | MISSING | MUST | krt2_safepoint no-op rt.c:1322 (**verified**); codegen emits none (**0 hits** in Backend/*.hs, verified); scalar fast-path tight loop has no interrupt check (emitScalarLoop C.hs:4642-4659). Only fiber_step top (rt.c:1010) checks, reached only between OP nodes. Documented unfixed: runtime/docs/CPS-DESIGN.md:90,138. | medium |
| §32.2.6/§27.6/§26.1.4 rt-blocking MUST NOT monopolize a worker | PARTIAL | MUST | krt2_blocking identity rt.c:91-97 (**verified**), runs inline; no uv_queue_work lane (0 hits). Multi-worker (default_workers=nproc rt.c:1341-1347) → >N blocking calls starve. Haskell justification ("single-agent… vacuously") FALSE for the real multi-worker runtime (Capabilities.hs:20-24). | medium |
| §27.6/§34.3.3 a backend lacking rt-multishot-effects MUST reject reachable multi-shot before KBackendIR | IMPLEMENTED | MUST | Cap withheld (rt.c:17 & Capabilities.hs:30, **verified**). recordMultishotOps Check.hs:7599; multishotLegality C.hs:489-509 rejects; runtime backstop rt.c:829-831. Shared C+LLVM. | none (verify-only) |
| §27.6/§18.1.17/§34.3.3 normative capability token is `rt-multishot-effects` | PARTIAL | SHOULD | Code/diagnostics use short `rt-multishot` (Explain.hs:250, C.hs:505; rt.c:829, internal.h:101). Spec token: `rt-multishot-effects`. Behavior correct, token wrong (confuses capability-matching tooling). | trivial |
| §27.6/§32.2.10 rt-parallel only if actually provided | PARTIAL | MUST | Runtime DOES create nproc OS-thread workers (rt.c:1341-1413, worker_main rt.c:1325) so rt.c:17's claim is backed — but Capabilities.hs:30 does NOT advertise it and calls the runtime single-agent. Contradiction. §32.2.10 cross-fiber happens-before under real parallelism untested (rt.c:1350-1352 REVIEW note). | small reconcile / medium audit |
| §27.6/§32.2.9 rt-shared-stm only with cross-worker validity | PARTIAL | MUST | Advertised rt.c:18 but NOT Capabilities.hs:30 (same contradiction). STM exists (stm.c, OP_ATOMICALLY rt.c:1221); single-agent serializability plausible, but cross-worker commit-serialization under concurrent committers is exists-but-unproven (no stress test). | medium |
| §34.3.3 pre-KBackendIR legality checkpoints (no unerased Type/q0, fixed arity, handler/scheduler/sync structures, std.atomic under rt-atomics, multi-shot under rt-multishot-effects, layout, concrete dicts, explicit roots) | PARTIAL | MUST | Only two realized as explicit gates: multishotLegality (C.hs:489) and the FFI→capability gate (Capabilities.hs:37, fail-closed). The rest are NOT a single named pre-KBackendIR verifier — the recently-fixed erased-type-application crash shows an unerased-term case reached the backend. | large |
| §34.4 cleanup/defer/using/handlers preserved as language semantics, NOT host finalizers; no GC-finalization reliance | IMPLEMENTED | MUST | OP_DOSCOPE/OP_DEFER push an explicit ExitStack (rt.c:1137-1152) with a hard trap if a defer escapes its do-scope (rt.c:1149, fails closed). LIFO+masked via begin_finseq/KK_FINSEQ. No GC finalizer hooks on Fiber/Scope/Promise. Deep reinstall rt.c:843. | none (verify-only) |
| §34.4.1 rt-multishot-effects advertiser MUST document clone/reclaim or withhold | IMPLEMENTED | MUST | Withheld; one-shot strategy documented (internal.h:101, CPS-DESIGN.md:170). Multi-shot doc obligation vacuously satisfied. No over-claim. | none |
| `rt-timers` capability-name completeness | IMPLEMENTED | MAY | No such spec capability; monotonic timers fold into rt-core (§27.6). OP_SLEEP via libuv reactor (rt.c:1060-1062), OP_NOW uv_hrtime (rt.c:1063). Absence of rt-timers token is correct. | none |

---

## Area 5 — std Runtime Modules: Scheduler / Reactor / Timers / Clocks / Blocking (§29, §18.1.5/.6)

The scheduler/reactor/clock spine is solid (true M:N, libuv reactor, monotonic
clock, verified race/timeout). The gaps cluster in **std.atomic** (correct impl
is dead code), **std.supervisor** (total stub), **nonpositive sleep** (sign-cast
bug), and **blocking** (no offload).

| Requirement (§) | Status | Sev | Evidence (§ + file:line) | Effort |
|---|---|---|---|---|
| §18.1.5/§32.2.6 weak fairness; continuously-runnable fiber eventually scheduled; cede yields | IMPLEMENTED | MUST | Global mutex+condvar FIFO (rt.c:358 push-tail, rt.c:387 pop-head); cede re-enqueues at tail rt.c:1056-1059. FIFO ⇒ weak fairness. | none |
| Work-stealing M:N | PARTIAL | MAY | No per-worker deques / stealing; ONE shared FIFO (rt.c:358-405, internal.h:301-303), all workers contend on rq_lock. Fair & conformant — not a normative gap. | L |
| §18.1.6/§32.2.6 monotonic timer delivery; sleep parks only the fiber | IMPLEMENTED | MUST | libuv reactor owns timers; OP_SLEEP parks + submits IoReq rt.c:1060-1062; reactor.c:25-40; nowMonotonic = uv_hrtime rt.c:1063-1064. | none |
| **§18.1.6 sleepFor/sleepUntil with nonpositive d returns immediately** | **MISSING** | MUST | OP_SLEEP does `(uint64_t)kas_int(...)` rt.c:1061; reactor.c:33/38 only special-cases nanos==0. A negative ns (sleepUntil of a past instant, Prelude.hs:847-848) wraps to a huge uint64 → never fires. No nonpositive guard. | S |
| §18.1.6 timeout with nonpositive d behaves as fire-first | PARTIAL | MAY | krt2_timeout always forks action + sleep watcher (race.c:104); nonpositive rounds to ms=0 but action still forked and wins on tie (race.c:94). Spec permits MAY-avoid; minor. | S |
| §18.1.6 race/timeout — concurrent, correct winner, loser interrupted+awaited, tie-breaks | IMPLEMENTED | MUST | race.c: race checks left first (tie→left, race.c:49-59); timeout checks action first (tie→completion, race.c:94); loser = WAITING interrupt so finalizers run. | none |
| §18.1.1 nowMonotonic + Instant/Duration arithmetic | IMPLEMENTED | MUST | uv_hrtime rt.c:1063; Duration/Instant data-driven Kappa (Prelude.hs:806-848). | none |
| **§29.1 AtomicRef is a distinct atomic cell; RMW atomic w.r.t. all ops on the cell** | **MISSING** | MUST | Prelude lowers `AtomicRef a = MkAtomicRef (Ref a)` and every op via readRef/writeRef (Prelude.hs:3045-3131); __atomicRmw = readRef-then-writeRef (3110-3116). Correct lock-free atomic.c EXISTS + compiled but is **dead code** — **verified 0 backend hits** for krt2_atomic_*. RMW/CAS race on the multi-worker runtime. | M |
| §29.1 compare-exchange uses rep-equality + applies success/failure memory orders | PARTIAL | MUST | atomic.c models all four order kinds + real CAS (atomic.c:68-145), but the prelude path runs instead → order args IGNORED, CAS = value-compare over Ref (Prelude.hs:3105-3108). Fixed by the cell-wiring fix above. | M (same) |
| §29.1 AtomicValue Bool + std.ffi fixed/pointer-width ints; AtomicInteger; polymorphic fetch-* | PARTIAL | MUST | Only `AtomicValue Bool`, `AtomicValue Integer`, `AtomicInteger Integer` (Prelude.hs:3078-3080); fetch-* monomorphic over Integer not `forall a. AtomicInteger a` (Prelude.hs:3118-3131). No std.ffi-int instances. Noted SPEC_COMPLIANCE.md:184. | M |
| **§29.2 std.supervisor — OTP supervision (policies/strategies/intensity/cause/idempotent shutdown)** | **MISSING** | MUST | Total stub: startSupervisor = pure (MkSupervisor children); shutdown = pure (); await = pure (Success ()) (Prelude.hs:3282-3297). No fibers, restart engine, intensity window, or cause propagation. Lone test exercises empty-children idempotent-shutdown only. Confirmed SPEC_COMPLIANCE.md:185, ROADMAP.md:385. | L |
| **§18.1.11/§29 blocking through bridge so foreign work doesn't monopolize; rt-blocking honored** | **PARTIAL** | MUST | krt2_blocking identity, inline on worker (rt.c:91-97, **verified**); no uv_queue_work lane (0 hits). rt-blocking still advertised (rt.c:18). 1 worker/CPU + true blocking syscall ⇒ worker occupied. Same root as cross-area #4. | M |
| §18.1.5 blocking foreign work MUST NOT permanently monopolize scheduler resources | MISSING | MUST | No offload / compensating-worker / host support; FFI runs on the worker. N concurrent blocking calls deadlock the scheduler. Same root cause as the blocking-bridge item. | M (shared) |
| §29 required-modules scope (semaphores/queues/Ref-over-TVar) | IMPLEMENTED | MAY | Not a gap: §29 required modules are atomic/supervisor/hash/unicode/bytes/debug/config/build (Spec §30755+). No normative semaphore/queue/channel. Future `.kp` library work (ROADMAP.md:385). | n/a |

---

## De-duplication ledger

Findings reported in more than one area audit, collapsed to a single root cause
above:

- **Safe-points (§32.2.5/.6)** — Area 3 (§32.2.6), Area 4 (rt-core obligation),
  Area 5 (weak-fairness). One root: empty `krt2_safepoint` rt.c:1322 + no codegen
  emission. Counted **once** (cross-area #2).
- **`blocking` identity (§18.1.11 / §18.1.5)** — Areas 1, 2, 4, 5. One root:
  `krt2_blocking` identity rt.c:97 + no offload lane + over-advertised
  `rt-blocking`. Counted **once** (cross-area #4).
- **Handler abandonment (§32.2.20/.21)** — Area 2 (handlers) and Area 3
  (state machine). One root: severed Resumption slice GC'd without draining its
  KK_DOSCOPE exit actions. Counted **once** (cross-area #1).
- **§32.2.12 finalizer-cause + cleanup-wait masking** — Area 2 (the `Then`
  half) and Area 3 (both halves). Single PARTIAL item.
- **std.atomic (§29.1)** — Area 5 reports it as three rows (distinct cell /
  memory orders / instances); one root wiring fix (prelude→krt2_atomic_*) closes
  the first two. Counted as **one** MUST gap (cross-area #3).
- **Multi-shot diagnostic token** — Area 2 (code/family) and Area 4 (token
  name); both are SHOULD/diagnostic-quality, not the 11-count MUST gaps.
