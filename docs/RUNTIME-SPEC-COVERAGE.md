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

### Normative-MUST runtime gaps: **5**

Counting distinct MISSING or PARTIAL items at MUST severity, after
de-duplicating the same root cause reported across multiple area audits.
(Several appear in 2–3 audits; the count below collapses them.)

| # | Gap (deduped) | Status | Areas reporting |
|---|---|---|---|
| 1 | **std.supervisor is a stub** — restart policies / strategies / intensity / cause semantics all absent (§29.2) | MISSING | std-scheduler |
| 2 | **`sandbox`/`unsandbox` no native lowering** — declared + in oracle, rejected `E_BACKEND_UNSUPPORTED` on native (§18.1.2) | MISSING | effects-stm |
| 3 | **`Alternative STM` / `orElse` unreachable** — runtime `STM_ORELSE` exists, and `Pointed (STM a)` supplies `empty = retry`, but no `Alternative STM` instance binds `<|>` to the runtime choice node (§18.1.13) | MISSING | effects-stm |
| 4 | **Fiber labels** — `get/set/locallyFiberLabel` entirely absent (§18.1.10) | MISSING | fibers |
| 5 | **UnhandledChildFailure** — a forked-and-never-awaited child that fails silently vanishes; never aggregated into its scope's Exit (§18.1.3/.8) | MISSING | fibers |

Additional MUST items that are **PARTIAL refinements** of an otherwise-working
mechanism (not counted separately above, listed in area tables): §32.2.12 mandatory-cleanup-wait masking; §32.2.13 mask-state restore on resume; the §27.6 capability-declaration inconsistency (C runtime vs Haskell profile disagree on `rt-parallel`/`rt-shared-stm`); std.atomic fixed-width and broader polymorphic instance coverage.

### Highest-priority gaps (ranked)

1. **std.supervisor stub (#1)** — an entire normative §29.2 module returns
   constants. Large but self-contained (`.kp` library over the existing
   Scope/Fiber/Monitor/Promise primitives).
2. **`sandbox`/`unsandbox` (#2)** and **`Alternative STM` (#3)** — reachable
   surface features that hard-fail or remain unreachable on native; both have the
   runtime half already present.
3. **Fiber labels** — the source-visible label API remains absent. Source-level
   `blocking` and classified native `rt-blocking` routing are implemented.

### What is solidly done

The **core CK-machine is a faithful realization of §32.2 for the sequential,
one-shot profile**, and the §18.1 structured-concurrency surface is
**C-backend-complete**:

- §32.2.1 fiber-state schema, §32.2.13 captured-continuation boundary, §32.2.18
  store-sharing (no rollback), §32.2.17 abortive direct-escape, §32.2.20/.21
  one-shot handler-abandonment drain, §32.2.22 deep re-installation —
  implemented, codegen-reachable, regression-tested.
- §18.1.4–.9 fork / await / join / interrupt (WAITING form so loser finalizers
  run before the combinator returns) / newScope / shutdownScope / monitor /
  Promise / FiberRef — all end-to-end on C, with real C tests
  (`cancel`, `scopes`, `scope_drain`, `race`, `fiberref_promise`, `finalizer_mask`).
- §18.1.6 race / timeout with correct tie-breaks and waiting-interrupt of the loser.
- §18.1.12 poll / uninterruptible / mask+restore / ensuring / acquireRelease;
  §32.2.5 masked-LIFO finalizer drain (interrupt mid-drain cannot drop remaining defers).
- §18.1.13 STM core: optimistic journal, read-version validation, real
  retry-parking with lost-wakeup closure, commit-uninterruptible.
- §18.1.21/.22 shallow & deep one-shot handlers, including runtime
  `KK_ABANDON`/`KK_ABANDEND` drain for unresumed captured segments; §18.1.16/.17/.20
  multi-shot capability gating + the control-flow-linearity capture rule
  (static).
- §18.1.5/.6 scheduler/reactor spine: M:N (1 worker/CPU), libuv reactor thread,
  `uv_hrtime` monotonic clock, FIFO weak fairness.
- §34.4 cleanup/defer/using are first-class scheduler nodes, **not** host GC
  finalizers (fails closed if a defer escapes its do-scope).

### Profile-scoped latitude (NOT conformance gaps)

- **LLVM backend** parity is profile-scoped and implementation-tracked, not a
  spec relaxation. The old CK-primitive blocklist is empty in current code, and
  concurrency/STM/timer primitives lower through runtime nodes where implemented;
  any remaining LLVM gaps must stay clean `E_BACKEND_UNSUPPORTED` failures or be
  fixed, not described as incomplete by design.
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
`sc->lock`). Gaps are at the edges: fiber labels (identity is implemented) and
unhandled-child-failure aggregation. Source-level `blocking` is wired to the
native blocking lane.

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
| poll/uninterruptible/mask+restore/ensuring/acquireRelease — finalizers masked, poll delivers under mask (§18.1.12) | IMPLEMENTED | MUST | Spec.md:19055; Prelude exposes all source terms; rt.c masking/finalizer paths; both backends lower the protected-scope machinery; tested by finalizer_mask.c, cancel.c, and conformance source-term fixtures | none |
| cede / nowMonotonic / sleepFor / sleepUntil — interruptible, non-agent-blocking (§18.1.5/.6) | IMPLEMENTED | MUST | Spec.md:18739; cede Prelude.hs:449 → rt.c:1056; sleep prims Prelude.hs:661-662; derived std.time Prelude.hs:843-848 | none |
| fiberId / currentFiberId — source-visible unique identity (§18.1.10) | IMPLEMENTED | MUST | Spec.md:18984. Prelude exposes `currentFiberId`/`fiberId`, the interpreter maps them to stable per-thread ids, and native codegen lowers `__currentFiberId`/`__fiberId` through the runtime builders. Covered by `tests/conformance/effects/fiber-id.kp`. | none |
| **get/set/locallyFiberLabel — per-fiber diagnostic label (§18.1.10)** | **MISSING** | MUST | Spec.md:18992. No `Fiber.label` field (internal.h:214-246); header lists `krt2_*_fiber_label` as remaining (kappart2.h:185); no prim, no codegen. Entire sub-API absent. | M |
| **UnhandledChildFailure — attached child failing-unacknowledged at scope exit → Defect (§18.1.3/.8)** | **MISSING** | MUST | Spec.md:18629. fiber_finish only stores Exit + wakes awaiters; scope_detach unlinks + decrements live (rt.c:477-496, scope.c:119-134) — neither inspects the child's Exit; root-scope shutdown discards exits (rt.c:1394-1423). | L |
| **blocking : IO e a → IO e a — route through backend blocking bridge; gate on rt-blocking (§18.1.11)** | **IMPLEMENTED** | MUST | Spec.md:19030. `std.prelude.blocking` lowers to `krt2_blocking`, classified native calls lower to `knative_blocking` / `knative_sat_blocking`, and both park the fiber on an off-worker lane. The lane now drives arbitrary CK-machine IO, including timer suspension. Covered by `tests/conformance/effects/blocking-source-positive.kp`, `tests/conformance/effects/blocking-sleep-positive.kp`, `test/native/cases/blocking-source.kp`, `test/native/cases/blocking-sleep.kp`, and `runtime/tests/blocking_lane.c`. | none |
| fork/forkIn captures () borrow-escape → E_QTT_BORROW_ESCAPE (§18.1.4) | PARTIAL | MUST | Spec.md:18708. Signatures carry `captures ()` (Prelude.hs:479-482,1510,1518) so the obligation is expressed; the E_QTT_BORROW_ESCAPE-emitting check was not located — **elaboration/QTT concern, defer to that audit lane.** | unknown |
| LLVM backend parity for §18.1 concurrency | PARTIAL | profile-scoped | Current `ckMachinePrims` is empty; implemented fork/scope/monitor/promise/STM/timer primitives lower through runtime nodes, and remaining unsupported constructs must fail closed with `E_BACKEND_UNSUPPORTED`. This is a parity backlog, not a design exemption. | M-L/group |

---

## Area 2 — Effect Handlers & STM (§18 effects, §18.1.13 STM)

The algebraic-effect handler kernel (handle / deep handle / perform / resume,
one-shot) and STM with real optimistic-journal parking are genuinely implemented
and wired through both backends; multi-shot is capability-gated and the §18.1.20
capture rule is statically enforced. One-shot handler abandonment is implemented
through `KK_ABANDON`/`KK_ABANDEND`; the remaining gaps are reachable-but-broken
surface features.

| Requirement (§) | Status | Sev | Evidence (§ + file:line) | Effort |
|---|---|---|---|---|
| Shallow & deep one-shot handlers — nearest-label capture, one return + one-per-op, k typed at quantity, deep auto-reinstall, other labels propagate (§18.1.21/.22) | IMPLEMENTED | MUST | Static: elabHandle Check.hs:7824-7948. Runtime: do_perform rt.c:761-817 (label walk eff_label_same rt.c:736), do_resume rt.c:822-855 (deep re-push rt.c:841-844). Both backends C.hs:2014-2017. Native abandonment execution is covered separately by `runtime/tests/abandon_drain.c` and `runtime/tests/abandon_perform.c`; broader handler-surface conformance remains covered by source tests. | none |
| Resumption-quantity discipline — one-shot default; multi-shot gated; §18.1.20 capture rule (§18.1.16/.17/.20) | IMPLEMENTED | MUST | csMultishotOps Check.hs:7599-7603; multishotLegality C.hs:499-511; capture analysis Usage.hs:2149-2280 (E_QTT_CONTINUATION_CAPTURE); runtime one-shot backstop rt.c:826-832; conformance tests under tests/conformance/qtt/ | none |
| Exit/Cause vocabulary, throwError/catchError on Fail only, __reraiseCause, Promise single-assignment (§18.1.2/.4/.9) | IMPLEMENTED | MUST | Cause ctors rt.c:45-49; KK_CATCH rt.c:949-955; reraise C.hs:2308-2317 → rt.c:1034; Promise rt.c:602-656 | none |
| STM core — serializable atomically, consistent snapshot, commit-only writes, retry-park-on-change, commit-uninterruptible (§18.1.13/§32.2.9) | IMPLEMENTED | MUST | stm.c: journal stm.c:82-89, read-version validate stm.c:182-204, retry-park + revalidate stm.c:207-224; commit sync within OP_ATOMICALLY. Parked retry interruptible (scope.c:43-52 + rt.c:1010). Two self-documented SHOULD deviations (stm.c:25-37): RUN phase uninterruptible; possible torn read-snapshot. | none core / S for SHOULD |
| Handler abandonment — clause completes WITHOUT resuming → drain captured do-scope `defer`/`using` masked-LIFO before clause result (§32.2.20/.21) | IMPLEMENTED | MUST | Spec.md:35380. `do_perform` captures the segment into `Resumption`; when a one-shot resumption is abandoned the runtime drives the segment through `RK_DRAIN` using `KK_ABANDON`/`KK_ABANDEND` and `begin_abandon_drain` so captured exit actions run once before the clause result. Covered by `runtime/tests/abandon_drain.c` and `runtime/tests/abandon_perform.c`. | none |
| **Alternative STM / orElse — right branch runs only on left-retry, rolling back left writes, keeping reads (§18.1.13)** | **MISSING** | MUST | Spec.md:19144. Runtime ready: krt2_or_else stm.c:60, STM_ORELSE rollback stm.c:130-153. But **no surface binding** — zero `instance Alternative STM`; `Pointed (STM a)` only supplies `empty = retry`, and the unrelated `Option` `orElse` is not STM choice. STM_ORELSE is dead code until `<|>` is wired. | low-med |
| **sandbox / unsandbox — expose/re-hide terminal Cause in typed channel (§18.1.2)** | **MISSING** | MUST | Spec.md:18599 normative expect-term. Declared Prelude.hs:451-454, in oracle Interp.hs:669-680, but **0 hits** in Backend/C.hs & LLVM.hs; krt2_sandbox only a doc comment (kappart2.h:188). emitPrim turns it into compile-time E_BACKEND_UNSUPPORTED → reachable use rejected on native. | M |
| §32.2.12 failing-finalizer cause composes `Then` + remaining finalizers still run (§32.2.12) | IMPLEMENTED | MUST | Spec.md:35202. `compose_reason_into` records cleanup failures as `Then(primary, cleanup)` and the abnormal `KK_FINSEQ` path keeps the same frame alive to drain remaining finalizers before applying the composed reason (rt.c:1205-1241,1821-1840). | none |
| Multi-shot rejection diagnostic code/family (§18.1.17) | IMPLEMENTED | MUST | Spec.md:19337. Rejection uses `E_FEATURE_BACKEND_CAPABILITY_MISSING` / `kappa.feature.gated` and names the required `rt-multishot-effects` capability. Shared by the C and LLVM native legality gates. | none |
| var/loop family (var/:=/while/for/break/continue) inside Eff-typed do-block (§18.6/§32.2.19) | MISSING | SHOULD | Spec.md:20747. elabEffDo rejects them Check.hs:8120-8131 (`defer`/`using` ARE supported, Check.hs:8063-8119). Deliberate interp-vs-native parity guard; IO do-kernel does support the loop family. | high |

---

## Area 3 — Runtime State Machine (§32.2)

The CK-machine is a faithful §32.2 realization for the **sequential, one-shot**
case. Handler-abandonment cleanup (§32.2.20/.21) is implemented; the remaining
state-machine gaps are PARTIAL refinements (mask-restore on resume and
cleanup-wait masking) plus withheld multi-shot machinery. Safepoints and
finalizer-cause composition are implemented.

| Requirement (§) | Status | Sev | Evidence (§ + file:line) | Effort |
|---|---|---|---|---|
| §32.2.1 fiber-state schema + transition families | IMPLEMENTED | MUST | Spec.md:34864. Fiber struct internal.h:214-246 (cur/k, status, att/cur_scope, mask_depth, interrupt_pending/cause, cur_exits, locals, exit); step/deliver/unwind rt.c:859-1006; handler-abandonment transitions use `KK_ABANDON`/`KK_ABANDEND`. | n/a |
| §32.2.13 captured-continuation boundary (suffix to nearest matching handler incl. loop/return/do-scope/other-handler frames) | IMPLEMENTED | MUST | Spec.md:35222. do_perform outward walk rt.c:766-803; cur_exits snapshot rt.c:786,796. | n/a |
| **§32.2.13 resume re-enters under capture-point mask state** | **PARTIAL** | MUST | Spec.md:35237. Resumption (rt.c:463-471) saves cur_exits but NOT mask_depth; do_resume rt.c:822-855 doesn't restore mask before splice → resumed body inherits the clause's mask. Correct only when captured slice contains the relevant KK_POPMASK/SETMASK frames. No perform-under-mask test. | S |
| §32.2.14 one-shot destructive / multi-shot persistent | PARTIAL | profile-scoped | Spec.md:35246. One-shot destructive impl (do_resume rt.c:826-833 with `used` backstop). Multi-shot not impl; rt-multishot-effects withheld; reachable multi-shot statically rejected (C.hs:499-516). ">1 MUST" satisfied vacuously by rejection. | L (v2) |
| §32.2.15 tail-resumptive join-point optimization | MISSING | MAY | Spec.md:35260. No detection; do_perform always allocates a Resumption (rt.c:795-814). Observationally equivalent — deferred optimization, not a gap. | M (optional) |
| §32.2.16 reclamation doesn't invalidate a live one-shot resumption | IMPLEMENTED | MUST | Spec.md:35284. Captured slice GC_MALLOC'd, held via Resumption.head/tail (rt.c:464-465), Boehm-traced. | n/a (one-shot) |
| §32.2.17 abortive direct-escape but still §32.2.13 boundary + §32.2.19/.20 unwind | IMPLEMENTED | MUST | Spec.md:35310. Direct escape works and abandoned captured segments are drained through the handler-abandonment path before the clause result is delivered. | none |
| §32.2.18 continuation reuse ≠ store rollback (heap stays shared) | IMPLEMENTED | MUST | Spec.md:35328. do_perform only severs Cont + cur_exits pointer (rt.c:801,786), never touches the heap; refs are ordinary GC cells (rt.c:1173-1182). | n/a (one-shot) |
| §32.2.19 do-scope exit-stacks copied with continuation; each resume unwinds its own | PARTIAL | profile-scoped | Spec.md:35341. cur_exits restored on resume (rt.c:849) so a single resume unwinds its own defers. Per-clone independence is multi-shot (moot). Abandon path covered under §32.2.20. | M / L (v2) |
| §32.2.20 clause-without-resume abandons captured segment: unwind do-scope frames once, run exit actions masked-LIFO | IMPLEMENTED | MUST | Spec.md:35358. `begin_abandon_drain` drives the captured slice with `RK_DRAIN`; `KK_ABANDON` starts the drain and `KK_ABANDEND` resumes the handler result after captured exit actions finish. Static escape checks for future multi-shot/escaping resumptions remain a separate capability-gated stage. | none runtime / future static |
| §32.2.21 worked example (using r + defer): both run once masked-LIFO before clause result, post-op code doesn't run | IMPLEMENTED | MUST | Spec.md:35380. Covered by `runtime/tests/abandon_drain.c` and `runtime/tests/abandon_perform.c`; the runtime path drains captured `defer`/`using` actions exactly once before returning the abortive clause result. | none |
| §32.2.22 deep = shallow + recursive driver (reinstall around resumption) | IMPLEMENTED | MUST | Spec.md:35425. do_perform records deep handler on Resumption (rt.c:807-808); do_resume re-pushes fresh KK_HANDLER (rt.c:841-844). One-shot only. | n/a (one-shot) |
| **§32.2.12 cleanup-cause composition + masked mandatory-cleanup waits** | **PARTIAL** | MUST | Spec.md:35191. Masked-LIFO drain and cleanup `Then` composition are IMPLEMENTED, including a finalizer that fails while a scope is already unwinding (rt.c:1205-1241,1821-1840). Remaining GAP: interrupt-wait / shutdown-wait parks set F_PARKED WITHOUT raising mask_depth (scope.c:62-72,147-166) → waiting fiber interruptible during a spec-masked wait. | M |
| §32.2.5 finalizers run masked; pending request observed at next interruption point | IMPLEMENTED | MUST | Spec.md:34974. begin_finseq raises mask_depth + KK_POPMASK (rt.c:701-711); deliver only when mask_depth==0 (rt.c:1010). Tested finalizer_mask.c. | n/a |
| **§32.2.6 weak fairness — long-running pure execution behaves as if it has safe points** | **IMPLEMENTED** | MUST | Spec.md:34996. IO-step granularity preemptible; `krt2_safepoint` now polls pending interrupts and opportunistically runs another ready fiber, and generated C/LLVM loop back-edges call it through a counter gate. Covered by native `interrupt-tight-loop`, `interrupt-general-loop`, and scalar-worker S2.3b gates. | none (verify-only) |
| §32.2.3 per-do-block nested supervision scope drained before that block's release actions | PARTIAL | MUST | Spec.md:34930. Exit-action machine ordered correctly, BUT per-do-block scopes NOT created — fork attaches to a flat per-fiber f->cur_scope (rt.c:569-578); internal.h:566-568 notes flat-nesting-in-v1. A block's defers aren't guaranteed to run after that block's forked children drain. | L |

---

## Area 4 — Capabilities & Lowering Obligations (§27.6, §34.3.3, §34.4)

The native profile now advertises `rt-blocking` for the source-level bridge and
classified native calls: `std.prelude.blocking` builds OP_BLOCKING, plan
resolution accepts `classify blocking`, C/LLVM preserve the classification into
blocking native actions, and the runtime parks the fiber while an off-worker
thread executes the call. `blocking-cancellable` still fails closed because no
safe cancellation bridge is implemented. The C runtime's internal
capability list still names implementation features not all advertised by the
Haskell build profile, so that profile/runtime split needs a smaller
reconciliation audit. The multi-shot gate and the §34.4 cleanup-not-host-finalizer
obligation are solidly met.

| Requirement (§) | Status | Sev | Evidence (§ + file:line) | Effort |
|---|---|---|---|---|
| §27.6 a backend MUST declare an authoritative, self-consistent capability set | PARTIAL | MUST | The Haskell native profile advertises the binding-relevant set `{rt-core, rt-blocking, rt-atomics}`; the C runtime list names `{rt-core, rt-parallel, rt-blocking, rt-shared-stm, rt-atomics}`. The C list is not consumed by build planning (NativeProbe uses Capabilities.hs), so the split still needs an explicit authoritative-profile story for `rt-parallel`/`rt-shared-stm`. | small |
| §32.2.5/.6 long-running pure execution MUST behave as if it has safe points (rt-core) | IMPLEMENTED | MUST | `krt2_safepoint` is real and generated C/LLVM loops emit counter-gated calls. Scalar worker abort is reported through `KRT2_SCALAR_ABORT` and transferred to the active fiber-step boundary with `krt2_scalar_abort`, so pending interrupts are delivered before later generated source effects run. | none (verify-only) |
| §32.2.6/§27.6/§26.1.4 rt-blocking MUST NOT monopolize a worker | IMPLEMENTED | MUST if advertised | Source-level `blocking` builds OP_BLOCKING; classified native calls emit blocking K_NATIVE nodes; the blocking lane runs the CK machine off-worker and `runtime/tests/blocking_lane.c` proves a single scheduler worker is not monopolized by a blocking native call. | none |
| §27.6/§34.3.3 a backend lacking rt-multishot-effects MUST reject reachable multi-shot before KBackendIR | IMPLEMENTED | MUST | Cap withheld (Capabilities.hs and runtime docs, **verified**). recordMultishotOps Check.hs; multishotLegality C.hs rejects with `E_FEATURE_BACKEND_CAPABILITY_MISSING` / `kappa.feature.gated` and message token `rt-multishot-effects`; runtime backstop also reports `rt-multishot-effects`. Shared C+LLVM. | none (verify-only) |
| §27.6/§18.1.17/§34.3.3 normative capability token is `rt-multishot-effects` | IMPLEMENTED | SHOULD | Code, diagnostics, runtime backstop, and current docs use the spec token `rt-multishot-effects`; historical notes that mention the old short token are marked as historical only. | none |
| §27.6/§32.2.10 rt-parallel only if actually provided | PARTIAL | MUST | Runtime DOES create nproc OS-thread workers (rt.c:1341-1413, worker_main rt.c:1325) so the C runtime list's claim is backed — but Capabilities.hs does NOT advertise it in the build profile. §32.2.10 cross-fiber happens-before under real parallelism remains undertested (rt.c:1350-1352 REVIEW note). | small reconcile / medium audit |
| §27.6/§32.2.9 rt-shared-stm only with cross-worker validity | PARTIAL | MUST | Advertised by the C runtime list but NOT by the Haskell build profile. STM exists (stm.c, OP_ATOMICALLY rt.c:1221); `runtime/tests/stm.c` stress-runs parallel transfers across worker threads and checks serializable total preservation. Remaining work is reconciling whether/when the Haskell profile should advertise `rt-shared-stm`. | small reconcile |
| §34.3.3 pre-KBackendIR legality checkpoints (no unerased Type/q0, fixed arity, handler/scheduler/sync structures, std.atomic under rt-atomics, multi-shot under rt-multishot-effects, layout, concrete dicts, explicit roots) | PARTIAL | MUST | Only two realized as explicit gates: multishotLegality (C.hs:489) and the FFI→capability gate (Capabilities.hs:37, fail-closed). The rest are NOT a single named pre-KBackendIR verifier — the recently-fixed erased-type-application crash shows an unerased-term case reached the backend. | large |
| §34.4 cleanup/defer/using/handlers preserved as language semantics, NOT host finalizers; no GC-finalization reliance | IMPLEMENTED | MUST | OP_DOSCOPE/OP_DEFER push an explicit ExitStack (rt.c:1137-1152) with a hard trap if a defer escapes its do-scope (rt.c:1149, fails closed). LIFO+masked via begin_finseq/KK_FINSEQ. No GC finalizer hooks on Fiber/Scope/Promise. Deep reinstall rt.c:843. | none (verify-only) |
| §34.4.1 rt-multishot-effects advertiser MUST document clone/reclaim or withhold | IMPLEMENTED | MUST | Withheld; one-shot strategy documented (internal.h:101, CPS-DESIGN.md:170). Multi-shot doc obligation vacuously satisfied. No over-claim. | none |
| `rt-timers` capability-name completeness | IMPLEMENTED | MAY | No such spec capability; monotonic timers fold into rt-core (§27.6). OP_SLEEP via libuv reactor (rt.c:1060-1062), OP_NOW uv_hrtime (rt.c:1063). Absence of rt-timers token is correct. | none |

---

## Area 5 — std Runtime Modules: Scheduler / Reactor / Timers / Clocks / Blocking (§29, §18.1.5/.6)

The scheduler/reactor/clock/blocking spine is solid (true M:N, libuv reactor,
monotonic clock, verified race/timeout, and source/classified blocking through
the off-worker lane). The gaps cluster in **std.supervisor** (total stub) and
remaining **std.atomic** fixed-width/polymorphic instance coverage.

| Requirement (§) | Status | Sev | Evidence (§ + file:line) | Effort |
|---|---|---|---|---|
| §18.1.5/§32.2.6 weak fairness; continuously-runnable fiber eventually scheduled; cede yields | IMPLEMENTED | MUST | Global mutex+condvar FIFO (rt.c:358 push-tail, rt.c:387 pop-head); cede re-enqueues at tail rt.c:1056-1059. FIFO ⇒ weak fairness. | none |
| Work-stealing M:N | PARTIAL | MAY | No per-worker deques / stealing; ONE shared FIFO (rt.c:358-405, internal.h:301-303), all workers contend on rq_lock. Fair & conformant — not a normative gap. | L |
| §18.1.6/§32.2.6 monotonic timer delivery; sleep parks only the fiber | IMPLEMENTED | MUST | libuv reactor owns timers; OP_SLEEP parks + submits IoReq rt.c:1060-1062; reactor.c:25-40; nowMonotonic = uv_hrtime rt.c:1063-1064. | none |
| §18.1.6 sleepFor/sleepUntil with nonpositive d returns immediately | IMPLEMENTED | MUST | OP_SLEEP reads the signed ns value and immediately delivers Unit for `ns <= 0`; `sleep-nonpositive.kp` covers zero, negative, and past-`sleepUntil`. | none |
| §18.1.6 timeout with nonpositive d behaves as fire-first | PARTIAL | MAY | krt2_timeout always forks action + sleep watcher (race.c:104); nonpositive rounds to ms=0 but action still forked and wins on tie (race.c:94). Spec permits MAY-avoid; minor. | S |
| §18.1.6 race/timeout — concurrent, correct winner, loser interrupted+awaited, tie-breaks | IMPLEMENTED | MUST | race.c: race checks left first (tie→left, race.c:49-59); timeout checks action first (tie→completion, race.c:94); loser = WAITING interrupt so finalizers run. | none |
| §18.1.1 nowMonotonic + Instant/Duration arithmetic | IMPLEMENTED | MUST | uv_hrtime rt.c:1063; Duration/Instant data-driven Kappa (Prelude.hs:806-848). | none |
| **§29.1 AtomicRef is a distinct atomic cell; RMW atomic w.r.t. all ops on the cell** | **IMPLEMENTED** | MUST | The std.atomic surface uses an opaque `AtomicRef` wrapper, not ordinary `Ref`; the native backend wires ops to `krt2_atomic_load/store/exchange/cas/fetch_*` in `runtime/atomic.c`. `test/native/cases/atomic.kp`, `atomic-race.kp`, and `runtime/tests/atomic.c` cover single-cell behavior and the old lost-update race. | none |
| §29.1 compare-exchange uses rep-equality + applies success/failure memory orders | IMPLEMENTED | MUST | `runtime/atomic.c` maps the Kappa order ADTs to C11 `memory_order_*` through backend-private integer codes and performs real CAS over the runtime value representation; the prelude reconstructs `Exchanged`/`NotExchanged` at source level. | none |
| §29.1 AtomicValue Bool + std.ffi fixed/pointer-width ints; AtomicInteger; polymorphic fetch-* | PARTIAL | MUST | Only `AtomicValue Bool`, `AtomicValue Integer`, `AtomicInteger Integer` (Prelude.hs:3078-3080); fetch-* monomorphic over Integer not `forall a. AtomicInteger a` (Prelude.hs:3118-3131). No std.ffi-int instances. Noted SPEC_COMPLIANCE.md:184. | M |
| **§29.2 std.supervisor — OTP supervision (policies/strategies/intensity/cause/idempotent shutdown)** | **MISSING** | MUST | Total stub: startSupervisor = pure (MkSupervisor children); shutdown = pure (); await = pure (Success ()) (Prelude.hs:3282-3297). No fibers, restart engine, intensity window, or cause propagation. Lone test exercises empty-children idempotent-shutdown only. Confirmed SPEC_COMPLIANCE.md:185, ROADMAP.md:385. | L |
| **§18.1.11/§29 blocking through bridge so foreign work doesn't monopolize; rt-blocking honored** | **IMPLEMENTED** | MUST | `Capabilities.hs` advertises `rt-blocking`; `std.prelude.blocking` lowers to `krt2_blocking`; `ResolvedNativeSymbol.ffiClass` reaches C/LLVM codegen; blocking calls emit `knative_blocking`/`knative_sat_blocking`; `runtime/tests/blocking_lane.c` covers the non-monopolization invariant. | none |
| §18.1.5 blocking foreign work MUST NOT permanently monopolize scheduler resources | IMPLEMENTED | MUST | Blocking native actions park the fiber and execute off-worker; the single-worker runtime regression completes an unrelated promise before the blocking sleep returns. | none |
| §29 required-modules scope (semaphores/queues/Ref-over-TVar) | IMPLEMENTED | MAY | Not a gap: §29 required modules are atomic/supervisor/hash/unicode/bytes/debug/config/build (Spec §30755+). No normative semaphore/queue/channel. Future `.kp` library work (ROADMAP.md:385). | n/a |

---

## De-duplication ledger

Findings reported in more than one area audit, collapsed to a single root cause
above:

- **Safe-points (§32.2.5/.6)** — formerly reported by Area 3 (§32.2.6),
  Area 4 (rt-core obligation), and Area 5 (weak-fairness). This is now
  implemented: `krt2_safepoint` is real, generated C/LLVM loop back-edges emit
  counter-gated calls, and the scalar-worker abort channel transfers pending
  interrupts to the active fiber-step boundary. No longer counted as a gap.
- **`rt-blocking` (§18.1.11 / §18.1.5)** — native routing is implemented:
  source-level `blocking` and classified blocking calls are accepted, lowered to
  blocking actions, and run on an off-worker lane.
- **Handler abandonment (§32.2.20/.21)** — formerly reported by Area 2
  (handlers) and Area 3 (state machine). This is now implemented by
  `KK_ABANDON`/`KK_ABANDEND` plus `begin_abandon_drain`; no longer counted as a
  gap.
- **§32.2.12 cleanup-wait masking** — finalizer `Then` composition is now
  implemented; the remaining PARTIAL item is masked mandatory-cleanup waits.
- **std.atomic (§29.1)** — the former distinct-cell / memory-order wiring gap is closed
  by the prelude-to-`krt2_atomic_*` path. Remaining rows are fixed-width and
  polymorphic instance coverage, not a capability-honesty blocker.
- **Multi-shot diagnostic token** — Area 2 (code/family) and Area 4 (token
  name); both are SHOULD/diagnostic-quality, not the 6-count MUST gaps.
