# Perceus Stage S4 — Implementation Plan (thread-shared atomic split + shared reclamation)

Status: **LANDED for the C/runtime path (2026-07-03).** S0→S3.4 landed precise RC with free-on-zero
default-on for the C/runtime path; S4 now pays down the two costs S3 deliberately deferred:
(A) thread-local RC uses the **biased fast path** (atomic discriminator load, then direct non-RMW count update
for unshared values), and (B) free-on-zero extends to **shared** objects via atomic counted RC +
acquire-before-free. Companion to
[PERCEUS-RC-DESIGN.md](PERCEUS-RC-DESIGN.md) §5 (thread-shared / atomic RC) and
[PERCEUS-S3-PLAN.md](PERCEUS-S3-PLAN.md).

## 0. Where S3.4 left us — the two costs S4 paid down

At the S3.4 boundary, `kdup`/`kdrop` (`kappart.h`) both took an **atomic CAS loop** on the header, and both
**early-returned to a no-op when the shared bit was set** (the old encoding used `KRC_SHARED_BIT = 0x80000000`
with the remaining 31 bits as the count). Two consequences:

- **Thread-local objects paid the atomic tax.** Every `kdup`/`kdrop` on a `tshare==0` object was a
  `compare_exchange_weak` loop — even though the object is fiber-private. The design's own warning
  (RC-DESIGN §5): *uniform atomic RC is 20–130% slower even single-threaded — the biased split is
  load-bearing, not optional.* Since S3.4 made RC default-on, **every program paid this.**
- **Shared objects were never reclaimed.** A `tshare==1` object's `kdup`/`kdrop` were no-ops, so its count was
  frozen and it (and its whole recursively-marked-shared subgraph) leaked to Boehm. The recursive mark-shared
  publish points (S3.1) already *identified* the shared set precisely; S4 makes it counted + freeable.

## 1. Deliverable A — the biased fast/slow split (the perf recovery)

**The soundness invariant** (the whole thing rests on this): *a non-atomic rc op is only ever performed by
the fiber that exclusively owns the object, before it is published.* The S3.1 recursive mark-shared at the
publish points (generated global/CAF cache release-store, fork/`forkIn`, promise completion,
fiber-exit-to-awaiters, TVar commit/new, AtomicRef publish, FiberRef registry/snapshot,
stored interrupt causes, blocking submit, fiber-local snapshot, wake/resume, plus the
write-into-already-shared cases) enforces it: an object is marked shared **before** it can
become reachable by a second fiber. So a
genuinely `tshare==0` object is fiber-private and no other fiber ever touches it.

- **Fast path (`tshare==0`):** an **atomic relaxed discriminator load** of the header, then a **direct
  non-RMW decrement/increment**, no CAS; free-on-zero exactly as today. The discriminator load is deliberately
  atomic so the shared-bit read is TSan/C-memory-model clean if publication races with a stale local owner.
  The count update is still non-atomic on the proven thread-local path; this is the common-case perf win.
  If the direct path reaches the representable max count, it sets the same sticky saturation bit used by the
  shared path and leaks to Boehm rather than returning an uncounted alias.
- **The shared-bit check is safe** because publish points recursively mark before making the value reachable
  by another fiber, and every post-publish owner observes the bit before it can take an RC slow path. No fiber
  may do a non-atomic count update on a shared object, including the origin fiber's own post-publish drops.
- **Ref/array storage reads preserve the same split.** `kref_get`/`karr_get` always return an owned value, but
  private cells read directly and take the ordinary thread-local `kdup`; only shared cells take the storage
  lock before duplicating the occupant. `kref_set`/`karr_set` mirror the split for the swap/drop barrier. This
  keeps S4-A's private fast path visible for first-class refs/arrays rather than replacing atomic RC traffic
  with an unconditional mutex.
- **Encoding decision.** S4 keeps the explicit `KRC_SHARED_BIT` flag plus a branch and reserves
  `KRC_SATURATED_BIT` below it, so the count mask is now the low 30 bits. The Koka-style signed
  compare/negative-rc fold remains a possible micro-optimization, but it is not required for S4 correctness and
  was not adopted because the TSan-clean discriminator load is the principled boundary for this runtime.

## 2. Deliverable B — shared-object atomic RC + reclamation

- **`kdup` (shared):** a checked **relaxed** atomic increment on the count, implemented as a single
  `fetch_add` on the common path. It does not need the decrement-side CAS loop because shared is one-way and
  increment has no zero/free transition. The header reserves a sticky saturation bit below the shared bit; if
  an increment observes the maximum representable low-30 count or an already-saturated header, the header is
  normalized to sticky saturation; max itself remains representable. Subsequent drops no-op and the object
  leaks to Boehm rather than wrapping the count or clearing the shared bit.
- **`kdrop` (shared):** a checked **release** atomic decrement; if it brings the count to 0, an **acquire fence
  before the recursive free** (RC-DESIGN §5: *"drop = release decrement with an acquire before free so child
  counts are synchronized"*), then `kfree_recursive`. The implementation uses a CAS decrement rather than a
  raw fetch-sub so release builds fail closed instead of wrapping a stale zero count. Because the mark is
  **recursive**, a shared object's children are all shared too, so the recursive free only ever performs
  atomic child drops — no mixed atomic/non-atomic descent.
- **Free-on-zero scope is unchanged:** the same `kis_rc_freeable` strict-immutable partition
  (`K_CTOR`/`K_REC`/`K_VARIANT`/`K_STR`/`K_BOUNCE`/`K_FAIL`). A shared object of a mutable/cycle/resource tag
  (`K_REF`/`K_ARRAY`/`K_THUNK`/`K_FGN`) stays Boehm-retained exactly as at S3 — the ref/lazy cycle collector
  is still "Later".
- **The concurrency-correctness crux** is the acquire-before-free: prove no fiber can still hold a reference
  to a shared object whose atomic count reached 0 (the last drop's release + the freeing fiber's acquire
  linearize the observation of count==0). This is the standard concurrent-RC pattern; it is the single most
  important thing to get right and to test (§5).

## 3. Re-verify the S3.3 write-barriers on now-freeable shared objects

The S3.3 drop-olds (STM commit `old->val`, `atomic_store` drop-old, `kref_set`/`karr_set`/`setFiberRef` on a
shared container, promise re-completion) became **real atomic drops → real reclamation of superseded shared
contents** at S4. This is the verification surface S3 never exercised. Re-check each:

- **STM commit `old->val`:** the superseded TVar value is shared; its atomic count includes every reader that
  `readTVar`'d it because `j_read` duplicates the sampled value under `g_stm` before the writer can drop the
  TVar's reference. The commit's drop-old releases the TVar's own reference; the value is freed only if no
  reader still holds it.
- **`atomic_store` drop-old / write-into-shared-ref/array:** the old cell value is shared; drop-old is now a
  real atomic decrement, freeing it only when no other holder remains. `AtomicRef`, `Ref`, and boxed-array
  reads all duplicate the observed value while holding the same lock/version protection that guards the cell
  load once the cell is shared; private Ref/array reads take the direct no-lock path under the same
  thread-local invariant as S4-A. A writer cannot drop the last cell reference before a shared reader owns its copy.

## 4. Publish-point exhaustiveness — re-audit at raised stakes

The biased split's soundness rests **entirely** on the mark-shared being **publish-point-exhaustive**: a
*missed* publish leaves a genuinely-shared object at `tshare==0`, so two fibers do non-atomic ops on it → a
data race → torn count → UAF. S3.0/S3.1 audited this while a missed mark was a *benign no-op*; at S4 a missed
mark is a **live data race**, so re-audit and **pin the invariant with an assert** (every KValue reachable
from a publish point is marked before the publishing release store — the S2.3c-style exhaustiveness pin,
extended). The practical enforcement tool is ThreadSanitizer (§5).

The implementation-level list is intentionally redundant with the S3 audit: generated C/LLVM
global and CAF caches mark before their process-wide release-store; runtime publication marks
forked actions, promise/fiber exits, wake/resume actions, interrupt causes, FiberRef snapshots,
TVar/AtomicRef cells, blocking-lane payloads, and every write into already-shared mutable
storage. RC-off builds still perform these publication marks because the shared bit is also
the synchronization discriminator for Ref/Array storage; RC-off only disables `kdup`/`kdrop`
counting/freeing.

## 5. Verification

1. **ThreadSanitizer (primary).** The biased split + shared reclamation is a *data-race* surface, so TSan is
   the S4 analog of S3's poison-on-free gate. `runtime/Makefile` now has a focused `tsan-rc` target over the
  shared-RC concurrency corpus (`atomic`, `fiberref_promise`, `parallel`, `race`, `stm`, `stm_retry`,
   `stm_orelse`, `blocking_lane`, `perceus_s3_prereq`, `perceus_s4_shared`), and
   `test/native/run-native-tests.sh` runs it as the
   S4 native gate. In `KRT2_TSAN` builds, Boehm collection/free is disabled for this lane because TSan does
   not understand Boehm's heap reuse; the poison and real-free lanes remain the reclamation oracles.
   Fork-isolated poison-oracle subcases inside `perceus_s4_shared` are excluded from the TSan build because
   this TSan runtime rejects starting scheduler threads after a multi-threaded `fork`; those subcases still run
   in `poison-rc`.
2. **Poison-on-free (from S3.2), extended to shared frees.** A shared object freed while another fiber holds
   it is a UAF → the `K_FREED` sentinel traps. `runtime/Makefile` now has a `poison-rc` target that runs the
   same shared-RC concurrency corpus under `KAPPA_POISON=1` + RC-on + parallel load (`KAPPA_RT_WORKERS=8`),
   and `test/native/run-native-tests.sh` runs it as the S4 poison gate.
   Native C stress tests that allocate or free from helper threads use `GC_pthread_create`, matching the
   runtime worker/reactor creation rule; raw watchdog-only pthreads remain valid because they do not touch
   Boehm-managed `KValue` storage.
3. **Perf recovery — the whole point.** `runtime/bench/rc_biased.c` and `make -C runtime bench-s4-rc` compare
   the thread-local direct-update fast path against the shared atomic slow path in one process, and also compare
   private no-lock `kref_get`/`karr_get` against shared locked `kref_get`/`karr_get`. The gate fails if the
   private storage reads are not close to the local RC baseline or do not clearly beat the shared locked paths.
   The native suite runs this as the S4 perf gate.
4. **Shared reclamation fires.** `runtime/tests/perceus_s4_shared.c` proves shared `Ref`/array reader counts
   keep overwritten values live and that the last reader drop reclaims them; the S3.2/S3.4 generated-drop
   real-free heap gates remain in the native suite for non-shared generated code.
5. **Publish-mark assertion.** Debug builds re-walk each graph after `krc_mark_shared_recursive` and assert
   every reachable `KValue` is shared. Runtime-private `K_FGN` payloads remain delegated to
   `krt2i_mark_fgn_payload_shared`, which has its own exhaustiveness assert for known runtime kinds.
6. **Invariants preserved:** RC-on == RC-off byte-identical, underflow-assert clean, conformance 2094/0,
   parity 150/0.

## 6. Risks

- **R-missed-publish (highest — now a live race).** A shared object not marked → two-fiber non-atomic race →
  UAF. Mitigate: the §4 re-audit + the mark-before-release assert + the TSan gate.
- **R-nonatomic-on-shared.** A non-atomic op on an object that is actually shared. Prevented by the
  mark-before-publish invariant; TSan catches any violation.
- **R-shared-free-race.** Freeing a shared object another fiber still holds. Prevented by atomic-count-0 +
  acquire-before-free (§2); the classic concurrent-RC hazard — the crux to test.
- **R-write-barrier-shared.** The S3.3 drop-olds become real on shared objects (§3) — re-verify.
- **R-perf-no-payoff.** If the biased fast path doesn't beat atomic-everywhere, S4 doesn't pay for itself —
  the perf gate (§5.3) is the backstop.
- **R-cycle (unchanged).** Shared refs/arrays/thunks stay Boehm-retained; the cycle collector is still Later.

## 7. Sub-stages, ordering, gates

| sub | what | gate |
|---|---|---|
| **S4.0** | biased-split encoding decision (explicit shared flag + TSan-clean atomic discriminator load) + fast/slow branch skeleton | landed; thread-local path uses direct count writes, shared path uses atomic slow path |
| **S4.1** | shared-object atomic RC (`kdup`/`kdrop` atomic on shared) + acquire-before-free + shared free-on-zero | landed; focused TSan, `poison-rc`, and shared-reclamation harnesses pass |
| **S4.2** | re-verify + turn the S3.3 write-barriers real on shared objects (§3) | landed; `perceus_s4_shared` covers shared Ref/array, promise poll, FiberRef snapshot, and STM same-pointer commit |
| **S4.3** | publish-point re-audit + wire the TSan RC-corpus gate (§4) | landed; debug recursive publish assertion, `runtime` `tsan-rc` target, and native-suite gate |
| **S4.4** | perf-recovery measurement + gate (biased vs shared atomic slow path, private vs shared ref/array-read paths) | landed; `bench-s4-rc` gate |

Ordering rationale retained for review: S4.0 introduced the biased branch, S4.1 made the shared branch counted
and reclaiming, S4.2 re-validated the S3.3 barriers now that shared drops are real, S4.3 wired the TSan corpus
gate for the publish-point invariant, and S4.4 added the fast/slow-path perf gate.

## 8. Scope notes

- **S4 is backend-agnostic and runtime-focused.** The atomic/non-atomic decision is a runtime branch on the
  `tshare` bit in `kdup`/`kdrop` — **no codegen change**, so S4 needs neither the LLVM-RC port nor the
  KCore/KBackendIR split. The perf recovery applies to whichever backend emits RC (the C/runtime path today;
  LLVM once LLVM-RC lands).
- **Independent of the layout arc.** Unlike S5 (FBIP, which needs typed KBackendIR constructors), S4 does not
  touch representation. It can proceed in parallel with, or before, the KBackendIR split.

## Critical files

- `runtime/kappart.h` — `kdup`/`kdrop` biased fast/slow split; explicit shared-bit encoding; checked release
  decrement + acquire-before-free on shared drops.
- `runtime/value.c` — `kfree_recursive` on shared objects (atomic child drops); the shared write-barrier drops
  (already present, become real).
- `runtime/rt.c` / `runtime/stm.c` / `runtime/atomic.c` — publish-point marks (re-audit + the mark-before-
  release assert); the write-barriers on shared containers (§3).
- `runtime/Makefile` — the focused `tsan-rc` lane, `poison-rc` lane, and `bench-s4-rc` perf gate.
- `runtime/bench/rc_biased.c` — the S4 biased-RC fast/slow-path and private/shared ref/array-read perf gate.
- `runtime/tests/perceus_s4_shared.c` — shared-counted-RC reclamation and transfer-return regressions.
- `test/native/run-native-tests.sh` — the TSan RC-corpus gate, poison RC-corpus gate, the perf-recovery gate,
  and the existing generated-drop heap-high-water reclamation checks.

## Spec anchors

- **RC-DESIGN §5** (thread-shared / atomic RC — the biased split, explicit shared/saturation header flags, the publish points,
  the acquire-before-free, the 20–130% cost warning) and **§7** (S4 in the staging).
- **§32.2.9 / §32.2.10** (concurrency / atomics / TVar publish ordering), **§18.1.x** (fibers, promises,
  scopes, fiber-refs — the publish points).
- **§34.4.1** (memory-management obligations).
