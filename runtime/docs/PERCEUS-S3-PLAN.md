# Perceus Stage S3 — Implementation Plan (flip free-on-zero)

Status: **S3.0 through S3.4 landed for the C/runtime path.** S0→S2.3d have landed and been independently reviewed sound
([PERCEUS-S2.3-DROP-COMPLETION.md](PERCEUS-S2.3-DROP-COMPLETION.md)): dup/drop placement is correct and
`rc` is maintained. S3 wires the guarded `kdrop` free-on-zero branch for the conservative strict-immutable
FREESET, adds S3.3 overwrite/publication-failure precision drops, and makes RC validation/emission default-on
for native builds with `KAPPA_PERCEUS_RC=0` as the explicit RC-off differential baseline. That baseline disables
both generated ownership maintenance and runtime RC effects in the generated binary. At the S3 boundary, retained
tags, shared objects, cycles, resources, and LLVM output remained Boehm-backed until their later stages. Companion to
[PERCEUS-RC-DESIGN.md](PERCEUS-RC-DESIGN.md) (the arc, §4 cycles / §5
thread-shared / §7 staging) and [PERCEUS-S2-PLAN.md](PERCEUS-S2-PLAN.md) (the dup/drop layer S3 turns live).
Historical note: this document describes S3's landed boundary. S4 has since replaced S3's shared-value
dup/drop no-op with counted shared atomic RC for the strict immutable FREESET; see
[PERCEUS-S4-PLAN.md](PERCEUS-S4-PLAN.md) for the current shared-object state.

## 0. The transition that reshapes everything — the risk model inverts

Through all of S2 the failure modes were **benign**: a missed drop was a leak, a double-drop / missed-dup
tripped the DEBUG `rc`-underflow assert, and Boehm remained the actual reclaimer, so nothing
was ever used after free. S3 removes that net. The moment `kdrop` frees on zero, the design's *"dangerous
one"* (RC-DESIGN §7 failure table) goes live: **a missed dup / double drop is now a use-after-free.** The
backstop's job inverts — it stops catching *leaks* (those become real bugs we no longer see for free) and
must start catching *double-frees*.

So S3 is not "add `GC_FREE` to `kdrop`." It is gated on three things, in order:
1. **A conservative scope** — free-on-zero only the shapes where reclamation is provably safe (§1).
2. **The runtime prerequisites** — the counting/concurrency/stack-safety facts the flip depends on (§2).
3. **A differential flip** — free-on-zero ON while an effective UAF oracle (poison-on-free / Boehm debug,
   with ASan/UBSan as a supplemental native sanitizer) watches (§4).

The S2.3 reviews already discharged the *placement* half (dup/drop are correct under the backstop). S3 adds
the *reclamation* half and re-validates it with a UAF detector instead of an underflow assert.

## 1. The central decision — WHICH shapes free-on-zero at S3

At the S3 boundary, free-on-zero was only sound for **acyclic, non-shared, non-resource** objects. Partition the runtime tags
(counted shapes per RC-DESIGN §2):

**RC-freed at S3 (the strict, immutable, acyclic core — "most of the win"):**
`K_CTOR` (n-ary), `K_REC`, `K_VARIANT`, `K_STR`, `K_BOUNCE`, `K_FAIL`. These are built children-first ⇒
**acyclic by construction** (RC-DESIGN §4) ⇒ garbage-free with no cycle collector.

**Retained on Boehm at S3 (rc maintained, not RC-freed in this stage; `K_FGN` remains never-RC-free):**
- `K_REF`, `K_ARRAY` — mutable ⇒ **cycle sources** (RC-DESIGN §4.1); the mutable-cell cycle protocol is
  "Later".
- `K_THUNK` — the lazy tie-the-knot **cycle source** (§4.2); opt-in future work.
- `K_CLO`, `K_IO`, `K_IOTAIL`, `K_IOEFFECT`, `K_IOFINALLY` — closure/action wrappers capture `KEnv`
  chains and finalizer arrays whose ownership/free protocol is not represented yet. They remain counted for
  paired dup/drop validation, but Boehm-retained until the free site can prove env/action ownership.
- `K_BIGINT` — the GMP `mpz` has its own allocation lifecycle (Boehm-routed in `gc.c`); not worth an RC
  path for S3.
- `K_BYTE`, `K_BYTES` — scalar/byte-sequence carriers are retained until the byte slab ownership/free path is
  represented. `K_BYTE` normally uses immediates, but the boxed tag remains a valid runtime shape.
- `K_NATIVE` — a native host-binding action wrapper. Pure saturated natives immediately return their result,
  but partial/effectful natives are suspended action values, so they stay with the retained action-wrapper set
  until native-action ownership is represented.
- `K_FGN` — a **resource handle** whose lifetime is `defer`/`using`/the ExitStack, NOT memory (§1,
  RC-DESIGN §2/§34.4.1). Freeing it on `rc==0` would double-close. **Never RC-freed, at S3 or ever.**
- **Any `tshare==1` (thread-shared) object**, regardless of tag — deferred to S4 (§2.2).

This "immutable strict data frees; everything mutable/lazy/action/foreign/shared stays on Boehm" split is
exactly the design's *"ship RC for strict data first"* (§4). It captures the n-ary ctor/record/string
reclamation that FBIP (S5) then optimizes, while Boehm **remains linked** for the retained tags and as the
flip-window oracle. Encode the partition once as
`kis_rc_freeable(v) = !kis_imm(v) && tshare(v)==0 && tag ∈ FREESET`; S3.1 tests and the disabled
`kfree_recursive` skeleton consult it, and S3.2 makes it the single guard on the `kdrop` free branch.

## 2. Runtime prerequisites — must land BEFORE the flip (Phase A)

### 2.1 Derived-container alias counts — LANDED, the UAF-direction runtime gaps
`karr_new` previously filled N slots with a single `init` after one **owned** transfer
(`__newArray = [borrowed, owned]`, S2.3c): `for (i<n) slab[i]=init;` with no per-slot `kdup`. Even though
the *array* is Boehm-retained, its **elements are RC-freed shapes**. So N array aliases are backed by an rc
that counts **one** reference; once the caller's other references drop, RC frees the element while N−1 array
slots still point at it ⇒ **UAF**. **S3.1 fix:** `karr_new` now transfers the first slot and `kdup(init)`s
each additional boxed slot. This is unconditional rc bookkeeping because the free branch is still off; when
arrays later join the FREESET, their free path must drop exactly one counted reference per boxed slot.

Record rest binders have the same shape in a strict freeable container: `krec_without` builds a fresh
residual `K_REC` whose kept fields alias fields of the source record. S3.1 now `kdup`s each kept field, so
dropping the source record under S3.2 cannot free a field still owned by the residual record. The residual
record's name array is metadata under Boehm; a future record-representation pass can make that metadata
precisely owned, but it is not a child-value UAF path.

### 2.2 Thread-shared mark + no-op shared dup/drop — LANDED for S3.1, concurrency soundness
The runtime is M:N concurrent; an RC-freed immutable object can be **published** across fibers and then
concurrently dropped ⇒ non-atomic `rc--` races ⇒ premature/double free. At the S3 boundary the full atomic split was S4, but its
**cheap half must move forward into S3**: the one-time recursive **mark-shared** at publication boundaries,
riding the **sign of the header `rc`** (Koka's negative-rc trick). Then `kis_rc_freeable` returned false for
`tshare==1`, so shared objects **deferred to Boehm**. S3.1 also made `kdup`/`kdrop` on already-shared objects
no-ops, because the low count was ignored until S4's counted shared-object RC.
S4 supersedes this boundary: shared objects now use counted atomic RC and can be free-on-zero reclaimed when
their tag is in the strict immutable FREESET. (This is a deliberate
refinement of RC-DESIGN §7, which lumps mark+atomic-ops together in S4; S3.1 already makes the header word
atomic so the shared-bit transition and no-op shared dup/drop are data-race-free, while counted shared-object
RC remains a later perf/reclamation recovery.)

S3.1 implements the high-bit encoding, recursive mark traversal, and mark-before-publish at synchronized
runtime publication boundaries: fiber spawn/finish/wake, promise completion, blocking-worker submission,
fiber-local snapshot publication, TVar commit/new, AtomicRef creation/store/exchange/CAS success/fetch-update,
FiberRef init, generated global/CAF caches, and stored interrupt causes. Generated caches use acquire/release
atomic publication so a reader cannot observe the cached pointer without also observing the prior shared marks.
Writes into already-shared plain refs/arrays/thunks mark the incoming value as a conservative RC aid, but
ordinary refs/arrays/thunks were not claimed as high-level publication APIs in S3. S4 later added storage
synchronization for Ref/array ownership safety; that lock does not turn every plain cell operation into a
semantic publish point. At S3, shared objects preserved their existing low count, S3.1 dup/drop did not mutate
it, and `kis_rc_freeable` rejected them so S3.2 would not free them. S4 replaces that historical no-op policy
with atomic counted shared dup/drop for the same strict immutable FREESET.

### 2.3 Iterative drop-descent — LANDED for S3.2 robustness
A recursive `kfree` of a long list / deep tree recurses O(depth) on the C stack. The design's own criterion
is *"a big list is freed incrementally as it is consumed"* (RC-DESIGN §3). Implement `kfree_recursive` with
an **explicit worklist** (or the classic freed-node-as-worklist-link trick), not native recursion, so
freeing an N-element spine is O(N) time and O(1) stack. The S3.2 runtime harness includes a deep-structure
stress fixture that would overflow a naïve recursive drop. S3.2 uses an explicit worklist with stack-scanned inline storage for ordinary shallow frees and a
scanned heap overflow buffer only for deeper graphs. That keeps the common free-on-zero path non-allocating
while preserving Boehm visibility for pending children during dynamic growth.

### 2.4 Write barriers / CAS-fail / promise-recomplete drops — LANDED for S3.3 precision
S3.3 adds the leak-direction ownership barriers that S2.3c intentionally left to the runtime stage:
`karr_set`/`kref_set`/`setFiberRef`/`krt2_atomic_store` drop the displaced occupant, failed CAS drops the
unpublished `desired`, promise re-completion drops the losing `Exit`, and STM drops duplicate/rolled-back
journal-owned writes. No-return stores also consume an owned self-assignment argument: if the stored pointer is
the same as the old occupant, the barrier drops one counted reference while keeping the cell value live.
`krt2_atomic_exchange` is deliberately different: it returns the displaced old value to the caller, so it does
not drop that returned ownership. For publication paths that mark contents shared (`AtomicRef`, TVar commit),
the S3 drop was mostly correctness scaffolding because shared `kdrop` was a no-op until S4 shared RC; unique
`Ref`/array/FiberRef cells get current free-on-zero reclamation for displaced strict immutable values. These
barriers remain scoped to retained mutable containers; refs/arrays themselves are still outside the S3 FREESET
until the post-S3 cycle/container protocol.

### 2.5 Arity-guard alignment — LANDED before caller-drops widen
The S2.3c `argConvSelectGlobal` arity check counts kind-domain params differently from `classifyCallArgs`
(DROP-COMPLETION §(d) arity pin). Inert today, but reconcile (count by the `erasedOrKind` rule, or emit an
S1.5 finding on mismatch) before any stage widens caller-side drops, so a future kind-domain-param prim
cannot left-shift an `ArgBorrowed` onto a storing position.

S3.1 reconciles this in the shared representation table helper used by `repSelect` and
`argConvSelectGlobal`: implicit, `Q0`, and kind-domain parameters are skipped consistently with ownership's
runtime-argument filter.

### 2.6 S3.0/S3.1 re-review findings — hardening carried to S3.2 (all LOW; inert under the current backstop)

The S3.0/S3.1 re-review (four adversarial lenses, all SOUND; the prior shared-`KEnv` UAF and FREESET-overreach
blockers both resolved) surfaced five low-severity, forward-looking items. S3.2 settled the FGN payload pin
and free-visitor assert; the remaining items stay scoped to later precision/backend stages.

1. **The free-on-zero win is C-backend-only until the LLVM backend emits `kdup`/`kdrop` (scope, not a bug).**
   `generateLL` runs the C backend purely as the R-path validator, then emits LLVM with an explicit
   `krc_set_enabled(0)` runtime counting/freeing gate. S4 publish marking may still be emitted because
   shared bits are synchronization metadata, not ownership maintenance. So RC-on == RC-off on LLVM is trivial
   today for ownership effects, but the C backend reclaims on `rc==0` while LLVM emits no `kdrop` and stays
   fully Boehm-backed — an *under*-free, never a UAF. Free-on-zero therefore covers the C backend only;
   extending reclamation to LLVM is a separate task (grow LLVM dup/drop emission), and the §5.3 garbage-free
   trend applies to C until then.
2. **Pin the FGN-payload mark-shared exhaustiveness (the S2.3c-style invariant).**
   Landed in S3.2: `krt2i_mark_fgn_payload_shared` (`rt.c`) now handles the known runtime `K_FGN` kinds
   explicitly. It recursively marks the unprotected `RESUMPTION` and `ABORT_EXIT` continuation payloads, and
   pins the lock-owned `Fiber`/`Scope`/`Promise`/`Monitor`/`TVar`/`AtomicRef` kinds to their synchronized
   publication-site marks instead of recursively taking locks from the generic value walker. `FiberRef` is
   documented as carrying no hidden payload today, and DEBUG builds assert for unhandled `rt.*`/`krt2.*`
   kinds. User FFI handles remain outside this runtime-private exhaustiveness pin.
3. **Make `kfree_visit`'s `default` assert-unreachable in DEBUG.** The switch falls through to `kgc_free(v)`
   for any tag without an explicit case. Inert now (every FREESET tag has a case), but a
   future FREESET addition that forgets its `kfree_visit` case would free the shell while leaking its boxed
   children — a partition/visit desync. A DEBUG `assert(unreachable)` makes that fail loudly instead of
   leaking silently.
4. **Give `mark_cont_stack_shared` a visited guard (defense-in-depth).** The `Cont`-chain walker terminates
   only on `&g_done`; unlike the value-graph marker (cycle-safe via the shared bit), it would infinite-loop on
   a cyclic `Cont` chain. `Cont` chains are strictly acyclic today (including the `KK_ABANDON` re-link), so
   this is robustness only — but a future continuation-capture change could regress it silently.
5. **`dropStaticGlobalPrefixArgs` skips a self-call nested inside another self-call's argument** (`CoreOps.hs`;
   `mapTermWithDepth` stops at the first rewrite). Fail-closed, not a miscompile: the un-trimmed nested call
   keeps `n+static` args, `lr1SelfArgs` rejects it, and the worker declines to the boxed path — a missed
   scalar-worker optimization only. Re-check if a future stage widens the tail grammar.

## 3. The free-on-zero mechanism (Phase C) — `kappart.h` + `value.c`

- **`kdrop`** (`kappart.h`): after the thread-local count decrement, calls
  `kfree_recursive(v)` when the old count was 1 and `kis_rc_freeable(v)` holds. Immediate/shared/retained-tag/resource
  cases fall through exactly as before. In S3, shared values remained no-op until S4 reclamation; S4 has since
  replaced that with atomic counted shared dup/drop and guarded shared free-on-zero for FREESET tags.
- **`kfree_recursive(v)`** (`value.c`): per-tag, decrements each boxed child, pushes zero-count freeable
  children onto the iterative worklist, then releases the shell:
  - children: `K_CTOR` `as.ctor.args[0..argc-1]`; `K_REC` `as.rec.vals[0..n-1]`; `K_VARIANT`
    `as.var.payload`; `K_BOUNCE` `fn`+`arg`; `K_FAIL` `err`. `K_CLO`/`K_IO`/action/native wrappers stay out
    of the FREESET until env/action ownership is represented.
    (`K_STR` bytes are an atomic buffer — no child drops.)
  - shell + slabs: `GC_FREE` the args/vals/env slab and the `KValue` (`gc.c` — add a thin `kgc_free`
    wrapper; a per-size free-list is the S5 FBIP reuse target, out of scope here). Never `GC_FREE` a
    retained-tag or `K_FGN` cell.
  - **iterative** (§2.3): push children onto the inline/scanned-overflow worklist rather than recursing.
- **Immediates** (`kis_imm`) already short-circuit both ops. **`K_FGN`** is never reached (excluded by
  `kis_rc_freeable`) — re-pin the §1 carve-out at the free site with a comment + a `usingsusp` regression.

## 4. The differential flip — how to turn it on without shipping a UAF (Phase D)

The flip is staged so free-on-zero is exercised under a watchdog before it is trusted:
- **D1 — mechanism, still OFF.** Land `kfree_recursive` + `kis_rc_freeable` but keep the public entry disabled
  and do not call the free branch. Observable behavior remains RC-on == RC-off; nothing frees. **Landed in S3.1.**
- **D2 — ON in the C/runtime path.** Enable free-on-zero **in the C backend/runtime path** (per §2.6.1 —
  LLVM stays fully Boehm-backed until it grows its own `kdup`/`kdrop` emission). S3.2 is validated by the
  runtime free-on-zero harness, the generated-code ownership gates, native RC-on-vs-RC-off output parity, and
  allocation gates. A dedicated poison-on-free harness is the effective Boehm-heap UAF oracle shipped with
  S3.2; the native RC corpus lane runs generated binaries with `KAPPA_POISON=1`, including a non-vacuous
  generated-drop fixture. ASan remains useful for ordinary native memory bugs but is not sufficient by itself
  for `GC_FREE` managed cells.
- **D3 — garbage-free validation.** With free-on-zero ON, confirm the RC-freed shapes' live set does **not**
  monotonically grow (`KAPPA_GC_STATS` heap-high-water on an allocation-heavy loop) — this is the payoff and
  the proof that drops actually reclaim. **Landed in S3.4** via the generated-drop N=100 vs N=100000 heap gate
  in the real-free lane (`KAPPA_POISON` unset), while the separate poison run stays the UAF oracle.
- **D4 — default on.** Free-on-zero is the default; Boehm stays linked for the retained tags (§1) + cycles;
  the oracle build stays in CI (RC-DESIGN §7: *"keep a Boehm-as-backstop build in CI through the S2–S3
  window"*). **Landed in S3.4** for native builds; set `KAPPA_PERCEUS_RC=0` only for explicit RC-off
  differential baselines, where generated `main` calls `krc_set_enabled(0)` before runtime execution.

## 5. Verification

1. **Poison-on-free / Boehm-debug UAF oracle (primary for Boehm-managed cells).** The S3.2 poison harness
   retains freed shells, stamps them `K_FREED`, and verifies runtime accessors plus raw primitive/show readers
   trap deliberately injected stale aliases. `KAPPA_POISON=1` enables the same oracle from `krt_init` for
   generated binaries. This is the replacement for the S2 underflow-only backstop; ASan/UBSan is supplemental
   because Boehm `GC_FREE` is outside ASan's normal heap.
2. **RC-on == RC-off output-identical** (the S2 invariant persists — reclamation must not change observable
   behavior) + **conformance 2094/0** + **llvm-parity 150/0**. The native RC lane builds each corpus case
   with RC off and RC on, then compares both native outputs with the interpreter.
3. **Garbage-free trend** (`KAPPA_GC_STATS`): RC-freed-shape heap-high-water bounded on a tight
   alloc/drop loop; not monotonic growth.
4. **Concurrency stress under the sanitizer/oracle lanes** (`fork`/`promise`/`stm`/`race`/`fiber-*` cases): exercises the
   S3 `tshare` mark + skip boundary and, after S4, the counted atomic shared-RC path.
5. **Resource carve-out (§1)** (`usingsusp.kp`/`usinginterrupt.kp`/`defer-*`): no `K_FGN`/resource cell is
   freed by RC; the ExitStack still owns handle release.
6. **Deep-structure stress** (§2.3): a million-node spine frees without stack overflow.

## 6. Risks

- **R-UAF (the whole category, now live).** Mitigated by the conservative FREESET (§1), the proven S2.3
  placement, `karr_new`/`tshare` prerequisites, the poison-on-free/Boehm-debug oracle, and supplemental
  native sanitizers (§4). This is *the* risk S3 exists to manage.
- **R-derived-container-undercount** → `karr_new` per-slot dup + `krec_without` kept-field dup, §2.1
  (mitigated before S3.2).
- **R-shared-race** → atomic header ops + `tshare` mark + no-op shared dup/drop at S3, §2.2 (blocking);
  counted shared-object reclamation is S4 and supersedes the no-op shared policy.
- **R-stack-overflow** → iterative drop-descent, §2.3.
- **R-mixed-collector.** An RC-freed cell must not be Boehm-reachable. It is not: `rc==0` means no counted
  reference — *provided* every reference is counted, which is exactly what `karr_new` (§2.1) and the owned
  ref/TVar transfers (S2.3c) guarantee. A Boehm-retained container holding an RC-freed element is the
  `karr_new` case; refs hand out a single counted alias (safe).
- **R-cycle-leak** → refs/arrays/thunks retained on Boehm by design; the incremental cycle collector over
  ref/lazy nodes is "Later" (RC-DESIGN §4/§7).
- **R-resource-free** → `K_FGN` excluded from the FREESET (§1); re-pinned at the free site.

## 7. Sub-stages, ordering, gates

| sub | what | gate |
|---|---|---|
| **S3.0** | `kis_rc_freeable` tag partition (§1) + `tshare` sign encoding infra; free-on-zero still OFF | landed; no reclamation |
| **S3.1** | Phase A prereqs: `karr_new` per-slot dup (§2.1), atomic header + `tshare` mark + no-op shared dup/drop (§2.2), iterative `kfree_recursive` skeleton (§2.3), arity-guard reconcile (§2.5) | landed; RC-on == RC-off, underflow-clean, nothing frees yet |
| **S3.2** | wire the guarded free branch in `kdrop`; make the worklist root-safe/non-allocating on the common path; close the returning-arm match and projection-result ownership entry gates; run generated drops under poison | landed for C/runtime; runtime S3.2 harness + native RC/generated-code/allocation gates pass; LLVM remains Boehm-backed |
| **S3.3** | precision: write-barrier drop-old + CAS/promise drops (§2.4) | landed; runtime free harness covers ref/array/FiberRef, STM duplicate/rollback, promise recomplete, and failed CAS |
| **S3.4** | default-on; Boehm retained for un-RC'd tags; oracle build stays in CI (§4 D4) | landed for C/runtime; native harness defaults to RC-on, keeps explicit RC-off differential baselines that disable generated+runtime RC, runs poison-oracle generated binaries, and gates generated-drop heap high-water plus positive `frees=` counts against an explicit RC-off `frees=0` baseline |

Ordering rationale: the tag partition + `tshare` infra must precede any free; the
Phase A prerequisites all precede S3.2 because each closes a distinct UAF path (array under-count, shared
race, stack overflow). S3.2 also closed the ownership entry gates recorded in ROADMAP/S2.3d: returning-arm
match cell-drop tightening, projection-result ownership through nested/control expressions, and the current
S2.3c storing-primitive audit. Precision write-barriers (S3.3) were leak-direction until S3.4 made RC the
default native path; the landed default-on gate keeps the poison oracle and explicit RC-off comparison visible.

## Critical files

**Landed S3.0-S3.4 runtime/backend files:**
- `runtime/kappart.h` — `kis_rc_freeable`, the shared-bit accessors, `kfree_recursive` prototype, the poison
  sentinel/API, and the S3 `kdup`/`kdrop` immediate + shared no-op guards that S4 later supersedes with
  counted atomic shared RC. S3.2 enables the guarded `kdrop` free branch.
- `runtime/value.c` — iterative `kfree_recursive` per-tag child traversal + shell release, stack-inline/scanned
  overflow worklist, poison-on-free shell retention for the oracle lane, `karr_new` per-slot dup (§2.1),
  zero-length owned-init consumption, record-rest kept-field dups, shared ref/array/thunk incoming-value marks,
  and `kref_set`/`karr_set` displaced-value drop barriers.
- `runtime/gc.c` — `kgc_free` (`GC_FREE`) wrapper and debug free counter for the S3.2 runtime harness.
- `runtime/rt.c` / `runtime/stm.c` / `runtime/scope.c` / `runtime/atomic.c` / `runtime/reactor.c` —
  recursive shared marking before runtime publication points (§2.2), runtime-private `K_FGN` payload-marking
  exhaustiveness pins, and the S3.3 barriers for FiberRef overwrite/modify aliasing, STM journal truncation,
  promise recomplete, failed CAS, and AtomicRef store.
- `src/Kappa/Backend/C.hs` / `src/Kappa/Backend/LLVM.hs` — mark generated global/CAF cache values shared
  before process-wide publication. S4 made this mark independent of the RC counting/freeing gate because the
  shared bit also selects synchronized Ref/Array storage access. C validates/emits ownership maintenance by
  default while preserving an explicit RC-off baseline; LLVM runs the C-side RC validator but emits
  `krc_set_enabled(0)` and no generated ownership `kdup`/`kdrop` until LLVM ownership emission lands, while
  still emitting publication marks.
- `src/Kappa/Backend/Driver.hs` / `src/Kappa/Backend/C.hs` — `KAPPA_PERCEUS_RC=0` is the explicit off baseline;
  unset/true/on keep native RC validation and emission enabled by default, while off builds emit
  `krc_set_enabled(0)` so runtime counting/freeing barriers are inert too.
- `src/Kappa/Backend/Repr.hs` / `src/Kappa/CoreOps.hs` — runtime-argument mask alignment for kind-domain
  parameters (§2.5) and scalar-worker static-prefix rewrites.
- `runtime/tests/perceus_s3_prereq.c`, `runtime/tests/perceus_s3_free.c`, `runtime/tests/perceus_s3_poison.c`,
  `test/Spec.hs`,
  `test/native/run-native-tests.sh`, `test/native/llvm-parity.sh` — S3 prerequisites, free-on-zero,
  S3.3 transfer/drop regressions, default-on/off-baseline validation, generated-code, poison, and real-free
  heap gates.

**Remaining post-S3 work:**
- `src/Kappa/Backend/LLVM.hs` — emit and validate LLVM `kdup`/`kdrop` before claiming LLVM free-on-zero.
- `runtime/gc.c` / `src/Kappa/Backend/Driver.hs` — broader Boehm-debug/poison corpus lane plus supplemental
  ASan/UBSan build lanes beyond the current `KAPPA_POISON=1` native RC generated-binary lane.
- `test/native/run-native-tests.sh` — broader oracle/sanitizer corpus runs, concurrency stress, and resource
  carve-out regressions beyond the current default-on generated-drop poison oracle and real-free heap gate.
