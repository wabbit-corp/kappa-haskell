# Perceus Stage S3 — Implementation Plan (flip free-on-zero)

Status: **S3.0 + S3.1 landed; S3.2+ pending.** S0→S2.3d have landed and been independently reviewed sound
([PERCEUS-S2.3-DROP-COMPLETION.md](PERCEUS-S2.3-DROP-COMPLETION.md)): dup/drop placement is correct and
`rc` is maintained. The S3.0/S3.1 prerequisites are now in place: the freeable-tag partition, the shared-bit
encoding and marking, per-slot array init counts, a disabled iterative `kfree_recursive` skeleton, and the
compiler/runtime-argument arity alignment. `kdrop` still **never frees** — Boehm reclaims until S3.2 wires
the free-on-zero branch. Companion to [PERCEUS-RC-DESIGN.md](PERCEUS-RC-DESIGN.md) (the arc, §4 cycles / §5
thread-shared / §7 staging) and [PERCEUS-S2-PLAN.md](PERCEUS-S2-PLAN.md) (the dup/drop layer S3 turns live).

## 0. The transition that reshapes everything — the risk model inverts

Through all of S2 the failure modes were **benign**: a missed drop is a leak, a double-drop / missed-dup
trips the DEBUG `rc`-underflow assert — and in every case **Boehm still frees**, so nothing
is ever used after free. S3 removes that net. The moment `kdrop` frees on zero, the design's *"dangerous
one"* (RC-DESIGN §7 failure table) goes live: **a missed dup / double drop is now a use-after-free.** The
backstop's job inverts — it stops catching *leaks* (those become real bugs we no longer see for free) and
must start catching *double-frees*.

So S3 is not "add `GC_FREE` to `kdrop`." It is gated on three things, in order:
1. **A conservative scope** — free-on-zero only the shapes where reclamation is provably safe (§1).
2. **The runtime prerequisites** — the counting/concurrency/stack-safety facts the flip depends on (§2).
3. **A differential flip** — free-on-zero ON while a double-free oracle (Boehm + ASan) still watches (§4).

The S2.3 reviews already discharged the *placement* half (dup/drop are correct under the backstop). S3 adds
the *reclamation* half and re-validates it with a UAF detector instead of an underflow assert.

## 1. The central decision — WHICH shapes free-on-zero at S3

Free-on-zero is only sound for **acyclic, non-shared, non-resource** objects. Partition the runtime tags
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
concurrently dropped ⇒ non-atomic `rc--` races ⇒ premature/double free. The full atomic split is S4, but its
**cheap half must move forward into S3**: the one-time recursive **mark-shared** at publication boundaries,
riding the **sign of the header `rc`** (Koka's negative-rc trick). Then `kis_rc_freeable` returns false for
`tshare==1`, so shared objects **defer to Boehm**. S3.1 also makes `kdup`/`kdrop` on already-shared objects
no-ops, because the low count is ignored until S4's counted shared-object RC.
S4 later gives shared objects real counted atomic RC *and* extends free-on-zero to them. (This is a deliberate
refinement of RC-DESIGN §7, which lumps mark+atomic-ops together in S4; S3.1 already makes the header word
atomic so the shared-bit transition and no-op shared dup/drop are data-race-free, while counted shared-object
RC remains a later perf/reclamation recovery.)

S3.1 implements the high-bit encoding, recursive mark traversal, and mark-before-publish at synchronized
runtime publication boundaries: fiber spawn/finish/wake, promise completion, blocking-worker submission,
fiber-local snapshot publication, TVar commit/new, AtomicRef creation/store/exchange/CAS success/fetch-update,
FiberRef init, generated global/CAF caches, and stored interrupt causes. Generated caches use acquire/release
atomic publication so a reader cannot observe the cached pointer without also observing the prior shared marks.
Writes into already-shared plain refs/arrays/thunks mark the incoming value as a conservative RC aid, but
ordinary refs/arrays/thunks are not cross-fiber synchronization primitives (§32.2.10) and are not claimed as
publication boundaries. Shared objects preserve their existing low count but S3.1 dup/drop does not mutate it,
and `kis_rc_freeable` rejects them so S3.2 will not free them.

### 2.3 Iterative drop-descent — SKELETON LANDED for robustness
A recursive `kfree` of a long list / deep tree recurses O(depth) on the C stack. The design's own criterion
is *"a big list is freed incrementally as it is consumed"* (RC-DESIGN §3). Implement `kfree_recursive` with
an **explicit worklist** (or the classic freed-node-as-worklist-link trick), not native recursion, so
freeing an N-element spine is O(N) time and O(1) stack. The 8 MiB fiber stack (L0) would mask this on the
current corpus, so S3.2 should add a deep-structure stress fixture that would overflow a naïve recursive
drop. S3.1 has the explicit-worklist free skeleton and child traversal in place, but the public entry is
fail-closed/no-op and is not called from `kdrop` until S3.2.
Before that flip, the worklist allocation itself must be made GC-root-safe or non-allocating so Boehm cannot
miss children that are reachable only from the pending free stack.

### 2.4 Write barriers / CAS-fail / promise-recomplete drops — NON-blocking (leak-direction), sound to add
`karr_set`/`kref_set`/`writeTVar`/`setFiberRef`/atomic store+exchange overwrite without dropping the old
occupant; CAS-failure and promise re-completion never drop the un-stored `owned` arg (S2.3c review,
DROP-COMPLETION §(d)). At S3 these are **leaks, not UAFs** — the overwritten immutable value simply keeps the
container's uncounted +1 and is Boehm-reclaimed. They are **sound to add within S3** as a precision win (a
`kref_set` drop-old reclaims the old immutable contents precisely) and become **blocking** only when
refs/arrays themselves join the FREESET (post-S3 cycle protocol). Schedule in Phase C, not Phase A.

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
blockers both resolved) surfaced five low-severity, forward-looking items. None is a defect while free-on-zero
is off; each is a thing to settle before or during S3.2.

1. **The free-on-zero win is C-backend-only until the LLVM backend emits `kdup`/`kdrop` (scope, not a bug).**
   `generateLL` (`LLVM.hs` ~459) runs the C backend purely as the R-path validator, then emits RC-op-free
   `.ll`. So RC-on == RC-off on LLVM is trivial today (identical `.ll`), but at S3.2 the C backend reclaims on
   `rc==0` while LLVM emits no `kdrop` and stays fully Boehm-backed — an *under*-free, never a UAF. **S3.2 must
   state that free-on-zero covers the C backend only**; extending reclamation to LLVM is a separate task (grow
   LLVM dup/drop emission), and the §5.3 garbage-free trend applies to C until then.
2. **Pin the FGN-payload mark-shared exhaustiveness (the S2.3c-style invariant).**
   `krt2i_mark_fgn_payload_shared` (`rt.c`) handles only `RESUMPTION` and `ABORT_EXIT`; the other six `K_FGN`
   kinds are safe *only because* each marks its embedded `KValue`s at its own synchronized write site
   (Promise→exit at complete, TVar box→val at commit, AtomicRef→cell at store/CAS/fetch-*, Fiber→exit at
   finish; SCOPE/MONITOR carry no user `KValue`). That is an unstated cross-cutting invariant: a future FGN
   kind, or a create-time-set field reachable via a shared handle, becomes a silent S3.2 UAF. Before the flip,
   either mark the value-bearing kinds defensively at the recursive FGN site, or add an assert/comment pinning
   *"every FGN-embedded `KValue` is marked at its write site"* — the analog of the S2.3c
   storing-prims-exhaustive pin.
3. **Make `kfree_visit`'s `default` assert-unreachable in DEBUG.** The switch falls through to `kgc_free(v)`
   for any tag without an explicit case (`value.c` ~205). Inert now (every FREESET tag has a case), but a
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

- **`kdrop`** (`kappart.h`): after the thread-local count decrement, add
  `if (krc_count(v) == 0 && kis_rc_freeable(v)) kfree_recursive(v);`. Immediate/shared/retained-tag/resource
  cases fall through exactly as today; shared values remain no-op until S4 reclamation. Guard the whole free
  branch on the S3 build/flag so the OFF path still performs no reclamation.
- **`kfree_recursive(v)`** (new, `value.c`): per-tag, `kdrop` each boxed child, then release the shell:
  - children: `K_CTOR` `as.ctor.args[0..argc-1]`; `K_REC` `as.rec.vals[0..n-1]`; `K_VARIANT`
    `as.var.payload`; `K_BOUNCE` `fn`+`arg`; `K_FAIL` `err`. `K_CLO`/`K_IO`/action/native wrappers stay out
    of the FREESET until env/action ownership is represented.
    (`K_STR` bytes are an atomic buffer — no child drops.)
  - shell + slabs: `GC_FREE` the args/vals/env slab and the `KValue` (`gc.c` — add a thin `kgc_free`
    wrapper; a per-size free-list is the S5 FBIP reuse target, out of scope here). Never `GC_FREE` a
    retained-tag or `K_FGN` cell.
  - **iterative** (§2.3): push children onto the worklist rather than recursing.
- **Immediates** (`kis_imm`) already short-circuit both ops. **`K_FGN`** is never reached (excluded by
  `kis_rc_freeable`) — re-pin the §1 carve-out at the free site with a comment + a `usingsusp` regression.

## 4. The differential flip — how to turn it on without shipping a UAF (Phase D)

The flip is staged so free-on-zero is exercised under a watchdog before it is trusted:
- **D1 — mechanism, still OFF.** Land `kfree_recursive` + `kis_rc_freeable` but keep the public entry disabled
  and do not call the free branch. Observable behavior remains RC-on == RC-off; nothing frees.
- **D2 — ON under the oracle.** Enable free-on-zero **in the C backend** (per §2.6.1 — LLVM stays fully
  Boehm-backed until it grows its own `kdup`/`kdrop` emission) in a build compiled with **AddressSanitizer**
  (`Driver.hs` gains an S3/ASan rtCFlags lane) — ASan is the UAF/double-free detector that replaces the
  underflow assert as the *primary* gate. Run the full corpus: RC-on must be **ASan-clean** and
  **RC-on == RC-off output-identical**. Optionally keep a "poison-on-free + shadow-set" double-free check for
  non-ASan builds.
- **D3 — garbage-free validation.** With free-on-zero ON, confirm the RC-freed shapes' live set does **not**
  monotonically grow (`KAPPA_GC_STATS` heap-high-water on an allocation-heavy loop) — this is the payoff and
  the proof that drops actually reclaim.
- **D4 — default on.** Free-on-zero is the default; Boehm stays linked for the retained tags (§1) + cycles;
  the oracle build stays in CI (RC-DESIGN §7: *"keep a Boehm-as-backstop build in CI through the S2–S3
  window"*).

## 5. Verification

1. **ASan/UBSan corpus, RC-on (primary).** Every `test/native/cases/*` + the conformance drop-site programs
   run clean under ASan — the S3 replacement for the S2 underflow-assert gate.
2. **RC-on == RC-off output-identical** (the S2 invariant persists — reclamation must not change observable
   behavior) + **conformance 2094/0** + **llvm-parity 150/0**.
3. **Garbage-free trend** (`KAPPA_GC_STATS`): RC-freed-shape heap-high-water bounded on a tight
   alloc/drop loop; not monotonic growth.
4. **Concurrency stress under ASan** (`fork`/`promise`/`stm`/`race`/`fiber-*` cases): exercises the
   `tshare` mark + skip; a shared object must never be RC-freed.
5. **Resource carve-out (§1)** (`usingsusp.kp`/`usinginterrupt.kp`/`defer-*`): no `K_FGN`/resource cell is
   freed by RC; the ExitStack still owns handle release.
6. **Deep-structure stress** (§2.3): a million-node spine frees without stack overflow.

## 6. Risks

- **R-UAF (the whole category, now live).** Mitigated by the conservative FREESET (§1), the proven S2.3
  placement, `karr_new`/`tshare` prerequisites, and ASan-as-gate (§4). This is *the* risk S3 exists to
  manage.
- **R-derived-container-undercount** → `karr_new` per-slot dup + `krec_without` kept-field dup, §2.1
  (mitigated before S3.2).
- **R-shared-race** → atomic header ops + `tshare` mark + no-op shared dup/drop, §2.2 (blocking);
  counted shared-object reclamation is S4.
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
| **S3.1** | Phase A prereqs: `karr_new` per-slot dup (§2.1), atomic header + `tshare` mark + no-op shared dup/drop (§2.2), disabled iterative `kfree_recursive` skeleton (§2.3), arity-guard reconcile (§2.5) | landed; RC-on == RC-off, underflow-clean, nothing frees yet |
| **S3.2** | after the S2.3 ownership entry gates below are green, wire the free branch in `kdrop`; free-on-zero ON under the ASan oracle (§4 D2) | ASan-clean, RC-on == RC-off, no double-free, garbage-free trend (§5.1–5.4) |
| **S3.3** | precision: write-barrier drop-old + CAS/promise drops (§2.4) | ASan-clean; leak-trend improves; still byte-identical output |
| **S3.4** | default-on; Boehm retained for un-RC'd tags; oracle build stays in CI (§4 D4) | full-corpus ASan-clean; heap-high-water bounded; resource carve-out (§5.5) |

Ordering rationale: the tag partition + `tshare` infra must precede any free; the
Phase A prerequisites must ALL be in before the free branch is wired (S3.2), because each closes a distinct
UAF path (array under-count, shared race, stack overflow). S3.2 also inherits the still-open S2.3 ownership
entry gates recorded in ROADMAP/S2.3d: returning-arm (`SinkTail`/`SinkBounce`) match cell-drop tightening,
projection-result ownership before broader scope-close drops, and a current audit of S2.3c storing primitives.
Those are not runtime S3.1 prerequisites, but they are free-on-zero prerequisites: enabling recursive
reclamation before the ownership layer can prove those aliases would turn formerly leak-biased omissions into
UAF risks. Precision write-barriers (S3.3) are safe to defer because their absence is a leak, not a UAF;
default-on (S3.4) waits until the full corpus is ASan-clean.

## Critical files

**Landed S3.1 prerequisites:**
- `runtime/kappart.h` — `kis_rc_freeable`, the shared-bit accessors, `kfree_recursive` prototype, and
  `kdup`/`kdrop` immediate + shared no-op guards. The `kdrop` free branch is still pending.
- `runtime/value.c` — disabled `kfree_recursive` per-tag child traversal + shell release, `karr_new` per-slot
  dup (§2.1), record-rest kept-field dups, and shared ref/array/thunk incoming-value marks.
- `runtime/gc.c` — `kgc_free` (`GC_FREE`) wrapper, currently used only by the disabled free skeleton.
- `runtime/rt.c` / `runtime/stm.c` / `runtime/scope.c` / `runtime/atomic.c` / `runtime/reactor.c` —
  recursive shared marking before runtime publication points (§2.2).
- `src/Kappa/Backend/C.hs` / `src/Kappa/Backend/LLVM.hs` — mark generated global/CAF cache values shared
  before process-wide publication.
- `src/Kappa/Backend/Repr.hs` / `src/Kappa/CoreOps.hs` — runtime-argument mask alignment for kind-domain
  parameters (§2.5) and scalar-worker static-prefix rewrites.
- `runtime/tests/perceus_s3_prereq.c`, `test/Spec.hs`, `test/native/run-native-tests.sh` — S3.1 prerequisite
  and generated-code gates.

**S3.2+ work:**
- `src/Kappa/Backend/C.hs` / `src/Kappa/Usage.hs` / `src/Kappa/Ownership.hs` — close the S2.3 ownership entry
  gates before enabling free-on-zero: returning-arm match cell drops, projection-result ownership for broader
  scope-close drops, and the storing-primitive audit.
- `runtime/kappart.h` / `runtime/value.c` — wire the guarded `kdrop` free branch and make the free worklist
  non-allocating or GC-root-safe before enabling it.
- `runtime/gc.c` / `src/Kappa/Backend/Driver.hs` — ASan/double-free oracle build lanes.
- `test/native/run-native-tests.sh` — ASan corpus run, garbage-free heap-high-water check, deep-structure
  stress, concurrency-under-ASan, and resource carve-out regressions.
