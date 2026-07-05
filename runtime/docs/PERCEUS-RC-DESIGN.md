# Perceus Reference Counting + Boehm→Precise-GC Migration — Design

Status: **Staged implementation in progress; S0→S4 landed for the C/runtime path.** Owner: compiler architecture · Audience: backend + runtime

This is the design for moving the native runtime from conservative Boehm-backed allocation toward **Perceus
precise reference counting** (Reinking/Xie/de Moura/Leijen 2021; drop-guided reuse, Lorenzen/Leijen
2022). Boehm remains the allocation/rooting backstop for retained shapes and future stages, while S3/S4
already reclaim the strict immutable FREESET on the C/runtime path. It is the back half of the
"Perceus + value-unboxing" lever: immediate tagging (UNBOXING Stages
0/1/1b/1d/1e) and the scalar workers (Stage 2b) already landed and captured the cheap Int/ctor allocation
wins; this arc targets the *dominant residual* allocation those cannot touch — **n-ary record/ctor
per-field box indirection** and the **~832 B/fork CPS frame** — via RC drop + FBIP reuse on the CPS seam.

It is grounded in a spec-first study (Spec.md memory model), the locked decisions in
[UNBOXING-DESIGN](UNBOXING-DESIGN.md) / [CPS-DESIGN](CPS-DESIGN.md) / [TAGGING-RESEARCH](TAGGING-RESEARCH.md),
the current runtime (`runtime/*.c`), and the primary Perceus literature.

---

## 0. Thesis and the one validated bet

**Kappa's quantity/borrow system already *is* the Perceus ownership substrate.** This is the head-start
that makes RC materially more tractable here than a from-scratch Koka-style implementation (where ownership
is *inferred*). Confirmed against the spec:

- Quantity is **ownership accounting**, not info-flow (§12.2.7, Spec.md:11428). The lattice (§12.2,
  Spec.md:10539) gives exactly owned/borrowed/shared: `1` = linear, owned, **consumed exactly once**;
  `&` = the borrow marker, **non-consuming** (§12.3, Spec.md:11577) — this is *literally* Perceus's
  owned-vs-borrowed parameter convention; `ω` = unrestricted/shareable; `0` = erased (no runtime rep).
- **Path-sensitive last-use is already computed** at elaboration (§12.2.6 linear discharge Spec.md:11336;
  §13.2.4 partially-consumed records Spec.md:12606) — precise decrement points, including per-field.
- **Droppability is decided**: `1`/`≥1` are not droppable (must be explicitly consumed); `0`/`≤1`/`ω`
  are droppable (Spec.md:11403). The type system already tells RC which values may be silently
  decref-freed vs which carry a consumption obligation.

**The catch (the one real gap):** this information "does not require a distinct runtime representation"
(§13.2.4) and is **erased before KBackendIR** (§31.2, Spec.md:34629). So the RC pass consumes the
*elaborated ownership decisions threaded as backend metadata*, **not** a runtime linearity oracle. Closing
that threading — carrying owned/borrowed/last-use onto the IR the backend lowers — is the foundational
compiler work item (CCtor/CMatch carry no type today; cf. the `stage2-layout-staging` note).

The spec **permits RC explicitly** and binds only observable behavior: §34.4.1 (Spec.md:38233) "memory-
management strategy is implementation-defined… A backend MAY use tracing GC, reference counting, arenas…";
§32.2.16 (Spec.md:35283) forbids rejecting a program *because* you chose RC. No source semantics may depend
on the collector.

---

## 1. The correctness contract — what RC must preserve (non-negotiable)

These are spec obligations, not optimizations. Violating any is a soundness bug.

1. **Resource release is `defer`/`using`/`MonadFinally`, NEVER an RC-decref-to-zero** (§34.4.1,
   Spec.md:38233-38245). RC-free is *memory reclamation only* — it must be side-effect-free and
   observationally invisible. The **ExitStack drain** (`begin_finseq` rt.c:846 / `krun_finish` prims.c:854)
   is the authoritative last-use point for resources. **RC must treat any object reachable from a live
   ExitStack as held** and must not drop a `K_FGN`/resource-carrying object before its `defer` runs —
   else double-close (RC + defer) or close-too-early.
2. **`defer` ordering**: LIFO, masked/uninterruptible, exactly-once, on every exit path (§18.7,
   Spec.md:21298; runtime: `begin_finseq` pushes `KK_POPMASK` beneath `KK_FINSEQ`, rt.c:865). RC decrefs
   may not reorder or precede these.
3. **Structured-concurrency happens-before**: child fibers (incl. their finalizers) terminate **before**
   the parent scope releases resources it owns (§32.2.3, Spec.md:34921). RC must honor this, not reorder
   frees by reachability.
4. **Linear single-consumption survives to runtime** (§11.1.15, Spec.md:1855 — non-deferrable). RC must
   never `dup` (incref-share) a value the frontend consumed linearly if that would let a destructor run
   twice, nor drop one whose destructor must run.
5. **Silent handle reclamation** (§32.2.8, Spec.md:35077): dropping the last handle to a Fiber/Scope/
   Promise/Monitor/TVar/FiberRef must **not** interrupt/shutdown/cancel/wake it. RC reclamation must be
   observationally equivalent to continued existence.
6. **Continuation unwinding** (§32.2.20, Spec.md:35358): abandoning an unresumed continuation still drains
   its captured do-scope exit actions exactly once (masked LIFO) — RC freeing an unreachable continuation
   runs those pending defers **first**. Multi-shot capture of linear/borrowed state is rejected at compile
   time (§18.1.20) ⇒ RC may assume any value captured by a multi-shot continuation is `ω`/duplicable.

The takeaway: **the ExitStack/finalizer machinery owns resource lifetime; RC owns only memory.** They are
sequenced so the finalizer holds the last reference and runs before the drop.

---

## 2. Heap-object layout — the home for the RC word

- `KValue` is `{ KTag tag; uint32_t rc; union as; }` (kappart.h), `sizeof = 48`, using the old **free
  4-byte hole at offset 4** (tag is 4 bytes at 0; the union is 8-aligned starting at 8). The header word
  stores `KRC_SHARED_BIT` in the high bit, `KRC_SATURATED_BIT` below it, and a low-30-bit owner count —
  **zero struct growth**. (Shrink `KTag` to `uint8` to free 3 more header bytes if wanted.)
- **The RC count + borrow/thread-shared discriminator live in the HEADER, not the pointer tag.** This
  resolves the former doc conflict: UNBOXING-DESIGN now follows TAGGING-RESEARCH:29-41 — the low 3 tag bits
  are *immediate kinds only*;
  an RC discriminator in the pointer would **alias** (the same object reached via a borrowed vs an owned
  reference would carry different tags). S4 deliberately kept an explicit shared-bit branch instead of the
  Koka-style signed-compare fold; the extra saturation bit makes overflow sticky and fail-closed.
- **Immediates skip RC entirely** (b001 Int, b010 nullary ctor, b011 packed 1/2-field ctor) — they are
  value-copied, never counted (TAGGING-RESEARCH:38-40). Every `dup`/`drop` is guarded by `kis_imm` (an
  extra hot-path branch — measure its tax, §8).
- **Heap-header shapes**: every non-immediate `KValue` has the `rc` word. S4 free-on-zero is deliberately
  narrower than "has a header": only the strict immutable FREESET (`K_CTOR`, `K_REC`, `K_VARIANT`, `K_STR`,
  `K_BOUNCE`, `K_FAIL`) may be reclaimed by `kdrop`. Mutable, lazy, foreign/resource, closure/env,
  bigint/bytes, and action-wrapper shapes remain Boehm-retained until their later ownership protocols land.

---

## 3. The RC algorithm — the modern pipeline

Adopt the **drop-guided** pipeline (post-2021), not the original PLDI'21 one:

```
explicit-control-flow core
  → Perceus dup/drop insertion   (per-branch fv liveness; push-dup-LATE, emit-drop-EARLY; precise
                                   drop = last-use, NOT lexical scope — a big list is freed incrementally
                                   as it is consumed)
  → drop specialization + dup/drop fusion   (inline drop at a known ctor; cancel dup/drop pairs; on the
                                             statically-unique fast path RC ops vanish)
  → drop-guided reuse (FBIP)      (Lorenzen/Leijen 2022 — runs AFTER dup/drop; frame-limited, avoiding
                                   Koka's fragile algorithm-K and Lean's heap-bloating algorithm-D)
  → borrowing                     (LAST, opt-in only — §6)
```

- **Consume the quantity/borrow decisions** as the owned/borrowed parameter convention: an owned (`1`)
  param ⇒ callee consumes (drops or reuses) it; a borrowed (`&`) param ⇒ callee reads + dups but **never
  drops** (caller still owns). Already decided by elaboration — thread it; do not re-derive.
- **FBIP reuse is the lever** for the n-ary record/ctor per-field allocation that tagging cannot touch.
  `drop-reuse(x)` yields a reuse token (`&x` if `rc==1`, else `NULL` after a normal decref); the matching
  same-size constructor writes fields **in place** when the token is live. A unique k-field node rebuild
  becomes **0 alloc + k field stores** instead of malloc + k stores + free. Constraints: object unique at
  runtime; token size matches the alloc; drop and alloc in the same frame/branch. Proof target: Koka's
  red-black-tree insert is ~19% faster than hand-tuned C++ `std::map` with this.
- Perceus is **garbage-free** (Thm 4) on the strict core — at every step every heap object is reachable
  from the erased program, i.e. no float-ing garbage between a last-use and its drop.

### 3a. Tighter-than-declared usage refinement (whole-program; sound while there is no separate compilation)

A declared quantity is the **upper bound** the programmer committed to in the signature; the program's
*actual* usage may be tighter. `foo : ω Foo -> Bar` whose body — and, across the visible call graph, whose
callers — use the `Foo` exactly once supports refining the effective range to `[1,1]`. That lets the RC
(a) treat the parameter as **owned**, so it can **drop/reuse** the `Foo`'s storage instead of conservatively
treating it as shared, and (b) **elide the `dup`** a conservative `ω` would force at a use that looks shared.
The refinement only ever **tightens** a declared range, never widens it, so it can never violate the source
contract — it just unlocks reuse where the program proves it safe.

This refinement is **whole-program sound** whenever the analysis sees **all** uses of a binder — which it
always does in Kappa's current **whole-program-static** compile (there is no dynamic linking and no separate
compilation yet). So **every** provably-single-use binder is refined: exported, re-exported (§8.4), and
internal binders are all eligible. Mechanism: compute the refined per-binding usage interval during the same
whole-program pass that threads ownership to KBackendIR (S1, §7); store it as IR metadata; the refinement
only tightens, so it folds into the S1 ownership threading — the same data, just tighter.

The genuine gating boundary for §3a is the **dynamic-link / separately-compiled interface** — the one place
the analysis *cannot* see all uses (a separately-compiled caller may use the value differently → an S2
use-after-free if S2 dropped/reused it). That interface is **empty right now**.

> **TODO — DYNAMIC LINKING / SEPARATE COMPILATION (a hard prerequisite before S2 ships under it).** When a
> separately-compiled boundary exists, §3a **must** fall back to the **declared** quantity (`boRefined =
> Nothing`) for any binder reachable through that interface. The earlier module-export/re-export gating was a
> premature proxy for this boundary and has been removed; re-add the gate then, keyed on the **real**
> separate-compilation interface (not on module exports/re-exports).

---

## 4. Cycles — totality is the asset

Pure RC cannot reclaim cycles. Kappa's totality makes this a small, isolated problem:

- **Strict, total (co)inductive constructor data is acyclic by construction** (building a node requires its
  children to already exist) → the garbage-free guarantee holds with **no cycle collector**. **Ship RC for
  strict data first and get most of the win.**
- Exactly **two cycle sources**, both confinable to small tracked sets:
  1. **Mutable refs** (`Ref`/`:=`, the main mutation per §31.5): programmer breaks the cycle (Swift's
     model), or a small incremental cycle collector over *only* ref-typed nodes.
  2. **Future opt-in `lazy data`** (tying the knot — e.g. `let xs = 1 :: lazy xs`): a memoized delayed head
     whose closure points back at the cell forms a cycle the moment it is forced/updated. Because this design
     remains opt-in future-stage work, the intended cost is localized to lazy nodes only — they carry the
     mutable-cell RC protocol + cycle-set membership; the strict 99% stays on the cheap garbage-free path.
     The RC-relevant invariants are that the delayed-head *closure* is the capture point, enter is a
     destructive in-place update RC treats as a unique/owned mutation, and quantity/borrow/region obligations
     hold at the delayed-head boundary.

---

## 5. Thread-shared / atomic RC

Non-atomic by default; flip to atomic only where a value genuinely crosses fibers. The runtime study found
the publish points are **few and localized**, but S4 treats the list as soundness-critical and exhaustive:

- **tshare triggers** (one-time recursive mark-shared): generated global/CAF cache release-stores,
  `fork`/`forkDaemon` (the action closure + captured env), Promise completion, fiber exit delivered to
  awaiters, wake/resume, stored interrupt causes, FiberRef init/snapshot, blocking-lane payloads, TVar
  creation/commit, AtomicRef creation/store/exchange/CAS-success/fetch-update, and writes into already-shared
  Ref/Array/thunk storage. Current `AtomicRef` stores boxed `KValue*` occupants behind a mutex; load and
  CAS-failure duplicate witnessed values while protected. The earlier scalar-only prototype is historical.
- **Encoding**: the header word has an explicit shared flag, a sticky saturation flag, and a low-30-bit
  owner count. Thread-local `dup`/`drop` use the biased direct path after an atomic discriminator load;
  shared `dup` = relaxed atomic increment on the common path; shared `drop` = release decrement with an
  **acquire before free** (so child counts are synchronized before the recursive drop). The Koka
  negative-RC trick remains design background, not the landed S4 encoding.
- This matches the borrow/thread-shared split already named as a design axis (UNBOXING A4, CPS §182): a
  fiber's own unpublished values are thread-local ⇒ non-atomic; any value crossing one of the publish points
  above pays atomic/shared storage costs after the recursive mark.
- **Cost warning** (lit): uniform atomic RC is 20-130% slower even single-threaded — the biased split is
  load-bearing, not optional.

---

## 6. Coroutines / the CPS seam, and the slot-kind map

- The `kdo_N_kM(KEnv*, KValue*)` continuation function + the `Cont` deliver/unwind protocol is the
  **designated stable seam** (CPS §176): Perceus (and LLVM `coro.id.retcon.once`) slot in, they don't tear
  it out. One-shot linear `Cont`/`KEnv`/`kclo` is "a good Perceus citizen" — explicit control flow gives
  explicit dup/drop sites (a `KK_BIND` drops its continuation after `kapp`; a branch join dups the shared
  tail per arm). Continuation spines are acyclic ⇒ the cycle caveat doesn't bite the machinery.
- **dup/drop go at**: closure capture (`kclo`/`kpush` = the owned-set unit), the **park/resume seams**
  (`krt2i_wake` CAS rt.c:393 + the park returns in `do_await`/`do_await_promise`/STM-retry/`OP_SLEEP`), and
  the fork/promise/TVar publish points (§5). The **cross-suspend live set** is exactly what is reachable
  from `(f->cur, f->k, f->cur_exits, f->locals)` at park; the natural per-frame owned set is `Cont.a`'s
  closure env plus the `aux` ExitStack.
- **One-shot is the default** (the spec's default; `coro.id.retcon.once`) = move/in-place, no copy, no
  atomic. **Multi-shot** = dup the resumption object (children = captured frames) + copy on each use —
  gated behind the compile-time escape-check + the not-yet-existing `rt-multishot-effects` capability (CPS §170).
- **The slot-kind map (UNBOXING Stage 3) is the shared artifact**: the `Boxed | I64 | F64 | FixedFFI`
  layout kind threaded onto **every** continuation/do-scope frame, **joined with the already-landed
  `gsSuspenders` suspendability witness**, consumed by **both** Perceus dup/drop **and** LLVM CoroSplit.
  Build it once at the seam. It is what later enables the typed scalar-spill slot (a `Double` counter
  surviving a park unboxed) — deferred behind precise GC because under conservative Boehm a non-immediate
  unboxed value in a scanned frame slot is a false root (UNBOXING A6).

---

## 7. Migration staging — safe, incremental, Boehm-backstopped

The collector contract (interior-pointers OFF, 8-byte alignment) is already enforced in `krt_init`
(gc.c:48-58). The migration:

- **S0/S4 — Reconcile + header.** Adopt TAGGING-RESEARCH's ruling (§9); add the `rc` header word to the
  KValue header hole (offset 4), later refined by S4 into explicit shared + saturation flags plus low count;
  update UNBOXING-DESIGN's stale "reserve low bits for Perceus" lines.
- **S1 — Thread ownership to the IR.** Carry the elaborated owned(`1`)/borrowed(`&`)/last-use decisions
  onto KBackendIR (`Core.hs`); give CCtor/CMatch the type/size info reuse needs. *This is the real
  foundational cost.*
- **S2 — Insert dup/drop, Boehm still frees (DIFFERENTIAL BACKSTOP).** Perceus dup/drop on the strict core;
  a debug mode where `drop` decrements and asserts `rc >= 0` but **Boehm still does the freeing** —
  validates the counts against a ground-truth collector before any RC-free can cause a use-after-free.
- **S3 — Flip free-on-zero** for strict (acyclic ⇒ garbage-free) data. Immediates skip RC (`kis_imm`).
- **S4 — Thread-shared split** + atomic fast/slow path at the §5 publish points.
- **S5 — Drop-guided reuse (FBIP)** — the n-ary-ctor allocation win; the rbtree-class result lands here.
- **S6 — Borrowing (opt-in only)** + **inferred** FIP-style in-place analysis (FP², Lorenzen/Leijen/Swierstra
  2023): the reuse-credit / `◇ₖ` accounting that yields the zero-alloc in-place guarantee is **derived from the
  code itself** — from the quantity/borrow facts (`1` owned / `&` borrowed) and the already-computed used-once
  usage intervals (`ucHi == 1`, `Usage.hs`) — **NOT** from `fip`/`fbip` surface keywords. No annotation; the
  compiler infers which functions are fully-in-place. A natural fit with Kappa's quantity/erasure machinery,
  and the erasure-aware runtime layout (S5.A) is on its soundness path (same-size reuse must be over
  runtime-kept fields).
- **Later — precise stacks + cycles.** Precise roots in the 8 MiB pthread fiber stacks (stack maps /
  shadow stack) or keep them as conservative root regions; the mutable-ref + lazy-node cycle collector.

**Failure modes & guards** (lit): missed drop = leak (the Boehm-backstop differential catches it); missed
dup / double drop = **use-after-free — the dangerous one** (the garbage-free proof + a debug rc-underflow
assert + the differential guard it); cycles leak silently (the tracked sets); atomic race (tshare
completeness — every fiber-crossing path must trigger it); reuse mutating a non-unique object
(the runtime is-unique check).

---

## 8. Honest scope

This is the marquee perf arc **and a large one**. The cheap unboxing wins are already captured; this arc
exists for the *dominant* residual: n-ary record/ctor per-field box indirection (→ FBIP reuse, S5) and the
832 B/fork frame + 416 B/bind tree (→ RC move/reuse on the CPS seam). It is gated on a foundational GC
migration; the Boehm-backstop differential (S2) is what makes that migration de-riskable rather than a
flag-day. "As fast as Go/Rust" is **false until S5** and only on the linear/non-suspending path — reuse
trends to zero only for linear non-escaping binds; multishot, branch-join-shared continuations, and
fork-captured values break linearity and don't reuse.

---

## 9. Open questions / resolved reconcile notes

- **Resolved tag/RC placement:** UNBOXING-DESIGN now follows TAGGING-RESEARCH:29-41 — RC/discriminator live
  in the **header**, low bits are immediate kinds only. Keep future tag work from reintroducing a pointer-tag
  RC discriminator, because that would alias owned/borrowed views of the same heap object.
- **Borrow-through-IO gap** ([D6](../../docs/notes/BORROW_THROUGH_IO_MONAD.md)): `ioBind` is monomorphic in
  its capture set, so a borrowed region cannot thread through a recursive IO do-block. The borrow *side* of
  the borrow/thread-shared split therefore has a hole at the IO-monad boundary. Likely **not** a v1 blocker
  (borrowing is S6, opt-in), but Perceus borrow inference must eventually agree with the region system.
- **Precise stack rooting** for deep non-tail recursion: stack maps / shadow stack, or keep fiber pthread
  stacks as conservative regions.
- **K_THUNK memoization** (cache write): model as a write-barriered ref-set; concurrent
  force of a shared lazy head needs the atomic-force CAS path.
- **Tag reclamation (post-RC)**: once precise RC no longer needs odd words GC-invisible, can the 2 stolen
  low bits be reclaimed (61→63-bit Int)? (TAGGING-RESEARCH:94-96.) Revisitable, not now.
- Keep a **Boehm-as-backstop** build in CI through the S2-S3 window.

---

## 10. Key files

**Runtime** — `runtime/gc.c` (Boehm boot + alignment contract :40-69), `runtime/kappart.h` (KValue header
hole at offset 4 :114; immediate accessors :205+), `runtime/value.c` (constructors / counted shapes
:16-319), `runtime/rt.c` (Cont/park/resume/fork/promise seams :393/578/659/701/846/1483), `runtime/stm.c`
(TVar publish), `runtime/internal.h` (Fiber/Cont/ExitStack/rt->all root set :181-406), `runtime/scope.c`
(do-scope exits), `runtime/reactor.c` (the one manual `free`).

**Compiler** — `src/Kappa/Core.hs` (thread ownership + layout/slot-kind onto IR), `src/Kappa/Backend/C.hs`
(`gsSuspenders` witness, the `kdo_N_kM`/Cont seam, dup/drop emission), `src/Kappa/Usage.hs` (the
quantity/borrow source of the owned/borrowed decisions).

**Design** — [UNBOXING-DESIGN.md](UNBOXING-DESIGN.md) (slot-kind map, immediates-skip-RC, A1-A10),
[CPS-DESIGN.md](CPS-DESIGN.md) (the seam, one-shot/multishot, Stage 5 Perceus), [TAGGING-RESEARCH.md](TAGGING-RESEARCH.md)
(header-vs-tag ruling), plus the future lazy-data/RC boundary described above.
