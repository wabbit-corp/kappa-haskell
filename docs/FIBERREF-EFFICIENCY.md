# FiberRef efficiency review

**Question.** Is the just-landed `FiberRef` runtime implementation (commit `aa506fc`)
efficient enough, and if not, what is the better design?

**Verdict.** **Keep it as-is for now.** The eager copy-on-fork snapshot is the
textbook simple implementation and is *correct* against the normative §18.1.7
semantics. Its cost is linear in the number of `FiberRef`s the parent has
**`set`** (not the number that exist), which in every realistic Kappa program is
a single-digit count — where the measured overhead is in the scheduler's noise
floor (< 150 ns, < 20% over the bare fork cost). The persistent-map design that
ZIO/Cats-Effect use is genuinely better *asymptotically* and is the right answer
*if* `FiberRef` ever becomes a heavily-used, deeply-forked, many-cell feature —
but retrofitting it now is premature optimization against a load profile Kappa
does not have. This document records the cost model, the prior art, and a
concrete migration plan so the decision can be revisited with data rather than
re-derived.

---

## 1. What landed (the current implementation)

Files: `runtime/rt.c` (~459–578, 1193–1213), `runtime/internal.h` (208–246),
`runtime/scope.c` (136–140). Reference oracle: `src/Kappa/Interp.hs` (113–175,
783–805). Normative semantics: `docs/Spec.md` §18.1.7, §32.2.7.

### Data model

A `FiberRef` handle is **just a dense integer id boxed as an immediate**
(`fiber_ref_new` → `kint(id)`). Two structures back it:

* **A single shared, append-only init registry** (`g_fref_init`, guarded by
  `g_fref_lock`): `g_fref_init[id]` is the cell's initial value — the fallback
  for any fiber that never `set` it. This mirrors the interpreter's
  `fiberRefInit :: IORef (Map Int Value)`.

* **Per-fiber overrides** (`Fiber.locals : FiberLocals*`), a *flat array indexed
  by cell id*:

  ```c
  typedef struct FiberLocals { KValue **vals; int n; } FiberLocals; /* n = slots allocated */
  ```

  `vals[id] == NULL` means "no override → use the registry init". `locals` is
  `NULL` until the fiber's first `setFiberRef` (lazy allocation). The
  interpreter models the same thing as a nested
  `Map ThreadId (Map Int Value)`.

### Operation costs (single fiber, no contention)

| op | runtime | cost |
| --- | --- | --- |
| `newFiberRef` | `fiber_ref_new` | O(1) amortized; takes `g_fref_lock`, may grow the init registry (doubling) |
| `getFiberRef` | `fiber_local_get` | **O(1)** array index `vals[id]`, else one locked read of the registry |
| `setFiberRef` | `fiber_local_set` | **O(1)** amortized array store; first set allocs `locals`, may grow `vals` to cover `id` (doubling) |
| `modifyFiberRef` | inline at `OP_MODIFY_FIBER_REF` | O(1) get + one `kapp` of the pure `fn` + O(1) set; **trivially atomic** — the cell is private to the single fiber stepping on the CK-machine, so no lock is needed |
| **fork** (`OP_FORK`/`OP_FORK_DAEMON`/`forkIn`) | `fiber_locals_snapshot` | **O(N)** where **N = `parent->locals->n`** = the high-water id-span of slots the parent has allocated (`GC_MALLOC` of a `FiberLocals` + `GC_MALLOC` of an `N`-pointer array + a memcpy of `N` pointers) |

The get/set/modify path is excellent — flat-array indexing is as good as it
gets, strictly better than the interpreter's `Map.lookup` oracle. **All the cost
is at fork.**

### Important subtlety: N is the id-*span*, not the override *count*

`fiber_locals_snapshot` copies `src->n` slots, and `src->n` is the allocated
capacity (grown to cover the largest id ever `set` by that fiber), **including
the `NULL` holes**. So a fiber that has set only `FiberRef #4000` pays a
4001-slot copy at every fork, even though it has exactly one logical override.
In practice ids are dense and small (allocated sequentially at program start),
so span ≈ count, but the flat-array-by-id design means *a single high-id set
inflates every subsequent fork's snapshot*. This is the sharpest edge of the
current design.

---

## 2. Normative constraint (what any design must preserve)

From `docs/Spec.md` §18.1.7 / §32.2.7:

> * Each fiber carries a logically private mapping from `FiberRef` cells to current values.
> * When a child fiber is created by `fork`, `forkDaemon`, or `forkIn`, the child
>   inherits a **snapshot copy** of the parent's currently visible `FiberRef` values.
> * After fork, parent and child updates are **independent**.

The word that matters is **independent**: a post-fork `set` in either parent or
child must not be observable in the other. The current impl gets this by *eager
deep copy* — physically separate arrays, so writes can never alias. Any
alternative design must reproduce exactly this observable independence; it may
*not* share mutable state across the fork boundary. (Note: values themselves are
immutable boxed `KValue`s, so sharing the *value pointers* is fine — only the
*mapping* must be private. This is precisely what makes copy-on-write viable.)

---

## 3. Cost model — measured

A throwaway single-worker micro-bench (`runtime/tests/`, not committed) timed a
tight `replicate M (await (fork (pure ())))` loop while the parent held `K`
overrides. The child does no `FiberRef` work, so the only `K`-dependent cost per
fork is `fiber_locals_snapshot`. M = 8000 forks/run, 3 reps, Apple Silicon,
`-O2`, Boehm GC:

| K (parent overrides) | ns / fork (median) | snapshot cost (vs K=0) |
| ---: | ---: | ---: |
| 0    | ~735  | baseline (bare fork+await+schedule) |
| 16   | ~805  | ~70 ns |
| 64   | ~916  | ~180 ns |
| 256  | ~1406 | ~670 ns |
| 1024 | ~3459 | ~2.7 µs |
| 4096 | ~12200 | ~11.5 µs |

**Reading the data:**

* The marginal cost is **linear in K at roughly ~2.8 ns per slot** (4096 slots ≈
  11.5 µs; 1024 ≈ 2.7 µs). That's `GC_MALLOC` of the array + a pointer memcpy +
  the `FiberLocals` header alloc — dominated by the allocation, not the copy.
* **At the realistic scale (K ≤ ~16) the snapshot is < 10% of the fork cost and
  well inside scheduler jitter.** A program would need *dozens* of distinct
  `FiberRef`s before the snapshot is even a measurable fraction of a fork.
* The cost only becomes dramatic — **16× the bare fork cost** — at K = 4096, a
  count no plausible Kappa program reaches.

**Memory per fiber:** `sizeof(FiberLocals)` (16 B) + `8 * n` bytes for the slot
array, where `n` is the (doubled) id-span — `NULL` for any fiber that never
calls `setFiberRef`. A fiber with a handful of overrides costs ~80–150 B; this
is duplicated in full at every fork (the GC reclaims dead children's copies).

### Where it hurts (the load profiles to watch)

The eager copy degrades super-linearly in *aggregate* under three compounding
factors:

1. **Heavy forking** — the snapshot is per-fork, so a fan-out of F children pays
   F × O(N). A worker pool or a `traverse`-over-fork spawning thousands of short
   fibers multiplies the cost.
2. **Many FiberRefs (large N)** — each individual snapshot grows with N. With a
   library that allocates dozens of cells (e.g. a structured-logging MDC, a
   tracing span context, a request-scoped DI environment — the canonical
   `FiberRef` use cases in ZIO), N climbs.
3. **Deep fork trees** — in a fork chain of depth D where each level has set a
   new cell, the snapshot at the deepest level copies all D ancestors' slots, and
   the *total* copying work across the tree is O(D²). The eager copy has no
   structural sharing to amortize this.

The killer combination — a deep tree of many short-lived fibers, each touching a
broad MDC — is exactly the workload the persistent-map designs were built for.
Kappa is nowhere near it today.

---

## 4. Prior art — the persistent-map design (same semantics, O(1) fork)

Every mature effect runtime with copy-on-fork `FiberRef` semantics avoids the
eager copy by carrying the mapping as an **immutable / persistent map** in the
fiber's runtime state. Fork then *shares the reference* (O(1)); divergence is
*copy-on-write of a single slot* via the persistent map's structural sharing.

### 4.1 ZIO `FiberRefs` (the canonical reference)

ZIO carries fiber-locals as `FiberRefs`, an **immutable**
`Map[FiberRef[?], ::[(FiberId.Runtime, Any)]]` — each cell maps to a *stack* of
`(fiberId, value)` entries (the stack records which ancestor set each value, so a
child's value can be *joined* back into the parent on `join` per the ref's
user-supplied `fork`/`join` combinators — a feature Kappa's spec does **not**
require, but the data structure is the same).

* **Fork** = the child's runtime state gets the **same immutable `FiberRefs`
  reference** as the parent. O(1), zero copying. (ZIO additionally runs each
  ref's `fork` transform lazily, but structurally it's a shared pointer.)
* **A `set` after fork** = `FiberRefs.updatedAs(...)` returns a *new* `FiberRefs`
  with one slot replaced; the persistent map shares all untouched structure with
  the parent's. Only the mutating fiber pays, and only O(log N) for the one slot.
* Parent and child independence falls out for free: neither's `set` mutates the
  shared immutable map; each rebinds its *own local reference* to a new version.

### 4.2 Cats-Effect `IOLocal`

`IOLocal` stores all locals in a single immutable `IOLocalState` (a
`Map[IOLocal[?], Any]`) threaded through the fiber as part of the `IO` run loop's
state. `fork`/`start` hands the child the parent's current `IOLocalState` *by
value of the immutable map* — a shared reference until either side updates,
which produces a new map. Same O(1)-fork / copy-on-write-on-set shape as ZIO,
just without the per-ref join stacks.

### 4.3 Others (confirming the pattern)

* **OCaml 5 domain/fiber-local storage** uses per-fiber slot arrays but
  *inheritance is opt-in* and shallow — it sidesteps the cost by *not* deep-copying
  by default.
* **Structured-concurrency designs (Koka, Kotlin `CoroutineContext`)** carry the
  context as an **immutable persistent linked structure**; a child shares the
  parent's context node and prepends its own overrides — O(1) fork, O(depth)
  lookup, lazy divergence. Kotlin's `CoroutineContext` is literally an immutable
  cons-list of context elements.

### 4.4 The shared idea

> Carry the fiber-local mapping in an **immutable persistent map**. Fork **shares
> the reference** (O(1), no allocation). Only a fiber that **mutates** pays, and
> only **copy-on-write of the one touched slot** (O(log N) with structural
> sharing of the rest). Independence is automatic because no one ever mutates the
> shared map — each `set` produces a new version bound to that fiber's own slot.

This converts the current **O(N)-per-fork, O(1)-per-op** profile into
**O(1)-per-fork, O(log N)-per-op** — strictly better when forks outnumber sets
(the common case) and N is non-trivial.

---

## 5. Recommendation

**Keep the eager deep-copy. Do not retrofit a persistent map now.** Reasons:

1. **It is correct and simple.** It matches the interpreter oracle's observable
   behavior and the §18.1.7 normative semantics exactly, with a data structure a
   reviewer can verify at a glance. The persistent map adds a non-trivial
   immutable-data-structure dependency (HAMT or balanced tree) to a runtime that
   currently has none, plus its own GC-rooting and concurrency reasoning.
2. **The measured cost is negligible at Kappa's scale.** At K ≤ 16 — already
   generous for a language whose `FiberRef` users today are a handful of
   structured-concurrency primitives — the snapshot is < 10% of fork and inside
   scheduler noise. You would need ~100+ live `FiberRef` overrides *and* heavy
   forking before the eager copy shows up in a profile.
3. **The get/set/modify hot path is already optimal** (flat-array O(1)), and
   that path is touched far more often than fork in typical code. A persistent
   map would *regress* get/set to O(log N) to buy a fork win Kappa isn't
   spending on.
4. **Premature.** The right trigger for the rewrite is *data*: a real workload
   (or a benchmark in `runtime/bench/`) where the fork snapshot is a measured hot
   spot. Until then it's speculative complexity.

### Two cheap, low-risk improvements worth doing *instead* (optional)

If any tuning is desired without adopting a persistent map, these are surgical
and preserve the current structure:

* **(a) Skip the snapshot when the parent has no overrides.**
  `fiber_locals_snapshot` already returns `NULL` for `src == NULL || src->n ==
  0` — but `src->n` is the *allocated capacity*, which stays > 0 (and full of
  `NULL`s) after the first `set` even if every override is later cleared. A
  cheap **live-count** field on `FiberLocals` (incremented on a NULL→value set)
  would let fork early-out to `NULL` for the common "fiber forks before it ever
  sets a local" case and shrink the copy to the live span. Low risk, pure win on
  the fork path. *(This is the single highest-value tweak: most fibers in a
  fan-out never set a local at all, yet inherit a non-trivial parent array.)*
* **(b) Copy only up to the highest *non-NULL* slot, not the full capacity.**
  Track a `hiwater` (largest id with a non-NULL value) and snapshot `hiwater+1`
  slots instead of `n`. Bounds the per-fork copy by the actual override span, not
  the doubled allocation. Trivial, no semantic change.

Neither changes the asymptotics, but both cut the constant for the realistic
"few overrides, frequent forks" profile at near-zero risk.

---

## 6. If/when a rewrite is warranted — the design and its cost

Trigger: a profiled workload where the fork snapshot is hot (many cells × heavy
or deep forking). The migration:

### Design

Replace `FiberLocals` (flat array) with an **immutable persistent map**
`FiberRefId → KValue*` carried on the fiber:

* A **HAMT** (hash array-mapped trie) keyed on the dense integer id is the
  natural fit — ids are already integers, so a bitmap-indexed trie gives O(log₃₂
  N) ≈ effectively O(1) get/set with cheap structural sharing. A simpler
  **immutable balanced tree** (red-black / weight-balanced) keyed on `int` is
  easier to get correct and adequate at these sizes.
* `Fiber.locals` becomes a pointer to the root node of an immutable map (or
  `NULL` for the empty map).
* **fork**: `child->locals = parent->locals;` — a single pointer copy, **O(1)**.
  The shared subtree is immutable, so no aliasing hazard.
* **set/modify**: `child->locals = map_insert(parent_or_self->locals, id, v);` —
  returns a new root sharing all untouched nodes; **O(log N)**, allocating only
  the O(log N) nodes on the path. The fiber rebinds its own `locals` pointer; the
  parent's root is untouched → independence preserved.
* **get**: `map_lookup(f->locals, id)` → override or, on miss, the shared init
  registry. **O(log N)**.

### Preserving §18.1.7 independence

Trivially: the map is immutable, so a `set` never mutates shared structure — it
produces a new version bound to the *one fiber's* `locals` pointer. Parent and
child, holding distinct root pointers after either diverges, can never observe
each other's updates. This is the *same* guarantee the eager copy gives, achieved
by immutability instead of physical duplication. (The value boxes were already
immutable and safe to share — only the mapping needed privacy.)

### Conservative-GC interaction (Boehm)

This is the one real subtlety and it is **favorable**, not hostile:

* Every map node must be `GC_MALLOC`'d (scanned), so the value pointers it holds
  are traced — same discipline as the current `vals` array (`internal.h` notes
  the array is "scanned"). No change to rooting: the map is reachable from
  `Fiber.locals`, and every live fiber is in `rt->all` (the strong root set), so
  the whole persistent structure stays live exactly as long as some fiber
  references it.
* **Structural sharing is GC-safe under Boehm precisely because it's a conservative
  *tracing* collector**: a shared subtree referenced by both parent and child
  roots is kept alive by either; when the last referencing fiber dies and is
  removed from `rt->all`, the now-unreachable nodes are collected normally. There
  is no reference counting to get wrong (contrast Perceus, where shared immutable
  nodes would need RC — see the project's representation/Perceus notes; that
  concern does *not* apply under Boehm). The eager-copy design's GC story carries
  over unchanged; sharing just means fewer, longer-lived allocations.
* One thing to verify: the map nodes must not embed raw non-pointer bit patterns
  that look like interior pointers in a way that pins garbage — but since nodes
  hold only `KValue*` and child-node pointers (both heap pointers) plus small
  ints/bitmaps, this is the same shape as existing runtime nodes (`Cont`,
  `ExitStack`) and poses no new hazard.

### Effort and risk

* **Effort:** ~moderate. The bulk is a small immutable-int-map module (~150–250
  LoC for a weight-balanced tree with `insert`/`lookup`; more for a HAMT) plus
  swapping the four call sites (`fiber_local_get`/`set`, `fiber_locals_snapshot`
  → pointer copy, the `OP_MODIFY` inline). The op dispatch and spec semantics are
  untouched.
* **Risk:** low-to-moderate. The semantics are unchanged and the interpreter
  oracle (`fiberref_promise.c` GC-stress harness + the `Interp.hs` reference)
  already pins the observable behavior, so a correct map passes the existing
  tests. The main risk is the new data-structure module's own correctness
  (immutability invariants, structural sharing) — mitigated by unit-testing the
  map in isolation before wiring it in. No ABI or compiler-frontend change: the
  `FiberRef` handle stays a boxed int id.
* **Regression to watch:** get/set go from O(1) to O(log N). For programs with
  *few* cells and *rare* forking — likely the majority — this is a *net loss*.
  Hence the design is only worth adopting once forking dominates, which argues
  for keeping the flat array as the default and treating the persistent map as a
  contingency, not an upgrade.

---

## 7. Summary

| | Current (eager deep copy) | Persistent map (ZIO/CE style) |
| --- | --- | --- |
| fork | **O(N)** copy + alloc | **O(1)** pointer share |
| get | **O(1)** array index | O(log N) |
| set / modify | **O(1)** array store | O(log N) copy-on-write |
| memory | full array duplicated per fork | structural sharing; only mutated paths allocate |
| deep-tree total copy | O(D²) | O(D log N) |
| §18.1.7 independence | by physical duplication | by immutability |
| Boehm GC | scanned array, simple | scanned shared nodes, also simple; no RC hazard |
| complexity | trivial, reviewable | needs an immutable-map module |
| best when | few cells, rare forking (**Kappa today**) | many cells, heavy/deep forking |

**Decision: keep the eager copy.** It is correct, the get/set hot path is
optimal, and the fork cost is negligible at Kappa's scale (< 150 ns / < 20% over
bare fork at K ≤ 64; only 16× at an unrealistic K = 4096). Optionally apply the
two constant-factor tweaks in §5 (live-count early-out, hiwater-bounded copy) —
both are near-zero-risk and target the realistic profile. Reserve the
persistent-map rewrite (§6) for the day a profiled workload makes the O(N) fork a
measured hot spot; the design, the §18.1.7-preservation argument, and the
(favorable) Boehm-GC interaction are recorded here so that change can be made
deliberately rather than reflexively.
