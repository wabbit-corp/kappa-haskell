# Memory-Efficiency Research: Reuse, Stack/Region Allocation, and RC for Kappa

Status: research synthesis + staged recommendation. Audience: anyone working on
the native backends (C and LLVM), the kappart2 runtime, or the QTT/§12 borrow
analysis. This document surveys the literature on minimizing heap churn in
functional languages, then assesses each technique against Kappa's *specific*
situation: a CK-machine CPS runtime, a conservative Boehm GC, immediate tagging,
and — the distinctive asset — a static substrate (QTT quantities, §12
borrow/region system, purity, totality) that several of these techniques have to
*reconstruct* by whole-program inference.

The grounding fact, from `docs/RUNTIME-EFFICIENCY-REVIEW.md`: **"allocation, not
indirection, is the dominant cost ... almost nothing is recycled."** Fork is
~832 B/op and the fork/await ping-pong ~704 B/op, versus Go's ~128 B/op (Go
reuses pooled `g` structs). Every recommendation here is judged by how much
allocation it removes per unit of implementation complexity, with prerequisites
stated honestly.

---

## Part 1 — Survey of the techniques

The four families all attack the same problem (heap allocation in idiomatic
functional code) from different angles. They are not mutually exclusive; the
realistic end state is a hybrid.

### 1.1 Functional in-place / space reuse (Perceus, FP²/FIP, Frame-Limited Reuse)

The core question: when a program pattern-matches (destructs) a heap node and
then builds a node of the same size, can the *old* cell's memory be handed
directly to the new node — eliminating the free+malloc pair? This turns
idiomatic functional code (list reverse, tree rebalancing, `map`) into in-place
mutation with zero allocation, without the programmer writing imperative code.
The axis that matters for Kappa: *how* you know the consumed node is unique —
dynamically (a runtime refcount==1 test) or statically (linearity/uniqueness).

**Perceus** (Reinking, Xie, de Moura, Leijen — PLDI 2021) is precise,
non-deferred reference counting. The compiler inserts `dup(x)` / `drop(x)` so
the program is *garbage-free*: every object is freed at the exact moment its
last reference dies. Two static rewrites make it cheap:

- *Ownership transfer* — references are consumed (owned) by callees rather than
  retained by callers, pushing `dup`s to the leaves and `drop`s to last-use.
  For `map` this halves live memory: the input is freed cell-by-cell *as* the
  output is built.
- *Reuse analysis + drop specialization* — a destructive match yielding a
  known-size node, paired with a same-size constructor, is rewritten so the
  freed cell's address becomes a *reuse token* `ru`. The generated code is
  `val ru = if is-unique(xs) then &xs else { ... ; alloc(2) }` then
  `Cons@ru(...)` — i.e. *if the consumed node is unique, the malloc is
  eliminated and the constructor is written in place*; if shared, it falls back
  to a fresh `alloc`.

Cost model: RC's overhead is dup/drop traffic (one memory write + a branch
each) and, critically, *atomicity* — counts on thread-shared objects need
atomic ops. Perceus uses non-atomic counts where statically safe; the paper
reports up to **220% speedup on microbenchmarks** purely from that. Reuse trades
RC traffic for eliminated malloc/free plus cache locality (the freed cell is
hot). Break-even: reuse pays off whenever per-node RC bookkeeping is cheaper
than an allocator round-trip — usually true.

**FP² / FIP — "Fully in-Place Functional Programming"** (Lorenzen, Leijen,
Swierstra — ICFP 2023) is the *static-guarantee* story and the closest match to
Kappa's design. A `fip`-checked function is *guaranteed* to run with no
(de)allocation and constant stack space when its arguments are unique — a
compile-time guarantee, not a runtime "maybe." Machinery:

- *Owned vs borrowed environments*. Parameters split into *borrowed* `ŷ` (hat
  `^f`, freely shared, inspectable but not destructively matched/consumed/
  returned) and *owned* `x̄` (linear, used exactly once). Linearity is enforced
  *syntactically* in the FIP rules, not via a linear type system.
- *Reuse credits ◇ₖ* (Hofmann space-credit lineage). A destructive `match!` on
  an owned size-k node yields a credit `◇ₖ`; the only way to build a fresh
  constructor is to *spend* a matching-size credit. Credits cannot be split or
  merged — that linearity is what preserves cell identity.
- *Atoms + unboxed tuples*. Nullary constructors (Nil, True/False) are *atoms* —
  pointer-tagged, never heap-allocated, needing no credit. Tuples are unboxed
  (returned in registers / as multiple values). Both are *essential*: without
  them splay-tree `lookup` returning `(bool, tree)`, in-place quicksort, and
  finger-tree cons would all still allocate.
- *fip vs fbip*: `fip` = no alloc AND constant stack (tail-recursive, in-place);
  `fbip` = in-place but may use stack (non-tail recursion); `fip(n)`/`fbip(n)`
  allow ≤ n constant cells. Containment: **FIP ⊂ FBIP ⊂ λ^fip** (λ^fip re-adds
  full RC, so FIP is exactly the fragment needing *no* runtime memory
  management).

Discharging the call-site uniqueness obligation (FIP checks the *definition*;
calls still need the inputs to be unowned) has two routes: **(a) uniqueness/
linear types** (Clean, Linear Haskell) — static, no runtime RC at all, at the
cost of code duplication (a unique `reverse` and a shared `reverse`); or
**(b) dynamic Perceus RC** (what Koka does) — one function with an `is-unique`
runtime branch that adapts when the argument happens to be shared.

**Frame-Limited Reuse** (Lorenzen, Leijen — ICFP 2022) fixes two real defects:
(i) *fragility* — match-guided reuse (Koka's algorithm K, Lean's algorithm D) is
destroyed by inlining/hoisting/reordering; (ii) *unbounded peak heap* — pushing
reuse into branches can inflate peak memory by an arbitrary factor. The fix is
**drop-guided reuse**: generate reuse tokens from *drops* (after Perceus has
placed RC ops), so the token appears exactly where the cell dies, robust to
transformation. The **★ condition** on a normalized linear calculus precisely
characterizes three regimes: unrestricted (sound), *garbage-free* (the Perceus
property), and *frame-limited* (every call uses ≤ a constant factor c more
memory). Robust reuse made purely-functional red-black insertion ~19% faster
than hand-optimized in-place C++ `std::map`.

**Lean 4** (Ullrich, de Moura — "Counting Immutable Beans," IFL 2019; CADE 2021)
ships Perceus-style RC + reuse in production (a theorem prover). Its
contribution over Koka was *borrow inference* — inferring which parameters can
pass borrowed (no RC increment), crucial for recursive code. It rests on the
*resurrection hypothesis*: objects often die just before an object of the same
kind is allocated — exactly what reuse exploits. Directly relevant: Lean is
dependently typed and validates that this approach is fast enough for one.

**Roc** is the deliberate *anti-static* design point: by philosophy it will
*never* have linear/uniqueness/dependent/refinement types, relying entirely on
runtime RC + opportunistic in-place mutation (refcount==1 ⇒ mutate in place).
The pure-dynamic end of the spectrum; works with zero static info, at the cost
of the static guarantee.

**Uniqueness / linear / borrowing** is the common static enabler: Clean's
uniqueness typing proves exactly-one-reference so update needs *no* runtime
check; Linear Haskell makes linearity a property of arrows (`a %1 -> b`),
enabling O(1) `freeze` and guaranteed-single-threaded in-place arrays. The
through-line: **static linearity/uniqueness lets you do reuse with LESS (or
zero) runtime RC** — it discharges the `is-unique` obligation at compile time,
deleting both the branch and the dup/drop traffic.

### 1.2 Escape analysis → stack allocation

Per allocation site: does the object's lifetime stay within the allocating
frame, or escape (returned, stored in a longer-lived object, reachable from a
global/another thread)? If it provably does *not* escape, allocate it in the
stack frame or in registers instead of the GC heap. Three compounding payoffs:
**stack allocation** (no heap, no tracing, free pop), **scalar replacement**
(dissolve the object into its fields as SSA registers — the object never
materializes), and **synchronization elision** (a non-escaping object can't be
contended). The analysis is a points-to/reachability problem on a connection
graph (Choi et al., OOPSLA 1999) over the lattice
`NoEscape < ArgEscape < GlobalEscape`. ArgEscape is the hard middle — it needs
inlining or interprocedural summaries, which is why escape analysis is so
coupled to inlining.

- **HotSpot C2** (Kotzmann & Mössenböck, VEE 2005) is the canonical production
  system and the cautionary baseline. It is *flow-insensitive*: an object
  escaping on *any* path is considered escaping, so control-flow merges kill
  scalar replacement. Published measurements: ~2/3 of methods never considered,
  and ~80% of candidates rejected as escaping. Fragile to inlining decisions
  that are themselves heuristic.
- **Graal Partial Escape Analysis** (Stadler, Würthinger, Mössenböck, CGO 2014)
  is the key advance: *flow-sensitive*, keeps objects *virtual* and materializes
  them only on the specific branches where they actually escape (e.g. the slow
  path), recovering exactly the merge/conditional cases C2 loses. Double-digit
  speedups on allocation-heavy code. **Lesson: flow sensitivity is the
  difference between a toy and a useful escape analysis.**
- **.NET** demonstrates two complementary routes. *Language-level*: `ref struct`
  / `Span<T>` are forbidden from the heap by the type system, and C# 11
  `scoped` + ref-safety rules statically bound managed-pointer lifetimes
  (conceptually close to Rust's borrow checker — and to Kappa's §12 borrows).
  *Automatic*: .NET 10's RyuJIT does real object escape analysis + stack
  allocation, now modeling struct fields and doing physical promotion (scalar
  replacement), but still conservative/intraprocedural/inlining-bounded.
- **GHC** does *not* do classic escape analysis. Its toolbox: strictness/demand
  + cardinality analysis (Sergey et al., POPL 2014) driving worker/wrapper
  *unboxing*; unboxed tuples `(# a, b #)` as return-value scalar replacement;
  Selective Lambda Lifting (Graf & Peyton Jones, `StgLiftLams`) to avoid
  definition-site closure allocation, gated by a *closure-growth* cost model
  (modest, sometimes-negative speedups — closure avoidance has subtle
  tradeoffs). Most relevant research: **ASAP** ("As Static As Possible," Proust,
  Cambridge tech report UCAM-CL-TR-908, 2017) — fully automatic, annotation-free
  whole-program static *liveness* analysis that inserts `free()`s where blocks
  become provably inaccessible. Not escape-to-stack per se, but it occupies
  exactly the static-automatic gap between manual `free` and tracing GC.
- **Go** does conservative-by-design escape analysis (assignment-graph
  data-flow, "leaking param" interprocedural summaries; triggers =
  return-pointer / store-into-interface / closure-capture / goroutine). "If
  there is any doubt, it escapes." Deliberately accepts heap-when-stack-was-safe
  to never produce stack-when-escape-was-real. Heuristics are *unstable across
  compiler versions* — not a contract.

Cost-model caveats common to all: stack frames are bounded (cap object size /
array length, don't stack-allocate unbounded or loop-allocated objects). Pairs
naturally with scalar replacement.

### 1.3 Region-based memory management

**Tofte–Talpin region inference** (Information and Computation 1997; Tofte &
Birkedal TOPLAS 1998; MLKit). The compiler translates a typed CBV lambda
calculus into a region-annotated language: `e at ρ` allocates into region ρ;
`letregion ρ in e` pushes a fresh region on a *region stack*, evaluates `e`,
then **pops ρ in O(1)** bulk-freeing everything in it. Lifetimes are strictly
**LIFO / stack-disciplined**. *Region polymorphism* (`Λρ`) lets callees allocate
into caller-chosen regions; *region-polymorphic recursion* gives tight bounds
(and makes inference hard). The analysis is a **type-and-effect system**: the
effect is the set of regions read/written/allocated; `letregion ρ` is sound
exactly when ρ does *not* appear in the result's type/effect — the
*observable-effect / region-escape* condition. *Multiplicity analysis* bounds
each region 0/1/∞ (a ≤1 region can be unboxed/stack-allocated).
*Storage-mode analysis* (`atbot`/`attop`/`sat`) reclaims *within* a still-live
region to fight bloat.

Cost model. *Win*: allocation is a bump pointer; deallocation is O(1) bulk pop —
zero per-object free, no tracing, no pauses, predictable. *Loss — region bloat/
leaks*: a single long-lived value pins the whole region until its `letregion`
exits; programs frequently need manual region-aware rewriting (MLKit ships a
profiler because region performance is non-obvious and brittle). *Limit*: pure
Tofte–Talpin can't express non-nested lifetimes.

**Cyclone** (Grossman et al., PLDI 2002) makes regions *explicit first-class
types*: every pointer carries its region `int *`ρ``; the type tracks a
*capability* (the live-region set), checked modularly via function signatures
with outlives-constraints `ρ1 :> ρ2` — no whole-program pass. Region kinds: LIFO
lexical regions, the GC'd heap region, *unique pointers* (`*`U``, exactly-one-
reference, explicitly freeable, dangling ruled out by modular flow analysis),
and *dynamic* (non-LIFO) regions valid while *open*. Their ISMM'04 experience
report's lesson: **pure LIFO regions are insufficient** for servers/event-loops;
you need dynamic regions + unique pointers + a fallback GC.

**Linear Regions Are All You Need** (Fluet, Morrisett, Ahmed, ESOP 2006) is the
modern unification, most relevant to Kappa: the LIFO restriction comes *entirely*
from the stack discipline; represent each live region by a **linear capability
token** threaded through the program, and lifetimes need no longer be LIFO — a
region is freed exactly when its token is consumed. *Linearity is the soundness
mechanism the region stack stood in for.* (Spegion, ECOOP 2025, pushes to
implicit non-lexical regions with sized/splittable allocations via an effect
system.)

**Hybrid region + GC** (Hallenberg, Elsman, Tofte, PLDI 2002): MLKit runs a
Cheney copying GC *inside* the regions — regions cap fragmentation and give the
GC large pre-sized arenas; GC reclaims intra-region dead values storage-mode
missed. Measured: for code *not* hand-tuned for regions, adding GC *reduces*
memory; regions reduce GC frequency. Complementary, not competitors — the
realistic production target.

### 1.4 Combining RC with tracing to handle cycles

RC frees an object the instant its count hits 0; its fatal blind spot is a
*cycle* — mutually-referencing objects keep every count ≥1 even when the whole
clique is unreachable. Bacon–Cheng–Rajan's "Unified Theory of GC" (OOPSLA 2004)
explains structurally why: tracing and RC are *duals* (live-set-from-roots
least-fixpoint vs dead-set greatest-fixpoint complement); detecting a cycle
needs a non-local reachability query, which is exactly what tracing does. Every
production "RC" collector couples RC with *some* tracing. The four families:

- **Bacon–Rajan trial deletion / the Recycler** (ECOOP 2001). A cycle can only
  become garbage when a count is *decremented to a non-zero value*; such objects
  are buffered *purple* as candidate roots. Trial deletion does a *local*
  sub-trace over the candidate set: *MarkGray* (recursively decrement children's
  counts, subtracting intra-candidate references so each node's residual count
  reflects only *external* references), *Scan*/*ScanBlack* (anything with
  residual >0 is externally reachable → repaint live, restore counts; the rest
  go white), *CollectWhite* (white = genuine cyclic garbage → free). Cost is
  bounded by the candidate subgraph size, **not** the whole heap. The concurrent
  Recycler (Jikes/Jalapeño) hit ~6 ms max pauses — the first on-the-fly cycle
  collector — at the cost of substantial bookkeeping.
- **Backup tracing**: run plain RC for all fast-path frees, let cyclic garbage
  float, and periodically run an *ordinary global mark-sweep* that ignores
  counts. Simplest correct hybrid; coarse and infrequent if cyclic garbage is
  rare. This is what **Koka exposes as opt-in** — Perceus is garbage-free for
  *cycle-free* programs and leans on a backup trace only when cyclic data is
  actually built.
- **CPython**: RC always on (frees the acyclic majority immediately) + a
  generational cyclic collector using `gc_refs` trial deletion. Crucially, it
  *tracks only container types that can cycle* (lists/dicts/instances) and
  *untracks* immutable-only tuples/dicts — the canonical "narrow tracing only
  over what can actually cycle" design.
- **Swift ARC**: RC with *no* cycle collector at all — cycles leak. The
  programmer breaks them manually with `weak` (auto-niled, no increment) and
  `unowned`. The "you break cycles by hand" extreme.

**The crux for a pure language**: immutable inductive (least-fixpoint) data is
*acyclic by construction* — a constructor `C a b` can only reference values that
*already existed*, so the heap object graph is a DAG. Koka relies on exactly
this; Lean 4 structurally forbids cycle-forming constructs, so its RC needs no
cycle collector for ordinary data. Cycles arise *only* from (a) mutable
references (`ref`, `TVar`, `IORef`), (b) shared knot-tying laziness/`letrec`
updated in place (Haskell's `let xs = 1 :: xs`), or (c) mutually-capturing
closures. Pure re-evaluating thunks cannot cycle because nothing is overwritten.

---

## Part 2 — Where Kappa's allocation actually comes from

Grounded in `docs/RUNTIME-EFFICIENCY-REVIEW.md`, the CPS/UNBOXING design notes,
and the runtime/Core source. There are **three distinct, measured sources** — do
not conflate them; they have different fixes.

1. **Fork/scheduler frames — the dominant per-op cost, and it is REUSE-shaped,
   not RC-shaped.** Fork ≈ 832 B/op, fork/await ping-pong ≈ 704 B/op, vs Go's
   ~128 B/op. A fork allocates 208 B Fiber + 40 B Cont + KEnv cells + 24 B
   Waiter + RQNode + a 64 B `pthread_mutex`, none pooled. The review's own
   verdict: *"Nothing in this runtime is the wrong SIZE — the problem is that
   almost nothing is RECYCLED."* This is finding #1, "the single biggest lever;
   the pre-Perceus version of the deferred Stage-5 reuse." **No type-system work
   touches this** — only pooling does.

2. **CK-machine continuation churn (the genuinely-suspending path only).** Each
   *suspending* bind costs ~4–5 `GC_MALLOC`s: the OP_BIND node, the closure box,
   a KEnv cons, the `KK_BIND` Cont, and a re-applied `kapp` (~104 B/bind atop
   the node). Loop bodies rebuild the action tree per iteration. Crucially, the
   landed suspendability analysis (Stage 1.5) keeps *non-suspending* binds as
   straight-line C, so this cost hits only the genuinely-suspending path.

3. **Ctor/record/KValue boxing.** Every value is a ~40 B boxed `KValue`;
   per-field box indirection for records/ctors is "most of real allocation
   volume" and stays Boehm-bound until precise RC. Immediate tagging
   (`kappart.h`: b001 Int / b010 nullary / b011 packed single/two-field) already
   kills the Int-allocation half and gives FIP "atoms" for free, but does
   nothing for n-ary ctor fields (the missing piece is FIP "unboxed tuples" —
   the deferred LLVM-layout work).

### 2.1 The distinctive static asset — verified present, under-exploited

The QTT/§12 machinery is real and runs. `Usage.hs` performs the full §12.2–§12.4
quantity-and-borrow analysis (linear-drop, linear-overuse, borrow-consume,
borrow-escape, borrow-overlap, inout threading). **Critically, the `Q` quantity
(`Q0/Q1/QW/QLe1/QGe1`) survives into the Core IR the backend consumes** — it is
carried on `CLam/CPi/CLet/CLetRec` and on `KBind/KLet` do-items, plus the §12.3
borrow marker on `CPi/VPi`. So the static linearity asset is **available at
codegen** (`C.hs`), not trapped in the typechecker.

The gap: today `C.hs` reads `Q` only for *erasure* (`Q0`/kind-domain →
`kunit()` placeholder) — it does **not** use `Q1/QLe1` for in-place reuse or
drop elision. For **`Q1`-annotated** code Kappa has the exact static information
Koka/Lean *synthesize* with whole-program borrow/heap-share inference (Perceus
§2–3), **already computed and type-checked, and currently discarded after
erasure.**

**Important caveat — the asset is present only where the quantity is annotated.**
This is the one place not to overstate. An *unannotated* binder does **not**
default to a single-use quantity: `qOf Nothing → QW` and `binderQ` returns `QW`
for the symbolic / borrowed / implicit / unannotated cases alike
(`src/Kappa/Check.hs:3194-3208`); only an explicit `Just S.QOne` becomes `Q1`.
And `src/Kappa/Usage.hs` only *checks* quantities (linear-overuse / linear-drop /
borrow-escape) and *propagates* field-linearity from already-`Q1` sources
(`mergeFieldQuantities`/`litLinearFields`) — it does **not** *infer* or
reconstruct `Q1` for a provably-single-use unannotated binder. So for the
**unannotated majority** there is no `Q1` reuse signal at all; the values land at
`QW` and the reuse machinery below never fires on them. Recovering that signal
needs a **single-use / multiplicity inference pass** — exactly what MLKit does
statically and Perceus does dynamically (`is-unique`) — which Kappa does **not**
have. That inference is therefore itself Stage-1 work, not a free pre-existing
asset: the "static linearity Perceus infers" is present for the `Q1`-annotated
fragment and must be *built* for the rest.

Map to the literature precisely (read every "QTT proves uniqueness" below as
scoped to the `Q1`-annotated fragment until the inference pass exists):

- QTT quantity `1 = [1,1]` (linear, used-once, *not* droppable per §12.2) **is**
  an *owned* FIP parameter — destructively matchable and reusable in place with
  **zero runtime refcount check**. This is FIP's static "method (a)"
  (uniqueness-typed reuse), and because the quantity is *part of the signature*
  it sidesteps the code-duplication drawback of Clean-style uniqueness.
- `ω = [0,∞]` is FIP's shared/copy case; `0` is erased and never reaches
  runtime; `≤1` is affine. This is MLKit's multiplicity analysis (0/1/∞) *for
  free*.
- The §12 borrow/region system (`&`/`&[s]` skolem-region borrows, skolem-escape,
  path-sensitive record borrows, first-class `Zipper`/`BorrowView`) **is** FIP's
  `^f` borrowed-parameter discipline — and stronger; it even ships the zipper
  datastructure FIP uses as its flagship example. The §12 `E_QTT_BORROW_ESCAPE`
  check ("closures capturing borrowed bindings escaping through the result") is
  *literally an escape analysis Kappa already runs*.

### 2.2 Acyclicity-by-purity — verified, and it defangs the one RC killer

The *only* two heap-cycle sources in the entire runtime are (a) `K_REF` mutable
cells (`kref_new`/`kref_set`) and (b) `kthunk`/`CLetRec` knot-tying via
`kenv_set_val` backpatch ("CLetRec captures the binder cell"). Everything else —
every ctor, record, closure-over-pure-env, and the entire `Cont`/`KEnv`
continuation spine — is **acyclic by construction** under purity + totality.

This is load-bearing. The classic RC objection (cycles leak) applies to a
*vanishingly small, statically-identifiable* surface. Mapping to the Spec: pure
inductive data is a DAG; codata is expressed via `Thunk` (by-name, re-evaluates,
no shared cell) / `Need` (by-need, write-once memo cell that *cannot reference
itself* because recursion is name-level, §9.3.1.1/§15) — so **codata creates no
heap cycles either**, unlike Haskell's knot-tying `letrec`. The single genuine
cycle source in *pure* terms is mutable shared state: STM `TVar` (§18.1.13), plus
any future `Ref`/`MVar`/`IORef` — all effect-confined, never inside pure data.

---

## Part 3 — How Kappa does reuse/stack/region with LESS runtime machinery

The unifying observation: **every system in Part 1 is reconstructing
ownership/lifetime facts Kappa already has statically *where the program annotates
its quantities*.** HotSpot/Go spend a whole-program points-to analysis to
*approximate* what QTT carries in the types; Perceus/Koka run borrow inference to
*derive* the linearity QTT *proves* — for an explicitly-`Q1` binding. The honest
asymmetry (§2.1): on the **unannotated** fragment Kappa is *not* ahead — an
unannotated binder defaults to `QW`, and Kappa has no single-use inference, so
for those values it must *build* the very multiplicity inference MLKit/Perceus
run (MLKit statically, Perceus via the dynamic `is-unique` test). So the
"Kappa already has it" framing holds for the `Q1`-annotated fragment and is a
*to-do* (a Stage-1 inference pass) for the rest. Purity + totality do help
everywhere regardless: they close the two worst enemies of all these analyses
(hidden store-to-global mutation; divergent/exceptional control paths), making
Kappa's escape/liveness graph *exact* rather than conservative once a quantity is
known.

**Reuse (FIP) — target the static guarantee, not dynamic RC.** A `Q1`,
sole-consumer destructive match that reconstructs a same-arity constructor can be
a **guaranteed in-place field write** — better than Perceus, which needs a
runtime `refcount==1` branch, because QTT *proves* uniqueness at compile time
(verified by `Usage.hs E_QTT_LINEAR_OVERUSE`). The design: treat a `Q1`
destructive match as yielding a static reuse token (size = ctor arity),
spendable by a same-size constructor in scope; emit the in-place write with no
`is-unique` branch and no RC field. For `ω`/unprovable cases, fall back to copy
or to a per-size free-list. The frame-limited **★ condition** is the right model
for *certifying* the region/borrow interactions, and a checked `fip`/`fbip`
annotation can statically certify "no alloc / constant stack" from QTT+borrow
info — a guarantee Koka only approximates and Roc rejects on principle.

**Stack allocation — drive it off QTT + §12, don't port a JIT escape analysis.**
Linear (`Q1`) and borrowed values are *provably non-escaping* ⇒ stack-allocate +
scalar-replace with no points-to graph; `Q0` is erased pre-analysis; only `ω`
needs a real pass (and there, a Graal-PEA-style *flow-sensitive,
materialize-only-where-it-escapes* pass, seeded with Kappa's ownership facts à la
ASAP, is far cheaper than in Java/Go because purity/totality close the worst
edges). The CK-machine/CPS is double-edged: it *reifies continuations as heap
closures* (the textbook escape pattern — naively it *manufactures* the
short-lived garbage we want gone), **but** in a total/pure language continuations
are **linear and LIFO** (one-shot, no `call/cc` capture), so QTT-linearity is the
static witness to lower one-shot continuations to the **call/continuation stack**,
heap-allocating only multi-shot / suspended (fork/promise/`TVar`-crossing)
continuations. This converts the CK-machine's "continuation = heap closure"
liability back into "continuation = stack frame."

**Region allocation — ride the §12 escape analysis already proven.** §12 *is*
the Tofte–Talpin discipline renamed: rigid `ρ` + the **skolem-escape rule** is
*literally* the `letregion` soundness side-condition (ρ not in the result's
type/effect), already checked *modularly* (no whole-program pass); `captures(s)`
is the region effect/outlives; region polymorphism is already spelled
`forall (s : Region)`. The Spec **already sanctions** arena allocation for
`runST` ("zero-cost deallocation without garbage collection," §17.x) and lists
"arena allocation, region-like runtime disciplines" as a permitted backend
strategy (§34.4.1). So wherever the checker already proves a value can't escape
ρ, the backend is *already entitled* to arena-allocate it and bulk-free in O(1)
instead of GC — no new analysis. And QTT-`1` linearity is precisely the **Linear
Regions Are All You Need** soundness device: it licenses *early, non-LIFO* free,
escaping Tofte–Talpin's region-bloat/LIFO limit without dynamic regions.

The common limit, stated honestly and threaded throughout: **every reuse /
in-place / frame-local / region win concentrates on the linear, non-escaping,
acyclic, suspension-free surface.** Multishot and branch-join-shared
continuations, fork/promise/`TVar`-crossing values, and n-ary ctor field boxing
stay Boehm-bound until precise RC. And without a runtime RC header Kappa
*cannot* do Roc/Koka-style "adapts dynamically when shared" — it must choose
statically. That is the correct trade for a total, pure, dependently-typed
language optimizing for *predictable* zero-allocation.

---

## Part 4 — The cycle question for Kappa

**Can Kappa ship precise RC with no general cycle collector?** Yes — and it is an
unusually clean case.

Because purity + totality + name-level-only recursion make *all* pure inductive
data **and** all codata acyclic by construction (Part 2.2), the entire functional
core needs only plain RC (or QTT-guaranteed in-place) with *zero cycle
bookkeeping*. The only genuine cycle sources are `K_REF`/`TVar` mutable cells and
recursive-thunk (`CLetRec`) knot-tying — a narrow, statically-identifiable,
effect-confined set, much sharper than CPython (which must runtime-track every
container).

Recommended design — the CPython lesson with a far sharper static boundary:

1. Segregate `TVar`/`Ref`-bearing state into its own runtime region. The STM
   runtime already owns these and brackets them at `atomically` — a natural
   collection boundary.
2. Collect *that region* with either Bacon–Rajan trial deletion (small,
   localized candidate sets are its sweet spot) or a simple backup mark-sweep
   over just that region.
3. Run RC (or QTT in-place) with **no cycle machinery at all** everywhere else.

This is strictly less work than Koka's general cycle handling, closer to Lean 4
(structurally cycle-free core) than to Python (always-on generational cyclic GC),
and cleaner than Swift's manual `weak`/`unowned` because the cycle-forming set is
*effect-confined* rather than pervasive. QTT compounds it: `Q1` values free
without any refcount op; borrows remove count traffic; `Q0` never reaches runtime
— so both RC traffic and the cycle question shrink to the genuinely-shared,
genuinely-mutable subset. **Net: a backup tracer (or trial deletion) confined to
`Ref`/`TVar` + recursive thunks suffices; no general cycle collector is
required.**

Caveat: *today* the conservative Boehm collector already collects `TVar` cycles
transparently — this question only becomes load-bearing on a *future*
precise-RC migration.

---

## Part 5 — The conservative-GC blocker for precise RC

This is the constraint that gates the high-ceiling work, and it must be stated
plainly: **the conservative Boehm GC is a genuine BLOCKER for precise RC, not a
nuisance.**

Perceus needs (i) *precise per-slot pointer-vs-scalar discrimination* to know
what to `dup`/`drop`, and (ii) write-barrier-free dup/drop. Boehm gives neither
precise roots nor the layout metadata. A conservative collector *also* cannot be
the long-term *backup tracer* for a precise-RC scheme — it can't precisely
identify pointers, so it can't be trusted to reclaim exactly the cyclic garbage a
precise RC leaves behind. Moving to precise RC therefore entails emitting precise
layout/tracing metadata anyway — which is exactly the LLVM-backend layout work.

Two mitigants are *already in place* (verified in `runtime/kappart.h`):

- **Immediate tagging reserves the low 3 bits** as the pre-installed
  pointer-vs-scalar discriminator. `kappart.h` is explicit that b100–b111 are
  reserved for additional immediate *kinds*, and that the Perceus RC borrow /
  thread-shared discriminator lives **in the heap header, not the immediate
  tag** ("an immediate is value-copied and never reference-counted"). Odd words
  are RC-exempt by construction; the alignment assert (`>= 8-byte heap
  alignment, low 3 bits free`) enforces the contract.
- **The do-kernel is already CPS**, which is exactly Perceus's required input
  form: explicit control flow = explicit `dup`/`drop` sites.

The designed bridge to precise RC is the LLVM `coro.id.retcon.once` flat-frame
seam plus a precise stackmap / slot-kind map (UNBOXING Stage 3), or a bespoke
precise collector. Until one of those lands, **Boehm stays the universal safety
net**, precise RC is introduced for the pure acyclic majority, and tracing is the
fallback only for the statically-identified `TVar`/`Ref` region.

Two further constraints to respect regardless: the escape/reuse pass must run
**post-erasure** (RuntimeErased: types + `Q0` + Q0 dictionaries, never reasoning
about a dict that won't exist at runtime — the discipline that fixed the native
IO crash); and scalar-replaced / stack / arena slots must keep pointers in the
Boehm-scannable, immediate-tag-faithful representation (don't hide a live pointer
in a form Boehm won't recognize — e.g. arithmetic-mangled). Naively grafting
arenas onto conservative Boehm risks pointer-misidentification pin-leaks or
corruption; couple the region/arena layer to the precise-layout move.

---

## Part 6 — Staged, prioritized path

The ordering principle: most churn removed per unit of complexity, prerequisites
flagged. Near-term wins (Stages 0–1) are deliberately separated from
research-grade ambition (Stages 2–3). The crucial split: **Stages 0–1 need no
precise GC; Stage 2 is hard-gated on replacing the conservative collector.**

### Stage 0 — Pool the fork hot path (NOW; no type-system or GC prerequisites)

This is the "least complexity, most churn" winner and is **independent of all
type-system work.** It is the pre-Perceus band-aid the efficiency review names as
finding #1 — and it attacks the largest single byte reduction available (the
832 B/op fork cost) directly.

- Intrusive `rq_next` + embedded `Waiter` in the `Fiber` (zero-alloc
  enqueue/park).
- Per-worker `Fiber`/`Cont`/`KEnv`/`RQNode` free-lists (reset-and-reuse on
  finish/pop).
- A 1-word lock replacing the 64 B `pthread_mutex`.
- Inline `{tag, a, b}` OP node (1 malloc, not 2).

Prerequisite-prerequisite: the persistent-runtime fix (review §1) — fixes the
`run_main` re-entrancy crash *and* deletes per-run churn.

**Effort: low. Risk: low** (pure runtime engineering, no semantics change).
**Payoff: the largest measured byte reduction.**

### Stage 1 — QTT-driven frame-local allocation + guaranteed in-place (NEAR-TERM; NO precise GC)

Exploit the asset *under Boehm*. Thread the already-present `Q1/QLe1` + §12
borrow-escape facts from Core into `C.hs` (they are there for *annotated* code —
stop discarding them after erasure). Then:

- For a `Q1`, provably-non-escaping, acyclic ctor/`KEnv` cell: emit arena /
  frame-local allocation that bypasses GC entirely (a frame-local cell never
  reaches the collector).
- For the FIP match-reconstruct-same-ctor shape on a `Q1` scrutinee: emit a
  **guaranteed in-place field write** — no refcount check, because QTT *proves*
  uniqueness. This is the distinctive Kappa move: in-place update *proven*
  statically rather than *checked* dynamically.
- Realize the already-blessed `runST`/`ST` arena (escape already proven by
  skolem-escape) — the canonical first region win, costing no new theory.

**The hard part of Stage 1, stated honestly (§2.1):** the two reuse bullets above
fire only where a binder is `Q1`. Today that means **explicitly-annotated code
only** — an unannotated binder is `QW`, and Kappa has no pass that *infers* `Q1`
for a provably-single-use unannotated binder. So Stage 1 is really *two* pieces:
(i) thread + consume the quantities that already exist (cheap, the data is there
for annotated code), and (ii) **build a single-use / multiplicity inference pass**
(MLKit-style static, or a Perceus-style `is-unique` dynamic fallback) so reuse
extends to the unannotated majority. Without (ii), Stage 1 is correct but narrow —
it only pays off on the hand-annotated linear surface. (ii) is the load-bearing
new analysis, not a thread-through.

This works under Boehm because frame-local cells never reach GC and QTT-proven
in-place needs no RC header.

Prerequisites: a small Core→backend `Q`/borrow propagation pass (the data already
exists for annotated code) **plus the single-use inference pass above for the
unannotated majority**, and the immediate-tagging GC/alignment contract (UNBOXING
Stage 0, already partly landed). **Effort: low–moderate for the threading,
moderate for the inference pass. Risk: low–moderate** (the
in-place write must respect the match-reconstruct shape and Boehm-faithful
pointer representation). **Payoff: removes allocation on the linear/non-escaping/
acyclic surface, including much of the CPS continuation churn (source #2) — but
explicitly NOT the fork frame (Stage 0's job) and NOT fork-crossing/shared-join
values.**

### Stage 2 — Full Perceus dup/drop + reuse on the CPS spine (MEDIUM-TERM; HARD-GATED on precise GC)

Highest ceiling, hardest prerequisite. Insert Perceus dup/drop + reuse on the
CPS continuation spine, with **annotated QTT supplying the linearity witness Koka
infers** (so the front half of Perceus — borrow analysis — is free *for the
annotated fragment*; for the unannotated majority Stage 1's single-use inference
pass, or Perceus's own dynamic `is-unique`, supplies it) and the §12 borrow +
thread-shared-across-fork facts supplying the **non-atomic-vs-atomic RC split**
(`f->k` is thread-local → non-atomic; fork/promise/`TVar` crossings → atomic).
Only the back half (drop/reuse insertion) must be built.

**Hard prerequisite, stated plainly: a precise / non-conservative collector.**
Boehm cannot do Perceus. The path is (a) the LLVM `coro.id.retcon.once`
flat-frame seam + precise slot-kind map (UNBOXING Stage 3), or (b) a bespoke
precise collector. **Effort: high. Risk: high** (new collector + RC correctness
under concurrency). **Payoff: drives per-bind alloc toward zero on the linear
non-escaping path — but honestly, that is largely the path Stage 1 already
covers; the incremental Perceus win is the *ω/shared* values Stage 1 can't prove
statically.** Kappa's QTT (linearity proven, not inferred) + acyclicity-by-purity
make this RC *substantially cheaper to build correctly* than for any conventional
language — but it remains research-grade.

### Stage 3 — RC + GC hybrid for cycles; regions on §12 (END STATE)

- RC + GC hybrid (Part 4): confine the tracing fallback to `K_REF`/`TVar` +
  recursive-thunk closures *only*, exploiting verified acyclicity-by-purity so
  the cycle collector touches a tiny, statically-known surface. Inherits Stage
  2's precise-RC prerequisite.
- Region allocation on the §12 borrow facts (Hallenberg/Elsman hybrid
  region+GC), layered as an optimization where lexical lifetimes beat per-object
  RC. Note honestly: the §12 region system's headline fit notwithstanding, the
  *dominant measured cost* (fork frames) is scheduler-lifecycle, not
  lexical-region-shaped, and regions interact awkwardly with fork/promise/`TVar`-
  crossing values — so regions help the *same* linear/non-escaping surface as
  Stages 1–2, with more machinery. They are an optimization layer, not a primary
  lever.

Known type-system gap to resolve before regions/borrows thread through arbitrary
recursive `IO` loops: the monomorphic `ioBind` wall
(`docs/notes/BORROW_THROUGH_IO_MONAD.md`) caps allocation-regions for `do`-scopes
just as it caps borrows. The clean fix is a **region-threading `do`-scope treated
like the primitive `using` scope**, *not* capture-polymorphic `ioBind`. Until
then, arenas/borrows are safe on the straight-line / `using` / `runST` /
fork-frame shapes — already most of the win.

---

## Bottom line

- **Single biggest lever**: pooling the fork/scheduler frames (Stage 0). It is
  the largest measured byte reduction (832 → toward Go's ~128 B/op), needs no
  type-system or GC work, and is the explicit pre-Perceus band-aid the efficiency
  review already names as finding #1.
- **Most distinctive Kappa win**: QTT-driven *guaranteed* in-place update +
  frame-local allocation (Stage 1) — for `Q1`-**annotated** code Kappa proves
  statically what Koka/Lean check dynamically and Go/HotSpot approximate, and the
  linear/non-escaping/acyclic subset works *under Boehm* with no precise RC. The
  honest caveat (§2.1): unannotated binders default to `QW` and Kappa has no
  single-use inference, so extending this win past the annotated surface requires
  a **single-use / multiplicity inference pass that Kappa does not yet have** —
  itself part of Stage-1 work, not free.
- **Highest ceiling, gated**: full Perceus (Stage 2) is hard-blocked on replacing
  the conservative collector; but QTT (linearity proven where annotated, inferable
  with the Stage-1 pass otherwise) + acyclicity-by-purity (cycles confined to
  `Ref`/`TVar`/recursive thunks) make the eventual RC dramatically cheaper to
  build than for any conventional language, and a backup tracer confined to the
  mutable region means Kappa may never need a *general* cycle collector.

## Key sources

- Reinking, Xie, de Moura, Leijen, "Perceus: Garbage Free Reference Counting with
  Reuse," PLDI 2021.
- Lorenzen, Leijen, Swierstra, "FP²: Fully in-Place Functional Programming,"
  ICFP 2023.
- Lorenzen, Leijen, "Reference Counting with Frame-Limited Reuse," ICFP 2022.
- Ullrich, de Moura, "Counting Immutable Beans," IFL 2019; Lean 4, CADE 2021.
- Choi et al., "Escape Analysis for Java," OOPSLA 1999; Kotzmann & Mössenböck,
  VEE 2005; Stadler, Würthinger, Mössenböck, "Partial Escape Analysis," CGO 2014.
- Sergey, Vytiniotis, Peyton Jones, "Modular, higher-order cardinality
  analysis," POPL 2014; Graf & Peyton Jones, "Selective Lambda Lifting,"
  arXiv:1910.11717.
- Proust, "ASAP: As Static As Possible memory management," UCAM-CL-TR-908, 2017.
- Tofte & Talpin, "Region-Based Memory Management," Inf. & Comp. 1997; Tofte &
  Birkedal, TOPLAS 1998; Grossman et al., "Region-Based Memory Management in
  Cyclone," PLDI 2002; Fluet, Morrisett, Ahmed, "Linear Regions Are All You
  Need," ESOP 2006; Hallenberg, Elsman, Tofte, "Combining Region Inference and
  Garbage Collection," PLDI 2002.
- Bacon & Rajan, "Concurrent Cycle Collection in Reference Counted Systems,"
  ECOOP 2001; Bacon, Cheng, Rajan, "A Unified Theory of Garbage Collection,"
  OOPSLA 2004.

In-repo: `docs/RUNTIME-EFFICIENCY-REVIEW.md`, `docs/Spec.md` (§12, §15, §17,
§18.1.13, §34.4.1), `docs/notes/BORROW_THROUGH_IO_MONAD.md`,
`runtime/kappart.h` (immediate tagging / Perceus reservation),
`src/.../Core.hs` (Q quantities on Core binders), `src/.../Usage.hs` (§12
analysis), `src/.../C.hs` (codegen / erasure).
