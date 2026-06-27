# Stack-Safe Deep Recursion in Kappa — A Layered Design

Status: design / staged plan. Companion to the floor-fix already shipped in
`runtime/rt.c:1981-2005` (`krt2i_thread_stack_bytes` / `KAPPA_STACK_MB`).

---

## 1. Motivation and problem statement

Kappa is a **total, dependently-typed** language. Every recursive definition
carries a `decreases` termination witness, so recursion depth is *provably
finite* — but "finite" is not "small". A program that maps over a million-element
list, or folds a long IO-produced stream, recurses to a depth bounded only by its
input.

The native backends (C + LLVM) compile a recursive Kappa function to a native
recursive call on the worker pthread's C stack. Two cases behave very
differently:

* **Tail self-calls are already constant-stack.** `compileFunctionGlobal`
  (`src/Kappa/Backend/C.hs:687-730`) lowers each n-ary global to a
  `static KValue *kw_g(params){ while(1){ <body> } }` worker. A direct saturated
  self-call in tail position is recognised by `selfTailArgs`
  (`src/Kappa/Backend/C.hs:1682-1685`) and lowered by `emitTailLoop`
  (`src/Kappa/Backend/C.hs:1690-1704`) to: evaluate new args into temps, reassign
  the parameter cells, `continue;` — a zero-allocation loop. Any *other* tail
  call (mutual recursion, a call through a function value) goes through
  `emitTailApp` (`src/Kappa/Backend/C.hs:1716-1737`), which returns a heap
  `kbounce(f,a)` cell, drained in one C frame by `ktrampoline`
  (`runtime/value.c:387-394`). IO do-blocks get the analogous treatment: they
  lower to heap `OP_BIND`/`OP_THEN` nodes driven by the flat `krun_io` trampoline
  (`runtime/prims.c:854-917`) with an explicit heap `defers` stack.

* **Non-tail recursion runs native frames and overflows.** Consider

  ```
  count xs = match xs of Nil -> 0 | x :: rest -> addInt 1 (count rest)
  ```

  Here `count rest` is an *argument* to `addInt`, not in tail position. The sink
  traversal `consume` (`src/Kappa/Backend/C.hs:2907-2959`) takes its default arm
  → `compileApp` → `compileAppGlob` (`src/Kappa/Backend/C.hs:2503`) →
  `compileDirectCall` (`src/Kappa/Backend/C.hs:2614-2633`), which emits the bare
  C call `kw_count(rest)`. Each recursion level is one live worker-pthread C
  frame. On the C backend (fatter frames than LLVM) this overflows at
  **~8372 frames** — `repro/native-stack-repro.kp`.

The shipped **floor-fix** gives worker/reactor threads a bigger, lazily-committed
stack (default 8 MiB to match the main thread, env `KAPPA_STACK_MB`;
`runtime/rt.c:1991-1996`). Because pthread stacks are demand-paged, the
reservation is virtual (VSZ), not resident (RSS), until the recursion actually
goes deep. This is a *floor*, not a fix: it raises the overflow depth but does
not remove it, and a sufficiently deep total program still dies.

**Goal:** a principled transformation that makes the *common* deep-recursion
shapes run in **constant (or near-constant) stack**, without forcing a large
per-worker virtual reservation — keeping the floor only as a backstop.

The spec already commits to this principle for the Python backend
(`docs/Spec.md:28204-28213`, §27.5A.3): *"Recursive Kappa definitions accepted by
Kappa termination checking MUST be lowered using loops, trampolines,
defunctionalized control, CPS, an explicit runtime stack, or another stack-safe
representation … Failure to provide stack-safe lowering … is a backend
rejection, not a permitted runtime RecursionError."* The C/LLVM backends lean on
the OS stack today only because native stacks are large. This document extends
that principle to the native backends.

---

## 2. Surveyed techniques and tradeoffs

### 2.1 TRMC — Tail Recursion Modulo Cons (constructor destination-passing)

A recursive call sitting in a single constructor field in tail position —
`map f (x::xs) = f x :: map f xs` — is *almost* tail-recursive. TRMC allocates
the `Cons` node **first** with its tail field left as an uninitialised **hole**,
passes a pointer-to-that-hole (the *destination*) into the recursive call, and
the recursion writes its result directly into the hole. The call becomes a true
tail call (a loop): one traversal, constant stack, **same allocation** as the
original. Bour/Clément/Scherer (2021) measure this matching the non-tail
original, while a CPS rewrite is a constant-factor slowdown.

* Qualifying condition (Lorenzen & Leijen): the call is `C[f e]` in tail
  position where `C` is a single-hole **constructor** context. OCaml ships this
  as `[@tail_mod_cons]` (4.14+): first-order, syntactic, emits a direct entry +
  a destination-passing (DPS) variant.
* **Does NOT cover:** non-constructor wrappers (`addInt 1 (count rest)`,
  `n * product xs` — "addition is not a data constructor"); results that flow
  through a non-constructor before the hole; multiple recursive calls under one
  constructor (`Node (recur l) (recur r)` — only one can be the hole);
  higher-order/indirect recursion.
* Soundness: the hole write is a hidden mutation, but confined to a freshly
  allocated, not-yet-observed cell — observationally pure (Bagrel 2023 makes this
  safe with a write-once linear `Dest` type). It breaks **only** under
  multi-shot continuations (call/cc, multi-shot effect handlers), which re-enter
  a captured half-filled context. **Single-shot resumption stays linear and
  sound** (OCaml 5 effects); Koka needs the hybrid refcount-guarded copy because
  it has general multi-shot handlers.

### 2.2 Accumulator modulo an associative operator (monoid-context TRMC)

`f c (recur)` where `op` is associative with a unit is tail-recursion modulo an
associative operator (Leijen & Lorenzen, POPL'23, §4.4): a worker threads an
accumulator and applies `op` eagerly going down, so the call becomes genuinely
tail. This is exactly the `count`/`sum`/`length`/`concat` family — the prompt's
own `addInt 1 (count rest)` (op = `addInt`, unit = 0).

* The **sole** obligation is *associativity*; the unit only seeds the base case.
  Commutativity is **not** required. A monoid with recursion on either side needs
  a product `(l,r)` context (§4.5).
* Non-associative ops (subtraction) are ineligible and silently wrong — the
  recognition table must be vetted.
* Strictness matters: the accumulator must be forced eagerly or the overflow just
  relocates to heap thunks. Kappa is strict, so this is moot.
* Risch's REMREC (1973) already did the modulo-associative-operator case; this is
  old, well-understood ground.

### 2.3 CPS + defunctionalisation — the universal fallback

CPS-convert so **every** call is a tail call, then trampoline to constant native
stack; defunctionalise the continuation into an explicit heap **frame-stack**.
This linearises **any** recursion shape (tree, mutual, non-linear), which is why
it is the correct universal fallback behind TRMC.

* `count' (x::rest) k = count' rest (λv. k (addInt 1 v))`: every call is now
  tail; a trampoline runs it in constant native stack. The cost has *moved*, not
  vanished — an O(N) continuation chain on the heap. Defunctionalisation
  (Reynolds 1972; Danvy & Nielsen 2001) replaces each continuation lambda with a
  tagged frame capturing only its free variables, plus one first-order `apply_k`
  dispatcher: a contiguous, GC-friendly, cache-friendly **explicit data stack**.
* This is *principled*, not ad-hoc: the functional correspondence (Ager,
  Biernacki, Danvy, Midtgaard 2003) shows CPS-then-defunctionalise-the-continuation
  is exactly how you derive a CEK/CESK abstract machine from an evaluator — the
  defunctionalised continuation **is** the machine's control stack.
* Production precedent: Scala (`cats`/`scalaz` `Trampoline`/`Free`), Clojure
  `trampoline`. The universal lesson: native recursion is far cheaper per frame,
  so deploy the heap stack **selectively** (only where depth can exceed the
  native stack), not as a blanket default.

### 2.4 Runtime-level stack management

* **Cheney on the M.T.A.** (Baker 1994; CHICKEN, Cyclone): whole-program CPS,
  functions never return, the C stack is a GC nursery, a copying minor-GC
  evacuates live objects off the stack then `longjmp`s SP back. Core is a
  **moving** collector + whole-program CPS.
* **Segmented stacks** (Go ≤1.3): linked segments; abandoned for the "hot split"
  pathology (a call on a segment boundary in a hot loop thrashes alloc/free).
* **Contiguous growable stacks** (Go ≥1.3): on overflow, copy the whole stack to
  a 2× one and fix up every interior pointer — requires **precise** stack maps.
* **GHC heap-allocated stacks + chunks**: the thread stack lives in the GC heap,
  split into clean/dirty chunks with an underflow frame at each boundary. The
  mature "heap stack" design — but presumes a **precise** GC and an RTS that
  already runs on that heap stack.
* **JVM fixed stack** (`-Xss`): deep recursion throws `StackOverflowError`; no
  TCO. "Fixed stack + clean failure" is a legitimate, widely-shipped floor.

**The common thread:** every technique that *grows or relocates* a stack
(Cheney, Go contiguous, GHC heap stacks) requires **precise pointer
information**. Kappa's runtime uses **conservative Boehm**, a **non-moving**
mark-sweep collector with interior pointers off
(`runtime/gc.c` — `GC_set_all_interior_pointers(0)`), scanning each worker C
stack conservatively. This **rules out Cheney-MTA and Go-style growable C stacks**
for Kappa as-is: both demand a moving/precise GC. Adopting either means replacing
the GC *and* (for Cheney) CPS-converting the entire backend so functions never
return — a foundational rewrite, for no advantage over §3's plan.

The techniques that need **no precise info**, and therefore fit Kappa: (i) a
fixed/large lazily-committed native stack (the JVM floor, already shipped);
(ii) IR-level transforms that turn the recursion into a loop (TRMC) or move the
frames onto an **explicit heap data structure the runtime already roots** — which
is precisely what the existing IO CK machine (`krun_io` + `K_BOUNCE`/`K_IOTAIL`
heap cells) does for IO. Holes and frames are ordinary `GC_MALLOC` cells Boehm
already traces; **no GC change is needed.**

---

## 3. The chosen layered design

A single technique cannot be both cheap-on-the-common-case and universal. So the
design is **layered**, cheapest-first, with each layer catching what the one
above it cannot:

```
  Layer 1  TRMC (constructor + associative-op)   — constant stack AND heap, automatic
              covers: map/filter/append/concatMap (cons), count/sum/length/concat (assoc-op)
  Layer 2  CK-machine heap frame-stack            — constant native stack, O(N) heap
              covers: the residue (tree folds, mutual rec, f x (g (recur)), non-linear)
              entered only past a native-depth budget
  Layer 0  big lazily-committed worker stack      — backstop; clean diagnostic on overflow
```

### 3.1 Primary technique to implement first: **TRMC (Layer 1)**

TRMC is the highest value-to-risk step. It gives **true constant stack AND
constant heap** (no per-frame allocation) for the *most common* deep-recursion
shapes, needs **no GC change** and **no runtime change**, and is Boehm-safe
because the holes live in the same `kctor` cells the backend already allocates.

Two sub-cases, both as a Core→Core (or KBackendIR) pass on the worker-lowering
path, run **after** type/quantity erasure (so it sees runtime constructor arity,
matching `compileCtor`):

1. **Modulo-cons** (`x :: recur`, `Wrap (recur)`): detect a recursive call in a
   single-hole constructor field in tail position; allocate the node with a
   hole; thread a destination; turn the call into the existing
   `emitTailLoop`/`kbounce` machinery writing into the hole. Targets: the
   linear-spine list-builders — `map`, `filter`, `append`, `concatMap`,
   `take`, range-without-accumulator. Several are stdlib functions every program
   pulls in; `append` is already written in modulo-cons form **and** carries
   linearity annotations (`append : {a} -> (1 xs) -> (1 ys) -> List a`).

2. **Modulo-associative-op** (`addInt 1 (recur)`, `x + sum xs`, `acc ++ recur`):
   rewrite `f` into a worker `f' … acc` folding the op-context into `acc`
   eagerly; the recursive call becomes `selfTailArgs`-eligible and the **current**
   `emitTailLoop` turns it into a constant-stack `continue` — **no runtime
   change at all**. Recognition starts from a *trusted allowlist* of associative
   prims (`addInt`/`mulInt`/`max`/`min`, String/List `append`, bigint), names
   centralised in `Kappa.Builtins`, mirroring the `trustedIntPrimModule` posture
   in `Kappa.Termination`. This kills `count`/`sum`/`length`/`concat`.

**Why Kappa can make this automatic (no annotation).** OCaml makes TMC opt-in
because it is impure: moving the held argument to be evaluated *last* can reorder
observable effects/exceptions. Kappa is **pure, strict, total, and
effect-tracked** — the reorder is observationally invisible, so the transform is
a sound *automatic* optimisation, not an opt-in. *Recommendation:* still surface
an optional diagnostic/attribute so a programmer who *expects* constant stack
gets a warning when a refactor (e.g. moving the recursive call into a `let`)
silently drops it out of TMC position — the documented OCaml footgun.

**Boxing caveat (interacts with UNBOXING).** `compileCtor`
(`src/Kappa/Backend/C.hs:2795-2811`) routes small/nullary constructors to
immediate packed words (`Repr.LayoutImmediate` → `kctor0`) with **no addressable
hole**. TRMC must force the **boxed** `kctor` path for any cell it threads a
destination through, and its hole write must target the **same field index**
`compileCtor` uses. Share the field-index logic between the TRMC pass and both
backends' ctor lowering (C + the LLVM mirror).

### 3.2 General fallback: **extend the IO CK machine to pure recursion (Layer 2)**

For the residue TRMC cannot cover — general tree folds, mutual recursion,
`f x (g (recur))`, non-linear shapes — the principled fallback is CPS +
defunctionalised heap frame-stack (§2.3). **Kappa already has this machine, for
IO.** The runtime has:

* a flat heap-continuation driver — `krun_io` (`runtime/prims.c:854-917`), a
  single `while(1)` trampoline;
* heap deferred-call cells — `K_BOUNCE`/`K_IOTAIL` (`runtime/value.c:387-419`),
  sharing the `as.bounce.{fn,arg}` shape;
* the precedent of moving a recursion's pending obligations off the C stack onto
  an explicit heap stack — the `defers` frames (`runtime/prims.c:863-894`);
* GC tracing, safepoints, and interruption already wired for these `Cont` nodes.

The gap is purely that **pure evaluation never enters this machine** — the only
site that emits eager native recursion for a defined global is
`compileDirectCall` → `kw_g(args)` (`src/Kappa/Backend/C.hs:2631`). The
`KKind` frame enum is entirely IO/effect control; there is **no pure-computation
frame kind** ("apply `addInt 1 □` to my result"). The work is to **add**
pure-arg frame kinds (e.g. `KK_PUREARG`) to the `Cont` chain and route a
potentially-deep non-tail call through a frame-push + a `krun_io`-shaped drain,
instead of a nested `kapp`. This is *extending* a proven, GC-traced,
interruptible evaluator — not inventing a runtime, and it keeps the non-moving
Boehm invariant intact.

This is the same family the spec already blesses (§27.5A.3) and the same
construction (CPS + defunctionalise the continuation) that derives the CEK
machine — so it is principled, not ad-hoc.

**Selectivity is mandatory** (Layer 2 is a regression if applied blanket). Every
frame becomes a heap alloc + a dispatch-loop turn + a value re-box, versus a
register-passing C frame; and it fights the UNBOXING/scalar-worker work (a scalar
`Int` recursion routed through the CK machine loses its unboxed fast path). So:

* keep the existing tail fast paths (`emitTailLoop`, `emitTailApp`) untouched;
* run non-tail recursion **native by default**;
* at the loop back-edge / function entry, check a cheap **native-depth budget**
  (a thread-local counter, or a stack-pointer / guard-page probe; the runtime
  already has `backedge_budget`/safepoint plumbing). Only when depth crosses the
  threshold does the worker capture the rest as a heap continuation and continue
  on the CK machine.

This pays **zero** heap cost for shallow recursion (the overwhelming common case
stays native and fast, unboxed where applicable), and only the deep tail ever
touches the heap stack. It is the in-tree scalar-worker pattern
(`src/Kappa/Backend/C.hs:769-826` — a fast path with a sound escape to a boxed
slow path) applied to recursion depth.

### 3.3 Role of the `decreases` witness — soundness license, NOT a depth oracle

The user asked whether `decreases` can pre-size the stack, justify the
transform, or act as a static depth oracle. Verdict, grounded in the spec and
code:

* **Pre-size the stack from the measure — NO (unsound/impractical).** The measure
  is an **erased compile-time artifact**: *"those witnesses are compile-time only
  and do not appear in runtime code"* (`docs/Spec.md:15331-15333`); *"decreases
  does not change runtime behavior"* (`docs/Spec.md:15354`). It is absent from
  the backend IR — `Core.Term` has no measure constructor
  (`src/Kappa/Core.hs:102-163`), and the backend reads only `gsBodies`/`gdType`
  (`src/Kappa/Backend/C.hs:108`). It is generally **symbolic/lexicographic**
  (`structural xs`, `length xs`, a `by R using proof` well-founded relation;
  Spec §15.3/§15.4/§15.11), so even a `Nat` measure yields no static depth bound.

* **Justify the transformation — YES, decisively (the soundness license).**
  Termination acceptance proves the recursion is finite, so a heap-stack/CPS
  lowering provably terminates and every TRMC hole is provably filled. This is
  the *correctness license* for an unconditional, automatic stack-safe rewrite —
  exactly the property §27.5A.3 relies on. It does not *pick* the transform, but
  it removes the "unfilled hole / diverging recursion" hazard that an
  effectful/partial language must guard against. (Totality also discharges the
  termination side-condition of the accumulator rewrite for free.)

* **Static depth oracle — NO in general**, because the measure is erased and
  symbolic. A *future* refinement could, when the measure is a closed/small
  literal bound, statically prove a call chain stays within the native budget and
  skip Layer 2 entirely (leaving it native) — but this requires un-erasing a
  restricted measure into the backend, which portable v1 forbids, so it is
  explicitly out of scope here.

Net: use totality as the **license** that makes the rewrites unconditionally
sound and automatic; do **not** try to read the measure at runtime.

### 3.4 Worker-stack floor (Layer 0) and virtual-memory optics

Keep the lazily-committed worker stack as the permanent backstop for whatever is
not transformed (non-TRMC tree second-branches, residue below the depth budget
during Layer-2 rollout). Tuning:

* **Default size:** 8 MiB today (main-thread parity, `runtime/rt.c:1993`). Once
  Layer 1 lands and Layer 2's depth-guarded escape exists, **lower the default to
  ~2–4 MiB** — the floor no longer needs to absorb arbitrarily deep recursion,
  only shallow non-transformed residue. Keep `KAPPA_STACK_MB` as the override.
* **Optics — keep VSZ modest and RSS proportional to real depth:**
  * **Lazy commit** (already true): `pthread_attr_setstacksize` reserves
    *virtual* address space; pages become resident only when touched. A recursion
    that uses 2 MiB costs ~2 MiB RSS even under a larger reservation.
  * **Worker count is bounded:** workers = ncpu, capped 64 (`runtime/rt.c`), so
    total VSZ = `stack_mb × min(ncpu,64)` is bounded and RSS tracks real depth.
  * **Main-thread parity:** keep the worker default equal to the main thread's so
    a program's depth behaviour does not depend on which thread hosts the fiber.
  * **Failure mode:** prefer a **clean stack-overflow diagnostic** ("stack
    overflow at recursion depth N in `f`") over a raw `SIGSEGV` — the JVM
    "fixed stack + clean failure" posture. Once Layer 2 is in, a depth-budget
    crossing routes to the heap stack instead of failing, so the floor's overflow
    becomes effectively unreachable for accepted total programs.
  * **Per-fiber growable stacks are NOT pursued** — that is the Go/GHC moving/
    precise-GC path, incompatible with conservative Boehm (§2.4).

---

## 4. Staged implementation plan

**Stage 0 — Floor (DONE, keep).** Big lazily-committed worker stack,
`KAPPA_STACK_MB`, main-thread parity (`runtime/rt.c:1981-2005`). After Stage 1
lands, lower the default to ~2–4 MiB and add a clean overflow diagnostic.
*Tradeoff:* O(depth) memory, finite ceiling; covers all shapes with zero
per-call cost. Backstop only.

**Stage 1 — TRMC, automatic (PRIMARY).** Core→Core pass after erasure.
  * 1a. **Modulo-cons** for the single-hole constructor-tail list-builders
    (`map`, `filter`, `append`, `concatMap`, `take`, …). Force the boxed `kctor`
    path; share field-index logic with `compileCtor`
    (`src/Kappa/Backend/C.hs:2795`) and the LLVM mirror; thread the destination
    through `emitTailLoop`/`kbounce`.
  * 1b. **Modulo-associative-op** from a trusted prim allowlist (`Kappa.Builtins`),
    synthesising a worker + strict accumulator and routing through the **existing**
    `emitTailLoop` — **no runtime change**. Kills `count`/`sum`/`length`/`concat`.
  * Optional `[@constant_stack]`-style diagnostic when a definition that *looks*
    like it should be TMC falls out of position.
  * *Verify with native perf gates* (scalar-worker/alloc), not just llvm-parity —
    parity passes on correct-but-boxed regressions.

**Stage 2 — Multi-hole constructors, partial.** For `Node (recur l) (recur r)`,
make the rightmost branch the tail-position hole (OCaml's rule), leave the
other(s) native. Halves stack growth for balanced trees; full constant-stack for
trees needs a worklist/zipper, out of scope for an automatic pass.

**Stage 3 — CK-machine heap frame-stack (GENERAL FALLBACK).** Add pure-arg
`Cont` frame kinds (`KK_PUREARG`) to the IO CK machine; at `compileDirectCall`'s
non-tail recursion site (`src/Kappa/Backend/C.hs:2631`), emit a frame-push + a
`krun_io`-shaped drain instead of a nested native call, **gated behind a
native-depth budget** so shallow recursion stays native and unboxed. Mirror in
LLVM. Reuses `krun_io`/`K_BOUNCE` (`runtime/prims.c:854-917`,
`runtime/value.c:387-419`); no GC change. This closes the residue Stage 1/2
leave open and removes the need for a *large* per-worker reservation.

**Stage 4 — Modulo-monoid generalisation (longer horizon).** Extend Stage 1b
from the trusted prim allowlist to any `Monoid`/`Semiring` `append` (Leijen &
Lorenzen §4.4–4.6), with a product `(l,r)` context when recursion can land on
either side. Note `src/Kappa/Prelude.hs` states the associativity laws are
**structural-contract only** (no equational-rewriting layer yet), so until that
layer exists, instance membership is a *trust assertion* (an
`assertTerminates`-style escape), not a machine-checked proof. Promote to
*proven* once the equational layer lands.

**Stage 5 — Hybrid uniqueness-guarded TRMC (only if Kappa exposes multi-shot
resumption).** Pure total recursion is single-shot/linear, so in-place hole
filling is unconditionally sound and Stages 1–4 need no refcount check. **Only**
if effect handlers later allow multi-shot resumption does the Koka hazard apply
(a captured half-filled context re-entered). Then add the Perceus-refcount
uniqueness check: fill in place if unique, copy-the-context-path if shared
(Lorenzen & Leijen §7.2; the refcount-free sentinel-hole variant is §7.4).
Sequence **after** Perceus RC lands — they share the same refcount substrate.
Until then, **skip it** (pure overhead) and forbid TRMC under any multi-shot
handler.

---

## 5. Key tradeoffs, summarised

* **TRMC vs the big-stack floor:** TRMC gives *true constant stack* for the
  common case with no per-worker reservation; the floor is O(depth) memory with a
  ceiling. TRMC only covers modulo-context shapes, so the floor stays as backstop.
* **TRMC vs whole-program CPS:** CPS makes *all* recursion constant-stack but
  pays a heap continuation per call, including the 90% cheap leaf/tail calls
  (Bour et al., Leijen-Lorenzen both measure this tax). TRMC pays nothing extra
  on the fast path and matches hand-written loops. The principled hybrid is
  exactly §3: TRMC for modulo-context, CK-machine CPS only for the residue — the
  "fall back to general evaluation contexts" instance of the unified
  Leijen-Lorenzen framework.
* **Automatic vs annotation-driven:** Kappa's purity + strictness + totality +
  effect-tracking make the eval-order reorder invisible, so the transform is
  automatic and silent (unlike OCaml). Keep an *optional* diagnostic for the
  refactor footgun.
* **Why not Cheney-MTA / Go growable stacks:** both need a moving/precise GC;
  kappart2 is conservative non-moving Boehm with interior pointers off. Adopting
  either is a foundational GC + backend rewrite for no gain over §3.
* **Soundness ceiling:** in-place hole-filling is sound *because* pure total
  recursion is single-shot. The only thing that breaks it is multi-shot effect
  resumption — gated behind Stage 5.

---

## 6. Open questions

1. **Depth-budget probe (Stage 3):** thread-local counter at the loop back-edge,
   or a stack-pointer / guard-page check against `pthread_attr_getstack`? The
   counter is portable but per-call; the SP probe is cheaper but platform-specific.
2. **Threshold tuning:** at what native depth does Layer 2 take over? Must leave
   enough headroom for one heap-stack escape frame on the smaller (Stage-0-lowered)
   default stack.
3. **LLVM mirror coupling:** Stages 1–3 must be implemented twice (C + LLVM) or
   coordinated with the planned LLVM Phase-2 representation/coroutine-CPS work, to
   avoid divergent field-index / frame-kind logic. The `emitTailApp` ↔
   `workerMayBounce` lock-step warning (`src/Kappa/Backend/C.hs:1712-1715`) shows
   the cost of a coupled-authority drift.
4. **Multi-hole completeness (Stage 2):** is "rightmost hole + native rest"
   acceptable for the realistic balanced-tree workloads, or is a worklist/zipper
   transform worth it?
5. **Restricted-measure depth oracle:** is there a useful subclass of `decreases`
   measures (closed literal bounds) worth un-erasing into the backend to skip
   Layer 2 entirely for those functions, despite the portable-v1 erasure rule?
6. **Interaction with Perceus + reuse:** Stage 3's per-frame heap traffic is
   mitigated by Perceus RC + reuse on the roadmap; sequence so the CK-frame work
   composes with (not duplicates) that effort.

---

## 7. Primary sources

* Bour, Clément, Scherer, *Tail Modulo Cons* (2021), arXiv:2102.09823 — DPS
  direct+destination pair; CPS-vs-TMC perf.
* OCaml manual, *The Tail Modulo Constructor program transformation* —
  qualifying conditions, `[@tail_mod_cons]`, eval-order-last caveat, first-order
  restriction.
* Leijen & Lorenzen, *Tail Recursion Modulo Context: An Equational Approach*,
  POPL'23 — modulo-context generalisation, §4.4 associative-operator/length, §4.5
  monoid product, §4.6 semirings, §9 REMREC/Risch 1973.
* Lorenzen & Leijen, *Tail Recursion Modulo Context* (JFP'25 ext.) — §7.1
  non-linear control (multi-shot break), §7.2 refcount hybrid, §7.4 sentinel-hole.
* Bagrel, *Destination-passing style programming: a Haskell implementation*
  (2023), arXiv:2312.11257 — write-once linear `Dest`, safe holes in a pure
  language.
* Reynolds (1972) *Definitional Interpreters*; Danvy & Nielsen (2001)
  *Defunctionalization at Work* (BRICS RS-01-23); Ager, Biernacki, Danvy,
  Midtgaard (2003) *A Functional Correspondence between Evaluators and Abstract
  Machines* (BRICS RS-03-13) — CPS + defunctionalise-continuation = CEK/Krivine/SECD.
* Baker (1994), *Cheney on the M.T.A.*; CHICKEN internals; Go contiguous-stacks
  (Agis); GHC stack-chunks (Well-Typed); JVM Spec §2.5.2 — runtime stack survey.
* Boehm-Demers-Weiser GC (non-moving, conservative).

## 8. Internal references (file:line)

* `src/Kappa/Backend/C.hs:687-730` — `compileFunctionGlobal` `while(1)` worker.
* `src/Kappa/Backend/C.hs:1682-1704` — `selfTailArgs`/`emitTailLoop` (tail
  self-call → loop).
* `src/Kappa/Backend/C.hs:1716-1737` — `emitTailApp` (tail call → `kbounce`);
  authority coupled to `workerMayBounce`.
* `src/Kappa/Backend/C.hs:2614-2633` — `compileDirectCall` emits `kw_g(args)`:
  the non-tail native-recursion site (Stage 3 integration point).
* `src/Kappa/Backend/C.hs:2795-2811` — `compileCtor` eagerly builds `kctor`
  fields; `Repr.LayoutImmediate` → `kctor0` has no hole (TRMC must force boxed).
* `src/Kappa/Backend/C.hs:769-826` — scalar-worker fast-path + boxed escape: the
  in-tree fast-path/escape staging precedent for Stage 3.
* `src/Kappa/Core.hs:102-163` — `Term` has no `decreases`/measure constructor.
* `src/Kappa/Syntax.hs` — `Decreases`/quantities (`QZero`/`QOne`/…); `append`
  already `(1 xs)(1 ys)`.
* `src/Kappa/Check.hs:13645-13814` / `src/Kappa/Termination.hs` — termination
  checker consumes `decreases`; `trustedIntPrimModule` posture.
* `runtime/rt.c:1981-2005` — `krt2i_thread_stack_bytes` / `KAPPA_STACK_MB` floor
  (names the ~8372-frame overflow).
* `runtime/value.c:387-434` — `ktrampoline` drain; `kbounce`/`kio_tail`/`kapp`.
* `runtime/prims.c:854-917` — `krun_io` flat IO CK-machine trampoline + heap
  `defers` stack.
* `runtime/rt.c:77-78` — `krt2_bind`/`krt2_then` heap OP-node builders.
* `runtime/gc.c` — `GC_INIT`, `GC_set_all_interior_pointers(0)` (non-moving Boehm).
* `docs/Spec.md:15268-15366` (§15.11: measure erased, no runtime behavior);
  `docs/Spec.md:28204-28213` (§27.5A.3: termination-checked recursion MUST be
  lowered stack-safely; overflow = backend rejection).
* `repro/native-stack-repro.kp` — the `addInt 1 (go rest)` overflow repro.
