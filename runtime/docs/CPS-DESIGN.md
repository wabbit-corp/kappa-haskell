# Kappa Do-Kernel CPS / Continuation Rewrite — Final Design

**Status:** Final design of record (post-review). Ready to stage.
**Author:** Runtime architect (revised incorporating correctness, performance, and feasibility critiques)
**Scope:** the do-kernel lowering in `src/Kappa/Backend/C.hs` and the `kappart2` CK-machine in `runtime/`
**Supersedes:** the prior "DECISION" draft. This version keeps the surviving recommendation, corrects the load-bearing claims the critiques found false against the code as it actually exists, and adds the **Risks & mitigations** and **Rejected alternatives** sections.

> **Reading note.** Three claims in the prior draft were *false against the runtime as written* and are corrected here in place, with a banner where they appear:
> 1. "Finalizers run masked / a child interrupt while parked still runs pending defers in masked LIFO order" — **false today**: `begin_finseq` never raises `mask_depth` (rt.c:377), and an interrupt mid-finseq abandons the scope's remaining defers (rt.c:464). Now a **required fix**, not a property.
> 2. "Structured-shutdown child-drain-before-parent-defer is `OP_DOSCOPE` + `OP_SHUTDOWN_SCOPE` already" — **false today**: `OP_DOSCOPE` (rt.c:609) only allocates an `ExitStack`; it does not create a supervision `Scope` or thread `cur_scope`. Now a **decision to make explicit + implement**, not a property.
> 3. "1 small frame per suspending bind" and "as fast as Go/Rust" — **wrong by ~4–5×** on the suspending path and unmeasured. Corrected in §6 with the real allocation accounting and an explicit honesty statement about Stages 1–4 running on Boehm GC.

---

## 1. Recommendation (TL;DR)

**Adopt the strategy the runtime already embodies: finish CPS-lowering the do-kernel into the existing defunctionalized, heap-reified `Cont` CK-machine.** Do *not* introduce a new continuation mechanism (no stackful fibers, no native-stack copying, no whole-program MTA-CPS, no separate state-machine IR). Concretely:

1. **C stage (now):** rewrite `compileItems` so each **suspending** non-tail bind emits `krt2_bind(action, kclo(kdo_N_kM, cenv))` — a *constructor* of a `krt2_*` action tree — instead of a straight-line `krun_io(action)`. **Non-suspending** binds stay straight-line C, gated by an explicit suspendability analysis (§3.3 — this analysis is a *prerequisite*, not an optimization). The continuation is the existing `kclo(cont_fn, KEnv)`; the captured environment is the de Bruijn `KEnv` we already thread. Retire the `krun_io` bridge for do-kernel code incrementally.
2. **One continuation mechanism for fibers *and* effect handlers — unify** on the `Cont` chain, by adding a single `KK_HANDLER` prompt frame (later capability; frame designed now). Effect `perform` becomes a resumable variant of `unwind`; the captured resumption is the `Cont` sub-chain from the op site to the handler.
3. **Keep one-shot as the default and the fast path**; gate multishot (`rt-multishot`) behind a compile-time escape-check, because only multishot forces the destructively-popped `Cont`/`ExitStack` spine to become persistent/copy-on-resume.
4. **Migration target:** the per-bind `kclo` continuation maps 1:1 onto an LLVM `coro.id.retcon.once` resume function, and the one-shot linear `Cont` frame maps onto Perceus move/reuse. Design the C stage so the continuation function `kdo_N_kM` and the runtime `Cont` protocol are the *seam* LLVM/Perceus slot into — not something they must tear out.

### Where the cost actually is (feasibility re-baseline)

The runtime is **done**. `rt.c` (795 lines) + `internal.h` already implement every `OP_*` (fork/await/sleep/atomically/scopes/mask/while/defer/return/break/continue), deliver/unwind, `KK_DOSCOPE`/`KK_FINSEQ`/`KK_LOOP`/`KK_SETMASK`/`KK_POPMASK`, STM, scopes, promises, the park/wake CAS, and the reactor — all wired into `fiber_step`. `emitMain` already calls `krt2_run_main`. Therefore:

- **~0% of Stage 1–3 risk is in the runtime.** It is concentrated almost entirely in `src/Kappa/Backend/C.hs` `compileItems` (~2741) and its helpers — **the most load-bearing function in the backend.** The honest framing (which `INTEGRATION.md` already uses, REVIEW.md B1) is: *reorganize the most load-bearing backend function while keeping a byte-identical legacy path behind a flag.* This is a real rewrite, not "emit `krt2_bind` per bind."
- **Three runtime correctness fixes are genuinely outstanding** (masked finalizers, finseq abandonment, structured-shutdown scope) and are NOT "already there." They are scoped as required work in §4 and §7.

### Why this and not the alternatives

The decisive constraints are: **effect-typed language**, **future LLVM + Perceus precise RC**, **ZIO-rich cancellation (mask/scope/finalizer) that must survive suspension**, **"as fast as possible"**, and **an existing, tested CK-machine.** (See §8 for the full rejected-alternatives table with reasons.) The one-line argument: every other strategy either *replaces* a validated, GC-transparent spine, or *re-derives* it under a different name. The existing machine is the right answer; the gap is that generated `.kp` code does not yet *reach* it. We close the gap; we do not rebuild the machine.

---

## 2. Should fiber-suspension unify with the algebraic effect handlers? — **Yes, on one `Cont` substrate, with a single new frame.**

The effects map (`Eval.hs` `evalEffPrim`: `Op l op a cont` carrying a re-entrant `cont`; `__handleEff` deep-handlers `reinstall` it) and the runtime map agree structurally: the `Eff` interpreter's free-monad `Op/Pure` tree and the runtime's `krt2_bind`-tree are the **same defunctionalized algebraic-effect term with a reified resumption.** They differ only in that today `Eff` is a pure rewrite with no scheduler handle (so a `handleEff` clause cannot park), and the runtime `Cont` chain has no prompt frame.

**Decision:**

- **Keep the *types* distinct** per spec §18.1.14: `fork`/`await`/STM/`sleep` stay in `IO` (not an `EffRow` effect). `fork` is **not** an `EffRow` operation. This is a typing decision, not a runtime one.
- **Unify the *runtime mechanism*:** model the scheduler as a single, always-installed built-in prompt, and add **one** new continuation frame, `KK_HANDLER`, carrying the installed `(label → handler)` table. Then:
  - `perform op` = an `unwind`-like search outward for the nearest matching `KK_HANDLER` (exactly as `KK_CATCH` is searched for `RK_FAIL`), reifying the `Cont` sub-chain between the op site and the handler as the resumption `k`.
  - `resume k v` = splice that saved sub-chain back onto `f->k` and `deliver` v — O(1), reusing `krt2_bind`/`kclo`, no copy.
  - The scheduler ops (`OP_FORK`/`OP_AWAIT`/`OP_SLEEP`/`OP_ATOMICALLY`) are simply the built-in prompt's operations; they already park/wake by stashing `(cur,k)`.

**Why unify:** because mask, do-scope/defer, and loop frames already live on the same chain a captured delimited continuation rides, an effect resumption **automatically carries the correct finalizer/mask frames** *once the finalizer-masking fix in §4 lands* — without it, the abandonment path inherits the same bugs (see the caveat below). Two continuation worlds would duplicate all of mask/scope/finalizer logic and force an impedance match at every boundary.

**The caveat to get right (now built on a substrate with three known holes — see §4):** dropping an *unresumed* delimited continuation (a handler clause that returns without resuming) must run that captured segment's `KK_DOSCOPE`/`KK_FINSEQ` frames exactly once, in **masked LIFO order** (spec §32.2.20 abandonment rule). The realization is "through the existing `unwind` path" — **but that path does not yet raise mask and silently abandons remaining finalizers on a mid-finseq interrupt.** So the abandonment guarantee is *contingent on the §4 fixes landing first.* Additionally, §32.2.20's escape restriction is a **compile-time** check deferred to the multishot capability; until then there is no enforcement that a resumption with pending exit actions cannot escape, so an escaped one-shot `k` would leave an `ExitStack` dangling on a dropped `Cont` with no run site. This is acceptable **only** because Stage 4 (handlers) lands *after* the §4 fixes are in and tested in Stages 1–3.

**Scope discipline:** ship the built-in scheduler prompt now; full *user-level* multi-prompt handlers (`.kp` code defining its own effects with `resume`) reuse the same `KK_HANDLER` machinery but add marker/evidence management and the escape-check — land that as a later capability (Stage 4), not in the do-kernel rewrite. Note that `__handleEff` is today a **pure** tree rewrite (`kpf___handleEff`, a 5-arg prim) with no scheduler handle; making a handler clause able to park is a cross-cutting change and may force continuation-representation adjustments. We do not claim it "won't be revisited"; we claim the `Cont`/`kclo`/`KEnv` *seam* is the right place for it to attach, and design the frame now so the do-kernel emission shape need not change.

---

## 3. What the backend must emit, and what the runtime must add/change

### 3.1 Backend changes (the cut site)

The cut site is `compileItems` (~C.hs:2741) and its emit helpers `emitRunIOValue` (~3059), `emitRunIODiscard` (~3066), `emitTailIO` (~3087), plus the do-fn assembly in `compileDoBlock` (~2631–2652). Today a do-block is a function `kdo_N(KEnv*)` that *drives* `krun_io`; after the rewrite a **suspending** do-block is a **constructor of a `krt2_*` action tree**, while non-suspending segments remain straight-line.

**Per-item lowering, after the rewrite (suspending segments only):**

| do-kernel item | Today (synchronous) | After (CPS / `krt2_*` node) |
|---|---|---|
| Non-tail bind `x <- m; rest`, **m can suspend** | `KValue *x = krun_io(m); /*rest*/` | `return krt2_bind(m, kclo(kdo_N_kM, cenv));` + emit `kdo_N_kM(KEnv *cenv, KValue *x){ KEnv *e = kpush(x,cenv); /*rest, in CPS*/ }` |
| Non-tail bind, **m provably cannot suspend** | `KValue *x = krun_io(m); /*rest*/` | **unchanged — stays straight-line C** (see §3.3) |
| Non-tail effect / `_ <- m`, suspending | `KValue *io = krun_io(m); (void)io;` | `return krt2_then(m, <rest-as-action>);` |
| Tail action (last `KExpr` in Tail mode) | `return kio_tail(m);` | `return m;` (the do-fn yields the action node directly; tail position, **not** a nested bind — preserves stack-safety, see §4) |
| `defer t` / `using` | register on `gsDefer`/`gsScopeDefers` GC array; flush via `kio_finally`/inline | `krt2_defer(t)` → push onto the enclosing `KK_DOSCOPE`'s `ExitStack` (`OP_DEFER`/`OP_DOSCOPE`) |
| do-scope boundary | C-side ExitStack array + `kio_finally` | wrap body in `OP_DOSCOPE` → `KK_DOSCOPE` frame (runs defers on every exit via `begin_finseq`/`KK_FINSEQ`) |
| `while c { body }` / `for` | `emitScalarLoop` int64 locals where possible; else inline | `OP_WHILE[condIO, bodyIO]` → `KK_LOOP`; **each iteration body is a fresh do-scope**; back-edge re-runs `iterate` via `KK_LOOP`. Keep the scalarized non-suspending loop fast-path **only when the body is suspension-free** (§3.3, §4). |
| `break`/`continue`/`return[L]` | inline defer-flush + C `return`/`goto` | `OP_BREAK`/`OP_CONTINUE`/`OP_RETURN` → `unwind(RK_BREAK/RK_CONTINUE/RK_RETURN)`, running crossed-scope defers |
| `mask`/`uninterruptible`/`poll` | (not reachable from do-block today) | `OP_MASK`/`OP_UNINTERRUPTIBLE`/`OP_POLL` → `KK_SETMASK`/`KK_POPMASK` |
| `fork`/`await`/`sleepFor`/`atomically`/`newPromise`/`cede`/`forkDaemon`/`forkIn`/`newScope`/`shutdownScope` | **not emittable** (missing from `primEntries`) | add `primEntries` mapping each to its `krt2_*` builder so they become `OP_*` nodes the CK-machine parks on |

**Two backend tasks beyond the per-item rewrite:**

- **Add the missing `primEntries`** for `fork`/`forkDaemon`/`await`/`sleepFor`/`cede`/`newPromise`/`completePromise`/`awaitPromiseExit`/`newScope`/`forkIn`/`shutdownScope`/`monitor`/`awaitMonitor`/`atomically` → their `krt2_*` constructors. Today only `ioBind`/`ioThen`/`ioPure`/`throwIO`/`catchIO`/`finallyIO`/`newRef`/`readRef`/`writeRef`/`print*`/`atomically` exist, and `atomically` wrongly lowers to synchronous `krun_io` (`kpf_io_atomically → krun_io`). **This is the *proximate*, independently-shippable gap** and can be wired (and exercised by `runtime/tests/*.c`) before the structural CPS work.
- **Preserve the fast paths — but only where suspension-free.** Keep `readRef`/`writeRef`/`newRef` lowered to direct `kref_*` cell ops, and keep `emitScalarLoop` int64 locals — **subject to the eligibility rule in §3.3 and the ordering barrier in §4.** A bind whose action provably cannot suspend should stay straight-line C. Only `fork`/`await`/`sleep`/`retry`/effect-`perform` boundaries should pay the `kclo`+`Cont` cost.

**Gating:** the rewrite is flag-gated (`--runtime kappart2`); with the flag off, output is byte-identical to today. This is how the conformance suite stays green during the transition (§7). The dual-representation tax this imposes on shared helpers is accounted for in §3.4.

### 3.2 Runtime changes (`runtime/`)

The spine is largely *done*. Required changes are small, additive, **plus the three correctness fixes** the review surfaced:

1. **Retire the `krun_io` bridge for do-kernel code (incrementally).** The `fiber_step` default arm (rt.c ~659–671) matching `K_IO/K_IOTAIL/K_IOEFFECT/K_IOFINALLY/K_BOUNCE/K_NATIVE/K_FAIL` and calling `krun_io(cur)` synchronously disappears for do-blocks once emission stops producing legacy nodes. Keep it only as long as any legacy producers remain (host members, library code not yet rewritten); plan its removal in Stage 3.
2. **`krt2_safepoint` must become real AND be emitted into straight-line/scalar loops** (rt.c:682 is a no-op today). It must check `interrupt_pending && mask_depth==0` and cede/deliver an interrupt. **Critically:** the `fiber_step`-top check (rt.c:488) only fires *between* `OP` nodes; a scalarized straight-line C loop never re-enters `fiber_step`, so it has **no** interruption point. Therefore the backend must *emit* `krt2_safepoint()` calls into the bodies of straight-line/scalarized loops, and the runtime must make it real. Without both, the fast path is uninterruptible (violates spec §32.2.5/§32.2.6). See §4 and §6 for the cost this adds.
3. **Mask finalizers (required fix).** `begin_finseq` (rt.c:377) and the `KK_FINSEQ` arm (rt.c:417) must run the *entire* finalizer drain — including each finalizer body's internal steps — at raised `mask_depth`, restored on both normal completion and the abnormal-finseq abandonment path (rt.c:464). See §4.
4. **Fix finseq abandonment (required fix).** A finalizer that itself fails must compose causes per §18.8.3/§32.2.12, not silently drop sibling defers (rt.c:464). With masking in place this becomes unreachable for *async* interrupts; the failing-finalizer case still needs cause composition. See §4.
5. **Establish a real per-do-block supervision scope OR document that do-blocks do not (decision in §4).** `OP_DOSCOPE` (rt.c:609) currently only allocates an `ExitStack`; it does not create a `Scope` or thread `cur_scope`. See §4.
6. **Fail-closed `OP_DEFER`.** `OP_DEFER` (rt.c:617) silently discards the action when `f->cur_exits == NULL`. Replace the silent skip with a hard assertion/trap so a mis-lowered defer outside any scope is a diagnosed error, not a §18.7 exactly-once violation that fails open.
7. **Add `KK_HANDLER`** + `perform`/`resume` ops (Stage 4 capability; design the frame now).
8. **No new continuation datatype, no stack switching, no marker/evidence vector** for the scheduler prompt. The de Bruijn `KEnv` is the captured environment; `f->k` is the reified continuation.

### 3.3 The suspendability analysis (prerequisite, not optimization)

The entire fast-path argument — and the promise *not to regress* the sequential suite — rests on classifying each bind as **cannot-suspend** (keep straight-line) vs **may-suspend** (CPS-split). This analysis **does not exist in the backend today** and is specified here as a Stage-1 prerequisite. The IO/pure distinction in the types is **insufficient**: a pure ref op and an `await` are both `IO`.

**Source of truth.** Thread the **effect/suspendability witness from the typechecker into `KItem`**. A bind may-suspend iff its action's effect signature can reach a *suspending primitive* (`fork`/`forkDaemon`/`await`/`awaitPromise`/`awaitMonitor`/`sleepFor`/`cede`/`atomically`/`retry`/`shutdownScope`/`perform`) — directly or transitively through a called function. This is the sound source; it must be available at `compileItems`, not reconstructed there.

**Conservative default.** If the witness is unavailable or uncertain for a given action (unknown/recursive user function, higher-order action passed as a value, `perform` whose handler may park, anything behind `--runtime kappart2` indirection that the analysis cannot see through), the bind is treated as **may-suspend** and CPS-split. This is sound (never keeps a suspending bind straight-line) but pays the closure+frame cost. **Soundness invariant:** *every* action reachable to a suspending primitive must be classified may-suspend; the analysis errs toward CPS, never toward straight-line.

**Cost of the conservative fallback.** When the analysis cannot prove cannot-suspend, the bind pays the full `kclo`+`Cont`+`KEnv` cost (§6). For sequential-heavy code dominated by ref ops, arithmetic, and known pure prims, the witness is precise and the fast path holds; for code calling opaque higher-order user functions, expect more CPS-splitting and correspondingly more allocation. We do **not** claim the fast path covers all sequential code — only code whose suspending-reachability the typechecker can witness as empty.

**Whitelist is rejected as the primary mechanism** (a syntactic prim-name whitelist misses user functions that transitively await, and fails *open* — unsound). A whitelist may serve only as a *fast positive* check layered on top of the sound effect witness, never as the sole classifier.

### 3.4 Dual-representation tax (feasibility)

With `--runtime kappart2` **off**, output must stay byte-identical. So `compileItems` cannot be replaced; it must **grow a parallel CPS path** branched at every item kind, sharing the same state monad (`gsDefer`, `gsEnv`, `gsScalars`, `gsParamLvals`, tail-mode) while the new path needs *different* state (continuation-function emission, a worklist of pending `kdo_N_kM` functions, fresh `KEnv` threading per continuation). The following helpers are shared between legacy and CPS paths and **each must branch on `gsRuntime` or be duplicated** — decided per helper, enumerated so the cost is visible up front rather than discovered mid-stage:

| Helper / construct | Legacy behavior | CPS behavior | Branch or duplicate |
|---|---|---|---|
| `emitPropagateFailure` | emits `if (kis_fail) return v` | `unwind(RK_FAIL)` | branch |
| `registerDefer` | writes a C-local ExitStack array | `OP_DEFER` onto `KK_DOSCOPE` | branch |
| `flushFramesInline` | inline defer flush | `begin_finseq` via `KK_DOSCOPE` exit | duplicate (shapes diverge) |
| `emitTailIO` / `emitTailReturn` | `return kio_tail(m)` / C return | `return m` (tail node) / `OP_RETURN` | branch |
| `gotoLoop` / `compileLoop` / `withLoop` | C goto-loop + `gsScalars` | `OP_WHILE` + per-iteration doscope | duplicate |
| `emitRunIOValue` / `emitRunIODiscard` | `krun_io` | `krt2_bind` / `krt2_then` or straight-line (per §3.3) | branch |
| do-fn assembly (`compileDoBlock`) | single `kdo_N(KEnv*)` body | family of `kdo_N_kM` siblings via `drainQueue` worklist (C.hs:442) | duplicate emission shape |

Count from the review: ~29 call sites of the four legacy emit helpers, ~86 control-flow references (`goto`/`emitTailReturn`/`gotoLoop`/`withLoop`/`flushFramesInline`/`compileLoop`/`gsScalars`/`gsParamLvals`) in the 2741–3460 region. This dual-path coexistence persists through Stages 1–4 and is deleted only at Stage 5. The CPS emission shape (stop emitting into the current function, `return krt2_bind(...)`, queue a new top-level `kdo_N_kM`) is feasible because `drainQueue` already provides the worklist — but it is a *different shape* from the current single-body `captured`-block model, so every helper that assumes "I am appending statements to the current function" must branch.

---

## 4. The subtleties (and how each is handled)

**Tail-call stack-safety.** Two trampolines coexist: the value-level `ktrampoline`/`K_BOUNCE` drain and the action-level CK loop. The tail action of a do-block must emit in **tail position** (the do-fn *returns the action node*), not as a nested `krt2_bind` — otherwise an accept-loop or `do { …; loop n }` grows the heap continuation unboundedly. `fiber_step` is a flat loop, never recursion; a suspending op *returns* leaving `f->cur` set to what re-runs. Finalizers already run *through* the CK-machine (not C recursion), so unwinding N nested scopes is constant native stack.

*Subtle interaction (per-iteration do-scope under a loop):* a do-scope tail action is **not** in true tail position — the `KK_DOSCOPE` frame must still run defers after it (deliver → `KK_DOSCOPE` → `begin_finseq`). This stays constant native stack (it goes through the CK loop). The real risk is loop growth: with "each iteration body is a fresh do-scope," the `OP_WHILE` re-run (rt.c:629) must ensure the per-iteration `KK_DOSCOPE` is **fully unwound (defers run, frame popped)** before `KK_LOOP` re-iterates — else `f->k` grows by one `KK_DOSCOPE` per iteration. The current `KK_LOOP` re-run (rt.c:408/456) keeps `KK_LOOP` and re-runs `iterate`; nothing in the code *proves* the inner per-iteration `KK_DOSCOPE` is popped on the normal path. **Required test (Stage 1/2):** an accept-loop with a per-iteration defer must show `f->k` depth constant across iterations.

**De Bruijn `KEnv` capture across suspension.** The continuation environment is *the current `KEnv`* — it already holds exactly the live locals, captured by reference (so a deferred action re-reads mutated cells at flush time, spec §18.8). Each `kdo_N_kM` does `kpush(boundValue, cenv)`, so captured variables keep **identical de Bruijn indices** and reads resolve the same cells before and after a park. **This "free liveness" holds ONLY for values that live in the `KEnv`.** It is **false** for two optimizations the prior draft promised to keep (see "Scalarized loops" below).

**Scalarized loops / flat-worker locals vs suspension (required decision).** `emitScalarLoop` lowers a var+while group to **int64 C locals** (`gsScalars`: de Bruijn index → (local, ref)) living on the C stack of `kdo_N`; `gsParamLvals` holds flat-worker pattern bindings as C locals read by index, **not via `KEnv`.** The moment any bind inside such a loop body can suspend — including the `cede`/safepoint the fairness mandate itself requires on every back-edge — those C-stack locals are **lost across the park** (not in `KEnv`, not in `f->k`). The "free liveness via `KEnv`" enabler is *false* for exactly these two fast paths. **Decision (eligibility rule):** *a do-scope that uses scalarized loops or flat-worker locals is **ineligible for suspension points** in the affected region.* The suspendability analysis (§3.3) decides eligibility: if the loop body is provably suspension-free, it stays scalarized straight-line C (and must still carry an emitted `krt2_safepoint()` for fairness — see below); if it may suspend, it must be lowered to the `OP_WHILE`/`KK_LOOP` form with all live values materialized in `KEnv` (de-scalarization). The eligibility check is sound because §3.3 errs toward may-suspend. We do **not** promise to keep scalarization *and* suspend through it — we pick: scalarize iff suspension-free.

**Safepoint in straight-line loops (required fix, with cost).** Because the interrupt check lives only at the `fiber_step` top, a suspension-free scalar loop has no interruption point. The backend must **emit `krt2_safepoint()`** into straight-line/scalar loop bodies and the runtime must make it real (interrupt check + cede). This costs an acquire-load per iteration (and, if it cedes, a re-entry into the scheduler). The scalar fast path therefore survives only when: body is suspension-free **and** has no defers **and** fairness is handled by the emitted safepoint. This narrows the fast path more than a naive reading of §6 suggests; §6 accounts for it.

**Masking / scope / finalizer frames on the reified continuation.**

> **CORRECTION (was stated as a property; is a required fix).** `KK_SETMASK`/`KK_POPMASK` correctly restore `mask_depth` on both deliver and unwind, so a suspend-while-masked resumes still masked — that part is true and `mask_depth` is part of the saved suspension state on `f`. **But finalizers do NOT currently run masked**, and an interrupt mid-finseq drops the scope's remaining defers. Specifically:
>
> - `begin_finseq` (rt.c:377) and the `KK_FINSEQ` arm (rt.c:417) **never raise `f->mask_depth`.** Finalizers execute by setting `f->cur = krt2_pure(...)` (the "kick", rt.c:384) and looping back through `fiber_step`, whose top (rt.c:488) delivers a pending interrupt whenever `interrupt_pending && mask_depth==0`. So while a do-scope's defers are unwinding (after `RK_RETURN`/`RK_FAIL`), an async interrupt is delivered **mid-finalizer**: `deliver_interrupt → unwind(RK_INTERRUPT)`, which from inside `KK_FINSEQ` hits the abandonment case (rt.c:464) and **silently drops the scope's remaining defers** — violating §18.7 ("exactly once on every exit path"), §18.8.3 primary-error precedence, and §32.2.5 ("finalizers run in masked state").
> - The check is at the `fiber_step` top, so **every** intermediate node of a finalizer body is an interruption point — even on a *normal*-exit do-scope whose finalizer does real work.
>
> **Required fix.** Raise `mask_depth` for the **full duration of every finalizer drain** — covering each finalizer body's internal steps *and* the whole `KK_FINSEQ` sequence — by pushing a `KK_POPMASK` under the `KK_FINSEQ` (or carrying a masked flag in `FinSeq`), and restore it on **both** normal completion and the abnormal-finseq path (rt.c:464). With masking installed, async interrupts cannot land mid-finseq, so the abandonment case becomes unreachable for interrupts. The **failing-finalizer** case (a defer that itself throws mid-unwind) must then **compose causes** per §18.8.3/§32.2.12 (`Then`), not drop sibling defers.
> **Required tests:** (a) an interrupt delivered while a multi-defer do-scope unwinds runs **all** remaining defers in LIFO order; (b) primary-error precedence holds when a defer fails mid-unwind.

Once fixed: `KK_DOSCOPE`/`KK_FINSEQ` run defers LIFO on every exit (normal/return/break/continue/fail/interrupt) via `begin_finseq`, *through* the CK-machine — so a finalizer that itself blocks suspends the whole unwind correctly, and a child interrupt firing while parked runs the pending defers in masked LIFO order with primary-error precedence preserved.

**Structured-shutdown ordering (required decision + implementation).**

> **CORRECTION (was "already exists"; it does not).** "Drain attached children and their finalizers before the parent scope's own defers" is **not implemented.** `OP_DOSCOPE` (rt.c:609) only allocates an `ExitStack` and pushes a `KK_DOSCOPE` frame; it does **not** create a supervision `Scope` and does **not** update `f->cur_scope`. `KK_DOSCOPE` on exit (rt.c:411/458) calls `begin_finseq` only — no child drain. `krt2i_spawn` attaches children to the inherited `f->cur_scope` (rt.c:292/521), which for a do-block is still the **parent/root** scope (set once at rt.c:758, changed only by an explicit `newScope`). So a do-block that `fork`/`forkIn`s and then exits runs its own defers **without first draining its forked children** — children outlive the lexical scope, contradicting §32.2.3 and the prior draft's own ordering claim.
>
> **Decision (pick one, pin it with a Stage-2/3 test):**
> - **(a) Structured do-blocks:** `OP_DOSCOPE` establishes a real supervision `Scope`, threads `f->cur_scope`, and injects a **child-drain + finalize step ahead of the defer `KK_FINSEQ`** (children terminate and run their finalizers before the enclosing scope's releases, §32.2.3). This is substantial new runtime work — *not* "already exists."
> - **(b) Non-structured do-blocks:** do-blocks do **not** create supervision scopes; forks escape to the enclosing explicit scope. Simpler, but then structured concurrency requires an explicit `newScope` and the docs/tests must say so.
>
> **This design recommends (a)** to match ZIO-style structured concurrency and the spec, and budgets it as real Stage-3 runtime work (see §7). Whichever is chosen, a conformance test must pin it.

**STM-retry / await parking.** `await`/`awaitPromise`/`awaitMonitor`/`shutdownScope` follow check-park-under-lock / wake-under-lock; the parked fiber's entire state is `cur + k + mask_depth + cur_exits` on the GC heap, kept live via `rt->all`. STM `retry` leaves `f->cur` as the `OP_ATOMICALLY` node so the whole transaction **re-runs** on wake (re-validate read-set, re-link TVar watchers, `stm_unpark` unlinks stale ones). The idempotent `F_PARKED→F_RUNNABLE` CAS in `krt2i_wake` guards lost-wakeup/double-enqueue — any new suspension point (including effect-handler park) **must** set `F_PARKED` under the waitable object's lock the waker holds, or it races the wake.

**Source-order sequencing of Ref/var effects across suspension (required fix).** Spec §18.1.13 requires ref/var effects to observe source order on a single fiber. **The prior draft asserted this obligation with no mechanism.** `readRef`/`writeRef` are kept as direct `kref_*` cell ops in straight-line C (§3.1 fast path), the `Ref` cells are plain heap (not atomic/volatile), and the C compiler is free to reorder a non-`volatile` `kref_get` across the construction of a `kclo` (a pure struct-returning call). On the suspending path, values are sequenced by data dependency through `KEnv` — **but a discarded read (`_ <- readRef r`) before a suspending bind has no such dependency** and can be reordered past the park. **Required fix — pick the mechanism per call site:**
- **Route ref ops that *precede a suspension point* through the CK-machine** (emit them as `OP_*`/`krt2_then` nodes so the CK loop sequences them), accepting they leave the straight-line fast path; **or**
- **Insert an explicit compiler sequencing barrier** (e.g. `atomic_signal_fence(memory_order_seq_cst)` / a `volatile` access / a compiler barrier) between a straight-line ref op and the following `kclo` construction.

This directly tensions the "refs stay straight-line" rule: a ref op that is the *last* thing before a suspending bind cannot be both fully straight-line *and* guaranteed source-ordered without a barrier. The rule is therefore: ref ops stay straight-line **except** when immediately preceding a suspension boundary, where they take a barrier (or route through the CK-machine). Stage 1 must enforce this; a test must exercise a discarded `readRef` before an `await`.

**One-shot vs multishot.** One-shot is the default and fast path: `f->k` is a uniquely-owned mutable spine; deliver/unwind destructively pop frames; `krt2i_wake` resumes at most once. This makes RC a *move* (no atomic traffic) and matches `coro.id.retcon.once`. Multishot (`rt-multishot`) requires (a) the spine + `ExitStack`s to become persistent/copy-on-resume rather than destructively popped, and (b) each logical clone to carry its own independent pending-defer set. It is a *semantic change* to deliver/unwind, not a flag — gated behind a **compile-time escape-check** (a resumption with pending exit actions must not escape its clause; reject at compile time). `KRT2_CAPABILITIES` today lists `rt-core`/`rt-parallel`/`rt-shared-stm`/`rt-blocking`/`rt-atomics` — **`rt-multishot` does not yet exist** and must be added with the escape-check before any multishot lands. The `Eval.hs` interpreter already models the multishot semantics the runtime must converge to.

---

## 5. Migration path to LLVM coroutines + Perceus RC

**Design rule for the C stage:** treat the per-bind continuation function `kdo_N_kM(KEnv*, KValue*)` and the runtime `Cont` protocol (deliver/unwind over `KK_*` frames) as the **stable seam.** LLVM and Perceus slot into that seam; they do not require tearing it out.

**LLVM coroutine lowering.** Each `kdo_N`/`kdo_N_kM` becomes an LLVM coroutine. `CoroSplit` recomputes the cross-suspend live set — *seed it with the `KEnv` capture set* — and replaces the hand-emitted `kpush` chain with a flat spilled frame (faster `kvar`, no linked-list walk). Choose the **`coro.id.retcon.once`** ABI (returned-continuation, one-shot): each suspension yields a distinct continuation function pointer the resume site *tail-calls*, so `krt2i_wake` becomes a tail-call rather than a switch re-dispatch. `coro.suspend` sits at each `krt2_bind`/`await`/`sleep`/`retry`; the (park / resume-with-value / destroy-and-run-finalizers) switch maps to the three deliver/unwind outcomes; `coro.end`'s unwind form is the natural home for "run defers on every exit including interrupt." **Keep the mask/scope/loop `Cont` frames as an explicit runtime-owned list *alongside* the coroutine frame** — they encode runtime *policy* (interruptibility, finalizer scopes) that deliver/unwind must inspect; they are not merely locals live across a suspend, and the coro frame replaces only the `KEnv` spill. Multishot bypasses `coro.*` (coroutines are one-shot) and uses explicit spine copy in the runtime.

> **CORRECTION to the `CoroElide` claim.** The prior draft said `CoroElide` "recovers today's straight-line speed without giving up suspendability." **`CoroElide` fires only when LLVM proves the coroutine does not escape and is destroyed in the caller.** A fiber frame handed to the run queue and **resumed on another worker DOES escape** — so elision will **not** fire for the `fork`/`await`-bearing blocks that actually suspend. `CoroElide` therefore helps only blocks that were *already* kept straight-line by §3.3 (non-suspending sub-do blocks) — it does not "recover speed" on the suspending path; it removes a frame only where there was no real suspension to begin with. Net honest statement: LLVM removes overhead where there was little (non-suspending blocks elide to straight-line) and **leaves the per-suspend frame cost where it hurts** (genuinely suspending blocks).

**Perceus precise RC.** The one-shot linear `Cont`/`KEnv`/`kclo` is a good Perceus citizen *because the do-kernel is already CPS* (explicit control flow = explicit `dup`/`drop` sites): a `KK_BIND` `drop`s its continuation after `kapp`; a branch join that shares a tail continuation `dup`s per arm. **Reuse analysis (FBIP)** turns the per-bind `KEnv`/`Cont` allocation into an in-place write **on a tight, linear, non-escaping loop.** A fiber's own `f->k` is thread-local (one worker steps it at a time) → **non-atomic RC**; only values crossing fork/promise/TVar boundaries need atomic RC (Perceus borrow inference + thread-shared analysis gives exactly this split). Continuation spines are acyclic by construction, so the Perceus cycle caveat does not bite the continuation machinery.

> **Honest bound on "trends to zero."** Perceus reuse drives per-bind alloc toward zero **only for linear, non-escaping binds** — straight-line linear loops, i.e. again the blocks that never needed CPS. Multishot, **shared continuations at branch joins**, and **any value captured across `fork`** break linearity, so reuse does *not* fire there. The interaction to get right: `KK_DOSCOPE`/`KK_FINSEQ` finalizers holding the last reference to a resource must run **before** RC drops it — RC drop order must not preempt explicit defer/finalizer semantics. Multishot is the one place RC gets harder (a resumption escapes, must be `dup`'d) — another reason it stays gated.

**Net (corrected):** the C-stage representation (heap `Cont` frames + `kclo`/`KEnv`, one-shot default) is what `coro.id.retcon.once` and Perceus move/reuse were built for, and the seam is correct. The future path **removes overhead on the non-suspending/linear path** (elide + reuse) and **retains a real per-suspend frame cost on the genuinely suspending path** — it does not make suspension free. No corner; but no magic either.

---

## 6. Performance posture (corrected, with honest accounting)

**The fast (no-suspend) path is the thing to protect — and it is contingent on §3.3.** Naive whole-block CPS pays `kclo` + `Cont` cell + `KEnv` cons + indirect `kapp` *per bind*. The mitigation is **mandatory and is the sound suspendability analysis of §3.3, not a vague "only split what suspends."** With it, the no-suspend path stays straight-line C; without it, Stage 1 would make sequential code **slower than the current `krun_io` bridge** and worse than Go/Rust. This is the single most important performance decision; it is now a *prerequisite with a specified algorithm and conservative default* (§3.3), not an aspiration.

**Suspending-bind allocation — corrected accounting.** The prior draft's "1 small frame / tens of bytes" is **wrong by ~4–5×.** A single `krt2_bind(m, kclo(kdo_N_kM, cenv))` on the suspending path costs, verified against `rt.c`/`kappart.c`:

1. the `OP_BIND` node: one `KValue` box **plus** a 2-element `KValue*` args array (`kappart.c:259–265`);
2. the `kclo` box (`kappart.c:306`);
3. a `KEnv` cons via `kpush` for the captured value;
4. the `KK_BIND` `Cont` via `cont_new` at step time (rt.c:230);
5. `kapp(c->a, v)` in `deliver` (rt.c:397), which can allocate again.

That is **4–5 `GC_MALLOC`s** (Boehm) and as many cache-cold loads per suspending bind — **not** "tens of bytes." For comparison: Go parks a goroutine with **zero** heap alloc on the common path; Rust `async` monomorphizes the whole future into one flat struct with **no per-`await` alloc.** So on the suspending path, pre-LLVM, the runtime is **not** in Go/Rust allocation class; the gap is roughly 4–5 allocations + linked-list/`Cont` walks per suspend.

**KValue boxing is NOT orthogonal — it compounds with CPS.** Every value threaded through a continuation — the bound result `v` in `kapp(c->a,v)`, every captured local in the `KEnv`, every loop counter crossing a safepoint — is a ~40-byte boxed `KValue` (`kappart.h:92–125`; `kint` outside `[-16,256]` even allocates). The CPS rewrite **increases** the set of values that must be materialized as first-class boxed `KValue`s, because anything live across a suspend point must be a real `KValue` in the `KEnv` — defeating future unboxing/scalar-in-register opts *at exactly the suspension boundaries*. **Honest statement:** pre-LLVM, with `KValue` boxing in force, the runtime is not in Go/Rust allocation class on the suspending path, and the continuation representation pins values boxed across binds. Unboxing/specialization is a separate, larger effort; we bound the gap rather than dismiss it.

**Cache behavior.** `kvar(env, ix)` walks a singly-linked `KEnv` (`kappart.h:132–135`): O(index) cache-missing loads per variable read vs a constant-offset stack/register load in Go/Rust. The `Cont` chain is likewise a heap linked list walked on every deliver/unwind, with no locality guarantee (each `cont_new`/`kpush` is a fresh `GC_MALLOC`). LLVM `CoroSplit` flattens the `KEnv` spill into a contiguous frame — **but that is Stage 5; the conformance suite ships on the C backend for Stages 1–4**, during which the hot path eats linked-list latency.

**Allocator reality (Stages 1–4 run on Boehm).** `kgc_alloc = GC_MALLOC` (`kappart.c:45`). Boehm with thread-local freelists handles the small-object fast path lock-free, but (a) freelist refill and large objects take the global allocator lock — real contention under the M:N scheduler with many workers each CPS-stepping fibers; (b) conservative mark scans the heap including all `Cont`/`KEnv` pointers — mark cost scales with the live continuation graph, which CPS enlarges; (c) Go uses a precise low-pause collector, Rust uses none. The Perceus fix is Stage 5. **Plain statement: "as fast as Go/Rust" is FALSE for Stages 1–4; the doc says so rather than implying otherwise.** The strategy is *designed to become* Go/Rust-class at Stage 5 (Perceus + LLVM coro on the non-suspending/linear path); pre-Stage-5 it is a correct, GC-transparent, cancellation-correct CK-machine that is *not yet* in that allocation class.

**Safepoint cost (accounted).** Making `krt2_safepoint` real adds, on a scalar loop forced through `OP_WHILE`/`KK_LOOP`: an acquire-load of `interrupt_pending` per iteration, a `kctor` re-dispatch per iteration (`f->cur = iterate`, rt.c:409), and a fresh do-scope per iteration if the body has any defer. Go/Rust loops pay none of this. The "keep `emitScalarLoop` straight-line" escape hatch survives **only** when the body provably cannot suspend **and** has no defers **and** fairness is handled by an emitted `krt2_safepoint()` (an acquire-load per iteration even there). The fast path is thus narrower than a naive reading suggests; this is the cost of interruptibility.

**Two trampolines.** The value-level `ktrampoline`/`K_BOUNCE` drain and the action-level CK loop coexist; every `kapp` drains tail bounces (`kappart.h:172`). This is an extra indirect-dispatch layer on every step that native-stack competitors lack. The tail-action-returned-not-nested invariant (§4) is what prevents unbounded `f->k` growth in accept-loops and is pinned by test, not just convention.

**Mandatory measured baseline (now a Stage-1 gate, not Stage 5).** No "competitive with Go/Rust" or "same class as a goroutine park" claim ships without measurement. Add, **as non-regression gates from Stage 1**:
- alloc-count and cycles for **(a)** a non-suspending straight-line bind, **(b)** a suspending `await`, **(c)** a tight scalar loop forced through `OP_WHILE` with a real safepoint,
- versus a **Go goroutine ping-pong** and a **Rust `async` equivalent**,
- plus an interrupt-latency benchmark.

The expected result, stated honestly up front: (a) competitive with Go/Rust straight-line; (b) ~4–5 allocs + park/CAS/run-queue-push, *not* zero-alloc — same *latency class* as a goroutine park (O(1) capture + CAS + enqueue, no stack copy) but *not* the same *allocation* class until Perceus; (c) per-iteration acquire-load + re-dispatch overhead vs a bare native loop. The gates exist to catch regression against these numbers, not to assert parity that does not yet hold.

**Residual gap.** Beyond the suspend-path allocations, the remaining gap to Rust-class numbers is **value boxing** (the `KValue` model) — larger than, and only partly orthogonal to, the continuation strategy (it compounds at suspension boundaries, as above). Unboxing/specialization is the bigger lever there and is a separate milestone.

---

## 7. Staged implementation plan (re-ordered for minimal-risk first capability)

Each stage is independently shippable, flag-gated, and keeps the native conformance suite green. **Invariant for every stage:** with `--runtime kappart2` off, codegen is byte-identical to today and the suite passes unchanged; with the flag on, the suite must also pass — that is the gate to advance.

> **Re-ordering rationale.** The prior draft's Stage 1 ("entire sequential suite through CPS") was the **maximal-risk** ordering and delivered **zero** new user capability (sequential programs already run via the `krun_io` bridge). It front-loaded the hardest semantic-preservation work (finalizer ordering through `KK_DOSCOPE`/`KK_FINSEQ`, completion-channel) with nothing to show. We **invert it:** ship real `fork`/`await` suspension from `.kp` first on a *minimal* CPS slice, leaving defer/return/break/loop on the legacy bridge until later.

**Stage 0 — Harness, baseline, and the three correctness fixes.**
Wire `--runtime kappart2` through `compileItems` as a no-op branch (still legacy nodes). Add a CI lane running the full native conformance suite under the flag. **Land the three runtime correctness fixes** even before CPS emission, since they are bugs in the existing machine: (1) mask finalizers in `begin_finseq`; (2) fix finseq abandonment / cause composition (rt.c:464); (3) make `OP_DEFER` fail closed (rt.c:617). Make `krt2_safepoint` real. **Add the measured baseline harness** (alloc-count + cycles for non-suspending bind, suspending await, scalar loop; Go/Rust ping-pong; interrupt latency) and wire it as a non-regression gate.
*Tests:* whole suite green both flag states; interrupt-while-multi-defer-unwinding runs all defers LIFO; failing-defer composes causes; defer-outside-scope traps; tight-loop interruptible (run specifically against a **scalarized int64 loop**, not a CK-level `OP_WHILE`); baseline numbers recorded.

**Stage 1 — Minimal real concurrency from `.kp` (fork/await only).**
Add the missing concurrency `primEntries` (`fork`/`forkDaemon`/`await`/`sleepFor`/`cede`/`newPromise`/`completePromise`/`awaitPromiseExit`; real `krt2_atomically` replacing the synchronous `kpf_io_atomically → krun_io`). Implement the suspendability analysis (§3.3) threaded from the typechecker into `KItem`. CPS-split **only** at a recognized leading suspending bind; keep the existing legacy straight-line lowering for everything else (defer/return/break/while stay on the bridge). Enforce the §4 ref-ordering barrier at any straight-line ref op immediately preceding a suspension boundary.
*Target program:* `do { f <- fork child; r <- await f; printlnString (show r) }` under `KAPPA_RT_WORKERS=1`, matching interpreter stdout. **No completion-channel rewrite, no defer/return/break/loop re-expression.**
*Tests:* fork+await ordering (happens-before); `sleepFor` parks and the reactor wakes it; two fibers interleave via `cede`; discarded `readRef` before an `await` observes source order; baseline gates from Stage 0 hold (no sequential regression because non-suspending binds stay straight-line per §3.3).

**Stage 2 — Defer/scope/loop in CPS + STM parking.**
Now re-express `defer`/`using`/do-scope as `OP_DOSCOPE`/`OP_DEFER`/`KK_DOSCOPE`; `break`/`continue`/`return`/`while` as `OP_*`/`unwind`; `atomically`+`retry` parking. This is where the dual-representation tax (§3.4) and the per-iteration-do-scope loop-growth invariant (§4) are paid and tested.
*Tests:* the sequential conformance subset touching defer LIFO / primary-error / mask / return / break / sub-do passes under the flag (golden tests assert `krt2_bind` nodes, diff exit codes/stdout vs legacy lane per file); `atomically`+`retry` parks until a TVar write; an interrupt at an `await` runs the scope's defers in **masked** LIFO order (relies on Stage-0 fix); accept-loop with per-iteration defer shows constant `f->k` depth; 10⁴+ fibers parked on promises stay GC-live via `rt->all`.

**Stage 3 — Structured scopes, masking, structured shutdown end-to-end.**
Add `primEntries` for `newScope`/`forkIn`/`shutdownScope`/`monitor`/`awaitMonitor` and `mask`/`uninterruptible`/`poll`. **Implement the structured-shutdown decision from §4** (recommended option (a): `OP_DOSCOPE` establishes a supervision `Scope`, threads `cur_scope`, drains+finalizes children before its own defers). Retire the `krun_io` bridge for do-kernel nodes (keep only for remaining legacy producers; assert do-kernel code never takes the bridge arm).
*Tests:* spec §32.2 mirrors — child-drain-before-parent-defer ordering; cancellation completes target before canceller proceeds; race/timeout loser-cleanup waits; `acquireRelease` across suspension; mask survives park; finalizer-suspends-the-unwind. A test pins whichever structured-shutdown semantics §4 chose.

**Stage 4 — Effect-handler unification (later capability).**
Add `KK_HANDLER` + `perform`/`resume`; lower `Eff` handlers onto the same `Cont` chain. Default one-shot/tail-resumptive fast path first; `rt-multishot` (new capability, with the compile-time escape-check) behind the flag. **Depends on the §4 finalizer-masking fix being in** (the abandonment path reuses `KK_FINSEQ`).
*Tests:* `Interp.hs`/`Eval.hs` reference semantics stay observably equal to the runtime (differential-testing harness); abandonment test — a clause that returns without resuming runs the captured segment's defers exactly once, masked; multishot tests gated behind the capability.

**Stage 5 — LLVM + Perceus migration (separate milestone).**
Retarget `kdo_N_kM` emission to LLVM `coro.*` (`retcon.once`), seed `CoroSplit` liveness from `KEnv`, enable `CoroElide` for non-suspending blocks **(only — per §5, escaping fiber frames do not elide)**. Introduce Perceus `dup`/`drop`/reuse on `Cont`/`KEnv`, non-atomic for thread-local `f->k`. The C stage remains the fallback backend.
*Tests:* the same conformance suite, now on the LLVM backend, matches the C-backend lane bit-for-bit on observable behavior; alloc-count and interrupt-latency benchmarks tighten as non-regression gates and must now show the non-suspending/linear path trending to Go/Rust-class.

---

## 8. Rejected alternatives (and why)

| Strategy | Verdict | Reason |
|---|---|---|
| **Defunctionalized heap-reified CPS (existing CK-machine) + do-kernel rewrite** | **CHOSEN** | It *is* the runtime. `krt2_bind`/`kclo`/`KEnv`/deliver/unwind already exist and pass the v1 suspension tests. Mask/scope/loop frames already ride the same chain (modulo the three §4 fixes). Maps cleanly to `coro.*` + Perceus. The only structural work is the (real, bounded) `compileItems` rewrite plus three runtime correctness fixes. |
| **Delimited continuations + algebraic effect handlers** (as a separate engine) | **Rejected as a separate engine; adopted as semantics** | This is the same machine described from the effects side: a one-prompt delimited-continuation engine. We take its unification insight (scheduler = built-in prompt; handlers = additional prompt frames) and realize it as `KK_HANDLER` on the existing chain. A second engine would duplicate mask/scope/finalizer logic and need an impedance match at every boundary. |
| **Classic CPS as front-end IR (naive whole-block)** | **Rejected wholesale; borrow the discipline** | Whole-block CPS over-CPSes (admin closures on non-suspending binds) — §6 shows this is *worse than the legacy bridge* and worse than Go/Rust, regressing the sequential suite. We adopt Kennedy's *second-class* `letcont` discipline for join points/loops/returns (maps to LLVM basic-block args later) but keep non-suspending segments straight-line via the §3.3 analysis. |
| **Stackless state-machine (hand-rolled `switch(state)` in the C stage now)** | **Rejected now; it IS the LLVM lowering later** | A per-do-block state machine is exactly what LLVM `CoroSplit` builds. Hand-rolling it now means a *second* continuation representation to interop with the `Cont` machine. Defer to the LLVM backend (Stage 5) where `coro.*` generates it with elision. |
| **Multi-return (λ_MR)** | **Rejected as a basis; descriptive only** | deliver/unwind *is* a fixed-schema multi-return. Validates the design; adds no suspension mechanism (the actual hard problem). Cited, not built on. |
| **Stackful fibers / native stacks (as the spine)** | **Rejected** | Fatal against Perceus: live pointers sit in native frames at compiler-chosen offsets; precise/moving RC cannot see or relocate them without per-frame stackmaps, and conservative scanning of thousands of suspended stacks pins everything. ~2–4 KiB/fiber slack vs tens–hundreds of bytes for the heap `Cont`. Re-introduces the worker-blocking native stack we are removing. *Narrow legitimate use:* a blocking-FFI lane (run a genuinely blocking C call on a dedicated OS thread, park the CK-fiber) — additive, not the spine. |
| **Stack-copying (Loom-style) / Cheney-on-the-MTA** | **Rejected (the copying)** | Loom-style native-frame copying and MTA's mandatory copying collector both fight Perceus (frame maps / forced copying). |
| **WasmFX typed continuations as a codegen target** | **Rejected as a target; adopted as semantics** | WasmFX *semantics* (typed delimited continuation = effect-handler primitive, one-shot default, opt-in multishot) are exactly right and already match the `Cont` chain + `rt-multishot` staging — but as semantics to mirror, not a Wasm codegen target. |
| **Per-bind whitelist of suspending prim names (as the suspendability classifier)** | **Rejected as primary** | A syntactic whitelist misses user functions that transitively await/perform and fails *open* (unsound). Replaced by the effect-witness analysis of §3.3; a whitelist may serve only as a layered fast-positive, never the sole classifier. |
| **Two continuation worlds (bespoke concurrency runtime beside the effect system)** | **Rejected** | Duplicates mask/scope/finalizer logic and forces an impedance match at every fiber↔handler boundary. One `Cont` substrate gives ZIO-style structured concurrency and algebraic effects from the same deliver/unwind machinery. |

---

## 9. Risks & mitigations

| # | Risk | Severity | Mitigation |
|---|---|---|---|
| R1 | **Finalizers not masked → interrupt mid-finseq silently drops remaining defers** (rt.c:377/464); breaks §18.7 exactly-once, §18.8.3 precedence, §32.2.5. | Critical (correctness) | **Stage-0 required fix:** raise `mask_depth` for the full finseq drain (push `KK_POPMASK` under `KK_FINSEQ` / `FinSeq` masked flag), restore on normal *and* abnormal (rt.c:464) paths. Tests: interrupt-while-unwinding runs all defers LIFO; failing-defer composes causes. **Blocks Stage 2 and Stage 4.** |
| R2 | **Suspendability analysis does not exist**; without it Stage 1 CPS-splits everything and regresses the sequential suite (worse than the `krun_io` bridge and Go/Rust). | Critical (perf + feasibility) | §3.3: thread the effect/suspending-reachability witness from the typechecker into `KItem`; conservative default = may-suspend (sound); whitelist only as layered fast-positive. **Prerequisite to Stage 1**, with the measured baseline (Stage 0) as the regression gate. |
| R3 | **Per-do-block structured-shutdown not implemented** (`OP_DOSCOPE` only allocs an ExitStack; `cur_scope` not threaded); forked children outlive the lexical scope (§32.2.3). | High (correctness) | §4 decision: implement option (a) — `OP_DOSCOPE` establishes a supervision `Scope`, threads `cur_scope`, drains+finalizes children before its own defers — as real **Stage-3** runtime work; pin with a test. (Option (b) documented as the fallback.) |
| R4 | **Suspending-bind cost undercounted ~4–5×; "as fast as Go/Rust" false for Stages 1–4** (Boehm GC, KValue boxing, linked-list KEnv/Cont). | High (perf, expectations) | §6 corrected accounting (4–5 `GC_MALLOC`s/suspend), explicit honesty statement that Stages 1–4 are *not* Go/Rust allocation-class, measured baseline gates from Stage 0, and a stated path to parity (Perceus + LLVM coro, Stage 5) **only on the non-suspending/linear path**. |
| R5 | **Scalarized/flat-worker locals live on the C stack, lost across a park**; "free KEnv liveness" is false for them. | High (correctness + perf) | §4 eligibility rule: scalarize iff the region is provably suspension-free (decided by R2's analysis); otherwise de-scalarize and materialize live values in `KEnv`. The eligibility check is sound because R2 errs toward may-suspend. |
| R6 | **Straight-line/scalar loops have no interruption point** (`fiber_step`-top check only fires between OP nodes); `krt2_safepoint` is a no-op (rt.c:682). | Medium (correctness) | §3.2/§4: make `krt2_safepoint` real **and emit it into** straight-line/scalar loop bodies; test against a *scalarized int64 loop*, not a CK-level `OP_WHILE`. Cost accounted in §6. |
| R7 | **Ref/var reads reorderable across a `kclo` boundary** (plain heap cells, C compiler free to reorder); discarded `_ <- readRef r` before a suspend has no data dependency (§18.1.13). | Medium (correctness) | §4: ref ops immediately preceding a suspension boundary take a compiler sequencing barrier *or* route through the CK-machine; the "refs stay straight-line" rule is amended accordingly. Test: discarded `readRef` before an `await`. |
| R8 | **`compileItems` dual-representation tax**: legacy + CPS paths coexist in shared helpers behind a flag for Stages 1–4 (~29 emit-helper call sites, ~86 control-flow refs). | High (feasibility / effort) | §3.4 enumerates each shared helper with a branch-vs-duplicate decision up front; the effort is re-baselined (§1) as "reorganize the most load-bearing backend function," matching `INTEGRATION.md`/REVIEW.md B1 — not a one-liner. |
| R9 | **Stage ordering front-loaded the hardest work with zero new capability.** | Medium (feasibility / morale / risk) | §7 inverts the ordering: minimal real `fork`/`await` from `.kp` (Stage 1) before defer/scope/loop re-expression (Stage 2). |
| R10 | **`OP_DEFER` silently drops a defer when `cur_exits==NULL`** (rt.c:617); CPS rewrite makes mis-emitting a defer outside a scope easier; fails *open*. | Low–Medium (correctness) | §3.2: replace the silent skip with a hard assertion/trap (Stage 0). |
| R11 | **Effect-handler unification may force continuation-representation revisions** (`__handleEff` is today a pure 5-arg prim with no scheduler handle); `rt-multishot` capability and escape-check do not exist. | Low–Medium (feasibility) | Staged last (Stage 4), *after* R1 is fixed (the abandonment path reuses `KK_FINSEQ`). Design `KK_HANDLER` now so the do-kernel emission shape need not change; add `rt-multishot` + compile-time escape-check before any multishot lands. Claim is bounded: the seam is right, not that no revisit is needed. |
| R12 | **Per-iteration do-scope under a loop could grow `f->k`** if the inner `KK_DOSCOPE` is not fully unwound before `KK_LOOP` re-iterates. | Low (correctness / stack-safety) | §4: explicit Stage-1/2 test asserting constant `f->k` depth across iterations of an accept-loop with a per-iteration defer. |
| R13 | **`CoroElide` will not fire for escaping (resumed-on-another-worker) fiber frames**; "recovers straight-line speed without giving up suspendability" overclaimed. | Low–Medium (perf expectations) | §5 corrected: elision helps only already-straight-line non-suspending blocks; the suspending path retains a real per-suspend frame cost. Stated plainly so Stage-5 expectations are calibrated. |
| R14 | **Boehm GC contention + conservative mark cost** under the M:N scheduler with many CPS-stepping fibers (global alloc lock on refill/large objects; mark scales with the CPS-enlarged live continuation graph). | Medium (perf) | Acknowledged for Stages 1–4 (§6); Perceus (precise, non-atomic for thread-local `f->k`) is the Stage-5 fix. Baseline gates (Stage 0) track allocation-count so regression is visible during the Boehm window. |
| R15 | **Two coexisting trampolines** (value-level `K_BOUNCE` + action-level CK loop) add a dispatch layer; the tail-action-returned-not-nested invariant is subtle and spread across `emitTailIO`/`compileDoBlock`. | Low (perf + correctness) | Invariant pinned by the R12 stack-safety test and a golden test asserting the tail action emits a returned node, not a nested `krt2_bind`. Dispatch overhead accepted as the cost of stack-safety + suspendability; flattened by LLVM at Stage 5. |

---

## 10. Key files

- **Backend cut site:** `src/Kappa/Backend/C.hs` (`compileItems` ~2741, `emitRunIOValue` ~3059, `emitRunIODiscard` ~3066, `emitTailIO` ~3087, `compileDoBlock` ~2631–2652, `primEntries` ~1675, `emitMain` ~1243, `drainQueue` ~442). Capabilities: `src/Kappa/Backend/Capabilities.hs`.
- **Runtime spine:** `runtime/rt.c` (`krt2_bind` :56, `begin_finseq` :377, `deliver` :390, `unwind` :429, `KK_FINSEQ` abandonment :464, `fiber_step` :484, interrupt check :488, bridge arm ~659–671, `OP_DOSCOPE` :609, `OP_DEFER` :617, `OP_WHILE`/`KK_LOOP` :629, `krt2_safepoint` :682 (no-op), root scope :758), `runtime/internal.h` (`KK_*`, `OP_*`, `Fiber` `k`/`mask_depth`/`cur_exits`/`cur_scope`), `runtime/kappart.c` (`OP_BIND`/`kctor` :259–265, `kclo` :306, `kgc_alloc=GC_MALLOC` :45), `runtime/kappart.h` (`KValue` :92–125, `kvar`/`KEnv` :132–135). Capabilities list: `KRT2_CAPABILITIES` (rt.c:17 — no `rt-multishot`, no `KK_HANDLER` yet).
- **Subsystems:** `runtime/scope.c`, `runtime/stm.c`, `runtime/reactor.c`, `runtime/race.c`.
- **Plan & semantics of record:** `runtime/docs/INTEGRATION.md`, `runtime/docs/REVIEW.md` (B1 — names this a real rewrite), `docs/Spec.md` (§18.7/§18.8, §18.1.4–18.1.14, §27.5A.3/.4, §32.2.3/.5/.6/.12/.20).
- **Reference semantics for differential testing:** `src/Kappa/Interp.hs`, `src/Kappa/Eval.hs` (`evalEffPrim`/`__handleEff` ~1051–1118).
