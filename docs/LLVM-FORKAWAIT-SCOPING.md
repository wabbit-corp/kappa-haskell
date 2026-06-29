# Scoping: fork / await / CK-machine (suspending path) on the LLVM backend

**Status:** scoping only — no code changed. Base: `14b5393` (Stage 4a, `KK_HANDLER`
one-shot effect handlers present in the runtime).

**TL;DR / recommendation.** The LLVM backend is *much* closer to the suspending
path than the "LLVM is C-only for concurrency" framing suggests. The do-kernel
CPS (`krt2_bind`/`krt2_then`/`kdo_N` continuation closures), the exception/masking
node-builders, **and one-shot effect handlers (`OP_HANDLE`/`OP_PERFORM`/
`OP_RESUME`) already work end-to-end on LLVM** — verified empirically: a
non-suspending `handle … with … resume k v` program produces identical output on
C and LLVM (`test/native/cases/effects.kp` → `20 / 42 / 36 / 107` on both). The
runtime ABI is the same for both backends (the runtime has an explicit comment
that `kenv_set_val` exists *for the LLVM backend*). **No runtime change is
needed — this is purely IR emission.** What fails closed today is a single,
narrow thing: the suspending **prims** (`fork`/`await`/`sleep`/promises/scopes/
monitors/STM) are on the `ckMachinePrims` blocklist
(`src/Kappa/Backend/LLVM.hs:560-578`), so they are removed from the lowerable set
and surface as `E_BACKEND_UNSUPPORTED … as a curried value`. The recommended plan
is a 5-stage port; **Stage 1 (fork/await + the basic do-kernel CPS) is small**
— the CPS machinery is already built; it is mostly un-blocklisting and closing
the `__awaitFiber`-as-curried-value gap.

All `file:line` references are to base `14b5393`.

---

## 1. The gap, precisely

### 1.1 What already works on LLVM (verified, not assumed)

| Construct | Mechanism | Evidence |
|---|---|---|
| Linear & imperative do-kernel CPS | `cpsItemsLL` → `krt2_bind`/`krt2_then`/`krt2_pure` + `kdo_N` continuation closures | `LLVM.hs:1901-2066`, `emitDoCont` `LLVM.hs:2210-2231` |
| `var`/`:=`/`while`/`break`/`continue`/`return` | `krt2_new_ref`/`krt2_write_ref`/`krt2_while`/`krt2_return` | `LLVM.hs:1968-2027` |
| `ioBind`/`ioThen`/`ioPure` as explicit applications | `ioNodeBuilder` → `krt2_bind`/`then`/`pure` | `LLVM.hs:3299-3301` |
| `throwIO`/`catchIO`/`finallyIO`/`__reraiseCause` | `ioNodeBuilder` → `krt2_throw`/`catch`/`finally`/`reraise` | `LLVM.hs:3303-3306` |
| `onExit`/`onInterrupt`/`locallyFiberRef` | `ioNodeBuilder` | `LLVM.hs:3310-3312` |
| `uninterruptible`/`__mask`/`poll` | `ioNodeBuilder` | `LLVM.hs:3316-3318` |
| `using` (acquire/release) | `krt2_acquire_release` | `LLVM.hs:2052-2065` |
| **One-shot effect handlers** — `handle`/`perform`/`resume` | `__handleEff`→`kpf_rt_handle`, `__effBind`→`kpf_eff_bind`, `runPure`→`kpf_run_eff` (in `primEntries`, **not** blocklisted); `resume k v` is plain application `k v` | `effects.kp` builds + runs identically on C and LLVM |

The decisive fact: **the LLVM continuation closure is already byte-for-byte the
runtime's `KFn` ABI.** `emitDoCont` (`LLVM.hs:2221-2229`) emits

```
define internal ptr @kdo_N(ptr %cenv, ptr %arg) { build: … ret ptr <node> }
```

which is exactly `typedef KValue *(*KFn)(KEnv *env, KValue *arg)`
(`runtime/kappart.h:105`). The CK-machine re-enters it at `deliver`'s `KK_BIND`
arm — `f->cur = kapp(c->a, v)` (`runtime/rt.c:865-866`) — where `c->a` is the
`kclo(@kdo_N, %cenv)` the LLVM backend already emits (`LLVM.hs:2095`) and `v` is
the delivered/resumed value. **There is nothing to redesign in the continuation
ABI — it is done and proven by the working effect-handler path.**

### 1.2 What fails closed, and exactly why

The suspending prims are listed in `ckMachinePrims` (`LLVM.hs:560-578`):

```
"atomically","stmBind","stmPure","retry","newTVar","readTVar","writeTVar",
"forkIO","fork","spawn","spawnIn","spawnLink",
"__awaitFiber","awaitPromise","awaitPromiseExit",
"monitor","awaitMonitor","demonitor",
"sleepFor","yieldNow","self",
"newScope","forkIn","scopeJoin","scopeCancel"
```

`lowerablePrim` (`LLVM.hs:3445-3448`) short-circuits to `Nothing` for any name in
this set, so `globPrimName` does not recognise it, so the prim is treated as an
**ordinary global**. Two failure shapes result:

1. **Saturated occurrence** (e.g. `fork action`) → falls to `compileAppDefault`
   → `kapp(compile fork, action)`; `compile fork` (a bare `CGlob`) →
   `compilePrimValue "__forkRun"` → `primNativeEntry` is `Nothing` (blocklisted)
   → `E_BACKEND_UNSUPPORTED`.

2. **The `__awaitFiber`-as-curried-value gap** (the one agents keep hitting). The
   prelude defines `let await fib = __awaitFiber fib` (`Prelude.hs:1480`). Inside
   `await`'s lifted body the spine head `__awaitFiber` is blocklisted, so
   `globPrimName` returns `Nothing`, the spine falls to `compileAppDefault` →
   `kapp(compile __awaitFiber, fib)`, and `compile __awaitFiber` →
   `compilePrimValue "__awaitFiber"` → `Nothing` → the exact diagnostic observed:

   ```
   <std.prelude>:611:1: error[E_BACKEND_UNSUPPORTED] … definition 'await':
   the LLVM backend does not implement the primitive '__awaitFiber'
   as a curried value; use the C backend
   ```

   This fires at *prelude load* — every program transitively reaches `await`,
   so the whole module is rejected before user code is even examined.

### 1.3 Two *kinds* of suspending construct, different effort

Not all blocklisted names are equal — they split by how the C backend lowers them:

* **(A) `primEntries` node-builders, `isIO=False`** — `fork`/`__forkRun`,
  `__forkDaemon`, `__awaitFiber`, `cede`, `__sleepForNanos`, the promise ops,
  the FiberRef ops, `newScope`/`forkIn`/`shutdownScope`/`monitor`/`awaitMonitor`/
  `demonitor` (C.hs `primEntries`, `C.hs:2063-2085`). These already have a
  `kpf_*` wrapper and an arity; building the node is *pure construction* (the
  `isIO=False` flag), and the existing LLVM `compilePureWrapper`
  (`LLVM.hs:3408-3429`) emits `call ptr @kpf_fork(ptr %argv)` — the node — for
  free. **For these the port is almost entirely un-blocklisting.**

* **(B) Bespoke `krt2_*` node-builders, special-cased in `compileAppGlob`** — STM
  (`stmBind`→`krt2_stm_bind`, `atomically`→`krt2_atomically`, `newTVar`/`readTVar`/
  `writeTVar`, `C.hs:2372-2397`). These have **no `kpf_*` array wrapper**; the C
  backend emits a direct `krt2_stm_bind(m, k)` etc. For LLVM these need new
  `ioNodeBuilder` entries (exactly the shape the exception ops already use,
  `LLVM.hs:3289-3319`), not just un-blocklisting.

* **(C) Node-builders used as *curried values*** — the secondary gap. e.g.
  `awaitPromise`'s prelude body references `__reraiseCause` partially, so
  `compilePrimValue "__reraiseCause"` is hit and `__reraiseCause` (an
  `ioNodeBuilder`, no `kpf_*` entry) is rejected. Observed building
  `promise.kp`. The fix is a `kpf_*` curried wrapper or eta-expansion so a
  partial reference to a node-builder has a closure form.

---

## 2. The design

**Principle: emit the identical runtime calls the C backend emits; the runtime is
backend-agnostic.** `runtime/kappart2.h:28-32` states the contract: the `krt2_*`
builders "are what `Kappa.Backend.C` emits in place of the bare kappart IO calls;
each returns a suspended `KValue` IO action; the fiber step loop interprets it."
Nothing in that contract is C-specific. The LLVM port adds **no runtime code** —
only `.ll` emission of the same symbols.

### 2.1 The continuation-function signature + CK-machine re-entry (already correct)

* **Signature.** `KValue *(*)(KEnv *env, KValue *arg)` = `KFn`
  (`kappart.h:105`). LLVM: `define internal ptr @kdo_N(ptr %cenv, ptr %arg)`.
  Already emitted by `emitDoCont` (`LLVM.hs:2210-2231`) and `compileLam`.
* **Closure.** `K_CLO` = `{KFn fn; KEnv *env}` (`kappart.h:122`); built by
  `kclo(KFn, KEnv*)`. LLVM emits `call ptr @kclo(ptr @kdo_N, ptr %cenv)`
  (`LLVM.hs:2095`). The env is a de Bruijn linked list
  (`struct KEnv {KValue *val; KEnv *next;}`, `kappart.h:149-152`); push via
  `kpush`, read via `kvar`.
* **Re-entry.** The machine never calls `fn` directly — always via `kapp`
  (`kapply_once`, `kappart.c:715-719`) so a returned `K_BOUNCE` is trampolined.
  The bind re-entry is `deliver`'s `KK_BIND` arm: `f->cur = kapp(c->a, v)`
  (`rt.c:865-866`). After a park, the waker sets `f->cur = krt2_pure(value)`
  (`krt2i_wake`, `rt.c:371-385`); stepping that `OP_PURE` calls `deliver`, which
  applies the bind continuation with the resumed value — i.e. **the resumed value
  arrives as the continuation's `%arg` and the captured environment as `%cenv`,
  identically to the synchronous case.** The only difference is which worker
  thread runs it. The LLVM backend needs no awareness of parking at all.

### 2.2 The KEnv / closure representation across a park

`var` cells must survive a park, which is why a `var x = e` lowers to
`krt2_new_ref` and is `kpush`ed onto the KEnv (so it lives in the heap env chain,
reachable from the parked fiber's `Cont`). The LLVM backend already does this
(`newRefAction` `LLVM.hs:2476+`, pushed in `emitDoCont`'s `bindPatDo`). No change.

### 2.3 GC roots / statepoints under the conservative collector

**The single most reassuring finding for the port.** The runtime is a conservative
Boehm GC, but **liveness across suspension is via an explicit heap root set, not
C-stack scanning** (`internal.h:10-24`). Every not-yet-DONE fiber is in `rt->all`,
a strong doubly-linked root reachable from the static `g_rt`; its live
continuation is the heap `Cont` chain (`f->k`) and `f->cur`. A parked fiber's
`IoReq`/`Waiter`/`RQNode` are all `GC_MALLOC`'d and reachable
(`reactor.c:85-94`, `rt.c:359`). A suspending op simply `return`s out of
`fiber_step` — the C stack unwinds and no roots are lost.

Consequence: **the LLVM IR needs no GC statepoints or stack maps.** It only needs
to (a) route allocations through `GC_MALLOC`/`kgc_alloc` (it already does, via
the runtime builders) and (b) keep live values in the heap node/env graph (it
already does — it only emits node-builder calls; the machine owns the `Cont`
chain). Scheduler fairness is handled separately: generated scalar loops emit
counter-gated `krt2_safepoint` calls, but those are interruption/fairness polls,
not GC statepoints. This removes the scariest hypothetical risk from the port.

### 2.4 The fix shape per construct kind (from §1.3)

* **(A) prims** — remove from `ckMachinePrims`; the existing `compilePureWrapper`
  (saturated, `kpf_X(argv)`) and `compilePrimValue` (curried, `knative(kpf_X,…)`)
  paths build the node. Confirm each `kpf_*` symbol is declared.
* **(B) STM** — add `ioNodeBuilder` entries `stmBind→krt2_stm_bind`,
  `atomically→krt2_atomically`, etc. (the exception-op shape), plus the
  STM-family is interpreted by `stm_run`, not `fiber_step` — but that is
  runtime-internal; the backend only builds the nodes.
* **(C) curried node-builders** — give node-builders without a `kpf_*` wrapper a
  curried form (wrapper symbol or compiler-side eta-expansion) so a partial
  reference (e.g. `__reraiseCause` inside `awaitPromise`) lowers.

---

## 3. What LLVM already has vs must build

**Already has (reuse verbatim):**

* Value model: uniform `KValue*`; `kctor`/`kclo`/`kpush`/`kvar`/`kapp`/`kbounce`
  emission; the tagged-immediate discriminator is shared with C.
* The do-kernel CPS (`cpsItemsLL`) and the `KFn`-shaped continuation closures
  (`emitDoCont`) — the load-bearing mechanism.
* All exception/masking/finalizer node-builders (`ioNodeBuilder`).
* `krt2_acquire_release` (`using`).
* `OP_HANDLE`/`OP_PERFORM`/`OP_RESUME` effect handlers (works today).
* `knative_sat`/`knative`/`compilePureWrapper`/`compilePrimValue` prim paths,
  all derived from the shared `primEntries`/`primDirect` C tables (`LLVM.hs:3431-3448`).
* `@main` calling `krt2_new`/`krt2_run_main`/`krt2_exit_is_success`
  (`LLVM.hs:693-712`) — the scheduler handoff is already wired.

**Must build:**

* Un-blocklist the kind-(A) prims and verify their `kpf_*`/`krt2_*` declarations.
* Kind-(B) STM `ioNodeBuilder` entries (+ the `OP_ATOMICALLY` bridge node).
* Kind-(C) curried form for node-builders lacking a `kpf_*` wrapper.
* Replicate the C backend's `suspenderGlobals` / `cpsEligible` detection IF the
  LLVM `compileDo` needs to choose between bridge and CPS — **but note** the LLVM
  backend already lowers *every* do-block through the CPS path
  (`LLVM.hs:1770-1773`: "one lowering for both the sequential and the (future)
  suspending case"), so it has *no* synchronous bridge to fall off. This is an
  advantage: the LLVM do-kernel does not need the C backend's bridge-vs-CPS gate
  at all; once the prims build their nodes, suspension Just Works on the uniform
  path. The `firstUnsupportedItem` gate (`LLVM.hs:1818-1859`) still rejects
  labeled break/continue / `while`-else / `KFor` / `KDefer` / `KLetQ`, which are
  orthogonal do-kernel features, not concurrency.
* Conformance: extend `test/native/llvm-parity.sh` to cover the
  `test/native/cases/*.kp` concurrency corpus (fork/await/promise/STM/scope/
  effparking) gated interp == C == LLVM.

---

## 4. Staged plan

Each stage is independently shippable and gated by `llvm-parity.sh` (interp == C
== LLVM). Effort is rough engineer-days; risk is the chance of a hidden ABI/Core
surprise.

### Stage 1 — fork / await + the basic do-kernel CPS  ·  effort: S (1-2d)  ·  risk: low
Un-blocklist `__forkRun`/`fork`/`forkIO`, `__awaitFiber`, `cede`, `__sleepForNanos`/
`sleepFor`, `yieldNow`, `self` from `ckMachinePrims`. Close the
`__awaitFiber`-as-curried-value gap (kind C) so the prelude `await`/`fork`
definitions lower (give the node-builder prims a curried `kpf_*` form, or confirm
the `compilePrimValue` `knative(kpf_await,1,…)` path works — `kpf_await` already
exists and returns the `OP_AWAIT` node). Gate `fork-transitive.kp`,
`suspendloop.kp` parity. *Most of the work is already done — this stage is
primarily list surgery + the curried-value fix.*

### Stage 2 — race / timeout / promises / the IO combinators  ·  effort: S-M (2-3d)  ·  risk: low
Un-blocklist the promise ops (`newPromise`/`completePromise`/`awaitPromiseExit`/
`pollPromise`/`isDonePromise`) and confirm `krt2_race`/`krt2_timeout` (composite
trees built in `race.c`) lower — `__race`/`__timeout` are surfaced via prims, so
once the underlying fork/await/promise prims lower, race/timeout follow. Fix the
`__reraiseCause`-as-curried-value gap (kind C) blocking `awaitPromise`. Gate
`promise.kp`, `timeout.kp`, `interrupt-cause.kp`.

### Stage 3 — masking / using / structured scopes  ·  effort: S (1-2d)  ·  risk: low
Masking (`__mask`/`uninterruptible`/`poll`) and `using` already lower; this stage
adds the scope/monitor prims (`newScope`/`forkIn`/`shutdownScope`/`monitor`/
`awaitMonitor`/`demonitor`) and FiberRef ops (the non-suspending FiberRef
builders already lower via `onExit`/`onInterrupt`/`locallyFiberRef`, but the
suspending scope ops are blocklisted). Gate `monitor.kp`, `usinginterrupt.kp`,
`on-exit-interrupt.kp`.

### Stage 4 — effect handlers that park  ·  effort: XS (≈0.5d)  ·  risk: very low
**Handlers already work** (`effects.kp` passes). The only thing missing is a
handler clause that *suspends* (forks/awaits/sleeps before `resume`) — and that is
unblocked automatically once Stage 1 lands, since the clause body is an ordinary
do-block on the same CK-machine. Gate `effparking.kp`. This is mostly a
conformance-test stage, not an emission stage.

### Stage 5 — STM (the bespoke node-builders)  ·  effort: M (2-4d)  ·  risk: medium
Un-blocklist `atomically`/`stmBind`/`stmPure`/`retry`/`newTVar`/`readTVar`/
`writeTVar` AND add `ioNodeBuilder`-style entries that emit the bespoke
`krt2_stm_bind`/`krt2_atomically`/`krt2_new_tvar`/`krt2_read_tvar`/
`krt2_write_tvar` calls (C.hs:2372-2397) — these have no `kpf_*` array wrapper, so
the standard prim path does not reach them. Verify the STM-family/`OP_ATOMICALLY`
IO-bridge node and the `Monad STM` desugaring lower. Gate `stm-tvar.kp`. Highest
risk because it is the one kind-(B) family with a distinct emission shape.

---

## 5. Riskiest parts + recommendation

1. **The continuation-function ABI match** — *de-risked.* It is already emitted
   and proven by the working effect-handler path (`effects.kp` C == LLVM). The
   `kdo_N(ptr %cenv, ptr %arg)` form *is* `KFn`. No remaining risk.

2. **GC roots across a park** — *de-risked.* The conservative collector keeps
   parked fibers live via the `rt->all` root set, not the C stack
   (`internal.h:10-24`, `reactor.c:85-94`). The LLVM IR needs **no statepoints,
   no stack maps**. The only obligation — keep live state in the heap node/env
   graph and allocate via `GC_MALLOC` — is already met because the backend only
   emits node-builder calls and the machine owns the `Cont` chain.

3. **The `__awaitFiber`-as-curried-value gap** — *the real remaining work, but
   small.* This is a code-emission gap (a node-builder prim used as a partial
   value with no curried form), not an architectural one. The prelude
   `await`/`fork`/`awaitPromise` definitions reference these node-builders
   curried; the fix is a `kpf_*` curried wrapper (the prim ones, e.g. `kpf_await`,
   already exist — confirm `compilePrimValue`'s `knative(kpf_await,…)` builds the
   `OP_AWAIT` node) or compiler-side eta-expansion for the bespoke node-builders
   (`__reraiseCause`).

4. **STM's bespoke emission (kind B)** — *medium.* The only family without a
   uniform `kpf_*` path; needs new `ioNodeBuilder` cases. Isolated to Stage 5.

**Recommendation: proceed, starting with Stage 1.** The framing that "LLVM is
C-only for concurrency because it fail-closes on the suspending path" overstates
the gap: the suspending *machinery* (CPS continuations, the CK-machine handoff,
effect handlers, the conservative-GC park protocol) is already present and
verified. The blocker is a narrow, well-understood prim-coverage gap plus the
curried-value emission fix. Stage 1 (fork/await) is a small, high-confidence
change that unblocks the majority of concurrency programs and effect-handler
parking simultaneously; STM (Stage 5) is the only piece with a genuinely distinct
emission shape and should be sequenced last. No runtime changes are required at
any stage — the kappart2 ABI is backend-agnostic by design.
