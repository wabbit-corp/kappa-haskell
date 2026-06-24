# Kappa Runtime Roadmap

The master checklist tying the design documents together so nothing is lost.
Each item links to the design doc (and spec section) that specifies it, and to
the measurement that gates it where one exists.

**Design documents**
- [`CPS-DESIGN.md`](CPS-DESIGN.md) — the do-kernel CPS / continuation rewrite (Stages 0–5, R1–R15).
- [`UNBOXING-DESIGN.md`](UNBOXING-DESIGN.md) — value-representation specialization (immediate tagging + worker/wrapper).
- [`PRIMITIVES.md`](PRIMITIVES.md) — the ADD/DERIVE/SKIP analysis of missing concurrency primitives.
- [`COVERAGE.md`](COVERAGE.md) — ZIO/Cats-Effect combinator coverage.
- [`DESIGN.md`](DESIGN.md) / [`REVIEW.md`](REVIEW.md) / [`RESEARCH.md`](RESEARCH.md) — the original runtime architecture + 8-lens review.
- [`bench/README.md`](../bench/README.md) — the perf baseline (`make bench`); the numbers that gate the perf work.
- `docs/Spec.md` — §18 (effects/fibers/STM), §27 (capabilities/native), §29 (std.atomic/supervisor), §32.2 (runtime state machine).

---

## Done ✅

- [x] **kappart2 runtime is the unconditional native runtime** (M:N fibers, libuv reactor, STM, structured concurrency, CK-machine); the value model + scheduler live in [`runtime/`](..).
- [x] **No by-name prim dispatch** — codegen lowers to direct `kp_*`/`kpf_*` calls or curried `K_NATIVE`; `prim_fire_pure`/`K_PRIM` removed.
- [x] **`std.atomic`** ([`../atomic.c`](../atomic.c)) — real C11 lock-free `AtomicRef`, stress-verified; `rt-atomics` honest.
- [x] **Single-agent STM from `.kp`** (`TVar`/`atomically` over a cell, matching the interpreter).
- [x] **CPS Stage 0** — R1 masked finalizer drains, R10 fail-closed `OP_DEFER` (CPS-DESIGN §4, R1/R10).
- [x] **CPS Stage 1** — real `fork`/`await` suspension from `.kp` (CPS-DESIGN §3.1, Stage 1).
- [x] **CPS Stage 2 (partial)** — `defer`/do-scope in suspending blocks; fail-closed boundary for not-yet-CPS-able shapes (CPS-DESIGN §3.1/§7, Stage 2).
- [x] **CPS Stage 3 (partial)** — structured concurrency `newScope`/`forkIn`/`shutdownScope`/`monitor`/`awaitMonitor` from `.kp` (§18.1.8, §32.2.3).
- [x] **Perf baseline** — [`../bench`](../bench): boxing is the 50× lever (allocation), fork/await ~3.5× a goroutine; CPS indirection is not the dominant cost.
- [x] **Design docs** — CPS-DESIGN, UNBOXING-DESIGN, PRIMITIVES.

---

## Recommended order

The two big tracks (CPS, Unboxing) interleave around one shared prerequisite —
**§3.3 suspendability/escape analysis** — which is why it is first.

1. [ ] **§3.3 suspendability analysis** — the shared unblock. ← *in progress*
2. [ ] **Unboxing Stage 0** — GC/alignment contract + canonical encoding (safe prep, parallel).
3. [ ] **CPS loop family** — var-read normalization.
4. [ ] **Unboxing Stage 1** — immediate-int tagging (the allocation win).
5. [ ] **CPS Stage 2/3 remainder** — `using`, `return`, masking surface.
6. [ ] **General CPS** — `ioBind` expressions (unblocks `join`/`race`/`timeout`).
7. [ ] **Unboxing Stage 2** — worker/wrapper specialization (`Double`/FFI/fused).
8. [ ] **Missing primitives** — `onInterrupt`/`onExit`, `FiberRef.modify`, `Promise.poll`, `disconnect`.
9. [ ] **CPS Stage 4** — effect-handler unification (`KK_HANDLER`).
10. [ ] **Perf** — fiber/continuation pooling.
11. [ ] **CPS Stage 5 + Unboxing endgame** — LLVM coroutines + Perceus RC.

---

## Track: CPS do-kernel rewrite ([`CPS-DESIGN.md`](CPS-DESIGN.md))

- [ ] **§3.3 suspendability analysis** (CPS-DESIGN §3.3, "Stage 1.5"). Replace the
      flat syntactic `suspendingNames` spine-head check (`C.hs`) with a sound
      call-graph reachability analysis: a global may-suspend iff it transitively
      references a suspending primitive; conservative default = may-suspend.
      Unblocks transitive suspenders (user helpers that fork) and is the gate for
      the unboxing worker/wrapper. **Test:** a user fn that forks, used in a
      do-block, suspends correctly; a proven-pure fn stays straight-line.
- [ ] **Loop family** (CPS-DESIGN §4, R5/R7/R12). `var`/`:=`/`while`/`break`/
      `continue` in a suspending block. **Blocker:** var reads in a re-run body
      must become run-time `OP_READ_REF` (a de-Bruijn hoist preserving
      read-after-write), not build-time `kref_get`. Loop eligibility (scalarize
      vs CPS) is decided by §3.3 + the R5 escape rule. **Test:** accept-loop
      (`while running { c <- accept; fork (handle c) }`); a counter loop forking
      per iteration; constant `f->k` depth across iterations (R12).
- [ ] **`using`** (§19.5). Resource scope: acquire-bind + register `release` as a
      defer + bind the resource. (Needs the Resource-trait test surface.)
- [ ] **`return`** (§18.8). Early non-local return — needs the do-block boundary so
      `return` exits the block, not the fiber.
- [ ] **Masking surface** (§18.1.12). `mask`/`uninterruptible`/`poll` are runtime-
      only (`krt2_*`) — NOT yet exposed in the prelude. Requires prelude `prim`
      decls + interpreter handling FIRST, then the (trivial) backend wiring.
- [ ] **General CPS for `ioBind` expressions** (CPS-DESIGN §3.1). Today only `CDo`
      blocks are CPS-lowered; an `ioBind (await …) k` expression (e.g. the
      prelude `join`/`race`/`timeout` bodies) still hits the bridge. Lower
      `ioBind`/`ioThen` spines to `krt2_bind`/`krt2_then` when they may-suspend.
- [ ] **`atomically`/`retry` real parking** (§18.1.13). Switch the single-agent
      `Ref` STM shim to the journaled `krt2_atomically`/`OP_ATOMICALLY` so
      transactions park + retry across fibers ([`../stm.c`](../stm.c) already implements it).
- [ ] **Stage 4 — effect-handler unification** (CPS-DESIGN §2, Stage 4). One
      `KK_HANDLER` prompt frame; `perform`/`resume` reuse `deliver`/`unwind`.
      Depends on R1 (done). `rt-multishot` behind the compile-time escape-check.
- [ ] **Stage 5 — LLVM coroutines** (CPS-DESIGN §5). Retarget `kdo_*`/`kdok_*` to
      `coro.id.retcon.once`; seed `CoroSplit` liveness from the `KEnv`.

---

## Track: Value unboxing ([`UNBOXING-DESIGN.md`](UNBOXING-DESIGN.md))

- [ ] **Stage 0 — GC/alignment contract + canonical encoding** (UNBOXING §5.2/§5.4/§7).
      Verify `GC_MALLOC` 8-byte alignment (low 3 bits 0) + Boehm treats odd words
      as non-pointers; canonicalize `kbool`/`kunit`/`kint`/nullary-ctor encoding to
      a single form; reserve the low 3 tag bits. **Safe, verifiable prep** that
      de-risks Stage 1.
- [ ] **Stage 1 — immediate-int tagging** (UNBOXING §1/§5/§7). `(i<<1)|1` in the
      `KValue*` word for small `Int`/`Bool`/`Char`/`Unit`. **299+ deref sites in
      `kappart.c` must tag-test** — a runtime-wide audit, not a swap. Removes the
      per-`addInt` allocation; survives CPS parks. **Gate:** the
      ctor-build/match-heavy go/no-go (UNBOXING §7); measure against `make bench`.
- [ ] **Stage 1.5** = the §3.3 analysis above (shared).
- [ ] **Stage 2 — worker/wrapper specialization** (UNBOXING §1/§7). Generalize
      `scalarPlan`/`kwi_`/`kwd_` to a layout kind (`Boxed|I64|F64|FixedFFI`) on Core
      types; one unboxed worker per class, boxed `kw_g` as the reference, the
      `kunbox_*`/`*ovf` escape as the floor. Unboxes `Double`/wide-FFI/fused hot
      paths. **Blocked on §3.3** (Stage 2a re-proves suspension-freedom).

---

## Track: Missing primitives ([`PRIMITIVES.md`](PRIMITIVES.md))

- [ ] **`onInterrupt`/`onExit`** — finalizer receiving the exit Reason; small
      extension of `KK_FINSEQ` (which already carries the Reason). PRIMITIVES #2.
- [ ] **`FiberRef.modify` + copy-on-fork** — §18.1.7 parent/child independence
      (normative conformance gap). PRIMITIVES #4 / ADD #4.
- [ ] **`Promise.poll`/`isDone`** — non-blocking peek. PRIMITIVES #3.
- [ ] **`disconnect`** — detached interruption (verify forkDaemon doesn't already
      cover it). PRIMITIVES #5.
- [ ] **DERIVE as `.kp` library** — `zipPar`/`foreachPar`/`raceAll`/`timeoutTo`,
      `Cause` projections (pure folds), `std.supervisor`, memoize, semaphores/
      queues over `TVar`+`Promise`. Gated on the general-CPS lowering above.
- [ ] Keep the interpreter (`src/Kappa/Interp.hs`) in lockstep for the ADD items.

---

## Track: Performance ([`bench/README.md`](../bench/README.md))

- [ ] **Fiber/continuation pooling** — the fork path allocates 832 B/op
      (`sizeof(Fiber)=200`, ~64 of which is the per-fiber `pthread_mutex`).
      Lighter sync + a free-list (careful with the conservative GC + the
      await/exit lifetime).
- [ ] **Perceus precise RC** (CPS-DESIGN §5) — non-atomic for thread-local `f->k`;
      turns the per-bind/continuation allocation into a reuse/in-place write.
      The endgame for the suspension path; needs the §3.3/unboxing ptr-vs-scalar map.
- [ ] Keep `make bench` green as a non-regression gate from each stage.
