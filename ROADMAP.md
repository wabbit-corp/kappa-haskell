# Kappa Roadmap — the grand plan

The single ordered plan for the **kappa-haskell** compiler + runtime, so work
does not scatter across 20 directions. Each item links to the design doc (and
spec section) that specifies it, and to the measurement that gates it where one
exists. This started life as the runtime-only roadmap and is being grown to
cover the whole implementation (front end, IRs, backend, runtime, spec gaps).

**Two implementations** — keep them straight:
- **kappa-haskell** (this repo) — the native (C + LLVM) compiler + the kappart2
  runtime. The one we are building. It currently lowers `Term` (its KCore)
  *directly* to C/LLVM with no KBackendIR (see the IR-pipeline track).
- **`../kappa/`** (F#/.NET) — a second, more spec-complete implementation
  (`KFrontIR.fs` → `KCore.fs` → `KBackendIR.fs` → `KBackendLowering.fs` →
  CLR). Use it as a **structural reference for the §34.3 stage decomposition
  ONLY** — its IR-level detail decisions are short-sighted and must NOT be
  copied. `docs/Spec.md` is the source of truth, not either implementation.

**Design documents**
- [`Spec.md`](docs/Spec.md) — the normative spec. IR pipeline: §30.2 KCore (the
  typed kernel), §34.2 KFrontIR, §34.3 KBackendIR (§34.3.1 lowering stages:
  ERASURE / INHABITANCE / REPRESENTATION_SELECTION / CALL_LOWERING / …). Runtime:
  §18 (effects/fibers/STM), §27 (capabilities/native), §29 (std.atomic/supervisor),
  §31 (erasure), §32.2 (runtime state machine).
- [`LAYOUT-DESIGN.md`](runtime/docs/LAYOUT-DESIGN.md) — the value-layout system
  (immediate tagging `b010`/`b011`, niche, Direct-tag, the uniform-vs-niche split).
- [`UNBOXING-DESIGN.md`](runtime/docs/UNBOXING-DESIGN.md) — value-representation specialization (immediate tagging + worker/wrapper).
- [`CPS-DESIGN.md`](runtime/docs/CPS-DESIGN.md) — the do-kernel CPS / continuation rewrite (Stages 0–5, R1–R15).
- [`PRIMITIVES.md`](runtime/docs/PRIMITIVES.md) — the ADD/DERIVE/SKIP analysis of missing concurrency primitives.
- [`COVERAGE.md`](runtime/docs/COVERAGE.md) — ZIO/Cats-Effect combinator coverage.
- [`DESIGN.md`](runtime/docs/DESIGN.md) / [`REVIEW.md`](runtime/docs/REVIEW.md) / [`RESEARCH.md`](runtime/docs/RESEARCH.md) — the original runtime architecture + 8-lens review.
- [`bench/README.md`](runtime/bench/README.md) — the perf baseline (`make bench`); the numbers that gate the perf work.

---

## Done ✅

- [x] **kappart2 runtime is the unconditional native runtime** (M:N fibers, libuv reactor, STM, structured concurrency, CK-machine); the value model + scheduler live in [`runtime/`](runtime).
- [x] **No by-name prim dispatch** — codegen lowers to direct `kp_*`/`kpf_*` calls or curried `K_NATIVE`; `prim_fire_pure`/`K_PRIM` removed.
- [x] **`std.atomic`** ([`../atomic.c`](runtime/atomic.c)) — real C11 lock-free `AtomicRef`, stress-verified; `rt-atomics` honest.
- [x] **Single-agent STM from `.kp`** (`TVar`/`atomically` over a cell, matching the interpreter).
- [x] **CPS Stage 0** — R1 masked finalizer drains, R10 fail-closed `OP_DEFER` (CPS-DESIGN §4, R1/R10).
- [x] **CPS Stage 1** — real `fork`/`await` suspension from `.kp` (CPS-DESIGN §3.1, Stage 1).
- [x] **CPS Stage 2 (partial)** — `defer`/do-scope in suspending blocks; fail-closed boundary for not-yet-CPS-able shapes (CPS-DESIGN §3.1/§7, Stage 2).
- [x] **CPS Stage 3 (partial)** — structured concurrency `newScope`/`forkIn`/`shutdownScope`/`monitor`/`awaitMonitor` from `.kp` (§18.1.8, §32.2.3).
- [x] **Perf baseline** — [`runtime/bench`](runtime/bench): boxing is the 50× lever (allocation), fork/await ~3.5× a goroutine; CPS indirection is not the dominant cost.
- [x] **Value layout — uniform immediates + packing** (LAYOUT-DESIGN): immediate Int (`b001`, `addInt` 48→0), nullary-ctor immediates (`b010`, every nullary ctor, `ctor0-build` 48→0), packed single-field ctors (`b011`, `Some smallInt`/`Ok`/`Err`, 48→0), and packed two-field ctors (`b011`, `Pair`/`Cons(small,Nil)`/small `Rational`, 0 B/op). All UNIFORM (explicit discriminant), adversarially verified (corpus 102/102 interp==C==LLVM, sweeps + clean audits).
- [x] **Erased-type-application native crash FIXED** — `sequence`/`for_`/`traverse` over IO crashed both native backends (`kapp` on a non-function); root cause was an erased type *application* `f a` lowered as `kapp(unit,unit)`. Fixed via the RuntimeErased erasure verdict (types + Q0, never dicts) at the application spine.
- [x] **Design docs** — Spec, LAYOUT-DESIGN, UNBOXING-DESIGN, CPS-DESIGN, PRIMITIVES.

---

## Recommended order

The plan front-loads the **uniform** wins (sound with no IR scaffolding) and the
shared **§3.3 suspendability** prerequisite, then makes the one **architecture
investment** (KBackendIR / representation selection) that unblocks every
*type-directed* layout (the niche), then finishes the CPS + primitives + perf
endgame. The big near-term fork is item 6 — until it lands, the niche and clean
type-directed layout are blocked (see the IR-pipeline track for why).

1. [x] **§3.3 suspendability analysis** — the shared unblock. ✅
2. [x] **Value layout — uniform immediates + packing** — `b001` Int, `b010` nullary, `b011` single- AND two-field packing. DONE, adversarially verified (corpus 102/102). The NON-uniform layouts (niche, full-range Int) are blocked on item 6, NOT on more runtime work — see [`LAYOUT-DESIGN.md`](runtime/docs/LAYOUT-DESIGN.md).
3. [x] **CPS loop family** — var/while/break/continue/return in suspending blocks + R7 var-read normalization. DONE (`for`/labeled/`using`/`let?` still fail-closed).
4. [x] **Erased-type-application native crash fix** — the RuntimeErased erasure verdict (types + Q0, never dicts) at the application spine. DONE.
5. [~] **Scalar Double worker** (UNBOXING §7 Stage 1.5 + 2b) — the per-binding transitive may-suspend witness (a C-local `double` is lost across a fiber park), then the `kwd_` Double worker with FP pinned (`-ffp-contract=off`). Kills the `addDouble` 48 B/op box. IN PROGRESS.
6. [ ] **KBackendIR slice — INHABITANCE + REPRESENTATION_SELECTION** (§34.3) — **the architecture investment.** Introduce a representation-typed backend IR between KCore (`Term`) and the C/LLVM emitter, choosing layouts/tags/reps at compile time with type + inhabitance info, instead of the current ad-hoc runtime packing + hand-rolled scalar worker. Pairs with a **Core/KBackendIR Lint** (catches the erasure-bug class; realizes "verified at Core"). THE home for items 7. See the IR-pipeline track.
7. [ ] **Niche `Option<boxed>` + full-range `Option<Int>`** — the headline non-uniform layout wins; ride on item 6 (need the concrete type at construct/match + a coercion at mono/poly boundaries).
8. [ ] **CPS Stage 2/3 remainder** — `using`, `return`, masking surface.
9. [ ] **Missing primitives** — `onInterrupt`/`onExit`, `FiberRef.modify`, `Promise.poll`, `disconnect`.
10. [ ] **CPS Stage 4** — effect-handler unification (`KK_HANDLER`).
11. [ ] **Perf** — fiber/continuation pooling.
12. [ ] **Spec coverage** — the not-yet-implemented spec surfaces, surveyed + ordered (see the Spec-coverage track; to be populated).
13. [ ] **CPS Stage 5 + Unboxing endgame** — LLVM coroutines + Perceus RC.

---

## Track: Compiler IR pipeline & representation selection (the architecture)

**The gap.** The Spec mandates `KFrontIR` (§34.2) → **KCore** (§30.2, the typed
kernel) → **KBackendIR** (§34.3); KCore→KBackendIR runs §34.3.1's conceptual
stages, including **`INHABITANCE`** (shape summaries "consulted by representation
selection") and **`REPRESENTATION_SELECTION`** ("choose runtime representation
classes, layouts, and tag encodings for data, variants, records, dictionaries,
…"). kappa-haskell has **no KBackendIR**: `Backend/C.hs` lowers `Term` (its
KCore) directly to C/LLVM, doing representation selection **at runtime, per
value** (`kctor`: argc/fit → `b010`/`b011`/boxed) plus a hand-rolled scalar-worker
analysis. That is sound + ideal for **uniform** reps (explicit discriminant,
decodable blind) but **structurally cannot do type-directed layout** — the niche
`Some p = p` needs the concrete type at the construct/match site, a compile-time
decision. `Term` is only partially annotated (`CPi`/`CLet` carry types;
`CLam`/`CCtor`/`CMatch`/`CPCtor` do not — Core.hs), and there is no Core re-checker.
This track is the one big architecture investment; **scope it as its own effort
first** (the §34.3 stages × what `Backend/C.hs` does today × the minimal
niche-unblocking slice) before implementing.

- [ ] **Representation-node type annotations** — thread the concrete head type
      onto `CCtor`/`CMatch`/`CPCtor` (and ideally `CLam`) from `Check.hs`, the way
      `CLet`/`CPi` already carry types. The minimal enabler for BOTH the Lint and
      representation selection.
- [ ] **KBackendIR slice: `INHABITANCE` + `REPRESENTATION_SELECTION`** (§34.3.1) —
      a representation-typed backend IR between KCore and the emitter; per-type
      layout/tag/rep chosen at compile time with type + inhabitance info. Subsumes
      the ad-hoc runtime `kctor` packing AND the hand-rolled `scalarPlan` worker
      analysis under one principled pass. Structural reference ONLY (never its
      detail): `../kappa/` `KBackendIR.fs` (rep-annotated nodes +
      `KBackendDataLayout`/`KBackendConstructorLayout`) + `KBackendLowering.fs`.
- [ ] **Core / KBackendIR Lint** — an independent re-checker of the typed IR.
      Would have caught the erased-type-application crash (`apply unit to unit` is
      ill-typed) at compile time; realizes "formally verified at Core level."
      Sequence: annotate nodes → Lint → niche rides on it.
- [ ] **Niche `Option<boxed>` = bare pointer + full-range `Option<Int>`**
      (LAYOUT-DESIGN classes 2 & 3 over boxed/large payloads) — the non-uniform
      layout wins; need REPRESENTATION_SELECTION + a coercion-insertion pass (box a
      niche value when it escapes into polymorphic code). DEFERRED until the slice
      exists.

---

## Track: CPS do-kernel rewrite ([`CPS-DESIGN.md`](runtime/docs/CPS-DESIGN.md))

- [x] **§3.3 suspendability analysis** (CPS-DESIGN §3.3, "Stage 1.5") — DONE: `suspenderGlobals` call-graph closure in `C.hs`; transitive user-helper forks work (`fork-transitive` case). Replace the
      flat syntactic `suspendingNames` spine-head check (`C.hs`) with a sound
      call-graph reachability analysis: a global may-suspend iff it transitively
      references a suspending primitive; conservative default = may-suspend.
      Unblocks transitive suspenders (user helpers that fork) and is the gate for
      the unboxing worker/wrapper. **Test:** a user fn that forks, used in a
      do-block, suspends correctly; a proven-pure fn stays straight-line.
- [x] **Loop family** (CPS-DESIGN §4, R5/R7/R12) — DONE (commit `67d4ce9`, merged
      `411933d`). `var`/`:=`/`while`/`break`/`continue`/`return` now CPS-lower inside
      a suspending do-block (previously fail-closed): `KVarItem`→`krt2_new_ref`+KEnv
      push, `KAssign`→`krt2_write_ref`, `KWhile`→`krt2_while`/`KK_LOOP`,
      `KBreak`/`KContinue`→`krt2_break`/`continue`, `KReturn`→`krt2_return` delimited
      by a new `OP_RETSCOPE`/`KK_RETSCOPE` frame, statement-`if` via a selector
      closure. **R7 var-read normalization** (the blocker): every var read hoists to
      a run-time `krt2_read_ref` (`OP_READ_REF`) bind with de-Bruijn shifting, so a
      re-run body re-reads the LIVE cell. Eligibility reuses the pure §3.3 witness.
      VERIFIED: corpus 82/82 interp==C==LLVM, native suite green, conformance
      1738/1738, the accept-loop / counter-fork-loop / read-after-write tests pass,
      and R12 holds (flat ~4.9 MB RSS across 10⁴–10⁶ suspending iterations = constant
      `f->k` depth). `for`/labeled loops/loop-`else`/`using`/`let?` in a suspending
      block remain fail-closed (`E_BACKEND_UNSUPPORTED`), not silently dropped.
- [ ] **`using`** (§19.5). Resource scope: acquire-bind + register `release` as a
      defer + bind the resource. (Needs the Resource-trait test surface.)
- [ ] **`return`** (§18.8). Early non-local return — needs the do-block boundary so
      `return` exits the block, not the fiber.
- [ ] **Masking surface** (§18.1.12). `mask`/`uninterruptible`/`poll` are runtime-
      only (`krt2_*`) — NOT yet exposed in the prelude. Requires prelude `prim`
      decls + interpreter handling FIRST, then the (trivial) backend wiring.
- [x] **General CPS for IO combinator expressions** (CPS-DESIGN §3.1) — DONE: a
      saturated `ioBind`/`ioThen`/`catchIO`/`finallyIO` whose body action
      may-suspend (§3.3) lowers to the CK-machine node
      (`krt2_bind`/`then`/`catch`/`finally`) in `compileAppGlob` — and in tail
      position too (`cpsNodeApp` routes around `emitTailApp`). So an
      `ioBind (await …) k` / `catchIO (join f) h` EXPRESSION (not just a `CDo`)
      drives the body through the CK-machine instead of the synchronous bridge.
- [x] **`__reraiseCause` + `join`** (§18.1.4) — DONE: `__reraiseCause` lowers to a
      new `OP_RERAISE`/`RK_RERAISE` that re-raises a full `Cause` as-is (catchable
      iff `Fail`, else propagates to `Failure(cause)`; mirrors
      `Interp.reraiseCauseValue`). With the IO-combinator lowering + result-ctor
      ids, **`join` now runs native** — success, typed-failure, and `catchIO`
      around it all ≡ interpreter (`join-success`, `join-catch` cases).
- [x] **`race`/`timeout` run native** (§18.1.6) — DONE: `__race`/`__timeout` lower
      to the `krt2_race`/`krt2_timeout` node builders (`compileAppGlob`, suspending
      per §3.3); the `Duration` constructors (`nanos`/`micros`/`millis`/`seconds`/
      `minutes`) are wired as pure prims (`kp_*` via `kp_mulInt` for big-Int
      parity). `race.kp` → `1`, `timeout.kp` → `TIMED-OUT\n42\n`, and a
      `ScopeShutdown` interrupt-cause match all ≡ interpreter (`race`, `timeout`,
      `interrupt-cause` cases).
- [x] **`withScope` / `interrupt` / `interruptFork` / `demonitor` wired** (§19.5/
      §18.1.4/§18.1.8) — `withScope`→`krt2_with_scope`, `__interruptWait`→
      `krt2_interrupt_as`, `__interruptNoWait`→`krt2_interrupt_fork_as` (nodes);
      `demonitor` a kpf no-op shim.  `scope`/`monitor`/`interrupt` conformance
      tests run native ≡ interpreter (`withscope`/`monitor`/`interrupt` cases).
- [x] **`awaitPromise` native** (§18.11) — DONE: now a `.kp` def over
      `awaitPromiseExit` (like `join`), and `awaitPromiseExit` gained a free error
      channel (`forall e a r. … -> IO r (Exit e a)`, was fixed `Void`) so the
      re-raise typechecks. `promise` runs native ≡ interpreter; full conformance
      suite (1738) still green.
- [x] **`durationCompare` + Duration/Instant arithmetic native** (§18.1) — DONE:
      `Ordering` (`LT`/`EQ`/`GT`) given fixed `KCT_` ids; `durationCompare` builds
      it; `durationAdd`/`durationSub`/`instantAdd`/`instantDiff` reuse
      `kp_addInt`/`subInt`; `nowMonotonic` a `kpf_now` clock shim. `timer-duration`
      runs native ≡ interpreter.
- [ ] **Native effects-suite — remaining gaps**:
      - `newFiberRef` + FiberRef copy-on-fork (§18.1.7). Unblocks `fiber-local`.
      - [x] **REAL STM retry/parking — DONE** (`scheduler-retry` runs native ≡
        interp, 42, cross-fiber). STM is now a real monad: prelude Functor/
        Applicative/Monad/Monoid STM + stmBind/stmPure prims; it is removed from
        the do-dispatcher carriers (`doKernelCarriers`, distinct from
        `kernelMonadCarriers` which still rejects it as an active-pattern result)
        so its do-notation desugars through `elabMonadDo`. The backend lowers
        stmBind/stmPure/newTVar/readTVar/writeTVar to the journaled `STM_*` nodes,
        `atomically` to `OP_ATOMICALLY`, and `retry` to the `STM_RETRY` node
        (`kpf_retry`); `check` is a `.kp` def. Also extended `elabMonadDo` with
        `let?` (DoLetQ → match + `empty`), a general win for all user monads.
        Full conformance suite (1738) + native suite (61) + stm-tvar green.
      - **`bracket` finalizer-on-interrupt** — TWO causes, one fixed:
        1. [x] §3.3 HIGHER-ORDER: `bracketM = ioBind acquire (\r -> finallyIO
           (use r) …)` suspends through the `use`/`acquire` PARAMETERS (CVars), so
           the old `spineHeadSuspends` gate kept the combinators on the legacy
           bridge. FIXED: `mayActSuspend` also CPS-lowers a combinator whose action
           is parameter-headed (`spineHeadIsLocal`) — bracketM now uses
           `krt2_finally` (verified). Regression-free (full native suite + effects
           sweep clean). REMAINING: a §3.3 SEED extension to also mark such
           higher-order globals may-suspend (so a NON-forked `r <- bracket …` is
           CPS at the call site too — forked uses already work via the fiber).
        2. [ ] MASKING SURFACE (§18.1.12): even with (1), the release is skipped
           because the fiber is BORN-INTERRUPTED — native delivers a pending
           interrupt at the fiber's first step (`rt.c` fiber_step), before the
           acquire registers the finalizer. ZIO/bracket semantics require the
           acquire to be UNINTERRUPTIBLE; the interpreter only gets away without a
           mask via GHC's lenient async-exception timing. Fix = expose
           `uninterruptibleMask` (the runtime `krt2_uninterruptible` exists) in the
           prelude + interp and wrap bracketM's acquire — a distinct piece.
- [x] **Native result-ctor matching — COMPLETE** (§28 shapes) — every runtime-built
      result ctor now carries a FIXED `KCT_*` id shared with codegen
      (`builtinCtorTag`): `Exit`/`Cause`/`Option` (done earlier) PLUS the
      dynamic-named `RaceOutcome` (`ROLeft`/`RORight`), `TimeoutOutcome`
      (`TOTimedOut`/`TOExit`), and `InterruptCause`/`InterruptTag`
      (`MkInterruptCause`/`Requested`/`ScopeShutdown`/`TimedOut`/…).  Zero ctors
      remain on `KCT_OTHER`; the divergent duplicate `interrupt_cause` (rt.c vs
      scope.c) is consolidated and the dead `ctor1`/`ctor2` removed.
- [ ] **`atomically`/`retry` real parking** (§18.1.13). Switch the single-agent
      `Ref` STM shim to the journaled `krt2_atomically`/`OP_ATOMICALLY` so
      transactions park + retry across fibers ([`../stm.c`](runtime/stm.c) already implements it).
- [ ] **Stage 4 — effect-handler unification** (CPS-DESIGN §2, Stage 4). One
      `KK_HANDLER` prompt frame; `perform`/`resume` reuse `deliver`/`unwind`.
      Depends on R1 (done). `rt-multishot` behind the compile-time escape-check.
- [ ] **Stage 5 — LLVM coroutines** (CPS-DESIGN §5). Retarget `kdo_*`/`kdok_*` to
      `coro.id.retcon.once`; seed `CoroSplit` liveness from the `KEnv`.

---

## Track: Value unboxing ([`UNBOXING-DESIGN.md`](runtime/docs/UNBOXING-DESIGN.md))

- [~] **Stage 0 — GC/alignment contract + canonical encoding** (UNBOXING §5.2/§5.4/§7).
      GC/alignment **CONTRACT now ENFORCED in the runtime** (`krt_init`, kappart.c):
      `GC_set_all_interior_pointers(0)` *before* `GC_INIT` (Boehm roots only BASE
      pointers, so a tagged odd word is a non-pointer, not a false interior root);
      a startup `krt_assert_gc_alignment` (sampled `GC_MALLOC` all 8-aligned,
      fail-closed); `_Static_assert(_Alignof(max_align_t) >= 8)`. The **low-3-bit
      tag budget is reserved + documented** (`b000` ptr / `b001` imm-Int / `b010`
      imm-ctor / `b011..` Perceus) with the `kis_imm`/`kderef`/`kimm_payload`
      discriminator API in `kappart.h` — a debug `kderef` assert pins "no immediate
      yet (every value is a b000 pointer)" ahead of the Stage-1 deref audit.
      VERIFIED safe under heavy collection: **corpus 81/81**, a 1M-cons-cell
      **251-collection GC stress** (interp == C == LLVM, correct), full native suite
      green. **Stage-0 BENCHES LANDED** (`bench/rt_bench.c` rows 3, 6–10 + the
      `bench/README.md` baseline table, `make bench`): boxed `addDouble` (the F64
      boxing cost, 48 B/op → 0 unboxed), `ctor-build` (n-ary, 112 B/op — control) + `ctor0-build`
      (nullary `None`, 48 B/op — the immediate WIN that should drop to 0), `ctor
      deref boxed` + `ctor0 dispatch` (the tag-test tax/win = the go/no-go gate),
      and a sum-checked `scalar across a park` (1184 B/op, asserts the carried Int
      survives) — bytes/op bit-identical across runs. **REMAINING:** canonicalize
      `kbool`/`kunit`/`kint`/nullary-ctor encoding to a single form, which folds
      into the Stage-1 deref audit.
- [~] **Stage 1 — immediate tagging** (UNBOXING §1/§5/§7). **Immediate INT (b001)
      DONE** (commit `a074259`, merged `4cdd181`): a small Int rides the `KValue*`
      word as `(value<<3)|b001`, a 61-bit signed immediate (the **3-bit** tag of
      `docs/TAGGING-RESEARCH.md`, not the original `(i<<1)|1`); out-of-range escapes
      to boxed `K_BIGINT`; `kint()` canonical (`kint_cache` retired as a carrier,
      §5.2); `kp_*Int` + compares tag-test with `__builtin_*_overflow`->GMP +
      canonical reduce-to-inline; Int eq/match normalizes across inline/bignum
      (`kint_cmp`, never `klit_eq`'s tag shortcut, §5.3); the ~299-site
      `->tag`/`->as.*` deref audit routes through `kis_imm`/`kderef` (the debug
      assert stayed live and never fired). VERIFIED: **corpus 82/82**
      interp==C==LLVM (incl. the §5.3 boundary test at 2^60), full native suite
      green, **boxed `addInt` 48 -> 0 B/op** (the ~50x allocation lever; `ctor-build`
      112 -> 64 B as its `kint` head is now immediate too), the go/no-go ctor-deref
      tax flat in isolation. **REMAINING:** the secondary `b010` immediate-CTOR
      (`Bool`/`Unit`/`Nil`/`None` -> 0-alloc; `ctor0-build` 48 -> 0) deferred.
- [ ] **Stage 1.5** = the §3.3 analysis above (shared).
- [ ] **Stage 2 — worker/wrapper specialization** (UNBOXING §1/§7). Generalize
      `scalarPlan`/`kwi_`/`kwd_` to a layout kind (`Boxed|I64|F64|FixedFFI`) on Core
      types; one unboxed worker per class, boxed `kw_g` as the reference, the
      `kunbox_*`/`*ovf` escape as the floor. Unboxes `Double`/wide-FFI/fused hot
      paths. **Blocked on §3.3** (Stage 2a re-proves suspension-freedom).

---

## Track: Missing primitives ([`PRIMITIVES.md`](runtime/docs/PRIMITIVES.md))

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

## Track: Performance ([`bench/README.md`](runtime/bench/README.md))

- [ ] **Fiber/continuation pooling** — the fork path allocates 832 B/op
      (`sizeof(Fiber)=200`, ~64 of which is the per-fiber `pthread_mutex`).
      Lighter sync + a free-list (careful with the conservative GC + the
      await/exit lifetime).
- [ ] **Perceus precise RC** (CPS-DESIGN §5) — non-atomic for thread-local `f->k`;
      turns the per-bind/continuation allocation into a reuse/in-place write.
      The endgame for the suspension path; needs the §3.3/unboxing ptr-vs-scalar map.
- [ ] Keep `make bench` green as a non-regression gate from each stage.

---

## Track: Spec coverage — not-yet-implemented surfaces (to be populated)

To make this roadmap hold *all* the tasks, the remaining work is a survey of
[`docs/Spec.md`](docs/Spec.md) against kappa-haskell's implementation status.
**Next planning step: run that survey and fold the missing tracks here in
dependency order.** Areas to assess (done / partial / missing), each against its
spec section + the corresponding source:

- §11 universes / classifiers / rows / **propositions** (`IsProp`/`RuntimeErased`);
  §12 quantities / borrow / erasure justifications; §13 sealed packages /
  signatures / existentials; §14 traits / coherence / **specialization** (ties to
  the IR-pipeline track); §15 termination / refinement evidence; §16 implicits /
  closure capture; §17 match / refinement / erased scrutinees; §19 resources /
  scopes (`using`); §20 queries / collection lowering; §21–23 metaprogramming /
  quotes / reflection; §26–27 native / capabilities / FFI / bridge contracts;
  §28 effectful traversal; §29 std.atomic / supervisor; §30 KCore surfaces; §31
  erasure; §33 gradual / `DynRep`; §34 compilation / IRs / tooling / backends.
- Cross-cutting: the diagnostic catalogue (the `E_*` codes) — which are emitted
  vs missing — is a concrete coverage signal worth a pass of its own.
