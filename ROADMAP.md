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
- [`SPECIALIZATION-SCOPING.md`](docs/SPECIALIZATION-SCOPING.md) — scoping of a monomorphization/specialization pass; **verdict: not worth it** (the static niche needs whole-program mono, which §8.3 separate-compilation forbids; the already-shipped uniform wins + Perceus RC are the better levers).
- [`CPS-DESIGN.md`](runtime/docs/CPS-DESIGN.md) — the do-kernel CPS / continuation rewrite (Stages 0–5, R1–R15).
- [`PRIMITIVES.md`](runtime/docs/PRIMITIVES.md) — the ADD/DERIVE/SKIP analysis of missing concurrency primitives.
- [`COVERAGE.md`](runtime/docs/COVERAGE.md) — ZIO/Cats-Effect combinator coverage.
- [`DESIGN.md`](runtime/docs/DESIGN.md) / [`REVIEW.md`](runtime/docs/REVIEW.md) / [`RESEARCH.md`](runtime/docs/RESEARCH.md) — the original runtime architecture + 8-lens review.
- [`bench/README.md`](runtime/bench/README.md) — the perf baseline (`make bench`); the numbers that gate the perf work.
- [`SPEC_COMPLIANCE.md`](SPEC_COMPLIANCE.md) — the spec-conformance gap list (single source of truth; see the Spec-coverage track), backed by [`docs/audit/`](docs/audit) (probe-audits) + [`docs/digests/`](docs/digests) (per-§ digests) + [`docs/notes/KNOWN_SPEC_ISSUES.md`](docs/notes/KNOWN_SPEC_ISSUES.md).
- [`TESTING_STRATEGY.md`](docs/TESTING_STRATEGY.md) — testing & verification
  strategy: independent oracles (imported elpi/cross-language corpora, F#↔Haskell +
  backend differential, generative fuzzing, internal property/subject-reduction
  checks); see the Testing track.
- Native backend: [`NATIVE_BACKEND.md`](docs/NATIVE_BACKEND.md), [`LLVM-BACKEND.md`](runtime/docs/LLVM-BACKEND.md), [`NATIVE_FFI_DESIGN.md`](docs/NATIVE_FFI_DESIGN.md), [`NATIVE_BACKEND_OPTIMIZATION_GUIDE.md`](docs/NATIVE_BACKEND_OPTIMIZATION_GUIDE.md).

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
5. [x] **Scalar Double worker** (UNBOXING §7 Stage 1.5 + 2b) — DONE. The per-binding transitive may-suspend witness (`scalarBodyMaySuspend`, proven load-bearing — a C-local `double` is lost across a fiber park) gates the `kwd_` Double worker; FP pinned (`-ffp-contract=off -fno-fast-math`) so results are bit-identical to interp. A fused Double loop is 0 B/op. (Surfaced a pre-existing `kp_showDouble` last-digit printer bug, flagged separately.)
6. [x] **KBackendIR slice — typed annotations + Lint + inhabitance + rep table + verifier** (§34.3) — **the architecture investment, LARGELY DONE.** Stages 0–3 landed: typed-Core head annotations + observe-only `CoreLint.hs` (Stage 0), the §30.2.7 `Inhabitance.hs` query (Stage 1), the shared `Backend/Repr.hs` rep/layout table + `repSelect` rep-plan authority (Stages 2–3), and the user-invokable §34.3.3 legality verifier (`kappa verify-kbackendir`). The erasure-bug class is now caught at compile time; rep selection is identity-keyed (§1.2). See the **Compiler IR pipeline track** for the per-stage detail. (Full §34.3.3 error-promotion + the runtime-profile checkpoints remain.)
7. [ ] **Niche / full-range non-uniform layout — DEFERRED (architectural mismatch with type erasure).** The headline type-directed layout wins, BUT Kappa erases types (no monomorphization), so a niche value needs coercions at every erased-type boundary (pervasive) and the win is mostly eroded — revisit only alongside specialization/monomorphization. See the IR-pipeline track's Stage 4 + the `niche-layout-vs-type-erasure` analysis.
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

**Staged plan** (scoped 2026-06-26; §34.3's "observationally equivalent" clause
means we need NOT materialize a distinct KBackendIR datatype — only behave as-if,
so this is a *verifier + rep-table over the existing pipeline*, NOT a big-bang IR
rewrite. Each stage stays interp==C==LLVM byte-identical until the niche). The
ONE ordering constraint: typed-Core head annotations are the keystone — niche AND
the real Lint are both impossible without them.

- [x] **Stage 0 — typed-Core head annotations + observe-only Lint. DONE** (merged
      `6315758`). `CMatch`/`CCtor` carry an optional head-type field, threaded from
      `Check.hs`; observe-only (`Eq Term` ignores it, backends don't read it) →
      parity byte-identical 104/104. The `CoreLint.hs` Lint warns
      `W_BACKENDIR_NON_FUNCTION_HEAD` — clean on the whole corpus, catches the
      `kapp(unit,…)` miscompile class at compile time. The keystone for the rest.
- [x] **Stage 1 — §30.2.7 inhabitance query. DONE** (merged `63400fb`; `Inhabitance.hs`).
      Soundness hardened across 3 adversarial sweeps — a rigid-index hole, a
      pre-existing existential-index hole, and a de Bruijn miscompile (all caught +
      fixed: `a7fa3b1`, `60b81bd`, `aa5af7c`; conformance 1738→1755). It generalizes
      `scrutineeEmpty` (`Check.hs:8276`) into the
      terminating structural `InhabitanceSummary = Empty | Subsingleton |
      Contractible | Finite n | Unknown`, keyed by `InhabitancePurpose` (Stage 1
      uses only SourceReachability; Stage 4 uses RuntimeShape — they MUST NOT
      cross). Closes the SPEC_COMPLIANCE §30.2.7 gap + unblocks `case
      impossible`/§17.1.4. **Reference:** `../datatron/app-type-counting` (+ the
      `fp-counting-type-inhabitants` article) is a COMPLETE exact inhabitant-counter
      (`Cardinality` Finite|Infinite, `Series` generating functions, a solver,
      parametricity) — *too much* for this conservative MUST (keep `Unknown`); but
      it is THE reference for a future PRECISE Optimization-purpose summary
      (recursive-type cardinality → tighter layouts in Stage 4+).
- [x] **Stage 2 — shared compile-time rep/layout table. DONE** (merged `2782abf`;
      pure `Backend/Repr.hs`). `Rep`/`scalarRep` (the runtime-rep discriminator,
      ex-`scalarHeadKindV`) + `CtorLayout`/`ctorLayout` (nullary⇒immediate `b010`,
      1–2 immediate fields⇒`LayoutMayPack` b011, else boxed) + `tagId`/
      `assignUserCtorTags` (THE `KCT_USER_BASE+i` numbering authority). C+LLVM now
      consult it → agree on tag ids + marshalling by construction; proven
      byte-identical (generated `.c`+`.ll` for 3 ADTs identical, parity 104,
      conformance 1755). `LayoutMayPack` is defined-but-unconsumed — the Stage 4
      seed. NOT per-node decoration (the reference's short-sighted, unused part).
      *Residual:* the C-only scalar-**worker** marshalling stays in `C.hs` (not
      cross-backend duplication; `scalarRep` already centralizes its discriminator).
- [x] **Stage 3 — §34.3.3 legality verifier + `scalarPlan` unification. DONE**
      (hard). **Verifier landed** (merged `b6cbb0b`; `Backend/Verify.hs`,
      user-invokable `kappa verify-kbackendir [--json] FILE`, observe-only). Checks
      the three currently-relevant §34.3.3 checkpoints: erasure-legality (generalizes
      Stage 0's non-function-head + erased-type-form-in-runtime-slot, dual of
      `erasedSpinePositionsP`), fixed runtime arity (`CCtor` vs `runtimeField`), and
      layout-consistency vs `Repr` (tag-id injectivity + `ciData` back-pointer). 1199
      programs verify clean / 0 false positives; catches `W_BACKENDIR_NON_FUNCTION_HEAD`
      / `_ERASED_REFERENCE` / `_ARITY_MISMATCH` / `_LAYOUT_INCONSISTENT`.
      **`scalarPlan` unification landed** (merged `12de5d0`): `Repr.repSelect` is the
      rep-plan authority (`EvalCtx -> Value -> Maybe ([Rep], Rep)`); `typeScalarKinds`
      derives its `ParamKind`/`ScalarKind` from it; proven byte-identical (the
      `kwd_`/`kwi_`/`kwm_` worker codegen unchanged, native perf gates green).
      Deferred: the runtime-profile checkpoints (handlers/fibers/atomics/multishot/
      §34.3.9/.11) + error-promotion + the §34.3.6 interpreter gate.
      *NB:* Stage 2's `Repr.scalarRep` keyed on `gKey` (qualified) not the bare type
      name — regressed the Int/Double scalar workers to boxing; fixed `f9e0bf4`
      (caught by `run-native-tests.sh` perf gates, invisible to `llvm-parity`).
      Then made principled in `c776a9c`: classify by **declaration-symbol IDENTITY**
      (`GName` equality vs the canonical prelude globals), not a spelling string —
      §1.2 "a resolved reference MUST NOT target a spelling string" (a user type
      spelling `Double` in another module now stays boxed; unit-pinned). A §1.2 audit
      of `C.hs`/`LLVM.hs` then caught the same smell in `runIOSplice`/`runIOSpliceLL`
      (they matched the bare name `"__runIO"`) — fixed `ef6987b` to compare
      `g == prelRunIO`; the rest of the backend's string uses (mangling, diagnostics,
      module-gated prim tables) were reviewed and cleared.
- [ ] **Stage 4 — niche layout + coercion pass. DEFERRED — architectural mismatch
      with type erasure.** A bare-pointer niche (None=null, Some x=x) for ANY
      niche-able ADT *shape* (k nullary ctors + one ctor wrapping a niche-having
      field — shape-based, NEVER `Option`-by-name, per §1.2). **Why deferred:** Kappa
      is `RuntimeErased` — `Option Foo` and `Option a` share ONE runtime body (no
      monomorphization), so the runtime cannot distinguish a niche-able instance from
      a generic one. The niche then needs coercions at every erased-type boundary
      (pervasive), and even the universal `None=0` trick (immediate-tagging makes
      every `Some` payload non-zero) dies on nested `Option<Option<_>>`. Net: the
      highest-complexity / miscompile-risk stage (no byte-identical net) for a payoff
      mostly eroded by erasure — it survives only for short-lived concrete
      `Some<boxed>` that never escapes to polymorphic code. Revisit ONLY alongside
      specialization/monomorphization, or a type-directed LLVM layout. **§21.6
      semantic reflection** still reuses the typed-Core foundation (Stage 0)
      independent of the niche. (Analysis: 2026-06-26; see the
      `niche-layout-vs-type-erasure` memory.)

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
- [x] **Masking surface** (§18.1.12). DONE (merged `e1a1482`). `uninterruptible`/
      `mask`/`poll` (+ `__mask`/`__restore`) exposed in the prelude, handled in the
      interpreter (per-fiber restore stack), and lowered to `krt2_mask`/
      `krt2_uninterruptible`/`krt2_poll` in C + LLVM — all agree interp==C==LLVM
      (`masking.kp`). **`bracketM` now masks acquire+register**, closing the
      bracket-on-interrupt common case (release RUNS on interrupt; `bracket-mask-
      interrupt.kp`, load-bearing). *Two caveats tracked:* (a) `restore` is rank-1
      (`IO e a -> IO e a`) not the spec's rank-2 `forall x.` — the runtime restore
      closure is monomorphic, and rank-2 emits an erased type-application it consumes
      as the action; spec-exact rank-2 needs a runtime change. (b) the synchronous
      `krun_io`/`krt2_run_op_sync` bridge still can't drive `OP_MASK` for `bracketM`
      reached as a bare `K_BOUNCE` worker behind the `MonadResource` dict (born-
      interrupt can still skip release on C) — needs the deferred do-kernel CPS Stage 2/3.
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

## Track: Spec coverage ([`SPEC_COMPLIANCE.md`](SPEC_COMPLIANCE.md))

[`SPEC_COMPLIANCE.md`](SPEC_COMPLIANCE.md) is the DETAILED single source of truth
for "remaining work to 100% conformance with [`docs/Spec.md`](docs/Spec.md)" —
structured by area with `file:line` fix loci, backed by the hostile probe-audits
in [`docs/audit/`](docs/audit) and the per-§ digests in
[`docs/digests/`](docs/digests); known issues in
[`docs/notes/KNOWN_SPEC_ISSUES.md`](docs/notes/KNOWN_SPEC_ISSUES.md). This roadmap
**references** it rather than duplicating the list. **STALE:** it states
`1334/1334` (2026-06-23); current is **1738/1738** → needs a status refresh + a
per-gap re-verify (some may have closed).

Buckets (SPEC_COMPLIANCE §Status-at-a-glance): **29 core MUST gaps** (§1), 12
SHOULD (§2), 22 profile-scoped (§3), 1 MAY (§4), ~6 open questions (§5).
Soundness (§1.1) is fully RESOLVED. The core gaps that CROSS-CUT this roadmap's
other tracks (do them THERE, not as separate items):

- **§30.2.7 inhabitance-summary query** (§1.2, large) — IS the `INHABITANCE`
  lowering stage; build it in the **IR-pipeline track** (also unblocks §17.1.4
  `impossible`).
- **§21.6 semantic-reflection tier** (`asCore`/`reifyCore`/…) + §21.5
  quotation-pattern matching (§1.5, large) — need "a faithful runtime Core
  representation carrying QTT/scope evidence" → the **typed-Core / Lint** work in
  the IR-pipeline track.
- **§19.5 borrow-correct `bracket`** + **§32.2.19-21 Eff-typed do-blocks**
  (`defer`/`using`/`var`/loop) + **§28.2 `mask`/`poll`/`uninterruptible`/
  `ensuring`** (§1.3-1.4) — the **CPS track** (the bracket + masking-surface items).

Self-contained spec-coverage items (no other track; pull into dated tasks here as
scheduled): the rest of §1.2 (§11.4.2 bool→type coercion, §16.3.2 named holes,
§16.4.1-2 flow-refinement exhaustiveness + `not`-refinement), §1.4 prelude surface
(fiber-id terms, `and`/`or`/`force` as values, `DefectTag`/`DefectInfo`/
`InterruptCause` shapes, the row/var/eff solver traits), §1.5 `std.deriving.shape`,
§1.6 §3.1.7 repair-ranking. Refresh step: re-verify SPEC_COMPLIANCE's §1 gaps vs
current code + the `E_*` diagnostic-catalogue coverage.

### Known issues (not spec gaps, but tracked)

- [x] **`kp_showDouble` + `kp_intToDouble` now match the interpreter EXACTLY**
      (commit `5736f31`, merged `3178f72`). `show_double` ports GHC's
      `floatToDigits`/Dragon4 via GMP (the exact algorithm `show` uses);
      `kp_intToDouble` does IEEE round-to-nearest-even (was truncating via
      `mpz_get_d`). Verified against a GHC oracle over ~276k cases (incl. 10,944
      exact-tie integers, bignums to 2^1000), zero mismatches; corpus 104,
      conformance 1738.

---

## Track: Testing & verification strategies ([`TESTING_STRATEGY.md`](docs/TESTING_STRATEGY.md))

The path from "the conformance suite passes" to **high assurance the compiler is
correct**: many *independent oracles*, so a bug must fool all of them to survive.
[`docs/TESTING_STRATEGY.md`](docs/TESTING_STRATEGY.md) is the detailed write-up
(mechanism, deps, effort, source paths); this track is the worklist. The enabler is
that the `--!` Appendix-T format is **shared** with the reference impl and the CLI
emits `--json` portable-code diagnostics, so generated/imported fixtures drop in and
two implementations compare on a stable key. Three strategies port from
`../kappa/`; the rest are new.

**Now — cheap, all differential (do first):**
- [x] **Coverage-selected elpi import — DONE** (2026-06-26;
      [`tests/conformance/elpi-generated/`](tests/conformance/elpi-generated)). Ran the
      5,000 read-only: **1,821 pass**; rather than bulk-import the repetitive corpus,
      HPC greedy set-cover picked the **13** that add the entire +0.16% new
      compiler coverage (the other 1,808 are redundant) — gate 1781→1794, all pass,
      runnable ones `interp==C==LLVM`. Method + run log in
      [`TESTING_STRATEGY.md`](docs/TESTING_STRATEGY.md). **Key finding:** the 3,179
      failures collapse to one real gap — **block-local declarations** (nested-`block`
      layout + local `trait`/`instance`/`effect`/`summon`); a candidate spec-coverage
      task, not test noise.
- [x] **Coverage-driven new tests + dedup — DONE** (2026-06-26;
      [`TESTING_STRATEGY.md`](docs/TESTING_STRATEGY.md) §coverage-driven). (A) Crafted
      + independently verified **52 negative tests** for previously-untested
      diagnostics →
      [`tests/conformance/diagnostics-coverage/`](tests/conformance/diagnostics-coverage),
      **+0.36% compiler coverage** (558 boxes, ~83% `Kappa.Check` error paths), gate
      1794→1849. (B) Coverage-signature dedup found **87 strong-duplicate clusters**
      (55 byte-identical exact-copies naive dedup catches; **32 textually-differ-but-
      coverage+assertion-identical that naive dedup misses**; 6 distinct-contract →
      keep) — review candidates, not auto-deleted.
- [ ] **Land `tests/pending-import/391`** (OracleImport cross-language corpus: Kotlin
      `codegen/box`, Scala 3 `patmat`, harvested from `../datatron/`) + copy any fresh
      oracle `.kp`. Real-world regression behavior the synthetic generators miss. ~1–2h.
- [ ] **F#↔Haskell differential** ⭐ — a wrapper running every shared `.kp` through
      both `kappa` binaries, comparing portable §3.1.4 codes (the `portableAlias`
      table in [`Diagnostic.hs`](src/Kappa/Diagnostic.hs)) + run stdout/exit, with a
      small known-divergence allowlist. Two mature impls cross-check; pairs with every
      generator. ~1 day.

**Force-multiplier — generative fuzzing:**
- [ ] **Port the fuzzer** (`../kappa/scripts/kappa_fuzz*.py`, ≈4400 LOC, mostly
      compiler-agnostic): rewire the CLI path + backend names to our `kappa` +
      `interp/C/LLVM` (the parity harness IS its oracle); reuse the
      `ddmin`-minimize / trace-cluster / promote pipeline (`bounded_run.py`,
      `triage_pending.py`) as-is. Has caught real crashes/timeouts/backend-mismatches
      on the reference. ~1–2 days.
- [ ] **Retraining & generator variants** — (a) **auto-retrain on training-data
      change** (hash the corpus, retrain when it changes; training is fast, so do it
      often); (b) try a **transformer/LLM-style generator** instead of the char-LSTM
      (better long-range structure for dependent+effect code); (c) add a
      **grammar/type-directed generator as a *separate, parallel* fuzzer** (different
      bias, different bugs, no PyTorch dep) — *the more the merrier*, both feed the
      same oracle + promote loop.

**Internal, always-on (no external deps):**
- [ ] **Type-preservation / KCore subject-reduction** — extend the §34.3.3 legality
      verifier ([`Backend/Verify.hs`](src/Kappa/Backend/Verify.hs)) toward "each
      lowering/reduction preserves KCore types". The architecture work doubles as a
      testing strategy; highest-leverage internal oracle. (Cross-cuts the IR-pipeline track.)
- [ ] **Metamorphic testing** — semantics-preserving transforms (α-rename, η-expand,
      let-inline, reorder independent binds, dead-code insert, redundant annotations)
      must not change typeability/output. The program is its own oracle.
- [ ] **Property-based / typed-term generation (Hedgehog)** — in-process type-directed
      generator checking invariants: total ⇒ terminates, well-typed ⇒ accepted, no
      crash on any well-formed AST, interp ≡ compiled. Integrates into `cabal test`.
- [ ] **Roundtrip / idempotence** — `parse ∘ print = id`; `normalize` is a fixpoint.
      Cheap; catches parser/printer + normalization asymmetries.

**Later / research:**
- [ ] **Mutation testing** — mutate the compiler, confirm a test fails; measures
      corpus thinness. Most useful once the corpora above are large.
- [ ] **Port the elpi generator** (vendor `kappa_generator.elpi` + Elpi opam dep +
      `kappa_lp_generate.py`, validate against our binary) for fresh/deeper synthesis
      as we add features. ~1–2 days. (Only needed beyond the committed 5,000.)
- [ ] **Port the OracleImport importer** to Haskell (`aeson` + `regex-tdfa`) for live
      corpus refresh as upstream suites grow. ~4–8h. (Optional — the `.kp` outputs
      already drop in; the importer only matters for staying in sync.)
- [ ] **Elpi as a *live* checker oracle** (DEFERRED — large) — extend the λProlog
      judgment to *classify arbitrary* programs (accept/reject), adjudicating fuzzer
      output (oracle-rejects + compiler-accepts = soundness bug). This is ≈writing a
      second complete independent type checker, so deferred until the cheaper oracles
      are exhausted; synthesis (#1) already gives most of the value.
