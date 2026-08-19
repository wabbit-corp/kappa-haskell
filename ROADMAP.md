# Kappa Roadmap — the grand plan

The single ordered plan for the **kappa-haskell** compiler + runtime, so work
does not scatter across 20 directions. Each item links to the design doc (and
spec section) that specifies it, and to the measurement that gates it where one
exists. This started life as the runtime-only roadmap and is being grown to
cover the whole implementation (front end, IRs, backend, runtime, spec gaps).

**Two implementations** — keep them straight:
- **kappa-haskell** (this repo) — the native (C + LLVM) compiler + the kappart2
  runtime. The one we are building. Since S5.A it materializes and validates a
  native `KBackendIR` tree for backend value/do lowering, while older planning
  and a few backend analyses still read KCore where explicitly called out (see
  the IR-pipeline and Perceus S5 tracks).
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
- [`UNIVERSES-PLAN.md`](docs/UNIVERSES-PLAN.md) — implementation plan for the §11.1/§11.3/§10.4.1
  universe redesign (`TypeLevel` algebra incl. `ω`, stable first-class level terms, explicit/
  inferred universe schemas, portable solver outcomes, rigid declaration generalization,
  parametric witness packages, recursive schemas, certified nominal-family variance, explicit
  `schemaLift`, arithmetic certificates, and versioned KCoreText); closes KNOWN_SPEC_ISSUES
  §16/§17.
- [`NAT-FIN-REFINEMENT-PLAN.md`](docs/NAT-FIN-REFINEMENT-PLAN.md) — staged implementation
  plan for logical `Nat`, checked no-confusion/derivation, proof-producing value arithmetic,
  `Fin`, `Refined`, symbolic cardinality, replayable representation certificates, and required
  backend representation profiles.
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
- Native backend: [`NATIVE_BACKEND.md`](docs/NATIVE_BACKEND.md), [`LLVM-BACKEND.md`](runtime/docs/LLVM-BACKEND.md), [`NATIVE_FFI_DESIGN.md`](docs/NATIVE_FFI_DESIGN.md), [`NATIVE_BACKEND_OPTIMIZATION_GUIDE.md`](docs/NATIVE_BACKEND_OPTIMIZATION_GUIDE.md), [`scalarization_review.md`](docs/scalarization_review.md) (evidence-aware IO/`var` scalarization roadmap).

---

## Recent progress — Session 2026-06-27 (runtime + compiler burst)

A large correctness + perf burst landed on `main`, each piece independently gated AND
adversarially reviewed. The reviews caught **5 serious bugs past green gates** (a daemon
hang, a drain leak, a responsiveness regression, a drain-state hang, an abandonment
FOREIGN-terminal hang) — the adversarial-review-every-merge discipline paid for itself.

**Landed + verified:**
- **Abandonment** (§32.2.12/.20/.21) — C2 cause composition, the cause-shape asymmetry, the
  perform-during-drain residual, and the FOREIGN-terminal hang regression.
- **Masking** — rank-2 `restore` (§18.1.12, scoped `__restoreAt` adapter; [`MASKING-RANK-RATIONALE.md`](docs/MASKING-RANK-RATIONALE.md)) + masked-sleep suppression (§32.2.5).
- **Daemon teardown** (§32.2.3) — the hang regression (bounded best-effort drain) + the D1
  drain-window ordering leak.
- **Interrupt delivery** — orphan sleep-timer (reactor-owned cancel + full-duration re-park)
  + **safe-points (§32.2.6)** — `krt2_safepoint` made real + emitted on loop back-edges across
  C/LLVM/interp; a tight CPU loop is interruptible now; no scalar perf regression.
- **std.atomic** (§29.1) — boxed mutex-protected atomic cells, proven exact under an N×M race.
- **delve renders on C** + `restore`-over-suspending-do-block — both the sync-bridge `OP_*`
  gap (`finallyIO`/`catchIO`/`OP_RESTORE` returned unrun; fixed in `C.hs suspendingNames`).
- **Runtime split** (`kappart.h` plus cohesive value/gc/prims/scheduler TUs, `-flto`) + synchronous bridge fixes for curried IO values.
- **LLVM Int while-loop scalar-unboxing** — sumloop ~1195× → C parity.
- **Cross-language benchmark suite** ([`bench/xlang`](bench/xlang), `make xbench`, [`CROSS-LANGUAGE-BENCHMARKING.md`](docs/CROSS-LANGUAGE-BENCHMARKING.md)) — 13 CLBG/Savina ports; concurrency runs the full suite correct + byte-identical to Go/GHC (the alloc-lever multiplier is not a model defect).

**Current open items (folded into the tracks below):** the completed June items formerly listed here
are now recorded in the landed section below: LLVM curried CK-machine prims, let-blind/function
scalar workers, FP/sqrt/transcendental + fixed-precision formatting, boxed `MutArray` Stage A,
fiber identity, std.atomic, and several CPS/runtime edges have landed. The remaining active items are
the explicit OPEN entries in the prioritized list: evidence-aware IO/`var` scalarization (P0.2
restore after S2.3b), `MutArray` element unboxing and related array specialization, selected
C-backend CPS edge cases, the `kctor` value-box multi-worker race, native harness
concurrency-safety, remaining runtime spec-coverage stubs, and the Perceus precise-RC follow-up
stages.

---

## Next up — prioritized execution order

The forward plan (Session 2026-06-27), in priority order. Disjoint items run in parallel
(worktree-isolated); same-file items are sequenced to avoid merge churn. Each lands gated +
adversarially reviewed, same discipline as the burst above.

**✅ Landed (2026-06-28) — main `6756af1`, conformance 1916/0, parity 121/0:** Monoid
lawful-by-default + `Pointed` for IO/STM (`5efbe3d`, #9); IO `MutArray` boxed (`e4f3378`, #2; unboxing
deferred); `disconnect` (`8ea9f58`, PRIMITIVES #5); LLVM function scalar-worker (`555f50b`, #5); P1
inhabitance/UIP suite (`93fbccf`, #7); runtime bugs — sleepFor-nonpositive + fiberId/currentFiberId
(`339b8f7`, #4); the native backend now erases proof-typed defs (`b917f73` — the proper proof-system
completion that lawful-by-default exposed); `__arrayIndexUnsafe` de-Bruijn fix (`07cda19`). Foundations
earlier this session: IsProp-under-Π soundness + honest List proofs (`d45480f`, 4 holes closed under a
6-review audit), or-pattern existential fix (`b846acb`).

**✅ Landed (`6756af1`) — unsafe-intrinsics gate + the `!e` desugaring fix:** the raw-admit intrinsics
(`__eqProof`/`__transport`/`__absurd`/`__handleEff`/`__debugInspect`/`__debugCompare`/`__unsafeAssertProof`/
`failNow`/`__arrayIndexUnsafe`) are restricted to `@AllowUnsafeIntrinsics` modules — closing a
CRITICAL pre-existing TOTAL unsoundness (any module could `let bogus : (=) True False = __eqProof` → `Void`).
The decisive find: the `!e` bang-splice was desugaring to a pure extraction; per **Spec §18.3.1** it
must be a monadic **bind** (`tmp <- x; f tmp`) — fixing the desugaring closed both extraction forges + a
backtick-spellable sentinel bypass at the root, and a sibling pure-result-`do` extraction was closed too.
~10 holes found + closed across multi-model adversarial review (Claude workflows + Codex xhigh). Lesson
logged: read the **spec** first, not the buggy code. Conformance 1916/1916, parity 121/0.

1. **Numeric prims — FP/sqrt/transcendental + fixed-precision Double formatting** — ✅ **DONE**
   (merged `6ae3ff4`). libm math fns + `%.*f` formatting as ordinary prims (both backends + interp);
   **nbody + spectralnorm byte-identical to the reference**, parity 115/0.
2. **Mutable O(1) array** — ✅ **Stage A DONE** (`e4f3378`): IO `MutArray` (boxed), one `K_ARRAY` object with
   the `elemkind`/`element_size` unboxing seam, 3-tier total indexing; design [MUTABLE-ARRAY-DESIGN.md](runtime/docs/MUTABLE-ARRAY-DESIGN.md).
   **OPEN — Stages B→H (element unboxing):** the backend specializes array ops at the call site *pre-erasure*
   via `Repr.scalarRep` to pick unboxed `double[]`/`int64[]` slabs (atomic-GC'd, no per-element box) for
   monomorphic scalar elements, boxed `KValue*[]` otherwise (runtime tag-sniffing is unsound — `Array (Maybe
   Int)` mixes word kinds). Couples with the value-unboxing lever (#5). ST `runST`/`STArray` §18.6.4 and
   linear `LinArray` also deferred (the boxed/Boehm runtime can't witness uniqueness yet).
3. **Unlock more benchmarks** — ✅ **DONE** (`5a96969`): the Tier-2 concurrency suite now builds on LLVM
   (5/6 byte-identical), nbody/spectralnorm unblocked by the FP prims; numbers folded into
   [`CROSS-LANGUAGE-BENCHMARKING.md`](docs/CROSS-LANGUAGE-BENCHMARKING.md). (Array benchmarks pending the `feat/mut-array` impl.)
4. **Smaller issues** — ✅ done: the `let`-blind scalar-worker (both backends, `555f50b`); do-block-tail-call
   stack overflow (`997323a`); `sleepFor`/`sleepUntil` nonpositive (`339b8f7`); `fiberId`/`currentFiberId`
   wired (`339b8f7`); `__arrayIndexUnsafe` de-Bruijn (`07cda19`); reactor-shutdown sleep-timer cleanup
   (`1162ddc`). **OPEN:** the C-backend CPS edges (suspend-in-`for`, `var:Double` helper miscompile); the
   `kctor` value-box multi-worker race (value.c, TSan); the timing-flaky `race`/`timeout` test; **the native
   test harness is not concurrency-safe** (`run-native-tests.sh` shares `/tmp/kserver` + the frag dir + a
   fixed port → false failures under parallel agents — needs a per-run temp dir + dynamic port); the
   remaining runtime spec-coverage stubs (supervisor, labels, sandbox).
5. **Bigger levers** — ✅ done: LLVM **curried-CK-machine-prim** gap (`2ceea5f`); LLVM **function**
   scalar-worker (`555f50b`); **value-unboxing largely landed** — immediate tagging (Int `b001` + nullary
   `b010` + packed 1/2-field `b011` ctors, all active in `value.c`), the suspendability gate (Stage 1.5),
   the F64 Double worker (Stage 2b). **OPEN — the marquee: Perceus precise RC** — design **DONE**
   ([PERCEUS-RC-DESIGN.md](runtime/docs/PERCEUS-RC-DESIGN.md)). The only path to the *dominant residual*
   allocation that tagging cannot touch (n-ary ctor per-field box indirection + the 832 B/fork frame);
   replaces Boehm, reuses Kappa's **quantity/borrow system as the ownership substrate** (owned `1` / borrowed
   `&` / shared `ω` + path-sensitive last-use already computed — erased before KBackendIR, so it must be
   *threaded* as IR metadata). Staged:
   - **S0 — reconcile + header.** ✅ **done** (`71e6639`): the reconcile (`8775aec`) + the `rc` word in the
     free `KValue` header hole (offset 4, `sizeof` unchanged at 48, init=1 at heap alloc, immediates skip).
   - **S1 — thread ownership onto KBackendIR** — plan [PERCEUS-S1-PLAN.md](runtime/docs/PERCEUS-S1-PLAN.md).
     A side-table (`Ownership.hs`), NOT new `Term` fields; owned/borrowed is already in `CPi`, only last-use
     is erased. **S1 ✅ COMPLETE** (`71e6639`→`b26ef7c`): the full ownership-analysis layer — last-use over
     Core, ctor layout, the **whole-program §3a refinement** (dynamic-link gate is a documented TODO, not
     module-export), the owned/borrowed accessor — all observe-only/parity-identical, validated by the
     cross-check gate over 665 globals. → **S2** (dup/drop — the first stage that *consumes* `OwnInfo` +
     changes codegen; the Boehm-differential-backstop go/no-go).
   - **S2 — dup/drop, Boehm differential backstop. ✅ S2.0–S2.3b LANDED + independently reviewed SOUND;
     S2.3c primitive convention table and S2.3d per-path dead-binder drops implemented**
     (`9c19790`→`272be14` plus current S2.3c/S2.3d work): dup/drop runtime ops + historical child-position threading (S2.0/S2.1), dup
     emission (S2.2), the match-destructure cell-drop (S2.3a — `kdrop` now fires: 101 sites / 33 files, 315
     `kdup` / 66), and the consume-vs-read flag consumed CONSERVATIVELY (S2.3b — dup only a consuming
     `NonLast`; scope-close consults consuming uses, while S3.2 supplies the proved projection-result ownership
     subset needed by free-on-zero). S2.3c routes global call-boundary ownership
     through `argConvSelectGlobal`, keyed by resolved primitive identity, with audited `ArgOwned` positions
     for runtime-cell publishers and `ArgBorrowed` positions for confirmed read-only primitive handles.
     Ambiguous result/action-transfer primitives remain conservative `ArgShared`. S2.3d records branch-local
     dead-binder drop sites in `OwnInfo` and emits drops only for current flat locals whose binder identity and
     owned-reference bit prove the selected branch omitted an owned droppable value, including saturated
     eta-expanded constructor let-locals that codegen lowers to fresh `kctor` allocations and guarded arms after
     a non-consuming guard succeeds. It keeps raw borrowed record-projection owners live while the borrowed alias
     is live, and analyzes guarded arms with the later-arm failure continuation so consuming guards get `kdup`
     when fallthrough can still use the value; drop-only fallthrough after a consuming guard is leak-biased instead
     of double-dropping until guard-result path ownership is modeled. Incoming worker parameters are intentionally not marked owning until caller-side
     ownership transfer normalizes borrowed/projection actuals into owned refs; restoring param drops is an open
     S2/S3 bridge item, not a permanent capability reduction. A recorded
     droppable branch-drop binder that cannot resolve in a top-level flat worker frame is an RC validation
     miss, not a silent leak; capture-free nested flat closures can drop their own resolved owned locals,
     while missing outer/captured binders and CPS/boxed paths remain conservative no-drop sites. Through S2
     this was a Boehm-backed maintenance layer with an underflow assert. S3 has since made the C/native path
     default to RC validation/emission plus free-on-zero for the conservative strict-data FREESET, while
     `KAPPA_PERCEUS_RC=0` remains the explicit whole-binary RC-off/Boehm baseline and LLVM generated output
     keeps runtime RC disabled until it emits matching ownership ops. Last verified 2026-07-02: conformance
     2094/0, with native RC parity covered by `test/native/run-native-tests.sh`; underflow-clean +
     non-vacuous when those gates pass. S3.2 tightened returning-arm (`SinkTail`/`SinkBounce`) match cell drops
     and owned projection results through nested/control expressions; the S2.3c storing-primitive audit remains
     a standing invariant for later runtime-store precision.
   - **S3 — flip free-on-zero** for strict (acyclic ⇒ garbage-free) data; immediates skip RC. Full plan:
     [PERCEUS-S3-PLAN.md](runtime/docs/PERCEUS-S3-PLAN.md) — scope = RC-free the immutable acyclic thread-local
     shapes only (`K_CTOR`/`K_REC`/`K_VARIANT`/`K_STR`/`K_BOUNCE`/`K_FAIL`), retain closures,
     IO/action/native wrappers, `K_REF`/`K_ARRAY`/`K_THUNK`/`K_BIGINT`/`K_BYTE`/`K_BYTES`/`K_FGN`, and S3-era
     shared values on Boehm until the S4 ownership/atomic stage; S3.0/S3.1 prereqs landed = `kis_rc_freeable` +
     shared-bit encoding, `karr_new` per-slot dup, `krec_without` kept-field dup, S3-era `tshare`
     marking that deferred shared RC to S4,
     iterative drop-descent skeleton, and
     arity-guard reconcile. **S3.2-S3.4 landed for the C/runtime path:** `kdrop` now frees zero-count values in
     the conservative FREESET using an inline/scanned-overflow iterative worklist; S3.3 drops displaced runtime
     cell values and failed-publication arguments (`Ref`/array/FiberRef/STM/promise/failed CAS); S3.4 makes native
     RC validation/emission default-on with `KAPPA_PERCEUS_RC=0` reserved for explicit RC-off differential baselines
     that disable runtime RC effects as well as generated maintenance.
     LLVM and retained mutable/lazy/foreign/resource shapes remain Boehm-backed until their later stages; S4 below
     now covers shared strict immutable FREESET reclamation. The native corpus lane runs
     generated C binaries with `KAPPA_POISON=1`, includes a non-vacuous generated-drop fixture, and gates the
     generated-drop heap high-water trend in a separate real-free lane with `KAPPA_POISON` unset.
   - **S4 — thread-shared atomic split** at the fork / promise / fiber-exit / TVar publish points. Full plan:
     [PERCEUS-S4-PLAN.md](runtime/docs/PERCEUS-S4-PLAN.md) — **landed for the C/runtime path**: thread-local
     RC uses an atomic discriminator load followed by direct non-RMW count updates, shared values use counted
     atomic RC with acquire-before-free, and the strict immutable FREESET is reclaimable even after publication.
     Runtime-only, backend-agnostic — needs neither LLVM-RC nor the KBackendIR split. Gates now include the
     focused `runtime` `tsan-rc` shared-RC concurrency corpus, `perceus_s4_shared` poison/reclamation
     regressions, a debug recursive publish-mark assertion, and `bench-s4-rc` for biased fast-path recovery.
     Mutable/lazy/foreign/resource tags remain Boehm-retained until the later cycle/resource ownership stages.
   - **S5 — drop-guided FBIP reuse** — ✅ **LANDED for the native C path**: the n-ary-ctor allocation win
     (rbtree/boxed-rebuild allocation reduction now; the literal `std::map` speed target remains
     representation/unboxing-gated). Full plan: [PERCEUS-S5-PLAN.md](runtime/docs/PERCEUS-S5-PLAN.md).
     **Decision: split-first** — Phase A landed the KCore/KBackendIR split
     ([KCORE-KBACKENDIR-SCOPING.md](docs/KCORE-KBACKENDIR-SCOPING.md): A0 thread erasure classification / kill
     `quote∘force`, A1 stable identities / **retire R-path**, A2 materialize KBackendIR, A3 representation
     classes), then Phase B landed the FBIP reuse pass (`drop_reuse`/`reuse_alloc`, reuse only a unique cell —
     the S4 shared bit is the concurrency guard, so shared cells are never reused). Close-out gates include
     conformance `2644/0`, full native green, LLVM parity `163/0` including deterministic S5 reuse fixtures,
     poison/TSan RC lanes with the S5 primitive harness, reuse-on == RC-on/reuse-off via
     `KAPPA_PERCEUS_REUSE=0`, and positive B3 reuse/allocation-reduction counts (`20000` / `32767` /
     `139631` reuses; `1278288B` / `3145680B` / `13402752B` saved). The tracked `std::map` comparison still
     reports about `1.3x` slower and belongs to the representation/unboxing program; generalized cross-arm/
     frame reuse-credit threading stays visible as S5.B5 report-only.
   - **S6 — borrowing (opt-in) + inferred FIP / reuse-credit checking (no surface `fip`/`fbip` keywords).**
     Later: precise stack roots; the ref/lazy cycle set.
   Couples with the array element-unboxing (#2 Stages B→H) and the lazy-data/RC boundary for any future opt-in
   lazy-data design.
6. **Evidence-aware IO/`var` scalarization (P0.2 restore)** — design plan **DONE**
   ([`docs/scalarization_review.md`](docs/scalarization_review.md)); **SCA-0→SCA-3 (LLVM) RESTORED +
   reviewed SOUND** (`4f5df2f`). S2.3b correctly retired the old raw-ref peephole (it bypassed selected
   `MonadRef` evidence); 4f5df2f restored scalarization on the LLVM lane via a checker-owned,
   evidence-verified witness (never name-based): `scalar_intwhile` emits `@kscalarloop` with no `krt2_while`,
   the alloc gates pass, and a user `MonadRef` is provably never scalarized (parity 150/0 incl.
   `monadref-user-evidence`). **Remaining:** the C backend still uses the boxed `krt2_while`/selected-action
   fallback (SCA-3 C), plus SCA-4→SCA-6. Stage map (LLVM done unless noted):
   - **SCA-0 gates ✅:** keep `arithloop` report numbers visible; add scoped generated-code negative fixtures
     (named region/worker or planner rejection, not global scalar-worker absence) for user
     `MonadRef`, STM, wrong carrier, `ref x` escape, suspension/finalizer constructs (`cede`, `sleep`,
     `await`/`join`, `fork`, `blocking`, `mask`/`poll`, `catch`/`finally`, handlers, `defer`/`using`), and
     overflow-after-prior-writes; run accepted/rejected fixtures under the default RC-on native gate
     (`KAPPA_PERCEUS_RC=0` only for explicit whole-binary off baselines).
   - **SCA-1 checker witness ✅:** have the checker attach compact `BuiltinIORef` action witnesses, tied by a
     stable hidden-cell id, to compiler-elaborated `KVarItem`, `KAssign`, and generated current-read `KBind`
     actions when the selected evidence is exactly the builtin `MonadRef (IO e)` instance. No backend
     name/string recognition.
   - **SCA-2 shared planner ✅:** build a conservative scalar-region planner that proves non-escape,
     source-order reads/writes, scalar-expressible condition/body, no suspension, and exact overflow
     fallback; rejection means the existing boxed selected-action lowering.
   - **SCA-3 backend restore (LLVM ✅ / C ⏳):** LLVM first for `scalar_intwhile` (implemented in the current
     evidence-aware LLVM lane), then C or shared C+LLVM. Hot path must have
     scalar locals/SSA, no per-iteration `K_REF`/`readRef`/`writeRef`/`krt2_bind`/`krt2_while`, and only
     counter-gated `krt2_safepoint`. Gate per backend: LLVM-only work flips LLVM codegen/perf checks; the
     default `arithloop` raw-C ratio gate flips to `<=5x` only once the C/default backend scalarizes or the
     harness has an explicit LLVM ratio lane. Keep a tracked `<=2x` target once the harness has
     repetitions/CI.
   - **SCA-4 bounded normalizer:** later, recognize simple indirect selected-action wrappers (typeapps,
     eta, local renames, known dictionary projections) with fuel and whitelist; no user global unfolding or
     monad-law rewriting.
   - **SCA-5/SCA-6:** general direct no-suspend IO regions, then heap-framed native resumable loops for real
     `cede`/park points. Until SCA-6, real suspension in a scalar region falls back.
7. **Stack-safe deep recursion** — design **DONE** ([STACK-SAFETY-DESIGN.md](runtime/docs/STACK-SAFETY-DESIGN.md)).
   Layered: (L1) automatic TRMC — modulo-cons + accumulator-modulo-associative-op (kills the non-tail
   `count`/`sum` overflow, no runtime change); (L2) extend the IO CK machine to pure recursion; (L0, DONE
   `d01b8a7`) the lazily-committed 8 MiB worker-stack floor. `decreases` is the soundness *license*, not a
   runtime depth oracle. The accumulator opt's prerequisite — **lawful Monoids** — is ✅ done (`5efbe3d`, #9);
   the L1 TRMC and L2 CK-machine impl remain **OPEN**.
8. **Inhabitance + h-level conformance suite** — [INHABITANCE_TESTS.md](docs/INHABITANCE_TESTS.md). The
   §30.2.7 inhabitance analysis (`Inhabitance.hs`) is done (`63400fb`); this suite pins its summaries AND
   the h-level/equality soundness the IsProp/IsSet work rides on (summaries must stay strictly separate
   from source-level evidence synthesis — §13).
   - **P1 — equality/UIP tripwire — ✅ PARTIAL** (merged `93fbccf`, `tests/conformance/hlevel/`, 10 tests).
     The directly-testable subset, translated to the compiler's ACTUAL surface (the IsProp-under-Pi solver
     + gated `unsafeAssertProof` — NB the compiler has **no match-based path induction** and **no intrinsic
     h-level rules**): `badK` rejected (`E_UNSOLVED_IMPLICIT`); `goodKWithSet` accepted with `IsSet ((=) x x)`;
     no-confusion Empty; **nominal type disequality is NOT empty** (univalence-critical); `IsProp Bool` /
     abstract `IsSet a` unsolvable (no unbounded search). **DEFERRED within P1 — needs a compiler-owned
     intrinsic h-level solver (the compiler has NONE; only `instance IsSet String` resolves):** the §8
     synth-PASS matrix (`IsSet Bool`, `IsContr Unit`, `IsSubsingleton Void`, …) and the entire `IsNType n A`
     family (no `IsNType` trait exists). **Building that intrinsic h-level solver is the real remaining §8
     work** — a genuine feature, not a test.
   - **P2 — inhabitance summaries.** §3 algebraic/products/sums/GADT-refinement, §4 completion/enumeration
     (+ threshold), §5 `impossible` only on exact `Empty` + opaque-≠-empty. Pins `Inhabitance.hs`; needs a
     `%summary`/`%enumerate` query directive (or translate to `mode check`/`check-fails`).
   - **P3 — coverage.** §9 trait-evidence (`IsSubsingleton (Eq Bool)` yes, `IsProp` no), §10 `IsSubsingleton`
     ≠ inhabitance, §12 runtime-shape-vs-source (erased impossible proofs stay `Empty`), §11 optional
     finite-function strengthening (gated mode; must NOT imply function h-levels).
9. **Spec-conformant Monoid laws** — ✅ **DONE** (`5efbe3d`): the three laws (`appendAssoc`/`appendLeftIdentity`/
   `appendRightIdentity`) are folded into the base `Monoid` trait (Spec.md:29828-29842 — every `Monoid` is
   lawful); `IO e a`/`STM a` moved off `Monoid` onto a minimal `Pointed` trait (`empty` only, for the §18.1.13
   `let?`/STM-`empty` desugaring); the separate `LawfulMonoid` is removed. List laws by induction, String
   asserted via `IsSet String`. NB: a *custom* user `Monoid` now must discharge the three laws (by real proof
   or behind `@AllowUnsafeIntrinsics`) — a `derive`-style law-by-`Eq`-reflection helper could ease this later.
10. **Intrinsic h-level solver** *(IMPLEMENTATION, not spec work — surfaced by item 8's P1)* — the spec
   DEFINES `intrinsic trait IsNType (level : Nat) (a : Type)` (Spec.md:9250/14703) plus `IsContr`/`IsProp`/
   `IsSet`/`IsGroupoid`, with evidence "introduced by compiler-owned solvers" (9303), the `IsNType n`
   interpretation (14717-14722: 0=Contr, 1=Prop, 2=Set, 3=Groupoid, n+1 ⇔ all equalities are `IsNType n`),
   and the hard rule (14735-14736): **MUST NOT solve `IsNType n A` by unbounded search — only deterministic,
   terminating, specified intrinsic rules.** The compiler implements NONE of this (only the bare
   `instance IsSet String` marker; no `IsNType` trait). Build the compiler-owned h-level solver: the
   structural intrinsic rules (`IsSet` of finite / decidable-equality ADTs via Hedberg; `IsContr` of records
   of contractibles; `IsProp`/`IsSubsingleton`; the `IsNType` level lattice) consistent with the §30.2.7
   `Inhabitance.hs` summaries. Unblocks INHABITANCE_TESTS.md §8's synth-PASS matrix (item 8). Cross-ref the
   exact inhabitant-counter (`../datatron`) for the conservative rule-set; any precise-MUST-set ambiguity is
   minor spec-clarification pinned during impl.

---

## Done ✅

- [x] **kappart2 runtime is the unconditional native runtime** (M:N fibers, libuv reactor, STM, structured concurrency, CK-machine); the value model + scheduler live in [`runtime/`](runtime).
- [x] **No by-name prim dispatch** — codegen lowers to direct `kp_*`/`kpf_*` calls or curried `K_NATIVE`; `prim_fire_pure`/`K_PRIM` removed.
- [x] **`std.atomic` — real boxed `AtomicRef`/CAS, WIRED** ([`../atomic.c`](runtime/atomic.c),
  commit `67e1d60`). The prelude `AtomicRef` ops lower to `krt2_atomic_load/store/
  exchange/cas/fetch_*`; the native cell is protected by a per-cell mutex rather
  than promising lock-free hardware atomics for arbitrary Kappa values. Proven exact
  under an N×M multi-worker race (`atomic-race.kp` + `atomic_lostproof.c`: the old
  plain-`Ref` lost 1,193,432 / 1,280,000 updates; the atomic path loses 0). Two
  honest in-code caveats: the order is passed as an Integer §29.1 declaration index
  (ctor tags are global), and the interpreter is the sequential oracle (cannot test
  the race). `rt-atomics` is now honest.
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

The plan front-loaded the **uniform** wins (sound without type-directed layout)
and the shared **§3.3 suspendability** prerequisite, then landed the architecture
investment in item 6 (KBackendIR / representation selection). The remaining
non-uniform layout fork is item 7: niche/full-range layouts need more than the
now-landed KBackendIR substrate because Kappa erases types without
monomorphization, so they are deferred to the specialization/representation
program.

1. [x] **§3.3 suspendability analysis** — the shared unblock. ✅
2. [x] **Value layout — uniform immediates + packing** — `b001` Int, `b010` nullary, `b011` single- AND two-field packing. DONE, adversarially verified (corpus 102/102). The NON-uniform layouts (niche, full-range Int) now depend on item 7's specialization/monomorphization work, NOT on more runtime work — see [`LAYOUT-DESIGN.md`](runtime/docs/LAYOUT-DESIGN.md).
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

**Status.** The original gap was that the Spec mandates `KFrontIR` (§34.2) →
**KCore** (§30.2, the typed kernel) → **KBackendIR** (§34.3), while
kappa-haskell previously lowered `Term` (its KCore) directly to C/LLVM and did
representation selection mostly at runtime/per value (`kctor`: argc/fit →
`b010`/`b011`/boxed). S5.A changed that architecture for native value/do
emission: `src/Kappa/Backend/IR.hs` now materializes a distinct recursive
KBackendIR tree, validates it, structurally omits erased positions, and carries
node-local ownership/argument/layout facts consumed by C/LLVM. Remaining work in
this track is therefore **not** "add KBackendIR"; it is to broaden the staged
§34.3 representation-selection program on top of the landed tree, keeping older
KCore-reading analyses explicit and preventing them from reattaching ownership
or layout facts by structural path.

**Historical staged plan** (scoped 2026-06-26; updated after S5.A/S5.B). Early
stages experimented with observe-only annotations and representation tables; S5.A
then did materialize the distinct KBackendIR datatype because Perceus reuse needed
typed layout + stable node-local ownership. Each remaining stage still stays
interp==C==LLVM byte-identical until it deliberately lands a representation
change.

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
      `scrutineeEmpty` (`Check.hs:8276`) into a terminating structural
      cardinality interval `InhabitanceSummary { minCount, maxCount }`, with a
      natural lower bound and a finite-or-unbounded upper bound. The familiar
      `Empty`/`Subsingleton`/`Contractible`/`Finite n`/`Unknown` spellings are
      canonical exact/range patterns over that representation, not a closed
      five-constructor lattice. The query is keyed by `InhabitancePurpose` (Stage 1
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
      of `C.hs`/`LLVM.hs` then caught the same smell in the old splice helpers
      (they matched a bare internal name). Those helpers were removed when
      bang-splice lowering became ordinary monadic bind-lifting; the rest of the backend's string uses (mangling, diagnostics,
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
      `411933d`; S2.3b updated the mutable-cell representation). `var`/`:=`/
      `while`/`break`/`continue`/`return` now CPS-lower inside suspending do-blocks.
      Mutable cells are checked through the selected `MonadRef m` evidence: `var`
      elaborates to the selected `newRef`, assignment and recognized `writeRef`
      use the selected `writeRef`, and current-value reads/recognized `readRef`
      use the selected `readRef` action. Raw runtime refs (`krt2_new_ref`,
      `krt2_read_ref`, `krt2_write_ref`) are an implementation detail only for
      checker-witnessed builtin-IO/STM lowerings; they are not the source-level
      semantics and are not used to bypass user `MonadRef` dictionaries.
      **R7 var-read normalization**: current-value reads are hoisted to explicit
      selected read actions at the nearest valid do-item boundary, with
      VarCurrent facts invalidated by writes, escapes, joins, loop back-edges, and
      multi-shot operation sites per §18.6.2. The LLVM backend restores the
      unboxed mutable-var while scalar worker only for the subset whose selected
      evidence is proven equivalent to builtin IO refs; unproven user evidence
      falls back to the selected-action path. Follow-up work remains to recognize
      more indirect aliases/eta-renamings of read/write actions without general
      normalization (`docs/scalarization_review.md`).
      VERIFIED: corpus interp==C==LLVM, native suite green, conformance green, the
      accept-loop / counter-fork-loop / read-after-write tests pass, and R12 holds
      for the suspending loop family. Unsupported loop subforms still fail closed
      (`E_BACKEND_UNSUPPORTED`) rather than being silently dropped.
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
        2. [~] MASKING SURFACE (§18.1.12) — COMMON CASE DONE (merged `e1a1482`):
           `uninterruptible`/`mask`/`poll` exposed in the prelude + interp, lowered
           to `krt2_*`, and `bracketM` now masks acquire+register so a born-
           interrupted fiber registers the finalizer before the interrupt — release
           RUNS (`bracket-mask-interrupt.kp`, interp==C). REMAINING: when `bracketM`
           is reached as a bare `K_BOUNCE` worker behind the `MonadResource` dict,
           the synchronous `krun_io`/`krt2_run_op_sync` bridge can't drive `OP_MASK`,
           so bracket-as-whole-fiber-action with a born-interrupt can still skip
           release on C — closing it needs the do-kernel CPS Stage 2/3 (the sync
           bridge handling the masking OPs).
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
- [~] **Stage 4 — effect-handler unification** (CPS-DESIGN §2, Stage 4). **4a DONE**
      (merged `1a6ae2f`): one-shot algebraic effect handlers run as `KK_HANDLER`
      prompt frames on the CK-machine — `handle` installs the frame, `perform`
      searches `f->k` outward + severs the op-site→handler Cont sub-chain as a
      one-shot resumption (`do_perform`/`do_resume`, rt.c; the sever is the only new
      primitive), `resume` splices it back. `__EffPure`/`__EffOp` now run on the one
      Cont chain (not the pure `kpf___handleEff` rewrite). Deep+shallow; abandonment
      free via R1. **The parking wildcard (R11) WORKS** (a handler clause that
      forks/awaits/sleeps on libuv before resuming, interp==C); GC-safe (50k
      perform/resume under aggressive collection); multi-shot compile-time-rejected
      via the `Usage.hs` escape-check; differential-tested vs `Eval.hs`
      (state/abort/reader/nested, interp==C==LLVM). Conformance 1851→1854.
      *Partial:* `elabEffDo` lifts only `defer` (not `using`/`var`/loop — §32.2.19-21
      residual). **4b** tail-resumptive fast path + **4c** multi-shot (LARGE, behind a
      new `rt-multishot-effects` capability) remain. See
      [`docs/EFFECT-HANDLER-SCOPING.md`](docs/EFFECT-HANDLER-SCOPING.md) for the full
      design + the 4b/4c plan.
- [ ] **Stage 5 — LLVM coroutines** (CPS-DESIGN §5). Retarget `kdo_*`/`kdok_*` to
      `coro.id.retcon.once`; seed `CoroSplit` liveness from the `KEnv`.

---

## Track: Value unboxing ([`UNBOXING-DESIGN.md`](runtime/docs/UNBOXING-DESIGN.md))

- [~] **Stage 0 — GC/alignment contract + canonical encoding** (UNBOXING §5.2/§5.4/§7).
      GC/alignment **CONTRACT now ENFORCED in the runtime** (`krt_init`, split boxed-runtime TUs):
      `GC_set_all_interior_pointers(0)` *before* `GC_INIT` (Boehm roots only BASE
      pointers, so a tagged odd word is a non-pointer, not a false interior root);
      a startup `krt_assert_gc_alignment` (sampled `GC_MALLOC` all 8-aligned,
      fail-closed); `_Static_assert(_Alignof(max_align_t) >= 8)`. The **low-3-bit
      tag budget is reserved + documented** (`b000` ptr / `b001` imm-Int / `b010`
      imm-ctor / `b011` packed ctor / `b1xx` future immediates; Perceus RC lives in
      the heap header) with the `kis_imm`/`kderef`/`kimm_payload` discriminator API in
      `kappart.h` — a debug `kderef` assert pinned immediate-safety ahead of the
      Stage-1 deref audit.
      VERIFIED safe under heavy collection: **corpus 81/81**, a 1M-cons-cell
      **251-collection GC stress** (interp == C == LLVM, correct), full native suite
      green. **Stage-0 BENCHES LANDED** (`bench/rt_bench.c` rows 3, 6–10 + the
      `bench/README.md` baseline table, `make bench`): boxed `addDouble` (the F64
      boxing cost, 48 B/op → 0 unboxed), `ctor-build` (n-ary, 112 B/op — control) + `ctor0-build`
      (nullary `None`, 48 B/op — the immediate WIN that should drop to 0), `ctor
      deref boxed` + `ctor0 dispatch` (the tag-test tax/win = the go/no-go gate),
      and a sum-checked `scalar across a park` (1184 B/op, asserts the carried Int
      survives) — bytes/op bit-identical across runs. The canonical value encoding
      work later landed with Stage 1 / layout packing.
- [x] **Stage 1 — immediate tagging and uniform small ctor packing** (UNBOXING §1/§5/§7).
      **Immediate INT (b001) DONE** (commit `a074259`, merged `4cdd181`): a small Int rides the `KValue*`
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
      tax flat in isolation. The later layout pass completed the secondary `b010`
      immediate nullary ctors and `b011` packed one-/two-field ctors; see the current
      value-layout completion item above.
- [ ] **Stage 1.5** = the §3.3 analysis above (shared).
- [ ] **Stage 2 — worker/wrapper specialization** (UNBOXING §1/§7). Generalize
      `scalarPlan`/`kwi_`/`kwd_` to a layout kind (`Boxed|I64|F64|FixedFFI`) on Core
      types; one unboxed worker per class, boxed `kw_g` as the reference, the
      `kunbox_*`/`*ovf` escape as the floor. Unboxes `Double`/wide-FFI/fused hot
      paths. **Blocked on §3.3** (Stage 2a re-proves suspension-freedom).

---

## Track: Missing primitives ([`PRIMITIVES.md`](runtime/docs/PRIMITIVES.md))

- [x] **`onInterrupt`/`onExit`** — finalizer receiving the exit Reason; small
      extension of `KK_FINSEQ` (which already carries the Reason). PRIMITIVES #2.
      Landed end-to-end (runtime `OP_ONEXIT_FIN`/`OP_ONINT_FIN` + both backends +
      interp); test `tests/conformance/effects/on-exit-interrupt.kp`.
- [x] **`FiberRef.modify` + copy-on-fork** — §18.1.7 parent/child independence
      (normative conformance gap). PRIMITIVES #4 / ADD #4. Landed (per-fiber
      `FiberLocals` + fork-time deep copy); test `…/fiber-ref-modify.kp` +
      `runtime/tests/fiberref_promise.c`.
- [x] **`Promise.poll`/`isDone`** — non-blocking peek. PRIMITIVES #3. Landed
      (runtime `OP_POLL_PROMISE`/`OP_IS_DONE_PROMISE` + both backends + interp);
      test `tests/conformance/effects/promise-poll.kp`.
- [ ] **`disconnect`** — detached interruption (verify forkDaemon doesn't already
      cover it). PRIMITIVES #5.
- [ ] **DERIVE as `.kp` library** — `zipPar`/`foreachPar`/`raceAll`/`timeoutTo`,
      `Cause` projections (pure folds), `std.supervisor`, memoize, semaphores/
      queues over `TVar`+`Promise`. Gated on the general-CPS lowering above.
- [ ] Keep the interpreter (`src/Kappa/Interp.hs`) in lockstep for the ADD items.
      (Done for onExit/onInterrupt, Promise.poll/isDone, FiberRef.modify; remaining
      for `disconnect` and any future ADD items.)

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
- **Cross-language benchmarking** ([`CROSS-LANGUAGE-BENCHMARKING.md`](docs/CROSS-LANGUAGE-BENCHMARKING.md))
      — the external apples-to-apples layer on top of `make bench` (which carries a Go-goroutine point).
      Strategy: **lead with concurrency** (Kappa's strength: `fork/await ≈ 3.5× a goroutine`); use
      allocation-bound programs as an **honesty gate** for the boxing lever. **Status: Tiers 1 + 2 imported
      & measured; 1.5 + 3 planned; nofib declined.**
   - **✅ Imported + measured** (`5a96969`, suites under [`bench/xlang/`](bench/xlang)):
      - [x] **Tier 1 — CLBG numeric:** `nbody`, `spectralnorm`, `mandelbrot`, `fannkuch`, `pidigits`
            (GMP-strong), `binarytrees` (the standing boxing-lever gate — loses until unboxing lands; track
            the trend, don't market it), + `sumloop`. Reference impls present; `N` hardcoded (no `getArgs`/stdin yet).
      - [x] **Tier 2 — concurrency (the differentiator):** `skynet` (1M-fiber spawn/join), `threadring`,
            + the Savina set `pingpong` / `forkjoin` / `bankstm` (Bank-Transaction over STM) / `philosophers`.
            All over `fork`/`TVar`/`Promise`; build on LLVM, 5/6 byte-identical to the reference.
   - **⬜ Planned, not yet imported:**
      - [ ] **Tier 1.5 — Are We Fast Yet** (Richards / DeltaBlue / Havlak / Json / CD + micros) — the fair
            compiler-vs-compiler story; medium port (objects → records/traits). No runtime blocker — doable now.
      - [ ] **Tier 3 — TechEmpower (TFB), flagship** — gated on an HTTP/JSON framework that **does not exist
            yet**. On-ramp = Plaintext + JSON over the already-linked libuv (TFB accepts partial); the DB tests
            (Single/Multiple Query, Fortunes, Updates) then need a Postgres FFI driver. **We DO want this**
            (the libuv + M:N-fiber runtime is exactly what should shine under load) — **revisit once the
            runtime is feature-complete**; it's multi-week library work, not a benchmark port.
   - **🚫 Won't import wholesale** (justified):
      - **nofib (Haskell)** — GHC-specific harness + idioms; a whole port has low marginal value because the
            vs-GHC number already comes free from CLBG (GHC is a CLBG entrant). Cherry-pick a single
            imaginary/spectral kernel ONLY if a specific GC/laziness question ever needs it.

---

## Track: Memory efficiency & GC/RC ([`MEMORY-EFFICIENCY-RESEARCH.md`](docs/MEMORY-EFFICIENCY-RESEARCH.md), [`ANALYSES-AND-SPEC-BACKPORT.md`](docs/ANALYSES-AND-SPEC-BACKPORT.md))

How to stay memory-efficient — minimal GC churn even in highly-FP code — by
exploiting Kappa's static guarantees (QTT usage intervals, §12 borrow/region,
purity ⇒ acyclic inductive data, totality). Theme: *allocation*, not indirection,
is the dominant cost, and Kappa can prove more reuse statically + more cheaply than
dynamic-RC languages. Staged so each rung lands real wins without waiting on the
precise collector. Research 2026-06-27.

- [ ] **Stage 0 — pool the fork/scheduler hot path** (the single biggest lever; =
      the efficiency-review #1, subsumes the Performance-track pooling item). Per-
      worker Fiber/Cont/KEnv/RQNode free-lists, intrusive `rq_next` + embedded
      `Waiter`, a 1-word lock for the 64 B `pthread_mutex`, an inline `{tag,a,b}` OP
      node — removes the ~832 B/op fork cost (vs Go's ~128 B/op pooled `g`). No
      type/GC prerequisites; gated only on the persistent-runtime `run_main` fix.
- [ ] **Stage 1 — static reuse from the usage interval + §12 facts** (P0,
      "extend-existing", no precise GC needed). The single-use reuse signal is the
      INFERRED usage count, NOT the declared quantity (unannotated binders are ω,
      §13156) — and `ucHi==1` is **already computed for every binder**
      ([`Usage.hs:168-184`](src/Kappa/Usage.hs)); it is merely *gated* (no
      Optimization purpose, not exported, no backend consumer; `countedQ`/`closeVar`/
      `sBail` restrict it to checking). Ungate it (an Optimization purpose split,
      like inhabitance's) → guaranteed in-place field writes on the FIP
      match-rebuild-same-ctor shape + frame-local/arena alloc of non-escaping acyclic
      cells under Boehm. Pair with §12.3 region escape (already a typechecked local
      analysis, exact under purity+totality; `bodyCapturesEnv` ships but is binary —
      plumb to stack-alloc / ref-elision).
- [ ] **Stage 2 — full Perceus dup/drop + reuse on the CPS spine** (HARD-GATED on a
      precise collector). QTT/§12 supply the linearity + the non-atomic/atomic RC
      split; bridged by the LLVM-coro flat-frame + slot-kind map.
- [ ] **Stage 3 — RC+GC hybrid.** RC for the acyclic-by-purity majority; tracing /
      trial-deletion confined to the ONLY cycle sources (`Ref`/`TVar` + recursive-
      thunk knots).
- [ ] **Cross-cutting prerequisite — our own precise GC/RC (Boehm is TEMPORARY).**
      The conservative Boehm collector blocks precise RC (no precise slot/root
      discrimination) and is the gate for Stages 2–3; the enabling pieces are
      designed (LLVM-coro flat-frame + slot-kind map, the low-3-bit immediate-tag
      reservation).

---

## Track: Record representation ([`RECORD-REP-OPTIMIZATION.md`](docs/RECORD-REP-OPTIMIZATION.md))

Boxed records are heavy: `K_REC = {int n; const char **names; KValue **vals}` is 3 words and
`krec` ([`value.c`](runtime/value.c)) does **two** scanned-heap allocations per
instance — the box (~4 words) **plus a separate copied `vals` array** (~`n` words) — and records
**never pack** (a 2-field record allocates, while `Pair(Int,Int)` is 0 B/op). The `names` pointer
is already a SHARED static literal (zero per-instance bytes); the redundancy is the `names` *word*
in the box + the `strcmp` scan it enables for open/sealed/dict projection (closed-sorted records
already project by static index via `CProjAt`→`krec_at`, no `strcmp`). **Closed-record flattening
is erasure-safe TODAY** — record SHAPE (arity + slot index) is a static elaboration-site fact
([`Check.hs:5956-5975`](src/Kappa/Check.hs) bakes `CProjAt … i`), so it needs neither typed Core
nor a coercion the `CRecord`/`CProj` nodes lack (unlike the deferred niche). Research 2026-06-27.

- [ ] **Stage 1 — flatten `K_REC` inline** (cheapest high-payoff first step). Replace the separate
      `vals` array with a flexible-array-member (`{tag; int n; KValue fields[]}`): **one allocation
      instead of two** for EVERY record. Only `krec`'s body changes
      ([`value.c`](runtime/value.c)) — codegen still calls `krec(n,names,vals)` and
      `CProjAt`/`krec_at` just index the inline slot. GC-positive, interpreter-parity-trivial
      (`VRecordV` is a separate Haskell type), zero typed-Core work, a better Perceus reuse target.
- [ ] **Stage 2 — drop the per-instance `names` word for closed records.** Extend index-based
      `CProjAt` to every closed-sorted site + route the three name consumers (`kproj`,
      `krec_without`, `kvalue_rep_eq`) through a per-type static descriptor: −1 word/instance + no
      `strcmp` for closed records.
- [ ] **Stage 3 — shared per-type field-ID descriptor** (Elm-FieldGroup style) + `krec_at_id`, so
      open/row-polymorphic projection becomes an int search not a `strcmp` scan — unifies closed +
      open layout (open cost == closed). Fixes the missed `CProjAt` at
      [`Check.hs:5993-6001`](src/Kappa/Check.hs).
- [ ] **Stage 4 — pack small records into immediates.** Add a record arm to
      [`Repr.hs`](src/Kappa/Backend/Repr.hs) + lower 1-2 all-immediate-field closed records to
      synthetic anonymous ctors through the existing `kctor`/b011 path: zero allocation for the
      common small record, closing the gap with `Pair(Int,Int)`. Carries the `kis_imm`/`kderef`
      audit + one reserved tag code (after Stages 1-2).
- [ ] **DEFERRED — record niche / per-shape specialized structs.** Need typed Core +
      coercions/monomorphization (the deferred-niche erasure blocker); the flatten+pack line
      captures the allocation win without the type dependence. Do NOT schedule.

---

## Track: Universes / observation modes / `TypeLevel` / KCoreText ([`UNIVERSES-PLAN.md`](docs/UNIVERSES-PLAN.md))

**First-class-level and solver-generalization design applied 2026-07-21.** The current
`docs/Spec.md` retains independent observation/formation modes, floating bare `Type`, explicit
global/local universe schemas, unbounded parametric witness packages, natural-sum `TypeLevel`,
finite-origin KCore observation checking, certified nominal-family variance, explicit
`schemaLift`, and KCoreText verification. It now additionally admits every stable total
first-class level term through canonical neutral identities; separates constructor NF, exact
rigid entailment, and portable metavariable inference; represents declaration constraints as
ordinary erased proof binders; requires rigid declaration-boundary generalization; permits
same-or-lower recursive schema calls; and versions complete arithmetic replay.

The implementation contains complete U-E and U-F support: global/local
schemas and SCC inference, natural-sum levels, witness-package sealing, finite observation
dependencies, structural level certificates, nominal role inference and closures,
`NominalCumulativitySummary`, explicit `CSchemaLift`, schema certificates, and KCoreText support.
The current contract validator reports 48 ordinary/parametric suites, 89 package/schema suites,
34 current variance suites plus 8 gated future suites, and the 67 first-class-level suites plus
5 strengthening suites. U-E and U-F therefore have clean focused owner gates. The 2026-08-18
full conformance result is clean at 4,014 passed, zero failed, and ten explicitly unsupported
optional/future capabilities (4,024 total): eight future variance suites and two optional
compact Nat/Fin layout suites.

The first-class-level bundle adds 67 contracts: 47 accepts and 20 rejects, split into 29
positive source, 17 negative source, 13 solver, and 8 KCoreText suites. All 67 are imported and
active with 5 implementation-strengthening contracts under
`tests/conformance/spec-coverage/first-class-levels-solver-generalization/`, and
`scripts/validate_universe_contract.py` reports the full clean ledger (48 ordinary/parametric,
89 package/schema, 34 current variance, 8 gated future, 67 first-class-level + 5 strengthening). U-G owns neutral
level terms, the specified solver outcomes, rigid generalization, proof-binder migration,
recursive schemas, complete arithmetic replay/versioning, schema reification, and ordinary
`Monotone` evidence — implemented per `docs/UNIVERSES-PLAN.md` (2026-07-21) with owner gates
green. Recursive global level producers now cross KCoreText through exact, versioned
size-change certificates whose SCC and graph are recomputed from typed KCore; unsupported local
recursive producers remain fail-closed. Selected local `Monotone` witnesses are pre-verified
with their full local dependency closure and without the schema certificates they authorize.
The 2026-07-24 closeout passed the full validator/conformance, C/LLVM parity, LLVM RC,
poison RC, TSan RC, and Railyard/Voxelcraft/Delve package gates. A quadratic installed-level
substitution rewrite was replaced by an indexed dependency graph, reducing the Delve cold
native build from roughly five minutes to 42.36 seconds while preserving zero Perceus
findings.

Completed U-P through U-D detail remains trimmed. Existing programs without runtime
`TypeLevel` observations retain the native-output non-regression requirement. Detailed file
ownership, gates, dependencies, risks, and spec anchors live in `docs/UNIVERSES-PLAN.md`.

### U-E — migrate to observation modes and KCoreText

- [x] **U-E0 — re-gate the active revised contract.** The 47 + 71 imported leaves and 17
      strengthening suites are active and pass `scripts/validate_universe_contract.py`.
      Record a clean build/full-suite result and verify that no expectation was weakened during
      promotion.
- [x] **U-E1 — separate observation from formation.** Keep explicit mode plumbing, allow
      parametric observation over every well-formed domain and borrowed access, delete
      `E_PARAMETRIC_BINDER_DOMAIN`, preserve parametric-kind defaults, add a separate Pi/Sigma
      formation judgment, and share grouped annotations/metas.
- [x] **U-E2 — implement the commutative `TypeLevel` algebra.** Replace ordinal addition in
      `Level`, solver formulas, evaluator, runtime, C, LLVM, and tests with componentwise natural
      sum; provide opaque source bodies, four checked algebraic instances, and required laws.
- [x] **U-E3 — add explicit schemas and principal inference.** Parse/retain `.{u,v}` on every
      semantic declaration/reference form; enforce schema arity/scope/completeness; classify
      metas as generalizable or minimizable; compute one principal least solution per top-level
      or local SCC; serialize local/global telescopes and constraints.
- [x] **U-E4 — implement witness packages and standard schemas.** Accept unbounded parametric
      witness packages while rejecting ordinary codes/payloads; preserve projection mode;
      replace `TypeBelow`/`TypeAtMost` with schemas; implement schema-based equality/Dec/
      eliminators with parametric endpoints; complete data/constructor/grouped-binder grammar.
- [x] **U-E5 — implement the KCore dependency calculus.** Replace the current single-mode
      approximation with finite parametric-origin sets and the normative application, let,
      substitution, construction/sealing, projection, case, conversion, and reduction rules.
- [x] **U-E6 — make assumptions and level-lift evidence replayable.** Reject recognized inconsistent
      comparisons deterministically; require each lift to cite a scoped erased proof binder or
      independently verified level certificate; substitute and recheck evidence with levels.
- [x] **U-E7 — complete pre-variance KCoreText.** Remove free universe declarations; use instantiated
      `globalUse` everywhere; add local schemas/constraints and explicit letrec bodies; type
      generic payload values; declare extensions; parse/print/verify level certificates; apply
      canonical SCC/stable-ID/certificate ordering.
      **Open hardening follow-up (2026-07-26):** Core `CMatch` records the
      scrutinee type but not the checked result type. A dependent nominal-field
      type can therefore contain a valid constructor-projection match in a
      context where KCoreText cannot recover its result contract. Add explicit
      result metadata to typed Core, preserve it through every rewrite and
      interface, and restore a generated-KCore round-trip gate for
      `erased-named-field-projection-positive.kp`; do not infer it from source
      names or weaken the valid source fixture.
- [x] **U-E8 — migrate artifacts, prelude, diagnostics, and tests.** Round-trip schemas,
      constraints, modes, dependency summaries, and verified certificate identities through
      interfaces/hashes/stage dumps; remove stale diagnostics/declarations; promote passing
      suites with a replacement ledger for every changed historical expectation.
- [x] **U-E9 — adversarial audit and closeout.** Require each Hurkens/Girard attempt to fail at
      parametric promotion or ordinary universe self-containment; audit all sinks, sealing
      boundaries, generated helpers, instantiations, certificates, generic nodes, interfaces,
      and lowering; run validator, unit/property, full conformance, KCoreText, interpreter,
      C/LLVM native, sanitizer, package, and performance gates.

**U-E exit:** no pre-variance universe-design suite remains pending; no compiler path derives observation
from quantity, treats observation as formation, computes ordinal `TypeLevel` addition, accepts
unverified lift evidence, or serializes a free KCore universe declaration; KCoreText round-trips
verified KCore and all intended universe soundness barriers reject.

### U-F — certified nominal-family universe variance

- [x] **U-F0 — re-gate the active 42-suite variance contract.** Preserve the exact 24 accepts,
      18 rejects, direct `.kcore` fixtures, and manifest already active under
      `tests/conformance/spec-coverage/universe-variance/`. Keep 34 current-feature leaves
      mandatory and 8 future HIIT/HIRT/QIT/QIIT leaves honestly capability-gated.
- [x] **U-F1 — re-gate role syntax, metadata, rendering, and diagnostics.** Parse contextual
      `invariant`/`covariant`/`irrelevant` schema roles, preserve explicit-vs-inferred status,
      reject roles on non-nominal declarations, add the four portable aliases and three
      diagnostic families, and show effective roles in verbose tooling output.
- [x] **U-F2 — re-gate nominal signature closures and inferred roles.** Normalize complete ordinary-
      data signature closures after principal inference/size/positivity, then run the joint
      greatest fixed point from irrelevant downward. Keep roles independent from positivity,
      observation, quantity, formation, and erasure; force invariant for runtime transforms,
      function domains, coupled parameters, and unsupported operations/clauses.
- [x] **U-F3 — re-gate explicit saturated KCore `schemaLift`.** Relate only fully saturated
      applications of the same family, recheck source/target constraints, align identical term
      arguments left-to-right, carry covariant evidence, and reject downcasts, invariant/family/
      argument mismatches, partial heads, and runtime mappings. Do not expand definitional
      equality or instance-head matching.
- [x] **U-F4 — re-gate independently verified action certificates.** Version and hash the
      normalized closure; certify constructor/eliminator/computation-rule action, identity,
      composition, observation/quantity preservation, and representation identity. Distinguish
      forged/stale certificates from invalid uses of valid certificates.
- [x] **U-F5 — re-gate variance KCoreText.** Give nominal data declarations role telescopes and mandatory
      certificate references; add `schema-certificate` declarations and `schema-lift` terms;
      print every role/evidence/aligned target argument; canonicalize lift composition; verify
      all identities, hashes, clauses, saturation, and alignment at checkpoint loading.
- [x] **U-F6 — re-gate interfaces, opacity, identity, and trait coherence.** Serialize
      `NominalCumulativitySummary`; include roles/certificates in semantic hashes and query keys;
      permit opaque imported lifts only through verified summaries; degrade missing support to
      invariant; keep exact schema instantiations for instance selection.
- [x] **U-F7 — re-gate standard and generated nominal families.** Publish equality as
      irrelevant and `TypeBelow`/`TypeAtMost` as covariant; certify trait evidence, GADT family
      argument alignment, constructors, patterns, projections, recursors, and iota/case
      coherence; eta-expand partial source forms only to fully saturated erased lifts.
- [x] **U-F8 — re-gate the future boundary, metatheory, and closeout.** Keep future nominal-extension
      capabilities false until complete path/equation/recursive-operation naturality checkers
      exist. Prove/replay reflexivity, transitivity, substitution, subject reduction,
      identity/composition, opacity, and erasure; promote all 34 current leaves and run the full
      validator/unit/conformance/interface/KCoreText/interpreter/native/sanitizer/package/perf
      gate.

**U-F exit:** all current nominal cross-instance uses are explicit verified `schemaLift` nodes;
no role changes judgmental equality, family arguments, instance overlap, observation, quantity,
or runtime representation; all 34 current variance leaves are active; all 8 future leaves are
either mandatory under an honestly implemented capability or honestly skipped.

### U-G — first-class levels, solver generalization, and recursive schemas

All U-G stages and the combined U-E/U-F/U-G repository-wide closeout are green (see
`docs/UNIVERSES-PLAN.md`, 2026-07-24).

- [x] **U-G0 — 67-suite contract ledger.** The exact bundle tree is
      active under `tests/conformance/spec-coverage/first-class-levels-solver-generalization/`
      with 47 accepts/20 rejects and all source/solver/KCoreText category metadata preserved;
      `validate_universe_contract.py` owns every path with no capability skips and
      machine-checks the exact 67-base + 5-strengthening provenance partition against the
      current `docs/Spec.md`.
- [x] **U-G1 — admit stable total levels and canonical neutral identities.** Check level-term
      typing, totality, lifetime stability, scope, expression lifting, serialization, and rigid
      meta freedom before atomization; decompose only standard operations and preserve opaque
      applications, projections, and immutable snapshots as alpha-stable neutral atoms.
- [x] **U-G2 — separate constructor NF, rigid entailment, and portable inference.** Keep AC/ACI
      normalization syntactic, implement exact paired QF Presburger entailment, implement only
      the specified selected-meta assignment fragment, return all five portable outcomes with
      checked witnesses, and diagnose out-of-fragment inference locally. Selected assignment
      DAGs remain compact until a bounded materialization boundary; over-budget inference or
      entailment returns `IndeterminateResourceLimit` and fails closed, with a regression that
      prevents repeated-meta DAGs from expanding exponentially.
- [x] **U-G3 — rigidly recheck generalized declarations and migrate constraints.** Generalize
      only complete declaration/SCC boundaries, replace candidates with parametric binders,
      recheck all user/generated terms and observation sinks, reject parametric escape, and
      replace authoritative side lists/indexes with ordinary implicit erased proof binders plus
      derived summaries.
- [x] **U-G4 — complete and version KCoreText arithmetic replay.** Add arithmetic/max-least
      proof forms, canonical irredundant assumption dependencies, proof-irrelevant lift identity,
      and independent algebra/normalizer/entailment/inference/certificate version fields to
      KCoreText, interfaces, caches, and semantic hashes.
- [x] **U-G5 — implement same-or-lower recursive schemas.** Allow omitted identity calls,
      require explicit complete non-identity instantiations, reject upward/incomparable and
      implicit non-identity calls with the specified diagnostics, and feed only proved strict
      schema decreases to termination.
- [x] **U-G6 — bound expected-type schema transformations.** Keep direct fully saturated
      `schemaLift` insertion from solving metas or searching intermediates; add expected-type
      schema eta-reification without inventing explicit term arguments; require ordinary
      `PreservesParametricForall` evidence for quantifier interchange.
- [x] **U-G7 — make nominal monotonicity ordinary frozen evidence.** Bootstrap
      `std.typelevel.Monotone`, standard partial-operation instances, and optional separate
      `OrderEmbedding`; select local/global evidence before role inference, record it in the
      closure, reject cycles, and never scan arbitrary theorem declarations.
- [x] **U-G8 — artifacts, harness, metatheory, and closeout.** Add the four aliases, three
      families, and twelve Appendix T assertions; serialize neutral terms, proof summaries,
      recursive edges, selected evidence, and versions; promote all 67 bundle leaves plus 5
      strengthening leaves at owner gates;
      then run the combined U-E/U-F/U-G unit, conformance, interface/KCoreText, interpreter,
      C/LLVM, sanitizer, package, and performance gate.

**U-G exit:** every stable total level term has a deterministic serialized identity; rigid
entailment and portable inference remain distinct replayable contracts; constraints have one
proof-binder authority; recursive schemas, reification, and monotonicity evidence are explicit;
all 67 bundle suites plus 5 strengthening suites are active; and the combined universe
regression gate is clean.

## Track: Logical Nat / Fin / refinements / value arithmetic ([`NAT-FIN-REFINEMENT-PLAN.md`](docs/NAT-FIN-REFINEMENT-PLAN.md))

**Portable contract implemented 2026-07-30.**
`docs/Spec.md` now defines canonical logical `Nat`, generated no-confusion, checked
`derive IsSet` / `derive Eq`, the corrected semiring hierarchy, proof-producing
value-arithmetic providers and certificates, `Fin`, `Refined`, ordinary `Contains`
range membership, symbolic cardinality, representation certificates, and tiered
backend obligations.

The implementation now has ordinary logical `Nat`, checked derivation, the
value-arithmetic solver, refinement surface, independently replayed certificate
artifacts, exact non-unary native execution, verified proof erasure, and
profile-scoped backend classes. The exact 104-suite contract is active under
`tests/conformance/spec-coverage/nat-fin-refinement/`: 102 suites pass in the
conservative profile and the two optional compact-layout suites report
`Unsupported` because that profile does not advertise
`rt-compact-finite-ordinal`, `rt-packed-finite-fields`, or
`rt-unboxed-refinement`.
`scripts/validate_nat_fin_contract.py` owns bundle provenance, paths, categories,
capabilities, stage ownership, and T.12 coverage.
The 2026-07-30 aggregate recheck passed `cabal test all`. A fresh 2026-08-18
active-conformance run passed 4,014 cases with zero failures and the same ten
declared optional/future capability skips.

- [x] **NFR-0 - contract and harness observability.** Implement every new Appendix T
      arithmetic/inhabitance/representation directive through production queries,
      advertise only complete capabilities, convert certificate mutation prose
      into executable fixtures, and add KCore/provider comparisons that distinguish
      inserted transport from conversion and compare actual provider/certificate
      identity rather than only nominal summaries.
- [x] **NFR-1 - logical Nat and exact numeric substrate.** Replace the opaque Nat
      authority with ordinary `Zero`/`Succ` semantics, preserve exact compact
      evaluator/C/LLVM execution, make narrowing explicit, and keep propositional
      arithmetic out of conversion. Verify the boundary with an untransported
      KCore rejection, not by rejecting source that may insert `subst`.
- [x] **NFR-2 - no-confusion and checked derivation.** Generate ordinary verified
      KCore no-confusion packages, make `Eq` refine `IsSet`, implement checked
      `derive IsSet` / `derive Eq`, and reject unsupported shapes without UIP/K.
- [x] **NFR-3 - algebraic hierarchy and value arithmetic.** Land
      `AdditivelyNoncommutativeSemiring`, coherent standard evidence, deterministic
      provider selection, the portable proof solver, automatic explicit transports
      at expected-type boundaries, compact certificates, and mutation-checked
      replay. Portable polynomial replay preserves multiplicative factor order,
      fails closed at deterministic 4096-node/4096-term limits, and compares
      canonical proof/certificate bodies across unrelated-import variants. Keep
      this authority separate from universe-level `TypeLevel` arithmetic.
- [x] **NFR-4 - Fin, Refined, subsumption, and ranges.** Add the proof-carrying
      prelude surface, exactly-once proof synthesis, ownership-preserving
      construction/projection, and ordinary `contains`; retain rejection of special
      `in` syntax.
- [x] **NFR-5 - analysis and representation evidence.** Extend purpose-keyed
      inhabitance, add canonical symbolic cardinality, and produce independently
      checked ordinal, exact-natural, and refinement representation certificates.
- [x] **NFR-6 - KCoreText and artifact trust boundary.** Version, serialize, hash,
      round-trip, and independently verify every certificate before KBackendIR;
      reject forged, stale, context/provider, proof, erasure, and profile mutations.
- [x] **NFR-7 - verified backend profiles.** Require exact non-unary Nat and proof
      erasure on every runnable backend; add certificate-backed finite-ordinal,
      packed-field, and unboxed-refinement classes only where advertised; audit
      dynamic, FFI, bridge, and ABI narrowing.
- [x] **NFR-8 - adversarial closeout and promotion.** Promote the exact 104 suites
      only after every declared outcome and assertion passes, then run full
      conformance/unit, KCoreText/interface/cache, interpreter/C/LLVM parity,
      native exactness, RC/poison/TSan, package, and performance gates.

**Implemented ordering:** NFR-0 landed first; the critical implementation path was
NFR-1 -> NFR-2/NFR-3 -> NFR-4 -> NFR-5 -> NFR-6 -> NFR-7 -> NFR-8.
Logical source/KCore `Nat` remains authoritative throughout. Compact runtime forms
are selected only from verified certificates and never feed back into conversion,
trait search, proof checking, or source reachability.

**Performance closeout (2026-08-18):** the checked generated Prelude artifact
eliminates repeated source elaboration during ordinary compiler startup.
`scripts/check_trivial_compile_budget.sh` now measures a 506 ms cold compile on
the release workstation, below the one-second regression budget.

## Track: Module-wide declaration SCCs / induction-recursion ([`MODULE-SCC-INDUCTION-RECURSION-PLAN.md`](docs/MODULE-SCC-INDUCTION-RECURSION-PLAN.md))

**Specification applied 2026-08-01; implementation pending.**
`docs/Spec.md` now makes top-level declaration order non-semantic (§7.1A),
pairs separate signatures with definitions in either order and across
fragments (§9.2, §36.12), infers recursive groups from typed declaration
facets with header strata and checking SCCs (§9.5), admits ordinary
inductive-inductive and inductive-recursive groups (§10.4.4), derives hidden
phases from the call graph instead of source order (§15.10), and adds KCore
declaration-group records, inductive-group certificates, permutation-invariant
hashes, group-fingerprinted invalidation, and a large Appendix T assertion
surface.

The exact 190-suite contract is staged under
`tests/pending-import/module-scc-ir/` (validated by
`scripts/validate_module_scc_ir_contract.py`); the 2026-08-01 `f1e4161b`
baseline is recorded per-suite in `-- STATUS` lines. Conformance fixtures the
revision invalidates are rewritten and staged under
`tests/pending-import/module-scc-ir/retargeted/`.

**Partial implementation note (2026-08-18):** explicit-measure SCC checking now
derives hidden phases from equal-measure call edges and rejects cyclic phase
constraints; structural descent also follows checked nominal field-projection
evidence. This is a principled MSI-5 foothold, but it does not complete MSI-5
or promote the pending 190-suite module-wide contract.

- [ ] **MSI-0 - contract freeze + harness observability.** New Appendix T
  directives typed and routed through public queries; three new diagnostic
  families registered; unknown capabilities report `Unsupported`.
- [ ] **MSI-1 - module-wide shapes + signature pairing.** §7.1A scope,
  order/fragment-free pairing, inline-signature recursion.
- [ ] **MSI-2 - facet graph, header strata, checking SCCs.** Group
  classification, strict value cycles, group root diagnostics, atomic
  publication.
- [ ] **MSI-3 - joint inductive groups + positivity.** Any-order mutual and
  inductive-inductive data; group GFP positivity;
  `E_DATA_STRICT_POSITIVITY`.
- [ ] **MSI-4 - induction-recursion.** Recursive operations, IR
  admissibility, externality, joint eliminators, definitional equations
  (`Code`/`decode`).
- [ ] **MSI-5 - termination reforms.** Group structural relation;
  call-graph-derived hidden phases; computational-member `decreases` rules.
- [ ] **MSI-6 - KCore/interfaces/hashes.** Declaration-group records,
  inductive-group certificates + mutation rejection, permutation-invariant
  identity.
- [ ] **MSI-7 - incremental + scheduling.** `DeclarationGroupFingerprint`
  invalidation, SCC recomputation on generated syntax, no prefix-environment
  answers.
- [ ] **MSI-8 - promotion + adversarial closeout.** Promote the exact 190
  suites, return retargeted fixtures, permutation fuzzing, forged-certificate
  probes.

**Planned ordering:** MSI-1 -> MSI-2 -> {MSI-3, MSI-5} -> MSI-4 -> MSI-6 ->
MSI-7 -> MSI-8, with MSI-0 first for observability. This revision is the
prerequisite for the future higher/quotient/coinductive nominal features
reserved by §10.5; it deliberately does not deliver them.

## Track: Unified derive / canonical evidence ([`DERIVE-AUTOMATION-PLAN.md`](docs/DERIVE-AUTOMATION-PLAN.md))

**Specification applied 2026-08-02; implementation pending.**
`docs/Spec.md` now defines the unified `derive` elaboration protocol
(expressions, synthesized members/supertraits, whole-instance and
declaration-level deriving), independent `evidence uniqueness` certificates
beside sealed-coherent evidence, `fallback instance` resolution with negative
absence dependencies (the `Eq -> Equiv` bridge is the standard fallback),
portable binder-aware function extensionality + `Reflects` + Hedberg, the
rebuilt `Preorder`/`PartialOrder`/total-`Ord` hierarchy (no `compareTotal`),
lawful `Alternative` under `Applicative`, the proof-automation provider
engine with deterministic logical budgets, and the two-level evidence
identity model of §33.2.1, plus five capabilities and ~30 Appendix T
directives.

The exact 109-suite contract is staged under
`tests/pending-import/derive-automation/` (validated by
`scripts/validate_derive_automation_contract.py`; per-suite
`-- STATUS(3014a0d9)` baselines: 0 pass / 0 fail / 20 unsupported / 89
harness errors). Invalidated conformance fixtures are staged under
`tests/pending-import/derive-automation/retargeted/`.

**Partial implementation note (2026-08-18):** finite-provider `Eq` automation
now proves the generated law surface for tag-coded enumerations through selected
evidence. The unified 109-suite derive protocol remains pending and no DA stage
is marked complete by this narrower support.

- [ ] **DA-0 - contract freeze + harness observability.**
- [ ] **DA-1 - grammar + expression forms.**
- [ ] **DA-2 - extensionality foundation, `Reflects`, h-level closure.**
- [ ] **DA-3 - evidence uniqueness + construction modes.**
- [ ] **DA-4 - instance facet completion + synthesized members.**
- [ ] **DA-5 - fallback instances + `Eq -> Equiv` bridge.**
- [ ] **DA-6 - revised standard traits (h-level, relations, orders, Alternative).**
- [ ] **DA-7 - the derivation engine (providers, induction, helpers, profiles).**
- [ ] **DA-8 - pipeline, KCore, interfaces, incremental.**
- [ ] **DA-9 - promotion + adversarial closeout.**

**Planned ordering:** DA-0; DA-1 -> DA-2 -> DA-3 -> DA-4 -> DA-5 -> DA-6;
DA-7 grows incrementally from DA-2; DA-8 after DA-3/DA-5/DA-7; DA-9 last.

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
- [ ] **C-backend delve renders nothing (C-vs-LLVM miscompile)** — surfaced while
      adversarially exercising delve on the native backends. After the `krun_io`
      OP-driver fix (`0693103`) delve BUILDS and no longer crashes on C, but the
      C-built binary renders **0 bytes** and exits 0: `runLoop` renders then
      `match game.mode case Quit -> exit`, and `game.mode` reads as `Quit` even
      though `initialMenu` sets `MainMenu` ([`engine.game.kp:1476`](examples/packages/delve/src/delve/engine.game.kp)).
      The **LLVM-built** delve renders the full title through the identical PTY
      harness, so it is a genuine C-vs-LLVM divergence, not the harness. Ruled out
      (all `interp==C==LLVM`): traverse order, 5/15-field record updates, the
      `initialMenu` shape, catch-over-parameter, stale runtime objects. Most likely
      suspects: delve's term host-FFI marshalling (`delve_open_terminal2`/
      `delve_write_all2`/`delve_read_key2`) or a `config.loadDefault` combinator
      producing a subtly-wrong pack on C. Deferred 2026-06-25 (the native
      conformance baseline is otherwise green; delve is the only known C holdout).
      See the `c-backend-delve-render-bug` memory for the exact repro.

---

## Track: Runtime spec-coverage gaps ([`RUNTIME-SPEC-COVERAGE.md`](docs/RUNTIME-SPEC-COVERAGE.md))

The `runtime-spec-coverage-audit` workflow (2026-06-26, `file:line`-grounded,
commit `93f20af`) originally mapped kappart2 against the spec's §18/§29/§32.2/
§27.6 MUSTs and found **11 normative-MUST gaps + several PARTIAL refinements**.
The live status is maintained in [`docs/RUNTIME-SPEC-COVERAGE.md`](docs/RUNTIME-SPEC-COVERAGE.md);
as of the current S2.3b work it reports **5 deduplicated normative-MUST gaps**.
This track keeps the remaining worklist and the closed items that materially
changed runtime semantics. The CK-machine core (§32.2 sequential one-shot),
native `rt-blocking`, atomics, STM core, and handler-abandonment drain are wired
and tested; the remaining open items below are still real spec gaps.

**Silent-correctness MUST violations (real bugs):**
- [x] **Handler abandonment cleanup (§32.2.20/.21) — FIXED.** A one-shot handler
      clause that completes without resuming now drains the captured segment
      through `KK_ABANDON`/`KK_ABANDEND` and `begin_abandon_drain`, running captured
      `using`/`defer` actions exactly once in masked LIFO order before delivering
      the clause result. Covered by `runtime/tests/abandon_drain.c` and
      `runtime/tests/abandon_perform.c`; see the implemented row in
      [`docs/RUNTIME-SPEC-COVERAGE.md`](docs/RUNTIME-SPEC-COVERAGE.md).
- [x] **`std.atomic` wired + atomic (§29.1) — FIXED** (commit `67e1d60`). The prelude
      `AtomicRef` ops now lower to boxed, mutex-protected `krt2_atomic_*` cells (was a plain `Ref`);
      proven exact under the multi-worker race test (the old impl lost ~93% of
      updates). Memory-order constructors are validated at the runtime boundary, but
      this does not claim lock-free hardware atomics for arbitrary Kappa values. See
      the Done section.
- [x] **`sleepFor`/`sleepUntil` nonpositive duration parks ~forever (§18.1.6)** —
      fixed in `OP_SLEEP`: durations are read as signed nanoseconds and
      nonpositive values deliver Unit immediately. Covered by
      `test/native/cases/sleep-nonpositive.kp`.
- [ ] **`UnhandledChildFailure` swallowed (§18.1.3/.8)** — an attached,
      never-awaited child that fails is unlinked and its `Exit` discarded
      (`fiber_finish` rt.c:477-496, `scope_detach` scope.c:119-134, root shutdown
      rt.c:1394-1423); it is never aggregated into the scope's `Exit` as a Defect,
      so a failing fork silently vanishes.
- [ ] **`Alternative STM`/`orElse` has no surface instance (§18.1.13)** — runtime
      `STM_ORELSE` rollback exists (`stm.c:60,130-153`) and `Pointed (STM a)` supplies
      `empty = retry`, but no `Alternative STM` instance binds `<|>` to the runtime choice node.
      This is unreachable surface, not an S2.3b mutable-`var` blocker.

**Fairness / blocking MUST gaps:**
- [x] **Safe-points are a no-op (§32.2.5/.6)** — `krt2_safepoint` now polls
      pending interrupts, opportunistically runs another ready fiber for fairness,
      and C/LLVM scalar workers plus boxed generated loops emit counter-gated
      back-edge polls. Covered by `interrupt-tight-loop`,
      `interrupt-general-loop`, and the S2.3b scalar-worker native gates.
- [x] **`rt-blocking` routed for source and classified native calls (§18.1.11 / §18.1.5)** —
      `std.prelude.blocking` builds a real action node, blocking `K_NATIVE`
      actions park the fiber, and the host call runs on an off-worker lane.
      `blocking-cancellable` remains rejected until a safe cancellation bridge exists.

**Reachability gaps (runtime half present, no source path):**
- [ ] **`sandbox`/`unsandbox` no native lowering (§18.1.2)** — declared + in the
      oracle but 0 backend hits → reachable use hard-fails `E_BACKEND_UNSUPPORTED`.
- [x] **`fiberId`/`currentFiberId` wired (§18.1.10)** — prelude surface,
      interpreter ids, and native codegen are present; `fiber-id.kp` pins the
      source-visible identity properties.
- [ ] **Fiber labels absent (§18.1.10)** — `get/set/locallyFiberLabel` + the
      `Fiber.label` field entirely missing.
- [x] **Source-level `blocking` surface wired (§18.1.11)** — `std.prelude.blocking`
      lowers to `krt2_blocking`, while build manifests still resolve
      `std.build.blocking` as the FFI-classification token through config schema
      scoping.
- [ ] **`std.supervisor` is a total stub (§29.2)** — `startSupervisor`/`shutdown`/
      `await` return constants ([`Prelude.hs:3282-3297`](src/Kappa/Prelude.hs)); no
      restart engine/intensity/strategy/cause. (The Missing-primitives DERIVE item
      mentions `std.supervisor`; this is the normative-MUST shape of it.)

**Capability declaration + PARTIAL refinements:**
- [ ] **§27.6 capability decl split needs an authoritative profile story** —
      `KRT2_CAPABILITIES` names runtime implementation features
      {rt-core, rt-parallel, rt-blocking, rt-shared-stm, rt-atomics}, while
      `Backend/Capabilities.hs` advertises the binding-relevant native profile
      {rt-core, rt-blocking, rt-atomics}; reconcile the remaining
      `rt-parallel`/`rt-shared-stm` profile boundary.
- [ ] **PARTIAL refinements** (detail in the doc): §32.2.13 resume does NOT restore
      the capture-point `mask_depth` (resumed body inherits the clause's mask);
      §32.2.12 interrupt/shutdown waits park without raising `mask_depth`;
      §32.2.3 per-do-block supervision scopes aren't created (fork attaches to a
      flat per-fiber scope); §29.1 missing `std.ffi` fixed-width `AtomicValue`
      instances. Multi-shot rejection now emits the mandated
      `E_FEATURE_BACKEND_CAPABILITY_MISSING` / `kappa.feature.gated`
      diagnostic naming `rt-multishot-effects`. The remaining STM RUN-phase
      interruptibility SHOULD deviation is self-documented (`stm.c:25-30`);
      S4 removed the earlier multi-TVar snapshot inconsistency by sampling TVars
      under the STM lock.

### Shortcuts & over-claims to review (the "DONE"/"advertised" may not be real)

Cross-cutting the gaps above — and the reason they hid so long — several runtime
capabilities were implemented as the **easy stub** and then advertised, recorded
as a capability, or marked DONE. These are not missing features anyone forgot;
they are shortcuts that *look* finished. **Audit each before trusting it:**

- [x] **`std.atomic` / "`rt-atomics` honest"** — fixed with the §29.1 atomic wiring:
      `AtomicRef` lowers to the runtime atomic cell and native ops call `krt2_atomic_*`
      instead of the old plain-`Ref` path. Remaining std.atomic gaps are fixed-width/
      polymorphic instance coverage, not the capability being falsely advertised.
- [x] **`rt-blocking` honest** — the native binding profile advertises
      `rt-blocking` because source-level `blocking` and classified blocking calls
      lower to blocking actions and run off-worker. `blocking-cancellable` still
      fails closed.
- [x] **`krt2_safepoint`** — implemented and emitted on generated loop/scalar
      back-edges; the old documented-only stub is gone.
- [ ] **`std.supervisor`** — every entry returns a constant; the only test
      exercises empty-children shutdown, so the stub "passes" a green suite.
- [ ] **`Alternative STM` / `orElse`** — the runtime `STM_ORELSE` path exists, but the surface still
      lacks an `Alternative STM` instance mapping `<|>` to it. `Pointed (STM a)` only supplies
      `empty = retry`.
- [ ] **Parallelism claims need sharper coverage boundaries** — the C runtime advertises
      `rt-parallel` / `rt-shared-stm`. STM now has real cross-worker conservation
      stress in `runtime/tests/stm.c` and is part of the S4 TSan/poison RC corpus.
      Remaining open work: broader cross-fiber happens-before (§32.2.10) stress and
      profile-authority cleanup where the Haskell profile still describes the runtime
      as single-agent.
- [ ] **Verification-methodology shortcut — parity-only checks mask silent boxing
      regressions.** A codegen change can keep `interp==C==LLVM` byte-identical
      while quietly regressing a scalar worker to the **boxed** path (the result is
      still correct; only the unboxing win is lost — invisible to a value-parity
      check). This already happened once (Stage-3 `scalarRep` keyed on the qualified
      `gKey` → Int/Double silently boxed; caught only by `run-native-tests.sh`'s
      alloc/scalar-worker gates, **not** `llvm-parity`; fixed `f9e0bf4`/`c776a9c`).
      Make the native perf gates a **required** check for every codegen change, and
      re-audit earlier parity-only-verified changes for undetected boxing. See the
      `backend-verify-native-perf-gates` memory.

---

## Track: De-hardcoding the compiler↔prelude contract (`Kappa.Builtins`)

An ongoing effort (memory `dehardcoding-builtins`) to drive every compiler-hardcoded
name/fact from a single source of truth ([`src/Kappa/Builtins.hs`](src/Kappa/Builtins.hs))
validated against the prelude at load. **Stages 0–2 done** (Check/Pipeline/Config/
Eval/Interp migrated; the 27 runtime ctor-tags + prim registry single-sourced,
commit `8314f1c`, which is what made the C/LLVM **user-ctor tag-id divergence**
that the delve LLVM-vs-C debug agent caught — `hostCtorTags` vs `gsCollectCtors`
disagreeing — impossible by construction: both now go through
`Repr.assignUserCtorTags`). **Remaining stages** include one with a real latent bug:
- [ ] **Usage.hs hardcoded per-function FACTS → prelude attributes/lang-items** —
      the linearity checker dispatches on magic *names*, not signatures, so
      shadowing/aliasing silently uses wrong demand facts. Flagged by the
      de-hardcoding audit agent; the sharpest is a **latent linearity-soundness
      hole**: `resolveFields` hardcodes `Zipper → [("focus",_),("fill",QOne)]`
      ([`Usage.hs:534`](src/Kappa/Usage.hs)) as a fallback whenever a type named
      `Zipper` is NOT in `aliases` (e.g. a user/imported `Zipper` with a different
      field shape the usage pass can't resolve locally), which can admit
      consumption of fields that shouldn't be consumable. Same name-dispatch smell:
      `builtinFns`/`escapeKindFor` (fork/forkDaemon/forkIn escape kinds, `Usage.hs:505,738`)
      and the `pure`/`ioPure`/`return` taint-preservation list (`Usage.hs:1684`).
- [ ] **Other remaining stages** (low/cleanliness, see the memory): internal markers
      (`__stuck_app`/`__rp`/`__inst_`), FFI scalar ctors (`NativeFfi.hs`), parser/lexer
      soft keywords + magic idents, and the bulk `E_*`/`kappa.*` diagnostic-code strings.

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
- [ ] **Benchmark ports double as differential fixtures** — every cross-language
      benchmark with a reference output is also an `interp == C == LLVM` oracle, so the
      [`CROSS-LANGUAGE-BENCHMARKING.md`](docs/CROSS-LANGUAGE-BENCHMARKING.md) ports (CLBG
      numeric set, AWFY) drop into the conformance corpus as correctness checks too —
      cheap dual-use with the Performance track.

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
- [ ] **Deep-layout parser complexity** — the balanced parenthesis lookahead now avoids the
      former pure-nesting hang and correctly distinguishes parenthesized quantity binders,
      including soft-newline forms, but the existing deep-nesting fixture still takes roughly
      23 seconds and peaks near 780 MiB on the current development machine. Profile and remove
      the remaining superlinear parser-state/backtracking cost without weakening the fixture.

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
