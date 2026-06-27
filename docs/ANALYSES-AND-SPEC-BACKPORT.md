# Analyses & Spec Backport

This document has two parts:

1. **Optimization-enabling static analyses** — a ranked survey of analyses (existing
   and prospective) that would let Kappa generate better code, leading with the
   quantity/usage-inference conformance gaps and the single-use reuse opportunity.
2. **Spec backport list** — an actionable list of what to add/codify/correct in
   `docs/Spec.md`, grounded in this session's runtime/effects/atomics work. Each item is
   tagged **[BACKPORT]** (codify a decision/addition we made), **[CONFORMANCE-FIX]**
   (the impl is behind an already-adequate spec — fix the impl, not the spec), or
   **[DECISION-NEEDED]** (a fork the user must resolve).

> This file is a planning artifact. It does **not** edit `Spec.md`.

---

## Part 1 — Optimization-enabling analyses

**Cross-cutting thesis.** Kappa's differentiator is that QTT (§12) + totality (§15) +
inhabitance (§30.2.7) make facts that Koka / Lean / MLton pay *whole-program inference*
for **available by typechecking** and **already carried in Core** (`Q` on
`CLam`/`CPi`/`CLet`/`CLetRec`/`KBind`, `Core.hs:86`; §12.3 regions; §30.2.7 summaries).
The dominant gap is almost entirely **consumption** — `Repr.hs` / `C.hs` / `LLVM.hs`
reading `Q` / region / inhabitance for allocation placement — **not fresh analysis.**
Today the backend reads `Q` only for *erasure* (`Q0`), discarding `Q1`/`QLe1`
(linear = owned = reusable-in-place).

### 1.1 Ranked table

| # | Analysis | What it enables | Spec status | Kappa state | Priority |
|---|----------|-----------------|-------------|-------------|----------|
| 1 | **Usage-interval reuse (Perceus/FIP from QTT)** | Single-use binder ⇒ in-place ctor/record update + drop-elision; the single biggest residual allocation lever | §34.3.2 permits the rep choice; §31.5 licenses ref/state elision | **Per-binder interval ALREADY computed** as `UseCount [lo,hi]` (`Usage.hs:168-184`); `Q1`/`QLe1` already in Core (`Core.hs:86`). Blocked by two narrow gates + module not exporting the interval. Extend-existing, not build-new. | **P0** |
| 2 | **Escape / region / liveness** | Stack/frame-local alloc of non-escaping values; `ref`→register/SSA (§31.5); fiber/closure-frame **pooling** (~832 B/op fork lever) | §31.5 (ref elision), §34.3.2 (closure-capture omission), §12.3 (escape is sound + local, no whole-program analysis) | §12.3 rigid-`rho` region inference is **already a typechecked local escape analysis** + `captures(s̄)` minimal-set; a **local** `bodyCapturesEnv` ships (`C.hs:629-665`) but is binary/per-loop, not value-granular. Purity+totality make escape EXACT not conservative. Facts computed, not consumed for placement. | **P0/P1** |
| 3 | **Strictness / demand** | Skip `Thunk`/`Need` boxing when a suspension is provably forced (~4–5 `GC_MALLOC`s per suspending bind) | §16.2.2 demand-multiplication is the soundness basis; §34.3.2 permits the rep choice | Kappa is strict-by-default (§32.1) so **no pervasive thunk tax** — but the QTT usage-interval `[lo,hi]` is already computed; a `thunk`/`lazy` with statically guaranteed force (lower bound ≥1) ⇒ build eagerly. Same shape as the landed effect-suspendability Stage-1.5. | **P1** |
| 4 | **Inhabitance for the Optimization purpose** | Drop `Empty` branches; omit storage for `Contractible` fields/payloads/captures/results (§31.2.1); bit-pack small `Finite n`; zero-sized contractible calling-convention slots | §34.3.2 enumerates the uses; §31.2.1 elision; §30.2.9 optional strengthening (incl. \|B\|^\|A\| for finite functions) | `Inhabitance.hs` computes the §30.2.7 lattice but **only for SourceReachability**; the RuntimeShape/Optimization purposes are reserved (`Inhabitance.hs:57-62`) and **not consulted by `Repr.hs`**. `../datatron` is the precise exact-counter reference. *Caveat:* many contractible distinctions are already gone via `Q0` erasure — measure first. | **P1** |
| 5 | **Purity / effect** | Reorder/CSE/hoist/DCE of pure subterms (type-level `IO`/`Eff` rows make purity free to read); elide no-op safepoints on non-blocking stretches; gate one-shot vs multi-shot lowering on the capability witness | §34.3.2 DCE; §32.1 evaluation order = reorder-soundness boundary; §34.3.3 capability gating | Purity is type-level (rows), so available by typechecking. §3.3-style suspendability is *one* effect fact among these; multi-shot gating already partly wired via `E_QTT_CONTINUATION_CAPTURE`. | **P1–P2** |
| 6 | **Cardinality / type-counting** | Small-`Finite n` dense/bit-packed reps (§34.3.2); exhaustiveness (already via SourceReachability) | §34.3.2 | Overlaps (4). The polymorphic **niche is DEFERRED** — payoff eroded under erasure (every polymorphic boundary re-boxes; even GHC declines to niche `Maybe a`, `SPECIALIZATION-SCOPING.md §3.3`). Value is the small-`Finite-n` bit-packing of (4), not the niche. | **P2** (bundle w/ 4) |
| 7 | **Defunctionalization / closure CFA** | Reaching-closures (0CFA) ⇒ direct calls replacing indirect dispatch; closure-layout specialization; **dict/trait devirtualization** (§11.1.4/§11.1.6) | §34.3.7 permits closure-convert/hybrid; §34.3.8 single-ctor wrapper unboxing is a degenerate permitted case | Current closure conversion is per-§34.3.1 `ENVIRONMENT_LOWERING`; no CFA/0CFA pass. Devirtualization is the concrete sub-win; whole-program defunctionalization conflicts with §8.3 separate compilation (like mono). | **P2** |
| 8 | **Totality / termination** | **Enabler/multiplier, not standalone.** Makes ASAP "free at last use" SOUND (no divergence/exception to extend a lifetime ⇒ escape is EXACT); no-cycle SCC reasoning; precondition for δ-reduction / compile-time partial eval (§15.1) | §15.1–§15.3; §15 explicitly allows runtime `while`/`for` in `do` to diverge (Spec L14943) | **Checked** (`Termination.hs`, 813L, with an abstract-arithmetic measure prover). Not a separate build — it is the soundness license already in hand that raises the precision ceiling of (1)/(2). Applies to the **total fragment**, not unrestricted IO loops. | (enabler) |
| — | **Specialization / monomorphization** | Layout specialization, the LLVM niche's "somewhere to live", dict-devirt | §34.3.7 **PERMITS** (keyed only on runtime-relevant rep; erased indices/`Q0`/proofs/rows/regions MUST NOT force distinct specializations) | **DEFER** (`SPECIALIZATION-SCOPING.md §5`): layout payoff eroded under erasure, highest cost + no byte-identical safety net, whole-program mono incompatible with §8.3 separate compilation. Revisit only on a non-perf axis. The cheap S0 hook (CCtor/CMatch typed-Core annotation) is deliberately kept. | scoped-out |

### 1.2 Lead item — Quantity / usage inference: conformance + the single-use reuse signal

**(a) Conformance.** Kappa implements the spec's required usage-interval inference fully
and conformantly inside `src/Kappa/Usage.hs`:

- **Unannotated-binder default = ω — CONFORMANT, implemented** (`Check.hs:3192-3208`; spec
  Spec.md:13156). Kappa does **not** infer `1` from a single use. `Core.Q` has exactly five
  concrete constructors (`Core.hs:86`: `Q0 | Q1 | QW | QLe1 | QGe1`).
- **Usage-interval inference on paths** (§12.2.5, Spec.md:11218-11254; "inferred usage
  interval" Spec.md:2708/1385) — implemented. Per-binding `UseCount{ucLo,ucHi,ucTouches}`
  (`Usage.hs:168-184`); composition operators match the spec exactly: `seqUC` adds
  (sequential §12.2.2), `altUC` min-lo/max-hi at branch joins, `scaleUC` multiplies by
  demand, `loopU` forces lower bound 0 (`Usage.hs:206-272`). Completion-indexed checking
  (Normal/Return/Break/Continue, Spec.md:11223-11231) via `walkItems` + `altUs`
  (`Usage.hs:1265-1269`). `closeVar` is the §12.2.5 scope-boundary check
  (`Usage.hs:890-998`), emitting `E_QTT_LINEAR_DROP` / `E_QTT_LINEAR_OVERUSE` /
  `kappa.quantity.positive-lower-bound`.
- **Lambda quantity-obligation from free-var uses** (§16.2.1, Spec.md:16741-16819) —
  implemented for the interval / positive-lower-bound aspect via a **latent multiset**
  (`WalkResult.wrLatent`, `Usage.hs:368-373`; `taintLatent`, `1365-1368`; stored in
  `VInfo.vLatent`, `2017`) folded in at exactly-once consumption (`flatR`) and multiplied
  by the consumer's demand interval (`scaleUC`) — precisely §16.2.1's
  `[l_closure,u_closure]·[l_body,u_body]`. **PARTIAL:** the §16.2.1 "linear contamination"
  rule (a closure capturing a `1`-var must itself be a quantity-`1` value) is enforced only
  *indirectly* through latent-scaling, never as an explicit inferred closure quantity — so
  store/return escape paths that don't re-consume locally are not contamination-checked the
  way the spec phrases it. The borrow-capture half IS modeled via the taint path
  (escape check `Usage.hs:781-806`).
- **GAP — quantity-metavariable solving / `QuantitySatisfies`** (§12.2.1–§12.2.4, §9031 =
  Spec.md:9029-9032) — **NOT implemented** (structural absence). `QuantitySatisfies` appears
  in **zero** source files. `Core.Q` has no metavariable constructor, so the elaborator never
  *creates* a quantity metavariable — nothing to default (§9031), solve (§12.2.4), or reify as
  an implicit premise (§12.2.3). Symbolic/quantity-polymorphic binders
  (`forall (q:Quantity)`, Spec.md:10629-10647) are **approximated**: `qOf (QTerm) = QW`
  (`Check.hs:3200`), `pDemand` treats `QTerm` as exactly-once (`Usage.hs:112`). A program
  relying on `QuantitySatisfies` evidence discharge (the `useOnce`/`ignore` examples,
  Spec.md:10674-10710) is not checked through the spec's obligation mechanism. **This is the
  single biggest conformance gap in the quantity area.**

**(b) The single-use reuse signal — already present.** The reuse signal the optimization
task wants ("a binder USED ONCE ⇒ in-place reuse") is exactly `ucHi == 1` (or
`length ucMoves == 1`) on `UseCount` (`Usage.hs:168-184`), computed for **every** binding the
walk places into the Usage map, via the same `seqUC`/`altUC`/`scaleUC` arithmetic used for
checking. The signal does **not** depend on the declared quantity (ω for unannotated) — it is
read off the **inferred** count, exactly as framed.

What blocks using it as a universal reuse analysis today is **two narrow gates** plus an
export omission — not missing analysis:

1. **`countedQ`** (`Usage.hs:2077-2082`) maps `QOmega → Nothing` and `QTerm → Nothing`, and
   `closeVar`'s `case vQ vi` (`Usage.hs:987-998`) only fires on `QOne`/`QAtLeastOne`/`QAtMostOne`.
   So ω/unannotated binders — the overwhelming majority — get their interval **computed and
   then discarded** (fall through to `_ -> pure ()`). The interval is present in `u` at the
   `closeVar` call site; only the *check* is gated off, not the *computation*.
2. **`sBail`** (`Usage.hs:306-307`, gate at `analyzeDecl` `Usage.hs:473-477`): a definition
   containing any unmodeled construct is dropped wholesale (returns `[]`). Correct for a
   conservative reject-only purpose; for an optimization purpose it just means "no reuse hint
   here" (safe default = box/refcount as usual).
3. **Export omission:** `Usage.hs` exports only `PInfo`/diagnostics/`tailResumptiveClause`
   (lines 56-62); the per-binder interval never leaves the module.

**Assessment — extend-existing, the direct analogue of the Inhabitance
SourceReachability-vs-Optimization purpose split.** Concretely:
(i) add an **Optimization "purpose"** that keeps the computed `UseCount` for ALL bindings
instead of gating on `countedQ`/`vQ`;
(ii) **export** the per-binder `ucHi`/`ucMoves`;
(iii) consume `ucHi <= 1` in the backend as a static reuse precursor (candidate in-place
reuse / no dup — the static analogue of Perceus's RC-1 drop-and-reuse).
The hard arithmetic (sequential add, branch min/max join, demand/latent scaling,
completion-path alts, path-sensitive §12.4 events) is **already written and sound where it
runs**; the work is purpose-plumbing + an export + a backend consumer.
*One mismatch to fix for an optimization read:* `closeVar`'s linear path downgrades
`QOne → QAtMostOne` via `countedQ` at the effect-op site (`Usage.hs:1299`) but `lamBind` stores
raw `QOne` (`Usage.hs:1471`) — an optimization purpose should read `ucHi` directly and ignore
`vQ` entirely, sidestepping this.

**Literature.** Target technique: **Perceus reuse analysis** (Reinking, Xie, de Moura,
Leijen, PLDI 2021 — <https://xnning.github.io/papers/perceus.pdf>), the basis of Koka's
functional-but-in-place (FBIP). Koka derives reuse from RC-driven liveness; the *static
precursor* is exactly a per-binder dup/drop usage count — which `UseCount` already is.
FIP/borrow inference: Lorenzen master thesis
(<https://antonlorenzen.de/master_thesis_perceus_borrowing.pdf>). ASAP / region late-alloc-
early-free: Aiken–Fähndrich–Levien, "Better Static Memory Management," PLDI'95
(<https://theory.stanford.edu/~aiken/publications/papers/pldi95.pdf>). Couples naturally with
the planned LLVM-backend Perceus RC work (`representation-is-llvm-layout` /
`llvm-backend-foundation`).

---

## Part 2 — Spec backport list

Grounded in this session's runtime / effects / atomics / capabilities work, against
`docs/Spec.md`. **[BACKPORT]** = codify a decision/addition (spec is silent or imprecise);
**[CONFORMANCE-FIX]** = impl is behind an already-adequate spec (do not change the spec);
**[DECISION-NEEDED]** = a fork the user must resolve.

### Load-bearing decision

**[CONFORMANCE-FIX] — masking `restore` rank: KEEP rank-2, fix the impl** (resolved 2026-06-27,
[`MASKING-RANK-RATIONALE.md`](MASKING-RANK-RATIONALE.md); was `[DECISION-NEEDED]` — the
relax-to-rank-1 recommendation is **OVERTURNED**).
Spec §18.1.12 (Spec.md:19063-19066) mandates **rank-2**:
`mask : forall e a. ((restore : forall (x:Type). IO e x -> IO e x) -> IO e a) -> IO e a`.
We shipped **rank-1**: `__mask`'s `restore` is monomorphic `IO e a -> IO e a` (instantiated at
mask's own result type `a`), `Prelude.hs:561-566`. The runtime `restore` is one 1-arg closure
(`krt2_mask` / `OP_RESTORE`); a rank-2 `restore` emits an erased implicit type-application
`kappi(restore, ⟨x⟩)` that the 1-arg closure consumes *as* the action ("non-function value" crash).
**Resolution — keep rank-2, make the impl conformant.** The research established: rank-2 is the
*universal* `mask` idiom across the GHC (`forall a. IO a -> IO a`) → Cats-Effect (`Poll[F] = F ~> F`)
→ ZIO (`InterruptibilityRestorer`) lineage Kappa's ZIO-flavored IO descends from, where the `forall`
is load-bearing (one captured masking capability applied to sub-actions of caller-chosen types). The
"never exercised" premise is **false going forward**: compiled `kappa check` counterexamples prove
rank-1 rejects the canonical idiom — `restore getInt` + `restore getStr` into a `P Integer String`
result gives `E_APPLICATION_ARGUMENT_MISMATCH`, and *even a single* restore at any non-result type is
rejected (the first non-trivial `mask` body a user writes; cf. Cats-Effect `bracketFull` applying one
`poll` at both resource type `A` and result type `B`). It holds only for the shipped corpus
(`bracketM` applies restore once at the result type).
**The fix:** lower `restore`-application to **drop** the erased `kappi(restore, ⟨x⟩)` type-app before
the 1-arg closure — NOT a monomorphisation, no ABI/closure rewrite (the runtime restore is already
type-erased + uniformly boxed). If deferred, ship rank-1 only as a **marked KNOWN RESTRICTION**
(restore cannot apply where the resource type differs from the mask result, breaking standard
`bracket`), never justified by the false "never exercised" claim.

### Effects / handlers / continuations

**[BACKPORT] B1 — codify the KK_HANDLER prompt-frame model as a §32.2 reference realization.**
§30.2.2.7 (Spec.md:33065-33127) gives KCore structure and §32.2.13 (Spec.md:35222-35243)
defines the captured-continuation boundary, but the runtime operational model is left fully
implementation-defined. We have implemented + validated a concrete unified model on one heap
`Cont` chain: `handle`/`deep handle` installs a `KK_HANDLER` frame on `f->k` carrying
(label-value, `Handler*`, saved `cur_exits`, deep-flag) (`internal.h:163-180`, `rt.c:226-227`);
`perform` = a resumable generalization of `unwind`, capturing (not discarding) the
op-site→handler sub-chain (`rt.c:789-875`); `resume k v` = a deliver-splice, twin of deliver's
`KK_BIND` arm (`rt.c:877-919`). This is the Hillerström–Lindley CK-machine + multi-prompt
delimited control. Add a non-normative appendix (companion to N.2) presenting it as ONE
conforming realization — two repo docs (`RESEARCH.md` two-world vs `CPS-DESIGN.md` unified)
currently contradict each other; blessing the unified substrate resolves it.

**[BACKPORT] B2 — make the §32.2.20 exit-action-ESCAPE restriction testable + clarify it is
distinct from §18.1.20.** §32.2.20 (Spec.md:35370-35374) + §18.1.21/.22 say a resumption whose
captured segment contains pending exit actions MUST NOT escape the operation clause. This is
**different** from the §18.1.20 multi-shot duplicability rule (Spec.md:19451-19473): §32.2.20
applies to **any** resumption (incl. one-shot) that escapes carrying pending defers; §18.1.20
applies only to multi-shot and is about clone-duplicability. Only the §18.1.20 check exists
(`Usage.hs:2087-2096`, `2452-2474`, `E_QTT_CONTINUATION_CAPTURE`); the §32.2.20 escape check is
absent (`RUNTIME-SPEC-COVERAGE.md:200`). Tighten §32.2.20 to define the exit-action-escape
predicate over the §32.2.13 captured segment precisely, and cross-reference that it is NOT
§18.1.20's rule, so a conformance test can be written. Coupled CONFORMANCE-FIX: add the actual
escape check (see C1).

**[BACKPORT] B3 — bless the one-shot-default + `rt-multishot` gate as normative (only a
name/witness nit).** GOOD NEWS: the gating is **already normative** — §18.1.17
(Spec.md:19311-19327), §27.6 (Spec.md:28539-28562), §34.3.9 (Spec.md:38071-38073) — and our
impl conforms (`Check.hs:7604` records `csMultishotOps`; `Backend/C.hs:498-513`
`multishotLegality` scans main's reachable closure and rejects). **Do not relax.** The one
correction: the spec capability is spelled `rt-multishot-effects` (Spec.md:28499, 28539) but
our runtime/diagnostics/docs use the short `rt-multishot` (`rt.c:887-889`, `internal.h:101`,
`Backend/C.hs:509`). All five other capabilities match the spec verbatim — **rename the impl to
`rt-multishot-effects`** (this is the CONFORMANCE-FIX route, recommended) or add `rt-multishot`
as an accepted short name (BACKPORT route). Also confirm/bless our backend-closure scan as
equivalent to the §34.3.4 KBackendIR multi-shot witness, or treat the missing witness as a
small CONFORMANCE-FIX.

**[BACKPORT] B4 — bless the deep-vs-shallow reinstall-frame realization (no semantic change).**
§18.1.22 (Spec.md:19721-19735) desugars `deep handle` to a shallow handler + recursive `__go`
driver; §32.2.22 (Spec.md:35425-35433) requires reinstall-then-resume; §18.1.21 says shallow
does not auto-reinstall. Our impl realizes deep by a runtime reinstall-flag rather than the
source-level driver: `do_perform` records `(label, Handler*, handler_exits)` on the Resumption
for deep handlers (`rt.c:865-869`); `do_resume` re-pushes a fresh `KK_HANDLER` beneath the
spliced body (`rt.c:910-913`); shallow skips this (`rt.c:867-868`). Observationally equal to
§18.1.22's desugaring and matches the `Eval.hs` oracle's `reinstall cont`. §30.2.2.7:33122
already permits no distinct primitive. Note in the B1 appendix that deep reinstall MAY be a
runtime frame-rebuild, not the literal `__go` driver, provided §32.2.22 holds.

**[BACKPORT] B5 — add an explicit constant-Cont-depth obligation to §32.2.15 (tail-resumptive).**
§32.2.15 (Spec.md:35260-35281) + Appendix N.2 permit in-place transfer "without general
resumption capture," and §34.3.9 (Spec.md:38079-38086) forbids applying it merely because
local control is a jump. Our impl does exactly the permitted optimization (`rt.c:822-847`
fast path; `Usage.hs:2098-2174` `tailResumptiveClause`): when a DEEP clause resumes `k` exactly
once in tail position, the op-site→handler segment is not severed, no `Cont` is allocated, the
`KK_HANDLER` is never popped/re-pushed — constant `Cont` depth across an effect loop. But the
spec only says the optimization "MAY" be done; it never states the **space guarantee** that
motivates it. Add a (possibly non-normative) note that a conforming tail-resumptive realization
SHOULD NOT grow the captured-continuation representation across repeated tail resumptions —
else an implementer can "conform" with an unbounded-growth realization that defeats the purpose.
The scoping doc already mandates this as a test (`EFFECT-HANDLER-SCOPING.md:439-442`).

**[BACKPORT] B6 — specify handler-clause PARKING under an `IO e` carrier (genuinely
under-specified).** §18.1.21/.22 (Spec.md:19604) explicitly permit a handler clause running
under `IO e`, but nowhere does §32.2 state that such a clause (or a resumption it triggers) may
park/await/fork on the scheduler, nor what the captured resumption + its mask/exit-action state
must do across a park/wake. §32.2.13 says the captured continuation includes the
interruption-mask state; §32.2.1 lists "handler capture/resume/abandon" alongside
"suspend/wake" — but the **interaction** is unspecified. Add an obligation that (a) a captured
resumption remains valid and GC-reachable across a clause park/wake; (b) an interrupt delivered
to a parked clause that then exits without resuming triggers §32.2.20 abandonment of its
captured segment (§32.2.21's last paragraph, Spec.md:35417-35419, half-covers "fails or is
interrupted before resuming" but not the PARKED case). Without this the IO-carrier permission is
a semantic hole. The scoping doc calls this the highest-uncertainty item
(`EFFECT-HANDLER-SCOPING.md:465-475`).

**[CONFORMANCE-FIX] C1 — handler abandonment (§32.2.20/.21) is BROKEN at runtime (most urgent,
now LIVE).** §32.2.20 (Spec.md:35358-35377) + worked example §32.2.21 (Spec.md:35380-35422)
**MANDATE**: a clause that completes without resuming `k` MUST unwind the captured do-scope
frames exactly once and run their pending exit actions in masked LIFO before the clause result
is observable; §32.2.21's last line MUST NOT drop the captured continuation without unwinding.
Today `do_perform` severs `[head..prev]` into `Resumption r->head` (`rt.c:856-861`); if resume
is never called the slice is GC'd and the defers/using **never run** — no path runs
`begin_finseq` over `r->head` (`RUNTIME-SPEC-COVERAGE.md:172,200`). **Critical new fact making
this live:** the §3.3 elaborator restriction has been **lifted** — `elabEffDo`
(`Check.hs:8003-8021`) now accepts `DoDefer`/`DoUsing` and wraps the block in `prelEffDoscope`
(`krt2_doscope`/`krt2_defer`, `Check.hs:8014-8016`), so an `Eff` do-block can now carry
exit-action frames and the abandonment path is structurally reachable. Fix: `do_perform`/
`do_resume` must run `begin_finseq` over the abandoned `r->head` when the clause completes
without resuming. Couple with B2 so the §32.2.21 worked example becomes an authored test
(both `using` release and `defer` run exactly once masked-LIFO before `pure 0`;
`useResource r` NOT run).

**[CONFORMANCE-FIX] C2 — §32.2.12 failing-finalizer cause composition on the abandonment path.**
§32.2.12 (Spec.md:35191-35213): a finalizer that itself fails composes via `Then` and remaining
finalizers still run. Our runtime abandons remaining finalizers and does not `Then`-compose on
the failing path (`rt.c:973-981`, self-admitted; `RUNTIME-SPEC-COVERAGE.md:175,203`). Spec is
adequate; impl is the gap. Lands on the same abandonment drain as C1 — fix together.

### Concurrency / runtime / atomics / capabilities

**[BACKPORT] A1 — §29.1 std.atomic memory-order ABI encoding.** The order ADTs
(`LoadOrder`/`StoreOrder`/`RmwOrder`/`CasFailureOrder`, Spec.md:30798-30818) are spec'd as
typed Kappa values, but the spec is **silent** on the runtime ABI lowering. Our impl crosses the
boundary as a small Integer **code** = the constructor's declaration-order index, wired via
`*OrderCode : Order -> Integer` (`Prelude.hs:3147-3184`) read by `kas_int` at the ABI
(`atomic.c:81-113`). Codify a §29.1 note that the encoding is **backend-private and
source-unobservable** (the source surface is the ADT, never the Integer — no portable program
can depend on the numbering). Optionally bless declaration-order as the canonical lowering.

**[BACKPORT] A2 — add four ZIO-parity primitives to the §18.1/§29 surface (currently additions
with no spec home).**
- `onExit : forall e a. IO e a -> (Exit e a -> IO e Unit) -> IO e a` (`Prelude.hs:617-622`) —
  Exit-carrying generalization of `ensuring`. Home: §18.1.12, as a derived/standard combinator.
- `onInterrupt : forall e a. IO e a -> (InterruptCause -> IO e Unit) -> IO e a`
  (`Prelude.hs:626-630`) — handler fires only on interrupt exit. Home: §18.1.12.
- `pollPromise : forall e a. Promise e a -> UIO (Option (Exit e a))` (`Prelude.hs:698-702`) —
  non-parking peek (`isDonePromise` derivable as `isSome . poll`). Home: §18.1.9
  (Spec.md:18943); the spec's promise API has no non-blocking inspector. The spec must pick the
  name to avoid clashing with §18.1.12's interrupt-poll (a Promise-qualified name is warranted).
- `modifyFiberRef : forall a. FiberRef a -> (a -> a) -> UIO a` (`Prelude.hs:603-606`) —
  trivially atomic (per-fiber), sugar over `get >>= set`. Home: §18.1.7 (Spec.md:18837), which
  lists only `new`/`get`/`set`/`locally`. The spec must pin the return convention (we return the
  **new** value; ZIO returns a projected `b`).

**[BACKPORT] A3 — §27.6 single-source capability obligation.** §27.6 (Spec.md:28490) says every
backend profile MUST declare a capability set, but not that within one implementation every
internal representation of that set MUST agree. We have **two disagreeing copies**:
`rt.c:17-19` `KRT2_CAPABILITIES = {rt-core, rt-parallel, rt-shared-stm, rt-blocking,
rt-atomics}` vs `Capabilities.hs:30` `nativeRuntimeCapabilities = {rt-core, rt-blocking,
rt-atomics}` (only the Haskell list is consumed; the C list is dead, `kappart2.h:250`). Add a
MUST that the capability set is single-authoritative and any secondary copy MUST be derived from
or checked against it. (Which list is *correct* is the separate CONFORMANCE question C3.)

**[BACKPORT — optional micro-notes] A4 — three areas the spec already covers; no change needed.**
- **Multi-shot withhold-and-reject** is already correct: §27.6 names `rt-multishot-effects`
  (Spec.md:28499,28539-28542); §18.1.17/§34.3.3 already mandate rejecting reachable multi-shot
  (Spec.md:19322-19325). **No backport** — only the token spelling is wrong (C1-cap below).
- **`run_main` re-entrancy / persistent-runtime** is impl latitude: §40 models runtime-init and
  process-exit as profile-recorded fields (Spec.md:40777-40781, 40808-40815) and enumerates
  entrypoint kinds (40783-40796) without mandating a `run_main` shape. **No backport** unless
  cross-backend re-entrancy becomes a portable goal.
- **FiberRef copy-on-fork** (§18.1.7, Spec.md:18860-18862) is already precise: snapshot copy +
  post-fork independence fully fix observable semantics and correctly leave eager-vs-CoW open;
  our deep-copy conforms (`internal.h:208-243`). Optional micro-note only: state that the value
  bindings are copied but the bound values themselves are shared.

**[CONFORMANCE-FIX] C-cap-1 — multi-shot capability token spelling.** Code/diagnostics use
`rt-multishot` (`Explain.hs:250`, `C.hs:505`, `rt.c:829/887`, `internal.h:101`); the spec token
is `rt-multishot-effects` (Spec.md:28499). Behavior is correct; only the string is wrong.
(Same item as B3's correction, viewed from the impl side.)

**[CONFORMANCE-FIX] C-cap-2 — multi-shot rejection diagnostic code/family.** We emit
`E_BACKEND_UNSUPPORTED` / `kappa-hs.backend.unsupported`; §18.1.17 mandates code
`E_FEATURE_BACKEND_CAPABILITY_MISSING`, family `kappa.feature.gated` (Spec.md:19337-19338).

**[CONFORMANCE-FIX] C-cap-3 — capability *content* mismatch (over/under-advertising).**
Independent of A3's "they must agree" rule:
- `rt.c` advertises `rt-parallel`/`rt-shared-stm` (backed by real `nproc` OS-thread workers,
  `rt.c:1341-1413`) but `Capabilities.hs:30` does not, and its comment falsely calls the runtime
  "single-agent and synchronous" (`Capabilities.hs:19-24`) — **under-advertised**.
- `rt-blocking` is advertised by both, but `krt2_blocking` is identity (`rt.c:91-97`, no
  `uv_queue_work` offload) — **over-advertised** vs §26.1.4:26664-26665 (MUST NOT starve
  unrelated fibers) and §27.6:28527-28530.
- `rt-atomics` is over-advertised: RMW/CAS are lowered to non-atomic `readRef`/`writeRef`
  (`atomic.c` dead) vs §29.1:30886-30888 (MUST). All us-behind-spec; the spec is already correct.

---

### Quick index of the most urgent items

- **Most urgent impl gap (in progress):** C1 — handler abandonment, structurally broken + now
  *reachable* (`elabEffDo` opened to `defer`/`using`). The one-shot drain landed (`a374abb`); the
  nested-abandon (H1), drain-time failure (H2) and §32.2.12 cause-composition (C2) follow-ups are
  in fix-forward. A §32.2.20/.21 MUST.
- **Load-bearing decision (RESOLVED):** masking `restore` — **keep rank-2, fix the impl** (drop the
  erased `kappi` type-app), not relax §18.1.12; see [`MASKING-RANK-RATIONALE.md`](MASKING-RANK-RATIONALE.md).
- **Biggest conformance gap (quantity area):** `QuantitySatisfies` / quantity-metavariable
  solving (§12.2.1–§12.2.4, §9031) entirely absent.
- **Highest-payoff optimization (extend-existing):** Perceus-style single-use reuse from the
  already-computed `UseCount` interval.
