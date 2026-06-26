# Specialization Scoping

Status: scoping decision document. Decides whether to invest in a
specialization / monomorphization pass to unblock type-directed (niche)
runtime layout. The short answer is up front in §6; the case is built in
§1–§5. Every claim is grounded in source (`file:line`) or spec (`§ref`).

This document subsumes and formalizes the verdict already reached with the
user on 2026-06-26 (memory `niche-layout-vs-type-erasure`; `ROADMAP` Stage 4
DEFERRED) and adds the spec-conformance and prior-art analysis behind it.

---

## 0. The question, precisely

Kappa compiles polymorphic code to **one shared runtime body over uniformly
boxed values**. `Option Int` and `Option a` lower to the same body and the
same heap layout because the only type-distinguishing input — the type
argument `@T` — is **erased to `kunit()`** at codegen. The Stage-4 niche /
discriminator layout pass exists in the IR design (`src/Kappa/Backend/Repr.hs:16`)
but is *starved of input*: with types erased there is nothing per-instantiation
for it to read.

The proposed unblock is a **specialization pass**: clone a polymorphic body
per concrete instantiation while the types are still present, so that
`Option Int`'s body can pick a niche-able layout that `Option a`'s body cannot.

This doc asks: is that worth building? It is a large, cross-cutting,
elaboration+IR+backend change with no byte-identical safety net. We need to be
honest about the payoff before committing.

---

## 1. What "specialization" concretely means for Kappa given erasure

### 1.1 The erasure baseline (why the question even arises)

There is **no physical erasure pass**. KCore *is* the elaborated `Term` IR
(`src/Kappa/Core.hs:102-164`), which carries types, proofs, and dictionaries
as ordinary terms right through the tree-walking interpreter. Erasure is a
thin, **late, per-argument codegen rewrite** in the C/LLVM backends, not an
IR-to-IR transform (`docs/audit/lane-types.md:180-181` marks the §31.2
physical-erasure pass `INTENTIONALLY-UNSUPPORTED(partial)`).

Two backend mechanisms do the erasing:

1. Syntactic per-arg erasure — `isErasableArg` / `compileErasableArg`
   (`C.hs:1707-1731`): a value-position argument that is a type-level syntactic
   form (`CSort`/`CPi`/`CVariantT`/`CRecordT`/`CMeta`/`CQuote`, or a head that
   `isTypeGlob`) becomes `kunit()`.
2. Telescope-driven spine erasure — `erasedSpinePositionsP` / `eraseQ0ArgsP`
   (`C.hs:979-1033`), invoked from `compileApp` (`C.hs:2128-2134`): walks the
   head's `gdType` Pi telescope and erases each position iff `q == Q0` **or**
   the domain is a kind (`isKindDomain`). So in `map @a @b f xs`, `@a @b`
   become unit slots.

What is **kept**: trait **dictionaries** and method projections. A dict's
domain is a trait type `C a : Type` — an inhabitant of a kind, not a kind — so
`isKindDomain` is False for it and it survives as a real `QW` runtime value
(`C.hs:997-1000`; Spec §31.2.1 `docs/Spec.md:34718`; §14.4 "IsTrait does not
imply RuntimeErased"). Dispatch is a runtime record-field projection
`CProj dict member` (`Check.hs:5992-5999`). **This is classic GHC/Swift-style
dictionary-passing, type-erasing.** Kappa today is squarely the
*pre-specialization* end of the spectrum (Spec §9436: "a method-bearing trait
such as `Eq a` may be subsingleton while its method projection is still
runtime-relevant **before specialization**").

### 1.2 Three distinct things people call "specialization"

These must not be conflated; the spec and the prior art treat them
differently.

- **(A) Full whole-program monomorphization (MLton/Rust).** No polymorphic
  code survives to runtime; every use of `Option a` becomes a distinct
  monotype with its own layout, then representation selection niche-packs each.
  Requires a **closed world** (no separate compilation in MLton's case).

- **(B) Targeted / opportunistic specialization (GHC `{-# SPECIALIZE #-}`,
  Swift WMO, OCaml flambda).** Opt-in, demand-driven clones at concrete types,
  *local or per-package*; cross-module only when the body is exposed in the
  interface artifact. The default stays uniform; specialization is an
  optimization layered on top, **never a correctness precondition**.

- **(C) Runtime representation-passing (Swift value witness tables).** Do *not*
  duplicate the body. Pass a layout witness (size/align/copy/move/niche
  descriptor) alongside the dictionaries Kappa already passes, so one generic
  body manipulates unknown-layout values at runtime. Keeps separate
  compilation; pays runtime indirection; gives a *runtime* layout decision, not
  a *static* LLVM niche.

For Kappa the live options are **(B)** and **(C)**. **(A)** is structurally
incompatible (§3.3, §5).

### 1.3 The intervention point

Any specializer **must run on the elaborated `Term` IR before backend
codegen erasure** — before `compileApp` / `eraseQ0Args` / `compileErasableArg`
collapse types to `kunit()`. At that stage the concrete type argument is still
present at each call site. The pass clones `f`'s body monomorphized to `T`,
and re-points the construct/match sites at the concrete head type. The erasure
machinery downstream is *self-adjusting*: a monomorphic clone `f_Int` has a
`gdType` telescope with no kind-domain type binder, so `erasedSpinePositionsP`
naturally flags nothing spurious there — **no change to the erasure code is
needed** (erasure findings, implications).

The natural anchor already exists: `CCtor`/`CMatch` carry an optional,
**observe-only** monomorphic head-type annotation (`Core.hs:117-131`,
populated from `sTy1` at `Check.hs:8542-8547`), built explicitly "for the
(later) niche/discriminator work." It is deliberately ignored by every backend
and dropped by `Eq Term` / conversion (`Core.hs:122-131, 184-186`). To
become load-bearing it must be (a) populated everywhere construct/match happen
(`CCtor`'s slot is `Nothing` almost everywhere today — the one `Just` is the
§13.2.10 narrowing arm `Check.hs:6522`), (b) read by the backend for layout,
and (c) carried on `CPCtor`, the match-arm pattern, which has no type field at
all (`Core.hs:260`).

---

## 2. Design options and tradeoffs vs the spec

The spec **permits** specialization explicitly and even **anticipates** it for
dictionary removal — it does *not* block this. But it constrains *how*, and one
clause (§34.3.7) cuts directly against the naive framing. The framing shift the
doc insists on: **erasure does not forbid niches; it forbids the layout
decision from leaking to runtime.** The blocker is the *implementation's*
uniform-boxed representation class plus §34.3.7's keying rule, not erasure
per se (spec-stance findings, point 2).

### Hard spec constraints any pass must satisfy

1. **Key by runtime representation class, not by source type.** §34.3.7
   (`docs/Spec.md:37971-37986`): "Implementations MAY monomorphize,
   dictionary-pass, closure-convert, or use any hybrid strategy" — *but*
   "specialization MUST be keyed only by runtime-relevant representation.
   Erased indices, quantity-`0` arguments, proofs, row arguments, region
   arguments … MUST NOT by themselves force distinct runtime specializations."
   Since `@T` is erased, `Option Foo` and `Option a` differ *only* in an erased
   index. You may **not** specialize "on the source type." You may specialize
   only when `Foo`'s **runtime representation class** (e.g. niche-able heap
   pointer) genuinely differs from the uniform-boxed class. The keying function
   *is the whole game*.

2. **Decide layout entirely at compile time; carry no residual runtime
   dependence on the erased type.** §31.2 / §30.2.3A (`Spec.md:34629-34691,
   33484-33568`): erased data must disappear and "A KBackendIR term MUST NOT
   contain a runtime dependency on a KCore occurrence whose only available
   value was erased" (`34683`); a legality verifier MUST reject violations
   (`34688-34690`). So the layout choice must be made during
   REPRESENTATION_SELECTION over still-typed KCore, and the emitted KBackendIR
   must not recover the type at runtime to pick a layout. Fine for option (B):
   the type *is* known at compile time at each instantiation.

3. **Hold every observational-equivalence and boundary invariant.** §34.3.8
   (`Spec.md:37989-38016`): representation-class specialization, dictionary
   specialization, wrapper erasure, etc. MUST preserve source-level behavior;
   "If an implementation cannot prove that a wrapper specialization is
   observationally equivalent, it MUST decline that optimization" and emit
   `E_BACKEND_SPECIALIZATION_SEMANTICS` (`38012-38016`; diagnostic at
   `Spec.md:1033-1034`). §34.3.9 forbids weakening handler/resumption
   semantics. §34.3.2 external-boundary restrictions (`37858-37868`) and
   §34.3.8 (`38000-38010`) pin exported ABI/FFI, bridge contracts,
   Dyn/DynRep/DynamicType, stable variant `TagId` (§31.3/§34.3.2:37848-37856),
   and forbid collapsing semantically-distinct nominal/opaque types in
   diagnostics/reflection/Dyn. **Internal bodies are free; every external
   boundary is pinned.** A niche chosen for `Option Foo` must still respect
   `Foo`'s opacity and not leak through Dyn/reflection.

### Freedoms the spec grants

- **No fixed pass ordering.** §34.3.1 (`Spec.md:37823-37824`): conceptual
  stages MAY be fused/reordered if the result is observationally equivalent. A
  specialization pass may interleave with ERASURE and REPRESENTATION_SELECTION.
- **Firewalled from source acceptance.** `Spec.md:9040-9047`: backend
  specialization keys / layout classes are not source-level inference
  variables and MUST NOT affect what type-checks. A mono pass can be added or
  changed freely without altering source acceptance.
- **Inhabitance is the sanctioned lever.** §31.2.1 / §34.3.2
  (`Spec.md:34693-34728, 37827-37871`) bless compact/niche layouts when
  inhabitance analysis proves no runtime observation distinguishes
  alternatives — *but* §34.3.2 (`37870`) forbids treating `Unknown` inhabitance
  as finite/Contractible/etc. A polymorphic `Option a` has an **`Unknown`**
  payload shape, so you may **not** niche-pack it as-is. Monomorphizing
  `Option Foo` turns `Unknown` into a concrete shape that §31.2.1/§34.3.2 then
  let you niche-pack. **This is the formal justification for investing in
  mono** — and equally the proof that mono is *required* before niching.

### The separate-compilation tension (the architectural crux)

Kappa has genuine, cryptographically-identified separate compilation: §8.3.4
(package-mode reproducible builds), §8.3.7 (effective import environment,
module-interface identity, semantic hashes, dependency closure). The interface
artifact is "backend-independent" and carries a `SemanticCertificateSummary`
(typing/quantity/erasure surface) — **not** a committed runtime layout or a
single shared body (spec-stance findings, point 6; `Spec.md:36260-36344`).

Consequences:

- Whole-program / link-time mono is **permitted** (the interface pins no
  shared body), but downstream compilation "MUST be sufficient … without
  consulting the defining module's source text" (`Spec.md:36268-36269`). So
  specializing an *exported* generic at a *downstream* call site requires the
  body shipped in a **separate implementation artifact** (§34.1.9 allows one,
  `36266`) — the GHC exposed-unfolding / Rust serialized-generic-body
  compromise.
- This makes **option (A) full whole-program mono architecturally hostile**:
  it needs a closed world that §8.3 deliberately refuses. The optimization
  guide already names this: whole-program mono is "the maximal escape but a
  **closed-world commitment**" (`docs/NATIVE_BACKEND_OPTIMIZATION_GUIDE.md:228`),
  filed under P2 "architectural, deliberate decisions only."

### Tradeoff summary

| Option | Niche payoff | Sep-comp | Spec conformance | Cost |
|---|---|---|---|---|
| **(A) Whole-program mono** (MLton/Rust) | Full — delivers the static niche | **Breaks §8.3** unless confined to a closed sub-world | Allowed (§34.3.7) but boundary carve-outs hard | Very high; no bounded instantiation set (§3.3) |
| **(B) Targeted / per-package opt-in mono** (GHC/Swift WMO) | Partial — niche only inside the specialized sub-world; default stays boxed | **Preserved**; cross-module via implementation artifact (§34.1.9) | Cleanest fit; must key by rep class (§34.3.7), decide at compile time (§31.2) | High but bounded; reuses landed worker/wrapper machinery |
| **(C) Value-witness passing** (Swift VWT) | Runtime layout only — **no static LLVM niche** | **Preserved** | Conformant; layout decided by witness, not at codegen | Medium; runtime indirection on every unspecialized boundary |
| **(0) Status quo** (uniform + b001/b010/b011 + scalar worker) | Already banked the cheap wins; no niche | Preserved | Conformant | Zero (shipped) |

---

## 3. What it unblocks: niche vs. already-banked wins, and the honest size

### 3.1 What is ALREADY done under erasure — no specialization needed

These are shipped and adversarially verified (corpus 102/102 interp==C==LLVM;
`ROADMAP` "Done"; `LAYOUT-DESIGN.md`):

1. Immediate Int `b001` — boxed `addInt` 48→0 B/op (the ~50x allocation
   lever).
2. Nullary-ctor immediate `b010` — `None`/`Nil`/`True`/`Unit`/enum variants
   alloc-free; `ctor0-build` 48→0 B/op.
3. Packed single+two-field ctors `b011` — `Some smallInt`, `Ok`/`Err`,
   `Pair(Int,Int)` small, `Cons(small,Nil)` all 0 B/op.
4. Scalar Int64/Double worker (`kwi_`/`kwd_`/`kwm_`) — a fused Double loop is
   0 B/op, O(1) total.

The decisive fact: **these wins do NOT need specialization because the
discriminant is stored EXPLICITLY in the tagged word.** `kctor_tagid` reads the
tag blind, so polymorphic code runs correctly over packed ADTs with no
specialization (`LAYOUT-DESIGN.md:27-52`). Specialization here is "a
*performance* refinement … NOT a correctness requirement."

The **scalar worker is the load-bearing proof** that "specialize the concrete
hot path, box at the uniform boundary" already works under erasure *without*
monomorphizing polymorphic bodies. `scalarPlan`/`typeScalarKinds`
(`C.hs:873-928`) read the top-level binding's concrete type via
`Repr.repSelect ctx (gdType gd)` (`C.hs:925`), classify each param
PScalar/PBoxed, emit one unboxed worker per layout class, and keep the boxed
`kw_g` as the always-correct fallback with a wrong-tag/overflow escape
(`C.hs:704-708, 1345`). A type variable falls through to `RepBoxed` by
construction (`Repr.hs:119-126`). This is "**per representation class, not per
type**" — bounded to ~4 layout classes, no Rust-style bloat. It is exactly the
§34.3.7-conformant pattern (key by rep class, not source type).

### 3.2 What specialization UNIQUELY buys

Only three candidate wins genuinely need it (`LAYOUT-DESIGN.md:50-52, 108-114,
253-263`):

- **A. Niche `Option<boxed>` = bare pointer** (`None` = reserved immediate,
  `Some p` = `p`). Saves one heap box (a `Some<boxed>` is a real `K_CTOR`
  today — `b011` cannot pack a full pointer) plus one discriminant word, for
  Option/Result/Maybe over **heap** payloads. The only sizable item.
- **B. Full-range `Option<Int>` / wider Direct-tag packing** — values outside
  the `b011` bit budget (single-field 40 bits; two-field ±2^16). Specialization
  lets a statically-known monomorphic `Option<Int>` use a dedicated wider
  layout instead of boxing the overflow case.
- **C. Inline construct/match/project at hot sites over known layouts** — skip
  the `kctor_tagid` dispatch when the concrete layout is statically known
  (Swift-style). Pure dispatch elision, not allocation — the smallest item.

### 3.3 Why the niche payoff is largely ERODED under erasure

This is the core of the cost/benefit case (`ROADMAP` Stage 4;
`niche-layout-vs-type-erasure` memory; decided with the user 2026-06-26):

- `Option Foo` and `Option a` share one runtime body (no mono today). The
  runtime cannot distinguish a niche-able instance from a generic one:
  `kctor_tagid(Some p)` would read the **inner** value's tag
  (`LAYOUT-DESIGN.md:41-52`).
- The mandatory "box a niche value escaping into polymorphic code" coercion
  "isn't a rare edge — **under erasure EVERY polymorphic boundary is that
  edge**, and it just moves the allocation to the coercion site." The saved
  `Some<boxed>` box reappears at the coercion site. The niche survives only for
  short-lived concrete `Some<boxed>` that never escapes (`ROADMAP:178-181`).
- Even the universal `None=0` trick **dies on nested `Option<Option<_>>`**:
  `Some None` collides with `None`. The already-shipped `b011` packing
  deliberately **beats** the niche here — `Some None` packs as a `b011` word
  distinct from `None`'s `b010` because the discriminant is explicit
  ("the soundness win over a niche", `LAYOUT-DESIGN.md:47, 183-184`).
- **No bounded instantiation set.** Full Rust-style mono is "intractable under
  Kappa's dependent-ish, trait/effect-typed, possibly-unbounded instantiation
  sets — there is no bounded instantiation set to enumerate"
  (`UNBOXING-DESIGN.md:§10`). Niche pays off in Rust because of mono + **no
  GC** (zero-cost through generics); Kappa erases types and boxes uniformly —
  "the opposite preconditions." And Kappa's conservative-GC **Boehm caveat**
  (any niche/low-bit tag must never be mistaken for a heap pointer;
  `OPTIMIZATION_GUIDE.md`) is a constraint Rust does not carry.

### 3.4 What specialization does NOT touch

The dominant residual allocation volume in real programs is elsewhere and
specialization leaves it entirely Boehm-bound until Perceus RC
(`UNBOXING-DESIGN.md:§8 Residual`): per-field ctor box indirection ("most of
real allocation volume"), the 832 B/op fork frame, the 416 B/bind CPS tree.
Specialization touches **none** of these. The honest framing of the headline:
the ~50x boxing lever is allocation+arithmetic on the most favorable pure-Int
microloop; whole-program speedup is "materially below 50x," and the cheap half
is already banked (`UNBOXING-DESIGN.md:§1.2, §8`).

### 3.5 Prior art confirms the binary

Niche / non-uniform **data** layout is delivered **only** by models that
monomorphize the data layout — MLton (whole-program mono + representation
selection, the closest analogue to Stage 4, *requires* whole-program, no
separate compilation) and Rust (per-instantiation mono + niche-filling, no GC,
bodies serialized into consumer crate metadata). GHC, OCaml, Swift, Koka all
keep a **uniform** datatype layout regardless of type arguments and instead
attack the *cost* of polymorphism (worker/wrapper, immediate ints, witness
tables, RC reuse) — **none give `Option Foo` a different shape than
`Option a`.** GHC itself declines to niche-layout `Maybe a` for exactly this
reason (prior-art findings, key facts). So "invest in specialization to unblock
niches" *is* "invest in monomorphizing data layout," which pulls toward the
closed-world commitment §8.3 refuses.

---

## 4. Staged plan (if pursued) and the effort/risk

If specialization is pursued, it should be **option (B): opt-in, per-package
targeted mono**, mirroring GHC `{-# SPECIALIZE #-}` / Swift WMO, *never* MLton
whole-program. Reuse the landed worker/wrapper + mixed PScalar/PBoxed machinery
as the spine. Staging:

- **S0 — Make typed Core load-bearing (prerequisite, no perf yet).** Populate
  the `CCtor` head-type annotation everywhere (today `Nothing` except
  `Check.hs:6522`); add a type field to `CPCtor` (`Core.hs:260`, currently
  none); keep `CMatch`'s populated annotation. Risk: low-medium, but
  cross-cutting in elaboration. No behavior change yet (annotations stay
  observe-only until S2 reads them). *This is the genuine gate* — both the
  erasure and poly-lowering studies converge on "annotate + read CCtor/CMatch"
  as the real prerequisite.

- **S1 — Specialization pass over `Term` (pre-erasure).** At each polymorphic
  call with a statically-known concrete instantiation, clone the callee body,
  key the clone **by chosen runtime representation class** (§34.3.7), not by
  source type. Reroute saturated calls in `compileApp`/`compileDirectCall`
  (`C.hs:2105, 2418`). Confine to a closed sub-world (intra-package); for
  exported generics either decline or ship a separate implementation artifact
  (§34.1.9). Risk: medium-high — new infrastructure, no prior art in `src/`,
  interacts with totality/conversion (dependently-typed IR). Add dictionary
  devirtualization as a strictly-additional win in the same pass (replace
  `CProj dict member` with a direct instance-member call when the instance is
  statically known) — independently blessed by §11.1.4/§11.1.6.

- **S2 — Backend reads the annotation for layout.** Make `ctorLayoutByArity`
  (`Repr.hs:307`, today keyed on **arity alone**) consult the concrete head
  type; `Repr.ctorLayout` already accepts field-Reps. Risk: medium.

- **S3 — Coercion-insertion pass (re-box on escape to poly).** Re-box a niche
  value whenever it crosses into still-polymorphic code (any shared body,
  higher-order callback, unspecialized boundary). This is where §3.3's payoff
  erosion bites: under erasure every poly boundary is a coercion site. Risk:
  **high — highest miscompile risk, no byte-identical safety net** (`ROADMAP`
  rates Stage 4 highest-complexity). Must satisfy the §34.3.8 observational-
  equivalence side condition or decline + emit
  `E_BACKEND_SPECIALIZATION_SEMANTICS`.

- **S4 — Niche layout proper** (the actual `Option<boxed>` = bare pointer win),
  gated by inhabitance per §31.2.1/§34.3.2, honoring the Boehm/GC-immediate
  caveat and all boundary carve-outs (Dyn/reflection/opacity/stable TagId).
  Risk: high.

**Aggregate effort:** large — a multi-month, cross-cutting
elaboration+IR+backend program with new pass infrastructure, a coercion pass,
and a layout-selection rework, the riskiest stage having no byte-identical
verification net. **The marginal allocation win over the already-banked uniform
packings is small, fusion-/escape-bounded, and leaves the dominant residual
costs (per-field indirection, fork frame, CPS-bind) untouched — those need
Perceus RC, not specialization.**

A far cheaper alternative if *some* type-directed layout is wanted without
abandoning sep-comp: **option (C) value-witness passing** (Swift VWT) — pass a
layout witness alongside dictionaries. Preserves sep-comp fully, degrades
gracefully to boxed at genuinely polymorphic boundaries, but yields a *runtime*
layout decision, **not** the static LLVM niche the Stage-4 goal names. Useful
if the goal is "don't always box"; weak if the goal is "emit the niche-able
LLVM struct."

---

## 5. Recommendation

**Do not invest in specialization now to unblock niche/type-directed layout as
a standalone performance play.** This confirms the verdict already reached with
the user on 2026-06-26 (`ROADMAP` Stage 4 DEFERRED).

Rationale, in priority order:

1. **The payoff is marginal and structurally eroded.** Every erasure-compatible
   layout win that keeps an explicit discriminant in the tagged word
   (`b001`/`b010`/`b011`, scalar worker) is already shipped and captured the
   dominant allocation lever (`LAYOUT-DESIGN.md:27-52`; `UNBOXING-DESIGN.md:§8`).
   What specialization uniquely buys is dominated by the niche, and the niche's
   payoff relocates rather than removes the allocation — under erasure every
   polymorphic boundary is a re-box coercion site (`ROADMAP:178-181`); it also
   loses on nested `Option<Option<_>>` to the already-shipped `b011` packing
   (`LAYOUT-DESIGN.md:47, 183-184`).

2. **The cost is the highest in the layout program, with no safety net.** New
   pass infrastructure (none exists in `src/`), a coercion-insertion pass, and
   a layout-selection rework — the riskiest stage with no byte-identical
   verification (`ROADMAP` Stage 4). No bounded instantiation set exists for
   whole-program mono (`UNBOXING-DESIGN.md:§10`).

3. **Whole-program mono (the only model that *fully* delivers the niche) is
   architecturally incompatible** with Kappa's §8.3 separate-compilation
   commitment (`Spec.md:36260-36344`; `OPTIMIZATION_GUIDE.md:228`). Only MLton
   and Rust deliver the static niche, both at the price of a closed world Kappa
   refuses (prior-art §3.5). GHC — the closest mechanism fit — *declines* to
   niche `Maybe a` for exactly the reason Kappa would have to.

4. **The dominant residual costs are untouched by specialization** and need
   Perceus RC instead (`UNBOXING-DESIGN.md:§8`).

**If specialization is ever pursued, justify it on a non-payoff axis, not on
the layout/perf ROI studied here** — e.g. it is the architecture that gives
the niche/type-directed LLVM layout "somewhere to live," or it enables §21.6
semantic-reflection reuse of typed Core, or dictionary devirtualization
(§11.1.4/§11.1.6) as a goal in its own right. The layout/perf case is the
weakest part of the argument.

**Recommended near-term trajectory instead** (low-risk, on the current path,
matching OCaml/flambda + immediate-ints as the proven null hypothesis):
continue the uniform-rep + immediate-int + opportunistic-local-unboxing line
(extend the scalar worker / `b011` toward monomorphic non-primitive scalar
heads where `Repr` already has the type at the *binding* site, no call-site
cloning), and pair with **Perceus RC** as the orthogonal allocation-pressure
reducer that attacks the residual volume specialization cannot. Keep the
`CCtor`/`CMatch` typed-Core annotation as the deliberate, cheap hook so that
**if** the architecture is later justified on a non-perf axis, S0's groundwork
is already laid.

---

## Appendix: load-bearing references

- Erasure model / no physical pass: `docs/audit/lane-types.md:180-181`;
  `src/Kappa/Core.hs:102-164`; `C.hs:979-1033, 1707-1731, 2128-2134`.
- Dictionaries kept (QW), classic dict-passing: `C.hs:997-1000`;
  `Check.hs:5992-5999, 12663-12672, 15135-15139`; Spec §31.2.1
  `docs/Spec.md:34718`, §14.4.
- Typed-Core hook (observe-only): `Core.hs:117-131, 184-186`;
  `Check.hs:6522, 8542-8547`; `CPCtor` untyped `Core.hs:260`.
- Layout authority keyed on arity: `Repr.hs:307`; scalar worker
  `C.hs:873-928, 1136-1148, 1345`, `Repr.hs:114-126, 182`.
- Spec: §34.3.7 keying `Spec.md:37971-37986`; §31.2/§30.2.3A erasure
  `34629-34691, 33484-33568`; §34.3.2 inhabitance/Unknown `37827-37871`;
  §34.3.8 obs-equiv + `E_BACKEND_SPECIALIZATION_SEMANTICS` `37989-38016, 1033`;
  §34.3.1 reordering `37823-37824`; §9.040-9047 firewall; §34.1.9/§8.3
  sep-comp `36260-36344`; §11.1.4/§11.1.6 trait-evidence `9275-9282, 9416-9438`.
- Payoff: `LAYOUT-DESIGN.md:27-52, 47, 50-52, 108-114, 183-184, 253-263`;
  `UNBOXING-DESIGN.md:§1.2, §8, §10`; `ROADMAP` Stage 4 `:74, 168-183`;
  `runtime/bench/README.md`.
- Prior art: GHC worker/wrapper + SPECIALIZE; MLton whole-program mono +
  representation selection; Rust niche-filling + consumer-crate mono; OCaml
  uniform rep + flambda; Swift witness tables; Koka/Perceus reuse
  (`OPTIMIZATION_GUIDE.md:215, 221, 222, 228`).
