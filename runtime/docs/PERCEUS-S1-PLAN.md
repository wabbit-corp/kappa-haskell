# Perceus Stage S1 — Implementation Plan: Threading Ownership onto the Backend IR

Status: **historical S1 COMPLETE** (`71e6639`→`b26ef7c`; conformance 1916/0, parity 121/0; the full
ownership-analysis layer was observe-only and Boehm untouched at this stage). Later stages have since landed:
S2 consumes this metadata for dup/drop/drop-site emission, and S3.4 makes the C/runtime path RC-on by default
with free-on-zero for the conservative freeable partition. This document records the S1 design constraints; use
[PERCEUS-S3-PLAN.md](PERCEUS-S3-PLAN.md) and [ROADMAP.md](../../ROADMAP.md) for current runtime status.
Companion to [PERCEUS-RC-DESIGN.md](PERCEUS-RC-DESIGN.md) (the arc) — this is the detailed S1 blueprint.

## The framing that drives every decision

Three findings (from a spec-first scoping pass) reshape the naive reading:

1. **There is no distinct `KBackendIR` datatype.** `Term` (`src/Kappa/Core.hs:103`) *is* the KCore, and the
   backends lower it directly. Per §34.3's "observationally equivalent" clause, "thread onto KBackendIR" =
   **a side-table keyed by Core node/binder identity that the backend reads** — exactly the §31.2
   mandatory-erasure audit-trail shape (Spec.md:34680, "keyed by KCore node identity, binder identity") —
   **not** a parallel IR.
2. **The owned/borrowed *parameter* convention is already in the IR.** `CPi !Icit !Q !Bool …`
   (`Core.hs:113`) carries the quantity `Q` *and* the borrow `Bool`; `CLam`/`CLet` carry `Q`.
   `Usage.coreFnParams` (`Usage.hs:1901`) reconstructs per-param `(quantity, borrow)`, and
   `Backend/Repr.repSelect` (`Repr.hs:182`) already walks that telescope. The calling convention needs **no
   new metadata** — only a backend that *acts* on the `Q`/`Bool` already present.
3. **The only genuinely-erased thing is per-binding/per-occurrence last-use** (+ the §3a refined interval).
   `Usage.hs` *computes* it (`UseCount`, `ucEvents` with `PMove`/`PBorrow` spans, `Usage.hs:166-219`) but is
   **diagnostics-only**: it runs over the surface `Expr`, returns `[Diagnostic]`, and the last-use decisions
   are thrown away (`Pipeline.hs:641-645`). **Closing that discard is the entire S1 gap.**

## (a) The metadata to thread — `OwnInfo`

```haskell
data UseKind   = LastUse | NonLast | Borrowed
data BinderOwn = BinderOwn
  { boDeclQ     :: Q                       -- declared quantity (already on CPi/CLam/CLet)
  , boRefined   :: Maybe (Int, Maybe Int)  -- §3a tightened interval, static-link only (Nothing ⇒ boDeclQ)
  , boBorrowed  :: Bool                    -- from CPi Bool / let & — non-consuming
  , boDroppable :: Bool }                  -- §12.2.6: True for 0/≤1/ω, False for 1/≥1
data OwnInfo = OwnInfo
  { oiBinders :: Map BinderId BinderOwn    -- BinderId = (GName, child-position path) — de-Bruijn-stable
  , oiUses    :: Map UseSite  UseKind
  , oiUseConsumes :: Map UseSite Bool       -- S2.3b: use transfers ownership vs read-only
  , oiBinderUses :: Map BinderId [UseKind]
  , oiBinderConsumingUses :: Map BinderId [UseKind] }
```

`UseKind` plus `oiUseConsumes` is the directly-consumable form for S2's drop-after-last-use /
dup-before-non-last rule. S2.3b makes the split explicit because a `LastUse` or `NonLast` can be a
read-only occurrence (projection base, borrowed call argument) that must not receive a balancing `kdup`.
`boDroppable` reads straight from §12.2.6 (Spec.md:11403). `boRefined` (§3a) only ever *narrows* the
declared bound. The refinement is **whole-program sound** whenever the analysis sees every use of a binder,
which it always does in Kappa's current **whole-program-static** compile (no dynamic linking / separate
compilation). So `boRefined` is populated for **every** provably-single-use binder — exported, re-exported,
and internal alike; the genuine §3a gating boundary is the **dynamic-link / separately-compiled interface**,
which is **empty right now**. (**TODO — separate compilation:** once that boundary exists, fall back to
`boDeclQ` for any binder reachable through it; the earlier `csModuleExports`/`csReExports` gating was a
premature proxy for it and has been removed — see R4.) The owned/borrowed *param* convention (A3) is sourced
from the `CPi` telescope, NOT a side table — avoids a second source of truth.

## (b) Where it lives — a post-elaboration side-table (NOT new Term fields)

Adding fields to `CVar` was measured at **586 occurrences** (162 hand-built in `Prelude.hs`) and collides
with §31.2 (the metadata must never become a runtime dependency). Instead: a new module
`src/Kappa/Ownership.hs` exporting `annotateOwnership :: EvalCtx -> Map GName Term -> Map GName Term -> Map GName OwnInfo`
(constructor types, then core bodies), run in `Pipeline.hs` right after `csCoreBodies` are finalized
(beside `lintCoreBodies`), stored as
`csOwnership` in `CheckState` and carried to the backend as `gsOwnership` beside `gsSuspenders`. It mirrors
the Stage-0 `CCtor`/`CMatch` `Maybe Term` annotation precedent (observe-only; `Eq Term` ignores it;
`CoreLint.hs` is the first observe-only consumer). The *checking* (rejecting linearity violations) stays in
`Usage.hs`; the new pass only *records* the already-validated decisions in Core coordinates.

## (c) The CCtor/CMatch layout gap (for S5 FBIP reuse) — close in `Repr.hs`, no Term change

FBIP needs the field count/layout at a `CMatch` arm (scrutinee side) and `CCtor` (construct side). The
construct side already has it (`compileCtor` in `src/Kappa/Backend/C.hs`). The scrutinee side is in the
`CMatch` head-type annotation in `Kappa.Core.Term` — already produced, no backend reads it. Close via
`Repr.ctorLayoutOf ::
EvalCtx -> Maybe Term -> Maybe CtorLayout` (observe-only in S1, consumed by S5), plus populating the
`CCtor` annotation where it's currently `Nothing`. `Nothing ⇒ conservatively skip reuse` (sound, slower).
No `Term` arity change.

## (d) How the backend reads it (S2 shape, defined now)

- **Owned/borrowed convention**: at each `CApp`, resolve the callee `CPi` telescope to per-arg `(Q, borrow)`.
  Globals use the global type; local and pattern-bound first-class callees use recovered binder/pattern types.
  Owned runtime positions consume; borrowed, `Q0`, and kind-domain positions read/erase as appropriate.
- **dup** before a consuming `NonLast` use; read-only `NonLast` occurrences stay bare because no consumer-side
  drop balances a dup.
- **drop** at conservative structural seams only when the value is known owned. In the original S1 framing,
  `CDo` was still treated as an opaque future seam; S2.3b closed that gap by walking and validating do-kernel
  bodies, while resource-specific lifetime is still protected structurally by the do-kernel/defer/using lowering
  rather than by a stored resource flag in `OwnInfo`.
- Placement precedent: the `gsSuspenders` threading in `src/Kappa/Backend/C.hs`, computed once from Core bodies
  and consulted by application/do lowering instead of being rediscovered at each call site.

**S2 consumption discipline (from the S1.1 R1 review).** The `OwnInfo` keys are structural child-position
paths. S2 must consume them by **walking the lowered term and looking up each node's path** (visit node →
compute its path → query the table), NOT by iterating the table. A stale key naming an erased subterm
resolves to a `CSort 0` childless leaf (safe — it addresses nothing, never a wrong binder), but
walk-and-lookup never queries a deleted key at all. S2.3b pins this with the default-on Perceus validation
gate: every non-erased runtime lookup must resolve both `oiUses` and `oiUseConsumes`, or the backend fails
(`KAPPA_PERCEUS_RC=0` is reserved for explicit RC-off differential baselines that also disable runtime RC effects).

## (e) Sub-stages, ordering, risks

| stage | what | status |
|---|---|---|
| **S1.0** | `OwnInfo` type + empty pass + `csOwnership`/`gsOwnership` plumbing | ✅ `71e6639` |
| **S1.1** | last-use computation over Core (port the `Usage.hs` lattice to `Term`) | ✅ `32bb984` |
| **S1.2** | `kappa dump-ownership` + the **declared-Q cross-check gate** (validatable deliverable) | ✅ folded into `32bb984` |
| **S1.3** | populate `CCtor` annotations + `Repr.ctorLayoutOf` (evidence-field-correct) | ✅ `e63c768`/`bd2f5f5` |
| **S1.4** | §3a whole-program refinement (whole-program-static ⇒ no export gate; every single-use binder refined; dynamic-link gate = TODO) | ✅ `e63c768`→`b26ef7c` |
| **S1.5** | backend owned/borrowed accessor (telescope-derived, observe-only) | ✅ `e63c768` |

Ordering: S1.0 → S1.1 → S1.2 gates everything (the audit trail must exist + be validated before S2 trusts
it). S1.3/S1.5 are telescope-derived, independent of S1.1. S1.4 depends on S1.1.

**Risks.** **R1 (highest) — de-Bruijn identity stability**: the side-table keys must survive post-elaboration
`Term` rewriting (zonking in `Pipeline.hs`, the `eraseQ0Args` spine rewrite in `Backend/C.hs`). Mitigate: compute
`OwnInfo` *after* zonking; re-key after `eraseQ0Args` (verify the de-Bruijn shift; `Q0` binders are
non-runtime). **R2 — §31.2 erasure**: keep `OwnInfo` strictly out of `Term`; register it with the
`verify-kbackendir` legality check. **R3 — surface/Core last-use divergence** (partially-consumed records,
§13.2.4): the S1.2 differential assert; start with whole-binder last-use, defer per-field path-sensitivity
(treat partially-consumed as non-reusable — sound, leaves S5 wins on the table). **R4 — §3a boundary
soundness**: the refinement is whole-program sound while the analysis sees all uses, which the current
whole-program-static compile guarantees, so every provably-single-use binder is refined (no export gate).
**TODO — separate compilation (hard prerequisite before S2 ships under it):** when a dynamic-link /
separately-compiled interface exists, fall back to `boDeclQ` (`boRefined = Nothing`) for any binder reachable
through it — re-add the gate keyed on that real interface, NOT on `csModuleExports`/`csReExports` (a premature
proxy, now removed). The surviving cross-check invariant is tighten-only (`boRefined ⊆ boDeclQ`).

## (f) Incremental validation (Boehm untouched, zero codegen change through all of S1)

1. **`kappa dump-ownership <file>`** — per global, each binder's `(declQ, refined, borrowed, droppable)` +
   each `CVar` occurrence's `LastUse|NonLast|Borrowed` and `consumes=True|False`.
2. **Cross-check vs the quantity checker** — on the well-typed corpus that `Usage.hs` has already accepted,
   every linear (`1`) binder has at least one consuming `LastUse` and no consuming `NonLast`; every borrowed
   binder has no `LastUse` consume. A mismatch is an internal-invariant error in ownership classification.
   The quantity checker remains the path-sensitive authority for “consumed on every path.”
3. **§31.2 legality** — extend `verify-kbackendir` to assert no runtime term depends on `OwnInfo`.
4. **Parity invariant** — all S1 consumers are observe-only ⇒ interp == C == LLVM byte-identical, full
   corpus unchanged. Boehm is the collector throughout S1; RC-free arrives at S3.

## Critical files
- `src/Kappa/Core.hs` — the IR (`Term`; `CVar`/`CLam`/`CLet`/`CPi` Q+borrow; `CCtor`/`CMatch` annotation channel).
- `src/Kappa/Usage.hs` — the source-of-truth last-use/move lattice to port + cross-check against.
- `src/Kappa/Ownership.hs` — **new** (S1.0 landed): the `OwnInfo` side-table + `annotateOwnership`.
- `src/Kappa/Pipeline.hs` — populate `csOwnership` after `csCoreBodies` finalize (`:747`).
- `src/Kappa/Backend/C.hs` — `gsSuspenders`/`gsOwnership` threading; `compileCtor` (S5 site); future dup/drop.
- `src/Kappa/Backend/Repr.hs` — the single rep/layout authority; home for `ctorLayoutOf`.
