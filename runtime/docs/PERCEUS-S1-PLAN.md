# Perceus Stage S1 — Implementation Plan: Threading Ownership onto the Backend IR

Status: **S0 + S1.0 LANDED** (`71e6639`, conformance 1916/0, parity 121/0, inert). S1.1 next.
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
  , oiUses    :: Map UseSite  UseKind }
```

`UseKind` is the directly-consumable form for S2's drop-after-last-use / dup-before-non-last rule.
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
`src/Kappa/Ownership.hs` exporting `annotateOwnership :: EvalCtx -> Map GName Term -> Map GName OwnInfo`,
run in `Pipeline.hs` right after `csCoreBodies` are finalized (beside `lintCoreBodies`), stored as
`csOwnership` in `CheckState` and carried to the backend as `gsOwnership` beside `gsSuspenders`. It mirrors
the Stage-0 `CCtor`/`CMatch` `Maybe Term` annotation precedent (observe-only; `Eq Term` ignores it;
`CoreLint.hs` is the first observe-only consumer). The *checking* (rejecting linearity violations) stays in
`Usage.hs`; the new pass only *records* the already-validated decisions in Core coordinates.

## (c) The CCtor/CMatch layout gap (for S5 FBIP reuse) — close in `Repr.hs`, no Term change

FBIP needs the field count/layout at a `CMatch` arm (scrutinee side) and `CCtor` (construct side). The
construct side already has it (`compileCtor`, `C.hs:3012`). The scrutinee side is in the `CMatch` head-type
annotation (`Core.hs:132`) — already produced, no backend reads it. Close via `Repr.ctorLayoutOf ::
EvalCtx -> Maybe Term -> Maybe CtorLayout` (observe-only in S1, consumed by S5), plus populating the
`CCtor` annotation where it's currently `Nothing`. `Nothing ⇒ conservatively skip reuse` (sound, slower).
No `Term` arity change.

## (d) How the backend reads it (S2 shape, defined now)

- **Owned/borrowed convention**: at each `CApp`, resolve the callee `CPi` telescope (already done by
  `Repr.repSelect`) to per-arg `(Q, borrow)`. Owned `1`/`≥1` ⇒ callee consumes (caller transfers, no
  post-call drop); borrowed `&` ⇒ caller retains (callee reads+dups, never drops).
- **dup** before a `NonLast` use whose effective interval (refined if static-link-safe, else declared) is
  `>1`-capable; immediates skip it (`kis_imm` guard).
- **drop** after the `LastUse` of a non-borrowed binder, or at a droppable-unused binder — **except** when
  the value is reachable from a live ExitStack (§1 contract: resource lifetime is `defer`/`using`, never
  RC-to-zero). S1 records per-binder whether it carries `K_FGN`/resource state (via `Repr` head type).
- Placement precedent: the `gsSuspenders` threading (`C.hs:110/474`, consulted at `:935/983/2497`).

**S2 consumption discipline (from the S1.1 R1 review).** The `OwnInfo` keys are structural child-position
paths. S2 must consume them by **walking the lowered term and looking up each node's path** (visit node →
compute its path → query the table), NOT by iterating the table. A stale key naming an erased subterm
resolves to a `CSort 0` childless leaf (safe — it addresses nothing, never a wrong binder), but
walk-and-lookup never queries a deleted key at all. Pin this with an explicit assertion when the S2 dup/drop
consumer lands.

## (e) Sub-stages, ordering, risks

| stage | what | status |
|---|---|---|
| **S1.0** | `OwnInfo` type + empty pass + `csOwnership`/`gsOwnership` plumbing | ✅ `71e6639` |
| **S1.1** | last-use computation over Core (port the `Usage.hs` lattice to `Term`) | ✅ `32bb984` |
| **S1.2** | `kappa dump-ownership` + the **declared-Q cross-check gate** (validatable deliverable) | ✅ folded into `32bb984` |
| **S1.3** | populate `CCtor` annotations + `Repr.ctorLayoutOf` (observe-only) | (parallel to 1.1) |
| **S1.4** | §3a whole-program refinement (call-graph over `csGlobals`; whole-program-static ⇒ no export gate, every single-use binder refined) | (after 1.1) |
| **S1.5** | backend owned/borrowed accessor (telescope-derived, observe-only) | (parallel to 1.1) |

Ordering: S1.0 → S1.1 → S1.2 gates everything (the audit trail must exist + be validated before S2 trusts
it). S1.3/S1.5 are telescope-derived, independent of S1.1. S1.4 depends on S1.1.

**Risks.** **R1 (highest) — de-Bruijn identity stability**: the side-table keys must survive post-elaboration
`Term` rewriting (zonking `Pipeline.hs:727`, the `eraseQ0Args` spine rewrite `C.hs:1110`). Mitigate: compute
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
   each `CVar` occurrence's `LastUse|NonLast|Borrowed`.
2. **Cross-check vs the quantity checker** — every binder `Usage.hs` proved linear (`1`) has exactly one
   `LastUse` and no `NonLast`; every borrowed binder has no `LastUse` consume; every non-droppable binder is
   consumed on every path. A mismatch is an internal-invariant error. This is the ground truth before any RC.
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
