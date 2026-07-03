# Perceus Stage S2 — Implementation Plan (dup/drop under the Boehm differential backstop)

Status: **HISTORICAL S2 kickoff plan.** The current S2.3b-d status lives in
[PERCEUS-S2.3-DROP-COMPLETION.md](PERCEUS-S2.3-DROP-COMPLETION.md) and the repository
[ROADMAP.md](../../ROADMAP.md). Keep this file as design archaeology for the original S2 arc; do not treat
the counts, line references, or flat-parameter drop targets below as current implementation status.
Companion to [PERCEUS-RC-DESIGN.md](PERCEUS-RC-DESIGN.md) (the arc) and [PERCEUS-S1-PLAN.md](PERCEUS-S1-PLAN.md)
(the analysis layer S2 consumes).

S2 emits `kdup`/`kdrop` in the C backend, consuming the S1 `OwnInfo`, to maintain each heap object's `rc` —
under the **Boehm differential backstop**: Boehm STILL frees (no free-on-zero — that is S3); `dup`/`drop`
only maintain + assert the `rc`. So a wrong placement is a **leak (missed drop)** or an **`rc`-underflow
assert (extra drop / missed dup)** — *never a use-after-free*. The historical run was byte-identical; use
the current S2.3 drop-completion note for fresh verification counts. S2 gets dup/drop *correct*
under a backstop before S3 removes the net.

## 0. The architectural fact that reshapes everything

`OwnInfo` keys are **structural child-paths** (`Ownership.hs` `biPath`/`usPath`); the S1.1-R1
discipline mandates **walk-the-lowered-term-and-look-up-each-node's-path**, never iterate the table. But the
native lowering (`compile`/`compileTerm` in `C.hs`) is **expression-oriented and carries no path** —
it returns C-expression `Text`, with statement seams only at `sinkToExpr`, `consumeMatch`, `consumeAlt`,
`consumeAltBody`, `consumeIf`, `CLet` (via `sinkToExpr`), and `compileLam`. Two consequences:

1. **S2 must thread a `gsPath :: [Int]`** (reversed child-position) through `compileTerm`/`compileApp`/
   `compileCtor`/`consume*`, incremented at exactly the child positions `annotateOwnership` used
   (`Ownership.walk`: CApp head=1/arg=2, CCtor args=3.., CLet rhs=2/body=3, CMatch scrut=1/arm=2+i,
   …). **The path discipline in the two modules must be IDENTICAL** → extract the child-position constants
   into one shared module both `Ownership.hs` and `C.hs` consult. *This is the single highest-value
   correctness investment* (R-path below).
2. **dup/drop are statements** but most lowering is nested expressions, so **drops land only at statement
   seams that already bind a C lvalue** (a `let`/match-arm binding, a `scrut_`/`r_` temp, a flat-worker
   param `gsParamLvals`). A dup before a NonLast use wraps the use in `kdup(<expr>)` (comma/return-v).

## (a) Runtime `kdup`/`kdrop` — `kappart.h` + `value.c`

S0 substrate is present (`rc` field in `kappart.h`; `alloc_val`/`_atomic` init `rc=1` in `value.c`;
`kis_imm`; the `sizeof==48`/`offsetof(rc)==4` static asserts). Add:
- `static inline KValue *kdup(KValue *v)` — `if (kis_imm(v)) return v; v->rc++; return v;` (composes inside
  an expression; `kis_imm` is the single immediate-skip guard).
- `static inline void kdrop(KValue *v)` — `if (kis_imm(v)) return;` then **DEBUG** `assert(v->rc > 0 &&
  "kdrop: rc underflow (double-drop / missed-dup)");` then `v->rc--;` and **explicitly NO free** (pin: "S3
  flips free-on-zero; S2 is maintain+assert only, Boehm owns reclamation"). Under `NDEBUG` the assert
  compiles out but `rc--` stays so the count is ready for S3.
- **DEBUG counters** `k_dups_total`/`k_drops_total` (behind `#ifndef NDEBUG` so release stays byte-identical)
  + `void krc_report(void)` (dups/drops/net) for the leak-trend check.
- The §1 carve-out is a runtime no-op by construction (`kdrop` never frees, so a dropped `K_FGN`/`K_REF`
  survives for its `defer`/ExitStack drain). Enforcement is in codegen (b.5). Pin the K_FGN/K_REF shapes as
  **never-free-on-drop** — the S3 hazard note.

## (b) Codegen emission — `C.hs`

- **b.1** Read `gsOwnership` for `gsCur` at body entry into a new `gsCurOwn :: Maybe OwnInfo`
  (set in `emitGlobal`/`compileFunctionGlobal`). Add `gsPath :: [Int]` pushed/popped at each
  descent, **mirroring `Ownership.walk` positions exactly** (shared constants). Gate the whole pass on
  `gsRcEnabled` (default ON as of S3.4; `KAPPA_PERCEUS_RC=0` keeps the explicit byte-identical baseline by
  disabling both generated ownership maintenance and runtime RC effects in the generated binary).
- **b.2 walk-and-lookup** at `CVar i` (`compileTerm`): build `UseSite gsCur (reverse gsPath)`, look up
  in `oiUses`: `NonLast` → `kdup(<expr>)`; `LastUse` → bare (consumed/moved here); `Borrowed`/`Nothing` →
  bare. A missing key is safe by the S1 invariant (stale key resolves to nothing, never a wrong binder).
- **b.3 owned/borrowed call boundary** at each `CApp` `CGlob` head (`compileApp`, after `eraseQ0Args`):
  `Repr.argConvSelectGlobal ctx g` (the S1.5-validated accessor plus the S2.3c primitive override
  table) → zip `[ArgConv]` vs the explicit runtime args: `ArgOwned` → caller transfers (no post-call drop);
  `ArgBorrowed` → callee never drops (caller retains); `ArgShared` → conservative transfer.
  Non-`CGlob` head → all-shared fallback.
  `boRefined` (§3a) is **observe-only in S2** — do not act on it (its gate is the dynamic-link interface;
  consuming it is S3+).
- **b.4 historical drops target** at statement seams: the original plan targeted any proven-droppable
  `CLet`/match-arm binder, per-arm completion paths, worker parameters, and destructure temporaries.
  **Current S2.3d implements only locally-proven owned flat locals; restoring incoming-parameter drops waits
  for caller-side ownership-transfer normalization.** Drop against the bound C local, never a fresh `kvar`
  rvalue re-read (R-flat).
- **b.5 historical `CDo` carve-out (superseded):** the original plan treated `CDo` as an ownership-erased
  island to keep do-scope resources under the ExitStack alone. Current S2.3b+ instead walks `CDo` with the
  shared `PathScheme` positions and validates generated do-kernel paths. Drops still must not cross a
  do-block/resource boundary unless the lowered structure proves ownership transfer; boxed/CPS paths remain
  conservative no-drop sites where ownership is not represented as a current flat local.

## (c) Differential-backstop validation (Boehm still frees)

- **Primary:** the `kdrop` underflow assert — a missed-dup/double-drop drives `rc` below Boehm-proven-live
  and trips `assert(rc>0)` *before* any UAF is possible (nothing is freed).
- **Secondary (soft):** `krc_report` net per program — a missed drop shows as a newly-positive net; a
  corpus-wide trend check, not a hard gate (top-level/long-lived values are never dropped).
- **Static ground truth (existing):** `crossCheckBodies`/`argConvBodies` keep the
  `OwnInfo` S2 consumes consistent with declared quantities — keep green.

## (d) Sub-stages, ordering, risks

| sub | what | gate |
|---|---|---|
| **S2.0** | runtime `kdup`/`kdrop` + assert + counters + `krc_report` | byte-identical (nothing calls them) |
| **S2.1** | `gsPath` + shared child-position constants; `gsCurOwn`/`gsRcEnabled`; walk-and-lookup **asserted, emits nothing** | byte-identical (flag off); the **R-path assert** validates the path-threading over the corpus |
| **S2.2** | emit `kdup` at NonLast uses (b.2) | outputs unchanged (dup is a no-op); assert clean |
| **S2.3** | emit `kdrop` at last-use/droppable seams (b.4) + owned/borrowed boundary (b.3) | outputs unchanged; **underflow-assert clean over corpus** |
| **S2.4** | do-kernel/ExitStack validation + leak-trend check (c) | resource cases unchanged |

Ordering: S2.0 → S2.1 (path infra first, byte-identical) → S2.2 (dup is safe, pure increment) → S2.3 (drop
is where underflow surfaces) → S2.4. **dup before drop** — a wrong drop with a missing earlier dup is
exactly the underflow the backstop must catch, so landing dup first means S2.3's asserts test real placement.

**Risks.** **R-path (highest):** `gsPath` divergence from `Ownership.walk` silently misattributes every op —
mitigate with the shared constants + a debug assert that every emitted op's looked-up key EXISTS in
`oiBinders`/`oiUses` (a `Nothing` at a *non-erased* runtime `CVar` is a path bug, distinct from a
legitimately-stale erased-arg key). **R-erase:** `eraseQ0Args` rewrites erased args to `CSort 0`
*during* `compileApp`; it removes no binder and shifts no index, so walking the erased body and getting
`Nothing` for erased-arg `CVar`s is safe — pin with a Q0-before-runtime regression. **R-flat-vs-boxed:** a
binder's C lvalue differs flat (`gsParamLvals`) vs boxed (`kvar(env,i)`); drop against the bound local, not
a `kvar` rvalue. **R-CDo:** current S2.3b+ walks `CDo` and requires generated do-kernel paths to validate
against ownership facts; resource and CPS/boxed paths remain conservative where no current flat-local
ownership proof exists.

## (e) Verification
1. Historical target: conformance + parity **byte-identical** through every sub-stage while dup/drop are rc
   no-ops and Boehm frees. Use the S2.3 completion note and `ROADMAP.md` for current counts and gates.
2. **Underflow-assert clean over the corpus** (DEBUG build, every `test/native/cases/`) — the primary S2
   success criterion.
3. Leak-trend (`krc_report` net) — soft.
4. Static ground truth (`crossCheckBodies`/`argConvBodies`) green.
5. Resource regressions (`usingsusp.kp`, `usinginterrupt.kp`, …) — output unchanged + no spurious drop
   fires inside a do-scope (proves the §1 carve-out).

## Critical files
- `src/Kappa/Backend/C.hs` — thread `gsPath`/`gsCurOwn`/`gsRcEnabled`; walk-and-lookup; dup at
  NonLast; drop at `consumeAlt`/`sinkToExpr`/CLet seams; owned/borrowed at `compileApp`/
  `eraseQ0Args`.
- `src/Kappa/Ownership.hs` — the canonical child-position path scheme in `walk`; source of the
  shared path constants.
- `src/Kappa/Backend/Repr.hs` — `argConvSelect`/`ArgConv`, the call-boundary accessor.
- `runtime/kappart.h` / `runtime/value.c` — `kdup`/`kdrop`/counters/`krc_report` beside the S0 `rc`
  and `alloc_val`; K_FGN/K_REF never-free-on-drop.
