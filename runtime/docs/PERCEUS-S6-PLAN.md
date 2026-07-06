# Perceus Stage S6 — Implementation Plan (opt-in Borrowing → inferred FIP)

Status: **Planned.** S0→S4 landed and reviewed sound (precise RC, free-on-zero, biased fast/slow split +
shared reclamation). S5 is landing: the KCore/KBackendIR split (Phase A) and drop-guided **FBIP reuse**
(Phase B) — `drop_reuse`/`reuse_alloc`, the reuse pass, zero-allocation on the rbtree/list-map fixtures.
S6 is the next and **last major** Perceus rung before the "Later" work (precise stacks + cycles). It has two
threads: **(1) opt-in Borrowing** — stop paying reference-counting on read-only accesses — and **(2) inferred
FIP** — statically prove where reuse always succeeds, elide the runtime uniqueness guard, and *derive* (never
declare) which functions run fully in place. Companion to [PERCEUS-RC-DESIGN.md](PERCEUS-RC-DESIGN.md) §7 (S6
in the staging) and [PERCEUS-S5-PLAN.md](PERCEUS-S5-PLAN.md) (the reuse machinery S6 builds on).

**Decision (recorded, non-negotiable): FIP is *inferred*, never annotated.** The FP² paper (Lorenzen/Leijen/
Swierstra 2023) makes "fully in place" a *checked keyword* discipline (`fip`/`fbip` on a function, a
compile error if it can't be lowered to zero allocation). **Kappa does NOT add `fip`/`fbip` keywords.** The
in-place property is *derived* from the ownership and usage facts the compiler already computes — the quantity/
borrow annotations (`1` owned, `&` borrowed, §12.2/§12.3) and the used-once usage intervals (`ucHi == 1`,
`Usage.hs`). There is no surface annotation; the compiler figures out in-place-ness from the code itself and
may *report* it, but a program never *asserts* it. (Kappa is unusually suited to this: FP² had to infer the
linear discipline on top of Koka's Perceus, whereas Kappa's quantity system *declares* exactly the
owned-consumed-once / borrowed-read discipline FIP needs.)

## 0. Why S6, and why in this order

**What "borrowing" is.** Every use of an *owned* value pays reference-counting: a non-final read may `dup`
(bump the count so the value survives to a later use) and the owner eventually `drop`s. A **borrowed**
parameter — written `&x` in a signature, e.g. `readSig : (& s : Sig) -> Int` — is a *read-only loan*: the
callee reads through it but never consumes it, and the **caller** keeps ownership and performs the single
`drop`. A borrowed access therefore needs **no `dup` and no `drop`** — it is a bare pointer read. This is
*literally* Perceus's owned-vs-borrowed calling convention, and Kappa already has it: `&` is the
non-consuming quantity (§12.3), the elaborator computes it, and S5 already carried it onto the backend IR
(`BinderOwn.boBorrowed`, the `Borrowed` use-kind — a borrowed use is read-only and never a last-use). So S6's
borrowing thread is mostly about *consuming* facts that already exist, plus verifying the borrow doesn't
escape.

**What "FIP" is.** S5's FBIP reuse is *opportunistic*: `drop_reuse(x)` checks `x`'s reference count is
exactly `1` **at run time** and falls back to `malloc`/`free` if it is not. Where the compiler can *prove* a
cell is uniquely owned, that runtime check is dead weight — the reuse always succeeds. **Fully-in-Place
(FIP)** is the property that a function performs **zero heap allocation and constant stack** on its reuse
path. Inferring it buys two concrete things: (1) **guard elision** — on a proven-unique reuse, drop the
`rc==1` branch entirely and overwrite in place unconditionally; and (2) **zero-allocation knowledge** — the
compiler *knows* (and can report/gate) that a function allocates nothing, which is both a guarantee and the
substrate the representation/unboxing program consumes.

**Why borrowing before FIP.** FIP's uniqueness proof asks "is this owned cell the *only* live reference
here?" — a question whose answer depends on knowing which other uses are *borrows* (non-consuming, don't
count against uniqueness) versus *owning moves*. Threading and consuming the borrow facts (Phase A) is the
prerequisite for the uniqueness analysis (Phase B). And S6 as a whole comes **after S5**: you cannot elide a
reuse guard until the guarded reuse exists.

**Honest scope (read this before expecting speed).** S6 removes *reference-counting* overhead — the `dup`/
`drop` traffic on reads (borrowing) and the `rc==1` branch on proven-unique reuse (FIP). It does **not** touch
the *representation* overhead: on Kappa's uniform-boxed `KValue`, each field access is still a `kctor_arg`
dispatch and each scalar a `kas_int` unbox (the residual that keeps the S5 rbtree fixture ≈1.3× slower than
`std::map` — see PERCEUS-S5-PLAN.md §4). Closing the gap to C/Rust/`std::map` is the **representation/
unboxing program** (immediate tagging + struct-packed layout, coupled with the LLVM backend), a separate arc.
S6 and unboxing are complementary: S6 removes RC ops and the uniqueness branch; unboxing removes the boxing/
dispatch. Neither alone beats hand-tuned C; together they are the endgame.

## 1. Phase A — opt-in Borrowing (consume the borrow facts; retire RC on reads)

Each sub-stage is **byte-identical / RC-neutral** (same observable output, RC-on == RC-off), exactly like the
earlier Perceus stages; the *measurable* win is a drop in emitted `dup`/`drop` count on borrow-annotated code.

- **S6.A0 — RC-elide borrowed uses.** *The problem:* today a borrowed parameter is still reference-counted as
  if owned — the callee may `dup` a read and the flow inserts `drop`s — pure waste, because the caller owns
  the value and drops it once. *The fix:* in the RC emission (`C.hs`/`LLVM.hs`, driven by the KBackendIR
  ownership node-facts), a `Borrowed` use emits **no `dup`**, and a borrowed binder carries **no `drop`
  obligation** (the owner's single `drop` at the call site is authoritative). A borrowed argument is passed as
  a bare, non-owned pointer. *Gate:* RC-on == RC-off; byte-identical output; **strictly fewer `dup`/`drop`
  ops** on the borrow corpus (the win); poison-clean; no leak (the owner still drops exactly once) and no
  double-free (the borrower drops never).
- **S6.A1 — borrow-escape verification (fail-closed).** *The problem:* the RC-elision in A0 is sound **only**
  if a borrowed value never outlives the borrow — it must not be stored in a heap cell that survives the call,
  returned as owned, captured by an escaping closure, or handed to a callee that expects to consume it. If it
  escapes, the caller `drop`s it while the escapee still reads freed memory — the classic borrow UAF. *The
  fix:* Kappa's elaborator already enforces this (`kappa.borrow.escape` / `borrow-escape-site`, §12.3), so S6
  adds a **defensive KBackendIR legality check** that trusts the front-end but **fails closed** if a borrowed
  binder ever reaches an owning sink in the lowered tree — analogous to the S5 §34.3.3 fail-closed validator.
  *Gate:* the verifier is green over the corpus; a synthetic escape (a borrowed value stored/returned owned)
  is rejected at compile time, not miscompiled.
- **S6.A2 — borrow across the IO/call boundary (close the D6 gap).** *The problem:* borrowing is most valuable
  exactly where reads are hottest — through a `do` block, a borrowed `& ref` read, a borrowed record/ctor
  projection base, a value passed borrowed into a sub-call — but that is the known "borrow-through-IO" hole
  (D6): the current flow conservatively re-owns across the IO-monad seam and across nested calls. *The fix:*
  extend the A0 elision through the IO/`do` lowering and the call convention so a value borrowed by the caller
  stays borrowed into the callee (the callee's parameter is `&`, so it neither dups nor drops). *Gate:*
  RC-op reduction on the IO/borrow-heavy paths; TSan/poison clean; borrow-on == borrow-off.

## 2. Phase B — inferred FIP (static uniqueness → guard elision → zero-alloc knowledge)

**The uniqueness proof.** For a drop/reuse candidate (an S5 fusion site: a dying owned cell about to be
overwritten by a same-size constructor in the same frame), the cell is **statically uniquely owned** when a
conjunction the compiler can already evaluate holds:
1. the binder is **owned and linear** — quantity `Q1` (consumed exactly once), not `QW`/shared, not `&`
   borrowed;
2. its **used-once interval** is exactly one — `ucHi == 1` in `Usage.hs`: no other live reference in scope
   reads it after the reuse;
3. the value is **statically non-shared** — a linear owned value that never crossed a fiber boundary can never
   carry the S4 `KRC_SHARED_BIT`, so runtime sharedness is provably false;
4. the reuse token **does not escape** the frame and there is **no aliasing use** between the drop and the
   reuse (the S5 frame-limited, non-escaping discipline) — and no suspension/effect boundary in between.

When all four hold, the reuse *cannot fail at run time*, so the runtime `rc==1` guard is redundant.

- **S6.B0 — the static-uniqueness analysis.** A dataflow pass over KBackendIR that evaluates the conjunction
  above at every S5 reuse candidate, from the S5 ownership node-facts + the `ucHi` usage intervals. It is
  **conservative by construction**: anything unknown ⇒ *not* proven unique ⇒ keep the S5 runtime-guarded
  reuse. *Gate:* the analysis runs and is *sound* — it never claims uniqueness where the runtime `rc==1` would
  be false. This is validated by keeping the runtime check as a **poison-mode debug assert** on claimed-unique
  sites (§3): a static-unique site whose runtime count is not `1` traps deterministically.
- **S6.B1 — guard elision (static reuse).** Where B0 proves uniqueness, lower the drop+alloc pair to
  `reuse_in_place(x, C, fields)` — a header rewrite that overwrites the cell's tag and fields **with no `rc==1`
  branch and no shared check** (contrast S5's `drop_reuse`, which branches). *Gate:* byte-identical;
  RC-on == RC-off; the uniqueness branch is **provably gone** on proven paths (a measurable instruction-count
  drop); **poison-clean is the primary safety oracle** — a wrong proof is a UAF that poison traps; a perf
  improvement on the linear reuse path.
- **S6.B2 — reuse-credit (`◇ₖ`) accounting → whole-function FIP.** *What it is:* the FP² calculus tracks, per
  frame, a balance of same-size cells *freed* (from proven-unique drops) against cells *allocated* — a
  "reuse credit" `◇ₖ` is a free reusable k-field cell in hand. A function whose credits balance (every
  constructor it allocates is matched by a proven-unique same-size cell it frees within the frame) is **fully
  in place**: it allocates nothing. *Why it generalizes B1:* B1 fuses a single match-arm drop with a single
  arm allocation; the credit accounting lifts this to whole-body zero-allocation across multiple constructors
  — the classic FIP shapes (in-place `reverse`, `map`, red-black-tree rotation/rebalance). *Gate:* the FIP
  fixtures (`reverse`, `map`, rbtree rotation) allocate **zero** and carry no reuse guard.
- **S6.B3 — the inferred-FIP property (derive, expose, gate) — NO keyword.** Surface the derived fact: (a) a
  KBackendIR node/function annotation "fully-in-place" computed by B2 (inferred, never declared); (b) an
  *optional diagnostic* that reports which functions the compiler inferred as FIP — the user's insight, and a
  precise signal for where the representation program will pay off; (c) a **regression gate** that a
  known-FIP hot function stays zero-allocation (a change that silently de-FIPs it is caught). There is **no
  `fip`/`fbip` surface keyword**: FIP-ness is a derived property of the code, reported but never asserted.
  *Gate:* the inferred FIP set is stable under the byte-identical/RC-neutral gates; de-FIP regressions on the
  tracked functions fail closed.

## 3. The correctness crux

- **Borrow soundness (Phase A).** A borrowed value MUST be dropped exactly once, by its **owner**, never by
  the borrower, and MUST NOT escape the borrow's lifetime. Invariant: a `Borrowed` use emits no `dup`/`drop`;
  the owner retains the single `drop`; an escape is rejected (A1). The failure mode is the classic
  use-after-free — a borrowed value stored past the call, then read after the owner freed it.
- **Uniqueness-proof soundness (Phase B — the dangerous one).** Guard elision (B1) *removes the runtime
  `rc==1` safety net*, so a **wrong** uniqueness proof is a silent UAF/corruption. Therefore B0 MUST be
  **sound (conservative)**: elide only where uniqueness is provable; any doubt keeps the S5 runtime-guarded
  reuse. Staged safety net, mirroring the whole arc: (i) keep the runtime `rc==1` as a **poison-mode debug
  assert** on B1 sites — a mis-proof traps deterministically before it can corrupt; (ii) the Boehm
  differential backstop catches a missed drop. This is the same de-risking discipline that made S2→S3 safe.
- **Composes with S4 for free.** A value that crossed a fiber boundary is marked shared (`KRC_SHARED_BIT`) and
  uses atomic RC; a *statically* owned linear value never crossed such a boundary, so it is provably
  non-shared and guard elision never applies to a cell another fiber could observe. The S4 shared bit remains
  the concurrency guard — a shared cell is never borrowed-uniquely and never guard-elided.
- **Totality + effects.** A FIP reuse path MUST be effect-neutral: a `defer`/`using`/handler that could
  observe a half-reused cell, or a suspension that could hand the token a second reference, breaks the
  in-place guarantee. The analysis excludes reuse across a suspension/effect boundary (the S5 frame-limit
  already enforces the token non-escape). Totality is an asset: structural recursion, no partial reuse from an
  escaping exception.
- **Erasure-aware "same size."** "Same size" for reuse is measured over **runtime-kept** fields (post-erasure)
  — the S5.A erasure-aware layout correctness is on FIP's soundness path; the uniqueness proof, the reuse, and
  the allocation it replaces must all agree on the runtime footprint.

## 4. Verification

1. **Poison detector (primary).** Build the corpus RC-on with `KAPPA_POISON=1`. A guard-elided static reuse
   of a non-unique cell overwrites storage another reference reads → that read traps on the `K_FREED`
   sentinel. Keep the runtime `rc==1` as a poison-mode assert on every B1 site so a mis-proof traps at the
   *reuse*, not later.
2. **Byte-identical / RC-neutral.** Borrowing and FIP must not change behavior: borrow-on == borrow-off,
   FIP-on == FIP-off, RC-on == RC-off, over the whole corpus.
3. **RC-op reduction (the measurable win).** Borrow-heavy code emits **strictly fewer** `dup`/`drop` ops
   (Phase A); proven-unique reuse **drops the `rc==1` branch** (Phase B). Gate on the op-count / branch
   reduction, not just correctness.
4. **Zero-allocation FIP fixtures.** In-place `reverse`, `map`, and rbtree rotation must allocate **zero**
   heap cells RC-on (the FIP property), and the inferred-FIP set must include them.
5. **ThreadSanitizer.** Shared cells are never borrowed-uniquely and never guard-elided, so there is no new
   data-race surface — the existing TSan run over the concurrency corpus must stay clean.
6. **Conformance / parity / underflow-clean** through both phases.

## 5. Risks

- **R-unique-misproof (highest).** Guard elision on a cell that is not actually unique ⇒ silent UAF. Guarded
  by conservative B0 inference + the poison-mode runtime assert on B1 sites + the Boehm backstop. *A doubtful
  proof must fall back to the S5 runtime-guarded reuse, never elide.*
- **R-borrow-escape (high).** A borrowed value stored/returned/captured beyond its borrow ⇒ UAF. Guarded by
  the elaborator's borrow-check (`kappa.borrow.escape`) + the A1 fail-closed KBackendIR verifier.
- **R-effect-reuse.** In-place reuse across an effect/suspension boundary ⇒ a half-reused cell observed by a
  deferred action or a resumed continuation. Excluded by the frame-limit + effect-neutrality condition in B0.
- **R-perf-illusion.** RC-op count drops but wall-clock barely moves because boxing/dispatch (`kctor_arg`/
  `kas_int`) dominates. Honest and expected: S6 removes RC overhead; the C/Rust/`std::map` gap is the
  **representation/unboxing** program's to close (see PERCEUS-S5-PLAN.md §4). S6's gates are RC-op reduction
  and zero-alloc, **not** a cross-language speed target.
- **R-inference-cost.** The static-uniqueness dataflow adds compile time. Mitigated by reusing the S5
  ownership node-facts + the already-computed `ucHi` intervals rather than a fresh analysis, and by keeping it
  a single pass over KBackendIR.

## 6. Sub-stages, ordering, gates

| sub | what | gate |
|---|---|---|
| **S6.A0** | RC-elide borrowed uses (no `dup`/`drop` on `Borrowed`; borrowed arg passed bare) | RC-on==RC-off; byte-identical; strictly fewer `dup`/`drop` on the borrow corpus; poison-clean; no leak/double-free |
| **S6.A1** | borrow-escape fail-closed KBackendIR verifier | green on corpus; a synthetic borrowed escape is rejected at compile time |
| **S6.A2** | borrow across the IO/`do`/call boundary (close D6) | RC-op reduction on IO/borrow paths; borrow-on==borrow-off; TSan/poison clean |
| **S6.B0** | static-uniqueness analysis over KBackendIR (`Q1` ∧ `ucHi==1` ∧ static-non-shared ∧ non-escaping) | conservative + **sound**: never claims uniqueness where runtime `rc==1` is false (poison-assert validated) |
| **S6.B1** | guard elision — `reuse_in_place` (no `rc==1` branch) on proven-unique sites | byte-identical; the uniqueness branch is gone on proven paths; poison-clean; perf up on the linear reuse path |
| **S6.B2** | reuse-credit (`◇ₖ`) accounting → whole-function FIP | `reverse`/`map`/rbtree-rotation allocate zero and carry no guard |
| **S6.B3** | inferred-FIP property: derive + optional diagnostic + regression gate (**no keyword**) | inferred FIP set stable; de-FIP regressions on tracked hot functions fail closed |

Ordering rationale: Phase A precedes Phase B (uniqueness inference needs the borrow facts to know which uses
don't count against uniqueness); within A, elision (A0) precedes the escape verifier (A1) precedes the
IO/call widening (A2); within B, the sound analysis (B0) precedes guard elision (B1) precedes the whole-
function credit accounting (B2) and the derived-property surface (B3). S6 as a whole follows S5 (it elides a
guard on a reuse that must already exist).

## Critical files

- `src/Kappa/Usage.hs` — the used-once usage intervals (`UseCount`/`ucHi`); the `ucHi == 1` precursor B0
  consumes.
- `src/Kappa/Ownership.hs` — `BinderOwn.boBorrowed` and the `Borrowed` use-kind (already computed); the
  owned/borrowed/shared lattice the RC-elision (A) and uniqueness proof (B) read.
- `src/Kappa/Backend/IR.hs` — the static-uniqueness dataflow (B0) and the inferred-FIP annotation (B3) as
  passes over KBackendIR node-facts; the borrow-escape verifier (A1) as a fail-closed KBackendIR check.
- `src/Kappa/Backend/C.hs` / `LLVM.hs` — consume the borrow facts to elide `dup`/`drop` (A); emit
  `reuse_in_place` on proven-unique sites (B1).
- `runtime/kappart.h` / `runtime/value.c` — `reuse_in_place` (the guard-free in-place rewrite) + the
  poison-mode `rc==1` debug assert on static-unique sites.
- `test/native/run-native-tests.sh` — the RC-op-count reduction gate (A/B); the zero-allocation FIP fixtures
  (B2); the borrow/FIP poison + TSan corpus.

## Spec anchors

- **§12.2** (quantities are ownership-only; §12.2.7) and **§12.3** (the `&` borrow marker, non-consuming) —
  the owned/borrowed/shared substrate S6 consumes.
- **`kappa.borrow.escape` / borrow-escape-site** (§12.3) — the front-end borrow discipline the A1 verifier
  defends.
- **§34.4.1** (memory-management obligations — an RC-free MUST NEVER drive a source-level release) and
  **§34.3.7** (representation classes — the erasure-aware "same size" footprint).
- **PERCEUS-RC-DESIGN.md §7** (S6 in the staging: borrowing + inferred FIP) and **PERCEUS-S5-PLAN.md** (the
  reuse machinery S6 builds on; §4 for the representation-gated speed ceiling).
- **FP²: Fully in-Place Functional Programming** (Lorenzen/Leijen/Swierstra, ICFP 2023) — the reuse-credit
  calculus, adapted here as an **inferred** analysis with no surface keyword.
