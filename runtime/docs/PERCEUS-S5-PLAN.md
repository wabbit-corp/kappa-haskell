# Perceus Stage S5 — Implementation Plan (KCore/KBackendIR split → drop-guided FBIP reuse)

Status: **SCOPED, not started.** S0→S4 have landed and been independently reviewed sound: precise RC with
free-on-zero is default-on, with the biased fast/slow split + shared-object reclamation (TSan/UAF-clean,
25–45% thread-local RC perf recovered). S5 is the **marquee perf lever** — drop-guided **FBIP reuse**
(Functional But In-Place; Lorenzen/Leijen 2022), the rbtree-beats-`std::map` class of win. **Decision
(recorded):** S5 is done **split-first** — the KCore/KBackendIR split lands as Phase A, then the FBIP reuse
pass as Phase B on the typed IR. Companion to [PERCEUS-RC-DESIGN.md](PERCEUS-RC-DESIGN.md) §3 (the reuse
pipeline) and [KCORE-KBACKENDIR-SCOPING.md](../../docs/KCORE-KBACKENDIR-SCOPING.md) (the Phase A design).

## 0. Why split-first (the decision)

Full FBIP needs three things the current single-`Term` + path-keyed side-table cannot cleanly provide, and
all three are the KCore/KBackendIR split:
1. **Typed constructors** — the reuse pass matches a dropped cell's size against an allocated ctor's size;
   for cross-ctor and (future) unboxed/mixed layouts the size ≠ arity, so it needs the ctor **type + size /
   representation class** (§34.3.7), not a runtime tag-sniff.
2. **Stable ownership keys** — the reuse pass consumes drop-liveness + runtime-uniqueness facts, which today
   live in the **path-keyed** side-table (`Ownership.hs`); threading reuse tokens through that fragile
   `gsPath` scheme compounds the R-path risk that has been the recurring highest-rated hazard of the whole
   arc.
3. **A materialized erasure/representation lowering** — so the backend reads node fields instead of
   re-deriving (`isKindDomainValueAt`'s `quote∘force`, `argConvSelect` re-walks, …; ~69 sites).

The alternative — *basic same-arity match-local reuse on the side-table* (the rbtree win, faster payoff) —
was **not** chosen: split-first does S5 **once, cleanly**, retires R-path, and the split independently unblocks
**LLVM-RC** and the **layout/unboxing** program, so it is one foundational investment serving three levers.

## 1. Phase A — the KCore/KBackendIR split (S5's prerequisite; also the LLVM-RC + layout enabler)

The spec already mandates this pipeline (KFrontIR→KCore→KBackendIR; §28/§30.2/§31.2/§34.3 — see
[KCORE-KBACKENDIR-SCOPING.md](../../docs/KCORE-KBACKENDIR-SCOPING.md)). The current single-`Term` +
path-keyed side-table is the divergence. Migration, staged with gates — each **byte-identical / RC-neutral**,
exactly like the Perceus stages:

- **S5.A0 — thread the erasure classification (kill the `quote∘force`).** The elaborator already computed
  erased-vs-runtime (`Q0` ∨ kind-domain) at typecheck; carry it as a per-binder annotation and **delete
  `isKindDomainTerm`/`isKindDomainValueAt`**. Cheap, no refactor; kills the codegen NBE re-run. Gate:
  byte-identical; the re-derivation-site count drops; no `quote∘force` in the emitter.
- **S5.A1 — stable KCore identities; re-key the ownership audit table (retire R-path).** Replace the
  structural-path keys with stable binder/node identities (§30.2.5, §31.2's "keyed by … binder identity").
  The ownership metadata keys on identities, not `gsPath`. **This is the highest correctness value:** the
  `gsPath`-vs-`Ownership.walk` divergence class becomes structurally impossible. Gate: byte-identical;
  RC-on == RC-off; the S2.3d "silent lookup miss" class cannot recur.
- **S5.A2 — materialize KBackendIR.** A distinct lowered IR (pragmatically, an annotated `Term` wrapper
  first) produced by an explicit KCore→KBackendIR pass that discharges §31.2 erasure **once** and carries
  erasure / ownership / arg-convention as node **fields**. The backend reads fields; the ~69 re-derivation
  sites collapse. Gate: byte-identical; conformance/parity; the §34.3.3 KBackendIR legality checkpoints green.
- **S5.A3 — representation classes on KBackendIR nodes (§34.3.7).** Each ctor/match node carries ctor
  **type + size + rep class** — the substrate FBIP reuse consumes (and the unboxing/layout program). Gate:
  ctor size/type available at every drop/alloc site.

Validation mirrors the Perceus arc (byte-identical / RC-on==RC-off / conformance / parity through every
sub-stage). **A0 + A1 deliver most of the re-derivation + R-path relief before the full KBackendIR type
lands**, so the risk is front-loaded-cheap.

## 2. Phase B — drop-guided FBIP reuse (S5 proper)

The reuse pipeline (RC-DESIGN §3; runs **after** dup/drop insertion, **frame-limited**):

- **The reuse pass (on KBackendIR).** Identify a `drop(x)` of a ctor cell followed, in the **same
  frame/branch**, by an `alloc(C, fields)` of a **same-size** ctor → fuse into
  `token = drop_reuse(x); y = reuse_alloc(token, C, fields)`. The size comes from the S5.A3 rep class, not a
  runtime tag-sniff. The natural first site is exactly the S2.3a **match-destructure drop** + a same-size
  ctor built in the arm (`Cons h t → Cons h' t`, rbtree rotate, etc.).
- **The runtime primitives** (`kappart.h`/`value.c`):
  - `drop_reuse(x)` → if `x` is **unique** (thread-local `rc==1` **and not** `KRC_SHARED_BIT`) return `&x`
    *unfreed*; else a normal `kdrop` and return `NULL`.
  - `reuse_alloc(token, C, fields)` → `token != NULL`: write `C`'s tag + fields **in place** (0 alloc), reset
    the header to a fresh unique `rc=1` (a reused cell was thread-local-unique, so the shared bit is already
    clear); else `kctor` (malloc). A unique k-field rebuild becomes **0 alloc + k field stores** instead of
    malloc + k stores + free.
- **Drop specialization + dup/drop fusion** (the pipeline's middle): inline `drop` at a known ctor, cancel
  `dup`/`drop` pairs, so on the statically-unique fast path the RC ops **vanish**. This is where the typed
  KBackendIR (known ctor shapes) pays off.
- **The FBIP frontier**: frame-limited — the token must not escape the frame, and there is no reuse across a
  suspension/call that could re-alias `x`. Reuse credits (`◇ₖ`, RC-DESIGN §3) track available tokens within a
  frame.

## 3. The correctness crux — reuse ONLY a unique cell

- Reusing a still-aliased cell overwrites storage another reference reads ⇒ corruption/UAF. `drop_reuse`'s
  `rc==1` check is the **sole** guard.
- **Composes with S4 for free.** Uniqueness = thread-local `rc==1` **and not shared**. A **shared** cell is
  never `rc==1`-unique (it crossed a fiber boundary; atomic count; potential concurrent owners), so
  `drop_reuse` returns `NULL` for shared ⇒ **shared cells are never reused** and stay on the normal
  atomic-reclamation path. The S4 shared bit *is* the concurrency guard for reuse — a shared cell can't be
  overwritten out from under another fiber.
- **Reused-cell hygiene**: the match already `kdup`'d the kept fields (S2.3a); `reuse_alloc` overwrites the
  slots with the new fields and resets `rc=1`. Ensure no double-free of the old children and no leak of the
  reused cell's prior contents (the fields the arm does not carry forward are dropped exactly once).
- **Frame-limited / non-escaping**: the pass restricts reuse to a drop+alloc in the same frame/branch with a
  non-escaping token (a reused cell handed to a callee that stores it while the original path still uses it
  would alias) — the R-frame-escape guard.

## 4. Verification

1. **Correctness under the poison detector (primary).** Build the corpus RC-on + `KAPPA_POISON=1`: a reuse of
   a non-unique cell shows up as a read of an overwritten/poisoned cell → traps. The `rc==1` guard + the
   shared-bit exclusion + the frame discipline must keep it clean.
2. **Byte-identical output** — reuse must not change behavior: reuse-on == reuse-off, and RC-on == RC-off.
3. **TSan (the S4 gate continues).** Reuse composes with the biased split; shared cells are never reused, so
   there is no new concurrency surface — TSan-clean over the concurrency corpus must hold.
4. **The rbtree payoff (the whole point).** RC-DESIGN §3's proof target: Koka's rbtree insert ≈ 19% faster
   than hand-tuned C++ `std::map` with FBIP. Add an rbtree/list-map benchmark; gate on the **alloc reduction**
   (unique k-field rebuild ⇒ 0 alloc) and the speedup.
5. Conformance / parity / underflow-clean through both phases.

## 5. Risks

- **R-reuse-nonunique (highest).** Reusing an actually-aliased cell ⇒ UAF. Guarded by the runtime `rc==1`
  check + the shared-bit exclusion + the frame-limited non-escaping token; poison + TSan catch a violation.
- **R-size-mismatch.** The token size must equal the alloc size — the S5.A3 rep class provides it; the pass
  fuses only same-size drop/alloc. A mismatch ⇒ a reused cell too small/large ⇒ corruption.
- **R-frame-escape.** A token escaping its frame (stored by a callee; reused across a suspension). The pass
  restricts to same-frame/branch, non-escaping tokens.
- **R-shared-reuse.** A shared cell reused ⇒ concurrency UAF. Prevented by the shared-bit exclusion (shared ⇒
  never unique ⇒ never reused).
- **R-split-regression (Phase A).** The KBackendIR refactor is large (≈586 `CVar` sites, the interp, both
  backends). Mitigated by the incremental A0→A3 staging + the byte-identical gates; A0/A1 front-load the
  cheap, high-value relief.

## 6. Sub-stages, ordering, gates

| sub | what | gate |
|---|---|---|
| **S5.A0** | thread the erasure classification; delete `isKindDomain*`/`quote∘force` | byte-identical; re-derivation sites shrink |
| **S5.A1** | stable KCore identities; re-key the ownership audit table off `gsPath` | byte-identical; RC-on==RC-off; R-path class retired |
| **S5.A2** | materialize KBackendIR (erasure discharged once; ownership/rep as node fields) | byte-identical; §34.3.3 legality green; conformance/parity |
| **S5.A3** | representation classes (ctor type + size) on KBackendIR nodes | ctor size available at every drop/alloc site |
| **S5.B0** | runtime `drop_reuse`/`reuse_alloc` + the S4-aware is-unique check | unit: reuses a unique cell, never a shared/aliased one |
| **S5.B1** | the reuse pass (match-destructure drop + same-size arm alloc) | rbtree/list-map: 0-alloc unique rebuild; byte-identical |
| **S5.B2** | drop specialization + dup/drop fusion | RC ops vanish on the statically-unique path |
| **S5.B3** | the rbtree perf gate + poison/TSan over the corpus | the ≈19%-vs-`std::map` target; UAF/race clean |

Ordering rationale: Phase A must precede Phase B (the reuse pass reads typed ctor sizes + stable ownership);
within A, the cheap high-value relief (A0/A1) lands first; within B, the runtime primitive + a single proven
site (B0/B1) precede the general specialization (B2) and the perf gate (B3).

## Critical files

- `src/Kappa/Core.hs` + a new **KBackendIR** module — the typed KCore + the lowered, field-annotated
  KBackendIR (Phase A).
- `src/Kappa/Ownership.hs` — re-key on stable identities (A1); the reuse-token liveness / uniqueness facts
  (B).
- `src/Kappa/Backend/C.hs` / `LLVM.hs` — consume KBackendIR fields (retire the re-derivation sites); emit
  `drop_reuse`/`reuse_alloc` at the fused sites (B).
- `runtime/kappart.h` / `runtime/value.c` — `drop_reuse`/`reuse_alloc` + the S4-aware is-unique check; the
  in-place ctor rebuild.
- `test/native/run-native-tests.sh` — the rbtree perf gate; reuse-on==reuse-off; the poison/TSan corpus.

## Spec anchors

- **RC-DESIGN §3** (the drop-guided reuse pipeline, FBIP, drop specialization / dup-drop fusion, the rbtree
  target) and **§7** (S5 in the staging).
- **KCORE-KBACKENDIR-SCOPING.md** (the Phase A design + migration; the spec pipeline **§28 / §30.2 / §31.2 /
  §34.3**).
- **§34.3.7** (representation classes and specialization), **§34.4.1** (memory-management obligations).
