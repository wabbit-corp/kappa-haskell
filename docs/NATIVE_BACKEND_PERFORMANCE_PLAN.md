# Native backend performance plan

Response to `docs/NATIVE_BACKEND_PERFORMANCE_REVIEW_NOTES.md` (2026-06-17).
The objection is accurate: the backend defaults to the generic boxed/string
ABI even where the compiler has the type/layout to do better. This plan
separates **quick wins** (this iteration) from **larger representation
changes** (staged), with concrete mechanisms, and ends with benchmark gates
and an adversarial performance review.

## Status (2026-06-17)

Quick wins **QW1–QW4 are DONE** (built `-Werror` clean; native suite ALL
PASSED incl. the new benchmark gates; conformance 242/242; native ≡
interpreter preserved). Measured: the `sum 1..1_000_000` perf smoke dropped
~0.45s → ~0.22s after QW1 (direct prim helpers eliminated per-iteration string
dispatch); a tight self-tail Int loop keeps `heap_size` ≈ 128 KB under QW2
(parameter env no longer rebuilt per iteration — confirmed by `bench.sh`'s
heap gate). The larger representation changes **LR1 (typed unboxed workers)**
and **LR2 (numeric ctor/variant/field IDs)** are STAGED (see below) with
benchmark evidence: the dominant remaining allocation in a tight Int loop is
`kint` result boxing (≈193 MB total / ≈1500 collections for `sum 1..2e6`,
`heap_size` tiny) — i.e. LR1's target, not the env (QW2 removed that). An
adversarial performance review (criterion #8) covers QW1–QW4's correctness and
efficacy and grounds the LR staging.

## Raw-C review (`NATIVE_BACKEND_RAW_C_PERFORMANCE_REVIEW.md`) — status scorecard

The raw-C report is the governing performance standard. Honest status (NOT a
claim the backend is raw-C overall — only the LR1 Int-worker case meets it):

| Item | Status |
|---|---|
| **P0.1** monomorphic numeric boxed → scalar workers | **MET for `Int`** (LR1: scalar `int64` worker, zero per-iter alloc, 1.03× `cc -O2`); `Bool`/`Double` workers not yet done |
| **P0.2** `var` loops are heap-ref loops | **MET for non-escaping Int var loops** — `arithloop` 145 MB → 704 bytes, 81.5× → 0.7× `cc -O2` (scalar int64 loop, GMP-overflow escape); effectful/escaping/non-Int/else/nested/for loops stay boxed |
| **P0.3** `KEnv`/`kvar` on hot paths | **MET for LR1 Int workers** (scalar locals, no `KEnv`/`kvar`); general first-order code still uses `kvar` (QW2 only removed the per-iter *rebuild*) |
| **P0.4** records/ADTs generic+string | **MET (no string scans on the match/projection path).** Records: `r.f` on a statically-known *sorted* layout → fixed-offset `krec_at` (named records + tuples <10; tuples ≥10 / open / sealed / dict stay `kproj`). Ctors/variants (**LR2**): pattern matching dispatches on a numeric `tagid` int compare (`kctor_tagid`/`kvariant_tagid`), not `kctor_is`/`kvariant_is` strcmp; `kis_cons`/`kas_bool` likewise. The `switch`/jump-table shape is deferred (linear int-compare chain kept); the boxing/alloc on a record/ctor-param worker is orthogonal (LR1-class) |
| **P0.5** known calls carry trampoline/closure | **MET for LR1 Int self-calls** (loop / direct, no trampoline); general known calls still trampoline |
| **P1.1** `-O2` perf builds | **DONE** (`bench.sh` builds native + raw-C at `-O2`) |
| **P1.2** raw-C baseline gates + ratios | **DONE** (raw-C baselines + native/C ratio; `tailsum` gated ≤5× C — actually 0.2×; `arithloop` reported as P0.2-pending) |
| **P1.3** QW2 doc overclaim | **FIXED** (QW2 = "env rebuild removed", not "env/kvar eliminated"; see below) |

LR1 (Int workers), P0.2 (`var`-loop locals), P0.4 (closed-record fixed-offset
projection), and LR2 (numeric ctor/variant match tags) are landed. The
remaining raw-C iterations are the `switch`/jump-table match shape (deferred
from LR2), Bool/Double scalar workers, and the general P0.3/P0.5 (bare locals +
direct calls for non-`Int` first-order code), each to be landed behind the
boxed-ABI fallback with its own review and raw-C gate.

## Quick wins (this iteration) — DONE

### QW1 — Kill string dispatch for statically-known saturated primitives (notes §1)
- Add a `KPrimId` enum (`runtime/kappart.h`) and factor the hot pure ops in
  `prim_fire_pure` into direct C helpers (`kp_addInt`, `kp_leInt`,
  `kp_showInt`, …) that the string chain also calls (one source of truth).
- Codegen (`compileApp`): for a saturated application whose spine head is a
  known prim with a direct helper, emit the **direct helper call**
  (`kp_addInt(a,b)`) — no `kprim_call`, no `prim_arity`, no `prim_is_io`, no
  `strcmp`. Fall back to `kprim_call` only for IO/partial/unlisted prims.
- A Haskell `primDirect :: Text -> Maybe (Text, Int)` table (helper name +
  arity) is the codegen source of truth; the native suite catches drift.

### QW2 — No per-iteration `KEnv` *allocation* in direct worker loops (notes §3, §5, criterion #4)
- **What QW2 actually does (corrects an earlier overclaim, raw-C review P1.3):**
  a capture-free worker builds its parameter `KEnv` cells ONCE before the
  `while(1)` loop and a self-tail call updates `cell->val` in place, so the
  loop performs no per-iteration `KEnv` *allocation*. It does NOT eliminate
  `KEnv`/`kvar` from the boxed worker's code path — params are still read via
  `kvar(kw_env,i)`. So QW2 = "env rebuild removed", NOT "env/kvar eliminated".
- Full elimination of `KEnv`/`kvar` (params as bare C locals, raw-C review
  P0.3) is achieved for **monomorphic Int workers by LR1** (the `kwi_*` worker
  uses scalar `int64_t` C params/locals — no `KEnv`/`kvar` at all). For general
  (non-Int / higher-order-adjacent) first-order code it remains open work.

### QW3 — Source-faithful generated C names + source-span comments (notes §6, criterion #6)
- Thread an enclosing-name hint into `freshN` for closures/lambdas/match
  blocks (`kfn_main_len__cons`, `kmatch_main_len`), with the global counter
  kept only as a uniqueness suffix.
- Emit a `/* <module.fn> : <role> */` comment before each generated helper.

### QW4 — Benchmarks + allocation/GC gates (notes §7, criterion #7)
- `test/native/bench.sh`: arithmetic loop, tail-recursive sum, list fold,
  record projection, variant match, bytes append/slice, IO loop — each timed
  native vs interpreter, with `GC_get_heap_size`/allocation counters in a
  `--bench` runtime mode. Wire a bounded smoke into the native suite so the
  optimized paths are *exercised*, not dead.

## Larger representation changes (STAGED — next iteration, with fallback to the boxed ABI)

Staging rationale: LR1/LR2 are whole-value-representation changes whose failure
mode is a *silent miscompile* (a wrong unboxing boundary or a ctor-tag
mismatch produces a wrong answer, not a crash) — the exact bug class the
native-backend conformance work (seven review rounds) fought. They are
sequenced as a distinct reviewed iteration rather than bundled with the
low-risk QW1–QW4 wins, each landing behind a boxed-ABI fallback and its own
native ≡ interpreter gate. Safe-design constraints captured now:

- **LR1** — an unboxed `int64_t` `Int` worker MUST escape to the GMP/boxed
  path on overflow (`Int`/`Integer` are unbounded, §6), so even a first pass
  needs the overflow-escape + boxed wrapper at every generic/HO/partial
  boundary; `Bool` (C `int`) and `Double` (IEEE, no overflow escape) are the
  lower-risk first targets. Target evidenced by the benchmark above (`kint`
  result boxing dominates a tight Int loop).
- **LR2** — ctor/variant tags must be CONSISTENT between codegen-emitted
  `kctor` calls and the runtime's own ctors (`knil`/`kcons`/`kbool`/`krat`);
  the safe scheme is a name-derived tag (e.g. a compile-time hash emitted by
  codegen + stored by `kctor`) with a `strcmp` confirm on tag-match (no
  collision miscompile), or record/tuple **fixed offsets** where the layout is
  statically known. The review's `remaining-cost` dimension picks the
  higher-value piece (note that short prelude-name `strcmp`s already
  early-exit, so record fixed-offset projection may outrank ctor tags).

### LR1 — Typed unboxed `Int` workers (notes §2, criterion #3; raw-C review P0.1) — **DONE (Int)**
A first-order monomorphic `Int` function gets an auxiliary scalar worker
`int64_t kwi_g(int64_t…, int *kovf)` beside the boxed `kw_g`:
- **Eligibility** (conservative; src/Kappa/Backend/C.hs `lr1Arity` + `i64Elig*`):
  n explicit, relevant (non-`Q0`) leading binders, and a body built ONLY from
  in-range `Int` literals, params, the int prims `{add,sub,mul,div,mod,neg,eq,
  lt,le}Int`, `if` with an int-compare condition, and SATURATED self-calls.
  Anything else (CLet, if-in-value-position, calls to other globals,
  ctor/proj/match/do/lambda, an implicit/erased binder, a user-shadowed prim)
  ⇒ ineligible ⇒ boxed-only.
- **Codegen**: tail self-calls become an int64 `while`-loop with direct param
  reassignment (no `KEnv`/`kvar`); non-tail self-calls recurse `kwi_g`; arith
  uses `__builtin_*_overflow`/`INT64_MIN` guards mirroring the `kp_*` helpers.
- **Overflow escape (§6 unbounded `Int`)**: the call site (`compileLr1Call`)
  unboxes `K_INT` args (`kunbox_i64`); a non-`K_INT` arg OR any int64 overflow
  sets `kovf` and re-runs the boxed worker `kw_g` from the ORIGINAL boxed args,
  so the result is identical to the interpreter (the boxed/GMP path is the
  reference). The unboxed worker is auxiliary — never the closure entry.
- **Verified**: a 20-program battery + two adversarial reviews (overflow/escape
  parity, eligibility soundness, regression) all PASS; `tailsum 1e6`:
  193 MB → **368 bytes**, and **1.03×** a handwritten `cc -O2` int64 loop at
  N=1e9 (raw-C review P0.1/P0.3/P0.5 met for the Int-worker case; gated in
  `bench.sh`). Soundness is enforced at runtime by `kunbox_i64` even if the
  body-structural classifier over-accepts: a non-`K_INT` arg always escapes
  before the unboxed worker runs.
- **Not yet done**: `Bool`/`Double` unboxed workers, and cross-function int64
  chaining (calls to OTHER eligible Int globals are currently a boxed
  boundary). These are follow-ups; `Int` self-recursive kernels are the win.

### P0.2 — Scalarize non-escaping Int `var` loops (raw-C review P0.2) — **DONE (Int)**
A run of @var x = <in-range Int literal>@ declarations immediately followed by
a @while <int compare> do <flat non-monadic Int KAssign>+@ (no else, no IO /
closures / nested-or-for loops anywhere in the loop or continuation) lowers
each var to an int64 C local that shadows its retained heap ref:
- **Eligibility** (`scalarLoopPlan`/`i64LoopExpr`/`i64LoopCond`/`itemHasClosure`):
  conservative — anything outside the shape (effectful body, a closure/thunk/do
  anywhere, non-Int var, computed init, monadic assign, else clause, nested/for
  loop, an outer-var read in the body/cond) keeps the fully-boxed lowering, so
  no deferral can regress.
- **Codegen** (`compileScalarWhile`): a scalar int64 `while` loop; each var is
  SNAPSHOTted (int64 register copy, no alloc) at the iteration top; the body
  commits each assignment in place (sequential reads see new values).  On any
  overflow / INT64_MIN edge the escape flushes the SNAPSHOTS (pre-iteration
  values, NOT the partially-mutated scalars — avoiding double-application of an
  earlier assignment) to the heap refs and jumps to the EXISTING boxed loop,
  which re-runs that iteration with GMP promotion (§6).  Normal completion
  flushes the final scalar values; the continuation reads the refs.
- **Verified**: a battery + two adversarial reviews — the second found and this
  fixes a mid-iteration-overflow double-apply blocker (the snapshot mechanism);
  re-review PASS, zero serious.  `arithloop` 145 MB → **704 bytes**, 81.5× →
  ~4× `cc -O2` (scalar int64 loop, zero per-iteration allocation), gated in
  `bench.sh`.
- **Not yet done**: loops with an else clause, nested/for loops, effectful
  bodies (correctly boxed today), Bool/Double vars.

### P0.4 — Fixed-offset closed-record projection (raw-C review P0.4) — **DONE (record projection)**
A projection `r.f` where the receiver's type is a statically-known closed
record (`VRecordT fs`) lowers to a fixed-offset `krec_at(r, i)` (the tuple
fast path) instead of `kproj(r, "f")` (a linear `strcmp` scan over the K_REC
field names) — the report's "no string scans / fixed-offset access".
- **A new Core node `CProjAt e f i`** carries the offset from elaboration to
  the backend. The elaborator (`Check.hs` `ordinaryAt`, the closed-`VRecordT`
  branch — the ONE site with a statically-known closed layout) computes
  `i = elemIndex f (map fst fs)`. The interpreter (`Eval.hs`) treats `CProjAt`
  EXACTLY like `CProj` (projects by name, ignores the index), so `check`/`run`/
  `test` are byte-identical — `CProjAt` is a backend-only refinement. Every
  other projection site (open / row-polymorphic, sealed §13.2.10, trait-dict,
  derived single-ctor, metavariable receiver) stays a name-based `CProj`.
- **Soundness guard (the one subtle invariant):** the offset is the field's
  index in the K_REC *slot* order, which is the value's `CRecordV` order. For
  NAMED records that order is canonical `sortOn fst`, so the index = the
  field's position in the (sorted) `fs`. TUPLES are the one closed record
  whose value is built POSITIONALLY (`_1.._n`); at arity ≥10 the positional
  order diverges from lexicographic (`_10` sorts before `_2`), so a
  lexicographic index would read the WRONG slot. Therefore `CProjAt` is emitted
  **only when `map fst fs == sort (map fst fs)`** (the layout is provably
  sorted, so `fs` order = the krec emit order); any unsorted layout (tuples
  ≥10) falls back to the name-based `CProj`/`kproj`. Named records and tuples
  of arity <10 keep the fast path.
- **Verified**: a battery + an adversarial review (which FOUND the ≥10-tuple
  wrong-slot blocker — the guard above is the fix) + a focused re-review, both
  PASS zero-serious; in-tree conformance 242/242, `cabal test`, the native
  suite (incl. `recordproj` named-record + `tupleproj` arity-2..12 cases), and
  the external fixture corpus all show native ≡ interpreter with **zero
  regression** (per-fixture identical pre/post P0.4).
- **Scope honesty**: this removes the `strcmp` string scan on the projection
  path (a time win — `recproj` 0.16→0.13s). It does NOT reduce `recproj`'s
  allocation (96.8 MB is `kint` boxing in the un-scalarized record-param
  worker — an orthogonal LR1-class issue). Ctor/variant pattern-match tags
  (still `kctor_is`/`strcmp`) are DEFERRED to LR2 (#147).

### LR2 — Numeric tags for constructors / variants (notes §4, criterion #5) — **DONE (ctor/variant match dispatch)**
Pattern matching dispatches on a per-value numeric `tagid` (an int compare)
instead of a `kctor_is`/`kvariant_is` `strcmp` over the constructor name —
the raw-C "no string scans on the match common path". (Record-field offsets
were the P0.4 half of criterion #5.)
- **Representation**: `int tagid` added to the `K_CTOR` and `K_VARIANT` union
  members (`runtime/kappart.h`). It is FREE — the `KValue` union was already
  32 bytes (the `thunk` member), so `sizeof(KValue)` stays 40 and there is no
  per-value allocation increase. The constructor/variant `name`/`tag` strings
  are retained (diagnostics, rep-equality, §13.3 member identity).
- **Identity scheme**: the runtime builds 8 builtins (Unit/True/False/`::`/
  Nil/Some/None/`__rat`) so those share a FIXED enum (`KCT_*`, pinned by a
  `_Static_assert`) between the runtime and codegen. Every other (user)
  constructor is referenced by a `KT_<mangle gKey>` name, collected during
  emission and given a `KCT_USER_BASE + i` id by `assemble`; variants (never
  runtime-built) get a 0-based `KVT_<mangle tag>` id. The `assemble` step
  emits the `enum { KT_… }` / `enum { KVT_… }` blocks, so construction and
  match reference the *same* symbolic constant — correctness needs only that
  user ids clear the builtins (`KCT_USER_BASE`) and that distinct names get
  distinct constants (the existing `mangle` is injective). `kctor_tagid`
  returns `-1` for a non-constructor (and `KCT_UNIT` for the canonical
  `K_UNIT`), so a ctor test on a non-ctor scrutinee fails — preserving the
  `v->tag == K_CTOR` type guard the old `kctor_is` carried.
- **Construction/match**: `kctor`/`kctor0`/`kinject` gained a leading `tagid`
  parameter (the 7 runtime builtin sites pass the fixed enum; codegen passes
  the program id). `patTest` emits `kctor_tagid(v) == <KCT_*|KT_*>` /
  `kvariant_tagid(v) == KVT_*` / (`CPInjectRest`) `kvariant_tagid(v) != KVT_*`.
  `kis_cons` and `kas_bool` are now `tagid` compares too. The linear if-chain
  shape is unchanged (only the per-alt test expression changed), so behaviour
  is provably identical; `kctor_is`/`kvariant_is` (strcmp) remain for the
  non-hot diagnostics/rep-eq paths.
- **Verified**: a vetted design review (3 angles) + this iteration's three
  adversarial reviewers (spec-compliance, perf/code-quality, duplication/
  architecture) all PASS zero-serious; in-tree conformance 242/242, `cabal
  test`, the native suite (new `ctortags` case + a codegen assertion that the
  generated match path carries no `kctor_is`/`kvariant_is`), and the external
  fixture corpus (interpreter-only — LR2 touches only the `kappa build` path)
  all native ≡ interpreter with zero regression.
- **Deferred**: the `switch`/jump-table match shape — the int-compare chain
  already removes every `strcmp` from the dispatch, and for the dominant hot
  cases (list `::`/Nil, Bool, Option) `N` is tiny, so a jump table is a
  follow-up gated on a closed-ADT 8–16-arm microbench showing it ≥2× faster
  with guard-free single-head-tag arms. Also deferred: `as_rat` strcmp (non-
  hot), Bool/Double scalar workers.

## Adversarial performance review (criterion #8) — findings + remediation

The QW1–QW4 work was put through an adversarial performance reviewer (prebuilt
binary only). Outcome:

- **QW1 (direct prim helpers)** — verified behaviour-preserving: argument
  evaluation is forced into temps before the `kp_*` call; partial application
  correctly still curries via `kprim_call`; div/mod-by-zero, `INT64_MIN`,
  GMP-overflow promotion, and `eqDouble` (raw-bit) vs `floatEq` all match the
  interpreter. Reviewer-flagged gap (pure prims still on string dispatch):
  fixed by extending `primDirect` with `showInt`/`showDouble`/`showScalar`/
  `showStringLit`/`intToDouble`/`eqByte`/`ltByte`/`__intAnd`/`__intOr`/
  `__intXor`.
- **QW2 (in-place self-tail loop)** — reviewer found a **blocker**: an escaping
  closure/thunk capturing a loop parameter was corrupted because the in-place
  `cell->val =` mutation overwrote the snapshot it must observe. **Fixed**:
  `compileFunctionGlobal` now uses the in-place loop ONLY for a capture-free
  body (`bodyCapturesEnv`); a body that creates any env-capturing value
  (closure/thunk/do/letrec) falls back to the per-iteration env rebuild (the
  pre-QW2 behaviour), so each iteration's escaping closures capture a distinct
  env — matching the interpreter. Capture-free hot loops keep the no-alloc
  in-place path. The argument-aliasing case (`f a b = f b a`) was verified
  correct (args snapshotted into temps before any update).
- **QW4 (gates)** — reviewer found the `heap_size` gate **insensitive** to the
  per-iteration-allocation regression it claimed to catch (a reintroduced env
  rebuild moves `total_bytes` +65% but leaves `heap_size` byte-identical).
  **Fixed**: `bench.sh` now gates on `total_bytes` (cumulative, deterministic,
  sensitive) with per-bench bounds.
- **Remaining-cost** — confirmed the staged plan identifies the dominant costs:
  `kint` result boxing (~48 B/box, small-int cache `[-16,256]`) dominates a
  tight Int loop and is allocation-bound (LR1's target); the higher-value LR2
  sub-piece is record/tuple **fixed-offset projection** (`kproj` linear
  `strcmp` ~31 ns/op) over ctor tags (short prelude-name `strcmp`s already
  early-exit). This sharpens the LR staging above.

After remediation, a focused re-review (QW2 capture-correctness + gate
soundness + a regression sweep) returned **PASS / PASS, zero confirmed
serious**: `bodyCapturesEnv` is structurally total over all 25 `Term`
constructors (a missed capture is impossible by construction); every escaping
closure/thunk/do/letrec shape uses rebuild mode and matches the interpreter;
capture-free workers stay in the no-alloc in-place loop; the `total_bytes`
gate catches the +65% per-iteration-allocation regression a `heap_size` gate
would miss; and a 22-program sweep + the 25 native-suite cases show no
regression from the QW1 helper extension or the QW2 branching.

## Acceptance + review
- After QW1–QW4 (and as much of LR1/LR2 as lands), an **adversarial
  performance reviewer** (notes §8) checks for remaining string dispatch in
  generated hot paths, avoidable boxing, avoidable heap-env allocation, and
  opaque names — and that the optimized paths are exercised by the benchmarks.
- `KValue` stays the fallback ABI; the goal is that monomorphic first-order
  arithmetic / bool / projection / direct calls no longer route through it.
