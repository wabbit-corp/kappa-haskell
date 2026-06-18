# Kappa Native Backend — Optimization Guide (authoritative)

Status: **authoritative, current to HEAD (R1.1/P0-A direct constructor lowering landed), 2026-06-18.**
This document consolidates and **replaces** six prior native-backend performance documents,
which have been **deleted** to reduce clutter (see §11 for the explicit old→new mapping; the
three git-tracked ones remain recoverable from git history, and all non-stale content — including
every citation and gap/roadmap item — is captured here and in the research workspace). The
companion `KAPPA_NATIVE_BENCHMARK_DESIGN.md` (detailed bench taxonomy) and
`test/native/bench/proposed/` (proposed bench sources) remain live and are referenced from §7/§8.
Scope: `src/Kappa/Backend/C.hs`, `runtime/kappart.{c,h}`, `test/native/bench/*`, and generated C
under `test/native/cases/`. Nothing here modifies compiler/runtime code — it is review, research,
and planning.

Provenance note: the research findings (§5) and full citation list (§6) carry `[measured]` /
`[design]` / `[folklore]` tags and survived two adversarial review passes (§10); two citation
errors and one stale implementation claim were corrected during that review. Where this guide and
any older document (e.g. in git history) disagree, **this guide is current and wins** — the six
older performance docs have been deleted and consolidated here (§11).

---

## 1. What is true today (one-paragraph verdict)

The backend is genuinely **near raw C for first-order monomorphic `Int` scalar/loop code** and
nothing else yet. The fast island is real and well-engineered: unboxed `int64` workers (LR1),
scalarized `Int` `var` loops (P0.2), fixed-offset closed-record projection (P0.4), and — landed
during this study — **integer-tag constructor/variant pattern matching (LR2)**, which removed the
`strcmp` dispatch the earlier reviews complained about — and, landed after it, **direct lowering of
saturated constructor applications (R1.1/P0-A)**, which removed the eta-expanded closure storm that
dominated `listfold`/`adtbuild`. **Outside that island the generic boxed/curried ABI is still the
default**: using a non-`Int` scalar or passing a function falls back to per-element allocation and
the arity-1 closure chain, one to two orders of magnitude from C. With P0-A fixed, `listfold`
dropped from 2.0 s / 544 MB to **0.68 s / 240 MB**, and `adtbuild` from ~1.09 GB to **480 MB**
(~240 B/iter) — the residual is now the genuine *data-representation* cost (one cons cell + one
`kint` box per element: P0-D / P1-F), not closure overhead. The boxed `KValue`/`KEnv` ABI is
correct as a *fallback* and must stay; the objection — repeated across all prior reviews and still
valid — is that it remains the *default* for monomorphic non-`Int` code.

**Can the output plausibly approach raw C?** Yes for what the typed IR can specialize to
first-order monomorphic scalar/loop code (demonstrated: LR1 ≈1.03× `cc -O2` — a single-config
internal measurement, see §8). No, not in general, without architectural commitments
(whole-program monomorphization; a precise moving GC) that carry documented failure modes (§5).
The defensible target: a small constant factor of C on first-order monomorphic code and on the
per-operation cost of the ADT/closure machinery; a larger but bounded factor on genuinely
higher-order/polymorphic code; the boxed ABI as the never-miscompiling fallback.

---

## 2. Runtime representation (the starting point everything reacts to)

Every Kappa value is a heap-boxed `KValue { KTag tag; union { … } }` (`runtime/kappart.h`),
~48 bytes on LP64, traced by a conservative Boehm GC. Functions are curried arity-1 closures
(`K_CLO`); multi-argument application is a chain of `kapp`. The de Bruijn environment is a
linked list of `KEnv` nodes (`kpush`/`kvar`). A small-int cache covers `[-16, 256]`
(`runtime/kappart.c`). `kbool` returns cached `the_true`/`the_false` singletons (so `Bool`-
returning comparisons allocate nothing). Pointer-free string/byte *payloads* use
`GC_MALLOC_ATOMIC`, but scalar boxes (`kint`/`kdbl`/`kchr`/`kbyte`) are allocated on the scanned
path. This is the uniform representation the optimization work selectively escapes.

---

## 3. Current implementation status (scorecard, current to HEAD)

Legend: **DONE** = landed and gated; **PARTIAL** = landed for a subset; **OPEN** = not started.

| Item | Status | Evidence (verified against re-emitted C at HEAD) |
|---|---|---|
| QW1 — direct prim helpers for saturated pure prims (`kp_addInt`, …) | **DONE** | `primDirect` has 32 entries (`C.hs`); emitted hot loops call `kp_*` directly, no `kprim_call`/`strcmp` |
| QW2 — no per-iteration `KEnv` *allocation* in capture-free self-tail loops | **DONE** | in-place `kw_c*->val =` update; capturing bodies fall back to per-iter rebuild (`bodyCapturesEnv`) |
| QW3 — source-faithful generated names + span comments | **DONE** | `kw_main_2e_range`, `kfn_main_2e_range_8`, `kmatch_*` |
| QW4 — benchmark + allocation/GC gates | **DONE** | `test/native/bench.sh` (total_bytes + raw-C ratio gates) |
| LR1 — unboxed `int64` `Int` workers (overflow escape to boxed/GMP) | **DONE (Int)** | `tailsum`: 193 MB → **368 B**, ≈**1.03× `cc -O2`**; scalar `kwi_*` worker, no `KEnv`/`kvar` |
| P0.2 — scalarize non-escaping `Int` `var` while-loops to `int64` C locals | **DONE (Int)** | `arithloop`: 145 MB → **704 B**, ≈4× `cc -O2` (gated ≤5×); the boxed loop is a dead overflow-escape fallback |
| P0.4 — fixed-offset closed-record projection (`krec_at`, no `kproj` strcmp) | **DONE (proj)** | named records + tuples <10; tuples ≥10 / open / sealed / dict stay `kproj` |
| **LR2 — numeric ctor/variant pattern-match tags** | **DONE (match dispatch)** | `patTest` emits `kctor_tagid(v) == KCT_*` / `kvariant_tagid(v) == KT_*` **integer** compares; `kctor_is`/`strcmp` gone from the match path. **`switch`/jump-table shape deferred** (linear int-compare chain kept). Record-field-label tags for record *patterns* not done. |
| **R1.1/P0-A — direct lowering of saturated constructor applications** | **DONE** | `etaCtorApp` (C.hs) beta-reduces a saturated eta-expanded ctor (`CApp…(CLam…(CCtor g …))`) to a direct `CCtor`; `compileApp`/`emitTailApp` emit `kctor(…)` with no `kclo`/`kapp`/`kappi`. Gated by `adtcons` (interpreter-equivalence) + a codegen-shape assertion (`kctor(KCT_CONS,` present, no `kappi(kclo(`). |
| **P0-B — capture-free in-place self-tail loop re-enabled** | **DONE (with R1.1)** | `bodyCapturesEnv` looks through the eta lambdas to the real fields, so a list-builder body is now capture-free; the QW2 cells update via `kw_c…->val =` instead of rebuilding `kw_env` each iteration. |

> **LR2 currency note (important).** LR2 (integer ctor/variant match tags) **landed during this
> study** (committed `fac5008`). Older drafts — and parts of the now-superseded
> `NATIVE_BACKEND_PERFORMANCE_PLAN.md`, which is internally inconsistent (one row says LR2 DONE,
> another still says "STAGED" / "DEFERRED to #147") — described matching as a `strcmp`/`kctor_is`
> chain. **That is stale.** Freshly re-emitted C at HEAD (`listfold.kappa.c`) shows
> `if (kctor_tagid(scrut) == KCT_NIL) … == KCT_CONS`. The user's "string-dispatched constructors"
> concern is therefore **resolved**; what remains is the much smaller `switch`-shape refinement
> (§4, P1-C).

### Reconciliation with the raw-C review's P0 blockers
The historical `NATIVE_BACKEND_RAW_C_PERFORMANCE_REVIEW.md` defined five P0 blockers; current
state:
- **P0.1** monomorphic numeric boxed → scalar workers: **MET for `Int`** (LR1); `Bool`/`Double` OPEN.
- **P0.2** `var` loops are heap-ref loops: **MET for non-escaping `Int` var loops**; effectful/escaping/non-`Int`/else/nested/for loops still boxed.
- **P0.3** `KEnv`/`kvar` on hot paths: **MET for LR1 `Int` workers** (scalar locals); general first-order code still uses `kvar`.
- **P0.4** records/ADTs generic+string: **MET on the match/projection path** — projection is fixed-offset `krec_at`; ctor/variant matching is integer-tag (LR2). The `switch` shape and record-param boxing remain.
- **P0.5** known calls carry trampoline/closure: **MET for LR1 `Int` self-calls** and **now for saturated constructor applications (R1.1/P0-A — a direct `kctor`, no eta-ctor closure chain)**; general known *function* calls still `ktrampoline` (P1-E).

---

## 4. Remaining issues (prioritized; P0 = blocks the raw-C-like claim for ordinary code)

Gap IDs (P0-A … P2-M) are defined here in §4 (they originate from the now-consolidated gap
analysis — see the §11 mapping); each remediation maps to a roadmap item in §7.

**P0-A — Saturated constructor applications lower to an eta-expanded arity-1 closure chain.
RESOLVED (R1.1, this study).** Previously `n :: acc` became
`kapp(kapp(kappi(kclo(kfn_range_4, kw_env), kunit()), …), …)` (the 3-deep curried `(::)` closure,
only the innermost calling `kctor`) — one cons cell costing ~3 `kclo` + 3 `kpush` + 2 `kapp` + 1
`kappi`, which dominated `listfold` (544 MB). Root cause: elaboration eta-expands the constructor
to a lambda (`§10.1 etaCtor`) and `compileApp` special-cased only prims and known function globals.
**Fix:** `etaCtorApp` recognises a saturated eta-ctor application (spine head is a `k`-deep `CLam`
chain whose body is `CCtor g [CVar …]`, with exactly `k` applied args) and beta-reduces it — each
field var names a binder, so the payload is just the applied arguments at those positions — to a
direct `CCtor`, lowered by `compileApp`/`emitTailApp` via the existing `compileCtor` as a single
`kctor(…)` with no closure/`kapp`. Verified on re-emitted `adtbuild.kappa.c` (`kctor(KCT_CONS,…)`,
no `kclo`/`kappi`); `listfold` 544 MB → **240 MB**, 2.0 s → **0.68 s**; `adtbuild` ~1.09 GB →
**480 MB**.

**P0-B — A captured env disabled the QW2 in-place loop for the whole worker. RESOLVED (with R1.1).**
The P0-A cons closure captured `kw_env`, so `bodyCapturesEnv` was true and the `range` worker
rebuilt `kw_env = kpush(p1, kpush(p0, 0))` every iteration. The R1.1 fix makes the cons a direct
`kctor` (capturing field *values*, not the env), and `bodyCapturesEnv` now looks through the eta
lambdas to the real fields — so the body is capture-free and the no-alloc in-place loop
(`kw_c…->val =`) is re-enabled. Confirmed in the re-emitted builder worker.

**P0-D — Every non-`Int` scalar result is boxed; non-`Int` first-order workers use `KEnv`/`kvar`.**
`Double`/`Bool`/record-param workers box a `kint`/`kdbl` per iteration (`recproj`'s 96.8 MB is
`kint` boxing) and read params via `kvar(kw_env,i)` linked-list walks. LR1 covers only
self-recursive `Int`. Pervasive — "the fallback ABI is still the default" for every scalar that
isn't a self-recursive `Int`. → **R2.2 / R2.3 / R2.4**.

**P1-C — Pattern matching is a linear if-chain over integer tags, not a `switch`/decision tree.**
*(Downgraded from P0 — LR2 shipped the integer tags; this is now a codegen-shape refinement, not a
representation problem.)* `consumeMatch` emits one `kctor_tagid(x) == K` test per alternative.
For few constructors this is already `-O2`-jump-table-able; the win is for many-constructor
matches and nested patterns (a Maranget decision tree avoids re-testing), plus numeric record-
field-label tags for record *patterns*. The collision-free `KCT_USER_BASE + i` IDs mean **no
name-derived-tag / `strcmp`-confirm scheme is needed**. → **R1.2** (re-ranked low).

**P1-E — Known saturated calls are wrapped in `ktrampoline` even when they cannot bounce.**
`compileDirectCall` wraps every non-LR1 worker call in `ktrampoline`. Correct at dynamic/higher-
order boundaries; wasteful for a known first-order call whose tail position cannot produce a
`K_BOUNCE`. → **R3.1**.

**P1-F — Scalar boxes are GC-scanned, not `GC_MALLOC_ATOMIC`. RESOLVED (R2.1, this study).**
`kint`/`kdbl`/`kchr`/`kbyte` have pointer-free payloads but allocated on the scanned path. **Fix:**
a new `alloc_val_atomic` (runtime `kappart.c`) allocates these four boxes via `GC_MALLOC_ATOMIC`,
so the collector skips them during mark and they are no longer conservative-GC false-pointer
sources. Sound because the payloads are genuinely pointer-free, the boxes are immutable / never
re-tagged, and all readers dispatch on `tag` (so `GC_MALLOC_ATOMIC`'s non-zeroed inactive union
bytes are never observed). `kstr`/`kbytes` (buffer pointer) and `kbigint` (mpz pointer) stay
scanned; `kbool`/`kunit` are one-shot singletons (left scanned). The win is cheaper collections
(less mark work) for `Double`/`Char`/`Byte` and out-of-cache integers — small ints in `[-16,256]`
are cache-served and allocate nothing, so they see no change. Gated by a runtime source invariant
in the native suite (the four scalar constructors must use `alloc_val_atomic`, never scanned
`alloc_val`) plus the full interpreter-equivalence suite (which proves the non-zeroing alloc is
correct). → **R2.1**.

**P1-G — Small-int cache is narrow (`[-16,256]`).** Any accumulator/counter outside that band
allocates a fresh box per update on the boxed path. The principled fix is immediate-tagged small
ints (with the Boehm tagging caveat, §5.1); the cache is a stopgap. → **R3.3**.

**P1-H — `KEnv` is a per-binding linked list, not a flat frame.** `kpush`/`kvar` allocate one node
per bound variable and walk the chain on lookup (`foldSum` does 2× `kpush` per element). Both slow
(chain walk) and space-unsafe (Shao/Appel). Flat frames + lambda-lifting non-escaping helpers fix
it. → **R3.2**.

**P1-I — Benchmark suite is a regression gate, not a raw-C performance proof.** `bench.sh` does
several things right (raw-C baselines at `-O2`, `volatile`+runtime-N, `total_bytes` gates, two
ratio gates) but is a single timed run over 4 narrow benches with no CIs and no coverage of
closures/HOFs/ADTs/strings/IO/effects. → **R0.1** + §7.

**P2 (architectural, deliberate decisions only):** whole-program monomorphization / flow-directed
defunctionalization (P2-J); precise generational/moving GC (P2-K); escape analysis → stack
allocation (P2-L); limited regions/arenas (P2-M, *not* full Tofte–Talpin). See §5/§7.

### Generated-name faithfulness & FFI (lower-priority, from the original review notes)
QW3 made names source-derived; residual nits are the `_2e_` dot-mangling readability and counter
suffixes that shift under unrelated edits (low priority). FFI/IO fast paths must remain
spec-compliant foreign bindings, not hidden prelude globals (the sqlite/socket demo direction);
the `sqlite_shape` bench (§7) deliberately models the *shape* without depending on non-spec
primitives.

---

## 5. Research findings (themes; full citations in §6)

Tags: `[measured]` = source reports its own benchmark; `[design]` = reasoned/formal argument;
`[folklore]` = widely repeated but not established by the cited primary source.

**5.1 Value representation & unboxing.** The central tradeoff (Leroy): uniform boxing makes
polymorphism trivial but forces allocation; specialized unboxing is faster but inserts coercions
at polymorphic boundaries that can *regress* hot polymorphic code `[measured]`. So selective
unboxing must be gated (worker/wrapper + demand/boxity analysis to avoid "reboxing"), and making
the *uniform* `KValue` cheaper is the lower-risk first move: low-bit **pointer tagging** of the
constructor tag (Marlow et al., ~14%/2% — figure from abstract metadata, indicative) `[measured]`,
**immediate small ints / NaN-boxing** (OCaml-style 63-bit tagged ints; LuaJIT/SpiderMonkey)
`[design]`, and **niche/NPO** for two-variant types like `Option` (Rust) `[design]`. **Boehm
caveat:** any low-bit tagging of the `KValue` word must guarantee the collector never mistakes an
immediate for a heap pointer — a real GC-contract risk on a conservative collector, more than a
footnote for the re-tag-the-word options. Whole-program **monomorphization + representation
selection** (MLton: unbox single-ctor types, flatten products) is the maximal escape but a
closed-world commitment.

**5.2 Closures & calling conventions.** Kappa's "every function is a chain of arity-1 `KFn`
closures" is **push/enter taken to the limit** — a saturated 3-arg call allocates and enters 3
closures. Marlow & PJ measured push/enter vs eval/apply as **roughly equal** and recommend
eval/apply for *implementation simplicity*, not a measured speedup `[measured-parity]`; note GHC's
push/enter does **not** allocate a closure per arg, so the paper does not directly measure Kappa's
pathology — the transferable lever is "give functions true arity + make saturated calls direct,"
justified by Kappa's *own* emitted C. Closures should be **flat** records (Shao/Appel: linked
closures like `KEnv` are both slow and space-unsafe) `[design]`; non-escaping helpers should be
**lambda-lifted** to top-level functions (no closure at all) `[design]`. **Defunctionalization**
(MLton flow-directed) is attractive only if whole-program; imprecise flow degenerates `apply` into
a big switch.

**5.3 Tail calls, IR, pattern matching.** Self-tail recursion must become a loop in the
*frontend* — `-O2` won't recover it (LLVM frontend docs; Regehr) `[design]`. For general tail
calls: trampoline (portable, Kappa's current choice), Cheney-on-the-MTA (Chicken; CPS + stack-as-
nursery), or LLVM `musttail`/`tailcc` (guaranteed but signature-restricted). C is a constrained
target (C--: no guaranteed tail calls / accurate GC roots / multiple returns). IR: a well-scoped
functional IR already *is* SSA (Appel) — adopt ANF (maps to C statements) or 2nd-class-continuation
CPS; "CPS is faster" is `[folklore]`. Pattern matching: Maranget decision trees test each subterm
at most once with a `switch` on an integer tag — Maranget measures *tree size*, not runtime, so
the runtime win is `[design]`. LR2 already shipped the integer tags; the `switch`/tree shape is the
remainder (P1-C).

**5.4 Allocation, GC, regions.** "Allocation is nearly free" is `[folklore]` for Kappa — true only
with a moving generational nursery (OCaml/GHC bump-pointer), not Boehm mark-sweep, where dead
objects are not free and integer-shaped words cause false retention. The one free win without
changing collectors: `GC_MALLOC_ATOMIC` for pointer-free scalar boxes `[design]`. **Escape
analysis** → stack allocation is GC-compatible and sound for AOT, but in a curried-closure
language almost everything escapes via a closure, so it pays off only *after* uncurrying/known-call
optimization (Choi `[measured]` 13–95% stack-allocated, up to ~43%/21% mean runtime — JIT,
whole-program; AOT must be conservative). **Regions:** do **not** adopt full Tofte–Talpin — MLton
rejected pure regions as space-leaky; at most a limited scoped-arena with GC fallback. JIT
"allocation sinking" is `[folklore]` for AOT (coupled to deopt).

**5.5 Benchmark methodology.** A performance *claim* needs more than a regression gate: defeat
dead-code elimination (`volatile` sink / runtime N), report mean ± confidence interval not
best-of-N (Georges) `[measured]`, randomize setup to expose measurement bias (Mytkowicz)
`[measured]`, spend repetitions where variance lives (Kalibera & Jones) `[design]`, and **count
allocations** separately from time.

---

## 6. Provenance — full citation list

All metadata verified via web search; the two corrected during adversarial review (§10) are
flagged. PDFs that returned binary (Marlow pointer-tagging numbers; Leroy) are flagged as
metadata-only. The MLton wiki is HTTP-only (read via search snippets). Raw per-cluster research
notes with extended notes live in the research workspace (`research/cluster{1..4}-*.md`); the
machine-readable index is `summary.json`.

Representation / unboxing / specialization:
- Leroy, "Efficient data representation in polymorphic languages," PLILP **1990**, LNCS 456 — https://doi.org/10.1007/BFb0024189
- Leroy, "Unboxed objects and polymorphic typing," POPL 1992 (coercion transform + measured ML speedups) — https://doi.org/10.1145/143165.143205
- Gill & Hutton, "The worker/wrapper transformation," JFP 19(2), 2009 — https://people.cs.nott.ac.uk/pszgmh/wrapper.pdf
- Peyton Jones & Launchbury, "Unboxed Values as First Class Citizens," FPCA 1991 — https://www.microsoft.com/en-us/research/publication/unboxed-values-as-first-class-citizens/
- GHC `GHC.Types.Demand` (demand + boxity) — https://hackage.haskell.org/package/ghc-9.12.1/docs/GHC-Types-Demand.html
- MLton WholeProgramOptimization / DeepFlatten / RefFlatten — http://mlton.org/WholeProgramOptimization
- Ziarek, Weeks, Jagannathan, "Flattening tuples in an SSA intermediate representation," HOSC 21(4):333–358, 2008 — https://doi.org/10.1007/s10990-008-9035-3
- OCaml "Memory Representation of Values" — https://ocaml.org/docs/memory-representation
- Marlow, Yakushev, Peyton Jones, "Faster laziness using dynamic pointer tagging," ICFP 2007 — https://dl.acm.org/doi/10.1145/1291220.1291194
- Rust Reference, "Type layout" (tagged union + niche/NPO) — https://doc.rust-lang.org/reference/type-layout.html
- de Vries & Löh, "True Sums of Products," WGP 2014 — https://www.andres-loeh.de/TrueSumsOfProducts/TrueSumsOfProducts.pdf
- "Type-Preserving Flow Analysis and Interprocedural Unboxing," arXiv:1203.1986 — https://arxiv.org/abs/1203.1986
- Titzer, "Unboxing Virgil ADTs for Fun and Profit," arXiv:2410.11094 — https://arxiv.org/abs/2410.11094

Closures / calling conventions / tail calls / IR:
- Marlow & Peyton Jones, "Making a Fast Curry: Push/Enter vs. Eval/Apply," ICFP 2004 / JFP 2006 — https://doi.org/10.1145/1016850.1016856
- Shao & Appel, "Efficient and Safe-for-Space Closure Conversion," TOPLAS 22(1), 2000 — https://doi.org/10.1145/345099.345125
- Paraskevopoulou & Garg, "Closure Conversion is Safe for Space," ICFP 2019 — https://doi.org/10.1145/3341687
- Johnsson, "Lambda Lifting," FPCA 1985, LNCS 201 — https://doi.org/10.1007/3-540-15975-4_37
- Reynolds, "Definitional Interpreters for Higher-Order Programming Languages," ACM 1972 — https://doi.org/10.1145/800194.805852
- Cejtin, Jagannathan, Weeks, "Flow-Directed Closure Conversion for Typed Languages," ESOP 2000 — https://doi.org/10.1007/3-540-46425-5_4
- Baker, "CONS Should Not CONS Its Arguments, Part II: Cheney on the M.T.A.," 1995 — https://www.plover.com/~mjd/misc/hbaker-archive/CheneyMTA.html
- LLVM LangRef (`tailcc`) / Clang `musttail` — https://llvm.org/docs/LangRef.html ; https://reviews.llvm.org/D99517
- Reig, Ramsey, Peyton Jones, "C--: A Portable Assembly Language that Supports GC," PPDP 1999 — https://www.cs.tufts.edu/~nr/c--/download/ppdp.pdf
- Flanagan, Sabry, Duba, Felleisen, "The Essence of Compiling with Continuations" (ANF), PLDI 1993 — https://dl.acm.org/doi/10.1145/155090.155113
- Kennedy, "Compiling with Continuations, Continued," ICFP 2007 — https://doi.org/10.1145/1291151.1291179
- Appel, "SSA is Functional Programming," 1998 — https://www.cs.princeton.edu/~appel/papers/ssafun.pdf
- Maurer, Downen, Ariola, Peyton Jones, "Compiling without Continuations," PLDI 2017 — https://doi.org/10.1145/3062341.3062380

Pattern matching / allocation / GC / regions / benchmark methodology:
- Maranget, "Compiling Pattern Matching to Good Decision Trees," ML Workshop 2008 — https://doi.org/10.1145/1411304.1411311
- Augustsson, "Compiling Pattern Matching," FPCA 1985 — https://doi.org/10.1007/3-540-15975-4_48
- LLVM Frontend Performance Tips — https://llvm.org/docs/Frontend/PerformanceTips.html ; Regehr, "How LLVM Optimizes a Function" — https://blog.regehr.org/archives/1603
- Tofte & Talpin, "Region-Based Memory Management," Inf.&Comp. 132(2), 1997 — http://ropas.snu.ac.kr/lib/dock/ToTa1997.pdf ; MLton "Regions" — http://mlton.org/Regions
- Choi et al., "Escape Analysis for Java," OOPSLA 1999 — https://faculty.cc.gatech.edu/~harrold/6340/cs6340_fall2009/Readings/choi99escape.pdf ; Blanchet — https://bblanche.gitlabpages.inria.fr/escape-eng.html
- Peyton Jones, Partain, Santos, "Let-floating," ICFP 1996 — https://dl.acm.org/doi/10.1145/232627.232630 ; Stadler et al., "Partial Escape Analysis and Scalar Replacement," CGO 2014 — https://dl.acm.org/doi/10.1145/2581122.2544157
- OCaml GC docs — https://ocaml.org/docs/garbage-collector ; Marlow et al., parallel generational-copying GC, ISMM 2008 — https://simonmar.github.io/bib/papers/parallel-gc.pdf
- Boehm GC interface (`GC_MALLOC_ATOMIC`) — https://hboehm.info/gc/gcinterface.html ; Bone, Boehm fragmentation — https://paul.bone.id.au/blog/2016/10/08/memory-fragmentation-in-boehmgc/
- Mytkowicz et al., ASPLOS 2009 — https://users.cs.northwestern.edu/~robby/courses/322-2013-spring/mytkowicz-wrong-data.pdf
- Georges et al., OOPSLA 2007 — https://dri.es/files/oopsla07-georges.pdf ; Kalibera & Jones, ISMM 2013 — https://kar.kent.ac.uk/33611/

---

## 7. Proposed solutions & priority

Sequenced into reviewable waves; each lands behind the boxed-ABI fallback with a native≡
interpreter gate (the project's standing safety discipline — a wrong unboxing boundary or tag is a
*silent miscompile*, not a crash). Guiding principle: do what `-O2` cannot (direct construction,
tag switches, unboxed loop bodies, self-tail loops) in the frontend; do **not** re-implement
LICM/unrolling/GVN that `-O2` already does. Full per-item detail (acceptance gates, dependencies)
is preserved from the roadmap below.

| Order | Item | Targets | Impact | Complexity | Risk |
|------:|------|---------|:------:|:----------:|:----:|
| 1 | **R0.1** rigorous bench harness + broad coverage | P1-I | High | Med | Low |
| ✓ | **R1.1** direct lowering of saturated constructor applications — **DONE** | P0-A/B | **Very high** | Med | Med |
| ✓ | **R2.1** `GC_MALLOC_ATOMIC` for pointer-free scalar boxes — **DONE** | P1-F | Med | Low | Low |
| 4 | **R2.2** `Bool`/`Double` unboxed workers (LR1 generalized) | P0-D | Med-High | Med | Med |
| 5 | **R2.3** first-order worker params/locals as C locals / flat frame | P0-D/P1-H | High | High | Med |
| 6 | **R2.4** cross-function unboxed scalar chaining | P0-D | Med | Med | Med |
| 7 | **R3.1** drop `ktrampoline` on known non-bouncing saturated calls | P1-E | Med | Med | Med |
| 8 | **R3.2** generalized eval/apply known-arity calls + flat closures | P0-D/P1-H | High | High | Med-High |
| 9 | **R3.3** immediate-tagged small integers (Boehm tagging caveat) | P1-G | High | High | High |
| 10 | **R1.2** `switch`/decision-tree match shape + record-field-pattern tags (LR2 core already shipped) | P1-C | Low-Med | Med | Low-Med |
| — | **R4.x** architectural: escape analysis (R4.1), precise GC (R4.2), monomorphization/defunctionalization (R4.3), limited regions (R4.4) | P2-J/K/L/M | — | — | — |

Rationale: **R1.1 landed (this study)** — it attacked the verified worst path (`adtbuild`/
`listfold`), was backend-local, and re-enabled QW2's in-place loop for free (P0-B); the next
non-harness item, **R2.1** (atomic scalar boxes), also landed; next is the Wave-2 non-`Int`
calling-convention work (**R2.2** `Bool`/`Double` unboxed workers, then **R2.3/R2.4**). **R1.2 is
re-ranked to the bottom of the active list because LR2's core shipped** — only the `switch` shape
remains, and a linear integer-`==` chain is already `-O2`-jump-table-able. Wave 2 is the pervasive
non-`Int` calling-convention work where Leroy's regression warning bites — do the low-risk
`GC_MALLOC_ATOMIC` first and gate the unboxing. Wave 3 needs Waves 1–2 to shrink the surface
first. Wave 4 is deliberate architecture, justified only by post-Wave-3 measurements; do **not**
adopt full region inference.

---

## 8. Raw-C expectations & measurement gates

**Expectation by code class:** first-order monomorphic `Int` scalar/loop code — small constant
factor of C (LR1 reports ≈1.03× `cc -O2` for `tailsum`; P0.2 ≈4× for `arithloop`, gated ≤5×; these
are single-config internal measurements reproducible via the live `test/native/bench.sh` (and
originally recorded in the now-deleted performance plan, in git history per §11), subject to the
§5.5 caveats and to be re-measured with CIs). ADT/record/closure/polymorphic code —
currently one to two orders of magnitude from C, expected to reach a *bounded* factor as Waves
1–3 land, never as low as the `Int` island without architectural changes (§5/§7). The boxed ABI
remains the correct fallback.

**Current measured workloads** (native `-O2` vs conservative raw-C, from the historical raw-C
review; re-measure under §5.5 before citing as proof):

| Bench | Native time / alloc | Raw-C time | Note |
|---|---|---|---|
| `arithloop` 2e6 | 704 B (was 145 MB) | 0.0021 s | P0.2 scalar `int64` var loop; ≈4×, gated ≤5× |
| `tailsum` 2e6 | 368 B (was 193 MB) | 0.0023 s | LR1 unboxed `Int` worker; ≈1.03× |
| `recproj` 1e6 | 96.8 MB | 0.0014 s | P0.4 removed `strcmp`; `kint` boxing remains (P0-D) |
| `listfold` 1e6 | **240 MB / 0.68 s** (was 544 MB / 2.0 s) | 0.050 s | R1.1 removed the eta-ctor closure storm (P0-A); residual = cons cells + `kint` boxing (P0-D) |
| `adtbuild` 2e6 | **480 MB / ~240 B/iter** (was ~1.09 GB) | 0.14 s | R1.1 direct `kctor`; the P0-A probe — now data-representation-bound |

**Current gates (`test/native/bench.sh`, P1.1/P1.2 DONE):** native + raw-C built at `-O2`;
`total_bytes` allocation bounds (`arithloop`/`tailsum` ≤1 MB, `recproj` ≤140 MB, `listfold`
≤620 MB); raw-C ratio gates `tailsum` and `arithloop` ≤5×. Gates are on cumulative `total_bytes`
(not `heap_size`, which is insensitive to per-iteration churn). **Methodology gap (P1-I):** single
timed run, no CIs/repetition, no setup randomization, narrow coverage — a regression gate, not a
raw-C proof.

**Benchmark plan (full taxonomy in `KAPPA_NATIVE_BENCHMARK_DESIGN.md`).** Adopt: ≥10 invocations
with median ± interval; setup randomization; per-iteration allocation (`total_bytes / N`);
allocation counted separately from time; ratio gates extended beyond the two scalar cases as
roadmap items land (e.g. an `adtbuild` alloc/iter gate after R1.1; a `switch`-emitted check on
`adtmatch` after R1.2). **Suggested initial gate thresholds (from the raw-C review):** scalar
arithmetic and tail-recursive numeric loops ≤ 5× conservative C with zero per-iteration
allocation on the non-overflow path; fixed record projection ≤ 10× conservative C with no string
scans on the optimized path; list fold may allocate list cells but should not allocate closure/
env/bounce boxes per element beyond the required data representation. **16 proposed benches** exist and **all build and run** at HEAD under
`test/native/bench/proposed/` (+ raw-C baselines + README), each documenting purpose / expected
lowering / raw-C baseline / failure mode, covering: scalar `Int`/`Double` loops, ADT construction
(`adtbuild` — the P0-A probe) and matching (`adtmatch`), mutual recursion, HOFs/closures, escaping
closures/space-safety, `Option`/`Result`, polymorphic-vs-monomorphic, list pipelines, byte loops,
string building (quadratic check), IO boundary, defer/effects, a sqlite-shaped query loop
(modeled, no real FFI), and a tiny HTTP/serialization kernel.

---

## 9. Internal-consistency invariants (so this doc does not go stale the way the old ones did)

- **LR2 = DONE (match dispatch); `switch`-shape = OPEN.** Never describe matching as `strcmp`/
  `kctor_is` — that is the pre-`fac5008` state.
- **R1.1/P0-A = DONE; P0-B = DONE (with it).** Never describe a saturated constructor application
  as an eta-expanded `kclo`/`kapp`/`kappi` chain — that is the pre-R1.1 state; it is now a direct
  `kctor`, and the list-builder's in-place self-tail loop is re-enabled. Partial ctor applications
  still build a closure (correctly), and the small-arity `kctor` still copies a stack `argv` array
  (a separate, optional ABI refinement).
- **LR1/P0.2 = `Int` only.** `Bool`/`Double`/record-param scalars are still boxed (P0-D).
- **P0.4 = projection only**, and only for sorted/closed layouts (named records, tuples <10);
  ctor/record-*pattern* field access and tuples ≥10 still use name-based paths.
- **The boxed `KValue`/`KEnv` ABI is the intended fallback**, not a defect — the objection is that
  it is the *default* for monomorphic non-`Int` code.
- **Raw-C numbers are single-config internal measurements** until re-run under §5.5.

---

## 10. Provenance, adversarial review, and currency history

This guide consolidates a study whose research and review trail is preserved in the research
workspace (`/opt/workspaces/kappa-haskell-perf-research/`): four raw research-cluster notes
(`research/cluster{1..4}-*.md`), implementation evidence with emitted C
(`evidence/`), a machine-readable `summary.json`, and two adversarial review records
(`research/adversarial-review-{1-sources,2-applicability}.md`). Two adversarial passes ran against
the source documents:

- **Pass 1 (sources/provenance):** 2 BLOCKER + 4 MAJOR + 4 MINOR; 9 remediated, 1 rejected with
  web-verified rationale. Corrected: Leroy "Efficient data representation" is PLILP **1990** (not
  1992; the 1992 paper is "Unboxed objects and polymorphic typing"); Ziarek "Flattening tuples" is
  HOSC 21(4) 2008 (the prior ACM DOI resolved to an unrelated paper). Re-tagged: eval/apply as
  `[measured-parity]` (the paper found ~equal performance, recommends eval/apply for simplicity),
  Maranget's runtime claim as `[design]` (it measures tree size). Rejected: the Choi escape-
  analysis figures (13–95% / ~43% / ~21%) — web-verified as the OOPSLA'99 paper's own.
- **Pass 2 (applicability/bench quality):** 2 BLOCKER + 4 MAJOR + 2 MINOR, all valid findings
  remediated. The decisive finding: **LR2 landed mid-study**, so the "strcmp chain" gap was stale —
  re-verified against re-emitted C at HEAD and corrected (this is why §3/§4 are LR2-current). Also
  fixed: three proposed benches that segfaulted on deep non-tail recursion (rewritten tail-
  recursive; the segfault is itself a noted robustness observation — native non-tail recursion
  rides the C stack), a `byteloop` that measured `natToInt` not per-byte work, and `kbool`
  wrongly listed as an allocating scalar box.

---

## 11. Old → new document mapping (nothing important lost)

The six consolidated documents have been **deleted** (not stubbed) to reduce clutter, per the
project decision that git history plus this guide preserve everything important. Their content
maps as follows; the three git-tracked docs (`NATIVE_BACKEND_PERFORMANCE_PLAN.md`,
`…REVIEW_NOTES.md`, `…RAW_C_PERFORMANCE_REVIEW.md`) remain recoverable via
`git show HEAD:docs/<file>`; the three untracked docs (`FUNCTIONAL_…RESEARCH.md`,
`…GAP_ANALYSIS.md`, `…OPTIMIZATION_ROADMAP.md`) had no git history but are fully captured here and,
in extended form, in the research workspace (`research/cluster{1..4}-*.md`, `summary.json`,
`research/adversarial-review-*.md`).

| Old document | Maps into this guide |
|---|---|
| `FUNCTIONAL_NATIVE_BACKEND_OPTIMIZATION_RESEARCH.md` (research survey, ~40 cited sources, folklore/measured tags) | §5 (findings by theme) + §6 (full citation list) + §10 (provenance/tag corrections). Extended per-cluster notes remain in `research/cluster{1..4}-*.md`. |
| `KAPPA_NATIVE_BACKEND_IMPLEMENTATION_GAP_ANALYSIS.md` (gaps P0-A…P2-M vs HEAD, answers to concerns) | §3 (status scorecard) + §4 (remaining issues, same IDs) + §1 (verdict / "approaches raw C") + §9 (invariants). |
| `KAPPA_NATIVE_BACKEND_OPTIMIZATION_ROADMAP.md` (waves R0–R4, impact/complexity/risk) | §7 (priority table + rationale). |
| `NATIVE_BACKEND_PERFORMANCE_PLAN.md` (QW1–QW4 + LR1/LR2/P0.2/P0.4 status, adversarial perf review) | §3 (scorecard, LR2-current — supersedes the plan's internally-inconsistent LR2 status) + §8 (numbers/gates) + the raw-C P0.x reconciliation in §3. |
| `NATIVE_BACKEND_PERFORMANCE_REVIEW_NOTES.md` (original harsh review: string dispatch, boxing, KEnv, names, FFI) | §2 (representation) + §4 (P0-A/D, P1-C/E/F/G/H, names & FFI notes) — its §1 string-dispatch objection is recorded as RESOLVED (QW1 + LR2). |
| `NATIVE_BACKEND_RAW_C_PERFORMANCE_REVIEW.md` (raw-C bar, P0.1–P0.5 blockers, gate proposals) | §3 (P0.1–P0.5 reconciliation) + §8 (raw-C expectations, numbers, gates) + §1 (verdict). |

Documents intentionally **not** consolidated (kept as-is): `KAPPA_NATIVE_BENCHMARK_DESIGN.md`
(detailed bench taxonomy — companion to §8), `NATIVE_BACKEND.md` (GC model / supported-subset
design), `NATIVE_BACKEND_REPORT.md`, `NATIVE_FFI_DESIGN.md`, `NATIVE_ESCALATIONS.md`.
