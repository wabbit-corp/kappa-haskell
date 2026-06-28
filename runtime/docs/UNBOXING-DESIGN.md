# Value-Representation Specialization (Unboxing) for the Kappa Native Backend

Status: Proposed (final) · Owner: compiler architecture · Audience: backend + runtime

This is the FINAL design. It incorporates the adversarial correctness, performance, and
feasibility reviews. Where a review demanded a fix, it is either applied below or
explicitly addressed in §11 (Required-fix ledger) with a pointer to where it is handled.
Two themes from the reviews reshaped the plan and are worth stating up front:

1. **Stage 1 is not a "localized overlay."** Low-bit immediate tagging is a *whole-runtime
   invariant change*. There are **299 raw `->tag`/`->as.*` dereference sites in
   `runtime/kappart.c`** (plus 2 in `rt.c`, 6 in `atomic.c`); every one that can receive a
   value we make immediate must tag-test before it dereferences, or it silently miscompiles
   or segfaults on an odd word. The cheap *codegen* delta does not imply a cheap *runtime*
   delta. Stage 1 is re-scoped accordingly (§5, §7).
2. **The honest win is smaller than "50x → 1x."** Tagging removes the *allocation* half of
   the gap (64 B → 0 B) but leaves per-op tag arithmetic; worker/wrapper unboxing only pays
   off in *unbox-to-unbox-fused, suspension-free* regions because `compileScalarCall`
   re-boxes every isolated result. Per-stage expected wins are quantified in §8, not
   hand-waved.

---

## 1. TL;DR recommendation

Do **both**, in this order, because they attack different halves of the same gap and one
unblocks the other:

1. **Stage 1 — low-bit immediate tagging of `Int` (and `Bool`/`Char`/`Unit`/nullary ctors)
   in the native backend only.** A small `Int` rides *inside* the `KValue*`-sized word as
   `(i<<1)|1`. Uniform representation change — no type analysis, no specialization. It
   closes the per-`addInt` allocation everywhere a value flows (calls, `KEnv`, across CPS
   parks), composes with conservative Boehm (odd words are non-pointers), and pre-installs
   the ptr-vs-scalar discriminator a future Perceus RC needs. **Caveat now made central:**
   it is a runtime-wide deref audit, not a localized swap, and it requires canonicalizing
   value encoding (§5.2) and a verified GC/alignment contract (Stage 0, §7) *before* it is
   sound.

2. **Stage 2 — type-directed worker/wrapper specialization per *representation class*, not
   per type.** Generalize the existing `scalarPlan`/`typeScalarKinds`/`kwi_`/`kwd_`
   machinery from "non-escaping Int loop var" to a first-class **layout kind**
   (`Boxed | I64 | F64 | FixedFFI<n>`) carried on Core types and read off `gdType`. Emit one
   unboxed worker per layout class actually used, with the boxed `KValue` worker (`kw_g`) as
   the always-correct reference and the existing tag-checked **unbox-or-escape**
   (`kunbox_i64`/`kunbox_dbl` → `*ovf`) as the soundness floor. This is what unboxes
   `Double`, wide FFI ints, and the polymorphic-at-Int hot paths that tagging alone cannot.
   **Hard dependency now named:** Stages 2a–2c are blocked on the CPS-DESIGN §3.3
   suspendability analysis (today `suspendingNames` is a flat syntactic set that does *not*
   see transitive suspension — `C.hs:2656–2658`). §3.3 is reclassified as a prerequisite
   stage, **Stage 1.5** (§7), not gate prose.

**Why both and not one.** Immediate-int tagging is the only scheme that lets an unboxed
scalar survive a CPS park *today* (it fits the `KValue*` slot, so it sits in the `KEnv`
unchanged). Tagging is *structurally incapable* of unboxing `Double` (a binary64 has no
spare bits) or full-width FFI int64, and does nothing for record/ctor field indirection.
Worker/wrapper specialization covers those — but it is more invasive, its unboxed values
*cannot* cross a park, and it only beats the boxed path when producer and consumer are both
unboxed and *fused* (no `boxScalar` round-trip between them, §8). They share one artifact —
the static "this slot is a scalar, not a pointer" map — which is also what Perceus and an
LLVM precise GC require.

**Explicitly rejected** (see §10 for full reasoning): NaN-boxing, full Rust-style
monomorphization, and changing the shared 40-byte `KValue` layout.

---

## 2. Constraints this must satisfy (and how the choice meets each)

| Constraint | Consequence for the design |
|---|---|
| **Effect-typed trait polymorphism, possibly unbounded/dependent instantiation** | No whole-program monomorphization. The uniform boxed `KValue` stays the single calling convention for all polymorphic code (compile once over pointers). Unboxing is a *per-monomorphic-instantiation, per-call-site* backend decision. A polymorphic position stays boxed *by construction* — a type variable presents as a non-scalar head in `scalarHeadKindV` and falls through to `PBoxed`, the safe default. |
| **Boxed `KValue` shared with the interpreter** | Unboxing is a **native-backend overlay only** for *codegen*. The 40-byte box layout (`kappart.h`, K_CTOR/K_REC/K_CLO/K_NATIVE union) never changes, so the interpreter's boxed model is unaffected. Immediate tagging reinterprets the native `KValue*` *word* but the runtime's deref discipline must be made tag-safe at all 299+ sites (§5.1). |
| **CPS do-kernel + values-across-suspension (`KEnv`)** | Tagged immediates fit the `KValue*` `KEnv` slot → they cross a park natively (Stage 1's biggest *structural* win, though second-order in bytes against the 832 B/fork frame, §8). Worker/wrapper unboxed scalars live in C locals (`gsScalars`/`gsParamLvals`), are *lost across a park* (CPS-DESIGN R5), so they stay gated to provably suspension-free regions; at a real safepoint they re-box into the `KEnv`. |
| **Future Perceus precise RC + LLVM** | The layout kind / low-bit tag is exactly the per-slot ptr-vs-scalar map RC needs: `dup`/`drop` adjust only boxed pointers (LSB 0), skip immediates (LSB 1) and scalar-typed slots. **Stage 1 reserves the full low 3 bits** (not just 1, §5.4) for immediate KINDS; the Perceus RC count + borrow/thread-shared discriminator live in the heap-object header, NOT the tag (§5.4 correction / TAGGING-RESEARCH / PERCEUS-RC-DESIGN §2). |
| **`emitScalarLoop` precedent** | Stage 2 is the generalization of it: replace the syntactic prim-name/shape gate with the type-directed `scalarHeadKindV`-over-`gdType` decision the backend *already computes*; reuse `kunbox_i64`/`kunbox_dbl`/`*ovf` as the escape net. The new eligibility must *independently* re-prove suspension-freedom via §3.3, because the prim-name allowlist previously guaranteed that implicitly (§7, Stage 2a). |
| **Portable `Int = int64 + GMP`** | The overflow-escape (`__builtin_*_overflow` → `K_BIGINT`/GMP) is preserved in both stages. Stage 1's immediate is a 63-bit int with an overflow check to the existing boxed bignum path; Stage 2's int64 worker has the identical escape. This is OCaml/Zarith's exact shape — *with the added obligation* that Int equality/match normalizes across the inline/bignum boundary (§5.3). |

---

## 3. The recommendation, weighed

### (a) Immediate-int tagging — the cheap near-term lever (with the now-explicit caveats)

`kgc_alloc` is `GC_MALLOC` (`kappart.c:46`); on 64-bit targets it returns ≥8-byte-aligned
pointers, so the low 3 bits of any real `KValue*` are 0. Steal them: low bit `1` ⇒ immediate
(payload `(i<<1)|1`, a 63-bit signed Int); low bit `0` ⇒ ordinary `KValue*`. `Bool`/`Char`/
`Unit`/nullary constructors (`Nil`/`None`) also become immediates in the remaining tag space.
This is the OCaml/V8-Smi model, **not** GHC's pointer tagging (no info-tables — that is the
whole point of the uniform box).

Why this is the right *first* move:

- **It closes the allocation half of the measured gap with zero analysis.** `kp_addInt` on
  two tagged words is `a + b - 1` plus an overflow check; no `kint()` allocation, no
  `[-16,256]` cache dependence. Uniform — the polymorphic-over-Int case is served *without
  specialization*, which is exactly what Kappa's dependent-ish polymorphism needs.
- **It is the only scheme that solves cross-park liveness today.** The `KEnv` slot stays one
  word; an unboxed loop counter rides it across a fork/await park as a tagged immediate and
  is recovered by an untag on resume. Strictly better than `emitScalarLoop`, which must wall
  scalars off from suspension and flush to boxed refs on escape. Directly answers
  CPS-DESIGN R5 for the common Int case.
- **It composes with both GC eras.** Boehm ignores odd words as non-pointers — *given the
  interior-pointer config is locked down* (Stage 0). For Perceus the same low bits are the
  "no refcount" discriminator.

Costs, accepted and now made load-bearing prerequisites rather than footnotes:

- **Range shrinks to 63-bit.** Values in `[2^62, 2^63)` spuriously promote to bignum. This
  is not merely a perf cost — it is an *observable representation divergence* unless every
  Int equality/match path normalizes across inline/bignum (`klit_eq` short-circuits on tag
  inequality, `kappart.c:807`). Fixed by §5.3.
- **Two encodings for one value.** The interpreter-shared `the_true`/`the_false`/`the_unit`/
  `kint_cache` boxed singletons (`kappart.c:247,285,99`) collide with the new immediates.
  Pointer-identity shortcuts (`kvalue_rep_eq` `a==b`, `kforce`) break. Fixed by
  canonicalization, §5.2.
- **`Double` and full-width FFI int64 cannot be immediates** and stay boxed (Stage 2's job).
- **Every deref gains a tag-test branch** — pure overhead on boxed-heavy ctor/record/closure
  code, which dominates real programs. This is a *potential net regression* on realistic
  mixed workloads even as it wins the Int microbench. Gated by a Stage 0 ctor/match
  microbench with an explicit go/no-go threshold (§7, §8).
- **The `KValue*` reinterpretation is a 299-site audit**, not a "thread the convention
  through." Every load that derefs must tag-test first via disciplined `kis_imm`/`kderef`
  accessors plus a debug-build assert (OCaml's `Is_long`/`Is_block` discipline) covering
  `rt.c` and `kappart.c`, not just codegen (§5.1).

### (b) Type-directed unboxing (worker/wrapper per representation class) — the principled scheme

This is the generalization of the shipped `scalarPlan` engine. The backend *already* reads a
global's full elaborated monomorphic type off `gdType` (the `VPi` telescope), classifies each
domain head via `scalarHeadKindV` (`Int`/`Nat`/`Integer` → `KInt64`, `Float`/`Double` →
`KDouble`, anything else incl. type variables → boxed), and emits `kwi_`/`kwd_` workers beside
the boxed `kw_g`, with `kunbox_i64`/`kunbox_dbl` unboxing saturated args and escaping to the
boxed worker on wrong-tag or overflow. The recommendation is to (1) promote `ScalarKind` to a
first-class **layout kind** `Boxed | I64 | F64 | FixedFFI<n>`, (2) drive worker generation off
the kind rather than the syntactic prim-name allowlist, and (3) thread that kind onto Core
bindings so it can later seed the Perceus per-frame slot map.

Why per representation class, not per type: it bounds code growth to ~4 layout classes (not
#types → no Rust bloat, tractable on a young codebase), gives full speed on each class, and
stays sound for polymorphism by falling back to boxed wherever the layout cannot be resolved.
It honors the levity-polymorphism hard rule — no binder may have a representation-*polymorphic*
type at a calling-convention site — exactly as the existing eligibility gate does: unknown
layout ⇒ uniform boxed `KValue`. This is the GHC/OxCaml middle path, and Kappa already runs a
working instance of it.

**Two costs the review surfaced that the prose previously buried:**

- **Boundary re-boxing.** `compileScalarCall` (`C.hs:1194–1221`) unboxes each arg
  (`kunbox_i64`/`kunbox_dbl`, line 1209) and **re-boxes the result** via `boxScalar`
  (line 1221 = `kint(r)`/`kdbl(r)`). An *isolated* unboxed call therefore still allocates
  one box — the very allocation we set out to kill. The win exists only for a **fused**
  producer→consumer chain that threads the raw scalar in `cScalarTy` locals without a
  `boxScalar` round-trip. For `Double` (no tagging fallback), every value flowing to a
  polymorphic position, record field, ctor arg, or non-fused boundary gets re-boxed. **The
  fusion precondition is now stated explicitly and the win is bounded to fused
  suspension-free regions** (§8).
- **The `let`/`match`-local re-inference is the real Stage-2 cost, not the worker emission.**
  Top-level params get their layout from `gdType`'s `VPi` telescope today; but `let`/
  `match`-bound locals carry no per-node type in Core, so the plan needs a *new
  backend-side representation re-inference pass over untyped Core* (`scalarKindOf` does this
  in miniature). Making that pass *sound* — err-to-boxed on every `CLet`/`CMatch`/`CProjAt`
  ambiguity under dependent/effect types — is easily larger than all the worker codegen
  combined. It is broken out as its own reviewed sub-stage (§7, Stage 2a-pre).

### Which path closes the gap?

- **Int arithmetic:** allocation closed by **both**; tagging closes it uniformly and across
  parks, the I64 worker closes the residual *and* the >63-bit case inside fused
  suspension-free monomorphic regions. Residual per-op tag arithmetic remains (§8).
- **`Double` arithmetic:** closed **only** by the F64 worker, **only in fused regions**
  (tagging cannot help; boundaries re-box).
- **Record/ctor field indirection and per-field box allocation:** closed by **neither in
  scope here** — needs flattened/unboxed fields inside `K_CTOR`, which means changing the
  shared `KValue` layout; explicitly deferred (§10). This is *most of real allocation
  volume* and stays Boehm-bound until precise RC.

---

## 4. Polymorphism: specialization vs uniform-boxed fallback at the boundary

One rule: **the uniform boxed `KValue` is the calling convention for every polymorphic body;
unboxing is a representation refinement that only fires where the type is statically
monomorphic and the layout resolves.**

- A trait/effect-polymorphic function compiles **once** over boxed `KValue*`. A type variable
  is a non-scalar head in `scalarHeadKindV` → `PBoxed` → boxed slot. No dictionary, no
  monomorphization, no levity annotation in surface kinds (representation stays a
  *backend-derived* property of monomorphic types; do **not** reify `RuntimeRep` into Kappa's
  surface kinds — it interacts badly with the dependent/trait/effect-row machinery).
- A polymorphic function *instantiated at Int* gets unboxing two ways: (1) immediate tagging
  applies **uniformly** — an Int argument is already a tagged word in the boxed `KValue*`
  slot, so the polymorphic body needs no specialization at all for the Int case (the
  immediate trick's signature advantage; verified sound by the review); (2) where a
  specialized monomorphic copy exists and both producer and consumer are unboxed *and fused*,
  the I64/F64 worker carries the raw scalar.
- **The boxed wrapper `kw_g` is MANDATORY at every mixed-representation call boundary**
  (boxed polymorphic ⇄ unboxed worker). The required safety net is the wrong-tag escape in
  `kunbox_i64`/`kunbox_dbl` (`kappart.h`): a call site that picks `kwi_` for an arg whose
  *static* type is Int but whose *runtime* value is `K_BIGINT` (overflowed earlier) is caught
  — `kunbox_i64` sees the non-`K_INT` tag and escapes to the boxed worker. This is already
  shipped and verified sound; it is stated here as an **invariant**, not an optimization that
  relies on "both ends unboxed."
- At any boundary where the layout is unknown — opaque higher-order argument, separately-
  compiled polymorphic export, dependent/trait-dispatched type not yet resolved — **box and
  fall back.** Always correct, just slow. This is the existing default and is sound by
  construction.

No full value-witness-table scheme: Perceus handles value lifecycle and the boxed fallback
already covers unknown-layout copy/move, so a Swift-style VWT is overkill.

---

## 5. Correctness: the invariants Stage 1 must establish

The correctness review's dominant finding: Stage 1 is *not* a localized overlay, and three
distinct divergences hide in the "just reinterpret the word" framing. Each gets a concrete
mechanism below. The `kunbox → *ovf → boxed` escape net is the soundness floor for
*wrong-tag and overflow at the unbox site* — it does **not** cover any of §5.1–§5.4, which is
why each needs its own discipline.

### 5.1 The 299-site deref audit (blocking)

Under low-bit tagging, every site that reads `v->tag` or `v->as.*` and can receive a value we
make immediate must `kis_imm`-test first and only `kderef` a confirmed pointer. The codegen
side is genuinely near-zero — codegen already routes through accessors (`kas_bool`,
`kctor_tagid`, `kint`, `kp_addInt`), so the fear of "thread type info to every codegen site"
does *not* apply to tagging. The runtime is where it bites:

- **`runtime/kappart.c`: 299 `->tag`/`->as.*` sites.** Concrete must-convert sites the
  reviews named: `kctor_tagid` (`kappart.c:710`, the **primary** pattern-match dispatch —
  must return the tag of an immediate nullary ctor *without* deref, else garbage tagid →
  wrong arm → silent divergence); `klit_eq` (807); `kvalue_rep_eq` (1042, used by
  `atomicCompareExchange`); `kas_int`/`kas_dbl`/`kas_u64`/`kas_bool`/`kas_fgn` (828–866);
  **every** `kp_*` arithmetic/compare prim (1443+, each tests `x->tag==K_INT` then
  `x->as.i`).
- **`runtime/rt.c`: 2 sites**, including the scheduler `switch(cur->tag)` and
  `kas_int(kctor_arg(cur,0))`.
- **`runtime/atomic.c`: 6 sites.**

Mechanism: introduce `kis_imm(v)` / `kderef(v)` (and `kimm_payload(v)`) accessors in
`kappart.h`; route all 299+2+6 sites through them; add a **debug-build assert in `kderef`
that the LSB is 0**, so any raw deref that bypasses the tag-test trips in CI. The Stage 0
assert must cover `rt.c` and `kappart.c`, not just worker codegen. Realistic Stage 1 runtime
diff: **400–800 lines + a full deref audit.** Budget it as such.

### 5.2 Canonical value encoding — exactly one representation per value (blocking)

`kbool` returns boxed `the_true`/`the_false` (`kappart.c:286`); `kunit` returns boxed
`the_unit` (249); `kint_cache` serves `[-16,256]` as boxed `K_INT` singletons (99). Stage 1
makes `Bool`/`Unit`/`Nil`/`None`/small-`Int` *immediates*. Two encodings for one value breaks
every pointer-identity shortcut (`a==b` in `kvalue_rep_eq:1043`, `kforce`, ref aliasing) and
every site that *assumes* the boxed encoding (FFI returning `kbool`, the interpreter-shared
`kint_cache`).

**Fix (chosen):** make the immediate encoding **canonical** — rewrite `kbool`/`kunit`/`kint`
and retire `kint_cache`/`the_*` as value carriers so these values are *always* immediates with
no surviving boxed singleton. (`kint_cache` was a per-step allocation dodge; immediates make it
obsolete for the in-range case — net simplification.) Audit every `a==b` identity shortcut:
after canonicalization, immediate equality *is* word equality, which is correct and faster;
the hazard is only during a partial migration, which canonicalization eliminates. The boxed
`K_INT`/`K_BIGINT`/`K_CTOR` carriers remain for out-of-range Ints, FFI full-width values, and
n-ary ctors. **Acceptance:** no code path may produce a boxed `K_UNIT`/`True`/`False`/in-range
`K_INT` after Stage 1; a debug assert in `alloc_val` (or the constructors) catches regressions.

### 5.3 Int equality/match normalizes across inline/bignum (blocking)

`klit_eq` (`kappart.c:807`) returns 0 on `a->tag != b->tag` *before* comparing values. A
native value in `[2^62, 2^63)` is an immediate that overflows to `K_BIGINT`, while the
interpreter's 64-bit boxed `K_INT` represents the same number inline → different tags → any
literal-match (`CPLit`) or eq prim routed through `klit_eq`'s shortcut returns **not-equal**
for equal numbers. `kint_cmp` already normalizes across the boundary (and the `kp_eqInt`
family routes through it, `kappart.c:1482`); `klit_eq` does **not**.

**Fix:** route Int literal-match and Int equality through a normalizing comparison
(`kint_cmp`-style: compare *numeric value*, not tag), never through `klit_eq`'s tag shortcut,
for the Int/Integer case. `klit_eq`'s tag shortcut is fine for `K_STR`/`K_BYTES`/`K_CHR`/
`K_BYTE` (no inline/bignum duality) — scope the change to the Int arms. **Conformance:** add a
test that an `Int` literal in `[2^62, 2^63)` is matched against, and `==`-compared with, an
equal `Int` produced via the boxed/bignum path; assert native == interpreter.

### 5.4 Reserve the full low 3 bits; lock the GC/alignment contract (blocking, Stage 0)

The whole scheme rests on `GC_MALLOC` returning ≥8-byte-aligned pointers *and* Boehm not
scanning unaligned/interior pointers. Neither is currently asserted in-tree: `GC_INIT()` is
called bare at `kappart.c:40` with **no** `GC_set_all_interior_pointers(0)`, and there is no
`_Static_assert` on alignment. With interior pointers ON (Boehm's historical default on some
builds), a tagged immediate `(i<<1)|1` whose bit pattern lands inside a live object's address
range becomes a **false interior root** (leak); the scheme also assumes aligned-only scanning.

**Fix (Stage 0 code, not documentation):**
- Call `GC_set_all_interior_pointers(0)` **before** `GC_INIT()` and add a runtime assert that
  the config took.
- Add `_Static_assert(alignof(max_align_t) >= 8, ...)` and a runtime check that `kgc_alloc`
  and `gmp_gc_alloc` (`kappart.c:21,46`, both `GC_MALLOC`) return 8-aligned pointers (sample
  a few allocations at init, assert LSB-3 == 0).
- **Reserve all low 3 bits** for immediate KINDS, documenting the tag-space budget so a future
  immediate kind is not boxed in by a 1-bit convention baked into ~299 sites. Budget (as
  implemented): `b000` pointer, `b001` immediate-Int, `b010` immediate nullary-ctor (tag id in
  the payload), `b011` packed 1/2-field ctor; `b1xx` reserved for further immediate kinds (e.g.
  immediate Char). **CORRECTION (supersedes the earlier "reserved for Perceus" framing, per
  [TAGGING-RESEARCH](TAGGING-RESEARCH.md):29-41): the Perceus RC count + borrow/thread-shared
  discriminator do NOT live in these tag bits.** An immediate is value-copied and never
  reference-counted, and a tag-bit RC discriminator would *alias* — the same heap object reached
  via a borrowed vs an owned reference would carry different tags. The RC count + discriminator
  live in the heap-object header (the free 4-byte hole at `KValue` offset 4); see
  [PERCEUS-RC-DESIGN §2/§9](PERCEUS-RC-DESIGN.md).

### 5.5 Floating-point semantics for the F64 worker (Stage 2b)

The interpreter's `Double` equality is **raw-bit** (`kp_eqDouble`, `kappart.c:1493–1496`,
memcpy-to-uint64 then compare), distinct from `kp_floatEq` (`==`, line 1491). Lowering
`eqDouble`/`leDouble` to C `==`/`<=` on an unboxed F64 worker would make `NaN != NaN` and
`+0.0 == -0.0`, diverging. The existing denylist already keeps `eqDouble`/`leDouble` *out* of
the unboxed allowlist (verified: `arithPrim`/`cmpPrim` list `ltDouble`/`floatEq` but **not**
`eqDouble`). **This denylist is a load-bearing invariant and must never be relaxed** — add a
regression guard.

The previously-unflagged hazard: **FP contraction.** `intToDouble`/`negDouble`/`div`/`mul`/
`add` on the unboxed F64 worker must be bit-identical to the boxed `kp_*` prims. If the native
build enables `-ffast-math` or `-ffp-contract=fast`, the worker may contract `a*b+c` into a
single-rounded FMA while boxed `kp_mulDouble`+`kp_addDouble` does two rounded ops → different
`Double` → native != interpreter. **Fix:** assert the native build does **not** enable
`-ffast-math` / `-ffp-contract=fast` on unboxed Double workers (compile the worker TU with
`-ffp-contract=off` and `-fno-fast-math`, and add a build-time guard). Conformance: NaN/
signed-zero corners green.

### 5.6 FixedFFI<n> unbox primitive and carrier semantics (Stage 2c)

`kas_u64` (`kappart.c:855`) reads the full unsigned 64-bit magnitude including the `≥2^63`
range that `kas_int` rejects, via `mpz_export` for bignums; such a `U64` lives as a
`K_BIGINT` box. The FixedFFI path **must not reuse `kunbox_i64`** (`kappart.h`), which accepts
only `K_INT` and escapes on `K_BIGINT` — that would wrongly reject every `U64 ≥ 2^63` to the
slow path or mis-handle it.

**Fix:** define a carrier-specific unbox (`kunbox_u64<n>` etc.) replicating `kas_u64`'s
`mpz_export` semantics, with a re-box rule that produces the **same encoding the interpreter
and downstream Int ops expect** for that numeric value (`K_BIGINT` for top-bit-set, in-range
immediate/`K_INT` otherwise). Conformance: FFI round-trip at `0xFFFFFFFFFFFFFFFF`.

---

## 6. Crossing a CPS suspension point and telling boxed from unboxed under RC

Two mechanisms, matching the two stages.

**Tagged immediates cross a park natively.** The `KEnv` cons cell stays
`{ KValue *val; KEnv *next; }`; the `val` word may now hold a tagged immediate. A small Int /
Bool / Char live across `do_await`/`fork`/`OP_SLEEP` sits in the `KEnv` chain (kept live by
the `rt->all` strong set) and is recovered on resume by a tag-test. Boehm skips it (odd word,
*given* the §5.4 config). For Perceus the low bits are the "no RC" discriminator. `kapp`/
`deliver` feed it as a `KValue*`-shaped word unchanged — nothing derefs without a tag-test
(§5.1). **This is the cross-suspension story for the common scalar case and requires no
frame-layout change.** The review confirmed this as the design's strongest claim. (Caveat:
in *bytes* it is second-order — it saves the box of one carried scalar against the 832 B/fork
frame, §8.)

**Worker/wrapper unboxed scalars (Double, int64, FixedFFI) do *not* cross a park.** They live
in C locals (`gsParamLvals`/`gsScalars`), absent from `KEnv` and `f->k`, so CPS-DESIGN R5
declares them lost across a park. The escape net (`kunbox → *ovf → boxed`) guards *wrong-tag
and overflow at the unbox site* — it does **not** guard *liveness across a suspension*. The
*only* thing protecting cross-park correctness for these values is the suspendability witness,
and the review correctly flagged that **a witness that under-approximates suspension silently
loses a live scalar with no crash.** Therefore:

- **Hardened gate (mandatory):** unbox in C locals only in a *provably* suspension-free
  region. The §3.3 analysis **must err toward may-suspend**: every layout-unresolved,
  effect-polymorphic, or opaque-higher-order call is classified **may-suspend**, and a binder
  whose live range crosses any may-suspend call is *not* eligible for a C-local unboxed slot.
  Today `suspendingNames` is a flat syntactic set that does *not* see transitive suspension
  (`C.hs:2656–2658`: "a block that suspends only transitively stays on the legacy bridge until
  the §3.3 analysis lands"). **This is why §3.3 is a named prerequisite — Stage 1.5 — and
  Stages 2a–2c are *not* independently shippable before it lands** (§7).
- At a real safepoint a non-immediate scalar **re-boxes into the `KEnv`** before the park and
  re-unboxes on resume (the shipped `gsI64Escape` "flush snapshots; goto boxed" pattern). The
  escape decision for a cross-suspension value must be made **before** the frame is built
  (R5 a5: there is no single C function to bail out of across a park).
- **Conformance (mandatory):** a test carrying an unboxed `Double` counter across an `await`
  *through a polymorphic/effect indirection*, asserting native == interpreter — i.e. exactly
  the case where a naive gate would under-approximate.

The longer-term upgrade — a typed unboxed-scalar spill slot in the continuation frame, so a
`Double` counter survives a park without boxing — is deferred to the LLVM
`coro.id.retcon.once` flat-frame seam, where CoroSplit computes the cross-suspend live set;
that frame must then carry the boxed-vs-scalar classification, which is the same slot-kind map
below (Stage 3).

**How a future Perceus tells boxed from unboxed:** per-slot static discrimination is mandatory
and is the artifact both stages produce.
- For immediates: the **low bits** are the discriminator — `dup`/`drop` adjust only pointer
  words (LSB 0), skip immediates. Free, exact, no metadata table.
- For typed unboxed scalars: the **layout kind** on the slot (the `ParamKind`/layout-class
  `scalarPlan` computes) tells RC the slot is a raw scalar — no refcount, no trace. Propagated
  onto **every continuation/do-scope frame's slot-kind map**, not just leaf workers, and
  joined with the suspendability witness so the stay-unboxed-vs-box-into-`KEnv` decision is
  sound at each bind.
- **Under Boehm today** the *only* safe place for a non-immediate unboxed cross-park value is
  one Boehm need not read as a pointer (a C local, an atomic-allocated side array) — never a
  GC-scanned `KEnv`/`Cont` slot, or it becomes a conservative false root. This is why Stage 2
  stays C-local-and-re-box until precise RC arrives. Immediates are exempt (odd words are safe
  in scanned slots, §5.4).
- Restrict unboxing to **true scalars** (Int/Double/Byte/Char) — never a `K_REF`/`K_FGN`/
  `K_CTOR` holding releasable state a `defer` needs (R5 b4: finalizer ordering must hold the
  last reference).
- A scalar **captured across `fork`** crosses a thread boundary; classify it distinctly
  (thread-shared) so that if it ever needs boxing it gets atomic RC — matching Perceus's
  borrow/thread-shared split — the thread-shared bit is a heap-header field, not a tag code (§5.4 correction / PERCEUS-RC-DESIGN §2/§5).

---

## 7. Staged plan — each stage measurable against `runtime/bench`

The bench (`rt_bench.c`: the `addInt` loop at `~13 ns + 64 B` boxed vs `~0.23 ns + 0 B` raw)
is the standing yardstick. **Invariant across all stages: native == interpreter**, verified by
the conformance suite; the boxed path is always the reference result. Note that the `50x`
headline is a *pure-Int allocation microloop* — the most favorable possible case for tagging.
Stage 0 adds the benches that detect where it *isn't* representative.

### Stage 0 — Instrumentation, GC contract & guardrails (blocking prereq)
- **GC/alignment contract (code, not docs, §5.4):** `GC_set_all_interior_pointers(0)` before
  `GC_INIT()`; `_Static_assert` + runtime alignment check on `kgc_alloc`/`gmp_gc_alloc`;
  reserve the low 3 tag bits and document the budget.
- **Accessor layer:** `kis_imm`/`kderef`/`kimm_payload` in `kappart.h`; debug-build assert in
  `kderef` (LSB 0) covering `rt.c` + `kappart.c`.
- **Benches (all three must land and record baselines BEFORE Stage 1 ships):** (1) `Double`
  add; (2) **ctor-build** and (3) a **match/projection-heavy** microbench (the tag-test tax
  detectors); (4) "value live across a park" (counter through `await`).
- *Measurable:* baselines recorded. *Ships:* no behavior change.

### Stage 1 — Immediate-int tagging (the cheap lever)
- Canonicalize encoding (§5.2): rewrite `kbool`/`kunit`/`kint`, retire `kint_cache`/`the_*` as
  carriers; `(i<<1)|1` for in-range Int; immediate `Bool`/`Char`/`Unit`/`Nil`/`None`.
- Tag-dispatch arithmetic: `kp_addInt`/`subInt`/`mulInt`/compares become `a+b-1`-style with
  `__builtin_*_overflow` → `K_BIGINT` escape; `kctor_tagid` returns the immediate tag without
  deref.
- Route **all 299+2+6 deref sites** through `kis_imm`/`kderef` (§5.1).
- Normalize Int literal-match/eq across inline/bignum (§5.3); never via `klit_eq`'s tag
  shortcut for Int.
- Thread tagged words through `rt.c` (`kapp`/`deliver`/`kvar`/`kpush`, park/resume); `KEnv`
  layout unchanged.
- **GO/NO-GO GATE:** the ctor-build and match/projection benches must show **no worse than
  ~5–10% regression** on boxed-heavy code. If they regress beyond that, the uniform
  tag-test-on-every-deref may be net-negative for realistic mixed workloads and Stage 1 must
  be reworked (e.g. restrict immediates to Int only, dropping ctor immediates) before merge.
- *Independently shippable:* yes (interpreter `KValue` layout untouched; native codegen
  near-zero delta). *Measurable:* `addInt` bench drops to **0 B/op** and **~1–3 ns/op**
  (residual tag arithmetic, §8); "counter across a park" shows zero allocation. *Invariant:*
  conformance green, including the §5.3 `[2^62,2^63)` test.

### Stage 1.5 — CPS-DESIGN §3.3 suspendability analysis (named prerequisite for Stage 2) — **LANDED**
Today `suspendingNames` is syntactic and does not see transitive suspension (`C.hs:2656–2658`).
Build the transitive, err-toward-may-suspend reachability witness, threaded to the backend at
**per-binding granularity** (not just per-function), classifying every layout-unresolved /
effect-polymorphic / opaque-higher-order call as may-suspend. **Stages 2a–2c are blocked on
this** — they are *not* independently shippable before it lands, because a C-local unboxed
scalar is lost across an unpredicted park (R5).
- *Measurable:* the conformance test of §6 (Double counter across `await` through a
  polymorphic indirection) passes; previously-bridged transitive-suspension blocks are now
  correctly classified.
- **Landed:** the existing transitive closure `suspenderGlobals`/`gsSuspenders` (`C.hs`)
  — already computed for the §3.3 do-bind CPS analysis — is now the SOUNDNESS GATE on the
  unboxed scalar worker.  `scalarPlan` (`C.hs`) refuses a worker for any binding `g` that
  (a) is itself in the transitive suspender closure (`g ∈ gsSuspenders`) OR (b) has a body that
  `scalarBodyMaySuspend` (a new per-body walk) classifies may-suspend — a spine-head suspending
  prim / `gsSuspenders` global, or an opaque local-headed (higher-order) call — recursing into
  `if`/`match`/`let`/ctor/arg positions and treating any `CDo` as may-suspend.  Both the
  worker-emission site and the call-site dispatch call the same `scalarPlan`, so the decision is
  consistent.  Today the arithmetic-only body grammar already makes a scalar body suspension-free
  *implicitly* (no admitted form is an IO/suspending op; a non-scalar `UIO a` result is already
  rejected by `scalarHeadKindV`), so the gate refuses nothing the grammar wouldn't — but it makes
  that property EXPLICIT and INDEPENDENT so it survives the Stage-2a-pre widening to `let`/`match`
  (which CAN carry a suspending sub-term).  The gate's transitivity is verified load-bearing by a
  controlled experiment: marking a leaf arith prim (`addDouble`) as suspending pushes a pure
  `Double` loop into `gsSuspenders` and the worker is correctly REFUSED (falls to the boxed
  `kw_g`, program still correct) — a naive flat-`suspendingNames` *spine-head* check would NOT
  catch it (the loop's spine head is the `if`/self-call, not `addDouble`).  The §6 across-`await`
  Double-accumulator conformance test (`test/native/cases/await-dbl-acc.kp`) is green native ==
  interpreter.

### Stage 2a-pre — Local representation re-inference over untyped Core (own soundness review)
Separate, reviewed sub-stage *before* worker emission. `let`/`match`/`CProjAt` binders carry
no per-node type in Core; generalize `scalarKindOf` to a sound backend-side re-inference that
**errs to `Boxed` on every ambiguity** under dependent/effect types. This is the actual
Stage-2 risk and cost — do **not** fold it into "additive worker." Its own conformance review.

### Stage 2a — Type-directed I64 worker (generalize `emitScalarLoop`)
Promote `ScalarKind` → layout kind; replace the `scalarLoopPlan` syntactic gate with the
`scalarHeadKindV`-over-`gdType` decision (+ Stage 2a-pre re-inference for locals). **Re-prove
suspension-freedom per binder via the §3.3 witness** — widening eligibility from the prim-name
allowlist removes the *implicit* suspension-freedom the allowlist provided, so the new gate
must establish it independently. Keep `kunbox_i64`/`*ovf` escape; `kw_g` mandatory at
boundaries (§4). Emit `kwi_` workers for monomorphic suspension-free Int functions/loops beyond
the immediate range.
- *Shippable:* yes, *given* Stage 1.5. Additive worker beside boxed `kw_g`. *Measurable:* an
  **unbox-to-unbox-fused** int64 loop runs at near-raw-add speed past 63 bits with **0 B/op**;
  an *isolated* call still allocates one box (§8). *Invariant:* overflow → identical GMP result
  as interpreter.

### Stage 2b — F64 worker (`Double`) — **LANDED**
Add `kwd_` worker generation off the `F64` layout class. Keep `eqDouble`/`leDouble` out of the
unboxed allowlist; pin FP semantics (`-ffp-contract=off`, no `-ffast-math`, §5.5).
- *Shippable/Measurable:* **fused** `Double` add drops to 0 B/op; *non-fused/boundary* Doubles
  re-box and do not improve (state this — it bounds the win). Conformance (NaN/signed-zero,
  FMA) green.
- **Landed:** `kwd_` Double-worker generation is ON via the existing `F64` (`KDouble`) layout
  class — `scalarHeadKindV` maps `Float`/`Double` → `KDouble`, `arithPrim` admits
  `add/sub/mul/div/negDouble` + `intToDouble`, `scalarArith` emits native `double` +,-,*,/ in C
  locals, and `scalarWorkerName` emits `kwd_`.  `eqDouble`/`leDouble` stay OUT of the allowlist
  (`cmpPrim` admits only `ltDouble`/`floatEq`, whose C operator matches the prim exactly;
  `eqDouble` is §6.1.3 raw-bit equality ≠ C `==`).  FP semantics are PINNED in the build driver
  (`src/Kappa/Backend/Driver.hs`): `-ffp-contract=off` (no implicit FMA fusion — a `mul`-then-`add`
  rounds twice, matching boxed `kp_mulDouble`+`kp_addDouble`) AND `-fno-fast-math` (defensively
  pins that no present/future flag relaxes IEEE).  A fused `Double` accumulator loop is a raw
  `double` `while(1)` with **0 B/op** in the hot loop (verified: the only boxes are the one-time
  arg/result boxes at the call site; the native suite's R2.2 gate measures
  `scalar_doubleloop ≈17 KB total` for 2 000 000 iterations, i.e. O(1) not O(N)).  FP bit-identity
  is verified by `test/native/cases/fpbitident.kp` (FMA/mixed-op/accumulator/signed-zero probes,
  native == interpreter) and the parity test `tests/native/llvm/double-fma-parity.kp`
  (interp == C == LLVM).  *Known orthogonal limitation:* the native `kp_showDouble` printer
  diverges from the interpreter's `show` on the last decimal digit for some large-magnitude
  Doubles (same IEEE bits, different shortest-decimal) — a pre-existing formatting bug on the
  *boxed* path (LLVM, which has no unboxing, diverges too), unrelated to the worker; tracked
  separately.

### Stage 2c — FixedFFI worker
`FixedFFI<n>` unboxed-but-not-tagged path at the `external` boundary; carrier-specific unbox
(`kas_u64`/`mpz_export` semantics, **not** `kunbox_i64`, §5.6); re-box to the interpreter-
consistent encoding on out-of-carrier result.
- *Shippable/Measurable:* FFI int64 round-trip shows no box for in-carrier values; round-trip
  at `0xFFFFFFFFFFFFFFFF` green.

### Stage 3 — Perceus-ready slot-kind map (lands with RC/LLVM, gated behind precise GC)
Thread the layout kind onto every continuation/do-scope frame's static slot map (immediates by
low bits; typed scalars by kind). Consumed by Perceus `dup`/`drop` and LLVM CoroSplit; enables
the *later* typed scalar-spill slot so a `Double` counter survives a park unboxed. **Deliberately
after** the Boehm→Perceus migration — under conservative Boehm a non-immediate unboxed value in a
scanned frame slot is a false-root hazard (§6).
- *Measurable:* RC microbench shows `dup`/`drop` no-op on scalar slots.

**Sequencing rationale.** Stage 0 is a hard blocker (GC contract + benches). Stage 1 lands the
dominant Int allocation win plus the cross-park property — but only after the deref audit,
canonicalization, normalization, and the boxed-heavy go/no-go gate. Stage 1.5 (§3.3) is a named
prerequisite for everything in Stage 2; Stages 2a–2c are *not* independently shippable before it.
Stage 3 is gated behind precise RC by GC soundness, not preference.

---

## 8. Expected bench-measurable wins per stage (honest, with the allocation/arithmetic split)

The microbench bundles allocation and arithmetic; the reviews require separating them.

| Stage | What it measurably wins | What it does NOT win |
|---|---|---|
| **0** | Baselines for Double-add, ctor-build, match-heavy, across-park. GC contract enforced. | No behavior/perf change. |
| **1 (Int tagging)** | `addInt` loop: **64 B → 0 B/op** (allocation half eliminated); **~13 ns → ~1–3 ns/op**, i.e. **~5–13× of raw** (residual = untag/retag `a+b-1` + 2 LSB tests + overflow check, and loss of the autovectorization raw int64 enjoys). Net captured: **~80–90% of the Int-microbench gap**, *not* 100%. "Counter across a park": **0 B** for the carried scalar. | Does **not** reach raw (per-op tag arithmetic remains). Does **not** help `Double`, FFI int64, or >63-bit Int. **Risks net regression** on ctor/record/closure-heavy code (extra LSB test per deref, zero offsetting win) — held to ≤~5–10% by the go/no-go gate, else reworked. Fork path: **≈0%** (832 B/fork frame is untouched; the across-park scalar saving is real but second-order in bytes). |
| **2a (I64 worker)** | A **fused, suspension-free** monomorphic int64 loop: **0 B/op at near-raw-add speed past 63 bits**. | An **isolated** unboxed call still allocates one box (`boxScalar`, `C.hs:1221`). No win at non-fused boundaries or polymorphic positions. Blocked on Stage 1.5. |
| **2b (F64 worker)** | **Double add inside fused suspension-free regions: 0 B/op.** This is the *only* path for `Double` (tagging cannot help). | Every `Double` flowing to a polymorphic position / record field / ctor arg / non-fused boundary is **re-boxed** and does not improve. The Double win is materially *fusion-bounded* — quantify per workload; do not assume whole-program. Blocked on Stage 1.5. |
| **2c (FixedFFI)** | FFI int64 round-trip: **no box for in-carrier values**. | Out-of-carrier (`≥2^63` where the carrier is signed) re-boxes to `K_BIGINT` as the interpreter expects. |
| **3 (slot-kind map)** | RC microbench: `dup`/`drop` **no-op on scalar slots**; later, typed scalar-spill lets a Double counter cross a park unboxed. | Nothing until precise RC ships. |

**Residual after both stages (explicitly out of scope, stays Boehm-bound until Perceus):**
record/ctor **per-field box indirection** (§10 — this is *most* of real allocation volume),
bignum/FFI-carrier Ints, boundary-crossed Doubles, and the **832 B/op CPS fork frame** plus
416 B/bind CPS bind-tree. **Whole-program speedup will be materially below the 50× microbench
number** and dominated by these deferred costs. Say so to every stakeholder.

**Code-size note (bounded, but measure it):** per eligible global we emit boxed `kw_g` **plus**
scalar/mixed workers (`kwi_`/`kwd_`/`kwm_`). Bounded to ~4 layout classes (not Rust-tier
bloat), but each eligible global can ~2–4× in emitted C. Track emitted-C LOC delta and compile
time per stage; do not assume negligible.

---

## 9. Risks & mitigations

| # | Risk | Severity | Mitigation |
|---|---|---|---|
| R1 | **Missed deref site** among the 299+8 → silent miscompile (wrong match arm via a garbage tagid) or segfault on an odd word. The boxed-fallback floor does **not** catch this (these are fast-path derefs, not worker-escape). | Critical | Mechanical audit routed through `kis_imm`/`kderef`; debug-build assert in `kderef` (LSB 0) covering `rt.c`+`kappart.c` (§5.1); conformance suite + a fuzz pass that forces immediatized ctors through every match. Treat as a 400–800-line change, reviewed line-by-line. |
| R2 | **Dual encoding** (immediate vs boxed singleton) → `a==b` identity fails for equal values; FFI returns boxed where caller tag-tests immediate. | High | Canonicalize: immediates are the *only* encoding for in-range Int / Bool / Unit / Nil / None; retire `kint_cache`/`the_*` as carriers; debug assert that no boxed `K_UNIT`/`True`/`False`/in-range `K_INT` is ever allocated post-Stage-1 (§5.2). |
| R3 | **63-bit promotion divergence**: `[2^62,2^63)` immediate→`K_BIGINT` vs interpreter inline `K_INT`; `klit_eq` tag-shortcut returns not-equal for equal numbers. | High | Route Int literal-match/eq through `kint_cmp`-style numeric normalization, never `klit_eq`'s tag shortcut for Int; conformance test in `[2^62,2^63)` (§5.3). |
| R4 | **Boehm interior-pointer / alignment** unset → false interior roots (leak) / unaligned mis-scan; the whole low-bit scheme is unsound. | High | Stage 0 *code*: `GC_set_all_interior_pointers(0)` before `GC_INIT`; `_Static_assert` + runtime alignment check on `kgc_alloc`/`gmp_gc_alloc`; reserve low 3 bits (§5.4). |
| R5 | **Tag-test tax** net-regresses boxed-heavy real code while the Int microbench improves. | High | Stage 0 ctor-build + match-heavy benches as a **go/no-go gate** (≤~5–10%); if exceeded, restrict immediates to Int-only or rework before merge (§7, §8). |
| R6 | **§3.3 does not exist** — Stage-2 C-local unboxing is unsound across transitive suspension; `suspendingNames` is syntactic (`C.hs:2656–2658`). | High | Reclassify §3.3 as **Stage 1.5**, a named prerequisite blocking 2a–2c; err-toward-may-suspend; per-binding granularity; conformance test of a Double counter across `await` through a polymorphic indirection (§6, §7). |
| R7 | **Boundary re-boxing** cancels the Stage-2 win for isolated/non-fused calls; worst for `Double` (no tagging fallback). | High | State the fusion precondition; bound the win to unbox-to-unbox-fused suspension-free regions; the boxed `kw_g` wrapper is mandatory at every mixed boundary (§4, §8). |
| R8 | **`let`/`match`-local re-inference** is a new untyped-Core analysis — a soundness minefield, larger than the worker codegen. | High | Break out as **Stage 2a-pre** with its own soundness review; err-to-`Boxed` on every ambiguity (§7). |
| R9 | **FP contraction / raw-bit compare** on the F64 worker diverges from the interpreter (`a*b+c` FMA; `NaN`/signed-zero). | Medium | `-ffp-contract=off`, no `-ffast-math` on worker TUs; keep `eqDouble`/`leDouble` out of the unboxed allowlist with a regression guard (§5.5). |
| R10 | **FixedFFI unbox** naively reuses `kunbox_i64` and wrongly escapes every `U64 ≥ 2^63`. | Medium | Carrier-specific unbox replicating `kas_u64`/`mpz_export`; interpreter-consistent re-box; round-trip test at `0xFFFFFFFFFFFFFFFF` (§5.6). |
| R11 | **One-way door** (RESOLVED): the Perceus RC discriminator does NOT live in the tag — it is a heap-header field (TAGGING-RESEARCH / PERCEUS-RC-DESIGN §2), so the low 3 bits being load-bearing for immediate kinds boxes nothing in for Perceus. | Low | Reserve the low 3 bits for immediate kinds; the RC discriminator is a header field, not a tag code (§5.4). |
| R12 | **Worker fan-out** inflates compile time / i-cache. | Low | Bounded to ~4 layout classes; measure emitted-C LOC + compile-time delta per stage (§8). |

---

## 10. Rejected alternatives

- **NaN-boxing.** Hostile to conservative Boehm: a NaN-boxed pointer is invisible to the
  conservative scan (it does not look like a pointer in the payload bits), and a NaN-boxed int
  can alias a real heap address → mis-scan / false retention. It presupposes precise GC, which
  Kappa does not yet have. The low-bit scheme, by contrast, makes immediates *odd* words that
  Boehm cleanly skips (given §5.4). Reconsider only *after* precise RC, and even then only if
  it beats the layout-kind map already required for Perceus.
- **Full Rust-style whole-program monomorphization.** Intractable under Kappa's dependent-ish,
  trait/effect-typed, possibly-unbounded instantiation sets — there is no bounded instantiation
  set to enumerate. Code-bloat on a still-churning codebase. The per-representation-class
  worker scheme gets most of the speed at ~4× (not #types×) emitted code, with boxed fallback
  for everything unresolved.
- **Changing the shared 40-byte `KValue` layout (e.g. heap-unboxing `K_CTOR`/`K_REC` fields).**
  The box is shared with the reference interpreter, which must stay boxed; flattening fields
  would force a layout change across both or risk semantic drift. This is *the* item that would
  attack record/ctor per-field indirection (most of real allocation volume), but it is deferred
  to the precise-RC era where the slot-kind map (§6) makes flattening tractable. Out of scope
  here.
- **Reifying `RuntimeRep`/levity into Kappa's surface kinds (GHC-style).** Interacts badly with
  the dependent/trait/effect-row machinery. Representation stays a *backend-derived* property of
  monomorphic types, as today; the calling-convention rule is "unknown layout ⇒ boxed" (§4).
- **Swift-style value-witness tables.** Overkill: Perceus handles value lifecycle and the boxed
  fallback already covers unknown-layout copy/move (§4).
- **Stealing only 1 tag bit.** Rejected for forward-compat: reserve all low 3 for additional immediate KINDS,
  not boxed in by a convention baked into ~299 sites (the Perceus discriminator is a header
  field, not a tag — TAGGING-RESEARCH)
  (§5.4, R11).

---

## 11. Required-fix ledger (every critique fix, and where it lands)

**Correctness lens**
1. 299-site deref audit, not just `kp_addInt`/`kctor_tagid`; convert all `->tag`/`->as.*` in
   `rt.c`/`kappart.c`/`atomic.c` through `kis_imm`/`kderef`; debug assert covers runtime not
   just codegen → **§5.1, Stage 0/1, R1.**
2. Canonicalize value encoding (one representation per value); rewrite `kbool`/`kunit`/`kint`/
   `kint_cache`/`the_*` → **§5.2, R2.**
3. Prove Int eq/match normalizes across inline/bignum; fix `klit_eq` tag-shortcut; conformance
   in `[2^62,2^63)` → **§5.3, R3.**
4. Harden & demonstrate the §3.3 suspendability witness (err-to-may-suspend; per-binding;
   polymorphic/opaque = may-suspend); Double-across-await-through-indirection test → **§6,
   Stage 1.5, R6.**
5. Pin FP semantics (`-ffp-contract=off`, no `-ffast-math`); keep `eqDouble`/`leDouble`
   denylisted with a guard → **§5.5, R9.**
6. Specify FixedFFI unbox (not `kunbox_i64`; `kas_u64`/`mpz_export` semantics; interpreter-
   consistent re-box); round-trip at `0xFFFFFFFFFFFFFFFF` → **§5.6, R10.**
7. `kw_g` wrapper MANDATORY at every mixed boundary, with wrong-tag escape as the required net
   → **§4, R7.**

**Performance lens**
8. Re-state wins with allocation/arithmetic split; Stage 1 = ~80–90% of the Int gap (0 B,
   ~1–3 ns), not 1×; fork-path ≈0% → **§8.**
9. `GC_set_all_interior_pointers(0)` as Stage-0 *code* + runtime assert → **§5.4, Stage 0, R4.**
10. ctor-build + match/projection benches as a go/no-go GATE for Stage 1 → **§7 Stage 0/1, §8,
    R5.**
11. §3.3 reclassified as a named prerequisite stage (1.5) blocking 2a–2c → **Stage 1.5, R6.**
12. Boundary re-boxing precondition stated; Stage-2 win bounded to fused suspension-free
    regions; Double most exposed → **§3(b), §8, R7.**
13. Residual scoped: ctor-field indirection, bignum/FFI Ints, boundary Doubles, 832 B fork
    frame remain Boehm-bound until Perceus → **§8, §10.**

**Feasibility lens**
14. Alignment guarantee from footnote to Stage-0 blocker (`_Static_assert` + runtime check on
    `kgc_alloc`/`gmp_gc_alloc`) → **§5.4, Stage 0, R4.**
15. Stage-1 runtime diff honestly scoped at 400–800 lines + full deref audit (codegen ≈0) →
    **§5.1, Stage 1, R1.**
16. Land all three Stage-0 microbenches + baselines before Stage 1 → **§7 Stage 0, R5.**
17. `let`/`match`-local re-inference as its own sub-stage (2a-pre) with separate soundness
    review → **§7 Stage 2a-pre, R8.**
18. Confirm §3.3 witness is threaded at per-binding (not per-function) granularity before
    Stage 2a is "additive"; new gate re-proves suspension-freedom the prim-name set provided
    implicitly → **Stage 1.5 + Stage 2a, R6.**
19. Reserve full low 3 tag bits + document budget → **§5.4, R11.**

---

## 12. Key files (all absolute)

**Runtime**
- `/Users/wabbit/ws/kappa-haskell/runtime/kappart.h` — `KValue`/`KEnv` layout; `kunbox_i64`/
  `kunbox_dbl`; **new `kis_imm`/`kderef`/`kimm_payload` accessors + tag-space macros** (Stage 0/1).
- `/Users/wabbit/ws/kappa-haskell/runtime/kappart.c` — **GC contract** at `GC_INIT` (`:40`,
  add `GC_set_all_interior_pointers(0)` + alignment asserts); `gmp_gc_alloc`/`kgc_alloc`
  (`:21,46`); canonicalize `kbool`/`kunit`/`kint`/`kint_cache`/`the_*` (`:99,247,285`);
  tag-safe `kctor_tagid` (`:710`), `klit_eq` (`:807`), `kvalue_rep_eq` (`:1042`), `kas_*`
  (`:828–866`), all `kp_*` prims (`:1443+`); `kp_eqDouble` raw-bit invariant (`:1493`);
  `kas_u64`/`mpz_export` for FixedFFI (`:855`). **The 299-site audit lives here.**
- `/Users/wabbit/ws/kappa-haskell/runtime/rt.c` — scheduler `switch(cur->tag)` + 2 deref
  sites; `kapp`/`deliver`/`kvar`/`kpush`, park/resume (`do_await`, `OP_SLEEP`) carry tagged
  words; `KEnv` unchanged.
- `/Users/wabbit/ws/kappa-haskell/runtime/atomic.c` — 6 deref sites (incl.
  `atomicCompareExchange` via `kvalue_rep_eq`) made tag-safe.

**Compiler**
- `/Users/wabbit/ws/kappa-haskell/src/Kappa/Backend/C.hs` — `ScalarKind`/`ParamKind` → layout
  kind; `scalarPlan`/`typeScalarKinds`/`scalarHeadKindV`; `emitScalarLoop`/`gsScalars`/
  `gsI64Escape`; `compileScalarCall` boundary re-boxing (`:1194–1221`, `boxScalar` `:1221`);
  `unboxScalar`/`unboxWorker`/`boxScalar` (`:704–712,1086`); arith/cmp denylist
  (`arithPrim`/`cmpPrim`) keeping `eqDouble`/`leDouble` boxed; **`suspendingNames` →
  transitive §3.3 witness** (`:2656–2681`); new type-directed gate + Stage-2a-pre local
  re-inference.
- `/Users/wabbit/ws/kappa-haskell/src/Kappa/Core.hs` — layout kind on Core types/bindings
  (Stage 2/3 threading).

**Bench & docs**
- `/Users/wabbit/ws/kappa-haskell/runtime/bench/rt_bench.c` +
  `/Users/wabbit/ws/kappa-haskell/runtime/bench/README.md` — Stage 0 microbenches (Double-add,
  **ctor-build**, **match/projection**, **across-park**); the standing yardstick.
- `/Users/wabbit/ws/kappa-haskell/runtime/docs/CPS-DESIGN.md` — R5 / §3.3 suspendability gate
  (the Stage 1.5 prerequisite); Stage 3 frame slot-kind map and `coro.id.retcon.once` seam.
