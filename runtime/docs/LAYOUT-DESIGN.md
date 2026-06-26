# Value-layout system — packing small ADTs into the tagged word

Status: design of record (in progress). Generalizes the Stage-1 immediate-Int
tagging ([`UNBOXING-DESIGN.md`](UNBOXING-DESIGN.md) §1/§5) into a Rust-style value
layout: small ADTs / individual constructor cases compress into ONE tagged
`KValue*`-sized word instead of a heap `K_CTOR` box. Pointer-tagging foundations
in [`TAGGING-RESEARCH.md`](TAGGING-RESEARCH.md); the layout/niche/specialization
specifics are being grounded by a follow-up research pass (Rust `rustc_abi`
layout + niche optimization, Swift value-witness tables vs specialization).

## The substrate (already in place)

The `KValue*` word carries a 3-bit low tag (GC_MALLOC is 8-aligned, interior
pointers OFF, so a low-tagged odd word is a non-pointer to Boehm):

```
b000  a heap KValue* pointer (a boxed K_CTOR/K_REC/… — kderef needs no mask)
b001  immediate Int   (value<<3)                         [DONE — Stage 1]
b010  immediate ctor  (a NULLARY constructor; tag id in the payload) [DONE — 1b]
b011  packed ctor     ([field-word:41 | tagId:20 | b011]; one immediate field) [DONE — 1d]
b1xx  RESERVED        (niche markers, immediate Char, future kinds)
```

`kis_imm`/`kderef`/`kimm_payload` are the discriminator API; the debug `kderef`
assert pins the "no raw deref of an immediate" invariant across the runtime.

## The key insight: the uniform path is transparent to packing

Kappa compiles every polymorphic body ONCE over boxed `KValue*` (the uniform
calling convention). A packed ADT is *still a `KValue*`-shaped word* — just one
with low bits set. So as long as the constructor accessors `kctor_tagid` /
`kctor_arg` (and `kis_imm`/`kderef`) are immediate-AWARE, **polymorphic code runs
correctly over packed ADTs with no specialization** — it sees a `KValue*`, calls
`kctor_tagid`, and the accessor reads the discriminant out of the word instead of
dereferencing a box. Specialization (Swift-style) is therefore a *performance*
refinement (skip the dispatch / unpack inline for a statically-known layout), NOT
a correctness requirement. This is the central simplification vs Swift's VWT
machinery: our "value witness" is the single set of immediate-aware accessors.

**Crucial caveat (found 2026-06-26): this holds ONLY when the discriminant is
stored EXPLICITLY in the word** (`b010` nullary, `b011` packed — `kctor_tagid`
reads the tag blind). A **niche** layout (`Some p = p`, the discriminant *implicit*
in a field's invalid values, Rust-style) does NOT have this property:
`kctor_tagid(Some p)` would see the INNER value's tag, and nested `Option<Option a>`
makes `Some None` collide with `None` — which a polymorphic `Option a` cannot
disambiguate (it doesn't know whether `a` is itself an `Option`). So **niche
layouts are non-uniform and require specialization** (the Swift path) — they are
**Stage 2, not Stage 1**. The uniform, sound Stage-1 packings (`b010`, `b011`) all
keep an explicit discriminant, which is exactly why they survive nesting and
polymorphism. `Option<Int>` (small) and `Option<Bool>` pack uniformly via `b011`;
`Option<boxed>` (the bare-pointer niche) and full-range `Option<Int>` need
specialization.

## Layout classes (computed per ADT at compile time)

Input: `DataInfo.diCtors` (the variants) and each ctor's `CtorInfo.ciType` (the
Pi telescope → field types). The layout is computed RECURSIVELY (a field's layout
feeds its parent's); it bottoms out at Int (`b001`), nullary-ctor (`b010`),
pointer (`b000`), and the boxed fallback.

1. **Nullary-ctor immediate** (`b010`) — a constructor with NO fields, of any ADT.
   `Build = (ctorTagId << 3) | b010`; `kctor_tagid(imm) = payload >> 3 = tagId`.
   Covers every enum variant *and* the nullary case of a mixed ADT (`None`, `Nil`,
   `Quit`, `True`, `False`, `Unit`, …) — they become alloc-free, and a match on
   them is a deref-free integer compare. Mixed ADTs work because the tag id
   distinguishes the immediate `None` from a boxed `Some` uniformly through
   `kctor_tagid`. **This is the first increment** and generalizes the narrow
   Bool/Unit/Nil/None special-case the user rejected.

2. **Niche-optimized pointer carrier** (Rust's Option<&T>) — an ADT with one
   variant carrying a single BOXED (`b000`) field and the other variants nullary
   (e.g. `Option<List>`, `Result<boxed, small>`). Represent the pointer variant AS
   the pointer (`Some p = p`), and the nullary variants as their `b010`
   immediates — the immediate (an odd, misaligned, non-pointer word) IS the niche
   that distinguishes `None`. Zero box, zero discriminant word for the whole
   `Option<boxed>`. The match tests `kis_imm` (→ a nullary variant by tag id) vs a
   pointer (→ the carrier variant). The killer optimization for `Option`/`Maybe`
   over heap types.

3. **Packed tagged union** (`b011`) — every variant's `discriminant + packed
   payload` fits the 61-bit field (e.g. `Option<Int>`, `Result<small, small>`,
   small enums carrying a small scalar). Encode `payload<<k | discriminant<<3 |
   b011`; build packs, match reads the discriminant, projection unpacks. Payload
   packing recurses (an Int field is its 61-bit value, a nullary field its tag id,
   a nested small ADT its packed word). The bit budget + niche reuse is the part
   the research is grounding (rustc's algorithm).

4. **Boxed fallback** (`b000` → `K_CTOR`) — anything too big or recursive (e.g.
   `Cons` carries two pointers; `List`/trees stay boxed). Unchanged from today.

## Soundness obligations

- **Deref audit extends to ctor sites.** `kctor_tagid`/`kctor_arg`/`kctor_argc`
  and the construction path must branch on `kis_imm` and read the discriminant/
  payload from the word for packed reps, `kderef` only a real `b000` box. The
  debug assert keeps catching raw derefs.
- **Canonicalization** (§5.2): a packed value has exactly ONE representation
  (`None` is always the same immediate), so pointer-identity equality and
  `kvalue_rep_eq` stay correct; never leave an equivalent boxed form.
- **GC safety**: every packed/immediate rep is an odd low-tagged word → a
  non-pointer to Boehm; niche markers must likewise be low-tagged, never a value
  that aliases a heap address (no NaN-box-style high-bit niches).
- **Match exhaustiveness / id agreement**: the discriminant encoding must agree
  with the codegen tag ids the `match` dispatches on (the `KCT_*`/`KCT_USER_BASE`
  scheme), so the layout pass and the match lowering share one source of truth.

## Specialization (Swift-style, a later perf stage)

For a polymorphic function applied at a statically-known monomorphic layout, emit
a specialized worker that constructs/matches the packed rep inline (no
`kctor_tagid` dispatch, no `kctor_arg` call) — the generalization of the existing
`scalarPlan`/`kwi_` worker/wrapper to a layout kind. The boxed `KValue*` body is
the always-correct fallback (the "value witness"), so specialization never
gates correctness. Truly polymorphic positions stay uniform.

## Research-grounded refinements (cited; full report in the session log)

A fact-checked survey (Rust `rustc_abi`, Swift OOPSLA'19, GHC unboxed sums,
OCaml/POPL'24 "Unboxed Data Constructors", OxCaml, BDW-GC) confirmed the design
and pinned the algorithm + the soundness gate:

- **Two encodings, named after Rust's `TagEncoding`.** **Direct** = the
  discriminant stored explicitly (class 3, packed unions). **Niche** = the
  discriminant encoded in values invalid for a field (class 2, `Option<boxed>` =
  the bare pointer, `None` = a reserved immediate; Rust *guarantees* `Option<&T>`
  is one word, `None` = the null niche). Class 1 (all-nullary enum) is GHC's
  "zero-width sum collapses to a pure integer tag." Niche packing is a PRIVATE
  per-ADT choice, never an ABI Kappa must honor.
- **The layout algorithm is compute-both-pick-smaller** (rustc's actual algorithm,
  not a size heuristic): for each ADT compute the Direct (tagged) candidate and,
  when possible, the Niche candidate; keep the smaller that fits one word (tie →
  larger remaining niche → else tagged); else stay boxed. Recurse over variants
  (`diCtors`) × field types (each ctor's Pi telescope), bottoming out at
  Int/enum immediates + pointers; a field that itself needs boxing, or a recursive
  occurrence, is a pointer base case — so the "too big → boxed" fallback always
  fires on lists/trees.
- **The gating SOUNDNESS check is head-shape disjointness (POPL'24).** Packing must
  be statically REJECTED if it could make two distinct source values share one
  representation. Compute each ADT's "head shape" (the immediate code / block tag
  each ctor would occupy); accept a packing ONLY if all ctors' heads are pairwise
  DISJOINT. (OCaml rejects `X of string | Y of string [@@unboxed]` exactly here.)
  For Kappa: a reserved immediate (`None`, a packed enum) must provably never
  collide with a pointer or another packed case. The argument rests on Kappa's OWN
  tag invariant — **only `b000` is a pointer** — not imported from OCaml's
  precise-GC odd/even discipline (a disanalogy the verifiers flagged).
- **Canonicalization is "always inline, never sometimes-boxed."** A packable value
  has exactly ONE representation, so pointer-identity / `kvalue_rep_eq` / hashing
  stay consistent (including across a future specialization boundary).
- **Specialization = uniform path + opportunistic worker/wrapper, NOT a runtime
  VWT.** Swift's VWT uniform path is 1.56×–21.75× slower than specialized; Kappa
  already has the uniform boxed path for free, so add worker/wrapper specialization
  per layout class only where the concrete layout is statically known — never
  per-value runtime witness passing.

**Open (to settle while building 1c/1d):** the exact tag allocation across
`b010..b111` (6 codes over 61 bits) for nullary-enum vs Direct-union vs niche
ranges (can one code be sub-partitioned?); whether to do Rust's MULTI-variant
niche-filling (it caused rustc compile-time regressions, PR #70477 closed →
#94075 — start with the simple Option-style single niche); the exact
recursive-ADT termination rule. Sources: rustc_abi `TagEncoding`/`layout.rs`,
Nomicon, `std::option`; Swift OOPSLA'19 (VWT cost); GHC unboxed-sums guide;
OCaml RFC #14 + POPL'24 constructor-unboxing; OxCaml layouts; BDW-GC.

## Staged plan

- **Stage 1b — nullary-ctor immediates (`b010`), ALL nullary ctors. DONE**
  (commit `20498d1`, merged `2050f08`). Runtime-only: `kctor(argc==0)`/`kctor0`/
  `kbool`/`kunit` → `kmk_imm_ctor(tagId)` (the `the_true`/`the_false`/`the_unit`
  carriers retired, §5.2); `kctor_tagid`/`kctor_argc`/`kctor_name`/`kas_bool` read
  the id from a `b010` word before any deref; a `knullary_builtin_id` name→id
  table keeps the runtime's race/scope outcome name-matching working (`kctor_is`
  turned out NOT to be purely diagnostic). VERIFIED: **corpus 83/83**, native
  suite + conformance 1738/1738 green, kderef assert never fired, **`ctor0-build`
  48→0 B/op** for arbitrary enums (`ctor-build` flat 64 B, the boxed Cons control).
- **Stage 1d — packed single-field ctors (`b011`). DONE** (runtime-only, the b010
  analogue one tag code up). A constructor with EXACTLY ONE explicit field whose
  runtime value is an IMMEDIATE (a b001 Int or a b010 nullary ctor) that fits the
  payload packs into a single word; otherwise (heap-pointer field / too-big
  immediate / argc≠1 / tagId ≥ 2^20) it stays the boxed `K_CTOR`. This makes the
  `Some`/`Ok`/`Err` single-field arms of `Option<Int>` / `Option<Bool>` /
  `Option<enum>` / `Result<small,small>` alloc-free. The discriminant (`tagId`) is
  stored EXPLICITLY in the word so `kctor_tagid` decodes it blind (polymorphic
  `Option a -> …` works) and **`Some None` packs as a b011 word DISTINCT from
  `None`'s b010** — nested `Option<Option>` has NO collision (the soundness win
  over a niche, per the caveat above). Per-value packing is canonical: a given
  value has ONE rep (`Some 5` always packs; `Some (2^55)` always boxes), so
  equality stays consistent. Runtime: `kctor(argc==1 && fits)` → `kmk_imm_packed`;
  `kctor_tagid`/`kctor_argc(=1)`/`kctor_arg(=field word)`/`kctor_name`/`kctor_is`
  are b011-aware (a `kbuiltin_ctor_id` name→id table extends Stage-1b's nullary
  table to the single-field builtins — `Some`/`Success`/`RaceWonLeft`/
  `RaceWonRight`/`TimeoutDone` — whose Exit field can itself be a packing
  immediate, so the OUTCOME packs too and is matched by name in race/scope/atomic
  paths); `kvalue_rep_eq` compares a packed value STRUCTURALLY against any ctor
  rep. The packing also gates on `tagId` fitting 20 bits so the kappart2 CK-machine
  OP nodes at `KRT2_OP_BASE = 0x40000000` (e.g. `ioPure(immediate)`) stay boxed and
  keep their full id. VERIFIED: **corpus 90/90** interp==C==LLVM (incl. the
  nested-`Option<Option<Int>>` soundness test and `Some None /= None`), native
  suite + conformance 1738/1738 green, kderef assert never fired, **`packed-build
  (Some smallInt)` 0 B/op** (the bench WIN), `ctor0-build` / `addInt` still 0,
  `ctor-build` (n-ary Cons) flat 64 B. No backend change needed — single-field
  `CCtor` lowers through `kctor` and `CMatch` dispatches via `kctor_tagid`/
  `kctor_arg`, all now b011-aware. *(Layout note: the single-field encoding was
  renumbered into the unified `b011` layout below when Stage 1e landed — see the
  bit budget there; functionally identical, the field shrank 41→40 bits.)*
- **Stage 1e — packed MULTI-field ctors (one OR two fields, unified `b011`). DONE**
  (runtime-only, the b010/b011 analogue — NOT specialization). The `b011` tag now
  carries a 1-bit `nfields` selector, so ONE encoding covers both arities:

  ```
  bits 0..2   : b011         (3)   immediate-kind tag
  bit  3      : nfields      (1)   0 → single field, 1 → two fields
  bits 4..23  : tagId        (20)  the explicit discriminant (program ctor ids)
  bits 24..63 : field region (40)  payload — split per nfields:
     nfields=0:  field0 word                       (40 bits, arithmetic-recovered)
     nfields=1:  field0 word (20) | field1 word (20)  (each arithmetic-recovered)
  ```

  **Bit budget (every bit accounted):** 3 (tag) + 1 (nfields) + 20 (tagId) = 24
  fixed bits, leaving 64−24 = 40 payload bits. Single: 40 → field0. Double: 40 →
  20+20. Both sum to 64. The single-field budget is therefore 40 bits (was 41
  before the nfields bit was carved out); each two-field slot is 20 bits, so a
  field's WHOLE immediate word (a b001 Int `(v<<3)|1` or a b010 ctor `(id<<3)|2`)
  must fit ±2^19 — i.e. a value in roughly ±2^16 for an Int, every small nullary
  ctor for an enum. **Single-field corpus stays green** by renumbering into this
  unified layout (the cleaner of the two options the scoping allowed): the
  single-field encoder/decoder shift by the same `HDR_BITS=24`, so they stay
  self-consistent; the packed-* tests observe only values, which are unchanged.
  A two-field ctor packs when `argc==2 && tagId fits 20 bits && BOTH fields fit
  their 20-bit slot`; else (heap-pointer field / too-big immediate / argc∉{1,2} /
  tagId ≥ 2^20) it stays the boxed `K_CTOR`. This makes `Pair(Int,Int)` (small),
  2-scalar records lowered to a ctor, and 2-enum variants allocation-free.
  **Soundness/uniformity** are the same argument as 1d, extended: the tagId AND
  BOTH fields live explicitly in the word, so `kctor_tagid`/`kctor_arg` decode
  blind (a polymorphic `Pair a b -> …` works) and a packed `Pair(None,None)` is a
  b011 word DISTINCT from any nullary b010. Runtime: `kctor(argc==2 && fits)` →
  `kmk_imm_packed2`; `kctor_argc` returns 1 or 2 from the `nfields` bit, `kctor_arg`
  reconstructs field `i` from its slot, `kvalue_rep_eq` compares packed values
  structurally over ALL fields (same tagId + arity + recursively-equal fields).
  Two-field runtime ctors that can now pack were audited: `__rat` (a small
  Rational e.g. `1/2`), `Cons(smallInt, Nil)` (a singleton list), and
  `MkInterruptCause(tag, None)` — their raw-deref readers (`as_rat`, `kis_cons`,
  `kpf_showRat`) were routed through the rep-agnostic `kctor_tagid`/`kctor_arg`;
  the STM/OP nodes at `KRT2_OP_BASE` are gated out of packing as before. No backend
  change needed — `CCtor` lowers through `kctor(tc,name,len,arr)` for any arity and
  `CMatch`/`CProj` read via `kctor_arg`/`kctor_argc`, all rep-agnostic.
  VERIFIED: **corpus 102/102** interp==C==LLVM (incl. `Pair(Int,Int)` build/match/
  project-both, large-field boxed fallback, 2-enum, mixed immediate+heap boxed
  fallback, equality, nested `Option (Pair Int Int)` / `Pair (Pair 1 2) 3`,
  negative-field sign round-trip, a packed Pair through a polymorphic swap),
  native suite + conformance 1738/1738 green, kderef assert never fired,
  **`pair-build (Pair smallInt smallInt)` 0 B/op** (the bench WIN), `packed-build`
  / `ctor0-build` / `addInt` still 0, `ctor-build` (n-ary Cons) flat 64 B.
- **Stage 2 — specialization** (worker/wrapper per statically-known layout), which
  UNLOCKS the non-uniform layouts that the uniform `b010`/`b011` packings cannot
  reach:
  - **niche** `Option<boxed>` = the bare pointer / `None` = a reserved immediate
    (the former "1c" — non-uniform per the caveat above, so it rides on
    specialization, not Stage 1);
  - full-range `Option<Int>` and multi-field / multi-variant Direct-tag packing
    (the per-ADT compute-both-pick-smaller layout pass + head-shape gate);
  - inline construct/match/project for hot polymorphic call sites over known
    layouts. The uniform boxed path stays the always-correct fallback.
