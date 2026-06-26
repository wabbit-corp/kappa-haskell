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
b010  immediate ctor  (a NULLARY constructor; tag id in the payload)
b011  packed union    (discriminant + small payload in the 61-bit field)
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

## Staged plan

- **Stage 1b — nullary-ctor immediates (`b010`), ALL nullary ctors.** The first
  increment: a compile-time "is this ctor nullary" check drives `kmk_imm_ctor` at
  construction; `kctor_tagid` returns the tag id from a `b010` word; the ctor
  deref audit gains the `b010` branch. Gate: `ctor0-build` 48→0 B/op for arbitrary
  enums; corpus/native/conformance green; the go/no-go ctor-deref tax flat.
- **Stage 1c — niche optimization** for the single-boxed-payload + nullary-rest
  shape (`Option<boxed>` and friends). (Research-informed.)
- **Stage 1d — packed tagged unions (`b011`)** for small-payload multi-variant
  ADTs, with the per-ADT bit-layout algorithm.
- **Stage 2 — specialization** (worker/wrapper per layout) for hot polymorphic
  code over packed ADTs.
