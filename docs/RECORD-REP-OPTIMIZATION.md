# Record Representation Optimization

How `K_REC` is represented and projected today, where the redundancy is, the
optimization directions ordered by payoff × feasibility, the row-polymorphic
story (with cross-language evidence), and a hard erasure verdict on what is free
versus what is blocked.

All claims are grounded in `file:line`. The headline conclusion: **closed-record
flattening is fully doable under erasure today** — record *shape* (arity + slot
index) is a static fact at the elaboration site, carried in `CRecordV`/`CProjAt`
as constants, with no type variable to monomorphize over. This is structurally
unlike the deferred niche, which needs runtime knowledge erasure throws away.

---

## 1. Current cost

### 1.1 The box: 3 words + a separate heap array

A record is `K_REC`, whose union member is

```c
struct { int n; const char **names; KValue **vals; } rec;   // runtime/kappart.h:121
```

= 3 words (arity padded to 8 B + two pointers). Construction goes through `krec`:

```c
KValue *krec(int n, const char **names, KValue **vals) {     // runtime/value.c
  KValue *r = alloc_val(K_REC);          // (1) box: kgc_alloc(sizeof(KValue))  — kappart.c:85-89
  r->as.rec.n = n;
  r->as.rec.names = names;               // stored verbatim — a generated static literal (387)
  if (n) {
    KValue **v = (KValue **)kgc_alloc(sizeof(KValue *) * (size_t)n);  // (2) SECOND heap alloc
    for (int i = 0; i < n; i++) v[i] = vals[i];                       // copies caller's vals
    r->as.rec.vals = v;
  } else r->as.rec.vals = NULL;
  return r;
}
```

**Per instance: two scanned-heap allocations** — the box (`~4` words / 32 B) and
the `vals` array (`n` words) — for `~(4 + n)` words. Both are on the scanned
Boehm heap (`kgc_alloc`, not `kgc_alloc_atomic`), so the GC conservatively scans
both objects.

### 1.2 The redundant names

The `names` array is **not** per-instance heap data: the backend emits it once as
a shared static literal —

- C: `static const char *rnames_[]` (`src/Kappa/Backend/C.hs:2758-2770`)
- LLVM: a module-level `@.rnames.N = private constant [n x ptr]` (`src/Kappa/Backend/LLVM.hs:1168-1213`)

So per-instance names cost **zero bytes** already. The redundancy to attack is the
`names` *word in the box* (1 word/instance) plus the runtime `strcmp` scan it
enables — not allocation bytes.

### 1.3 Projection: index-based OR name-based, decided at the site

Core has two projection nodes (`src/Kappa/Core.hs:135-144`):

- `CProj !Term !Text` — name only → `kproj` → **linear `strcmp` scan** over
  `names[]` (`runtime/value.c`).
- `CProjAt !Term !Text !Int` — name + a **static slot index `i`** → `krec_at` →
  **direct `vals[i]` read, no `strcmp`** (`runtime/value.c`).

The elaborator picks per-site (`src/Kappa/Check.hs:5956-5975`, verified verbatim).
It emits `CProjAt tm1 f i` **only** when the receiver type forces to a CLOSED
`VRecordT fs`, the field is present, the layout is already sorted, and the index
is known:

```haskell
let f = nameText mn0
    names = map fst fs
    proj
      | names == sort names
      , Just i <- elemIndex f names = CProjAt tm1 f i   -- Check.hs:5973
      | otherwise                   = CProj    tm1 f     -- Check.hs:5974
```

Everything else — **open / sealed / dict / derived** projection, and tuples of
arity ≥ 10 (positional `_1.._n`, where `_10 < _2` breaks lexicographic order) —
stays name-based `CProj`/`kproj`. So a name-free index discipline **already
exists and is exercised**; it is just gated on the closed-sorted case.

**Crucial subtlety on slot order**: the canonical order is NOT plainly
lexicographic. Per §13.2.1.1/§31.4 (`docs/Spec.md:12366, 12384-12450`) it is a
*dependency-respecting topological* order, lexicographic only as the tie-break.
Construction (`sortOn fst`, `Check.hs:3258`) and the projection index
(`elemIndex f (sort names)`) must agree, which is exactly why `CProjAt` is gated
on `names == sort names`. Any flatten that drops names **must take slot order
from the same canonicalizer the constructor used**, never re-derive it by sorting
at the projection site.

### 1.4 The three runtime name consumers (names are not vestigial)

Names are load-bearing in exactly three runtime ops:

1. `kproj` — `strcmp` scan for name-based projection (`kappart.c:925-939`).
2. `krec_without` — §17.2.5 rest binder; `strcmp` to filter excluded labels
   (`kappart.c:979-996`).
3. `kvalue_rep_eq` — structural equality; `strcmp(names[i])` then `rep_eq(vals)`
   (`kappart.c:1454-1459`).

There is **no** runtime record `show` (the `show*` family covers only
Int/Double/Scalar/String); records are shown by Kappa-level code. And the
**runtime itself** projects effect-handler `ops` records BY NAME:
`kproj_opt(h->ops, "__tailResumptive")` and `kproj(h->ops, op->as.str.p)`
(`runtime/rt.c:497-512, 849`). This is decisive proof that names cannot be dropped
*globally* — they survive on the open/handler path.

### 1.5 Records never pack

`Repr.hs` (the layout authority) classifies **constructors only** — `CtorLayout`
= `LayoutImmediate`/`LayoutMayPack`/`LayoutBoxed` (`src/Kappa/Backend/Repr.hs:276-309`),
with no record entry; records are implicitly `RepBoxed`. Tuples and records both
lower `CRecordV → krec/K_REC`, never through `kctor` (`Check.hs:3258, 3341-3345`),
so they get **none** of the b011 immediate packing. The runtime comment
"a 2-scalar record lowered to a ctor" (`kappart.c:352`, `LAYOUT-DESIGN.md:231`) is
**aspirational** — no such lowering exists in `src/Kappa/`. Consequently
`Pair(Int,Int)` is 0 B/op while `{x:Int, y:Int}` is box + vals-array
(`LAYOUT-DESIGN.md:246-252`). That gap is the headline opportunity.

---

## 2. Optimization directions

Five directions, increasing in cost. Each is independent except where noted.

### A. Drop the per-box `names` word (index-based projection)

- **Saves**: 1 word/instance + the runtime `strcmp` scan; unblocks flattening.
- **Mechanism**: keep `names` as a per-record-*type* static descriptor (already
  static — `C.hs:2768`) and reroute the three name consumers (§1.4). Closed
  records already use `CProjAt`/`krec_at` (no names touched), so for them names
  are dead weight droppable now. Open/sealed/dynamic still need a name→index map,
  but it is compile-time-known *per type*, so it lives in the static descriptor,
  not the per-instance box.
- **Erasure-safe**: yes for the closed part. The open part needs a shared
  descriptor escape hatch (see §3).
- **Migration surface**: `kproj`, `krec_without`, `kvalue_rep_eq` consult a
  descriptor instead of a per-instance pointer; the elaborator's closed-sorted
  gate (`Check.hs:5972`) extends to more sites.

### B. Flatten `vals` into the box

- **Saves**: 1 allocation + 1 pointer-chase + 1 scanned GC object, for **every**
  record. The single biggest, lowest-risk win.
- **Mechanism**: a flexible-array-member `K_REC` variant
  `struct { KTag tag; int n; KValue *fields[]; }` allocated in one
  `kgc_alloc(sizeof(KValue) + n*sizeof(KValue*))`. `krec_at` becomes
  `rec->fields[i]` — no second indirection. Only `krec`'s body changes; codegen
  is unaffected (still calls `krec(n, names, vals)`).
- **Erasure-safe**: yes, unconditionally — depends only on arity `n` (already
  passed); element types are irrelevant (every slot is a uniform `KValue*`).
- **GC**: neutral-to-positive — one scanned object instead of two, one fewer
  false-pointer source. Conservative Boehm traces the inline FAM automatically
  (zero precise/typed GC descriptors anywhere in `runtime/`; interior pointers
  OFF, `kappart.c:60`, but the runtime only ever holds the base record pointer).
- **Interpreter parity is a non-issue**: the interpreter has its own Haskell
  `VRecordV ![(Text, Value)]` (`Core.hs:336`), NOT the C `KValue` struct. Parity
  is *observational* (via `kvalue_rep_eq`), not struct-identity — so the
  `UNBOXING-DESIGN.md §10` (`:599-604`) deferral reason ("box shared with the
  interpreter") does **not** bind for the in-box-flatten variant. This is a real
  reason to revisit §10 specifically for records.
- **Perceus-enabling**: one contiguous block is a strictly better in-place-reuse
  target than box + array.

### C. Pack small records into b011 immediates

- **Saves**: zero allocation for 1–2 all-immediate-field closed records (closes
  the `{x:Int,y:Int}` vs `Pair(Int,Int)` gap).
- **Mechanism**: add a record arm to `Repr.hs` and lower closed all-immediate
  records to a *synthetic anonymous constructor* with a program-assigned tag id,
  routing through the **existing** b011 path (`kctor` per-value fits-check,
  `kappart.c:347-358`; `KIMM_PACKED_TAG_BITS=20` has ample room, `kappart.h:318`).
  Rewrite the closed `CProjAt i` → `kctor_arg(v,i)`. The per-value fits-check is
  canonical and works *blind* under erasure — same as b011 ctors already do.
- **Erasure-safe**: yes — the fits-test is per-VALUE, not per-instantiation; it
  needs no type. It does carry a `kis_imm`/`kderef` deref-audit cost
  (`UNBOXING-DESIGN.md` R1) and one reserved tag-space code (`b100..b111`,
  `kappart.h:175`), so it follows B, not precedes it.
- **CLOSED only**: a row-polymorphic record can grow fields and must stay boxed.

### D. Row-polymorphic handling

See §3. The key result: open records need **no per-instance names either** —
adopt the Elm/OCaml shared field-ID table so the open case costs the same as the
closed case (an int search, far cheaper than today's `strcmp` scan). Saves the
names word on the open path too; replaces every open/dynamic `strcmp` (`kproj`)
with an `O(log n)` search over small ints.

### E. Per-shape specialization (DEFERRED — do not pursue)

- A per-shape specialized struct, or a record niche (1-field-record-as-bare-field),
  needs typed Core + monomorphization/coercions. Ruled **NOT WORTH IT** under §8.3
  separate compilation (`SPECIALIZATION-SCOPING.md`); the niche reintroduces the
  exact erasure blocker the niche work was deferred for
  (`niche-layout-vs-type-erasure`). The flatten + explicit-discriminant-pack line
  (B+C) gets the allocation win **without** the type dependence. Skip.

---

## 3. The row-polymorphic story

### 3.1 What Kappa does today

Open records are **purely a type-level distinction**. At runtime an open record is
an ordinary fully-materialized, lexicographically-sorted `K_REC` with **all** names
present: `__rowExtend` inserts the field into the sorted list (`Eval.hs:597-601`,
`insertField`), producing a fresh `VRecordV`; neither backend nor the runtime
implements `__rowExtend` (it normalizes to `CRecordV` before codegen). All row
machinery is erased / Q0: `LacksRec r l` is discharged by the unit witness
`__rowEvidence` (`Check.hs:2611-2632`); `__openRec`/`__closedRow`/`__rowExtend`/
`__rowEvidence` are erased prelude globals (`Builtins.hs:399-403`, `Prelude.hs:126-137`).

So there is **no runtime value that "doesn't know its fields"** — the callee
receives a concrete `K_REC`. What it lacks statically is the *full field set*, not
the field-ID of the field it projects.

**The missed optimization** (`Check.hs:5993-6001`): projecting an explicit-prefix
field of an `__openRec r prefix` *always* emits name-based `CProj`, even though the
prefix is a sorted `VRecordT fs` whose index is computable with the same
`elemIndex` used at line 5973. A raw positional `CProjAt` is **not** safe here (a
residual-row label can interleave with prefix labels in sort order), but a
field-ID search **is** safe regardless of interleaving.

### 3.2 Cross-language evidence (offset static-or-dynamic? names at runtime?)

| Language | Offset | Names at runtime? | Open-row mechanism | Fit for AOT/erasure |
|---|---|---|---|---|
| **Roc** | fully static | none | monomorphized; records/tuples share one fixed layout | No — no erasure (the extreme Kappa rejected) |
| **GHC** (`HasField`/RecordDot) | static when concrete; selector passed as dict when abstract | none (positional heap objects) | pass the selector as a runtime dictionary | Partial — no first-class open records |
| **PureScript** | dynamic, JIT-cached (V8 hidden classes) | yes (object keys) | plain JS object, `obj.label` | No — needs a JIT |
| **TS-on-V8** | static-behind-shape-guard; megamorphic → dict lookup | yes | hidden class + inline cache | No — needs a JIT |
| **OCaml** | dynamic (binary search over sorted hashed method-tags) | tags (ints), not strings, in a *shared* table | same hashed-tag search; poly-variants tagged by name-hash | **Yes — AOT-friendly** |
| **Elm** | dynamic (search over the type's sorted int field-ID array) | **none per-instance**; shared static `FieldGroup` | accessor-by-ID; **open costs the same as closed** | **Yes — the closest match** |

Three strategies emerge: (1) monomorphize → static offsets, zero metadata
(Roc/GHC-concrete) — rejected by erasure; (2) per-instance hidden class + inline
cache (V8/PureScript/TS) — needs a JIT, wrong for AOT C/LLVM; (3) **shared
compile-time field-ID table + search/index, no per-instance names** (Elm
FieldGroup, OCaml method suite) — the AOT-friendly sweet spot, and the one that
makes the open case cost the same as the closed case.

Elm's source is explicit: "All records of the same type point to a single shared
FieldGroup" (`dev.to/briancarroll/elm-in-wasm-custom-types-and-extensible-records-15m0`).

### 3.3 Recommended row strategy — adopt Elm/OCaml

- **Closed records**: `K_REC` carries a pointer to a per-*type* static descriptor
  `{ int n; const uint32_t *field_ids; }` (sorted field-IDs, interned once per
  distinct sorted field-name set) plus the flattened values inline (§2.B). Names-
  as-strings vanish; `krec_at(rec,i)` is unchanged.
- **Open records**: share the **same** field-ID representation — they are already
  fully-materialized sorted `K_REC` at runtime, and the row machinery is erased.
  Resolve open-row access by interning each label to a global field-ID and
  emitting "find `id` in this record's sorted id-array, then index" — a small
  branch-predictable binary search over ints (`krec_at_id(rec, id)`), far cheaper
  than today's `strcmp` scan.
- **Degradation ladder**: (a) closed sorted → flat inline + raw `krec_at` (zero
  metadata); (b) open with closed residual row → flat + `krec_at_id` search;
  (c) fully abstract row tail → same `krec_at_id` search (descriptor travels with
  the value). No case needs per-instance name strings; no case needs
  monomorphization.
- **Immediate low-risk win** (independent of the rep change): switch the
  `Check.hs:5993-6001` open-prefix projection from `kproj` (strcmp) to a field-ID
  search — correct regardless of interleaving. Only emit a raw `CProjAt` offset
  when the residual row is provably a `__closedRow` whose labels all sort after
  the prefix.

**Caveats to verify before implementing**: (i) `krec_without` (§17.2.5 rest,
`kappart.c:979-996`) builds a filtered field set — under field-IDs it must intern
a residual descriptor (precomputable: excluded labels are statically known at the
`CPRecord`/`CPInjectRest` pattern site). (ii) Tuples at arity ≥ 10 diverge from
lexicographic order — derive IDs from the **slot order**, not raw name sort.
(iii) `__rowExtend` must insert into both the id-array and values in matching
order (or rebuild from a precomputed descriptor — the new label is statically
known at `elabOpenPatch`, `Check.hs:6547`).

---

## 4. Erasure verdict

**Closed-record flattening is doable under erasure today. It needs neither typed
Core nor a coercion the `CRecord`/`CProj` nodes lack.**

The reason is structural and decisive. The deferred niche was deferred because it
needs *type-variable knowledge erasure throws away*: `Some p = p` is unsound under
one shared body (`kctor_tagid(Some p)` reads the inner value's tag; nested
`Option<Option>` collides — `LAYOUT-DESIGN.md:40-52`). Record **shape has no such
dependency**: at every construction site the elaborator has the full closed field
list, and at every closed projection it computes the index — `Check.hs:5969-5974`
builds `CProjAt tm1 f i` with `i = elemIndex f names` from `VRecordT fs`. Arity
and slot index are **static facts at the site**, baked into `CRecordV`/`CProjAt`
as constants, with **no type variable to monomorphize over**.

The §34.3.7 keying rule that kills general specialization ("MUST be keyed only by
runtime-relevant representation; erased indices/row args MUST NOT force distinct
specializations", `SPECIALIZATION-SCOPING.md:130-141`) is **satisfied for free**:
a closed record's flat shape is the same runtime layout regardless of the erased
element types, because every slot is a uniform `KValue*` word. Flattening changes
the layout of ALL `K_REC` the same way — a codegen change, not a specialization
keyed on erased type.

**Sub-step status:**

| Sub-step | Status | Why |
|---|---|---|
| Flatten `vals` into the box (B) | **FREE** | Needs only arity `n` (already passed); types irrelevant; interpreter `VRecordV` untouched |
| Drop names — closed records (A) | **FREE** | `CProjAt`/`krec_at` already name-free; names already static |
| Drop names — open records (D) | **FREE** with a shared field-ID descriptor | Field-ID table keyed by structural field-set; identical for closed/open views ⇒ no coercion at the boundary |
| Pack small records into b011 (C) | **FREE but costs runtime machinery** | Per-VALUE fits-check works blind; needs a reserved tag code + `kis_imm`/`kderef` audit, no typed Core |
| Record niche / per-shape struct (E) | **BLOCKED** | Reintroduces the deferred niche's type dependence; needs typed Core + coercions |

The only thing that is **not** free is the genuinely niche-like variant
(1-field-record-as-bare-field) and per-shape specialized structs — and those are
explicitly not recommended.

---

## 5. Staged plan (payoff × feasibility)

Ordered cheapest-high-payoff first. Each item is ROADMAP-ready.

1. **Flatten `K_REC` values inline into the box (FAM), eliminating the separate
   `vals` allocation** — one `kgc_alloc` instead of two for every record; only
   `krec`'s body changes (`kappart.c:384-396`), codegen untouched; GC-positive
   (one fewer scanned object), interpreter-parity-trivial, zero typed-Core work.
   *This is the cheapest high-payoff first step.*

2. **Extend index-based (`CProjAt`) projection to every closed-sorted site and
   route the three name consumers (`kproj`, `krec_without`, `kvalue_rep_eq`)
   through a per-type static descriptor, removing the `names` word from the
   per-instance box** — drops 1 word/instance and the runtime `strcmp` scan for
   closed records.

3. **Replace per-instance names with a shared per-type field-ID descriptor (Elm
   FieldGroup) and add `krec_at_id` so open/row-polymorphic projection becomes an
   int search instead of a `strcmp` scan** — unifies closed and open layout, makes
   open cost the same as closed, and fixes the missed `CProjAt` at
   `Check.hs:5993-6001`.

4. **Add a record arm to `Repr.hs` and pack 1–2 all-immediate-field closed records
   into b011 immediates by lowering them to synthetic anonymous constructors
   through the existing `kctor` path** — zero allocation for the common small
   record, closing the `{x:Int,y:Int}` vs `Pair(Int,Int)` gap
   (`LAYOUT-DESIGN.md:246-252`); carries the `kis_imm`/`kderef` audit + one
   reserved tag code, so it follows steps 1–2.

5. **DEFERRED — do not schedule: record niche (1-field-record-as-bare-field) and
   per-shape specialized structs** — both need typed Core + coercions/monomorphization
   and reintroduce the deferred-niche erasure blocker; the flatten + pack line
   (1–4) captures the allocation win without the type dependence.

---

*Do not edit `ROADMAP.md` from this document — the user folds these items in.*
