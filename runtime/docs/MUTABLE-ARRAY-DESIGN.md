# Mutable Arrays for Kappa — Design

Status: design plus landed boxed-runtime floor. The `K_ARRAY` boxed storage tag,
owned get/set/len runtime operations, and S4 shared-storage synchronization are
implemented; scalar/unboxed slabs, linear arrays, and `TArray` remain design work.
Audience: implementers extending the runtime tag, prims, both backends, the
prelude surface, and the tests.

This document synthesizes four research passes (linear/uniqueness arrays,
monadic ST/IO arrays, representation/RC/bounds, and Kappa-internal fit) into a
single principled design grounded in the actual runtime and `docs/Spec.md`. All
runtime references below are symbolic unless a short snippet is shown, so
unrelated edits do not stale the design evidence.

---

## 1. Motivation

Kappa now has an O(1) boxed mutable-array runtime floor (`K_ARRAY` with get/set/len);
the remaining design work in this document is scalar/unboxed slabs, linear arrays,
and richer prelude/backend surfaces. The older immutable `Array a` facade declared in
`docs/Spec.md` §29 was backed by a **cons-list facade**:
`__arrayFromList`/`__arrayToList` are the identity over a `List`
(`runtime/prims.c`, `kpf___queryFromList`), and `__arrayIndexUnsafe`
**walks the linked list** one cons at a time:

```c
/* runtime/prims.c, kpf___arrayIndexUnsafe */
KValue *kpf___arrayIndexUnsafe(KValue **a) {
  KValue *v = a[0]; int64_t i = kas_int(a[1]);
  while (kis_cons(v)) { if (i <= 0) return kctor_arg(v, 0); v = kctor_arg(v, 1); i--; }
  krt_fail("__arrayIndexUnsafe: index out of range");
}
```

So `arrayGet`/`arrayIndex` are O(n) and there is no in-place update at all. The
prelude confirms it: `arrayGet = __listIndex (__arrayToList xs)` and
`arrayIndex = __arrayIndexUnsafe ...` (`src/Kappa/Prelude.hs`, §29 ops). This
task closes a real gap: it gives arrays their true **flat, contiguous backing**
with O(1) get/set, rather than inventing a brand-new concept.

The constraint that makes this interesting: Kappa is a **total, dependently
typed, QTT language** (quantities 0/1/ω/affine/relevant, `docs/Spec.md` §12.2;
totality §15; erasure §31.2). Runtime APIs carry a `KValue*`-shaped tagged word:
immediates and packed small values are not heap `KValue`s, while non-immediate
objects are ordinary Boehm-traced heap values. A mutable array must:

1. preserve **purity/totality** at the type level — no partial `get` in the
   pure fragment;
2. be **erasure-safe** — no `Type`/quantity/proof may reach a `kpf_*` symbol
   (this is exactly the class of bug that caused the prior native IO crash;
   see the `native-io-dict-passing-crash` memory note);
3. be **GC-correct** under Boehm's conservative, interior-pointer-OFF
   collector; and
4. ship **incrementally** on the current boxed runtime while BAKING IN a
   first-class, extremely-performant **element-unboxing** path from day one —
   the boxed slab ships first, but the representation tag and the call-site
   specialization seam exist from the start so an `int64[]`/`double[]` slab + the
   scalar worker give an end-to-end unboxed numeric hot loop with zero
   per-element allocation (§5.3), with no `K_ARRAY` redesign between stages.

---

## 2. Surveyed options and tradeoffs

There are three schools for "O(1) mutable arrays without breaking referential
transparency," plus a fourth runtime-only mechanism. All four compile to the
**same in-place mutation** in Kappa, because both linearity (`1`) and the ST
region tag (`s`) are **erased** under §31.2 — so the choice is about
**ergonomics, proof obligations, and what is SOUND to ship first**, not about
runtime speed.

### Option A — Linear / uniqueness array (the user's first proposal)

An opaque **quantity-1** handle threaded through every op, line-for-line like
Idris2 `Data.Linear.Array` (the same QTT as Kappa's multiplicity-1) and
`linear-base`'s `Data.Array.Mutable.Linear`:

```
arraySet : (1 arr : Array a) -> (i : Nat) -> a -> Array a   -- consumes, returns fresh handle
arrayGet : (1 arr : Array a) -> (i : Nat) -> LPair a (Array a)  -- element ω, array threaded back
arrayFreeze : (1 arr : Array a) -> ImmArray a              -- O(1), result unrestricted
```

Soundness rests on §12.2.6: a linear value is **non-droppable and
non-duplicable**, discharged only by transfer/consume — so the old handle is
provably dead after `set`, and the backend may mutate destructively. The
guarantee is **static and in the type**: misuse is a compile error, never a
silent O(n) copy.

- **Pro:** strongest static guarantee; needs **no Perceus RC** for correctness;
  O(1) copy-free freeze falls out of single-handle consumption.
- **Con (decisive for "first"):** heaviest ergonomics — every op consumes and
  returns the array, threaded by hand (or via a state-monad helper); extracted
  scalars must be re-wrapped unrestricted (`Ur`/`LPair`-second) to escape the
  linear context. And critically, **the Kappa runtime cannot yet *witness*
  uniqueness**: a `K_ARRAY` is just a boxed pointer that any closure capture can
  alias. The *types* are sound, but making the *destructive write* observably
  pure depends on the elaborator's linearity check being airtight end-to-end,
  which is a larger correctness surface than an IO action whose impurity is
  honest. This is a uniqueness-at-runtime / Perceus-adjacent project.

### Option B — ST-region array (rank-2 `runST`)

The `STArray s a` tied to a ghost region `s`, escaping only through
`runST : forall a. (forall s. ST s a) -> a`. The rank-2 `forall s` skolem
forces the body polymorphic in `s`, so no `STRef s`/`STArray s` (nor a closure
capturing one) can appear in the result — a skolem-escape **type error**. This
makes local mutation **observably pure** despite in-place writes.

**This is already specified.** `docs/Spec.md` §18.6.4
gives, nearly verbatim, `expect data ST (s) (a)`, `expect data STRef (s) (a)`,
`instance MonadRef (ST s)`, and `runST : forall a. (forall s. ST s a) -> a`,
states the skolem-escape proof explicitly, and even authorizes a **bump-arena
allocator** tied to the `runST` frame for zero-cost deallocation.

- **Pro:** observably pure mutation in **total** code (`sortArray : Array a ->
  Array a` with no IO in its type); a **sound zero-copy freeze** (the boundary
  proves the array dead); arena allocation the IO array can never have; one
  `runST` wrapper instead of hand-threading; **already mandated by the spec**.
- **Con:** `ST` itself must be implemented (an erased region-newtype over the
  IO/state machinery); rank-2 signatures are slightly heavier than plain IO.

### Option C — IO / STM array (the user's second proposal)

A `MutArray a` whose ops are `UIO` actions, structurally identical to the
existing `Ref`/`TVar`. This is `MonadRef` (§18.6.1) with
an index — `var`-style mutation one categorical step up. Concurrent sharing is
a separate `TArray` (a `TVar`-wrapped array, journaled by the kappart2
scheduler, §18.1.13).

- **Pro:** lowest risk; reuses `do`, `var`-style sugar, the existing IO driver,
  and the `Ref`/`TVar` runtime verbatim; **zero new type-system work**;
  honest impurity (it lives in IO).
- **Con:** result is impure (cannot be used in a pure total function without
  `unsafe`); zero-copy freeze needs an explicit deadness argument.

### Option D — opportunistic RC=1 in-place (Lean/Roc/Koka)

No surface annotation: `set` mutates in place iff the runtime refcount is 1,
else copies (FBIP / Perceus reuse). The proof obligation is on the **programmer**
to keep usage single-threaded.

- **Pro:** fully implicit; the immutable `Array` *becomes* the mutable one once
  Perceus lands — no new type.
- **Con (rejected as PRIMARY):** **no static guarantee**; accidental sharing
  silently degrades O(1) to O(n) (Lean issue 2218: "if-then-else breaks
  apparent linearity"). For a **total language whose entire value proposition is
  type-level guarantees**, a silent performance cliff is the wrong default.
  Also requires Perceus precision for immutable-array reuse, which is not part
  of the current S3 freeable partition: C/runtime Perceus RC is default-on for
  the conservative strict-immutable shapes, but arrays remain Boehm-retained
  until the later FREESET/FBIP stages prove array-element reuse and reclamation.
  **Keep D as a future optimization** of the immutable `Array`, not the
  headline mechanism.

### What is the same across A/B/C

All three compile to **one runtime object** (`K_ARRAY` = `K_REF`'s single cell
generalized to N cells) with the **same three ops**. Linearity (`1`) and the
region tag (`s`) are erased under §31.2 (`docs/Spec.md`) exactly like
Haskell's `%1` and `s`. **Do not build three runtime arrays.** Build one, and
wrap it in the cheapest-to-prove typed front-end first.

---

## 3. Chosen design and rationale

**Resolution of linear-vs-IO/STM:** ship in the order **C → B → (A) → (D)**, not
the user's linear-first instinct. One runtime array (`K_ARRAY`), three typed
front-ends layered over it, staged by *soundness-to-ship* and *risk*:

1. **IO `MutArray` first (Option C).** It reuses `Ref`/`TVar`/`var`/`do`
   verbatim, needs no type-system work, and unblocks real imperative programs
   immediately. Its impurity is honest. This is the right *first ship*.

2. **ST `STArray` second (Option B) — the BEST design for PURE use, and already
   specified.** This is the answer to "does Kappa need rank-2 ST or just IO?":
   **both, for different jobs.** IO for impure in-place work; the rank-2
   `runST` is *required* to get observably-pure mutation and a sound zero-copy
   freeze into **total** code (sorts, DP tables, sieve). The spec already
   commits to it in §18.6.4, including the arena-allocation payoff — so there is
   no design debate, only implementation. `ST s` is an **erased region-newtype**
   over the same `K_ARRAY` ops; the `s` is a quantity-0 phantom and adds no
   runtime object.

3. **Linear `Array` (Option A) deferred — but design for it.** It is fully
   expressible (Kappa has `1`/`<=1`/`&`, §12.2) and is the *eventual* zero-RC
   fast path, reusing the **same `K_ARRAY` and the same `kpf_*` ops** — only the
   surface quantity/threading changes. Hold it until the elaborator's linearity
   end-to-end story (and ideally Perceus, which can *witness* uniqueness at
   runtime) is solid, because today a captured `K_ARRAY` can be aliased, so the
   destructive write's observable purity leans entirely on the static checker.

4. **Perceus RC=1 in-place (Option D) deferred** as an *optimization of the
   immutable §29 `Array`*, not a new type. Design `arraySet`/`arrayMap` on the
   immutable array to be RC-reuse-friendly (single-owner detection) so Perceus
   can turn them in-place later (FBIP). This is the implicit path; the explicit
   linear `MutArray` becomes a niche escape hatch.

**Why this order is the SOUND one for a total QTT language.** The substrate
(`kref_set` widened, GC, `K_ARRAY`) is identical across A/B/C, so "linear-first"
buys no runtime advantage — it only front-loads the riskiest correctness story
(runtime uniqueness) before the easy wins. C is provably correct on day one
(it is `Ref` with an index). B is *mandated by the spec* and is what pure
algorithms actually want. A and D are where the deep guarantees live, and they
are strictly easier to land *on top of* a working `K_ARRAY` than to bootstrap.

**Element unboxing is ORTHOGONAL to this front-end ordering.** The C/B/A/D axis
is about *which typed surface* (IO vs ST vs linear) proves the mutation sound;
**element unboxing is about the SLAB representation underneath all of them** and
is a first-class concern from day one (§5.3). Every front-end shares the one
`K_ARRAY` substrate, so when the unboxed INT64/DOUBLE slabs land (§7 Stage H)
they accelerate IO `MutArray`, ST `STArray`, and linear `LinArray` alike, with no
per-front-end work. The boxed slab ships first because it is what is correct on
the current Stage-0 runtime — NOT because unboxing is an afterthought; the
`elemkind`/`element_size` seam and the call-site specialization mechanism are
designed in from Stage A precisely so the unboxed payoff is additive.

---

## 4. The API (Kappa surface syntax)

All three front-ends follow the **AtomicRef precedent** exactly
(`src/Kappa/Prelude.hs`+): an opaque `data` wraps an opaque cell, and each
surface op `match`-unwraps it and forwards **only values** to a `__`-prim. The
element type is a `forall (a : Type)` = **quantity-0 erased** parameter that
**never reaches the prim** (this is the erasure-safety contract; see §6).

### 4.1 Shared opaque type and primitives

```kappa
-- opaque handle: a one-field data wrapping the runtime buffer (cf. MkAtomicRef)
data MutArray (a : Type) : Type = MkMutArray (buf : __ArrayBuf a)

-- the three erased-element primitives (forall a is Q0, dropped before codegen):
--   __newArray  : forall (a : Type). Nat -> a -> UIO (__ArrayBuf a)   -- arity 2 at the prim
--   __arrayRead : forall (a : Type). __ArrayBuf a -> Nat -> UIO a     -- arity 2
--   __arrayWrite: forall (a : Type). __ArrayBuf a -> Nat -> a -> UIO Unit  -- arity 3
--   __arrayLen  : forall (a : Type). __ArrayBuf a -> Nat              -- arity 1, PURE
```

### 4.2 IO `MutArray` (Option C — ships first)

```kappa
newArray : forall (a : Type). (n : Nat) -> a -> UIO (MutArray a)
let newArray n init = do
    let buf <- __newArray n init
    pure (MkMutArray buf)

-- O(1), pure, total: length is stored in the buffer header
arrayLen : forall (a : Type). MutArray a -> Nat
let arrayLen arr = match arr case MkMutArray buf -> __arrayLen buf

-- TOTAL, proof-carrying read: the (i < len) proof is ERASED (§31.2), so this
-- lowers to a bare O(1) load with NO bounds check.  THIS is the primary form.
arrayRead : forall (a : Type).
    (arr : MutArray a) -> (i : Nat) -> (@_ : (i < arrayLen arr) = True) -> UIO a
let arrayRead arr i = match arr case MkMutArray buf -> __arrayRead buf i

-- TOTAL, proof-carrying write (mirror of arrayRead)
arrayWrite : forall (a : Type).
    (arr : MutArray a) -> (i : Nat) -> (@_ : (i < arrayLen arr) = True) -> a -> UIO Unit
let arrayWrite arr i v = match arr case MkMutArray buf -> __arrayWrite buf i v

-- ERGONOMIC, proof-free, total because Option absorbs OOB (cf. §29 arrayGet)
arrayReadOpt : forall (a : Type). MutArray a -> Nat -> UIO (Option a)
arrayWriteOk : forall (a : Type). MutArray a -> Nat -> a -> UIO Bool

-- bridge to the immutable §29 Array (copying; always sound)
freeze : forall (a : Type). MutArray a -> UIO (Array a)
-- preferred: hand back the length AS the proof index so reads are total O(1)
freezeSized : forall (a : Type). MutArray a -> UIO (exists (n : Nat). SizedArray n a)
thaw   : forall (a : Type). Array a -> UIO (MutArray a)
```

### 4.3 ST `STArray` (Option B — ships second, per §18.6.4)

```kappa
-- ST s, STRef s, runST are §18.6.4 verbatim; STArray is the array sibling.
instance MonadRef (ST s) = ...                      -- already prescribed

newSTArray  : forall (s a : Type). (n : Nat) -> a -> ST s (STArray s a)
readSTArray : forall (s a : Type).
    (arr : STArray s a) -> (i : Nat) -> (@_ : (i < stArrayLen arr) = True) -> ST s a
writeSTArray: forall (s a : Type).
    (arr : STArray s a) -> (i : Nat) -> (@_ : (i < stArrayLen arr) = True) -> a -> ST s Unit

-- the escape-prevented runner (rank-2): no STArray s can appear in `b`
runST : forall (b : Type). (forall (s : Type). ST s b) -> b

-- O(1) zero-copy freeze: sound BECAUSE the skolem boundary proves arr is dead.
-- Expose unsafeFreeze ONLY behind this wrapper (the runSTArray pattern), never raw.
runSTArray : forall (a : Type). (forall (s : Type). ST s (STArray s a)) -> Array a
```

`runSTArray` is where a pure `sortArray : Array a -> Array a` lives: thaw into
an `STArray`, sort imperatively, freeze with zero copy, all inside `runST` —
**no IO in the type**, total.

### 4.4 Linear `Array` (Option A — deferred; design for later)

```kappa
-- v2: same K_ARRAY runtime, quantity-1 surface, Idris2/linear-base shape
linAlloc  : forall (a b : Type). (n : Nat) -> a -> (1 k : (1 arr : LinArray a) -> b) -> b
linGet    : forall (a : Type). (1 arr : LinArray a) -> (i : Nat) -> LPair a (LinArray a)
linSet    : forall (a : Type). (1 arr : LinArray a) -> (i : Nat) -> a -> LinArray a
linFreeze : forall (a : Type). (1 arr : LinArray a) -> Array a        -- O(1), result ω
linFree   : forall (a : Type). (1 arr : LinArray a) -> Unit           -- explicit destructor
```

### 4.5 Concurrent `TArray` (deferred; only for cross-fiber sharing)

A `TArray` wraps the multi-fiber `TVar` machinery (a `K_FGN` handle journaled
by the kappart2 scheduler, `runtime/stm.c`), as either one `TVar` holding the
whole array, or per-slot `TVar`s for fine-grained conflict detection. Per
§18.1.13. **Not** needed for the single-threaded hot loop, and orthogonal to the
linear story.

---

## 5. Runtime representation

### 5.1 The `K_ARRAY` tag — `K_REF` generalized from 1 cell to N

Current `Ref` storage is a `KRefCell*`: a mutex plus one owned `KValue*`
occupant. Private refs use direct owned get/set under the S4 thread-local
invariant; shared refs take the cell lock while acquiring or replacing the
counted occupant. **An array is the N-slot sibling of that storage discipline,
as a SINGLE object** — not N separate `Ref` boxes (that would be N allocations,
no length, and no locality).

Add to the `KTag` enum and the `KValue` union in `runtime/kappart.h`, beside
`as.ref` and `as.fgn`:

```c
K_ARRAY,   /* mutable array: length-prefixed slab; elemkind picks the rep (§5.3) */
/* ... in the union: */
struct { void *elems; int64_t len; int64_t cap;
         uint8_t elemkind; uint8_t element_size; } arr;
```

`elems` is the storage base. In the current boxed runtime it points at a
small array box containing a mutex plus the `KValue*` slots; the slots are
scanned and have the same owned-transfer/drop-barrier discipline as `K_REF`.
Private arrays use direct slot access under the S4 thread-local invariant;
shared arrays take the storage lock while acquiring or replacing a counted
owner. The future scalar slabs remain direct `kgc_alloc_atomic(len *
element_size)` buffers (§5.2/§5.3). `len` makes `arrayLen` O(1) and pure.

**`elemkind` and `element_size` are FIRST-CLASS from Stage A — not "ignored
seeds."** They are the discriminator the load/store path dispatches on and the
flag that selects the GC-alloc entry point (§5.2). The boxed slab is just
`elemkind == BOXED` (`element_size == 8`); shipping boxed-first means *every
array is born BOXED*, but the field that will say INT64/DOUBLE already exists,
so the unboxed slabs are a new prim + a new dispatch arm, NOT a struct change.
`elems` is typed `void *` (not `KValue **`) precisely so the same struct holds a
`KValue*[]`, an `int64_t[]`, or a `double[]` without reinterpretation games. `cap`
remains the growth seed (ship `cap == len`).

Ops mirror `kref_new`/`kref_get`/`kref_set` in `runtime/value.c` with the same
`kis_imm(v) || v->tag != K_ARRAY` tag guard:

```c
/* BOXED slab (Stage A): elems = kgc_alloc(n*sizeof(KValue*)) [SCANNED], fill init */
KValue *karr_new(int64_t n, KValue *init);
KValue *karr_get(KValue *arr, int64_t i);             /* O(1): returns an owned slot value */
KValue *karr_set(KValue *arr, int64_t i, KValue *v);  /* O(1): owned-transfer store + drop-old */
int64_t karr_len(KValue *arr);                        /* O(1): arr.len                   */

/* UNBOXED scalar slabs (following stage): elems = kgc_alloc_atomic(n*8) [UNSCANNED].
 * The boxed-API entry points box/unbox at the boundary (kint/kdbl, kunbox_*);
 * the scalar-worker fast path reads/writes the raw word with no box (§5.3.4). */
KValue *karr_new_i64(int64_t n, int64_t init);   double  karr_get_dbl(KValue *arr, int64_t i);
int64_t karr_get_i64(KValue *arr, int64_t i);    /* raw word, for the scalar worker     */
void    karr_set_i64(KValue *arr, int64_t i, int64_t v);   /* raw word, no box           */
KValue *karr_new_dbl(int64_t n, double init);    void karr_set_dbl(KValue *arr, int64_t i, double v);
```

The boxed `karr_*` ops mirror `kref_new`/`kref_get`/`kref_set` in
`runtime/value.c`, with the same `kis_imm(v) || v->tag != K_ARRAY` tag guard.
The scalar `karr_*_i64`/`_dbl` ops are the following stage;
their *existence in the API surface from the start* is what makes the seam
first-class — the boxed prim never needs reshaping when they arrive.

### 5.2 GC correctness — the binding constraint

Boehm runs with `GC_set_all_interior_pointers(0)` set **before** `GC_INIT`
(`runtime/gc.c`): the collector roots only **base**
pointers, and the immediate-tag contract requires 8-byte alignment with the low
3 bits free (`runtime/kappart.h`; asserted at startup by
`krt_assert_gc_alignment` in `runtime/gc.c`). The two public allocators are
`kgc_alloc` = `GC_MALLOC` (scanned) and `kgc_alloc_atomic` =
`GC_MALLOC_ATOMIC` (NOT scanned). Three hard rules, all
non-negotiable — and the FIRST is the explicit, `elemkind`-driven
performance+correctness property at the heart of the unboxing design:

1. **The alloc entry point is chosen BY `elemkind`/`element_size`, and the choice
   is BOTH a correctness and a performance property.**
   - **BOXED slab → non-atomic `kgc_alloc` (SCANNED), NEVER atomic.** Every slot
     is a base `KValue*`, so element liveness is correct for free with no custom
     mark routine — traced exactly like `K_REF`'s cell (`value.c`) and
     `K_CTOR`'s args (`value.c`). If a boxed slab were allocated atomic (the
    `kgc_alloc_atomic` / `alloc_val_atomic` path in `runtime/value.c`,
     used for byte/scalar LEAVES that hold no pointers), live elements would be
     **collected out from under the array** — a use-after-free. So a boxed slab
     MUST be scanned.
   - **INT64 / DOUBLE slab → atomic `kgc_alloc_atomic` (UNSCANNED), NEVER
     non-atomic.** These slabs hold **raw machine words, no pointers** — there is
     nothing for the collector to trace. Scanning them is wrong-in-principle
     (a raw `int64`/`double` bit-pattern that happens to look like a heap
     address would **falsely retain** an unrelated object — the classic
     conservative-GC false-retention leak) AND wasted work (scanning N words that
     are provably non-pointers on every collection). So a scalar slab MUST be
     atomic.

   The single field that decides this — `elemkind` (and the matching `element_size`
   / `karr_new` vs `karr_new_i64`/`_dbl` entry point) — is therefore a GC-safety
   invariant, not a hint. **Scan-vs-atomic MUST track `elemkind` exactly; a
   mismatch in either direction is a memory bug** (boxed-atomic = collected live
   elements; scalar-non-atomic = false retention + wasted scan). This is the
   array-level statement of the same rule the runtime already follows: pointer-
   bearing values (`K_REF`, `K_CTOR`) use `kgc_alloc`; pointer-free leaves
   (`K_BYTE`, `K_BYTES`, `K_DBL`, `K_CHR`) use the atomic path
   (`runtime/value.c`).

2. **Store the buffer BASE pointer in the box and index via `base + i*element_size`.**
   Never hand the GC only an interior/offset pointer — interior-pointer
   recognition is OFF (`gc.c`), so an interior-only reference would not keep
   the block alive. The base is in `arr.elems`; every index is computed from it.

3. **Scan-safety of immediates in a boxed slab.** Immediate-tagged small Ints /
   nullary ctors (b001/b010, Stage 1) stored in a SCANNED boxed slab are already
   scan-safe by the low-3-bits contract in `runtime/kappart.h`: an odd word is
   treated as a non-pointer and never followed. (The unboxed INT64 slab side-steps
   this entirely — it is unscanned and holds the bare untagged `int64`.)

### 5.3 Element unboxing — a FIRST-CLASS concern (boxed ships first, but the seam is built in)

Unboxing is NOT a vague "later slab swap." It is the headline performance
property of `K_ARRAY`, designed in from day one. The boxed slab shipped first
because it is the uniform representation that can hold every current `KValue`
word, including b000 heap pointers and b001/b010/b011 immediates; scanned Boehm
slabs are safe because immediate words are non-pointers by the low-3-bit tag
contract. The representation tag (`elemkind`), the `element_size`, the GC-alloc
choice, and the backend specialization boundary all exist from Stage A, so the
unboxed scalar slabs land as a following stage with zero `K_ARRAY` redesign (§7).

#### 5.3.1 THE CRUX — sound unboxed-rep selection under erasure (no monomorphization)

The element type `a` is a `forall (a : Type)` = **quantity-0 erased** parameter
(§4.1): KBackendIR lowering uses the shared `Repr.erasedSpinePositions`
erasure verdict to omit it before codegen, so it **never reaches the `kpf_*`
op**. The runtime op CANNOT inspect `a` to choose a slab rep. The
question is: *where does the element kind come from soundly?* There are exactly
two candidate sources, and only one is sound.

**SOURCE 1 — COMPILE-TIME, at the array-op call site, PRE-erasure = SOUND, the
chosen mechanism.** The backend holds the typed `Term` *before* erasure runs, so
it knows the element type at every `newArray`/`arrayRead`/`arrayWrite` call site.
It emits a **SPECIALIZED prim** when the element type is a known UNIFORM
unboxable scalar, else the generic boxed prim:

```
element type head        emitted prim                              slab
  Double / Float    →    __newDoubleArray / __read… / __write…     raw double[]   (DOUBLE)
  Int / Nat / Integer →  __newInt64Array  / __read… / __write…     raw int64[]    (INT64)
  anything else     →    __newArray       / __arrayRead/__arrayWrite  KValue*[]   (BOXED)
```

This is **the existing scalar-worker mechanism applied to arrays**, not a new
analysis. The scalar worker already decides "is this type head an unboxed scalar?"
in exactly one place — `Repr.scalarRep` (`Repr.hs`), which matches a
bare fully-applied primitive type head (`VGlobN T []`) against the canonical
prelude numeric globals via `primScalarRep` (`Repr.hs`: `RepInt` for
`Int`/`Nat`/`Integer`, `RepDouble` for `Double`/`Float`), and `RepBoxed`
otherwise. The array call-site specializer calls the SAME `Repr.scalarRep` on the
*element type's* whnf head and maps its `Rep` to the prim family:

- `RepInt`    → the `__*Int64Array` family (INT64 slab),
- `RepDouble` → the `__*DoubleArray` family (DOUBLE slab),
- `RepBoxed`  → the generic `__array*` family (BOXED slab).

The C backend's `typeScalarKinds` (`C.hs`) already consumes
`Repr.repSelect` (`Repr.hs`) — the one authority that walks a function
type telescope — and projects each `Rep` to its `ParamKind`/`ScalarKind` via
`repScalarKind` (`C.hs`). The array element-kind decision is the same
projection applied to a single type (the element type), not a whole telescope.
The boxing/unboxing helpers `boxScalar`/`unboxScalar` (`C.hs`:
`kint`/`kdbl` to box, `kunbox_i64`/`kunbox_dbl` to unbox) are exactly the
get/set-boundary conversions the DOUBLE/INT64 slabs need on the boxed-API path
(§5.3.4).

**Why this is erasure-safe.** The chosen rep is encoded in the **prim SYMBOL
itself** (`__newDoubleArray` vs `__newInt64Array` vs `__newArray`). No `Type`, no
dict, no witness, no quantity reaches the runtime — the symbol *is* the kind. This
is the identical erasure-safety contract the AtomicRef surface already honours
(§4.1; `src/Kappa/Prelude.hs`): the opaque `data` wraps an erased-
element cell and each op forwards only values. The §31.2 KBackendIR legality
verifier sees no runtime dependency on erased data,
because the kind was resolved *before* erasure and baked into the symbol. This is
also why it is *not* the bug class that caused the prior native IO crash (an
ERASED-TYPE-APPLICATION reaching the runtime as `kapp(unit,unit)`; see the
`native-io-dict-passing-crash` memory note): nothing type-shaped is emitted at
all — a *different symbol* is.

**SOURCE 2 — RUNTIME tag-sniffing (inspect the init/element runtime tags to pick
the rep) = UNSOUND, REJECTED.** One might imagine the boxed `__newArray` op
peeking at the runtime tag of the `init` element (or the first written element)
and "upgrading" the slab to INT64/DOUBLE. This is **wrong for any sum type with a
non-uniform element representation**, and the immediate-tagging scheme makes the
failure concrete. Consider `Array (Maybe Int)`:

- `None` is a NULLARY ctor → the canonical **b010 immediate** word
  (`kctor0` → `kmk_imm_ctor` in `runtime/value.c`/`runtime/kappart.h`). It is
  not a pointer and not an `int64`.
- `Some n` is a 1-field ctor → either a **b011 packed** word (if `n` is a fitting
  immediate, per `runtime/value.c`/`runtime/kappart.h`) or a **b000 boxed
  `K_CTOR`** pointer.

So the elements of one `Maybe Int` array carry **three different word kinds**
(b010, b011, b000) — there is no single uniform machine rep. A slab rep picked
from the first element (say `None` ⇒ "looks small, use int64[]") would
mis-store every `Some (bigPointer)`. Only **monomorphic, uniform-rep element
types** (a bare `Int`/`Double` whose *every* value is the same machine word
shape) qualify — and that is *exactly* what `Repr.scalarRep` recognizes
(`VGlobN T []` with `T ∈ {Int,Nat,Integer,Double,Float}`; a type with arguments
like `Maybe Int` or `Option a` is `RepBoxed`, `Repr.hs`). Runtime
sniffing cannot distinguish "uniform scalar" from "non-uniform sum that happens
to start with a small-looking element," so it is rejected outright.

**NET.** Monomorphic scalar-element arrays (the hot numeric case —
`MutArray Double`, `MutArray Int`) unbox via backend call-site specialization;
polymorphic / sum-typed / boxed-element arrays (`MutArray (Maybe Int)`,
`MutArray a` under an abstract `a`, `MutArray String`) stay boxed and correct.
This is the **same monomorphic gating** the scalar worker already uses
(`scalarPlan`/`typeScalarKinds` reject anything but a known scalar head,
`C.hs`) — so the array unboxing inherits the scalar worker's proven
soundness boundary rather than inventing a new one.

#### 5.3.2 OPEN: how the backend NAMES and dispatches the elemkind at the call site

The mechanism above assumes the backend can recover the element type at an
array-op call site. Two threads to nail down in implementation:

1. **Where the element type is read.** `newArray`'s prim is
   `__newArray : forall (a:Type). Nat -> a -> UIO (__ArrayBuf a)` — `a` is in
   scope as the erased first telescope slot, and the *value* argument `init : a`
   pins it. For `arrayRead`/`arrayWrite` the element type is the `__ArrayBuf a`
   argument's type parameter. The specializer must read `a` from the call site's
   typed KCore spine (the `forall a` slot, before KBackendIR erasure), force it to whnf, and
   feed the head to `Repr.scalarRep`. `repSelect` already does the analogous
   read on a whole telescope; the array case is the single-type projection.
2. **A non-obvious uniform-scalar caveat.** `Repr.scalarRep` is deliberately
   conservative: a transparent prelude alias (`type Float = Double`) is unfolded
   by the elaborator before this point (`Repr.hs` matches both the
   `Double` and the `Float` alias identity to be safe), but a *user* type whose
   representation is "morally a Double" (a `newtype`-like single-field record over
   `Double`, or a units-of-measure wrapper) is `RepBoxed` and stays boxed. That is
   SOUND (never a miscompile) but leaves performance on the table for wrapper
   types; widening it is future work tied to the same layout pass that would
   unbox a single-`Double`-field record generally.

#### 5.3.3 The three slabs

`K_ARRAY` carries `elemkind` + `element_size`, set by the specialized prim
(§5.1):

| elemkind | slab type    | element_size | alloc (§5.2)          |
|----------|--------------|--------------|------------------------|
| BOXED    | synchronized `KValue*[]` box | 8 | non-atomic `kgc_alloc` (scanned) |
| INT64    | `int64_t[]`  | 8            | atomic `kgc_alloc_atomic` (unscanned) |
| DOUBLE   | `double[]`   | 8            | atomic `kgc_alloc_atomic` (unscanned) |
| (future) BYTE/BIT | packed bytes | 1 / sub-byte | atomic | — for `Bool`/small-enum |

Indexing is uniform: `addr = base + i * element_size`, with an
`elemkind`-dispatched load/store (a `KValue*` load for BOXED, a raw `int64_t`/
`double` load for the scalar slabs). The packed BYTE/BIT slab for `Bool` /
small-enum (`RepImmCtor` in `src/Kappa/Backend/Repr.hs`) is a natural future elemkind —
the same call-site mechanism would emit it when `Repr.scalarRep`/the ctor-layout
table reports a nullary-immediate element — but it is out of scope for the first
unboxed stage (INT64/DOUBLE).

Relation to the immediate-tagging scheme (`runtime/kappart.h`): a
b001 immediate `Int` rides INSIDE a `KValue*` word as `(value << 3) | KIMM_INT`
(`kmk_imm_int`) and is recovered with an arithmetic
`>> 3` (`kimm_int_val`). The **INT64 slab is the raw machine word
WITHOUT the 3-bit tag** — a plain `int64_t[i]`, the full 64-bit value, no shift,
no `KIMM_INT` tag, no `K_INT` box. The boxed slab would instead hold either a
b001 immediate `Int` word or a b000 `K_INT` pointer per element; the INT64 slab
strips both encodings down to the bare integer. That is the whole point: the
unboxed slab is denser (no per-element box, no per-element tag dance) AND the
scalar-worker fast path reads/writes it with no immediate-decode step (§5.3.4).

#### 5.3.4 READ/WRITE semantics + the scalar-worker pairing (the "extremely performant" path)

The get/set behaviour is `elemkind`-dispatched, and the DOUBLE/INT64 slabs have
TWO read/write paths — a boxed-API path and a scalar-worker fast path:

- **BOXED slab.** `read` returns an owned duplicate of the stored `KValue*`;
  `write` consumes the owned incoming `KValue*`, stores it, and drops the
  displaced occupant exactly once. Exactly `kref_get`/`kref_set` (`value.c`)
  generalized to N cells: direct on private arrays, locked on shared arrays.
  No representation conversion.

- **DOUBLE / INT64 slab, BOXED-API path** (a one-off `arrayRead`/`arrayWrite`
  outside a hot loop): `read` loads the raw scalar from the slab and
  **RE-BOXES** it into a `KValue` (`boxScalar`, `C.hs`:
  `kint(slab[i])` / `kdbl(slab[i])`); `write` **UNBOXES** the incoming `KValue`
  to a raw scalar (`unboxScalar`, `C.hs`: `kunbox_i64`/`kunbox_dbl`)
  and stores it. Critically, **storage stays unboxed** — 8 bytes/element, NO
  per-element heap box — even though the API boundary trades in `KValue`s. So
  even the slow path already wins the per-element allocation (a boxed slab of
  `K_INT` would be N+1 allocations; the INT64 slab is 1).

- **DOUBLE / INT64 slab, SCALAR-WORKER FAST path** (a hot loop over the array —
  the demanded case): when an array `read`/`write` sits inside an unboxed scalar
  worker (`compileScalarWorker`, `C.hs`+; the LLVM function scalar-worker
  path around `LLVM.hs`+), `read` feeds the **RAW** scalar (`slab[i]`, an
  `int64_t`/`double` C local) directly to the worker's arithmetic with NO box,
  and `write` stores the worker's raw scalar result into `slab[i]` with NO box.
  The worker already keeps its values in raw C locals (`int64_t`/`double`) that
  LLVM lowers as scalar SSA values, so an **unboxed
  numeric array + the scalar worker = an end-to-end unboxed hot loop with ZERO
  per-element allocation** and no per-element tag/immediate decode. This is the
  intended analogue of an evidence-preserving scalar optimization, not a
  precedent for evidence-oblivious surface `var` lowering. The obsolete pre-S2.3b scalarized
  var-ref peephole is retired because it bypassed the checker-selected
  `MonadRef` evidence; any replacement must prove it is semantically equivalent
  to the selected `newRef`/`readRef`/`writeRef` actions before lowering to raw
  locals. For arrays, the analogous future
  peephole is an array read/write lowering that, while `gsScalarRegion` (or the
  LLVM scalar-loop body) is active, reads/writes `slab[i]` instead of re-boxing.
  This is the
  "extremely performant" path the design is built around; it is why the
  `elemkind`/`element_size` seam must exist from Stage A even though the boxed
  slab ships first.

#### 5.3.5 Monomorphic gating recap

Both the boxed-API and scalar-worker fast paths above only ever exist for a slab
whose `elemkind` is INT64/DOUBLE, which is set ONLY by a specialized prim, which
is emitted ONLY when `Repr.scalarRep` reports a uniform scalar element at the
call site (§5.3.1). Never attempt scalar packing while the element type is an
erased type variable or a sum/applied type (RuntimeErased discipline; the same
`Repr.scalarRep` ⇒ `RepBoxed` gate the scalar worker uses).
`Array a` and `SizedArray n a` share this representation (§29 permits it,
with `n` erased).

### 5.4 GC/Perceus migration

- **Original Boehm-only path:** the array object and the slab are two `GC_MALLOC`s;
  element retain/drop is automatic; `set` just overwrote a slot (the old element
  became unreachable iff no other root held it); no Perceus barrier existed on
  that path.
- **Current S4 C/runtime path:** `K_REF`, `TVar`, and `K_ARRAY` containers remain
  outside the FREESET as retained mutable shells/cycle sources, but their boxed
  occupants are counted. `get` returns an owned occupant; `set`/write barriers
  store the owned new occupant and drop the displaced slot reference, including
  the self-assignment case where the drop consumes the incoming owned duplicate
  while leaving the slot live. Private storage uses direct S4 thread-local access;
  shared storage uses the storage lock while acquiring or replacing the owner.
- **Future (Perceus precise container RC, post-LLVM-layout):** the array carries a header
  RC. `set` on a **unique (RC==1)** array mutates in place AND drops the old
  slot value / retains the new (the Koka/Lean discipline) — the FBIP reuse win;
  `set` on a **shared** array copies. The **linear `LinArray`** (Option A)
  discharges the is-unique obligation **at compile time** (quantity 1), so its
  `set` needs neither the RC branch nor dup/drop traffic — it stays the cheapest
  path even under precise RC. The `elemkind` byte is also the seed of the
  per-slot pointer-vs-scalar metadata Perceus needs — and it *interacts cleanly*
  with the scalar slabs: a **scalar (INT64/DOUBLE) slab has NO per-element
  retain/drop at all** (the words are not pointers), so its FBIP in-place `set`
  is a bare store with no RC traffic, while a boxed slab's in-place `set` must
  drop-old/retain-new. So the unboxed-element design *reduces* the Perceus work,
  it does not complicate it. Until precise container/cycle reclamation lands,
  Boehm remains the safety net for the mutable container shells, not for every
  strict immutable occupant stored in them.

- **Double-unboxing is an ARRAY-LEVEL win available BEFORE general LLVM-layout
  Double unboxing.** A scalar `Double` is, today, a boxed `K_DBL` leaf
  (`alloc_val_atomic(K_DBL)` in `runtime/value.c`) — Doubles are not
  yet immediates (the b001/b010/b011 immediate kinds are Int/ctor only,
  per `runtime/kappart.h`; a future immediate Double would need a b1xx kind or
  NaN-boxing, deliberately deferred per the tagging research). The **DOUBLE slab
  IS the array-level Double unboxing**: a `MutArray Double` stores N contiguous
  raw `double`s with zero `K_DBL` boxes, achieving for arrays the density that
  scalar Double unboxing will later achieve for individual values — and it lands
  with the rest of the scalar-slab stage, not gated on the LLVM-layout Double
  work. The two efforts share the `Repr.RepDouble`/`scalarRep` classification
  (`Repr.hs`) but are independently shippable.

---

## 6. Indexing discipline — staying total

Kappa is total (§15): totality is a property of
*transparent definitions / compile-time conversion*, and effectful runtime
computations MAY fail in the Cause/Defect channel (§18.1.2-18.1.3). **A panic is
an IO effect, not partiality.** So adopt the **three-tier** discipline the spec
already half-specifies for the immutable array (mirroring Lean's `a[i]` /
`a[i]?` / `a[i]!`):

1. **Proof-carrying total (PRIMARY).** `arrayRead`/`arrayWrite` carry an
   **erased** `(i < arrayLen arr) = True` witness, copying the existing
   `arrayIndex`/`sizedArrayIndex` shape in §29. Under
   §31.2 the proof erases to nothing — `subst`/
   `pathInd` compile as type-directed coercion, not a runtime branch — so the
   emitted code is a **bare O(1) load/store with NO bounds check**. This is the
   Lean `a[i]` / Idris2 `Fin n` discipline, and it is the spec's chosen design.

2. **Option-returning (ERGONOMIC, proof-free).** `arrayReadOpt : ... -> UIO
   (Option a)` returns `None` out of bounds — total because `Option` absorbs the
   partiality (mirrors §29 `arrayGet : Array a -> Nat -> Option a`).

3. **Bounds-throwing (RUNTIME FLOOR ONLY).** The `kpf_*` prim itself bounds-
   checks and `krt_fail`s on OOB (exactly like `__arrayIndexUnsafe` and
   `kref_get`'s tag check). This raises a `Defect` in the IO channel
   (§18.1.2-18.1.3). **CRITICAL:** throwing is acceptable ONLY on
   the effectful/IO path, **NEVER** as a pure total function. The pure total
   path MUST be proof-carrying (tier 1); only IO/Eff may panic.

`newArray : (n : Nat) -> a -> ...` is total for all `n` (a `Nat` cannot be
negative, so there is no ill-formed length by construction).

---

## 7. Staged implementation plan

Each stage is independently testable. Land them in order. **The governing
principle: `K_ARRAY` is UNBOXING-READY from day one.** Stages A–G ship the boxed
slab, but every one of them is SHAPED so the unboxed scalar slabs (Stage H) are a
purely additive change — a new `elemkind`, new prims, a new dispatch arm — with
**NO `K_ARRAY` redesign** between stages. The representation tag and the
specialization seam exist from Stage A.

### Stage A — runtime representation + ops (born unboxing-ready)
- `runtime/kappart.h`: add `K_ARRAY` to the `KTag` enum and the
  `as.arr` union member beside `as.ref`. The struct carries
  `elemkind` + `element_size` FROM THE START (§5.1) — `void *elems` (not
  `KValue **`) so the same box later holds `int64_t[]`/`double[]` with no
  reshape. Boxed = `elemkind == BOXED`, `element_size == 8`.
- `runtime/value.c`: add `karr_new`/`karr_get`/`karr_set`/`karr_len` right
  after `kref_*`, each with the `kis_imm || tag !=
  K_ARRAY` guard. The boxed slots are scanned; `karr_get` duplicates directly
  while the array is private and under the lock once it is shared. `karr_set`
  mirrors that split, dropping the displaced occupant exactly once. Leave the scalar
  `karr_*_i64`/`_dbl` entry points UNwritten but their *shape* designed (§5.1)
  so Stage H slots them in beside the boxed ops.
- **Grep every `K_REF` case site** (`show.c`, any GC-trace switch,
  rep-equality) and add a `K_ARRAY` case beside each — a missing case silently
  mishandles the new tag. This is the one easy-to-miss risk.

### Stage B — prim entry points + registration (the specialization seam)
- `runtime/prims.c`: add `kpf_io_newArray`/`arrayRead`/`arrayWrite` and the
  pure `kpf_arrayLen` next to the `kref` block. Each sees only
  `a[0]`, `a[1]`, ... values (no type, no dict).
- `src/Kappa/Backend/C.hs`: register them in `primEntries` next to `newRef`
  and the **AtomicRef rows** — copy those
  rows verbatim as the template: `PrimEntry "kpf_io_newArray" 2 True`,
  `... "kpf_io_arrayRead" 2 True`, `... "kpf_io_arrayWrite" 3 True`,
  `... "kpf_arrayLen" 1 False`. The `forall (a : Type)` is Q0 and is omitted by
  KBackendIR lowering before codegen, exactly as for STM's
  `forall (a : Type)` signatures — **no type/dict/proof ever reaches a `kpf_*`
  symbol** (the erasure-safety contract, §31.2, the prior-crash class).
- **SHAPE the specialization seam now (even though only the boxed prim is
  emitted):** the call-site lowering of `newArray`/`arrayRead`/`arrayWrite` must
  go through one helper that reads the element type from the typed spine and
  picks the prim family. In Stage A–G that helper always returns the boxed
  family; Stage H makes it consult `Repr.scalarRep` (§5.3.1). Putting the
  element-type read in place now means Stage H changes ONE function, not the
  whole lowering. Register the `__*Int64Array`/`__*DoubleArray` `primEntries`
  rows in Stage H beside the boxed ones (same `PrimEntry` shape).

### Stage C — C backend (boxed correctness + action lowering)
- The general IO-prim path already emits `knative_sat(kpf_io_*, args, 1)` for
  any `PrimEntry _ _ True`, so the ops get correct lowering for free.
- **Perf delta:** keep array operations on the ordinary action-lowering path,
  and add any direct-cell fast path at the action builder/codegen point that
  already sees the `MonadRef`/array operation. Do not route this through a
  value-position IO extraction: that is not part of the spec model, and backend
  optimizations must not synthesize or depend on it.

### Stage D — LLVM backend (boxed)
- Mirror the same action-lowering recognitions in LLVM so both backends agree.
  Default IO-prim lowering already covers correctness; any inline path is a
  perf-only delta and must stay on the explicit action/`MonadRef`
  representation.

### Stage E — prelude API
- Add a `std.array.mutable` module (or fold into `std.prelude`) following the
  **AtomicRef wrapper shape** (`src/Kappa/Prelude.hs`): opaque
  `data MutArray (a) = MkMutArray (buf : __ArrayBuf a)`, the `__array*` prims
  declared with `forall (a : Type)` erased signatures, and the §4.2 total
  surface (proof-carrying + Option). Then `ST`/`STArray` per §18.6.4 (Stage E2).

### Stage F — parity tests (boxed)
- Add cases under `test/native/cases` with expected output in
  `test/native/expected`. **Run BOTH** `test/native/llvm-parity.sh` (C vs LLVM
  vs interpreter agreement) **AND** `run-native-tests.sh`. Per the
  `backend-verify-native-perf-gates` memory note, parity alone passes on
  correct-but-boxed regressions; `run-native-tests.sh` has the scalar-worker/
  alloc perf gates that catch a slow array.

### Stage G — benchmark (the unboxing target)
- Add an array micro-bench under `test/native/bench` (sum-of-N, fill-then-read,
  in-place map) comparing against the cons-list `Array`, wired through
  `bench.sh` (gated by `$KAPPA_GC_STATS`, `gc.c`, for the alloc count),
  to demonstrate the O(1) win and guard the Stage C/D inline fast path against
  regression. Bench a `MutArray Double`/`MutArray Int` loop specifically — this
  is the bench that will SHOW the Stage H unboxing win (allocation count drops
  to O(1) once the scalar slab lands).

### Stage H — UNBOXED scalar slabs (the first-class unboxing payoff)
This is a SEPARATE, FOLLOWING stage — gated exactly like the scalar worker —
that adds the INT64/DOUBLE slabs WITHOUT touching the `K_ARRAY` struct or the
boxed ops:
- `runtime/value.c`: add `karr_new_i64`/`karr_get_i64`/`karr_set_i64` and the
  `_dbl` trio, allocating `elems` with **atomic** `kgc_alloc_atomic` (§5.2 rule
  1) and setting `elemkind = INT64`/`DOUBLE`. Boxed-API `get`/`set` box/unbox at
  the boundary (`boxScalar`/`unboxScalar`, `C.hs`).
- `runtime/prims.c`: add the `kpf_io___newInt64Array`/`…DoubleArray` and
  read/write entry points; register their `primEntries` rows (Stage B seam).
- `src/Kappa/Backend/C.hs` + `LLVM.hs`: turn the Stage-B element-type helper on
  — consult `Repr.scalarRep` (`Repr.hs`) on the element type and emit
  the `__*Int64Array`/`__*DoubleArray` family for `RepInt`/`RepDouble`, the
  generic boxed family for `RepBoxed` (§5.3.1). **Wire the scalar-worker fast
  path:** when an array read/write sits in a scalar region (`gsScalarRegion`,
  `C.hs`; the LLVM function scalar-worker path, `LLVM.hs`+) lower it to a
  RAW slab access with no box (§5.3.4) — the array analogue of an
  evidence-preserving var-ref optimization, never a revival of the obsolete
  pre-S2.3b scalarized `readRef`/`writeRef` peephole.
- **Verify with BOTH `llvm-parity.sh` AND `run-native-tests.sh`** (the latter
  has the alloc/scalar perf gates `llvm-parity.sh` misses, per the
  `backend-verify-native-perf-gates` memory note — parity passes on a
  correct-but-still-boxed regression, so the Stage G bench + the perf gates are
  what prove the unboxing actually fired).

---

## 8. Pitfalls to encode now

1. **GC scan-vs-atomic MUST track `elemkind` exactly — both directions are
   bugs (§5.2 rule 1).** A boxed slab allocated atomic lets Boehm collect live
   `KValue*` elements (use-after-free); a scalar slab allocated non-atomic causes
   false retention (a `double`/`int64` bit-pattern that looks like an address
   pins an unrelated object) plus wasted scanning. Boxed slabs are non-atomic
   (`kgc_alloc`); only unboxed scalar slabs are atomic (`kgc_alloc_atomic`). The
   `elemkind`/`element_size` field IS this GC invariant, not a hint.
2. **No interior pointers to the GC.** Store the buffer base in the box; index
   via `base[i]` (`GC_set_all_interior_pointers(0)`).
3. **Erasure-safety.** The array ops take ONLY value arguments. Thread the
   `(i < len) = True` proof so the KBackendIR legality verifier
   sees no runtime dependency on erased data. This is the
   exact contract whose violation caused the prior native IO crash.
4. **MonadRef laws.** `MutArray` must obey the §18.6.1 freshness/aliasing laws
   in `docs/Spec.md`: a fresh array reachable only through its handle.
5. **Cross-fiber writes.** A plain `Ref`-style store is fine for fiber-local
   arrays; cross-fiber sharing belongs on the STM/`TArray` path, not raw
   `MutArray` (use release semantics there).
6. **Grep every `K_REF`/`KTag` switch** for a missing `K_ARRAY` case (§7
   Stage A).
7. **Read the element kind PRE-erasure, NEVER at runtime (§5.3.1).** The element
   type is erased (Q0) before codegen, so the scalar-slab decision MUST be made
   at the call site from the typed spine and baked into the prim SYMBOL
   (`__newDoubleArray` vs `__newArray`). Runtime tag-sniffing of the init/first
   element is UNSOUND for sum/non-uniform element types (the `Array (Maybe Int)`
   counterexample: `None` is b010, `Some big` is b000 — no single slab rep) and
   must never be attempted. Gate scalar packing on `Repr.scalarRep == RepInt /
   RepDouble`, the same monomorphic witness the scalar worker uses.

---

## 9. Open questions

1. **Growth (`cap` + push/pop)?** v1 is fixed-length (`newArray n`). A growable
   vector (`cap` doubling, `karr_push`) is a natural follow-up but not required
   for the totality story; defer unless a caller needs it.
2. **`freezeSized` existential ergonomics.** `exists (n : Nat). SizedArray n a`
   gives total proof-carrying reads at zero cost, but unpacking the existential
   at use sites may be clunky. Decide whether `freeze : MutArray a -> Array a`
   (with `arrayLength` re-derived) is the ergonomic default and `freezeSized`
   the opt-in.
3. **`unsafeFreeze` exposure.** Keep it strictly behind `runSTArray` (the
   skolem boundary discharges deadness). Should an IO `unsafeFreeze` exist at
   all, gated behind an `unsafe` import? Lean toward no until a measured need.
4. **STM granularity.** One `TVar` per array vs per-slot `TVar`s — defer until a
   concurrent workload demands fine-grained conflict detection.
5. **Linear `LinArray` trigger.** Land it once the elaborator's end-to-end
   linearity check is trusted for opaque handles (and ideally once Perceus can
   witness uniqueness at runtime). Until then, B + C cover the real use cases.
6. **Perceus-reuse on the immutable `Array` (Option D).** Design `arraySet`/
   `arrayMap` on the §29 immutable array to be single-owner detectable now, so
   Perceus can later make them in-place for free — making the explicit linear
   array a niche, not the main road.
7. **How the backend NAMES + dispatches the elemkind at the call site (§5.3.2).**
   The chosen mechanism reads the element type `a` from the typed array-op spine
   (the `forall a` slot / the `__ArrayBuf a` argument) PRE-erasure and feeds its
   whnf head to `Repr.scalarRep`. Open: the exact spine position to read for each
   of `newArray`/`arrayRead`/`arrayWrite`, and confirming the type survives in
   the KCore term at that point (it must be read before KBackendIR lowering
   omits the erased slot). `repSelect` already does the analogous telescope
   read; the array case is the single-type projection — but the precise
   plumbing is the first thing to settle in Stage H.
8. **Types whose uniform-scalar-ness is non-obvious (§5.3.2).** `Repr.scalarRep`
   matches ONLY a bare primitive numeric head (`Int`/`Nat`/`Integer`/`Double`/
   `Float`). A `newtype`-like single-`Double`-field record, a units-of-measure
   wrapper, or any user type that is "morally a Double" stays `RepBoxed` → boxed
   slab. SOUND (never a miscompile) but leaves perf on the table for wrapper
   types; widening it is the same future work as unboxing a single-scalar-field
   record generally (couples to the LLVM-layout pass, not this design).

---

## 10. References (verified against the tree)

- `runtime/kappart.h` — `KTag`, the 48-byte `KValue` union, `as.ref`, the
  Stage-0 tag/alignment contract, immediate-Int encoding, immediate nullary
  constructors, and packed b011 constructors.
- `runtime/value.c` — `alloc_val_atomic`/`kgc_alloc_atomic` scalar leaves,
  `kctor0`/`kctor`, `K_BYTE`/`K_BYTES`, `kref_new`, `kref_get`, `kref_set`,
  `karr_new`, `karr_get`, and `karr_set`.
- `runtime/gc.c` — `krt_assert_gc_alignment`, `GC_set_all_interior_pointers(0)`,
  `kgc_alloc`/`kgc_alloc_atomic`, and `$KAPPA_GC_STATS` allocation reports.
- `runtime/prims.c` — `kpf_io_newRef`/`kpf_io_readRef`/`kpf_io_writeRef` as
  `kref_*` templates, plus the cons-list `Array` facade whose O(n) gap this
  design closes.
- `runtime/stm.c` — multi-fiber TVar as a `K_FGN` handle, which is the TArray
  precedent.
- `runtime/atomic.c` + `src/Kappa/Prelude.hs` — `AtomicRef` as an opaque
  `__AtomicCell` wrapper whose surface ops `match`-unwrap and forward only
  values; this is the API and erasure-safety template the array surface copies.
- `src/Kappa/Backend/Repr.hs` — `Rep`, `scalarRep`, `primScalarRep`, and
  `repSelect`, which are the representation authorities the array call-site
  specializer consults.
- `src/Kappa/Backend/IR.hs` / `src/Kappa/Backend/C.hs` — KBackendIR erasure over
  `Repr.erasedSpinePositions`, plus `boxScalar`/`unboxScalar`, scalar planning,
  scalar workers, primitive registration, and do/action lowering for explicit
  mutable operations.
- `src/Kappa/Backend/LLVM.hs` — function scalar workers, including the `kwi_` /
  `kwd_` unboxed SSA paths the array scalar fast path would feed.
- `docs/Spec.md` — §12.2/§12.2.6/§12.2.7 (quantities and linear
  non-droppable/ownership-only rules), §15 (totality), §18.1.2-18.1.3 (Defect
  as IO effect), §18.1.13 (STM/TVar), §18.6.1 (MonadRef + var laws), §18.6.4
  (ST/STRef/runST), §29 (Array/SizedArray), and §31.2 (erasure and BackendIR
  legality).
- External: Marshall et al. ESOP'22 (linearity=output / uniqueness=input,
  dual); Idris2 `Data.Linear.Array` + stefan-hoeck/idris2-array (the QTT
  template); linear-base `Data.Array.Mutable.Linear`; Tweag Linear Constraints
  (O(1) freeze RW/RO tokens); Haskell `Data.Array.ST` (`runST`/`runSTArray`/
  `unsafeFreeze`); Lean 4 `Array.set`/`uset` (RC=1 FBIP), `a[i]`/`a[i]?`/
  `a[i]!`; Koka Perceus (PLDI'21, reuse/FBIP); Roc opportunistic in-place;
  OCaml float-array tag 254 / Bigarray (off-heap unscanned scalars).
