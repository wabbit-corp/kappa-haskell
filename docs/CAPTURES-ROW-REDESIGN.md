# Captures as a coeffect row — §12.3.1 redesign scoping

**Verdict up front.** The current capture system (§12.3/§12.3.1) is *value-level only*: it infers capture
sets structurally per value and checks user-written `captures (...)` upper bounds, but it has no story at
**nominal or generic boundaries** — no capture polymorphism, no rule lifting a constructor's closure/thunk
field captures into the constructed type, no defined meaning for an *unannotated* demanded type, and no
latent capture row on arrows. Monads sit exactly on those boundaries, so monadic code either **launders**
captures (a borrow escapes through `bind` — unsound) or is **blocked wholesale** (`E_QTT_BORROW_ESCAPE`,
`src/Kappa/Check.hs:3025` — the current, sound-but-blocking reading; this *is* the D6 borrow-through-IO
hole). The fix is not more annotations: it is re-founding captures as an **inferred coeffect row** carried
by every elaborated type — the same architectural lane quantities already occupy — with **one implicit row
per type former**, **`cap(a)` transparency** for type variables, **subcapturing** as the only subtyping,
and a **rank-2 scope-discharge rule** at `using`/scope binders. Surface syntax is unchanged; users write no
capture annotations in the common case; every genuine escape remains an error. Rows are erased before
KBackendIR (§31.2/§34.3), so this is **front-end + spec work only** — the landed Perceus S5 backend is
untouched, and Perceus S6.A2 is *blocked on this document* (see §14).

Companion to [PERCEUS-S6-PLAN.md](../runtime/docs/PERCEUS-S6-PLAN.md) (A2 consumes this),
[KCORE-KBACKENDIR-SCOPING.md](KCORE-KBACKENDIR-SCOPING.md) (the role model: spec-first scoping before
implementation), and Spec.md §12 (quantities/borrowing/regions/captures).

## 1. What the spec has today (and keeps)

- `captures (s̄)` as a postfix annotation on **any** value type, explicitly because *"a non-function value
  may hide closures or other region-carrying values inside records, packages, or abstract data"*
  (Spec.md:12664) — the premise of this redesign is already conceded there.
- **Structural per-value inference**: a composite value (tuple, record, ctor application, injection,
  package) gets the **union** of its runtime constituents' capture sets (12690); branching forms union
  their branches (12692); user annotations are **upper bounds** (12666); subsumption is `S ⊆ S'` against an
  *annotated* demanded type (12698).
- Rigid lexically-scoped regions: bare `&` binders introduce an **anonymous** rigid `ρ`; anonymous regions
  are never writable in an annotation — a value that would need one to escape is rejected by the
  **skolem-escape rule** instead (12669, 12592-12607).
- Arrows carry an *implicit side condition* (valid only where the mentioned regions are live, 12588) — but
  no capture row in the type proper.
- Bespoke library uses that prove the need: `fork : Scope -> (IO e a captures ()) -> UIO (Fiber e a)`
  (30976), the query core's hand-threaded `QueryCore mode q item captures (ρ)` (31254-31340), existential
  packaging `exists (ρ : Region). ((Unit -> Int) captures (ρ))` (9859-9861), and §7210's requirement that
  interface-crossing lifetimes be exposed through `captures (...)`.
- "Capture metavariable" already appears in the unsolved-meta diagnostic list (2210) — the elaborator
  design anticipated inference variables; the type system never got them.
- Capture annotations are **not part of definitional equality** (12704-12706) and are **erased** under
  §31.2/§34.3 (12659). Both properties are load-bearing and are preserved by this redesign.

## 2. The four deficiencies

1. **Unannotated demanded types are semantically undefined.** Subsumption fires only against an annotated
   type. What does plain `IO a` demand in `bind : IO a -> (a -> IO b) -> IO b`? If *unconstrained*, a
   capturing action flows through and its row vanishes at the seam — the borrow escapes through the monad
   (laundering; unsound). If *`captures ()`*, no capturing action can ever be passed to `bind` — the
   observed behavior (`E_QTT_BORROW_ESCAPE`) and precisely the D6 hole. The spec never acknowledges the
   choice; the implementation picked the sound-but-blocking reading. **The failing S6.A2 regression is the
   spec working as (under-)written, not an implementation bug.**
2. **No capture polymorphism.** Capture sets are concrete sets of explicit `Region` binders; there is no
   quantification over them, so `bind`/`pure`/`traverse` cannot be capture-generic and no annotation
   discipline can fix that (call-site regions differ and are usually anonymous).
3. **No captures on data declarations.** Nothing lifts a constructor's closure/thunk-typed field captures
   into the constructed nominal type. The structural union works at construction *sites* and dies at the
   first written signature. Each capture-aware datatype currently needs bespoke spec text (`QueryCore …
   captures (ρ)`), which does not scale to `IO`, `Fiber`, `Promise`, streams with `Thunk` tails, or any
   user monad.
4. **Arrows have no latent capture row in the type.** A returned closure's captures survive only through
   local value inference, which any nominal or generic boundary severs.

Consequence (the D6 identity): a `do` action derived from an anonymous borrowed parameter has a row
containing an unannotatable `ρ`, so *any* signature crossing trips skolem escape.

## 3. Design overview — four pillars

1. **Captures are a coeffect row, not type-level sets** — a parallel lane like quantities; never in
   definitional equality; join-only algebra.
2. **One implicit row per type former + `cap(a)` transparency** — the data-declaration lifting rule and
   symbolic absorption by type variables; this is what keeps signatures clean and inference tractable.
3. **Subcapturing is the only subtyping** — a preorder from lexical region nesting plus row inclusion,
   applied only at subsumption boundaries; rows covariant, `Ref`'s row invariant, everything else
   invariant.
4. **Rank-2 scope discharge at `using`/scope binders** — the `runST` pattern, which makes borrow-using
   monadic code work with zero annotations while keeping every genuine escape an error.

Precedents, and what is taken from each: **Rust** — types are actively descriptive of the lifetimes they
capture (implied outlives-bounds; one lifetime lattice per type), which is what integrates with
HKTs/typeclasses; **Scala 3 Capturing Types (CC<:□, Boruch-Gruszecki et al., TOPLAS 2023)** — the
subcapturing order and the treatment of `cap`; we deliberately do **not** take its box/unbox discipline
(annotation noise) and use `cap(a)` transparency instead; **Koka** — join-only row inference with
generalization gives principal types; **`runST` (rank-2 state threads)** — the scope-discharge shape.

## 4. The row lane

Row syntax (elaboration-internal; surface grammar unchanged):

```text
k ::= ∅ | {ρ} | k ∪ k | κ            -- κ: capture metavariable (Spec 2210, now real)
      | cap(a)                        -- symbolic row of a type variable (§5)
```

- Every elaborated type occurrence carries a row: written `T ^ k` in this document. Rows are sets over
  rigid region variables after solving; `∪` is the only operator (no subtraction, no negation — the one
  apparent exception, scope discharge, is a *binder*, not an operator; §8).
- **Rows never participate in conversion/definitional equality** (preserves 12704-12706). Type-level
  computation cannot inspect or produce rows. Region *variables* remain ordinary dependent binders and may
  appear in types (`BorrowView ρ A` is unchanged); the *sets* stay in the coeffect lane. This is what
  avoids dependent-variance machinery entirely: a `data Foo (f : Region -> Type) (l : Region) = Foo (f l)`
  needs no transport rules for rows, because rows are not in the equational theory.
- The surface form `T captures (s̄)` keeps its exact meaning: a user-written **upper bound** on the row
  (`k ⊑ {s̄}` — subcapturing, §6). `T captures ()` demands `k ⊑ ∅`, i.e. purity. Nothing existing breaks.

The base row function `cap(·)` on type formers:

```text
cap(Int) = cap(Double) = cap(String) = ...  = ∅        -- scalars never capture
cap((q x : A) -> B)                          = the arrow's LATENT row (the closure environment's row)
cap(Thunk A) / cap(Lazy A)                   = the suspension's latent row ∪ cap(A)
cap(a)                                       = cap(a)  -- symbolic; resolved at instantiation (§5)
cap(D ā)                                     = k_D ∪ ⋃ { cap(āᵢ) | āᵢ used in a runtime field }   (§5)
```

## 5. The data-lifting rule and `cap(a)` transparency

**R1 (data lifting).** Every `data D params = C₁ f₁… | C₂ …` acquires **one implicit capture row
parameter** `k_D`. At a constructor application, `k_D` is instantiated with the **union of the rows of the
runtime-relevant fields** (the §12.3.1 structural union, now made *part of the constructed type* instead of
a value-side fact). At a pattern match, the scrutinee's `k_D` is re-exposed to the arm: a field extracted
from a `D`-value carries its contribution back out. Compile-time/erased fields contribute nothing
(preserves 12696). One row per *type* — not per field — is the deliberate Rust-style compromise that keeps
inference tractable; a per-field refinement is a compatible future extension.

**R2 (`cap(a)` transparency).** A type variable **may** be instantiated with a capturing type:
`a := T ^ s` records `cap(a) := s`. Every type former mentioning `a` already includes `cap(a)` in its row
via R1, so the captures ride along *inside* `a` and resurface at every use — nothing vanishes and nothing
must be written. This answers the "can `a := T captures (s)`?" question with **yes, tracked** — the
alternative (prohibition) is Scala's box/unbox discipline, which is sound but imposes exactly the
annotation burden Kappa is avoiding. The cost of transparency is that captures cannot be *hidden* inside
generic containers (a `List` of borrowing closures is visibly `List ^ {ρ}`); for an inference-first
language that is the desired behavior.

**R3 (arrows).** A function type carries its **latent row** — the row of its captured environment — as
part of the type (replacing the informal "implicit side condition" of 12588 with structure). The existing
postfix `((A -> B) captures (s))` is an upper bound on that latent row, unchanged.

With R1-R3, `bind` needs no capture syntax at all. The user writes and the elaborator generalizes:

```kappa
bind : IO a -> (a -> IO b) -> IO b
-- elaborated scheme (displayed only on demand):
-- bind : ∀ a b (κ₁ κ₂ κ₃ : Caps).
--        IO^{κ₁} a -> ((a -> IO^{κ₂} b) ^ κ₃) -> IO^{κ₁ ∪ κ₂ ∪ κ₃} b
-- cap(a), cap(b) ride inside IO^{…} a / b automatically via R1+R2.
```

## 6. Subcapturing — the only subtyping

**R4 (region order).** Kappa's rigid regions are lexically scoped, so region containment is *syntactic
scope nesting*: `ρ_outer ⊑ ρ_inner` when `ρ_outer`'s introducing scope encloses `ρ_inner`'s. A value
depending only on longer-lived regions is acceptable wherever one depending on shorter-lived regions is
(every use inside the inner scope is inside the outer scope). Decidable, no solver.

**R5 (subcapturing).** `S <: S'` iff every `ρ ∈ S` is a member of `S'` or `ρ ⊑`-precedes (outlives) some
member of `S'`. `∅` is bottom: `T^∅ <: T^k` for every `k` — pure values go anywhere. Reflexive,
transitive.

**R6 (where it applies, and variance policy).** Subcapturing is a **subsumption judgment** applied only at
(i) application/argument boundaries and (ii) `captures (...)` annotation checks — the same places the
existing `S ⊆ S'` rule fires. Rows are **covariant** (fewer / longer-lived captures = more general). All
other type structure remains **invariant**; the single exception is that a mutable cell's row parameter is
**invariant** (`Ref (T^k)`: reads are covariant uses, writes contravariant — same as every region system).
This "Tier 1" containment is what protects inference. **Tier 2** — full declarative subtyping with
variance over quantities and unions (`List (a -> b) <: List (1 a -> b)` and friends) — is explicitly out
of scope here; note before committing to it that the sound *direction* of quantity variance must be
derived from §12.2.7's "quantities are ownership-only" reading (for use-counts the usual sound direction
is `1`-use `<:` `ω`-use, the reverse of the folklore example).

## 7. Inference: sound, principal, and quiet

**R7 (constraint generation).** Elaboration emits row constraints exactly where §12.3 already computes
region environments: a variable occurrence contributes its binder's regions; a closure's latent row is the
union of its captured free variables' rows (16.2.1, unchanged in spirit); composites union (R1); branches
union; an application instantiates the callee's capture scheme with fresh `κ`s and flows argument rows into
parameter rows by subcapturing (R5).

**R8 (generalization — this closes deficiency #1).** An **unannotated type in a signature is
capture-generalized**, not `captures ()` and not unconstrained: at `let`/top-level, unsolved `κ`s and the
regions of borrowed parameters are generalized into the binding's capture scheme, ML-style. In particular,
a function whose result mentions a borrowed parameter's region gets the *makeGetter scheme inferred*:

```kappa
useRef : (& r : Ref Int) -> IO Int
-- inferred: ∀ρ. (&[ρ] r : Ref Int) -> IO^{ρ} Int      -- "runLoop is a lie" — not anymore
```

The signature stops lying without the user writing a region. Anonymous rigid regions remain unwritable
(12669 preserved) — they no longer need to be written, because generalization binds them in the scheme.

**Principality.** The algebra is join-only over a finite lattice; constraints are atomic `⊆`/`<:` over
unions of variables — the same class as Koka's effect-row inference: least solutions exist and schemes are
principal. This is precisely why R1 uses one row per type and why there is **no row subtraction** (§8's
discharge is a binder). Solving is a fixpoint over the do/let graph; recursion takes the least fixed point.

**Display policy (the "unwieldy" answer).** Solved-empty rows are never printed. Non-empty rows print only
(i) in diagnostics (which already must show inferred vs demanded sets, 2970-3010), (ii) at interface/
manifest boundaries (§7210 already requires exposing interface-crossing lifetimes — inferred schemes are
serialized there), and (iii) on explicit request. Day-to-day code shows no capture syntax at all.

## 8. Scope discharge — the rank-2 rule that makes it usable

**R9 (`using` / scope binders).** `using pat <- acquire` already introduces one rigid `ρ` for the protected
scope (12624-12635). Its elaboration type is now the region-rank-2 shape:

```kappa
using_ : IO^{k₁} r -> (∀ρ. (&[ρ] view) -> IO^{k₂ ∪ {ρ}} b) -> IO^{k₁ ∪ k₂} b
  -- well-formedness: ρ ∉ cap(b)  (b's row, via cap(b), must not mention ρ)
```

`ρ` is *bound* over the continuation and **discharged at the binder** — the block's row legitimately drops
`{ρ}` because the block-as-a-value re-acquires a fresh `ρ` on every run. Algorithmically this is
`(k₂ ∪ {ρ}) \ {ρ}` at the binder, which is sound *because `ρ` is rigid and bound exactly there* — it is
binding, not set subtraction on variables, so principality survives. Anything still mentioning `ρ` in the
result type is exactly the existing skolem-escape error (12592-12607), with the same diagnostics.

**R10 (monadic bind consumes rows).** Binding an action inside a `do` block **executes** it within the
current scope: `v <- (e : IO^{k} a)` contributes `k` to the *block's execution row* and binds
`v : a ^ cap(a)`. The block value's own row is, equivalently, just the ordinary closure rule (R7): the
union of the rows of its **free** variables — names bound by `using`/scope items inside the block are not
free in it. The two views agree; R10 is the itemized form the do-elaboration implements.

**R11 (skolem escape, unchanged).** The escape rule and its diagnostics are untouched — this redesign
changes *which* programs reach it (laundering becomes impossible; legitimate scoped uses no longer trip
it), not what it means.

## 9. Worked examples

**(1) The motivating loop — zero annotations, sound:**

```kappa
runLoop : (& t : Terminal) -> IO ()          -- inferred: ∀ρ. (&[ρ] Terminal) -> IO^{ρ} ()

foo : IO ()                                   -- inferred row: ∅
foo = do
  using t <- open                             -- binds rigid ρ over the rest of the block
  runLoop t                                   -- IO^{ρ} () — executed here, inside ρ (R10)
  doSomethingElse                             -- IO^{∅} ()
-- R9: block row = k_open ∪ (({ρ} ∪ ∅) \ {ρ}) = ∅; Unit's cap is ∅ so the WF side condition holds.
-- foo : IO^{∅} () — and `fork foo` is accepted, because the fiber re-acquires its own ρ.
```

**(2) The laundering direction — now impossible:**

```kappa
data Handler = MkHandler (Msg -> IO ())       -- R1: cap(Handler) = k_H, lifted from the field's arrow
mk : (& t : Terminal) -> Handler              -- inferred: ∀ρ. (&[ρ] Terminal) -> Handler^{ρ}
bad = do
  using t <- open
  let h = mk t                                -- h : Handler^{ρ}
  return h                                    -- ρ ∈ cap(result) → R9 WF fails → skolem escape ✗
```

**(3) The over-blocking direction (D6/S6.A2) — now allowed:**

```kappa
useRef : (& r : Ref Int) -> IO Int            -- inferred: ∀ρ. (&[ρ] Ref Int) -> IO^{ρ} Int
useRef r = do { v <- readRef r; return v }    -- body row {ρ} (r is free); v : Int^∅
-- Caller: using r' <- newRef 5; x <- useRef r'; …   — ρ instantiates to the using-block's region
-- and discharges at its binder (R9). The current E_QTT_BORROW_ESCAPE on this shape disappears;
-- the S6.A2 regression flips to passing. Escapes (returning the *action* out of the block) still fail.
```

**(4) Fibers stay strict:** `fork : Scope -> (IO e a captures ()) -> UIO (Fiber e a)` (30976) now demands
`IO^∅` — subcapturing admits any pure action; `fork (runLoop t)` inside a `using` block is rejected
(`{ρ} ⋬ ∅`), preserving "borrows never cross fibers". Multi-shot resumption duplicability (§18.1.20)
likewise gains a precise premise: a resumption whose row is non-empty is not duplicable.

**(5) Thunks in data (the "constructors that capture thunks" case):**

```kappa
data Stream a = SCons a (Thunk (Stream a))    -- R1 lifts the thunk's latent row into cap(Stream a)
tailFrom : (& s : Src) -> Stream Int          -- inferred: ∀ρ. (&[ρ] Src) -> Stream^{ρ} Int
-- storing that stream past the borrow's scope → skolem escape; consuming it inside → fine.
```

**(6) Existing explicit-region code is unchanged:** `makeGetter`/`packGetter` (12711-12718), `BorrowView ρ
A`, the existential packaging at 9859, and `QueryCore … captures (ρ)` keep their meaning verbatim — they
are the *explicit* spellings of what R8 now infers. The query core's bespoke rules become instances of
R1/R8 rather than special cases.

## 10. What stays unchanged (migration safety)

- **Surface grammar**: no new syntax; `captures (s̄)` remains the upper-bound form; no `fip`-style keywords
  anywhere (consistent with the S6 no-keywords decision).
- **Skolem escape** (rule + diagnostics), **anonymous-region unwritability**, **`using`'s primitive
  split**, **`fork`'s empty-capture demand**, **§7210 interface exposure** — all preserved; the redesign
  re-founds *how the checked facts are computed*, not what is forbidden.
- **Definitional equality** never sees rows (12704-06 preserved); **erasure** (12659, §31.2/§34.3) is
  unchanged — rows never reach KBackendIR, so the S5 backend, its validators, and its gates are untouched.
- The current `Captures`-as-wrapper reading of the postfix form migrates to a row constraint with identical
  user-facing meaning.

## 11. Spec-revision worklist

1. **§12.3.1 rewrite**: the row lane (§4), `cap(·)`, R1-R3, subcapturing R4-R6 (new subsection), the
   generalization rule R8 including the **explicit statement that unannotated signature types are
   capture-generalized** (closing deficiency #1 by name), and the display policy.
2. **§13/§14 data declarations**: the R1 lifting rule (one implicit row per datatype; construction
   instantiates; match re-exposes; erased fields contribute nothing).
3. **`do`/`using` elaboration**: R9 (rank-2 discharge, WF side condition) and R10 (bind consumes rows);
   cross-reference the unchanged skolem-escape rule.
4. **§16.2.1** (closure capture inference): restate as the latent-row rule R3/R7.
5. **§18**: restate `fork`'s demand as `IO^∅` via subcapturing; add the non-empty-row ⇒ non-duplicable
   premise to §18.1.20 multi-shot legality.
6. **§3.2.7 diagnostics**: inferred/demanded *rows* (the fields at 2970-3010 already anticipate this);
   capture metavariables (2210) become real and get an unsolved-κ diagnostic.
7. **Interfaces/manifests**: serialize inferred capture schemes at exported boundaries (§7210).

## 12. Implementation staging (after the spec lands; each gate conformance-clean)

| stage | what | gate |
|---|---|---|
| **C0** | the spec revision above; no implementation | reviewed; worked examples §9 all derivable on paper |
| **C1** | row lane in the elaborator, **infer-only**: rows computed and carried, current binary escape check still authoritative; differential report of would-change verdicts | conformance unchanged; the report enumerates exactly the D6-shaped acceptances and no new rejections |
| **C2** | flip enforcement: subcapturing subsumption + R8 generalization replace the binary check | conformance green; every current `E_QTT_BORROW_ESCAPE` fixture either still fails (true escapes) or is re-classified with a spec citation |
| **C3** | R9/R10 scope discharge in `do`/`using` | the S6.A2 regression flips to passing; laundering fixtures (§9.2) fail; `fork`-boundary fixtures unchanged |
| **C4** | interface/manifest scheme serialization + diagnostics polish (row printing, unsolved-κ) | round-trip: an exported inferred scheme re-imports to the same scheme |

The C1 differential mirrors the Boehm-backstop/observe-only discipline that de-risked Perceus S2→S3 and
S5.A: compute the new facts beside the old authority, diff, then flip.

## 13. Risks

- **R-inference-surprise.** Row generalization changes which programs elaborate; a too-eager `κ` could
  accept a laundering shape. Guarded by C1's differential (every verdict change enumerated before
  enforcement) and by keeping the algebra join-only (no operator can *remove* a region except the R9
  binder).
- **R-trait/HKT integration.** Dictionary methods carry capture schemes; instances over capture-indexed
  types must instantiate them per use. `cap(a)` transparency is designed to make `Monad m` work without
  row-indexed kinds, but this is the area to prototype first in C1.
- **R-diagnostic quality.** Rows in errors must name the borrow-start and escape site as today (3.2.7);
  a raw "κ₃ ⋬ ∅" is not acceptable output. Budget diagnostics work in C2/C4.
- **R-tier2-pressure.** Subcapturing will invite requests for full variance (quantities, unions). Hold the
  Tier-1 line in this arc; Tier 2 is its own future scoping doc with the §12.2.7 direction question
  settled first.
- **R-corpus-migration.** Existing conformance fixtures asserting `E_QTT_BORROW_ESCAPE` on D6 shapes flip
  by design in C3; each flip must cite the R9/R10 rule that legalizes it — no silent expectation edits
  (the house rule: never weaken a test without a spec citation).

## 14. Relation to Perceus S6

- **S6.A2 (borrow-through-IO) is blocked on this document** and then *implemented by* C1-C3. Its failing
  `E_QTT_BORROW_ESCAPE` regression is kept as the pinned D6 witness (expected-fail/report-only) until C3
  flips it. No IO-special-casing, no relaxation of the escape check outside this design.
- **S6.A1** (the backend borrow-escape validator) is independent — it reads `boBorrowed` + representation
  off KBackendIR nodes and defends storage/return sinks; rows never reach the backend.
- **S6.B (inferred FIP)** benefits directly: the uniqueness analysis's "no aliasing use between drop and
  reuse" premise can consume row facts (a borrowed read is visible as such), and the no-keywords stance is
  shared.

## Literature anchors

- **Capturing Types / CC<:□** — Boruch-Gruszecki, Odersky, et al. (TOPLAS 2023): subcapturing, `cap`;
  we replace boxing with `cap(a)` transparency.
- **Rust** — lifetimes in types, implied outlives-bounds, per-type lifetime parameters: the "types describe
  what they capture" discipline (R1/R2) and the `Ref`-invariance point.
- **Koka (Leijen)** — join-only row-effect inference with principal schemes: the R7/R8 algorithm class.
- **Lazy Functional State Threads** (Launchbury & Peyton Jones) — the rank-2 discharge shape of R9.
- **FP² / Perceus** (Lorenzen, Leijen, et al.) — the S6 consumer of these facts (borrowing + inferred FIP).
