# Pervasive Laziness in Kappa — Scoping Analysis

**Question (hypothetical):** what would it take to make Kappa pervasively lazy *à la* Haskell —
every data-constructor field a potential thunk, forced on demand?

**TL;DR / recommendation:** Don't. In a **total** language pervasive laziness buys far less than it
does in Haskell — there is no ⊥ to tiptoe around, so call-by-need and call-by-value are *semantically
equivalent* on finite data and differ only in cost — while it costs a great deal: it adds allocation and
indirection (the exact opposite of the value-unboxing + Perceus direction we just chose), it is hostile to
reference counting (thunks update in place; lazy cycles leak under RC — which is a chief reason GHC uses a
*tracing* GC), and it blurs the inductive/coinductive distinction that totality checking depends on. The one
thing strictness genuinely cannot express — productive infinite structures — is far better served by
**codata (coinductive types + a productivity/guardedness checker)** layered on the explicit `Thunk`/`Need`
suspensions Kappa already has. That is the Idris 2 / Lean 4 / Agda answer (strict-by-default + opt-in
laziness + codata), and it stays Perceus-compatible. Pervasive Haskell-style laziness is a net negative for
Kappa's goals.

## Where Kappa is today
- **Strict, call-by-value end to end.** Function arguments and constructor fields are evaluated eagerly;
  nothing is thunked implicitly. (`src/Kappa/Backend/C.hs` — `kapp`/`kctor` take already-evaluated `KValue*`.)
- **Explicit suspension only.** Two library types (`docs/Spec.md:9571–9598`): `Thunk A` (by-name,
  re-evaluates on each `force`) and `Need A` (by-need, memoized). The compiler never inserts them — the
  programmer writes the suspension and the `force`.
- **No codata / coinduction / productivity checking.** Infinite structures cannot be expressed naturally
  today; every step must be hand-suspended.
- **One uniform ~48-byte boxed `KValue`** (`runtime/kappart.h:114–150`), strict fields, Boehm GC, with
  immediate-tagging (Stage 1) live and Perceus RC + value-unboxing as the planned marquee perf lever.

## Why pervasive laziness is a poor fit

### 1. Totality reframes what laziness *is*
Haskell's laziness is inseparable from ⊥: `head []`, `undefined`, nontermination — laziness is what lets you
not-evaluate them. Kappa is total: **there is no ⊥; every term terminates.** Remove ⊥ and laziness reduces
to three residual effects:
- **evaluation order** — *when* a redex reduces, not *whether* (same result either way);
- **sharing** — memoizing a value used in several places;
- **infinite structures** — expressible only with a productivity guarantee (codata).

For all *finite* data, **call-by-need and call-by-value compute the same result** in a total language; they
differ only in *cost*. Pervasive laziness therefore adds no expressive power over the finite fragment — it
only changes, and complicates, the cost model.

### 2. Infinite structures want codata, not universal thunks
The single capability strictness lacks is productive infinite data (`iterate`, `repeat`, streams). The
principled total-language construct is **codata**: coinductive declarations checked for *productivity*
(guarded corecursion) — the exact dual of inductive data checked for *termination* (`decreases`). Codata is
lazy precisely where it must be (the coinductive fields) and nowhere else. Kappa already ships the runtime
primitive (`Need`, memoized by-need); codata adds the surface types + the guardedness check. That delivers
the only real benefit of laziness at a fraction of the cost, and keeps inductive data strict, finite, and
unboxable.

### 3. It fights Perceus + value-unboxing head-on
We just chose Perceus RC + value-unboxing to *cut* allocation (Kappa is 10–250× off the leaders, dominated
by boxing). Pervasive laziness does the opposite:
- a thunk allocation per nontrivial field;
- an indirection + force-check on every field access;
- the update/blackhole protocol (overwrite the thunk with its WHNF on first force).

Worse, **laziness is hostile to reference counting**, the substrate of Perceus:
- thunks mutate in place (thunk → indirection → value); RC must track that transition and the sharing it
  creates;
- lazy knot-tying builds cyclic structures, and **cycles leak under pure RC** — you'd need a backup cycle
  collector, eroding Perceus's whole appeal;
- this is a chief reason GHC uses a *tracing* GC rather than RC.

So pervasive laziness would likely force abandoning Perceus (back to tracing GC) — discarding the marquee
lever — or solving lazy-aware RC, which is a research problem. Recovering the lost performance then needs a
full **strictness/demand analyzer**, and even then space leaks (the perennial Haskell tax) remain.

### 4. It blurs the distinction totality depends on
Totality checking rests on separating **inductive** data (finite; strict; terminating recursion) from
**coinductive** codata (infinite; lazy; productive corecursion). Making *all* constructors lazy erases that
line — you'd have potentially-infinite "inductive" values, breaking the termination/productivity machinery.
Restoring soundness means re-introducing a productivity checker for the now-lazy data — i.e. re-deriving
codata anyway, having already paid the pervasive-laziness cost to get there.

## Recommendation
- **Keep strict-by-default.** It is right for a total language and it is what Perceus + unboxing need.
- **Add codata when infinite structures are wanted** — coinductive types + a productivity/guardedness
  checker, layered on the existing `Need` (by-need) suspension. Opt-in, localized, Perceus-compatible.
- This matches the modern total/dependent lineage (Idris 2, Lean 4, Agda, Coq): strict or explicit-lazy +
  codata — *not* Haskell's pervasive laziness.

## Appendix — what pervasive laziness would actually require (if pursued anyway)
1. **Representation:** every constructor field becomes a pointer to a thunk-or-WHNF carrying an info table
   (the STG model); the strict ~48-byte `KValue` grows an update/indirection protocol.
2. **Evaluation:** a force/update/blackhole mechanism, lazy pattern matching, thunk allocation at every
   nontrivial field, entry-code/info-table dispatch.
3. **GC:** almost certainly tracing, not Perceus RC (lazy + RC is research-level) — i.e. reverse the chosen
   runtime direction; or build a lazy-aware RC plus a cycle collector.
4. **Performance recovery:** a demand/strictness analyzer to unthunk hot paths; space-leak diagnostics;
   residual unpredictability remains.
5. **Totality:** re-separate inductive vs (now-lazy) coinductive with a productivity checker — re-deriving
   codata.

**Net:** high cost, reverses the runtime strategy, and converges back on codata — which we can get directly,
far more cheaply, strict-by-default.
