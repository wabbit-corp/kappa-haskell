# Masking `restore` Rank: Provenance, Rationale, and Recommendation

**Status:** decision study for the `[DECISION-NEEDED]` item at
`docs/ANALYSES-AND-SPEC-BACKPORT.md:139-158` (also a "Load-bearing user decision",
line 335).

**The fork.** Spec §18.1.12 (`docs/Spec.md:19063-19066`) mandates a **rank-2**
`restore`:

```
mask : forall (e : Type) (a : Type).
       ((restore : forall (x : Type). IO e x -> IO e x) -> IO e a) -> IO e a
```

The implementation ships **rank-1** — `__mask`'s `restore` is monomorphic
`IO e a -> IO e a`, instantiated at the mask's own result type `a`
(`src/Kappa/Prelude.hs:561-566`). So the impl is **non-conformant as written**.
The question: relax §18.1.12 to rank-1 (BACKPORT), or keep rank-2 and fix the impl
(CONFORMANCE-FIX)?

**Bottom line (decisive): keep rank-2; do the CONFORMANCE-FIX. This OVERTURNS the
backport note's relax-to-rank-1 recommendation.** The note's load-bearing premise —
that the rank-2 generality is "essentially never exercised" by idiomatic code — is
**false going forward**. It was generalized from the rank-1-safe subset
(`bracket`/`finally`), but the canonical mask idiom (one `restore` applied to
differently-typed sub-actions) is rank-2-essential across the entire Haskell →
Cats-Effect → ZIO lineage Kappa's `IO` descends from, and rank-1 **rejects it at
typecheck** — confirmed by compiling minimal Kappa counterexamples.

---

## 1. Provenance — where the rank-2 `restore` came from

### 1.1 Internal (Kappa repo + git history): an unmotivated, uncited import

The Kappa repo records **no standalone, Kappa-specific rationale** for rank-2:

- **Born rank-2 on day one, never edited.** `git blame -L 19063,19066 docs/Spec.md`
  attributes all four lines of the `mask`/`restore` block to a single commit —
  `c10a8e2` "Initial Kappa Haskell implementation scaffold" (Sir Wabbit,
  2026-06-11) — and `git log -L 19063,19066:docs/Spec.md` returns that one commit.
  There is no separate "introduction commit" carrying a design message to mine.
- **No in-section justification.** §18.1.12's prose (`Spec.md:19091-19092`) states
  *what* `restore` does ("re-enables interruption for a selected subcomputation")
  but never *why* it is polymorphic over `x`.
- **No external citation.** Grepping the spec for `ZIO` / `cats-effect` /
  `Control.Exception` yields zero hits near §18.1.12. The rank-2 shape is an
  uncited, unattributed mirror of the conventional GHC idiom.
- **The spec's only argued rank-2 rationale is for a *different* construct** —
  `runST` (§18.6.4, `Spec.md:21271-21288`, "Escape Prevention via Rank-2
  Polymorphism"), which uses `forall (s:Type)` for **skolem escape prevention**.
  That mechanism does **not** transfer to `restore`, whose `forall (x:Type)`
  quantifies the action's *result type for reuse-at-any-type*, not for skolem
  blocking. So the one place the spec defends rank-2 is non-transferable here.

**Internal provenance verdict:** rank-2 was scaffolded in as an inherited copy of
the standard `mask` shape with no documented Kappa-specific design intent. There is
no in-repo rationale that relaxing would "betray." *This is the strongest point in
the backport note's favor* — and it is genuine. But "no recorded rationale" is not
"no rationale": the external lineage supplies a precise, load-bearing one (§2).

### 1.2 External lineage: the rank-2 is universal and deliberate

Kappa's spec line is a **character-for-character transliteration** of GHC's
`mask`, inherited through the exact effect-system family a ZIO-flavored `IO`
descends from:

| Library | Signature (restore/poll capability) | Rank |
|---|---|---|
| **Haskell** (origin) | `mask :: ((forall a. IO a -> IO a) -> IO b) -> IO b` (also `uninterruptibleMask`) | rank-2 |
| **Cats-Effect** | `def uncancelable[A](body: Poll[F] => F[A]): F[A]`; `trait Poll[F[_]] extends (F ~> F)` (apply is `[A](fa: F[A]): F[A]`) | rank-2 |
| **ZIO** | `def uninterruptibleMask[R,E,A](f: InterruptibilityRestorer => ZIO[R,E,A])`; restorer `apply[R,E,A](effect): ZIO[R,E,A]` | rank-2 |
| **Kappa** | `((restore : forall (x:Type). IO e x -> IO e x) -> IO e a) -> IO e a` (`x=a`, `a=b`) | rank-2 |

Kotlin (`withContext(NonCancellable)`) and OCaml 5 Eio (`Cancel.protect`) are the
breadth check: they express masking **without** a polymorphic restore value because
they pass the protected block as a *thunk*, not a *reusable capability*. This
confirms the rank-2 is a specific consequence of the **capture-and-hand-back-a-
capability** shape that Haskell/Cats-Effect/ZIO — and Kappa — chose.

The original safety rationale (Marlow & Peyton Jones, *Asynchronous Exceptions in
Haskell*, PLDI 2001; GHC #4035 "wormholes kill modularity") makes the universal
quantification **load-bearing**: it stops the masking capability from being stored
and reused outside its scope. Note the two distinct `forall`s, often conflated:

- The **inner `forall a`** (rank-2-ness proper) lets one `restore` apply to
  sub-actions of *different* types within one mask block — **this is the part
  relevant to the spec decision.**
- The **outer argument-passing** of `restore` (vs. a free top-level `unblock`) is
  the #4035 modularity fix. Don't cite #4035 for the inner polymorphism.

---

## 2. Rationale — why rank-2 exists

`restore` is a **single captured masking-capability value** that re-enables
interruption for *whatever sub-action it is applied to*. Because that one value is
applied to sub-actions of arbitrary, caller-chosen types, its apply must be
universally quantified (rank-2 — a natural transformation `F ~> F`).

The point is **not** "the function returns the body result type `a`." It is "one
capability, applied at many types." Rank-1 `restore : IO e a -> IO e a` (instantiated
at the mask result `a`, exactly as the Kappa impl does) can only restore sub-actions
whose type *equals the block's final result* — a strict, and idiomatically
insufficient, subset.

**The decisive motivation: multi-restore of differently-typed sub-actions.** This is
the foundational `bracket`/`acquireRelease` combinator, and it genuinely needs the
generality. Cats-Effect's reference `bracketFull` is verbatim:

```scala
def bracketFull[A, B](acquire: Poll[F] => F[A])(use: A => F[B])
                     (release: (A, Outcome[F,E,B]) => F[Unit]): F[B] =
  uncancelable { poll => acquire(poll).flatMap { a =>
    guaranteeCase(poll(unit >> use(a)))(release(a, _)) } }
```

The **same `poll`** is applied to `acquire` (an `F[A]`) **and** to `use(a)` (an
`F[B]`). `A` (the resource) and `B` (the result) are independent type parameters; the
resource type is in general **not** the body result type. Likewise coot.me's
`withLock` applies one unmask to both `k :: IO a` and a handler
`putMVar lock () >> throwIO e :: IO ()`. Under rank-1 these are **type errors**.

So the generality is **real, idiomatic, and reachable** — not a corner case. The
"never exercised" intuition came from the rank-1-safe subset: GHC's own
`bracket`/`finally`/`bracketOnError` apply `restore` only to `(thing a)` at the
*result* type. That subset is exactly what Kappa's `bracketM` (`Prelude.hs:1494`,
`restore (use r) : IO e b` = result) reproduces — which is why the shipped code
survives. But the subset is not the idiom.

---

## 3. Is-it-exercised — verdict on the "never exercised" claim

**Two-part verdict:**

**(a) TRUE for shipped code — backporting breaks nothing today.** A full audit of
every `mask`/`restore` consumer in the repo found exactly the rank-1-expressible
shape everywhere:

- `bracketM` (`Prelude.hs:1494`) is the **only** prelude `restore` site:
  `mask (\restore -> ioBind acquire (\r -> finallyIO (restore (use r)) (release r)))`
  — one `restore (use r) : IO e b`, equal to the mask result. It backs `bracket`
  (`Prelude.hs:1497`), the `MonadResource (IO e)` instance, and the §18.8 finally
  kernel under `using`/`ensuring`/`acquireRelease`. So the note's "acquireRelease /
  bracket are rank-1-expressible" claim **holds for the shipped definitions.**
- The `masking.kp` test family (`test/native/cases/masking.kp:17`,
  `tests/native/llvm/masking.kp`, `tests/conformance/effects/masking.kp`) declares
  `masked : (IO Void Unit -> IO Void Unit) -> UIO Unit` and applies `restore` to
  three `IO Void Unit` actions at result `Unit` — restore is **hand-annotated
  monomorphic**, baking in the rank-1 assumption. The repo's own conformance suite
  never instantiates `restore` at a type ≠ the mask result.

So `restore`'s rank-2 is the spec's **sole** rank-2-restore occurrence (line 19065),
its sibling combinators (`uninterruptible`/`ensuring`/`acquireRelease`,
`Spec.md:19059-19077`) are all monomorphic `IO e a`, and no shipped code exercises
the generality.

**(b) FALSE going forward — rank-1 rejects the canonical idiom at typecheck.**
Confirmed empirically by compiling minimal counterexamples with `kappa check`:

- **Multi-type restore (REJECTED).** Body
  `mask (\restore -> ioBind (restore getInt) (\x -> ioBind (restore getStr) (\y -> ioPure (MkP x y))))`
  with `getInt : IO Void Integer`, `getStr : IO Void String`, result
  `IO Void (P Integer String)` → four `E_APPLICATION_ARGUMENT_MISMATCH` errors:
  `actual: IO Void Integer / expected: IO Void (P Integer String)` (and the String
  dual). The diagnostic literally proves `restore` was monomorphized to the mask
  result type.
- **Single restore at any non-result type (REJECTED).**
  `mask (\restore -> ioBind (restore getInt) (\x -> ioPure "done")) : UIO String` →
  `actual: IO Void Integer / expected: IO Void String`. The regression is not
  narrowly "multiple types" — it bites whenever `restore` is applied at **any** type
  other than the mask's own result `a`.
- **Control (ACCEPTED).** `mask (\restore -> restore getInt) : UIO Integer` →
  exit 0. The `bracketM` shape (restore once, at the result type) is the **only**
  thing rank-1 admits.

**Exercised verdict:** the rank-2 generality is genuinely **dead in the current
corpus** but **dead only because the corpus is small and self-consistent**. Relaxing
to rank-1 makes the type system *permanently unable* to express the canonical
GHC/Cats-Effect/ZIO mask idiom — the very pattern a user reaches for the first time
they write a non-trivial mask body. This is the worst kind of dead code: dead until
someone uses the feature normally.

---

## 4. Sharpened recommendation

### Recommendation: **keep rank-2 — CONFORMANCE-FIX.**

Retain §18.1.12's rank-2 `restore`. Make the implementation conformant by **lowering
`restore`-application to drop the erased implicit type-application before the 1-arg
runtime closure** — i.e. teach the lowering to consume `kappi(restore, ⟨x⟩)` as a
*type argument* rather than feeding it to the monomorphic closure *as the action*
(the current "non-function value" crash, `Prelude.hs:556-558`). The implicit type-app
elaborates to `CApp Impl` (`Check.hs`) and is lowered at `C.hs:2585/2601` /
`LLVM.hs:3111`; the fix erases it at the `restore` call site so the runtime restore
stays a single 1-arg closure **semantically** while the *source type* remains rank-2.

**This is explicitly NOT a monomorphisation.** No type specialization, no
polymorphic-closure ABI, no `krt2_mask` rewrite. The runtime restore is already a
type-erased, uniformly-boxed 1-arg function — at runtime there is nothing for the
type argument to do. The only bug is that the erased type-app currently flows to the
closure as a value; dropping it at the call site is the whole fix.

### Why this over relax-to-rank-1

1. **Provenance.** Rank-2 is a deliberate, industry-universal import (Haskell PLDI
   2001 → Cats-Effect `Poll` → ZIO restorer), where the `forall` is part of the
   *correctness/safety* story (capability cannot escape its scope). The absence of a
   *Kappa-local* rationale (§1.1) reflects that it was inherited wholesale, not that
   it is unmotivated.
2. **The premise is false.** The "essentially never exercised" claim holds only for
   the `bracket`/`finally` subset; the general `bracket`-with-distinct-resource-type
   and `withLock`-with-typed-handler idioms exercise `restore` at two independent
   types in one expression (§2), and rank-1 rejects them at compile time (§3b).
3. **The cost is asymmetric.** Relax-to-rank-1 is a *permanent expressiveness loss*
   that forbids the standard mask idiom forever and is a *visible divergence* from
   the lineage Kappa imitates. The CONFORMANCE-FIX is a *bounded lowering change* at
   the erasure boundary with no ABI impact and no spec divergence. The right place to
   absorb the runtime's 1-arg-closure constraint is the erasure/runtime boundary, not
   the type system.

### recommendation_vs_note: **OVERTURNS.**

The backport note (`ANALYSES-AND-SPEC-BACKPORT.md:149-153`) recommends **BACKPORT
(relax §18.1.12 to rank-1)**, resting on "the rank-2 generality is essentially never
exercised." This study **overturns** that recommendation. The note's own escape
clause is the correct path: it concedes (lines 154-158) that if rank-2 is essential
it becomes a CONFORMANCE-FIX — "lower `restore`-application to drop the `kappi`
type-app before the 1-arg closure — *not* a monomorphisation." The new evidence —
the multi-type idiom is rank-2-essential across the whole lineage, and compiled
counterexamples prove rank-1 rejects the very first non-trivial mask body — makes
rank-2 essential. So the fork resolves to the note's *alternative*, not its primary.

The note is correct that today §18.1.12 "silently mandates rank-2 with no escape
hatch, so the impl is non-conformant as written." The resolution is to make the impl
conformant, not to weaken the spec.

### Conditional escape hatch (only if the fix is deferred)

If the team cannot land the lowering fix immediately and must ship rank-1 as an
**interim**, then: (a) mark §18.1.12's rank-1 a **KNOWN RESTRICTION / DIVERGENCE**,
not a design choice; (b) name the breaking gap explicitly — *`restore` cannot be
applied to a sub-action whose type differs from the mask result, which forbids the
standard `bracket` where the acquired resource type ≠ the body result type*; (c) keep
a non-normative "backends MAY provide rank-2" note pointing at the CONFORMANCE-FIX as
the planned resolution. Do **not** justify the interim with the (false) "never
exercised" claim.
