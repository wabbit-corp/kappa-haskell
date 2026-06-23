# Independent Review: Totality / Proof-Search Hang

Scope: an adversarial, source-grounded correctness review of the totality /
proof-search hang touching checked-arithmetic evidence, branch facts,
normalization, and termination proof search, against the current dirty tree
(uncommitted changes to `src/Kappa/Check.hs`, `src/Kappa/Pipeline.hs`,
`src/Kappa/Backend/C.hs`, plus the new `tests/conformance/recursion/decreases-div-*`
fixtures).

**Headline result: the current dirty tree does not terminate.** A trivial
one-line program (in fact *any* program) hangs while type-checking the standard
prelude, in a tight CPU loop. I reproduced it, captured a cost-centre stack, and
traced it to a specific, newly-introduced metavariable-solving shortcut that
solves a metavariable **to itself** and then diverges in `unify`/`force`. This is
the active hang. The large branch-fact / normalization / caching rework in the
same changeset is largely sound on inspection, but it is addressing a *different*
(performance-class) problem and could not even be exercised end-to-end because
the prelude never finishes checking.

---

## 0. Reproduction and evidence (do this first)

Build and run the checker on a trivial input:

```
$ cabal build exe:kappa
$ printf 'module main\nlet x : Int = 5\n' > /tmp/triv.kp
$ kappa check /tmp/triv.kp        # never terminates; killed at 3 min
```

Trace output (the dirty tree is instrumented with `Debug.Trace`; HEAD has none)
shows the prelude grinding through modules and stalling inside `std.bytes`:

```
DBG std.bytes bodies
...
DBG body let bytesBuilderSizedArray
DBG let bytesBuilderSizedArray flush-pre
DBG let bytesBuilderSizedArray flush-post      <-- last line, then spins forever
```

`sample` shows a pure-Haskell CPU spin (no I/O, no deadlock) in a small cluster
of mutually-recursive local closures plus GC.

A `+RTS -xc` cost-centre dump (SIGINT into the profiling build while it hangs)
pins the innermost live stack precisely:

```
Kappa.Eval.force.go
  <- Kappa.Check.forceM
  <- Kappa.Check.unify.solveFlex
  <- Kappa.Check.unify.go
  <- Kappa.Check.unify.goTop
  <- Kappa.Check.unify
  <- Kappa.Check.expectType
  <- Kappa.Check.check.checkFallthrough
  <- Kappa.Check.withDemand / withArgIndexRetag
  <- Kappa.Check.checkExplicitArg
  <- Kappa.Check.elabAppChecked.step
  <- Kappa.Check.elabAppChecked / withArgFlatFor
  <- Kappa.Check.check
  <- Kappa.Check.checkAgainstSig.go
  <- Kappa.Check.elabLetDecl  (bytesBuilderSizedArray)
  ...
  --> evaluated by: Kappa.Check.unify.go
```

So the loop is `unify → solveFlex → forceM → force`, re-forcing a thunk that
`unify.go` produced — the textbook signature of a **cyclic metavariable
solution** being traversed.

Corroborating detail: the instrumented run shows the `SlotEvid` step *did* fire
(`DBG slot evid`) and then the `SlotExpl` step diverged (`DBG slot expl`), with
`appchecked … unify-result-post / steps-pre` immediately before. `SlotEvid` is
*rare* in the prelude — the common implicit `forall a. (a : Type)` is kind-like
and becomes a `SlotKind` *placeholder* (no `solveMeta`, safe), whereas
`forall (n : Nat)` is **not** kind-like and becomes a `SlotEvid` evidence slot.
That is precisely why the hang waits until the first function that applies a
`forall (n : Nat)` function and explains "why here."

The offending prelude definition is ordinary and unchanged
(`src/Kappa/Prelude.hs:2541`):

```kappa
bytesBuilderSizedArray : forall (n : Nat). SizedArray n Byte -> (1 builder : BytesBuilder) -> BytesBuilder
let bytesBuilderSizedArray arr builder = bytesBuilderBytes (bytesFromSizedArray arr) builder
```

It is the first prelude function to **apply** a `forall (n : Nat). …` function
(`bytesFromSizedArray : forall (n : Nat). SizedArray n Byte -> Bytes`,
`src/Kappa/Prelude.hs:2538`) in argument position where the implicit `n` is *not*
pinned by the result type (the result is `Bytes`, which does not mention `n`).
That is exactly the shape that trips the new code path below.

---

## 1. Likely root causes, ranked by confidence

### RC1 — (Certain) `elabAppChecked` evidence-slot fast path solves a metavariable to itself

`src/Kappa/Check.hs` — the `SlotEvid` arm of `elabAppChecked.step`
(approx. lines 4158–4189):

```haskell
ev <-
  if isEq
    then do { mid <- freshMetaId; ...; pure (CMeta mid) }   -- postpone eq goals
    else if q == Q0 && not isTrait && not isRow
      then pure m                                            -- (*) trivial evidence
      else resolveImplicitQ ctx sp q dom
evV <- evalIn ctx ev
mVf <- forceM mV
case (m, mVf) of
  (CMeta mid, VFlex meta []) | meta == mid -> solveMeta mid evV   -- (**) BUG
  _ -> void (unify ctx mVf evV)
```

For an ordinary erased implicit such as `forall (n : Nat)`:

* `peel` created the slot as `SlotEvid q dom m mV` with `m = CMeta m0` and
  `mV = VFlex m0 []` (`peel`, ~lines 4135–4144). `n : Nat` is **not** kind-like
  (`isKindLike` returns `True` only for sorts / `Pi`-to-sort; `Nat` is a type),
  so it becomes an evidence slot, not a `SlotKind` placeholder.
* `n` is erased (`q == Q0`), not a trait/row/eq goal, so branch `(*)` is taken:
  `ev = m = CMeta m0`.
* Therefore `evV = eval (CMeta m0) = VFlex m0 []`, and `mVf = forceM mV = VFlex m0 []`.
* The guard at `(**)` matches with `mid = m0`, `meta = m0`, so it executes
  `solveMeta m0 (VFlex m0 [])` — **it binds `?m0 := ?m0`.**

That self-cycle is fatal. Later, when the explicit argument `arr : SizedArray n Byte`
is checked against `SizedArray ?m0 Byte`, `expectType` calls `unify`, which calls
`solveFlex m0 …`. Because `?m0` is already "solved" to `VFlex m0 []`, `solveFlex`
does `sol' <- forceM sol; t' <- forceM t; go False lvl sol' t'`
(`solveFlex`, lines 1153–1159), where `force`'s self-reference fuel runs out and
returns `VFlex m0 []` again, `go` re-dispatches to `solveFlex m0 …`, and the
process repeats forever. This is exactly the `unify.go ↔ solveFlex ↔ forceM ↔
force.go` loop the `-xc` stack shows.

This is a **regression introduced by this changeset.** The diff replaced a
correct call:

```haskell
-      _ <- unify ctx mV evV
```

with the `(**)` shortcut. The old `unify mV evV` unified `VFlex m0 []` with
`VFlex m0 []`, which hits `solveFlex`'s reflexive guard
(`src/Kappa/Check.hs:1163`):

```haskell
VFlex m' [] | m' == m -> pure True          -- ?m ≡ ?m : trivially true, do NOT solve
```

and returns `True` **without ever binding `?m0`**. The shortcut bypasses that
guard and manufactures the cycle. `git show HEAD:src/Kappa/Check.hs` contains no
`Debug.Trace` and the prior `unify mV evV`, confirming HEAD did not hang here.

Confidence: **certain** — reproduced, cost-centre-confirmed, and the faulty
binding is mechanically derivable from the code for the `forall (n : Nat)` case.

### RC2 — (High) The analogous `SlotExpl` fast path is occurs-check-free and bypasses the same guard

`src/Kappa/Check.hs:4211–4222`:

```haskell
mVf <- forceM mV
case mVf of
  VFlex m [] | m == mid -> forceM aV >>= solveMeta mid   -- no occurs check, no reflexive guard
  _ -> when dep (void (unify ctx mVf aV))
```

This solves the explicit placeholder `mid := force aV` directly. The justifying
comment ("the placeholder … is not in scope for the argument's domain, so the
checked argument cannot contain it") is *plausible for the immediate case* but is
an unverified structural assumption made at a call site, with **no occurs check
and no reflexive `?m ≡ ?m` guard**. If `aV` ever forces to `VFlex mid []` (e.g.
an argument elaborated to the very placeholder, or a flex chain that resolves back
to `mid` through a dependent codomain), this reproduces RC1's self-cycle. Even if
no current input hits it, it is the same unsafe pattern and should not survive.

Confidence: **high** that it is unsound-in-principle; **medium** that a current
input triggers it (the prelude dies on RC1 first, so RC2 is presently masked).

### RC3 — (Medium) `unify`/`quote` have no divergence budget; the occurs check itself can diverge

`solveFlex`'s real occurs check is `quote ec lvl t; if occursMeta m tm` (lines
1166–1167). `quote` (`src/Kappa/Eval.hs:425`) is **not** fuel-bounded. `force`
is bounded (1000 non-runtime steps, `Eval.hs:218`) and so is `convertible`
(200, `Eval.hs:480`), but `quote`, `unify.go`, and the structural recursion that
consumes a forced value are not. Consequently:

* Once *any* cyclic solution exists (from RC1/RC2 or from a future flex-flex
  spine decomposition that individually passes occurs but jointly cycles), the
  whole checker hangs instead of producing a diagnostic.
* `solveFlex`'s `quote ec lvl t` occurs check will itself loop forever if `t` is
  *already* an infinite value, so the occurs check cannot be relied on as the
  backstop.

This is not the proximate cause but it is why the proximate cause is a hard hang
rather than a recoverable error. It is a pre-existing fragility that RC1 turns
lethal.

Confidence: **medium-high** as a contributing structural weakness.

### RC4 — (Medium; soundness, not a hang) the arithmetic solver now mints `refl`

The "intended" change routes the bounded arithmetic relation solver into
`propProof` so that checked-arithmetic obligations of the form `P = True` are
discharged by emitting `refl` (`propProof`/`proveBoolValueFromBranchFacts`/
`proveBoolValue`/`proveFact`, lines ~2592–2764, ~14067–14077). Previously
`propProof` only emitted `refl` when the two sides were **definitionally**
convertible (optionally after reducing in-scope `if` conditions with branch
facts). Now it emits `refl` for propositions that are *arithmetically* valid but
not definitionally equal to `True` (e.g. `leInt y x = True` proven from branch
fact `y <= x`). That is a legitimate decision-procedure-as-proof technique, but
it **expands the trusted core**: a soundness bug in `proveFact` is no longer
"accept a non-total function" (totality), it is a false `refl` (type
unsoundness). See §4 for the soundness audit (I found the new division rules
sound, but the surface area is now higher-stakes).

Confidence: **high** that this is a real trust expansion; **no concrete
unsoundness found** in the new rules.

### RC5 — (Low) residual caching concerns

The new `csNormCache` / `csPropCache` / `csEvidenceCache` (epoch-keyed, bounded)
appear sound on inspection (see §4), but could not be exercised because the
prelude hangs. Lower-confidence concerns are listed in §4.

---

## 2. Is each a principled fix?

* **RC1 fix is not principled as written** and must be reverted/repaired. The
  motivation (avoid `unify`'s `O(size)` `quote` when wiring a fresh, unreferenced
  placeholder) is reasonable, but the implementation drops two invariants that
  `unify` guarantees: the reflexive `?m ≡ ?m` guard and the occurs check. The
  correct shape is "shortcut only when the head meta of the candidate differs
  from the placeholder; otherwise it is either reflexive (do nothing) or needs
  the occurs check (use `unify`)." Crucially, the reflexive case the shortcut
  mishandles is *already O(1)* under `unify`, so the optimization buys nothing
  there — it only introduces the bug.

* **RC2** is the same anti-pattern; principled only if it provably never sees the
  placeholder and never needs an occurs check. That proof is not in evidence;
  prefer routing through `unify` (with the cheap reflexive/fresh fast paths
  living *inside* `unify`, where they are auditable once).

* **RC3**: adding a work budget to `unify`/`quote` is principled defense-in-depth
  but is a backstop, not the fix. The fix is to never create cyclic solutions.

* **RC4**: emitting `refl` from the solver is acceptable *if* deliberately chosen
  and documented as a trusted compiler-owned proof artifact (cf. the
  `patch_eq_refl.md` discussion of "law evidence realization" — the same
  principle: the implementation may supply intrinsic proof artifacts, but their
  identity and soundness must be owned and tested). It needs an explicit
  soundness contract and adversarial tests, not silent normalization creep.

* **The branch-fact surface-only discipline is principled and good.** The
  changeset's genuinely defensible core is the rule that branch facts and
  proof-search inputs are classified **without normalizing/forcing user terms**:
  `boolRelBranchM` (lines ~13809+), `neutralValueTerm` ("deliberately does not
  call `force` or `quote`", ~13830), `proveBoolValue` ("must not normalize
  arbitrary user functions", ~14026). Combined with the existing reducibility
  gate (`withSccOpaque` makes an SCC opaque during its own check, and
  `shouldDeferTermination`/`gdReducible` keep unverified recursive functions
  non-reducible during elaboration), these uphold "do not normalize/convert a
  term before its totality is known." That part of the patch is sound and worth
  keeping. It is simply orthogonal to RC1, which is the actual hang.

---

## 3. Concrete regression tests to add

1. **The exact repro, minimized** — a conformance test that applies a
   `forall (n : Nat). T n -> R` function where the result `R` does *not* mention
   `n`, so the erased implicit stays flex through the evidence slot:

   ```kappa
   --! assertNoErrors
   --! timeoutMs 10000          -- see test #6: a hang must FAIL, not wedge CI
   module main
   data Vec : Nat -> Type = MkVec Nat
   len : forall (n : Nat). Vec n -> Nat
   let len v = match v case MkVec k -> k
   wrap : forall (n : Nat). Vec n -> Nat
   let wrap v = addInt (len v) 1     -- application of a `forall (n : Nat)` fn in arg position
   ```

   This would have hung pre-fix and must compile post-fix.

2. **Prelude smoke test** — assert that `kappa check` of a trivial module
   terminates under a wall-clock budget. The prelude itself is the strongest
   regression test; today it is an infinite loop and nothing catches it.

3. **Reflexive flex-flex through evidence insertion** — a generic test that
   inserts an erased implicit that is never constrained by the result (so the
   placeholder is solved trivially), asserting termination and that the binding
   is *not* a self-cycle.

4. **Cyclic-solution backstop** — once a `unify`/`quote` work budget exists
   (§5), a test that constructs a would-be cyclic unification (e.g. `?f Int ≡
   Option (?f Int)` via spine decomposition) and asserts a clean diagnostic
   rather than a hang.

5. **`refl`-from-solver soundness/adversarial set** — extend the new
   `decreases-div-*` fixtures with *propositional* (not just termination)
   obligations: checked subtraction/division whose evidence `P = True` is minted
   by the solver, plus adversarial near-misses that must be rejected
   (`assertDiagnostic`), to lock down RC4's trusted surface. The existing
   `decreases-div-adversarial-reject.kp` / `decreases-div-half-reject.kp` cover
   termination *rejection* well; mirror them for *evidence* emission.

6. **Harness watchdog** — give the conformance harness a per-file timeout so a
   non-terminating compile is classified `Fail`/`HarnessError`, not an infinite
   CI job. Without this, RC1-class regressions are invisible to the suite.

7. **Cache-invalidation tests** (for the kept machinery): (a) a negative
   proposition cached, then a new instance/global added, must not be reused
   (epoch bump); (b) `withSccOpaque` enter/exit must not leak a normal form
   computed while a definition was reducible into a context where it is opaque,
   or vice versa.

---

## 4. Suspicious remaining unsoundness / incompleteness

**Soundness of the new arithmetic (RC4 surface) — audited, found sound:**

* `divInt = quot` (truncation toward zero) and only fires for nonzero divisor
  (`Eval.hs:558`); `subInt = a - b` (true subtraction, `Eval.hs:556`). `arithOf`
  maps `divInt → ADiv`, `subInt → ASub` (lines ~13996–14006), consistent with
  the bound rules.
* `divByPositiveConstBounds`/`divByNegativeConstBounds` (lines ~14263–14269):
  `x quot k` is monotonic non-decreasing in `x` for `k>0` (and non-increasing for
  `k<0`), so propagating endpoint-wise is correct. ✔
* `lowerBoundSpecial` (lines ~14162–14184): case 1 (`x - x/k >= 1` for `k>1,
  x>=1`) and case 2 (`x - y/k >= 1` for `k>1, 0<=y, y < k*x`) are both valid for
  truncating division **because the `y>=0` guard forces `quot == floor`**; the
  recursion in case 2 strips one division level per step over a finite `AExpr`,
  so it terminates. ✔ The reject fixtures (`divInt n 1`, `divInt n -2`,
  `divInt (2n+1) 2`, `mayStayZero`) are correctly *not* provable.
* `negateFact` (lines ~13726–13733) correctly refuses to negate `=` (avoids
  encoding disequality as a contradiction that would prove anything on an `else`
  branch). ✔

**Trusted assumption worth flagging (pre-existing, now higher-stakes):**
`arithOf` treats `natToInt`/`natOfInt`/`intToNat` as the identity (lines
~14003–14005). This is *value*-sound only because `Nat`/`Integer` share a
representation and `natOfInt` does **not** clamp (`Eval.hs:778`,
`int a`). The solver also assumes every `Nat`-typed binder is `>= 0`
(`varBounds`, `Set.member v natLvls`, line ~14247). Together these are sound for
well-typed surface programs, but `natOfInt` is a non-clamping internal primitive,
so the `Nat >= 0` axiom is *trusted*, not enforced. With RC4 this axiom now backs
`refl`, not just termination acceptance. Recommend documenting it as a trusted
basis and keeping `natOfInt` out of user surface.

**Caching concerns (could not be runtime-exercised — prelude hangs):**

* **Epoch coverage looks complete.** Every `csGlobals` mutation
  (`addGlobal:941`, `withSccOpaque:12447/12450`, `setGlobalReducible:12457`) and
  `csTraits`/`csInstances` mutation (`headerTrait`, `registerInstanceHead`) and
  `applyNativeModules` calls `invalidateSemanticCaches` (epoch++ + clear). The
  conversion-affecting `csFacts` is *not* epoch-tracked but is guarded by
  `Map.null (csFacts st)` in `normalizeTermAt` and `cachedPropDecision`, and
  `solveMeta` deliberately does not bump the epoch but is covered by the
  meta-freedom admission guards. I could not find a conversion-affecting mutation
  that escapes both the epoch and the guards.
* **`csPropCache` is effectively disabled exactly when it would help.**
  `cachedPropDecision` only caches when `null (csBoolFacts st)` (line 2702), but
  checked-arithmetic obligations are *always* under branch facts, so those
  decisions are never cached. The elaborate `factsKey`/`natKey` machinery in
  `propDecisionKey` is therefore dead at store time (facts always empty when
  stored). Not unsound — but it means the cache does not address the
  checked-arithmetic cost it was ostensibly built for.
* **Structural keys via `T.pack . show`** (`renderStructuralTermKey`, line ~202)
  assume `Show Term` is injective and cheap. Injectivity is fine for the derived
  algebraic `Term`; cost is `O(size)` per lookup *and* per miss, on a function
  (`normalizeTermAt`) called very frequently during termination — a real
  constant-factor risk on large modules, and an additional reason the developer
  may have perceived a "hang" before RC1 (i.e., there may have been a
  *performance* hang that this rework targets, distinct from the RC1
  *non-termination* it introduced).
* **`csEvidenceCache` omits the context** and relies on `ceImplicitLocal` flagging
  *all* locally-usable evidence (so `superCandidate`/local-dict projection can't
  make a "closed" goal context-sensitive). This is plausible but I did not fully
  verify that every local evidence source sets `ceImplicitLocal`; worth a
  targeted check.

**Process hygiene:** the tree ships 42 `Debug.Trace` calls and
`import Debug.Trace (trace, traceM)` (HEAD has zero), including a
`modify' $ \st -> trace "…" st` at line 4212. These must be removed before this
lands; they also force unbuffered stderr that masks the hang location under
redirection.

---

## 5. What I would change next (in order)

1. **Fix RC1.** Make the `SlotEvid` shortcut refuse the reflexive case. Minimal,
   behavior-preserving repair:

   ```haskell
   case (m, mVf) of
     -- ?m ≡ ?m  (the ev = placeholder case): nothing to do, exactly as
     -- unify's reflexive flex-flex guard. Never solve a meta to itself.
     (CMeta mid, VFlex meta []) | meta == mid, evHeadMeta evV == Just mid -> pure ()
     (CMeta mid, VFlex meta []) | meta == mid -> solveMeta mid evV   -- only when evV /= ?mid
     _ -> void (unify ctx mVf evV)
   ```

   or, simpler and safer, **delete the shortcut and restore `unify ctx mV evV`**.
   `unify` already handles the reflexive case in `O(1)` and the
   fresh-unreferenced case cheaply; the shortcut's only measurable win is on
   *non-reflexive, large* `evV`, which is not the hot path here.

2. **Fix RC2 the same way** (reflexive/occurs guard), or route it through `unify`
   and instead add the "fresh, result-unreferenced placeholder" fast path *inside*
   `solveFlex`, where the occurs check and reflexive guard already live and are
   audited once.

3. **Add a work/fuel budget to `unify.go` and `quote`** (RC3) so any future
   cyclic solution degrades to a `E_*`/internal diagnostic instead of wedging the
   compiler. The occurs check in `solveFlex` should be made robust to an
   already-cyclic `t` (e.g. bounded `quote`, or an occurs check that walks the
   forced value with a visited-set rather than fully quoting).

4. **Re-run the prelude and the full conformance suite** once RC1/RC2 are fixed.
   Everything downstream of the hang (the caches, the branch-fact rework, the
   `decreases-div-*` fixtures, RC4's `refl` emission) is currently **unverified
   end-to-end** because nothing compiles. Do not declare the totality rework done
   on the strength of code review alone; it has never run.

5. **Decide and document RC4.** Either (a) keep solver-minted `refl` and treat it
   as a trusted compiler proof artifact with an explicit soundness statement and
   the adversarial *evidence* tests from §3.5, or (b) restrict `propProof` to
   definitional convertibility (its prior behavior) and surface arithmetic facts
   only through the termination path. (a) is more powerful and consistent with
   the spec's "law evidence realization" direction, but only with the tests.

6. **Add the harness watchdog (§3.6)** so this class of regression can never again
   reach a green build by simply never finishing.

---

### One-paragraph summary for the author

The branch-fact / normalization / caching rework is mostly sound and its central
discipline — never force or normalize user terms whose totality is unknown — is
the right idea. But it is not the thing that is hanging. The hang is a
one-line metavariable shortcut in `elabAppChecked` (`SlotEvid`, ~line 4187) that
binds an erased implicit's placeholder *to itself* (`solveMeta m0 (VFlex m0 [])`)
whenever a `forall (n : <non-sort>)` argument is left unconstrained by the
result type; `unify` then loops forever traversing the self-reference. The
prelude trips it at `std.bytes`'s `bytesBuilderSizedArray`. Restore
`unify ctx mV evV` (or guard the shortcut against the reflexive case), apply the
same fix to the `SlotExpl` shortcut, add a divergence budget to `unify`/`quote`,
strip the `Debug.Trace` instrumentation, then re-validate the whole rework — none
of it has actually executed yet.
