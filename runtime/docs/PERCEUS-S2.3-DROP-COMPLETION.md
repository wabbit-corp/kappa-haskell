# Perceus S2.3 redux — Drop Completion (under the Boehm differential backstop)

Status: **S2.3a + S2.3b LANDED + independently reviewed SOUND** (`5723ec0`, `272be14`), with **S2.3c
implemented in this stage** by the primitive convention table. S2.2 (dup) +
S2.3-first-cut landed in `d5624e6` but `kdrop` fired ~0×; S2.3a completed the match-destructure cell-drop
so `kdrop` now fires (101 sites / 33 files, 315 `kdup` / 66 files), and S2.3b records the consume-vs-read
distinction and consumes it CONSERVATIVELY (dup only a consuming `NonLast`; scope-close drops stay on the
"no `LastUse` anywhere" rule). Empirically: RC-on == RC-off byte-identical (parity 150/0, conformance
2094/0), the DEBUG underflow assert is live, non-vacuous, and clean over the corpus (0 SIGABRT / 0
underflow). Next: **S2.3d** (per-path dead-binder drops) plus the returning-arm drop tighten before S3
free-on-zero.
Companion to [PERCEUS-S2-PLAN.md](PERCEUS-S2-PLAN.md) / [PERCEUS-RC-DESIGN.md](PERCEUS-RC-DESIGN.md).

## 0. Diagnosis (empirical)

Corpus: **63 `kdup(`, 0 `kdrop(`** across `test/native/cases/*.kappa.c`. Smoking gun (`adtcons.kappa.c`):
`match` reads fields out via **borrowing projections** (`kctor_arg`/`kproj`/`krec_at`/`kvariant_payload` —
`value.c:613/633/706/658` all `return v->as.ctor.args[i]`, no incref), moves one field out, returns it —
**the scrutinee cell and discarded fields are never dropped.** Every match-destructure leaks its cell.
Root cause: `rcBinderDroppableHere` (`C.hs:440-459`) drops a binder only with **no `LastUse` anywhere**; a
scrutinee gets `LastUse` at the match (its reference "moved into" the match), but the match never discharges
that cell. The move-at-LastUse transfers ownership *to the match*; the match never drops it.

## (a) S2.3a — MATCH-DESTRUCTURE drop (the big one)

Rule for `match s case C f₁…fₙ -> body` when the scrutinee's last use is the match:
**dup each kept (bound, runtime-relevant) field, then `kdrop` the scrutinee cell.** Sound for both:
- **unique** cell (rc 1→0 at S3): the surviving fields would be freed-by-recursion, so each kept field is
  `kdup`'d to keep it alive; the cell shell is freed.
- **shared** cell (rc>1): `kdrop` just decrements; the dup keeps the field count honest for the 2nd owner.
- **discarded** fields (`_`, omitted record fields): NOT dup'd; the single `kdrop(scrut)` is their decrement.

**Site:** the cell-`kdrop` goes in `consumeAltBody` (`C.hs:3902-3947`), per-arm, against the `scrut_N` (`sv`)
lvalue, alongside the existing `mapM_ rcEmitDrop patDrops`. The kept-field dups go in `bindPatScrut`
(`C.hs:5482`)/`patBindings` (`:4078`): a surviving slot `pat_k = kctor_arg(scrut,…)` becomes
`pat_k = kdup(kctor_arg(scrut,…))`, keyed by `P.patSlotPos k`. **Decision helper** `rcScrutDropDecision`
(in `consumeMatch:3807`): look up the scrutinee `CVar`'s `UseKind` at `matchScrutPos` — drop the cell for
`LastUse`/`NonLast` of a **non-borrowed** scrutinee; never for `Borrowed`; a **fresh** scrutinee (`CCtor`,
rc==1, no binder) always drops. Thread the decision into each arm; fire at the `SinkVar` seam only.
**SinkTail/SinkBounce (returning) arms:** skip the cell drop for S2 (a soft leak Boehm reclaims) — tighten
later (drop before the `return`). **Emit the cell-drop as a distinct statement against `sv`** (never folded
into the body) so S5 FBIP swaps the `{dup kept fields; kdrop cell}` pair for `{token=drop_reuse; kreuse}`
as a peephole on the unique path.

## (b) S2.3d — per-path DEAD-BINDER drops

Broaden `rcBinderDroppableHere`/`rcPatSlotDroppableHere` (`C.hs:440/467`) from "no `LastUse` ANYWHERE" to
**dead on THIS completion path**: a `boDroppable`, non-borrowed binder consumed on a *sibling* arm but
omitted on this one is dropped on the omitting arm. The data is half-present — `walkAlts` (`Ownership.hs:597`)
walks each arm against the same `liveOut`, so an outer binder is `LastUse` in arm A, absent in B. Add an
additive analysis field (`oiBinderArmDrops :: Map BinderId [ArmPath]`, or per-arm live-in difference);
consult it in `consumeAlt`/`consumeAltBody` (`:3884/3902`) at the `SinkVar` seam; same for `CIf`
(`consumeIf:3792`). Disjoint by construction: the consuming arm moves (no drop), the omitting arm drops.

## (c) S2.3b — the CONSUME flag (a real OwnInfo refinement)

`walk` classifies a `CVar` by **downstream liveness only** (`Ownership.hs:428-445`) — it does not see the
*position* the use flows into. A value whose only/last use is `kproj(x)` is `LastUse`, but the projection
**does not consume** `x` ⇒ `x` must still be dropped after the read. Fix: add a **`consuming` discriminator**
(`oiUseConsumes :: Map UseSite Bool`, or a `UseKind` field), set in `walk` by the syntactic position:
- **consuming** (no post-use drop): arg of `CCtor`/`CRecordV`/`CInject`, arg at a non-borrowed runtime call
  position (`ArgOwned`, conservative `ArgShared`, or unknown first-class fallback), the returned tail value.
- **non-consuming** (read only; caller/binder retains ownership): operand of `CProj`/`CProjAt`, an
  `ArgBorrowed` call position. Borrowing primitive arguments join this category after the S2.3c
  prim-convention table classifies them.
S2.3b records this in `OwnInfo`; the cross-check validates both the consuming subset used for linear
binders and the stored consume/read side tables. `C.hs` consumes the flag only where it is locally safe
(for example, read-only `NonLast` uses do not get an RC dup). Scope-close drops remain conservative:
they require a manifestly-owned local and still use the "no `LastUse` anywhere" rule until
projection-result ownership is modeled; otherwise `let x = rec in x.f` could return a borrowed field
after dropping `rec`. The later codegen step must either duplicate escaping borrowed projection results
or otherwise prove that the owner cannot be dropped before the result is owned.

## (d) S2.3c — the PRIM / runtime-ownership boundary (the one design decision)

**Investigation:** plain `argConvSelect` reported `ArgShared` for **every** prim arg — every prim arrow is
`(~>) = CPi Expl QW False` (`Prelude.hs:37`) ⇒ `QW` ⇒ `ArgShared` (`Repr.hs:282`). Storing prims
(`newRef`/`writeRef`/`__newArray`/`__arrayWrite`/`newTVar`, plus TVar/FiberRef/promise/atomic publishers)
genuinely **move** the arg into a runtime cell/container (`kref_new`, `kref_set`, `karr_set`,
`krt2_new_tvar`/`writeTVar`, `fiber_local_set`, `promise_complete`, `krt2_atomic_*` stores — `x = arg`,
no incref). Borrowing positions (`readRef`, `arrayRead`, `arrayLen`, `readTVar`, `getFiberRef`,
promise peeks/await, atomic load/order/ref/expected operands) **read or select**, not publish.

**Decision (implemented S2.3c):** `Repr.argConvSelectGlobal` applies a **primitive-convention override table**
keyed by resolved primitive identity (`primModule` or the prelude `VPrim` identity), then checks the override
arity against the walked type telescope. The table marks confirmed published value positions `ArgOwned` and
confirmed read-only positions `ArgBorrowed`; unmodeled result/action-transfer positions remain
`ArgShared` as a conservative fallback until result/action ownership is explicit. This is intentionally not
a blanket "all non-storing primitive args borrow" rule: alias-returning/result-transfer primitives such as
`__transport`, `ioPure`, query/list identity shims, compact/finish helpers, and do-kernel action captures
must not be silently converted to caller-retained borrows before their result ownership is modeled.
**No runtime-prim `kdrop` changes** — prims are C and cannot see rc cleanly. Primitive *types* stay unchanged
(lower churn, keeps the source contract stable).

**Unsoundness pin for S3:** a storing prim MISSING from the table and later treated as borrowing would let a
caller drop a moved-in value ⇒ **S3 UAF**. The table must stay **storing-prims-exhaustive** over audited
runtime stores in `value.c`, `prims.c`, `stm.c`, `rt.c`, and `atomic.c`; bias toward `ArgOwned` only on
confirmed publish positions, and leave ambiguous alias/action/result-transfer cases `ArgShared`. Gates:
`primArgConventionS23c` pins the table, ownership focused tests pin read-vs-transfer for IORef/TVar/FiberRef,
and `argConvBodies`/the C RC-on accessor consume the same `argConvSelectGlobal` path.

**Runtime rc-discipline pin for S3 (runtime-side, distinct from the table — surfaced by the S2.3c review, and
NOT covered by `R-prim-table-incomplete`, which is about compiler drop-placement/table completeness).** The
table classifies the *caller* boundary correctly, but three runtime store bodies lack the rc discipline S3
free-on-zero needs; each must land WITH the S3 flip (all inert now — `kdrop` never frees, Boehm traces the
scanned cells). Empirically verified clean under the S2 backstop (RC-on == RC-off, 0 underflow):
- **`karr_new` (`value.c:269`) — the UAF-direction one.** `for i<n: slab[i]=init` broadcasts ONE `ArgOwned`
  `init` (rc bumped once by the caller transfer) into N slots with no per-slot `kdup`; a naïve S3 free-on-zero
  recursion over boxed slots drops `init` N times ⇒ rc 1→0 on the first slot, slots 2..N dangling ⇒
  premature free / UAF for n≥2. Fix (runtime): `kdup(init)` ×(n−1) in `karr_new`, guarded by
  `KAPPA_PERCEUS_RC`. The table classification (`[borrowed, owned]`) is CORRECT; this is a runtime store gap.
- **Overwriting stores** — `karr_set` (`value.c:285`), `kref_set` (`value.c:841`), `fiber_local_set`
  (`rt.c:1145`), `krt2_atomic_store`/`exchange` (`atomic.c:131/142`) — overwrite a cell without dropping the
  OLD occupant (a write barrier). LEAK-only (safe even post-S3), but each needs a drop-old for a leak-free S3.
- **Not-stored `ArgOwned` args** — `krt2_atomic_compare_exchange` (`atomic.c:161`) stores `desired` only on
  success; `promise_complete` (`rt.c:1222`) stores `exitv` only on first completion. On the CAS-fail /
  already-completed path the moved-in `ArgOwned` arg is neither stored nor dropped. LEAK-only; needs a drop.

**Arity-guard alignment pin for S3 (compiler-side).** `argConvSelectGlobal`'s arity check counts params by
`argConvSelect`'s rule (`Expl ∧ q≠Q0`, which *includes* an explicit non-`Q0` kind-domain param), while
`Ownership.classifyCallArgs` consumes convs by `erasedOrKind` (`Q0 ∨ isKindDomainTerm`, which *skips*
kind-domain params). They diverge only on an explicit non-`Q0` kind-domain parameter — INERT today (no table
entry has one; only 4 erasure intrinsics in the prelude — `__effRowCons`/`__shapeInspectAdt`/
`__shapeInspectRecord`/`__shapeRequireFieldInstances` — carry such a param, none listed; and S2.3c is
observe-only). Before S3 enables caller-drops, make the override arity check count by the `erasedOrKind` rule
(or add an S1.5 finding on mismatch) so a future kind-domain-param prim cannot left-shift a convention onto a
real value position — which would land `ArgBorrowed` on a store, the one forbidden direction.

## (e) Owned/borrowed CALLER-drop completeness — folds into (c)

Real gap: passing an **owned** binder to a **borrowing** (`&`) param classifies the use by the *binder's*
liveness (`Ownership.hs:433-440` keys on `scBorrowed`, the binder's marker, NOT the call position) ⇒ a binder
that dies at a borrowed-arg position is `LastUse` ⇒ skipped as "moved" — but it was only *borrowed*, so it
must be dropped. The (c) consuming flag, set from the **call position's `argConv`**, identifies this
correctly (an `ArgBorrowed` position ⇒ non-consuming ⇒ binder retains ownership). Current C scope-close
code still stays on the conservative "no `LastUse` anywhere" rule, so the full caller-drop completion waits
for the same projection-result ownership step described above. Same root fix: classify by the *position the
value flows into*, not only the binder's marker.

## (f) Sub-stages, ordering, risks (dup already in place from S2.2)

| sub | what | gate |
|---|---|---|
| **S2.3a** | match-destructure cell drop (a) — the biggest fire-count win | underflow-assert clean; net → 0; byte-identical |
| **S2.3b** | consuming-vs-read flag (c); close-drops stay conservative until projection-result ownership | assert clean; metadata pins transfer vs read |
| **S2.3c** | prim-convention table (d): classify audited primitive publish/read positions; full caller-drop completion still waits for projection-result ownership | `primArgConventionS23c`; ref/TVar/FiberRef ownership regressions; assert clean |
| **S2.3d** | per-path dead-binder drops (b)+(e), after the path-local ownership facts are explicit | assert clean; net trends down |

**Risks (under the Boehm backstop: leak/assert now; S3 UAF risks called out explicitly):** **R-double-drop (highest)** — cell-drop +
sibling per-path drop + a move on the same cell; guard by disjoint conditions (cell-drop only when scrutinee
received the reference; per-path drops only on omitting paths); the underflow assert catches overlap before
S3. **R-prim-table-incomplete** — a storing prim missing from S2.3c becomes an S3 UAF risk once caller-drop
completion is enabled; require the `value.c`/`prims.c`/`stm.c`/`rt.c`/`atomic.c` store audit to stay current
before that switch. **R-runtime-store-discipline (NEW, S3-gating; see §(d)'s runtime pin)** — the *runtime*
store bodies lack per-slot dup (`karr_new` — UAF-direction), drop-old write barriers, and CAS-fail/promise-
recomplete drops; these are runtime-side, distinct from the table, and must land with the S3 flip. **R-arity-
alignment (NEW; see §(d)'s arity pin)** — the override arity check counts kind-domain params differently from
the conv consumer; inert today, but must be reconciled before S3 caller-drops.
**R-returning-arm leak** — SinkTail/SinkBounce arms skip the cell drop
(soft leak); flag for later. **R-CDo** — S2.3b walks and validates `CDo` bodies so generated do-kernel paths are
covered by RC checks; drops still do not cross a do-block boundary unless the lowered structure proves ownership transfer.
K_FGN/resource scrutinees must not be cell-dropped (structurally safe at S2 since `kdrop` never frees; re-pin
at S3). **R-path** — every new lookup (`matchScrutPos`, `patSlotPos k`, per-arm) uses the shared
`PathScheme` constants; `gsRcFindings` miss-log is fail-closed under `KAPPA_PERCEUS_RC=1`.

## (g) Verification — the backstop now genuinely exercised

1. **Underflow assert non-vacuous (primary):** after S2.3a, `grep -c kdrop( *.kappa.c` must be ≫0 (drops
   fire across every match-bearing program); the assert stays clean (drops never drive rc below the
   Boehm-live floor). **This is what proves S3 free-on-zero will reclaim.**
2. **Leak-trend net ≈ 0 per program** (`krc_report`), not monotonic-growth — modulo legitimately-never-
   dropped CAFs / `main`'s result. A persistently negative net with no live escapees = a missed drop.
3. **Outputs byte-identical** (2094/0, 150/0; RC-on == RC-off) — dup/drop are rc-maintenance while Boehm frees.
4. **Static ground truth green** (`crossCheckBodies`/`argConvBodies`, plus `primArgConventionS23c`) — new
   OwnInfo fields additive; the S2.3c prim table must keep `argConvBodies` and the direct convention matrix
   consistent with the audited storing-vs-borrowing primitive set.
5. **RC path lookup is zero-miss** — under `KAPPA_PERCEUS_RC=1`, `generateC` rejects nonzero
   `gsRcFindings`, and the native/LLVM harnesses assert the zero-miss diagnostic in redirected build logs.
6. **Resource regressions unchanged** (`usingsusp.kp`/`usinginterrupt.kp`) — no spurious drop inside a
   do-scope; a K_FGN scrutinee not cell-dropped (re-verify at the S3 flip).

## Critical files
- `src/Kappa/Backend/C.hs` — cell-drop in `consumeAltBody` (3902-3947)/`consumeMatch` (3807); kept-field
  dups in `bindPatScrut` (5482)/`patBindings` (4078); conservative `rcBinderDroppableHere`/
  `rcPatSlotDroppableHere` gates plus S2.3b consume/read dup filtering. Per-path drops, caller-drop
  completion, and result-ownership-aware close drops are later sub-stages.
- `src/Kappa/Ownership.hs` — position-aware consuming flag in `walk`, forced global/local parameter
  telescopes, pattern-bound field type recovery, additive `OwnInfo` consume/read fields, and cross-check
  validation for the stored side tables.
- `src/Kappa/Backend/Repr.hs` — `argConvSelect`/`argConv` plus `argConvSelectGlobal`; the audited
  primitive convention table is S2.3c.
- `src/Kappa/Prelude.hs` — storing `newRef`/`writeRef`/`__newArray`/`__arrayWrite` (838-848) vs borrowing
  `show*`/`print*` (497-511) the table classifies.
- `runtime/value.c` / `runtime/kappart.h` — confirm-only: stores (`kref_new` 248, `karr_set` 282, `kctor`
  159), reads (`kctor_arg` 613, `kproj` 633), the `kdrop` no-free assert.
