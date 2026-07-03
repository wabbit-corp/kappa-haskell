# Perceus S2.3 redux — Drop Completion (under the Boehm differential backstop)

Status: **S2.3a + S2.3b LANDED + independently reviewed SOUND** (`5723ec0`, `272be14`), with **S2.3c
implemented by the primitive convention table** and **S2.3d implemented for locally-proven path-local dead
owned flat locals**. S3.2 has since tightened the C backend entry gates needed by free-on-zero: returning-arm
match cleanup and owned projection results through nested/control expressions. S2.2 (dup) +
S2.3-first-cut landed in `d5624e6` but `kdrop` fired ~0×; S2.3a completed the match-destructure cell-drop
so `kdrop` now fires (101 sites / 33 files, 315 `kdup` / 66 files), S2.3b records the consume-vs-read
distinction and consumes it CONSERVATIVELY (dup only a consuming `NonLast`; general scope-close drops still
stay conservative outside the S3.2-proven projection-result subset), and S2.3d emits
branch-entry drops for locally-owned binders proven dead on that selected path. Last verified on 2026-07-02 with
`cabal test kappa-test --test-options='--hide-successes'` at conformance 2094/0; native RC parity is verified by
`KAPPA_PERCEUS_RC=true test/native/run-native-tests.sh`. The DEBUG underflow assert is live, non-vacuous, and clean
over the corpus when those gates pass. The S2.3c storing-primitive audit remains a standing invariant for
later runtime-store precision work.
Companion to [PERCEUS-S2-PLAN.md](PERCEUS-S2-PLAN.md) / [PERCEUS-RC-DESIGN.md](PERCEUS-RC-DESIGN.md).

## 0. Diagnosis (empirical)

Corpus: **63 `kdup(`, 0 `kdrop(`** across `test/native/cases/*.kappa.c`. Smoking gun (`adtcons.kappa.c`):
`match` reads fields out via **borrowing projections** (`kctor_arg`/`kproj`/`krec_at`/`kvariant_payload` —
the runtime accessors all return the stored field/payload pointer without an incref), moves one field out, returns it —
**the scrutinee cell and discarded fields are never dropped.** Every match-destructure leaks its cell.
Root cause: `rcBinderDroppableHere` drops a binder only with **no `LastUse` anywhere**; a
scrutinee gets `LastUse` at the match (its reference "moved into" the match), but the match never discharges
that cell. The move-at-LastUse transfers ownership *to the match*; the match never drops it.

## (a) S2.3a — MATCH-DESTRUCTURE drop (the big one)

Rule for `match s case C f₁…fₙ -> body` when the scrutinee's last use is the match:
**dup each kept (bound, runtime-relevant) field, then `kdrop` the scrutinee cell.** Sound for both:
- **unique** cell (rc 1→0 once S3.2 wires free-on-zero): the surviving fields would be freed by recursive
  descent, so each kept field is `kdup`'d to keep it alive; the cell shell is only actually released after
  the S3.2 flip.
- **shared** cell (rc>1, or S3.1 shared-bit marked): `kdrop` either decrements the thread-local count or is a
  shared no-op; the dup keeps the field count honest for another owner.
- **discarded** fields (`_`, omitted record fields): NOT dup'd; the single `kdrop(scrut)` is their decrement.

**Site:** the cell-`kdrop` goes in `consumeAltBody`, per-arm, against the `scrut_N` (`sv`)
lvalue, alongside the existing `mapM_ rcEmitDrop patDrops`. The kept-field dups go in `bindPatScrut`
and `patBindings`: a surviving slot `pat_k = kctor_arg(scrut,…)` becomes
`pat_k = kdup(kctor_arg(scrut,…))`, keyed by `P.patSlotPos k`. **Decision helper** `rcScrutDropDecision`
in `consumeMatch`: look up the scrutinee `CVar`'s use verdict plus consume bit at `matchScrutPos` — drop the
cell for consuming `LastUse` only when the source flat local owns the value, and for consuming `NonLast` when
the compiled scrutinee use first received its own `kdup`; never for read-only/borrowed scrutinees. A **fresh**
scrutinee (`CCtor`, rc==1, no binder) always drops. Thread the decision into each arm; S3.2 also emits the
paired cleanup before returning-arm `return`s. **Emit the cell-drop as a distinct statement against `sv`** (never folded
into the body) so S5 FBIP swaps the `{dup kept fields; kdrop cell}` pair for `{token=drop_reuse; kreuse}`
as a peephole on the unique path.

## (b) S2.3d — per-path DEAD-BINDER drops

Implemented by preserving the branch-local omission fact instead of asking only whether a binder has a
`LastUse` anywhere. `Ownership.walk` records `oiBranchDropSites :: Map [Int] [BinderId]`: for each `CIf`
arm and `CMatch` arm, binders live in the branch join but absent from that arm's live-in set are listed at
the arm path. `C.hs` resolves those `BinderId`s against the current flat-local metadata (`lvalue`, binder id,
owns-reference bit) and emits `kdrop(local)` at branch entry after the condition/pattern has selected the
path. Read-only projection aliases add owner dependencies to the branch-drop decision, so an owner is not dropped
on a path where a raw borrowed record projection remains live; constructor/data projection paths that first `kdup`
the field remain free to drop the owner. Guarded match arms analyze the guard with the later-arm failure
continuation: if a later arm actually uses a consumed guard argument, the guard use is `NonLast` and codegen emits
`kdup`; if a consumed guard argument is needed only for a later branch-dead drop, that later drop is suppressed
leak-biased until guard-result path ownership is modeled. Guard-success drops also exclude guard uses that actually
move a `LastUse`. The owned-reference proof includes direct constructor values and saturated eta-expanded
constructor applications, because the same `etaCtorApp` recognizer is used by codegen to lower them to fresh `kctor`
allocations.

The backend still re-checks `boDroppable` and `boBorrowed`, and it refuses to guess: boxed/KEnv-only binders,
borrowed binders, incoming worker parameters whose caller-side transfer has not been normalized, unproven
call/projection shapes, and pattern fields that were not first `kdup`'d by the match cell-drop path do not get
S2.3d drops. S3.2 proves owned projection results for the structural subset whose base is an owned flat local
read through the validated read-only use side table, and it materializes those results with `kdup` before any
owner cleanup. If a branch-drop site
lists a droppable binder that no longer resolves inside a top-level flat worker frame, the RC-on backend
records a `gsRcFindings` miss and rejects generation. Capture-free nested flat closures may drop their own
resolved owned flat locals under the same proof; missing outer/captured binders, boxed/CPS paths, and flat
locals whose ownership is resolved but unproven still intentionally emit no drop.

## (c) S2.3b — the CONSUME flag (a real OwnInfo refinement)

`Ownership.walk` classifies a `CVar` by **downstream liveness only** — it does not see the
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
they require a manifestly-owned local and still use the "no consuming `LastUse`" rule only for the subset
whose result ownership is proven. S3.2 duplicates escaping structural projection results when the base is an
owned flat local read through the validated read-only use table; unproven call/projection shapes remain
leak-biased instead of dropping an owner before a borrowed result is materialized.

## (d) S2.3c — the PRIM / runtime-ownership boundary (the one design decision)

**Investigation:** plain `argConvSelect` reported `ArgShared` for **every** prim arg — every prim arrow is
`(~>) = CPi Expl QW False` in the prelude ⇒ `QW` ⇒ `ArgShared` via `Repr.argConvSelect`. Storing prims
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
table classifies the *caller* boundary correctly. S3.1 has closed the UAF-direction derived-container alias
gaps before the free-on-zero flip: `karr_new` now stores the owned `init` in the first boxed slot and
`kdup(init)`s each additional boxed slot, and `krec_without` now `kdup`s every kept residual-record field.
The remaining runtime store bodies below are leak-direction precision work for S3.3; they must not be confused
with UAF blockers for S3.2 because the overwritten/not-stored value stays Boehm-reachable while retained
containers remain off the FREESET. Empirically verified clean under the S2 backstop (RC-on == RC-off, 0
underflow):
- **Overwriting stores** — `karr_set`, `kref_set`, `fiber_local_set`, `krt2_atomic_store`/`exchange` — overwrite a cell without dropping the
  OLD occupant (a write barrier). LEAK-only (safe even post-S3), but each needs a drop-old for a leak-free S3.
- **Not-stored `ArgOwned` args** — `krt2_atomic_compare_exchange` stores `desired` only on
  success; `promise_complete` stores `exitv` only on first completion. On the CAS-fail /
  already-completed path the moved-in `ArgOwned` arg is neither stored nor dropped. LEAK-only; needs a drop.

**Arity-guard alignment pin for S3 (compiler-side).** S3.1 reconciles `argConvSelectGlobal` and `repSelect`
with the ownership runtime-argument filter: implicit binders, `Q0` binders, and kind-domain binders are skipped
by the same helper before an override convention is matched. The original mismatch was inert because no table
entry used an explicit non-`Q0` kind-domain parameter, but the fix prevents a future primitive from
left-shifting an `ArgBorrowed` convention onto a real storing position.

## (e) Owned/borrowed CALLER-drop completeness — folds into (c)

Real gap: passing an **owned** binder to a **borrowing** (`&`) param classifies the use by the *binder's*
liveness (`Ownership.walk` keys on `scBorrowed`, the binder's marker, NOT the call position) ⇒ a binder
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
| **S2.3b** | consuming-vs-read flag (c); close-drops stay conservative outside the S3.2-proven projection-result subset | assert clean; metadata pins transfer vs read |
| **S2.3c** | prim-convention table (d): classify audited primitive publish/read positions; full caller-drop completion still waits for caller-side transfer normalization | `primArgConventionS23c`; ref/TVar/FiberRef ownership regressions; assert clean |
| **S2.3d** | per-path dead-binder drops (b)+(e) for locally-owned flat constructor let-locals, including guarded post-guard omissions, after the path-local ownership facts are explicit | `perceusS23dDeadBinderDrops`; branch-drop miss diagnostic; assert clean; net trends down |

**Risks (under the Boehm backstop: leak/assert now; S3 UAF risks called out explicitly):** **R-double-drop (highest)** — cell-drop +
sibling per-path drop + a move on the same cell; guard by disjoint conditions (cell-drop only when scrutinee
received the reference; per-path drops only on omitting paths); the underflow assert catches overlap before
S3. **R-prim-table-incomplete** — a storing prim missing from S2.3c becomes an S3 UAF risk once caller-drop
completion is enabled; require the `value.c`/`prims.c`/`stm.c`/`rt.c`/`atomic.c` store audit to stay current
before that switch. **R-runtime-store-discipline (S3 precision; see §(d)'s runtime pin)** — S3.1 closes the
`karr_new` and `krec_without` UAF-direction undercounts; drop-old write barriers and CAS-fail/promise-
recomplete drops remain runtime-side leak-direction precision work. **R-arity-alignment (see §(d)'s arity
pin)** — S3.1 reconciles the override arity check with the ownership/runtime-argument filter so future
kind-domain-param prims cannot left-shift a convention onto a real value position.
**R-param-provenance** — worker parameters are not S2.3d-droppable until caller-side transfer normalization
proves borrowed/projection actuals have been converted to owned references; this intentionally preserves soundness
at the cost of leaving param-dead branches as a visible restore item.
**R-returning-arm cleanup** — closed in S3.2 for proven-owned match cells by materializing kept fields and
emitting cleanup before `return`; guarded arms still stay conservative where guard-failure ownership is not
modeled. **R-CDo** — S2.3b walks and validates `CDo` bodies so generated do-kernel paths are
covered by RC checks; drops still do not cross a do-block boundary unless the lowered structure proves ownership transfer.
K_FGN/resource scrutinees must not be cell-dropped because S3.2 free-on-zero deliberately excludes resource
cells from the FREESET. **R-path** — every new lookup (`matchScrutPos`, `patSlotPos k`, per-arm) uses the shared
`PathScheme` constants; `gsRcFindings` miss-log is fail-closed under `KAPPA_PERCEUS_RC=1`, including
S2.3d branch-drop sites whose droppable binders no longer resolve in a top-level flat worker frame.

## (g) Verification — the backstop now genuinely exercised

1. **Underflow assert non-vacuous (primary):** after S2.3a, `grep -c kdrop( *.kappa.c` must be ≫0 (drops
   fire across every match-bearing program); the assert stays clean (drops never drive rc below the
   Boehm-live floor). This proves the placement/backstop half is exercised; S3.2's free-on-zero flip still
   needs its own UAF/oracle run before claiming actual reclamation.
2. **Leak-trend net ≈ 0 per program** (`krc_report`), not monotonic-growth — modulo legitimately-never-
   dropped CAFs / `main`'s result. A persistently negative net with no live escapees = a missed drop.
3. **Outputs byte-identical** (last checked 2026-07-02: conformance 2094/0; native RC parity by
   `KAPPA_PERCEUS_RC=true test/native/run-native-tests.sh`) — dup/drop are rc-maintenance while Boehm frees.
4. **Static ground truth green** (`crossCheckBodies`/`argConvBodies`, plus `primArgConventionS23c`) — new
   OwnInfo fields additive; the S2.3c prim table must keep `argConvBodies` and the direct convention matrix
   consistent with the audited storing-vs-borrowing primitive set.
5. **RC path lookup is zero-miss** — under `KAPPA_PERCEUS_RC=1`, `generateC` rejects nonzero
   `gsRcFindings`, and the native/LLVM harnesses assert the zero-miss diagnostic in redirected build logs.
6. **Resource regressions unchanged** (`usingsusp.kp`/`usinginterrupt.kp`) — no spurious drop inside a
   do-scope; S3.2 keeps `K_FGN` out of the FREESET and pins runtime-private FGN payload marking.

## Critical files
- `src/Kappa/Backend/C.hs` — cell-drop in `consumeAltBody`/`consumeMatch`; kept-field dups in
  `bindPatScrut`/`patBindings`; conservative `rcBinderDroppableHere`/`rcPatSlotDroppableHere` gates plus S2.3b
  consume/read dup filtering. S2.3d per-path local drops are implemented for locally-proven owned flat locals;
  caller-drop completion, parameter-drop restoration, and result-ownership-aware close drops remain later
  sub-stages.
- `src/Kappa/Ownership.hs` — position-aware consuming flag in `walk`, forced global/local parameter
  telescopes, pattern-bound field type recovery, additive `OwnInfo` consume/read and branch-drop fields, and
  cross-check validation for the stored side tables.
- `src/Kappa/Backend/Repr.hs` — `argConvSelect`/`argConv` plus `argConvSelectGlobal`; the audited
  primitive convention table is S2.3c.
- `src/Kappa/Prelude.hs` — storing `newRef`/`writeRef`/`__newArray`/`__arrayWrite` vs borrowing
  `show*`/`print*` positions the table classifies.
- `runtime/value.c` / `runtime/kappart.h` — stores (`kref_new`, `karr_set`, `kctor`), reads
  (`kctor_arg`, `kproj`), `kdrop` free-on-zero for the S3.2 FREESET, and the poison-on-free runtime oracle.
