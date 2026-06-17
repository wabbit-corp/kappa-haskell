# Native backend: escalations and remaining work

Per Spec.md §27.7 a conforming backend must compile **every accepted
program** correctly, with no target-limitation excuse. This document
classifies every remaining `E_BACKEND_UNSUPPORTED` path the native backend
can emit, into one of:

* **Escalated — not a runtime feature.** The construct is provably not the
  runtime value of an accepted, erased program (a type-level term erased
  per §12.2/§31.2, an elaboration invariant, or a form desugared away
  before codegen). Reaching it is an internal-invariant violation, reported
  (never silently miscompiled) per §27.7. These are *not* missing features.
* **Remaining implementable work.** A genuine runtime feature not yet
  implemented; the backend rejects it honestly at compile time (no silent
  divergence). These are tracked here with a concrete plan — they are
  implementable (not spec contradictions), so the rejection is a checkpoint,
  not a final limitation.

This complements the gap audit (a 16-agent adversarial workflow against
§27.7); see `docs/NATIVE_FFI_DESIGN.md` and `docs/NATIVE_BACKEND.md`.

## Escalated — not runtime features (spec-cited)

| Construct | Why it is never a runtime value of an accepted program |
| --- | --- |
| `CSort`, `CPi`, `CRecordT`, `CVariantT`, `CSigT` in value position | These are **type-level** terms (§12.2, §31.2). They CAN appear syntactically in a value/field/argument position of an accepted program (an explicit `(t : Type)` binder/field, a type stored in a constructor) — but the spec mandates such compile-time/static-object positions be erased (§11.1.6.1, §11.1.6.2). The backend therefore **erases** them to the unit placeholder (`compileErasableArg`, matching the interpreter, which stores the evaluated type value but never inspects it). The `compile` guard is reached only if such a term survives to a *non-erasable* value position, which an accepted runtime program never produces. |
| `CMeta` | A fully-elaborated **accepted** program has every metavariable solved (§16.3 implicit resolution succeeds or the program is rejected). A residual meta in an erased dictionary/type position is erased like any type-level term; a meta in a genuine value position is an elaboration-invariant violation, not a language feature. |
| `CQuote` | A syntax quote is an **elaboration-time / staging** value (§21 quotes, §23 staging, §30.2.4). It may be stored in a `Syntax _` field of an accepted program; that field is a compile-time position and is **erased** to the unit placeholder (§31.2), exactly as the interpreter ignores it. The `compile` guard remains for a quote reaching a non-erased runtime value position, which an accepted runtime program never produces. |
| bare positive-arity constructor reference | The elaborator **eta-expands** a constructor used as a value into a saturated `CCtor` under lambdas (§10.1, `etaCtor`); a bare positive-arity `CGlob` constructor never reaches codegen for an accepted program. (Verified: `Some`/`Cons` as values compile.) |
| `KUsing` | `using` is **desugared to a monadic bind** during elaboration (`Kappa.Check`, §18); a `KUsing` do-kernel item never reaches codegen. (The interpreter's `KUsing` arm is likewise dead.) |

Type-level / staging terms in value, field, record-field, and argument
positions are **erased** to a unit placeholder (`compileErasableArg`,
preserving constructor arity so positional projection stays aligned with
the interpreter — verified: a `(t : Type)` / `Syntax _` field stored and
the value field projected gives identical output native vs. interpreter).
The `compile`-level guards therefore back-stop only genuinely non-runtime
positions; they are not reached by accepted runtime programs.

## Remaining implementable work (honest compile-time rejection)

Every spec-mandated **runtime** feature the native backend can encounter is
now implemented — there is no accepted run-mode (`UIO`) program the backend
rejects.  The `E_BACKEND_UNSUPPORTED` mechanism remains only as a defensive
backstop for genuinely non-runtime forms (below).

### Implemented (no longer rejected)

| Feature | How |
| --- | --- |
| **Table-driven Unicode** — `__normalize` (NFC/NFD/NFKC/NFKD, UAX#15), `__caseFold`, UAX#29 segmentation (`__stringGraphemes`/`__graphemeCount`/`__graphemeValid`/`__graphemeOfString`/`__stringNextGrapheme`), `__stringWords`/`__stringSentences` | `tools/gen-ucd-c.py` parses the committed `Kappa.UnicodeData.hs` (the exact tables the interpreter uses) into `runtime/kappa_ucd.h`; `kappart.c` ports the `Kappa.Unicode` algorithms over those tables (case-fold is derived from `str.casefold()`). Verified native ≡ interpreter on the §29.4 conformance programs (`std-unicode-run`, `std_hash_run`). |
| `LitByte` / `LitBytes` / `LitGrapheme` literals + `std.bytes` prims + the linear `BytesBuilder`; §29.4 scalars / `StringBuilder` / string cursors / incremental UTF-8 decoder; §29.3 hash, §29.1 bitwise, §20 collection carriers; `Rational` | Ported to `kappart.c` (byte/UTF-8 buffers; cursors as scalar indices; FNV-1a lane; Rational over GMP). Verified native ≡ interpreter (`bytes`, `ubuilders`, `unidata`, `uhash`, `rational_run`). |
| Type-level / staging terms in value positions (`(t : Type)`/`Syntax _` field/arg, a `Type`/`Syntax`-typed global or local `let`) | Erased per §31.2 (`compileErasableArg`, the `compile`-level guards, the `CLet` rhs, and the no-body global accessor **only when the global is genuinely type-level** — a data/trait name or sort-typed builtin); accepted programs build and run natively (verified: a type/quote field projected, a `let t = Int`, a top-level `Syntax` global). |
| **Real value globals** — a top-level *prefixed* binding (`let 1 x`/`let &x`, the PVar pattern path) and a §9.1.1 `projection` selector | `recordCoreBody` captures their elaborated core body so the backend lowers the real value; without it they reached the no-body accessor and were erased to unit (a silent miscompile, now both fixed and guarded — see the `no-core-body` note below). Verified native ≡ interpreter (`prefixbind`, `projection`). |
| Stack-safe **local `let rec`**, mutual / value-indirect tail calls, AND **IO-`do` sequencing tail recursion incl. `defer`** | Trampoline `kbounce` for non-self tail calls; `kio_tail`/`kio_effect`/`kio_finally` for tail IO actions (the last carries §18.7 finalizers on a heap stack).  Constant C stack to depth 5,000,000 (§27.5A.3). |
| **`defer` nested in a loop/`if` body** (§18.7 per-scope frames) | Each scope (do-block, loop iteration, `if` branch) gets its own defer frame, run LIFO at its exit and at every `break`/`continue`/`return` that unwinds it (`gsScopeDefers` + `lcScopeDepth`; verified: per-iteration defer, defer-before-break, labelled-break LIFO across two scopes, early-return unwinding — all native ≡ interpreter). |
| **Lazy `defer` evaluation** (§18.7) | The deferred action is a suspended `kio` thunk (`compileDeferAction`) capturing the env, evaluated/run at scope exit — not eagerly at registration — so it observes mutations between registration and flush (verified `deferlazy`: mutated-var, running-accumulator, guarded-fault native ≡ interpreter). |
| **Nested binding or-pattern** (`CPOr` binding variables, §17.2.3) in `match`, `let?`, and the `let?` else residue | Distributed into the Cartesian product of or-free alternatives (`distributePat`); in `let?` the alternatives are tried in source order (first match wins) before the else (verified native ≡ interpreter — `letqor`). |
| **`let?` else residue** (§18.2.1) | The else's refutation residue pattern is tested against the scrutinee (`patTest` + `krt_fail` on a refutable mismatch, mirroring the interpreter's `matchPat ec rp x`); never silently binds the wrong constructor's fields (verified `letqelse`/`letqmiss`). |
| `__atomicRepEq` (§29.1 `atomicCompareExchange`) | Structural representation equality over canonical runtime values (`kvalue_rep_eq`). |

### Genuinely non-runtime (defensive `E_BACKEND_UNSUPPORTED` backstop only)

Not reachable by an accepted **run-mode** program; retained so a future
internal-invariant break is reported, never silently miscompiled:

* a bare un-eta-expanded positive-arity constructor reference, and a
  `KUsing` kernel item — both elaboration invariants (`§10.1` eta-expansion;
  `using` desugars to a bind in `Kappa.Check`);
* a primitive the linked runtime does not implement — the §21 symbol /
  §23 staging reflection prims (`sameSymbol`, `closeCode`, `genlet`, …),
  which live in the `Elab` (elaboration) monad and therefore cannot occur
  in a `UIO` runtime program; and algebraic-effect `handle` (`__handleEff`/
  `runPure`), which is `E_UNSUPPORTED` upstream in the interpreter itself.

### Documented representation limits (compile + run; bounded by C stack)

Genuinely non-tail recursion is bounded by the C stack like any deep
non-tail recursion (the interpreter is also O(n) here; fail-stop, never a
wrong answer; `ulimit -s` raises the bound): the recursive call in the
**bound leg** of `bindIO`/`ioThen` (left-nested `>>=`), a deeply-recursive
`!`-splice, and an `if`-branch recursion that is not the do-block's last
item.  Multi-arg **mutual** recursion trampolines through the curried
closure (one closure allocation per step; self- and arity-1 recursion are
allocation-free).

The `no-core-body` arm of `emitGlobal` erases to the unit placeholder **only**
when the global is genuinely type-level (a data/trait name or a sort-typed
builtin like `Integer`). For a global with a real value type but no recorded
core body — neither a primitive, a constructor, nor a captured
dictionary/projection/let body — it reports `E_BACKEND_UNSUPPORTED`
(fail-stop, no executable) rather than erasing a real value to unit. After
`recordCoreBody` covers the let-decl PVar (prefixed-binding), trait-member,
dictionary, and `projection` paths, no accepted program reaches this arm with
a real value; it is a defensive backstop that surfaces a future capture gap
honestly instead of silently miscompiling it (two such gaps — prefixed
bindings and `projection` globals — were found by review and fixed at the
source).
