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
| `CSort`, `CPi`, `CRecordT`, `CVariantT`, `CSigT` in value position | These are **type-level** terms. By §12.2 (quantity-0 binders are erased) and §31.2 (erasure), types/kinds/signature-types do not survive to runtime; an erased implicit type argument is passed as an unused placeholder, and no other value position holds a raw sort/Pi/record-type/variant-type/sig-type. |
| `CMeta` | A fully-elaborated **accepted** program has every metavariable solved (§16.3 implicit resolution succeeds or the program is rejected). An unsolved meta in codegen is an elaboration-invariant violation, not a language feature. |
| `CQuote` | A syntax quote is an **elaboration-time / staging** value handled by the §30.2.4 elaboration-time evaluator (§21 quotes, §23 staging). It is not produced as an ordinary native runtime value by the lowering of a runtime term. |
| bare positive-arity constructor reference | The elaborator **eta-expands** a constructor used as a value into a saturated `CCtor` under lambdas (§10.1, `etaCtor`); a bare positive-arity `CGlob` constructor never reaches codegen for an accepted program. (Verified: `Some`/`Cons` as values compile.) |
| `KUsing` | `using` is **desugared to a monadic bind** during elaboration (`Kappa.Check`, §18); a `KUsing` do-kernel item never reaches codegen. (The interpreter's `KUsing` arm is likewise dead.) |

These are exercised by no accepted program at runtime, so they are not
§27.7 conformance gaps. The guards exist defensively and cite the spec.

## Remaining implementable work (honest compile-time rejection)

These ARE runtime features; the backend rejects them precisely
(`E_BACKEND_UNSUPPORTED` naming the construct) rather than miscompiling.
They are implementable (no spec contradiction) and tracked for completion.

| Gap | Status / plan |
| --- | --- |
| **Table-driven Unicode** primitives — `__normalize` (NFC/NFD/NFKC/NFKD, UAX#15), `__caseFold`, and the UAX#29 segmentation ops `__stringGraphemes`/`__graphemeCount`/`__stringWords`/`__stringSentences` | The single genuinely large item: it requires the Unicode database (decomposition, combining class, composition exclusions, case-fold, and grapheme/word/sentence break-property tables) that the interpreter holds in `Kappa.UnicodeData`. Plan: emit those tables as a generated C source (auto-derived from `Kappa.UnicodeData`, so no manual transcription) plus a C port of the (well-specified) algorithms. Until then, a program using them is rejected at build time. |
| `LitByte` / `LitBytes` / `LitGrapheme` literals and the byte/bytes/grapheme prims (`__bytes*`, `eqByte`/`showByte`/`eqBytes`/`showBytes`/`eqGrapheme`/`showGrapheme`) and `Rational` (`addRat`..`showRat`, `ratOfDouble`) | Straightforward to port (memcpy/memcmp over a byte buffer; Rational as a normalized ratio over two bignum lanes with `mpz_gcd`). In progress. |
| Nested binding or-pattern (`CPOr` that binds variables *inside* a larger pattern) | Top-level or-patterns are split into alternatives and fully supported (including binders). A binding or-node *nested* within another pattern needs decision-tree compilation; lift it to top-level alternatives meanwhile. Bounded, rare. |
| `defer` nested in a loop/if body | A `defer` at do-block top level is fully supported (LIFO at scope exit). A `defer` inside a loop/if body is a distinct per-iteration scope whose timing the do-block-level model would change, so it is rejected rather than run at the wrong time. Bounded; needs per-scope defer frames. |

The `no-core-body` guard is a catch-all for a reachable global with neither
a recorded core body, a primitive value, nor a constructor — after
dictionary/projection capture it is not expected for accepted programs and
is reported rather than approximated.
