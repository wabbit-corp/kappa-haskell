# Immediate / pointer tagging — cross-runtime research (for UNBOXING Stage 1)

Fact-checked survey (GHC, OCaml/Zarith, V8, HotSpot, BDW-GC, Koka/Perceus;
.NET CLR + Swift named but not primary-source-verified this round) distilled into
actionable guidance for the Kappa Stage-1 immediate-tagging design. See
[`UNBOXING-DESIGN.md`](UNBOXING-DESIGN.md) §5/§7 for the staged plan this refines.

## The landscape

- **Low-bit tagging of word-aligned pointers is the canonical scheme** for
  functional/JS runtimes. OCaml: 1 bit (`Is_long(x)=x&1`); odd = 63-bit int, even
  = pointer. V8: low bit 0 = Smi, 1 = heap pointer (+ 2nd bit strong/weak). GHC:
  the 2 (32-bit) / 3 (64-bit) spare low bits of a word-aligned closure pointer
  encode a constructor tag/evaluatedness (a 2-bit tag covers >95% of `case`s,
  3-bit ~99%; the optimization gave ~14% speedup at ~2% code growth by killing
  indirect-branch mispredicts). The 3-spare-bits-on-64-bit budget comes directly
  from 8-byte object alignment — exactly Kappa's reserved low-3-bit budget.
- **HotSpot / CLR / Swift do NOT tag immediates** — every value is a header-+-body
  heap object (a HotSpot `Integer` is a 12-byte-header object; the JVM spec
  "provides no way of encoding tagged pointers"). This is the per-scalar
  allocation cost Kappa's tagging exists to avoid — it validates the motivation.

## Recommendations for Kappa Stage 1 (cited)

1. **Tag width — use the 3-bit tag (61-bit Int), not OCaml's 1-bit (63-bit).**
   The extra codes are worth the 2 lost int bits *for room to grow the immediate
   kinds*, the way V8 (2nd bit = strong/weak) and GHC (3 bits = ctor tag) use the
   higher spare bits. (`+/-2^60` still covers every realistic small Int; overflow
   escapes to GMP.) **CORRECTION to the Stage-0 comment:** `b011..b111` are for
   *additional immediate KINDS* (e.g. an immediate `Char`), **NOT** the future
   Perceus borrow / thread-shared discriminator. Perceus encodes that
   discriminator in the **sign of a heap-object header field** (Koka folds
   "thread-shared atomic / unique-free / shared-fast" into one inlined
   `rc <= 1`-style compare) — an *immediate* is value-copied and never
   reference-counted, so the immediate tag space only ever distinguishes immediate
   kinds. Putting an RC discriminator in the *pointer* low bits would also alias
   (the same object reached via a borrowed vs an owned reference would carry
   different tags). Keep the RC discriminator in the header; keep `b011..b111` for
   immediate kinds. *(GHC's "tag 0 = always-safe unknown" asymmetry is
   lazy-thunk-specific; Kappa's strict/eager immediates need no reserved "unknown"
   code.)*

2. **Canonicalize singletons — one representation per value.** With `Bool`/`Unit`/
   `Nil`/`None` as `b010` immediates and small `Int` as `b001`, any pre-existing
   **cached heap singleton** (`kint_cache[-16..256]`, `the_true`/`the_false`,
   `the_unit`) is a *second* representation of the same logical value and breaks
   pointer-identity equality against its immediate twin. The audit must (a) route
   construction of these values through the immediate encoding ONLY (retire the
   boxed singletons as carriers), and (b) make equality compare **tag+payload,
   never a raw pointer**, for tagged values. (Zarith's `ml_z_reduce` guarantees
   equal values share a representation; OCaml already encodes `()`/`[]`/`false`/
   `true` as immediates, not heap singletons.)

3. **Bignum boundary — Zarith's dual representation + canonical reduction.** Small
   ints inline (`b001`), big ints heap GMP (`K_BIGINT`). Correctness across the
   boundary is *engineered, not free*: **never leave a boxed bignum that fits in 61
   bits — always re-tag it inline** (`ml_z_reduce`: "if it fits in an int, store an
   int, not a block"), or `==`/ordered-compare/pattern-match silently break. Int
   equality/compare must normalize across inline-vs-GMP (a custom compare handling
   int-vs-int / int-vs-block(by sign) / block-vs-block), and `klit_eq`'s tag
   short-circuit must NOT be used for the Int/Integer arms (route through a
   value-normalizing compare like `kint_cmp`). V8 keeps the Smi/HeapNumber boundary
   correct by the same discipline.

4. **NaN-boxing — do NOT.** Unsound under conservative Boehm: a high-bit-tagged
   immediate leaves its **low 32 bits looking like a pointer**, causing accidental
   retention (Wingo, V8/Guile implementer). Low-bit tagging is the opposite — an
   odd/`b001`/`b010` word is *misaligned* and dismissed as a non-pointer cheaply on
   the GC fast path. NaN-boxing's one benefit (a single slot holding doubles+ints+
   pointers) is irrelevant here (we don't pack IEEE doubles immediately) and the
   conservative-GC cost is prohibitive. Kappa's low-bit + interior-pointers-OFF
   contract is exactly right: alignment filtering rejects tagged immediates first,
   so the conservative-scan tax falls only on the rarer words that *look* like
   aligned heap pointers.

5. **The ~299-site deref tax — triage by hot path; it won't shrink to a handful.**
   GHC's untagging concentrated at a few RTS sites (GC, ENTER, indirection entry,
   heap-inspection, profiler, sanity) — but **only because GHC's codegen
   auto-inserts untagging at every `case`/tail-call; Kappa has no such pass**, so
   the 299 sites must be triaged by hot-path frequency, not assumed to collapse.
   Keep the boxed-heavy tax within ~5–10% (the `ctor-build` + `ctor deref boxed`
   go/no-go gate) by: **(a) `b000` = heap pointer (zero low bits) so a real pointer
   deref needs NO masking on the common path** — only immediates carry nonzero low
   bits, so `kderef` of a known pointer is free and the test is a single
   `& 7`/branch; **(b) hoist/share one tag test across multiple field accesses of
   the same object** rather than re-testing per `->as.*`. The `kderef` debug assert
   (installed in Stage 0) is the audit's safety net: any missed raw deref of an
   immediate trips it under the test suite before it segfaults on an odd word.

## Open questions (carry into Stage 1 / later)

- Realistic hot-path subset of the 299 sites; does `b000`=pointer genuinely let
  the common deref skip masking (validate with the `ctor deref boxed` bench delta).
- After the LLVM backend + Perceus precise RC land, does the conservative-GC
  alignment argument still bind, or can Kappa **reclaim the 2 bits (61→63-bit
  Int)** since precise RC no longer needs odd words to be GC-invisible?
- .NET CLR object-layout/boxing and Swift's tagged-pointer + value-witness model
  were not primary-source-verified this round (only HotSpot's no-immediates design
  was) — revisit if their specifics become decision-relevant.

## Primary sources

GHC pointer-tagging paper (`simonmar.github.io/bib/papers/ptr-tagging.pdf`) + RTS
wiki; OCaml `runtime/caml/mlvalues.h` + `ocaml/Zarith`; V8 `v8.dev/blog/pointer-compression`;
Wingo `wingolog.org/.../value-representation-in-javascript-implementations`; BDW-GC
`hboehm.info/gc/{gcdescr,conservative}.html`; Perceus PLDI'21
(`microsoft.com/.../perceus-pldi21.pdf`); HotSpot `shipilev.net/jvm/objects-inside-out`.
