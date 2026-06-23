# Readability backlog — deferred structural work

Running list of structural changes that would improve readability but were
**intentionally deferred** so the current pass stays "in-code prose only"
(comments, docs, and at most light within/between-module moves — no logic
changes, no big refactors). Revisit when there's appetite for a structural pass.

Each item: what, why it would help, rough size/risk.

## High value

- **Split `Check.hs` (~14.4k lines) into ~8 cohesive modules.** It is the single
  biggest navigability barrier. The 23 existing `-- ── … ──` dividers already
  fall on clean seams. Proposed cut (line numbers approximate, at audit time):
  - `Check.State` — state, `Ctx`, `DataInfo`/`CtorInfo`/`TraitInfo`, bind/refine helpers (~85–948)
  - `Check.Unify` — `unify`, `qSubsumes`, occurs check, meta solving (~949–1594)
  - `Check.Names` — name resolution/scoping (~1595–1936)
  - `Check.Implicits` — implicit-arg + trait/instance resolution ladder (~1937–3037)
  - `Check.Elab` — `infer`/`check`/spines, the heart (~3038–4490)
  - `Check.Elab.Records` / `.Literals` / `.Control` — records/projections, literals, lambdas/effects/match/do (~4490–9170)
  - `Check.Elab.Meta` — quotes/macros/Elab, derivation reflection, comprehensions (~9170–10980)
  - `Check.Declarations` — `checkModule`, decls, instances, positivity (~10980–12884)
  - `Check.Totality` — SCC edges, size-change, measures (~12885–14362)
  Size: large. Risk: low-ish (mechanical, but lots of import wiring + export lists).

- **Extract `Pipeline.compileFilesWithCfgInj`'s ~300-line `let`
  (`Pipeline.hs:352-649`) into named phase functions.** Right now the end-to-end
  story (parse → name → merge fragments → dependency-order → per-module check →
  usage → re-zonk) is one tangled expression interleaved with edge-case
  diagnostics. A top-level skeleton like `parse >=> resolve >=> check >=> usage`
  would make this file the readable "spine" of the whole compiler. Size: medium.

## Medium value

- **`Check.infer` / `Check.check` are ~430-line `case` ladders.** Even without
  splitting the file, each arm-group (literals, application, records, control)
  could become a helper with its own doc. Currently mitigated only with an
  arm-index comment. Size: medium. Risk: low.

- **`Lexer.hs` is one ~900-line `lexSourceTokens` with every scanner as a local
  `where` binding** (`scanString`, `splitInterp`, `dedentMultiline`, …). Hoisting
  the independent scanners to top-level (where they don't need the closure) would
  let each be read and documented on its own. Size: medium.

- **`Usage.hs` terse data model** — `data Cnt = Cnt !Int !Int ![Span] !Int …`
  (positional 6-field, `Usage.hs:164`), `data R`, `data S`, magic `wInf = 1000000`
  standing in for ω. Converting to record syntax with named fields (a mechanical
  change, but touches many call sites) would make the usage algebra self-describing.
  Size: medium. Risk: medium (many constructors/patterns).

- **`Eval.evalPurePrim` (~270 lines) and `Interp.runPrimIO'` are flat
  string-keyed `case` ladders over primitive names.** Grouping them (arithmetic /
  bytes / string / IO) behind sub-dividers or sub-tables would make the primitive
  surface navigable. Size: small–medium.

## Low value / nice-to-have

- The `__`-prefixed "internal primitive" naming convention (e.g. `__bytesBreakIndex`)
  is never stated in one place. A one-line note where primitives are registered
  would do; ideally a shared constant/legend.

- Several `Eval.hs` comments are commit-message archaeology (performance history
  of `force`/spine handling). Useful to a maintainer, noise to a learner — could
  move to a `NOTES`/`PERFORMANCE.md` cross-reference.

## Definition ordering (read top-to-bottom)

Goal: each module should read like a chapter — orientation, then the data it
works on, then the headline entry point, then supporting detail. Haskell is
order-independent at the top level, so reordering is behavior-preserving; the
only friction is diff churn and `where`-block boundaries.

Done as small moves:
- `Syntax.hs`: the AST-traversal helpers (`projBinderGroups`, `surfaceThisRefs`,
  `surfaceVarNames`, `projYieldPlaces`) were interleaved in the middle of the
  `data` catalog; moved to an "AST traversals and span helpers" section at the
  bottom next to `exprSpan`\/`patternSpan`, so the type catalog is contiguous.

Larger reorders still worth doing (deferred — bigger diffs / tied to splits):
- **`Check.hs`: headline-first per section.** Within several of the 23 sections
  the main entry sits *below* its helpers (Haskell's bottom-up habit). For a
  top-down read each section should lead with its documented entry point, then
  helpers. Best done together with the module split (above), since the cut
  points are the same. Size: large.
- **`Eval.hs`: lead with the NbE triple.** `eval`\/`force`\/`quote`\/`convertible`
  are the headline of the module but `force` (217) and `quote` (439) are
  separated by `matchPat` and the spine helpers, and the ~270-line `evalPurePrim`
  table sits in the middle of the conversion machinery. Consider grouping the
  four NbE functions adjacently up top, then the primitive tables last. Size: medium.
- **`Interp.hs` / `Eval.hs` primitive tables.** (Also under "Medium value"
  above.) The flat string-keyed `case` ladders read better split into labelled
  sub-groups (arithmetic / bytes / string / IO), each its own `where` helper or
  divider — a reorder + grouping, not just comments. Size: small–medium.
- **General convention to settle:** pick one — "headline entry first, helpers
  below" (book style) vs. Haskell's "helpers first, entry last" — and apply it
  consistently per module. Currently mixed. Documenting the choice in CONTRIBUTING
  would stop the two styles fighting. Size: small (decision) + ongoing.

## Naming suggestions (deferred — renames touch many call sites)

These names obscure intent. The documentation pass has explained them in
comments; renaming would let the code read without the gloss. All are
behavior-preserving but ripple across call sites, so they're deferred.

**`Usage.hs`** (the worst offenders — single letters for core types):
- `Cnt` → `Use` / `UseCount` — one binding's usage interval + metadata.
- `S` → `AnalysisState`; `M` (= `State S`) → `Analysis`.
- `R` → `WalkResult`; its fields `rU`/`rT`/`rL` → `wrUsage`/`wrTaint`/`wrLatent`.
- `wInf` (= 1000000) → `omegaBound` / `qOmegaSentinel` — an arbitrary large
  stand-in for ω; the magic literal should be a named sentinel.
- The `…C` helper suffix (`zeroC`/`oneC`/`seqC`/`altC`/`scaleC`) just means
  "of `Cnt`"; follows whatever `Cnt` becomes.
- `cLo`/`cHi`/`cTouch` → `useLo`/`useHi`/`useTouched`.

**`Check.hs`** (local, lower-ripple):
- `qok` (threaded through `unify`) → `allowQSubsumption`.
- `ec_` accessor → spell out the eval/conversion context it returns.
- `goTop`/`go` workers inside `unify`/`infer` → `unifyAt`/`inferArm` etc.

**`Eval.hs`**:
- `forceQ` vs `force` vs `vforce` — three force-like names; clarify which is
  the conversion-time vs runtime variant in their names.
