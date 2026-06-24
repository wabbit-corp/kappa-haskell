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

- **`Usage.hs` terse data model** — DONE. `Cnt` (positional 6-tuple) is now the
  record `UseCount` with named fields, and the combinators (`seqUC`/`altUC`/
  `scaleUC`/…) use field syntax instead of positional matching; `R`/`S` renamed,
  `wInf` → `omegaBound`.

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
  move to a `docs/notes/PERFORMANCE.md` cross-reference.

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
- **`Eval.hs` / `Interp.hs` primitive tables.** (Also under "Medium value"
  above.) `evalPurePrim` (~270 lines) and `runPrimIO'` are flat string-keyed
  `case` ladders; splitting them into labelled sub-groups (arithmetic / bytes /
  string / IO), each its own `where` helper or divider, would make the primitive
  surface navigable — a reorder + grouping, not just comments. Size: small–medium.
  (Note: `Eval.hs`'s top-level sectioning — Evaluation → Quotation → Conversion
  → primitives, each led by its headline function — already reads well; only the
  primitive tables need work.)
- **General convention to settle:** pick one — "headline entry first, helpers
  below" (book style) vs. Haskell's "helpers first, entry last" — and apply it
  consistently per module. Currently mixed. Documenting the choice in CONTRIBUTING
  would stop the two styles fighting. Size: small (decision) + ongoing.

## Naming suggestions

These names obscured intent; the documentation pass explained them in comments,
and the worst are now renamed (all were module-internal, so behavior-preserving
and contained — GHC verifies completeness).

**`Usage.hs`** — DONE (all were internal to the module):
- `Cnt` → `UseCount`; accessors `cLo`/`cHi`/`cTouch` → `ucLo`/`ucHi`/`ucTouched`;
  combinators `zeroC`/`oneC`/`touchC`/`evC`/`seqC`/`altC`/`scaleC` → `…UC`.
- `S` → `AnalysisState`; `M` → `Analysis`; `R` → `WalkResult` (fields
  `rU`/`rT`/`rL` → `wrUsage`/`wrTaint`/`wrLatent`).
- `wInf` (= 1000000) → `omegaBound` (a named sentinel for ω).

**`Check.hs`** — DONE: `qok` (threaded through `unify`) → `allowQSubsumption`.
- Still deferred (riskier — `go` is used everywhere; `ec_` is exported-ish):
  `ec_` accessor → spell out the eval/conversion context it returns;
  `goTop`/`go` workers inside `unify`/`infer` → `unifyAt`/`inferArm` etc.

**`Eval.hs`** — deferred: `forceQ` vs `force` vs `vforce` are three force-like
names; clarify which is the conversion-time vs runtime variant.

## Record field prefixes vs. dot syntax (codebase-wide decision)

Every record in the codebase prefixes its fields with a type abbreviation —
`Pos {posLine, posCol}`, `Span {spanFile, …}`, `Ctx {ctxEntries, …}`,
`UseCount {ucLo, …}`, `BuildConfig {bcName, …}`, etc. This is the standard
Haskell workaround: record field selectors are ordinary top-level functions in
one shared namespace, so two records with a bare `name` field would clash. It's
extremely common but widely considered a wart (the alternative camp uses
lens-style `_name` + `makeLenses`).

GHC 9.14 (this repo) supports the modern alternatives:
- `OverloadedRecordDot` → `record.field` access (the Kappa-like syntax). Purely
  additive: can be enabled project-wide with zero breakage; existing `f x`
  selectors keep working. But fields keep their prefixes, so you get
  `x.ucLo`, not `x.lo` — a mild win.
- `DuplicateRecordFields` + `NoFieldSelectors` → drop the prefixes entirely
  (`UseCount {lo, hi, …}`, accessed `x.lo`). This is the full Kappa-like
  experience, but it's a large migration: rename every field across every
  record AND rewrite every access site from `field record` to `record.field`.
  `NoFieldSelectors` is per-module and removes the `f x` selectors, so it can't
  be adopted piecemeal without converting that whole module's call sites.

**Hard rule (correctness, not style): never dot-access a partial field.**
`OverloadedRecordDot` on a field that isn't in every constructor desugars to a
partial `getField` that crashes at runtime on the wrong constructor — the same
footgun as the old partial selectors (`tBackend t`). Dot access is only sound on
__single-constructor records__ (every field total). A partial field must be read
inside a `case`/pattern match that has already fixed the constructor. So the
dot-syntax house style applies to single-constructor records; sum types with
per-constructor fields stay pattern-matched.

**Pilot — DONE on `Build.Lock.LockEntry`** (single constructor, 3 total fields):
fields are now unprefixed (`kind`/`key`/`identity`) and read as `e.kind` via
`OverloadedRecordDot` + `NoFieldSelectors`; the only consumer (`app/Main.hs`)
uses dot too. Construction sites in `Build.Plan`/`Backend.NativeProbe` are
positional, so they were untouched. This is the reference for what the house
style looks like — review it to decide on broader adoption.

Recommendation: a full migration is large, but it can proceed
record-by-record (single-constructor records first), each contained. Do NOT
migrate sum types with partial fields to dot access (see the hard rule).

### Phase 1 — Build subsystem: DONE
`Build.Types` (incl. the `Target` restructure below), `Build.Reify`,
`Build.Plan`, `Build.Lock`, and the build commands in `app/Main.hs` all use the
dot-syntax house style now. `Target` was restructured to total-by-design:
`Target {name, spec}` with `spec :: TargetSpec` a sum whose variants each carry
a single-constructor spec record — so the partial-field footgun is gone and all
dot access is sound. Verified: build clean, conformance 1342/1342, manifest
`--check` renders all targets. This is the reference implementation of the style.

### Phase 2 — Backend interface records: DONE
- `BuildOptions` (`Backend.Driver`) → unprefixed dot fields; consumer `Main`.
- `ResolvedNativeSymbol` (`Backend.NativeFfi`) → unprefixed dot fields
  (`rnsModule` → `moduleName`, since `module` is a keyword); consumers
  `Build.Plan`, `Backend.C`, `Pipeline`, `Main`, `Driver` each gained
  `OverloadedRecordDot`. Verified: build all clean, conformance 1342/1342.

### Remaining phases (single-constructor records)
- **Backend internal plumbing** (parallel-safe, lower ROI): `Backend.C`'s codegen
  records (`GenState`/`LoopCtx`/`TailInfo`/…) — `GenState` is accessed pervasively
  across C.hs (~3.4k lines), a big internal sweep; `Backend.NativeProbe`
  (`NativeProvenance`/`PkgInfo`/`HdrInfo`); `Backend.HeaderGen`.
- **Front-end records** (`Binder`, `LetDef`, …) — HIGHER readability value, but
  consumers include `Check.hs`, which the parallel team is actively modifying.
  Migrating these (and especially the core types below) would force dot
  conversions across `Check.hs` and collide with that work. **Hold until the
  parallel Check work settles, or coordinate.**
- **Core types** (`Span`/`Pos`/`GName`, `Ctx`, the `Eval`/`Check` records) are
  LAST: migrating `Source` (Span/Pos) ripples to nearly every module via
  `NoFieldSelectors` — the biggest single step, and maximally exposed to the
  parallel Check work.

`Build.Types.Target` partial-field smell: RESOLVED by the Phase-1 restructure
(was: partial selectors `tBackend t`/`tMain t` guarded by `-Wno-partial-fields`).
