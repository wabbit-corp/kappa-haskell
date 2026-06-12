# Implementation notes

Haskell (GHC 9.4.7, boot packages only) implementation of a Kappa
subset. This document maps the architecture, records the key design
decisions and why they were taken, and catalogues approximations and
their deltas from `docs/Spec.md`.

## Architecture map

```
app/Main.hs              CLI: kappa (check|run|test) PATH
src/Kappa/
  Source.hs              positions, spans, module names
  Diagnostic.hs          structured diagnostics (§3.1): severity, stage,
                         code, family, notes/helps; shared text renderer
  Token.hs, Lexer.hs     hand-rolled lexer + Python-style layout (§5–§6);
                         all literal families, interpolation fragments
  Syntax.hs              surface AST (unified term/type expression grammar)
  Parser.Monad.hs        token-stream parser monad, error recovery
  Parser.hs              recursive-descent parser; operators kept as flat
                         chains (EOpChain/POpChain)
  Resolve.hs             fixity collection + operator re-association
                         (§5.5.2), import scope checks (§8)
  Core.hs                KCore subset (§30.2): de Bruijn terms, values,
                         closures; structured CDo/KItem for do-blocks
  Eval.hs                NbE: eval/quote/convertible (§31.1);
                         pure primitive reduction
  Check.hs               bidirectional elaborator (§16/§17/§14/§6.1.5/§18):
                         unification, implicit resolution, traits,
                         exhaustiveness, declaration checking, termination
  Prelude.hs             builtin types/primitives + embedded std.prelude
                         source (§28.2 subset)
  Pipeline.hs            prelude bootstrap, module loading in import order
                         (§8.2), parse → resolve → elaborate
  Interp.hs              strict CBV interpreter (§32.1) executing the
                         §18.8 completion kernel; stdout sink for capture
  Pretty.hs              term/value rendering (also variant tags, §31.3)
  TestHarness.hs         Appendix T harness (directives, suites, capture)
```

Sizes: ~10.7k lines total; the elaborator (`Check.hs`, ~3.1k lines) and
parser (~2.6k) dominate.

## Key decisions

**Unified term/type grammar.** Types are `Expr`s. Kappa is dependently
typed enough (propositional `(=)`, universes, records in type position)
that a separate type grammar would duplicate the expression parser. Type
positions run the same elaborator with a "prefer the type facet" name
rule (§7.2). The rule is recursive: in `check`, a name or application
checked against a universe re-enters the type-facet path, so heads of
nested parenthesized type arguments (`Wrap (Wrap Integer)`,
`List (Wrap Integer)`) also resolve in the type facet.

**Soft keywords via a two-tier stop set.** Application is
juxtaposition, so the parser ends an argument run at "stop keywords".
These are two tiers (§5.2, KNOWN_SPEC_ISSUES.md #11): a structural set
(`then`/`else`/`with`/`in`/statement starters/…) that always
terminates, and a query-clause set (`group by order skip take distinct
join yield into`) that terminates only while a comprehension body is
open (`withExtraStops` in the parser state; `by` is also activated
inside a `decreases` measure). Bracketed sub-expressions clear the
active clause context, so `(take + 2)` inside a comprehension is the
variable again. `deep` is keyword-read only when immediately followed
by `handle`; `when` and `handle` are never argument terminators
(handler expressions are recognized at expression heads, with
backtracking). Net effect: query/handler keywords are ordinary
identifiers in binder, assignment, and argument positions
(`tests/conformance/lexer/soft-keyword-identifiers.kp`); the
structural tier remains reserved in argument position (delta table
below, SPEC_COVERAGE.md §5.2).

**Flat operator chains, re-associated after parsing.** Fixity is
block-scoped and declarable mid-module (§5.5.2), so the parser cannot
know precedences. It emits flat `EOpChain`/`POpChain` nodes; `Resolve`
re-associates them once the module's (plus prelude's) fixity table is
known. This also guarantees no syntax-shaped decisions after resolution
(§1.2A): elaboration only ever sees fully associated applications.

**Traits are dictionary records; members are projection globals.** A
`trait Show a = show : …` declaration elaborates to: a record-like
dictionary type, one global per member that takes the dictionary as an
implicit argument and projects the field, and instance globals
(`__inst_*`) holding dictionary values. Premise instances
(`instance Eq a => Eq (List a)`) are functions from premise dictionaries
to dictionaries. Default members are stored on the trait and
materialized into instance dictionaries that omit them. Coherence is the
§14.3.1 unique-candidate rule: more than one matching instance is
`E_INSTANCE_INCOHERENT` at the use site.

**Postponed implicit goals.** Implicit arguments are inserted along the
application spine (§16.1.7.1) as metavariables, and trait/equality goals
are queued rather than solved at insertion point. They are flushed after
the enclosing body is elaborated, when spine unification has had the
chance to fix the type arguments (e.g. the element type in
`show (1 :: Nil)`). The §16.3.3 ladder then runs: local implicit
context → global instance search → boolean-proposition normalization,
where `(lhs = rhs)` goals decided by conversion yield `refl` (this is
what makes `1 + 1 = 2` and `5 - 3`'s `subDefined` proof work, and what
makes symbolic `x - y` fail honestly with `E_IMPLICIT_UNSOLVED`).
`zonk`-style replacement then eliminates solved metas from stored
globals so instance dictionaries contain no live metas.

**NbE with reducibility gating.** Conversion is normalization by
evaluation (β, δ, ι, η, suspension reduction, canonical record/variant
equality). Per §15.1, only *conversion-reducible* definitions δ-unfold;
a definition that fails structural termination verification is still
runnable but opaque to conversion, which keeps the type checker total
without trusting unverified recursion. Quantities are part of Pi-type
identity (§31.1). Conversion carries fuel; running out only ever
produces "not convertible" — the checker may reject more than the spec,
never accept more.

**Structured `CDo`, interpreted completion kernel.** Instead of
lowering do-blocks to the spec's `Completion`-returning combinator
chain (§18.8.4–18.8.14), core keeps a structured `CDo` with typed
`KItem`s (bind, let, var, while, for, defer, try, if-statement, …). The
interpreter executes exactly the kernel semantics: completion records
(`Normal`/`Break`/`Continue`/`Return`), LIFO exit actions run exactly
once, loop `else` only on no-`Break` exit, typed IO failure
propagation through `catch`/`finally`. The observable behaviour matches
§18.8 (verified by `tests/conformance/run/*`); the delta is internal
representation only, but it does mean `Completion` is not a first-class
core value.

**`var` cells.** `var x = e` allocates a `Ref`; a *read* of `x`
elaborates to a splice `__runIO (readRef x)` typed at the element type
(§18.6.1), and assignments become `writeRef`. There is no §31.5 elision:
cells are real refs at runtime.

**Variant tags are canonical rendered member types.** A variant value
carries the canonical rendering (after alias normalization) of its
member type (§31.3), so `Int` and `Integer` members coincide and
widening is a no-op. Records canonicalize to lexicographic field order
(§31.4) while a `CLet` chain preserves source-order evaluation of
initializers.

**Prelude = builtins + embedded source.** `Kappa.Prelude` registers
opaque builtin types and `VPrim` primitives (arithmetic, strings, IO,
refs), then an embedded `std.prelude` source file — data types, traits,
operators, instances, list functions — is compiled by the ordinary
pipeline at startup. The prelude is therefore checked by the same
elaborator it bootstraps, and prelude names resolve like any module's
(§28.1). The cost is recompilation per CLI invocation (see
PERFORMANCE.md).

**Recursion needs a preceding signature.** Per §9.2/§15.16, bodies are
checked in a second pass against header types; direct recursion without
a signature is `E_RECURSION_NO_SIGNATURE`. Structural descent (some
explicit parameter strictly decreases at every direct self-call, via
constructor sub-patterns) certifies termination; otherwise the
definition gets `W_TERMINATION_UNVERIFIED` and is conversion-opaque.

**Error tolerance boundaries.** The parser recovers at declaration
boundaries (§3.1.14A) and the checker continues past errors using holes
(`anyHole`) so one bad declaration doesn't silence the rest. The lexer
deliberately stops at the first lexical error (documented delta —
lexical states make recovery guesses worse than a clean stop).

## Approximations and spec deltas

| Area | Approximation | Spec delta |
| --- | --- | --- |
| Quantities (§12) | Parsed, stored on Pi binders, part of type identity | Usage counting not enforced; `0`-marked binders are not checked erased in bodies; symbolic quantities collapse to `ω` |
| Borrows/regions/captures (§12) | Parsed only | No borrow/region/capture checking; §3.2.7/§3.3 diagnostics never fire |
| Effects (§18.1) | `scoped effect` + `Eff` rows + `handle`/`deep handle`/`runPure` elaborated and run (a pure `__EffPure`/`__EffOp` tree reduced by `Kappa.Eval.evalEffPrim`; continuations are ordinary closures, so multi-shot is naturally re-entrant) | Closed rows only (no row variables, weakening, or `SplitEff` polymorphism; multi-entry rows keep source order); operations take exactly one explicit parameter; handler target carrier is fixed to `Eff residual`; scoped effects hoist to the head of their block and their operation signatures must be closed over block locals; the §18.1.20 capture check is lexical (the remaining do-items of the operation's own block); top-level `effect`, `effect label`, effect parameters, completion-carrying handlers and fibers remain unsupported |
| do-blocks (§18.8) | Structured `CDo` executed by the interpreter | `Completion` is not a core-level value; behaviour matches the kernel tests |
| Universes (§11.1) | `Type0..n` + cumulativity | No universe polymorphism; composite types pinned at `Type 0` |
| Implicit universalization (§11.3.3) | Free ASCII-lowercase heads in top-level signatures, instance heads, and instance premises generalize | Heuristic, not the spec's exact binding-group rule; block-local signatures do not generalize |
| Supertraits (§14.1.4, §14.3.3) | Premises enforced at instance declarations (`E_SUPERTRAIT_UNSATISFIED`), satisfiable through depth-bounded transitive conformance paths from the instance's own premises | Use-site implicit resolution does not walk conformance paths (evidence of a subtrait does not discharge a supertrait goal at call sites) |
| Constructor field defaults (§10.1.1) | Stored on the constructor, elaborated at each application site against the field type | Defaults may not refer to the constructor's other fields |
| Parse recovery (§3.1.14A) | Declaration-boundary recovery only | A parse error inside a `do` block abandons the block; later block lines cascade as bogus declaration-level errors far from the cause |
| Soft keywords (§5.2) | Query/handler keywords identifier-usable everywhere outside their clause contexts; structural keywords context-insensitive argument terminators | A bare reference named `then`/`else`/`is`/`as`/`on`/`using`/`where`/… in argument position misparses (full residual list in SPEC_COVERAGE.md §5.2) |
| GADTs (§17.1.1–17.1.2) | Constructor result unified with scrutinee type | No general index refinement or `impossible` reasoning |
| Exhaustiveness (§17.1) | Closed ADTs/Bool/variants/records/tuples; literals need catch-all | No guard-aware or flow-aware coverage proofs |
| Flow typing (§16.4) | None | `&&`/`||`/`not` refinement, transport, lower-bound flow checks absent |
| Conversion (§31.1) | Fuel-bounded NbE | May reject convertible terms (sound direction only) |
| Erasure (§31.2) | Erased implicit ctor params dropped | No full erasure pass |
| Diagnostics (§3) | Structured records, text rendering | No JSON output, registry, payloads, fix-its, explanations |
| Modules (§8) | Import-ordered multi-file suites | No visibility/opacity/export enforcement, URL imports |
| Lexer recovery (§3.1.14A) | Stops at first lexical error | Multi-error lexical fixtures under-count |
| Prelude (§28) | §28.2 subset, not closable | Missing names listed in SPEC_COVERAGE.md §28.2 row |
| Labeled control (§18.2.5, §18.5.1, §18.7) | `break@L`/`continue@L` implemented with compile-time label resolution (`E_LABEL_UNRESOLVED` when no enclosing labeled loop of the do-scope matches); unlabeled `break`/`continue` outside a loop body of the do-scope → `E_BREAK_OUTSIDE_LOOP` (§18.6); `return@L`/`defer@L` → `E_UNSUPPORTED`; labels on `do`/lambda/`match` parse and are inert | Inert labels are sound here because every construct that could consume them is rejected at its use site (see "Review responses" #2). Loop targets never cross a first-class do-value boundary — each do-expression is a fresh scope, so break/continue inside `let inner = do …` are rejected even when `inner` is spliced inside a loop (loud-conservative; matches the "Completion is not first-class" delta above) |
| Unicode data (§29.4, §6.5) | UCD 15.0.0 embedded as `Kappa.UnicodeData`, generated once by `tools/gen-unicode-data.py` and committed (normalization tables, grapheme-cluster-break classes); `Kappa.Unicode` implements UAX #15 normalization and UAX #29 extended grapheme clusters over them | `Extended_Pictographic` and the Indic `Prepend` component are vendored snapshots of the 15.0 data files (the script documents the derivation); `words`/`sentences` are simple whitespace/terminator approximations, not UAX #29 segmentation; `displayWidth` is a documented one-cell-per-grapheme policy |
| Quoted-literal handlers (§6.5) | The conventional `g`/`b` handlers are built into the elaborator (`EQuotedLit` in `Check.hs`) and validate the §6.5 text/byte views directly | No user-extensible `QuotedLiteralMacro` machinery (depends on the §21–§23 macro stack); other prefixes stay `E_UNSUPPORTED` |
| Implicit deferral (§16.3.3) | A postponed trait goal whose head is still an unsolved meta after its declaration, in a context with no local implicit candidates, stays pending and is committed at module end (so `let f x y = x + y` used later at `Int` elaborates) | Not let-generalization: the first determining use fixes one monotype for every use of the definition; goals in contexts with local candidates commit at the declaration (a late local-candidate solution would leak local rigids into the zonked stored term) |
| Metaprogramming (§21, §22, §6.3.4, §20.9) | Quotes keep SURFACE syntax (`CQuote`/`VQuote` carry the payload `Expr` with numbered grafting holes); `$( … )` evaluates its `Elab (Syntax t)` argument with the runtime-mode NbE evaluator and interprets the resulting stuck `__elab*` primitive applications in `Kappa.Check.runElab`; the produced syntax is grafted (`Kappa.SyntaxOps.substQuoteHoles`) and re-elaborated at the splice site, with the grafted expansion recorded in `csExpansions` so `Kappa.Usage` charges object-level uses at the splice | Hygiene is capture-list-based, not alpha-renaming of quoted binders: payload occurrences of quote-site locals are renamed to fresh spellings and resolved by binding LEVEL at the splice site (shadow-immune); names rebound anywhere inside a payload are left un-captured and re-resolve at the splice site (loud-conservative for the §21.4 corner where a quote both rebinds and references one spelling). Macro execution shares the evaluator's fuel rather than a §21.8 step limit; `$( … )` is layout-transparent in the lexer so `do` suites work inside splices, and suite parsers accept a closing bracket in place of a dedent |
| Source hygiene (§3.1.3) | `W_UNICODE_BIDI_CONTROL` / `W_UNICODE_CONFUSABLE_IDENTIFIER` / `W_UNICODE_NON_NORMALIZED_SOURCE_TEXT` always on, at most one per class per file, scanned at load time (`loadSourceFile`); invalid UTF-8 bytes are `E_UNICODE_INVALID_UTF8` with U+FFFD recovery | Confusable detection uses a small documented Cyrillic/Greek homoglyph table (so `λ` never warns), not UTS #39 skeletons; bidi scanning excludes double-quoted string contents by a line-local scan |

Everything rejected rather than approximated is surfaced as
`E_UNSUPPORTED` with a note pointing at SPEC_COVERAGE.md (see
`unsupported`/`reportUnsupported` in `Check.hs` and the per-declaration
rejections).

## Review responses

Responses to the adversarial code-quality review (each finding either
fixed or justified here).

1. **Labeled `break`/`continue` targeting (BLOCKER)** — fixed.
   `Kappa.Interp.targets` was keyed on the loop's label instead of the
   break's: an unlabeled `break` now targets the nearest loop (labeled
   or not), and `break@L`/`continue@L` pass through every loop until
   the one labeled `L` (`src/Kappa/Interp.hs`). Conformance fixtures
   added under `tests/conformance/labels/` cover both reported
   misbehaviours plus `continue@outer`.
2. **Silently discarded labels** — fixed by rejection or shown inert.
   `return@L` and `defer@L` now emit `E_UNSUPPORTED` at the label
   (`elabDo`); `break@L`/`continue@L` are resolved at compile time
   against the enclosing loop labels of the do-scope
   (`E_LABEL_UNRESOLVED` otherwise, per §18.2.5 "compile-time error").
   Labels on `do`, lambdas, and `match` remain accepted and inert:
   the only constructs that could consume them (`defer@`, `return@`,
   `break@`/`continue@`) all diagnose at their own use sites, so an
   unconsumed label cannot change program meaning. The parser comment
   at `pMatchExpr` records this. `markImplicitLocal` is no longer a
   no-op: `let (@x : T) = e` in a do-block joins the local implicit
   context (`tests/conformance/do/implicit-do-binding.kp`).
3. **Quadratic lexer lookahead** — fixed. `peekAt` is now
   `T.uncons . T.drop n` (n ≤ 2) instead of `T.length`/`T.index` over
   the remaining input. Float-/char-literal-heavy files now scale like
   int-heavy ones (PERFORMANCE.md §2a; `tools/gen-stress.sh` grew
   `float`/`char` modes to keep this measurable).
4. **`sortDiagnostics`** — deleted (it was dead, and its `show`-based
   key was wrong anyway). Diagnostics are emitted in source order by
   construction (single pass per file; `checkModule` restores order).
5. **Dead exported API** — trimmed. Removed `withLabel`/`withRelated`/
   `RelatedRole`/`relatedRoleText`/`Related`/`DiagLabel` and the
   `dLabels`/`dRelated`/`dPayload` fields (no producer or renderer
   existed; the doc header records the deliberate subset), and
   `SourceFile`/`mkSourceFile`/`lineAt`/`spanUnion`/`posBefore`,
   `Eval.normalize`, `Parser.parseTypeText`.
6. **Warning-suppression hacks** — removed: the always-true guards, the
   `keepSkip`/`peekFirstMeaningful`/`srcPadded` aliases, the pointless
   `seq`, every `_ <- pure x` discard, `_unusedBsp`/`_unusedSp`,
   the dead `elabIs` stub (rewritten to use the real constructor
   arity), and `pExprNoDecreases` (whose comment was wrong; `decreases`
   is a global stop keyword, so plain `pExpr` already stops there).
7. **Partial functions** — the lexer indent stack is a `NonEmpty Int`;
   `env !! i` is a checked `lookupEnv` with a contextual message (used
   by `Eval` and `Prelude`); the or-pattern binder check no longer uses
   `head`; `exprSpan`'s empty-chain `error` documents the parser
   invariant; `sortName` bounds-checks the universe suffix before
   `read`, so `Type99999999999999999999` is an unresolved name instead
   of a negative level.
8. **O(n²) diagnostic accumulation** — `report` prepends and
   `checkModule` reverses once; `compileFiles` accumulates per-file
   chunks and concatenates once.
9. **`{}` map literal** — now `E_UNSUPPORTED` like the non-empty case
   (`tests/conformance/unsupported/map-literal.kp`). Defining a real
   `Map` just for the empty literal would be a stub value with no
   operations, which is the same trap one step later.
10. **Duplicated diagnostic renderers** — extracted to
    `Kappa.Diagnostic.renderDiagnostic`, used by both the CLI and the
    harness (the harness now renders notes/helps too; its assertions
    are containment-based, so fixtures are unaffected).
11. **Splitting `Check.hs`** — justified, not done. Three of the four
    proposed submodules are mutually recursive with the bidirectional
    core: pattern elaboration calls `inferType`/`check` (typed and
    variant patterns), do-elaboration calls `check` and is called from
    `infer`, and instance elaboration checks member bodies via
    `check`. Splitting them needs `hs-boot` files or a record of
    callbacks, both of which obscure more than a sectioned single
    module (the section headers the review credits). The termination
    analysis alone is extractable but is ~100 lines with a single
    caller; not worth a module boundary.
12. **Test hygiene** — fixed. Labeled-loop/labeled-control fixtures
    (`tests/conformance/labels/`), `label@match`, `defer@`, `return@`,
    and `{}` fixtures added (suite grew to 80 fixtures in that round,
    83 with the round-3 additions below); the test-suite
    stanza carries the same `-with-rtsopts=-K64m` as the executable.
13. **Unlabeled `break`/`continue` outside a loop** — fixed. `elabDo`
    now tracks one entry per enclosing loop (labeled or not): an
    unlabeled `break`/`continue` with no enclosing loop in its
    do-scope is rejected at compile time with `E_BREAK_OUTSIDE_LOOP`
    (§18.6 "Using them outside a loop body is a compile-time error";
    `tests/conformance/do/continue-outside-loop.kp`,
    `do/break-in-loop-else.kp` — the `else` suite runs after the loop,
    so the loop itself is not a target there). The now-unreachable
    runtime catch-all in `runIOValue` that silently converted an
    escaping `CplBreak`/`CplContinue` to unit was replaced with a loud
    internal error.
14. **Completion confinement at first-class do-value boundaries** —
    fixed (loudness) / documented (semantics). The silent half is gone:
    finding 13's check makes `break` inside `let inner = do break`
    a compile-time `E_BREAK_OUTSIDE_LOOP` even when `inner` is spliced
    inside a loop (`tests/conformance/do/break-in-first-class-do.kp`),
    matching the already-loud labeled case. The semantic delta itself —
    §18.8.10 lets break exit nested do-scopes, this implementation
    confines targets to the do-scope the break is written in — is
    retained deliberately (it is the "Completion is not a first-class
    core value" representation choice above) and is now stated
    explicitly in SPEC_COVERAGE.md's §18.2–18.8 row and the deltas
    table here, instead of only in prose.
15. **`if c then do break` inside a loop (info)** — justified, not
    changed. `then do …` introduces a nested first-class do-expression,
    which is a fresh do-scope, so the `break` is rejected at compile
    time with `E_BREAK_OUTSIDE_LOOP` (§18.6) rather than targeting the
    enclosing loop; the idiomatic statement-`if` (`if c then` + layout,
    as in `tests/conformance/run/for-break-continue.kp`) targets the
    loop as expected. This is the per-do-scope confinement delta of
    #14 surfacing through a syntax variant, not a separate behavior:
    making this one spelling transparent while `let inner = do break`
    stays confined would need an ad-hoc "syntactically immediate do"
    carve-out in `elabDo`, splitting one rule into two. The rejection
    is loud, names the rule and section, and the documented delta
    (SPEC_COVERAGE.md §18.2–18.8 row; "Completion is not a first-class
    core value" above) covers it — per the reviewer, no action
    required.
