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
                         code, family, labels, notes/helps, related
                         origins with standardized roles (§3.1.1A)
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
  Eval.hs                NbE: eval/quote/convertible/normalize (§31.1);
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
| Effects (§18.1) | `effect` declarations parse | No rows, handlers, fibers; the only do-carrier is `IO e` |
| do-blocks (§18.8) | Structured `CDo` executed by the interpreter | `Completion` is not a core-level value; behaviour matches the kernel tests |
| Universes (§11.1) | `Type0..n` + cumulativity | No universe polymorphism; composite types pinned at `Type 0` |
| Implicit universalization (§11.3.3) | Free ASCII-lowercase heads in top-level signatures, instance heads, and instance premises generalize | Heuristic, not the spec's exact binding-group rule; block-local signatures do not generalize |
| Supertraits (§14.1.4, §14.3.3) | Premises enforced at instance declarations (`E_SUPERTRAIT_UNSATISFIED`), satisfiable through depth-bounded transitive conformance paths from the instance's own premises | Use-site implicit resolution does not walk conformance paths (evidence of a subtrait does not discharge a supertrait goal at call sites) |
| Constructor field defaults (§10.1.1) | Stored on the constructor, elaborated at each application site against the field type | Defaults may not refer to the constructor's other fields |
| Parse recovery (§3.1.14A) | Declaration-boundary recovery only | A parse error inside a `do` block abandons the block; later block lines cascade as bogus declaration-level errors far from the cause |
| GADTs (§17.1.1–17.1.2) | Constructor result unified with scrutinee type | No general index refinement or `impossible` reasoning |
| Exhaustiveness (§17.1) | Closed ADTs/Bool/variants/records/tuples; literals need catch-all | No guard-aware or flow-aware coverage proofs |
| Flow typing (§16.4) | None | `&&`/`||`/`not` refinement, transport, lower-bound flow checks absent |
| Conversion (§31.1) | Fuel-bounded NbE | May reject convertible terms (sound direction only) |
| Erasure (§31.2) | Erased implicit ctor params dropped | No full erasure pass |
| Diagnostics (§3) | Structured records, text rendering | No JSON output, registry, payloads, fix-its, explanations |
| Modules (§8) | Import-ordered multi-file suites | No visibility/opacity/export enforcement, URL imports |
| Lexer recovery (§3.1.14A) | Stops at first lexical error | Multi-error lexical fixtures under-count |
| Prelude (§28) | §28.2 subset, not closable | Missing names listed in SPEC_COVERAGE.md §28.2 row |

Everything rejected rather than approximated is surfaced as
`E_UNSUPPORTED` with a note pointing at SPEC_COVERAGE.md (see
`unsupported` in `Check.hs` and the per-declaration rejections).
