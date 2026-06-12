# Spec coverage matrix

Coverage of `docs/Spec.md` (Kappa Language Specification) by this
implementation, at section granularity, for all Parts I–X plus
Appendix T. Statuses:

* **Implemented** — behaviour conforms within the noted limits and is
  exercised by tests.
* **Partial** — a meaningful, documented subset conforms; the rest is
  missing or approximated (notes say which).
* **Parsed-only** — the surface syntax is accepted by the lexer/parser
  (and usually carried in the AST), but elaboration rejects it with
  `E_UNSUPPORTED` or ignores it.
* **Not implemented** — no meaningful support.

Test references are paths under `tests/conformance/` (the in-tree
suite, 68/68 passing) or `examples/`. The external black-box corpus
tally is in `tests/external-results.md` and TESTING.md.

## Part I. Language Contract and Conformance

| Section | Status | Notes / tests |
| --- | --- | --- |
| §1 Design principles | Partial | Diagnostics are typed records rendered to text (§1, §3.1.8) — `src/Kappa/Diagnostic.hs`. No typed compiler artifacts/query layer (§1.2): the pipeline is a batch compiler. §1.2A (no syntax-shaped decisions post-resolution) is followed in spirit: fixity is resolved before elaboration, names by semantic identity. |
| §2 Profiles, gates, versions, conformance | Not implemented | One fixed profile; no feature-gate machinery. `unicode-names` (§2.1A) is permanently inactive; the lexer emits the gate-aware error for Unicode numeric suffixes (§6.1.6). Backend-lacking-capability rejection (§2.1) is approximated only by the test harness classifying such fixtures unsupported. |
| §3.1 Diagnostic records, codes, families | Partial | Structured records with severity, stage, code, `kappa.*` family, primary span, labels, notes, helps, and related origins with the standardized §3.1.1A roles (`Kappa.Diagnostic`). Stable symbolic codes (§3.1.2). Missing: machine-readable registry CLI (§3.1.2A), JSON payloads (§3.1.9), fix-its (§3.1.6 — notes/help only), repair ranking (§3.1.7), provenance frames (§3.1.5A), explanations (§3.1.13). |
| §3.1.14/§3.1.14A Recovery | Partial | Parse-level recovery to declaration boundaries: `parser/recovery.kp` (two errors reported, checking continues). Recovery granularity is declaration-level only: a parse error *inside* a `do` block abandons the whole block, so the remaining block lines re-parse as (failing) top-level declarations and the introducer can produce a spurious `E_UNRESOLVED_NAME: 'do'` — a cascade of mislocated follow-on errors after the genuine one. The lexer stops at the first lexical error by design (documented delta; multi-error lexical fixtures in the external corpus under-count). |
| §3.2 Standard diagnostic families | Partial | The families used by implemented features carry spec spellings (e.g. `kappa.name.unresolved`, `kappa.type.mismatch`); families for unimplemented subsystems (borrows, macros, bridges, Python backend, …) are absent. |
| §3.3 Path-/borrow-sensitive failure diagnostics | Not implemented | Requires borrow/quantity checking. |
| §4 Unsafe and debug facilities | Not implemented | No `unsafe`/`debug` gating, `unhide`/`clarify`, termination escapes, or audit ledger. |

## Part II. Surface Syntax and Names

| Section | Status | Notes / tests |
| --- | --- | --- |
| §5.1 Identifiers | Implemented | ASCII identifiers. §5.1A Unicode name profile: not implemented (gate inactive). |
| §5.2 Keywords | Implemented | All keywords are soft: lexed as identifiers, contextually recognized by the parser (`Kappa.Lexer` design note). |
| §5.3 Comments | Implemented | Line comments; comment-only lines never affect layout. |
| §5.4 Whitespace, indentation, continuation | Implemented | Python-style INDENT/DEDENT at bracket depth zero; logical-line indentation is the first token's column. Tabs rejected: `lexer/tab-in-indent.kp`, `lexer/tab-in-source.kp`. Bad dedent: `parser/bad-dedent.kp` (`E_LAYOUT_BAD_DEDENT`). |
| §5.5.1 Operator tokens, longest match | Implemented | Longest-match-first incl. `let?`/`for?`, `?.`, `?:`, `?name` holes, `~=`, `<[`, `]>` (see KNOWN_SPEC_ISSUES.md for a consequence). |
| §5.5.1.1 Operator sections | Implemented | Left/right/bare sections; `(infix op)`/`(prefix op)` forms parse. `(op e)` is unary prefix application when a `prefix` fixity for `op` is in scope (so `(-1)`/`(- a)` are negation per §28.2.3's `(-) : prefix 80`, with chain precedence preserved: `(- 1 + 2)` is `negate 1 + 2`); `(prefix -)` denotes `negate` (§5.5.1, §6.1.4): `fixity/paren-negation.kp`. Sections usable in check mode. |
| §5.5.2 Fixity declarations | Implemented | Block-scoped; parser emits flat chains, the resolver re-associates once fixities are known. `fixity/user-fixity.kp`; missing fixity → `E_OPERATOR_NO_FIXITY` (`fixity/no-fixity.kp`). |
| §5.5.3 Infix gating | Partial | The §28.2.3 default fixity table is provided (`Kappa.Resolve.defaultFixities`); per-name infix-permission gating beyond fixity presence is not modeled. |
| §6.1 Numeric literals | Implemented | Radix forms (`literals/radix.kp`), fraction/exponent vs suffix split (`literals/float-exponent.kp`, `literals/suffix-term.kp`), §6.1.5 typing/defaulting: integer literals through `FromInteger` (`literals/defaulting.kp`), float literals through `fromFloat : Double -> t` when the expected type has a `FromFloat` instance, defaulting to `Double` (`literals/fromfloat.kp`). §6.1.6 Unicode suffixes: gate-off error. §6.1.3: `eqDouble` is raw-bit equality; `floatEq` is IEEE equality. |
| §6.2 Boolean literals | Implemented | Prelude `Bool`/`True`/`False`. |
| §6.3.1–6.3.3 Basic/raw/multiline strings | Implemented | Escapes (`lexer/bad-escape.kp`, `lexer/unterminated-string.kp`), `#"…"#` raw forms, multiline fixed dedent. |
| §6.3.4 Prefixed strings + interpolation | Partial | The `f` handler with `${expr}`/`$name` interpolation works end to end (`run/string-interp.kp`, `examples/todo.kp`). Other handlers (`re`, `b`, `type`) lex/parse but elaborate to `E_UNSUPPORTED`. |
| §6.3.5 Conventional type-prefix handler | Not implemented | See KNOWN_SPEC_ISSUES.md (lookahead interaction). |
| §6.4 Unicode scalar literals | Implemented | `LitScalar`; `eqScalar`/`showScalar` primitives; `Char = UnicodeScalar` alias (§28.5). |
| §6.5 Prefixed quoted literals | Parsed-only | Plain scalar literals work; `g`/`b` handler forms → `E_UNSUPPORTED`. |
| §6.6 Unit and tuples | Implemented | `Unit`; tuples as positional records, tuple patterns (`match/tuple-record-patterns.kp`), punned tuples. |
| §7.1 Ordinary lexical lookup | Implemented | Scope-stack lookup during elaboration; `names/unresolved.kp`, `names/duplicate.kp`. §7.1.1 kind-qualified name expressions: not implemented. |
| §7.2 Same-spelling families, type facet | Partial | Type positions prefer the type facet of a head name (`Check.hs` "type-facet lookup"); the full data-family/static-member story is absent. |
| §7.3 Dotted name resolution | Partial | Projection, method-style member access, safe navigation; module-qualified dotted paths only within the loaded-suite module graph. |
| §8 Modules, imports, exports, visibility, opacity | Partial | Multi-file directory suites compile in import order with cycle detection (§8.2; `Kappa.Pipeline`). Import statements select scope; export lists, visibility/opacity enforcement, URL imports, and import hashes are not implemented. |

## Part III. Declarations and Static Language

| Section | Status | Notes / tests |
| --- | --- | --- |
| §9 Declarations and definitions | Partial | Signature + `let` pairs, `data`, `type` aliases, `trait`, `instance`, `fixity`, `import`; two passes (headers then bodies) per the preceding-signature recursion rule (§9.2, §15.16). `derive`, `pattern` (active patterns), projection declarations, top-level splices: Parsed-only → `E_UNSUPPORTED` (`tests/conformance/shape/decl-kinds.kp` counts declaration kinds). |
| §10 ADTs and type aliases | Implemented | Parameterized `data` with named constructor fields, constructor-arity checking (`application/ctor-arity.kp`), named constructor application with field defaults (§10.1.1: a missing label is permitted iff the parameter has a default, which is elaborated at the application site — `records/ctor-field-defaults.kp`, `records/ctor-field-default-missing.kp`; defaults referring to earlier fields of the same constructor are not supported), transparent aliases (`Int`, `UIO`, …). GADT-style indexed results: "GADT-lite" — the constructor result is unified with the scrutinee type at match (§17.1.2 approximation). |
| §11.1 Universes | Partial | `Type`, `Type0..n`, `*` spellings; cumulativity `Type m ≤ Type n` for `m ≤ n` (§11.1.1). No universe polymorphism; records/Pi types currently land in `Type 0`. |
| §11.2 Classifiers | Not implemented | No `Row`/`Label`/intrinsic classifier names. |
| §11.3 Implicit binders, universalization | Partial | §11.3.3 approximated: free ASCII-lowercase heads in top-level signatures, instance heads, and instance premises that resolve to no global are implicitly universalized as erased implicit `Type` binders (`application/lambda-hof.kp` uses `apply2 : (b -> a -> b) -> b -> a -> b`). Block-local signatures are not universalized. |
| §11.4 Propositions | Partial | §11.4.1 propositional `(=)` with `refl` (`equality/refl-conversion.kp`); `(lhs = rhs)` implicit goals decided by conversion (`1 + 1 = 2` by refl; `5 - 3` via `subDefined` proof: `equality/sub-proof.kp`; symbolic `x - y` fails `E_IMPLICIT_UNSOLVED`: `equality/sub-unknown.kp`). §11.4.2 boolean-to-type coercion: not implemented. |
| §12 Functions, binders, quantities | Partial | All five portable interval quantities (`0`, `1`, `ω`, `≤1`, `≥1`) parse and are carried on core Pi binders, where they participate in type identity (§31.1). **Usage counting is not enforced** — quantity-violation diagnostics (§3.2.5) never fire. Symbolic quantities approximate to `ω`. |
| §12 Borrowing, regions, captures | Parsed-only | `&`, `&[region]`, capture clauses parse into the AST; no borrow checking, region inference, or capture checking. `inout`/`~` call-site arguments → `E_UNSUPPORTED`. |
| §13.1–13.2 Records | Implemented | Closed records: literals, punning (`records/punning.kp`), projection (`records/basics.kp`, missing field → `E_RECORD_PROJECTION_MISSING_FIELD`), functional patch `.{ }` (§13.2.5; unknown field → `E_UNKNOWN_FIELD`, `records/patch-unknown-field.kp`), rest patterns. Canonical lexicographic field order with source-order initializer evaluation (§31.4). Not: open rows / `:=` row extension, dependent records, nested patch paths, projection-section updates. |
| §13.1.3, §13.3 Variants / closed unions | Implemented | `(\| A \| B \|)` types, expected-type-directed injection incl. literals (`variants/injection.kp`), widening as a no-op, closed-union match (`variants/closed-union.kp`, missing member → error: `variants/missing-member.kp`), `Int?` Option sugar (`variants/option-sugar.kp`). Member identity = canonical rendered member type after alias normalization (§31.3). Not: open variant rows. |
| §13.4–13.5 Sealed packages, existentials | Parsed-only | `seal`/`exists`/`open` → `E_UNSUPPORTED` (`unsupported/seal.kp`, `unsupported/exists.kp`). |
| §14 Traits | Partial | User traits, instances, premise instances (`instance Eq a => Eq (List a)`: `traits/premise-instance.kp`), default members (`traits/default-member.kp`). Resolution: local implicit context, then global instance search with a unique-candidate coherence rule (§14.3.1) — ambiguity → `E_INSTANCE_INCOHERENT` (`traits/incoherent.kp`), no candidate → `E_IMPLICIT_UNSOLVED` (`traits/missing-instance.kp`). Supertrait premises (§14.1.4) are enforced at instance declarations: missing evidence → `E_SUPERTRAIT_UNSATISFIED` (`traits/supertrait-unsatisfied.kp`); satisfiable from global instances or the instance's own premises, including depth-bounded transitive supertrait conformance paths (`traits/supertrait-satisfied.kp`). Not: supertrait conformance paths during *use-site* implicit resolution (evidence of `MyOrd a` does not yield `MyEq a` at member call sites), associated static members (§14.3.4), named instances, instance search-depth control (§14.3.5 beyond a recursion bound). |
| §15 Totality, termination, unfolding | Partial | §15.1 split between total-certified and conversion-reducible is modeled: only reducible definitions δ-unfold during conversion. Structural-descent verification for direct recursion (§15.3 minimum): `recursion/structural.kp` (clean), `recursion/non-structural.kp` (`W_TERMINATION_UNVERIFIED`), recursion without a preceding signature → `E_RECURSION_NO_SIGNATURE` (`recursion/no-signature.kp`). `decreases` measures parse but are not checked; §15.10–15.17 lanes not implemented. |

## Part IV. Expressions, Control Flow, and Effects

| Section | Status | Notes / tests |
| --- | --- | --- |
| §16.1 Application, spine, implicits | Implemented | Application-spine implicit insertion (§16.1.7.1) with postponed trait goals; named function application and named-argument blocks (§16.1.7); non-callable application → `E_APPLICATION_NON_CALLABLE` (`application/non-callable.kp`). |
| §16.1.1 Dotted forms | Partial | Projection, method sugar, safe navigation `?.` (§16.1.1.2). Projector/accessor descriptors (§16.1.5–16.1.6): not implemented. |
| §16.1.2 Elvis `?:` | Not implemented | Token lexes; no elaboration/prelude support. |
| §16.1.3 Short-circuit booleans | Implemented | `(&&)`/`(||)` over `Thunk Bool` with suspension binder sugar (`(thunk x : T)` ⇒ `Thunk T`, §16.2.4) and `force (thunk e) ↦ e` reduction. |
| §16.1.4 / §16.1.8 Subsumption, equality transport | Partial | Variant widening and alias-transparent conversion at application boundaries; automatic transport insertion limited to conversion-decided `(=)` goals. |
| §16.2 Lambdas | Implemented | Typed/untyped binders (including multi-argument unannotated lambdas against polymorphic HOF parameters: `application/lambda-hof.kp`), implicit binders, suspension sugar. |
| §16.3 Implicits, holes | Partial | §16.3.3 ladder: local implicit context → global instance search → boolean-proposition normalization for `(lhs = rhs)` goals decided by conversion. Named holes lex; no interactive hole reporting. |
| §16.4 Conditionals, flow typing | Partial | `if`/`elif`/`else` expressions (else required in value position: `run/if-expr-needs-else.kp`); statement `if` without `else` in do-blocks (`run/if-no-else.kp`). **Flow-sensitive refinement (§16.4.1–16.4.4) is not implemented** (a large bucket of external-corpus failures). |
| §17 Patterns, matches | Partial | Constructor, literal, tuple, record, variant, or-patterns (`match/or-patterns.kp`), guards (`match/guards.kp`), nesting (`match/nested-ctor.kp`). Exhaustiveness (§17.1) for closed ADTs, `Bool`, variants, records, tuples; literal scrutinees require a catch-all (`match/literal-patterns.kp`, `match/not-exhaustive.kp`, `match/bool-missing-case.kp`). Active patterns (§17.3): Parsed-only → `E_UNSUPPORTED`. `impossible` branches, erased-scrutinee discrimination, guard evidence: not implemented. |
| §18.1 Effects, fibers | Not implemented | No effect rows, handlers (`unsupported/handle.kp`), fibers, or structured concurrency. `effect` declarations parse → `E_UNSUPPORTED`. |
| §18.2–18.8 do-blocks, kernel | Partial | The §18.8 completion kernel is implemented structurally (`CDo` in core, executed by `Kappa.Interp`): completion records, LIFO `defer` (`run/defer-lifo.kp`), `return` (`run/return-early.kp`), `break`/`continue`, loop `else` only on no-break (`run/loop-else-break.kp`, `run/for-break-continue.kp`), `while` (`run/while-var.kp`), `for`, `let pat <- e` monadic bind, `let? … else` (`run/letq-else.kp`), `var` cells as `Ref` with auto-deref reads (§18.6.1), `!e` splices (§18.3). The only carrier is `IO e` — do-blocks are not generic over user monads. `using` resource binds → `E_UNSUPPORTED`. |
| §19 Errors, try/except/finally | Partial | Typed IO errors: `raise`/`throwError`/`catchError`, `try`/`except`/`finally` statements (`run/try-except-finally.kp`, `examples/todo.kp`). `try match` and `bracket`-style resources: not implemented. |
| §20 Collections, ranges, comprehensions | Partial | List literals and list comprehensions (`[for x in xs yield e]`, with `if`/`let` clauses). Empty map literal only; non-empty map/set literals, set/map comprehensions, group/order/join query clauses → `E_UNSUPPORTED`. Ranges `..`/`..<`: fixity exists, no prelude implementation. |

## Part V. Metaprogramming and Staging

| Section | Status | Notes |
| --- | --- | --- |
| §21 Syntax, macros, elab, reflection | Not implemented | Quotation/splice forms parse → `E_UNSUPPORTED`. |
| §22 Derivation-shape reflection | Not implemented | `derive` declarations parse → `E_UNSUPPORTED`. |
| §23 Staged code | Not implemented | |

## Part VI. Dynamic Values, Boundaries, and Interop

| Section | Status | Notes |
| --- | --- | --- |
| §24 Dynamic values | Not implemented | No `Dynamic`, no runtime representations registry. |
| §25 Boundary contracts, bridges | Not implemented | |
| §26 FFI, host bindings | Not implemented | |
| §27 Backend / runtime capability profiles | Not implemented | Tree-walking interpreter only; the harness classifies backend- or capability-requiring fixtures as unsupported (§T.8). See `examples/README.md` for the consequence (no network demo). |

## Part VII. Standard Library Reference

| Section | Status | Notes / tests |
| --- | --- | --- |
| §28.1 Implicit prelude import | Partial | Every file compiles against `std.prelude` (builtins + embedded source, `Kappa.Prelude`), including the fixed unqualified constructor subset (`True`…`refl`). It cannot be disabled (see KNOWN_SPEC_ISSUES.md). |
| §28.2 Normative minimum contents | Partial | Provided: `Void`/`Unit`/`Bool`/`Ordering`/`Option`/`Result`/`List`, aliases `Int`/`Float`/`Char`/`UIO`, `not`/`(&&)`/`(||)` over `Thunk`, the `Show`/`Eq`/`Ord` traits + comparison operators with instances for every §28.2-mandated base type this implementation has — `Eq`: `Unit`, `Bool`, `UnicodeScalar`, `String`, `Integer`, `Nat`, `Double`, `Ordering`; `Ord`: `Bool`, `UnicodeScalar`, `String`, `Integer`, `Nat`, `Double`, `Ordering`; `Show`: `Unit`, `Bool`, `UnicodeScalar`, `String`, `Integer`, `Nat`, `Double`, `Ordering` (aliases `Int`/`Float`/`Char` share them transparently; `traits/base-instances.kp`) — numeric traits per §28.2.1–28.2.3 (`Add`, `Mul`, `Negatable`, `CheckedSub`/`Div`/`Mod` with proof-carrying `(-)`/`(/)`/`(%)`, `FromInteger` for `Nat`/`Integer`/`Double`, `FromFloat` for `Double` incl. literal elaboration), `(++)`, `show`/`print`/`println`/`printString`/`printlnString`, `pure`/`raise`/`throwError`/`catchError`, `identity`, `(\|>)`/`(<\|)`, list functions (`map`, `filter`, `foldl`, `foldr`, `listAppend`, `concatMap`, `listLength`), `orElse`, `newRef`/`readRef`/`writeRef`, `floatEq`. Missing: the mandated instances for types this implementation lacks (`Byte`, `Bytes`, `Grapheme`, `Rational`, `Duration`, `Instant`), container/traversal trait instances (`Functor`/`Foldable`/`Traversable`/… — `Eq`/`Ord`/`Show` for `List`/`Option`/`Result` are also absent), monad operators (`>>=`, `>>`), `traverse`/`sequence`, equality combinators (`sym`, `trans`, `cong`, `subst`, `pathInd`, `absurd`), `witness`/`summon`, fibers/STM/timers, arrays/sets/maps, ranges, `re`/`b`/`type` handlers, `bracket`. |
| §28.2.3 Standard fixities | Implemented | `Kappa.Resolve.defaultFixities`. |
| §29 Required standard modules | Not implemented | None of `std.atomic`, `std.supervisor`, `std.hash`, `std.unicode`, `std.bytes`, `std.debug`, `std.config`, `std.build`. |

## Part VIII. Core Semantics and Identity

| Section | Status | Notes |
| --- | --- | --- |
| §30.1–30.2 Elaboration, KCore | Partial | Bidirectional elaboration to a pragmatic KCore subset (`Kappa.Core`): de Bruijn terms, Pi with icit+quantity, saturated constructors, match, canonical records/variants, literals, metas. Deliberate delta: do-blocks stay structured (`CDo` + `KItem`) rather than lowering to the spec's completion-kernel combinators; the interpreter executes the kernel semantics directly (§18.8). |
| §31.1 Definitional equality | Partial | NbE conversion: β, δ (conversion-reducible definitions only, §15.1), ι (match/if on known scrutinees), record/variant canonical-form equality, suspension reduction, function η. Quantities participate in Pi identity. Conversion is fuel-bounded; fuel exhaustion is only ever reported as "not equal" (sound, incomplete). |
| §31.2 Erasure | Partial | Erased (quantity-0) implicit constructor parameters are dropped from runtime payloads; full erasure pipeline absent. |
| §31.3 Variant runtime representation | Implemented | Tags are canonical renderings of alias-normalized member types, so `Int` and `Integer` members coincide. |
| §31.4 Record canonicalization | Implemented | Lexicographic canonical field order; initializers still evaluate in source order via a `CLet` chain. |
| §31.5 Elision of mutable state | Not implemented | `var` cells are real `Ref`s at runtime. |
| §32 Runtime semantics | Partial | §32.1 strict, call-by-value, left-to-right evaluation; §18.8 completion kernel with exit actions run exactly once; typed IO failures via catch/finally. No fibers, STM, handlers, timers. |
| §33 Content-addressed identity | Not implemented | |

## Part IX. Compiler, Tooling, Config, and Build

| Section | Status | Notes |
| --- | --- | --- |
| §34 Pipeline, IRs, tooling, lowering | Not implemented | No KFrontIR/KBackendIR, no queries, no dumps. The internal pipeline is parse → resolve → elaborate → interpret (`Kappa.Pipeline`), exposed as `kappa (check\|run\|test)`. |
| §35 Config mode | Not implemented | |
| §36 Build system | Not implemented | |

## Part X. Tooling, IDE, and Interactive Semantic Services

| Section | Status | Notes |
| --- | --- | --- |
| §37 LSP/IDE services | Not implemented | |

## Appendix T. Test harness

| Section | Status | Notes |
| --- | --- | --- |
| §T.2–T.8 | Partial | Single-file inline tests, directory suites (`suite.ktest`/`main.kp`/direct directory argument, multi-file compilation in import order), the §T.3 directive subset listed in TESTING.md, inline `--!!` markers, unsupported-classification per §T.8. `mode analyze`/`compile`, backends, capabilities, stdin/args, dump assertions: classified unsupported. |
