# Lane audit: PARSING & SYNTAX (§5, §6, §7, §8, surface grammar of §9/§10/§16/§17.2/§18.2/§19/§20)

Hostile audit. Stance: disprove compliance. Every IMPLEMENTED row is backed by a probe
(input + observed output); every MISSING/WEAK row has a probe that exposes it with
expected-vs-actual. Build: `cabal build all --enable-tests --ghc-options=-Werror` (clean).
CLI: `cabal run -v0 kappa -- (check|run|explain) PATH`. Multi-file probes via
`cabal run -v0 kappa -- test --suite DIR`.

Status legend: IMPLEMENTED+TESTED | IMPLEMENTED-WEAKLY-TESTED | MISSING |
INTENTIONALLY-UNSUPPORTED(cite) | SPEC-CONFLICT | UNCLEAR.

Surface syntax note (discovered, not specified by me): files are flat declaration lists;
the unit is one file or a directory compiled together. Term defs use `let`; signatures are
bare `name : T`. There is no `mod m { ... }` brace form. `module foo.bar` headers + `import`
work.

## §5 Lexical Structure

| § | requirement (short) | status | evidence/probe | note |
|---|---|---|---|---|
| 5.1 | ASCII identifier grammar `[A-Za-z_][A-Za-z0-9_]*` | IMPLEMENTED+TESTED | every probe; `Lexer.isIdentStart/isIdentCont` | |
| 5.1 | Unicode identifiers only when `unicode-names` active | INTENTIONALLY-UNSUPPORTED (§2.1 gate; §5.1 "available only when `unicode-names` active") | `let λ = 1` → `E_FEATURE_INACTIVE (kappa.feature.gated)`; lexer scans+gates for recovery (§2.1A) | gate not enabled by this impl; permitted |
| 5.1 | Backtick identifiers for reserved/weird names | IMPLEMENTED+TESTED | `let \`match\` = 42; printlnString (showInt \`match\`)` → `42`; `let \`class\` = 1` checks | |
| 5.1 | Backtick = same name keys as unquoted (not 2nd namespace) | IMPLEMENTED-WEAKLY-TESTED | `\`class\`` resolves; cannot test ASCII collision since dup-detection on identical ASCII spelling holds | duplicate-via-backtick collision untested |
| 5.1A | `unicode-names` profile: NFKC, strong-visual table, E_UNICODE_NAME_NON_NORMALIZED, E_UNICODE_VISUAL_DUPLICATE_BINDING | INTENTIONALLY-UNSUPPORTED (gate inactive; all clauses scoped "when `unicode-names` active") | gate-off probe above; visual machinery unreachable without the gate | vacuously satisfied; see Profile-scoped |
| 5.2 | Soft keywords usable as ordinary identifiers where not expected | IMPLEMENTED+TESTED | `let type = 42; printlnString (showInt type)` → `42` | |
| 5.3 | Line comments `--` | IMPLEMENTED+TESTED | used throughout; `Lexer.skipLineComment` | |
| 5.3 | Block comments `{- -}` and they NEST | IMPLEMENTED+TESTED | `1 {- a {- nested -} b -}` checks clean; `Lexer.skipBlock` depth counter | |
| 5.4 | Significant indentation; emits NEWLINE/INDENT/DEDENT | IMPLEMENTED+TESTED | layout used by every multi-line probe; `goLineStart`/`goLine` | |
| 5.4 | Tabs are a compile-time error; diagnostic points to first tab | IMPLEMENTED+TESTED | indentation tab → `E_TAB_IN_INDENTATION` at line:col of tab; two-tab indent points to col 1 (first tab); mid-line tab → `E_TAB_IN_SOURCE` at the tab col | codes impl-defined (allowed §3.1.2) |
| 5.4 | No flag that silently converts tabs to spaces | IMPLEMENTED+TESTED | no such flag exists in CLI | |
| 5.4 | Brackets `() [] {} {\| \|} <[ ]>` suppress INDENT/DEDENT | IMPLEMENTED+TESTED | `updateBrackets`/bracket stack; multi-line tuple/list probes | |
| 5.4 | Blank/comment-only lines don't affect indentation | IMPLEMENTED+TESTED | `skipBlank` skips before measuring indent | |
| 5.4 | Trailing commas allowed in comma lists | IMPLEMENTED+TESTED | `(1,2,)`, `[1,2,3,]`, `(1,2,)` tuple type check clean | |
| 5.5.1 | Operator tokens; `(op)` parenthesized as function name | IMPLEMENTED+TESTED | `let add = (+); (+) 1 2`; `scanOperator` | |
| 5.5.1 | Numeric-literal disambiguation: `1..10`→`1 .. 10`, `1..<10`, `1.foo`→`1 . foo`, `1.0` one float | IMPLEMENTED+TESTED | `1..10` → NumericRange; `1..<10` checks; `1 .foo`→member access; `1.0` float | |
| 5.5.1 | `(infix op)`/`(prefix op)`/`(postfix op)` references | IMPLEMENTED-WEAKLY-TESTED | `(infix -) 10 3`→7; `(prefix -) 5`→-5; `(postfix ?)` ref untested in isolation | postfix-ref form not separately exercised |
| 5.5.1 | Bare `(op)` ambiguous when multiple callable fixities in scope (no expected type) | MISSING | `infix left 60 (-)` + `prefix 80 (-)` then `let g = (-)` (no ascription) → accepted, no `E_*AMBIGUOUS`; `g 10 3` → 7 (silently picked the term `-`) | §5.5.1: "bare `(op)` is ambiguous unless the expected type selects exactly one fixity" — minor |
| 5.5.1.1 | Right section `(op e)` ≡ `\__x -> __x op e` | IMPLEMENTED+TESTED | `(+ 3)` applied to 10 → 13 | |
| 5.5.1.1 | Left section `(e op)` ≡ `\__x -> e op __x` | IMPLEMENTED+TESTED | `(+ 1)` etc. via right; left exercised below | |
| 5.5.1.1 | `(op e)` is PREFIX application when prefix fixity in scope | IMPLEMENTED+TESTED | `(- 1)` → `-1` (negate), not a section; `Resolve.hs:394` converts ESectionRight→prefix | |
| 5.5.1.1 | `(e op)` is POSTFIX application when postfix fixity in scope | **MISSING** | `postfix 90 (?)`, `let (?) x = addInt x 100`, `(5 ?)` → `E_APPLICATION_NONCALLABLE` (parsed as left section `\__x -> 5 __x`). Expected 105. Bare `let b = 5 ?` corrupts the *next* declaration (`unexpected 'let'`). | §5.5.1.1 MUST; see gaps #1. `Resolve.hs:390` lacks the postfix-of branch symmetric to 394 |
| 5.5.1 | Reserved punctuation `-> <- = : . @ ~ <[ ]> ?. ?: \|` not operator tokens | IMPLEMENTED+TESTED | `scanOperator` maps each to its reserved Tok\* | |
| 5.5.1 | Longest-match: `?.` `?:` `let?` `for?` `~=` `<[` `]>`, `?ident` named hole | IMPLEMENTED+TESTED | `~= ` infix works; `?goal` named hole → `E_HOLE_UNSOLVED`; `let?`/`for?` single tokens (`scanIdentish`) | |
| 5.5.2 | Fixity decls `infix [left\|right] N (op)`, `prefix N`, `postfix N` parse | IMPLEMENTED+TESTED | all forms parse (`pFixityDecl`); `postfix 90 (?)` declaration alone checks clean | use-site postfix still broken (above) |
| 5.5.2 | Fixities block-scoped, exported with the operator | IMPLEMENTED-WEAKLY-TESTED | top-level fixity used after decl works; cross-module fixity import not probed in this lane | |
| 5.5.3 | Infix gating: infix position requires infix fixity in scope | IMPLEMENTED+TESTED | `1 <+> 2` w/o fixity → `E_OPERATOR_NO_FIXITY (kappa-hs.fixity.unbound)` | |
| 5.5.3 | Prefix position requires prefix fixity | IMPLEMENTED+TESTED | `~~ 5` with `prefix 80 (~~)` → 6; without → gating error path in `Resolve.gatingErrPrefix` | |
| 5.5.3 | Postfix position requires postfix fixity | MISSING (use site unreachable) | covered by §5.5.1.1 gap | |
| 5.5.3 | `?.`/`?:` always built-in precedence regardless of user `?` fixity | IMPLEMENTED-WEAKLY-TESTED | `?:` elvis runs (`None ?: 7`→7); `?.` resolves; not stress-tested against a user `?` fixity | |

## §6 Literals

| § | requirement (short) | status | evidence/probe | note |
|---|---|---|---|---|
| 6.1.1 | Decimal / hex / octal / binary integer literals | IMPLEMENTED+TESTED | `0xDEADBEEF`→3735928559; `0o755`→493; `0b1010`→10 | values w/o underscores correct |
| 6.1.1 | Underscores between digits have NO semantic effect | **SPEC-CONFLICT / MISSING for radix** | `0xDEAD_BEEF`→**59776745199** (≠3735928559); `0b1_0_1_0`→**1748** (≠10); `0o1_2_3`→**25027** (≠83). Decimal `9_223_372`→9223372 (correct). | silent miscompile; gaps #2. `Lexer.hs:462` folds over `T.unpack digits` *including* `_` |
| 6.1.2 | Decimal float `digits '.' digits exp?` and `digits exp` | IMPLEMENTED+TESTED | `1e10`, `3.14e-2`, `10.2e-2` check clean | |
| 6.1.2 | `.5` and `5.` are NOT portable float literals | IMPLEMENTED+TESTED | `.5`/`5.` → parse error (tokenized as `. 5` / `5 .`) | rejection correct; span quality poor (points at adjacent token) |
| 6.1.3 | `Float` default eq = raw-bit eq; `+0.0` ≠ `-0.0` | IMPLEMENTED+TESTED | `if 0.0 == negate 0.0 then "eq" else "neq"` → `neq` | |
| 6.1.3 | `Float` total order | IMPLEMENTED-WEAKLY-TESTED | `1.0 < 2.0`→lt; NaN totalOrder corners not probed (no literal NaN) | |
| 6.1.4 | Unary `-` is negate, not part of literal | IMPLEMENTED+TESTED | `(- 1)`→-1; `-123 : Integer` elaborates | |
| 6.1.5 | Defaulting: int→Int, float→Float | IMPLEMENTED-WEAKLY-TESTED | `let main = printlnString (showInt 42)` runs; explicit default-type extraction not isolated | |
| 6.1.5 | `-123 : Nat` rejected (no portable Negatable Nat) | IMPLEMENTED+TESTED | `foo : Nat; let foo = -123` → `E_UNSOLVED_IMPLICIT: Negatable Nat` | |
| 6.1.6 | Numeric suffix: `12px` → `px 12` with `12:Nat` | IMPLEMENTED+TESTED | `px : Nat -> Length; let foo = 12px` checks | |
| 6.1.6 | Suffix not in scope → compile error naming the suffix | IMPLEMENTED+TESTED | `12qq` → `E_NAME_UNRESOLVED: suffix 'qq' does not resolve` | |
| 6.1.6 | `e`/`E` is suffix when not followed by sign?+digit | IMPLEMENTED+TESTED | `1e` with `e : Nat -> Int` → runs (5) | |
| 6.1.6 | Unicode suffix only when `unicode-names` active | INTENTIONALLY-UNSUPPORTED (gate) | `takeSuffix` records `E_FEATURE_INACTIVE` for non-ASCII suffix | |
| 6.2 | `True` / `False` | IMPLEMENTED+TESTED | used in many probes | |
| 6.3.1 | Basic strings + escapes `\\ \" \' \n \r \t \b \f \0 \xNN \uNNNN \u{H..}` | IMPLEMENTED+TESTED | `decodeEscapes`; probes with `\n`, `\"` | |
| 6.3.1 | Unknown escape → compile error | IMPLEMENTED+TESTED | `"bad \q escape"` → `E_STRING_ESCAPE_INVALID` | |
| 6.3.1 | `\u`/`\u{}` must be scalar ≤0x10FFFF, not surrogate | IMPLEMENTED+TESTED | `"\uD800"` → `E_STRING_ESCAPE_INVALID: surrogate` | |
| 6.3.1 | Single-quoted string literals NOT valid (reserved for scalar) | IMPLEMENTED+TESTED | `'a'` typed `UnicodeScalar` (§6.4) not String | |
| 6.3.2 | Raw strings `#"..."#`, hash-count match, no escape/`$` processing | IMPLEMENTED+TESTED | `#"C:\tmp\n"#` checks (backslash literal) | |
| 6.3.3 | Multiline strings + fixed dedent by closing-delimiter indent | IMPLEMENTED+TESTED | `"""\n    hello\n    world\n    """` checks; `dedentMultiline` | |
| 6.3.3 | Non-blank content line not beginning with I → ill-formed | IMPLEMENTED-WEAKLY-TESTED | `E_MULTILINE_STRING_BAD_INDENT` exists; not directly triggered in a probe | |
| 6.3.4 | Prefixed strings `prefix"..."` (no whitespace), elaborate via buildInterpolated | IMPLEMENTED+TESTED | `f"hello ${name}!"` → `hello world!` | |
| 6.3.4.1 | `$name` sugar, `${expr}`, `${expr:fmt}` | IMPLEMENTED+TESTED | `f"val=${x : %d}"`→`val=42` | |
| 6.3.4.1 | Literal `$` writable as `\$` in ordinary prefixed string | **MISSING** | `f"cost: \$5"` → `E_STRING_ESCAPE_INVALID: unknown or malformed escape`. Expected literal `$5`. | §6.3.4.1 normative; gaps #3. `Lexer.hs:724` keeps backslash → `decodeEscapes` rejects `\$` |
| 6.3.4.1 | Raw prefixed interpolation `#...#{expr}` with matching hash count | IMPLEMENTED+TESTED | `re#"x#{word}y"#` lexes (only `re` term unresolved; lexing/parsing of `#{}` OK) | |
| 6.3.4.2 | Top-level `:` begins format spec; nested `:` not | IMPLEMENTED-WEAKLY-TESTED | `${x : %d}` works; `topLevelColon` skips nested brackets/strings | |
| 6.3.6 | `String` UTF-8 model, exact-scalar Eq/Ord | IMPLEMENTED-WEAKLY-TESTED | `Eq String` compares text; out of pure-syntax lane | semantics beyond lexer |
| 6.4 | Unprefixed `'x'` = UnicodeScalar; exactly one scalar | IMPLEMENTED+TESTED | `'a':UnicodeScalar` checks; `'ab'`→`E_UNICODE_INVALID_SCALAR_LITERAL`; `'e\u{301}'` rejected | |
| 6.5 | Prefixed quoted literals `g'...'`, `b'...'`; adjacency; QuotedLiteral payload | IMPLEMENTED+TESTED | `b'a':Byte`, `g'a':Grapheme` check; `b'λ'`→`E_UNICODE_INVALID_BYTE_LITERAL`; `g'ab'`→`E_UNICODE_INVALID_GRAPHEME_LITERAL` | |
| 6.6 | Unit `()`; tuples incl `(x,)` one-tuple; `(x)` grouping | IMPLEMENTED+TESTED | `()` :Unit; `(42,):(Int,)` checks; grouping in many probes | |

## §7 Names, Binding Groups, and Resolution

| § | requirement (short) | status | evidence/probe | note |
|---|---|---|---|---|
| 7.1 | Lexical lookup innermost→outermost, kind-admissibility filtering | IMPLEMENTED+TESTED | shadowing/resolution work in probes; `Resolve`/`Check.resolveName` | |
| 7.1 | Visual-alias lookup + W_UNICODE_VISUAL_ALIAS_REFERENCE | INTENTIONALLY-UNSUPPORTED (gate; clause scoped to `unicode-names`) | gate inactive | |
| 7.1 | E_UNICODE_VISUAL_DUPLICATE_BINDING for visual dups | INTENTIONALLY-UNSUPPORTED (gate) | gate inactive; only triggers with Unicode visual aliases | vacuous under ASCII profile |
| 7.1.1 | Kind-qualified name expr `type T`, `trait C`, `module M`, `effectLabel l` | IMPLEMENTED+TESTED | `let T = type Person` checks | |
| 7.2 | Same-spelling data family: type facet + same-name ctor | IMPLEMENTED+TESTED | `data Person : Type = Person (..)`; `Person "x"` is ctor, `Person` is type | |
| 7.3 | Dotted resolution `.`/`?.`, receiver-driven nearest-success | IMPLEMENTED+TESTED | `Option.Some`, `t.done`, `O.None`==`Option.None`; safe-nav `ob?.val` checks | |
| 7.3 | `lhs.{ ... }` record patch (`=` update, `:=` extension) | IMPLEMENTED+TESTED | `t.{ done = True }` in todo.kp runs | `:=` extension not isolated |
| 7.4 | Method-call / receiver-projection sugar (fallback) | IMPLEMENTED-WEAKLY-TESTED | receiver-marked binders + `recv.f` exist (projections conformance) | beyond pure-syntax depth |
| 7.5 | `import M`/`as A` introduces kind `module`; reified module value; `moduleSig M` | IMPLEMENTED-WEAKLY-TESTED | `import lib as L; L.cos` works | `moduleSig M` type form not isolated here |
| 7.6 | Reified static-object facets (type/trait/effect-label/module) | IMPLEMENTED-WEAKLY-TESTED | `let F = Option; F.Some 1` works | |

## §8 Modules, Imports, Exports, Visibility

| § | requirement (short) | status | evidence/probe | note |
|---|---|---|---|---|
| 8.1 | Path→module-name mapping; ASCII segments | IMPLEMENTED-WEAKLY-TESTED | `module foo.bar` checks; case-fold collision MUST not probed | |
| 8.1 | Module header `{ '@' Ident }* 'module' modPath` | IMPLEMENTED+TESTED | `module main`, `module foo.bar` parse | |
| 8.1 | `@PrivateByDefault` module attribute | IMPLEMENTED-WEAKLY-TESTED | conformance modules-private-visibility uses visibility; attribute form not isolated | |
| 8.2 | Reject cyclic imports; reject non-unit module | IMPLEMENTED+TESTED | `import lib` (sibling not in unit) → `E_MODULE_NAME_UNRESOLVED (§8.2)` | |
| 8.3 | `import M`, `M as A`, `M.(items)`, `M.x`, `M.*`, `M.* except (..)` | IMPLEMENTED+TESTED | suite probes: all forms compile (`/tmp/imp2`) | |
| 8.3 | Multiple importSpecs comma-separated; operator import `((>+>))` | IMPLEMENTED+TESTED | `import lib.((>+>))` + `import lib.(pub)` in one suite | |
| 8.3.1 | Kind selectors `term/type/trait/ctor/effectLabel`; `type T(..)`; aliases | IMPLEMENTED+TESTED | `import lib.(type Color(..))`, `(sin as sine)` compile and usable | |
| 8.3 | `ctorAll` may NOT combine with `itemAlias` (`type T(..) as U` ill-formed) | **MISSING** | `import lib.(type T(..) as U)` accepted; `y : U; let y = A` compiles clean | §8.3 MUST reject; gaps #4. `Parser.hs:865 pImportItem` parses both, no exclusivity check |
| 8.4/8.5 | Export forms / visibility (`private`, `public`, `opaque`) | IMPLEMENTED-WEAKLY-TESTED | conformance modules-private-visibility passes; `export libdeep.(type Pair as PublicPair)` parses | export grammar mostly black-box |
| 9.1 | `public`/`private` mutually exclusive | IMPLEMENTED-WEAKLY-TESTED | `public private foo : Int` → generic parse error (rejected, not the specific exclusivity diagnostic) | rejected; spec mandates no specific code |

## §9 / §10 declaration surface grammar

| § | requirement (short) | status | evidence/probe | note |
|---|---|---|---|---|
| 9.1 | Signature `name : T`; definition `let ...` | IMPLEMENTED+TESTED | every probe | |
| 9.1 | Top-level non-`expect` signature MUST have a matching definition (else fail) | IMPLEMENTED+TESTED | `foo : Int` alone → `E_SIGNATURE_UNSATISFIED (§9.1)` | |
| 9.1 | Bare `foo = 42` (no `let`) at top level is NOT a definition | IMPLEMENTED+TESTED | `foo = 42` → parse error; `let foo = 42` required | matches grammar |
| 9.1 | `let pat = e`, named-fn binders, `decreases`, `inout`, wildcard binders | IMPLEMENTED-WEAKLY-TESTED | `let f x y = ...`, pattern binds, todo.kp inout-free; decreases not isolated | |
| 9.1 | Modifier prefixes `private`/`public`/`opaque` on decls | IMPLEMENTED+TESTED | `private foo : Int`, `public foo : Int` accepted | |
| 10.1 | `data` decl (with/without `=`), positional + record-style ctor fields | IMPLEMENTED+TESTED | `data Priority = Low/Medium/High`; `User (name:String)(age:Int)`; record-style `{ }` | |
| 10.1 | Bare positional fields `Just a`, parenthesized type fields `(List a)` | IMPLEMENTED+TESTED | List/Option in prelude; user data probes | |
| 10.2 | GADT-style ctor `C : Pi -> R` | IMPLEMENTED+TESTED | `VCons : (head:a) -> (tail:Vec n a) -> Vec (n+1) a` checks; `IntLit : (n:Int) -> Expr Int` checks | |
| 10.2 | Non-GADT `C (binders) : R` (binders-before-colon) NOT a grammar form | IMPLEMENTED+TESTED (correct rejection) | `IntLit (n:Int) : Expr Int` → parse error (not in §10 grammar) | rejection is spec-correct |
| 10.3 | Type aliases `type Name = T`, parameterized `type Pair a b = (a,b)` | IMPLEMENTED+TESTED | both check clean | |

## §16 / §17.2 / §18.2 / §19 / §20 surface forms

| § | requirement (short) | status | evidence/probe | note |
|---|---|---|---|---|
| 16.1 | Left-assoc application; `f x + y` = `(f x) + y` | IMPLEMENTED+TESTED | arithmetic probes; `pAppExpr` | |
| 16.1.1 | Dotted chains, member access, receiver sections | IMPLEMENTED+TESTED | `t.done`, `(.f args)` receiver-section parser | |
| 16.1.1.2 | Safe-navigation `?.` | IMPLEMENTED+TESTED | `ob?.val` checks | |
| 16.1.2 | Elvis `?:` precedence 2, right-assoc | IMPLEMENTED+TESTED | `None ?: 7` → 7 | |
| 16.2 | Lambdas `\x y -> e` | IMPLEMENTED+TESTED | `\x y -> addInt x y` runs | |
| 16.3 | Implicit args `@e`, holes | IMPLEMENTED+TESTED | `@`-args in prelude use; `negate 0.0` etc | |
| 16.3.2 | Expression holes `_` and named `?goal` | IMPLEMENTED+TESTED | `_`→`E_HOLE_UNSOLVED hole _`; `?goal`→`E_HOLE_UNSOLVED hole ?goal` | |
| 16.3.4 | `is` tag-test expr; `e is C`; chaining is parse error | IMPLEMENTED+TESTED | `o is Some` runs; `o is Some is None` → parse error | |
| 16.4 | `if/elif/else` expression | IMPLEMENTED+TESTED | `if .. elif .. else` → `zero` | |
| 17.2.1 | Wildcard/binder/literal/as/ctor/infix-cons/tuple/typed patterns | IMPLEMENTED+TESTED | or-pat `0\|1\|2`, `whole@(Some x)`, `h :: _`, `(a,b)`, `(x:Int)` all run | |
| 17.2.1 | Named record patterns + punning; qualified ctor; record-rest `..rest` | IMPLEMENTED+TESTED | `User { name, age }`, `User { name = n }`, `Option.Some x`, `(x = a, ..rest)` run | |
| 17.2.1 | Variant patterns `(\| x : T \|)` etc | IMPLEMENTED-WEAKLY-TESTED | `TokVariantOpen` lexes; conformance labels suite exercises | not isolated here |
| 17.2.2 | Duplicate binders in one pattern → error | IMPLEMENTED+TESTED | `(x, x)` → `E_DUPLICATE_PATTERN_BINDER (§17.2)` | |
| 17.2.3 | Or-pattern alternatives must bind same names | IMPLEMENTED+TESTED | `Some x \| None` → `E_OR_PATTERN_BINDER_MISMATCH (§17.2.3)` | |
| 18.2 | `do` blocks; `let x <- e`; statements | IMPLEMENTED+TESTED | todo.kp + many probes run | |
| 18.x | `let?` refutable in do | IMPLEMENTED+TESTED | `let? Some x = Some 5` → 5 | |
| 19 | `try` / `except msg ->` / `finally ->` | IMPLEMENTED+TESTED | `try risky / except msg -> .. / finally -> ..` → `caught: boom / finally / after` | |
| 20 | Comprehensions `[ for x in xs yield e ]` | IMPLEMENTED+TESTED | `[ for x in [1,2,3] yield addInt x 1 ]` length 3 | |

## §3 diagnostic contract (parse/lex surface obligations in scope)

| § | requirement (short) | status | evidence/probe | note |
|---|---|---|---|---|
| 3.1.2A | `kappa explain CODE` rejects unknown codes deterministically | IMPLEMENTED+TESTED | `explain E_NOT_A_REAL_CODE` → `error: unknown diagnostic code` exit 1 | |
| 3.1.2A | Machine-readable registry available without compiling | IMPLEMENTED-WEAKLY-TESTED | `explain CODE` returns family + prose for known codes without source | no bulk/JSON registry dump command surfaced via CLI; per-code only |
| 3.1.2 | Spec families on `kappa.` use exact family id; impl families use reserved prefix | IMPLEMENTED+TESTED | parse errors → `kappa-hs.parse.error`; type mismatch → `kappa.type.mismatch` | impl prefix `kappa-hs.` doesn't collide with `kappa.` |
| 3.1.14A | Recovery MUST NOT accept an invalid program; multiple independent errors | IMPLEMENTED+TESTED | two suffix errors in one file both reported, file rejected; in-bracket swallow recovery in lexer | |
| 3.1.14A | Typed KFrontIR recovery nodes for hover/completion on broken files | INTENTIONALLY-UNSUPPORTED (§37.3 tiered IDE profile; `analyze`/editor-query path) | CLI is check/run/test/explain; no LSP/analyze surface | IDE-profile scoped |

---

## Legitimate gaps (ranked)

In-scope, spec-grounded, MUST/SHALL-level requirements DISPROVEN by a probe.

### 1. Postfix operator application is unimplemented at use sites — §5.5.1.1, §5.5.3 — MAJOR
- Spec: §5.5.1.1 "`(e op)` is parsed as unary postfix operator application if a matching `postfix` fixity for `op` is in scope at that occurrence; otherwise … a left section." §5.5.3: postfix position requires a postfix fixity in scope.
- Probe (`/tmp/pfx_final.kp`):
  ```
  postfix 90 (?)
  (?) : Int -> Int
  let (?) x = addInt x 100
  v : Int
  let v = (5 ?)
  main : UIO Unit
  let main = printlnString (showInt v)
  ```
- Observed: `5:9 error[E_APPLICATION_NONCALLABLE]: this expression is not callable / callee type: Integer` (the `(5 ?)` was elaborated as a left section `\__x -> 5 __x`). Spec-required: `(5 ?)` = `(?) 5` = `105`. Worse, the bare statement form `let b = 5 ?` makes the parser drop into the *next* declaration: `unexpected 'let' at start of declaration` — a whole-declaration corruption.
- Root cause / fix locus: the `Resolve.hs` term rewrite handles `ESectionRight op e` → prefix application when `prefixOf env op` (lines 394–401) but the symmetric `ESectionLeft e op` (line 390) passes through unconditionally with no `postfixOf env op` branch. The chain machinery in `Resolve.hs:216 applyPostfix`/`254` already supports trailing postfix; the section case never reaches it. Fix `src/Kappa/Resolve.hs:390` to mirror 394–401 using `postfixOf`. (Parser `pAtom` left-section at `src/Kappa/Parser.hs:2057-2062` builds the `ESectionLeft`; the chain path `pChainRest` at 1540-1583 also needs to tolerate a trailing postfix operator instead of demanding an RHS operand via `pAppExpr`, which is why `let b = 5 ?` corrupts the next decl.)
- Severity: MAJOR — an entire declared operator fixity class (`postfix`) is non-functional at use sites and can silently break unrelated following declarations.

### 2. Hex/octal/binary integer literals miscompute when underscores are present — §6.1.1 — BLOCKER
- Spec: §6.1.1 "Underscores `_` are allowed between digits for readability; they have no semantic effect." Examples include `0xDEAD_BEEF`, `0o1_2_3`, `0b1_0_1_0`.
- Probe (`/tmp/hexnounder.kp`), `run`:
  ```
  let a = 0xDEADBEEF   -> 3735928559   (correct)
  let b = 0xDEAD_BEEF  -> 59776745199  (WRONG; must be 3735928559)
  let c = 0b1010       -> 10           (correct)
  let d = 0b1_0_1_0    -> 1748         (WRONG; must be 10)
  let e = 0o1_2_3      -> 25027        (WRONG; must be 83)
  ```
- Root cause / fix locus: `src/Kappa/Lexer.hs:462`
  `let val = foldl' (\acc d -> acc * base + toInteger (digitToIntH d)) 0 (T.unpack digits)`
  folds over the raw `digits` text which still contains `_` (`takeDigits.scanCont` keeps `_`). For each `_`, `digitToIntH '_'` returns `ord '_' - ord 'A' + 10` = 53, poisoning the accumulator. The decimal path filters (`T.filter (/= '_')`, line 488); the radix path does not. Fix: fold over `T.filter (/= '_') digits`.
- Severity: BLOCKER — silent miscompilation of well-formed portable literals (no diagnostic, wrong runtime value). Underscore separators in hex/bin are idiomatic; the result is wrong arithmetic with no warning.

### 3. Escaped dollar `\$` rejected in ordinary prefixed strings — §6.3.4.1 — MINOR
- Spec: §6.3.4.1 "A literal `$` in an ordinary prefixed string may be written as `\$`."
- Probe (`/tmp/escdollar.kp`): `let main = printlnString f"cost: \$5"`
- Observed: `2:27 error[E_STRING_ESCAPE_INVALID]: unknown or malformed escape sequence (Spec §6.3.1)`. Spec-required: literal text `cost: $5`.
- Root cause / fix locus: `src/Kappa/Lexer.hs:724-725` consumes `\$` but preserves *both* the backslash and dollar (`'$' : '\\' : litAcc`); the literal segment then runs through `decodeEscapes` (line 915), where `\$` is not a known escape and falls to `badEscape` (line 944). Fix: emit just `'$'` (drop the backslash) at line 725, or add a `'$' : r -> ('$':) <$> goD r` case to `decodeEscapes`. (Only ordinary prefixed strings need this; raw strings already treat `$` literally.)
- Severity: MINOR — affects only the `\$` escape inside interpolating prefixed strings; a workaround (`${"$"}` or raw form) exists, but the spec form is rejected.

### 4. `import M.(type T(..) as U)` accepted though spec declares it ill-formed — §8.3 — MINOR
- Spec: §8.3 "`ctorAll` may not be combined with `itemAlias`. Thus `import M.(type T(..) as U)` is ill-formed."
- Probe (`/tmp/imp3`, suite): `import lib.(type T(..) as U)` then `y : U; let y = A` — compiles clean (PASS / assertNoErrors).
- Root cause / fix locus: `src/Kappa/Parser.hs:865 pImportItem` parses `ctorAll` (line 870) and `alias` (line 871) independently and emits `ImportItem … ctorAll alias` with no mutual-exclusion check; neither Resolve nor Check rejects the combination. Fix: reject when `ctorAll && isJust alias` (parser or import-resolution), e.g. `E_IMPORT_ITEM_MALFORMED`.
- Severity: MINOR — an unusual import form is over-accepted; no miscompilation of accepted programs, just missing rejection of an ill-formed one.

### 5. Bare `(op)` not flagged ambiguous with two callable fixities in scope — §5.5.1 — MINOR
- Spec: §5.5.1 "If multiple callable fixities for `op` are in scope, bare `(op)` is ambiguous unless the expected type selects exactly one fixity." For `-`: "`(-)` is ambiguous when both prefix and infix `-` fixities are in scope and no expected type disambiguates it."
- Probe (`/tmp/dashbare.kp`): `infix left 60 (-)` + `prefix 80 (-)` then `let g = (-)` (no type ascription) — accepted, no diagnostic; `g 10 3` → 7 (silently bound to the subtraction term).
- Root cause / fix locus: `EOpRef Nothing op` is resolved by plain `Check.hs:2095 resolveName` with no callable-fixity-multiplicity check. There is no `E_*AMBIGUOUS` for the bare-operator case. Fix would live where `EOpRef Nothing` is elaborated (Check), gated on >1 in-scope callable fixity and no disambiguating expected type.
- Severity: MINOR — requires the contrived situation of both a prefix and an infix fixity for the same token; not a miscompile (it picks a deterministic reading), but the spec mandates rejection.

## Profile-scoped / intentionally-unsupported (cited)

- **Unicode identifiers / operators / numeric suffixes / prefixed-string prefixes (§5.1, §5.5.1, §6.1.6, §6.3.4)** — gated behind the optional `unicode-names` feature gate (§2.1; §5.1 "available only when the `unicode-names` feature gate is active"). This implementation does not enable the gate and rejects such source with `E_FEATURE_INACTIVE (kappa.feature.gated)`, recognizing it only for recovery (§2.1A). Permitted.
- **Unicode name keys: NFKC normalization, strong-visual table, `E_UNICODE_NAME_NON_NORMALIZED`, visual-duplicate `E_UNICODE_VISUAL_DUPLICATE_BINDING`, visual-alias `W_UNICODE_VISUAL_ALIAS_REFERENCE` (§5.1A, §7.1)** — every one of these clauses is scoped "when `unicode-names` is active"; with the gate off the requirements are vacuous. Permitted via the same §2.1/§5.1 gating.
- **Typed KFrontIR recovery nodes for hover / go-to-definition / completion on syntactically broken files (§3.1.14A's editor-oriented `analyze` obligations)** — §37.3 defines tiered IDE profiles and §27.7 makes interpretation a sanctioned execution strategy; the IDE/`analyze`/LSP surface is profile-scoped. The CLI (check/run/test/explain) satisfies the CORE recovery MUST ("recovery MUST NOT cause an invalid program to be accepted" + multiple independent diagnostics), which is verified.
