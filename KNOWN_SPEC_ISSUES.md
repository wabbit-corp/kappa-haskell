# Known spec issues

Genuine ambiguities, contradictions, and implementation burdens found in
`docs/Spec.md` while building this implementation and its test suites.
Citations are to spec sections; "evidence" points at code or fixtures in
this repository where the issue had to be confronted.

## 1. §28.1: the prelude cannot be disabled, but black-box testing wants bare environments

§28.1 mandates that *every* source file is processed as if it imports
`std.prelude.*` plus a fixed unqualified constructor subset, and offers
no opt-out. Appendix T (§T.4) likewise defines no configuration
directive to suppress the prelude. Consequences:

* fixtures that probe pure name-resolution or duplicate-declaration
  behaviour always race against ~100 ambient prelude names (a fixture
  defining `map` or `(==)` is testing shadowing whether it wants to or
  not);
* a conforming implementation cannot even be *asked* to present a bare
  environment, although several §T.10 hygiene tests are most meaningful
  in one.

Evidence: `tests/conformance/names/duplicate.kp` must use names not
exported by the prelude for its `assertErrorCount`-style expectations
to be portable, because whether a *user* redefinition of a prelude name
is a duplicate, a shadow, or an ambiguity at use sites is decided by
§7/§8 scope rules that never address the implicit import specifically.

## 2. §11.4.1 / §28.2: the `(=)` declaration leaves the parameter/index split implicit

The normative declaration (§11.4.1, restated in §28.2):

```kappa
data (=) (@0 a : Type) (x : a) : a -> Type =
    refl : x = x
```

`a` and `x` are *parameters* (left of the `:`), while the second `a` is
an *index*. Nothing in §10/§11 states the elaboration consequences of
that split for `(=)` specifically, yet they are observable:

* `refl : x = x` only makes sense if `x` is fixed as a parameter and
  only the index position generalizes;
* unification/matching against `lhs = rhs` must treat `lhs`
  (parameter) and `rhs` (index) asymmetrically;
* §3.2.3's equality diagnostics talk about "left/right" without
  acknowledging the asymmetry.

An implementation must reverse-engineer the intended discipline from
the `refl` constructor. Evidence: `Kappa.Prelude` hand-builds `(=)` /
`refl` with exactly this parameter/index telescope; getting it wrong
breaks `tests/conformance/equality/*`.

## 3. §5.5.1: longest-match-first makes `[1]>x` lex as `]>`

§5.5.1 reserves `<[` and `]>` as single tokens and states they are
recognized "in preference to `<` plus `[` and `]` plus `>`"
(longest-match-first, §5.5.1 "Token recognition uses
longest-match-first"). Therefore `xs[1]>x` and `[1]>x` lex with an
effect-row close-bracket token `]>` in the middle of ordinary
index/comparison code, producing a confusing parse error far from the
cause. Whitespace (`[1] > x`) is required. The spec neither warns about
this nor requires a tailored diagnostic. Evidence: the lexer here
follows the rule literally (`Kappa.Lexer` longest-match table) and the
misparse reproduces.

## 4. §6.3.5 / §7.1.1 / §9: the soft keyword `type` needs unbounded lookahead

`type` is simultaneously:

* a declaration keyword (`type Int = Integer`, §9/§10);
* a conventional prefixed-string handler (`type"List Int"`, §6.3.5);
* the kind-qualifier in kind-qualified name expressions
  (`(type Foo)`-style selectors, §7.1.1).

Since keywords are soft (§5.2), a parser at `type` cannot decide which
production it is in without scanning past an arbitrarily long name or
to a string quote — and `type "…"` *with* whitespace must not be the
handler form (§6.3.4 requires adjacency), so token gluing cannot be
decided in the lexer either. The spec never acknowledges that this one
identifier requires special lookahead treatment. Evidence: this
parser special-cases `type` in several distinct productions
(`Kappa.Parser`); the
prefixed-string handler form for `type` is consequently left
unsupported (SPEC_COVERAGE.md §6.3.5).

## 5. §16.1.3 vs §16.4.2: short-circuit operators are "ordinary terms", yet flow typing must see through them

§16.1.3 defines `(&&)` and `(||)` as ordinary prelude functions over
`Thunk Bool` — first-class values, shadowable, passable. §16.4.2 then
requires flow typing to recurse through conditions built with `&&`,
`||`, and `not`, keyed (per §1, "resolved semantic identity", and the
§16.4.2 rules) to those exact prelude identities, not spellings. The
combination forces every conforming implementation to special-case
three "ordinary" functions inside its refinement engine, and leaves
unstated what happens when a user rebinds `(&&)` locally to a function
of the same type (refinement silently off? error?). The two sections
read as if written under different assumptions. (This implementation
sidesteps it only because flow typing is unimplemented —
SPEC_COVERAGE.md §16.4.)

## 6. §28.2.1 + §16.4.4: checked subtraction makes ordinary `x - y` unwritable without flow facts

`(-)` requires an implicit proof `(@_ : subDefined x y = True)`
(§28.2.1). For `Integer`, `subDefined x y = True` definitionally, so
conversion discharges the goal. But for any type where `subDefined` is
non-trivial (`Nat`: `y <= x`), `x - y` on *variables* cannot be written
at all unless flow-sensitive lower-bound facts (§16.4.4) or a manual
proof are in scope. The spec never says plainly that Nat subtraction is
effectively gated on implementing §16.4 flow typing; a minimal-profile
implementation thus accepts `5 - 3` but must reject symbolic `x - y`
with an unsolved-implicit error that puzzles users. Evidence:
`tests/conformance/equality/sub-proof.kp` (literal case via conversion)
vs `tests/conformance/equality/sub-unknown.kp` (symbolic case fails
`E_IMPLICIT_UNSOLVED` by design).

## 7. §3.1.2 / §3.1.4: diagnostic code names are implementation-defined, so black-box suites do not transfer

§3.1.2 makes codes stable but implementation-chosen; §3.1.4 pins only a
small table of portable aliases. Everything else (`E_UNRESOLVED_NAME`
vs `E_NAME_UNRESOLVED`, `E_TYPE_MISMATCH` vs `E_TYPE_EQUALITY_MISMATCH`,
layout-error naming, …) is unpinned, so an Appendix-T fixture that
asserts a code outside the alias table only works on the implementation
that wrote it. Appendix T presents fixtures as if they were portable
artifacts; without a much larger normative alias registry they are not.
Evidence: a large slice of the 509 external-corpus failures
(`tests/external-results.md`, "foreign diagnostic-code naming") match
behaviour but fail purely on the asserted code name.

## 8. §31.3: variant member identity by "canonical rendering" is not pinned enough for interop

§31.3 keys variant runtime representation to stable member identities
derived from the member *type*, with alias-transparent identity. But
the canonical rendering itself (parenthesization, spacing, qualified vs
unqualified names, ordering inside nested unions) is not normatively
specified, even though §33 content-addressed identity and any
cross-implementation data exchange depend on byte-stable tags. Two
conforming implementations can pass §13/§17 tests yet disagree on every
tag. Evidence: this implementation had to invent a rendering
(`Kappa.Pretty`, alias-normalized; commit `bc08ecd` "alias-stable
variant tags") and external fixtures still cannot check it
portably.

## 9. §T.2/§T.6: directory suites leave compilation order and failure scope unspecified

§T.2 says a directory suite's "compilation roots are all `.kp` files
under the suite root", and §T.6 distributes assertions over files — but
nothing specifies (a) the order in which roots are compiled, (b)
whether they form one program or independent compilations, or (c)
whether a diagnostic in one file should count against suite-level
`assertErrorCount` totals from another file's perspective. With
intra-suite imports the order is forced topologically, but for
non-importing files assertion semantics differ between "compile all
together" and "compile sequentially". Evidence: this harness had to
invent a policy — single program, import-order topological compile,
suite-level directive merge (`Kappa.TestHarness`, TESTING.md, commit
`dd427f0`) — with no spec text to appeal to, and external directory
suites only began passing once that particular policy was chosen.

## 10. §6.1.3 / §28.2: two float equalities with the surprising one on `(==)`

§6.1.3 fixes `Double`'s `Eq` instance to raw-bit equality and provides
IEEE numeric equality separately as `floatEq` (§28.2). So in Kappa,
`0.0 == -0.0` is `False` and `NaN == NaN` is `True` whenever the
payload bits coincide — the reverse of every mainstream language's
`==` on floats — and nothing in §28.2
requires a lint when `(==)` is used on floats. This is a deliberate
choice (it makes `Eq` lawful for hashing/canonicalization), but the
spec never flags the footgun, and test fixtures that "sanity check"
float equality portably will silently encode one convention or the
other. Evidence: `Kappa.Prelude` exposes both `eqDouble` (raw-bit,
backing `Eq Double`) and `floatEq`, per the letter of the spec.
