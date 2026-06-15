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

## 11. §5.2 vs juxtaposition application: soft keywords after an expression are inherently ambiguous

§5.2 (normative) requires that implementations "permit their use as
ordinary identifiers in contexts where a keyword is not syntactically
expected". But application is juxtaposition (§16.1.7), so *any*
identifier directly after an expression is a position where both
readings can be grammatically live: in `[for x in f take 3 yield x]`
the `take` may be an argument to `f` or a clause keyword, and §5.2
gives no tie-break (the clause reading is clearly intended, but the
spec never says clause keywords win over argument positions inside
comprehension bodies, nor whether a separator is required). The same
holds for every expression-continuing keyword: `e is p`, `e captures
(r)`, `seal e as T`, `decreases m by r`, `if c then a else b` — each
makes `f is`, `f as`, `f then` (bare references in argument position)
unparseable-as-identifiers without unbounded context tracking, in
direct tension with §5.2's blanket "must permit".

This implementation resolves the tension contextually for the
query/handler keyword family (`group by order skip take distinct join
yield into when handle deep`): they terminate an argument run only
inside comprehension bodies (clause reading wins there, identifier
reading everywhere else; `deep` is keyword-read only when followed by
`handle`). The expression-continuing/statement keywords remain
context-insensitive argument terminators — the residual delta
enumerated in SPEC_COVERAGE.md §5.2. Evidence:
`tests/conformance/lexer/soft-keyword-identifiers.kp`, and
`Kappa.Parser` (`stopKeywords` vs `queryStopKeywords` /
`isStopKeywordAt`).

## 12. §21.6 vs §21.2: the convenience reflection queries are `Elab`-typed, but corpus programs use them as plain values

§21.6 types the convenience queries in `Elab`
(`defEqSyntax : … -> Elab Bool`,
`headSymbolSyntax : … -> Elab (Option Symbol)`), §21.2 makes
`$( … )`/`reifyCore` the only re-entry from elaboration-time
reflection into ordinary terms and forbids any "generic splice or
coercion … from meta-phase ordinary values directly into ordinary
runtime terms", and §11.1.6 lists `Symbol` among the elaboration-time
only, erased types. Yet the external corpus's static-object
reflection fixtures (`static_objects.reflection_accept_*`) bind
`sameType : Bool` directly to `defEqSyntax '{ … } '{ … }` and
`match` on `headSymbolSyntax '{ … }` in an ordinary definition,
asserting **no errors** — under the `Elab` signatures alone these
bodies cannot typecheck (`Elab Bool ≠ Bool`), and no spec rule says
an `Elab` query in an ordinary position is run implicitly.

The two readings cannot both hold; this implementation reconciles
them narrowly: the §21.6 wording that these operations "are
elaboration-time queries" is taken to license the elaborator running
an *applied standardized query* at its call site when (and only when)
the expected type is not `Elab`-headed, residualizing the first-order
result; in an `Elab`-typed position the spec signature is kept
(`tests/conformance/macros/reflection-query-elab.kp`). The
accommodation is restricted to `defEqSyntax`/`headSymbolSyntax` —
no generic meta-to-object coercion exists. Evidence:
`Kappa.Check.elabReflQuery`,
`tests/conformance/macros/reflection-queries.kp`.

## 13. §5.4: multi-line operator continuations at constant deeper indentation are undefined

§5.4 says that lines indented deeper than a logical line's first token
"form a continuation", but it never defines how *several* continuation
lines at the *same* deeper level relate to each other. This
implementation's Python-style layout opens an indented block at the
first deeper line, so each further line at that same level begins a new
statement: `a +` / `    b +` / `    c` (one constant continuation
level) fails to parse, while a single continuation line and
strictly-increasing indentation (`a +` / `    b +` / `        c`) both
work. The corpus's source implementation accepts the constant-level
form; both behaviors are defensible under §5.4's non-exhaustive text.
Same family as the two layout tracked gaps in
`tests/external-blocked.md`
(`fuzz.pending.reject_invalid_do_bind_indented_continuation`,
`fuzz.pending.reject_invalid_indented_expression_continuation`), where
the corpus expects the *opposite* (a syntax error on an indented
continuation after a complete do-bind RHS, where §5.4's reading here
makes it an application continuation). A normative continuation rule —
one logical line extends until a line at or below its starting column —
would settle all three.

## 14. §10.4: the strict-positivity fixed-point initialization direction is degenerate as written

§10.4 specifies computing parameter-positivity signatures for a mutually
recursive `data` group by fixed-point iteration and instructs:
"initialize every parameter of every type in the group as non-positive;
repeatedly recompute the signatures using the current signatures of the
whole group until a fixed point is reached." The recompute operator is
monotone in the *more-positive* direction — a parameter already known
positive lets a recursive index `T … pi …` recurse strictly-positively
rather than forcing `pi` to be absent — so iterating from the
all-non-positive bottom yields the *least* fixed point, which is
degenerate: it marks `a` in `data Tree a = Leaf | Branch (Tree a) a
(Tree a)` as non-positive (when checking `Branch`'s first field `Tree a`
with `Tree`'s still-non-positive signature, the index `a` is required to
be absent, which fails), and the iteration is already stuck at the
bottom. The signature the spec's own accepted examples require is the
*greatest* fixed point: start every parameter positive and refine
downward until stable. This implementation computes the greatest fixed
point (`positivityPass`/`fixpoint` in `Kappa.Check`, `sig0 = all True`),
which accepts §10.4's accepted examples (Tree, `Rose a = Node a (List
(Rose a))`) and rejects its rejected ones (`Bad`, `Rose a = Node a
((Rose a -> a) -> Rose a)`). The *rejection judgement* itself is then
computed against the converged signatures exactly as §10.4 describes.
Evidence: `Kappa.Check.positivityPass`,
`tests/conformance/data_types/positivity-*.kp`.

## 15. §3.1.5A / §30.2.3: KCore-node provenance frames vs diagnostic-facing provenance

§3.1.5A defines a full `ProvenanceFrame` record (id, kind, step, query,
inputs, inputObjects, output, generatedObject, explanation) and requires
that "every synthetic origin MUST either carry or reference a provenance
frame" and that a verbose diagnostic mode SHOULD render the whole chain.
§30.2.3 separately requires that "every synthetic KCore node MUST carry
provenance (origins + introduction kind)" and §30.2.3A requires per-erased
-occurrence erasure justifications. Read literally these demand a
provenance side-table threaded through KCore (`Term`), plus a query/stage
-dump surface to reconstruct chains.

The full KCore-node provenance store and its dump surface are §34 tooling
(stage dumps, query traces, conformance-verification mode) — explicitly
profile-scoped by §37.3 tiers and the §34 scope rule, and excluded from
the CORE remediation set (see `SPEC_AUDIT_MATRIX.md` profile-scoped
ledger). This implementation therefore implements only the
*diagnostic-facing* slice of §3.1.5A: a desugaring/generated construct
that produces a diagnostic blames the user-written source as `primary`
(spans are preserved through desugaring) and records the desugaring
provenance as a `desugared-from`/`generated-site` related origin (e.g.
the `!e` splice desugaring in `Kappa.Check`, `EBang`). It does **not**
attach a `ProvenanceFrame` to every synthetic `Term` node, nor expose a
chain-reconstruction query — `Kappa.Core.Term` carries no origin field.
Evidence: `Kappa.Check` `EBang` (`desugared-from` related origin);
`tests/conformance/diagnostics`.

## 16. §3.1.10/§3.1.11: cascade-suppression summaries are only populated where a surviving root diagnostic exists

The `suppressed` field (§3.1.1, §3.1.10, §3.1.11) is implemented and is
populated wherever this implementation drops a downstream diagnostic that
a *surviving* root diagnostic explains: the §3.1.14 parse-error →
`E_SIGNATURE_UNSATISFIED` suppression in `Kappa.Pipeline`
(`attachSuppressed`) records the dropped signature/elaboration diagnostics
as `Suppressed` summaries on the owning parse-error diagnostic, and the
implicit-goal cascade collapse in `Kappa.Check` (`emitUnsolvedGoal`)
records the dropped same-span mismatch on the surviving unsolved-goal
diagnostic. Where suppression happens *before any diagnostic is created*
— e.g. an operator-overload goal that is never raised as a pending goal
because the operand mismatch short-circuits resolution — there is, by
construction, no suppressed diagnostic record to summarize. §3.1.11's
"SHOULD emit one primary diagnostic and place the explained downstream
diagnostics in `suppressed`" is satisfied for the record-level cascades;
the upstream-collapse cases produce a single diagnostic with nothing to
summarize. Evidence: `Kappa.Pipeline.attachSuppressed`,
`tests/conformance/diagnostics/suppressed-cascade.kp`.

## 17. §28.2.2: algebraic numeric law members are not modelled as proofs

§28.2.2 declares `AdditiveMonoid`, `AdditiveGroup`, `MultiplicativeMonoid`,
`Semiring`, `Ring`, `EuclideanSemiring`, `FieldLike`, `OrderedAdditive`,
and `OrderedSemiring` with *proof-producing law members* (associativity,
left/right identities, distributivity, additive inverses, the
divide/modulo identity, and the field/monotonicity laws). The spec note
itself observes that "whether their values have runtime representation is
determined by the general `RuntimeErased` and ambient-demand rules", i.e.
they are erased proofs.

This implementation has no equational-rewriting proof engine: for neutral
terms `add (add x y) z` and `add x (add y z)` are *not* definitionally
equal (the `add` for `Nat`/`Integer` only reduces on closed literals), so
no closed `refl`-style proof discharges the obligations, and there is no
`unsafeAssertProof`-backed default the elaborator can synthesise per type.
The traits are therefore surfaced as **marker traits carrying exactly the
§28.2.2 supertrait graph** (`(Eq a, Zero a, Add a) => AdditiveMonoid a`,
`(Semiring a, AdditiveGroup a, CheckedSub a) => Ring a`, etc.) with the
law members omitted. The checkable, observable content — which operation
traits a type provides and the coherent supertrait premises — is
preserved exactly, so:

* every §28.2.3 mandated instance is present (`Semiring Nat`, the
  `Ring`/`AdditiveGroup` tower for `Integer`/`Int`, `FieldLike Rational`);
* every §28.2.2 "MUST NOT" exclusion holds, because the forbidden
  instances are simply never declared (`Ring Nat`, `Semiring`/`Ring`/
  `FieldLike` for `Float`/`Double` all fail implicit resolution).

The unmodelled part is solely the ability to *project a law member and use
its equation in a later proof*. Evidence:
`tests/conformance/prelude/algebraic_numeric.kp`,
`tests/conformance/prelude/algebraic_numeric_exclusions.kp`,
`Kappa.Prelude` (the algebraic-trait block).

## 18. §28.2: `Iterator.next`, the h-level proof traits, and `WellFoundedRelation.wf` reference content this implementation cannot express

* `Iterator` (§28.2) declares `next : (1 this : it) -> Option (item :
  Item, rest : it)`, referencing the associated member `Item` inside a
  sibling member signature *in an applied type position*. This
  implementation resolves an associated-type member only through an
  explicit `this.Member` projection in a sibling record/value context, not
  as a bare name inside an applied/nested type, so `Iterator` is surfaced
  with its associated `Item : Type` member only and the `next` step is not
  exposed. The trait name resolves.
* `IsContr`/`IsSubsingleton`/`IsProp`/`IsSet`/`IsGroupoid` (§28.2, §11.4)
  have proof-producing members (`center`/`contract`, `allEqual`,
  `pathIsProp`, `pathIsSet`) over propositional equality that, as in
  issue 17, cannot be synthesised for neutral terms. They are surfaced as
  nameable markers preserving the `IsSubsingleton => IsProp` edge.
  `IsEmpty` keeps its `absurdT : t -> Void` eliminator.
* `WellFoundedRelation` (§28.2/§15.11) is surfaced with its `rel` member
  but not the `wf : WellFounded a rel` accessibility witness, which is an
  erased proof with no closed inhabitant this implementation can build.
* `IntoQuery` (§18.6/§20.2/§23.7) declares the associated members
  `Mode`/`ItemQuantity`/`Item`/`SourceDemand` and `toQuery`'s result
  `QueryCore Mode ItemQuantity Item` references them. As above, this
  implementation cannot reference an associated type in an applied
  position, so `IntoQuery` is surfaced with a single associated
  `IntoItem : Type` and `toQuery : src -> Query IntoItem`, with the
  §23.7 instances for `List`/`Array`/`Set`/`Option`/`NumericRange`.
  `toQuery` resolves, but because the result type mentions the associated
  `IntoItem`, a use site must determine the item type independently (the
  `_.IntoItem` projection is not reduced from the instance during
  unification). The actual `for`/comprehension generator iteration does
  **not** rely on `toQuery`: it lowers each source directly to its
  element list under the §20.10.11 as-if model (`Kappa.Check`,
  `sourceInfo`/`wrapSrc` and the `DoFor` handler), so `for x in 1..n` and
  `[for x in 1..n, yield x]` iterate correctly for the §28.2.3 Rangeable
  element types. Evidence: `tests/conformance/queries/`
  `range_iteration_run.kp`.

In every case the *name* is a resolvable prelude export, satisfying the
§28.2 declaration MUSTs; only the proof-carrying members are omitted.
Evidence: `Kappa.Prelude` (trait declarations near `Iterator`).

## 19. §28.2: `sym`/`trans`/`cong`/`subst`/`pathInd` resolve but are usable only with determined endpoints

The §28.2 proof/equality helpers `absurd`, `subst`, `sym`, `trans`,
`cong`, `pathInd`, `unsafeAssertProof`, and `witness` are all declared as
prelude terms with their spec signatures and resolve by name. Their
*bodies*, however, cannot be written by `match eq case refl -> ...`,
because this implementation does not refine an equality's index `y := x`
when matching `refl` — a direct consequence of the unpropagated `(=)`
parameter/index split documented in issue 2. They are therefore realized
through erased-proof primitives (`__transport`, identity on the runtime
payload since the witness is erased; `__eqProof`, an inhabitant of the
erased equality goal; `__absurd`).

A second, more general consequence of issue 2 surfaces at *use* sites: a
call like `sym eq` for `eq : x = y` cannot determine the helper's `@0 x`
and `@0 y` implicits by unification, because the equality index is not
propagated. The undetermined erased implicits then fall to scope search,
which finds the two same-typed `@0` binders and reports
`E_IMPLICIT_AMBIGUOUS` (§16.3.3) — note this is *general* behaviour for
any function with two unconstrained same-typed `@0` binders, not specific
to the proof helpers. Likewise `subst`/`pathInd` require an explicit
motive annotation because the motive `p` is not inferable from the
payload alone. Consequently these helpers are usable only when the
equality endpoints (and motive, for transport) are concretely determined;
the names and signatures are nonetheless present per §28.2. Evidence:
`Kappa.Prelude` (proof-helper block), `tests/conformance/prelude/`
`proof_helpers_resolve.kp`.
