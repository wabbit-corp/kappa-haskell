# Known spec issues

Genuine ambiguities, contradictions, and implementation burdens found in
`docs/Spec.md` while building this implementation and its test suites.
Citations are to spec sections; "evidence" points at code or fixtures in
this repository where the issue had to be confronted.

## 1. §5.5.1: longest-match-first makes `[1]>x` lex as `]>`

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

## 2. §6.3.5 / §7.1.1 / §9: the soft keyword `type` needs unbounded lookahead

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
(`Kappa.Parser`). RESOLVED for the handler form (2026-06): the parser
already lexes adjacent `type"…"` as a prefixed string, and the
implementation now provides the conventional built-in `type"…"`
type-producing handler (it parses the literal content as a type
expression and elaborates it; `macros/type-prefix-handler.kp`,
SPEC_COVERAGE.md §6.3.5). The remaining lookahead observation about the
three roles of `type` stands as a spec-ergonomics note, but no
normative form is unsupported on its account.

## 3. §16.1.3 vs §16.4.2: short-circuit operators are "ordinary terms", yet flow typing must see through them

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

## 4. §28.2.1 + §16.4.4: checked subtraction makes ordinary `x - y` unwritable without flow facts

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

Precise mechanism (investigated 2026-06; relevant to the two native
package ports in `examples/packages/`): even an *explicitly* guarded
`if y <= x then x - y else 0` is rejected today, not just bare `x - y`.
`Check.propProof`/`factReduce` discharge an equality goal only by
reducing the goal term against the *condition terms* recorded in
`csBoolFacts` on entering an `if`/`match` branch. For `Nat`, the guard
`y <= x` lowers through `Ord`/`compare`
(`if ltInt (natToInt y) (natToInt x) then LT elif eqInt … then EQ else
GT`), the guard `i == 0` lowers to `eqInt (natToInt i) 0`, while the
proof goal `subDefined x y` lowers to `leInt (natToInt y) (natToInt x) =
True`. All three sit over the same `natToInt`+Int-primitive substrate,
but they are structurally distinct terms, so the syntactic
`factReduce` cannot connect a `<=`/`==` branch fact to the `leInt`-shaped
goal. A conforming fix is a §16.4.4 flow-typing **arithmetic bridge**: a
sound decision step over Int-primitive facts (`eqInt`/`ltInt`/`leInt` on
`natToInt _`) that closes the goal, including the non-negativity lemma
`natToInt n ≥ 0` for the `eqInt (natToInt i) 0 = False ⟹
leInt 1 (natToInt i) = True` step. This is a real multi-step elaborator
feature with regression surface on the implicit solver, not a
convertibility tweak. Total saturating
`natOfInt (subInt (natToInt a) (natToInt b))` compiles today but changes
checked-subtraction semantics.

## 5. §3.1.2 / §3.1.4: diagnostic code names are implementation-defined, so black-box suites do not transfer

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

## 6. §31.3: variant member identity by "canonical rendering" is not pinned enough for interop

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

## 7. §6.1.3 / §28.2: two float equalities with the surprising one on `(==)`

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

## 8. §5.2 vs juxtaposition application: soft keywords after an expression are inherently ambiguous

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

## 9. §21.6 vs §21.2: the convenience reflection queries are `Elab`-typed, but corpus programs use them as plain values

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

## 10. §5.4: multi-line operator continuations at constant deeper indentation are undefined

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

## 11. §3.1.5A / §30.2.3: KCore-node provenance frames vs diagnostic-facing provenance

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

## 12. §3.1.10/§3.1.11: cascade-suppression summaries are only populated where a surviving root diagnostic exists

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

## 13. §28.2.2: algebraic numeric law members are not modelled as proofs

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

## 14. §28.2: `Iterator.next` and h-level proof trait reference content this implementation cannot express

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
  issue 15, cannot be synthesised for neutral terms. They are surfaced as
  nameable markers preserving the `IsSubsingleton => IsProp` edge.
  `IsEmpty` keeps its `absurdT : t -> Void` eliminator.
* `WellFoundedRelation` (§28.2/§15.11) exposes the associated `rel` member.
  The implementation does not expose or inspect a real accessibility witness
  for arbitrary user relations, so the termination checker does not treat a
  `WellFoundedRelation` dictionary as proof that a `by` relation is safe.
  Well-foundedness is currently accepted only for compiler-recognized
  primitive orders such as the non-negative `ltInt` subset rule; the associated
  side conditions may use normalized helpers and nonlinear polynomial
  arithmetic. Evidence:
  `tests/conformance/prelude/wf-relation-combinators.kp`,
  `tests/conformance/recursion/decreases-nonlinear-int.kp`,
  `tests/conformance/recursion/decreases-measure-normalizes-helpers.kp`.
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

## 15. §28.2: proof-helper bodies still use erased primitives instead of equality matching

The §28.2 proof/equality helpers `absurd`, `subst`, `sym`, `trans`,
`cong`, `pathInd`, `unsafeAssertProof`, and `witness` are all declared as
prelude terms with their spec signatures and resolve by name. Their
*bodies*, however, cannot be written by `match eq case refl -> ...`,
because this implementation does not yet propagate the branch-local
family-argument equality forced by the `refl` result type. They are
therefore realized through erased-proof primitives (`__transport`,
identity on the runtime payload since the witness is erased; `__eqProof`,
an inhabitant of the erased equality goal; `__absurd`).

Endpoint inference for ordinary uses of `sym`/`trans`/`cong` works by
unifying the explicit equality proof argument with the helper's equality
family domain (`tests/conformance/prelude/proof_helpers_use.kp`). The
remaining limitation is equality-pattern refinement itself, plus the
ordinary need to make motives explicit for `subst`/`pathInd` when they
cannot be inferred from surrounding type information. Evidence:
`Kappa.Prelude` (proof-helper block), `tests/conformance/prelude/`
`proof_helpers_resolve.kp`, `tests/conformance/prelude/proof_helpers_use.kp`.

## 16. §4: unsafe/debug facilities are recognized, build-gated, and audited, but `unhide`/`clarify` carry no deeper semantic effect

The §4 unsafe/debug facilities are now recognized and gated by the §4.2
build configuration (`UnsafeConfig` in `Kappa.Check`, all `allow_*`
settings default to `false` for package mode). The §4.4 escapes
`assertTerminates`/`assertReducible`/`assertTotal` parse as a decl prefix
(`DUnsafeAssert`), the §4.5 `unsafeAssertProof` reference is gated at name
resolution, and the §8.3.1.1 `unhide`/`clarify` import modifiers are gated
during import resolution. Each disabled use is a compile-time error
(`E_FEATURE_INACTIVE` / `kappa.feature.gated`) naming both the offending
form and the disabling setting (§4.2). Each *permitted* use is recorded in
the §4.7 audit ledger (`csAuditLedger`), exposed as machine-readable JSON
by `kappa audit PATH` and asserted in tests via `assertAuditLedger`. The
test harness enables a facility per suite with the matching `allow_*`
directive.

Two scope limitations remain, neither weakening the gating MUST:

* **`unhide`/`clarify` semantics (§4.3) are gating + audit only.** The
  modifiers are recognized, gated, and audited, but `unhide` does not yet
  grant access to a `private` imported name and `clarify` does not change
  definitional-equality transparency of an `opaque` item. This
  implementation has no separate-compilation artifacts (§31.x is
  interpreter-scoped), so the §4.3 "compiler does not have access to the
  requested private/opaque content" condition is moot; the modifiers are
  therefore exercised on ordinary public names. Full visibility-escape
  semantics are out of scope for the interpreter.

* **Assertion effect is deliberately narrow.** `assertTerminates` is gating +
  audit only. Gated `assertReducible` records a conversion-reducibility
  override for the whole asserted recursive SCC, but it never changes runtime
  semantics (§4.4), and the wrapped definition is elaborated normally so no
  spurious §9.1 cascade piles onto the gate error. The §4.7 ledger records
  the core fields §4.7 enumerates
  (facility, module, origin, affected declaration, permitting build
  setting, reason); the hash/ABI/coherence-identity fields are
  separate-compilation-scoped and not modelled. Evidence:
  `Kappa.Check` (`elabUnsafeAssert`, `gateUnsafe`, `recordAudit`,
  `gateUnsafeAssertProof`), `Kappa.Pipeline` (`gateImportModifiers`),
  `tests/conformance/unsafe_debug/`,
  `tests/conformance/unsafe-debug-unhide-{gated,enabled}/`.
