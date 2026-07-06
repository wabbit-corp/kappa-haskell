# Known spec issues

Genuine defects found in `docs/Spec.md`: ambiguities, contradictions,
unsoundness, incompleteness, omissions, and implementation burdens.
Citations are to spec sections and `Spec.md` line numbers. Each item ends
with a **Possible fix** — the minimal spec edit that would resolve it.

The file has two parts:

* **Part I (items 1-15)** — issues found organically while building this
  implementation and its test suites; "evidence" points at code or fixtures
  in this repository where the issue had to be confronted.
* **Part II (items 16-92)** — a systematic spec-internal review
  (2026-07-06): twelve section-range reviews over the whole 47k-line spec,
  each finding then adversarially re-verified against the full spec text
  (the verifier's job was to refute by finding the resolving text
  elsewhere). Items marked **confirmed** survived that check outright;
  items marked **weakened** survived with a caveat — the quoted defect is
  real but narrower than first claimed (the verifier's note says why).
  Within each severity band, items are ordered by spec section.

Severity legend: **high** = unsoundness or a contradiction affecting real
programs; **medium** = divergent-implementations ambiguity or missing
normative machinery; **low** = footgun, wording defect, or minor gap.

# Part I — found during implementation

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

**Possible fix:** Amend §5.5.1 to require a targeted diagnostic when `]>` is lexed with no matching `<[` open (suggesting `] >`), or restrict the `]>` single-token rule to positions where an effect-row bracket is syntactically live; document the whitespace workaround normatively.

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
SPEC_COMPLIANCE.md §6.3.5). The remaining lookahead observation about the
three roles of `type` stands as a spec-ergonomics note, but no
normative form is unsupported on its account.

**Possible fix:** Add a normative disambiguation note (§5.2/§9): at `type`, adjacency to a quote selects the prefixed-string handler (§6.3.4); identifier followed by `=`/`:` in declaration position selects the declaration; otherwise the kind-qualifier reading. State that one token of lookahead plus the adjacency flag suffices, so implementations need not fear unbounded scan.

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
SPEC_COMPLIANCE.md §16.4.)

**Possible fix:** State in §16.4.2 that refinement is keyed on the resolved prelude identities of `(&&)`/`(||)`/`not`, and that a local rebinding (any type) simply does not participate in refinement — no error, refinement silently off for that condition. One sentence closes the divergence.

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

**Possible fix:** Either normatively require the §16.4.4 arithmetic bridge (closure over `eqInt`/`ltInt`/`leInt` facts on `natToInt _`, including the `natToInt n >= 0` lemma) in any profile that mandates checked `(-)` on Nat, or add a total prelude alternative (`subSat`/`subChecked : Nat -> Nat -> Option Nat`) plus an explicit spec note that symbolic `x - y` requires flow facts or a manual proof.

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

**Possible fix:** Expand the §3.1.4 portable-alias registry to cover every diagnostic code asserted anywhere in Appendix T fixtures, and add a T-side rule that portable fixtures MUST assert only registered aliases or §3.2 families, never raw implementation codes.

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

**Possible fix:** Normatively pin the canonical rendering as a small grammar (token spelling, single-space separation, parenthesization rule, fully-qualified names, nested-union member ordering) with byte-stable output — or replace rendering-keyed identity with a structural hash defined over the elaborated type tree (§33-style), making the byte format irrelevant.

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

**Possible fix:** Keep bit-equality (it makes `Eq` lawful) but add a normative advisory and a recommended lint (e.g. `W_FLOAT_BIT_EQUALITY`) for `(==)`/literal patterns on `Double` outside hashing/canonicalization contexts, cross-referencing `floatEq`.

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
enumerated in SPEC_COMPLIANCE.md §5.2. Evidence:
`tests/conformance/lexer/soft-keyword-identifiers.kp`, and
`Kappa.Parser` (`stopKeywords` vs `queryStopKeywords` /
`isStopKeywordAt`).

**Possible fix:** Specify the tie-break normatively: inside a construct's body, that construct's clause keywords terminate an argument run (clause reading wins); everywhere else the identifier reading wins; using a clause keyword as an argument there requires parentheses. Enumerate each construct's stop-keyword set (the implementation's `stopKeywords`/`queryStopKeywords` split is a working model).

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

**Possible fix:** Adopt the reconciliation into §21.6 normatively: an *applied* standardized convenience query at a site whose expected type is not `Elab`-headed is run at elaboration time and residualizes its first-order result; enumerate the queries this applies to (`defEqSyntax`, `headSymbolSyntax`); everywhere else the `Elab` signature stands. (Alternatively: fix the external corpus fixtures and keep §21.2 strict.)

## 10. §3.1.5A / §30.2.3: KCore-node provenance frames vs diagnostic-facing provenance

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
the CORE remediation set (see `SPEC_COMPLIANCE.md` profile-scoped
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

**Possible fix:** Explicitly tier the requirement: the full `ProvenanceFrame` store and chain-reconstruction queries belong to the §37.3 tooling tiers / §34 conformance-verification mode; CORE requires only primary-span preservation through desugaring plus a `desugared-from`/`generated-site` related origin on diagnostics. Say so in both §3.1.5A and §30.2.3.

## 11. §3.1.10/§3.1.11: cascade-suppression summaries are only populated where a surviving root diagnostic exists

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

**Possible fix:** Reword §3.1.11 to scope the SHOULD to diagnostics that were *created and then suppressed*; add a sentence acknowledging that upstream short-circuiting which prevents a downstream diagnostic from ever being created legitimately yields a single primary diagnostic with an empty `suppressed` list.

## 12. §28.2.2: algebraic numeric law members are not modelled as proofs

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

**Possible fix:** Declare the §28.2.2 law members *optional/defaulted* members: implementations without an equational proof engine may omit them while keeping the operation members and supertrait graph mandatory (the observable content); or gate the law members behind a `proof-laws` feature gate so their absence is a conformance-visible profile fact rather than a silent deviation.

## 13. §28.2: `Iterator.next` and h-level proof trait reference content this implementation cannot express

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

**Possible fix:** Either add the missing normative rules for referencing an associated member in applied type positions inside sibling member signatures (name resolution + reduction during unification), or restate the affected §28.2/§23.7 signatures (`Iterator.next`, `IntoQuery.toQuery`) in an explicit-projection form that is expressible without that feature — and pin whichever is chosen so implementations agree on the surfaced signatures.

## 14. §28.2: proof-helper bodies still use erased primitives instead of equality matching

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

**Possible fix:** Specify equality-pattern refinement — matching `refl` refines the family argument within the branch — as a required elaboration feature with its typing rules, or normatively bless primitive-backed helper bodies (`__transport`/`__eqProof`/`__absurd` realizations) as a conforming implementation strategy for the §28.2 helpers.

## 15. §4: unsafe/debug facilities are recognized, build-gated, and audited, but `unhide`/`clarify` carry no deeper semantic effect

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

**Possible fix:** Define §4.3 semantics for whole-program implementations explicitly: gated `unhide` grants name access at check time and `clarify` grants definitional transparency, with the "compiler lacks access to the content" carve-out applying only to separate compilation; gating + audit remain mandatory in all cases.

# Part II — systematic spec-internal review (2026-07-06)

## A. High severity — unsoundness, contradictions, and core incompleteness

## 16. §10.1.3, §10.2 vs §11.1: No universe size check for data constructor arguments — `data U : Type0 = MkU (t : Type0)` is admitted, enabling Russell-style inconsistency

**unsoundness** · severity **high** · verification: **confirmed** · Spec.md
lines 8707-8708, 8736-8737, 8985-9033

§10.1.3 says a data declaration's result classifier is `Type` "subject to the
ordinary universe rules", but the ordinary universe rules (§11.1) contain only
`Type u : Type (u+1)` and cumulativity; no rule anywhere requires a
constructor's argument types to inhabit a universe no larger than the declared
result universe (grep for constructor/universe size rules comes up empty).
Consequently `data U : Type0 = MkU (t : Type0)` — a GADT constructor `MkU :
Type0 -> U` where `Type0 : Type1` — violates no stated rule. Matching (§10.1.3
branch equalities) gives a projection `U -> Type0`, so `Type0` embeds into an
inhabitant of `Type0`, the standard self-containment that the stratified
hierarchy exists to forbid and that yields logical inconsistency
(Russell/Hurkens construction). Every mainstream checker (Coq, Agda, Lean)
rejects this with a universe-inconsistency error; the spec as written admits
it.

> lines 8707-8708: "the type constructor `F` has an elaborated telescope
corresponding to `Δ` and result classifier `Type`, subject to the ordinary
universe rules."; lines 8736-8737: "GADT-style constructors are written with
an explicit result type after `:`. The explicit result type may instantiate or
constrain any uniform data-family argument"

**Possible fix:** Add to §10.4 (or §10.1.3) the size rule: for `data F Δ :
Type u`, every explicit and implicit constructor binder type, and every
family-argument instantiation in a GADT result type, must be checkable at some
`Type v` with `v ≤ u`; declarations violating this are rejected with a
universe-inconsistency diagnostic. (If erased large arguments à la Coq's
`Prop`-style rules are intended for `@0` binders, state that exception
explicitly.)

## 17. §11.1, §11.1.2, §11.3 (vs. nothing anywhere): No Pi-type universe formation rule; quantification over `Universe : Type0` has no consistent level assignment (Type-in-Type/Hurkens risk)

**incompleteness** · severity **high** · verification: **confirmed** · Spec.md
lines 8992-8999, 9038, 9019, 9686-9694

The spec's entire universe discipline is `Type u : Type (u+1)` plus
cumulativity; the rule assigning a universe to a dependent function type `(x :
A) -> B` is never stated anywhere (grep for max/imax/level-of-Pi/limit-
universe over all 47070 lines comes up empty; §11.1.2 only says constraints
are generated 'from typing' without giving the typing rules that generate
them; §30.2 KCore defers back to these sections). Worse, `Universe : Type0` is
an ordinary intrinsic type and §11.3 explicitly endorses `forall (u :
Universe). ... Type u ...` (example at line 9694), whose codomain lives at
level `u+1` for a bound `u` — no finite level exists, and there is no limit
universe or bounding rule. Two conforming implementations diverge
catastrophically: one rejects the spec's own §11.3 example as untypeable;
another assigns the Pi a fixed level (e.g. Type0, since `Universe : Type0`),
which is impredicative quantification over all universes and admits a
Girard/Hurkens-style proof of False. The single most basic judgment of the
type-theory core is missing.

> line 8994: "in general, `Type u : Type (u+1)` at the meta-level."; line
8999: "Universe : Type0"; line 9694: "forall (u : Universe) (a : Type u) (b :
Type u). (a -> b) -> a -> b"; line 9038: "Elaboration generates constraints on
universe metavariables (e.g. `?u ≤ ?v`, `?u < ?v`) from typing."

**Possible fix:** Add to §11.1 a normative Pi-formation rule: if `A : Type u`
and `B : Type v` (under `x : A`) then `(x : A) -> B : Type (max u v)`; and a
rule for binders whose annotation is an intrinsic compile-time classifier
(`Universe`, `Quantity`, `Region`, rows, labels): either (a) introduce a top
classifier `Typeω` that such Pis inhabit and that itself is not a first-class
`Type u`, or (b) require that `u` in any `Type u` occurring in the codomain be
bounded by a level constraint `u < w` where `Type w` classifies the whole Pi,
and state that unbounded `forall (u : Universe)` types are accepted only as
declaration schemes, never as first-class inhabitants of any `Type v`.

## 18. §13.1.1 vs §33.1.2/§31.3/§8.5.2: Variant MemberId/TagId for opaque-alias member types: stability MUST and opacity MUST cannot both hold

**contradiction** · severity **high** · verification: **confirmed** · Spec.md
lines 12243-12251, 35923-35925, 35144-35145, 7335-7336

MemberId(T) is defined by 'the same canonical defining-module view used for
Hard Hashes (§33.1.2)' and is required to be 'stable across separately
compiled modules and artifacts'; TagId (runtime dispatch) is derived from
MemberId and must also be stable across modules. But §33.1.2's normalization
respects opacity per reached definition: 'inside the defining module, local
definitions are available normally; when normalization reaches a definition
imported from another module, it uses the transparency recorded in that
imported definition's canonical artifact.' For `opaque type Id a = a`
(§8.5.2), a union member type `Id Int` therefore normalizes to `Int` when the
union occurs in Id's defining module D (Id is local, unfolds) but stays un-
unfolded in an importer M (Id is imported opaque). So either (a) MemberId is
computed at each occurrence site — then D's injection into `(| Id Int | String
|)` stores TagId(Int) while M's exhaustive `match ... case (| x : Id Int |)`
dispatches on a different tag, and a closed-union match falls through every
arm at runtime (type-safety hole), directly violating the stability MUSTs; or
(b) MemberId always uses the alias-defining module's transparent view — then
in M, `ContainsVar (| Id Int |) Int` is solvable, so an importer can inject a
raw `Int` and match it out as `Id Int` (and vice versa) without `clarify`,
coercing across the §8.5.2 opacity boundary that δ-reduction is explicitly
forbidden to cross. The spec asserts both stability and opacity-respect and
never says which environment governs MemberId normalization, so no conforming
implementation can satisfy both.

> 12243-12245: "`MemberId(T)` is computed from the fully elaborated member
type using the same canonical defining-module view used for Hard Hashes
(§33.1.2): it ignores downstream `clarify`, and it is stable across separately
compiled modules and artifacts." — 35923-35925: "respect for `opaque` and
`private opaque` as defined from the perspective of the defining module:
inside the defining module, local definitions are available normally (§8.5.2);
when normalization reaches a definition imported from another module, it uses
the transparency recorded in that imported definition's canonical artifa …

**Possible fix:** Add to §13.1.1: 'For the purpose of MemberId, normalization
treats every definition according to its export-facing transparency as
recorded in its defining module's canonical artifact; in particular, an
`opaque` term or type alias is never unfolded when computing MemberId, even
for occurrences inside its own defining module.' This makes MemberId identical
at every occurrence site (stability holds) and keeps `Id Int` and `Int`
distinct variant members (opacity holds). Add a corresponding note to §33.1.2
that MemberId/TagId computation uses this export-facing view rather than the
defining-module-local view.

## 19. §16.1.7.1 + §16.3 + §16.3.3 vs §30.2.1 and pervasive examples: Implicit resolution (§16.3.3) has no unification/metavariable step, so ordinary polymorphic application is unelaborable as specified

**incompleteness** · severity **high** · verification: **confirmed** · Spec.md
lines 16420-16423, 17077-17078, 17307-17315, 17342, 33095

§16.1.7.1 says an unsupplied implicit binder is filled by 'the implicit-
resolution procedure of §16.3.3', §16.3 says omitting an implicit argument 'is
equivalent to passing an ordinary in-scope term chosen by §16.3.3', and
§30.2.1 says implicit insertion 'is completed before KCore is formed'. But
§16.3.3's four steps (local implicit context, trait evidence, boolean-prop
normalization, eqSound) contain no rule that introduces a fresh inference
metavariable to be solved by unification. Since `forall a. T == (@0 a : Type)
-> T` (line 9682), every ordinary polymorphic call such as `id 5` or the
spec's own `users |> map (.name)` (line 15919) hits an implicit goal `Type`:
step 1 finds no candidate (or worse, deterministically selects an arbitrary
in-scope type binder — e.g. inside `let g (@0 b : Type) (x : Int) : Int = id
x`, step 1 picks `b`, then `x : Int` fails against `b`; with two type binders
in scope the goal is declared ambiguous and rejected), step 2 fails (`IsTrait
Type` unavailable), steps 3-4 don't apply, and per line 17342 'compilation
fails with an error indicating the unsolved implicit goal G'. The same gap
exists for implicit Quantity/Region/row/label binders. Relatedly, the
§16.1.7.1 spine loop has no stopping condition for implicit binders (unlike
the explicit-binder partial-application stop), so a bare reference to an
implicit-headed function is always fully instantiated, with no rule
suppressing insertion when checking against an implicit-headed expected type
(e.g. `let m : forall a b. (a -> b) -> List a -> List b = map`) and no term-
level generalization rule to recover. Grep for 'fresh metavariable'/'solved by
unification' finds no call-site rule (only universe-inference §11.1.2).

> 16423: "otherwise synthesize the argument by the implicit-resolution
procedure of §16.3.3;" — 17077-17078: "After elaboration, omitting an implicit
argument is equivalent to passing an ordinary in-scope term chosen by
§16.3.3." — 17342: "If all steps fail, compilation fails with an error
indicating the unsolved implicit goal `G`."

**Possible fix:** Add a step 0 to §16.3.3: 'If the demanded implicit binder
type G is a compile-time classifier (Type u, Universe, Quantity, Region,
RecRow, VarRow, EffRow, Label, EffLabel) or G contains unsolved metavariables
and IsTrait G is not established, the compiler synthesizes a fresh inference
metavariable of type G, solved by ordinary unification against the remaining
spine and the expected type; steps 1-4 apply only to goals not discharged this
way (trait evidence and propositional goals), or to such a metavariable that
remains unsolved at the end of the checking unit.' Additionally state in
§16.1.7.1 that implicit-binder synthesis is suppressed when the site's
expected type is itself headed by a definitionally equal implicit binder.

## 20. §17.1 (matchCase grammar) + §17.1.9 + §17.2.1 vs §17.3.3: Guards on consuming `Match a r` active-pattern cases: Hit-side guard failure has no defined continuation and loses linear ownership

**unsoundness** · severity **high** · verification: **confirmed** · Spec.md
lines 17910, 18140, 18305-18312, 18491-18528

The match grammar `matchCase ::= 'case' pattern ['if' expr] '->' expr` (17910)
permits a guard on any case, and active-pattern applications are patterns
(§17.2.1). §17.3.3's threading rule only defines what happens on `Miss`
('elaboration threads the Miss residue into the subsequent case') and its
conceptual elaboration has no guard slot. For `match buffer case ConsumeToken
Header (data) if g -> e1 case _ -> e2` with `(1 buffer : Buffer)`:
`ConsumeToken Header buffer` consumes the linear buffer; if it yields `Hit
data` but `g` is False, §17.1.9 requires fallthrough to the next case ('Guard
failure does not by itself exclude pat'), yet the next case expects the Miss
residue, which does not exist on the Hit path, and the original scrutinee is
already consumed. Naively extending the conceptual elaboration yields an inner
match `case Match.Hit data if g -> e1 case Match.Miss __buf_1 -> ...` whose
Hit/guard-false remainder is uncovered — and because guard coverage is itself
undefined (see separate finding), a conforming implementation may accept the
program and control falls off the match at runtime, with the owned `Hit`
payload (and the linear buffer's ownership) lost. The same hole exists for
guards on grouped consuming total-view cases in §17.3.5, whose exhaustiveness
requirement inherits the undefined guard-coverage semantics.

> 18493-18494: "elaboration threads the `Miss` residue into the subsequent
case." — 17910: "matchCase ::= 'case' pattern ['if' expr] '->' expr" — 18140:
"Guard failure does not by itself exclude `pat` from subsequent cases."

**Possible fix:** Add to §17.3.3: 'A case whose pattern is a `Match`-returning
active-pattern application, or whose head active pattern consumes the
scrutinee at quantity 1, MUST NOT carry an `if` guard; such a guard is a
compile-time error. Guard-like filtering must instead be expressed inside the
pattern's payload subpattern via a subsequent non-consuming match.' Add the
analogous restriction (or a defined residue-preserving semantics) for guards
on grouped consuming total-view cases in §17.3.5.

## 21. §18.2.1/§18.8.7 vs §18.2 (`using`), §18.7, §18.8.3, §18.1.25.1: Plain `let?` failure (`empty`) bypasses do-scope exit actions, leaking `using` resources and skipping `defer`

**unsoundness** · severity **high** · verification: **confirmed** · Spec.md
lines 20313-20315, 22026-22035, 21890-21892, 20249-20251, 21923-21925

The plain form `let? pat = expr` short-circuits via `Alternative.empty`
(elaboration: `case _ -> empty`, §18.8.7). But the do-scope unwinder of
§18.8.3 fires only on (a) a Completion record or (b) a propagated monadic
error caught via `MonadError`; when `MonadError m` is not in scope the spec
says `finally` "simply sequences the finalizer after the main action using
ordinary monadic composition", and MonadFinally law 3 (§18.1.25.1) covers only
normal completion, completion-carrying abrupt control, and "monadic errors
when MonadError m is present". `empty` is none of these. Failure scenario: in
a carrier with `Alternative m` + `Releasable m A` + `MonadFinally m` but no
`MonadError m` (a parser or Option-like monad), `do { using h <- acquireFile;
let? Some x = None; use x h }` — on match failure `empty` short-circuits
`>>=`, the `Release[A] rel __res` exit action never runs, and the hidden
quantity-`1` resource is dropped without release. This directly contradicts
§18.2's "guaranteeing its release on exit" and §18.8.3's linearity note that
"all hidden owned-resource release obligations are consumed even when the
scope exits by error". No quantity rule guards the path either: §18.2.1 checks
only droppability of the refutation residue, and §12.2 line 11318 guards only
"source-level abrupt completion", which `empty` is not. Even with `MonadError`
in scope, nothing specifies that `empty` is a catchable monadic error, so
implementations diverge on whether exit actions run.

> line 21890-21892: "The detailed error-propagation algorithm below applies
only when an implicit `MonadError m` is in scope. When `MonadError m` is not
in scope, `finally` simply sequences the finalizer after the main action using
ordinary monadic composition over the completion-carrying result." — vs line
21923-21925: "all quantity-`1` deferred obligations and all hidden owned-
resource release obligations are consumed even when the scope exits by error."
— vs line 20249-20250: "safely binding it for the duration of the `do` block
while guaranteeing its release on exit."

**Possible fix:** Add to §18.2.1: "The plain `let?` form is additionally ill-
formed when any enclosing do-scope frame within the current function body
holds a pending `Release` exit action, or when the enclosing carrier does not
provide `MonadError m` evidence whose error channel is specified to subsume
`empty`; alternatively, an `Alternative m` used for plain `let?` MUST satisfy
the law `finally empty final ≡ final >>= \_ -> empty`, and the §18.8.3
unwinder MUST treat `empty`-failure of the scope body as a propagated failure
that runs exit actions." Pick one of the two mechanisms and state it
normatively.

## 22. §18.5 vs §18.8.9 (and §30.2.2.6): Completion-carrying `do` blocks may escape as first-class values (e.g. `fork (do return ())`), falsifying the guaranteed-target rule

**unsoundness** · severity **high** · verification: **confirmed** · Spec.md
lines 20907-20916, 20929-20931, 22128-22134, 33459-33460

§18.5 blocks bare `return` only at user-written lambda/local-function
boundaries, and explicitly makes `do` blocks "transparent to `return`". A `do`
block is an ordinary expression (§18.2 "the block's type is some `m T`"), so
it can appear as a first-class computation value in argument position. Failure
scenario: inside `let f : IO e Int = do { let fib <- fork (do return 5); ...
}` the inner `do return 5` lies inside the body of named function `f` with no
intervening lambda, so bare `return` resolves to `f` and is accepted by every
stated rule. Its elaboration is `IO e' (Completion(RetCtx, ...))` containing
`Return[f] 5`, but the computation runs on a child fiber where no construct
consumes `Return[f]` — §18.8.9's normative claim that "every well-typed
`Return[L] r` completion has a matching enclosing target on every dynamic
execution path" is false, and the internal `Completion` family (which §18.8.2
says "is not a surface syntax form") leaks into the fiber's `Exit` type via
unification with `fork`'s type variable `a`. The same hole exists for any
expression position that captures a `do` block as a value (stored in a record,
returned, passed to `timeout`/`race`, run twice). Nothing in §18 defines the
boundary at which completion-carrying elaboration must be discharged for `do`
blocks outside do-item-suite / function-body positions.

> line 20929-20930: "`return` does not target `do` blocks ... Those constructs
are transparent to `return` and propagate the `Return` completion outward
(§18.8.5)." — line 22132-22134: "Target existence is guaranteed by §18.5's
compile-time resolution rules: every well-typed `Return[L] r` completion has a
matching enclosing target on every dynamic execution path."

**Possible fix:** Add to §18.5 (and mirror in §18.8.5): "A `do` block that
appears in ordinary expression position — i.e., not as the body of a named
function, method, or labeled lambda, and not as a do-item suite (branch suite,
loop body, loop `else`, handled expression) elaborated within an enclosing
completion-carrying region — is an abrupt-control boundary equivalent to a
user-written lambda boundary: `return`, `break`, and `continue` inside it may
target only constructs inside that block. Violations are compile-time errors."

## 23. §32.2.10: Data-race semantics for ordinary refs are undefined: torn reads / wild values are not excluded

**omission** · severity **high** · verification: **confirmed** · Spec.md lines
35523-35531

§32.2.10 explicitly contemplates racy programs (nothing in the type system
prevents two fibers from sharing an ordinary `Ref`/`var` cell) but only says
such races have 'no portable inter-fiber ordering'. It never states what a
racy read may observe. A grep of the whole spec for 'torn', 'data race',
'racy' finds no other rule. Consequently a conforming backend may implement
multi-word ref cells (fat pointers, unboxed pairs) with non-atomic
loads/stores, so a racy read can return a torn, type-invalid value — a memory-
safety violation the spec's own safety story (precise ownership, no UB)
presumably forbids. Every implementer must decide between Java-style 'reads
see some written value' and C++-style UB, and the two choices are observably
(and catastrophically) different.

> 35528-35529: "unsynchronized concurrent read/write or write/write races on
such ordinary refs have no portable inter-fiber ordering beyond the happens-
before edges above;"

**Possible fix:** Add to §32.2.10: 'A racy read of an ordinary ref observes
some value that was written to that ref by the program (or its initial value);
races MUST NOT produce torn, out-of-thin-air, or type-invalid values, and MUST
NOT compromise memory safety.' (Alternatively, classify executions containing
such races as terminating with a `Defect`, but pick one.)

## B. Medium severity — divergent-implementation ambiguities and missing normative machinery

## 24. Appendix G.2: Appendix G.2's independence condition contradicts its own example

**contradiction** · severity **medium** · verification: **confirmed** ·
Spec.md lines 46020-46021, 46027-46040

G.2's second condition says 'No binding's right-hand side refers to any name
introduced by an earlier `<-` binding in the same `do` block.' A pure `let pat
= expr` binding is one of the enumerated do-item 'binding' forms, yet the very
next example contains `let y = f x1 x2`, whose right-hand side refers to `x1`
and `x2` introduced by the earlier `<-` bindings — and the shown elaboration
`liftA2 (\x1 x2 -> let y = f x1 x2 in final_expr) e1 e2` depends on exactly
that. As written, the condition excludes essentially every useful applicative
block (pure lets and the final expression could never consume the bound
results), and the normative text and example cannot both hold. An
implementation following the letter of the condition rejects the applicative
elaboration for the spec's own example.

> L46020-21: "No binding's right-hand side refers to any name introduced by an
earlier `<-` binding in the same `do` block." vs L46032: " let y = f x1 x2"
(example immediately below, elaborated at L46038 as "liftA2 (\x1 x2 -> let y =
f x1 x2 in final_expr) e1 e2")

**Possible fix:** Reword the condition to: "No `<-` binding's right-hand side
refers to any name introduced by an earlier `<-` binding or earlier pure `let`
binding that itself depends on a `<-` binding; pure `let` bindings and the
final expression MAY refer to names introduced by earlier `<-` bindings."

## 25. §10.4 vs §10.2: Strict positivity checks only constructor argument types; recursive occurrences in GADT result-type family arguments are never checked

**incompleteness** · severity **medium** · verification: **confirmed** ·
Spec.md lines 8853-8854, 8736-8737, 8933-8944

The strict-positivity judgment (line 8853: occurrences "in every constructor's
argument types") and the final rejection judgment (line 8934: "a recursive
occurrence means an occurrence of any type constructor declared by the group
`G` in any constructor argument type") both quantify only over argument types.
§10.2 allows a GADT constructor's result type to instantiate family arguments
with arbitrary type expressions, so `data D (a : Type) : Type = C : D (D Nat
-> Nat)` places a recursive occurrence (in negative position, even) solely in
the result type and passes positivity vacuously. Coq and Agda both check
indices/result instantiations for exactly this case because such occurrences
interact with the branch-local family-argument equalities of §10.1.3 (matching
on `C` at scrutinee type `D a` yields the type equation `a = (D Nat -> Nat)`)
in ways whose consistency the spec establishes nowhere. Likewise the
parameter-positivity signature recomputation (lines 8883-8885) ignores
parameter occurrences in result types. This is normative machinery missing for
a case the grammar explicitly makes reachable.

> lines 8853-8854: "A `data` declaration is **strictly positive** iff every
occurrence of the defined type constructor in every constructor's argument
types is in a strictly positive position."; lines 8736-8737: "The explicit
result type may instantiate or constrain any uniform data-family argument of
the enclosing `data` declaration."

**Possible fix:** Extend §10.4: 'A recursive occurrence additionally means any
occurrence of a type constructor declared by group `G` inside the family-
argument instantiations of any constructor result type of `G`. Such
occurrences MUST NOT occur; the group is otherwise rejected.' (Or, if such
occurrences are intended to be allowed, define their positivity discipline and
its interaction with the §10.1.3 branch equalities.)

## 26. §12.3 vs §12.3.1: "Downward-only" region compatibility for higher-order calls is referenced but never defined; whether borrow-capturing closures can be passed to HOFs is unspecifiable

**ambiguity** · severity **medium** · verification: **confirmed** · Spec.md
lines 11757-11759, 11774-11779, 11828-11829

The skolem-escape rule makes it an escape point to pass a rho-mentioning value
"as an argument to a function whose parameter does not itself mention `rho`",
parenthetically excusing parameters "known to be downward-only with respect to
`rho`" — but 'downward-only' occurs exactly once in the whole document
(verified by grep) and is never defined. Meanwhile §12.3.1 states anonymous
rigid regions are never written in capture annotations, so no function
parameter type can ever mention an anonymous `rho`; under a literal reading a
closure capturing a bare-`&` borrowed binder can therefore be passed to no
function at all. The 'Downward-only closures' paragraph then asserts the
opposite — such closures "may be passed to higher-order functions, provided
those functions' parameters are themselves elaborated with compatible region
environments" — a judgment defined nowhere. Two conforming implementations
observably diverge on the central use-case of borrowing: e.g. with `(& x : Box
Int)` in scope, whether `map (\y -> y + get x) xs` typechecks.

> lines 11757-11759: "passing the value as an argument to a function whose
parameter does not itself mention `rho` (that is, the parameter is not known
to be downward-only with respect to `rho`)"; lines 11776-11778: "may be passed
to higher-order functions, provided those functions' parameters are themselves
elaborated with compatible region environments"; lines 11828-11829: "Anonymous
rigid regions introduced locally are never written in a capture annotation."

**Possible fix:** Define the downward-only judgment normatively in §12.3,
e.g.: 'A function parameter `p` of the callee is downward-only for a call iff
the callee's type is region-polymorphic in a variable `s : Region` with `p`'s
type carrying `captures (s)` (instantiating `s := rho` at the call site), or
the callee is a lambda/local function checked in the same scope where `rho` is
live, in which case the argument's region environment is propagated into the
callee's checking environment.' Then delete or align the 'compatible region
environments' sentence with that definition.

## 27. §14.1 vs §14.1.4/§14.3.1: Ord trait laws use (<=), whose implicit Ord premise is unsatisfiable inside the trait's own declaration

**incompleteness** · severity **medium** · verification: **confirmed** ·
Spec.md lines 13975-13983, 14003-14012, 14306-14310

The canonical prelude `Ord` declares law members `compareTransLE` and
`compareTotal` whose types use `(x <= y) = True`. But `(<=)` is not a member
of `Ord`; it is a separate top-level function declared *after* the trait with
signature `forall (a : Type). (@_ : Ord a) -> (& x : a) -> (& y : a) -> Bool`.
Elaborating the occurrences of `(<=)` inside Ord's member signatures therefore
requires solving the implicit goal `Ord a` inside Ord's own declaration body.
§14.1.4 makes only *supertrait* evidence ('supertrait evidence is available
inside the trait body') available there, and no rule anywhere adds the under-
declaration trait's own evidence to the local implicit context of §14.3.1 step
1 (grep confirms no such rule; §14.2.1 mentions 'the current trait evidence'
only for associated-member reference). As written, the spec's own normative
prelude Ord cannot be elaborated by a conforming implementation;
implementations must invent a self-evidence rule, and whether they do (and at
what point in the telescope it becomes available) changes which trait
declarations are accepted.

> 13975-13979: "compareTransLE : forall (x : a) (y : a) (z : a). (x <= y) =
True -> (y <= z) = True -> (x <= z) = True" — 14003-14006: "(<=) : forall (a :
Type). (@_ : Ord a) -> (& x : a) -> (& y : a) -> Bool" — 14307: "supertrait
evidence is available inside the trait body"

**Possible fix:** Add to §14.1.4 (or §14.2): 'While checking the member
signatures and default bodies of `trait C1, ..., Cn => Tr params`, the local
implicit context additionally contains the evidence value being declared, at
type `Tr params`; member and non-member overloaded names may resolve their `Tr
params` premises against it.' Alternatively, minimally rewrite the Ord laws to
use only the member `compare` (e.g. `compareTransLE : compare x y /= GT ->
compare y z /= GT -> compare x z /= GT`) and state that trait member
signatures may reference only sibling members and supertrait members.

## 28. §15.1 vs §31.1/§33.1.2: Recursive conversion-reducible definitions have no specified δ-unfolding discipline; 'complete δ-unfolding' for HardIdentity has no normal form

**incompleteness** · severity **medium** · verification: **confirmed** ·
Spec.md lines 15099-15108, 15117-15121, 34728-34729, 35918, 35927-35928

§15.1 grants structurally recursive definitions conversion-reducibility ('may
be unfolded by δ-reduction during definitional equality'), and §31.1 states
δ-reduction of conversion-reducible definitions unconditionally, with no guard
on when a recursive definition unfolds. Standard practice (Coq/Agda/Lean)
restricts fixpoint unfolding to constructor-headed recursive arguments
precisely because unrestricted δ on a recursive body is non-normalizing:
`length = \xs -> match xs ... 1 + length rest` reintroduces `length` under the
Cons branch on every unfold. Consequently §33.1.2's requirement of 'complete
δ-unfolding of transparent conversion-reducible definitions reachable from the
definition being normalized' is unsatisfiable for any recursive conversion-
reducible definition — the 'fully normalized form' whose canonical
serialization defines HardIdentity does not exist. The escape hatch
('memoization, fuel, or an equivalent implementation technique sufficient to
guarantee that the normalization procedure itself terminates') makes the
result depend on implementation fuel/strategy, so HardIdentity is not a
canonical cross-implementation identity, undermining its normative uses in
§33.2.1 semantic coherence and cross-artifact identity. Two conforming
implementations produce different HardIdentity values for the same instance
artifact and therefore diverge on accepting overlapping-but-extensionally-
equal instances.

> 15099-15100: "**conversion-reducible.** The definition may be unfolded by
δ-reduction during definitional equality." — 15106-15108: "It is structurally
recursive under §15.3 and its defining equations reduce by ordinary β/ι/δ
reduction without exposing well-founded proof terms." — 35918: "complete
δ-unfolding of transparent conversion-reducible definitions reachable from the
definition being normalized" — 35927: "memoization, fuel, or an equivalent
implementation technique sufficient to guarantee that the normalization
procedure itself terminates."

**Possible fix:** Specify guarded fixpoint unfolding: in §15.1 (and cross-
reference from §31.1 δ-reduction and §33.1.2), add: 'A conversion-reducible
recursive definition δ-unfolds only when its designated structural-recursive
(or measure) scrutinee position is constructor-headed after normalization;
otherwise the occurrence remains a neutral fixpoint constant. Hard-Hash full
normalization uses the same guarded rule, and recursive definitions appear in
canonical normal forms as guarded fixpoints.' Delete or qualify the fuel
bullet in §33.1.2 so that the guarded normal form (which exists and is unique)
— not a fuel-truncated form — defines HardIdentity.

## 29. §16.3.2: Named holes shared across occurrences with different local contexts: solution scoping and cross-context expected-type equality are undefined

**incompleteness** · severity **medium** · verification: **confirmed** ·
Spec.md lines 17163-17169, 17259-17264

§16.3.2 makes repeated occurrences of `?h` within one declaration 'refer to
the same metavariable' and requires they 'elaborate at definitionally equal
expected types', but the occurrences may sit under different local binders,
e.g. `(\x -> (?h : Int)) 1 + (\y -> (?h : Int)) 2`. The spec never constrains
which variables a solution of the shared metavariable may mention: an
implementation that solves ?h := x at the first occurrence produces an ill-
scoped (unsound) term at the second; a contextual-metavariable implementation
restricts solutions to the common context and rejects. Moreover
'definitionally equal expected types' is not well-defined when the expected
types mention occurrence-local binders (e.g. `Vec x Int` at one occurrence and
`Vec y Int` at another live in different contexts, so the comparison judgment
as stated has no common context). Grep for any scoping rule for shared hole
metavariables (beyond 'Named holes do not escape their enclosing declaration')
comes up empty.

> 17165-17166: "Repeated occurrences of the same named hole within one
enclosing declaration or local right-hand side refer to the same
metavariable." — 17167-17168: "Repeated occurrences of the same named hole
MUST elaborate at definitionally equal expected types; otherwise compilation
fails."

**Possible fix:** Add to §16.3.2 Semantics: 'The shared metavariable of a
named hole is created in the largest context common to all of its occurrences.
A solution may mention only binders in scope at every occurrence; a candidate
solution mentioning any other binder is rejected. Expected types of the
occurrences are compared for definitional equality after restriction to that
common context; an expected type that cannot be expressed in the common
context makes the hole inconsistent (kappa.hole.inconsistent).'

## 30. §17.1 + §17.1.5 + §17.1.9 (cf. §3.2.10 diagnostics): Contribution of guarded cases to `match` exhaustiveness is never defined ('accounting for ... guards' is an undefined judgment)

**incompleteness** · severity **medium** · verification: **confirmed** ·
Spec.md lines 17787-17790, 17918, 18140, 3176

§17.1 states the exhaustiveness MUST ('match must be exhaustive; missing cases
are a compile-time error') but never defines whether a case with a guard
covers its pattern. §17.1.5 accepts `case impossible` 'after accounting for
the preceding cases and guards', but that accounting is defined nowhere; a
semantic accounting of guard truth is undecidable. §17.1.9 says guard failure
does not exclude the pattern, and the §3.2.10 diagnostic payload mentions
'guard information when guards prevent coverage', implying but never stating
the conservative rule. Grep for any normative sentence like 'a guarded case
contributes no coverage' comes up empty. Two conforming implementations
diverge on real programs: an implementation that counts `case True if g -> e1
case False -> e2` over `Bool` as exhaustive compiles a match that falls
through at runtime when the scrutinee is True and g is False — and the spec
defines no runtime behavior for a match with no matching case (grep for match-
failure runtime semantics finds none), so that reading is unsound; a
conservative implementation rejects the same program.

> 17789: "For **closed** types (e.g. ADTs, `Bool`), `match` must be
exhaustive; missing cases are a compile-time error." — 17918: "It is accepted
only if, after accounting for the preceding cases and guards, the remaining
uncovered remainder of the scrutinee is unreachable"

**Possible fix:** Add to §17.1 Exhaustiveness: 'For coverage purposes, a case
carrying an `if` guard contributes no coverage of its pattern; exhaustiveness
must be established by the unguarded cases (including `case impossible`)
alone. An implementation MAY additionally treat a guard that normalizes to
True under the branch-local refinement context (§31.1.2) as absent.' Reference
this rule from §17.1.5's 'accounting for the preceding cases and guards'.

## 31. §17.2.1/§17.2.3 vs §17.1.7 (and §16.4.2's || analogue): Or-pattern branches have no refinement-evidence rule: neither per-alternative HasCtor checking nor residual LacksCtor contribution is defined

**incompleteness** · severity **medium** · verification: **confirmed** ·
Spec.md lines 18343-18347, 18362-18371, 17947-17952, 17958-17968

§17.1.7 introduces `HasCtor s ⟨C⟩` only for a branch 'headed by constructor
C', and residual `LacksCtor` only from 'preceding top-level unguarded
constructor branches'. An or-pattern branch `case A _ | B _ -> body` is headed
by no single constructor, and the spec defines: (a) no branch-local evidence
for its body (contrast §16.4.2, which for `if p is IntBox || p is NatBox then
p.value else 0` explicitly requires the then-body to be checked once per
success environment — no analogous rule exists for the pattern form `case
IntBox _ | NatBox _ -> p.value`), and (b) no negative facts contributed to
later branches (does `case LT | EQ -> a case _ -> b` give the residual branch
`LacksCtor o ⟨LT⟩` and `LacksCtor o ⟨EQ⟩`, hence derived `HasCtor o ⟨GT⟩` per
§16.4.1 narrowing?). §17.2.3 constrains only binder names/types/quantities.
Grep over the whole spec finds or-patterns addressed only at lines 5013, 11017
(quantity merge), 18343-18371. Conforming implementations will observably
diverge on whether such programs (constructor-field projection in or-branch
bodies; refl-style proofs in residual branches after or-branches) are
accepted.

> 17947-17948: "When a `match` scrutinee `s` is checked against a top-level
constructor branch headed by constructor `C`, that branch is typechecked under
additional erased implicit evidence" — 18345: "p1 | p2 | p3" — 18366: "Each
alternative must bind the **same set of names**."

**Possible fix:** Add to §17.1.7 (or §17.2.3): 'A branch whose pattern is an
or-pattern is typechecked once per alternative, under the bindings and
refinement evidence (including HasCtor and family-argument equalities) of that
alternative, exactly as §16.4.2 checks the success body of `||` per disjunct;
the guard, if any, is likewise checked per alternative. An unguarded top-level
or-pattern branch whose alternatives are all constructor patterns contributes
LacksCtor evidence for each alternative's head constructor to subsequent
residual branches.'

## 32. §18.1.12 (and §32.2.5): `mask` restore semantics under nesting unspecified: unconditional unmask vs restore-to-entry-state

**ambiguity** · severity **medium** · verification: **confirmed** · Spec.md
lines 19213-19215, 19241-19242, 35376-35395

The only normative statement about `restore` is that it "re-enables
interruption for a selected subcomputation"; §32.2.5 adds nothing about
nesting. Two conforming readings exist with observably different behavior: (A)
`restore` unconditionally re-enables interruption delivery; (B) `restore`
restores the interruptibility state that was in effect when the corresponding
`mask` was entered (the GHC/ZIO discipline). Failure scenario:
`uninterruptible (helper ...)` where `helper` internally uses `mask (\restore
-> ... restore waitOp ...)` — under reading (A), a pending interruption is
delivered inside `waitOp`, breaking the caller's uninterruptible cleanup
guarantee (any library using mask/restore silently punches a hole in every
caller's mask); under reading (B) it is not delivered. Since finalizers run
masked (19246-19247) and §32.2.14 permits finalizers that "explicitly restore
interruption" (line 35614), this ambiguity directly affects resource-safety
code.

> line 19241-19242: "`mask f` suppresses interruption while `f` executes. The
`restore` function re-enables interruption for a selected subcomputation."

**Possible fix:** Add to §18.1.12: "The `restore` function passed to `mask f`
restores the interruptibility status that was in effect immediately before
that `mask` was entered; it does not unconditionally enable interruption. In
particular, applying `restore` inside an outer `mask` or `uninterruptible`
region whose masking was already in effect at that `mask`'s entry does not
make the subcomputation interruptible." Mirror the sentence in §32.2.5.

## 33. §18.1.19 vs §18.1.21: §18.1.19 worked example describes deep-handler behavior but uses shallow `handle`

**contradiction** · severity **medium** · verification: **confirmed** ·
Spec.md lines 19539-19562 vs 19766-19767

The first worked example handles `do { inner.put 1; outer.put 2; inner.get ()
}` with shallow `handle` whose clauses resume via bare `k ()` / `k 10` and
never re-handle the resumption. Under §18.1.21 ("The current handler is not
automatically reinstalled around `k`"), after the inner handler consumes
`inner.put 1` and resumes, the inner handler is gone; after the outer handler
consumes `outer.put 2` and resumes, both handlers are gone; so the trailing
`inner.get ()` is unhandled. The example's normative prose — that `inner.get`
"is intercepted by the handler for `inner`" — is therefore false as written;
it holds only for `deep handle` (or for clauses that explicitly re-handle). An
implementer calibrating handler semantics against this example would implement
auto-reinstalling (deep) behavior for `handle`, directly contradicting
§18.1.21.

> line 19561-19562: "The operation `inner.get` is intercepted by the handler
for `inner`, not by the handler for `outer`, even though both labels carry the
same effect interface." — vs line 19766-19767: "The current handler is not
automatically reinstalled around `k`. To continue handling the same label
after resumption, the handler body must explicitly handle the resumed
computation again."

**Possible fix:** In §18.1.19, change both `handle` occurrences of the first
example (and the outer/inner handlers) to `deep handle`, or rewrite the
operation clauses to re-handle the resumed computation (e.g. `case put _ k ->
handle inner (k ()) with ...`). The second (`sameLabel`) example only
exercises one operation and may remain shallow, but should be changed to `deep
handle` for consistency.

## 34. §20.2, §20.10.2 (cf. §6.4, §30.7): Element semantics of ranges (endpoint inclusion, direction, emptiness, meaning of `exclusive`) are never defined

**omission** · severity **medium** · verification: **confirmed** · Spec.md
lines 22868-22903, 24053-24054

§20.2 mandates portable Rangeable instances for Nat, Int, Integer, and
UnicodeScalar and defines `..`/`..<` as `range from to False/True`, but the
spec never defines what value sequence a range denotes: whether `to` is
included when exclusive=False (the flag is never given a meaning), the step,
whether `3 .. 1` is empty or enumerates descending, or what `..<` does when
from == to. §20.10.2 only says the range IntoQuery has 'mode and cardinality
determined by the range implementation'. The sole enumeration text anywhere in
the spec is §6.4's 'Rangeable UnicodeScalar enumerates by increasing scalar
value, skipping invalid surrogate code points' (line 5842), which still does
not fix endpoint inclusion or the from>to case. Greps for 'inclusive',
'descending', 'empty range', 'from > to' over the whole spec return nothing
else. Two conforming implementations can disagree on `[ for x in 1..3, yield x
]` (is 3 included?) and `[ for x in 3..1, yield x ]` ([] vs [3,2,1]) — core
observable divergence for essentially every loop-over-range program.

> L22894-22895: "* `from .. to` elaborates to `range from to False`.\n* `from
..< to` elaborates to `range from to True`." ... L22902: "The portable prelude
MUST provide `Rangeable` instances for `Nat`, `Int`, `Integer`, and
`UnicodeScalar`." L24053-24054: "the canonical range result type of §20.2,
with mode and cardinality determined by the range implementation"

**Possible fix:** Add to §20.2: 'For the required
Nat/Int/Integer/UnicodeScalar instances, `range from to exclusive` denotes the
ascending sequence from, from+1, ..., bounded above by to; `to` itself is
included iff exclusive = False. If from > to (or from >= to when exclusive =
True) the range is empty; ranges never enumerate descending. Cardinality of
the resulting IntoQuery is QZeroOrMore.'

## 35. §20.6.1: `order by expr` has no defined sort direction and multi-key ordering has no defined comparison rule

**incompleteness** · severity **medium** · verification: **confirmed** ·
Spec.md lines 23315-23356

§20.6.1 gives four syntactic forms including bare `order by expr` and multi-
key `order by (asc expr1, desc expr2, expr3)`, and gives typing (Ord K per
key) and stability, but the only semantic sentence is 'order by applies stable
sorting to the current query pipeline'. Nowhere does the spec say (a) that
bare `order by expr` (and a direction-less key inside a tuple) sorts
ascending, (b) how `asc`/`desc` map onto the `Ord` instance's comparison, or
(c) that multiple keys compose lexicographically left-to-right. A whole-spec
grep for 'ascending'/'descending' returns zero hits. Two conforming
implementations can sort the same comprehension in opposite orders, or
prioritize keys differently — directly observable in every `order by` result
and also feeding the encounter-order-sensitive semantics of skip/take, keep
first/last, and grouped fold order.

> L23318-23321: "order by expr\norder by asc expr\norder by desc expr\norder
by (asc expr1, desc expr2, expr3)" ... L23333: "* `order by` applies stable
sorting to the current query pipeline."

**Possible fix:** Add to §20.6.1 Semantics: 'A key without an explicit
direction sorts ascending. `asc` orders rows so that keys are nondecreasing
under Ord K; `desc` reverses that key comparison. Multiple keys compare
lexicographically in written left-to-right order: later keys are consulted
only when all earlier keys compare equal.'

## 36. §22 (22.4 signatures) vs §16.3.3 and §9.3: std.deriving.shape requires implicit discharge of a quantified goal `forall x. IsTrait (tc x)` that the implicit-resolution procedure cannot solve

**incompleteness** · severity **medium** · verification: **confirmed** ·
Spec.md lines 25833-25846, 17288-17342, 9324-9325

`requiredRuntimeFieldConstraints`, `requireRuntimeFieldInstances`, and
`requireRecordFieldInstances` all take an implicit parameter `(@_ : forall (x
: Type). IsTrait (tc x))` — a Pi-typed (quantified) evidence goal. The
normative implicit-resolution procedure of §16.3.3 has exactly four steps
(local context defeq lookup, trait-evidence resolution requiring `IsTrait G`
for the goal G itself, boolean-proposition normalization, equality
reflection); none can synthesize a lambda inhabiting a forall-type, and
`IsTrait (forall x. IsTrait (tc x))` does not hold, so step 2 never fires.
§9.3 says the compiler synthesizes `IsTrait (Tr args)` only 'for every well-
formed full application of a trait constructor', and user source 'MUST NOT
declare instances of IsTrait', so users also cannot register the quantified
witness as an instance. Consequently the intended call
`requireRuntimeFieldInstances Show shape` fails with an unsolved implicit goal
in every conforming implementation, making the mandatory Phase 0 API unusable
as specified.

> 25834-25836: "forall (tc : Type -> Type) (@0 a : Type).\n (@_ : forall (x :
Type). IsTrait (tc x)) ->\n AdtShape a -> Elab (List (FieldConstraint tc))";
17281-17282: "if the callee expects an implicit argument `(@x : G)` and the
call site does not supply one, the compiler attempts to synthesize a term of
type `G`."

**Possible fix:** Either add a rule to §16.3.3: "If the goal G is a Pi-type
`forall (x : A). G'`, resolution introduces a fresh binder x and recursively
solves G' under it, returning the lambda" (eta-expansion of quantified
evidence goals); or change the three §22 signatures to drop the quantified
implicit and instead require IsTrait evidence per concrete field type inside
the Elab action (e.g. take `tc` plus resolve `IsTrait (tc F)` at each field
type F during execution, failing with the existing kappa.deriving.shape
diagnostics).

## 37. §23.2 (with §23.3, §23.7): Staged code has no level discipline: escape outside quotes, nested quotation, and cross-level variable occurrences are unspecified

**incompleteness** · severity **medium** · verification: **confirmed** ·
Spec.md lines 26131-26143

§23.2 gives only two rules: "If expr : t, then .< expr >. : Code t" and `.~c`
"requires c : Code t and splices the staged subterm into the surrounding Code
quote". There are no staging-level rules at all: (a) whether `.~c` occurring
OUTSIDE any quotation is ill-formed (MetaOCaml forbids it; the grammar here
does not); (b) whether quotes nest (`.< .< e >. >. : Code (Code t)`) and, if
so, how many escapes are needed to reach a given level; (c) at which level the
escaped expression `c` is typechecked when quotes nest; (d) whether a binder
introduced at quotation level 1 may occur at level 2 (e.g. `.< \x -> .< x >.
>.`) — this is neither a 'present-stage value' under §23.3 nor covered by the
scope-safety rules of §23.7, which address only extrusion to LOWER levels. Two
conforming implementations can disagree on the accepted/rejected status of
straightforward nested-staging programs, and §23.7's scope-extrusion checks
cannot even be stated precisely without a level assignment.

> 26135: "If `expr : t`, then `.< expr >. : Code t`."; 26143: "requires `c :
Code t` and splices the staged subterm into the surrounding `Code` quote."

**Possible fix:** Add a level-indexed typing paragraph to §23.2: every
expression is checked at a stage level n >= 0; `.< e >.` checks e at level
n+1; `.~c` is permitted only at level n >= 1 and checks c at level n-1; a
variable occurrence is well-staged only at the level of its binder, except
present-stage (lower-level) values admitted through §23.3 lift; `.~` at level
0 is a compile-time error with a named diagnostic.

## 38. §23.3, §23.5 vs §28 prelude: Cross-stage persistence is unusable as specified: no Lift instances are required anywhere, 'simple variable occurrence' is undefined, and global references inside quotes have no rule

**incompleteness** · severity **medium** · verification: **confirmed** ·
Spec.md lines 26155-26156, 26196-26204, 26151-26152, 29856-29858

§23.3 makes `liftCode` (trait `Lift`) the ONLY way a present-stage value may
occur inside `.< ... >.`: explicitly or 'via elaboration of a simple variable
occurrence'. But (a) grep of the whole spec finds zero required `Lift`
instances — only the two trait declarations at lines 26151 and 29856 — so no
type is portably liftable and every use of cross-stage persistence is non-
portable; (b) 'simple variable occurrence' is used nowhere else in the spec
(only other hit is unrelated, line 20149) and is never defined —
implementations cannot know which occurrences trigger implicit liftCode
insertion; (c) there is no rule at all for references to resolved GLOBAL
declarations inside a quote. The spec's own §23.5 example `genlet .< expensive
n >.` mentions the global function `expensive` and the local `n`: under the
stated rule this requires `Lift` evidence for a function type (never
specified, and function types are elsewhere treated as non-representable) or
an unstated global-persistence rule. As written, the normative example cannot
elaborate.

> 26155-26156: "A present-stage value may occur inside `.< ... >.` only if it
is inserted by `liftCode`, either explicitly or via elaboration of a simple
variable occurrence."; 26198: "let shared = genlet .< expensive n >."

**Possible fix:** Add to §23.3: (1) "A reference to a resolved global
declaration inside `.< ... >.` denotes the same declaration at the generated
stage and does not require `Lift`."; (2) define: "A simple variable occurrence
is a bare occurrence of a local binder `x : a`; elaboration inserts `liftCode
x` for it, requiring coherent `Lift a` evidence at the quotation site."; (3)
add a portable-minimum `Lift` instance list (at least `Unit`, `Bool`, the
integer types, `Float`, `Double`, `String`, `Bytes`, and
`Option`/`Result`/`List` of liftable types) to §23.3 or §28.

## 39. §28.2 (with §18.1.6): Duration's range, resolution, overflow behavior, and unit-conversion identities are unspecified despite total constructors, required AdditiveGroup laws, and observable Eq/Ord/Show

**omission** · severity **medium** · verification: **confirmed** · Spec.md
lines 29968-29999, 30604-30632, 30614-30620

`nanos`..`minutes` are total pure functions from arbitrary-precision `Integer`
to `Duration`, and the prelude MUST provide `Eq/Ord/Show Duration`,
`CheckedSub Duration` with `subDefined x y = True`, and
`AdditiveMonoid/AdditiveGroup Duration` (whose law members must actually
hold). Nothing states whether `Duration` is arbitrary-precision or fixed-
width, what `nanos (10^30)` denotes, or even that `micros 1 = nanos 1000` /
`minutes 1 = seconds 60` (the constructors' unit semantics are never given as
laws — only suggestive names). Since totality (§15) forbids trapping in these
pure signatures, an implementation must silently pick arbitrary-precision or
wrapping fixed-width; both satisfy the stated group laws but disagree
observably: `durationCompare (nanos (2^64)) (nanos 0)` is GT under arbitrary
precision and LT under 64-bit wrapping, and `minutes 1 == seconds 60` may be
False in a conforming implementation as written.

> line 29971-29972: "expect term nanos :\n Integer -> Duration"; line 30607:
"`nanos`, `micros`, `millis`, `seconds`, and `minutes` accept signed `Integer`
values."; line 30620: "AdditiveMonoid Duration, AdditiveGroup Duration"

**Possible fix:** Add normative rules to §28.2: `Duration` is observationally
a signed integer count of nanoseconds (pin the resolution); `micros n = nanos
(1000 * n)`, `millis n = nanos (1000000 * n)`, `seconds n = nanos (10^9 * n)`,
`minutes n = nanos (60 * 10^9 * n)`; and either (a) `Duration` is arbitrary-
precision, or (b) implementations MUST document the fixed range and the
required behavior of constructors and `durationAdd`/`durationSub` outside it
(with the choice pinned, not implementation-defined, if the group instances
are to remain portable).

## 40. §29.5: std.bytes search/prefix/take-drop operations have no specified semantics: argument order, out-of-range behavior, and first-match are all implementer guesses

**ambiguity** · severity **medium** · verification: **confirmed** · Spec.md
lines 32173-32198, 32283-32292

The required operations `bytesStartsWith : Bytes -> Bytes -> Bool`,
`bytesEndsWith`, `bytesContains`, and `bytesBreakOn : Bytes -> Bytes -> Option
(prefix, suffix)` never state which argument is the pattern/needle and which
is the subject — two conforming implementations can flip them (grep shows
these names occur only in §29.5; the 'Extensional semantics' block at
32283-32292 covers only length/index/Eq/Ord/append/slice). `bytesTake n bs` /
`bytesDrop n bs` are total but their behavior when `n > bytesLength bs` (clamp
vs. something else) is unstated. `bytesFind : Byte -> Bytes -> Option Nat`
does not say it returns the FIRST occurrence, and `bytesBreakOn`'s split point
(first occurrence of the separator? is the separator included in prefix or
suffix or dropped?) is entirely unspecified. Each of these is directly
observable and each admits at least two natural conforming readings.

> line 32179-32181: "expect term bytesStartsWith :\n Bytes -> Bytes -> Bool";
line 32188-32189: "expect term bytesFind :\n Byte -> Bytes -> Option Nat"

**Possible fix:** Add a Rules block after the core operations:
`bytesStartsWith prefix bs` / `bytesEndsWith suffix bs` / `bytesContains
needle bs` name and fix the argument roles; `bytesFind b bs` returns the least
offset at which `b` occurs; `bytesBreakOn sep bs` splits at the first
occurrence of `sep`, with `prefix` the bytes before it and `suffix` the bytes
from the start of the match (state whether `sep` is included), plus the empty-
separator case; `bytesTake n bs` / `bytesDrop n bs` clamp `n` to `bytesLength
bs`.

## 41. §29.7: `IsOk` is used in required `std.config` signatures but never defined anywhere in the spec

**incompleteness** · severity **medium** · verification: **confirmed** ·
Spec.md lines 32453-32466

The portable minimum of the required module `std.config` gives `unify` and
`(<&>)` proof parameters of type `IsOk (tryUnify xs) = True`, but `IsOk` is
not declared in §29.7's portable minimum, is not a prelude export (§28.2 lists
no `IsOk`), and appears nowhere else in the 47k-line spec (grep -n 'IsOk'
Spec.md yields only lines 32457 and 32465). As written, the required
signatures of `unify` and `(<&>)` do not typecheck: they reference an
unresolved name. Additionally, discharging the obligation requires normalizing
an application of `tryUnify`, which is declared only as an opaque `expect
term` with no requirement that it be conversion-reducible, so even with `IsOk`
defined the checked forms could be universally unusable in a conforming
implementation.

> line 32455-32458: "expect term unify :\n forall (a : Type).\n (@_ :
ConfigUnify a) ->\n (xs : List a) ->\n (@_ : IsOk (tryUnify xs) = True) ->\n
a"

**Possible fix:** Add to §29.7's portable minimum: `IsOk : forall (e : Type)
(a : Type). Result e a -> Bool` with `IsOk (Ok _) = True; IsOk (Err _) =
False`, declared transparent, and state that a conforming
loader/implementation MUST make `tryUnify` applications conversion-reducible
enough for the §29.7 normalization rule (or explicitly scope the checked forms
to config-mode evaluation where the loader evaluates `tryUnify`).

## 42. §3.1.5 vs Appendix-T harness (assertDiagnosticAt) and §37.8: Diagnostic column numbers have no defined counting unit, yet portable conformance assertions compare columns

**omission** · severity **medium** · verification: **confirmed** · Spec.md
lines 1057-1069

§3.1.5 requires source origins to carry start/end column and pins only
'1-based', and requires the OPTIONAL extra offsets (byte, UTF-8, UTF-16,
scalar) to be 'clearly named' — but never says what unit a column itself
counts: UTF-8 bytes, Unicode scalars, UTF-16 code units, or grapheme clusters.
Grep over the whole spec finds no definition; §37.8 even forbids 'an unlabeled
integer offset whose unit is ambiguous' while 'column' is exactly such an
integer, and the conformance harness directive `assertDiagnosticAt <path>
<severity> <code> <line> <column>` (line 46539) 'requires the primary origin
to begin at the given 1-based line and 1-based column' (46582-46583). For any
diagnostic on a line containing non-ASCII text before the blamed token, two
conforming implementations report different columns for the same origin, so
portable conformance fixtures using assertDiagnosticAt give divergent
pass/fail results.

> L1066-1069: 'Line and column numbers in JSON diagnostic output are
1-based.\n\nImplementations MAY additionally expose 0-based byte offsets,
UTF-8 byte offsets, UTF-16 code-unit offsets, or Unicode scalar offsets, but
such offsets MUST be clearly named.'

**Possible fix:** Add one sentence to §3.1.5 after line 1066: 'A column counts
Unicode scalar values from the start of the line; the first scalar value on a
line is column 1. A tab counts as one scalar value.' (Any single pinned unit
suffices; scalar values match the §6.3.6 string text model.)

## 43. §32.2.20 (referenced by §18.1.21/§18.1.22 at lines 19765, 19898): Resumption-escape restriction (§32.2.20) is fail-open: violation is a MUST NOT with only optional enforcement and no defined runtime behavior

**incompleteness** · severity **medium** · verification: **confirmed** ·
Spec.md lines 35773-35776

Whether a captured segment 'contains pending exit actions' is a dynamic
property, so static detection is necessarily approximate. The spec makes
rejection conditional ('if the implementation detects such an escape,
compilation fails') and conservative rejection merely permitted ('MAY
conservatively reject'). An implementation that neither detects nor
conservatively rejects is textually conforming, yet it then executes a program
that violates the MUST NOT — and the spec defines no semantics for that
execution: when (if ever) do the escaped segment's pending `defer`/`using`
release actions run? Once, never, per use? This is a resource-safety hole
(leaked `using` resources or double-release) with unspecified behavior, in
contrast to §32.2.19 which delegates the analogous multi-shot problem to a
definite rejection rule (§18.1.20).

> 35774-35776: "a resumption value whose captured segment contains pending
exit actions MUST NOT escape the operation clause; and if the implementation
detects such an escape, compilation fails. A conforming implementation MAY
conservatively reject when it cannot prove that the captured segment is free
of pending exit actions."

**Possible fix:** Make the check fail-closed: 'An implementation MUST reject
at compile time any program in which it cannot prove that every resumption
value escaping its operation clause has a captured segment free of pending
exit actions.' (Or, alternatively, define the runtime semantics: an escaped
segment's pending exit actions run in masked LIFO order when the resumption
value is abandoned, and abandonment of the last live reference is a defined
runtime event.)

## 44. §32.2.3 (with §18.4 forkDaemon, line 18840): No program-termination semantics: fate of daemon fibers (and their finalizers) when the main fiber completes is unspecified

**omission** · severity **medium** · verification: **confirmed** · Spec.md
lines 35326-35345

§32.2 defines fiber creation, supervision scopes, and scope shutdown, and
§18.4 says `forkDaemon` creates a fiber 'not attached to the current
structured runtime scope' — but the runtime model never defines whole-program
termination. Greps for 'program exit', 'process exit', 'program terminat',
'runtime shutdown', and 'main fiber' find nothing normative: when the
main/root fiber's computation completes while daemon fibers are still live,
does the runtime (a) wait for them, (b) interrupt them and run their
finalizers (like scope shutdown), or (c) abandon them without running
finalizers? All three are implemented in real runtimes (Go abandons, JVM user-
threads wait, ZIO interrupts) and are observably different (program hangs vs
exits; `using` releases run or not). Every implementer must decide; the model
is incomplete exactly at the 'orphaned fibers' boundary it otherwise regulates
carefully.

> 35336: "`forkDaemon` does not attach the created child fiber to that scope;"
— no rule anywhere states what happens to such fibers when the program's root
computation terminates.

**Possible fix:** Add a §32.2 subsection 'Program termination': 'When the root
fiber's computation completes, the runtime behaves as if the root supervision
scope exits: still-live daemon fibers are interrupted with tag `ScopeShutdown`
(or a new `RuntimeShutdown` tag) and the runtime waits for their termination
and finalizers before the process-level exit; their causes do not alter the
root Exit.' (Or pick abandonment — but say so.)

## 45. §34.3.3 vs §14, §32.2: §34.3.3 legality checkpoint cites wrong chapters for runtime obligations (Traits ch.14 and §34 itself) and never cites Chapter 32 where those obligations actually live

**incompleteness** · severity **medium** · verification: **confirmed** ·
Spec.md lines 38287-38290

The mandatory pre-publication KBackendIR validation requires that 'handler,
resumption, cleanup, and error-propagation structures satisfy the runtime
obligations of Chapters 18, 19, and 14' — but Chapter 14 (line 13930) is
'Traits (Typeclasses)' and contains no runtime obligations for handlers or
error propagation. The next bullet requires scheduler/timer/promise/fiber
structures to satisfy 'the runtime obligations of Chapters 18, 30, and 34' — a
self-reference — while the actual normative runtime obligations for fibers,
supervision, interruption, scheduling, timers, promises, STM, handlers, and
resumptions are in Chapter 32 (§§32.2.3-32.2.22, 'Runtime model for IO,
fibers, interruption, STM, handlers, and resumptions'), which neither bullet
cites. An implementer building the required checkpoint verifier from these
citations checks against the wrong normative text. (Note also §34.4 line 38618
similarly omits Chapter 32 from the backend preservation list.)

> L38287-38290: "handler, resumption, cleanup, and error-propagation
structures satisfy the runtime obligations of Chapters 18, 19, and 14; *
scheduler, timer, promise, fiber-identity, fiber-label, and synchronization
structures satisfy the runtime obligations of Chapters 18, 30, and 34;"

**Possible fix:** Change the first bullet's citation to "Chapters 18, 19, and
32" and the second bullet's to "Chapters 18, 30, and 32"; additionally add
Chapter 32 to the preservation list in §34.4 line 38618 ("Chapters 6, 18, 19,
20, 30, 32, 33, and 4").

## 46. §36.12 vs §36.39: Undeclared fragment suffixes: §36.12's iff-selection silently drops files, but E_BUILD_FRAGMENT_TAG_UNKNOWN is a required diagnostic class with no specified trigger

**ambiguity** · severity **medium** · verification: **confirmed** · Spec.md
lines 40697-40705, 43530, 41508

§36.12 defines selection as a biconditional: a file 'is selected for a target
iff ... 4. every fragment suffix on the file is declared or admitted by the
build configuration; and 5. every fragment suffix on the file is present in
the target's enabled fragment-tag set.' A file bearing an undeclared suffix
(e.g. the typo `log.natve.kp`) therefore fails condition 4 for every target
and is silently excluded from the whole build — no rule anywhere requires
diagnosing it (grep: the only 'undeclared fragment tag' rule, line 41508,
governs features, not source files). Yet §36.39 lists
`E_BUILD_FRAGMENT_TAG_UNKNOWN` among the required diagnostic classes without
ever specifying when it is emitted. Two conforming implementations diverge
observably: one rejects the build with E_BUILD_FRAGMENT_TAG_UNKNOWN, the other
silently compiles without the file (a serious correctness footgun, since the
missing module may only be detected — or not — at import time).

> L40702-03: "4. every fragment suffix on the file is declared or admitted by
the build configuration; and 5. every fragment suffix on the file is present
in the target's enabled fragment-tag set." — L43530:
"E_BUILD_FRAGMENT_TAG_UNKNOWN" (listed with no triggering rule)

**Possible fix:** Add to §36.12: "A `.kp` file under a selected source root
that carries a fragment suffix not declared by any fragment axis and not
otherwise admitted by the build configuration is a build error diagnosed as
`E_BUILD_FRAGMENT_TAG_UNKNOWN`; such a file is never silently excluded."
(Condition 4 then becomes redundant and should be removed or restated as this
error.)

## 47. §5.5.2 vs §5.5.1, §6.1.4, §36.12: Exported fixity is defined per operator, not per fixity kind, making prefix and infix `-` non-co-exportable

**contradiction** · severity **medium** · verification: **confirmed** ·
Spec.md lines 5071-5073, 4967, 5180, 40772-40773

§5.5.2 says the exported fixity for an operator is singular: the last top-
level fixity declaration for `op`. But an operator legitimately carries
several fixities of different kinds simultaneously (prefix, infix, postfix):
§5.5.1 explicitly discusses the state where 'both prefix and infix `-`
fixities are in scope' (which for portable code can only come from the
prelude's exports), and §6.1.4/§6.1.5 require prefix `-` to be usable in every
module (`-123` is `negate 123`) while binary `-` must also parse. Under §5.5.2
as written, a module (including std.prelude) that declares both `prefix 80
(-)` and `infix left 60 (-)` exports only whichever declaration is textually
last, so importing modules could not parse both `-x` and `a - b`. §36.12 (line
40772) compounds this by rejecting an effective module when two fragments
export fixities for the same operator that differ 'in kind', treating kind as
a conflict axis rather than a coexistence axis. Two conforming implementations
diverge: one exports one fixity record per operator (breaking `-`), one
exports one per (operator, kind).

> line 5071-5073: "A top-level fixity declaration for operator `op` is
exported iff the name `op` is exported under §8.5. The exported fixity for
`op` is the fixity that is in scope at the end of the module, i.e. the last
top-level fixity declaration for `op`." line 4967: "`(-)` is ambiguous when
both prefix and infix `-` fixities are in scope and no expected type
disambiguates it."

**Possible fix:** In §5.5.2 replace the sentence with: 'For each fixity kind
(infix, prefix, postfix), the exported fixity of that kind for `op` is the
fixity of that kind in scope at the end of the module, i.e. the last top-level
fixity declaration of that kind for `op`. An operator may export at most one
fixity per kind.' In §36.12 change 'a top-level fixity declaration for the
same operator' to 'for the same operator and same fixity kind' and drop 'kind'
from the identity triple.

## 48. §6.3.3: Multiline-string dedent prefix `I` is undefined when the closing delimiter is not preceded only by spaces on its line

**ambiguity** · severity **medium** · verification: **confirmed** · Spec.md
lines 5433-5439

The dedent rule defines `I` as 'the exact sequence of leading spaces on the
line containing the closing delimiter, immediately before that delimiter'. The
two qualifiers conflict whenever the closing delimiter is not preceded solely
by spaces on its line — which the grammar allows: the single-line form `let s
= """abc"""` (content does not begin with a newline, so it is legal), or a
final content line ending in text directly followed by `"""`. Reading (a): `I`
= the line's leading spaces from column 0 — then an indented ` let s =
"""abc"""` has `I` = four spaces, the content line `abc` does not begin with
`I`, and the literal is ill-formed. Reading (b): `I` = the maximal space run
immediately before the delimiter — empty here, so the literal is accepted.
Conforming implementations diverge on acceptance of a very common form, and on
how many spaces are stripped from a trailing-content closing line.

> lines 5433-5434: "Let `I` be the exact sequence of leading spaces on the
line containing the closing delimiter, immediately before that delimiter."
line 5439: "If a non-blank content line does not begin with `I`, the literal
is ill-formed."

**Possible fix:** Add: 'If the closing delimiter is preceded on its line by
any non-space character, `I` is the empty sequence (equivalently: the dedent
line is the closing-delimiter line only when that line contains nothing but
spaces before the delimiter; otherwise no dedent is performed).' Or
normatively require the closing delimiter of a multiline literal whose content
spans more than one line to appear on a line containing only spaces before it,
and define `I` as those spaces.

## 49. §T.5.5, §T.7 vs §34.1.6: Appendix T trace assertions require an event/subject classification of trace steps that Chapter 34 never defines

**incompleteness** · severity **medium** · verification: **confirmed** ·
Spec.md lines 46783-46818, 46852-46859, 36482-36487

T.5.5 evaluates `assertTraceCount <event> <subject> <relop> <n>` against 'the
portable view of the pipeline trace', retaining 'only trace steps whose event
and subject classifications both use the portable names listed above' (events:
parse, buildKFrontIR, advancePhase, emitInterface, lowerKCore,
evaluateElaboration, lowerKBackendIR, lowerTarget, reuse, verify; subjects:
file, declaration, module, interface, KCoreUnit, KBackendIRUnit, targetUnit).
But §34.1.6 requires a trace step to identify only 'a stable step name; its
input and output checkpoint names; whether the step changed the
representation; and whether verification was attempted' — there is no event or
subject classification field, and the portable event/subject names appear
nowhere in the spec outside Appendix T (verified by grep: buildKFrontIR/advanc
ePhase/evaluateElaboration/KCoreUnit/KBackendIRUnit/targetUnit occur only at
lines 46787-46807). Which internal steps map to which (event, subject) pair —
and hence every portable count — is unspecified; a conforming implementation
could classify nothing as portable, making every assertTraceCount count 0
while satisfying T.9's determinism, so incremental-reuse conformance tests
(T.7) are unportable and the MUST in T.5.5 is uncheckable as stated. This is
distinct from known issue 5 (diagnostic code names).

> L46813-14: "The portable view retains only trace steps whose event and
subject classifications both use the portable names listed above." vs
L36482-87: "Each trace step MUST identify at least: * a stable step name; *
its input and output checkpoint names; * whether the step changed the
representation; and * whether verification was attempted and whether it
succeeded."

**Possible fix:** Amend §34.1.6 to require each trace step to additionally
carry an `event` and a `subject` classification, enumerating the portable
names of T.5.5 there and pinning their meaning (e.g. one
`emitInterface`/`interface` step per module interface artifact produced; one
`reuse`/<unit> step per cache-reused unit; one `advancePhase`/`declaration`
step per KFrontIR phase advancement of a declaration), or alternatively gate
assertTraceCount behind a `requires capability pipelineTrace` whose
classification table the implementation MUST publish.

## 50. §24.9 vs §24.3/§24.4 and §28 (Dec): sameDynRep's `No` arm is an unguarded refutation: two valid DynReps for the same type can prove False

**unsoundness** · severity **medium** · verification: **weakened** · Spec.md
lines 26519-26521, 26338-26340, 26299, 26383-26384, 29781-29783

`sameDynRep : DynRep a -> DynRep b -> Dec (a = b)` where `Dec p = Yes p | No
(p -> Void)` (line 29781-29783). The `No` arm therefore carries a genuine
refutation of type equality. But every stated soundness condition in §24.3
constrains only the `Yes` direction: 'Yes p is sound only if p is valid
propositional equality' and implementations must prevent fabrication of
'unsound equality evidence'. Nothing forbids returning `No` when the
represented types ARE equal. This is reachable in conforming programs: §24.4
permits libraries to provide DynRep values for indexed/refined/higher-order
types via their own 'explicit runtime witness scheme', and §24.3's
extensional-equivalence rule covers only 'multiple coherent DynamicType a
instances in the same effective instance environment' — not two independently
supplied DynRep values for the same type from different libraries or
environments. If `r1, r2 : DynRep T` come from two mutually unaware witness
schemes, an implementation that returns `No np` violates no stated rule, and
the program can evaluate `np refl : Void`, producing an inhabitant of the
empty type at runtime (logical inconsistency / arbitrary type via absurd). The
§24.3 bullet 'MUST NOT be hidden inside two incompatible DynRep a values for
the same apparent a' is an obligation on representation designers, not a rule
making `No` sound.

> 26520-26521: "forall (@0 a : Type) (@0 b : Type). DynRep a -> DynRep b ->
Dec (a = b)"; 26338-26340: "`sameDynRep repA repB = Yes p` is sound only if
`p` is valid propositional equality between the represented types.";
29781-29783: "data Dec (p : Type) : Type = Yes p No (p -> Void)"

*Verifier caveat (why this is weakened):* The quotes are accurate and §24.3
(26336-26344) does state soundness only for the Yes direction. But the
scenario the finding needs is directly forbidden elsewhere in the same
section: §24.3's final bullet (26355-26359) says a policy/encoding/witness-
scheme distinction 'MUST NOT be hidden inside two incompatible DynRep a values
for the same apparent a' — the two-mutually-unaware-schemes setup is itself
non-conforming — and §24.4 (26383-26384) permits exotic DynReps only with a
witness scheme tha …

**Possible fix:** Change the result type to `Option (a = b)` (with `None`
meaning 'not known equal'), and in §24.1 replace "If `sameDynRep repTarget
repStored = No _`, `checkedCastWith` returns `Result.Err`" accordingly.
Alternatively, keep `Dec` but add to §24.3: "`sameDynRep repA repB = No np` is
sound only if the represented types are propositionally unequal; a conforming
implementation MUST return `Yes` for any two valid `DynRep` values whose
represented types are equal, regardless of the instance, library, or witness
scheme that produced them." (Note the alternative makes cross-library rep
comparison a completeness obligation that is likely unimplementable, so the
Option change is the minimal sound edit.)

## C. Low severity — footguns, wording defects, and minor gaps

## 51. §10.1.1: Evaluation order of constructor default expressions relative to supplied field expressions is unspecified

**omission** · severity **low** · verification: **confirmed** · Spec.md lines
8549-8551, 8580

§10.1.1 pins supplied field expressions to "evaluated exactly once in source
order" but says defaults are "instantiated in constructor-parameter order
after supplied fields have been checked for duplicates and extra labels" —
checked, not evaluated. Whether a default expression is evaluated before or
after later-in-source supplied fields (and before or after all supplied
fields) is left open. Defaults are arbitrary expressions (e.g. `xs : Vec n a =
replicate n defaultElement` at line 8517) that can defect or diverge, so the
order is observable: for `data C : Type = C (a : Int = defectA) (b : Int)` and
the call `C { b = defectB }`, one conforming implementation raises defectB
first (all supplied fields, then defaults), another raises defectA first
(strict constructor-parameter order). Every implementer must decide this and
the spec is silent.

> line 8549: "Supplied field expressions are evaluated exactly once in source
order."; lines 8550-8551: "Defaults are instantiated in constructor-parameter
order after supplied fields have been checked for duplicates and extra
labels."

**Possible fix:** Add one sentence to the §10.1.1 rules: 'Default expressions
are evaluated after all supplied field expressions have been evaluated, in
constructor-parameter order.' (Or specify full constructor-parameter-order
interleaving; either choice, stated normatively, removes the divergence.)

## 52. §12.2.6 vs §12.2, §12.2.1: Duplicability table lists `&` among "ordinary v1 surface quantities", contradicting "`&` is not a quantity"

**contradiction** · severity **low** · verification: **confirmed** · Spec.md
lines 11484-11489 vs 10619, 11037

§12.2 states flatly "`&` is not a quantity" and §12.2.1 states "Borrowed
access is not an inhabitant of `Quantity`", yet the §12.2.6 duplication-
position table, explicitly scoped to "ordinary v1 surface quantities",
enumerates `&` as a duplicable quantity: "duplicable quantities: 0, &, >=1,
ω". An implementer deriving the duplicability predicate over `Quantity` from
this table must invent a sixth quantity value that other sections forbid; it
also leaves unstated whether a `(1 & x : A)` binding (borrowed access,
interval quantity 1) is duplicable — the `&` row says yes, the `1` row says
no.

> line 10619: "`&` is not a quantity."; lines 11486-11489: "For ordinary v1
surface quantities, ignoring internal path state: duplicable quantities: 0, &,
>=1, ω not duplicable quantities: 1, <=1"

**Possible fix:** Remove `&` from the quantity table and add a separate
sentence: 'A borrowed binding's view is duplicable as a shared borrow
regardless of access mode; the binding's interval quantity is checked
separately, so a borrowed binding at interval quantity 1 or <=1 remains non-
duplicable for interval accounting.' (Mirror the analogous fix already made
for droppability at lines 11473-11474.)

## 53. §14.1 vs §14.1.1: Eq's eqSound/eqComplete declared with borrowed binders in §14.1 but owned binders in §14.1.1

**contradiction** · severity **low** · verification: **confirmed** · Spec.md
lines 13956-13957 vs 14115-14116

The same prelude trait `Eq` is rendered twice with definitionally different
member types: §14.1 gives `eqSound : (& x : a) -> (& y : a) -> ((x == y) =
True -> x = y)` (borrowed operands), while §14.1.1 gives `eqSound : (x : a) ->
(y : a) -> ((x == y) = True -> x = y)` (owned, default quantity ω). Per §31.1
('Quantities are part of a function type's identity' / binder-mode strict
invariance), these are not definitionally equal member types, so an instance's
`eqSound`/`eqComplete` definition that checks against one declaration fails
against the other (an owned-binder proof may consume its arguments; a
borrowed-binder one may not). Every hand-written `Eq` instance and every
explicit projection `d.eqSound` is affected; two conforming implementations
following the two renderings accept disjoint instance bodies. (Note also that
§14.1.1's eliminator list omits the declared member `eqIsSet`.)

> 13956: "eqSound : (& x : a) -> (& y : a) -> ((x == y) = True -> x = y)" —
14115: "eqSound : (x : a) -> (y : a) -> ((x == y) = True -> x = y)"

**Possible fix:** Make §14.1.1's example quote the §14.1 header verbatim
(borrowed binders: `(& x : a) -> (& y : a) -> ...` for both eqSound and
eqComplete), and extend the eliminator list to "(==), eqSound, eqComplete, and
eqIsSet". Add a sentence to §14.1 stating that the §14.1 header text is the
normative prelude declaration wherever the spec re-renders it.

## 54. §14.3.2 vs §14.3.1: §14.3.2 cross-reference points at the wrong resolution step

**contradiction** · severity **low** · verification: **confirmed** · Spec.md
lines 14649 vs 14564, 14595

§14.3.2 states 'Candidate collection in §14.3.1 step 2 uses normalized goals
and normalized instance heads', but §14.3.1's step 2 is 'Intrinsic solver
traits' (compiler-owned solvers, no candidate collection); global candidate
collection is step 3, which itself says 'Normalize the goal and instance heads
according to §14.3.2.' A literal reader could conclude intrinsic-solver goals
(ContainsRec, LacksVar, etc.) are matched by head-normalized candidate
collection, which contradicts their compiler-owned-solver semantics. Almost
certainly a stale step number after the local-context step was inserted, but
it sits in normative text defining the resolution algorithm.

> 14649: "Candidate collection in §14.3.1 step 2 uses normalized goals and
normalized instance heads." — 14595: "3. **Global ordinary instances.**
Normalize the goal and instance heads according to §14.3.2."

**Possible fix:** Change §14.3.2's sentence to 'Candidate collection in
§14.3.1 step 3 uses normalized goals and normalized instance heads.'

## 55. §16.4.1 vs §17.1/§17.1.5 grammar: §16.4.1 example uses `match opt with`, a form the match grammar does not admit, and reverses HasCtor argument order

**contradiction** · severity **low** · verification: **confirmed** · Spec.md
lines 17513-17521 vs 17768-17784, 17909-17911

The failure-side narrowing example in §16.4.1 is written `match opt with`
followed by case clauses, but the normative match form (§17.1) and grammar
(§17.1.5: matchCase ::= 'case' pattern ['if' expr] '->' expr) contain no
`with` keyword; grep over the whole spec shows `with` appears after `match`
only here and in one explicitly 'rejected' snippet (line 14159). The same
example's comment writes the evidence as `HasCtor Some opt`, reversing the
normative argument order `HasCtor e ⟨C⟩` (line 17476-17477: '@p : HasCtor e
⟨C⟩') used everywhere else (e.g. 17547 `HasCtor x ⟨Some⟩`) and omitting the ⟨⟩
tag brackets. A reader/implementer cannot tell whether `with` is an accepted
alternative surface form and which argument order of `HasCtor` is canonical
for tooling that renders refinement facts.

> 17514: "match opt with" — 17519: "the branch may be refined with `HasCtor
Some opt`." — versus 17476: "@p : HasCtor e ⟨C⟩"

**Possible fix:** In the §16.4.1 example, delete `with` (write `match opt` on
its own line) and change the comment to '... the branch may be refined with
`HasCtor opt ⟨Some⟩`.'

## 56. §18.6/§18.6.3 vs §18.8.12: `break`/`continue` inside a loop's own `else do` block: validity and consumption undefined

**ambiguity** · severity **low** · verification: **confirmed** · Spec.md lines
21083-21092, 21636-21645, 22186-22189

§18.6 permits `break`/`continue` "only within the body of a `while ... do ...`
or `for ... do ...` loop", and §18.7 lists the loop `else do` block as a
separate do-scope — but whether the `else` block counts as "within the body"
of its own loop is never stated, and label resolution ("targets the loop
labeled `L@` in that same body") does not say whether a loop lexically
encloses its own `else` block. If `break@L` inside L's `else do` is accepted,
§18.8.12 gives no consumption rule: the loop has already "completed normally"
and is specified to "run `onNoBreak` (if present) and return `Normal ()`"; a
`Break L` completion produced by `onNoBreak` has no defined consumer (the loop
is not re-entered, and propagating it outward reaches constructs that only
propagate mismatched labels). Failure scenario: `L@while c do { body } else do
{ break@L }` — one implementation rejects at compile time, another exits the
loop "again", a third propagates an unconsumed `Break L` outward with
undefined results.

> line 21084-21085: "`break` and `continue` are valid only within the body of
a `while ... do ...` or `for ... do ...` loop." — line 22177: "If false: the
loop completed normally; run `onNoBreak` (if present) and return `Normal ()`."

**Possible fix:** Add to §18.6.3: "The loop `else` block is not part of the
loop body for the purposes of `break`/`continue` targeting. `break`/`continue`
(labeled or not) occurring in a loop's `else` block may target only loops that
enclose the entire loop-plus-`else` construct; targeting the loop to which the
`else` block is attached is a compile-time error."

## 57. §18.8.7 vs §18.2.1: §18.8.7 normative `let?` elaboration never binds the pattern variables used by the continuation

**contradiction** · severity **low** · verification: **confirmed** · Spec.md
lines 22026-22035 vs 20405-20412

The normative elaboration is `⟦let? pat = expr; rest⟧ = bindC (lift matched)
(\tmp -> ⟦rest⟧)` with `matched = match expr case tmp@pat -> pure tmp case _
-> empty`. The continuation binds only the whole-value temporary `tmp`, but
`⟦rest⟧` refers to the variables bound by `pat` (that is the entire point of
`let?`); as written, those variables are unbound in `rest`, contradicting
§18.2.1's schematic `match expr case pat -> do rest`. Unlike the monadic-bind
case one bullet above it (which says "with `pat0` bound to `tmp`"), no binding
clause is stated here. A secondary issue: routing the whole scrutinee through
`tmp@pat` and `pure tmp` and then implicitly re-destructuring is not quantity-
neutral for linear payloads unless the re-match is made explicit. Failure
scenario: an implementer following §18.8.7 literally produces an elaboration
in which `let? Some x = maybeInt; println x` fails to resolve `x`, or must
invent an unspecified re-binding step, and different implementations may
disagree on where the destructuring (and its quantity accounting) happens.

> line 22028-22035: "`⟦let? pat = expr; rest⟧ = bindC (lift matched) (\tmp ->
⟦rest⟧)` where matched = match expr case tmp@pat -> pure tmp case _ -> empty"

**Possible fix:** Rewrite the rule as `⟦let? pat = expr; rest⟧ = bindC (lift
matched) (\tmp -> match tmp case pat -> ⟦rest⟧)` — or minimally append the
clause "with the variables of `pat` bound in `⟦rest⟧` exactly as by matching
`tmp` against `pat`, under ordinary quantity checking", matching the wording
already used for the monadic-bind case.

## 58. §24.7, §24.9: CastBlame 'MUST identify the demanded target representation' but is opaque with no specified accessor, rendering, or instance

**incompleteness** · severity **low** · verification: **confirmed** · Spec.md
lines 26450-26451, 26506

§24.7 imposes a normative content requirement on failed casts ('MUST identify
at least the demanded target representation', SHOULD attach boundary/source-
origin info), yet `CastBlame` is declared opaque (`expect data CastBlame :
Type`) and a whole-spec grep finds no accessor, projection, `Show`/render
requirement, or diagnostic-payload mapping for it anywhere (§25/§26 only add
`bridgeFailureToCastBlame`, which produces — not consumes — CastBlame).
Portable code therefore cannot observe the mandated identification, and the
MUST is unverifiable: an implementation whose CastBlame is a unit value with
the information stored nowhere reachable cannot be distinguished from a
conforming one through the portable surface.

> 26450-26451: "* `CastBlame` is opaque.\n* A failed `checkedCastWith` or
`checkedCast` MUST identify at least the demanded target representation.";
26506: "expect data CastBlame : Type"

**Possible fix:** Add to §24.9 a required observation operation, e.g. `expect
term renderCastBlame : CastBlame -> String` (deterministic, human-oriented,
MUST include the demanded target representation), or require a `Show
CastBlame` instance; alternatively rewrite §24.7's MUST as an implementation-
diagnostics requirement explicitly scoped to implementation-defined
observation channels.

## 59. §28.2 vs §28.2.1 (and §14.2.1): §28.2 classifies `(+)`, `(*)`, `(-)`, `(/)`, `(%)`, `(++)` as trait-member overloaded names, contradicting their canonical declarations as ordinary top-level functions

**contradiction** · severity **low** · verification: **confirmed** · Spec.md
lines 29492-29512 vs 30244-30249, 30761-30766, 30771-30776, 30790-30799

§28.2 says "Several listed terms are overloaded member names induced by the
corresponding prelude traits (§14.2.1)" and its list includes `(+)`, `(*)`,
`(-)`, `(/)`, `(%)`, and `(++)`. But the canonical declarations define these
as ordinary top-level `let` definitions over the traits (`trait Add ... = add
: a -> a -> a` then `let (+) x y = add x y`; likewise `(++)` via
`Monoid.append`), i.e. they are NOT trait members and §14.2.1's machinery
(evidence projection `d.(+)`, per-trait overloaded-name resolution) does not
apply to them. The two classifications are observably different: under the
member reading `d.(+)` for `d : Add Int` is a valid projection and a user
trait may add another `(+)` member that coexists under overloaded-member
resolution; under the ordinary-function reading `d.(+)` fails and a user
member named `(+)` collides with the global. Conforming implementations can
diverge on which programs are accepted.

> line 29492-29493: "Several listed terms are overloaded member names induced
by the corresponding prelude traits (§14.2.1)." (list at 29499 includes "zero,
one, add, (+), multiply, (*), negate"); line 30766: "let (+) x y = add x y"

**Possible fix:** In the §28.2 overloaded-member list, delete `(+)`, `(*)`,
`(-)`, `(/)`, `(%)`, `(++)` and add one sentence: "The operator spellings
`(+)`, `(*)`, `(-)`, `(/)`, `(%)`, and `(++)` are ordinary generic prelude
functions defined over the corresponding traits; they are not trait members
and do not participate in §14.2.1 overloaded-member resolution."

## 60. §29.3: std.hash internal list inconsistencies: `hashRational` declared but missing from the Terms list; `Hashable Nat` missing from required instances

**omission** · severity **low** · verification: **confirmed** · Spec.md lines
31499-31517, 31559-31560, 31709-31713

The §29.3 Terms list (lines 31500-31517) enumerates the module's exported
terms but omits `hashRational`, which is nonetheless canonically declared at
line 31559 — so whether `hashRational` is part of the portable minimum is
contradictorily specified. Separately, the required `Hashable` instances (line
31712) cover `Int, Integer, Rational, Float, Double, Ordering` etc. but omit
`Nat`, even though `Nat` is a core prelude numeric type with required `Eq
Nat`, `Ord Nat`, `Show Nat` (§28.2 lines 30660-30666) and the module itself
provides `hashNatTag`. A portable program using `Map Nat v` cannot rely on
hash acceleration while `Map Int v` can, for no stated reason (grep 'Hashable
Nat' over the whole spec is empty).

> line 31712: "Unit, Bool, Byte, Bytes, UnicodeScalar, Grapheme, String, Int,
Integer, Rational, Float, Double, Ordering" (no Nat); Terms list lines
31510-31513: "hashInt,\nhashInteger,\nhashFloatRaw,\nhashDoubleRaw," (no
hashRational, cf. declaration at 31559)

**Possible fix:** Add `hashRational` to the §29.3 Terms list, and add `Nat` to
the required `Hashable` instance list (its hash agreeing with `Eq Nat`).

## 61. §29.6 vs §28.2: §29.6 example calls `show` on `DebugEq`, but no rule provides or requires `Show DebugEq`

**contradiction** · severity **low** · verification: **confirmed** · Spec.md
lines 32405-32413, 30596-30602

The std.debug example is `println (show (debug.compare x y))`, where
`debug.compare` returns `DebugEq`. `println` requires `Show DebugEq` evidence.
The prelude's required `Show` instances (§28.2, lines 30596-30602) do not
include `DebugEq`, §29.6 does not require `std.debug` to export a `Show
DebugEq` instance (grep 'Show DebugEq' over the whole spec is empty), and
§29.6 explicitly says std.debug "does not synthesize or bind ordinary trait
evidence". So the spec's own example does not elaborate under the portable
minimum it defines.

> line 32412: " println (show (debug.compare x y))"; line 32376-32377:
"`std.debug` does not synthesize or bind ordinary trait evidence."

**Possible fix:** Either add "`std.debug` MUST export ordinary coherent
instances `Show DebugReason`, `Show DebugEq` (and optionally `Show
DebugTree`)" to §29.6, or change the example's last line to `println
(debug.render (debug.compare x y))`.

## 62. §34.1.9 (both lists) vs §15.1: §34.1.9 termination-kind enum and certificate strategy-kind enum have no defined mapping, and several strategy kinds have no corresponding termination kind

**ambiguity** · severity **low** · verification: **confirmed** · Spec.md lines
36829-36835 vs 36893-36905

The interface artifact must record, per exported transparent total-certified
definition, 'the termination kind (`structural`, `well-founded`, `size-
change`, `non-recursive`, `verified-assertTerminates`, or `assertReducible-
unverified`)', while the per-SCC certificate records 'the accepted strategy
kind' from a different ten-element enum (Structural, SemanticStructural,
NatMeasure, WellFoundedRelation, SizeChange, SizedType, LinearLexicographic,
ExternalChecked, AssertTerminatesUnverified, AssertReducibleUnverified). Grep
shows neither enum nor a mapping is defined anywhere else (the first list
appears only at 36830-36831; §15 defines neither). It is unspecified which
termination kind a SizedType, LinearLexicographic, or ExternalChecked
certificate yields (presumably `well-founded`, but SizedType is arguably
distinct), and whether SemanticStructural maps to `structural`. Since both
values are mandatory interface-artifact content that feeds §33 hashing and
downstream conversion-reducibility decisions, divergent mappings produce
interoperability-relevant divergent interfaces for the same program.

> L36829-36831: "the termination kind (`structural`, `well-founded`, `size-
change`, `non-recursive`, `verified-assertTerminates`, or `assertReducible-
unverified`)" vs L36895-36905: "the accepted strategy kind: * `Structural` *
`SemanticStructural` * `NatMeasure` * `WellFoundedRelation` * `SizeChange` *
`SizedType` * `LinearLexicographic` * `ExternalChecked` *
`AssertTerminatesUnverified` * `AssertReducibleUnverified`"

**Possible fix:** Add a normative mapping table to §34.1.9:
Structural/SemanticStructural → structural;
NatMeasure/WellFoundedRelation/SizedType/LinearLexicographic/ExternalChecked →
well-founded; SizeChange → size-change; non-recursive definitions → non-
recursive; AssertTerminatesUnverified later verified per §15.1(2) → verified-
assertTerminates; AssertReducibleUnverified → assertReducible-unverified.

## 63. §8.3.1 vs §8.5.3: `import M.(type T(..))` for an opaque data type: error or silent type-only import is unspecified

**ambiguity** · severity **low** · verification: **confirmed** · Spec.md lines
6796, 7355-7358

§8.3.1 defines `type T(..)` as importing 'the type `T` together with all
constructors declared by `T`'. §8.5.3 says the constructors of an `opaque
data` type 'are not exported' and are not name-resolvable outside the defining
module. Neither section says what `import M.(type Rope(..))` does when `Rope`
is opaque: one conforming implementation rejects the import item (it names
unavailable constructors — 'all constructors declared by T' cannot be
imported), another silently imports the type facet with zero constructors
(reading `(..)` as 'all exported constructors'). Observable divergence:
acceptance vs rejection of the program. The same question applies to `export
M.(type T(..))` re-exports (§8.4, line 7242-7243). Grep over the spec finds no
rule connecting `ctorAll` to opacity.

> line 6796: "* `type T(..)` imports the type `T` together with all
constructors declared by `T`." lines 7356-7357: "The constructors of Rope are
not exported. Outside the defining module, Rope's constructors are not name-
resolvable, including through dotted static-member selection on the type"

**Possible fix:** Add to §8.3.1: '`type T(..)` imports the type `T` together
with all constructors of `T` that are exported by `M`. If `T` is an `opaque
data` type whose constructors are not exported, `type T(..)` imports only the
type facet and the implementation MUST emit a warning (or, alternatively, a
compile-time error) noting that no constructors are available.' Pick one
behavior and state it; mirror the choice for `export` in §8.4.

## 64. §T.5.1: assertDiagnosticFixCompiles escape clause references 'follow-up assertions for the fixed source' that no directive can express

**incompleteness** · severity **low** · verification: **confirmed** · Spec.md
lines 46611-46614

T.5.1 says assertDiagnosticFixCompiles 'succeeds iff the fix applies cleanly
and the recompilation produces no error diagnostics unless the test explicitly
contains follow-up assertions for the fixed source.' No mechanism anywhere in
Appendix T (grep: 'follow-up assertion' occurs only at line 46614) lets a test
attach assertions to the post-fix recompilation — all other assertions are
evaluated against the original suite's diagnostic multiset. A harness cannot
know what syntactic form marks an assertion as targeting the fixed source, nor
what success means in that case (are the ordinary assertions re-evaluated
against the fixed compilation? both?). Conforming harnesses will implement
incompatible or no behavior for the clause.

> L46611-14: "then recompiles the resulting test source under the same test
configuration. It succeeds iff the fix applies cleanly and the recompilation
produces no error diagnostics unless the test explicitly contains follow-up
assertions for the fixed source."

**Possible fix:** Either delete "unless the test explicitly contains follow-up
assertions for the fixed source" (making the assertion always require an
error-free fixed compilation), or define a concrete mechanism, e.g. a
directive `assertFixedSource <assertion...>` whose payload is a standard
diagnostic assertion evaluated against the post-fix recompilation's diagnostic
multiset.

## 65. §T.5.2 vs §T.6: assertType in suite.ktest has no defined name-resolution environment

**ambiguity** · severity **low** · verification: **confirmed** · Spec.md lines
46681-46687, 46826-46828

T.5.2 says '`<name>` is resolved by ordinary name resolution in the test
suite' and '<typeExpr>` is parsed as a type expression in the ordinary type
grammar', and T.6 permits assertType to appear in `suite.ktest`. Ordinary
Kappa name resolution is scoped to a module's import environment, but a
`suite.ktest` file has no module, no imports, and no lexical scope, and a
directory suite contains many modules. It is unspecified whether an
unqualified `<name>` resolves against the union of all suite modules' top-
level declarations, only fully qualified names are meaningful, or some
designated root module's scope applies — and the same question applies to type
constructors inside `<typeExpr>` (e.g. does `String` resolve without the
prelude when `noPrelude` is set?). Two conforming harnesses can disagree on
whether an assertType directive is ill-formed-ambiguous or succeeds.

> L46683: "`<name>` is resolved by ordinary name resolution in the test
suite." — L46826-28: "suite-wide assertions such as `assertType`,
`assertStageDump`, and diagnostic assertions may appear inline or in
`suite.ktest`."

**Possible fix:** Specify: "In `suite.ktest`, `<name>` and every name in
`<typeExpr>` MUST be fully qualified module paths resolved against the suite's
effective modules plus the prelude (when implicit prelude is enabled). In an
inline `.kp` directive, names resolve in the lexical scope at the end of the
containing file."

## 66. Appendix G.1-G.2 vs §18.2.6 vs §14.1: ApplicativeDo: no Monad/Applicative agreement law, and Appendix G.2's syntactic license contradicts §18.2.6's observational-equivalence proviso

**contradiction** · severity **low** · verification: **weakened** · Spec.md
lines 46010, 46013-46023, 20654-20657, 14079-14102

The Applicative trait (§14.1) carries the four applicative laws and the Monad
trait carries left/right identity and associativity, but NO law anywhere
requires liftA2/<*> to agree with >>=-based sequencing (verified by grep: no
coherence/agreement law exists). G.1 only requires that a Monad instance
'determine' an Applicative instance, not that they agree. §18.2.6 permits the
applicative elaboration only 'provided the result is observationally
equivalent to the monadic desugaring', whereas Appendix G.2 states
unconditionally that a do block 'may be elaborated using only Applicative (not
Monad) when all of the following hold' — purely syntactic conditions. For a
lawful carrier whose Applicative sequences effects differently from its Monad
(e.g. a parallel/validation-style applicative — fully permitted by the stated
laws), G.2 licenses an elaboration that §18.2.6 forbids; two conforming
implementations produce observably different programs from the same
dependency-free do block. Additionally, for Applicative-only carriers (no
Monad instance) the monadic desugaring does not exist, so §18.2.6's
equivalence condition is vacuous and G.2's 'may' makes even ACCEPTANCE of such
do blocks implementation-dependent: a conforming implementation may reject
every Applicative-only do block.

> L46010: "`Monad` refines `Applicative`: any `Monad m` instance MUST also
determine an `Applicative m` instance for the same `m`." — L46015: "A `do`
block may be elaborated using only `Applicative` (not `Monad`) when all of the
following hold:" — L20656-7: "implementations MAY instead elaborate
independent groups using only `Applicative` operations such as `liftA2` /
`<*>`, provided the result is observationally equivalent to the monadic
desugaring."

*Verifier caveat (why this is weakened):* Quotes accurate, and the factual
core holds: grep confirms no <*>=ap / liftA2-vs->>= agreement law anywhere
(contrast Ord, which DOES get explicit compareEqSound/compareEqComplete
agreement members at L14226-14228, showing the spec knows how to pin agreement
and omitted it for Monad). But the claimed high-severity CONTRADICTION fails
under the charitable harmonized reading: §18.2.6 (L20655-57) explicitly cross-
references 'do blocks satisfying the conditions of Appendix G' and adds the
governing …

**Possible fix:** Add a coherence law member to the Monad trait (or a
normative rule in G.1): for any type with both instances, `liftA2 f x y = x
>>= \a -> y >>= \b -> pure (f a b)` (equivalently `<*> = ap`). Then in G.2:
(a) state that for carriers with a Monad instance the applicative elaboration
is subject to §18.2.6's observational-equivalence condition (now guaranteed by
the new law); (b) for Applicative-only carriers, make the G.2 elaboration
normative (a conforming implementation MUST accept and elaborate qualifying
blocks with the shown liftA2 scheme, preserving source order of the <- binds).

## 67. §11.1.3 vs §11.3.3: §11.1.3 forbids defaulting classifier-determining metavariables; §11.3.3 defaults unconstrained parameter annotations to `Type`

**contradiction** · severity **low** · verification: **weakened** · Spec.md
lines 9075-9077 vs 10010-10013, 10027

§11.1.3's kind/classifier bullet says a metavariable that determines whether a
binder ranges over `Type u`, `RecRow`, `EffRow`, etc. "MUST NOT be defaulted"
and enumerates its only outcomes as solved-by-context, generalized, or
rejected — an exhaustive list that excludes defaulting-by-explicit-rule
(unlike the section's General rule, which allows it). §11.3.3 then says an
unannotated header parameter whose annotation "is otherwise unconstrained ...
defaults to `Type`". For a genuinely unconstrained parameter — e.g. the
phantom `a` in `data Phantom a : Type = MkPhantom`, where nothing determines
whether `a` ranges over `Type`, `RecRow`, or `EffRow` — the two rules give
opposite verdicts: reject/generalize versus silently default to `Type`.
Implementations following the stricter rule reject common phantom-parameter
declarations that the other rule accepts.

> lines 9075-9077: "A metavariable whose classifier would determine whether a
binder ranges over `Type u`, `RecRow`, `VarRow`, `EffRow`, `Label`,
`EffLabel`, `Region`, `Quantity`, or another intrinsic compile-time classifier
MUST NOT be defaulted. Such a metavariable must be solved by context,
generalized by an explicit rule, or rejected."; line 10011: "If the annotation
is otherwise unconstrained, it defaults to `Type`."

*Verifier caveat (why this is weakened):* Quotes accurate (9075-9077, 10011,
10027), and the literal three-option list in the classifier bullet does
exclude defaulting. But the section's own General rule (9055-9057) expressly
permits defaulting 'according to an explicit defaulting rule in this
specification', and the Quantity bullet (9094-9097) establishes the spec's
intended pattern: elaboration-internal metavariables are never defaulted,
while explicit source-grammar defaults for omitted syntax (the ω quantity
default) are fine. §11.3 …

**Possible fix:** In §11.1.3's kind-and-classifier bullet, append: 'except
where §11.3.3 explicitly supplies the `Type` default for unannotated
declaration parameters and implicitly universalized identifiers; that rule is
the sole classifier-defaulting rule of this specification.'

## 68. §13.1.1/§13.1.5 vs §11.3.1: Closed unions with type-variable members: no distinctness obligation, and 'duplicate-free' vs 'duplicate removal' conflict under instantiation

**ambiguity** · severity **low** · verification: **weakened** · Spec.md lines
12250, 12336, 9833

Open rows get an explicit freshness side condition (`LacksVar r a`), but
nothing generates pairwise-distinctness obligations for the explicitly listed
members of a *closed* union such as `(| Int | a |)` or `(| a | b |)`.
Instantiating `a := Int` produces a row with two members of equal MemberId.
§11.3.1 says 'VarRow is a finite duplicate-free collection of member types'
(suggesting the instantiation is ill-formed), while §13.1.1 says row equality
is 'modulo permutation and duplicate removal by MemberId' (suggesting the row
silently collapses to `(| Int |)`). Neither section says which applies at
instantiation sites. Under the collapse reading, in `g : forall a. (| Int | a
|) -> Bool` with arms `case (| n : Int |) -> True` and `case (| x : a |) ->
False`, at `a := Int` both arms carry the same TagId, so the second arm is
silently dead and every value — including ones injected via the `a` member —
takes the Int arm (§32.1 top-to-bottom). Under the duplicate-free reading, the
instantiation `g @Int` must be rejected, but no rejection mechanism or
diagnostic is specified. Two conforming implementations observably diverge
(reject vs accept-with-collapse).

> 12250: "Row equality for `VarRow` is modulo permutation and duplicate
removal by `MemberId`." — 9833: "`VarRow` is a finite duplicate-free
collection of member types." — 12336: "The constraint `LacksVar r a` ensures
`a` is not already present in the row, preventing ambiguous overlaps at use
sites."

*Verifier caveat (why this is weakened):* Quotes accurate (12250, 9833, 12336)
and no section generates distinctness obligations for closed-union members
(grepped pairwise/distinct/collision/overlap). But the claimed accept-vs-
reject divergence rests on an uncharitable reading of 9833: §11.3.1's 'VarRow
is a finite duplicate-free collection' describes the normalized row domain,
and 12250's 'row equality is modulo permutation and duplicate removal by
MemberId' is the operative normative rule — so under instantiation `a := Int`,
`(| Int | …

**Possible fix:** Pick one behavior and state it in §13.1.1: either (a)
'Instantiating a union type so that two listed members acquire equal MemberId
is well-formed; the row normalizes by duplicate removal and match arms for the
collapsed member dispatch top-to-bottom per §32.1' (and add a reachability
warning family for the dead arm), or (b) 'Elaboration of a closed union type
generates a pairwise `LacksVar`-style distinctness obligation between every
two listed members that are not already distinguishable by MemberId;
instantiations violating it are rejected with kappa.variant.member-collision.'
Also reword §11.3.1's 'duplicate-free collection' to 'collection normalized by
duplicate removal' if (a) is chosen.

## 69. §15.10 vs §15.16 (and §15.11 minimum acceptance): §15.10 source-order hidden phase makes SCC acceptance order-dependent, against §15.16's reordering-invariance MUST

**ambiguity** · severity **low** · verification: **weakened** · Spec.md lines
15380-15385, 15488-15495, 15661-15662

The canonical hidden phase is assigned by source order ('first by normalized
source path, then by increasing source start offset'), and a call may preserve
the visible measure only toward a strictly smaller phase. Take SCC {f, g}
where f's call to g preserves the visible measure and g's call to f strictly
decreases it: declared f-before-g it is accepted by the canonical scheme (and
MUST be accepted per §15.11 minimum acceptance); declared g-before-f the f→g
edge targets a larger phase, so a minimal conforming implementation rejects
it. §15.16 says 'Reordering members within one semantic SCC MUST NOT change
accepted/rejected status, except where the source language explicitly defines
source-order behavior' — the spec never states whether §15.10's phase
assignment falls under that exception. Reading 1: exception applies, so
acceptance is legitimately order-dependent (and §15.16's guarantee is hollow
for termination). Reading 2: exception does not apply, so a minimal
implementation implementing exactly the required §15.10 scheme violates
§15.16. Conforming implementations observably diverge on the reordered
program.

> 15382-15384: "let the SCC members be ordered by deterministic source-origin
order: first by normalized source path, then by increasing source start offset
within that file" — 15661-15662: "Reordering members within one semantic SCC
MUST NOT change accepted/rejected status, except where the source language
explicitly defines source-order behavior."

*Verifier caveat (why this is weakened):* Quotes accurate (15382-15385,
15661-15662). But §15.16's MUST carries the exact exception needed: 'except
where the source language explicitly defines source-order behavior' — and
§15.10 is precisely a place where the language explicitly defines behavior by
source order ('first by normalized source path, then by increasing source
start offset', 15382-15384). The charitable and natural reading is that §15.10
instantiates the exception, so both minimal implementations behave identically
(reject th …

**Possible fix:** Best fix: make §15.10 order-insensitive — replace the
canonical source-order phase with 'the SCC is accepted by the hidden-phase
scheme iff the subgraph of recursive calls that preserve every visible measure
component is acyclic; any topological order of that subgraph defines the
phases.' (Polynomial to check and reorder-invariant.) Minimal fix: add to
§15.10 and §15.16: 'The canonical hidden phase component is an explicitly
source-order-defined behavior and is exempt from the reordering-invariance
requirement of §15.16.'

## 70. §17.1.8 vs §17.3.3: §17.1.8 'narrowing is non-consuming' blanket statement for `match e` contradicts §17.3.3 consuming active-pattern threading

**contradiction** · severity **low** · verification: **weakened** · Spec.md
lines 18096-18106 vs 18481-18516

§17.1.8 states without qualification that evaluating a scrutinee for `match e`
never consumes it, even at quantity 1, and that 'Each branch is checked
independently with the original scrutinee still available at its original
quantity'. §17.3.3 specifies the opposite for matches whose cases are `Match a
r` active patterns: the scrutinee is consumed by the active-pattern call ('If
an active pattern consumes a scrutinee at quantity 1 and may fail, it MUST
return Match a r'), and subsequent branches are checked against the threaded
Miss residue, not the original scrutinee. An implementer following §17.1.8's
letter would keep `buffer` available in every branch of a threaded match,
permitting double consumption of a linear resource; following §17.3.3
contradicts §17.1.8's 'each branch ... original scrutinee still available'.
The intended scope of §17.1.8 (structural constructor/literal discrimination
only) is not stated.

> 18098-18099: "Evaluating a scrutinee for `if e is C` or `match e` does not
by itself consume the scrutinee, even when that scrutinee is available at
quantity `1`." — 18101: "Each branch is checked independently with the
original scrutinee still available at its original quantity" — 18481-18482:
"If an active pattern consumes a scrutinee at quantity `1` and may fail, it
MUST return `Match a r`"

*Verifier caveat (why this is weakened):* The quoted lines are accurate, but
the contradiction only arises by reading §17.1.8's bullets out of their
scoping context. The section opens with 'Constructor discrimination is
observational only' (18094) — every rule in it elaborates that framing (branch
selection borrows the scrutinee, refined components, borrowed projections) —
and the more specific sections explicitly govern active patterns: §17.3.6
states 'Active patterns are functions, so their scrutinee parameters obey the
ordinary quant …

**Possible fix:** Scope §17.1.8 explicitly: change the first two rules to
'Evaluating a scrutinee for `if e is C` or for the structural (constructor,
literal, tuple, record, variant) cases of `match e` does not by itself consume
the scrutinee ...' and add: 'Cases headed by active patterns are ordinary
function applications of the scrutinee and are governed by §§17.3.2-17.3.6,
not by this section.'

## 71. §18.6.1 facet 4, §18.9.3-§18.9.5 vs §12.2.6, §30.2.2.1: "Consuming cell operation" and the var-place take/write-back discipline are referenced but never defined

**incompleteness** · severity **low** · verification: **weakened** · Spec.md
lines 21186-21193, 21332-21339, 22341-22343, 22521-22529, 33205-33209 (and
11522)

§18.6.1 says a mutable-variable read is a duplication position (rejected when
the stored value has a non-duplicable component) and that writes "discard the
previous stored value unless a more specific consuming cell operation is
selected" — but grep over the whole spec finds no consuming cell operation
ever specified (no take/swap/modify form; the only two mentions are lines
11522 and 21338, both deferring to an unnamed "specified"/"selected"
operation). The var-place facet (§18.6.1 facet 4) that `~x` uses is defined
only as "a special read/modify/write discipline over the hidden cell" subject
to "the same ... rules as the corresponding lower-level cell operations", and
§30.2.2.1 (line 33205-33209) likewise defers to "the corresponding
read/modify/write sequence". Failure scenario: §18.9.5's own example `do { var
file = initialFile; let (data = bytes) <- read ~file 1024 }` where `read
(inout f : File Open)` consumes `f` at quantity `1`: if `File Open` is non-
duplicable, the readRef-based reading of the current value duplicates it
(forbidden by 21332-21336), so one conforming implementation rejects the
program; another treats `~file` as an unspecified take-then-fill move and
accepts it. And under the accepting reading, the cell's contents between the
take and the write-back — observable if the call fails with a monadic error or
is interrupted, so write-back never happens — are entirely unspecified.

> line 21338-21339: "Recognized writes and assignments discard the previous
stored value unless a more specific consuming cell operation is selected." —
line 21190-21193: "It is a special read/modify/write discipline over the
hidden cell and is subject to the same quantity, droppability, duplicability,
and write-back rules as the corresponding lower-level cell operations." (grep
for `takeRef|swapRef|consuming cell operation` yields only the two deferring
mentions, no definition)

*Verifier caveat (why this is weakened):* The grep result is accurate —
'consuming cell operation' appears only at ln 11522 and 21338, and the
required MonadRef API (ln 21101-21106, 29941-29945) has no take/swap. But the
spec does pin the var-place discipline, so the claimed implementation
divergence doesn't follow: §18.6.1 facet 4 (ln 21190-21192) makes `~x`
'subject to the same quantity, droppability, duplicability, and write-back
rules as the corresponding lower-level cell operations'; §30.2.2.1 (ln
33205-33209) requires observable e …

**Possible fix:** Define the var-place discipline normatively in
§18.6.1/§18.9.4: either (a) restrict `~x` on var-rooted places to cells whose
stored value is duplicable and whose overwritten value is droppable (making
the discipline definable as readRef + writeRef and rejecting the linear-
typestate-in-var case), or (b) introduce a KCore-level consuming cell
operation (e.g. `TakePlaceRef : Ref A -> m A` marking the cell logically empty
until the paired `FillPlaceRef`) and specify that a monadic error or
interruption between take and fill propagates before any further access to the
cell is possible (the cell's binder scope ends with the scope's unwinding).

## 72. §2.1: Owning-gate selection depends on an undefined 'weakest/stronger' ordering on feature gates

**ambiguity** · severity **low** · verification: **weakened** · Spec.md lines
317-324, 361-367

The owning-gate rule mandates 'Every gated surface construct ... has exactly
one owning gate' and selects it as 'the weakest gate that supplies all
semantic consequences needed by that occurrence', with 'a stronger owning
gate' required for stronger consequences. No ordering on gates is defined
anywhere: grep shows 'weakest' occurs only at line 321, and §2.1's implication
machinery ('One feature gate MAY imply another only when this specification or
the selected build profile explicitly states that implication') is never
connected to gate strength. For a surface form shared by two independent
extension gates neither of which implies the other but each of which supplies
all needed consequences, 'the weakest gate' does not exist and 'exactly one
owning gate' is unsatisfiable/undetermined. Observable divergence: with
exactly one of the two gates active, one conforming implementation accepts the
construct (chose that gate as owner) and another rejects it with
kappa.feature.gated naming the other gate; the mandated diagnostic payload
('owning feature gate') and repair suggestion also differ.

> L317-321: '* Every gated surface construct, elaboration rule, typing rule,
effect rule, backend requirement, and standard-library surface has exactly one
**owning gate**.\n* If a surface construct is syntactically shared by several
features, the owning gate is the weakest gate that supplies all semantic
consequences needed by that occurrence.'

*Verifier caveat (why this is weakened):* True that 'weakest' occurs only at
L321 and no formal gate ordering is defined. But the charitable (and natural)
reading makes the rule a designation principle, not an implementation
algorithm: strength is consequence-inclusion (L323-324 and L2026 tie
'stronger/weaker' to 'semantic consequences required by the occurrence'), and
for every standardized gated construct the spec explicitly designates the
owner in that construct's section (e.g., §2.1A L412: 'This gate owns all of
the following semant …

**Possible fix:** Add to §2.1: 'Gate A is weaker than gate B iff the active
profile's stated implications give B implies A. When several implication-
minimal gates each supply all required semantic consequences of an occurrence,
the owning gate is the one this specification designates for that construct;
if none is designated, the occurrence is accepted iff at least one such gate
is active, and diagnostics MUST list all candidate gates.'

## 73. §2.1A vs §2.1 owning-gate rule vs §5.1/§5.1A/§3.1.3: unicode-names gate 'owns' name-key/visual-duplicate/name-profile machinery that is simultaneously mandated when the gate is inactive (backtick identifiers)

**contradiction** · severity **low** · verification: **weakened** · Spec.md
lines 417-419, 428-431, 313-315, 4576-4580

§2.1A states the `unicode-names` gate owns, among other consequences:
'Unicode-aware identifier and operator name keys under §5.1A', 'Unicode-aware
visual-duplicate binding checks under §7', and 'Unicode name-profile
diagnostics under §3.1.3'. §2.1's owning-gate rule says 'Successful
elaboration MUST check the construct against the feature gate that owns its
semantic meaning. If the owning gate is inactive, compilation fails with a
feature-gating diagnostic.' But §2.1A itself and §5.1 (lines 4576-4580)
require that with `unicode-names` INACTIVE, a backtick Unicode identifier like
`` `λ` `` 'remains syntactically available' and 'Its lookup behavior,
diagnostics, normalization checks, visual duplicate checks, and generated-name
metadata are still governed by §5.1A and §7' — i.e., the very semantic
consequences the inactive gate owns must be applied. Taken literally, the
owning-gate rule rejects every backtick Unicode identifier when the gate is
off; taken the other way, an implementation may skip §5.1A Unicode-aware keys
and visual-duplicate checks for backticks when the gate is off. Observable
divergence: whether `let A = 1` plus a backtick Greek-alpha binding in the
same scope produces E_UNICODE_VISUAL_DUPLICATE_BINDING under an inactive gate,
and whether non-normalized backtick names are checked at all.

> L417-419: '* Unicode-aware identifier and operator name keys under §5.1A;\n*
Unicode-aware visual-duplicate binding checks under §7;' ... L313-315:
'Successful elaboration MUST check the construct against the feature gate that
owns its semantic meaning. If the owning gate is inactive, compilation fails
with a feature-gating diagnostic.' L4579-4580: 'Its lookup behavior,
diagnostics, normalization checks, visual duplicate checks, and generated-name
metadata are still governed by §5.1A and §7.'

*Verifier caveat (why this is weakened):* The quoted texts are accurate, but
the contradiction only arises by reading the §2.1A ownership list (L412-421)
in isolation from the backtick carve-out two paragraphs later in the SAME
section: L428-431 'Backtick identifiers remain available independently of
unicode-names ... Unicode normalization, visual-duplicate checks, bidi-control
checks, and confusable diagnostics still apply.' The §2.1 owning-gate
rejection (L314-315) fires only for constructs a gate owns; backticks are
explicitly declar …

**Possible fix:** In §2.1A, restrict the owning-gate list to unquoted forms:
replace the three list items with 'Unicode-aware name keys, visual-duplicate
checks, and name-profile diagnostics for UNQUOTED Unicode identifiers and
Unicode operator tokens', and add one sentence: 'The §5.1A name-key
computation, §7 visual-duplicate checks, and §3.1.3 diagnostics apply to
backtick identifiers unconditionally; they are not gated by unicode-names.'

## 74. §20.8 vs §20.6.3 and §20.10.3: Join lowering's fresh `tmp` binding leaks into Row(Ξ), making `distinct` (and Eq (Row(Ξ))) after a join ambiguous

**ambiguity** · severity **low** · verification: **weakened** · Spec.md lines
23664-23674, 23412-23418, 24076-24077

§20.8's normative lowering of `join pat in xs on cond` is `for tmp in xs, let?
pat = tmp, if cond` with `tmp` a binding introduced by a clause; `tmp` is not
removed from the row afterwards (for an ω element it is not consumed by the
`let?`). §20.10.3 defines Ξ as 'the ordered quantitative row context of names
bound by preceding clauses', and §20.6.3 defines bare `distinct` as
deduplication on `Row(Ξ)` requiring `Eq (Row(Ξ))`. So for a comprehension `for
a in as, join (x, _) in ps on cond, distinct, yield ...`, one conforming
reading (surface: §20.8 says only pat's bindings are in scope) dedups on (a,
x); the other (normative lowering: tmp is a bound name of a preceding clause)
dedups on (a, x, tmp), i.e. including the ignored second pair component —
observably different results and a different Eq constraint (Eq on the whole
joined element). The spec's 'observationally equivalent' framing cannot
resolve this because Row(Ξ) itself is what determines the observation.

> L23666-23670: "`join pat in xs on cond` is observationally equivalent to:\n
for tmp in xs\n let? pat = tmp\n if cond" ... L24077: "let `Ξ` be the ordered
quantitative row context of names bound by preceding clauses" ... L23418:
"`distinct` keeps the first encountered row for each unique current
quantitative row record `Row(Ξ)`."

*Verifier caveat (why this is weakened):* The semantics are not actually
ambiguous: §20.8's own 'Type and scope rules' (L23689-23690) state that in
`join` 'the bindings introduced by pat are in scope in later clauses exactly
as for other successful row extensions' — identifying join's row extension as
pat's bindings; §20.10.3 (L24077) builds Ξ from 'names bound by preceding
clauses' of the surface program, and tmp is a fresh schematic name in an
observational-equivalence statement, not a binding of any written clause (nor
could a user s …

**Possible fix:** Add to §20.10.3 (or §20.8): 'Ξ contains exactly the surface-
visible bindings of the written clauses. Fresh names introduced by normative
lowerings (such as the join temporary `tmp`) are not entries of Ξ and do not
participate in Row(Ξ), distinct, or Eq (Row(Ξ)) requirements.'

## 75. §22.6: constructAdt: acceptance of an argument list that entirely omits an implicit field is unspecified

**ambiguity** · severity **low** · verification: **weakened** · Spec.md lines
26038-26049

The acceptance condition for `constructAdt shape ctor args` is an 'iff' over
five bullets. Non-implicit fields must have exactly one SuppliedFieldArgument,
but for implicit fields the only rule is 'an implicit field may either be
supplied explicitly or represented by OmittedImplicitFieldArgument' — which
reads both as a permission (absence also fine, treated as omitted) and as an
exhaustive two-way requirement (an entry is mandatory). A derivation macro
passing `[]` for a constructor with an implicit evidence field is accepted by
one conforming implementation (generates syntax letting implicit insertion
solve it) and rejected with KAPPA_DERIVING_SHAPE_BAD_CONSTRUCTOR_ARGUMENTS by
another — observably divergent behavior for portable macro packages.

> 26039: "The argument list is accepted iff, after grouping by field
identity:"; 26043: "* an implicit field may either be supplied explicitly or
represented by `OmittedImplicitFieldArgument`;"

*Verifier caveat (why this is weakened):* Quotes accurate (26039, 26043).
However, the literal reading of the 'accepted iff' bullet list yields a unique
answer: an entirely absent implicit field violates none of the five bullets —
bullet 1 (26041) constrains only non-implicit fields, bullet 3 (26043) is a
permission ('may either'), and bullets 4-5 (26044-26045) are unaffected — so
an empty argument list for an implicit-only constructor is accepted, and
26047's 'For an omitted implicit field, the generated syntax omits the
corresponding …

**Possible fix:** Add one sentence to §22.6: "An implicit field with no
corresponding argument is treated as if `OmittedImplicitFieldArgument` had
been supplied for it." (Or, if strictness is intended: "Every implicit
constructor field MUST appear exactly once in the argument list, either
supplied or omitted.")

## 76. §27.6 (Foreign-call interruption classification): blocking-cancellable cancellation 'MUST attempt ... at most once' permits zero attempts, silently downgrading to plain blocking

**ambiguity** · severity **low** · verification: **weakened** · Spec.md lines
29063-29064, 29070-29071

'MUST attempt the documented safe cancellation mechanism at most once' is
literally satisfied by never attempting cancellation. A conforming runtime may
therefore treat every `blocking-cancellable` call exactly like `blocking`
(interruption pending until natural return), while another attempts prompt
cancellation — an observable divergence (prompt fiber interruption vs.
indefinite hang until the foreign call completes). This zero-attempt reading
also contradicts the same section's rule that a backend that 'cannot realize
the documented safe cancellation mechanism MUST reject that foreign
declaration or deployment rather than silently downgrading it': a backend that
CAN cancel but chooses not to has achieved precisely the silent downgrade that
rule forbids.

> 29063-29064: "If a fiber is interrupted while executing a `blocking-
cancellable` call, the runtime MUST attempt the documented safe cancellation
mechanism at most once."; 29070-29071: "A backend that cannot realize the
documented safe cancellation mechanism MUST reject that foreign declaration or
deployment rather than silently downgrading it."

*Verifier caveat (why this is weakened):* Quotes accurate (29063-29064,
29070-29071) and the literal 'at most once' does state only an upper bound.
But the immediately following rules close the loophole under any charitable
reading: 29065 'The cancellation attempt is best-effort...' uses the definite
article, presupposing an attempt; 29066-29067 enumerate only failure modes of
an attempt made ('unavailable, refused, races with normal completion'); and
29082-29083 make the documented cancellation mechanism 'part of the required
runtime c …

**Possible fix:** Replace with: "the runtime MUST attempt the documented safe
cancellation mechanism, and MUST NOT attempt it more than once." (If
deliberate latitude is intended for races with normal completion, say instead:
"MUST attempt ... unless the call has already completed, and MUST NOT attempt
it more than once.")

## 77. §28.1 vs §28.2.3 (and §16.1.3): `and`/`or` must parse out of the box per §28.1, but the normative minimum fixity table omits them, so precedence is implementation-chosen and the same source parses differently

**ambiguity** · severity **low** · verification: **weakened** · Spec.md lines
29198-29199, 31099-31117

§28.1 requires the prelude to include fixity declarations for `and` and `or`
so they parse "out of the box". §28.2.3 then gives a table introduced as "The
following minimum table is normative" that pins precedences for `(&&)` (right
30) and `(||)` (right 20) but says nothing about `and` and `or` (grep for `and
:`/`or :` finds no type declaration either; §16.1.3 line 16204-16205 only says
they "remain ordinary terms"). Two conforming implementations can therefore
parse `a and b or c` as `(a and b) or c` or as `a and (b or c)` — an
observable behavioral divergence for a term the spec itself names as expected-
to-parse. The types of `and`/`or` (strict `Bool -> Bool -> Bool` vs
suspension-taking like `(&&)`) are also never stated, though §28.2 lists them
in the normative term minimum.

> line 29198-29199: "fixity declarations for any operator tokens that the
implementation expects to parse \"out of the box\" (e.g. `+`, `*`, `==`,
`and`, `or`, `..`, `..<`)"; line 31100: "The following minimum table is
normative:" (table lists `(&&)`, `(||)` but not `and`, `or`)

*Verifier caveat (why this is weakened):* Quotes accurate (29198-29199 lists
`and`, `or` as example 'operator tokens'; §28.2.3 table 31102-31117 omits
them; §28.2 term list 29401 requires `and, or`). But the headline failure
scenario is impossible: §5.5.1 (line ~4913ff) says operator tokens are
sequences of operator characters that MUST exclude 'alphanumeric characters'
and 'identifier-start and identifier-continue characters', and §5.5.2 fixity
declarations bind only to operator tokens, with §5.5.3 infix gating requiring
such a fixity …

**Possible fix:** Add two rows to the §28.2.3 normative fixity table: `and :
infix right 30` and `or : infix right 20` (mirroring `&&`/`||`), and add
canonical declarations in §28.2 pinning their types (e.g. `and : Bool -> Thunk
Bool -> Bool`, `or : Bool -> Thunk Bool -> Bool`, or explicitly strict
variants).

## 78. §3.1.2A vs §3.2.12 and §21 macro-diagnostic rule: Package/macro-owned diagnostic codes must be 'registered' but the only defined registry is the implementation's, whose entry schema cannot describe them

**incompleteness** · severity **low** · verification: **weakened** · Spec.md
lines 681-714, 689-701

§3.1.2A requires: 'A conforming implementation MUST publish a machine-readable
diagnostic code registry for every diagnostic code that may be emitted', 'The
registry MUST be available without compiling an invalid program', and 'A
diagnostic emitted in ordinary user-facing compilation MUST NOT use an
unregistered code'. Macros may define their own diagnostic codes (§3.2.12
payload: 'macro-defined diagnostic code when provided'; line 25584: 'A macro-
defined diagnostic MUST use a registered package-owned diagnostic code'), but
the spec never defines how a package-owned code becomes registered: the only
registry defined is the implementation's, whose entry schema requires
`introducedIn : ImplementationVersion` — meaningless for a code introduced by
a third-party package — and the emittable-code set becomes open-ended, making
the publish-for-every-code MUST unimplementable as stated. `kappa explain
<code>` must also 'reject unknown diagnostic codes deterministically', which
is undefined for codes known only to a package in some build. Implementations
will invent divergent package-registry mechanisms.

> L681-684: 'A conforming implementation MUST publish a machine-readable
diagnostic code registry for every diagnostic code that may be emitted outside
verbose internal-compiler tracing.\n\nThe registry MUST be available without
compiling an invalid program.' L714: 'A diagnostic emitted in ordinary user-
facing compilation MUST NOT use an unregistered code.'

*Verifier caveat (why this is weakened):* Quotes accurate, and the
registration FLOW for package codes is indeed never spelled out. But the
finding overlooks machinery that covers most of the gap: registry entries
carry owner : DiagnosticCodeOwner (L700) and L724 requires package/macro-
defined families to 'use a package-qualified owner identity'; §21 L25526-25528
REQUIRES 'constructors or checked smart constructors for package-defined
diagnostic codes and families' that 'MUST attach an owner identity' — the
checked constructor is the re …

**Possible fix:** Add to §3.1.2A: 'Package- or macro-owned diagnostic codes
are registered by the owning package: the package artifact MUST carry
DiagnosticRegistryEntry records for every code its macros may emit, with
`introducedIn` interpreted as the owning package version, and the
implementation's registry query and `kappa explain` MUST merge entries from
resolved build-plan packages.' Scope the implementation-publishing MUST at
line 681 to implementation-owned codes.

## 79. §3.2.1 vs §2.1: E_FEATURE_PROFILE_INCONSISTENT is a standardized code with no defined triggering condition; profile/gate consistency is never defined

**incompleteness** · severity **low** · verification: **weakened** · Spec.md
lines 2029-2037, 336-342

§3.2.1 tells implementations they SHOULD use the stable code
E_FEATURE_PROFILE_INCONSISTENT 'when the corresponding meaning applies', but
the meaning is never defined: the token appears exactly once in the entire
spec (grep confirms line 2036 is the sole occurrence), and §2.1 — which
defines profiles, gates, and implications — contains no notion of an
inconsistent profile, no rule about whether two active gates (or a stated
implication and an explicitly disabled gate) can conflict, and no rule about
when such a conflict must be detected or reported. Every implementer must
invent both the consistency predicate and the detection point (profile
determination vs elaboration), producing divergent acceptance for build
configurations that, e.g., enable gate A whose stated implication B is
explicitly disabled.

> L2029-2036: 'Implementations SHOULD use the following stable diagnostic
codes when the corresponding meaning applies: ...
E_FEATURE_PROFILE_INCONSISTENT'

*Verifier caveat (why this is weakened):* Factually accurate: the token occurs
exactly once (L2036) and grep finds no definition of profile inconsistency
anywhere (only L46501, an unrelated harness rule). But the defect is smaller
than claimed: the code list is SHOULD-level and conditional ('when the
corresponding meaning applies', L2029), detection of inconsistency is never
mandated anywhere, so no divergent REQUIRED behavior is derivable and no
portable conformance test can assert it. Moreover the finding's example
scenario (gate A im …

**Possible fix:** Add to §2.1 a definition and rule: 'A profile is
inconsistent when its stated implications cannot all be satisfied by the
active gate set, or when the same gate is simultaneously required active and
required inactive by the resolved build plan. A conforming implementation MUST
detect profile inconsistency when it determines the active profile (before
successful elaboration) and reject the compilation unit with
E_FEATURE_PROFILE_INCONSISTENT in family kappa.feature.gated.'

## 80. §31.2 (also mirrored at §25.x line 25964): Function-type erasure rule mixes a per-use condition into a type classification that then drives declaration-site field layout

**ambiguity** · severity **low** · verification: **weakened** · Spec.md lines
35055-35058

The first sentence classifies a *type* as runtime-erased partly by how 'the
function value is consumed' (only in erased ambient-demand positions) — a
property of occurrences, not of the type. The immediately following sentence
then omits from runtime representation every 'record field, constructor field,
trait member, package member, or local binding whose type is runtime-erased' —
a declaration-site layout decision. For a constructor or record field of type
`(x : A) -> Prf x` (with `RuntimeErased (Prf x)`), the consumption condition
is unevaluable at the declaration: the field's values are consumed at
arbitrarily many sites, possibly in other, separately compiled modules. Two
conforming implementations (or the constructing and matching modules within
one implementation) can disagree on whether the field physically exists,
producing incompatible layouts; alternatively an implementation that erases
the field breaks a downstream module that consumes such a function at runtime-
relevant demand. Note §31.2.1 separately forbids elision from changing
exported ABI layout, heightening the tension.

> 35055-35058: "A function type `(q x : A) -> B` is runtime-erased when, under
the extended telescope, the result type `B` is known to satisfy
`RuntimeErased`, and the function value is consumed only in an erased ambient-
demand position. A record field, constructor field, trait member, package
member, or local binding whose type is runtime-erased is omitted from runtime
representation unless explicitly reified by a runtime carrier."

*Verifier caveat (why this is weakened):* Quote accurate (35055-35058) and the
two-sentence structure is genuinely awkward. But the claimed conformance
failure does not materialize under the charitable reading: the rule is a
'when' condition on established knowledge ('known to satisfy'), so a function-
typed field is runtime-erased only where the implementation can PROVE the
consumption condition; for an exported field consumed in separately compiled
modules that proof is unobtainable, forcing retention — both constructing and
matching m …

**Possible fix:** Split the rule: (1) a function type `(q x : A) -> B` is
runtime-erased iff `B` is known to satisfy `RuntimeErased` under the extended
telescope (type-only condition, usable for field omission); (2) the 'consumed
only in an erased ambient-demand position' condition justifies erasing only
individual occurrences/arguments under `AmbientDemandZero`, never declaration-
site fields or members.

## 81. §32.2.13 vs §32.2.20, §32.2.7, §32.2.8: Invoking an escaped resumption from a different fiber has undefined fiber-identity, FiberRef, and supervision-scope semantics

**omission** · severity **low** · verification: **weakened** · Spec.md lines
35634-35637, 35762-35776

§32.2.20 permits a resumption to escape the operation clause when its captured
segment has no pending exit actions, so a resumption can be stored (e.g. in a
Ref or promise) and invoked later from a different fiber. §32.2.13 enumerates
what the captured continuation includes and pins only the interruption-mask
state as carried fiber-local control state; it is silent on everything else
fiber-bound: what `currentFiberId` returns inside the resumed segment, which
fiber's `FiberRef` map is read, which supervision scope a `fork` inside the
resumed segment attaches to, and whose pending interruption request is
observed at the segment's interruption points. A grep for cross-fiber
resumption rules ('another fiber', 'cross-fiber', resumption+escape) finds no
rule. CPS-style backends will naturally run the segment on the invoking fiber
(its id, refs, scope); stack-ownership backends may behave differently or
trap. These are observable, portable-program-visible divergences.

> 35635-35637: "any fiber-local dynamic control state in that segment whose
semantics affect subsequent execution, including the current interruption-mask
state under §32.2.5;"

*Verifier caveat (why this is weakened):* The scenario is reachable (an exit-
action-free, borrow-free resumption may escape per 35774-35776 and cross
fibers via a shared Ref), and no section explicitly addresses cross-fiber
invocation. But the compositional reading answers the headline questions:
§32.2.13 (35630-35645) exhaustively enumerates what the captured continuation
includes — segment-local state only, with the interruption mask the one
explicitly carried item — and everything the finding lists is defined relative
to the executin …

**Possible fix:** Add to §32.2.13: 'A resumption is invoked on the current
fiber of the invoker. Except for the captured interruption-mask state, the
resumed segment executes with the invoking fiber's identity, FiberRef map,
pending-interruption state, and current supervision scope.' (Or, if this is
not intended: 'A resumption value MUST be used only on the fiber that executed
the intercepted operation; use from another fiber terminates the invoking
fiber with a Defect.')

## 82. §32.2.9, §18.1.13: STM retry parking admits lost wakeups: 'changed' has no baseline and orElse's wait set is unspecified

**ambiguity** · severity **low** · verification: **weakened** · Spec.md lines
35501-35502, 19310-19311

Both statements of `retry` say the fiber parks 'until one or more TVars read
by the current attempt have changed', without a baseline or an atomicity
requirement between validation and parking. Reading A (wake if any read TVar
differs from the value the attempt observed, checked atomically with parking)
never loses a wakeup. Reading B (park, then wait for a subsequent change)
permanently deadlocks a transaction when a conflicting commit lands between
the failed attempt's reads and the park — yet is a literal conforming
implementation. Additionally, for `orElse` the spec says only that the right
operand runs when the left retries; it never says whether the parked wait set
includes the abandoned left branch's read set (nor that the left branch's
tentative writes are discarded). An implementation watching only the right
branch's reads never wakes when a left-read TVar changes in a way that would
let the left branch succeed. Both ambiguities produce observably divergent
(hang vs progress) conforming implementations.

> 35501-35502: "`retry` parks the fiber until one or more TVars read by the
current attempt have changed;" ... "transactional choice (`orElse`) runs its
right operand only when the left operand retries;"

*Verifier caveat (why this is weakened):* Quotes accurate (35501-35502,
19310-19311), and no other section elaborates (orElse appears only at
19303/35502; wait sets only named as abstract state at 35279). But both
divergences require uncharitable readings. Lost wakeup: 'parks the fiber until
one or more TVars read by the current attempt have changed' — the perfect
tense is relative to the attempt's reads, so a TVar invalidated between
validation and park already 'has changed' and the parking condition is
discharged; an implementation th …

**Possible fix:** In §32.2.9: '`retry` parks the fiber until at least one TVar
read by the current attempt holds a value different from the value that
attempt observed; this validation is performed atomically with parking, so a
commit that invalidates the attempt before parking completes MUST wake (or
prevent parking of) the fiber. The wait set of a parked transaction includes
the TVars read by every alternative attempted in the transaction, including
`orElse` branches whose tentative writes were discarded; those writes are
never visible to other alternatives or transactions.'

## 83. §34.1.6A vs §34.1.4, §34.2.2: §34.1.6A required checkpoint families and verifier invariants disagree with §34.1.4/§34.2.2: no invariants for STATUS and CHECKERS; IMPLICIT_SIGNATURES and MODAL_SOLVE checkpoints missing entirely

**incompleteness** · severity **low** · verification: **weakened** · Spec.md
lines 36517, 36527-36602 vs 36369-36376, 37193-37214

§34.1.4 requires a named checkpoint for 'each monotone KFrontIR phase of
§34.2.2', which includes IMPLICIT_SIGNATURES, MODAL_SOLVE, and CORE_LOWERING.
§34.1.6A then requires the conformance mode to 'verify every named checkpoint
crossed by the request'. But (a) the 'Required checkpoint families' list omits
KFrontIR.IMPLICIT_SIGNATURES and KFrontIR.MODAL_SOLVE, and (b) the 'Required
verifier invariants' blocks cover only RAW, IMPORTS, DECLARATION_SHAPES,
HEADER_TYPES, BODY_RESOLVE, KCore, and KBackendIR — KFrontIR.STATUS and
KFrontIR.CHECKERS appear in the required family list yet have no defined
invariants at all. Grep confirms no other section supplies verifier invariants
for STATUS, CHECKERS, IMPLICIT_SIGNATURES, or MODAL_SOLVE. So 'verify every
named checkpoint' is uncheckable as stated for four required checkpoints, and
two conforming implementations can disagree on whether a request crossing
MODAL_SOLVE must produce verifier facts for it.

> L36517: "verify every named checkpoint crossed by the request;" ...
L36529-36539 list: "KFrontIR.RAW / KFrontIR.IMPORTS /
KFrontIR.DECLARATION_SHAPES / KFrontIR.HEADER_TYPES / KFrontIR.STATUS /
KFrontIR.BODY_RESOLVE / KFrontIR.CHECKERS / KCore / KBackendIR" vs L36373:
"each monotone KFrontIR phase of §34.2.2"

*Verifier caveat (why this is weakened):* The textual observations are
accurate (family list L36529-36539 omits IMPLICIT_SIGNATURES/MODAL_SOLVE;
invariant blocks L36541-36602 cover neither STATUS nor CHECKERS), but the
'uncheckable'/divergence conclusion does not follow. §34.1.4 L36369-36376
independently names a checkpoint for every §34.2.2 phase, §34.1.6 L36491-36497
requires verification be available at ANY named checkpoint with
implementation-chosen invariants ('the violated invariant' is whatever the
implementation checks), and §34 …

**Possible fix:** Add KFrontIR.IMPLICIT_SIGNATURES and KFrontIR.MODAL_SOLVE to
the required checkpoint-family list (or state in §34.1.6A that checkpoints not
listed verify vacuously), and add minimal 'Required verifier invariants'
blocks for KFrontIR.STATUS (e.g. visibility/opacity/export/gating decisions
recorded as typed records), KFrontIR.CHECKERS (e.g. diagnostics carry required
payloads and deterministic ordering), KFrontIR.IMPLICIT_SIGNATURES, and
KFrontIR.MODAL_SOLVE (e.g. every emitted modality predicate is solved or
reported).

## 84. §34.1.6A vs §34.1.5: §34.1.6A conformance mode requires canonical dumps that §34.1.5 makes optional (SHOULD)

**contradiction** · severity **low** · verification: **weakened** · Spec.md
lines 36507-36518 vs 36417-36419

§34.1.6A says a conforming implementation MUST expose a mode observationally
equivalent to 'check --verify-each --dump-on-failure --canonical-dumps' and
MUST 'emit a canonical machine-readable dump for any checkpoint whose verifier
fails'. But the canonicalized dump mode is defined in §34.1.5 only as a
recommendation ('Implementations SHOULD additionally provide a canonicalized
dump mode ...'). An implementation that follows §34.1.5's SHOULD and omits the
canonicalized mode cannot satisfy §34.1.6A's MUST; conversely §34.1.6A makes
the §34.1.5 SHOULD a de facto MUST. (§3's diagnostic contract also references
'whether a canonical dump was emitted', line 3653.) Implementers cannot tell
whether canonicalized dumps are required for conformance.

> L36417: "Implementations SHOULD additionally provide a canonicalized dump
mode that omits, redacts, or deterministically renumbers unstable
implementation-generated identifiers" vs L36507-36510: "A conforming
implementation MUST expose a conformance verification mode observationally
equivalent to: check --verify-each --dump-on-failure --canonical-dumps"

*Verifier caveat (why this is weakened):* Quotes are accurate (L36417 SHOULD
vs L36507-36518 MUST), but there is no contradiction and no implementer
ambiguity: under RFC-2119 layering the specific MUST governs — canonical dumps
ARE required in the conformance verification mode for failing checkpoints,
full stop. §34.1.5's SHOULD covers a general-purpose canonicalized dump mode
usable at any checkpoint for diff-friendly testing; an implementation can
satisfy both by providing canonicalized dumps at least in the §34.1.6A mode.
The claim ' …

**Possible fix:** In §34.1.5 change "Implementations SHOULD additionally
provide a canonicalized dump mode" to "Implementations MUST provide a
canonicalized dump mode" (or, alternatively, weaken §34.1.6A to "emit a
canonicalized dump when the canonicalized mode is supported, and otherwise the
deterministic dump of §34.1.5").

## 85. §34.2.13 vs §34.2.2, §34.1.9: §34.2.13 step 3 attributes exported transparent definitional content and termination certificates to IMPLICIT_SIGNATURES, which by definition cannot produce them

**ambiguity** · severity **low** · verification: **weakened** · Spec.md lines
38101-38110 vs 37203-37205, 36828-36835, 36863-36864

Interface readiness (§34.2.13 step 3) is defined as running 'at least IMPORTS,
DECLARATION_SHAPES, HEADER_TYPES, STATUS, and only the portion of
IMPLICIT_SIGNATURES required to materialize exported signatures, importable
fixities, instance heads, and exported transparent definitional content'. But
§34.2.2 defines IMPLICIT_SIGNATURES as 'inference of declaration result types
or initializer types only' — it cannot produce elaborated transparent bodies,
elaborated constructor default expressions (§34.1.9 requires 'the elaborated
default expression'), conversion-reducible status, or the termination
certificates that §34.1.9 requires the interface artifact to record ('Each
recursive SCC that is accepted as total-certified MUST record a termination
certificate ... in the module interface artifact'). Producing those requires
BODY_RESOLVE (and MODAL_SOLVE/CORE_LOWERING) for the exported definitions,
which step 3 never mentions (it mentions MODAL_SOLVE only for modal
extensions). Two conforming readings diverge: (a) interface-ready requires
body elaboration of all transparent exports before any downstream module
starts (a very different pipelining/parallelism profile than steps 4-5
suggest), or (b) it does not, in which case the emitted artifact violates
§34.1.9's MUSTs.

> L38102-38104: "This includes at least `IMPORTS`, `DECLARATION_SHAPES`,
`HEADER_TYPES`, `STATUS`, and only the portion of `IMPLICIT_SIGNATURES`
required to materialize exported signatures, importable fixities, instance
heads, and exported transparent definitional content." vs L37203:
"`IMPLICIT_SIGNATURES`: inference of declaration result types or initializer
types only ..."

*Verifier caveat (why this is weakened):* The grammatical attachment is real
and sloppy — L38102-38104 hangs 'exported transparent definitional content'
off 'the portion of IMPLICIT_SIGNATURES', while §34.2.2 L37203-37204 limits
that phase to 'inference of declaration result types or initializer types
only'. But the alleged divergence between readings (a) and (b) does not exist:
§34.2.13 L38094-38095 DEFINES interface-ready as 'the implementation has
produced the module interface artifact of §34.1.9', and step 3 says 'This
includes at l …

**Possible fix:** Rewrite step 3's phase list to: "This includes at least
IMPORTS, DECLARATION_SHAPES, HEADER_TYPES, STATUS, the portion of
IMPLICIT_SIGNATURES required to materialize exported signatures, and the
portion of BODY_RESOLVE, MODAL_SOLVE, and CORE_LOWERING required to
materialize exported transparent definitional content, elaborated constructor
defaults, conversion-reducible status, and termination certificates for
exported total-certified definitions."

## 86. §35.13 vs §36.1: Build manifest's 'exactly one final build-configuration binding' is not pinned to a name, and the 'observationally equivalent' escape is undefined

**ambiguity** · severity **low** · verification: **weakened** · Spec.md lines
39538-39546, 39549, 39655

§35.13 requires a manifest to 'define exactly one final build-configuration
binding: `let buildConfig : BuildConfig = ...` or a value observationally
equivalent under the build-schema API.' It is unspecified (a) whether the
binding must be named `buildConfig` (§36.1 and §36 read 'the manifest's final
`buildConfig` binding' / 'the value of `buildConfig`', implying name-based
lookup, while the 'observationally equivalent' alternative implies a
differently named or differently shaped binding qualifies); (b) what 'final'
means — last in source order, or merely unique; and (c) what observational
equivalence 'under the build-schema API' is for a config binding, which is a
name+value pair, not a value. Two conforming build tools can disagree on
whether `let cfg : BuildConfig = package(...)`, or a manifest where
`buildConfig` is followed by later helper bindings, is a valid manifest —
divergent acceptance of the same portable manifest.

> L39538-44: "it MUST define exactly one final build-configuration binding:
```kappa let buildConfig : BuildConfig = ... ``` or a value observationally
equivalent under the build-schema API." vs L39655: "An **authored build
value** is a value reachable from the manifest's final `buildConfig` binding."

*Verifier caveat (why this is weakened):* Quote accurate, but the headline
claim (name not pinned) is substantially refuted by context: L39546 ('The name
`BuildConfig` is supplied by `std.build`'), L39550 ('Build-manifest evaluation
produces: the value of `buildConfig`'), and L39655 ('the manifest's final
`buildConfig` binding') all perform name-based reference — a tool accepting
`let cfg : BuildConfig = ...` could not produce 'the value of buildConfig'
required at L39550, so it is non-conforming; the charitable reading of 'or a
value o …

**Possible fix:** Replace with: "A build manifest MUST define exactly one top-
level binding named `buildConfig`, whose annotated or inferred type is
`BuildConfig` (as supplied by `std.build`). It need not be the last binding in
the file. The build system reads that binding by name." Delete the
'observationally equivalent' clause, or define it precisely (e.g. permit a
loader-documented alternate binding name selected by the build request).

## 87. §4.7 vs §4.1/§4.2/§29.6: Unsafe/debug audit ledger has no record kind for std.debug / allow_debug_introspection uses

**incompleteness** · severity **low** · verification: **weakened** · Spec.md
lines 4443-4461, 4271-4277, 4301

§4.1 classifies the std.debug module (§29.6) as an unsafe/debug facility
excluded from the safe portable subset, §4.2 gates it with
allow_debug_introspection, and §4.7 requires 'Every compilation unit ... that
depends on unsafe/debug or nonportable facilities MUST carry an unsafe/debug
audit ledger'. But the UnsafeDebugAuditLedger schema enumerates one field per
facility (unsafeAssertions, unsafeReducibility, unsafeTermination,
unsafeErasureEvidence, unhideUses, clarifyUses, backendEscapes,
nonPortableFeatures, hostBindingTrust, bridgeTrust, externalTranscripts) and
has no field for debug-introspection uses. A unit whose only unsafe dependency
is a std.debug import has no place to record it (allow_debug_introspection is
a build setting, not obviously a FeatureGateRecord), so
auditModule/auditPackage results diverge across implementations: some report
std.debug usage, some report an empty ledger.

> L4449-4461: 'UnsafeDebugAuditLedger =\n (unsafeAssertions : List
UnsafeAssertionRecord,\n unsafeReducibility : List AssertReducibleRecord,\n
unsafeTermination : List AssertTerminatesRecord,\n unsafeErasureEvidence :
List UnsafeErasureRecord,\n unhideUses : List UnhideRecord,\n clarifyUses :
List ClarifyRecord,\n backendEscapes : List BackendEscapeRecord,\n
nonPortableFeatures : List FeatureGateRecord,\n hostBindingTrust : List
TrustedHostBindingRecord,\n bridgeTrust : List TrustedBridgeRecord,\n
externalTranscripts : List ExternalTranscriptRecord)'

*Verifier caveat (why this is weakened):* The schema quote is accurate and no
field literally names debug introspection. But 'has no place to record it'
overstates: nonPortableFeatures : List FeatureGateRecord (L4457) is a
plausible and arguably intended home — allow_debug_introspection is a §4.2
build-configuration gate (L4301), feature provenance explicitly includes 'an
unsafe/debug build mode' (L353), E_FEATURE_UNSAFE_DEBUG_GATE_REQUIRED (L2035)
shows unsafe/debug settings are treated as feature gating, std.debug is
explicitly nonpor …

**Possible fix:** Add `debugIntrospectionUses : List DebugIntrospectionRecord`
to the UnsafeDebugAuditLedger schema in §4.7 (or add one sentence: 'Imports
and uses of std.debug are recorded as FeatureGateRecord entries under
nonPortableFeatures, naming allow_debug_introspection as the permitting
setting.').

## 88. §5.5.2 / §8.3.1A: No rule for conflicting imported fixities of the same operator and kind; parsing becomes unspecified

**incompleteness** · severity **low** · verification: **weakened** · Spec.md
lines 5074-5077, 5033-5034, 6845-6853

§5.5.1's fixity-collision rule applies only to 'declarations in the same
lexical scope', i.e. locally declared ones. §8.3.1A resolves imported
collisions as use-site ambiguities, but it covers 'spelling and declaration
kind' collisions among the six declaration kinds — fixity is metadata, not a
declaration kind, and use-site (type-directed) disambiguation cannot repair a
parse: the shape of `a ⊕ b ⊕ c` must be determined before any name/type
resolution. If module A exports `infix left 60 (⊕)` and module B exports
`infix right 40 (⊕)` and both are imported unqualified, no rule says whether
the import is an error, whether the later import wins, or whether every infix
use of `⊕` is ill-formed. Grep confirms the only fixity-conflict rules are the
same-scope rule (line 5033) and the fragment rule (§36.12, line 40772);
neither covers cross-module imports.

> lines 5074-5077: "Exported fixity declarations are imported only together
with the corresponding operator name. ... Imported fixities take effect from
the point of the import onward." line 6853 (§8.3.1A): "Such collisions are not
import-time errors by default. They are use-site ambiguities."

*Verifier caveat (why this is weakened):* Quotes accurate, and greps confirm
no explicit imported-fixity-conflict rule exists (only same-scope 5033 and
fragment 40772). But the headline scenario is mostly defused by §8.3.1A
itself: if modules A and B export DISTINCT operators spelled `⊕` (which is
where differing fixity declarations normally come from, since a fixity is
exported with its operator per 5074), then every use of `⊕` is a use-site
ambiguity error under 6850-6853 regardless of which precedence the parser
assumed — the program …

**Possible fix:** Add to §5.5.2 (or §8.3.1A): 'If two or more imported fixity
declarations for the same operator token and the same fixity kind are
simultaneously in scope and are not identical in precedence and associativity,
any use of that operator in a position governed by that fixity kind is a
compile-time error; identical imported fixities merge into one. `except`,
kind-qualified items, and aliases may be used to remove the conflict.'

## 89. §6.1.4 / §6.1.5 vs §5.5.2 / §5.5.3: Prefix minus is hard-wired to `negate`, contradicting the operator-resolution and infix-gating model

**ambiguity** · severity **low** · verification: **weakened** · Spec.md lines
5180-5181, 5201-5202, 5299, 5089-5092

§6.1.4 states unconditionally that `-123` 'is parsed as `negate 123`' and
§6.1.5/§6.1.6 repeat that the leading `-` 'is parsed as the ordinary prefix
operator `negate`'. But under §5.5, operators are ordinary term declarations
resolved lexically, and §5.5.3 requires a `prefix` fixity for `-` to be in
scope for prefix position at all. Two divergences follow: (1) if a user
declares their own prefix `-` (`prefix 80 (-)` plus a local `let (-) = f`),
one conforming reading elaborates `-x` to the lexical `(-)` applied to `x`,
the other to `negate x` resolved by name; (2) in a `@NoPrelude` module with no
prefix fixity for `-` imported, §5.5.3 makes `-123` a parse error while §6.1.4
says it parses as `negate 123`. The spec never gives the general elaboration
rule for prefix-operator application, so it is unclear whether `negate` names
the lexical binding of the operator token `-` or the identifier `negate`.

> lines 5180-5181: "* `-123` is parsed as `negate 123`\n* `-3.14e2` is `negate
(3.14e2)`" line 5092 (§5.5.3): "* prefix position requires a `prefix` fixity
in scope"

*Verifier caveat (why this is weakened):* Quotes accurate (5180-5181,
5201-5202, 5299, 5092). But the conflict dissolves under the reading the spec
itself signals: §6.1.5 (5201) calls the leading `-` 'the ordinary prefix
operator' — i.e. explicitly NOT a special literal-level form — and §5.5.1
(4968) says '(prefix -) denotes unary negation', with the prelude table
(31110) supplying `prefix 80 (-)`. On that reading, `-123` parses via the
ordinary §5.5.3-gated prefix operator whose prelude denotation is `negate`;
under `@NoPrelude` with n …

**Possible fix:** In §6.1.4 replace 'is parsed as `negate 123`' with: '`-123`
is parsed as the prefix-operator application `(prefix -) 123`, where `-`
resolves by ordinary operator lookup under §5.5.3 (in the standard prelude,
prefix `-` denotes `negate`)'; make the same substitution in §6.1.5/§6.1.6, or
alternatively state normatively that a prefix `-` immediately preceding a
numeric literal always elaborates to the prelude's `negate` regardless of
local rebinding.

## 90. §6.3.4.1 vs §6.3.1 / §6.3.4.4: `\$` escape in ordinary prefixed strings contradicts §6.3.1's unknown-escape error via §6.3.4.4

**contradiction** · severity **low** · verification: **weakened** · Spec.md
lines 5489, 5366, 5576-5577

§6.3.4.1 permits writing a literal dollar sign in an ordinary prefixed string
as `\$`. But §6.3.4.4 says literal segments of ordinary prefixed strings 'are
then decoded using the ordinary string escape rules of §6.3.1', and §6.3.1's
normative escape table does not contain `\$` and states 'An unknown escape
sequence is a compile-time error.' (Note §6.3.1's preamble extends its escape
set to 'ordinary string literals, Unicode scalar literals, and prefixed quoted
literals' — prefixed *strings* are not in that list, so no extension applies.)
A program like f"price: \$5" is simultaneously well-formed per §6.3.4.1 and a
compile-time error per §6.3.4.4+§6.3.1. Implementations will diverge on
acceptance and on the decoded text.

> line 5489: "A literal `$` in an ordinary prefixed string may be written as
`\$`." line 5366: "* An unknown escape sequence is a compile-time error." line
5576-5577: "In ordinary prefixed strings, literal segments are then decoded
using the ordinary string escape rules of §6.3.1."

*Verifier caveat (why this is weakened):* Quotes accurate (5489, 5366, 5576)
and the terminology check holds: 'prefixed quoted literals' in §6.3.1's
applicability list (5342-5343) are the single-quoted g'…'/b'…' family (5849,
5880), not prefixed strings, so `\$` is formally absent from the §6.3.1 table
that §6.3.4.4 invokes. But the 'simultaneously well-formed and a compile-time
error' framing only holds under an uncharitable reading: §6.3.4.1 line 5489 is
an explicit normative family-specific rule sanctioning `\$`, and the standard
spe …

**Possible fix:** Amend §6.3.4.4's first ordinary-prefixed-string bullet to:
'literal segments are then decoded using the ordinary string escape rules of
§6.3.1, extended with the additional escape `\$` denoting U+0024 DOLLAR SIGN
(and `\$` suppresses interpolation recognition).' Alternatively add `\$` to
§6.3.1's table with a note that it is meaningful only inside ordinary prefixed
strings.

## 91. §8.1 vs §5.1: Script-mode header module names may be non-ASCII, but the duplicate/case-fold rule is defined only for ASCII segments

**incompleteness** · severity **low** · verification: **weakened** · Spec.md
lines 6601-6603, 6570-6574, 4589, 4592-4595

§8.1 requires case-fold duplicate detection by 'converting each module-name
segment to lowercase ASCII', justified 'because path-derived module-name
segments are restricted to ASCII'. But in script mode a module header 'MAY
differ' from the path-derived name and 'the header name becomes the module
name', explicitly 'subject to the same fragment, duplicate, and case-folding
rules'. Header names are `modPath`s whose segments admit backtick identifiers
('a backticked segment contributes its unquoted text as the module-name
segment', §5.1) and, under `unicode-names`, Unicode identifiers — §5.1's
ASCII-only restriction is stated only for path-derived names. So a script-mode
header like module `Café` or a backticked non-ASCII segment yields an
effective module name for which 'converting to lowercase ASCII' is undefined,
and implementations will diverge on whether such headers are accepted and on
which pairs count as case-fold duplicates. Grep for 'effective module name'
shows no other section restricting header-name segments.

> lines 6601-6603: "In script mode, it MAY differ; if it differs, the header
name becomes the module name of the file. Effective module names are then
subject to the same fragment, duplicate, and case-folding rules as path-
derived module names." lines 6572-6573: "implementations MUST compare module
names after converting each module-name segment to lowercase ASCII. Because
path-derived module-name segments are restricted to ASCII letters, digits, and
`_`, no Unicode normalization is required."

*Verifier caveat (why this is weakened):* Quotes accurate (6601-6603,
6572-6574, 4589, 4594-4595), and the gap direction is right: 4594 restricts
only PACKAGE-mode path-derived names to ASCII, the segment regex (6556-6557)
is stated only for path segments, and modSeg admits backtick/Unicode
identifiers — so nothing forbids `module Café` in script mode. However, the
core claim that 'converting each module-name segment to lowercase ASCII is
undefined' for such names is overstated: ASCII lowercasing is a total,
deterministic operation on a …

**Possible fix:** Add to §8.1: 'Every effective module-name segment, whether
path-derived or header-derived, MUST match `[A-Za-z_][A-Za-z0-9_]*`; a script-
mode module header containing any other segment (including via backtick
segments) is a compile-time error.' (Or, if non-ASCII header names are
intended, define their case-fold comparison via the active
UnicodeNameProfile.)

## 92. §9.2 vs §8.5: Top-level non-simple pattern bindings 'MUST NOT be exported': implicit privatization vs compile error is unspecified

**ambiguity** · severity **low** · verification: **weakened** · Spec.md lines
7828, 7281-7283

§8.5 says that without `@PrivateByDefault` 'every ordinary top-level named
item ... is exported unless marked `private`'. §9.2 says 'A top-level pattern
binding whose binder is not a single simple name MUST NOT be exported.' In a
default-visibility module, a bare `let (a, b) = f ()` is caught between these:
one conforming implementation treats such bindings as implicitly private
(satisfying the MUST NOT automatically), another treats the unmarked binding
as exported-by-default and therefore rejects the program, requiring an
explicit `private`. Acceptance of ordinary programs diverges.

> line 7828: "* A top-level pattern binding whose binder is not a single
simple name MUST NOT be exported." lines 7281-7282: "Without
`@PrivateByDefault`, every ordinary top-level named item in the current module
is exported unless marked `private`."

*Verifier caveat (why this is weakened):* Quotes accurate (7828, 7281-7282).
But the immediately following bullet (7829-7830) resolves the intended
reading: 'CONSEQUENTLY, the explicit-signature requirement ... applies only to
exported top-level let definitions whose binder is a single simple name' —
'consequently' only follows if non-simple pattern bindings are definitionally
never exported (automatic privatization), not if programs lacking `private`
are rejected. Read as a constraint on the export surface (the natural RFC-2119
reading …

**Possible fix:** Replace the §9.2 bullet with one of: 'A top-level pattern
binding whose binder is not a single simple name is always private; the export
default of §8.5 does not apply to it (an explicit `public` on such a binding
is a compile-time error).' — or — 'A top-level pattern binding whose binder is
not a single simple name MUST be marked `private` (or appear under
`@PrivateByDefault` without `public`); otherwise compilation fails.'
