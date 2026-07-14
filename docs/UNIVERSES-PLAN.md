# Universes / `TypeLevel` / Parametric Type Witnesses — Implementation Plan

Status: **planned; compiler implementation not started.** The spec side is DONE: commits
`9a29e59a`..`39207986` rewrote §11.1 (universes, level expressions, `TypeLevel`), §11.3
(universal quantification), and §10.4.1 (constructor universe-size checking), then threaded
the *parametric type witness* capability through lookup, static facets, records, traits,
patterns, reflection, KCore, and diagnostics. Commit `7965dfd5` reconciled the pending
universe fixtures with the proof-bounded design. The current spec additionally makes
`zero`/`one`/`succ`/`+`/`max` ordinary resolved prelude operations backed by compiler-owned
`TypeLevel` instances and canonical KCore intrinsic heads. The staged gate is 28 files in
`tests/pending-import/spec-universes/`, 14 pending parametric-witness fixtures, and 8 active
acceptance fixtures. This plan closes KNOWN_SPEC_ISSUES **§16** (no constructor universe-size
check) and **§17** (Type-in-Type/Hurkens risk), both confirmed-high.

**Decision (recorded): the current `docs/Spec.md` is normative.** The working-tree note in
`docs/notes/KNOWN_SPEC_ISSUES.md` §17 describes a superseded intermediate cut ("option D":
finite-only `TypeLevel`, total ω-ceilings, no unbounded-telescope rejection, prenex level
generalization). The final cut is different on every one of those points: `TypeLevel` values
**include `ω`**; there is **no automatic ω ceiling**; unbounded level-indexed telescopes are
**rejected** (`E_UNIVERSE_UNBOUNDED_TELESCOPE`); bounds are **erased Boolean proof binders**
(`(@0 p : i < κ)`); and ordinary polymorphism is **parametric `0 Type` binders**, not level
schemes. The stale note must be corrected (D3). Where this plan and Spec.md disagree, Spec.md
wins; where the corpus and Spec.md disagree, the corpus gets fixed or a spec issue gets filed —
never a silent deviation.

**Decision (recorded): two independent mechanisms, not one.** The redesign is (1) a **level
discipline** — levels become canonical intrinsic expressions
(`zero | omega | succ | add | max | var | meta`) with a complete decidable ordering, ceilings,
and size rules — and (2) a **capability discipline** —
`(0 A : Type ρ)` binders introduce *parametric type witnesses* that are usable as types but are
never ordinary inspectable type-code values. They meet exactly twice: parametric binders are
exempt from level-bumping in formation (§11.1.2.8) and from constructor-size obligations
(§10.4.1). Phases A/B build the level discipline; Phase C builds the capability discipline.

**Decision (recorded): source operations are ordinary; canonical operations are intrinsic.**
The admitted KCore grammar is `__typeLevelZero | __typeLevelOmega | __typeLevelSucc l |
__typeLevelAdd l l | __typeLevelMax l l | variable | metavariable`. Source `0`, `1`, `ω`,
`succ u`, arbitrary `u + v`, `max u v`, and comparisons enter that grammar only after ordinary
resolution, implicit insertion, compiler-owned instance selection, and transparent
normalization. Recognition is by global/evidence identity, never rendered name. User code or
shadowed operations returning `TypeLevel` are rejected in universe position unless they
transparently normalize to the canonical heads.

**Decision (recorded): §11.3's `forall` desugaring is literal.** `forall a. T` introduces an
explicit erased `(0 a : Type)` Pi; `forall (a : S). T` introduces an implicit erased
`(@0 a : S)` Pi. The implementation and tests must preserve this asymmetry. This is no longer
an open question in the plan.

**Decision (recorded): capability is a checked KCore invariant, not elaborator scratch
state.** The representation may be derived from quantity plus the elaborated universe domain
instead of adding a new term constructor, but binder/field/projection origin and capability
must survive long enough for KCore checkpoint verification, interface emission, and erasure
justification (§30.2.2.9). A checker-only bit that disappears before those boundaries is
non-conforming.

## 0. Where the compiler actually is (audit 2026-07-14)

The pipeline is lex → parse (`Parser.hs`) → resolve → **elaborate/check (`Check.hs`, ~20k
lines, owns everything below)** → KCore (`Core.hs`) → KBackendIR → C/LLVM. Current universe
state, with anchors:

* Universes are a single sort with a **plain `Int` level**: `CSort !Int` / `VSort !Int`
  (`Core.hs:144,369`). Typing is hardwired `Type u : Type (u+1)` (`Check.hs:4012,5014`).
  There is **no level datatype, no level metavariables, no solver** — levels are computed
  directly by `max`/`+1` during elaboration (Pi `Check.hs:4228`, records `Check.hs:4106-4140`,
  forall/exists `Check.hs:5118-5196`).
* **Cumulativity already exists** as one line in conversion: `(VSort m, VSort n) -> pure (m <= n)`
  (`Check.hs:1346`). Failures surface as generic `kappa.type.mismatch`, never `kappa.universe.*`.
* `Type`/`TypeN`/`*` are **not keywords**; they are identifiers recognized late by `sortName`
  (`Check.hs:2315-2326`). So bare `Type` is *already* `Type0` in expression position — but
  `Typeω`, `Type u` (application form), `Type(ω+1)`, `Type(max u v)` do not parse/elaborate,
  and `TypeLevel` **does not exist anywhere** (no builtin, canonical intrinsic heads,
  compiler-owned operation instances, `LevelLe`/`LevelLt`, or `TypeBelow`/`TypeAtMost`).
* `data` result universes are **hardwired `Type0`** (`sortT = CSort 0`, `Check.hs:16475`;
  predeclare `Check.hs:16262`). There is **no constructor universe-size rule** — the only data
  checks are strict positivity and arity.
* **The vacuous-green trap:** a bare-`Type` kind annotation on a `type` alias is *ignored* —
  `elabAliasBody` short-circuits `Just kindE | isBareTypeExpr kindE -> inferAliasRhsKind`
  (`Check.hs:16417`). That is why `type SigSmall : Type = (0 A : Type, value : A)` and
  `type Poly : Type = (0 A : Type) -> A -> A` are green today even though the computed levels
  (which count `Q0` domains at their annotation level — there is **no parametric exemption**)
  would be `Type1`. The 8 green parametric-witness tests are real only for non-bare kinds
  (`SigLarge : Type1`); the rest pass through this hole. Enforcement (B3) and the parametric
  no-bump rule (B2) must land together or the corpus breaks.
* `(0 A : Type)` vs `(A : Type)`: quantity differs (`Q0` vs `QW`, `binderQ` `Check.hs:3914`),
  but **runtime erasure treats both as erased** (`runtimeErasedParam`, `Backend/Repr.hs:537`:
  `q == Q0 || valueDomainIsKind || resultIsProofValue`). There is **no capability distinction**
  and no promotion check of any kind (`E_PARAMETRIC*` greps empty).
* `forall`/implicit universalization produce **implicit `Q0` binders defaulting to `Type0`**
  (`elabForall` `Check.hs:5118-5137`; `freeLower` sites `Check.hs:16277,8218,16893,19570`).
  Unconstrained kind metas are solved to `CSort 0` or generalized into `(@__k : Type0)` binders
  (`Check.hs:16401-16414`) — the mechanism behind the active test
  `universe-metavar-generalization.kp`, which pins the **old** "fresh metavariable per bare
  `Type`" semantics that the new spec explicitly removes.
* None of the redesign's diagnostics exist: no `kappa.universe.*` family, no
  `E_UNIVERSE_SELF_CONTAINMENT` / `E_UNIVERSE_CONSTRAINT_UNSATISFIABLE` /
  `E_UNIVERSE_LEVEL_EXPRESSION` / `E_UNIVERSE_UNBOUNDED_TELESCOPE` /
  `E_DATA_CONSTRUCTOR_FIELD_UNIVERSE` / `E_PARAMETRIC_TYPE_PROMOTION` in `Explain.hs`/`Config.hs`.
* KCore carries binder quantity and universe domains but has **no explicit capability/provenance
  contract** for witnesses, projections, or aliases, and no checkpoint rejects witness-to-code
  promotion. Erasure records do not distinguish erased ordinary type-code values, erased
  parametric witnesses, and erased proof/trait evidence as required by §30.2.2.9.

**Honest scope.** This is a front-end (elaborator) program. Nothing in it may change generated
code for the existing corpus: levels are compile-time-only data and witnesses are already
erased. The native gate is *byte-identical output*, not perf. The payoff is soundness (two
confirmed Type-in-Type holes closed), spec conformance (42 staged fixtures + 8 active
acceptance fixtures),
and the substrate the backend was just licensed to exploit (§1.1.x now explicitly permits
specialization over erased type info post-erasure-justification).

## 0A. Preflight — make the staged gate complete

The current pending corpus covers the main acceptance/rejection spine, but it does not pin
every rule the implementation could get subtly wrong. Add these fixtures before, or in the
same commit as, the first stage that consumes them:

- **U-P0 — baseline and missing-fixture tranche.** Record the current conformance count and
  native outputs; validate all pending files with `scripts/validate.py`. Add pending fixtures
  for: invalid `Type (f u)` level expressions; closed and open `succ`/`+`/`max` normalization;
  arbitrary `Type(u + v)`; ordinal-addition direction (`1 + ω = ω`, `ω + 1 > ω`); each
  standard operation accepted by semantic identity; shadowed/user-defined `succ`, `+`, `max`,
  `<`, and `<=` rejected in universe/proof positions; transparent aliases accepted; source
  instances for `Eq`/`Ord`/`Zero`/`One`/`FromInteger`/`Successor`/`Add`/`Max TypeLevel`
  rejected; negative `TypeLevel` literals rejected; unsupported `Mul`/`Negatable`/algebraic
  instances absent;
  first-class `TypeLevel` values passed, returned, stored, projected, sealed, and opened;
  an inconsistent proof-bound context that must not justify self-containment; explicit
  `(i < κ) = True` / `(i <= κ) = True` proof binders; the `i <= ω` classifier
  `Type(ω+1)`; higher-level witness cumulativity (`0 Type3` to `0 Type4`) and forbidden level
  drop (`0 Type3` to `0 Type0`); `forall` explicit/implicit application asymmetry; witness
  capability across aliases, imports/exports, and generated projections; and a KCore unit
  test that injects the forbidden `ParamTypeWitness ρ -> TypeCode ρ` use. Every fixture names
  the exact spec anchor and portable diagnostic. *Gate:* existing active conformance remains
  green; all new fixtures validate and remain under `pending-import` until their owner stage.
  Before implementation, also reconcile the stale §3.2.3 sentence that defines the diagnostic
  only for an annotation "exactly `Type`" with the normative higher-universe rule
  `Type ρ` in §11.1.2.3A, and audit §10.4.1's `@0 A : Type1` example for the same editorial
  residue. Do not encode the narrower wording in the compiler.

## 1. Phase A — the level substrate (levels become expressions)

Each sub-stage keeps the full conformance gate green and native output byte-identical.

- **U-A0 — canonical level expressions.** Replace the `Int` in `CSort`/`VSort` with an
  alpha-stable `Level` AST whose constructors correspond exactly to `__typeLevelZero`,
  `__typeLevelOmega`, `__typeLevelSucc`, `__typeLevelAdd`, `__typeLevelMax`, rigid variables,
  and metavariables. Keep ordinal addition ordered: `LAdd a b` is not commutative. Normalize
  only sound identities (closed evaluation, add-zero identities, a single chosen canonical
  form for successor/`+ one`, and associative/commutative/idempotent flattening for `max`);
  do not rewrite by source names. Mechanical sweep of `CSort`/`VSort` sites maps `+1` to
  intrinsic successor and formation `max` to intrinsic max. With only closed finite levels,
  semantics are unchanged. *Gate:* Core equality/substitution/pretty round trips; old finite
  sorts agree with `Int`; conformance green; native byte-identical.
- **U-A1 — constraints, metavariables, and the complete ordering solver.** Add explicit
  `LevelConstraint` values (`lhs ≤ rhs`, origin, enclosing construct, active assumptions) and
  a solver result that distinguishes proved, disproved, and blocked-on-metavariable. The
  solver must assign `LMeta`s, perform occurs/self-containment checks, normalize after each
  assignment, and retain unsolved constraints for §11.1.3 generalization/defaulting; a Boolean
  `leqLevel` alone is insufficient. For rigid expressions, implement the complete
  §11.1.2.1 ordering for `zero`/`omega`/`succ`/ordinal `add`/`max`. Do not extend the old
  base-plus-offset comparator: arbitrary `u + v` makes that representation incomplete.
  Implement the decision procedure over the ordinal fragment denoted by the canonical AST;
  the recommended reference semantics translates values to an `(ω coefficient, finite tail)`
  pair and treats open addition/max as guarded quantifier-free Presburger obligations.
  Preserve addition order (`1 + ω = ω`, while `ω + 1 > ω`), prove
  `max a b ≤ w` iff both arms are ≤ `w`, and close scoped assumption edges without treating a
  consistent cycle (`u ≤ v`, `v ≤ u`) as contradiction. If a complete decision procedure for
  this exact grammar cannot be justified, stop and repair the spec rather than shipping a
  conservative solver under a normative completeness MUST.
  Classify normalized `succ u ≤ u` / `Type u : Type u` failures as self-containment. Rewire
  conversion (`Check.hs:1346`), inference, and formation to emit/solve constraints instead of
  directly comparing integers. Register `kappa.universe.constraint` and
  `kappa.universe.level-expression` with their portable aliases and complete §3.2.3 payloads.
  *Gate:* property-test rigid ordering against a reference ordinal evaluator over finite,
  `ω`, `ω+n`, repeated addition, and mixed open terms; exhaustively compare small expressions
  and assumptions; property-test meta solving for order independence; import
  `universe-self-containment-rejected.kp`; reconcile active tests that currently pin generic
  mismatch diagnostics in the same commit as the diagnostic change.
- **U-A2 — `TypeLevel` and the surface level language.** (a) New compiler-owned builtin
  `TypeLevel : Type0` (via `Kappa.Builtins`/`Prelude.hs`, following the de-hardcoding
  contract); rename nothing — `Universe` never existed in code, only in the old spec text.
  (b) Give ordinary compile-time `TypeLevel` terms a Core representation/canonicalization
  path distinct from `Level`: bind/pass/return/store/project/seal/open remain ordinary term
  operations, while use as a `Type` index must transparently normalize to an admitted `Level`.
  A bound `(u : TypeLevel)` maps to a stable rigid `LVar` identity only at that boundary.
  (c) Add ordinary prelude traits `Successor` and `Max`, plus compiler-owned
  `Eq`/`Ord`/`Zero`/`One`/`FromInteger`/`Successor`/`Add`/`Max TypeLevel` evidence backed by
  `__compareTypeLevel` and the five canonical level heads. Reject source instances for every
  compiler-owned `TypeLevel` head; accept only nonnegative `FromInteger` literals; do not add
  subtraction, multiplication, negation, division, modulo, or algebraic-law instances.
  (d) Numeric literals are finite levels; `ω`, `Typeω`, and `Type(ω+n)` lex/parse without the
  `unicode-names` gate. `Type e` is special universe-family syntax: first elaborate `e` by
  ordinary resolution/trait selection, then normalize only canonical compiler-owned evidence.
  Admit standard `succ`, arbitrary standard `u + v`, and standard `max`; reject shadowed or
  user-defined lookalikes with `E_UNIVERSE_LEVEL_EXPRESSION`. Comparisons reduce on closed
  levels, may remain neutral on open ones, and become assumptions only through B0's
  semantic-identity check.
  (e) `TypeLevel` values are compile-time-only (§11.1.6 list gains `TypeLevel`; erasure
  classifier already erases kind-domains — extend `valueDomainIsKind`-adjacent logic so
  `TypeLevel` domains erase identically). *Gate:* the U-P0 first-class/canonicalization
  fixtures plus `bounded-level-syntax-rejected.kp`; conformance green and native output
  byte-identical.

## 2. Phase B — the formation discipline (assumptions, ceilings, sizes)

- **U-B0 — level assumptions from erased proof binders.** Extend the §11.4.2 Boolean-proposition
  coercion (already implemented for `(@x : b)`, `Check.hs:4222` region) to recognize, at
  *erased proof-binder* positions, comparisons whose operands elaborate to solver-level
  expressions and whose operators resolve through the compiler-owned `Ord TypeLevel`
  evidence: `(@0 p : i < κ)` ⇒ local assumption `succ i ≤ κ`;
  `(@0 p : i <= κ)` ⇒ `i ≤ κ`;
  the explicit forms `(@0 p : (i < κ) = True)`; and the transparent aliases `LevelLt`/`LevelLe`
  (added to the prelude as ordinary `type` aliases, D1 ships them but B0 must already accept
  the unfolded form). Assumptions enter a lexically-scoped `Assumps` set threaded through the
  checking context (telescope-ordered: earlier binders' assumptions govern later components,
  §10.4.1/§11.1.2.8). **Satisfiability check on entry**: adding an assumption that makes the
  set inconsistent (derives `succ u ≤ u`) either rejects the binder with
  `kappa.universe.constraint` or demotes the proof to an ordinary proposition — it must never
  justify self-containment (§11.1.2.2). The solver may synthesize erased proof evidence for a
  valid comparison goal, but ordinary `Eq`/`Ord` dictionary resolution remains ordinary trait
  search; neither path may manufacture an invalid bound. Preserve assumption scopes through
  nested Pi, record, constructor, match-branch, and generated declarations without storing
  them globally. *Gate:* import `level-comparison-compat-aliases-accepted.kp` and
  `typelevel-eq-ord-proof-binders-accepted.kp`; the U-P0 explicit-equality and inconsistent-
  assumption fixtures behave as specified.
- **U-B1 — ceiling-based formation + unbounded-telescope rejection.** Rewrite the Pi/record/
  tuple/exists/package level computation to the §11.1.2.8 discipline. For Pi `(q x : A) -> B`:
  compute `β` for `B`; if `β` mentions binders of the telescope (an `LVar` bound inside it),
  use the declared/expected outer ceiling when one exists, otherwise infer the least
  expressible ceiling from active bounds. In either path, prove `β ≤ κ` and require `κ` to be
  well-formed outside the telescope; result `Type (max α κ)`. If no such ceiling exists:
  reject with `kappa.universe.unbounded-telescope` / `E_UNIVERSE_UNBOUNDED_TELESCOPE`, with the
  §3.x payload (telescope kind, escaping variable, component + classifier, assumptions in
  scope, attempted ceiling, suggested `(@0 p : i < κ)` repair). Same discipline for record/
  tuple/exists/package telescopes (`αi ≤ κ` for every field, κ outside the telescope). **There
  is no automatic ω ceiling** — `(i : TypeLevel) -> Type i` is an error, `(i : TypeLevel) ->
  (@0 p : i < ω) -> Type i : Typeω`. *Gate:* imports: `pi-over-levels-unbounded-rejected`,
  `dependent-record-over-levels-unbounded-rejected`, `existential-over-levels-unbounded-rejected`,
  `pi-over-levels-fixed-codomain-accepted`, `dependent-record-over-levels-bounded-accepted`,
  `existential-over-levels-bounded-accepted`, `bounded-pi-proof-bound-accepted`,
  `pi-over-typeomega-accepted`, `universe-explicit-shared-variable` (universes-intrinsics), and
  the U-P0 `i <= ω` classifier fixture.
- **U-B2 — the parametric no-bump formation rule.** In the same level computation, a binder/
  field with quantity exactly `Q0` whose annotation normalizes to a universe `Type ρ` is
  **parametric**: it contributes nothing to the enclosing former's level (no `succ ρ`), while
  uses of the witness *as a type expression* in later components still classify at `ρ`
  (§11.1.2.8: `(0 A : Type3) -> Int : Type`, `(0 A : Type3) -> A -> A : Type3`,
  `(0 T : Type3, foo : T) : Type3`). Erased-but-non-universe binders keep the ordinary rule
  ("erasure alone is not enough"). This is a *level* rule only — capability enforcement is
  Phase C. *Gate:* the 8 active parametric-witness acceptance tests stay green **once B3 makes
  them non-vacuous**; `pi-over-levels-first-class-accepted.kp` imports.
- **U-B3 — enforce declared classifiers (kill the vacuous-green hole) + bare-`Type` fixation.**
  Remove the `isBareTypeExpr` skip in `elabAliasBody` (`Check.hs:16417`): a bare-`Type` alias
  kind means `Type0` and the RHS is checked against it (cumulatively). Audit the other
  annotation sites (`DSig`, local sigs, exists/record ascriptions) for equivalent skips. Bare
  `Type` introduces **no metavariable anywhere** (§11.1.2.4) — audit the `freshMeta`-for-kind
  paths (`Check.hs:16277-16291,8218-8240,16401-16414`) so metas arise only where the spec
  licenses them, and the `(@__k : Type0)` kind-generalization survives only where it is
  the §11.1.3 boundary generalization. **Corpus reconciliation #2 (the flag-day stage,
  deliberately small):** `universe-metavar-generalization.kp` pins the removed
  per-occurrence-metavariable semantics (`idFn Type0` through `forall (a : Type)`) — under the
  new spec that instantiation is a level error (`1 ≤ 0`); rewrite it as the new-semantics
  witness (parametric identity reused at term types; higher-level uses become expected-reject
  arms) in the same commit. Sweep `tests/conformance/types/universe-stratification.kp`
  (survives — `polyId : Type1` holds by cumulativity even though `forall a. a -> a : Type0`
  now) and the `imported-anon` universe suite for level-sensitive pins. *Gate:* conformance
  green with the reconciled corpus; `SigSmall`/`Poly` acceptance tests now pass **non-vacuously**
  (flip B2 off in a scratch build → they must fail — proves enforcement is live); native
  byte-identical.
- **U-B4 — data universes + the constructor universe-size rule (§10.4.1).** Un-hardwire the
  data result sort (`Check.hs:16475,16262`): `data F Δ : Type ρ` elaborates its declared
  classifier (any solver-level `ρ`, including `ω`); default stays `Type0`. For every
  constructor-local binder (explicit fields, implicit/erased binders, GADT-signature binders,
  implicitly-universalized GADT variables, default- and record-sugar-introduced binders):
  check its annotation at `Type α` and demand `α ≤ ρ` under the header telescope Δ plus
  earlier constructor-binder assumptions (level-comparison proof binders inside the telescope
  count, §10.4.1) — schematic check, binders held abstract. **Parametric constructor binders
  are exempt** (no `succ ρ` obligation; they introduce a witness at `ρ`); later fields
  *mentioning* the witness are checked normally (`Box (0 T : Type3) (foo : Int)` OK in `Type`;
  `(foo : T)` forces `Type3`). Failures: `kappa.universe.constructor-size` /
  `E_DATA_CONSTRUCTOR_FIELD_UNIVERSE`. Positivity/arity checks unchanged. *Gate:* imports:
  all seven `ctor-field-*`, `gadt-local-binder-large-rejected`,
  `header-arg-large-small-family-accepted`, `rejected-data-constructor-ordinary-type-code-field`,
  `rejected-ordinary-type-code-field-in-type` (record-alias size, lands via B3+B2), and the
  KNOWN_SPEC_ISSUES §16 repro `data U : Type0 = MkU (t : Type0)` rejects.

## 3. Phase C — parametric type witnesses (the capability discipline)

- **U-C0 — one capability model from elaboration through KCore.** Factor one classification
  predicate: a binder/field/pattern/projection is `ParamTypeWitness ρ` iff its introducing
  quantity is exactly `Q0` and its expanded annotation normalizes to `Type ρ`. Represent
  capability and origin on context entries, global/type-alias metadata, record/package and
  constructor fields, generated projections/accessors, and KCore binder/checkpoint metadata.
  It may be derived from `(Q0, Type ρ)` where that pair and origin are still present; otherwise
  store it explicitly. Interface/export metadata must preserve enough information for an
  importing module to reconstruct the same judgment. `type T = A` creates a type-level alias
  that preserves the witness; it does not create an ordinary static-object term facet.
  *Gate:* no acceptance behavior changes; a deterministic debug/unit dump shows the same
  capability and level before and after KCore lowering and across a module boundary.
- **U-C1 — promotion enforcement (`E_PARAMETRIC_TYPE_PROMOTION`).** The one-way rule: ordinary
  type-code may instantiate a compatible `0 Type κ` binder when `ρ ≤ κ`; a witness may be used
  as a type expression, passed to `0 Type κ` binders (`ρ ≤ κ`), repackaged into parametric
  fields, matched, and rechecked in generated syntax — but any demand for **ordinary**
  type-code capability rejects with family `kappa.type.parametric-promotion`, payload
  (witness origin, expected `ordinary-type-code`, actual `parametric-type-witness`).
  Enforcement points, each with a fixture: (a) a term whose *checked-against or inferred result
  type* is `Type ρ` returning a witness (`let bad A = A`); (b) argument to a non-`Q0`
  `(B : Type)` binder; (c) ordinary `(A : Type)` record/package field value; (d) projection
  `r.A` used outside type positions (`rejected-parametric-projection-returned-type`);
  (e) pattern binders (`rejected-pattern-promotes-parametric-witness`); (f) static-object
  reification: `let T : Type = A` rejected while `type T = A` stays a usable type-level name
  (§7.6.1, `rejected-local-type-alias-reified-type`), and kind-qualified static-object lookup
  (`Check.hs:6533-6610`) refuses to supply a witness where term-expression position demands
  ordinary code; (g) reflection entry points (`elabReflQuery`, `Check.hs:4149,4618`; the
  `Elab`/`Syntax` tier) — no operation converts witness → code (§21.6.2; generated syntax is
  rechecked by construction since checks live in the elaborator). *Gate:* imports: all
  `rejected-*` promotion fixtures + `accepted-parametric-witness-to-zero-type-binder`,
  `accepted-pattern-preserves-parametric-witness`, `accepted-repackaging-preserves-parametric`;
  the 8 active acceptance tests stay green; add/use the U-P0 higher-level cumulativity,
  forbidden level-drop, and module-boundary fixtures.
- **U-C2 — generalization defaults + `forall` desugaring (§11.3, §11.3.3).** Implicit
  declaration-level universalization generalizes an inferred bare-`Type` type variable to a
  **parametric** binder `(0 a : Type)` (current `freeLower` output is already `Impl Q0` +
  `Type0` — largely aligned); a variable is generalized as ordinary type-code **only when a use
  demands it**, and when undecidable the compiler prefers parametric and reports the first
  ordinary-code demand as promotion (§11.3.3). Unannotated `data`/`type`/`trait`/`effect`
  header parameters likewise become `(0 a : Type)` (today: `(Impl, Q0)` at `Check.hs:16501` —
  verify against the spec'd *explicit* `0` form); `trait Functor f` infers
  `f : (0 A : Type) -> Type`. Align `elabForall` with the normative asymmetric desugaring:
  `forall a. T == (0 a : Type) -> T` (explicit erased) vs
  `forall (a : S). T == (@0 a : S) -> T` (implicit erased). Do not silently insert an
  argument for the explicit form. *Gate:*
  conformance sweep green (this stage touches every polymorphic declaration — the biggest
  blast radius; run the full native corpus too); `universe-row-implicit-universalization.kp`
  imports; `accepted-forall-parametric-type` and the U-P0 explicit/implicit application
  fixture stay green.
- **U-C3 — traits, instances, evidence, boxes (§14.3.1A).** Trait goals may mention witnesses
  (dictionary passing is the capability carrier); instance members that would return a witness
  as an ordinary `Type` result reject (`rejected-associated-member-promotes-parametric`);
  `Typeable`/`Generic`-style reflection works only through declared evidence members. Verify
  the stored-polymorphic-function shapes type-check end to end (they exercise C0-C2 through
  records + application): `box-parametric-polymorphism-accepted`,
  `box-parametric-self-application-accepted`, `list-of-boxes-parametric-polymorphism-accepted`,
  `parametric-identity-reused-accepted` (self-application `id Poly id`),
  `accepted-polymorphic-function-on-box`, `accepted-stored-polymorphic-function-box`,
  `accepted-trait-evidence-parametric-witness`, `accepted-reflection-evidence-representation-value`.
  *Gate:* all of the above import; native byte-identical.
- **U-C4 — KCore verification and erasure provenance (§30.2.2.9).** Add a fail-closed KCore
  legality check for any term, generated helper, or interface artifact that consumes a
  parametric witness as an ordinary `Type ρ` value. Verify generated constructor metadata,
  accessors, projections, match binders, alias/static facets, and macro/plugin output at the
  same checkpoint as source elaboration. Erasure-justification records must distinguish
  erased ordinary type-code values, erased parametric witnesses, and erased proof/trait
  evidence even when all three disappear before KBackendIR. KBackendIR must contain no
  runtime operand for any of them. *Gate:* the injected malformed-KCore U-P0 test fails with
  `kappa.type.parametric-promotion`; all accepted programs lower identically; KBackendIR
  erasure verification remains green.

## 4. Phase D — prelude, packaging, diagnostics, and closeout

- **U-D0 — prelude/std re-headers.** Per the spec's normalized declarations: `(0 t : Type)`
  headers for `FromInteger`, `FromFloat`, `InterpolatedMacro`, `QuotedLiteralMacro`, `Eq`-family,
  `IsEmpty`/`IsContr`/`IsSubsingleton`/`IsProp`/`IsSet`/`IsGroupoid`, `IsNType`,
  `RuntimeErased`, `IsTrait`; `Thunk`/`Need : (0 A : Type) -> Type`; `SyntaxFragment` ctor
  binders `(@0 t : Type)`; trait term facets like `Eq : (0 A : Type) -> Type`; the
  `expect data IO (0 e : Type) (0 a : Type)` contract forms (coordinate with the
  `Kappa.Builtins` de-hardcoding contract check). Evidence/erasure shapes must not move.
  *Gate:* conformance + full native corpus byte-identical (headers are erased either way).
- **U-D1 — `TypeBelow`/`TypeAtMost` + compat aliases.** Prelude data types
  `TypeBelow (κ : TypeLevel) : Type κ` / `TypeAtMost (κ : TypeLevel) : Type (succ κ)` with the
  erased bound-proof field (their well-formedness is itself a B0/B4 integration test), and the
  transparent aliases `LevelLe`/`LevelLt` (§11.1.2.2 — aliases, *not* traits; goals discharged
  by the universe solver, not instance resolution). *Gate:* `typebelow-package-accepted`,
  `typeatmost-package-accepted`, `level-comparison-compat-aliases-accepted` import.
- **U-D2 — defaulting, rendering, diagnostics, and interfaces.** (a) §11.1.3 universe-metavariable
  discipline: generalize at the boundary when the meta appears in the generalized type;
  least-level instantiation only when unobservable *and* order-independent; otherwise
  `kappa.type.unsolved-metavariable`. (b) Renderer rules: never print `Type : Type`; verbose
  shows `Type : Type1` (Pretty.hs). (c) Flesh out diagnostic payloads to the §3.x catalog
  (especially unbounded-telescope's suggested repair and parametric-promotion's origin/use
  capability fields). (d) Ensure pretty-printing, equality, imported globals, cache keys, and
  any emitted interface artifact preserve normalized levels and witness capability; reject
  an artifact that references an unbound level variable or loses capability provenance.
  *Gate:* defaulting order-independence property tests; verbose renderer snapshots; a
  two-module round trip produces identical judgments and diagnostics.
- **U-D3 — documentation and suite promotion.** Correct the stale KNOWN_SPEC_ISSUES §16/§17
  notes to the final design and mark implementation complete; update ROADMAP and any
  conformance counts. Move `tests/pending-import/spec-universes/` →
  `tests/conformance/universes/` and the
  parametric pending set → `tests/conformance/spec-coverage/parametric-type-witnesses/`
  (per the suite README); delete stale STATUS footers. *Gate:* full suite green; zero
  remaining universe or parametric-witness fixtures under `pending-import`; spec validator
  green; native output byte-identical to the U-P0 baseline.

## 5. The correctness crux

- **Soundness of the ordering solver (the dangerous one).** Everything sits on `leqLevel` being
  *complete and sound* on the fragment (§11.1.2.1 says MUST for both). An unsound `≤` proves
  `Type κ : Type κ` somewhere and the Hurkens door reopens — the exact hole this program
  closes. Property-test against brute-force valuation semantics (finite values + ω per
  variable, all assumption subsets); hand-pin the spec's table (`n ≤ ω`, `ω ≤ succ ω`,
  `succ u ≤ u` rejected, and the `max` laws).
- **Metavariable-solving soundness.** A complete rigid ordering test is not enough: assigning
  an inference variable too eagerly can make acceptance depend on traversal order or smuggle
  self-containment through a later constraint. Keep constraints until a principal assignment
  is justified; generalize/default only at the owning boundary; property-test permutations of
  each fixed constraint set.
- **Assumption hygiene.** Level assumptions are lexically scoped and telescope-ordered; they
  must never leak past their binder (no global constraint store) and an inconsistent set must
  never be *used* (§11.1.2.2). The B0 entry-satisfiability check plus scoped threading (reader
  discipline, not state mutation) is the guard.
- **The vacuous-green trap.** Half the "already passing" corpus passes because declared kinds
  are skipped (`Check.hs:16417`). B2 (no-bump) without B3 (enforcement) proves nothing; B3
  without B2 breaks every parametric acceptance test. They land adjacent, and the B3 gate
  includes the flip-off differential (disable the exemption → acceptance tests must fail) to
  prove enforcement is real.
- **Capability one-way-ness.** No path — elaboration, alias, projection, pattern, static-object
  lookup, trait member, macro output, reflection — may convert witness → ordinary code. The
  C1 enforcement-point list *is* the audit; each point carries a rejected fixture. Generated
  syntax is safe by construction only because all checks live in the single elaborator — if a
  second checking entry point ever appears, it inherits the obligation. The C4 checkpoint is
  the defensive backstop: malformed/generated KCore must fail even if front-end bookkeeping
  was lost.
- **Erasure invariance.** Levels and witnesses are compile-time-only; `runtimeErasedParam`
  (`Repr.hs:537`) already erases `Q0`-and-kind-domain binders. No stage may alter KBackendIR
  for existing programs — byte-identical native output is a per-stage gate, and per
  §34.x a KBackendIR term must never depend on an erased KCore occurrence (new programs with
  `TypeLevel` binders must erase them completely).
- **Corpus reconciliation is explicit.** Active tests pinning pre-redesign behavior
  (`universe-metavar-generalization.kp`, `universe-type-in-type-reject.kp`'s code pin, the
  `imported-anon` family pins) are rewritten *in the same commit* as the behavior flip, each
  with a comment citing the new spec rule — never silently weakened, never left red.

## 6. Verification

1. **The conformance gate** (`test/Spec.hs` over `tests/conformance/`) green at every stage;
   staged fixtures import per the stage's list (the plan names every file).
2. **Solver property tests** (A1): rigid `≤` ⇔ semantic ordinal ≤ under exhaustive small
   valuations, with and without assumptions; metavariable assignments are order-independent;
   self-containment classification is exact.
3. **Native byte-identical**: `test/native/run-native-tests.sh` output-differential on the
   existing corpus each phase (front-end-only program; run isolated — the harness is not
   concurrency-safe).
4. **Non-vacuousness differentials** (B3): disable B2's exemption in a scratch build — the
   parametric acceptance corpus must fail; re-enable — green. Same trick for C1 (disable
   promotion checks — the `rejected-*` corpus must fail to fail).
5. **Soundness pins**: KNOWN_SPEC_ISSUES §16/§17 repros as negative fixtures
   (`data U : Type0 = MkU (t : Type0)`; `(i : TypeLevel) -> Type i`; `Type0 : Type0`).
6. **KCore/interface negative injection** (C4/D2): a fabricated witness-to-code promotion and
   an interface with escaped/unbound level identity both fail closed before KBackendIR.
7. **`scripts/validate.py`** stays green over docs/tests touched (reserved spellings use
   real `ω` — confirm the validator's forbidden-character list doesn't flag it).

## 7. Risks

- **R-corpus-flag-day (highest).** Bare-`Type`-fixation + kind enforcement (B3) and the
  generalization flip (C2) touch every polymorphic declaration in the prelude, corpus, and
  examples. Mitigation: B2 before B3; B3 deliberately minimal (one skip removed + reconciled
  pins); C2 last in its phase with a full-corpus sweep gate; each stage independently
  revertible.
- **R-add-solver-completeness (highest).** Arbitrary ordinal `u + v` is noncommutative and
  invalidates the old max-of-offset-atoms design. A plausible-looking rewrite system can be
  incomplete on open terms while passing every closed example. Require a documented decision
  procedure, reference semantics, exhaustive small-expression differential, and assumption
  fuzzing before A1 is accepted; do not weaken §11.1.2.1's completeness requirement silently.
- **R-solver-subtlety.** Ordinal arithmetic with `add`/`max`/assumptions has classic edge cases
  (`1 + ω = ω`, `ω + 1 > ω`, max distribution, and consistent assumption cycles such as
  `u ≤ v, v ≤ u`). The property harness and spec-table pins are the mitigation; keep the
  fragment exactly §11.1.1 and reject `Type (f u)` when `f` is noncanonical.
- **R-semantic-identity-laundering.** Name-based checks accept a shadowed `+`/`max`/`<`, while
  checking only the selected trait name can accept user evidence. Carry resolved global and
  instance identities into canonicalization; transparent aliases may reduce to the standard
  head, but macros, imports, local fixities, and generated helpers receive no name-based
  privilege.
- **R-forall-flag-day.** `forall a. T` is normatively an explicit erased Pi, unlike today's
  implicit lowering. Unapplied generic calls may change behavior. Pin explicit-vs-implicit
  application before C2, then reconcile every affected declaration in C2's commit rather
  than retaining an undocumented insertion heuristic.
- **R-performance.** `leqLevel` runs inside conversion — the hottest checker path. Levels are
  almost always closed finite; keep the closed-finite fast path allocation-free (compare
  offsets), and only build assumption closures when variables are present. Watch check-time on
  the big corpus (`Check.hs` already dominates build time).
- **R-hidden-promotion-paths.** `Check.hs` is ~20k lines with many lookup/facet/reflection
  seams; a missed seam silently launders a witness into type-code. Mitigation: the C1
  point-by-point audit with per-point fixtures, plus the grep-level invariant that every
  `Type ρ`-demand site consults the capability bit.
- **R-defaulting-order-dependence.** §11.1.3's least-level instantiation must be
  order-independent or rejected; implement as a post-solve check (recompute under permuted
  constraint orders in debug builds) rather than trusting traversal order.
- **R-interface-capability-loss.** An imported alias/projection reconstructed without its
  witness bit can launder a parametric witness into ordinary type-code. Keep level identity,
  capability, and origin in the same typed interface record; reject incomplete artifacts.

## 8. Sub-stages, ordering, gates

| sub | what | gate (abridged; full lists above) |
|---|---|---|
| **U-P0** | baseline + missing fixtures | pending files validate |
| **U-A0** | canonical intrinsic `Level` AST | Core laws; conformance/native green |
| **U-A1** | add-aware constraints/metas/`≤` | decision-procedure properties |
| **U-A2** | first-class levels + owned operations | identity/shadowing/index fixtures |
| **U-B0** | proof binders → scoped assumptions | proof and inconsistency fixtures |
| **U-B1** | dependent-formation ceilings | bounded/unbounded fixtures |
| **U-B2** | parametric no-bump | non-vacuous acceptance |
| **U-B3** | enforce classifiers; bare `Type0` | reconciled corpus green |
| **U-B4** | data universes + ctor-size rule | ctor fixtures; KSI §16 rejects |
| **U-C0** | capability through KCore/interfaces | capability round trip |
| **U-C1** | promotion enforcement across (a)-(g) seams | all `rejected-*` promotion fixtures; accepted set green |
| **U-C2** | generalization + asymmetric `forall` | corpus/native; call-shape fixtures |
| **U-C3** | traits/evidence/boxes end-to-end | 8 box/trait/reflection fixtures import |
| **U-C4** | KCore verifier + erasure provenance | malformed Core rejects; erasure clean |
| **U-D0** | prelude/std `(0 t : Type)` re-headers + expect contracts | native byte-identical |
| **U-D1** | `TypeBelow`/`TypeAtMost`; `LevelLe`/`LevelLt` aliases | 3 packaging fixtures import |
| **U-D2** | defaulting/rendering/artifacts | order-independent; module round trip |
| **U-D3** | docs closeout and suite promotion | no universe/witness fixtures left pending; full gate green |

Ordering rationale: A before everything (B/C both speak `Level`); B0→B1 (ceilings consume
assumptions); B2 with/before B3 (enforcement without the exemption breaks the acceptance
corpus); B4 after B1+B2 (size rule uses assumptions + exemption); C0→C1 (enforce what is
classified); C2 after C1 (the default flip relies on promotion errors for the "prefer
parametric, report demand" rule); C3 integrates traits/reflection; C4 closes the trusted
KCore boundary. D0/D1 then exercise the completed discipline in the prelude, D2 closes
inference/artifact behavior, and D3 promotes the suites. A, B, and C each end corpus-green —
the plan has no long-lived red state.

## 9. Implementation checks (resolve with tests, not design drift)

- **Kind-meta boundary generalization (B3/D2).** The `(@__k : Type0)` alias-parameter
  generalization (`Check.hs:16401`) is behavior the corpus relies on
  (`alias-param-generalization.kp`). Retain it only when it is the explicit §11.1.3 boundary
  generalization of an observable universe metavariable; otherwise solve to the least level
  only under D2's order-independence rule or reject.
- **Higher-universe data backend neutrality (B4/C4).** A `data X : Type3` changes static
  classification, not runtime representation. Confirm with a KCore/KBackendIR differential
  that only compile-time levels/capabilities change and every `TypeLevel` or witness operand
  erases before backend lowering.
- **Artifact scope (C0/D2).** The compiler currently has no full separate-compilation type
  interface. Put normalized levels/capabilities into the nearest typed module artifact now,
  and make the eventual serialized interface consume that record rather than inventing a
  second representation.
- **Operation identity transport (A2/C0).** Canonicalization must key on declaration and
  selected-evidence identity that remains stable through imports, aliases, generated syntax,
  and typed artifacts. Add a round-trip test before treating an imported `Add TypeLevel`
  application as solver-owned.

## Critical files

- `src/Kappa/Core.hs` — `CSort`/`VSort` carry `Level`; Core retains enough binder/domain
  structure to derive or store witness capability and first-class `TypeLevel` terms.
- `src/Kappa/Check.hs` — everything else: `sortName`/spellings (`2315`), conversion+solver
  hook (`1346`), `inferType` (`4947`), Pi/record/exists formation (`4228`, `4106`, `5183`),
  `elabForall` (`5118`), alias kinds (`16390-16440`, the `16417` skip), data headers + ctor
  telescopes (`16461-16516`), sig universalization (`16277`, `8218`), static-object selection
  (`6533-6610`), reflection seams (`4149`, `4618`); the new `Level` solver + `Assumps` module
  (new file `src/Kappa/Level.hs` recommended, pure + property-testable).
- `src/Kappa/Explain.hs` + `src/Kappa/Config.hs` — five diagnostic families, six portable
  aliases, and their normative payload/rendering fields.
- `src/Kappa/Prelude.hs` / `src/Kappa/Builtins.hs` — `TypeLevel`, the five canonical level
  heads, `__compareTypeLevel`, `Successor`/`Max`, all compiler-owned `TypeLevel` operation
  instances, `LevelLe`/`LevelLt`, `TypeBelow`/`TypeAtMost`, and trait re-headers.
- Resolver/global/instance identity metadata in `Check.hs` — canonicalize standard operations
  by semantic identity after ordinary resolution; reject shadowed or user-owned evidence.
- `src/Kappa/Lexer.hs` / `src/Kappa/Parser.hs` — reserved `ω`/`Typeω`/`Type(ω+n)` spellings.
- `src/Kappa/Pipeline.hs` and the typed module/global metadata in `Check.hs` — preserve levels,
  rigid-variable identity, and witness capability across module/artifact boundaries.
- `src/Kappa/Backend/Repr.hs` + `src/Kappa/Backend/Verify.hs` — typed erasure provenance and
  fail-closed verification that levels/witnesses never become runtime operands.
- `test/Spec.hs` — pure level solver properties, malformed-KCore tests, and interface round trips.
- `tests/pending-import/spec-universes/`, `tests/pending-import/spec-coverage/
  parametric-type-witnesses/` — the staged gates; promoted to `tests/conformance/` as stages land.

## Spec anchors

- **§11.1.1** level expressions / `TypeLevel` / reserved spellings; **§11.1.2** predicative
  typing; **§11.1.2.1** ordering + cumulativity (solver MUST be decidable + complete);
  **§11.1.2.2** canonical level heads, compiler-owned operation instances, comparison, and
  semantic-identity-gated proof assumptions;
  **§11.1.2.3** bare `Type` = `Type0`; **§11.1.2.3A** parametric type witnesses (the capability
  rules); **§11.1.2.4** inference (no hidden metas); **§11.1.2.5** first-class levels;
  **§11.1.2.6** bounds are ordinary erased evidence (no special syntax); **§11.1.2.7** no
  universe of universes; **§11.1.2.8** formation ceilings + parametric no-bump +
  `TypeBelow`/`TypeAtMost`; **§11.1.3** defaulting; **§11.1.4** intrinsic compile-time values.
- **§11.3** `forall` desugaring; **§11.3.3** implicit universalization + the parametric default.
- **§10.4.1** constructor universe-size rule (parametric exemption; schematic header checking).
- **§11.4.2** Boolean-to-type coercion at proof-binder positions (level-assumption recognition).
- **§7.6.1** static-object facets; **§13.2.4A** parametric fields; **§14.3.1A** trait evidence;
  **§17.1.7A** parametric pattern binders; **§21.6.2** macros/reflection; §6.x lookup
  admissibility (term-position witness demand).
- **§30.2.2.9** KCore capability and erasure-provenance invariant; **§34.3** lowering legality.
- **§28.2.1** `Successor`/`Max` operation traits and **§28.2** compiler-owned `TypeLevel`
  instance minimum/non-instance exclusions.
- **§3.x diagnostics catalog** — five families, six aliases, and their required payloads.
- `docs/notes/KNOWN_SPEC_ISSUES.md` **§16/§17** — the soundness holes this closes (note: §17's
  working-tree annotation describes the superseded cut; correct it in D3).
