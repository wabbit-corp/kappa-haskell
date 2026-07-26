# Universes implementation contract

This note is the implementation contract for `docs/UNIVERSES-PLAN.md`. The
current `docs/Spec.md` is normative when this note, historical tests, or old
implementation comments disagree with it.

## Root-cause groups

- Level indices need a typed, total, stable, serializable KCore-term identity;
  the current closed standard-operation recognizer is not an admissibility
  judgment and cannot represent neutral first-class levels.
- Constructor normalization, exact rigid entailment, and selected-meta
  inference are different algorithms with different completeness contracts.
  They must not share an ambiguous success/failure result.
- Fresh polymorphism belongs only to complete semantic declaration/SCC
  boundaries. Declaration constraints must have one authority: ordinary
  implicit erased proof binders, with summaries derived as checked caches.
- KCore arithmetic evidence is a replayable theorem plus canonical assumption
  dependencies. Structural proof spelling, proof-object allocation, and solver
  internals are not semantic identity.
- Recursive declaration-schema calls are explicit same-or-lower edges;
  ordinary recursion over a first-class `TypeLevel` argument is not a schema
  edge.
- Schema lifts remain direct expected-type operations. Reifying a declaration
  schema into a first-class function is a separate bounded eta-expansion, and
  quantifier interchange requires selected ordinary evidence.
- User level functions affect nominal roles only through selected
  `std.typelevel.Monotone` evidence frozen into the signature closure. Names,
  theorem scanning, or an unverified role assertion are not evidence.
- Source, solver, KCoreText, interface, native, and harness artifacts must carry
  the same algebra/normalizer/entailment/inference/certificate versions and
  must reject incompatible inputs before semantic use.
- KCore nominal declarations, certificate replay, and backend erasure form one
  trust boundary. Canonical data declarations always spell every effective
  role and select a schema certificate, including declarations with no
  universe parameters; a missing certificate is never reconstructed from a
  producer-side default.
- A schema lift may erase only after the checkpoint and KBackendIR boundary
  have matched its payload's inferred nominal family, source universe vector,
  and saturated ordinary arguments against the recorded source, and have
  checked the recorded target against the surrounding typed expectation.
- Test-ledger metadata and Appendix T assertions are executable contracts, not
  inventory prose. Every suite records polarity, harness outcome, category,
  capabilities, owner stage, and complete files; canonical directives operate
  on the current artifact unless their syntax explicitly names another one.

## Invariants

- Observation mode, quantity, access mode, and formation are independent.
- Pi/Sigma formation mode is explicit checked KCore metadata. It is derived
  from the domain judgment during elaboration, serialized, and independently
  replayed by KCoreText; observation mode is never reused as formation
  authority.
- Bare `Type` introduces a fresh level metavariable; grouped annotations share
  one metavariable; declaration and local SCCs produce principal explicit or
  hidden universe schemas.
- Both `forall a.` and `forall (a : S).` elaborate to implicit, erased
  binders. Writing the domain constrains inference but does not change
  application syntax or binder explicitness.
- Explicit schemas are complete, rigid declaration identity. Every global,
  constructor, associated-member, and generalized-local use instantiates its
  schema explicitly in KCore and KCoreText.
- Universe generalization runs once over the semantic declaration SCC,
  including body dependencies and body-generated constraints. Every member
  publishes the same normalized SCC constraint block; occurrence checking
  specializes and proves that block, not only the member type.
- The leading authenticated declaration-constraint telescope is discharged at
  every occurrence before occurrence-specific implicit or explicit arguments
  are applied. Source application, generated trait/instance selection,
  constructor synthesis, and internal helper application share this boundary;
  no generated caller may feed its first semantic argument into a hidden
  `LevelLe` proof slot.
- A signed declaration whose interface is deferred until its body is checked
  retains every universe occurrence metavariable in that interface. Neither
  occurrence principalization nor defaulting may solve those metavariables
  before the complete semantic declaration SCC contributes its body
  constraints.
- Every provisional declaration occurrence records its typed global or
  constructor facet, source metas, and fresh Core level spine. Finalization
  projects that exact occurrence before zonking; an arity-only projection is
  used only when every source spine proves the same morphism. Equal-arity
  occurrences with different source orders therefore remain distinguishable
  without imposing a fabricated declaration-wide ordering on an evolving
  interface.
- Every block/do-local declaration is closure-converted over its exact semantic
  free-variable set. Local nominal families retain one declaration-site
  identity, while each occurrence applies the current captured arguments;
  scoped locals additionally capture the nearest lexical nominal-scope token,
  which is compile-time-only and cannot appear in a transparent escaping
  interface. Block and do scopes use the same declaration elaborator.
- An effect operation header is part of the owning effect interface's
  observable universe interface. The interface telescope covers its parameter
  and operation-signature levels; each operation selection freshens that one
  telescope and specializes the complete stored operation telescope with the
  same level spine. Effect-label aliases preserve the interface instance they
  name, and scoped effects obey the same rule without becoming module-visible.
- Standard `TypeLevel` syntax is recognized through checked semantic identity
  and selected evidence. Source spelling, projected member names, and rendered
  terms are never proof. Transparent aliases are admitted only after typed Core
  proves an exact rename or eta-expansion of an already authenticated
  operation; evaluating a user function on probes is not authentication.
- Recognized level assumptions are lexical. A cumulative lift cites an
  in-scope proof binder, a normalized declaration constraint, or an
  independently verified certificate; endpoint inequalities and authority are
  both replayed after every substitution.
- Natural level addition is commutative componentwise addition on
  `omega*c+n` in the checker, solver, interpreter, C, LLVM, and prelude laws.
- The required `TypeLevel` laws are checked source proofs through that same
  semantic bridge. The standard module does not use `unsafeAssertProof` to
  assert its algebra.
- Parametric type witnesses seal only at declared parametric boundaries.
  Ordinary sinks reject every nonempty dependency-origin set.
- KCore observation boundaries are enforced at declarations, binders,
  arguments, and declared fields, not recursively at presentation children of
  the same term. Lambda dependency discharge is applied before the enclosing
  boundary is tested, while a declared terminal `Type` result is checked in
  its lambda scope so abstraction cannot launder a returned parametric type
  witness.
- Observation dependency analysis is structural over term bodies but uses
  normal checked transparency for classifier types. In particular, record and
  nominal field metadata may be recovered through transparent type aliases;
  recursion is bounded by the global-body dependency equations, not by making
  every global opaque to type normalization.
- Ordinary trait evidence may mediate callable runtime behavior over its
  associated static members. The finite dependency calculus records the
  resolved trait identity and discharges only an all-trait-projection set at a
  callable boundary with an ordinary runtime terminal result; direct witness
  return and unrelated/package origins remain rejected.
- KCoreText is untrusted, total over finalized typed Core, canonical, and
  independently verifies schemas, uses, dependencies, constraints, evidence,
  certificates, and extensions before KBackendIR lowering.
- Every KCore nominal declaration has a mandatory certificate reference and
  every nominal universe binder has a mandatory effective role. This remains
  true at universe arity zero: the certificate authenticates the ordinary
  signature closure, constructor/eliminator/computation action, quantities,
  observation modes, and representation identity rather than merely a role
  vector.
- A KCore stable ID is the sole semantic identity. Readable names are
  presentation metadata: they do not participate in equality, ordering, or
  semantic hashing. Generated identities derive from normalized semantic
  origins rather than allocation order.
- KCoreText canonicalization is semantics-preserving: it topologically orders
  declaration SCCs, scopes local alpha-renamings lexically, and preserves the
  semantic identities of erased proof binders and canonical certificate
  dependencies while reordering declarations. Extension ownership is
  module-local, and every specialized or generic implementation node requires
  the declaring module's compatible extension.
- Syntax quotations use a versioned KCoreText syntax schema independent of
  Haskell constructor names and source paths. Their capture table is replayed
  against hygienic free occurrences in the decoded syntax.
- Module interfaces have an actual source-free serialized form. Loading an
  interface reconstructs and validates schemas, normalized constraints,
  modes, dependency summaries, certificates, and semantic identities without
  consulting the producer's source or live checker state.
- Declaration-universe variance applies only to fully saturated applications
  of one nominal family. It is never part of definitional equality, ordinary
  unification, instance-candidate selection, or term-argument variance.
- Each nominal schema parameter has a separately recorded inferred role and
  optional explicit upper bound. Role inference starts at `irrelevant` and
  monotonically tightens over one normalized signature closure for the entire
  mutually recursive nominal block; observation, quantity, formation,
  positivity, and runtime erasure are not role evidence.
- Every cross-instance nominal use is represented by an explicit typed
  `schemaLift`. It records the exact family identity, source and target schema
  instances, aligned saturated family arguments, per-role evidence, and an
  independently verified action-certificate identity. A valid lift is
  representation identity and is erased before KBackendIR.
- KBackendIR independently replays the typed source/target alignment before
  erasing a `schemaLift`. Equal arity is not alignment: replacing one recorded
  ordinary argument with a different well-typed argument is a lowering
  violation even when both backends would otherwise erase the evidence.
- A nominal action certificate is a versioned proof object over the normalized
  signature closure, not an assertion attached by the producer. Local and
  imported certificates are replayed independently, including constructor,
  eliminator, iota/case, dependency, quantity, and representation obligations.
- Exported nominal families carry one source-free
  `NominalCumulativitySummary`; semantic hashes include its roles, explicit
  flags, closure hash, certificate identity/version, clause kinds, arity, and
  representation result. Missing, stale, or unsupported summaries make every
  role invariant.
- A serialized pattern carries one typed structural slot for every matched
  component, including wildcards and omitted record fields. Source-visible
  bindings are marked separately. Dependent constructor and record telescopes
  are checked left-to-right after renaming each prior slot; a verifier never
  reconstructs those facts from source names or binder counts.
- Guarded, nested constructor, tuple, record, variant, or/as, and do-kernel
  forms are ordinary finalized Core. KCoreText preserves their checked typing,
  scopes, labels, and control structure; no valid finalized form is rejected
  merely because a checkpoint serializer omitted a schema case.
- Constructor-pattern field classifiers are recovered by aligning the exact
  constructor result with the finalized scrutinee family under the equalities
  introduced by that branch. Constructor-local telescope rigids and existing
  scrutinee rigids occupy disjoint level ranges; repeated indices and occurs
  checks remain load-bearing, and field classifiers are normalized under both
  constructor specialization and branch refinement. Nominal head, universe
  spine, arity, icitness, and structural mismatches still fail closed.
- Every serialized do child is checked against either its inferred finalized
  Core type or, for `return`, the exact enclosing monad result type. Nested do
  actions never acquire a guessed carrier or a hard-coded `IO` type.
- Every stable, total, well-scoped term of type `TypeLevel` may index `Type`.
  Canonical standard operations decompose into solver constructors; every
  other admissible term is a rigid neutral atom keyed by alpha-normalized typed
  KCore identity, resolved globals, and free semantic identities.
- Mutable current facets are not stable level terms in v1. Expression lifting
  runs first, so an immutable snapshot introduced by a do bind may be stable
  even when its source was a mutable read.
- Constructor NF preserves additive multiplicity and max idempotence only.
  Distribution, dominance, cancellation, and equality beyond that form belong
  to exact paired-Presburger rigid entailment. Portable selected-meta inference
  implements only the named assignable fragment and returns the five specified
  result classes.
- Declaration generalization selects metas not free in the environment,
  abstracts them as rigid parametric variables, and rechecks the entire
  declaration/SCC with the finite observation calculus. It never generalizes a
  lambda, pattern, handler, comprehension, or monadic `<-` binder and never
  commutes a quantifier through a constructor implicitly. At an inferred
  declaration boundary, candidate positions come from the completed semantic
  classifier; a freshly instantiated occurrence meta in such a position may
  therefore preserve existing declaration polymorphism, while result-only
  occurrence choices remain minimizable.
- Rigid replay of a recursive local declaration uses the same finalized lexical
  environment as its checked RHS, including the typed recursive self binding,
  local universe telescope, quantity, and all enclosing or sibling
  declarations. Local schema specialization is performed at that lexical de
  Bruijn depth; replay never quotes a local type at depth zero or reconstructs
  an environment from source names.
- Generated declaration constraints are ordinary implicit erased proof
  binders. User-written equivalent binders are reused by semantic equality;
  no side-table constraint list or positional constraint-index evidence remains
  authoritative.
- KCore arithmetic replay uses canonical `arithmetic [indices]` and
  `max-least` evidence, exact rigid entailment, irredundant ordered dependency
  sets, and the five pinned semantic versions. Equivalent proofs and composed
  lifts have identical semantic identity.
- Recursive calls inside one declaration SCC either use the identity schema or
  an explicit complete same-or-lower schema instance. A proved strict decrease
  may contribute to size change; non-strict `<=` never counts as termination.
  Recursive-schema classification and size-change checking consume the
  finalized level assignments and flushed erased proof obligations, never a
  provisional body-elaboration snapshot.
- One inferred recursive declaration SCC owns one hidden universe telescope.
  An implicit same-SCC reference that still carries the provisional
  all-interface-meta spine is rewritten to that shared rigid telescope exactly
  once. Equal-arity references are preserved so an explicit same-or-lower
  recursive instance is never collapsed to identity.
- Unconditional `u <= v` / `v <= u` cycles among inferred local schema metas
  denote one identity by antisymmetry and are quotient-ed before the shared
  telescope is published. Explicit schema parameters are rigid source
  identities and are never merged by this inference step.
- Every inferred expression checked against an expected type crosses the same
  cumulative/schema coercion boundary, including the fallback from
  expected-result-guided application elaboration. Specialized application
  planning cannot bypass schema-lift insertion or recursive-schema rejection.
- A solved inferred implicit type argument retains the authenticated
  creation-site universe coercion when its metavariable is reified into Core.
  Zonking must not erase that proof and KCoreText constructor matching may
  ignore only the verified classifier lift, never a nominal `schemaLift`.
- Expected-type schema eta-reification emits explicit KCore level lambdas and
  proof binders and is bounded by the expected type. It never fills an omitted
  explicit term-level `TypeLevel` argument.
- Nominal role inference selects `Monotone` evidence through ordinary implicit
  resolution before the fixed point and freezes that evidence into the
  independently checked signature closure.
- Finalized observation checking recovers callable interfaces through the
  exact checked type constructors that alter elimination shape without adding
  a runtime binder. In particular, it peels `__captures` annotations and
  expands `Projector Roots Focus` descriptors from their typed root record;
  neither operation is inferred from source names or record shape alone.
- The seeded `__captures` type former takes both its carrier and each region
  identity parametrically and returns the carrier's universe. Capture metadata
  can therefore participate in type identity and interface round trips but can
  never be mistaken for an ordinary runtime dependency.
- When an omitted `Region` argument is constrained by applying a borrowed Pi
  to an anonymous borrow, elaboration solves that argument to the internal
  typed witness `borrowRegionOf argument`. The witness is tied structurally to
  the borrowed term, never minted as a global region or left as a finalized
  metavariable, and its enclosing quantity-0 argument erases before runtime.
- Observation replay over a dependent record telescope carries that exact
  record interface as the classifier of canonical `this` projections. Nested
  records replace, rather than merge, this context, and occurrence paths are
  prefixed back into the enclosing Core tree so diagnostics and origins remain
  stable.
- Every checker-generated match retains the exact checked scrutinee classifier
  whenever that classifier is in scope. In particular, top-level irrefutable
  pattern projections do not ask later phases to reconstruct an erased numeric
  literal carrier from source shape. A genuinely unavailable classifier
  remains a fail-closed analysis error.
- A flexible inferred value-parameter carrier is not evidence that the source
  parameter itself is a type witness. Lowercase value parameters finalize as
  ordinary binders; their carrier metas are generalized into hidden
  parametric binders when unconstrained, or remain governed by pending
  evidence/use-site constraints. The direct `Type` default is reserved for
  explicit non-lowercase declaration parameters such as `A` in `id A x`.
- A non-final discarded action is checked against its actual finalized payload
  type. Defaulting a wholly unconstrained payload to `Unit` remains valid, but
  a constrained function, variant, nominal, or dependent payload must not
  become a spurious linear-drop error merely because a partial diagnostic
  delaborator cannot reconstruct its type syntax.

## Supported cases

All U-E1 through U-E9, current-feature U-F1 through U-F8, and U-G1 through
U-G8 surfaces in the plan are required: explicit and inferred
top-level/local schemas; data, constructor, equality, trait, instance, effect,
projection, package, record, and static-object uses; bounded lexical proof
telescopes; generated and hand-authored KCoreText; interface and semantic-hash
round trips; and interpreter/C/LLVM native paths after erasure.

The 67 first-class-level bundle suites are current requirements with no
capability skips: 29 positive source, 17 negative source, 13 direct solver, and
8 KCoreText suites. Their owning G-stage gates pass, and the exact bundle tree
is active under
`tests/conformance/spec-coverage/first-class-levels-solver-generalization/`.

The eight capability-gated HIIT/HIRT/QIT/QIIT variance suites remain future
syntax only until their complete signature-clause and naturality checkers
exist. Their skips must remain explicit and must not advertise those
capabilities.

## Fail-closed cases

- User-selected level operations do not masquerade as standard solver
  constructors. When they satisfy the admissibility judgment they become
  stable neutral atoms; otherwise they reject at the level-expression
  boundary.
- Inconsistent recognized assumptions reject deterministically.
- Escaped local, field, schema, or metavariable level identities reject at the
  typed checkpoint.
- A local nominal capture telescope that cannot be closed, represented in an
  interface, or specialized from the current lexical context rejects at the
  declaration/use boundary. It is never approximated by dropping captures or
  by minting a runtime-fresh nominal identity.
- Missing/wrong schema instantiations, unavailable proof authorities, forged
  certificates, undeclared extensions, and unsupported typed-Core nodes reject
  before backend emission.
- A role annotation on a non-nominal declaration, an annotation more
  permissive than inference, a partial or mismatched family application, an
  invalid direction, an unsatisfied target schema constraint, an unaligned
  family argument, or an unverified certificate rejects before a schema lift
  can be constructed.
- Imported opaque nominal metadata is accepted only through a verified
  source-free summary. The checker never reconstructs optimistic roles from a
  printed public type or trusts a stable identifier as evidence.
- A declaration occurrence whose specialized schema constraints are not
  proved rejects. Lift evidence must itself derive the claimed endpoints;
  ambient facts cannot make an unrelated selected authority acceptable.
- Effect metadata whose universe spine cannot be tied to its owning interface
  rejects at the typed checkpoint; selection never reuses raw declaration
  metavariables or guesses a `Type0` operation carrier.
- Malformed pattern slot telescopes, mismatched or-pattern binder
  permutations, ill-scoped guards, and malformed do control-flow nodes reject
  during independent KCoreText verification.
- A failed optimized or representation-specific proof falls back only where a
  semantically equivalent generic path exists; it never guesses.
- A level term with the wrong type, unresolved rigid meta, mutable lifetime,
  unstable totality status, ill-scoped identity, or unserializable KCore form
  rejects as a level expression. Opaque or neutral syntax alone is not a
  rejection reason.
- Selected-meta inference outside the portable assignable fragment rejects
  with `E_UNIVERSE_INFERENCE_REQUIRES_ANNOTATION` unless the meta is legally
  generalized. `NoPointwiseLeastSolution` is reported only with a checked
  witness; solver incompleteness is never mislabeled as nonexistence. Compact
  selected-meta assignment graphs are checked before materialization, and
  crossing the exact-solver node budget produces
  `IndeterminateResourceLimit`; it never proves a relation, reports a
  contradiction, or triggers unbounded expansion.
- Rigid parametric rechecking that exposes a proposed generalized value to an
  ordinary sink rejects with `E_GENERALIZATION_PARAMETRIC_ESCAPE`; the checker
  does not keep the unsound generalized declaration as recovery authority.
- Arithmetic evidence with unavailable, duplicate, meta-bearing, or
  non-authoritative assumptions, or with incompatible semantic versions,
  rejects before KCore acceptance.
- An upward, incomparable, implicit non-identity, or incompletely signed
  recursive schema edge rejects with the dedicated recursive-schema family.
- Missing `PreservesParametricForall` or `Monotone` evidence keeps the operation
  unavailable/invariant. The compiler does not search theorem declarations or
  infer an inverse conversion.

## Deferred work

The owner suites for U-E1 through U-E9, the 34 current-feature U-F suites, and
the 67 base plus 4 strengthening U-G suites are active. The artifact-hardening
gap below was discovered by an additional cross-feature probe after that
closeout and remains open; it is not treated as a capability downgrade or a
reason to weaken the valid source program. Other future-stage work must not
remove syntax, semantics, artifact, backend, or performance capabilities
required by the plan or the current specification.

### Artifact hardening discovered after the owner closeout

`CMatch` currently carries a checked scrutinee type but not its checked result
type. Most KCoreText emission sites recover the latter from their expected
context, but a constructor-projection match nested in a dependent type has no
such local context. The source program remains valid and is checked normally;
the generated KCoreText round trip fails closed instead of guessing. The
follow-up is to make match-result metadata explicit in typed Core, preserve it
through rewriting and interfaces, and gate the dependent erased-field fixture
with `assertStageDumpRoundTrips KCore`.
