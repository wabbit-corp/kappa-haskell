# Proof plan

The end goal is an assurance chain from the normative Kappa specification to the Haskell checker. The current project
establishes the universe algebra and the sound core of the normalization/solver layer; its claims remain deliberately
narrower than full language consistency.

## 1. Universe algebra (completed for the current model)

- Define the rigid canonical grammar from §11.1.1.
- Give it ordinal semantics below `ω²`.
- Prove successor strictness, absence of a top level, sound local entailment, and the impossibility of `Type u : Type u`.
- Record the one-way parametric witness capability rule.

## 2. Normalization and solver (in progress)

- [x] Add level metavariables and substitutions separately from rigid expressions.
- [x] Prove substitution agrees with semantic metavariable update.
- [x] Specify normalization for sound open identities over successor/addition/maximum.
- [x] Prove normalization preserves denotation and is idempotent, including with unresolved metavariables.
- [x] Implement and prove an executable decision procedure for closed constraints.
- [x] Define an open proof-certificate kernel and prove every checked certificate semantically sound.
- [x] Prove the occurs-checked single-assignment API returns a model of the accepted equation.
- [x] Extend assignments to ordered solver states and prove each accepted update preserves all prior equations and
  constraint satisfiability.
- [ ] Implement the complete open-expression decision procedure for variables, ordinal addition, maximum, and local
  assumptions; prove both soundness and completeness against semantic entailment.
- [x] Prove structural search emits only certificate-kernel derivations, so executable solver soundness follows from the existing
  certificate theorem.

## 3. Formation and ceilings (completed for the semantic reference model)

- [x] Formalize telescope scoping and the ceiling-independent-of-local-binders condition from §§11.1.2.7–11.1.2.8.
- [x] Prove strict and at-most erased bounds supply the classifiers required by `TypeBelow` and `TypeAtMost`.
- [x] Prove accepted bounded telescopes and Pi types have well-scoped outer classifiers.
- [x] Prove unbounded level-indexed telescopes admit no independent ceiling expression; `ω` is a direct corollary.
- [x] Formalize the parametric no-bump rule together with capability preservation, never in isolation.

## 4. KCore universe calculus (in progress)

- [x] Define a small intrinsically scoped KCore fragment with sorts, dependent functions, variables, application, and
  the two type capabilities.
- [x] Define scope-preserving renaming, weakening, substitution, and dependent instantiation operations.
- [x] Integrate capability evidence into application typing.
- [x] Add dependent Sigma formation with the parametric no-bump rule.
- [x] Prove `(0 t : Type rho, a : t) : Type rho`, including the `rho = 0` specification example.
- [x] Prove Sigma projection preserves parametric capability and cannot yield ordinary type code.
- [x] Prove universe-sort regularity and rule out a checked `Type u : Type u` judgment.
- [x] Prove parametric literals and variables cannot satisfy an ordinary-code application premise.
- [x] Prove typing weakening and renaming, with exact preservation of variable capabilities.
- [x] Prove general capability-compatible substitution and the dependent newest-variable substitution lemma.
- [ ] Define beta reduction and prove subject reduction.
- [ ] Prove the remaining regularity and canonical-forms lemmas needed by the consistency argument.

## 5. Consistency result

- Give the KCore fragment a semantic interpretation or prove normalization by logical relations.
- Derive that the empty type has no closed inhabitant.
- Reconstruct the relevant Girard/Hurkens encoding attempt and show the exact failed premise is the already-proved
  self-containment judgment, rather than merely asserting that the paradox is unavailable.

## 6. Haskell refinement

- Extract executable level normalization/ordering test vectors from Lean.
- Relate the future Haskell `Level`, constraint solver, and KCore lint invariants to the Lean definitions.
- Differential-test the implementation against the proved reference model.
- Keep this step separate: the normative specification remains the source model even while implementation work lags.
