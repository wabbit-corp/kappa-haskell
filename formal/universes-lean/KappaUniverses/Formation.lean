import KappaUniverses.Capability
import KappaUniverses.Solver

/-!
# Dependent formation and universe ceilings

This module models `docs/Spec.md` §§11.1.2.7–11.1.2.8. A valid ceiling must be
well-scoped outside the telescope's local level variables and must semantically
bound the component classifier under the active local assumptions.
-/

namespace Kappa.Universes

namespace LevelExpr

def OccursVar (needle : Nat) : LevelExpr → Prop
  | .zero | .omega => False
  | .var id => needle = id
  | .succ u => OccursVar needle u
  | .add u v | .max u v => OccursVar needle u ∨ OccursVar needle v

instance occursVarDecidable (needle : Nat) :
    (u : LevelExpr) → Decidable (OccursVar needle u)
  | .zero | .omega => isFalse (by simp [OccursVar])
  | .var id => inferInstanceAs (Decidable (needle = id))
  | .succ u => occursVarDecidable needle u
  | .add u v | .max u v =>
      match occursVarDecidable needle u with
      | isTrue hu => isTrue (Or.inl hu)
      | isFalse hu =>
          match occursVarDecidable needle v with
          | isTrue hv => isTrue (Or.inr hv)
          | isFalse hv => isFalse (by
              intro h
              exact h.elim hu hv)

def updateVar (valuation : Valuation) (needle : Nat) (value : LevelValue) : Valuation :=
  fun id => if needle = id then value else valuation id

theorem eval_update_of_not_occurs
    (valuation : Valuation)
    (needle : Nat)
    (value : LevelValue)
    (u : LevelExpr)
    (hFresh : ¬ OccursVar needle u) :
    eval (updateVar valuation needle value) u = eval valuation u := by
  induction u with
  | zero => rfl
  | omega => rfl
  | var id =>
      simp [OccursVar] at hFresh
      simp [eval, updateVar, hFresh]
  | succ u ih =>
      exact congrArg LevelValue.succ (ih hFresh)
  | add u v ihu ihv =>
      have hu : ¬ OccursVar needle u := fun h => hFresh (Or.inl h)
      have hv : ¬ OccursVar needle v := fun h => hFresh (Or.inr h)
      simp [eval, ihu hu, ihv hv]
  | max u v ihu ihv =>
      have hu : ¬ OccursVar needle u := fun h => hFresh (Or.inl h)
      have hv : ¬ OccursVar needle v := fun h => hFresh (Or.inr h)
      simp [eval, ihu hu, ihv hv]

end LevelExpr

/-- A level expression is outer when it mentions none of the telescope locals. -/
def IndependentOf (locals : List Nat) (u : LevelExpr) : Prop :=
  ∀ id, id ∈ locals → ¬ LevelExpr.OccursVar id u

instance independentOfDecidable (locals : List Nat) (u : LevelExpr) :
    Decidable (IndependentOf locals u) := by
  unfold IndependentOf
  infer_instance

/-- A semantic universe ceiling valid at one dependent component. -/
structure ValidCeiling
    (assumptions : Assumptions)
    (locals : List Nat)
    (component ceiling : LevelExpr) : Prop where
  outer : IndependentOf locals ceiling
  bounds : assumptions.Entails ⟨component, ceiling⟩

/-- A telescope is accepted only when every component fits one outer ceiling. -/
structure TelescopeAccepted
    (assumptions : Assumptions)
    (locals : List Nat)
    (components : List LevelExpr)
    (ceiling : LevelExpr) : Prop where
  outer : IndependentOf locals ceiling
  componentsFit :
    ∀ component, component ∈ components → assumptions.Entails ⟨component, ceiling⟩

def strictBound (localId : Nat) (ceiling : LevelExpr) : Constraint :=
  ⟨.succ (.var localId), ceiling⟩

def atMostBound (localId : Nat) (ceiling : LevelExpr) : Constraint :=
  ⟨.var localId, ceiling⟩

/-- An erased `i < κ` assumption supplies exactly the ceiling needed by `Type i`. -/
theorem strict_bound_provides_ceiling
    (localId : Nat)
    (ceiling : LevelExpr)
    (hOuter : IndependentOf [localId] ceiling) :
    ValidCeiling [strictBound localId ceiling] [localId]
      (.succ (.var localId)) ceiling := by
  constructor
  · exact hOuter
  · intro valuation hModel
    exact hModel (strictBound localId ceiling) (by simp)

/-- An erased `i ≤ κ` bound classifies `Type i` at `Type (succ κ)`. -/
theorem at_most_bound_provides_successor_ceiling
    (localId : Nat)
    (ceiling : LevelExpr)
    (hOuter : IndependentOf [localId] ceiling) :
    ValidCeiling [atMostBound localId ceiling] [localId]
      (.succ (.var localId)) (.succ ceiling) := by
  constructor
  · intro id hMember
    have hId : id = localId := by simpa using hMember
    subst id
    exact hOuter localId (by simp)
  · intro valuation hModel
    exact LevelValue.succ_mono
      (hModel (atMostBound localId ceiling) (by simp))

/-- A component already independent of the telescope may be its own ceiling. -/
theorem independent_component_is_own_ceiling
    (locals : List Nat)
    (component : LevelExpr)
    (hOuter : IndependentOf locals component) :
    ValidCeiling [] locals component component := by
  constructor
  · exact hOuter
  · intro valuation _
    exact LevelValue.le_refl (component.eval valuation)

/--
The semantic diagonal argument behind unbounded-telescope rejection: an outer
expression cannot bound `succ i` for every instantiation of local `i`.
-/
theorem independent_expression_cannot_bound_local_successor
    (localId : Nat)
    (ceiling : LevelExpr)
    (hIndependent : ¬ LevelExpr.OccursVar localId ceiling) :
    ¬ Assumptions.Entails [] ⟨.succ (.var localId), ceiling⟩ := by
  intro hEntails
  let base : LevelExpr.Valuation := fun _ => .zero
  let ceilingValue : LevelValue := ceiling.eval base
  let witness : LevelExpr.Valuation :=
    LevelExpr.updateVar base localId ceilingValue
  have hModel : Assumptions.SatisfiedBy witness [] := by
    intro constraint hMember
    simp at hMember
  have hBound := hEntails witness hModel
  have hCeiling : ceiling.eval witness = ceilingValue := by
    exact LevelExpr.eval_update_of_not_occurs
      base localId ceilingValue ceiling hIndependent
  have hLocal : witness localId = ceilingValue := by
    simp [witness, LevelExpr.updateVar]
  unfold Constraint.Holds at hBound
  change LevelValue.succ (witness localId) ≤ ceiling.eval witness at hBound
  rw [hLocal, hCeiling] at hBound
  exact LevelValue.succ_not_le ceilingValue hBound

/-- No ceiling independent of `i` can classify `(i : TypeLevel) -> Type i`. -/
theorem no_unbounded_telescope_ceiling
    (localId : Nat)
    (ceiling : LevelExpr) :
    ¬ ValidCeiling [] [localId] (.succ (.var localId)) ceiling := by
  intro hCeiling
  have hIndependent := hCeiling.outer localId (by simp)
  exact independent_expression_cannot_bound_local_successor
    localId ceiling hIndependent hCeiling.bounds

/-- In particular, `ω` is not an automatic ceiling for an unbounded local level. -/
theorem omega_is_not_an_unbounded_ceiling (localId : Nat) :
    ¬ ValidCeiling [] [localId] (.succ (.var localId)) .omega := by
  exact no_unbounded_telescope_ceiling localId .omega

/-- A one-component valid ceiling gives an accepted telescope. -/
theorem singleton_telescope_accepted
    {assumptions : Assumptions}
    {locals : List Nat}
    {component ceiling : LevelExpr}
    (hCeiling : ValidCeiling assumptions locals component ceiling) :
    TelescopeAccepted assumptions locals [component] ceiling := by
  constructor
  · exact hCeiling.outer
  · intro candidate hMember
    have hEq : candidate = component := by simpa using hMember
    subst candidate
    exact hCeiling.bounds

theorem independent_max
    {locals : List Nat}
    {left right : LevelExpr}
    (hLeft : IndependentOf locals left)
    (hRight : IndependentOf locals right) :
    IndependentOf locals (.max left right) := by
  intro id hMember hOccurs
  exact hOccurs.elim (hLeft id hMember) (hRight id hMember)

/-- The premises of the ordinary dependent Pi formation rule. -/
structure PiAccepted
    (assumptions : Assumptions)
    (locals : List Nat)
    (domainLevel codomainLevel ceiling : LevelExpr) : Prop where
  domainOuter : IndependentOf locals domainLevel
  codomainCeiling : ValidCeiling assumptions locals codomainLevel ceiling

def piFormationLevel (domainLevel ceiling : LevelExpr) : LevelExpr :=
  .max domainLevel ceiling

theorem pi_result_is_outer
    {assumptions : Assumptions}
    {locals : List Nat}
    {domainLevel codomainLevel ceiling : LevelExpr}
    (hPi : PiAccepted assumptions locals domainLevel codomainLevel ceiling) :
    IndependentOf locals (piFormationLevel domainLevel ceiling) := by
  exact independent_max hPi.domainOuter hPi.codomainCeiling.outer

theorem pi_domain_fits_result
    (valuation : LevelExpr.Valuation)
    (domainLevel ceiling : LevelExpr) :
    domainLevel.eval valuation ≤ (piFormationLevel domainLevel ceiling).eval valuation := by
  exact LevelValue.le_max_left (domainLevel.eval valuation) (ceiling.eval valuation)

theorem pi_codomain_fits_result
    {assumptions : Assumptions}
    {locals : List Nat}
    {domainLevel codomainLevel ceiling : LevelExpr}
    (hPi : PiAccepted assumptions locals domainLevel codomainLevel ceiling) :
    assumptions.Entails ⟨codomainLevel, piFormationLevel domainLevel ceiling⟩ := by
  intro valuation hModel
  exact LevelValue.le_trans
    (hPi.codomainCeiling.bounds valuation hModel)
    (LevelValue.le_max_right
      (domainLevel.eval valuation) (ceiling.eval valuation))

/--
Formation level for a binder whose annotation is the universe `Type rho`.
Ordinary code stores that universe value and contributes `succ rho`; a
parametric witness contributes no field merely by being bound.
-/
def universeBinderFormationLevel
    (capability : TypeCapability)
    (rho bodyLevel : LevelExpr) : LevelExpr :=
  match capability with
  | .ordinaryCode => .max (.succ rho) bodyLevel
  | .parametricWitness => bodyLevel

theorem ordinary_universe_binder_contributes
    (rho bodyLevel : LevelExpr) :
    universeBinderFormationLevel .ordinaryCode rho bodyLevel =
      .max (.succ rho) bodyLevel := by
  rfl

theorem parametric_universe_binder_no_bump
    (rho bodyLevel : LevelExpr) :
    universeBinderFormationLevel .parametricWitness rho bodyLevel = bodyLevel := by
  rfl

/-- The no-bump case retains witness capability and therefore cannot expose type code. -/
theorem parametric_no_bump_is_capability_safe
    (rho bodyLevel : LevelExpr) :
    universeBinderFormationLevel .parametricWitness rho bodyLevel = bodyLevel ∧
      ¬ CanCoerce .parametricWitness .ordinaryCode := by
  exact ⟨rfl, no_parametric_witness_to_ordinary_code⟩

/-- Using the witness as a type still contributes its declared level `rho`. -/
def parametricWitnessTypeUseLevel (_rho : LevelExpr) : LevelExpr :=
  _rho

theorem parametric_witness_type_use_keeps_level (rho : LevelExpr) :
    parametricWitnessTypeUseLevel rho = rho := by
  rfl

/--
Universe level of the dependent pair `(0 t : Type rho, a : t)`. The parametric
field itself does not bump; the value field `a : t` contributes exactly `rho`.
-/
def parametricDependentPairLevel (rho : LevelExpr) : LevelExpr :=
  universeBinderFormationLevel .parametricWitness rho
    (parametricWitnessTypeUseLevel rho)

theorem parametric_dependent_pair_stays_at_declared_level (rho : LevelExpr) :
    parametricDependentPairLevel rho = rho := by
  rfl

theorem parametric_dependent_pair_smallness_is_safe (rho : LevelExpr) :
    parametricDependentPairLevel rho = rho ∧
      ¬ CanCoerce .parametricWitness .ordinaryCode := by
  exact ⟨rfl, no_parametric_witness_to_ordinary_code⟩

/-- Projecting a type field preserves its original capability. -/
def projectedTypeFieldCapability (capability : TypeCapability) : TypeCapability :=
  capability

theorem parametric_projection_preserves_witness :
    projectedTypeFieldCapability .parametricWitness = .parametricWitness := by
  rfl

theorem parametric_projection_cannot_produce_code :
    ¬ CanCoerce (projectedTypeFieldCapability .parametricWitness) .ordinaryCode := by
  exact no_parametric_witness_to_ordinary_code

end Kappa.Universes
