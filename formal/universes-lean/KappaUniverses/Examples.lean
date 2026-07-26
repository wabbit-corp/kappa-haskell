import KappaUniverses.Soundness
import KappaUniverses.Capability
import KappaUniverses.Meta
import KappaUniverses.State
import KappaUniverses.Normalize
import KappaUniverses.Solver
import KappaUniverses.Formation
import KappaUniverses.Core

/-! Executable and proof-level checks for specification examples. -/

namespace Kappa.Universes.Examples

open Kappa.Universes
open LevelExpr

def closedValuation : Valuation := fun _ => .zero

def one : LevelExpr := .succ .zero

example : LevelExpr.eval closedValuation (LevelExpr.add one LevelExpr.omega) = LevelValue.omega := by
  rfl

example : ¬ LevelExpr.eval closedValuation (LevelExpr.add LevelExpr.omega one) ≤ LevelValue.omega := by
  exact LevelValue.omega_add_one_not_le_omega

example : SortHasType closedValuation .omega (.succ .omega) := by
  exact type_has_successor_type closedValuation .omega

example : ¬ SortHasType closedValuation .omega .omega := by
  exact no_type_in_type closedValuation .omega

example (u : LevelExpr) : ¬ SortHasType closedValuation u u := by
  exact no_type_in_type closedValuation u

example (u : LevelExpr) :
    LevelExpr.normalize (.add .zero (.max u u)) = LevelExpr.normalize u := by
  simp [LevelExpr.normalize, LevelExpr.smartAdd, LevelExpr.smartMax]

def acyclicAssignment : MetaEquation :=
  ⟨0, .succ (.var 2)⟩

example : acyclicAssignment.WellFormed := by
  simp [acyclicAssignment, MetaEquation.WellFormed, LevelTerm.Occurs]

def cyclicAssignment : MetaEquation :=
  ⟨0, .succ (.mvar 0)⟩

example : ¬ cyclicAssignment.WellFormed := by
  simp [cyclicAssignment, MetaEquation.WellFormed, LevelTerm.Occurs]

def zeroMetas : LevelTerm.MetaValuation := fun _ => .zero

example :
    (SolverState.tryExtend closedValuation zeroMetas [] acyclicAssignment).isSome = true := by
  rfl

example (u v : LevelExpr) :
    Derivation [] ⟨u, .max u v⟩ :=
  .maxLeft u v

example :
    (Constraint.selfContainment .omega).checkClosed = some false := by
  exact Constraint.checkClosed_self_containment_false .omega .omega rfl

example :
    (Derivation.search 1 [] .zero .omega).isSome = true := by
  rfl

example :
    (Derivation.search 3 [] (.var 0) (.max (.var 0) (.var 1))).isSome = true := by
  rfl

example :
    ValidCeiling [strictBound 0 .omega] [0] (.succ (.var 0)) .omega := by
  exact strict_bound_provides_ceiling 0 .omega (by
    simp [IndependentOf, LevelExpr.OccursVar])

example :
    ValidCeiling [atMostBound 0 .omega] [0]
      (.succ (.var 0)) (.succ .omega) := by
  exact at_most_bound_provides_successor_ceiling 0 .omega (by
    simp [IndependentOf, LevelExpr.OccursVar])

example :
    ¬ ValidCeiling [] [0] (.succ (.var 0)) .omega := by
  exact omega_is_not_an_unbounded_ceiling 0

example (rho bodyLevel : LevelExpr) :
    universeBinderFormationLevel .parametricWitness rho bodyLevel = bodyLevel ∧
      ¬ CanCoerce .parametricWitness .ordinaryCode := by
  exact parametric_no_bump_is_capability_safe rho bodyLevel

def emptyCoreContext : Core.Context 0 := Fin.elim0

def emptyCapabilityContext : Core.CapabilityContext 0 := Fin.elim0

example (level : LevelExpr) :
    CoreHasType closedValuation emptyCoreContext emptyCapabilityContext
      (.sort level) (.sort (.succ level)) := by
  exact .sort level

example (level : LevelExpr) :
    CoreHasType closedValuation emptyCoreContext emptyCapabilityContext
      (.sort level) (.sort level) → False := by
  exact CoreHasType.no_type_in_type level

def typeIdentity : Core 0 :=
  .lam .ordinaryCode (.sort .zero) (.var 0)

def typeIdentityType : Core 0 :=
  .pi .ordinaryCode (.sort .zero) (.sort .zero)

theorem typeIdentity_typed :
    CoreHasType closedValuation emptyCoreContext emptyCapabilityContext
      typeIdentity typeIdentityType := by
  exact .lam (.sort .zero) (.var 0)

example :
    CoreHasType closedValuation
      (Core.Context.extend emptyCoreContext (.sort .zero))
      (Core.CapabilityContext.extend emptyCapabilityContext .parametricWitness)
      (Core.weaken typeIdentity) (Core.weaken typeIdentityType) := by
  exact CoreHasType.weaken_preserves_typing typeIdentity_typed
    (.sort .zero) .parametricWitness

example :
    CoreHasType closedValuation emptyCoreContext emptyCapabilityContext
      (.app typeIdentity (.ordinaryTypeCode .zero)) (.sort .zero) := by
  exact .app typeIdentity_typed (.ordinaryTypeCode .zero)
    ⟨.ordinaryCode, rfl, CanCoerce.codeRefl⟩

/-- Ordinary code may safely instantiate a parametric type witness. -/
example :
    CoreHasType closedValuation emptyCoreContext emptyCapabilityContext
      (Core.instantiate (.var 0 : Core 1) (.ordinaryTypeCode .zero))
      (Core.instantiate (.sort .zero : Core 1) (.ordinaryTypeCode .zero)) := by
  exact CoreHasType.dependent_substitution
    (capability := .parametricWitness)
    (CoreHasType.var 0)
    (.ordinaryTypeCode .zero)
    (Core.ordinary_code_can_supply_parametric_witness
      emptyCapabilityContext .zero)

def onlyParametricCapability : Core.CapabilityContext 1 :=
  fun _ => .parametricWitness

example :
    ¬ Core.SafeUseAs onlyParametricCapability (.var 0) .ordinaryCode := by
  exact Core.parametric_variable_cannot_be_used_as_code
    onlyParametricCapability 0 rfl

example :
    ¬ Core.SafeUseAs
      (Core.CapabilityContext.extend onlyParametricCapability .ordinaryCode)
      (Core.weaken (.var 0 : Core 1)) .ordinaryCode := by
  exact Core.notSafeUseAs_rename
    (Core.weakeningCompatibility
      (fun _ => .sort .zero : Core.Context 1)
      onlyParametricCapability (.sort .zero) .ordinaryCode)
    (Core.parametric_variable_cannot_be_used_as_code
      onlyParametricCapability 0 rfl)

example (rho : LevelExpr) :
    CoreHasType closedValuation emptyCoreContext emptyCapabilityContext
      (.pi .parametricWitness (.sort rho) (.ordinaryTypeCode .zero))
      (.sort .zero) := by
  exact .piParametric (.ordinaryTypeCode .zero)

/-- The exact specification example: `(0 t : Type0, a : t) : Type0`. -/
example :
    CoreHasType closedValuation emptyCoreContext emptyCapabilityContext
      (CoreHasType.parametricDependentPair .zero) (.sort .zero) := by
  exact CoreHasType.parametric_dependent_pair_typed .zero

example :
    parametricDependentPairLevel .zero = .zero ∧
      ¬ CanCoerce .parametricWitness .ordinaryCode := by
  exact parametric_dependent_pair_smallness_is_safe .zero

example :
    Core.SafeUseAs
      (Core.CapabilityContext.extend emptyCapabilityContext .parametricWitness)
      (.var 0) .parametricWitness := by
  exact CoreHasType.parametric_pair_witness_has_parametric_capability
    emptyCapabilityContext

example :
    ¬ Core.SafeUseAs
      (Core.CapabilityContext.extend emptyCapabilityContext .parametricWitness)
      (.var 0) .ordinaryCode := by
  exact CoreHasType.parametric_pair_witness_not_ordinary_code
    emptyCapabilityContext

example :
    CoreHasType closedValuation emptyCoreContext emptyCapabilityContext
        (CoreHasType.parametricDependentPair .zero) (.sort .zero) ∧
      (CoreHasType closedValuation emptyCoreContext emptyCapabilityContext
        (.sort .zero) (.sort .zero) → False) := by
  exact CoreHasType.parametric_dependent_pair_does_not_collapse_universes .zero

example {package : Core 0}
    (packageType : CoreHasType closedValuation emptyCoreContext emptyCapabilityContext
      package (CoreHasType.parametricDependentPair .zero)) :
    CoreHasType closedValuation emptyCoreContext emptyCapabilityContext
        (.first .parametricWitness package) (.sort .zero) ∧
      ¬ Core.SafeUseAs emptyCapabilityContext
        (.first .parametricWitness package) .ordinaryCode := by
  exact CoreHasType.parametric_sigma_first_projection_safe packageType

example {package : Core 0}
    (packageType : CoreHasType closedValuation emptyCoreContext emptyCapabilityContext
      package (CoreHasType.parametricDependentPair .zero)) :
    CoreHasType closedValuation emptyCoreContext emptyCapabilityContext
      (.second .parametricWitness package)
      (.first .parametricWitness package) := by
  exact CoreHasType.parametric_sigma_second_projection_typed packageType

end Kappa.Universes.Examples
