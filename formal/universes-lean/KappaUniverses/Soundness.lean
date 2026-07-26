import KappaUniverses.Level

/-!
# Initial universe-stratification soundness results

These results cover the semantic kernel of `docs/Spec.md` §§11.1.2–11.1.2.2.
They do not yet constitute normalization or consistency proofs for the whole
Kappa term language; see `PROOF_PLAN.md` for that larger claim.
-/

namespace Kappa.Universes

open LevelExpr

/-- A canonical level inequality. -/
structure Constraint where
  lower : LevelExpr
  upper : LevelExpr
deriving DecidableEq, Repr

namespace Constraint

def Holds (valuation : Valuation) (constraint : Constraint) : Prop :=
  constraint.lower.eval valuation ≤ constraint.upper.eval valuation

def selfContainment (u : LevelExpr) : Constraint :=
  ⟨.succ u, u⟩

theorem self_containment_never_holds (valuation : Valuation) (u : LevelExpr) :
    ¬ (selfContainment u).Holds valuation := by
  exact LevelExpr.succ_not_le_self valuation u

end Constraint

abbrev Assumptions := List Constraint

namespace Assumptions

def SatisfiedBy (valuation : Valuation) (assumptions : Assumptions) : Prop :=
  ∀ constraint, constraint ∈ assumptions → constraint.Holds valuation

def Satisfiable (assumptions : Assumptions) : Prop :=
  ∃ valuation, SatisfiedBy valuation assumptions

/-- Semantic entailment is deliberately defined only through genuine models. -/
def Entails (assumptions : Assumptions) (goal : Constraint) : Prop :=
  ∀ valuation, SatisfiedBy valuation assumptions → goal.Holds valuation

/--
A satisfiable local proof-bound context cannot justify `succ u ≤ u`.

This is the semantic form of the §11.1.2.2 requirement that inconsistent erased
proof binders must never be used to manufacture universe self-containment.
-/
theorem satisfiable_not_entails_self_containment
    (assumptions : Assumptions)
    (u : LevelExpr)
    (hSatisfiable : Satisfiable assumptions) :
    ¬ Entails assumptions (.selfContainment u) := by
  intro hEntails
  rcases hSatisfiable with ⟨valuation, hModel⟩
  have hBad := hEntails valuation hModel
  exact Constraint.self_containment_never_holds valuation u hBad

theorem entails_self_containment_is_inconsistent
    (assumptions : Assumptions)
    (u : LevelExpr)
    (hEntails : Entails assumptions (.selfContainment u)) :
    ¬ Satisfiable assumptions := by
  intro hSatisfiable
  exact satisfiable_not_entails_self_containment assumptions u hSatisfiable hEntails

end Assumptions

/--
`SortHasType valuation u v` models the cumulative judgment `Type u : Type v`.
Predicativity first assigns `Type u` the classifier `Type (succ u)`; cumulativity
may then raise that classifier, but never lower it.
-/
def SortHasType (valuation : Valuation) (u v : LevelExpr) : Prop :=
  LevelExpr.eval valuation (LevelExpr.succ u) ≤ LevelExpr.eval valuation v

theorem type_has_successor_type (valuation : Valuation) (u : LevelExpr) :
    SortHasType valuation u (.succ u) := by
  simpa [SortHasType] using LevelValue.le_refl (LevelExpr.eval valuation (.succ u))

/-- Cumulativity cannot turn the predicative sort rule into `Type u : Type u`. -/
theorem no_type_in_type (valuation : Valuation) (u : LevelExpr) :
    ¬ SortHasType valuation u u := by
  simpa [SortHasType] using LevelExpr.succ_not_le_self valuation u

/--
The universe rule needed by the usual Girard construction is absent at every
Kappa level, including `ω`, `ω + 1`, and open levels under any valuation.
-/
theorem girard_type_in_type_premise_is_impossible
    (valuation : Valuation)
    (u : LevelExpr) :
    SortHasType valuation u u → False := by
  exact no_type_in_type valuation u

end Kappa.Universes
