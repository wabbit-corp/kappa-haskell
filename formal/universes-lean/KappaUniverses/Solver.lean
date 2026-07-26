import KappaUniverses.Normalize
import KappaUniverses.Soundness

/-!
# Sound constraint certificates and structural search

`Derivation` is a proof-certificate language checked by Lean.  The executable
search routine can return only such certificates. Unsupported cases return
`none`; completeness for the full open fragment remains a separate obligation.
-/

namespace Kappa.Universes

open LevelExpr

namespace Constraint

/--
Decide a constraint when both sides are closed. `none` means the expression is
open, not that the inequality is false.
-/
def checkClosed (constraint : Constraint) : Option Bool := do
  let lower ← constraint.lower.evalClosed
  let upper ← constraint.upper.evalClosed
  return decide (lower ≤ upper)

theorem checkClosed_true_sound
    (constraint : Constraint)
    (hChecked : constraint.checkClosed = some true) :
    Assumptions.Entails [] constraint := by
  unfold checkClosed at hChecked
  cases hLower : constraint.lower.evalClosed with
  | none => simp [hLower] at hChecked
  | some lower =>
      cases hUpper : constraint.upper.evalClosed with
      | none => simp [hLower, hUpper] at hChecked
      | some upper =>
          simp [hLower, hUpper] at hChecked
          intro valuation _
          unfold Holds
          rw [LevelExpr.evalClosed_sound valuation constraint.lower lower hLower]
          rw [LevelExpr.evalClosed_sound valuation constraint.upper upper hUpper]
          exact hChecked

theorem checkClosed_false_invalid
    (constraint : Constraint)
    (hChecked : constraint.checkClosed = some false)
    (valuation : Valuation) :
    ¬ constraint.Holds valuation := by
  unfold checkClosed at hChecked
  cases hLower : constraint.lower.evalClosed with
  | none => simp [hLower] at hChecked
  | some lower =>
      cases hUpper : constraint.upper.evalClosed with
      | none => simp [hLower, hUpper] at hChecked
      | some upper =>
          simp [hLower, hUpper] at hChecked
          unfold Holds
          rw [LevelExpr.evalClosed_sound valuation constraint.lower lower hLower]
          rw [LevelExpr.evalClosed_sound valuation constraint.upper upper hUpper]
          exact hChecked

/-- Closed self-containment is rejected by computation. -/
theorem checkClosed_self_containment_false
    (u : LevelExpr)
    (uValue : LevelValue)
    (hClosed : u.evalClosed = some uValue) :
    (selfContainment u).checkClosed = some false := by
  simp [checkClosed, selfContainment, LevelExpr.evalClosed, hClosed,
    LevelValue.succ_not_le]

end Constraint

inductive Derivation (assumptions : Assumptions) : Constraint → Type where
  | assumption (constraint : Constraint) (member : constraint ∈ assumptions) :
      Derivation assumptions constraint
  | refl (u : LevelExpr) :
      Derivation assumptions ⟨u, u⟩
  | zeroLower (u : LevelExpr) :
      Derivation assumptions ⟨.zero, u⟩
  | trans (u v w : LevelExpr)
      (left : Derivation assumptions ⟨u, v⟩)
      (right : Derivation assumptions ⟨v, w⟩) :
      Derivation assumptions ⟨u, w⟩
  | succMono (u v : LevelExpr)
      (premise : Derivation assumptions ⟨u, v⟩) :
      Derivation assumptions ⟨.succ u, .succ v⟩
  | maxLeft (u v : LevelExpr) :
      Derivation assumptions ⟨u, .max u v⟩
  | maxRight (u v : LevelExpr) :
      Derivation assumptions ⟨v, .max u v⟩
  | maxUpper (u v w : LevelExpr)
      (left : Derivation assumptions ⟨u, w⟩)
      (right : Derivation assumptions ⟨v, w⟩) :
      Derivation assumptions ⟨.max u v, w⟩
  | normalized (u v : LevelExpr)
      (premise : Derivation assumptions ⟨u.normalize, v.normalize⟩) :
      Derivation assumptions ⟨u, v⟩
  | closed (constraint : Constraint)
      (checked : constraint.checkClosed = some true) :
      Derivation assumptions constraint

namespace Derivation

/-- Every checked solver certificate is valid in every model of its assumptions. -/
theorem sound
    {assumptions : Assumptions}
    {goal : Constraint}
    (derivation : Derivation assumptions goal) :
    assumptions.Entails goal := by
  intro valuation hModel
  induction derivation with
  | assumption constraint member => exact hModel constraint member
  | refl u => exact LevelValue.le_refl (u.eval valuation)
  | zeroLower u => exact LevelValue.zero_le (u.eval valuation)
  | trans u v w _ _ ihLeft ihRight =>
      exact LevelValue.le_trans ihLeft ihRight
  | succMono u v _ ih =>
      exact LevelValue.succ_mono ih
  | maxLeft u v =>
      exact LevelValue.le_max_left (u.eval valuation) (v.eval valuation)
  | maxRight u v =>
      exact LevelValue.le_max_right (u.eval valuation) (v.eval valuation)
  | maxUpper u v w _ _ ihLeft ihRight =>
      exact LevelValue.max_le ihLeft ihRight
  | normalized u v _ ih =>
      simpa only [Constraint.Holds, LevelExpr.normalize_sound valuation u,
        LevelExpr.normalize_sound valuation v] using ih
  | closed constraint checked =>
      exact Constraint.checkClosed_true_sound constraint checked valuation (by
        intro impossible hMember
        simp at hMember)

/-- No checked certificate can prove self-containment from satisfiable assumptions. -/
theorem no_self_containment_certificate
    {assumptions : Assumptions}
    (hSatisfiable : assumptions.Satisfiable)
    (u : LevelExpr) :
    Derivation assumptions (.selfContainment u) → False := by
  intro derivation
  exact Assumptions.satisfiable_not_entails_self_containment
    assumptions u hSatisfiable derivation.sound

/--
Fuelled structural search. Every success contains a `Derivation`; unsupported
or not-yet-complete cases return `none` instead of guessing.
-/
def search :
    (fuel : Nat) →
    (assumptions : Assumptions) →
    (lower upper : LevelExpr) →
    Option (Derivation assumptions ⟨lower, upper⟩)
  | 0, _, _, _ => none
  | Nat.succ fuel, assumptions, lower, upper =>
      if hMember : (⟨lower, upper⟩ : Constraint) ∈ assumptions then
        some (.assumption ⟨lower, upper⟩ hMember)
      else if hEq : lower = upper then
        match hEq with
        | rfl => some (.refl lower)
      else if hClosed : (⟨lower, upper⟩ : Constraint).checkClosed = some true then
        some (.closed ⟨lower, upper⟩ hClosed)
      else
        match lower, upper with
        | .zero, upper => some (.zeroLower upper)
        | .succ lower, .succ upper =>
            match search fuel assumptions lower upper with
            | some premise => some (.succMono lower upper premise)
            | none => none
        | .max left right, upper =>
            match search fuel assumptions left upper,
              search fuel assumptions right upper with
            | some leftProof, some rightProof =>
                some (.maxUpper left right upper leftProof rightProof)
            | _, _ => none
        | lower, .max left right =>
            match search fuel assumptions lower left with
            | some leftProof =>
                some (.trans lower left (.max left right) leftProof (.maxLeft left right))
            | none =>
                match search fuel assumptions lower right with
                | some rightProof =>
                    some (.trans lower right (.max left right) rightProof (.maxRight left right))
                | none => none
        | lower, upper =>
            match search fuel assumptions lower.normalize upper.normalize with
            | some premise => some (.normalized lower upper premise)
            | none => none

/-- Executable search can return only semantically valid entailments. -/
theorem search_sound
    {fuel : Nat}
    {assumptions : Assumptions}
    {lower upper : LevelExpr}
    {derivation : Derivation assumptions ⟨lower, upper⟩}
    (_hSearch : search fuel assumptions lower upper = some derivation) :
    assumptions.Entails ⟨lower, upper⟩ := by
  exact derivation.sound

/-- The result of running search is sound without any external certificate input. -/
theorem search_result_sound
    (fuel : Nat)
    (assumptions : Assumptions)
    (lower upper : LevelExpr) :
    match search fuel assumptions lower upper with
    | none => True
    | some _ => assumptions.Entails ⟨lower, upper⟩ := by
  cases hResult : search fuel assumptions lower upper with
  | none => trivial
  | some derivation => exact derivation.sound

/-- Search cannot return a self-containment certificate from a satisfiable context. -/
theorem search_self_containment_none
    (fuel : Nat)
    (assumptions : Assumptions)
    (hSatisfiable : assumptions.Satisfiable)
    (u : LevelExpr) :
    search fuel assumptions (.succ u) u = none := by
  cases hResult : search fuel assumptions (.succ u) u with
  | none => rfl
  | some derivation =>
      exact False.elim (no_self_containment_certificate hSatisfiable u derivation)

end Derivation

end Kappa.Universes
