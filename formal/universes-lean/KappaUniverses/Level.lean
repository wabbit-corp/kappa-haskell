/-!
# Kappa universe levels

This file models the canonical, rigid fragment from `docs/Spec.md` §11.1.1:

* zero and omega;
* successor, ordinal addition, and maximum;
* rigid level variables.

Every closed expression in that grammar denotes an ordinal below `ω²`, uniquely
written `ω * omegaCoeff + finiteTail`.  Metavariables intentionally do not occur
in this semantic syntax: a sound solver must instantiate them with a rigid
expression before it claims that a constraint is solved.
-/

namespace Kappa.Universes

/-- An ordinal below `ω²`, represented in Cantor normal form as `ω * ωCoeff + finiteTail`. -/
structure LevelValue where
  omegaCoeff : Nat
  finiteTail : Nat
deriving DecidableEq, Repr

namespace LevelValue

def zero : LevelValue := ⟨0, 0⟩

def omega : LevelValue := ⟨1, 0⟩

/-- Ordinal successor. -/
def succ (u : LevelValue) : LevelValue :=
  ⟨u.omegaCoeff, Nat.succ u.finiteTail⟩

/--
Ordinal addition below `ω²`.

If the right operand has an omega component, its leading limit discards the
left operand's finite tail.  This is why `1 + ω = ω` but `ω + 1 > ω`.
-/
def add (u v : LevelValue) : LevelValue :=
  if v.omegaCoeff = 0 then
    ⟨u.omegaCoeff, u.finiteTail + v.finiteTail⟩
  else
    ⟨u.omegaCoeff + v.omegaCoeff, v.finiteTail⟩

/-- Ordinal ordering, lexicographic in Cantor normal form. -/
def le (u v : LevelValue) : Prop :=
  u.omegaCoeff < v.omegaCoeff ∨
    (u.omegaCoeff = v.omegaCoeff ∧ u.finiteTail ≤ v.finiteTail)

instance : LE LevelValue where
  le := le

instance (u v : LevelValue) : Decidable (u ≤ v) :=
  by
    change Decidable
      (u.omegaCoeff < v.omegaCoeff ∨
        (u.omegaCoeff = v.omegaCoeff ∧ u.finiteTail ≤ v.finiteTail))
    infer_instance

def max (u v : LevelValue) : LevelValue :=
  if u ≤ v then v else u

theorem le_refl (u : LevelValue) : u ≤ u := by
  exact Or.inr ⟨rfl, Nat.le_refl _⟩

theorem le_trans {u v w : LevelValue} (huv : u ≤ v) (hvw : v ≤ w) : u ≤ w := by
  rcases huv with huv | ⟨huvCoeff, huvTail⟩
  · rcases hvw with hvw | ⟨hvwCoeff, _⟩
    · exact Or.inl (Nat.lt_trans huv hvw)
    · exact Or.inl (lt_of_lt_of_eq huv hvwCoeff)
  · rcases hvw with hvw | ⟨hvwCoeff, hvwTail⟩
    · exact Or.inl (lt_of_eq_of_lt huvCoeff hvw)
    · exact Or.inr ⟨huvCoeff.trans hvwCoeff, Nat.le_trans huvTail hvwTail⟩

theorem le_total (u v : LevelValue) : u ≤ v ∨ v ≤ u := by
  rcases Nat.lt_trichotomy u.omegaCoeff v.omegaCoeff with huv | huv | huv
  · exact Or.inl (Or.inl huv)
  · rcases Nat.le_total u.finiteTail v.finiteTail with hTail | hTail
    · exact Or.inl (Or.inr ⟨huv, hTail⟩)
    · exact Or.inr (Or.inr ⟨huv.symm, hTail⟩)
  · exact Or.inr (Or.inl huv)

theorem succ_mono {u v : LevelValue} (h : u ≤ v) : succ u ≤ succ v := by
  rcases h with hCoeff | ⟨hCoeff, hTail⟩
  · exact Or.inl hCoeff
  · exact Or.inr ⟨hCoeff, Nat.succ_le_succ hTail⟩

theorem zero_le (u : LevelValue) : zero ≤ u := by
  change 0 < u.omegaCoeff ∨ (0 = u.omegaCoeff ∧ 0 ≤ u.finiteTail)
  cases u.omegaCoeff with
  | zero => exact Or.inr ⟨rfl, Nat.zero_le _⟩
  | succ coeff => exact Or.inl (Nat.zero_lt_succ coeff)

theorem zero_add (u : LevelValue) : add zero u = u := by
  unfold add
  split <;> rename_i hCoeff
  · cases u
    simp_all [zero]
  · cases u
    simp_all [zero]

theorem add_zero (u : LevelValue) : add u zero = u := by
  cases u
  simp [add, zero]

theorem max_self (u : LevelValue) : max u u = u := by
  simp [max, le_refl]

theorem max_zero_left (u : LevelValue) : max zero u = u := by
  simp [max, zero_le]

theorem le_max_left (u v : LevelValue) : u ≤ max u v := by
  unfold max
  split <;> rename_i h
  · exact h
  · exact le_refl u

theorem le_max_right (u v : LevelValue) : v ≤ max u v := by
  unfold max
  split <;> rename_i h
  · exact le_refl v
  · rcases le_total v u with hvu | huv
    · exact hvu
    · exact False.elim (h huv)

theorem max_le {u v w : LevelValue} (hu : u ≤ w) (hv : v ≤ w) : max u v ≤ w := by
  unfold max
  split
  · exact hv
  · exact hu

theorem succ_not_le (u : LevelValue) : ¬ succ u ≤ u := by
  intro h
  cases h with
  | inl hCoeff =>
      exact (Nat.lt_irrefl u.omegaCoeff) hCoeff
  | inr hSame =>
      have hTail : Nat.succ u.finiteTail ≤ u.finiteTail := hSame.2
      have hImpossible : u.finiteTail < u.finiteTail := Nat.lt_of_succ_le hTail
      exact (Nat.lt_irrefl u.finiteTail) hImpossible

theorem one_add_omega :
    add (succ zero) omega = omega := by
  rfl

theorem omega_add_one_not_le_omega :
    ¬ add omega (succ zero) ≤ omega := by
  intro h
  cases h with
  | inl hCoeff =>
      exact (Nat.lt_irrefl 1) hCoeff
  | inr hSame =>
      have hTail : 1 ≤ 0 := hSame.2
      exact (Nat.not_succ_le_zero 0) hTail

end LevelValue

/-- Canonical rigid level expressions from §11.1.1. -/
inductive LevelExpr where
  | zero
  | omega
  | var (id : Nat)
  | succ (u : LevelExpr)
  | add (u v : LevelExpr)
  | max (u v : LevelExpr)
deriving DecidableEq, Repr

namespace LevelExpr

abbrev Valuation := Nat → LevelValue

def eval (valuation : Valuation) : LevelExpr → LevelValue
  | zero => .zero
  | omega => .omega
  | var id => valuation id
  | succ u => (eval valuation u).succ
  | add u v => (eval valuation u).add (eval valuation v)
  | max u v => (eval valuation u).max (eval valuation v)

/-- Evaluate exactly when an expression contains no rigid variables. -/
def evalClosed : LevelExpr → Option LevelValue
  | .zero => some .zero
  | .omega => some .omega
  | .var _ => none
  | .succ u => do
      return (← evalClosed u).succ
  | .add u v => do
      return (← evalClosed u).add (← evalClosed v)
  | .max u v => do
      return (← evalClosed u).max (← evalClosed v)

/-- Closed evaluation agrees with evaluation under every valuation. -/
theorem evalClosed_sound
    (valuation : Valuation)
    (u : LevelExpr)
    (value : LevelValue)
    (hClosed : evalClosed u = some value) :
    eval valuation u = value := by
  induction u generalizing value with
  | zero => simp [evalClosed] at hClosed; subst value; rfl
  | omega => simp [evalClosed] at hClosed; subst value; rfl
  | var id => simp [evalClosed] at hClosed
  | succ u ih =>
      cases hValue : evalClosed u with
      | none => simp [evalClosed, hValue] at hClosed
      | some uValue =>
          simp [evalClosed, hValue] at hClosed
          subst value
          simp [eval, ih uValue hValue]
  | add u v ihu ihv =>
      cases hu : evalClosed u with
      | none => simp [evalClosed, hu] at hClosed
      | some uValue =>
          cases hv : evalClosed v with
          | none => simp [evalClosed, hu, hv] at hClosed
          | some vValue =>
              simp [evalClosed, hu, hv] at hClosed
              subst value
              simp [eval, ihu uValue hu, ihv vValue hv]
  | max u v ihu ihv =>
      cases hu : evalClosed u with
      | none => simp [evalClosed, hu] at hClosed
      | some uValue =>
          cases hv : evalClosed v with
          | none => simp [evalClosed, hu, hv] at hClosed
          | some vValue =>
              simp [evalClosed, hu, hv] at hClosed
              subst value
              simp [eval, ihu uValue hu, ihv vValue hv]

@[simp] theorem eval_succ (valuation : Valuation) (u : LevelExpr) :
    eval valuation (.succ u) = (eval valuation u).succ := by
  rfl

theorem succ_not_le_self (valuation : Valuation) (u : LevelExpr) :
    ¬ eval valuation (.succ u) ≤ eval valuation u := by
  exact LevelValue.succ_not_le (eval valuation u)

/-- No level expression is a greatest level; its successor is a larger witness. -/
theorem no_expression_is_a_ceiling (valuation : Valuation) (ceiling : LevelExpr) :
    ∃ candidate, ¬ eval valuation candidate ≤ eval valuation ceiling := by
  exact ⟨.succ ceiling, succ_not_le_self valuation ceiling⟩

end LevelExpr

end Kappa.Universes
