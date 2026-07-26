import KappaUniverses.Level

/-!
# Universe metavariables and checked assignments

Metavariables live in a syntax separate from rigid `LevelExpr`s.  This prevents
an unresolved metavariable from being mistaken for a semantic universe level.
Assignments are checked for self-occurrence before they are accepted.
-/

namespace Kappa.Universes

inductive LevelTerm where
  | zero
  | omega
  | var (id : Nat)
  | mvar (id : Nat)
  | succ (u : LevelTerm)
  | add (u v : LevelTerm)
  | max (u v : LevelTerm)
deriving DecidableEq, Repr

namespace LevelTerm

abbrev MetaValuation := Nat → LevelValue

def embed : LevelExpr → LevelTerm
  | .zero => .zero
  | .omega => .omega
  | .var id => .var id
  | .succ u => .succ (embed u)
  | .add u v => .add (embed u) (embed v)
  | .max u v => .max (embed u) (embed v)

def eval (rigid : LevelExpr.Valuation) (metas : MetaValuation) : LevelTerm → LevelValue
  | .zero => .zero
  | .omega => .omega
  | .var id => rigid id
  | .mvar id => metas id
  | .succ u => (eval rigid metas u).succ
  | .add u v => (eval rigid metas u).add (eval rigid metas v)
  | .max u v => (eval rigid metas u).max (eval rigid metas v)

def Occurs (needle : Nat) : LevelTerm → Prop
  | .zero | .omega | .var _ => False
  | .mvar id => needle = id
  | .succ u => Occurs needle u
  | .add u v | .max u v => Occurs needle u ∨ Occurs needle v

instance occursDecidable (needle : Nat) : (term : LevelTerm) → Decidable (Occurs needle term)
  | .zero | .omega | .var _ => isFalse (by simp [Occurs])
  | .mvar id => inferInstanceAs (Decidable (needle = id))
  | .succ u => occursDecidable needle u
  | .add u v | .max u v =>
      match occursDecidable needle u with
      | isTrue hu => isTrue (Or.inl hu)
      | isFalse hu =>
          match occursDecidable needle v with
          | isTrue hv => isTrue (Or.inr hv)
          | isFalse hv => isFalse (by
              intro h
              exact h.elim hu hv)

def updateMeta (metas : MetaValuation) (needle : Nat) (value : LevelValue) : MetaValuation :=
  fun id => if needle = id then value else metas id

def substituteMeta (needle : Nat) (replacement : LevelTerm) : LevelTerm → LevelTerm
  | .zero => .zero
  | .omega => .omega
  | .var id => .var id
  | .mvar id => if needle = id then replacement else .mvar id
  | .succ u => .succ (substituteMeta needle replacement u)
  | .add u v => .add (substituteMeta needle replacement u) (substituteMeta needle replacement v)
  | .max u v => .max (substituteMeta needle replacement u) (substituteMeta needle replacement v)

theorem eval_embed (rigid : LevelExpr.Valuation) (metas : MetaValuation) (u : LevelExpr) :
    eval rigid metas (embed u) = LevelExpr.eval rigid u := by
  induction u <;> simp [embed, eval, LevelExpr.eval, *]

theorem eval_substituteMeta
    (rigid : LevelExpr.Valuation)
    (metas : MetaValuation)
    (needle : Nat)
    (replacement term : LevelTerm) :
    eval rigid metas (substituteMeta needle replacement term) =
      eval rigid (updateMeta metas needle (eval rigid metas replacement)) term := by
  induction term with
  | zero => rfl
  | omega => rfl
  | var _ => rfl
  | mvar id =>
      by_cases h : needle = id <;> simp [substituteMeta, eval, updateMeta, h]
  | succ u ih => simp [substituteMeta, eval, ih]
  | add u v ihu ihv => simp [substituteMeta, eval, ihu, ihv]
  | max u v ihu ihv => simp [substituteMeta, eval, ihu, ihv]

theorem eval_update_of_not_occurs
    (rigid : LevelExpr.Valuation)
    (metas : MetaValuation)
    (needle : Nat)
    (value : LevelValue)
    (term : LevelTerm)
    (hFresh : ¬ Occurs needle term) :
    eval rigid (updateMeta metas needle value) term = eval rigid metas term := by
  induction term with
  | zero => rfl
  | omega => rfl
  | var _ => rfl
  | mvar id =>
      simp [Occurs] at hFresh
      simp [eval, updateMeta, hFresh]
  | succ u ih =>
      exact congrArg LevelValue.succ (ih hFresh)
  | add u v ihu ihv =>
      have hu : ¬ Occurs needle u := fun h => hFresh (Or.inl h)
      have hv : ¬ Occurs needle v := fun h => hFresh (Or.inr h)
      simp [eval, ihu hu, ihv hv]
  | max u v ihu ihv =>
      have hu : ¬ Occurs needle u := fun h => hFresh (Or.inl h)
      have hv : ¬ Occurs needle v := fun h => hFresh (Or.inr h)
      simp [eval, ihu hu, ihv hv]

end LevelTerm

structure MetaEquation where
  metaId : Nat
  rhs : LevelTerm
deriving DecidableEq, Repr

namespace MetaEquation

def WellFormed (equation : MetaEquation) : Prop :=
  ¬ LevelTerm.Occurs equation.metaId equation.rhs

instance (equation : MetaEquation) : Decidable equation.WellFormed :=
  inferInstanceAs (Decidable (¬ LevelTerm.Occurs equation.metaId equation.rhs))

def Holds
    (rigid : LevelExpr.Valuation)
    (metas : LevelTerm.MetaValuation)
    (equation : MetaEquation) : Prop :=
  metas equation.metaId = equation.rhs.eval rigid metas

def extend
    (rigid : LevelExpr.Valuation)
    (metas : LevelTerm.MetaValuation)
    (equation : MetaEquation) : LevelTerm.MetaValuation :=
  LevelTerm.updateMeta metas equation.metaId (equation.rhs.eval rigid metas)

/-- A successful occurs-checked assignment has a semantic model. -/
theorem extend_holds
    (rigid : LevelExpr.Valuation)
    (metas : LevelTerm.MetaValuation)
    (equation : MetaEquation)
    (hWellFormed : equation.WellFormed) :
    equation.Holds rigid (equation.extend rigid metas) := by
  unfold Holds extend
  rw [LevelTerm.eval_update_of_not_occurs rigid metas equation.metaId
    (LevelTerm.eval rigid metas equation.rhs) equation.rhs hWellFormed]
  simp [LevelTerm.updateMeta]

def tryAssign
    (rigid : LevelExpr.Valuation)
    (metas : LevelTerm.MetaValuation)
    (equation : MetaEquation) : Option LevelTerm.MetaValuation :=
  if equation.WellFormed then some (equation.extend rigid metas) else none

/-- The executable assignment API never returns a valuation that violates its equation. -/
theorem tryAssign_sound
    (rigid : LevelExpr.Valuation)
    (metas assigned : LevelTerm.MetaValuation)
    (equation : MetaEquation)
    (hAssigned : equation.tryAssign rigid metas = some assigned) :
    equation.Holds rigid assigned := by
  unfold tryAssign at hAssigned
  split at hAssigned
  next hWellFormed =>
    simp only [Option.some.injEq] at hAssigned
    subst assigned
    exact extend_holds rigid metas equation hWellFormed
  next _ => simp at hAssigned

end MetaEquation

end Kappa.Universes
