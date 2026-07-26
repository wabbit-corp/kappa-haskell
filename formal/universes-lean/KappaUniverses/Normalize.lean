import KappaUniverses.Meta

/-!
# Denotation-preserving normalization

The normalizer performs only identities valid for open ordinal expressions:
`0 + u`, `u + 0`, `max u u`, and `max 0 u`.  It deliberately does not treat
ordinal addition as commutative and does not use source-level names.
-/

namespace Kappa.Universes.LevelExpr

def smartAdd (u v : LevelExpr) : LevelExpr :=
  if u = .zero then v
  else if v = .zero then u
  else .add u v

def smartMax (u v : LevelExpr) : LevelExpr :=
  if u = v then u
  else if u = .zero then v
  else .max u v

def normalize : LevelExpr → LevelExpr
  | .zero => .zero
  | .omega => .omega
  | .var id => .var id
  | .succ u => .succ (normalize u)
  | .add u v => smartAdd (normalize u) (normalize v)
  | .max u v => smartMax (normalize u) (normalize v)

theorem eval_smartAdd (valuation : Valuation) (u v : LevelExpr) :
    eval valuation (smartAdd u v) =
      LevelValue.add (eval valuation u) (eval valuation v) := by
  unfold smartAdd
  split <;> rename_i hu
  · subst u
    simp [eval, LevelValue.zero_add]
  · split <;> rename_i hv
    · subst v
      simp [eval, LevelValue.add_zero]
    · rfl

theorem eval_smartMax (valuation : Valuation) (u v : LevelExpr) :
    eval valuation (smartMax u v) =
      LevelValue.max (eval valuation u) (eval valuation v) := by
  unfold smartMax
  split <;> rename_i huv
  · subst v
    simp [LevelValue.max_self]
  · split <;> rename_i hu
    · subst u
      simp [eval, LevelValue.max_zero_left]
    · rfl

/-- Normalization preserves the ordinal denotation of every open expression. -/
theorem normalize_sound (valuation : Valuation) (u : LevelExpr) :
    eval valuation (normalize u) = eval valuation u := by
  induction u with
  | zero => rfl
  | omega => rfl
  | var _ => rfl
  | succ u ih => simp [normalize, eval, ih]
  | add u v ihu ihv =>
      rw [normalize, eval_smartAdd, ihu, ihv]
      rfl
  | max u v ihu ihv =>
      rw [normalize, eval_smartMax, ihu, ihv]
      rfl

/-- Re-running the rigid normalizer makes no further change. -/
theorem normalize_idempotent (u : LevelExpr) :
    normalize (normalize u) = normalize u := by
  induction u with
  | zero => rfl
  | omega => rfl
  | var _ => rfl
  | succ u ih => simp [normalize, ih]
  | add u v ihu ihv =>
      rw [normalize]
      by_cases hu : normalize u = .zero
      · simp [smartAdd, hu, ihv]
      · by_cases hv : normalize v = .zero
        · simp [smartAdd, hu, hv, ihu]
        · simp [smartAdd, normalize, hu, hv, ihu, ihv]
  | max u v ihu ihv =>
      rw [normalize]
      by_cases huv : normalize u = normalize v
      · simp [smartMax, huv, ihv]
      · by_cases hu : normalize u = .zero
        · have hZeroV : ¬ (.zero : LevelExpr) = normalize v := by
            intro h
            exact huv (hu.trans h)
          simp [smartMax, hu, hZeroV, ihv]
        · simp [smartMax, normalize, huv, hu, ihu, ihv]

end Kappa.Universes.LevelExpr

namespace Kappa.Universes.LevelTerm

def smartAdd (u v : LevelTerm) : LevelTerm :=
  if u = .zero then v
  else if v = .zero then u
  else .add u v

def smartMax (u v : LevelTerm) : LevelTerm :=
  if u = v then u
  else if u = .zero then v
  else .max u v

def normalize : LevelTerm → LevelTerm
  | .zero => .zero
  | .omega => .omega
  | .var id => .var id
  | .mvar id => .mvar id
  | .succ u => .succ (normalize u)
  | .add u v => smartAdd (normalize u) (normalize v)
  | .max u v => smartMax (normalize u) (normalize v)

theorem eval_smartAdd
    (rigid : LevelExpr.Valuation)
    (metas : MetaValuation)
    (u v : LevelTerm) :
    eval rigid metas (smartAdd u v) =
      LevelValue.add (eval rigid metas u) (eval rigid metas v) := by
  unfold smartAdd
  split <;> rename_i hu
  · subst u
    simp [eval, LevelValue.zero_add]
  · split <;> rename_i hv
    · subst v
      simp [eval, LevelValue.add_zero]
    · rfl

theorem eval_smartMax
    (rigid : LevelExpr.Valuation)
    (metas : MetaValuation)
    (u v : LevelTerm) :
    eval rigid metas (smartMax u v) =
      LevelValue.max (eval rigid metas u) (eval rigid metas v) := by
  unfold smartMax
  split <;> rename_i huv
  · subst v
    simp [LevelValue.max_self]
  · split <;> rename_i hu
    · subst u
      simp [eval, LevelValue.max_zero_left]
    · rfl

/-- Normalization remains sound in the presence of unresolved metavariables. -/
theorem normalize_sound
    (rigid : LevelExpr.Valuation)
    (metas : MetaValuation)
    (u : LevelTerm) :
    eval rigid metas (normalize u) = eval rigid metas u := by
  induction u with
  | zero => rfl
  | omega => rfl
  | var _ => rfl
  | mvar _ => rfl
  | succ u ih => simp [normalize, eval, ih]
  | add u v ihu ihv =>
      rw [normalize, eval_smartAdd, ihu, ihv]
      rfl
  | max u v ihu ihv =>
      rw [normalize, eval_smartMax, ihu, ihv]
      rfl

/-- Re-running the metavariable-aware normalizer makes no further change. -/
theorem normalize_idempotent (u : LevelTerm) :
    normalize (normalize u) = normalize u := by
  induction u with
  | zero => rfl
  | omega => rfl
  | var _ => rfl
  | mvar _ => rfl
  | succ u ih => simp [normalize, ih]
  | add u v ihu ihv =>
      rw [normalize]
      by_cases hu : normalize u = .zero
      · simp [smartAdd, hu, ihv]
      · by_cases hv : normalize v = .zero
        · simp [smartAdd, hu, hv, ihu]
        · simp [smartAdd, normalize, hu, hv, ihu, ihv]
  | max u v ihu ihv =>
      rw [normalize]
      by_cases huv : normalize u = normalize v
      · simp [smartMax, huv, ihv]
      · by_cases hu : normalize u = .zero
        · have hZeroV : ¬ (.zero : LevelTerm) = normalize v := by
            intro h
            exact huv (hu.trans h)
          simp [smartMax, hu, hZeroV, ihv]
        · simp [smartMax, normalize, huv, hu, ihu, ihv]

end Kappa.Universes.LevelTerm
