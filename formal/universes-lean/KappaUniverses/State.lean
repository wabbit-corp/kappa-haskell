import KappaUniverses.Meta

/-!
# Ordered metavariable solver states

An accepted extension may not reuse a solved metavariable or assign a
metavariable mentioned by an earlier right-hand side.  This triangular ordering
lets a new valuation update preserve every equation already in the state.
-/

namespace Kappa.Universes

abbrev SolverState := List MetaEquation

namespace SolverState

def Holds
    (rigid : LevelExpr.Valuation)
    (metas : LevelTerm.MetaValuation)
    (state : SolverState) : Prop :=
  ∀ equation, equation ∈ state → equation.Holds rigid metas

def Satisfiable (rigid : LevelExpr.Valuation) (state : SolverState) : Prop :=
  ∃ metas, Holds rigid metas state

/-- `metaId` is absent from every earlier equation and its dependencies. -/
def FreshFor (metaId : Nat) : SolverState → Prop
  | [] => True
  | equation :: rest =>
      metaId ≠ equation.metaId ∧
      ¬ LevelTerm.Occurs metaId equation.rhs ∧
      FreshFor metaId rest

instance freshForDecidable (metaId : Nat) :
    (state : SolverState) → Decidable (FreshFor metaId state)
  | [] => isTrue True.intro
  | equation :: rest =>
      letI : Decidable (FreshFor metaId rest) := freshForDecidable metaId rest
      inferInstanceAs (Decidable
        (metaId ≠ equation.metaId ∧
          ¬ LevelTerm.Occurs metaId equation.rhs ∧
          FreshFor metaId rest))

theorem freshFor_member
    {metaId : Nat}
    {state : SolverState}
    {equation : MetaEquation}
    (hFresh : FreshFor metaId state)
    (hMember : equation ∈ state) :
    metaId ≠ equation.metaId ∧ ¬ LevelTerm.Occurs metaId equation.rhs := by
  induction state with
  | nil => simp at hMember
  | cons head rest ih =>
      simp only [FreshFor] at hFresh
      simp only [List.mem_cons] at hMember
      rcases hMember with rfl | hMember
      · exact ⟨hFresh.1, hFresh.2.1⟩
      · exact ih hFresh.2.2 hMember

theorem equation_holds_after_fresh_update
    (rigid : LevelExpr.Valuation)
    (metas : LevelTerm.MetaValuation)
    (equation : MetaEquation)
    (metaId : Nat)
    (value : LevelValue)
    (hHolds : equation.Holds rigid metas)
    (hDifferent : metaId ≠ equation.metaId)
    (hAbsent : ¬ LevelTerm.Occurs metaId equation.rhs) :
    equation.Holds rigid (LevelTerm.updateMeta metas metaId value) := by
  unfold MetaEquation.Holds at hHolds ⊢
  rw [LevelTerm.eval_update_of_not_occurs rigid metas metaId value equation.rhs hAbsent]
  simpa [LevelTerm.updateMeta, hDifferent] using hHolds

/--
Atomically add one equation and its valuation update.  Failure means either an
occurs-check violation or a violation of the state's triangular ordering.
-/
def tryExtend
    (rigid : LevelExpr.Valuation)
    (metas : LevelTerm.MetaValuation)
    (state : SolverState)
    (equation : MetaEquation) :
    Option (SolverState × LevelTerm.MetaValuation) :=
  if equation.WellFormed ∧ FreshFor equation.metaId state then
    some (equation :: state, equation.extend rigid metas)
  else
    none

/-- Every state returned by `tryExtend` satisfies the new and all prior equations. -/
theorem tryExtend_sound
    (rigid : LevelExpr.Valuation)
    (metas assigned : LevelTerm.MetaValuation)
    (state newState : SolverState)
    (equation : MetaEquation)
    (hState : Holds rigid metas state)
    (hResult : tryExtend rigid metas state equation = some (newState, assigned)) :
    Holds rigid assigned newState := by
  unfold tryExtend at hResult
  split at hResult
  next hChecks =>
    simp only [Option.some.injEq, Prod.mk.injEq] at hResult
    rcases hResult with ⟨rfl, rfl⟩
    intro candidate hMember
    simp only [List.mem_cons] at hMember
    rcases hMember with rfl | hPrior
    · exact MetaEquation.extend_holds rigid metas candidate hChecks.1
    · have hFresh := freshFor_member hChecks.2 hPrior
      exact equation_holds_after_fresh_update
        rigid metas candidate equation.metaId
        (equation.rhs.eval rigid metas)
        (hState candidate hPrior) hFresh.1 hFresh.2
  next _ => simp at hResult

/-- A successful ordered extension preserves existence of a state model. -/
theorem successful_extension_satisfiable
    (rigid : LevelExpr.Valuation)
    (metas assigned : LevelTerm.MetaValuation)
    (state newState : SolverState)
    (equation : MetaEquation)
    (hState : Holds rigid metas state)
    (hResult : tryExtend rigid metas state equation = some (newState, assigned)) :
    Satisfiable rigid newState := by
  exact ⟨assigned, tryExtend_sound rigid metas assigned state newState equation hState hResult⟩

end SolverState

end Kappa.Universes
