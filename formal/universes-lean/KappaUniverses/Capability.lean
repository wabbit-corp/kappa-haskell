/-!
# Parametric type-witness capability

`docs/Spec.md` §11.1.2.3A makes the no-bump rule safe by distinguishing an
ordinary, inspectable type-code value from an erased parametric type witness.
This file records the direction of the permitted capability coercion and proves
that it contains no witness-to-code promotion.
-/

namespace Kappa.Universes

inductive TypeCapability where
  | ordinaryCode
  | parametricWitness
deriving DecidableEq, Repr

/-- `CanCoerce source target` is the complete safe capability-coercion relation. -/
inductive CanCoerce : TypeCapability → TypeCapability → Prop where
  | codeRefl : CanCoerce .ordinaryCode .ordinaryCode
  | witnessRefl : CanCoerce .parametricWitness .parametricWitness
  | codeToWitness : CanCoerce .ordinaryCode .parametricWitness

theorem CanCoerce.refl (capability : TypeCapability) :
    CanCoerce capability capability := by
  cases capability
  · exact .codeRefl
  · exact .witnessRefl

theorem CanCoerce.trans
    {source middle target : TypeCapability} :
    CanCoerce source middle → CanCoerce middle target →
      CanCoerce source target
  | .codeRefl, coercion => coercion
  | .witnessRefl, coercion => coercion
  | .codeToWitness, .witnessRefl => .codeToWitness

/-- The forbidden direction from §11.1.2.3A is uninhabited. -/
theorem no_parametric_witness_to_ordinary_code :
    ¬ CanCoerce .parametricWitness .ordinaryCode := by
  intro h
  cases h

/-- A parametric witness is still legal in type position. -/
inductive UsePosition where
  | typePosition
  | inspectAsCode
deriving DecidableEq, Repr

def CanUseAt : TypeCapability → UsePosition → Prop
  | .ordinaryCode, _ => True
  | .parametricWitness, .typePosition => True
  | .parametricWitness, .inspectAsCode => False

theorem parametric_witness_usable_as_type :
    CanUseAt .parametricWitness .typePosition := by
  trivial

theorem parametric_witness_not_inspectable :
    ¬ CanUseAt .parametricWitness .inspectAsCode := by
  intro h
  exact h

end Kappa.Universes
