import KappaUniverses.Formation

/-!
# A small intrinsically scoped KCore universe calculus

`Core n` contains exactly the terms whose free de Bruijn variables fit in a
context of size `n`.  The fragment contains predicative sorts, dependent Pi
types, lambdas, application, ordinary type-code values, and abstract parametric
witnesses.  Renaming and substitution preserve scope by their types.
-/

namespace Kappa.Universes

inductive Core : Nat → Type where
  | sort {n : Nat} (level : LevelExpr) : Core n
  | var {n : Nat} (index : Fin n) : Core n
  | pi {n : Nat}
      (capability : TypeCapability)
      (domain : Core n)
      (codomain : Core (n + 1)) : Core n
  | sigma {n : Nat}
      (capability : TypeCapability)
      (first : Core n)
      (second : Core (n + 1)) : Core n
  | lam {n : Nat}
      (capability : TypeCapability)
      (domain : Core n)
      (body : Core (n + 1)) : Core n
  | app {n : Nat} (function argument : Core n) : Core n
  | pair {n : Nat} (first second : Core n) : Core n
  | first {n : Nat} (capability : TypeCapability) (package : Core n) : Core n
  | second {n : Nat} (capability : TypeCapability) (package : Core n) : Core n
  | ordinaryTypeCode {n : Nat} (level : LevelExpr) : Core n
  | parametricTypeWitness {n : Nat} (level : LevelExpr) : Core n
deriving DecidableEq, Repr

namespace Core

abbrev Renaming (source target : Nat) := Fin source → Fin target

def liftRenaming {source target : Nat}
    (rho : Renaming source target) :
    Renaming (source + 1) (target + 1) :=
  Fin.cases 0 (fun index => Fin.succ (rho index))

def rename {source target : Nat}
    (rho : Renaming source target) : Core source → Core target
  | .sort level => .sort level
  | .var index => .var (rho index)
  | .pi capability domain codomain =>
      .pi capability (rename rho domain)
        (rename (liftRenaming rho) codomain)
  | .sigma capability firstField secondField =>
      .sigma capability (rename rho firstField)
        (rename (liftRenaming rho) secondField)
  | .lam capability domain body =>
      .lam capability (rename rho domain)
        (rename (liftRenaming rho) body)
  | .app function argument =>
      .app (rename rho function) (rename rho argument)
  | .pair firstTerm secondTerm =>
      .pair (rename rho firstTerm) (rename rho secondTerm)
  | .first capability package =>
      .first capability (rename rho package)
  | .second capability package =>
      .second capability (rename rho package)
  | .ordinaryTypeCode level => .ordinaryTypeCode level
  | .parametricTypeWitness level => .parametricTypeWitness level

/-- Add one fresh variable outside a term's current context. -/
def weaken {n : Nat} (term : Core n) : Core (n + 1) :=
  rename Fin.succ term

abbrev Substitution (source target : Nat) := Fin source → Core target

def liftSubstitution {source target : Nat}
    (substitution : Substitution source target) :
    Substitution (source + 1) (target + 1) :=
  Fin.cases (.var 0) (fun index => weaken (substitution index))

def substitute {source target : Nat}
    (substitution : Substitution source target) : Core source → Core target
  | .sort level => .sort level
  | .var index => substitution index
  | .pi capability domain codomain =>
      .pi capability (substitute substitution domain)
        (substitute (liftSubstitution substitution) codomain)
  | .sigma capability firstField secondField =>
      .sigma capability (substitute substitution firstField)
        (substitute (liftSubstitution substitution) secondField)
  | .lam capability domain body =>
      .lam capability (substitute substitution domain)
        (substitute (liftSubstitution substitution) body)
  | .app function argument =>
      .app (substitute substitution function) (substitute substitution argument)
  | .pair firstTerm secondTerm =>
      .pair (substitute substitution firstTerm) (substitute substitution secondTerm)
  | .first capability package =>
      .first capability (substitute substitution package)
  | .second capability package =>
      .second capability (substitute substitution package)
  | .ordinaryTypeCode level => .ordinaryTypeCode level
  | .parametricTypeWitness level => .parametricTypeWitness level

/-- Substitute an argument for the newest variable in a dependent body. -/
def instantiate {n : Nat} (body : Core (n + 1)) (argument : Core n) : Core n :=
  substitute (Fin.cases argument (fun index => .var index)) body

@[simp] theorem liftRenaming_comp_apply
    {source middle target : Nat}
    (rho : Renaming source middle)
    (tau : Renaming middle target)
    (index : Fin (source + 1)) :
    liftRenaming tau (liftRenaming rho index) =
      liftRenaming (fun index => tau (rho index)) index := by
  refine Fin.cases ?_ (fun _ => ?_) index <;> rfl

/-- Renaming twice is the same as the composite renaming. -/
theorem rename_rename
    {source middle target : Nat}
    (rho : Renaming source middle)
    (tau : Renaming middle target)
    (term : Core source) :
    rename tau (rename rho term) =
      rename (fun index => tau (rho index)) term := by
  induction term generalizing middle target with
  | sort level => rfl
  | var index => rfl
  | pi capability domain codomain ihDomain ihCodomain =>
      simp [rename, ihDomain, ihCodomain]
  | sigma capability firstField secondField ihFirst ihSecond =>
      simp [rename, ihFirst, ihSecond]
  | lam capability domain body ihDomain ihBody =>
      simp [rename, ihDomain, ihBody]
  | app function argument ihFunction ihArgument =>
      simp [rename, ihFunction, ihArgument]
  | pair firstTerm secondTerm ihFirst ihSecond =>
      simp [rename, ihFirst, ihSecond]
  | first capability package ihPackage =>
      simp [rename, ihPackage]
  | second capability package ihPackage =>
      simp [rename, ihPackage]
  | ordinaryTypeCode level => rfl
  | parametricTypeWitness level => rfl

/-- Renaming under a binder commutes with weakening. -/
theorem rename_lift_weaken
    {source target : Nat}
    (rho : Renaming source target)
    (term : Core source) :
    rename (liftRenaming rho) (weaken term) = weaken (rename rho term) := by
  unfold weaken
  rw [rename_rename, rename_rename]
  apply congrArg (fun mapping => rename mapping term)
  funext index
  rfl

@[simp] theorem rename_liftSubstitution_apply
    {source middle target : Nat}
    (substitution : Substitution source middle)
    (rho : Renaming middle target)
    (index : Fin (source + 1)) :
    rename (liftRenaming rho) (liftSubstitution substitution index) =
      liftSubstitution (fun index => rename rho (substitution index)) index := by
  refine Fin.cases ?_ (fun older => ?_) index
  · rfl
  · exact rename_lift_weaken rho (substitution older)

/-- Renaming after substitution acts pointwise on the substituted terms. -/
theorem rename_substitute
    {source middle target : Nat}
    (substitution : Substitution source middle)
    (rho : Renaming middle target)
    (term : Core source) :
    rename rho (substitute substitution term) =
      substitute (fun index => rename rho (substitution index)) term := by
  induction term generalizing middle target with
  | sort level => rfl
  | var index => rfl
  | pi capability domain codomain ihDomain ihCodomain =>
      simp [rename, substitute, ihDomain, ihCodomain]
  | sigma capability firstField secondField ihFirst ihSecond =>
      simp [rename, substitute, ihFirst, ihSecond]
  | lam capability domain body ihDomain ihBody =>
      simp [rename, substitute, ihDomain, ihBody]
  | app function argument ihFunction ihArgument =>
      simp [rename, substitute, ihFunction, ihArgument]
  | pair firstTerm secondTerm ihFirst ihSecond =>
      simp [rename, substitute, ihFirst, ihSecond]
  | first capability package ihPackage =>
      simp [rename, substitute, ihPackage]
  | second capability package ihPackage =>
      simp [rename, substitute, ihPackage]
  | ordinaryTypeCode level => rfl
  | parametricTypeWitness level => rfl

@[simp] theorem liftSubstitution_liftRenaming_apply
    {source middle target : Nat}
    (rho : Renaming source middle)
    (substitution : Substitution middle target)
    (index : Fin (source + 1)) :
    liftSubstitution substitution (liftRenaming rho index) =
      liftSubstitution (fun index => substitution (rho index)) index := by
  refine Fin.cases ?_ (fun _ => ?_) index <;> rfl

/-- Substitution after renaming precomposes the substitution by the renaming. -/
theorem substitute_rename
    {source middle target : Nat}
    (rho : Renaming source middle)
    (substitution : Substitution middle target)
    (term : Core source) :
    substitute substitution (rename rho term) =
      substitute (fun index => substitution (rho index)) term := by
  induction term generalizing middle target with
  | sort level => rfl
  | var index => rfl
  | pi capability domain codomain ihDomain ihCodomain =>
      simp [rename, substitute, ihDomain, ihCodomain]
  | sigma capability firstField secondField ihFirst ihSecond =>
      simp [rename, substitute, ihFirst, ihSecond]
  | lam capability domain body ihDomain ihBody =>
      simp [rename, substitute, ihDomain, ihBody]
  | app function argument ihFunction ihArgument =>
      simp [rename, substitute, ihFunction, ihArgument]
  | pair firstTerm secondTerm ihFirst ihSecond =>
      simp [rename, substitute, ihFirst, ihSecond]
  | first capability package ihPackage =>
      simp [rename, substitute, ihPackage]
  | second capability package ihPackage =>
      simp [rename, substitute, ihPackage]
  | ordinaryTypeCode level => rfl
  | parametricTypeWitness level => rfl

/-- Dependent instantiation is natural with respect to renaming. -/
theorem rename_instantiate
    {source target : Nat}
    (rho : Renaming source target)
    (body : Core (source + 1))
    (argument : Core source) :
    rename rho (instantiate body argument) =
      instantiate (rename (liftRenaming rho) body) (rename rho argument) := by
  unfold instantiate
  rw [rename_substitute, substitute_rename]
  congr 1
  funext index
  refine Fin.cases ?_ (fun _ => ?_) index <;> rfl

/-- Lifted substitution commutes with weakening. -/
theorem substitute_lift_weaken
    {source target : Nat}
    (substitution : Substitution source target)
    (term : Core source) :
    substitute (liftSubstitution substitution) (weaken term) =
      weaken (substitute substitution term) := by
  unfold weaken
  rw [substitute_rename, rename_substitute]
  apply congrArg (fun replacement => substitute replacement term)
  funext index
  rfl

@[simp] theorem liftSubstitution_variables
    {n : Nat} :
    liftSubstitution (fun index : Fin n => (.var index : Core n)) =
      (fun index : Fin (n + 1) => (.var index : Core (n + 1))) := by
  funext index
  refine Fin.cases ?_ (fun _ => ?_) index <;> rfl

@[simp] theorem substitute_variables
    {n : Nat}
    (term : Core n) :
    substitute (fun index => .var index) term = term := by
  induction term with
  | sort level => rfl
  | var index => rfl
  | pi capability domain codomain ihDomain ihCodomain =>
      simp [substitute, ihDomain, ihCodomain]
  | sigma capability firstField secondField ihFirst ihSecond =>
      simp [substitute, ihFirst, ihSecond]
  | lam capability domain body ihDomain ihBody =>
      simp [substitute, ihDomain, ihBody]
  | app function argument ihFunction ihArgument =>
      simp [substitute, ihFunction, ihArgument]
  | pair firstTerm secondTerm ihFirst ihSecond =>
      simp [substitute, ihFirst, ihSecond]
  | first capability package ihPackage =>
      simp [substitute, ihPackage]
  | second capability package ihPackage =>
      simp [substitute, ihPackage]
  | ordinaryTypeCode level => rfl
  | parametricTypeWitness level => rfl

/-- Instantiating a weakened term leaves the original term unchanged. -/
@[simp] theorem instantiate_weaken
    {n : Nat}
    (term argument : Core n) :
    instantiate (weaken term) argument = term := by
  unfold instantiate weaken
  rw [substitute_rename]
  exact substitute_variables term

@[simp] theorem substitute_liftSubstitution_apply
    {source middle target : Nat}
    (first : Substitution source middle)
    (second : Substitution middle target)
    (index : Fin (source + 1)) :
    substitute (liftSubstitution second) (liftSubstitution first index) =
      liftSubstitution (fun index => substitute second (first index)) index := by
  refine Fin.cases ?_ (fun older => ?_) index
  · rfl
  · exact substitute_lift_weaken second (first older)

/-- Consecutive substitutions compose pointwise. -/
theorem substitute_substitute
    {source middle target : Nat}
    (first : Substitution source middle)
    (second : Substitution middle target)
    (term : Core source) :
    substitute second (substitute first term) =
      substitute (fun index => substitute second (first index)) term := by
  induction term generalizing middle target with
  | sort level => rfl
  | var index => rfl
  | pi capability domain codomain ihDomain ihCodomain =>
      simp [substitute, ihDomain, ihCodomain]
  | sigma capability firstField secondField ihFirst ihSecond =>
      simp [substitute, ihFirst, ihSecond]
  | lam capability domain body ihDomain ihBody =>
      simp [substitute, ihDomain, ihBody]
  | app function argument ihFunction ihArgument =>
      simp [substitute, ihFunction, ihArgument]
  | pair firstTerm secondTerm ihFirst ihSecond =>
      simp [substitute, ihFirst, ihSecond]
  | first capability package ihPackage =>
      simp [substitute, ihPackage]
  | second capability package ihPackage =>
      simp [substitute, ihPackage]
  | ordinaryTypeCode level => rfl
  | parametricTypeWitness level => rfl

/-- Dependent instantiation commutes with an outer substitution. -/
theorem substitute_instantiate
    {source target : Nat}
    (substitution : Substitution source target)
    (body : Core (source + 1))
    (argument : Core source) :
    substitute substitution (instantiate body argument) =
      instantiate (substitute (liftSubstitution substitution) body)
        (substitute substitution argument) := by
  unfold instantiate
  rw [substitute_substitute, substitute_substitute]
  congr 1
  funext index
  refine Fin.cases ?_ (fun older => ?_) index
  · rfl
  · change substitution older =
      instantiate (weaken (substitution older)) (substitute substitution argument)
    exact (instantiate_weaken (substitution older)
      (substitute substitution argument)).symm

@[simp] theorem rename_var
    {source target : Nat}
    (rho : Renaming source target)
    (index : Fin source) :
    rename rho (.var index) = (.var (rho index) : Core target) := by
  rfl

@[simp] theorem substitute_var
    {source target : Nat}
    (substitution : Substitution source target)
    (index : Fin source) :
    substitute substitution (.var index) = substitution index := by
  rfl

@[simp] theorem instantiate_newest
    {n : Nat}
    (argument : Core n) :
    instantiate (.var 0 : Core (n + 1)) argument = argument := by
  rfl

@[simp] theorem instantiate_older
    {n : Nat}
    (index : Fin n)
    (argument : Core n) :
    instantiate (.var (Fin.succ index) : Core (n + 1)) argument = .var index := by
  rfl

/-- A dependent typing context stores types already weakened into its full scope. -/
abbrev Context (n : Nat) := Fin n → Core n

namespace Context

def extend {n : Nat} (context : Context n) (domain : Core n) : Context (n + 1) :=
  Fin.cases (weaken domain) (fun index => weaken (context index))

@[simp] theorem extend_newest
    {n : Nat}
    (context : Context n)
    (domain : Core n) :
    extend context domain 0 = weaken domain := by
  rfl

@[simp] theorem extend_older
    {n : Nat}
    (context : Context n)
    (domain : Core n)
    (index : Fin n) :
    extend context domain (Fin.succ index) = weaken (context index) := by
  rfl

end Context

abbrev CapabilityContext (n : Nat) := Fin n → TypeCapability

namespace CapabilityContext

def extend {n : Nat}
    (context : CapabilityContext n)
    (capability : TypeCapability) : CapabilityContext (n + 1) :=
  Fin.cases capability (fun index => context index)

@[simp] theorem extend_newest
    {n : Nat}
    (context : CapabilityContext n)
    (capability : TypeCapability) :
    extend context capability 0 = capability := by
  rfl

@[simp] theorem extend_older
    {n : Nat}
    (context : CapabilityContext n)
    (capability : TypeCapability)
    (index : Fin n) :
    extend context capability (Fin.succ index) = context index := by
  rfl

end CapabilityContext

def inferCapability {n : Nat}
    (context : CapabilityContext n) : Core n → Option TypeCapability
  | .var index => some (context index)
  | .ordinaryTypeCode _ => some .ordinaryCode
  | .parametricTypeWitness _ => some .parametricWitness
  | .first capability _ => some capability
  | _ => none

def SafeUseAs {n : Nat}
    (context : CapabilityContext n)
    (term : Core n)
    (target : TypeCapability) : Prop :=
  ∃ source, inferCapability context term = some source ∧ CanCoerce source target

theorem parametric_literal_cannot_be_used_as_code
    {n : Nat}
    (context : CapabilityContext n)
    (level : LevelExpr) :
    ¬ SafeUseAs context (.parametricTypeWitness level) .ordinaryCode := by
  intro hUse
  rcases hUse with ⟨source, hSource, hCoerce⟩
  simp [inferCapability] at hSource
  subst source
  exact no_parametric_witness_to_ordinary_code hCoerce

theorem parametric_variable_cannot_be_used_as_code
    {n : Nat}
    (context : CapabilityContext n)
    (index : Fin n)
    (hParametric : context index = .parametricWitness) :
    ¬ SafeUseAs context (.var index) .ordinaryCode := by
  intro hUse
  rcases hUse with ⟨source, hSource, hCoerce⟩
  simp [inferCapability, hParametric] at hSource
  subst source
  exact no_parametric_witness_to_ordinary_code hCoerce

theorem ordinary_code_can_supply_parametric_witness
    {n : Nat}
    (context : CapabilityContext n)
    (level : LevelExpr) :
    SafeUseAs context (.ordinaryTypeCode level) .parametricWitness := by
  exact ⟨.ordinaryCode, rfl, CanCoerce.codeToWitness⟩

theorem parametric_projection_cannot_be_used_as_code
    {n : Nat}
    (context : CapabilityContext n)
    (package : Core n) :
    ¬ SafeUseAs context (.first .parametricWitness package) .ordinaryCode := by
  intro hUse
  rcases hUse with ⟨source, hSource, hCoerce⟩
  simp [inferCapability] at hSource
  subst source
  exact no_parametric_witness_to_ordinary_code hCoerce

/--
A renaming is admissible for a pair of contexts when it preserves both the
dependent type stored for every variable and that variable's capability.
-/
structure RenamingCompatibility
    {source target : Nat}
    (rho : Renaming source target)
    (sourceContext : Context source)
    (targetContext : Context target)
    (sourceCapabilities : CapabilityContext source)
    (targetCapabilities : CapabilityContext target) : Prop where
  typeAt : ∀ index,
    targetContext (rho index) = rename rho (sourceContext index)
  capabilityAt : ∀ index,
    targetCapabilities (rho index) = sourceCapabilities index

/-- Compatible renamings remain compatible after traversing a binder. -/
theorem RenamingCompatibility.lift
    {source target : Nat}
    {rho : Renaming source target}
    {sourceContext : Context source}
    {targetContext : Context target}
    {sourceCapabilities : CapabilityContext source}
    {targetCapabilities : CapabilityContext target}
    (compatibility : RenamingCompatibility rho sourceContext targetContext
      sourceCapabilities targetCapabilities)
    (domain : Core source)
    (capability : TypeCapability) :
    RenamingCompatibility (liftRenaming rho)
      (Context.extend sourceContext domain)
      (Context.extend targetContext (rename rho domain))
      (CapabilityContext.extend sourceCapabilities capability)
      (CapabilityContext.extend targetCapabilities capability) := by
  constructor
  · intro index
    refine Fin.cases ?_ (fun older => ?_) index
    · exact (rename_lift_weaken rho domain).symm
    · change weaken (targetContext (rho older)) =
        rename (liftRenaming rho) (weaken (sourceContext older))
      rw [compatibility.typeAt older]
      exact (rename_lift_weaken rho (sourceContext older)).symm
  · intro index
    refine Fin.cases ?_ (fun older => ?_) index
    · rfl
    · exact compatibility.capabilityAt older

/-- Adding a fresh newest variable gives a compatible weakening renaming. -/
theorem weakeningCompatibility
    {n : Nat}
    (context : Context n)
    (capabilities : CapabilityContext n)
    (domain : Core n)
    (capability : TypeCapability) :
    RenamingCompatibility Fin.succ context (Context.extend context domain)
      capabilities (CapabilityContext.extend capabilities capability) := by
  constructor
  · intro index
    rfl
  · intro index
    rfl

theorem inferCapability_rename
    {source target : Nat}
    {rho : Renaming source target}
    {sourceContext : Context source}
    {targetContext : Context target}
    {sourceCapabilities : CapabilityContext source}
    {targetCapabilities : CapabilityContext target}
    (compatibility : RenamingCompatibility rho sourceContext targetContext
      sourceCapabilities targetCapabilities)
    (term : Core source) :
    inferCapability targetCapabilities (rename rho term) =
      inferCapability sourceCapabilities term := by
  cases term <;> simp [rename, inferCapability, compatibility.capabilityAt]

/-- Capability-safe use is invariant under every compatible renaming. -/
theorem safeUseAs_rename
    {source target : Nat}
    {rho : Renaming source target}
    {sourceContext : Context source}
    {targetContext : Context target}
    {sourceCapabilities : CapabilityContext source}
    {targetCapabilities : CapabilityContext target}
    (compatibility : RenamingCompatibility rho sourceContext targetContext
      sourceCapabilities targetCapabilities)
    {term : Core source}
    {capability : TypeCapability}
    (safeUse : SafeUseAs sourceCapabilities term capability) :
    SafeUseAs targetCapabilities (rename rho term) capability := by
  rcases safeUse with ⟨sourceCapability, hSource, hCoerce⟩
  exact ⟨sourceCapability,
    (inferCapability_rename compatibility term).trans hSource, hCoerce⟩

theorem safeUseAs_rename_iff
    {source target : Nat}
    {rho : Renaming source target}
    {sourceContext : Context source}
    {targetContext : Context target}
    {sourceCapabilities : CapabilityContext source}
    {targetCapabilities : CapabilityContext target}
    (compatibility : RenamingCompatibility rho sourceContext targetContext
      sourceCapabilities targetCapabilities)
    (term : Core source)
    (capability : TypeCapability) :
    SafeUseAs targetCapabilities (rename rho term) capability ↔
      SafeUseAs sourceCapabilities term capability := by
  constructor
  · intro safeUse
    rcases safeUse with ⟨sourceCapability, hSource, hCoerce⟩
    exact ⟨sourceCapability,
      (inferCapability_rename compatibility term).symm.trans hSource, hCoerce⟩
  · exact safeUseAs_rename compatibility

/-- In particular, renaming cannot turn an unusable witness into code. -/
theorem notSafeUseAs_rename
    {source target : Nat}
    {rho : Renaming source target}
    {sourceContext : Context source}
    {targetContext : Context target}
    {sourceCapabilities : CapabilityContext source}
    {targetCapabilities : CapabilityContext target}
    (compatibility : RenamingCompatibility rho sourceContext targetContext
      sourceCapabilities targetCapabilities)
    {term : Core source}
    {capability : TypeCapability}
    (notSafe : ¬ SafeUseAs sourceCapabilities term capability) :
    ¬ SafeUseAs targetCapabilities (rename rho term) capability := by
  intro renamedSafe
  exact notSafe ((safeUseAs_rename_iff compatibility term capability).mp renamedSafe)

end Core

/--
Typing for the small KCore fragment. The valuation interprets open universe
levels for cumulative subsumption. The parametric Pi rule is restricted to a
universe domain and implements the specification's no-bump formation rule.
-/
inductive CoreHasType (valuation : LevelExpr.Valuation) :
    {n : Nat} → Core.Context n → Core.CapabilityContext n → Core n → Core n → Prop where
  | var
      {n : Nat}
      {context : Core.Context n}
      {capabilities : Core.CapabilityContext n}
      (index : Fin n) :
      CoreHasType valuation context capabilities (.var index) (context index)
  | sort
      {n : Nat}
      {context : Core.Context n}
      {capabilities : Core.CapabilityContext n}
      (level : LevelExpr) :
      CoreHasType valuation context capabilities (.sort level) (.sort (.succ level))
  | ordinaryTypeCode
      {n : Nat}
      {context : Core.Context n}
      {capabilities : Core.CapabilityContext n}
      (level : LevelExpr) :
      CoreHasType valuation context capabilities (.ordinaryTypeCode level) (.sort level)
  | parametricTypeWitness
      {n : Nat}
      {context : Core.Context n}
      {capabilities : Core.CapabilityContext n}
      (level : LevelExpr) :
      CoreHasType valuation context capabilities (.parametricTypeWitness level) (.sort level)
  | piOrdinary
      {n : Nat}
      {context : Core.Context n}
      {capabilities : Core.CapabilityContext n}
      {domain : Core n}
      {codomain : Core (n + 1)}
      {domainLevel codomainLevel : LevelExpr}
      (domainType : CoreHasType valuation context capabilities domain (.sort domainLevel))
      (codomainType : CoreHasType valuation (Core.Context.extend context domain)
        (Core.CapabilityContext.extend capabilities .ordinaryCode)
        codomain (.sort codomainLevel)) :
      CoreHasType valuation context capabilities (.pi .ordinaryCode domain codomain)
        (.sort (.max domainLevel codomainLevel))
  | piParametric
      {n : Nat}
      {context : Core.Context n}
      {capabilities : Core.CapabilityContext n}
      {rho : LevelExpr}
      {codomain : Core (n + 1)}
      {codomainLevel : LevelExpr}
      (codomainType : CoreHasType valuation
        (Core.Context.extend context (.sort rho))
        (Core.CapabilityContext.extend capabilities .parametricWitness)
        codomain (.sort codomainLevel)) :
      CoreHasType valuation context capabilities
        (.pi .parametricWitness (.sort rho) codomain)
        (.sort codomainLevel)
  | sigmaOrdinary
      {n : Nat}
      {context : Core.Context n}
      {capabilities : Core.CapabilityContext n}
      {first : Core n}
      {second : Core (n + 1)}
      {firstLevel secondLevel : LevelExpr}
      (firstType : CoreHasType valuation context capabilities first (.sort firstLevel))
      (secondType : CoreHasType valuation (Core.Context.extend context first)
        (Core.CapabilityContext.extend capabilities .ordinaryCode)
        second (.sort secondLevel)) :
      CoreHasType valuation context capabilities (.sigma .ordinaryCode first second)
        (.sort (.max firstLevel secondLevel))
  | sigmaParametric
      {n : Nat}
      {context : Core.Context n}
      {capabilities : Core.CapabilityContext n}
      {rho : LevelExpr}
      {second : Core (n + 1)}
      {secondLevel : LevelExpr}
      (secondType : CoreHasType valuation
        (Core.Context.extend context (.sort rho))
        (Core.CapabilityContext.extend capabilities .parametricWitness)
        second (.sort secondLevel)) :
      CoreHasType valuation context capabilities
        (.sigma .parametricWitness (.sort rho) second)
        (.sort secondLevel)
  | lam
      {n : Nat}
      {context : Core.Context n}
      {capabilities : Core.CapabilityContext n}
      {capability : TypeCapability}
      {domain : Core n}
      {body codomain : Core (n + 1)}
      {domainLevel : LevelExpr}
      (domainType : CoreHasType valuation context capabilities domain (.sort domainLevel))
      (bodyType : CoreHasType valuation (Core.Context.extend context domain)
        (Core.CapabilityContext.extend capabilities capability) body codomain) :
      CoreHasType valuation context capabilities (.lam capability domain body)
        (.pi capability domain codomain)
  | app
      {n : Nat}
      {context : Core.Context n}
      {capabilities : Core.CapabilityContext n}
      {capability : TypeCapability}
      {function argument domain : Core n}
      {codomain : Core (n + 1)}
      (functionType : CoreHasType valuation context capabilities function
        (.pi capability domain codomain))
      (argumentType : CoreHasType valuation context capabilities argument domain)
      (capabilityUse : Core.SafeUseAs capabilities argument capability) :
      CoreHasType valuation context capabilities (.app function argument)
        (Core.instantiate codomain argument)
  | pair
      {n : Nat}
      {context : Core.Context n}
      {capabilities : Core.CapabilityContext n}
      {capability : TypeCapability}
      {first second domain : Core n}
      {codomain : Core (n + 1)}
      (firstType : CoreHasType valuation context capabilities first domain)
      (secondType : CoreHasType valuation context capabilities second
        (Core.instantiate codomain first))
      (capabilityUse : Core.SafeUseAs capabilities first capability) :
      CoreHasType valuation context capabilities (.pair first second)
        (.sigma capability domain codomain)
  | first
      {n : Nat}
      {context : Core.Context n}
      {capabilities : Core.CapabilityContext n}
      {capability : TypeCapability}
      {package domain : Core n}
      {codomain : Core (n + 1)}
      (packageType : CoreHasType valuation context capabilities package
        (.sigma capability domain codomain)) :
      CoreHasType valuation context capabilities (.first capability package) domain
  | second
      {n : Nat}
      {context : Core.Context n}
      {capabilities : Core.CapabilityContext n}
      {capability : TypeCapability}
      {package domain : Core n}
      {codomain : Core (n + 1)}
      (packageType : CoreHasType valuation context capabilities package
        (.sigma capability domain codomain)) :
      CoreHasType valuation context capabilities (.second capability package)
        (Core.instantiate codomain (.first capability package))
  | cumulative
      {n : Nat}
      {context : Core.Context n}
      {capabilities : Core.CapabilityContext n}
      {term : Core n}
      {lower upper : LevelExpr}
      (premise : CoreHasType valuation context capabilities term (.sort lower))
      (levelLe : lower.eval valuation ≤ upper.eval valuation) :
      CoreHasType valuation context capabilities term (.sort upper)

namespace CoreHasType

/-- Every context-and-capability-compatible renaming preserves typing. -/
theorem rename_preserves_typing
    {source : Nat}
    {valuation : LevelExpr.Valuation}
    {sourceContext : Core.Context source}
    {sourceCapabilities : Core.CapabilityContext source}
    {term type : Core source}
    (typing : CoreHasType valuation sourceContext sourceCapabilities term type)
    {target : Nat}
    (mapping : Core.Renaming source target)
    {targetContext : Core.Context target}
    {targetCapabilities : Core.CapabilityContext target}
    (compatibility : Core.RenamingCompatibility mapping
      sourceContext targetContext sourceCapabilities targetCapabilities) :
    CoreHasType valuation targetContext targetCapabilities
      (Core.rename mapping term) (Core.rename mapping type) := by
  induction typing generalizing target with
  | var index =>
      rw [← compatibility.typeAt index]
      exact .var (mapping index)
  | sort level =>
      exact .sort level
  | ordinaryTypeCode level =>
      exact .ordinaryTypeCode level
  | parametricTypeWitness level =>
      exact .parametricTypeWitness level
  | piOrdinary domainType codomainType ihDomain ihCodomain =>
      exact .piOrdinary
        (ihDomain mapping compatibility)
        (ihCodomain (Core.liftRenaming mapping)
          (compatibility.lift _ .ordinaryCode))
  | piParametric codomainType ihCodomain =>
      exact .piParametric
        (ihCodomain (Core.liftRenaming mapping)
          (compatibility.lift _ .parametricWitness))
  | sigmaOrdinary firstType secondType ihFirst ihSecond =>
      exact .sigmaOrdinary
        (ihFirst mapping compatibility)
        (ihSecond (Core.liftRenaming mapping)
          (compatibility.lift _ .ordinaryCode))
  | sigmaParametric secondType ihSecond =>
      exact .sigmaParametric
        (ihSecond (Core.liftRenaming mapping)
          (compatibility.lift _ .parametricWitness))
  | lam domainType bodyType ihDomain ihBody =>
      exact .lam
        (ihDomain mapping compatibility)
        (ihBody (Core.liftRenaming mapping)
          (compatibility.lift _ _))
  | app functionType argumentType capabilityUse ihFunction ihArgument =>
      simpa only [Core.rename, Core.rename_instantiate] using
        (CoreHasType.app
          (ihFunction mapping compatibility)
          (ihArgument mapping compatibility)
          (Core.safeUseAs_rename compatibility capabilityUse))
  | pair firstType secondType capabilityUse ihFirst ihSecond =>
      have renamedSecond := ihSecond mapping compatibility
      rw [Core.rename_instantiate] at renamedSecond
      exact CoreHasType.pair
        (ihFirst mapping compatibility)
        renamedSecond
        (Core.safeUseAs_rename compatibility capabilityUse)
  | first packageType ihPackage =>
      exact .first (ihPackage mapping compatibility)
  | second packageType ihPackage =>
      simpa only [Core.rename, Core.rename_instantiate] using
        (CoreHasType.second (ihPackage mapping compatibility))
  | cumulative premise levelLe ihPremise =>
      exact .cumulative (ihPremise mapping compatibility) levelLe

/-- Typing weakening is the fresh-variable instance of admissible renaming. -/
theorem weaken_preserves_typing
    {n : Nat}
    {valuation : LevelExpr.Valuation}
    {context : Core.Context n}
    {capabilities : Core.CapabilityContext n}
    {term type : Core n}
    (typing : CoreHasType valuation context capabilities term type)
    (freshDomain : Core n)
    (freshCapability : TypeCapability) :
    CoreHasType valuation
      (Core.Context.extend context freshDomain)
      (Core.CapabilityContext.extend capabilities freshCapability)
      (Core.weaken term) (Core.weaken type) := by
  exact rename_preserves_typing typing Fin.succ
    (Core.weakeningCompatibility context capabilities freshDomain freshCapability)

/--
A well-typed substitution supplies a term of the substituted variable type and
may only strengthen its source capability (ordinary code may supply a witness,
but a witness cannot supply ordinary code).
-/
structure SubstitutionCompatibility
    (valuation : LevelExpr.Valuation)
    {source target : Nat}
    (substitution : Core.Substitution source target)
    (sourceContext : Core.Context source)
    (targetContext : Core.Context target)
    (sourceCapabilities : Core.CapabilityContext source)
    (targetCapabilities : Core.CapabilityContext target) : Prop where
  typingAt : ∀ index,
    CoreHasType valuation targetContext targetCapabilities
      (substitution index) (Core.substitute substitution (sourceContext index))
  safeAt : ∀ index,
    Core.SafeUseAs targetCapabilities (substitution index)
      (sourceCapabilities index)

/-- Capability-safe use is preserved by every compatible substitution. -/
theorem safeUseAs_substitute
    {source target : Nat}
    {valuation : LevelExpr.Valuation}
    {substitution : Core.Substitution source target}
    {sourceContext : Core.Context source}
    {targetContext : Core.Context target}
    {sourceCapabilities : Core.CapabilityContext source}
    {targetCapabilities : Core.CapabilityContext target}
    (compatibility : SubstitutionCompatibility valuation substitution
      sourceContext targetContext sourceCapabilities targetCapabilities)
    {term : Core source}
    {capability : TypeCapability}
    (safeUse : Core.SafeUseAs sourceCapabilities term capability) :
    Core.SafeUseAs targetCapabilities
      (Core.substitute substitution term) capability := by
  rcases safeUse with ⟨sourceCapability, inferred, coercion⟩
  cases term with
  | var index =>
      simp [Core.inferCapability] at inferred
      subst sourceCapability
      rcases compatibility.safeAt index with
        ⟨replacementCapability, replacementInferred, replacementCoercion⟩
      exact ⟨replacementCapability, replacementInferred,
        replacementCoercion.trans coercion⟩
  | ordinaryTypeCode level =>
      exact ⟨sourceCapability,
        by simpa [Core.substitute, Core.inferCapability] using inferred,
        coercion⟩
  | parametricTypeWitness level =>
      exact ⟨sourceCapability,
        by simpa [Core.substitute, Core.inferCapability] using inferred,
        coercion⟩
  | first fieldCapability package =>
      exact ⟨sourceCapability,
        by simpa [Core.substitute, Core.inferCapability] using inferred,
        coercion⟩
  | sort level => simp [Core.inferCapability] at inferred
  | pi binderCapability domain codomain =>
      simp [Core.inferCapability] at inferred
  | sigma binderCapability firstField secondField =>
      simp [Core.inferCapability] at inferred
  | lam binderCapability domain body =>
      simp [Core.inferCapability] at inferred
  | app function argument => simp [Core.inferCapability] at inferred
  | pair firstTerm secondTerm => simp [Core.inferCapability] at inferred
  | second fieldCapability package =>
      simp [Core.inferCapability] at inferred

/-- Compatible substitutions remain compatible underneath a binder. -/
theorem SubstitutionCompatibility.lift
    {source target : Nat}
    {valuation : LevelExpr.Valuation}
    {substitution : Core.Substitution source target}
    {sourceContext : Core.Context source}
    {targetContext : Core.Context target}
    {sourceCapabilities : Core.CapabilityContext source}
    {targetCapabilities : Core.CapabilityContext target}
    (compatibility : SubstitutionCompatibility valuation substitution
      sourceContext targetContext sourceCapabilities targetCapabilities)
    (domain : Core source)
    (capability : TypeCapability) :
    SubstitutionCompatibility valuation (Core.liftSubstitution substitution)
      (Core.Context.extend sourceContext domain)
      (Core.Context.extend targetContext (Core.substitute substitution domain))
      (Core.CapabilityContext.extend sourceCapabilities capability)
      (Core.CapabilityContext.extend targetCapabilities capability) := by
  constructor
  · intro index
    refine Fin.cases ?_ (fun older => ?_) index
    · change CoreHasType valuation
        (Core.Context.extend targetContext (Core.substitute substitution domain))
        (Core.CapabilityContext.extend targetCapabilities capability)
        (.var 0)
        (Core.substitute (Core.liftSubstitution substitution) (Core.weaken domain))
      rw [Core.substitute_lift_weaken]
      exact .var 0
    · change CoreHasType valuation
        (Core.Context.extend targetContext (Core.substitute substitution domain))
        (Core.CapabilityContext.extend targetCapabilities capability)
        (Core.weaken (substitution older))
        (Core.substitute (Core.liftSubstitution substitution)
          (Core.weaken (sourceContext older)))
      rw [Core.substitute_lift_weaken]
      exact weaken_preserves_typing (compatibility.typingAt older)
        (Core.substitute substitution domain) capability
  · intro index
    refine Fin.cases ?_ (fun older => ?_) index
    · exact ⟨capability, rfl, CanCoerce.refl capability⟩
    · exact Core.safeUseAs_rename
        (Core.weakeningCompatibility targetContext targetCapabilities
          (Core.substitute substitution domain) capability)
        (compatibility.safeAt older)

/-- Every well-typed, capability-compatible substitution preserves typing. -/
theorem substitute_preserves_typing
    {source : Nat}
    {valuation : LevelExpr.Valuation}
    {sourceContext : Core.Context source}
    {sourceCapabilities : Core.CapabilityContext source}
    {term type : Core source}
    (typing : CoreHasType valuation sourceContext sourceCapabilities term type)
    {target : Nat}
    (substitution : Core.Substitution source target)
    {targetContext : Core.Context target}
    {targetCapabilities : Core.CapabilityContext target}
    (compatibility : SubstitutionCompatibility valuation substitution
      sourceContext targetContext sourceCapabilities targetCapabilities) :
    CoreHasType valuation targetContext targetCapabilities
      (Core.substitute substitution term) (Core.substitute substitution type) := by
  induction typing generalizing target with
  | var index =>
      exact compatibility.typingAt index
  | sort level =>
      exact .sort level
  | ordinaryTypeCode level =>
      exact .ordinaryTypeCode level
  | parametricTypeWitness level =>
      exact .parametricTypeWitness level
  | piOrdinary domainType codomainType ihDomain ihCodomain =>
      exact .piOrdinary
        (ihDomain substitution compatibility)
        (ihCodomain (Core.liftSubstitution substitution)
          (compatibility.lift _ .ordinaryCode))
  | piParametric codomainType ihCodomain =>
      exact .piParametric
        (ihCodomain (Core.liftSubstitution substitution)
          (compatibility.lift _ .parametricWitness))
  | sigmaOrdinary firstType secondType ihFirst ihSecond =>
      exact .sigmaOrdinary
        (ihFirst substitution compatibility)
        (ihSecond (Core.liftSubstitution substitution)
          (compatibility.lift _ .ordinaryCode))
  | sigmaParametric secondType ihSecond =>
      exact .sigmaParametric
        (ihSecond (Core.liftSubstitution substitution)
          (compatibility.lift _ .parametricWitness))
  | lam domainType bodyType ihDomain ihBody =>
      exact .lam
        (ihDomain substitution compatibility)
        (ihBody (Core.liftSubstitution substitution)
          (compatibility.lift _ _))
  | app functionType argumentType capabilityUse ihFunction ihArgument =>
      simpa only [Core.substitute, Core.substitute_instantiate] using
        (CoreHasType.app
          (ihFunction substitution compatibility)
          (ihArgument substitution compatibility)
          (safeUseAs_substitute compatibility capabilityUse))
  | pair firstType secondType capabilityUse ihFirst ihSecond =>
      have substitutedSecond := ihSecond substitution compatibility
      rw [Core.substitute_instantiate] at substitutedSecond
      exact CoreHasType.pair
        (ihFirst substitution compatibility)
        substitutedSecond
        (safeUseAs_substitute compatibility capabilityUse)
  | first packageType ihPackage =>
      exact .first (ihPackage substitution compatibility)
  | second packageType ihPackage =>
      simpa only [Core.substitute, Core.substitute_instantiate] using
        (CoreHasType.second (ihPackage substitution compatibility))
  | cumulative premise levelLe ihPremise =>
      exact .cumulative (ihPremise substitution compatibility) levelLe

/-- Replacing the newest variable by a checked argument is compatible. -/
theorem instantiateCompatibility
    {n : Nat}
    {valuation : LevelExpr.Valuation}
    {context : Core.Context n}
    {capabilities : Core.CapabilityContext n}
    {domain argument : Core n}
    {capability : TypeCapability}
    (argumentType : CoreHasType valuation context capabilities argument domain)
    (argumentSafe : Core.SafeUseAs capabilities argument capability) :
    SubstitutionCompatibility valuation
      (Fin.cases argument (fun index => .var index))
      (Core.Context.extend context domain) context
      (Core.CapabilityContext.extend capabilities capability) capabilities := by
  constructor
  · intro index
    refine Fin.cases ?_ (fun older => ?_) index
    · change CoreHasType valuation context capabilities argument
        (Core.instantiate (Core.weaken domain) argument)
      simpa using argumentType
    · change CoreHasType valuation context capabilities (.var older)
        (Core.instantiate (Core.weaken (context older)) argument)
      simpa using
        (CoreHasType.var (valuation := valuation)
          (context := context) (capabilities := capabilities) older)
  · intro index
    refine Fin.cases ?_ (fun older => ?_) index
    · exact argumentSafe
    · exact ⟨capabilities older, rfl, CanCoerce.refl (capabilities older)⟩

/-- The standard dependent substitution lemma for the newest variable. -/
theorem dependent_substitution
    {n : Nat}
    {valuation : LevelExpr.Valuation}
    {context : Core.Context n}
    {capabilities : Core.CapabilityContext n}
    {capability : TypeCapability}
    {domain argument : Core n}
    {body type : Core (n + 1)}
    (bodyType : CoreHasType valuation
      (Core.Context.extend context domain)
      (Core.CapabilityContext.extend capabilities capability) body type)
    (argumentType : CoreHasType valuation context capabilities argument domain)
    (argumentSafe : Core.SafeUseAs capabilities argument capability) :
    CoreHasType valuation context capabilities
      (Core.instantiate body argument) (Core.instantiate type argument) := by
  exact substitute_preserves_typing bodyType
    (Fin.cases argument (fun index => .var index))
    (instantiateCompatibility argumentType argumentSafe)

/-- The general inversion principle used for universe-sort regularity. -/
theorem sort_regularity_general
    {n : Nat}
    {valuation : LevelExpr.Valuation}
    {context : Core.Context n}
    {capabilities : Core.CapabilityContext n}
    {term type : Core n}
    (typing : CoreHasType valuation context capabilities term type) :
    ∀ level classifier,
      term = .sort level →
      type = .sort classifier →
      (LevelExpr.succ level).eval valuation ≤ classifier.eval valuation := by
  induction typing with
  | var index =>
      intro level classifier hTerm
      cases hTerm
  | sort actual =>
      intro level classifier hTerm hType
      cases hTerm
      cases hType
      exact LevelValue.le_refl ((LevelExpr.succ actual).eval valuation)
  | ordinaryTypeCode actual =>
      intro level classifier hTerm
      cases hTerm
  | parametricTypeWitness actual =>
      intro level classifier hTerm
      cases hTerm
  | piOrdinary domainType codomainType ihDomain ihCodomain =>
      intro level classifier hTerm
      cases hTerm
  | piParametric codomainType ihCodomain =>
      intro level classifier hTerm
      cases hTerm
  | sigmaOrdinary firstType secondType ihFirst ihSecond =>
      intro level classifier hTerm
      cases hTerm
  | sigmaParametric secondType ihSecond =>
      intro level classifier hTerm
      cases hTerm
  | lam domainType bodyType ihDomain ihBody =>
      intro level classifier hTerm
      cases hTerm
  | app functionType argumentType capabilityUse ihFunction ihArgument =>
      intro level classifier hTerm
      cases hTerm
  | pair firstType secondType capabilityUse ihFirst ihSecond =>
      intro level classifier hTerm
      cases hTerm
  | first packageType ihPackage =>
      intro level classifier hTerm
      cases hTerm
  | second packageType ihPackage =>
      intro level classifier hTerm
      cases hTerm
  | cumulative premise levelLe ih =>
      intro level classifier hTerm hType
      cases hType
      exact LevelValue.le_trans (ih level _ hTerm rfl) levelLe

/-- Every typing of `Type u` has classifier at least `succ u`. -/
theorem sort_regularity
    {n : Nat}
    {valuation : LevelExpr.Valuation}
    {context : Core.Context n}
    {capabilities : Core.CapabilityContext n}
    {level classifier : LevelExpr}
    (typing : CoreHasType valuation context capabilities (.sort level) (.sort classifier)) :
    (LevelExpr.succ level).eval valuation ≤ classifier.eval valuation := by
  exact sort_regularity_general typing level classifier rfl rfl

/-- The checked KCore fragment has no judgment `Type u : Type u`. -/
theorem no_type_in_type
    {n : Nat}
    {valuation : LevelExpr.Valuation}
    {context : Core.Context n}
    {capabilities : Core.CapabilityContext n}
    (level : LevelExpr) :
    CoreHasType valuation context capabilities (.sort level) (.sort level) → False := by
  intro typing
  exact LevelExpr.succ_not_le_self valuation level (sort_regularity typing)

/-- Application has the dependent codomain obtained by capture-avoiding instantiation. -/
theorem application_preserves_dependent_type
    {n : Nat}
    {valuation : LevelExpr.Valuation}
    {context : Core.Context n}
    {capabilities : Core.CapabilityContext n}
    {capability : TypeCapability}
    {function argument domain : Core n}
    {codomain : Core (n + 1)}
    (functionType : CoreHasType valuation context capabilities function
      (.pi capability domain codomain))
    (argumentType : CoreHasType valuation context capabilities argument domain)
    (capabilityUse : Core.SafeUseAs capabilities argument capability) :
    CoreHasType valuation context capabilities (.app function argument)
      (Core.instantiate codomain argument) := by
  exact .app functionType argumentType capabilityUse

/-- The KCore encoding of `(0 t : Type rho, a : t)`. -/
def parametricDependentPair {n : Nat} (rho : LevelExpr) : Core n :=
  .sigma .parametricWitness (.sort rho) (.var 0)

/-- The exact small dependent pair is classified by `Type rho`, with no bump. -/
theorem parametric_dependent_pair_typed
    {n : Nat}
    {valuation : LevelExpr.Valuation}
    {context : Core.Context n}
    {capabilities : Core.CapabilityContext n}
    (rho : LevelExpr) :
    CoreHasType valuation context capabilities
      (parametricDependentPair rho) (.sort rho) := by
  exact .sigmaParametric (.var 0)

/-- Inside the second field, `t` is available as a type classified by `Type rho`. -/
theorem parametric_pair_witness_usable_as_type
    {n : Nat}
    {valuation : LevelExpr.Valuation}
    {context : Core.Context n}
    {capabilities : Core.CapabilityContext n}
    (rho : LevelExpr) :
    CoreHasType valuation
      (Core.Context.extend context (.sort rho))
      (Core.CapabilityContext.extend capabilities .parametricWitness)
      (.var 0 : Core (n + 1)) (.sort rho) := by
  exact .var 0

theorem parametric_pair_witness_has_parametric_capability
    {n : Nat}
    (capabilities : Core.CapabilityContext n) :
    Core.SafeUseAs
      (Core.CapabilityContext.extend capabilities .parametricWitness)
      (.var 0 : Core (n + 1)) .parametricWitness := by
  exact ⟨.parametricWitness, rfl, CanCoerce.witnessRefl⟩

/-- The same `t` cannot cross the forbidden witness-to-code boundary. -/
theorem parametric_pair_witness_not_ordinary_code
    {n : Nat}
    (capabilities : Core.CapabilityContext n) :
    ¬ Core.SafeUseAs
      (Core.CapabilityContext.extend capabilities .parametricWitness)
      (.var 0 : Core (n + 1)) .ordinaryCode := by
  exact Core.parametric_variable_cannot_be_used_as_code
    (Core.CapabilityContext.extend capabilities .parametricWitness) 0 rfl

/-- Projecting `t` from a package preserves both its type and parametric capability. -/
theorem parametric_sigma_first_projection_safe
    {n : Nat}
    {valuation : LevelExpr.Valuation}
    {context : Core.Context n}
    {capabilities : Core.CapabilityContext n}
    {package : Core n}
    {rho : LevelExpr}
    (packageType : CoreHasType valuation context capabilities package
      (parametricDependentPair rho)) :
    CoreHasType valuation context capabilities
        (.first .parametricWitness package) (.sort rho) ∧
      ¬ Core.SafeUseAs capabilities
        (.first .parametricWitness package) .ordinaryCode := by
  constructor
  · exact .first packageType
  · exact Core.parametric_projection_cannot_be_used_as_code capabilities package

/-- The value projection has the projected witness itself as its dependent type. -/
theorem parametric_sigma_second_projection_typed
    {n : Nat}
    {valuation : LevelExpr.Valuation}
    {context : Core.Context n}
    {capabilities : Core.CapabilityContext n}
    {package : Core n}
    {rho : LevelExpr}
    (packageType : CoreHasType valuation context capabilities package
      (parametricDependentPair rho)) :
    CoreHasType valuation context capabilities
      (.second .parametricWitness package)
      (.first .parametricWitness package) := by
  exact .second packageType

/--
Small Sigma formation and predicative sort stratification coexist: the former
does not manufacture the `Type rho : Type rho` premise needed by Girard.
-/
theorem parametric_dependent_pair_does_not_collapse_universes
    {n : Nat}
    {valuation : LevelExpr.Valuation}
    {context : Core.Context n}
    {capabilities : Core.CapabilityContext n}
    (rho : LevelExpr) :
    CoreHasType valuation context capabilities
        (parametricDependentPair rho) (.sort rho) ∧
      (CoreHasType valuation context capabilities
        (.sort rho) (.sort rho) → False) := by
  exact ⟨parametric_dependent_pair_typed rho, no_type_in_type rho⟩

end CoreHasType

end Kappa.Universes
