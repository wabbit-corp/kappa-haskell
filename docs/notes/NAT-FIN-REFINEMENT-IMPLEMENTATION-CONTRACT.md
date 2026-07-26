# Nat / Fin / Refinement implementation contract

This note records the implementation contract used while completing
`NAT-FIN-REFINEMENT-PLAN.md`. `docs/Spec.md` remains normative.

## Root causes

1. Logical `Nat` and its compact runtime representation were previously
   conflated. Constructor computation, source reachability, and proof
   generation must use the logical declaration; compact storage is a verified
   backend view.
2. H-level and equality derivation had no checked declaration path. A `derive`
   declaration must register coherent instance heads before body checking and
   must emit evidence that survives ordinary KCore checking.
3. Existing arithmetic helpers decide some propositions but do not carry a
   selected provider or replayable proof across the KCore boundary. Solver
   success is not itself evidence.
4. `Fin`, `Refined`, ranges, cardinality, and compact layouts need one
   proof-preserving chain from source definitions through verified
   representation certificates; no backend fact may leak back into source
   inhabitance.

## Invariants

* `Nat.Zero` and `Nat.Succ` are the source authority through checked KCore.
  Exact compact arithmetic must preserve every constructor and eliminator
  observation.
* Generated no-confusion and derivation evidence is stable, deterministic,
  visibility-aware, and checked like user KCore. Hidden constructors do not
  become proof sources outside their defining scope.
* Arithmetic normalization is authorized only by the exact coherent evidence
  selected by ordinary implicit resolution. Provider identity, assumptions,
  goal, normal form, solver version, and context are decisive certificate
  fields.
* Non-definitional arithmetic equality is represented by explicit checked
  evidence and transport. It is never accepted as conversion and is never
  encoded as `refl` at unequal endpoints.
* A refinement is constructed only with an inhabitant of its predicate fiber
  and matching `IsProp` evidence. Erasure follows checking; it cannot replace
  either proof.
* Source inhabitance and exhaustiveness use logical constructors and actual
  proof inhabitance. Runtime shape and optimization use independently
  verified representation evidence.
* Every optimized backend path has the same selected evidence and semantics as
  generic lowering. Unproved cases fall back conservatively or reject.

## Supported and fail-closed cases

* The portable derivation fragment supports ordinary visible point
  constructors, telescope-ordered fields with required h-level/equality
  evidence, and guarded recursive data SCCs. Functions without exact `IsSet`
  evidence, opaque unavailable fields, higher/path constructors, ambiguous
  refinement shapes, and non-natural representation shapes reject locally.
* The arithmetic service supports the provider-qualified fragment listed in
  Spec §15.8, with deterministic resource limits and principal meta
  assignment. Nonlinear, underconstrained, unsupported-provider, or
  resource-limited goals remain unknown and do not generate evidence.
* Compact finite/refinement layouts are optional profile capabilities.
  Exact non-unary Nat and verified proof erasure are required on every
  runnable backend. A required capability without a verified representation
  rejects with the specified backend diagnostic.

## Deferred work

Only extensions explicitly outside the v1 contract are deferred: higher/path
constructor no-confusion, user-defined declaration derivers, generalized
ordinal-layout derivation, and optional compact layouts on profiles that do
not advertise them. Required NFR-0 through NFR-8 behavior is not deferred by
this note.
