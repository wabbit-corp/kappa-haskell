# Universe / `TypeLevel` / constructor-size conformance tests (PENDING)

Portable conformance tests for the universe discipline in the spec after the
TypeLevel proof-bound revision: `TypeLevel` is the compile-time code type for
admitted universe levels, including `ω`; bounds are ordinary erased
level-comparison proof binders; `LevelLe` and `LevelLt` are transparent
compatibility aliases; and unbounded level-indexed telescopes are rejected with
`E_UNIVERSE_UNBOUNDED_TELESCOPE`.

PENDING: the implementation does not yet implement this full discipline
(including `TypeLevel`, `Typeω`, level-comparison proof binders, or the
unbounded-telescope diagnostic). Move these into `tests/conformance/universes/`
as the features land.

Notes:

* The old bounded-level binder syntax `(u : TypeLevel < κ)` is not part of
  Kappa v1. Use `(u : TypeLevel) -> (@0 p : u < κ) -> ...`.
* There is no automatic `ω` ceiling for `(u : TypeLevel) -> Type u`,
  `exists (u : TypeLevel). Type u`, or `(u : TypeLevel, T : Type u)`.
* Parametric constructor binders such as `(@0 A : Typeρ)` do not store ordinary
  type-code values and do not generate constructor-size obligations by
  themselves.
