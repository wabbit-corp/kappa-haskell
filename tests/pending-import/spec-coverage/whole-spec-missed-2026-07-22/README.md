# Whole-spec missed coverage — 2026-07-22

This campaign supplements the 2026-07-19 whole-spec campaign. It contains
requirements and cross-feature combinations that were not independently pinned
by that campaign and are unrelated to the first-class-universe implementation.

The fixtures have since been distributed into the parent directory's semantic
area folders; this file remains here as the campaign report.

Coverage added here:

- §14.1, §19.1, §19.5, and §28.2: standard-prelude supertrait closure,
  proof-valued Functor law members, and the required
  `MonadResource.bracket` dictionary member;
- §19.2 and §19.3: aligned `try` / `try match` clauses and `continue` crossing a
  `try` while `finally` still runs;
- §18.1.19, §18.1.21, and §18.1.22: a handled `do` computation beginning on the
  line after the selected effect label, as used by the specification's worked
  examples;
- §20.8, §20.10.3, and §20.10.6: compiler-generated join temporaries do not
  become fields of the surface quantitative row used by bare `distinct`;
- §9.4: more than one companion-fragment implementation of an `expect` is an
  ambiguous expectation, not merely an ordinary duplicate;
- §10.2 and §10.4.2: the current specification's unchecked negative recursive
  occurrence in a GADT constructor result index.

Each fixture combines the target with another language boundary: local evidence
and associated members, handlers and scoped effects, loops and unwinding,
queries and destructuring, GADT refinement, or multi-file fragment composition.

## Validation snapshot

Run independently against the existing working-tree compiler binary on
2026-07-22 (no rebuild): **4 pass / 6 fail / 0 unsupported / 0 harness-error**.

Passing coverage: aligned plain `try`, join-plus-bare-`distinct`, the written
GADT-result positivity rule, and ambiguous multi-fragment `expect` satisfaction.

The six failures expose distinct gaps:

- standard `Applicative`, `Traversable`, `MonadError`, and `MonadResource`
  evidence does not provide the supertraits declared by the specification;
- Functor dictionaries omit the required `mapId` and `mapComp` proof members;
- the standard `MonadResource` dictionary member is named `bracketM`, so
  `resource.bracket` is unavailable;
- aligned `try match` clauses are rejected at the following declaration;
- a next-line handled `do` block is rejected as unexpected indentation;
- `continue` inside `try` is incorrectly diagnosed as outside its enclosing
  loop.
