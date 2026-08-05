# Revision notes relative to the previous proposal

The new package is a rewrite, not a textual patch over the previous generated files.

1. `reflectsDec`, `reflectsSound`, `reflectsComplete`, `happly`, `happlyForall`, `borrowHapply`, and `eqReflect` now have ordinary implementations.
2. `funExt`, `forallExt`, and `borrowFunExt` are the only new genuine foundation `expect term` declarations; their mandatory provider and identity are explicit.
3. Hedberg's decision procedure uses ordinary borrowed arrows, not `forall` arguments.
4. Function-valued h-level theorems distinguish ordinary, implicit quantity-`0`, and borrowed Pis.
5. `evidence uniqueness` supplies a non-circular proof that all complete dictionaries of a trait application are equal.
6. Fresh first-class evidence construction is permitted only for independently unique evidence; general traits remain sealed-coherent.
7. Synthesized members use prefix syntax (`derive member : T`), eliminating the trailing-equality parsing problem.
8. Synthesized supertraits use `derive C` items in the supertrait context.
9. `Eq` and `Equiv` remain separate. `Eq -> Equiv` is a fallback instance, so a direct non-equality `Equiv` wins.
10. Proof-only relation-law traits are separate from selected ambient structures.
11. `Preorder`, `PartialOrder`, and a corrected total `Ord` are specified, and the old fake-totality member is removed.
12. `Alternative` now refines `Applicative` and carries only left identity, right identity, and associativity.
13. Appendix T fixtures are **individual suite files in 109 suite roots**, not one monolithic Markdown block.
