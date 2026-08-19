# Revision history for kappa-haskell

## 0.3.0 -- 2026-08-18

* Add first-class universe levels, replayable observation/evidence checks, and
  the logical Nat/Fin/refinement substrate.
* Strengthen QTT existential handling, checked derivation, and recursive
  termination checking, including call-graph phases and structural field
  projections.
* Make layout recovery fail closed in expression continuations while preserving
  declaration recovery, and support multiline named constructor blocks in
  `do` statements.
* Replace repeated Prelude elaboration with the checked generated artifact;
  the trivial cold-compile gate now completes in under one second.
* Make Delve's JSON parsers structurally total and restore its native package
  build and test gate.

## 0.1.0.0 -- 2026-06-21

* Initial compiler release.
