# Example package QTT regression note

Delve and Voxelcraft previously failed before backend selection with many `E_QTT_LINEAR_OVERUSE`, `E_QTT_LINEAR_DROP`, and related mutable-current-value diagnostics on unannotated local values.

The diagnostics do not match the draft spec. `docs/Spec.md` states that omitted quantities default to `omega` in section 12.2, and section 9.3 applies ordinary binder quantity defaults to local `let` and `let ... <-` bind patterns unless a binder prefix is written. For example, `examples/packages/delve/src/delve/content.kp` binds `crafts` with plain `let crafts = ...`, and `examples/packages/voxelcraft/src/voxelcraft/game_loop.game.kp` binds `faces` with plain `let faces <- ...`. Treating those binders as linear is a compiler regression rather than a legitimate source issue.

The Voxelcraft `x <- action` failures are different: section 18.2 reserves bare `x <- expr` for mutable-variable assignment, while monadic bind must be written `let x <- expr`.

Status: the QTT/default-omega regression is now covered by focused conformance tests and both packages advance past usage checking. The remaining package-build failures are native-backend Perceus RC validation misses, not QTT binder-default diagnostics.
