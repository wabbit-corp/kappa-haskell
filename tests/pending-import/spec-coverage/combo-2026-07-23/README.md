# Combo coverage — 2026-07-23

Feature-combination tests from the 2026-07-23 combo campaign (several lanes
contributed fixtures). Each file states the SPEC-CORRECT expectation; a
`-- STATUS(a0497523): ...` trailer records what the compiler actually does.

The fixtures have since been distributed into the parent directory's semantic
area folders. This report and `FINDINGS.md` remain here as campaign provenance;
paths in the findings report point to the fixtures' current locations.

## Lane: borrows/places x record patch x inout

Tests for §12.3–§12.4 (borrows, disjoint path borrowing, stable places),
§13.2.5 (record update/patch), and §18.9 (`inout` / `~`).

Highlights (see each header for the spec argument):

- `inout-marker-on-borrowed-binder-linear.kp` and
  `inout-marker-through-borrowed-alias-projection.kp` pin a LINEARITY HOLE:
  `~` accepts a borrowed binder (or a path projected from one), treats it as a
  fresh root, writes back to the alias only, and lets a quantity-1 place be
  consumed twice.
- `projection-read-of-consumed-path.kp` and
  `projector-descriptor-read-of-consumed-path.kp` pin that projector
  elimination ignores consumed-path state that the same direct projection
  rejects.
- `record-patch-unrestricted-root-under-live-borrow.kp` pins that a record
  patch of an unrestricted scrutinee is treated as a consuming use, rejecting
  patches whose normative elaboration (a full record literal of projections)
  is accepted verbatim.
- `pattern-borrow-decomposed-pathwise-inout.kp` pins §12.4's pathwise
  decomposition of `let & (field = b) = r` borrows.

The remaining fixtures pin correct-and-previously-untested combo behavior
(borrow live across inout write-back, branch-union `~` footprints,
dependency-closure disjointness, `~` on a consumed place, patch through a
borrowed whole-record alias).
