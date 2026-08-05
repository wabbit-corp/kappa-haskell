# Ready-to-insert specification changes for issues #32 and #52

This package is based on `Spec(107).md` and `KNOWN_SPEC_ISSUES(4).md`.

The canonical edit is `issues-32-52.patch`, which applies to repository paths:

```text
docs/Spec.md
docs/KNOWN_SPEC_ISSUES.md
tests/conformance/issues/issue-32-mask-restore/*.kp
tests/conformance/issues/issue-52-quantity-borrow/*.kp
```

Apply it with:

```text
git apply issues-32-52.patch
```

## Issue #52: interval quantity and access mode are orthogonal

The patch removes the category error everywhere it leaked rather than changing only one table.

### §12.2 ambient demand

Demand scaling uses the selected binder's interval quantity only. Owned-versus-borrowed access is checked separately.
`&` never participates in quantity arithmetic, comparison, or `QuantitySatisfies`.

### §12.2.5 droppability

A binder or field is checked as:

```text
(interval quantity, access mode, owned structure/path state)
```

The closed quantity table is:

```text
droppable interval quantities:      0, <=1, ω
not droppable interval quantities:  1, >=1
```

For owned access, abandoning the value must not lose a non-droppable owned component. For borrowed access, abandoning the
binding abandons only the shared view; it does not discard the referent and does not require the referent type to be
droppable.

### §12.2.6 duplicability

The closed quantity table is:

```text
duplicable interval quantities:      0, >=1, ω
not duplicable interval quantities:  1, <=1
```

For owned access, duplication requires the selected value/component/path to be duplicable. For borrowed access,
duplication copies only the shared view, not ownership of the referent; the region and selected path must remain valid,
but the referent itself need not be `Shareable`.

Consequently:

```text
(& x : A)       = (ω & x : A)    -- droppable and duplicable view
(>=1 & x : A)                    -- not droppable; duplicable view
(1 & x : A)                      -- not droppable; not duplicable
(<=1 & x : A)                    -- droppable; not duplicable
```

### Cross-section consistency

The patch applies the same decomposition to:

* borrow-root eligibility;
* lambda capture and ambient-demand prose;
* implicit borrowed binders;
* comprehension/query quantitative row entries;
* row droppability and row duplicability; and
* Appendix T's portable conformance matrix.

## Issue #32: compositional interruption masking

The patch replaces the vague “restore re-enables interruption” rule with a per-fiber state machine.

```text
base state + ordered restorable frame stack
Interruptible < Masked < Uninterruptible
effective state = maximum(base state, active frames)
```

### Operations

* `mask f` pushes a fresh ordinary frame and supplies a restore capability for that frame.
* `uninterruptibleMask f` pushes a fresh strong frame and supplies a restore capability for that frame.
* `uninterruptible body` is the no-restore strong form.
* A restore capability can suspend only its own topmost frame, only on its originating fiber.
* Wrong-order, repeated nested, inactive, and cross-fiber restore applications are observational no-ops.
* Nested restoration removes frames in runtime stack order.
* Frames are reinstated on normal completion, typed failure, interruption, and defect.

### Delivery and handoff

* Ordinary suspension points, waits, `cede`, safe points, and potentially suspending atomics deliver only in
  `Interruptible`.
* `Masked` suppresses those ordinary points but admits the explicit single-point checkpoint `poll`.
* `Uninterruptible` suppresses ordinary points and `poll`.
* Exposing `Interruptible` through restoration may deliver a pending request immediately before the restored action.
* There is no interruption point after a successfully completed restored action and before its frame is reinstated.

### Fibers, finalizers, and foreign calls

* A child inherits the parent's effective state as a non-restorable base state, not the parent's frame identities.
* Restoring around `fork` lets the child inherit the restored state.
* A non-waiting interruption operation records the request before returning.
* Finalizers run under a fresh ordinary mask while preserving any stronger outer state.
* A `blocking-cancellable` foreign call attempts its safe cancellation mechanism when interruption is deliverable,
  unless the call already completed, and never more than once; masked requests do not invoke host cancellation.

The foreign-call wording also closes known issue #76 as a consequence of making the mask-state interaction precise.

## Tests

The patch creates 29 standalone Appendix T files:

* 13 quantity/borrow files for issue #52;
* 16 interruption/masking files for issue #32.

The zero-width successful-restoration handoff is also a mandatory Appendix T conformance item in §T.10. A portable
source program cannot deterministically schedule a request inside that internal handoff, so a runtime may verify that
part with its conformance instrumentation rather than a timing-based black-box test.
