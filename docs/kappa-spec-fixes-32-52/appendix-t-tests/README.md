# Appendix T tests

Each `.kp` file is a standalone single-file Appendix T suite. They must be invoked individually rather than compiling a
whole issue directory as one directory suite, since each file deliberately uses module `main` and its own harness
configuration.

## Issue #52

The accepted cases prove that unrestricted or relevant borrowed views may be demanded repeatedly even when the referent
contains a quantity-`1` field, and that unrestricted or affine borrowed views may be discarded without discarding the
referent. Rejected cases prove that borrowed access does not loosen linear, affine, or positive-lower-bound interval
budgets. Query cases exercise repeated row evaluation, and a classifier test pins that `&` is never a `Quantity` value.

The matrix also includes accepted one-use cases for linear and affine borrowed binders, preventing an implementation
from "fixing" duplication by rejecting those binder forms wholesale.

Files: 13.

## Issue #32

The run suites coordinate fibers with one-shot promises rather than sleeps or timing assumptions. `interruptFork` is
sequenced before release of the child's gate; the patched specification guarantees that the request is registered before
that operation returns. Each child reports `True` only if it passes the tested interruption point; an `ensuring` finalizer
reports `False` if interruption wins first.

Cases cover:

* restoration from an interruptible base;
* stale/inactive restoration under a newer mask;
* ordinary and strong outer states;
* nested frame order;
* wrong-order and repeated nested restoration;
* `poll` under one and several ordinary masks;
* `poll` under strong masking;
* `uninterruptibleMask`, including restoration to an outer ordinary mask;
* inherited child state;
* restoring around `fork`; and
* isolated cross-fiber restoration; and
* retention and later delivery of a request suppressed by `Uninterruptible`.

Files: 16.

The successful-action-to-remasking handoff has no source-visible point at which a portable test can deterministically
inject interruption. It is therefore pinned as an explicit §T.10 conformance obligation and may be checked through
runtime conformance instrumentation; no fixture fakes this with scheduler timing.
