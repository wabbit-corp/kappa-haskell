# Runtime Import Surface Proposals

This note records imported runtime-test surfaces that are useful, but not yet
portable Kappa semantics. Fixtures under `tests/runtime-import/pending/` should
link to one of these classifications before moving into the executable lane.

## Fixture Classes

- `runtime-pending`: already required by `docs/Spec.md`; the implementation or
  source surface is missing.
- `library-proposal`: a candidate standard library module inspired by reference
  runtimes, not currently required by the spec.
- `host-bridge-proposal`: a host boundary or FFI behavior that needs explicit
  bridge rules before tests can be portable.
- `extension-proposal`: useful diagnostics/framework behavior that should stay
  outside portable semantics unless explicitly adopted.

## Candidate Library Modules

`std.queue` should define FIFO bounded and unbounded queues with `offer`, `take`,
`tryOffer`, `tryTake`, observable `size`, and cancellation atomicity: canceled
takes must not consume an element, canceled offers must not enqueue phantom
values, and back-pressured offers must complete after capacity is released.
ZIO `QueueSpec` and Cats Effect `QueueSuite` are the source pools.

`std.schedule` and `std.test_clock` should be decided together. Imported tests
need repeat/retry policies (`recurs`, `once`), deterministic time advancement,
partial ticks that do not over-advance, and deadlock/next-interval observation.
ZIO `ScheduleSpec` and Cats Effect `TestControlSuite` are the source pools.

`std.semaphore` is a separate candidate from queue. Cats Effect
`SemaphoreSuite` contributes cancellation-no-permit-leak and `acquireN`
rollback tests. This should not be hidden under `std.queue`.

## Host Bridges

`std.future` or an equivalent callback bridge needs a cancellation contract:
interrupting the Kappa fiber must run the registered host canceler when the
bridge is declared cancelable, and interrupt completion must backpressure on
that canceler when the bridge contract says so.

Blocking foreign calls need two distinct contracts. `blocking` itself only
prevents scheduler monopolization; it does not make arbitrary work cancellable.
Cancellable blocking needs an explicit foreign-call classification or test shim.

## Diagnostics And Extensions

`docs/Spec.md` requires a runtime observability facility, but leaves API shape
implementation-defined. To make imported runtime-debug tests portable, define a
small `std.runtime_diagnostics` source API for fiber identity, parent/scope,
status, wait reason, mask state, interruption-pending state, label, retained
exit, and scheduler counts.

Hook-style supervisors (`onStart`/`onEnd`) are not Kappa `std.supervisor`
semantics. Keep those as diagnostics/extension tests unless the spec adopts an
explicit hook module. Normative supervisor imports should target §29.2
OTP-style restart policies, strategies, intensity windows, shutdown, and cause
composition.

Erlang/OTP mailbox, selective receive, process registry, and timer-handle tests
should not be imported directly. They require explicit proposals such as
`std.mailbox`, `std.process_registry`, or `std.timer`; otherwise prefer Kappa
queues, supervisors, timers, and runtime diagnostics.
