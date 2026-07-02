# Pending runtime reference imports

These fixtures are converted from runtime tests in `/Users/wabbit/ws/refs` and selected
external runtime suites, but they are not executed by
`tests/runtime-import/run-runtime-imports.sh` yet.

Keep this directory separate from the passing import lane. Moving any file out of
`pending/` should come with the implementation work that makes the fixture executable
under both the interpreter and native parity harness.

Each pending fixture must be classified before it becomes an executable test:

- `runtime-pending`: already required by `docs/Spec.md`, but missing or stubbed.
- `library-proposal`: useful standard-library surface not currently specified.
- `host-bridge-proposal`: host boundary behavior that needs a bridge/test-shim contract.
- `extension-proposal`: useful diagnostics or framework behavior outside current portable semantics.

Current runtime-pending fixtures:

- `handler-abandon-cleanup.kp`: abortive handler clauses must run captured cleanup.
- `race-loser-interrupt-tag.kp`: race loser interruption must carry `RaceLost`.
- `runtime-debug-fiber-status.kp`: §32.2.11 fiber snapshots need a portable test API.
- `stm-or-else.kp`: source-level `<|>`/`orElse` for transactional retry choice.
- `supervisor-otp-restart-policies.kp`: §29.2 OTP-style supervisor restart policy behavior.

Current library-proposal fixtures:

- `queue-fifo.kp` and `queue-bounded-backpressure.kp`: FIFO queue operations and bounded backpressure.
- `schedule-test-clock.kp`: repeat/retry schedules plus deterministic time.

Current host-bridge-proposal fixtures:

- `blocking-does-not-starve.kp`: source-level `blocking` / native `rt-blocking`
  are implemented, but this imported fixture still needs a portable
  `std.testing.blocking` host-blocking shim.
- `blocking-cancellable-foreign-call.kp`: cancellable foreign blocking operations.
- `callback-future-cancel.kp`: cancellation and backpressure at async host boundaries.

Current extension-proposal fixtures:

- `supervisor-hooks.kp`: hook-style start/end observation around forked fibers.
