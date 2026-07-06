# Runtime Import Tests

This area stages runtime-semantics tests converted from the Scala reference
trees under `/Users/wabbit/ws/refs`.

Passing portable cases live in `tests/conformance/runtime-import`, so the Cabal
conformance suite picks up their interpreter/harness assertions. The
runtime-import runner adds the native parity check that conformance alone does
not provide:

```sh
cabal run -v0 kappa -- test tests/conformance/runtime-import
bash tests/runtime-import/run-runtime-imports.sh
```

`tests/runtime-import/pending/` contains converted reference tests that are
intentionally not executed yet. Those files are classified as `runtime-pending`,
`library-proposal`,
`host-bridge-proposal`, or `extension-proposal` in
`tests/runtime-import/pending/README.md` before they can move into the passing
import lane.

## First imported batch

The initial batch targets portable semantics already specified in
`docs/Spec.md` §18.1 and now lives in `tests/conformance/runtime-import`:

- `promise-multiple-waiters.kp`: ZIO `PromiseSpec` waiter stack safety and Cats
  Effect `DeferredSuite` get-blocks-until-set behavior.
- `promise-await-interruptible.kp`: Cats Effect `DeferredSuite` canceled get
  before forcing, mapped to Kappa's interruptible `awaitPromise`.
- `race-loser-finalizer.kp`: Cats Effect resource race loser cleanup and ZIO
  interrupt-waits-for-finalizer semantics.
- `timeout-finalizer.kp`: Cats Effect timeout finalizer behavior.
- `using-lifo-release.kp`: ZIO scope finalizer ordering and Cats Effect
  resource reverse-release behavior.
- `stm-retry-wakeup.kp`: ZIO STM retry behavior, using Kappa's current `check`
  and `atomically` surface.
- `promise-complete-once.kp`: ZIO `PromiseSpec` and Cats Effect `DeferredSuite`
  first-completion-wins behavior.
- `fiber-multiple-awaiters.kp`: Cats Effect `IOSuite` multiple awaiters observe
  the same fiber terminal exit.

## Pending imported batch

These cases are imported but intentionally parked under `pending/`:

- `pending/blocking-does-not-starve.kp`: Cats Effect blocking starvation
  behavior, blocked on a portable `std.testing.blocking` host-blocking shim.
  Source-level `blocking` and native `rt-blocking` are covered by the native
  runtime/backend gates.
- `pending/blocking-cancellable-foreign-call.kp`: Cats Effect interruptible
  blocking behavior, blocked on an explicit cancellable foreign-call contract.
- `pending/callback-future-cancel.kp`: Cats Effect Future/callback cancellation
  and cancellation backpressure, blocked on a standard async host bridge.
- `pending/handler-abandon-cleanup.kp`: Kappa handler abandonment cleanup,
  blocked on the native runtime gap tracked in `ROADMAP.md`.
- `pending/race-loser-interrupt-tag.kp`: Kappa `race` loser interrupt metadata,
  blocked on an interpreter/native cause-tag divergence.
- `pending/queue-fifo.kp` and `pending/queue-bounded-backpressure.kp`: ZIO/Cats
  Queue ordering and bounded backpressure, blocked on a standard queue surface.
- `pending/runtime-debug-fiber-status.kp`: runtime debug/fiber-status
  observability, blocked on portable runtime diagnostics APIs.
- `pending/schedule-test-clock.kp`: ZIO Schedule/test-clock semantics, blocked
  on standard schedule combinators and deterministic time.
- `pending/stm-or-else.kp`: ZIO STM `orElse` rollback/choice behavior, blocked
  on source-level `Alternative STM`.
- `pending/supervisor-otp-restart-policies.kp`: Erlang/OTP supervisor restart
  policy behavior, blocked on real `std.supervisor` semantics.
- `pending/supervisor-hooks.kp`: ZIO supervisor hook behavior, blocked on an
  explicit hook/diagnostics decision for Kappa.
