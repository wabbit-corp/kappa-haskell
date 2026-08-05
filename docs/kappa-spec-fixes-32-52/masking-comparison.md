# Interruption-mask design comparison and Kappa decision

This note records the external models considered for issue #32 and the reasons for Kappa's selected semantics.
It is explanatory; the normative rules are in the specification patch.

## Evaluation criteria

The design was judged against six properties:

1. **Caller authority.** A library helper must not be able to weaken a stronger mask imposed by its caller unless the
   caller explicitly delegates that authority.
2. **Local reasoning under nesting.** Each restoration capability should have a precise dynamic scope and predictable
   behavior when masks are nested.
3. **Prompt cancellation without hidden punctures.** Ordinary critical sections should remain responsive where the
   programmer explicitly permits interruption, without making arbitrary blocking operations secret cancellation points.
4. **Atomic result handoff.** A successfully completed restored action must hand its value back to masked continuation
   without a cancellation window that can discard that value.
5. **Fiber isolation.** Restoration authority must not become a cross-fiber capability merely because the value is
   captured by a closure.
6. **Implementability.** The contract must be realizable on callback, coroutine, green-thread, native-thread, and explicit
   run-loop backends without relying on host-specific asynchronous exception behavior.

## GHC / `base`

GHC exposes three states: `Unmasked`, `MaskedInterruptible`, and `MaskedUninterruptible`. The `restore` function supplied
by `mask` restores the masking state that prevailed outside that invocation rather than blindly unmasking. This gives a
strong compositional guarantee: a library entered under an existing mask cannot use its own `restore` to weaken the
caller's state.

GHC's ordinary mask remains interruptible at a host-defined class of blocking operations and at explicit
`allowInterrupt`; `uninterruptibleMask` suppresses those points. Threads created by ordinary `forkIO` inherit the
parent's current masking state.

Kappa adopts:

* restoration to the state outside the current mask rather than unconditional unmasking;
* the ordinary-versus-strong distinction;
* inherited effective state for children; and
* the warning that strong uninterruptible regions can deadlock.

Kappa does **not** adopt GHC's implicit class of interruptible blocking operations. A Kappa ordinary mask admits
interruption only at explicit `poll` or after correctly scoped restoration. This avoids making the cancellation behavior
of a critical section depend on whether a deeply called library routine happens to use a host operation classified as
interruptible.

GHC's public contract does not specify Cats Effect's identity-bearing, wrong-order, repeated-nesting, and cross-fiber
laws for restoration functions. Kappa takes those stricter laws from Cats Effect.

## Cats Effect 3 (`MonadCancel`)

Cats Effect gives each `uncancelable` region an identity-bearing `Poll`. Masks stack. To remove several masks, the
corresponding polls must be composed in stack order. Polling in the wrong order, nesting the same poll twice, or applying
a poll on another fiber is a no-op.

Cats Effect also specifies the subtle but essential handoff rule: cancellation may be observed before and within the
polled action, but there is no cancellation boundary after the successful end of that action and before the following
masked continuation. Without this rule, a resource acquisition or other successful effect could complete and then lose
its result before masked code can install the matching cleanup obligation.

Kappa adopts:

* semantic identity for every restore capability;
* topmost-frame-only restoration;
* wrong-order, repeated nested, inactive, and cross-fiber no-op behavior;
* explicit stack-order composition; and
* the no-post-action handoff boundary.

Kappa differs by retaining two mask strengths and by exposing a source-level single-point `poll` in ordinary `Masked`.

## ZIO 2

ZIO exposes `uninterruptible` and `uninterruptibleMask`, the latter supplying a restoration function. Child fibers inherit
interruptibility status. ZIO also exposes a general `interruptible` operator that can make a region interruptible even
inside an enclosing uninterruptible region; its own API documentation warns that this operator “punches holes” and
recommends `uninterruptibleMask` for ordinary structured use.

Kappa adopts `uninterruptibleMask` and child-state inheritance, but rejects the unrestricted hole-punching operator.
Kappa restoration can suspend only the frame that created it. The global `poll` is a single checkpoint rather than a
region-level state override, and it is inert under `Uninterruptible`.

## Monix `Task`

Monix offers `Task.uncancelable`, which makes cancellation ineffective for the wrapped task, and `Task.cancelBoundary`,
an explicit run-loop cancellation check commonly used in long loops. It does not expose the same scoped restoration token
and nested-mask laws as Cats Effect, GHC, or ZIO.

Kappa retains the useful explicit-checkpoint idea but combines it with identity-bearing restoration frames so that
acquire/use/release protocols can restore precisely one enclosing state rather than choosing only between globally
cancelable and globally uncancelable execution.

## Selected Kappa model

Each fiber has:

```text
non-restorable base state
ordered stack of identity-bearing restorable frames

Interruptible < Masked < Uninterruptible
effective state = maximum(base state, active frames)
```

The operations are:

* `mask`: push an ordinary `Masked` frame and supply its restore capability;
* `uninterruptibleMask`: push an `Uninterruptible` frame and supply its restore capability;
* `uninterruptible`: the no-restore strong form;
* `restore action`: suspend exactly the capability's own topmost frame on its originating fiber;
* `poll`: one explicit delivery checkpoint in `Masked`, inert in `Uninterruptible`.

The resulting properties are:

* older caller frames and inherited base state cannot be weakened accidentally;
* masks compose predictably under higher-order library calls;
* cross-fiber capture of a restore value does not transfer authority;
* a parent may deliberately restore around `fork` so the child inherits the restored state;
* ordinary waits and safe points do not secretly puncture `Masked`;
* strong masks cannot be punctured by `poll`;
* foreign-call cancellation obeys the same effective-state rules; and
* successful restored actions hand their result back to masked code atomically with respect to interruption delivery.

## Primary references consulted

* GHC `Control.Exception`, asynchronous exception control and interruptible operations:
  <https://hackage.haskell.org/package/base/docs/Control-Exception.html>
* Cats Effect 3 `MonadCancel`, masking, `Poll`, nesting, fiber locality, and cancellation boundaries:
  <https://typelevel.org/cats-effect/api/3.x/cats/effect/kernel/MonadCancel.html>
* ZIO interruption model and `uninterruptibleMask`:
  <https://zio.dev/reference/interruption/>
* ZIO API documentation for `interruptible` and its hole-punching warning:
  <https://zio.dev/api/zio/zio>
* Monix `Task.uncancelable` and `Task.cancelBoundary`:
  <https://monix.io/api/current/monix/eval/Task.html>
  <https://monix.io/api/current/monix/eval/Task$.html>
