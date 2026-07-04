# Borrowed resources do not compose with the `IO` monad across a function boundary

*Discovered 2026-06-24 while trying to make Delve's terminal lifetime
statically safe (`examples/packages/delve/src/delve/engine.game.kp`).*

## TL;DR

A long-lived resource that is **borrowed** (`& x`) cannot be threaded
through a **recursive, `IO`-returning helper function** in today's
implementation. The borrow is captured by the continuation closures that
a `do`-block desugars into, and those closures *are* the function's
return value, so the borrow escapes its scope (`E_QTT_BORROW_ESCAPE`,
§12.3.2). The principled fix the type system offers — annotate the
result with `captures (s)` so the region becomes part of the type — does
**not** work for `IO`, because the prelude `ioBind` is monomorphic in
its capture set: every `do`-step routes through it, and it can neither
accept a continuation that captures a region nor produce a
capture-annotated `IO`. There is no capture-polymorphic monadic bind.

The net consequence: for a *singleton, long-lived resource driven by a
recursive functional `IO` loop* (a TUI terminal, here), the only clean
options are a value-level bracket (`finallyIO` / a leaf `using`) or an
imperative `while`/`var` loop kept inside the acquiring scope. The
"recursive + borrowed + statically owned" shape is **not expressible**.

---

## 1. The setup

Delve's terminal facade (`src/delve/terminal.game.kp`) is the textbook
linear-resource interface:

```kp
expect data Terminal : Type

expect term open    : IO GameError Terminal
expect term close   : (1 terminal : Terminal) -> IO GameError Unit          -- consumes once
expect term readKey : (& terminal : Terminal) -> IO GameError Key           -- borrows
expect term write   : (& terminal : Terminal) -> String -> IO GameError Unit
expect term size    : (& terminal : Terminal) -> IO GameError Size

instance Releasable (IO GameError) Terminal =
    let release terminal = close terminal
```

`main` opens the terminal, runs a recursive driver loop, and closes it:

```kp
runLoop : term.Terminal -> Size -> Int -> GameState -> IO GameError Unit
let runLoop terminal mapSize lastMusic game =
    do
        term.write terminal (render.renderGame game)
        match game.mode
        case Quit -> pure ()
        case _    -> do
            ...
            key <- term.readKey terminal
            ...
            runLoop terminal mapSize musicAfterInput game2     -- recurse

main : IO GameError Unit
let main =
    do
        terminal <- term.open
        let cleanup = do audio.shutdown; term.close terminal
        let body    = do ...; runLoop terminal mapSize musicNone game
        finallyIO body cleanup
```

This compiles and is **runtime-safe**: `finallyIO` runs `cleanup` on
every exit path (normal *and* error), so the terminal is always restored
out of raw mode. But it is **not statically linear**: `terminal <-
term.open` binds `terminal` at the unrestricted quantity ω, so the
`(1 …)` on `close` is inert here — the checker would equally accept a
`main` that never closes (leak) or closes twice (use-after-close). We
wanted to close that gap.

## 2. The QTT model, in brief

- `(1 x : T)` — **linear**: must be consumed exactly once. No leak
  (must-use), no double-free (can't-use-twice).
- `(& x : T)` — **borrow**: use many times without consuming, while the
  *owner* keeps the release obligation. This is what lets `readKey` /
  `write` / `size` all take `& terminal` while `close` is the single
  consuming use.
- **Skolem-escape rule (§12.3.2 / Spec.md:11631).** "A value, including a
  closure, whose region environment mentions a rigid `rho` may not escape
  the lexical scope that introduced `rho`." Escape points include
  *"return from the function … that introduced the borrow"* and *"storing
  the value inside another … closure that would outlive `rho`"*. The
  check is **local / modular** — "no whole-program analysis is required,
  because `rho` is rigid and its scope is statically known"
  (Spec.md:11645).
- `using pat <- acquire` (§12.3, Spec.md:11661) is a **primitive**
  protected-scope split: a hidden exit obligation (`Releasable.release`
  on unwind) plus borrowed bindings exposed through `pat`. "Any closure
  created inside that scope that captures names from `pat` inherits
  `rho` and therefore cannot escape the `using` block." It is *not*
  modeled as ordinary closure capture — this is what makes `using` sound
  without explicit lifetime syntax.

## 3. Attempt 1 — `using` + a borrowed `runLoop`

Goal: have `main` own the terminal via `using` (release on all paths via
the `Releasable` instance) and pass a borrow to `runLoop`:

```kp
runLoop : (& terminal : term.Terminal) -> Size -> Int -> GameState -> IO GameError Unit
...
main =
    do
        using terminal <- term.open
        audio.init
        defer audio.shutdown
        ...
        runLoop terminal mapSize musicNone game
```

Build result:

```
engine.game.kp:1614:9: error[E_QTT_BORROW_ESCAPE] (kappa.borrow.escape):
  a closure capturing a borrowed binding escapes through the result (§12.3.2)
  related: borrow-start: borrow-capturing closure formed here
  related: borrow-escape-site: escapes through the result here
```

### Why

`IO a` is a **deferred** value — a closure. A `do`-block desugars each
step into a continuation lambda handed to `ioBind`
(`Check.elabMonadDo`): `x <- act; rest` becomes
`ioBind act (\x -> rest)`. In `runLoop`, the continuation
`\_ -> match game.mode … runLoop terminal …` **closes over `terminal`**,
and that closure flows out as `runLoop`'s return value.

The escape is detected at `runLoop`'s **definition**, checked in
isolation (`Usage.hs`, `walkLetDef` ~L770–793):

```haskell
let resCaptures = maybe False capturesAnnotated resultTy
unless resCaptures $
  forM_ taint $ \sp ->
    emitRel "E_QTT_BORROW_ESCAPE" "kappa.borrow.escape" sp
      [ related RoleBorrowStart sp "borrow-capturing closure formed here"
      , related RoleBorrowEscapeSite (exprSpan (ldBody ld)) "escapes through the result here" ]
      "a closure capturing a borrowed binding escapes through the result (§12.3.2)"
```

The parameter `terminal` has a rigid region `rho`. The declared result
type `IO GameError Unit` **does not mention `rho`** — it is a contract
that the value carries no live borrows — but the returned IO thunk
secretly does. Modular checking only has the type, and the type permits
a caller to stash the action and run it after the borrow's scope ends
(use-after-close). So it must reject.

**This is exactly Rust.** A function returning something that borrows a
parameter must name the lifetime in the return type
(`fn f<'a>(t: &'a T) -> impl FnOnce() + 'a`). `IO a` here is the captured
closure; the `+ 'a` is mandatory. Kappa's spelling of "+ 'a on the
result" is `captures (rho)`.

Primitives (`term.write : (& terminal) -> IO …`) are exempt: they are
`expect` declarations with **no Kappa body**, so there is no
continuation closure to analyze. The escape only arises from
*user-defined* `do`-blocks.

## 4. Attempt 2 — the `captures (s)` annotation

The spec sanctions this. §12.3.1 (Spec.md:11703–11704):

> The annotation may be written on **any value type, not only on function
> types**. This is necessary because a non-function value may hide
> closures or other region-carrying values inside records, packages, or
> abstract data.

So `IO` (an abstract type that hides region-carrying closures) is fair
game in principle. The annotation makes the boundary honest:

```kp
runLoop : forall (s : Region). (&[s] terminal : term.Terminal)
            -> Size -> Int -> GameState -> (IO GameError Unit captures (s))
```

It does **not** work, for two distinct reasons.

### 4a. Parser precedence discrepancy (workaroundable)

Written without inner parens —
`… -> (IO GameError Unit captures (s))` — the annotation attached to the
**last type argument** `Unit`, not to the whole application:

```
engine.game.kp:1614:9: error[E_TYPE_EQUALITY_MISMATCH]:
  actual:   IO GameError Unit
  expected: IO GameError (__captures Unit @4)
```

This contradicts §12.3.1's stated precedence (Spec.md:11713–11714):
*"`captures (...)` binds looser than type application and tighter than
`->`. Therefore `Boxed a captures (s)` means `(Boxed a) captures (s)`."*
By that rule `IO GameError Unit captures (s)` should mean
`(IO GameError Unit) captures (s)`; the implementation parsed it as
`IO GameError ((Unit) captures (s))` — i.e. *tighter* than application.
**Likely an implementation/spec gap worth filing.** Workaround: write the
inner parentheses explicitly, `((IO GameError Unit) captures (s))`.

### 4b. The decisive wall: `ioBind` is monomorphic in captures

With explicit parens the annotation parses correctly and the
borrow-escape check is *suppressed* (`capturesAnnotated` in `Usage.hs`
L832 matches the `ECaptures` node) — but the **type checker** then
rejects:

```
engine.game.kp:1624:17: error[E_TYPE_EQUALITY_MISMATCH]:   -- the recursive call
  actual:   __captures (IO GameError Unit) @9
  expected: IO GameError Unit
engine.game.kp:1614:9: error[E_TYPE_EQUALITY_MISMATCH]:    -- the do-block body
  actual:   IO GameError Unit
  expected: IO GameError (__captures (IO GameError Unit) @4)
engine.game.kp:1637:9: error[E_TYPE_EQUALITY_MISMATCH]:    -- main's using body
  actual:   __captures (IO GameError Unit) _
  expected: IO GameError Unit
```

The cause is the prelude bind primitive (`Prelude.hs:521`):

```haskell
prim "ioBind"
  (tyV (piI Q0 "e" tType (piI Q0 "a" tType (piI Q0 "b" tType
    (io (CVar 2) (CVar 1) ~> (CVar 2 ~> io (CVar 4) (CVar 2)) ~> io (CVar 4) (CVar 2))))))
```

and the `Monad` trait method it backs (`Prelude.hs:800`):

```
(>>=) : forall (a : Type) (b : Type). m a -> (a -> m b) -> m b
```

`ioBind`'s continuation parameter is `(a -> IO e b)` and its result is
`IO e b` — both **plain, region-free** `IO` (empty capture set). Every
`do`-step desugars through `ioBind`. So:

- the recursive call now has type `__captures (IO …) s`, but the
  enclosing `ioBind` continuation must return plain `IO …` → mismatch
  (L1624);
- conversely `ioBind` *produces* plain `IO …`, but `runLoop`'s declared
  result is `__captures (IO …) s` → mismatch (L1614);
- and `main`'s `using` body inherits the same conflict (L1637).

`__captures (IO e b) s` is a **distinct type** from `IO e b`; capture
subsumption is not definitional equality
(`tests/conformance/qtt/captures-identity.kp`:
*"the capture set is part of type identity; capture subsumption is NOT
definitional equality"*). There is no capture-polymorphic bind to thread
a non-empty region set through, and no coercion. The annotation is
correct in spirit but has nowhere to flow.

## 5. Root cause

`captures (s)` lives on a value's type and records the regions it hides.
The region machinery can carry it across an **arrow** (a first-class
closure literal carries its own capture set). But the `IO` monad
deliberately abstracts its underlying `World -> (a, World)` arrow behind
an **opaque** type, and `ioBind` / the `Monad` trait are written **once,
region-free**. That same abstraction — the thing that makes `IO` clean —
severs it from the capture system: there is no way to express "this `IO`
action borrows region `s`" and have `do`-notation construct it, because
`do` is sugar over a bind that is monomorphic in captures.

Contrast Rust, where the analogy *does* close: an `async fn` / closure
capturing `&'a` produces `impl Future + 'a`, the lifetime is part of the
type, and the combinators (`and_then`, `.await`) are lifetime-
polymorphic. Kappa has the type former (`captures`) but not the
lifetime-polymorphic monadic bind.

## 6. What works instead

| Shape | Compiles | Cleanup on crash | Static leak / double-close prevention | Fits Delve's style |
|---|:--:|:--:|:--:|:--:|
| **ω + `finallyIO`** (current) | ✓ | ✓ | ✗ | ✓ |
| Imperative `while`/`var` under `using` (same scope) | ✓ * | ✓ | ✓ | ✗ (no `var`/`while` elsewhere in Delve) |
| Own + thread `(1 terminal)`, close at each exit | ✓ | ✗ (manual; leaks on error) | ✓ | ✓ |

\* The imperative-loop option is the **only place the repo borrows a
resource across a loop**, and it does so by keeping the loop **inside the
acquiring scope** so the borrow never crosses a function-definition
boundary (no fresh rigid `rho` to erase from a result type). See
`input/kappa-http-stack/src/acme/http/server.kp` L14–57: `serve` does
`using listener <- net.bind …` then `while True do … net.accept listener
…` directly in its own body, and hands `handleConnection` an **owned
`(1 conn)`**, never a borrow. (Not separately verified for Delve — but
this is the supported pattern.)

For a **singleton** handle opened once in `main`, the static guarantees
add little (there is exactly one acquire site, visible at a glance) while
the runtime bracket delivers the property that actually matters for a TUI
— restore the terminal on *every* exit including a crash. So the
`finallyIO` form is the correct fit, not a consolation prize. QTT's
borrow/linear machinery earns its keep on **first-class values** and on
**fleets of short-lived resources in straight-line code** (HTTP
per-connection sockets), not on a singleton threaded through opaque `IO`.

## 7. Possible language-level fixes

If this gap is ever worth closing:

1. **Capture-polymorphic `ioBind`** (and `Functor`/`Applicative`/`Monad`
   for `IO`): abstract the bind over a region/capture row so a
   continuation capturing `&[s]` yields an `IO … captures (s)` and the
   set propagates. This is the direct analog of Rust's lifetime-
   polymorphic combinators. Touches `Prelude.hs` (`ioBind`, the `Monad`
   trait at L799–800) and how `Check.elabMonadDo` types the desugared
   binds.
2. **Region-threading `do`-scope**: make the `do` elaborator treat a
   borrowed-resource bind the way `using` is already treated — a
   primitive protected scope that carries `rho` — rather than plain
   `ioBind` capture, so the region is confined structurally instead of
   needing to appear in the bind's type.

Either is a type-system change, not something to encode in user code.

Also worth filing independently: the **§12.3.1 precedence discrepancy**
in §4a (the parser attaches `captures` tighter than type application,
contrary to the spec). Candidate for `docs/notes/KNOWN_SPEC_ISSUES.md`.

## 8. Reproduction

```sh
KAPPA=dist-newstyle/build/aarch64-osx/ghc-9.14.1/kappa-haskell-0.1.0.0/x/kappa/build/kappa/kappa
CPATH=/opt/homebrew/include LIBRARY_PATH=/opt/homebrew/lib \
  "$KAPPA" build --manifest examples/packages/delve --target delve-macos-arm64
```

Edit `engine.game.kp` `runLoop` / `main` per §3 and §4 above to
reproduce each error. The committed code uses the ω + `finallyIO` form
(§1) and builds clean.

## 9. References

- **Spec** `docs/Spec.md`: §12.3 escape rule (L11631–11652); `using`
  interaction (L11661–11674); §12.3.1 capture-annotated types
  (L11677–11716, esp. "any value type" L11703–11704, precedence
  L11713–11716).
- **Checker** `src/Kappa/Usage.hs`: `E_QTT_BORROW_ESCAPE` emission and
  `capturesAnnotated` suppression (~L770–835).
- **Prelude** `src/Kappa/Prelude.hs`: `ioBind` prim (L521–523), `Monad`
  trait (L799–800), `Releasable` trait (L815–816), `finallyIO` (L518).
- **Desugaring** `src/Kappa/Check.hs`: `elabMonadDo` (do → `ioBind`),
  `DoUsing` elaboration (the primitive `KUsing` protected scope).
- **Conformance**: `tests/conformance/qtt/captures-identity.kp` (capture
  identity ≠ subsumption); `…/modules-imports-positive-explicit-region-capture/`
  (a working `captures (s)` over a returned **closure**, for contrast);
  `tests/conformance/qtt/borrow-escape.kp`.
- **Precedent** `input/kappa-http-stack/src/acme/http/server.kp` L14–57
  (`using` + `while` in-scope; owned `(1 conn)` across the boundary).
- **Site** `examples/packages/delve/src/delve/engine.game.kp` (`runLoop`
  L1610, `main` L1626); `src/delve/terminal.game.kp` (facade +
  `Releasable` instance).
