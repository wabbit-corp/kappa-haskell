# Borrowed resources through `IO` across a function boundary

*Discovered 2026-06-24 while trying to make Delve's terminal lifetime
statically safe (`examples/packages/delve/src/delve/engine.game.kp`).*

> Status 2026-07-06: S6.A closes the kernel-`IO` part of this note. A
> user-defined `do` block may now return an action whose type explicitly records
> the borrowed region, e.g.
> `forall (s : Region). (&[s] x : T) -> ((IO e a) captures (s))`. The
> unannotated form `(& x : T) -> IO e a` remains a borrow escape, and first-class
> escape points such as `fork` still require `captures ()`. The sections below
> are kept as the historical diagnosis and to document the still-open generic
> user-monad/capture-polymorphic-bind gap.

## TL;DR

A long-lived resource that is **borrowed** (`& x`) cannot be threaded through a
plain, region-free `IO` result. A returned `IO` value is a closure; if it
captures a borrow, the result type must say so with `captures (s)`.

The current supported kernel-`IO` shape is:

```kp
runLoop :
    forall (s : Region).
    (&[s] terminal : term.Terminal) -> ((IO GameError Unit) captures (s))
```

This is intentionally not a silent relaxation: the unannotated
`(& terminal : term.Terminal) -> IO GameError Unit` shape is still rejected
with `E_QTT_BORROW_ESCAPE`. Generic user monads still need a future
capture-polymorphic bind story; S6.A only teaches the kernel `do` elaborator to
classify `((IO e a) captures (s))` as an `IO` action while preserving the
capture annotation on the result type.

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
the `Releasable` instance) and pass a borrow to a region-free `runLoop`:

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
game. The annotation makes the boundary honest:

```kp
runLoop : forall (s : Region). (&[s] terminal : term.Terminal)
            -> Size -> Int -> GameState -> (IO GameError Unit captures (s))
```

As of S6.A, the parenthesized kernel-`IO` form works. The two subsections below
record the historical implementation issues that produced this note.

### 4a. Historical parser precedence discrepancy

Before the S6.A cleanup, written without inner parens —
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
`IO GameError ((Unit) captures (s))` — i.e. *tighter* than application. Current
S6.A-era checks accept the unparenthesized form, so this is historical rather
than an open parser workaround.

### 4b. Historical wall: `ioBind` was monomorphic in captures

Before S6.A, even with explicit parens the annotation parsed correctly and the
borrow-escape check was suppressed (`capturesAnnotated` in `Usage.hs` matched
the `ECaptures` node), but the **type checker** then rejected:

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

The cause was treating the captured `IO` block as ordinary user-monad syntax
over the prelude bind primitive (`Prelude.hs:521`):

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
`IO e b` — both **plain, region-free** `IO` (empty capture set). The
pre-S6 checker classified `((IO e a) captures (s))` as a user monad instead of
as the kernel `IO` carrier, so it tried to route the block through that
monomorphic bind. So:

- the recursive call now has type `__captures (IO …) s`, but the
  enclosing `ioBind` continuation must return plain `IO …` → mismatch
  (L1624);
- conversely `ioBind` *produces* plain `IO …`, but `runLoop`'s declared
  result is `__captures (IO …) s` → mismatch (L1614);
- and `main`'s `using` body inherits the same conflict (L1637).

`__captures (IO e b) s` is a **distinct type** from `IO e b`; capture
subsumption is not definitional equality. S6.A fixes the kernel `IO` path by
peeling capture annotations for carrier classification, checking the block at
the underlying `IO e a`, and returning the original capture-annotated action
type. This does not make the generic `Monad` trait capture-polymorphic; user
monads remain future work.

## 5. Root cause

`captures (s)` lives on a value's type and records the regions it hides.
The region machinery can carry it across an **arrow** (a first-class closure
literal carries its own capture set). For kernel `IO`, S6.A now carries that
annotation through the primitive `do` elaborator. For generic user monads, the
old limitation still applies: the `Monad` trait is written once, region-free,
so there is no capture-polymorphic bind to thread an arbitrary capture set.

Contrast Rust, where the analogy *does* close: an `async fn` / closure
capturing `&'a` produces `impl Future + 'a`, the lifetime is part of the
type, and the combinators (`and_then`, `.await`) are lifetime-
polymorphic. Kappa has the type former (`captures`) but not the
lifetime-polymorphic monadic bind.

## 6. What works instead

| Shape | Compiles | Cleanup on crash | Static leak / double-close prevention | Fits Delve's style |
|---|:--:|:--:|:--:|:--:|
| Explicit `IO ... captures (s)` helper | ✓ | Depends on caller's bracket/using | ✓ for the borrow lifetime | ✓ for recursive helpers |
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

For a **singleton** handle opened once in `main`, a value-level bracket such as
`finallyIO` can still be the better engineering fit when crash cleanup matters
more than static leak/double-close prevention. The S6.A form is useful when the
caller already owns a protected borrow scope and wants to factor a recursive or
helper `IO` action without re-owning the resource.

## 7. Possible language-level fixes

If this gap is ever worth closing:

1. **Capture-polymorphic generic bind** (`Functor`/`Applicative`/`Monad`
   beyond kernel `IO`): abstract bind over a region/capture row so a
   continuation capturing `&[s]` yields an action type `captures (s)` and the
   set propagates. The direct kernel `IO` do elaborator no longer needs this to
   handle `((IO e a) captures (s))`, but user monads still do.
2. **Region-threading `do`-scope**: make the `do` elaborator treat a
   borrowed-resource bind the way `using` is already treated — a
   primitive protected scope that carries `rho` — rather than plain
   `ioBind` capture, so the region is confined structurally instead of
   needing to appear in the bind's type.

Either is a type-system change, not something to encode in user code.

The old §4a parser precedence discrepancy is no longer reproduced by the
S6.A-era checker; keep it in mind only when reading older diagnostics.

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
