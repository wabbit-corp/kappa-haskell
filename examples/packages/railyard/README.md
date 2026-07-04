# railyard — STM single-track signalling, with dependently-typed routes

A small native Kappa package that exercises **both** halves of the language at
once:

- **the concurrency runtime** — carts run as fibers and contend for a shared
  single-lane track through Software Transactional Memory, parking on `retry`
  exactly like a railway block signal; deliveries are reported over Promises and
  moves are tallied with a lock-free atomic counter; and
- **dependent types** — a cart's itinerary is a length-indexed `Route (n : PNat)`
  whose type records its hop count, sealed existentially so routes built at
  runtime share a type, and walked by an interpreter the compiler certifies
  **total** with no termination hint.

## The scenario

Five carts each start on a private *entry* siding, travel the same shared
*main line* of four single-lane segments in the same direction, and park on a
private *exit* siding. A segment holds at most one cart. To advance, a cart runs
one STM transaction that claims the next segment and releases its current one —
atomically — and blocks (`retry`) if the segment ahead is still occupied.

Because every cart goes the same way down one track, each only ever waits on the
segment immediately ahead, which the cart in front will vacate: the pipeline
drains with no collisions and no deadlock. The printed summary is therefore the
same on every run regardless of how the fibers interleave:

```
RAILYARD — single-track STM signalling
  carts dispatched:         5
  hops per cart (main + 1): 5
  receipts (sum of moves):  25
  atomic move counter:      25
  main line still occupied: 0
RAILYARD: ALL DELIVERED, TRACK CLEAR, MOVES CONSERVED
```

`receipts == atomic counter == 5 × 5` and `main line still occupied == 0` are the
conserved invariants: every move is counted exactly once (no lost atomic
updates), and every cart has left the shared track.

## Build & run

From the repository root:

```sh
# the dispatcher (the concurrent simulation)
cabal run -v0 kappa -- build --manifest examples/packages/railyard -o /tmp/railyard --target railyard
/tmp/railyard

# the pure-logic tests
cabal run -v0 kappa -- build --manifest examples/packages/railyard -o /tmp/railyard-tests --target railyard-tests
/tmp/railyard-tests   # -> RAILYARD TESTS: ALL PASS
```

The build emits two `W_TERMINATION_UNVERIFIED` warnings, for `buildMain` and
`spawnCarts` — the two helpers that count down a plain `Int`. The front end
records rather than verifies their termination; the route functions that the
dependent types are *about* (`runRoute`, `routeLen`, `buildRoute`) are proven
total and warning-free. See `DESIGN.md` for why.

## Layout

| File | Role |
|------|------|
| `src/railyard/core.kp` | `PNat`, the length-indexed `Route`, the existential `SomeRoute`, `Receipt` |
| `src/railyard/track.kp` | segment cells and the atomic `moveTo` signalling rule |
| `src/railyard/route.kp` | `buildRoute` (runtime list → sealed route) and `routeLen` |
| `src/railyard/cart.kp` | `runRoute` (total route interpreter) and the cart fiber |
| `src/railyard/yard.kp` | `runYard` — builds the topology, spawns carts, awaits receipts, audits; shared by the dispatcher and the tests |
| `src/railyard/dispatch.game.kp` | the executable entry point: runs a yard and prints the audit |
| `test/railyard/run_tests.test.kp` | route-length and move-invariant checks **plus** a real concurrent run asserting the conserved invariants |
| `kappa.build.kp` | manifest: a `railyard` (game) and a `railyard-tests` (test) executable target |

Target backend is `aarch64-apple-darwin` (C backend); change `targetTriple` in
`kappa.build.kp` for other hosts. The concurrency primitives are exercised on the
C backend.
