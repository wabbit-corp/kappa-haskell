# railyard — design notes

The goal was one example that genuinely leans on both the native concurrency
runtime and the dependent-type layer, while staying inside the subset this front
end and the C backend actually implement today. This note records the design and
the constraints that shaped it.

## Concurrency model: STM as railway signalling

Each track segment is a one-slot cell, `TVar Bool`, where `True` means "a cart is
on it". The whole movement rule is a single transaction:

```kappa
moveTo here next = do
    let occ <- readTVar next
    if occ then retry
    else do
        writeTVar next True
        writeTVar here False
```

Two properties fall out of running this `atomically`:

- **Collision safety.** Claiming `next` and releasing `here` happen in one
  transaction. STM commits a transaction only if every `TVar` it read still holds
  the value it saw; so if two carts race for the same `next`, only one commit
  wins and the other re-runs, observes `occ = True`, and `retry`s. At most one
  cart is ever on a segment.
- **Blocking via `retry`.** `retry` parks the fiber and the runtime re-wakes it
  when a `TVar` it read changes — i.e. when the cart ahead releases the segment.
  This is precisely a block signal: a cart holds at the boundary until the line
  ahead is clear.

**Deadlock freedom.** Every cart traverses the shared main line in the same
direction, and holds only its current segment while reaching for the next. A
hold-and-wait cycle would require some cart to wait on a segment *behind* it, but
no cart ever does. The lead cart's "next" is eventually its own (private, always
clear) exit siding, so it always makes progress and frees the segment behind it,
which lets the follower advance, and so on. The pipeline drains monotonically.

**Determinism of the report.** The summary numbers don't depend on interleaving:
the move counter is a lock-free `atomicFetchAdd`, so it sums every hop exactly
once with no lost updates; each cart publishes its receipt only *after* its last
move commits, and the dispatcher reads the counter only *after* every receipt has
arrived (`awaitPromise` on all of them), establishing the happens-before edge. So
`atomic counter == Σ receipts == carts × hops` on every run, and the shared main
line is clear once all receipts are in. Delivered carts still occupy their private
exit sidings by design.

Primitives exercised: `forkDaemon`, `atomically` + `TVar` + `retry`,
`Promise` (`newPromise`/`completePromise`/`awaitPromise`), and `std.atomic`
(`atomicFetchAdd`/`atomicLoad`).

## Dependent types: a length-indexed route

A route is a GADT indexed by its hop count:

```kappa
data Route (n : PNat) : Type =
    RDone : Route PZero
    RHop  : (seg : TVar Bool) -> (rest : Route n) -> Route (PSucc n)
```

The index is erased at runtime; it exists so the type tracks length. Its payoff
is **totality for free**: because the index strictly shrinks at each `RHop`, the
interpreter

```kappa
runRoute route here counter = match route
    case RDone -> ...
    case RHop next rest -> ... runRoute rest next counter ...
```

is accepted as total by structural recursion on the index, with *no* `decreases`
clause — a cart's script provably cannot loop forever. `routeLen` is total the
same way.

Routes are built from a runtime list (`buildRoute mainSegs exit`), whose length
the compiler can't see, so the index is sealed:

```kappa
data SomeRoute : Type =
    Pack : forall (n : PNat). Route n -> SomeRoute
```

`Pack` is an existential: it still carries the concrete length inside, but hides
it, which is what lets a homogeneous `List SomeRoute` (and a single `runCart`
signature) hold routes of different lengths. `buildRoute` itself is proven total
by an explicit `decreases listLength segs`.

So the dependent layer is doing real work here, not decoration:
- a compile-time length index (`Route n`),
- an existential seal over that index (`SomeRoute`),
- machine-checked totality of the route interpreter and builder.

**What the types do and don't prove.** Be precise about the boundary: the index
proves each route is *finite and well-formed*, which is what makes `runRoute`
total. It does **not** prove the railway-safety properties — collision freedom,
deadlock freedom, conservation. Those are guaranteed by the STM transaction
(collision freedom) plus construction invariants (acyclic same-direction routes,
fresh segments, private exits, occupied starts) that live in `railyard.yard`, not
in the types. Encoding *those* in the types would need richer indices — e.g. a
station-typed `Route from to` that rejects an illegal hop at compile time — which
is sketched under "Possible extensions". The split is deliberate and honest: the
type system carries the termination argument; the runtime carries the safety one.

## Constraints that shaped it

- **No O(1) array.** `Array` is a cons list with O(n) indexing, so the design
  stores a `TVar` reference directly inside each route hop; route execution walks
  the hop list and never indexes a global grid.
- **No error path in this example.** All effects are `UIO`/`STM`; failure is not
  raised even though the native backend supports typed error channels. There's no
  error channel to model here, which suits the conserved-invariant framing.
- **No `Fin`/`Vec` in the prelude.** "Dependent types" in practice means Nat
  indices + `decreases` + erased indices + existentials, all of which this
  example uses; it defines its own indexed `Route` rather than reaching for a
  library vector.
- `buildMain` and `spawnCarts` retain public `Int` wrappers for the package API,
  but recurse only in private `Nat` workers after a positive-input guard. Their
  termination is certified by ordinary structural descent.

## Possible extensions

- Two-way traffic (carts going opposite directions) would reintroduce genuine
  deadlock potential and motivate an ordered-acquisition or whole-path
  reservation scheme — a richer STM story.
- Heterogeneous route lengths already work through `SomeRoute`; varying them per
  cart would make the existential do visibly more.
- A Nat-typed cart count would clear the two termination warnings.
