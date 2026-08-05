# recursion-schemes for Kappa

An initial Kappa port of Edward Kmett's
[`recursion-schemes`](https://hackage.haskell.org/package/recursion-schemes)
package. It includes `Recursive` and `Corecursive`, the foundational `cata` and
`para` schemes, and a fully usable `ListF` base functor.

Kappa currently expresses the Haskell package's associated `Base t` type
family as a second trait parameter: `Recursive t f` and `Corecursive t f`.
That keeps the schemes generic while remaining direct, ordinary Kappa.

Generic unfolds (`ana`/`apo`) and hylomorphisms are deferred: their recursive
seed is produced by an arbitrary coalgebra, while portable Kappa currently has
no safe way to express the required termination argument. The same boundary
also prevents the conventional generic `Fix f` type; both limitations are
recorded in the repository's known spec issues rather than hidden behind an
unsafe termination assertion.

```sh
cabal run -v0 kappa -- build --manifest examples/packages/recursion-schemes \
  --target recursion-schemes-tests --update -o /tmp/recursion-schemes-tests
/tmp/recursion-schemes-tests
```

Upstream reference: `recursion-schemes-5.2.3`, BSD-2-Clause, copyright Edward
A. Kmett and contributors.
