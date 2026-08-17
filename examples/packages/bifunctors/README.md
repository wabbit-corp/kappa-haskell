# bifunctors for Kappa

An initial Kappa port of the foundational abstractions from Edward Kmett's
[`bifunctors`](https://hackage.haskell.org/package/bifunctors) package. The
port currently includes `Bifunctor`, `Bifoldable`, `Bitraversable`, the
standard `first`/`second`/`bifoldMap` helpers and the representative `PairF`
product type. It gives the prelude's branch-symmetric `Either` coproduct the
usual bifunctor, bifoldable, and bitraversable instances; `Result` remains
available for error/success-shaped values.

This is an API-level port, written in Kappa rather than a line-by-line source
translation. Template Haskell, compatibility shims, and the upstream wrapper
catalogue are intentionally deferred.

Build and run the native smoke/law suite from the repository root:

```sh
cabal run -v0 kappa -- build --manifest examples/packages/bifunctors \
  --target bifunctors-tests --update -o /tmp/bifunctors-tests
/tmp/bifunctors-tests
```

Upstream reference: `bifunctors-5.6.3`, BSD-3-Clause, copyright Edward A.
Kmett and contributors.
