# contravariant for Kappa

An initial Kappa port of Edward Kmett's
[`contravariant`](https://hackage.haskell.org/package/contravariant) package. It
includes `Contravariant`, `Divisible`, and `Decidable`; the `phantom` helper;
and the representative `Predicate`, `Equivalence`, `Comparison`, and `Op`
carriers.

The port uses the upstream-shaped `lose : (a -> Void) -> f a` member and the
prelude's branch-symmetric `Either` coproduct directly.

```sh
cabal run -v0 kappa -- build --manifest examples/packages/contravariant \
  --target contravariant-tests --update -o /tmp/contravariant-tests
/tmp/contravariant-tests
```

Upstream reference: `contravariant-1.5.6`, BSD-3-Clause, copyright Edward A.
Kmett and contributors.
