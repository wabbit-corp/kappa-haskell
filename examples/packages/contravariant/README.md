# contravariant for Kappa

An initial Kappa port of Edward Kmett's
[`contravariant`](https://hackage.haskell.org/package/contravariant) package. It
includes `Contravariant`, `Divisible`, and `Decidable`; the `phantom` helper;
and the representative `Predicate`, `Equivalence`, `Comparison`, and `Op`
carriers.

The public `lose` operation is currently derived from the equivalent
`loseEmpty : f Void` member. This keeps the usual API usable while the compiler
bug for associated members of type `(a -> Void) -> f a` remains pinned under
`tests/pending-import/kmett-ports/`.

```sh
cabal run -v0 kappa -- build --manifest examples/packages/contravariant \
  --target contravariant-tests --update -o /tmp/contravariant-tests
/tmp/contravariant-tests
```

Upstream reference: `contravariant-1.5.6`, BSD-3-Clause, copyright Edward A.
Kmett and contributors.
