# profunctors for Kappa

An initial Kappa port of Edward Kmett's
[`profunctors`](https://hackage.haskell.org/package/profunctors) package. It
contains the core `Profunctor`, `Strong`, `Choice`, and `Closed` traits plus the
representative `Fn`, `Star`, `Costar`, `Forget`, `Tagged`, and `Exchange`
carriers. The package uses the sibling Kappa `bifunctors` port for `PairF`.

This foundation is deliberately early in the porting order: profunctor optics
are one of the cleanest routes toward a useful `lens` port, while `Star` and
`Costar` also connect the abstraction to effectful and context-dependent code.

```sh
cabal run -v0 kappa -- build --manifest examples/packages/profunctors \
  --target profunctors-tests --update -o /tmp/profunctors-tests
/tmp/profunctors-tests
```

Upstream reference: `profunctors-5.6.3`, BSD-3-Clause, copyright Edward A.
Kmett and contributors.
