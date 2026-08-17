# comonad for Kappa

An initial Kappa port of Edward Kmett's
[`comonad`](https://hackage.haskell.org/package/comonad) package. It includes
the core `Comonad` API, Cokleisli composition, and useful `Identity`, `Env`,
`Store`, and `Traced` carriers.

The port is written as direct, ordinary Kappa. The transformer and indexed
class catalogue is deferred until its supporting packages are available.

Build and run the native law/smoke suite from the repository root:

```sh
cabal run -v0 kappa -- build --manifest examples/packages/comonad \
  --target comonad-tests --update -o /tmp/comonad-tests
/tmp/comonad-tests
```

Upstream reference: `comonad-5.0.10`, BSD-3-Clause, copyright Edward A. Kmett,
Dave Menendez, and contributors.
