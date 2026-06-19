# Design Notes

## Why the first version was too small

A raw server loop plus `Handler = Request -> IO HttpError Response` is useful for proving transport interop, but it leaves application design to convention. Conventions are where bugs go to wear a tiny fake mustache.

This version makes the core abstractions explicit:

```kappa
type App env e =
    (& env : env) -> RequestContext -> IO (| HttpError | e |) Response

type Middleware env e =
    App env e -> App env e

data Endpoint input output = ...
```

The application receives an environment by borrow, so large shared service packages are not copied or consumed. Typed application failures remain distinct from protocol/runtime `HttpError` by using a variant error channel.

## Borrowed ideas

| Source | Idea used | Kappa adaptation |
| --- | --- | --- |
| Ktor | plugins in request/response pipeline | `Middleware env e = App env e -> App env e` plus `install`/`pipeline` helpers |
| Ktor | content negotiation | `EntityCodec` plus `negotiate` over `Accept` and `Content-Type` |
| ZIO HTTP | `Routes`, typed errors, endpoints | `Routes env e`, `Endpoint input output`, `implement` |
| ZIO HTTP | streaming bodies | `Body.StreamBody (OnceQuery Bytes)`; the portable type surface is present, while stream folding/chunk decoding remains a runtime integration point |
| Snap | small handler core | `Route` returns explicit `RouteResult` rather than hiding fallthrough |
| Snap | modular snaplets | `Component env e` with startup/shutdown and mount prefix |
| Yesod | route datatype / type-safe URLs | `SiteRoute` examples and `UrlFor route` instead of raw string links |

## Why no ambient globals

Kappa's spec treats runtime capabilities as ordinary values. The application environment is an explicit borrowed package, and backend connections/listeners are linear resources. This avoids global runtime state masquerading as architecture.

## Error model

Transport/protocol errors are `HttpError`. Application errors are user-chosen `e`. The server runs applications in:

```kappa
IO (| HttpError | e |) Response
```

so middleware can choose whether to recover protocol errors, app errors, or both.

## Streaming model

`Bytes` is strict and finite. Large bodies should be represented as `OnceQuery Bytes` chunks, not glued into one heroic allocation so the garbage collector can experience personal growth.

## Backend model

The public module `acme.http.runtime` is entirely backend-neutral. JVM and .NET source fragments define the same effective module and satisfy `expect` declarations. Public application modules never import `host.jvm...` or `host.dotnet...` directly.
