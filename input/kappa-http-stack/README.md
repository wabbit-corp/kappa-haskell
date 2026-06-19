# Kappa HTTP Stack

This is a fuller Kappa HTTP server/source layout built around four separable layers:

1. **Wire**: byte-level HTTP/1.x parsing and rendering over `Bytes`.
2. **Runtime**: backend-neutral transport expectations, supplied by JVM and .NET fragments.
3. **Application**: typed routes, endpoints, content codecs, middleware, and components.
4. **Server**: connection lifecycle, keep-alive policy, structured fibers, and error recovery.

The design intentionally steals good ideas from mature stacks without cloning any of them:

- Ktor: request/response pipeline and installable plugins.
- ZIO HTTP: declarative endpoints, route collections, typed errors, middleware as route transformation, streaming bodies.
- Snap: tiny handler core plus composable application components.
- Yesod: type-safe reverse routing and route values instead of stringly link construction.

## Important honesty tax

Kappa is still a draft language and no compiler or host-binding generator is available in this environment. The files are written as spec-aligned Kappa source, not as compile-verified output. The backend fragments isolate implementation-defined host binding member names so a real toolchain only needs local adjustment in `runtime.jvm.kp` and `runtime.dotnet.kp`.

## Layout

```text
src/acme/http/core.kp          -- public HTTP model
src/acme/http/headers.kp       -- header normalization and lookup
src/acme/http/body.kp          -- strict and streaming body helpers
src/acme/http/codec.kp         -- content negotiation and entity codecs
src/acme/http/runtime.kp       -- backend-neutral expect surface
src/acme/http/runtime.jvm.kp   -- JVM NIO fragment
src/acme/http/runtime.dotnet.kp-- .NET sockets fragment
src/acme/http/wire.kp          -- HTTP/1.x parser/renderer
src/acme/http/router.kp        -- Route/Routes/App
src/acme/http/endpoint.kp      -- typed declarative endpoints
src/acme/http/middleware.kp    -- route/application middleware
src/acme/http/component.kp     -- Snaplet-style components
src/acme/http/server.kp        -- server loop and connection lifecycle
src/acme/http/example.kp       -- sample application
```

## Supported by the design

- HTTP/1.0 and HTTP/1.1
- request parsing by bytes, not host strings
- strict finite bodies
- streaming body surface via `OnceQuery Bytes`; streamed response writing and chunked request decoding are isolated runtime hooks
- keep-alive policy
- typed failures via `IO e a`
- structured per-connection fibers
- content codecs and negotiation
- typed endpoint descriptions
- middleware composition
- type-safe reverse route values
- backend-specific JVM and .NET fragments behind one portable facade

## Not implemented here

- TLS termination
- HTTP/2 or HTTP/3
- production-grade OpenAPI generation
- production routing trie generation
- all MIME/media-type corner cases

Those belong in additional modules or host/container integration. This package is a serious framework skeleton, not a magical web panacea. Magic remains disappointingly non-deterministic.
