# Native HTTP server over libuv

A small HTTP/1.1 server that builds and runs **natively** through the Kappa
native backend. It exercises the full chain the HTTP-stack design calls for:

- **Module-fragment selection (§8.1 / §36.12).** `src/acme/http/runtime.kp` is a
  backend-neutral facade that declares the transport surface with `expect term`
  (§9.2 / §9.4). The companion fragments realise it per backend:
  - `runtime.native.kp` (suffix `native`) — selected for the native target.
  - `runtime.jvm.kp` (suffix `jvm`), `runtime.dotnet.kp` (suffix `dotnet`) — NOT
    selected here. They import `host.jvm.*` / `host.dotnet.*` modules that do not
    exist natively, so a successful native build is itself proof that fragment
    selection excluded them.
- **Host bindings GENERATED from parsed headers — no hand-authored `symbolDecl`
  (§26.1 / §27.1.1 / §36.28).** Both native surfaces in `kappa.build.kp` use
  `generateFromHeader`: the build plan preprocesses the named header (with the
  binding's pkg-config cflags, `-D` defines, and target ABI), parses each named
  C function's declaration, and maps its types to the conservative
  `std.ffi`/opaque/Option vocabulary (a non-`char` pointer ⇒ `Option RawPtr`, a
  `char` pointer ⇒ the C-string convention, integer/float scalars ⇒ their
  exact-width nominal, `void` ⇒ Unit).
  - `host.native.libuv.Raw` is generated from the real `<uv.h>` discovered via
    `pkg-config` — the raw libuv surface (its synchronous, value-typed
    functions, e.g. `uv_version_string`, which the server prints at startup).
  - `host.native.uvnet` is generated from `native_uv_shim.h`, the public ABI of
    the blocking adapter. libuv's API is callback/async — which a conservative
    C-ABI binding cannot drive directly — so `native_uv_shim.c` is the justified
    event-loop companion (§26.1.9). It delegates entirely to libuv (no
    hand-rolled socket primitives) and is compiled against `<uv.h>`, so its
    libuv use is verified by the toolchain.
  pkg-config pins libuv's version/`.pc` identity and the header bytes are
  digested into `kappa.lock` (§36.7), so a header drift repins and regenerates.
- **Refining overlay.** `runtime.native.kp` is a thin Kappa overlay over the
  generated conservative surface: it refines the raw `Option RawPtr` handles
  into the facade's `RawPtr` `Listener`/`Connection` types and satisfies the
  facade's `expect` declarations.
- **Wire + router.** `wire.kp` parses the request line over `Bytes`; `router.kp`
  builds a well-formed response (byte-accurate `Content-Length`). `example.kp`
  is the server loop: print the (generated-surface) libuv version, then serve
  three requests and exit.

## Build & run

```sh
kappa build --update --manifest . -o /tmp/httpd   # discovers + pins libuv
/tmp/httpd &                                       # listens on 127.0.0.1:8090
curl -i http://127.0.0.1:8090/                     # 200, "hello from kappa + libuv"
curl -i http://127.0.0.1:8090/health               # 200, "ok"
curl -i http://127.0.0.1:8090/nope                 # 404
```

The server self-exits after serving three requests. Requires libuv installed
(`pkg-config --exists libuv`) and a C driver. Covered by the native suite
(`test/native/run-native-tests.sh`).
