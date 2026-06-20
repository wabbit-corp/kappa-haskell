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
- **libuv host binding, no hardcoded sockets (§26.1 / §26.1.5 / §36.28).** The
  native fragment delegates to `host.native.uvnet`, a `nativeBinding` in
  `kappa.build.kp`. The build plan discovers libuv via `pkg-config`, verifies the
  real `uv_*` prototypes the adapter uses against the installed `<uv.h>`
  (fail-closed), and pins the resolved host-source identity in `kappa.lock`
  (§36.7). `native_uv_shim.c` is an ordinary C blocking adapter over libuv — it
  does not hand-roll a socket primitive set.
- **Wire + router.** `wire.kp` parses the request line over `Bytes`; `router.kp`
  builds a well-formed response (byte-accurate `Content-Length`). `example.kp`
  is the server loop: serve three requests, then exit.

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
