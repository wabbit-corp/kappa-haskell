# Native backend examples

Programs compiled to real native executables by the Kappa native backend
(`kappa build`; see [`../../docs/NATIVE_BACKEND.md`](../../docs/NATIVE_BACKEND.md)).

A C driver is required. Either set `$KAPPA_CC` (e.g. `export KAPPA_CC="zig
cc"` or `export KAPPA_CC=cc`) or have `zig`/`cc`/`gcc`/`clang` on `PATH`.
The runtime links Boehm GC (`-lgc`); the demo also links `-lsqlite3`.

## `hello.kp`

The smallest end-to-end example: print a string from a native executable.

```sh
cabal run -v0 kappa -- build examples/native/hello.kp -o /tmp/hello && /tmp/hello
# hello, native kappa
```

## `http_sqlite/` — HTTP server + sqlite3

`server.kp` is a real native HTTP server backed by sqlite3. For each
request it performs a sqlite **write** (increment a persistent hit
counter) and a sqlite **read** (the new count), then sends an HTTP/1.1
response reporting the count. It serves three requests and exits.

```sh
export KAPPA_CC="zig cc"          # or cc / gcc / clang
bash examples/native/http_sqlite/run.sh
```

`run.sh` builds the server, starts it, sends three HTTP requests, and
checks both the responses (`hits=1`, `hits=2`, `hits=3`) and the persisted
database (`counter.hits = 3`). It is bounded by timeouts and self-cleaning.

Expected output ends with `DEMO OK`.
