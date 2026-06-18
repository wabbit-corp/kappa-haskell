# Native FFI: manifest-driven direct-call foreign boundary

This note records how the native backend's foreign capabilities (TCP
sockets + sqlite3, used by the HTTP demo) map onto the **explicit**
foreign-boundary mechanisms of `docs/Spec.md`, and the design invariant the
backend must keep: native bindings are discovered/resolved entirely from the
build manifest and lowered to **direct, typed C call sites** — there is no
hardcoded native catalog, no runtime primitive registration table, and no
string- or `KValue`-dispatched primitive firing in generated native output.

## What the design forbids (and how it is enforced)

Two earlier designs were rejected. The first registered the socket/sqlite
operations as magic prelude `prim` globals (`__tcpListen`, `__sqliteOpen`,
…): that smuggles host capabilities into the ordinary source namespace. The
second moved them behind a hardcoded in-compiler catalog
(`Kappa.Backend.NativeCatalog`) whose members lowered to string-named
runtime FFI primitives dispatched by `strcmp` in `runtime/kappart_ffi.c`:
that is still a hardcoded native list plus a runtime dispatch table. Both
are gone. The forbidden shapes — a hardcoded catalog, a generic FFI-unit, a
`kprim_call("__…")` / `prim_fire_pure` string dispatch over native symbols —
must not reappear in optimized native output (the build-test suite asserts
the generated `.kappa.c` contains the per-member wrapper and **no**
`kprim_call("__` for a native binding).

## The conformant mechanism

A program `import`s a `host.native.*` module (§8.3.5); a build manifest's
`nativeBinding` provider (§36.28) supplies it; the `zig` profile realizes it
through the direct native adapter (`native.direct`, §27.1.1). The binding
FULLY DESCRIBES its surface — there is nothing to look up in the compiler.

| Concern | Spec mechanism | Citation |
| --- | --- | --- |
| "which host modules exist and what they export" | the manifest `nativeBinding`'s `provides` + `symbolList` (a list of `symbolDecl member cSymbol params result`) | §36.28 (Spec.md:41768–41805); §27.1.1 (Spec.md:27357–27377) |
| "foreign handles / scalars have a stable ABI vocabulary" | `std.ffi` types — `OpaqueHandle`, `RawPtr`, scalars — via the conservative `CType` vocabulary | §26.1.1 PortableAbi (Spec.md:26031–26052); §26.1.4 conservative typing; §26.2 `std.ffi` |
| "the native realization is the zig profile via the direct native adapter" | `zig` realizes `host.native` through `native.direct` | §27.1 (Spec.md:27329–27355); §27.1.1; adapter modes §26.1.3 |

Under the interpreter (no manifest, no native profile) the `host.native.*`
imports are simply unresolved and compilation fails honestly with
`E_MODULE_NAME_UNRESOLVED` (§8.3.5) — no hidden global, no fallback.

### Surface → ResolvedNativeSymbol → direct call

The single source of truth is the manifest. `Kappa.Build.Plan.resolveBinding`
turns each binding's `provides × symbolList` into `ResolvedNativeSymbol`
records (`module ↦ member`, C symbol, `[CType]` params, `CType` result),
which thread to both elaboration and codegen — there is no catalog:

1. **Elaboration** (`Kappa.Pipeline.applyNativeModules`): each resolved
   member is registered as an abstract global (runtime-only, §34.5.1) under
   its module, with its Kappa type DERIVED from the ABI signature via
   `Kappa.Backend.NativeFfi.nativeMemberType` (`p₁ → … → UIO result`,
   conservative §26.1.4). The module export list comes from the members, so
   `import host.native.X as m; m.member` resolves and type-checks.
2. **Code generation** (`Kappa.Backend.C`): a reference to a member lowers
   to a curried native action (`knative`); a saturated application lowers to
   a direct `knative_sat(kw_<member>, arity, args)`. `assemble` emits, per
   used member, a direct `extern <ret> <cSymbol>(<params>);` prototype and a
   statically-typed marshalling wrapper `kw_<member>(KValue **a)` that
   unboxes each arg per its `CType` (`kas_int`/`kas_str`/`kas_fgn`/…), calls
   `<cSymbol>` **directly**, and boxes the result. `krun_io` fires a
   `K_NATIVE` action by calling that function pointer — no name, no `strcmp`.

The `CType ↔ C-ABI-spelling ↔ Kappa-type ↔ marshalling` mapping lives in
`Kappa.Backend.NativeFfi` (the only place that knows the ABI vocabulary).
Handles use `std.ffi.OpaqueHandle` and are represented at runtime as a
`K_FGN` wrapper around the C pointer (a socket fd or `sqlite3*`), which the
Kappa side treats opaquely (§26.2 permits a bare `OpaqueHandle` raw surface).

### Where the C symbols come from

The manifest's `inputs` name the realization (§36.28): a `shim [...]` is a
package-authored C translation unit compiled+linked by the driver; `headers`
/ `includeDir` add `-I`; `define` adds `-D`; `pkgConfig` runs `pkg-config`
for cflags/libs; `link` adds `-l`/`-L`. The HTTP demo's C symbols live in
`examples/native/http_sqlite/native_shim.c` (plain C-ABI functions named by
its `symbolList`), and sqlite3 is linked via `pkgConfig "sqlite3"`.

### Honest failure modes (no silent fallback)

* `kappa run` / `kappa check` (interpreter, no manifest): `host.native.*`
  imports are unresolved → `E_MODULE_NAME_UNRESOLVED` (§8.3.5).
* a `nativeBinding` providing a module not under the `host.native` root, or
  with an empty surface → `E_NATIVE_BINDING_UNSUPPORTED` (§27.1.1/§36.28).
* a load mode the zig profile does not realize (`runtimeLoad`,
  `providedByHost`, `bundledLoader`) → `E_BACKEND_HOST_LINK_UNREALIZABLE`
  (§34.5.3/§36.28).
* a reachable construct outside the supported native subset →
  `E_BACKEND_UNSUPPORTED` (unchanged).

## Native tail calls

The spec does not mandate general proper tail calls (it requires tail
*position* only for handler resumptions, §34875/§G), but unbounded C-stack
growth on tail recursion is a real defect for a native backend. The backend
therefore implements **self-tail-call elimination**: a function whose body
ends in a call to itself in tail position is compiled to a loop (rebind the
parameters, `continue`) instead of a recursive C call, so a tail-recursive
function runs in constant C stack. This is sound because a tail call's
result *is* the caller's result — evaluating it by looping rather than
recursing preserves the §31/§32 reduction semantics.

Tail calls that are **not** direct self-calls (mutual recursion, calls
through an unknown function value) are not eliminated: they remain ordinary
C calls and so are bounded by the C stack, exactly like the documented
deep-non-tail-recursion limit (`docs/NATIVE_BACKEND.md`). This is a
documented, honest limitation, not a miscompilation — the result is always
correct; only very deep mutual-tail chains can exhaust the stack. See
`docs/NATIVE_BACKEND.md` for the limitation statement.
