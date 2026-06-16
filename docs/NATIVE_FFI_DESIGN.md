# Native FFI: spec-conformant foreign boundary

This note records how the native backend's foreign capabilities (TCP
sockets + sqlite3, used by the HTTP demo) map onto the **explicit**
foreign-boundary mechanisms of `docs/Spec.md`, and why the previous design
(injecting `__tcp*` / `__sqlite*` as ordinary prelude `prim` globals) was
not conformant.

## Why the old surface was wrong

The first native backend registered the socket/sqlite operations as
ordinary prelude `prim` globals (`__tcpListen`, `__connRead`,
`__sqliteOpen`, …) with native-only IO semantics. That smuggles host
capabilities into the *ordinary source namespace*: every program saw those
magic globals in scope, with no declaration, no contract, and no backend
capability gate. The spec's foreign model (§26) and `expect` model (§9.4)
are explicit precisely to forbid this.

## The conformant mechanism

The boundary is built from three spec features that compose exactly:

| Concern | Spec mechanism | Citation |
| --- | --- | --- |
| "this module needs a foreign declaration the source file does not define" | `expect term name : T` — an external requirement | §9.4 (Spec.md:8021–8095) |
| "the native backend supplies that declaration" | a **backend intrinsic** of the selected backend profile satisfies the `expect` | §9.4 bullet "a backend intrinsic supplied by the selected backend profile (§34.5)" (Spec.md:8067); §34.5 (Spec.md:37878–37908); §34.5.3 host-binding intrinsics, runtime-only unless elaboration-available (Spec.md:37930–37951) |
| "foreign handles / scalars have a stable ABI vocabulary" | `std.ffi` types, in particular `OpaqueHandle` and the exact-width scalars | §26.1.1 PortableAbi grammar (Spec.md:26031–26052); §26.2 `std.ffi` (Spec.md:27264–27323) |
| "the native realization is the zig profile via the direct native adapter" | `zig` profile realizes `host.native` through `native.direct` | §27.1 (Spec.md:27329–27355); §27.1.1 (Spec.md:27357–27377); adapter modes §26.1.3 (Spec.md:26199–26230) |

So a source program that wants a foreign operation **declares it
explicitly** as an `expect term` using `std.ffi` types, and the operation
is available **only** when a backend profile that supplies the matching
intrinsic is selected. Under the interpreter (no native backend, §27.6
capability set excludes it) the `expect` is simply unsatisfied and
compilation fails honestly with `E_EXPECT_UNSATISFIED` (§9.4) — there is no
hidden global to call and no silent interpreter fallback.

### Capability → intrinsic → runtime mapping

The native (`zig`) profile supplies these runtime-only host-binding
intrinsics (§34.5.3). Each is identified by its Kappa spelling and a pinned
expected signature; the satisfying `expect`'s declared type must match the
intrinsic's signature up to definitional equality (§9.4 "must match the
expected signature up to definitional equality"; §34.5 "exactly up to
definitional equality"). Handles use `std.ffi.OpaqueHandle` — a raw
host-binding surface is permitted to expose bare `OpaqueHandle` (§26.1.1
"a nominal opaque handle type or `std.ffi.OpaqueHandle`"; §26.2 "A raw host
binding MAY expose bare `OpaqueHandle`"). Their concrete runtime
representation is backend-specific (§26.2) — here a `K_FGN` wrapper around a
socket fd or `sqlite3*`.

| Intrinsic (Kappa spelling) | Expected signature (std.ffi) | Native realization |
| --- | --- | --- |
| `tcpListen` | `Int -> UIO OpaqueHandle` | bind+listen on a port |
| `tcpAccept` | `OpaqueHandle -> UIO OpaqueHandle` | accept one connection |
| `connRead` | `OpaqueHandle -> UIO String` | read the request bytes |
| `connWrite` | `OpaqueHandle -> String -> UIO Unit` | write the response |
| `connClose` | `OpaqueHandle -> UIO Unit` | close a connection |
| `listenClose` | `OpaqueHandle -> UIO Unit` | close the listener |
| `sqliteOpen` | `String -> UIO OpaqueHandle` | open a database |
| `sqliteExec` | `OpaqueHandle -> String -> UIO Unit` | run a statement |
| `sqliteQueryInt` | `OpaqueHandle -> String -> UIO Int` | first column of first row |
| `sqliteQueryText` | `OpaqueHandle -> String -> UIO String` | first column of first row |
| `sqliteClose` | `OpaqueHandle -> UIO Unit` | close a database |

`Kappa.Backend.Intrinsics` is the single source of truth for this table
(name → expected Core type → runtime FFI primitive). It is consulted in two
places:

1. **Elaboration** (only when the native profile is selected): the
   intrinsic names seed `CheckState.csBackendIntrinsics`, so a matching
   `expect term` is satisfied (§9.4) — after a definitional-equality check
   of the declared type against the intrinsic signature (mismatch →
   `E_BACKEND_INTRINSIC_SIGNATURE_MISMATCH`, family
   `kappa.ffi.backend-intrinsic`). With no native profile the set is empty,
   so the `expect` is unsatisfied (`E_EXPECT_UNSATISFIED`).
2. **Code generation**: a reference to an intrinsic global lowers to the
   corresponding runtime FFI primitive (`runtime/kappart_ffi.c`).

The runtime FFI primitives are **never** registered as prelude globals, so
ordinary source can neither see nor call them; the only path to a foreign
op is the explicit `expect` + native-profile build.

### Honest failure modes (no silent fallback)

* `kappa run` / `kappa check` (interpreter, no native intrinsics): the
  demo's `expect term`s are unsatisfied → `E_EXPECT_UNSATISFIED` (§9.4).
* `kappa build` without `--ffi-full` (native, but FFI capability off): the
  intrinsic set excludes the socket/sqlite ops → `E_EXPECT_UNSATISFIED`.
* An `expect term` whose declared type disagrees with the intrinsic →
  `E_BACKEND_INTRINSIC_SIGNATURE_MISMATCH` at the declaration's span.
* A reachable construct outside the supported native subset →
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
