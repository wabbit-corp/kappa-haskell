# FFI, linking, and deployment — the kappart2 Driver plan

How a Kappa native binary calls C, links `kappart2` + libuv + Boehm GC + GMP, and
ships. Synthesized from four web+spec-grounded research passes (FFI/C-ABI,
dynamic linking, static linking, GC×FFI×threads — archived in the task outputs)
and grounded in the actual `Driver.hs` link command. This is the design the v2
Driver work follows.

## 1. FFI — keep the conservative-binding + blocking-shim pattern

The two runtime facts that shape everything: every value is a boxed `KValue*`
under a conservative Boehm collector, and the agent crossing the C boundary is a
known, GC-registered thread. From those, the existing posture is correct:

- **Conservative C-ABI bindings only.** Generated wrappers (`NativeFfi.hs`) emit
  calls whose params/results are scalars or pointers — the C compiler lays out
  the call, so `generateFromHeader` *fails closed* on callbacks/function-pointers,
  by-value structs/unions, variadics, `long long`, `long double`. Each would
  require kappart2 to reproduce target-ABI eightbyte/HFA/varargs classification by
  hand or synthesize a C function pointer that re-enters the GC'd runtime — so
  they're rejected and reported, never guessed (§26.1.2).
- **Callback-driven libraries → a blocking shim.** The canonical recipe (the
  `http_uv` example): wrap an async/callback C API in a thin shim that runs the
  loop on the *calling* thread and exposes a blocking surface; the library's
  callbacks fire on that one thread and only enqueue — they never re-enter Kappa.
  No thread attach, no GC registration, no foreign-thread-root problem.
- **kappart2's own reactor already does the safe thing**: libuv callbacks run on
  the reactor thread (GC-registered via `GC_pthread_create`) and only enqueue
  woken fibers — exactly the "callbacks enqueue, never re-enter" discipline.
- **Real callback ingress (§26.1.8), if ever needed**, has two hard prerequisites
  that must land together: (a) `GC_register_my_thread`/`GC_call_with_gc_active`
  around any foreign thread that will touch `KValue`s (and a thread-aware libgc),
  and (b) a boundary wrapper that catches Kappa typed-failures/defects and
  translates them to a host result — never letting a failure unwind through a C
  frame (mirror Rust's `extern "C"` abort discipline). Classify each boundary
  sync/async and name the registration-owning scope, or the surface is ill-formed.

## 2. GC × FFI × threads — the correctness substrate (mostly already done)

kappart2 already implements the recommended discipline; the Driver must back it:

- **Threaded libgc.** Compile the runtime TUs with `-DGC_THREADS`, link `-pthread`,
  and add a build-time probe (à la `discoverAndVerifyNative`) asserting the
  resolved libgc exposes `GC_do_blocking`/`GC_register_my_thread` — fail closed
  (`E_BACKEND_TOOLCHAIN`) otherwise, and pin the libgc identity in `kappa.lock`.
- **Thread creation.** `krt_init` → `GC_INIT()` then `GC_allow_register_threads()`;
  create reactor + worker + pool threads via `GC_pthread_create` so their stacks
  are located for stop-the-world. (kappart2 already uses `GC_pthread_create`.)
- **The rt-blocking lane** (when built): a bounded pool + handoff queue; each
  blocking foreign call runs inside `GC_do_blocking`; results come back as **raw
  C** (`GC_MALLOC_ATOMIC` buffers / scalars), and the GC-active reactor converts
  them to `KValue`s and resumes the fiber — pool threads must never allocate
  `KValue`s. Only then advertise `rt-blocking`.

## 3. Linking — default to self-contained, per-OS

The current `Driver.hs` link line (`cc … kappart.c <gen>.c <shims> -lgc -lgmp
<pkg-config libuv> -o out`) records `-lgc`/`-lgmp`/`-luv` as `DT_NEEDED` sonames
with **system-loader** semantics and **no rpath** — correct for `systemLoader`,
but *not* self-contained per §36.29 (the binary finds its deps only on the default
path). The plan:

**Add a deployment mode** to `BuildOptions` (`deployMode :: DeployMode`) deriving a
`linkMode :: LinkMode = WholeBinaryStatic | StaticDeps | Dynamic`, threaded through
`app/Main.hs` + `Build/Plan.hs`, and make the runtime deps **mode-aware** —
replace the literal `["-lgc","-lgmp"]` (`Driver.hs:240`) with a helper that emits
static or dynamic forms per `linkMode`, reusing the `-Wl,-Bstatic … -Wl,-Bdynamic`
idiom already in `linkFlags`.

**Default = self-contained, realized per-OS** (matching Go / Rust-musl / Zig):

| target | how | self-contained? |
|--------|-----|-----------------|
| Linux  | `zig cc -target <arch>-linux-musl -static` (zig + targetTriple already plumbed) — fully static incl. musl libc | yes |
| macOS  | static `libgmp.a`/`libgc.a`/`libuv.a` + dynamic libSystem (macOS forbids fully-static libc) | deps yes; report `system-prerequisite` for libSystem |
| Windows| static CRT (`/MT`) + static deps | yes |

**Statically link Boehm GC + GMP by default** regardless of mode — they're the
runtime's *own* ABI-stable deps; static linking removes them from the runtime
search entirely (`-Wl,-Bstatic -lgc -lgmp -Wl,-Bdynamic`), the single biggest win
toward self-contained with no rpath complexity. `kappart2` + libuv link the same
way for a static deploy; libuv stays the one host-binding whose load mode the
manifest controls.

**Harden the produced binary:** compile the runtime with `-fvisibility=hidden` +
a version script exporting only the public ABI (`kappa_main` / host-call entries),
keeping `krt_*`/`kp_*`/`krt2_*` internals local — prevents host/runtime symbol
collisions (e.g. a host's `uv_*` or `GC_malloc`) and speeds load. Default to
`-z now -z relro` (fail-fast binding + RELRO) so a missing/incompatible symbol is
a clean startup diagnostic, not a mid-run crash.

## 4. The §36 load modes → OS mechanisms

For the dynamic path (and per-binding host libraries like libuv):

| §36 load mode | Driver emits | deployment |
|---------------|--------------|------------|
| **systemLoader** (today) | plain `DT_NEEDED`/`LC_LOAD_DYLIB`, **no rpath**; loader uses the default search | **non-self-contained / `system-prerequisite`**; record required versioned soname + ABI fingerprint |
| **bundledLoader** | copy the resolved **versioned** lib (`libuv.so.1`, not the dev `.so`) next to the artifact + emit a relocatable rpath: Linux `-Wl,-rpath,'$ORIGIN/../lib' -Wl,--enable-new-dtags`; macOS `install_name @rpath/<leaf>` + `-Wl,-rpath,@loader_path/../lib` (+ `install_name_tool` fixup + **re-sign**); Windows DLL-beside-exe | self-contained |
| **runtimeLoad** | `dlopen("libuv.so.1", RTLD_NOW\|RTLD_LOCAL)` + `dlsym` with the `dlerror()` clear/call/check discipline (Windows `LoadLibraryExW`+`GetProcAddress`); `-ldl` on Linux | optional/plugin deps; structured "missing/incompatible runtime lib" diagnostics |
| **providedByHost** | nothing (symbols already in the loading process) | always non-self-contained; record host prerequisite |

**Branch all of the above on `targetTriple`** (already threaded): rpath syntax,
install-name handling, `-ldl`, and dlopen-vs-LoadLibrary are the cross-platform
divergences the Driver owns.

## 5. Pitfalls the Driver must avoid

- Bundle the **soname** (`libuv.so.1`), never the dev symlink (`libuv.so`).
- `$ORIGIN` must reach the linker literally (`-Wl,-rpath,'$ORIGIN/lib'`).
- Emit `DT_RUNPATH` (`--enable-new-dtags`), not legacy `DT_RPATH` (non-overridable,
  transitive — usually wrong).
- macOS SIP strips `DYLD_*` from system-launched processes → rely on install-names
  + `LC_RPATH`, never env vars; editing a Mach-O install-name requires re-signing.
- `dlsym` returning NULL is ambiguous → use the `dlerror()` sandwich.
- Don't build the cross-platform plugin path on `dlmopen`+`RTLD_GLOBAL` (glibc-only
  footgun).

## 6. Ranked Driver actions (for the v2 work)

1. Make `-DGC_THREADS -pthread` + the threaded-libgc probe a property of the
   runtime build (both the standalone Makefile and `Driver.hs`); fail closed on a
   non-thread-mode libgc; pin libgc identity in `kappa.lock`.
2. Add `deployMode`/`linkMode`; statically link GC+GMP (+libuv, +kappart2) by
   default; emit `-static` on Linux/musl via `zig cc`.
3. Compile the runtime `-fvisibility=hidden` + version script; produced exe `-z now`.
4. Implement `bundledLoader` (copy versioned lib + `$ORIGIN`/`@loader_path` rpath)
   and `runtimeLoad` (`dlopen` glue) as opt-in modes; keep `systemLoader` honest
   about the non-self-contained tag.
5. Link `libkappart2.a` + `-luv` unconditionally when the target uses kappart2
   (REVIEW.md M14 — the runtime can't ride a `hostBinding`/`pkgConfig` entry).
