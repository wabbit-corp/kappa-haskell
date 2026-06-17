# Native Backend Performance Review Notes

Date: 2026-06-17
Reviewer: Codex desktop supervisor
Scope: `runtime/kappart.c`, `runtime/kappart.h`, `src/Kappa/Backend/C.hs`, and generated native output such as `test/native/cases/arith.kappa.c`.

Update: `docs/NATIVE_BACKEND_RAW_C_PERFORMANCE_REVIEW.md` tightens this review from "performance-plausible native backend" to a raw-C-like bar for ordinary monomorphic first-order code. Treat that newer report as the governing acceptance standard for performance claims.

This is deliberately harsh because the native backend is being evaluated as something that should eventually run real code, not just prove that lowering is possible. The current implementation is a reasonable correctness scaffold, but it is still much closer to a boxed interpreter runtime emitted as C than to a performant native backend.

## Executive summary

The biggest performance risk is not one isolated function; it is the cumulative representation strategy:

- all Kappa values go through one heap-boxed `KValue` union;
- most known operations still re-enter string-keyed runtime dispatch;
- function application and local bindings allocate `KEnv` linked-list nodes heavily;
- constructors, variants, records, and primitive names are identified by strings at runtime;
- generated names are often opaque enough that C-level profiling/debugging is unnecessarily painful.

This is acceptable as a bootstrap backend only if the next iteration introduces typed/direct fast paths for monomorphic, first-order code. The backend does not need full whole-program monomorphization yet, but it should not route obviously monomorphic arithmetic, bool checks, tuple projection, and direct function calls through the most generic machinery.

## 1. Primitive dispatch is string-keyed in hot paths

Observed code:

- `runtime/kappart.h` exposes `KValue *kprim_call(const char *name, int argc, KValue **args);`.
- `runtime/kappart.c` routes saturated pure primitives through `prim_fire_pure(const char *p, KValue **a)`.
- `prim_fire_pure` uses `#define PRIM(n) (strcmp(p, n) == 0)` and a large `if (PRIM(...))` chain.
- `prim_arity` repeats the same string-chain pattern.
- generated C uses calls such as `kprim_call("addInt", 2, pa_47)` and `kprim_call("showInt", 1, pa_2)`.

Why this is bad:

- Every statically known primitive call performs runtime string comparisons.
- Hot numeric loops repeatedly allocate a stack argument array, call `kprim_call`, call `prim_arity`, call `prim_is_io`, then run the `prim_fire_pure` string chain.
- The current comment that arithmetic primitives are matched first reduces damage but does not fix the architecture.

Required remediation direction:

- Introduce a compile-time primitive ID enum, for example `KPrimId { KP_ADD_INT, KP_SUB_INT, ... }`.
- Emit `kprim_call_id(KP_ADD_INT, 2, args)` at minimum; better, emit direct helper calls for saturated known primitives: `kadd_int_boxed(a, b)`, `kle_int_boxed(a, b)`, `kshow_int_boxed(a)`.
- Keep string dispatch only for reflective/dynamic fallback and error reporting, not for normal generated code.
- Eliminate the `prim_arity(name)` check from codegen paths where the compiler already knows the primitive and saturation arity.

## 2. Uniform `KValue` boxing is too expensive for monomorphic code

Observed code:

- `runtime/kappart.h` says every value is a boxed heap `KValue`.
- Integer ops unbox from `KValue`, do arithmetic, then box with `kint` or GMP fallback.
- `test/native/cases/arith.kappa.c` shows simple functions like `sumTo`, `fact`, and `addPair` operating entirely on `KValue *`.

Why this is bad:

- Tight arithmetic loops allocate or at least touch boxed values on every iteration.
- Every operation pays tag checks and pointer chasing even when the compiler knows the type.
- The small-int cache helps only a narrow value band and does not remove dispatch/tag overhead.

Required remediation direction:

- Add typed worker generation for obvious monomorphic first-order functions. Examples:
  - `Int -> Int` can lower to `int64_t kw_main_sumTo_i64(int64_t p0, int *overflowed)` or a similar representation with GMP escape.
  - `Bool` can be C `int` inside a typed worker and boxed only at boundaries.
  - `Double`, `Byte`, and scalar/string/bytes helpers should have direct lanes where source types are concrete.
- Generate boxed wrapper functions only when a value crosses a generic/higher-order/polymorphic boundary.
- Start with simple local specialization, not full global monomorphization: if a function is non-polymorphic, first-order, and all call sites are saturated, it should have a typed worker.
- Add fallback to boxed workers when polymorphism, partial application, or existential/variant packaging requires generic values.

## 3. Direct workers exist but are underused

Observed code:

- `src/Kappa/Backend/C.hs` emits direct workers such as `kw_main_2e_mkPair(KValue *p0, KValue *p1)`.
- It also emits curried closure chains (`kclo0_41`, `kclo1_42`) for every function.
- Worker bodies still rebuild a `KEnv *kw_env = kpush(...)` linked list at loop top and access parameters with `kvar`.

Why this is bad:

- Direct workers are the right direction, but their internals still behave like closure/interpreter code.
- `kw_env` allocation inside every loop iteration is particularly wasteful for self-recursive loops.
- `kvar(kw_env, i)` obscures variables from the C optimizer and makes generated code harder to read.

Required remediation direction:

- In direct worker bodies, map de Bruijn variables for parameters to direct C locals (`p0`, `p1`) instead of rebuilding `KEnv`.
- Only allocate `KEnv` for actual escaping lambdas/closures, not for ordinary worker-local variable lookup.
- Lower direct self-tail recursion by reassigning local parameters and `continue`, without rebuilding a linked environment.
- Closure conversion should capture only free variables in a purpose-built struct where possible, not a generic linked list.

## 4. Constructors, variants, and record fields are runtime strings

Observed code:

- `K_CTOR` stores `const char *name`; `kctor_is` uses `strcmp`.
- `K_VARIANT` stores `const char *tag`; `kvariant_is` uses string equality.
- records store `const char **names` and `kproj` linearly scans with `strcmp`.
- generated pattern matches use code such as `kctor_is(scrut_49, "std.prelude.Nil")` and `kproj(rec, "field")`.

Why this is bad:

- Pattern matching and record projection should be among the fastest operations in compiled code.
- Repeated string comparisons and linear field scans are especially poor for list-heavy or record-heavy programs.

Required remediation direction:

- Assign per-program numeric IDs to constructors, variants, and fields.
- Store integer tags in `K_CTOR`/`K_VARIANT` with optional debug names retained only for diagnostics.
- Lower known record/tuple layouts to fixed offsets where the type/layout is known.
- Compile pattern matching to `switch` on integer constructor tags where possible.
- Keep string-based projection only for dynamic/open-record fallback.

## 5. Tail calls are stack-safe but not cheap

Observed code:

- `K_BOUNCE` and `ktrampoline` make mutual/local tail calls stack safe.
- Direct top-level worker lowering uses `while (1)`, but many recursive paths still allocate boxed arguments and bounce/apply through generic closures.

Why this is bad:

- Stack safety is necessary, but a trampoline is still allocation-heavy if every tail step creates `K_BOUNCE` or boxed arguments.
- Known direct self-recursion and known mutual recursion groups can often be compiled to loops/state machines.

Required remediation direction:

- For known self-tail calls, reassign locals and `continue`; avoid `K_BOUNCE` entirely.
- For known mutual tail-recursive SCCs, consider a generated state-machine loop before falling back to `K_BOUNCE`.
- Add benchmarks that distinguish stack-safety from actual throughput.

## 6. Generated C names are too opaque

Observed code in `test/native/cases/arith.kappa.c`:

- local closures and lambdas are named `kfn_9`, `kfn_7`, `kfn_5`, etc.; closure wrappers are `kclo0_41`, `kclo1_42`;
- temporaries are mostly `pa_35`, `scrut_49`, `env_52`, `matched_50`;
- source-level globals are more readable (`kw_main_2e_sumTo`, `kw_main_2e_fact`), but generated local functions lose source intent.

Why this is bad:

- Profiling, crash reports, disassembly, and compiler debugging become much harder.
- Numeric suffixes shift when unrelated earlier code changes, so diffs are noisy.
- The source has enough information to produce better names.

Required remediation direction:

- Derive closure/lambda/helper names from enclosing module/function and source role where possible:
  - `kfn_main_len_cons_builder_...`
  - `kclo_main_mkPair_arg0_...`
  - `kmatch_main_len_cons_...`
- Append a short stable hash/source span suffix for uniqueness instead of only a global counter.
- Emit comments with source spans or source fragments before generated helper functions and match blocks.
- Keep fallback numeric names only when no source label exists.

## 7. Runtime allocation strategy needs performance gates

Observed code:

- Boehm GC is used for simplicity.
- Some pointer-free buffers use `GC_MALLOC_ATOMIC`, which is good.
- Most `KValue`, `KEnv`, `K_CTOR` args, record fields, and bounce values allocate through scanned GC allocations.

Why this is bad:

- The generated backend will allocate aggressively even for simple first-order code.
- Boehm scanning boxed value graphs is fine for correctness but not enough for performance.

Required remediation direction:

- Use atomic allocation for pointer-free runtime payloads consistently.
- Avoid heap allocation entirely for non-escaping temporaries and worker locals.
- Add allocation counters or GC statistics in benchmark mode.
- Add microbenchmarks: arithmetic loop, tail-recursive sum, list fold, record projection, variant match, bytes append/slice, IO loop, sqlite query loop.
- Require native backend performance reports to include allocation counts or at least elapsed-time comparison against interpreter/backend baselines.

## 8. FFI/IO demo path should not hide performance/design debt

The current socket/sqlite demo direction is useful, but performance work must not depend on non-spec hidden primitives. If native-only IO hooks remain, they need to be exposed through the Spec.md FFI model, not as secret prelude globals. For performance specifically:

- repeated sqlite prepare/exec loops should grow prepared-statement handles if the spec permits;
- socket read/write should avoid avoidable KValue/string copies where concrete bytes are expected;
- any FFI fast path must still be typechecked and represented as a spec-compliant foreign binding.

## Required next-iteration acceptance criteria

Before the native backend is described as performance-plausible, the worker should produce at least the following:

1. A concrete plan separating quick wins from larger representation changes.
2. Direct primitive ID or direct helper calls for statically known saturated primitives, replacing string dispatch in generated hot paths.
3. A first typed-worker specialization pass for non-polymorphic first-order functions over at least `Int`, `Bool`, and `Double`, with boxed wrapper fallback.
4. No `KEnv` allocation inside simple direct worker loops when parameters can be accessed as locals.
5. Numeric constructor/variant/field IDs for generated-code fast paths, or a staged implementation with tests proving string paths are no longer used in list/tuple/record hot cases.
6. Source-faithful generated C names and/or source-span comments for local generated functions.
7. Benchmarks and tests showing the optimized path is actually exercised on representative code, not only implemented in dead code.
8. An adversarial performance review that specifically checks for remaining string dispatch, avoidable boxing, avoidable heap env allocation, and opaque generated names.

This review does not require abandoning `KValue` globally. A generic boxed representation is fine as the fallback ABI. The objection is that the current backend uses the fallback as the default even where the compiler has enough information to do substantially better.
