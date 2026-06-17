# Native Backend Raw-C Performance Review

Date: 2026-06-17
Reviewer: Codex desktop supervisor, with two independent read-only subagent reviews.
Scope: current `runtime/kappart.c`, `runtime/kappart.h`, `src/Kappa/Backend/C.hs`, generated native C under `test/native/cases/`, and existing native benchmark outputs.

## Verdict

The native backend is still not close to handwritten C for ordinary monomorphic first-order programs. It is a correct and useful boxed native runtime backend with some fast paths, but most generated code still resembles a VM/interpreter data path emitted as C:

- scalar values are `KValue *` boxes;
- worker parameters and locals are often retrieved through `KEnv` linked lists and `kvar`;
- mutable `var` is lowered to heap refs (`kref_get` / `kref_set`);
- records, constructors, and variants use generic heap objects and string-keyed dispatch/projection;
- known saturated calls and constructor applications still frequently go through closure, trampoline, or boxed wrapper machinery;
- benchmark gates check regression bounds, not small-constant-factor performance against raw C.

This is not a complaint about the fallback ABI. A generic boxed ABI is necessary for higher-order, polymorphic, partial, dynamic, and overflow/GMP cases. The problem is that the fallback ABI is still the default for simple programs where the compiler has enough information to emit scalar C locals and direct calls.

## Current benchmark evidence

One independent review ran the current native benchmarks with `KAPPA_CC="cc -O2"` and compared them to deliberately conservative handwritten C loops using volatile loop-carried state so the compiler could not fold the loops away.

Current generated native backend:

```text
arithloop  2e6: 0.49s, 289 MB allocated
tailsum    2e6: 0.26s, 193 MB allocated
recproj    1e6: 0.16s,  97 MB allocated
listfold   1e6: 2.00s, 544 MB allocated
```

Conservative raw C reference:

```text
arithloop: 0.0021s
tailsum:   0.0023s
recproj:   0.0014s
listfold:  0.050s
```

This means the scalar cases are still roughly two orders of magnitude slower than conservative C, with hundreds of megabytes of allocation in programs that should allocate little or nothing on the common path.

The rough generated-code census tells the same story. Representative generated files still contain frequent generic runtime calls:

```text
perf.kappa.c:      kpush=2  kvar=7  kref=9  kp=4  kprim_call=1
arith.kappa.c:     kpush=25 kvar=24 ktrampoline=8  kapp=8  kclo=20
loops.kappa.c:     kpush=51 kvar=49 kref=12 kapp=24 kclo=42
uhash.kappa.c:     kpush=65 kvar=65 ktrampoline=27 kbounce=8 kproj=4 krec=6
ubuilders.kappa.c: kpush=49 kvar=42 ktrampoline=18 kprim_call=23 kclo=34
```

The exact counts are not a quality metric by themselves, but they show that the generic machinery is still visible in ordinary generated code, not isolated to rare dynamic boundaries.

## P0 blockers to raw-C-like performance

### P0.1 Monomorphic numeric code is still boxed

Evidence:

- `runtime/kappart.h` defines all values as tagged `KValue` boxes.
- direct primitive helpers such as `kp_addInt`, `kp_subInt`, `kp_leInt`, and `kp_showInt` still accept and return `KValue *`.
- generated hot loops call boxed helpers and box results on every normal iteration.
- `docs/NATIVE_BACKEND_PERFORMANCE_PLAN.md` already notes `kint` result boxing as dominant, but treats typed workers as staged rather than mandatory for the current performance claim.

Why this is unacceptable:

An ordinary `Int` loop should compile to scalar `int64_t` locals plus overflow checks and a slow escape path. It should not allocate a `KValue` for each arithmetic result. The current path cannot be within a small constant factor of C while the common case boxes every scalar update.

Acceptance criteria:

- first-order monomorphic `Int`, `Bool`, and `Double` workers use scalar C params/results and scalar local lets;
- `Int` has an overflow escape to the boxed/GMP path, but the small-int non-overflow path stays scalar;
- boxing happens only at generic/higher-order/partial/data/IO boundaries or when the overflow escape is actually taken;
- tight scalar loops allocate zero `KValue`s per iteration on the non-overflow path.

### P0.2 Mutable `var` loops are heap-ref interpreter loops

Evidence:

`test/native/cases/perf.kappa.c` still lowers a simple accumulator loop to:

```c
KValue *var_1 = kref_new(kint(0LL));
KValue *var_3 = kref_new(kint(1LL));
if (!kas_bool(kp_leInt(kref_get(kvar(env_4, 0)), kint(1000000LL)))) ...
kref_set(kvar(env_4, 1), kp_addInt(kref_get(kvar(env_4, 1)), kref_get(kvar(env_4, 0))));
kref_set(kvar(env_4, 0), kp_addInt(kref_get(kvar(env_4, 0)), kint(1LL)));
```

Why this is unacceptable:

This should be two scalar locals and direct assignment. A C backend that compiles local mutation through heap cells, environment lookup, tag checks, and boxing is still running a runtime model, not generating native loop code.

Acceptance criteria:

- non-escaping monomorphic `var` lowers to C locals;
- assignment to such locals lowers to direct assignment;
- generated performance-loop C contains no `kref_get`, `kref_set`, `kvar`, or per-iteration `kint` in the optimized path;
- heap refs remain only for variables that escape into closures/thunks/IO or otherwise require identity semantics.

### P0.3 `KEnv` remains on hot paths

Evidence:

- `runtime/kappart.c` implements `kpush` allocation and `kvar` linked-list walking.
- current direct workers still build `KEnv *kw_c*` cells and use `kvar(kw_env, i)` for params/locals.
- `docs/NATIVE_BACKEND_PERFORMANCE_PLAN.md` says QW2 maps leading de Bruijn indices directly to C locals so loops touch no `KEnv`, but the generated code shows a weaker result: envs are hoisted out of some loops, not eliminated from the code path.

Why this is unacceptable:

Hoisting environment allocation out of a loop is a good quick win, but raw-C-like code should use local variables, not linked-list runtime frames and `kvar` calls.

Acceptance criteria:

- known worker params and non-escaping local bindings are represented as C locals or fixed frame slots;
- pattern-bound locals use direct local variables;
- `KEnv` is allocated only when something actually captures it, such as an escaping closure, thunk, do action, or genuinely dynamic higher-order path;
- performance reports must distinguish "env rebuild removed" from "env/kvar eliminated".

### P0.4 Records, constructors, variants, and pattern matches are generic dynamic objects

Evidence:

- `K_CTOR` stores a string name plus boxed args.
- `K_REC` stores field-name arrays plus boxed vals.
- `kctor_is`, `kvariant_is`, and `kproj` use string comparisons and linear scans.
- generated match code repeats dynamic deconstruction and allocates `KEnv` for bound fields.

Why this is unacceptable:

Closed ADTs and known records are statically available structure. Pattern matching should compile to a switch on compact tags and direct field loads. Record projection should often be fixed-offset access, not `strcmp` over field names.

Acceptance criteria:

- closed constructors/variants get numeric tags and switch lowering;
- known records/tuples get fixed layouts and offset loads;
- constructor/record names remain available for diagnostics, not dispatch;
- optimized record/ADT benchmarks contain no `kproj`, `kctor_is`, or `strcmp` on the common path.

### P0.5 Known saturated calls still carry closure/trampoline overhead

Evidence:

- first-order calls are often wrapped in `ktrampoline` even when statically known;
- mutual/local tail recursion can allocate `K_BOUNCE` per step;
- known constructor/list-building spines can still emit `kclo` + `kapp` chains before `kctor`.

Why this is unacceptable:

Trampolines are correct for stack safety at dynamic boundaries, but known first-order recursive SCCs should compile to loops/state machines. Saturated direct calls should just be direct calls. Known constructors should construct directly.

Acceptance criteria:

- direct known saturated calls bypass `kapp` and `ktrampoline` unless a dynamic/higher-order boundary requires it;
- first-order recursive SCCs lower to loops or dispatch-state loops;
- `K_BOUNCE` remains only for dynamic/higher-order tail calls;
- saturated known constructor applications lower directly, not through eta-expanded closure chains.

## P1 issues and report correctness

### P1.1 Build defaults understate the target

The build driver should use normal optimized C flags, at least `-O2`, for performance builds. This is not the dominant blocker, but a native backend performance claim should not be based on unoptimized C output.

Acceptance criteria:

- performance builds use `-O2` or an explicit configured optimization mode;
- debug builds remain available separately;
- reports state which mode was used.

### P1.2 Existing benchmark gates are regression gates, not raw-C performance gates

The current benchmark suite catches some allocation regressions, which is good. It does not prove small-constant-factor performance against C. It should not be cited as evidence that the backend is near raw C.

Acceptance criteria:

- add raw C baselines for scalar loop, tail recursion, record projection, list fold, and simple IO/bytes cases;
- track elapsed-time ratios and total allocation;
- fail scalar first-order cases when they exceed an explicit ratio threshold;
- report both native/backend and raw C numbers.

Suggested initial gates:

- scalar arithmetic and tail-recursive numeric loops: <= 5x conservative C and zero per-iteration allocation in the non-overflow path;
- fixed record projection: <= 10x conservative C and no string scans in optimized paths;
- list fold: may allocate list cells, but should not allocate closure/env/bounce boxes per element beyond the required data representation.

### P1.3 Current documentation overclaims QW2

The performance plan currently says QW2 maps leading de Bruijn indices directly to C locals so the loop touches no `KEnv`. That is not true in the current generated C. It hoists some env allocation, but generated code still uses `KEnv` and `kvar`.

Acceptance criteria:

