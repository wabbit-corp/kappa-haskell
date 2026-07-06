# Evidence-Aware IO and Var Scalarization Roadmap

Status: roadmap plan, updated after the first LLVM evidence-aware scalarizer
landing for the builtin-IO `var`/`while` subset.
Primary roadmap entry: `ROADMAP.md`, "Evidence-aware IO/var scalarization
(P0.2 restore)".

## 1. Problem Statement

S2.3b fixed mutable-variable semantics by making surface `var`, current reads,
explicit `ref` facets, and assignment elaborate through the selected `MonadRef`
evidence. That was the right semantic boundary. The performance regression was
that non-suspending scalar loops stayed represented as boxed `MonadRef` actions
and CK-machine loop nodes even when the checker already knew the selected
evidence was the builtin `MonadRef (IO e)` ref path. The first LLVM restore now
scalarizes the proven builtin-IO subset; the shared planner and C/default lane
remain open.

The old raw-ref scalarizer was unsound because it reconstructed backend refs
without proving equivalence to the selected evidence. The replacement must not
restore that mistake. It must scalarize only after a compiler-owned proof says:

- this is compiler-elaborated surface `var`, not arbitrary user `newRef`;
- the selected `MonadRef` evidence is the builtin `IO` ref evidence;
- the selected `newRef`/`readRef`/`writeRef` operations are the builtin ref
  operations selected by the checker;
- any escaping `ref x` remains a real, fresh-per-execution boundary ref, or the
  region falls back;
- the region is suspension-free, except for the non-resuming safepoint poll;
- the scalar lowering preserves source order, overflow behavior, final values,
  and boundary boxing.

The source language keeps one semantic `IO`. The backend should have multiple
representations:

```text
IO a
  -> direct no-suspend native code
  -> direct may-suspend native state machine with a heap frame
  -> CK action tree
```

The CK machine represents suspension and control effects. It must not be the
mandatory interpreter for every semicolon in a proven scalar loop.

## 2. Current State

The current Core shape is:

```haskell
data KItem
  = KVarItem Text Term Term (Maybe RefActionWitness)
      -- name, initializer value, selected MonadRef.newRef action, optional witness
  | KAssign Term Bool Term Term (Maybe RefActionWitness)
      -- ref term, monadic-rhs flag, rhs, selected MonadRef.writeRef action, optional witness
  | KBind Q CorePat Term (Maybe RefActionWitness)
      -- selected action, with optional read witness for current/ref reads
  | KWhile (Maybe Text) KCond [KItem] (Maybe [KItem])
  | ...
```

The checker builds selected `MonadRef` actions in `monadRefNewAction` and the
assignment/current-read paths. Usage already consumes checker-recognized
explicit `readRef`/`writeRef` facts through `eRecognizedRefOps`, avoiding
name-based guessing. Backends compile rejected `KVarItem`/`KAssign` regions by
running the selected action through `compileMonadicAction`; unplanned `while`
shapes lower to `krt2_while`.

That fallback is correct for unproven shapes, but it is not the performance
target for builtin-IO scalar loops. Current benchmark status after the first
evidence-aware restore:

- C/default `arithloop` remains report-only until the C/default lane has an
  evidence-aware scalarizer or the harness grows an explicit LLVM ratio lane;
- `scalar_intwhile` is the LLVM anchor and must emit an evidence-aware
  `@kscalarloop_N` worker with no hot-path `krt2_while`;
- user `MonadRef`, STM, abstract evidence, unsupported suspension/finalizer
  shapes, and non-scalar shapes remain on the selected-action fallback.

## 3. Design Contract

### Invariants

1. The checker, not the backend, proves builtin `IO` `MonadRef` identity.
2. Backend scalarization consumes a compact witness; it does not infer semantic
   equality from names, field strings, or arbitrary dictionary-shaped terms.
3. Failing to prove eligibility must produce the existing boxed selected-action
   lowering, not a partial scalarization.
4. Scalar regions are source-order preserving. Read/write reordering is illegal
   unless proven observationally equivalent under the selected evidence.
5. A `while` condition that contains lifted current reads is re-evaluated every
   iteration. The scalarizer must never freeze the condition at action
   construction time.
6. Raw integer arithmetic preserves Kappa `Int` semantics, including overflow
   escape to the boxed/GMP path.
7. Safepoints in scalar loops are non-resuming polls. A real `cede`, `sleep`,
   `await`, STM `retry`, finalizer boundary, handler operation, or blocking
   action requires a heap continuation frame and is out of the first restore.

### Non-Goals For The First Restore

- No scalarization of arbitrary user `MonadRef` instances.
- No global user-function unfolding to prove dictionary equality.
- No monad-law rewriting in the backend.
- No scalarization across `defer`, `using`, `fork`, `await`, `sleep`, `cede`,
  `throw`, `catch`, `mask`, STM, effect handlers, labels, loop `else`, or
  escaping `ref x`.
- No attempt to resume a scalar loop from C stack locals after a real park.

## 4. Representation Plan

Add checker-owned ref-action facts to Core do items.

Preferred shape:

```haskell
newtype RefCellId = RefCellId ...

data RefLoweringWitness
  = BuiltinIORefWitness
      { rlwCellId   :: RefCellId
      , rlwCarrier  :: Term
      , rlwStoredTy :: Term
      , rlwRefTy    :: Term
      , rlwDict     :: Term
      }

data RefActionWitness
  = BuiltinIORefNew RefLoweringWitness
  | BuiltinIORefRead RefLoweringWitness
  | BuiltinIORefWrite RefLoweringWitness

data KItem
  = KBind Q CorePat Term (Maybe RefActionWitness)
  | KVarItem Text Term Term (Maybe RefActionWitness)
  | KAssign Term Bool Term Term (Maybe RefActionWitness)
  | ...
```

The exact field names can change during implementation, but the key rule cannot:
the backend must be able to distinguish "checker proved builtin IO ref" from
"some term whose shape currently resembles readRef/writeRef." If Core churn is
too high, a side table is acceptable only if it is keyed by stable action
identities rather than structural child positions: keys must identify individual
action occurrences, transforms must re-key or invalidate entries, stale or
missing entries must reject scalarization, and validator/cross-check paths must
consume the same table as both native backends.

The witness is emitted only when the checker has selected the builtin
`MonadRef (IO e)` evidence. For user monads, STM, abstract evidence, wrong
carrier evidence, or unresolved/higher-order carriers, the witness is absent.
The `RefCellId` ties together the hidden cell created by `var`, generated
current-read binds, and assignments; the planner should not rediscover cell
identity by comparing arbitrary terms.

## 5. Scalar Region Eligibility

The first scalarizer recognizes a maximal surface-`var` region:

```kappa
var x = scalar
var y = scalar
while scalarCond do
    x = scalarExpr
    y = scalarExpr
use scalar locals after loop
```

Eligible region requirements:

- all mutable slots come from `KVarItem` with `BuiltinIORefNew`;
- stored types have a backend scalar representation in the current worker set
  (`Int` first; `Double` and mixed scalar slots after the basic path is stable);
- assignments to slots use `KAssign` with matching `BuiltinIORefWrite`;
- current reads lowered by the checker to selected `readRef` binds carry
  `BuiltinIORefRead` and are recognized as aliases of the scalar slots;
- a region whose ref facets escape must allocate the hidden refs while the IO
  action executes and must expose the same real `Ref` cells the generic selected
  actions would expose; otherwise escape falls back;
- loop has no label, no `else`, no `break`/`continue`/`return` in the first
  restore, and no nested suspending action;
- condition and body expressions are scalar-expressible under a small whitelist:
  literals, scalar locals, scalar lets, comparisons, arithmetic prims, and
  boundary boxing at the end of the region;
- overflow fallback reconstructs the correct boxed continuation or deoptimizes
  to the generic path without losing source-order effects.

Rejected shapes fall back to boxed `MonadRef` lowering and must stay covered by
interpreter/native parity tests.

## 6. Implementation Stages

### SCA-0: Baseline Gates And Failure Fixtures

Add or tighten tests before changing lowering:

- `scalar_intwhile` generated LLVM requires an evidence-aware scalar worker and
  no hot-path `krt2_while`.
- C/default `arithloop` remains report-only until the C/default lane scalarizes
  or the harness grows an explicit LLVM ratio lane, but its allocation and ratio
  numbers stay printed.
- Negative fixtures for user `MonadRef`, STM, wrong carrier evidence,
  unsupported escape contexts, `defer`/`using`, `cede`, `sleep`, `await`/`join`, `fork`,
  `blocking`, `mask`/explicit `poll`, `catch`/`finally`, handler operations,
  and unknown calls must prove the targeted region falls back and preserve
  output. Generated-code checks should be scoped to the named region/worker or
  planner rejection reason, not global absence of all scalar workers.
- A ref-freshness fixture must prove that a scalarized action value returning
  `ref x` allocates fresh hidden refs on each execution, not when the action
  tree is constructed or cached.
- A while-condition current-read fixture must prove the condition is re-read
  each iteration, not frozen.
- Overflow fixtures must match the boxed/GMP path, including a loop where
  overflow occurs after earlier writes and post-overflow reads prove the
  fallback continued from current scalar slot values rather than rerunning from
  original boxed inputs.
- RC-on validation must run for accepted and rejected scalar-region fixtures
  (now default-on; use `KAPPA_PERCEUS_RC=0` only for explicit whole-binary off baselines), and generated-code checks must cover dup/drop
  boundaries around scalar-region entry/exit where ownership metadata changes.

### SCA-1: Checker Witness

Teach the checker to emit `RefActionWitness` for:

- `KVarItem` created by surface `var` when `requireMonadRef` resolved to the
  builtin `MonadRef (IO e)` instance;
- `KAssign` to the same hidden cell using the same selected evidence;
- checker-generated current-read `KBind` action terms that use the same hidden
  cell and evidence.

The witness comparison must be based on resolved builtin/evidence identity or a
checker-owned canonical proof. It must not be a string comparison on `readRef`,
`writeRef`, field labels, or rendered names.

Validation:

- existing S2.3b conformance tests still pass;
- wrong-facet/wrong-carrier tests continue to reject;
- the witness is absent for user `MonadRef`, STM, and abstract dictionaries.

### SCA-2: Shared Scalar Region Planner

Create a shared planner module used by C and LLVM backends. It consumes `KItem`
plus witnesses and returns either:

```haskell
ScalarRegionPlan
  { scalarSlots     :: ...
  , scalarCondition :: ...
  , scalarBody      :: ...
  , boundaryBoxes   :: ...
  , overflowEscape  :: ...
  }
```

or a precise rejection reason for debugging/tests. The planner owns:

- ref escape/freshness checks;
- source-order read/write tracking;
- scalar expression classification;
- lifted-current-read aliasing;
- suspendability exclusion;
- overflow escape requirements.

The planner should be total and conservative. Any unsupported item returns
"fallback" with a reason.

### SCA-3: Backend Lowering Restore

Implement the scalar plan in LLVM first, because `scalar_intwhile.kp` is the
visible regression gate, then either share the same planner in C immediately or
land C in the same stage if the existing C scalar-loop code can be restored
cleanly. SCA-3 completion is backend-specific until both are restored: the LLVM
landing flips only LLVM generated-code/perf gates; the default native
`arithloop` ratio gate stays report-only until the C/default backend path also
scalarizes, or the benchmark harness grows an explicit LLVM ratio lane.

The generated loop must have:

- scalar locals/SSA values for mutable slots;
- no per-iteration `K_REF`, `readRef`, `writeRef`, `krt2_bind`, or `krt2_while`;
- a counter-gated `krt2_safepoint` poll;
- boundary boxing only when leaving the scalar region or entering overflow
  fallback;
- no change to generic boxed lowering for rejected shapes.

Initial gates:

- generated-code check: scalar worker present, no `krt2_while` on the hot path;
- allocation check: zero per-iteration allocation on non-overflow path;
- raw-C ratio gate restored for `arithloop` only on backends whose scalarizer has
  landed; start at `<= 5x` for CI stability, with a tracked target of `<= 2x`
  after the benchmark harness has repetitions and confidence intervals;
- RC-on validation and generated-code checks around scalar-region boundaries;
- interpreter, C, and LLVM outputs remain byte-identical.

### SCA-4: Bounded Action Normalizer

After surface `var` is restored, extend recognition to simple indirect uses of
selected builtin ref actions. This normalizer is checker-side or shared with the
planner, but it remains fuel-bounded and whitelist-only.

Allowed normalizations:

- strip type applications, implicit arguments, and ascriptions;
- strip eta wrappers around the selected builtin method;
- inline local lets that are pure renames of the selected action;
- project known fields from the selected builtin dictionary;
- recognize checker-generated `ioBind`/`ioPure` wrappers around lifted reads.

Forbidden:

- arbitrary user global unfolding;
- monad-law rewriting;
- assuming two dictionaries are extensionally equivalent;
- accepting on failure or fuel exhaustion.

### SCA-5: Direct No-Suspend IO Regions

Generalize beyond mutable `var` loops. A do-region that is proven no-suspend and
contains only direct builtin IO/state operations can lower as native
straight-line code with a state/fiber token rather than a CK action chain.

This stage is intentionally after SCA-3. It should reuse the same witness,
suspendability, and boundary-boxing machinery instead of creating a second
ad-hoc optimizer.

### SCA-6: Native Resumable Frames For Real Yield Points

Only after direct no-suspend regions are stable, support optional real yield
points such as explicit `cede` by spilling live scalar locals into a heap frame:

```c
typedef struct {
  int pc;
  int64_t i;
  int64_t acc;
  KEnv *env;
} KNativeLoopFrame;
```

On park, save locals and return a resumable native continuation. On resume,
reload locals and continue. This is the direct-style counterpart to CK
continuations; it is not part of the first scalarization restore.

## 7. Performance Contract

For the scalar mutable-loop class:

```text
allocations inside loop: 0
K_REF read/write inside loop: 0
krt2_bind inside loop: 0
krt2_while per iteration: 0
boxed Int allocation per iteration: 0
safepoint branch: cheap counter branch per iteration
real safepoint call: every N iterations only
```

Tiered targets:

- Tier 0: scalar numeric loops/direct imperative kernels: hard `<= 2x` target
  after the benchmark harness grows repetitions/CI; initial CI gate `<= 5x`.
- Tier 1: monomorphic first-order records/variants: scalar and field unboxing
  targets, not necessarily `<= 2x` immediately.
- Tier 2: higher-order/polymorphic code: target after specialization/evidence
  specialization.
- Tier 3: genuinely dynamic/fiber/STM/effectful code: measure honestly and
  optimize allocation/dispatch without pretending it is scalar C.

## 8. Review Checklist For Each Stage

Each scalarization stage requires adversarial review against these questions:

- Is every optimized ref operation backed by checker-selected builtin evidence?
- Are rejected shapes demonstrably falling back to selected-action lowering?
- Are source-order effects and current-read freshness preserved?
- Can any ref facet escape and leave the scalar slot unsound?
- Can any suspension point lose C stack locals?
- Does overflow exactly match boxed `Int` semantics?
- Do generated-code tests inspect the hot path, not just program output?
- Does Perceus/RC metadata still see the same ownership boundaries, or does the
  scalar region need explicit dup/drop/drop-elision facts?

The phrase to keep in mind:

```text
IO is semantically uniform but operationally stratified.
The CK machine represents suspension, not every semicolon.
```
