# Effect-Handler Unification on the kappart2 CK-Machine (`KK_HANDLER`) — Scoping

Status: scoping / design-of-record consolidation. This document scopes CPS-DESIGN
Stage 4 — replacing Kappa's pure free-monad effect kernel with a runtime
`KK_HANDLER` prompt frame on the existing kappart2 CK-machine. It is grounded in
five subsystem studies (current-eff, ck-machine, spec, prior-art, cps-design-plan)
and verified against current `runtime/rt.c`, `runtime/internal.h`,
`runtime/docs/CPS-DESIGN.md`, `src/Kappa/Eval.hs`, `src/Kappa/Check.hs`, and
`src/Kappa/Usage.hs`.

The honest one-line summary: this is the **single highest-risk runtime feature**
on the roadmap, but the substrate is unusually well-prepared — the hard
prerequisite (R1) is landed, the compile-time safety gate is already built, and
the two "hard" operations (perform/resume) are generalizations of code that
already exists. The one-shot path is **moderate**; multi-shot is where the real
risk lives, and it is correctly gated behind a capability that does not yet exist.

---

## 1. What `KK_HANDLER` unification concretely means for kappart2

### 1.1 Today: two disconnected worlds

Kappa already has a **complete, type-checked, running** algebraic-effect system —
but it is realized as a **pure free-monad tree rewrite** with no scheduler handle.
There is no runtime handler; perform/resume never touch the CK-machine's `Cont`
chain.

- `Eff : EffRow -> Type -> Type` is an opaque carrier (`Prelude.hs:104-110`).
  Effect rows are `__effRowCons label iface rest` / `__effRowNil`
  (`Prelude.hs:106-110`, `Builtins.hs:388-389`).
- Two constructors represent a computation: `__EffPure v` (`KCT_EFFPURE = 9`,
  finished) and `__EffOp label op payload cont` (`KCT_EFFOP = 10`, a suspended
  operation carrying a **re-entrant captured continuation** `cont`)
  (`Builtins.hs:382-385,671-672`; `runtime/kappart.h:81`;
  `runtime/kappart.c:308-309`).
- There is **no** `perform`/`resume` keyword. "perform" is the operation
  selection `label.op` — a first-class value `argTy -> Eff <[label:iface]> resTy`
  elaborated by `effOpSelection` (`Check.hs:7737-7779`), which builds
  `__EffOp label op payload (\r -> __EffPure r)` with the identity continuation
  (`Check.hs:7767-7775`). "resume" is just **applying** the clause's bound
  continuation binder `k` as an ordinary function (`Parser.hs:3194-3206`).
- `handle` / `deep handle` parse to `EHandle deep lbl scrut cases`
  (`Parser.hs:1651-1652,3162-3172`); `elabHandle` (`Check.hs:7802-7930`) emits
  `__handleEff deep label retLam opsRecord scrut` (`Check.hs:7919-7925`).
- Execution is a pure `KValue`-tree rewrite, **identical** in the Haskell
  interpreter (`Eval.hs:1053-1138`: `__effBind`, `__handleEff`, `runPure`) and the
  native runtime (`kappart.c:559-622`: `kpf___effBind`, `kpf___handleEff`,
  `kpf_runPure`). Neither touches `Fiber*`, `f->k`, `deliver`, `unwind`, or the
  scheduler. The C backend lowers the three prims to `kpf_runPure` /
  `kpf___effBind` / `kpf___handleEff` (`Backend/C.hs:1948-1950`); `Interp.hs` does
  not special-case `Eff` at all.

Separately, the **kappart2 CK-machine** is a stackless, heap-reified free-monad
interpreter: a fiber is `f->cur` (current action `KValue`) plus `f->k` (a
singly-linked `Cont` chain on the GC heap; `internal.h:133-139,164-165`). One
worker steps one fiber at a time via the flat `fiber_step` loop (`rt.c:623`). It
has a real M:N scheduler with fork/await/sleep/STM parking — but `Eff` cannot
reach any of it.

### 1.2 The gap

Because `__handleEff` is a pure 5-arg prim with no `Fiber*`, a handler clause
**cannot park, cede, await, fork, or do any real IO/STM** — it can only rewrite
the tree. `Eff` effects compose with each other but are walled off from the
fiber/IO/STM runtime (CPS-DESIGN R11, line 289; §line 51). Second, because
`elabEffDo` (`Check.hs:7952-8031`) accepts **only** `DoExpr`/`DoBind`/`DoLet`/
trailing-`DoIf` and rejects every other do-item via `unsupportedAt`
(`Check.hs:8027-8030`), an `Eff` do-block can never contain `defer`/`using`/`var`/
loop. So the captured `cont` carries **zero exit-action frames** and the spec's
abandonment guarantee (§32.2.19/.20/.21) is structurally unimplementable for
`Eff` today — this is the SPEC_COMPLIANCE §32.2.19/.20/.21 gap
(`SPEC_COMPLIANCE.md:101`, "medium").

### 1.3 The unification

`KK_HANDLER` unification means: **stop running effects as a separate pure engine
and run them as prompt frames on the one `Cont` chain.** Concretely, on the
CK-machine:

- A **handler** (`handle`/`deep handle`) installs a `KK_HANDLER` prompt frame on
  `f->k` carrying the installed `(label → handler-clause table)`.
- **perform** `label.op payload` is an *outward search* of `f->k` for the nearest
  `KK_HANDLER` whose installed label matches — structurally identical to how
  `unwind` already searches for `KK_CATCH` on `RK_FAIL`. The **delimited
  continuation between the perform site and that handler** — the `Cont` sub-chain
  including any crossed `KK_DOSCOPE`/`KK_FINSEQ` frames and the `mask_depth` — is
  reified as the resumption `k`, and the handler clause runs with `(payload, k)`.
- **resume** `k v` *splices* that saved sub-chain back onto `f->k` and `deliver`s
  `v` — O(1), reusing `krt2_bind`/`kclo`, no copy.

The decisive structural fact: the `Eff` free-monad tree (`__EffPure`/`__EffOp` +
re-entrant `cont`) is the **same defunctionalized algebraic-effect term** as the
runtime `krt2_bind` `Cont` chain with a reified resumption. This is a
**unification, not a greenfield engine** (CPS-DESIGN §1/§2/§8).

---

## 2. The design

### 2.1 The closest-fit model (prior-art)

Across the five prior-art families — (1) native stack-segment (OCaml 5), (2)
evidence-passing / yield-bubbling (Koka), (3) the original handler calculus
(Eff/Frank, Hillerström & Lindley CK/CEK), (4) multi-prompt delimited control
(shift/reset, named prompts), (5) C stack-copying (libhandler/libmprompt) — the
fit for kappart2 is:

> **Family (4) multi-prompt delimited control as the operational model + family
> (2) evidence-passing as the lookup/representation model, realized as ONE
> `KK_HANDLER` prompt frame on the existing heap `Cont` chain.**

This is exactly the Hillerström & Lindley CK-machine handler treatment and what
CPS-DESIGN §2/§3.2/§8 already chose. It fits because the substrate is *already* a
heap-reified delimited-continuation machine: capturing a `Cont` sub-chain is a
linked-list slice, one-shot resume is a pointer move (matching the destructive-pop
discipline already in `deliver`/`unwind`), and mask/do-scope/loop frames ride the
**same** chain, so a captured resumption automatically carries the correct
finalizer/mask frames.

**Rejected for kappart2, with reasons grounded in the code:** native
stack-segment (OCaml 5) and C-stack-copying (libhandler/libmprompt) both fight a
future Perceus precise/moving collector — live pointers sit in opaque native-stack
images at compiler-chosen offsets a moving GC cannot relocate without per-frame
stackmaps — and under today's **Boehm conservative GC** (`GC_MALLOC`,
`kappart.c:45`) thousands of suspended stacks would pin everything. A heap `Cont`
sub-chain is ordinary GC-walkable data (CPS-DESIGN §8).

### 2.2 The `KK_HANDLER` prompt frame

The current `Cont` frame is `{KKind kind; KValue *a; void *aux; void *aux2;
Cont *next;}` (`internal.h:133-139`) and `KKind` has exactly 10 kinds today,
**none** is `KK_HANDLER`:

```
KK_DONE, KK_BIND, KK_THEN, KK_CATCH, KK_POPMASK, KK_SETMASK,
KK_DOSCOPE, KK_FINSEQ, KK_LOOP, KK_RETSCOPE              (internal.h:124-132)
```

`KK_HANDLER` is added as an 11th kind. Following the existing field convention
(e.g. `KK_DOSCOPE` uses `aux`/`aux2` for ExitStack pointers, `internal.h:135-137`),
it carries:

- the installed `(label → handler-clause table)` — the label value and the
  `onReturn` + per-op clauses;
- the deep-vs-shallow flag (reinstall-on-resume);
- the `mask_depth`/scope snapshot needed at capture (or this rides on the crossed
  frames; see §2.4).

The frame is **singly-linked and refcount-free** like every other `Cont`
(`internal.h:133-139`) — fine for one-shot; the constraint multi-shot must break
(§2.6).

### 2.3 `perform` = a resumable generalization of `unwind`

`unwind` (`rt.c:551-610`) is a `for(;;)` that walks **outward** popping frames
until one handles the reason. The `KK_CATCH`/`RK_FAIL` arm is the exact template
(`rt.c:574-575`):

```c
case KK_CATCH:
  if (rkind == RK_FAIL) { f->k = c->next; f->cur = kapp(c->a, rval); return 1; }
```

`perform` walks `f->k` outward for the nearest `KK_HANDLER` whose installed label
matches the op's label. Two differences from `unwind`:

1. Matching is by **exact effect-label IDENTITY (value)**, nearest dynamically
   enclosing handler — not source spelling, not interface name (spec §18.1.18
   lines 19362-19378; §30.2.2.7 line 33103). The handler-frame search compares
   label values.
2. **Crucially, `perform` CAPTURES the popped sub-chain instead of discarding
   it.** Today `unwind` only ever *drops* frames (`f->k = c->next`, frame
   discarded) or terminates the fiber — there is **no** code path that severs a
   sub-chain and hands it back as a first-class value. This is the **one
   genuinely new primitive** (~20 lines): "capture from the op site up to (and
   excluding) the matching `KK_HANDLER`." It is a linked-list slice — set the
   captured tail's terminator and re-root `f->k` at the handler frame — no new
   continuation datatype (CPS-DESIGN §3.2.8 line 96: "the de Bruijn KEnv is the
   captured environment; f->k is the reified continuation").

This realizes spec `OpCall` (§30.2.2.7 lines 33065-33127): intercepted by the
nearest dynamically enclosing `HandleShallow` for the exact label; `k` is the
captured computation suffix from the OpCall site to that handler boundary
(§32.2.13).

### 2.4 `resume` = a deliver-splice

`resume k v` re-links the saved `Cont*` tail onto `f->k` and feeds `v`. The model
is `deliver`'s `KK_BIND` arm (`rt.c:516-517`):

```c
case KK_BIND: f->k = c->next; f->cur = kapp(c->a, v); return 1;
```

This is precisely "splice a continuation closure and feed it a value" — O(1),
reusing `krt2_bind`/`kclo`, no copy (CPS-DESIGN §2 line 46). The resume **payload
is always quantity-1**; multi-shotness reuses/duplicates `k`, never the payload
(spec §18.1.16 lines 19299-19303; §30.2.2.7 line 33109).

Because the captured sub-chain *includes* the crossed `KK_DOSCOPE`/`KK_FINSEQ`/
`KK_POPMASK`/`KK_SETMASK` frames, a resumed computation re-enters under the same
do-scope/exit-action/mask state that held at capture (spec §32.2.13 lines
35222-35243; re-enter under captured mask state, 35237-35238). The kappart2 fiber
already tracks masking + exit-action stacks (`internal.h:143`), so the resumption
snapshots/shares those by riding the chain rather than reconstructing them.

### 2.5 Deep vs shallow

Surface `deep handle` is **not** a distinct primitive — the spec desugars it to an
internal recursive driver over `HandleShallow` (§30.2.2.7 lines 33120-33123;
§18.1.22 lines 19722-19735). So **one** `KK_HANDLER` frame type plus a
reinstall-on-resume flag suffices: deep `k` first resumes the captured shallow
continuation, then **reinstalls the same deep handler** around the resumed
computation (spec §32.2.22 lines 35425-35433); shallow handlers do **not**
auto-reinstall (§18.1.21 lines 19616-19617). This matches the reference oracle:
`Eval.hs` `__handleEff` deep `k` self-reinstalls via `reinstall cont`
(`Eval.hs:1107-1118`); non-matching labels propagate outward with the handler
reinstalled inside the resumption (`Eval.hs:1112-1115`).

### 2.6 One-shot vs multi-shot, and the `rt-multishot` escape-check

This is the central gate.

**Spec rules:**
- Resumption quantity `q` quantifies the binding `k` itself, not the payload (spec
  §18.1.16 lines 19294-19301). Omitted annotation ⇒ `q = 1`, i.e. **one-shot by
  default** (§18.1.17 line 19311). Classes: abortive `q=0`, one-shot `q≤1 ∧ q≠0`,
  multi-shot `q>1` (§18.1.17.1 lines 19345-19347). **Multi-shot is NEVER inferred
  — it must be declared explicitly** (19320-19321).
- Runtime realization (§32.2.14 lines 35246-35257): one-shot MAY be destructive;
  multi-shot MUST be persistent — "every use of the resumption value must behave
  as if it resumed from the same captured control state."
- `rt-multishot-effects` (spec §27.6 lines 28539-28542) = persistent multi-shot
  resumption + logical cloning of captured segments + §32.2.16 storage/reclamation
  obligations. Native `zig`/C+LLVM SHOULD advertise it (28566-28572).
- A backend **without** the cap MUST **reject** any reachable multi-shot
  invocation and any exported decl that may invoke one, at compile time —
  diagnostic family `kappa.feature.gated`, code
  `E_FEATURE_BACKEND_CAPABILITY_MISSING` (§18.1.17 19322-19325; §34.3.3
  37890-37893; hard error at §3.1.x line 1863). What does **not** need the cap:
  one-shot ops, abortive ops, shallow handlers, deep handlers, and
  tail-resumptive one-shot clauses (§18.1.17 19326-19327; §28561-28562).

**Two compile-time escape-checks relieve the runtime of dynamic guarding:**
1. **Call-site capture rule** (§18.1.20 lines 19451-19473): for a multi-shot op,
   EVERY runtime-relevant captured value (live locals, borrows, partially-consumed
   owned paths, active do-scope frames, pending exit-action obligations) MUST be
   duplicable and free of borrow-lifetime obligations, else compile fails at the
   op-site. So the runtime clone is always sound.
2. **Abandonment escape restriction** (§32.2.20 lines 35370-35374): a resumption
   whose captured segment contains PENDING EXIT ACTIONS MUST NOT escape its
   clause; compile fails (impl MAY conservatively reject when it cannot prove the
   segment is exit-action-free).

**Major readiness finding: this escape-check is ALREADY IMPLEMENTED** in
`src/Kappa/Usage.hs`, which CPS-DESIGN treats as future work:
- `multishotOpCall` (`Usage.hs:2086-2095`) detects a call to a `QOmega`/
  `QAtLeastOne` (multi-shot) op.
- `walkItems`/`DoBind` (`Usage.hs:2147-2155`) runs the §18.1.20 call-site capture
  rule over the captured suffix.
- `checkMultishotCapture` + `captureKind` (`Usage.hs:2264-2286`) reject
  (`E_QTT_CONTINUATION_CAPTURE`) any captured value that is a borrowed binding or
  a quantity-1/at-most-once binding.
- `countedQ` (`Usage.hs:2076-2081`) encodes §18.1.21/§32.2.20 (a one-shot
  resumption may be abandoned without use; declared quantity 1 counts as
  at-most-once).
- `Check.hs:7470` notes the discipline "is enforced statically";
  `Check.hs:7577` sets the §18.1.17 one-shot default (`eoiQ = ... Q1`).

So the multi-shot line item reduces from "design+build an escape-check" to
**"wire the existing `E_QTT_CONTINUATION_CAPTURE` analysis to an `rt-multishot`
capability gate."**

### 2.7 Abandonment (the spec-mandated guarantee Stage 4 must finally deliver)

A clause may complete **without** resuming `k` (including abortive `q=0` clauses).
If `k` does not escape, abandonment happens immediately and the runtime MUST
(§32.2.20 lines 35358-35377; worked example §32.2.21 lines 35380-35422):

- unwind the captured do-scope frames **exactly once**;
- run their pending exit actions in **MASKED LIFO** order (same as ordinary scope
  exit);
- NOT roll back heap state or effects before the op site;
- for multi-shot, each logical clone carries its OWN pending exit obligations.

Hard requirement (§32.2.21 lines 35421-35422): an impl MUST NOT realize abortive
clauses by simply dropping the captured segment without unwinding its captured
exit actions.

On the CK-machine this **falls out of the existing `unwind` path** through
`KK_FINSEQ` — which now runs masked (R1, §3.1). So the abandonment guarantee is
**free on the one-shot path** because it routes through the already-fixed
`KK_FINSEQ`/`KK_POPMASK` drain — *but only because R1 landed; do not regress R1.*

### 2.8 Reused vs new CK-machine machinery

**Reused (already present):**

| Machinery | Location | Role for handlers |
|---|---|---|
| Outward frame search | `unwind` for-loop `rt.c:551-610`; `KK_CATCH`/`RK_FAIL` arm `rt.c:574-575` | `perform` walks `f->k` for nearest matching `KK_HANDLER` |
| Splice + value-feed | `deliver` `KK_BIND` arm `rt.c:516-517` | `resume k v` |
| Masked finalizer drain | `begin_finseq` `rt.c:486-506` (R1, landed) | abandonment runs captured defers exactly once, masked |
| Closure/env seam | `kclo`/`KEnv`/`kpush`/`kvar`/`kapp`/`kctor` `kappart.h:440-460,514-519` | box the captured resumption; no new datatype |
| Park/wake | `OP_FORK`/`AWAIT`/`SLEEP`/`ATOMICALLY`; `krt2i_wake` CAS `rt.c:286-300` | scheduler is already a built-in prompt in all but name |
| Strong root set | `rt->all` `internal.h:251-252` | keeps a captured resumption GC-reachable across a park |

**New (must be built):**

| Item | Where | Size |
|---|---|---|
| `KK_HANDLER` kind + handler-table field | `internal.h:124-132` | small |
| `OP_PERFORM`/`OP_RESUME`/`OP_HANDLE` opcodes + `krt2_*` builders | `internal.h` OP enum; `rt.c` (mirror `rt.c:54-164`) | small, mechanical |
| **Capture-sub-chain primitive** (sever op-site→handler) | `rt.c` | ~20 lines, genuinely new |
| `deliver`/`unwind` arm for `KK_HANDLER` | `rt.c:510`/`rt.c:551` | small |
| `rt-multishot` capability string | `rt.c:17` | trivial |
| Persistent / copy-on-resume `Cont` spine + ExitStacks | `rt.c` `deliver`/`unwind` | **large, semantic** (multi-shot only) |

Verified absent: grep across `runtime/*.c,*.h` finds **zero** `KK_HANDLER` /
`OP_PERFORM` / `OP_RESUME` / `prompt` / `delimited`; `KRT2_CAPABILITIES`
(`rt.c:17-18`) = `{rt-core, rt-parallel, rt-shared-stm, rt-blocking, rt-atomics,
NULL}` — **no `rt-multishot`** (confirmed against current `rt.c`).

---

## 3. Done vs. to-build

### 3.1 Already done (do NOT re-budget)

- **R1 — masked finalizer drains** (the stated Stage-4 dependency) is
  **CONFIRMED LANDED** in current `rt.c`, contradicting CPS-DESIGN's stale
  "required fix" framing (§3.2 item 3, §4 CORRECTION banner, §9 R1). `begin_finseq`
  (`rt.c:486-506`) pushes a `KK_POPMASK` beneath the `KK_FINSEQ` and does
  `f->mask_depth++` (`rt.c:499-500`) for the full drain; the mask is restored
  exactly once on BOTH the normal path (`KK_FINSEQ` done → `apply_reason` descends
  through `KK_POPMASK`, verified in `deliver` `rt.c:539-543`) and the abnormal/
  abandonment path (`unwind` through `KK_FINSEQ`). `COVERAGE.md:56` confirms
  "finalizers run masked." **The §2.7 abandonment guarantee is therefore
  satisfiable.** The only R1 residual is failing-finalizer cause-composition via
  §32.2.12 `Then` (`rt.c:602-604`, "a remaining refinement") — small and
  orthogonal to handler park/abandon.
- **Other Stage-0 prereqs landed:** `OP_DEFER` fails closed (`rt.c:761-769`,
  `krt_fail` on null `cur_exits` — R10); `KK_POPMASK`/`KK_SETMASK` restore the
  mask on both `deliver` (`rt.c:522-527`) and `unwind` (`rt.c:568-573`).
- **The compile-time escape-check** (multi-shot gate) is already built in
  `Usage.hs` (§2.6) — `multishotOpCall` / `checkMultishotCapture` / `countedQ`
  with `E_QTT_CONTINUATION_CAPTURE`.
- **The full surface + type system** for effects works: `effect` decls, rows,
  `handle`/`deep handle`, op-selection, one-shot default. The carrier-agnostic
  `elabHandle` (`Check.hs:7802-7930`) already eliminates into either `Eff
  residual` or a non-`Eff` carrier like `IO e` (`Check.hs:7846-7858`).
- **The reference oracle** for differential testing exists and matches the target
  semantics: `Eval.hs` `evalEffPrim`/`__handleEff` (`Eval.hs:1053-1131`),
  including the deep-handler `reinstall` (`Eval.hs:1107-1118`) and multi-shot
  (re-entrant closure `cont`).

### 3.2 To build — runtime (`rt.c`/`internal.h`)

1. `KK_HANDLER` kind + handler-table field (§2.2).
2. `OP_PERFORM`/`OP_RESUME`/`OP_HANDLE` opcodes + `krt2_*` builders (§2.8).
3. The **capture-sub-chain** primitive — the one genuinely new ~20-line piece
   (§2.3).
4. `deliver`/`unwind` arms for `KK_HANDLER`.
5. (Multi-shot, later) persistent/copy-on-resume spine + per-clone ExitStacks +
   `rt-multishot` capability string.

### 3.3 To build — elaborator / backend

- **Lift `elabEffDo`'s rejection of `defer`/`using`/`var`/loop**
  (`Check.hs:8027-8030`) **in LOCKSTEP** with the runtime work. Until `Eff`
  do-blocks can carry exit-action frames, there is *nothing for the abandonment
  path to unwind* and the §32.2.20 masked-LIFO guarantee cannot even be
  exercised. Scope these together (current-eff study, anchor 2).
- **Backend emits `OP_PERFORM`/`OP_HANDLE`/`OP_RESUME` nodes** in place of
  `kpf___effBind`/`kpf___handleEff`/`kpf_runPure` (`Backend/C.hs:1948-1950`) for
  computations that must run on the scheduler. The pure prims and their
  interpreter twins remain the OLD path and must stay **observationally equal** to
  the new runtime path (differential oracle, §3.1).
- **Add `perform` to the §3.3 suspendability witness** (a perform whose handler
  may park = may-suspend) — confirm with the backend lane.
- **Wire the existing `E_QTT_CONTINUATION_CAPTURE` analysis to the `rt-multishot`
  capability gate** (§34.3.3 legality check) — NOT a from-scratch build (§2.6).
- **Multi-shot KBackendIR witness:** multi-shot sites must record a
  backend-capability witness in the KBackendIR dump (spec §34.3.4 line 37929) and
  pass the §34.3.3 legality gate; lowering must preserve the §34.3.9
  optimization-stability invariants (e.g. "multi-shot MUST NOT be optimized into a
  one-shot destructive continuation"; "two uses MUST NOT share an already-advanced
  state", spec lines 38071-38073).

---

## 4. Staged plan

Recommended ordering matches the universal field consensus (OCaml 5, WasmFX,
libhandler all ship one-shot first; Koka specializes tail-resumptive) and
CPS-DESIGN §7 Stage 4.

### Stage 4a — `KK_HANDLER` + perform/resume, ONE-SHOT only

**Scope:** add the frame, the three ops + builders, the capture-sub-chain
primitive, the `deliver`/`unwind` arms; install the scheduler as the always-on
built-in prompt and user effects as additional `KK_HANDLER` frames; lift the
`elabEffDo` do-item restriction; rewire the C backend to emit the new nodes.
One-shot resume is a destructive pointer move — exactly how `f->k` already works
(destructively popped everywhere; `g_done` shared sentinel `rt.c:323`).

**Effort:** MODERATE (the bulk of the *self-contained* work; mostly mechanical
plus one new ~20-line primitive, all in `rt.c`/`internal.h` + the lockstep
elaborator change).

**Risk:** MEDIUM. The mechanics are generalizations of existing code. The
abandonment guarantee is free here because R1 landed. Main risk is the
**elaborator/runtime lockstep** (§3.3) and keeping the new path observationally
equal to `Eval.hs`.

**Done-when:** differential-test harness holds the runtime path observably equal
to `Eval.hs` `__handleEff` for one-shot + abortive + deep + shallow, including the
§32.2.21 abort worked example (both `using` release and `defer` run exactly once
in masked LIFO before `pure 0` is observable; post-op-site `useResource r` NOT
run).

### Stage 4b — tail-resumptive fast path

**Scope:** a clause that resumes `k` exactly once, in tail position, without
storing/escaping/duplicating it, runs **in place** without reifying the `Cont`
(spec §32.2.15 lines 35260-35281). This keeps effectful loops constant-depth and
is the overwhelmingly common handler shape. This is where RESEARCH.md's
evidence-passing instinct is right — preserved as a *specialization on top of* the
unified machine.

**Effort:** SMALL–MODERATE.

**Risk:** LOW–MEDIUM. Must still preserve exact label matching, shallow-vs-deep
reinstallation, and ALL defer/using/exit obligations (§32.2.15); §34.3.9 forbids
applying the optimization merely because local control is a jump — source
resumption quantity stays authoritative.

**Test the doc must mandate** (CPS-DESIGN §4 line 132): the captured-resumption
splice must not grow `f->k` unboundedly across repeated perform/resume cycles —
**assert constant `Cont` depth**, mirroring the per-iteration-doscope
loop-growth test.

### Stage 4c — MULTI-SHOT, behind `rt-multishot`

**Scope:** add the `rt-multishot` capability string (`rt.c:17`); wire the existing
`E_QTT_CONTINUATION_CAPTURE` gate to it; make `deliver`/`unwind` **copy-on-resume**
— the `f->k` spine AND each `KK_DOSCOPE` ExitStack become persistent rather than
destructively popped, and each logical clone carries an independent pending-defer
set (CPS-DESIGN §4 line 170; spec §18.1.20.1, §32.2.16, §32.2.19). This is the
ocaml-multicont/libmpeff clone model realized as a **`Cont`-sub-chain copy** (not
a native-stack copy), so it stays Perceus-compatible: multi-shot = dup the
resumption closure.

**Effort:** LARGE.

**Risk:** **HIGHEST.** This is a **semantic change to `deliver`/`unwind`**, not a
flag. Today's destructive-pop discipline and in-place-grown mutable ExitStack
(`internal.h:143`; `exitstack_push` `rt.c:356-364`) make a naive second resume
**unsound**. Each clone must re-run post-resume effects/allocs anew and own a
copied exit-action stack; abandoning one clone must not discharge another's
(§32.2.16 35296-35299; §32.2.18 store-not-rolled-back; §32.2.19). §34.3.9 bars
sharing an already-advanced continuation state across two uses.

### Cross-cutting risk that spans all stages: handler-clause **parking**

The single hardest item is giving a handler clause (or a resumption it triggers) a
real scheduler handle so it can `park`/`await`/`fork`. Today it provably cannot —
`__handleEff` is a pure 5-arg prim with no `Fiber*` (CPS-DESIGN §2 line 53, R11
line 289). The `Cont`/`kclo`/`KEnv` seam is the right attach point and the park
protocol (`rt.c:413-424,449-463`) applies unchanged with the captured resumption
kept GC-reachable via `f->k`/`rt->all` — but the design explicitly does **not**
rule out a continuation-representation revision surfacing here. **This capability
jump, not the tree mechanics, is where the real uncertainty lives.** It is
exercised the moment a Stage-4a handler clause performs IO under the scheduler.

---

## 5. The load-bearing decision: unify vs. two-world

There is a **direct contradiction** between two repo design docs the scoping must
resolve:

- **`runtime/docs/RESEARCH.md` §2 (lines 39-63):** kappart2 "is family (B)
  [evidence-passing] already" via `KCT_EFFOP`/`KCT_EFFPURE` + `__effBind`/
  `__handleEff`; "the Cont stack carries only IO control (do NOT unify)." Proposes
  a SEPARATE `K_RESUME { Cont* suffix; DoScopeFrame* scopes; MaskState mask;
  uint8_t shots }` gated as `rt-multishot-effects`.
- **`runtime/docs/CPS-DESIGN.md` §2 (lines 37-53), §8:** the OPPOSITE — unify onto
  ONE `Cont` substrate with a single `KK_HANDLER` frame; reject "two continuation
  worlds" as duplicating mask/scope/finalizer logic.

**Recommendation: resolve toward the unified `KK_HANDLER` substrate, with the
tail-resumptive / no-IO fast path preserved as a recognized specialization** (the
Koka tail-resumptive optimization layered on the multi-prompt machine — Stage 4b).
The two-world position's strongest argument — pure/tail-resumptive effects with no
IO segments never touch the scheduler and stay a cheap closure rewrite — is **fully
honored by Stage 4b**, so we lose nothing by unifying the *substrate*. The
unification's decisive argument: the **moment a handler clause must PARK**, two
worlds need an impedance match and you re-derive mask/scope/finalizer logic twice.
Since that park capability (§4 cross-cutting) is the whole point of running effects
on the scheduler, paying for two worlds is a false economy. This decision is
load-bearing for the entire stage — state it explicitly up front.

---

## 6. Recommendation

**Proceed, one-shot-first, on the unified `KK_HANDLER` substrate — but treat
multi-shot as a separate, later, capability-gated project, not part of the initial
landing.**

Rationale, honestly weighted:

1. **The substrate is unusually ready.** The hard prerequisite (R1 masked
   finalizer drains) is landed and verified in current `rt.c` — do **not** accept
   any plan that re-budgets it. The compile-time multi-shot safety gate is already
   built in `Usage.hs`. The two "hard" operations are generalizations of `unwind`
   (`rt.c:551`) and `deliver`'s `KK_BIND` arm (`rt.c:516`). The reference oracle
   (`Eval.hs`) exists for differential testing.

2. **One-shot is genuinely moderate** and self-contained in `rt.c`/`internal.h`
   plus a lockstep elaborator change. It delivers the §32.2.19/.20/.21 abandonment
   guarantee that is currently *structurally absent* for `Eff`
   (`SPEC_COMPLIANCE.md:101`) — real spec-compliance progress — and unlocks
   handler clauses that do real IO/STM, which the pure kernel can never do.

3. **Multi-shot is the real risk and is correctly walled off.** It is a semantic
   change to `deliver`/`unwind` (copy-on-resume), behind a capability
   (`rt-multishot`) that does not yet exist, gated by an escape-check that does.
   Do not let it be scoped as "a flag." It can land later without blocking the
   one-shot value.

4. **The one true wildcard is handler-clause parking** (§4). It is not a tree
   mechanic; it is the scheduler-handle integration that the pure prim never had,
   and the only place the design admits a possible continuation-representation
   revision. Build Stage 4a with a concrete parking handler test from day one so
   this surfaces early, not at multi-shot time.

Suggested sequencing: **4a (one-shot + abandonment + parking smoke test) →
differential-test gate against `Eval.hs` → 4b (tail-resumptive, assert constant
`Cont` depth) → 4c (multi-shot) as a distinct follow-on.** Land the R1
cause-composition refinement (`rt.c:602-604`) opportunistically; it is orthogonal.

Net: this is the highest-risk runtime work on the board, but it is **well-scoped,
well-prepared, and de-riskable by staging.** Recommend proceeding with one-shot
first.
