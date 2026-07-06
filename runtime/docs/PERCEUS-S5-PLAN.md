# Perceus Stage S5 — Implementation Plan (KCore/KBackendIR split → drop-guided FBIP reuse)

Status: **S5.A landed for native emission; S5.B native FBIP reuse is implemented in this changeset and pending final review.** S0→S4 have landed and been independently reviewed sound: precise RC with
free-on-zero is default-on, with the biased fast/slow split + shared-object reclamation (TSan/UAF-clean,
25–45% thread-local RC perf recovered). Phase A now has the native-codegen split the plan required:
erasure classification has a shared `Repr` authority; the codegen-only `quote∘force` kind-domain helper is
gone; `src/Kappa/Backend/IR.hs` defines a separate recursive `KBackendIR` tree whose lowering structurally
omits erased parameters/arguments; and the tree carries node-local ownership uses, binders, branch-dead drops,
argument conventions, and ctor/match layout facts. Native C/LLVM builds validate that tree before emission and
their main value/do lowering consumes `BackendTerm` roots rather than compiling a `Core.Term` body. The old
R-path bridge is no longer on the native emission path: backend-facing ownership is computed on KBackendIR
`BackendUseId`/`BackendBinderId` identities, and the legacy `OwnInfo`/`UseSite` table remains only as a
dump/cross-check/refinement artifact for older Perceus diagnostics. A few backend-wide planning analyses still
read `csCoreBodies` (suspendability, multishot legality, host tag collection, scalar function-worker
planning); those are explicit non-emission inputs and are not used to attach ownership facts or generate
ordinary value/do code. Landed as commit `0039ffa`. During review the split was found to have introduced one
miscompile *class* — erasing a **non-leading** field shrinks a runtime structure while pattern-match binders
(ctor `kctor_arg`, tuple `krec_size`/`krec_at`) and the polymorphic-lambda erasure fallback still used
pre-erasure indices (crash, and one silent-wrong-read case) — now **fixed** (runtime-kept reindexing) and
**gated** by native regression tests (`ctor-erased-tail-pattern`, `tuple-erased-field-pattern`,
`poly-lambda-erased-arg`); the projection path was already fixed via `runtimeRecordFieldIndex`. Three items
S5.A deliberately deferred to Phase B — A3-substrate-has-no-consumer, no-reuse-pass-yet, and physical
R-path cleanup — are enumerated as the Phase-B **entry state in §2.0** and their Phase-B status is called out
there. S5 remains the
**marquee perf lever** — drop-guided **FBIP reuse**
(Functional But In-Place; Lorenzen/Leijen 2022), the rbtree allocation-reduction class of win whose
literal `std::map` speed target is representation-gated (§4). **Decision
(recorded):** S5 is done **split-first** — the KCore/KBackendIR split lands as Phase A, then the FBIP reuse
pass as Phase B on the typed IR. Companion to [PERCEUS-RC-DESIGN.md](PERCEUS-RC-DESIGN.md) §3 (the reuse
pipeline) and [KCORE-KBACKENDIR-SCOPING.md](../../docs/KCORE-KBACKENDIR-SCOPING.md) (the Phase A design).

## 0. Why split-first (the decision)

Full FBIP needed three things the pre-S5.A single-`Term` + path-keyed side-table could not cleanly provide,
and all three are what the KCore/KBackendIR split now supplies or makes explicit:
1. **Typed constructors** — the reuse pass matches a dropped cell's size against an allocated ctor's size;
   for cross-ctor and (future) unboxed/mixed layouts the size ≠ arity, so it needs the ctor **type + size /
   representation class** (§34.3.7), not a runtime tag-sniff.
2. **Stable ownership keys** — the reuse pass consumes drop-liveness + runtime-uniqueness facts. Those are now
   backend-facing KBackendIR node/binder identities, not the old **path-keyed** ownership table
   (`Ownership.hs`). Threading reuse tokens through the old fragile path bridge would compound the R-path risk
   that has been the recurring highest-rated hazard of the whole arc; S5.A removes that bridge from native
   emission before FBIP starts.
3. **A materialized erasure/representation lowering** — so the backend reads node fields instead of
   re-deriving (`isKindDomainValueAt`'s `quote∘force`, `argConvSelect` re-walks, …; ~69 sites).

The alternative — *basic same-footprint match-local reuse on the side-table* (the rbtree win, faster payoff) —
was **not** chosen: split-first does S5 **once, cleanly**, retires R-path, and the split independently unblocks
**LLVM-RC** and the **layout/unboxing** program, so it is one foundational investment serving three levers.

**Non-negotiable — the split's product is a *separate tree IR*, not an annotated `Term`.** The whole value of
split-first evaporates if KBackendIR is materialized as a wrapper that carries the KCore `Term` with facts
bolted on the side (a `bbTerm :: Term` + `[Bool]` erasure masks + a path-keyed ownership bridge — i.e. the
former A2a scaffold). That is a *fact side-table wearing an IR's name*, and it is non-conformant: §34.3 says
the erased forms (`Type u`, row/label terms, region vars, quantity-`0` binders, proof terms, erased indices)
**do not appear in KBackendIR** and that every backend **lowers from** KBackendIR — a `Term` wrapper leaves
every erased node physically in the tree and leaves the emitter generating code from `Term`, so it satisfies
neither. It is also self-defeating: erased nodes remain, so the §34.3.3 legality verifier proves nothing, and
every consumer written against the wrapper is rewritten a second time when the real tree lands. KBackendIR
MUST be its **own recursive datatype** whose lowering **deletes** erased positions and carries
ownership/representation **as node fields**; the observe-only lowering is permitted **only** as a temporary
differential scaffold (A2a) that is deleted by A2c. The precise obligations are in §A2.

## 1. Phase A — the KCore/KBackendIR split (S5's prerequisite; also the LLVM-RC + layout enabler)

**What "the split" is.** A compiler lowers a program through a series of intermediate representations (IRs).
The spec mandates three of them: **KFrontIR** (post-parse, name-resolved), **KCore** (the *typed* kernel — the
fully elaborated, type-checked program), and **KBackendIR** (the *lowered* backend IR, produced from KCore by
discharging erasure and selecting runtime representations). Before S5.A, Kappa collapsed KCore and KBackendIR
into a **single** Haskell `Term` type, and carried the erasure/ownership metadata the backend needed in a
**side-table keyed by structural paths** — a pragmatic shortcut that diverged from that mandated pipeline
(§28/§30.2/§31.2/§34.3; the full argument is in
[KCORE-KBACKENDIR-SCOPING.md](../../docs/KCORE-KBACKENDIR-SCOPING.md)). The split makes the implementation
match the spec: a typed KCore, and a separate, field-annotated KBackendIR produced by an explicit lowering
pass. Migration, staged with gates — each **byte-identical / RC-neutral**, exactly like the Perceus stages:

- **S5.A0 — thread the erasure classification (stop re-running the type normalizer during code generation).**
  *The problem:* the backend must know, for each argument/binder, whether it is **runtime-erased** (a type, a
  kind, or a `0`-quantity/proof argument — it carries no value at run time and must be dropped from the
  generated code) or **runtime-relevant** (a real value). Before S5.A0 it re-computed this *at code-generation time*
  in `isKindDomainValueAt`, which calls `quote (force v)` — it runs the normalization-by-evaluation engine
  (evaluate a term to a semantic value, then read that value back into a term) inside the emitter, purely to
  inspect whether the argument's type is a `Type`/kind. That is the type-checker's own machinery re-run in the
  wrong phase (this is the "`quote∘force`" — a `quote` composed with a `force`). *The fix:* the elaborator
  already made exactly this classification while type-checking (an argument is erased when its quantity is `0`
  or its domain is a kind); carry that single bit forward as a per-binder annotation and **delete
  `isKindDomainTerm` / `isKindDomainValueAt`**, so the backend reads the annotation instead of re-deriving it.
  Cheap (one already-computed bit), no structural refactor. Gate: byte-identical output; the re-derivation
  count (§A2) drops; the old codegen-only `isKindDomainValueAt` `quote`/`force` readback is gone from the
  emitter.
- **S5.A1 — stable KCore identities; re-key the ownership metadata (retire the "R-path" risk).**
  *The problem:* the Perceus ownership metadata (which `dup`/`drop` to emit; whether a binder's last use is a
  consuming move or a borrowing read) originally lived in a **side-table keyed by a value's structural
  position** — a *path* of child-indices from the function's root node. If the producer and consumer walks ever
  disagreed about a child position — one counted a node the other skipped — facts could be missed or attached
  to the wrong node. That failure class is what we call **"R-path,"** and it was the highest-rated hazard of
  the RC arc (the S2.3d review's "silent branch-drop-site lookup miss" was one concrete instance). *The fix:*
  native emission now computes backend-facing ownership directly on the lowered KBackendIR tree and stores it
  on node-local `BackendUseId`/`BackendBinderId` identities. The legacy `OwnInfo` table may still be rendered
  or cross-checked, but it is not reattached to KBackendIR and not consulted by C/LLVM emission. Once the
  emitted tree carries the identity, the "both walks must agree on every position" fragility cannot exist on
  the native path. **This is the highest correctness value in the plan.** Gate: byte-identical; RC-on ==
  RC-off; deleting/tampering with `csOwnership` does not change validated native KBackendIR emission.
- **S5.A2 — materialize KBackendIR as a *separate, typed tree IR* (NOT a `Term` wrapper).**
  *The problem:* before S5.A2, a single Haskell `Term` type (`Core.hs`) served as *both* the typed core *and* the
  backend IR, and for backend purposes it is effectively **untyped** — constructors (`CCtor`) and matches
  (`CMatch`) carry no type — so the backend keeps **re-deriving** facts the type-checker already knew: is this
  argument erased? what is the callee's owned/borrowed/shared calling convention? what is a constructor's
  field layout? Roughly **69 sites** across `Repr`/`C`/`LLVM`/`Ownership`/`Usage` re-compute such facts, each
  a little differently.

  *What KBackendIR MUST be (normative — §34.3, §31.2, §28.456).* KBackendIR is a **distinct recursive
  datatype** — its own set of runtime-only node constructors (`data KBackendIR = KBApp … | KBLam … | KBCtor …
  | KBMatch … | KBLet … | …`), the last backend-independent IR — **not** a record that carries a KCore `Term`
  with fact-maps beside it. Three properties the spec *requires*, none of which a wrapper can satisfy:
  1. **Erasure is discharged structurally — erased nodes are ABSENT, not flagged.** §34.3 enumerates what
     "do not appear in KBackendIR": universes / `Type u`, row and label terms, raw trait-obligation type
     expressions, region variables, `FreshNomScope` tokens, `captures(...)` structure, **quantity-`0`
     computational binders / fields, proof-only terms, and erased dependent indices.** §34.3.1's `ERASURE`
     stage says *eliminate* them. A wrapper that keeps `bbTerm :: Term` leaves every one of those nodes
     physically in the tree and merely records a `[Bool]` mask beside them — so `Type u` and Q0 binders *do
     appear* in that "KBackendIR," in direct violation. The only representation under which "X does not appear
     in KBackendIR" can be *true* is one whose lowering **builds new nodes that omit the erased positions**:
     an erased constructor argument is simply not a `KBCtor` field; an erased binder is simply not a `KBLam`
     binder.
  2. **The backend LOWERS FROM KBackendIR — it must not read `Term`.** §34.3: *"Every standardized backend
     profile lowers from KBackendIR."* §28.456: the backend MUST NOT bypass KBackendIR. An observe-only facts
     artifact that leaves `C.hs`/`LLVM.hs` walking `Core.Term` + a path-keyed side-table is exactly such a
     bypass — the facts are *observed*, but the *code is still generated from `Term`*. Conformance requires the
     emitters to take the KBackendIR **tree** as their input and never pattern-match `Core.Term`.
  3. **Ownership + representation live AS FIELDS ON THE NODES — no side-table, no path keys.** The erasure /
     audit metadata §31.2 requires is *"keyed by binder identity"*; representation classes (§34.3.7) are
     properties of a node. In a real tree, a `KBApp` *contains* its argument conventions, a binder node
     *contains* its `BinderOwn`, a match arm *contains* its drop set, a `KBCtor` *contains* its resolved
    layout. There is no `Map [Int] BackendNodeId`, no `boiCompat*`/`boiMissing*` bridge, no `gsPath`. This is
    what finally **retires R-path**: A1 mints the stable identities; A2 makes each identity *the node itself*
    rather than a key into a parallel map that a second walk must reconstruct.

  *Why a wrapper is a dead end, not a pragmatic first step.* Every consumer written against `bbTerm` + fact-
  maps must be **rewritten again** when the real tree lands — the wrapper does the work twice, not less. And
  until it is replaced, the §34.3.3 legality verifier is asked to prove "no runtime term depends on an erased
  occurrence" *over a tree that still contains every erased occurrence* — so it proves nothing. The wrapper is
  strictly worse than doing it right once.

  *Staging (the differential scaffold is allowed; shipping it AS the IR is not).*
  - **A2a — the differential scaffold (temporary; now retired).** The observe-only wrapper was allowed only as
    a means to compute the erasure / convention / layout / ownership decisions and **differentially check**
    they reproduced the legacy path's decisions across the corpus — the same backstop discipline that
    de-risked S2→S3. It was scaffolding, not KBackendIR, and no emitter logic may be written against it.
  - **A2b — define the real tree and make the emitter consume it.** Introduce `data KBackendIR` with
    runtime-only nodes; write the KCore→KBackendIR lowering that **omits** erased positions and **fills** the
    ownership / convention / layout node fields; port `C.hs` (then `LLVM.hs`) to pattern-match the new nodes.
    The real tree, lowering, fail-closed tree validator, and main native emitter consumption are in place.
  - **A2c — delete the scaffold.** Remove `bbTerm`, the `[Bool]` erasure masks, `bbNodeIds` /
    `boiCompat*` / `boiMissing*`, and the path-keyed ownership producer/bridge from native emission. The
    §34.3.3 legality verifier now runs over a tree from which erased nodes are genuinely absent, so it is
    meaningful; the §34.3.4 KBackendIR graph dump and §34.3.6 interpretation stand on a self-contained tree.

  (This is the same move GHC makes lowering typed Core to STG — STG is its own datatype, not annotated Core —
  and it is what §28 / §30.2 / §31.2 / §34.3 already require.) *Gate:* byte-identical; conformance/parity; **the
  main value/do emitter consumes KBackendIR and performs no structural-path ownership lookup**; any remaining
  `Core.Term` reads are explicit non-emission planning inputs; the §34.3.3 KBackendIR legality checkpoints
  green *on a tree with no erased nodes*.
- **S5.A3 — representation classes on KBackendIR nodes (each value's run-time layout).**
  *What it is:* a value's **representation class** is how it is physically laid out at run time — a boxed heap
  pointer, an unboxed scalar in a register, a bit-packed small constructor, a niche, and so on (§34.3.7, and
  the representation rules of §31.2.1/§31.3/§31.4/§31.5). *Why S5 needs it:* the FBIP reuse pass (Phase B) may
  reuse a just-dropped cell for a new constructor only when the two are the **same size in bytes**, and size
  is a property of a constructor's *type/representation*, not of its name alone (a boxed k-field constructor
  and a hypothetical unboxed variant of the same arity differ in size). S5.A therefore carries ctor
  **type + representation metadata** on constructor/match nodes, including a validated
  `CtorLayoutInfo.clBoxedFootprintBytes` value when the current runtime representation may allocate a boxed
  constructor cell (`Nothing` for immediate-only nullary ctors, and `sizeof(KValue) + arity * sizeof(KValue *)`
  for allocating layouts). This is **metadata only** in Phase A: no emitter consumes the footprint, no
  allocation/drop pair is rewritten from it, and no same-size reuse discriminator exists yet. The delivered
  gate is deliberately narrower: constructor layout/type facts are carried and validated on constructor
  allocation nodes and match/destructure nodes; Phase B must thread those facts onto concrete
  drop/reuse-token candidates and build the discriminator before performing a same-size reuse.

Validation mirrors the Perceus arc (byte-identical / RC-on==RC-off / conformance / parity through every
sub-stage). **A0 + A1 deliver most of the re-derivation + R-path relief before the full KBackendIR type
lands**, so the risk is front-loaded-cheap.

## 2. Phase B — drop-guided FBIP reuse (S5 proper)

### 2.0 Entry state and current Phase-B progress

S5.A (landed, commit `0039ffa`) delivered the *substrate* Phase B consumes but deliberately stopped short of
reuse itself. Three items were explicitly deferred at the S5.A hand-off and are **Phase B's** to close:

1. **A3 is substrate, not a consumer until B adds the consumer.** The representation metadata exists and is
   validated on ctor/match nodes: `CtorLayout` is three-way (`LayoutImmediate | LayoutMayPack | LayoutBoxed`,
   `Repr.hs`), `CtorLayoutInfo` carries field reps plus `clBoxedFootprintBytes`, and the validator checks that
   footprint against `ctorBoxedFootprintBytes arity = 48 + 8·arity`. B0/B1's discriminator is the first
   consumer: it must read `CtorLayoutInfo` from the KBackendIR node, fail closed when the metadata is missing
   or non-allocating, and compare the validated boxed footprint before reusing a cell. The current C/native
   first site now does this for direct match-local constructor rebuilds; generalized credit threading still
   has to reuse the same node facts rather than re-sniffing tags or arity.
2. **First reuse sites vs generalized reuse.** B0/B1 now have runtime primitives (`kdrop_reuse_ctor` /
   `kreuse_ctor`, plus the fused/early-token helpers) and conservative C/native pass sites: an unguarded
   S2.3 match-destructure drop paired with a direct same-size constructor allocation in the same arm; moved
   constructor fields that eliminate the old dup/drop pair; the boxed recursive list-map shape where a
   unique cons cell moves its payload/tail through the arm before being rewritten; a rbtree-shaped recursive
   n-ary node rebuild; and the rbtree-insert path-copying shape where owned path cells transfer through
   direct worker calls into same-frame reuse. These are real reuse and are gated by
   `perceus-s5-reuse-direct`, `perceus-s5-reuse-move`, `s5_listmap_reuse`, `s5_rbtree_reuse`,
   `s5_rbtree_insert_reuse`, and the runtime primitive harness. The literal Koka-style
   rbtree-insert-vs-`std::map` speed comparison is carried as a **tracked report**, not an S5.B acceptance
   gate: the allocation/reuse gates prove the mechanism; *beating* `std::map` additionally needs the unboxed
   value representation and tighter layout/scalar paths for the residual boxed dispatch overhead (see §4) and
   is deferred to the representation/unboxing program. FBIP makes the proven rebuild operation allocation-free,
   but the current boxed benchmark fixture still has setup/result allocation and reports ≈1.3× slower today.
3. **Physical R-path cleanup.** Native value emission was already fully off the old path-keyed bridge —
   `C.hs`/`LLVM.hs` read no `csOwnership`/`OwnInfo` side table when attaching ownership facts. Phase B now
   also physically retires the leftover structural-path ownership producer: `Ownership.hs` uses deterministic
   owner-local ordinals for its observe-only binders, uses, and branch-drop sites; the obsolete child-position
   numbering module has been removed from the build; and KBackendIR lowering no longer bridges
   path→node identity. The ownership dump/cross-check/refinement artifact can still exist, but it cannot
   silently reintroduce R-path by reusing old structural keys.

**What FBIP does.** When a program pattern-matches a data structure and immediately rebuilds a same-shaped
one — the classic case is an in-place-looking update such as `Cons h t → Cons h' t`, or a red-black-tree
rotation — the old cell is about to be freed and a new, same-size cell is about to be allocated. If the old
cell is **uniquely owned** (no other reference points at it), we can **reuse it in place** — overwrite its
fields — instead of freeing it and `malloc`ing a fresh one. A unique k-field rebuild then costs **0
allocations + k field stores** instead of `malloc` + k stores + `free`. This is the reuse pipeline of
RC-DESIGN §3; it runs *after* dup/drop insertion and is **frame-limited** (explained below).

- **The reuse pass (on KBackendIR).** Find a `drop(x)` of a constructor cell that is followed, in the **same
  function-body region** (the same frame/branch), by an `alloc(C, fields)` of a **same-size** constructor, and
  fuse the two into `token = drop_reuse(x); y = reuse_alloc(token, C, fields)`. "Same size" is read from the
  S5.A3 representation class — a compile-time fact, not a run-time tag inspection. The natural first site is
  exactly the S2.3a **match-destructure drop** (the earlier stage that drops a matched scrutinee's cell once
  its fields have been read out) paired with a same-size constructor built in the match arm.
- **The runtime primitives** (`kappart.h`/`value.c`):
  - `drop_reuse(x)` → if `x` is **uniquely owned** (its thread-local reference count is exactly `1` **and** it
    is not marked shared — see §3) return the cell pointer `&x` *without freeing it*; otherwise perform a
    normal `kdrop` (which may free it) and return `NULL`.
  - `reuse_alloc(token, C, fields)` → if `token` is non-NULL, write `C`'s tag and fields **into that cell in
    place** (zero allocation) and reset its header to a fresh unique reference count of `1`; if `token` is
    NULL, `malloc` a new cell (`kctor`) as usual.
- **Drop specialization + dup/drop fusion** (the middle of the pipeline). Once a constructor's shape is known
  statically (which is exactly what the typed KBackendIR provides), a generic `drop` can be **specialized** —
  inlined into direct drops of its known children — and a `dup` immediately followed by a matching `drop` of
  the same value can be **cancelled** (they net to nothing). On a path the compiler can prove is uniquely
  owned, the reference-counting operations then **disappear entirely** rather than executing at run time.
- **Why it's "frame-limited."** In-place reuse is only sound when the `drop` and the `alloc` sit in the same
  function-body region *and* the reuse token (a raw cell pointer) **does not escape**: it must not be handed
  to a callee that could store it, and there must be no suspension or call in between that could hand `x` a
  second reference. The FBIP calculus tracks the **reuse credits** available within a frame (written `◇ₖ` in
  the literature — essentially an accounting of "how many free same-size cells are in hand right here") and
  only fuses a reuse where a matching credit is live.

## 3. The correctness crux — reuse ONLY a unique cell

- Reusing a still-aliased cell overwrites storage another reference reads ⇒ corruption/UAF. `drop_reuse`'s
  `rc==1` check is the **sole** guard.
- **Composes with S4's biased split for free.** S4 marks any value that has crossed a fiber boundary — been
  handed to another lightweight thread via `fork`, a promise, a `TVar`, etc. — as **shared** (a bit in its
  header, `KRC_SHARED_BIT`), and shared values use *atomic* reference counting and are never treated as
  uniquely owned. So the reuse uniqueness test — thread-local `rc==1` **and** the shared bit clear —
  automatically excludes every shared cell: `drop_reuse` returns `NULL` for a shared value, so shared cells
  are **never** reused and stay on the normal (atomic) reclamation path. In effect the S4 shared bit is
  *already* the concurrency guard for reuse — a cell another fiber can still observe can never be overwritten
  in place under it, with no extra machinery.
- **Reused-cell hygiene**: the match already `kdup`'d the kept fields (S2.3a); `reuse_alloc` overwrites the
  slots with the new fields and resets `rc=1`. Ensure no double-free of the old children and no leak of the
  reused cell's prior contents (the fields the arm does not carry forward are dropped exactly once).
- **Frame-limited / non-escaping**: the pass restricts reuse to a drop+alloc in the same frame/branch with a
  non-escaping token (a reused cell handed to a callee that stores it while the original path still uses it
  would alias) — the R-frame-escape guard.

## 4. Verification

1. **Correctness under the poison detector (primary).** The *poison-on-free detector* is the debug UAF oracle
   built for S3.2: with `KAPPA_POISON=1` a reclaimed cell is stamped with a `K_FREED` sentinel (and leaked
   rather than returned to the allocator) so that any later read of it traps deterministically. Applied to
   S5, a reuse of a *non-unique* cell would overwrite a cell another reference still reads → that read traps.
   Build the corpus RC-on with `KAPPA_POISON=1`; the `rc==1` guard + the shared-bit exclusion + the frame
   discipline must keep it clean.
2. **Byte-identical output** — reuse must not change behavior: reuse-on == reuse-off, and RC-on == RC-off.
3. **ThreadSanitizer (TSan) — the S4 concurrency gate continues.** Reuse composes with the biased split;
   shared cells are never reused, so there is no new data-race surface — the existing TSan run over the
   concurrency corpus (fork/promise/STM/atomic/fiber-ref) must stay clean.
4. **The reuse mechanism is the S5.B gate; the `std::map` speed target is representation-gated.** RC-DESIGN
   §3's headline is Koka's rbtree insert ≈ 19% faster than hand-tuned C++ `std::map` — but that is Koka's
   result *with its full unboxed value representation*, not FBIP alone. On Kappa's current uniform-boxed
   `KValue` representation, FBIP removes **allocation** but the tree loop still pays boxed-value and layout
   overhead that `std::map`'s inline-`int` / fixed-offset-load loop avoids (even where the native backend now
   uses direct proven slots and fast integer compares). Empirically, after FBIP **plus some additional
   unboxing** the insert fixture's hot reuse path is **allocation-free but ≈1.3× slower** than `std::map` — the residual is boxing/dispatch, a
   *different lever* (the representation / unboxing / layout program, coupled with the LLVM backend), which no
   reuse pass can close. **S5.B's hard gate is therefore the mechanism**: boxed list-map, rbtree-shaped
   recursive rebuilds, and rbtree insert must show positive reuse counts, RC-on allocation reduction,
   poison/TSan cleanliness, and byte-identical output. The literal cross-language `std::map` speed comparison
   is **carried as a tracked report**, not an acceptance gate: a reuse-proven run that is still slower than
   `std::map` is the *expected* state until unboxing lands, **not** an S5.B blocker. **Koka's ≈19% figure is
   likely out of reach for now without more unboxing**; that target moves to the representation program's
   acceptance, not FBIP's.
5. Conformance / parity / underflow-clean through both phases.

## 5. Risks

- **R-reuse-nonunique (highest).** Reusing an actually-aliased cell ⇒ UAF. Guarded by the runtime `rc==1`
  check + the shared-bit exclusion + the frame-limited non-escaping token; poison + TSan catch a violation.
- **R-size-mismatch.** The token size must equal the alloc size — the S5.A3 rep class provides it; the pass
  fuses only same-size drop/alloc. A mismatch ⇒ a reused cell too small/large ⇒ corruption.
- **R-frame-escape.** A token escaping its frame (stored by a callee; reused across a suspension). The pass
  restricts to same-frame/branch, non-escaping tokens.
- **R-shared-reuse.** A shared cell reused ⇒ concurrency UAF. Prevented by the shared-bit exclusion (shared ⇒
  never unique ⇒ never reused).
- **R-wrapper-nonconformance (Phase A — highest *design* risk).** Materializing KBackendIR as an annotated
  `Term` wrapper / observe-only facts artifact (a `bbTerm :: Term` + `[Bool]` erasure masks + a path-keyed
  ownership bridge) is **non-conformant** — §34.3 says the erased forms it enumerates MUST NOT appear and the
  backend MUST lower *from* KBackendIR — **and self-defeating**: erased nodes stay in the tree so the §34.3.3
  legality verifier proves nothing, the emitter still generates from `Term`, and every consumer is rewritten
  twice. This is the failure mode the split exists to avoid. Mitigation: A2 mandates a distinct recursive
  datatype whose lowering *deletes* erased positions and carries ownership/representation as node fields; the
  observe-only lowering is a **differential scaffold only** (A2a), no emitter logic is written against it, and
  it is deleted by A2c (`bbTerm` / masks / native path bridge gone).
- **R-split-regression (Phase A).** The KBackendIR refactor is large (≈586 `CVar` sites, the interp, both
  backends). Mitigated by the incremental A0→A3 staging + the byte-identical gates; A0/A1 front-load the
  cheap, high-value relief.

## 6. Sub-stages, ordering, gates

| sub | what | gate |
|---|---|---|
| **S5.A0** | thread the erasure classification; delete `isKindDomain*`/`quote∘force` | byte-identical; re-derivation sites shrink |
| **S5.A1** | move backend-facing ownership onto stable KBackendIR node/binder identities | byte-identical; RC-on==RC-off; R-path class retired from native emission; `csOwnership` tampering does not affect codegen |
| **S5.A2a** | differential scaffold: observe-only lowering computes erasure/conv/layout/ownership, checked vs the legacy path | retired; it was never the deliverable |
| **S5.A2b** | define `data KBackendIR` (separate tree; erased positions omitted; ownership/rep as node fields); port `C.hs`/`LLVM.hs` to consume it | real tree + fail-closed validator + main native emitter consumption landed; byte-identical; §34.3.3 legality green |
| **S5.A2c** | delete the scaffold: `bbTerm`, `[Bool]` masks, `bbNodeIds`/`boiCompat*`/`boiMissing*`, the path-keyed ownership bridge from native emission | wrapper scaffold is gone; KBackendIR lowering no longer reattaches `oiBranchDropSites`; legacy `Ownership.hs` remains observe/cross-check only |
| **S5.A3** | representation metadata (ctor type, packing class, field reps, validated boxed-footprint metadata) on KBackendIR nodes | ctor layout facts are carried and validated on ctor/match nodes; same-size reuse-site discrimination remains Phase B |
| **S5.B0** | runtime `drop_reuse`/`reuse_alloc` + the S4-aware is-unique check; **become the first A3 consumer** — read `CtorLayoutInfo.clBoxedFootprintBytes`/packing class from the KBackendIR node as the same-size discriminator (§2.0 item 1) | landed for boxed constructor cells as `kdrop_reuse_ctor` / `kreuse_ctor` plus fused/early-token helpers; runtime harness covers unique reuse, aliased/shared rejection, arity mismatch, packed-immediate fallback, moved-field fallback, and reuse counting |
| **S5.B1** | the reuse pass (match-destructure drop + same-size arm alloc) — closes §2.0 item 2 (first actual reuse) | C/native direct-arm site landed and is gated; reuse remains restricted to direct same-arm constructor rebuilds |
| **S5.B2** | drop specialization + dup/drop fusion | landed for direct moved constructor fields and for early-token unique branches where consumed old fields are moved through the arm; unproven/fallback paths keep the conservative dup/drop sequence |
| **S5.B3** | the reuse perf gate + poison/TSan over the corpus | **acceptance:** list-map, rbtree-shaped n-ary rebuild, and rbtree insert reuse gated with poison, RC-on==RC-off output, positive reuse counts, and RC-on allocation reduction. **Tracked report (NOT acceptance):** the ≈19%-vs-`std::map` comparison — representation-gated (FBIP makes the proven rebuilds allocation-free but the full boxed fixture remains ≈1.3× slower today; beating `std::map` needs the unboxing program, see §4). Koka's ≈19% is likely out of reach without more unboxing and moves to the representation program's gate |
| **S5.B4** | finish the physical R-path retirement (§2.0 item 3): re-key the observe-only `Ownership.hs` producer away from structural paths and delete the unused child-position module | landed: native emission remains off the path-keyed bridge; `Ownership.hs` binders/uses/branch-drop sites are owner-local ordinals; no residual structural-path producer remains; byte-identical |

Ordering rationale: Phase A must precede Phase B (the reuse pass reads typed ctor sizes + stable ownership);
within A, the cheap high-value relief (A0/A1) lands first; within B, the runtime primitive + first A3 consumer
and a single proven site (B0/B1) precede the general specialization (B2) and the perf gate (B3). B4 is now
done, so future reuse-token work has no structural-path ownership producer to accidentally reattach.

## Critical files

- `src/Kappa/Core.hs` (the typed KCore) + `src/Kappa/Backend/IR.hs` — the latter now holds the separate
  recursive `data KBackendIR` lowering (runtime-only nodes; erased positions omitted; ownership/rep as node
  fields). C/LLVM now consume the lowered tree for main emission. *Not* a `Term` wrapper — see §A2.
- `src/Kappa/Ownership.hs` — observe-only dump/cross-check/refinement ownership table, now keyed by
  deterministic owner-local ordinals rather than structural child paths. It is no longer reattached to
  KBackendIR for native codegen; FBIP reuse facts are computed on KBackendIR identities (B).
- `src/Kappa/Backend/C.hs` / `LLVM.hs` — consume KBackendIR fields (retire the re-derivation sites). C/native
  currently emits the initial `drop_reuse`/`reuse_alloc` fused site; LLVM still keeps runtime RC
  counting/freeing disabled and must grow ownership maintenance before it can participate in S5 reuse.
- `runtime/kappart.h` / `runtime/value.c` — `drop_reuse`/`reuse_alloc` + the S4-aware is-unique check; the
  in-place ctor rebuild.
- `test/native/run-native-tests.sh` — the rbtree perf gate; reuse-on==reuse-off; the poison/TSan corpus.

## Spec anchors

- **RC-DESIGN §3** (the drop-guided reuse pipeline, FBIP, drop specialization / dup-drop fusion, the rbtree
  target) and **§7** (S5 in the staging).
- **KCORE-KBACKENDIR-SCOPING.md** (the Phase A design + migration; the spec pipeline **§28 / §30.2 / §31.2 /
  §34.3**).
- **§34.3.7** (representation classes and specialization), **§34.4.1** (memory-management obligations).
