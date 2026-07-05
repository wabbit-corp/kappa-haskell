# KCore / KBackendIR split — scoping

**Verdict up front.** Splitting the compiler's single `Term` into a typed **KCore** and a lowered,
representation- and ownership-annotated **KBackendIR** is the right move — and, crucially, it is **not a new
architecture to invent**: the spec *already* mandates this exact pipeline. The current implementation, in
which one Haskell `Term` (`src/Kappa/Core.hs`) serves as both the typed core and the backend IR while a
path-keyed side-table (`src/Kappa/Ownership.hs`) carries much of the ownership metadata, is a pragmatic
**divergence from the normative pipeline**. S5.A0 started paying this down by moving erased-argument
classification to the shared `Kappa.Backend.Repr` authority, and S5.A2b has now replaced the old observe-only
wrapper scaffold with a **separate recursive `KBackendIR` tree** in `src/Kappa/Backend/IR.hs`: erased
parameters/arguments are structurally absent, ownership/layout facts live on nodes, and native C/LLVM builds
now fail closed if the lowered tree is missing required node-local facts. The native emitters' main value/do
lowering consumes those `BackendTerm` roots directly, and backend-facing ownership is computed on
`BackendUseId`/`BackendBinderId` identities instead of being reattached from the legacy path-keyed `OwnInfo`
table. The remaining divergence is narrower: a few backend-wide planning analyses still read `csCoreBodies`
(scalar worker eligibility, suspendability, host tag collection), but those are explicit non-emission inputs
rather than ownership or value-emission side tables.

Companion to [PERCEUS-RC-DESIGN.md](../runtime/docs/PERCEUS-RC-DESIGN.md) (RC wants the real KBackendIR),
the "representation is LLVM layout" thread, and the scoping notes
[SPECIALIZATION-SCOPING.md](SPECIALIZATION-SCOPING.md) / [LAZINESS-SCOPING.md](LAZINESS-SCOPING.md).

## 1. What the spec already mandates (normative — this is the spine of the argument)

The spec defines a **three-artifact pipeline** and forbids bypassing it. §27/§28 (backend profiles):

> The backend MUST NOT lower directly from Kappa surface syntax in a way that bypasses **KCore, KBackendIR,
> erasure, quantity/region discharge, representation selection, or KBackendIR legality checking.**

- **KFrontIR** (§34.2) → **KCore** (§30.2) → **KBackendIR** (§34.3) → target. These are distinct, named,
  conformance-visible artifacts (§34.1.5A typed dump schema; §34.3.4 KBackendIR graph dumps + legality
  witnesses).
- **KCore is the *typed* kernel.** It carries types, **stable semantic-object / binder identities**
  (§30.2.5, and §1.2 "typed compiler artifacts, not stringly-typed compilation": identities are typed, not
  positional/string), **places and path operations** as first-class (§30.2.2.1), and **erasure
  justifications** — §30.2.3A: *"Every KCore occurrence that is absent from runtime representation because of
  erasure MUST carry, or be associated with, an explicit erasure justification."* Proof-relevant transport
  MAY survive in KCore and is normalized away *before* KBackendIR (§10.x).
- **Erasure (§31.2) is the KCore→KBackendIR lowering step.** *"Lowering from KCore to KBackendIR occurs only
  after the erasure obligations of this section have been discharged (§34.3)."* It deletes `0`-quantity /
  `RuntimeErased` / compile-time / capture-annotation / `Type u` / quantity / region / row / label
  occurrences. A **KBackendIR legality verifier MUST reject** a runtime term that refers to erased
  `Type`/`Universe`/`Quantity`/`Region`/row/label/proof/… except through a specified runtime carrier
  (§31.2, §34.3.3 lowering legality checkpoints).
- **The §31.2 mandatory-erasure audit trail** is the exact mechanism the ownership side-table implements —
  but note *how* the spec says to key it: *"an erasure audit table keyed by KCore **node identity, binder
  identity, argument identity, field identity, or generated-origin identity**."* Stable identities, not
  structural positions.
- **Representation selection is normative KBackendIR content**, not backend guesswork: variant `TagId`
  (§31.3, stable content-addressed member identity), record canonicalization (§31.4), mutable-state / `var`
  elision — i.e. the scalarization work (§31.5), inhabitant-driven representation elision (§31.2.1), and
  **representation classes and specialization** (§34.3.7). Memory-management obligations (where Perceus RC
  lives) are §34.4.1.

So the pipeline the question proposes — *typed KCore that preserves types; a separate KBackendIR after
erasure + representation selection* — is **verbatim what §28/§30.2/§31.2/§34.3 already require.**

## 2. Where the implementation diverges

- **Historically, one `Term` played both KCore and KBackendIR.** That shape was effectively untyped for
  backend purposes — `CCtor` and `CMatch` carried no type — and had **no stable backend binder identities**;
  binders were addressed positionally. S5.A replaces this on the native emission path with a separate
  recursive `KBackendIR` tree.
- **Erasure is materialized in the lowered tree and consumed by the main native emitters.** S5.A0 introduced a
  shared semantic erasure classifier and S5.A introduced a recursive `KBackendIR` lowering that omits erased
  parameters/arguments.
- **Native ownership is node-local.** `Ownership.hs`'s `OwnInfo` remains a spec-*permitted* historical audit /
  dump table keyed by structural paths, but C/LLVM emission no longer consumes or reattaches it. The lowered
  tree computes uses, consuming-last-use facts, borrowed-result dependencies, and branch-dead drops on
  KBackendIR identities.
- **Consequence:** the backend still has some **explicit planning analyses** over KCore — especially scalar
  worker eligibility and suspendability — but ownership/layout facts for ordinary value/do emission now live
  on KBackendIR nodes.

## 3. Why it matters now (the symptoms compound, and block the roadmap)

- **The re-derivation tax grows every Perceus stage.** Each new stage that remains on untyped `Term` +
  side-tables is tempted to re-walk facts instead of reading a lowered field. S5.A0 removed the worst
  codegen-only kind-domain readback; the same consolidation needs to continue for ownership/layout consumers.
- **The R-path risk was the highest-rated Perceus risk**, and it existed on the native path only because
  ownership facts were positionally keyed. S5.A retires that class for C/LLVM emission by computing ownership
  on the lowered KBackendIR tree. The legacy path-keyed table can still drift, but that is now a dump /
  cross-check issue, not a native dup/drop emission issue.
- **The representation-layout program is blocked on this.** Unboxing / niche layout / `TagId` / `var`
  scalarization are §31.2.1/§31.3/§31.4/§31.5/§34.3.7 — *representation selection*, whose home is KBackendIR
  nodes. "Representation is LLVM layout" + "CCtor/CMatch carry no type" is exactly this gap.
- **S5 FBIP reuse needs typed constructors** (ctor type *and size* for `drop-reuse` / same-size in-place
  rebuild). It cannot be done cleanly on the untyped side-table.

## 4. What "KCore preserves types" should mean here (scope it so it doesn't balloon)

Not a second full dependently-typed kernel annotated on every node. The KCore *side* already is typed
(that's the elaborator's output); the work is to make the **KCore→KBackendIR lowering real** and have
KBackendIR carry, **as first-class node data**, the backend-relevant facts the lowering computes once:

1. **erased-vs-runtime** per binder / argument / field (the §31.2 classification) — replaces `isKindDomain*`
   and the `quote ∘ force`;
2. **owned / borrowed / last-use ownership** (§12.2, "quantities are ownership-only" §12.2.7) as node
   fields — replaces the path-keyed side-table and retires R-path;
3. the **scrutinee / constructor type + representation class** (§34.3.7) — unblocks layout + FBIP;
4. the **arg convention** (already derivable from the callee type) precomputed, not re-walked per call site.

KCore keeps types, **stable binder / semantic-object identities** (§30.2.5), and erasure justifications
(§30.2.3A). The lowering discharges erasure (§31.2), selects representation (§31.2.1/§31.3/§31.4/§31.5,
§34.3.7), and emits KBackendIR whose §31.2 audit trail is keyed by those **stable identities**, not paths.
This is the GHC Core→STG shape, but here it is the *spec's own* KCore→KBackendIR shape.

## 5. Migration path (incremental; each step independently validatable, like the Perceus stages)

- **Step 0 — landed.** The erasure classification (`0`-quantity ∨ kind-domain) now has a shared semantic
  classifier in `Kappa.Backend.Repr`, and the codegen-only `isKindDomainTerm` / `isKindDomainValueAt`
  readback helper is gone. First brick.
- **Step 1 — stable backend identities; remove the native path bridge (landed for C/LLVM).** Backend-facing
  ownership now lives on `BackendUseId`/`BackendBinderId` identities in the lowered tree. This retires the
  R-path risk class for native emission and makes the S2.3d "silent lookup miss" irrelevant to codegen.
- **Step 2 — materialize KBackendIR as a *separate tree IR* (not a `Term` wrapper).** A **distinct recursive
  Haskell datatype** (`data KBackendIR = KBApp … | KBCtor … | …`) produced by an explicit KCore→KBackendIR
  lowering that **deletes** the erased positions (§34.3: `Type u`, row/label terms, region vars, `0`-quantity
  binders, proof terms, erased indices **do not appear**; §34.3.1 `ERASURE` *eliminates* them) and carries
  erasure/ownership/arg-convention/representation **as node fields**. The backend's main value/do emitter then
  **lowers from KBackendIR** (§34.3 "every backend profile lowers from KBackendIR"; §28 must-not-bypass),
  pattern-matching the tree for ownership-bearing codegen rather than reading `Core.Term` or doing a
  structural-path ownership lookup; the re-derivation sites collapse.
  - **Why not an annotated `Term` wrapper (`bbTerm :: Term` + `[Bool]` masks + a path bridge).** It is
    *non-conformant* — the erased nodes it enumerates still physically appear in the tree, and the emitter
    still generates code from `Term` — and *self-defeating*: the §34.3.3 legality verifier (whose job is to
    prove no runtime term depends on an erased occurrence) is then run over a tree that still contains every
    erased occurrence, so it proves nothing, and every consumer written against the wrapper is rewritten again
    when the real tree lands. The wrapper does the work twice; it does not reduce it.
  - **Staging.** The observe-only wrapper was permitted only as a temporary differential scaffold — it could
    compute the erasure/convention/layout/ownership decisions and check them against the legacy path, but no
    emitter logic could be written against it. That scaffold has been replaced by the real
    `src/Kappa/Backend/IR.hs` tree and a build-time tree validator; residual backend-wide Core analyses now
    sit behind explicit non-emission phase boundaries.
- **Step 3 — representation classes on KBackendIR** (§34.3.7): the substrate for unboxing / niche layout /
  `TagId` and for **S5 FBIP**. This is where the layout program and the RC arc converge.

Validation discipline mirrors Perceus: each step is observable-output-parity / conformance-clean, with
RC-on-vs-RC-off baselines where relevant. S3+ also carries poison/free-count/heap gates for reclamation.
Step 2+ additionally unlocks the spec's KBackendIR legality checkpoints (§34.3.3) and dump/verifier schemas
(§34.1.5A / §34.3.4 / §34.1.6A) that the conflated `Term` cannot currently produce.

## 6. Sequencing against the Perceus / S3 arc (the practical call)

- **S3 has landed on the current side-table.** That was the right sequencing for the free-on-zero flip; do not
  retroactively churn the validated S3 path just to start this migration. S4 (atomic split) is runtime-side
  and also does not require it.
- **Schedule Phase B on top of the landed Step 1–3 native substrate.** S5 FBIP can now proceed against typed
  KBackendIR constructors and identity-keyed ownership consumers. Further cleanup of legacy ownership dumps
  and non-emission Core planning can happen independently, but reuse tokens must be implemented on KBackendIR.

## 7. Costs / notes

- **Large refactor** (≈586 `CVar` sites, the interp, both backends). Mitigated by the incremental steps and
  the per-stage validation discipline above; Step 0 and Step 1 deliver most of the pain relief before the
  full KBackendIR type lands.
- **The interpreter** evaluates KCore (or `Term`=KCore) and is already a separate evaluator; the backend
  consumes KBackendIR. They diverge cleanly.
- **Conformance upside:** a real KBackendIR is what makes §34.3.3 legality checkpoints, §34.3.4 legality
  witnesses, and §34.1.6A conformance-verification-mode dumps *achievable* — currently the conflated `Term`
  cannot expose a spec-conformant KBackendIR artifact at all.
- **This is where the RC obligations belong.** §34.4.1 (memory management; "RC-free never drives resource
  release", the §1 carve-out) is KBackendIR-level — another reason the Perceus arc ultimately wants the real
  KBackendIR rather than the path-keyed side-table it bootstrapped on.

## Spec anchors

- Pipeline mandate: **§28** (backend MUST NOT bypass KCore/KBackendIR/erasure/representation-selection/legality).
- KCore: **§30.2** (kernel), **§30.2.2.1** (places/paths), **§30.2.3A** (erasure justifications), **§30.2.5**
  (semantic object identities), **§1.2** (typed artifacts).
- Erasure: **§31.2** (+ mandatory-erasure audit trail; legality verifier), **§31.2.1** (inhabitant elision),
  **§11.1.6** (erasure / phases / elaboration time), **§12.2.7** (quantities are ownership-only).
- Representation selection: **§31.3** (variant `TagId`), **§31.4** (record canon), **§31.5** (mutable/`var`
  elision), **§24** (dynamic representations), **§34.3.7** (representation classes and specialization).
- KBackendIR: **§34.3** (+ **§34.3.1** conceptual lowering stages, **§34.3.3** legality checkpoints,
  **§34.3.4** legality witnesses), **§34.4.1** (memory management / RC obligations).
