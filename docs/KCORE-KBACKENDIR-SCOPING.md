# KCore / KBackendIR split — scoping

**Verdict up front.** Splitting the compiler's single `Term` into a typed **KCore** and a lowered,
representation- and ownership-annotated **KBackendIR** is the right move — and, crucially, it is **not a new
architecture to invent**: the spec *already* mandates this exact pipeline. The current implementation, in
which one Haskell `Term` (`src/Kappa/Core.hs`) serves as both the typed core and the backend IR while a
path-keyed side-table (`src/Kappa/Ownership.hs`) carries the erasure/ownership metadata, is a pragmatic
**divergence from the normative pipeline**. The accumulating symptoms — the backend re-deriving erased type
facts (`isKindDomainValueAt` quoting a forced value back to a term *at codegen*, `argConvSelect` re-walking
`CPi` telescopes, `ctorLayoutOf`, the S2.3c arity checks, the S2.3d `boBorrowed` re-checks; ~69 sites) and
the R-path risk class — are the cost of that divergence. This note scopes the conformance path.

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

- **One `Term` plays both KCore and KBackendIR.** It is effectively untyped for backend purposes — `CCtor`
  and `CMatch` carry no type — and has **no stable binder identities**; binders are addressed positionally.
- **Erasure is not a materialized lowering.** Instead of a KCore→KBackendIR pass that discharges §31.2 once,
  erasure is re-decided piecemeal at the backend (`eraseQ0Args` during `compileApp`, `isKindDomainTerm` /
  `isKindDomainValueAt` at codegen — the latter *runs NBE* (`quote ∘ force`) inside the emitter).
- **The audit table is keyed by structural child-position paths**, not the stable identities §31.2/§30.2.5
  envision. `Ownership.hs`'s `OwnInfo` is a spec-*permitted* audit table, but its positional keys are the
  fragile part: codegen's `gsPath` must reproduce `Ownership.walk`'s path scheme exactly (the shared
  `PathScheme`), and a divergence silently misattributes every op.
- **Consequence:** the backend continually **re-derives what the KCore→KBackendIR lowering was supposed to
  compute once** — erased-vs-runtime, arg conventions, ctor layout, ownership. ~69 re-derivation sites across
  `Repr`/`C`/`LLVM`/`Verify`/`Ownership`/`Usage`.

## 3. Why it matters now (the symptoms compound, and block the roadmap)

- **The re-derivation tax grows every Perceus stage.** Each new stage re-derives more from untyped `Term` +
  quoted `Value`. `isKindDomainValueAt`'s `quote ∘ force` at codegen is the worst case — re-running the
  normalization engine in the emitter.
- **The R-path risk is the highest-rated Perceus risk**, and it exists *only* because the audit table is
  positionally keyed. The spec wants identity keys (§31.2). The S2.3d review's "silent branch-drop-site
  lookup miss" was a direct symptom: a positional miss used to be fail-closed to a leak with poor
  diagnosability. Current validation reports those misses, and stable-identity keying would make the class
  structurally impossible.
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

- **Step 0 — pullable now, cheap, no refactor.** Thread the erasure classification the elaborator *already
  computed at typecheck* (`0`-quantity ∨ kind-domain) as a per-binder annotation, and delete
  `isKindDomainTerm` / `isKindDomainValueAt`. Kills the codegen `quote ∘ force` immediately. First brick.
- **Step 1 — stable KCore identities; re-key the audit table (highest correctness value).** Replace the
  structural-path keys with stable KCore binder / node identities (§30.2.5, §31.2). This alone **retires the
  R-path risk class** and makes the S2.3d "silent lookup miss" impossible. Ownership metadata is now keyed as
  the spec intends.
- **Step 2 — materialize KBackendIR.** A distinct Haskell type (or, pragmatically, an annotated `Term`
  wrapper first) produced by an explicit KCore→KBackendIR lowering pass that discharges §31.2 erasure once
  and attaches erasure/ownership/arg-convention as node fields. The backend reads fields; the re-derivation
  sites collapse.
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
- **Schedule Steps 1–3 as the S4→S5 interlude / the representation-layout enabler.** S5 FBIP genuinely cannot
  proceed cleanly without typed KBackendIR constructors, so this is S5's hard prerequisite — and it is shared
  with the whole layout/unboxing program, so it is one investment serving both.
- **Step 0 is schedule-free** — pull it forward whenever, to kill the `quote ∘ force`.

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
