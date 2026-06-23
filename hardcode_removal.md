# Hardcode Removal — design-smell audit & work plan

This tracks places where the Kappa compiler **hardcodes a decision** that a more
general / derived mechanism should handle. It is distinct from the
`Kappa.Builtins` centralization (which just gives hardcoded *names* one home):
here the concern is hardcoding that is **wrong** — it privileges builtins over a
mechanism that already exists, drifts between duplicated sites, or produces wrong
behavior for some input.

**Gate for every change:** `cabal build all && cabal test` (349 conformance
tests). Related: `memory/dehardcoding-builtins.md` (the names-centralization
effort and its remaining stages).

The unifying smell: **the compiler keys behavior on a hardcoded name/set when the
mechanism to derive it already exists** — a trait, an instance search, or the
declared type/signature.

---

## Tier 1 — A general mechanism already exists but is bypassed

### H1. Comprehension/collection carriers are a closed hardcoded set, not trait-driven
- **Where:** `src/Kappa/Check.hs` — `sourceInfo` (~10148) matches type heads
  `List`/`Array`/`Set`/`Map`/`Option`/`NumericRange`/`QueryCore` by name, else
  `SKUnknown`; `builtinCarrier` (~10667) rejects unknown carriers as
  "unsupported"; lowering intrinsics `__setToList`/`__mapToList`/… (~10747) are
  chosen per hardcoded `SrcKind`. Map comprehensions also hardcode field names
  `"key"`/`"value"` (~10156, 10725, 3332) and the group key field (~10418).
- **Mechanism bypassed:** `FromComprehensionRaw`/`FromComprehensionPlan`
  instances (~10612–10631) — consulted only as a *fallback*.
- **Why wrong:** a user-defined collection cannot be a comprehension target /
  literal even with a correct instance; the privilege is reserved to builtins.
- **General solution:** make instance search the primary path; builtins register
  instances like everyone else. Carry to-list/from-list and key/value field
  names in the instance, not in the compiler.
- **Severity:** High (biggest "more general solution" win). **Verified.**

### H2. `Usage.hs` hardcodes linearity facts about specific functions by name
- **Where:** `src/Kappa/Usage.hs` — `builtinFns` (423–446) maps NAME → quantity /
  capture bound / escape kind for `unsafeConsume`, `pure`, `ioPure`, `summon`,
  `fork`, `forkDaemon`, `forkIn`; `escapeKindFor` (~677) and the
  `["pure","ioPure","return"]` taint list (~1615) duplicate the same name set.
- **Why wrong:** a user cannot write their own fiber-spawning or result-lifting
  primitive and get correct escape/taint analysis — it is reserved to these
  spellings. The facts are also duplicated across three sites.
- **General solution:** express these as **declared attributes on the prelude
  signatures** (a lang-item mechanism); the checker reads the fact from the
  declaration so any function with the attribute qualifies.
- **Severity:** High (highest-value structural change). **Verified.**

### H3. Boolean `&&`/`||` flow refinement is keyed on the operator spelling
- **Where:** `src/Kappa/Check.hs` ~7813/7832 — `op == "&&"` unions refinement
  facts, `op == "||"` intersects them.
- **Why wrong:** a user-defined short-circuit combinator (or a stdlib `xor`) gets
  no flow refinement; reserved to two literal spellings.
- **General solution:** drive refinement off a "boolean connective kind"
  property rather than the spelling.
- **Severity:** Medium (niche but real over-specialization). **Verified.**

---

## Tier 2 — Under-general checks / latent bugs

### H4. Active-pattern result classification is an incomplete hardcoded set
- **Where:** `src/Kappa/Check.hs:12044` — rejects results whose head is in
  `["IO","STM","Elab"]` as "monadic," but **omits `Eff`**, which the do-block
  dispatcher (`src/Kappa/Check.hs:8628`) *does* list as a kernel carrier.
- **Why wrong:** an active pattern returning `Eff <…> a` is silently accepted as
  `APTotal` instead of rejected (spec §17.3.1). Two hardcoded lists that should
  be the same set have already drifted.
- **Correct general solution:** these are the **kernel effect carriers**
  (`IO`/`STM`/`Eff`/`Elab`) — NOT "anything with a Monad instance" (that would
  wrongly reject pure monads like `Option`/`List`/`Either`, which are valid
  total views). Centralize the carrier set as ONE Builtins list used by both the
  do-block dispatcher and the active-pattern check.
- **Severity:** Medium; small, verifiable fix. **Verified** (and the agent's
  "query Monad instance" proposal rejected as semantically wrong).

### H5. `Usage.hs` `Zipper` field hardcode ignores the actual type
- **Where:** `src/Kappa/Usage.hs:470` — `resolveFields` returns
  `[("focus",_),("fill",QOne)]` for any `Zipper(…)`, guarded only against type
  *aliases* (`not (Map.member "Zipper" aliases)`), not against a user
  `data Zipper`.
- **Why wrong:** the hardcode is correct for the prelude `Zipper`
  (`Prelude.hs:733`: `focus` + `1 fill`), but a user `data Zipper` with different
  fields gets wrong linearity facts. Root cause: `resolveFields` works on surface
  `Expr` and lacks resolved-type access.
- **Consequence:** wrong usage diagnostics (false accept/reject), NOT memory
  unsafety. Niche.
- **General solution:** thread resolved type-field quantities into usage
  checking instead of the surface-syntax table.
- **Severity:** Medium-low. **Verified** (severity downgraded from the agent's
  "CRITICAL soundness" claim).

---

## Tier 3 — Closed sets that *could* be open (likely intentional)

### H6. Do-block kernel carriers `["IO","STM","Eff","Elab"]`
- **Where:** `src/Kappa/Check.hs:8628`.
- **Assessment:** the boundary is **intentional** — kernel carriers have effect
  rows, splices, and abrupt control (`break`/`return`/`using`/`defer`) a generic
  `Monad` cannot express, and user monads *are* supported via the generic
  `elabMonadDo` path. Only the name-based dispatch is fragile (already mitigated
  by Builtins constants). Share the carrier list with H4. **Low priority.**

### H7. Projection descriptors / meta-phase type list
- **Where:** `src/Kappa/Check.hs:3813` (`["Projector","Getter","Opener","Setter","Sinker"]`),
  `src/Kappa/Check.hs:9495` (meta-phase type list).
- **Assessment:** closed vocabularies that could be declared, but plausibly
  deliberate fixed sets. **Low priority** — revisit only if extensibility is
  wanted.

---

## Tier 4 — Cleanup loose ends

### H8. `numericLitDomains`/`floatLitDomains` are dead; literal logic duplicates them
- **Where:** defined in `src/Kappa/Builtins.hs` but **unused**; `Check.hs` has 3
  inline `["Int","Nat","Integer"]` copies (e.g. literal admit checks ~4990,
  `isNumHead` ~5014, `litHeadAgrees` ~8529) and `["Float","Double"]` copies.
  `isNumHead`/`isFloatHead` are a fast-path duplicating what `FromInteger`/
  `FromFloat` instance search already decides.
- **General solution:** wire the constants into the inline sites (single source
  of truth). Optionally collapse the fast-path into trait resolution later (low
  value — prelude instances are identity, so not a runtime bug).
- **Severity:** Low / trivial. **Verified.**

---

## Dismissed as false positives (checked, not real)
- **Tuple `_1`/`_2` field collision** — `tupleComponents` uses `traverse
  tupleField` + a strict `== [1..n]` contiguity check (`Check.hs:13699`), so any
  non-`_N` field makes it fall through cleanly. Not a bug.
- **`this` / `yield` magic identifiers, `Thunk`/`Need` suspension kinds** —
  intentional keywords / spec-fixed grammar.
- **`-`→`negate`, `*` universe-vs-multiply** — fragile-by-name but already
  centralized via Builtins constants; low value to further generalize.

---

## Task plan (status)

| ID | Finding | Severity | Risk | Status |
|----|---------|----------|------|--------|
| H8 | Wire dead literal-domain constants | Low | Low | see task list |
| H4 | Active-pattern carrier set (+ `Eff`, shared list) | Medium | Low | see task list |
| H5 | Zipper field hardcode → resolved type | Med-low | Med | see task list |
| H3 | `&&`/`||` fact algebra → property | Medium | Med | see task list |
| H2 | Usage facts → declared attributes | High | High | see task list |
| H1 | Comprehension carriers → trait-primary | High | High | see task list |

Order of attack: H8 → H4 (cheap, verifiable; validate the loop) → H5 → H3 →
H2 → H1 (structural, larger). Each lands behind `cabal build all && cabal test`.
