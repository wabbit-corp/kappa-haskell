# Lane audit — Types / Elaboration / Diagnostics

Hostile compliance audit of the Kappa-Haskell implementation against `docs/Spec.md`
for §3 (diagnostic contract), §9–§17 (declarations through patterns), §30–§31
(elaboration/KCore/defeq/erasure). Verdicts are against normative spec text and
against observed CLI behavior of probe `.kp` programs, NOT against
`SPEC_COMPLIANCE.md` or the corpus pass rate.

Status legend: IMPLEMENTED+TESTED | IMPLEMENTED-WEAK | MISSING |
INTENTIONALLY-UNSUPPORTED(cite) | SPEC-CONFLICT | UNCLEAR.

Key structural fact (drives many rows): the diagnostic record
(`src/Kappa/Diagnostic.hs:48-59`) has only
`{code, family, severity, stage, primary, message, notes, helps}`. There is **no**
JSON renderer, no `--json`/`--format` flag (`app/Main.hs` only does prose
`renderDiagnostic`), and no `related`, `payload`, `labels`, `fixes`,
`schemaVersion`, `phase`, `explain`, or `suppressed` field. KCore `Term`
(`src/Kappa/Core.hs:76-103`) carries no provenance/origin. The implementation's
own harness (`src/Kappa/TestHarness.hs:168-185`) classifies
`assertDiagnosticPayload/Label/Related/Fix*/Suppressed` as
`structuredUnsupported`, and the in-tree corpus has **zero** such directives
(`grep` over `tests/conformance` → 0 files), so "195/195" does not touch these MUSTs.

## §3 Diagnostic contract

| § | requirement (short) | status | evidence/probe | note |
|---|---|---|---|---|
| 3.1 | error-tolerant frontend; recover and keep analyzing | IMPLEMENTED-WEAK | `/tmp/probe/multi.kp` (3 type errors) → 3 diagnostics; `/tmp/probe/recov.kp` (parse error then later decl) continues and reports the later type error | cross-declaration recovery works; intra-expression typed recovery nodes (§3.1.14A) unverified |
| 3.1 | human-readable renderer | IMPLEMENTED+TESTED | every probe renders `path:line:col: sev[CODE] (family): msg` + note/help | `renderDiagnostic` |
| 3.1 | **machine-readable JSON output** | **MISSING** | no `--json`; `grep aeson/toJSON/encode/object` in src → none; `kappa check --json` falls to usage | §3.1 line 493-496 MUST. Blocker. |
| 3.1 | tools MUST NOT need to parse prose to recover code/severity/ranges/related/fixes/family | MISSING | only prose output exists; the only structured surface is the in-process harness reading the `Diagnostic` record (no related/payload/fix fields at all) | §3.1 line 500-502 |
| 3.1.1 | JSON exposes fields ≡ {schemaVersion, code, family, severity, stage, phase, primary, message, labels, notes, helps, fixes, related, payload, explain, suppressed} | MISSING | record has 8 of these; no JSON at all; `schemaVersion/phase/labels/fixes/related/payload/explain/suppressed` have no representation (`Diagnostic.hs:48-59`) | §3.1.1 line 529-530 MUST |
| 3.1.1 | error severity fails compilation | IMPLEMENTED+TESTED | every error probe → exit 1 (`hasErrors`) | |
| 3.1.1A | diagnostic multi-span by default; `related` with stable roles | MISSING | no `related` field; no role enum in source | §3.1.1A line 535-590 |
| 3.1.1A | type-mismatch MUST include actual-expr site + expected-type origin | MISSING | `/tmp/probe/tm.kp` → only prose notes `actual/expected`; no structured related origins | §3.1.1A line 597-599 MUST |
| 3.1.1A | ambiguous-name/implicit MUST include all candidate sites | MISSING | `implicits/local_candidates.kp:32` `E_IMPLICIT_AMBIGUOUS` says "two implicit candidates" in prose; the two binder sites (`left`,`right`) are not exposed as related origins | §3.1.1A line 596,600 MUST |
| 3.1.1A | trait-coherence MUST include every surviving incoherent instance site | MISSING | `/tmp/probe/coh.kp` `E_INSTANCE_INCOHERENT` blames one line; other instance site not a related origin | §3.1.1A line 601 MUST |
| 3.1.1A | borrow/path MUST include intro site + failing use/escape site | IMPLEMENTED+TESTED | every `E_QTT_BORROW_ESCAPE`/`_OVERLAP`/`_CONSUME`/`_PATH_CONSUMED` emit site uses `emitRel` carrying `borrow-start`/`consumed-here` + the failing use/escape origin (re-probed `/tmp/probes/overlap_probe.kp` → `borrow-start`+`consumed-here`; `consume_probe.kp` likewise); regression in `qtt/record-paths.kp`, `qtt/inout-overlap.kp`, `qtt/borrow-consume-related.kp`, `projections/selector-footprint.kp` | §3.1.1A line 602 MUST — satisfied |
| 3.1.1A | machine renderer MUST preserve all related origins | MISSING | no machine renderer | §3.1.1A line 616 |
| 3.1.1A | unavailable required related origin → payload records why | MISSING | no payload | §3.1.1A line 610-611 |
| 3.1.2 | stable symbolic codes; not all-digits; symbolic form | IMPLEMENTED+TESTED | all observed codes `E_*`/`W_*`/`I_*` symbolic | `Explain.hs` registry |
| 3.1.2 | corresponding §3.2 family MUST be on the diagnostic | IMPLEMENTED-WEAK | families present in prose; e.g. `E_TYPE_EQUALITY_MISMATCH`→`kappa.type.mismatch`, `E_NUMERIC_LITERAL_DOMAIN_MISMATCH`→`kappa.type.literal-domain-mismatch`; impl-defined ones use reserved `kappa-hs.*` | family mapping correct; but only recoverable from prose (no JSON) — see 3.1.1 |
| 3.1.2A | machine-readable code registry, available without compiling invalid source | IMPLEMENTED+TESTED | `Explain.registry` is a static table; `kappa explain E_TYPE_MISMATCH` works with no source | registry is the entry list; portable aliases + Unicode codes registered |
| 3.1.2A | `kappa explain <code>` rejects unknown codes deterministically | IMPLEMENTED+TESTED | `kappa explain E_NOPE` → stderr "unknown diagnostic code", exit 1 | `cmdExplain` |
| 3.1.2A | registry entry shape (defaultSeverity, stability, payloadSchema, introducedIn, owner…) | IMPLEMENTED-WEAK | `ExplainEntry` carries only {code, family, explanation}; no stability/severity/version/owner/payloadSchema fields | §3.1.2A line 686-701; registry exists but is a thin subset of the conceptual entry |
| 3.1.3 | stable Unicode diagnostic codes (E_UNICODE_*, W_UNICODE_*) registered | IMPLEMENTED-WEAK | all 14 codes in `Explain.registry`; emission verified for some (corpus `unicode/`), not all (e.g. INVALID_GRAPHEME/BYTE/UTF8 emission unverified here) | spellings fixed; emission partially exercised |
| 3.1.4 | portable aliases recoverable without parsing prose | IMPLEMENTED-WEAK | `requiredAliasTable` maps rendered→portable; recoverable only via the in-process harness (`codeNames`), not via any machine output | §3.1.4 line 819-821; no JSON `code`/`portableCode` field |
| 3.1.5 | origins carry source ranges | IMPLEMENTED-WEAK | `Span` has start+exclusive-end (`Source.hs:27-31`); renderer prints only `line:col` start; no JSON range | data present, not exposed structurally |
| 3.1.5 | labels (sub-span labels) | MISSING | no `labels` field; harness lists `assertDiagnosticLabel` unsupported | §3.1.5 |
| 3.1.5A | **provenance frames** for generated syntax/obligations/implicit insertions/transports | MISSING | no `ProvenanceFrame`; KCore nodes carry no origin (`Core.hs`) | §3.1.5A line 1120,1163-1165 MUST |
| 3.1.5A | every synthetic origin carries/refs a provenance frame; diagnostic exposes frame | MISSING | none represented | §3.1.5A line 1163,1167-1168 MUST |
| 3.1.6 | fix-its (`DiagnosticFix`, `SourceEdit`, applicability) | MISSING | no `fixes` field; only `helps` prose; harness lists `assertDiagnosticFix*` unsupported | §3.1.6 line 1191-1271 |
| 3.1.7 | local repair ranking (delimiter < rewrite < import < gate < unsafe) | MISSING | no fix-its to rank | §3.1.7 |
| 3.1.8 | human renderer shows sev, code, message, primary range, labels(when avail), notes/help/fixes | IMPLEMENTED-WEAK | shows sev/code/family/point/message/notes/helps; no labeled excerpt, no fixes | §3.1.8 line 1331-1338; meets the unconditional bullets, missing the "when available" excerpt/fix |
| 3.1.9 | **diagnostic payloads** (`kind`, family-required fields) | MISSING | no `payload` field; harness lists `assertDiagnosticPayload` unsupported | §3.1.9 line 1362-1405 MUST for §3.2 families |
| 3.1.9 | `E_TYPE_MISMATCH` MUST expose expected/actual payload | MISSING | `/tmp/probe/tm.kp` mismatch carries types only in prose notes | §3.1.9 line 1498 MUST |
| 3.1.10 | obligation provenance / diagnostic selection determinism | UNCLEAR | selection appears deterministic across reruns of `multi.kp`; no obligation records exposed; cannot fully verify | §3.1.10 |
| 3.1.11 | root-cause suppression into `suppressed` | MISSING | no `suppressed` field; cascade errors emitted independently | §3.1.11 line 1588-1594 (SHOULD for suppression, MUST for retaining summary) |
| 3.1.11 | primary span anchored to user-written decl, no drift | IMPLEMENTED+TESTED | probes anchor to the offending expression/decl span | |
| 3.1.11 | internal-placeholder hygiene: no raw metavariable as the only explanation | SPEC-CONFLICT | `/tmp/probe/qid.kp`, `/tmp/probe/ctor.kp`, `/tmp/probe/esc2.kp` leak `?m1237`, `@-1.⟨wit0⟩` into the user-facing `actual:` note as the sole rendering of the type | §3.1.11 line 1607-1611 MUST; rendering bug |
| 3.1.11 | function-valued application binder names; payload arg index/binder | MISSING | no payload; binder metadata not surfaced | §3.1.11 line 1632-1639 MUST (payload part) |
| 3.1.12 | source-oriented warning hygiene | UNCLEAR | few warnings emitted (W_TERMINATION_UNVERIFIED); generated-use accounting not exercised | |
| 3.1.13 | `kappa explain <code>` long-form | IMPLEMENTED-WEAK | works for codes; entries are 1-2 sentences, lack minimal-example/corrected-example/common-causes (SHOULD fields) | §3.1.13 line 1750-1760 SHOULD |
| 3.1.13 | `kappa explain <family>` | MISSING | `kappa explain kappa.type.mismatch` → "unknown diagnostic code", exit 1; CLI `cmdExplain` only calls `lookupCode` (code path), though `Explain.explainExists` supports families internally | §3.1.13 line 1747 SHOULD; CLI not wired |
| 3.1.14 | continue after recoverable failures | IMPLEMENTED-WEAK | cross-decl recovery works (`recov.kp`) | SHOULD |
| 3.1.14 | recovery MUST NOT accept invalid program | IMPLEMENTED+TESTED | every invalid probe → exit 1 | |
| 3.1.14A | recovery as typed frontend state with `RecoveryNode`s for the listed conditions | MISSING | no `RecoveryNode`/recovery-metadata type; parser recovers by skipping to next decl, not by inserting typed recovery nodes | §3.1.14A line 1789-1832 MUST; partially mitigated — invalid programs are still rejected, so the soundness clause holds |
| 3.2.x | each standardized family's "Payload MUST include …" | MISSING | no payloads at all (see 3.1.9) | §3.2.1–§3.2.19 |
| 3.2 | family identifiers correct (`kappa.*` for standardized, reserved prefix otherwise) | IMPLEMENTED-WEAK | spot-checked: coherence/non-callable have no standardized §3.2 family → `kappa-hs.*` is permitted; standardized ones use `kappa.*` | only recoverable from prose |
| 3.3 | path/dep/borrow diagnostics (codes/families) | IMPLEMENTED+TESTED (related) | `E_QTT_BORROW_ESCAPE`/`_OVERLAP`/`_CONSUME`/`_PATH_CONSUMED` emitted with `kappa.borrow.*`/`kappa.path.consumed`/`kappa.quantity.unsatisfied`; all now carry §3.1.1A related origins (`borrow-start`/`consumed-here`/`borrow-escape-site`/`used-after-consume`) | code+family correct; related origins present for every borrow/path family; family-specific payloads (§3.2.x) still prose-only |

## §9 Declarations & §9.4 expect

| § | requirement | status | evidence/probe | note |
|---|---|---|---|---|
| 9.1 | signature without definition → error | IMPLEMENTED+TESTED | `E_SIGNATURE_UNSATISFIED` registered; corpus `recursion/` | |
| 9.3 | `let … in` | IMPLEMENTED+TESTED | used throughout corpus | |
| 9.4 | `expect` satisfaction; `E_EXPECT_UNSATISFIED`/`E_EXPECT_AMBIGUOUS` | IMPLEMENTED+TESTED | `/tmp/probe/expect2.kp` `expect term missingThing : Integer` → `E_EXPECT_UNSATISFIED`; `/tmp/probe/expect3.kp` with matching `present` def → exit 0 | grammar is `expect term NAME : TYPE` (also data/type/trait forms); checker tracks satisfier count (`Check.csExpects`) |

## §10 Data well-formedness & §10.4 strict positivity

| § | requirement | status | evidence/probe | note |
|---|---|---|---|---|
| 10.1 | `data` declarations, named/curried constructors | IMPLEMENTED+TESTED | corpus `data/`, every probe | curried ctors confirmed (`/tmp/probe/partial.kp` exit 0) |
| 10.2 | GADT-style constructors | IMPLEMENTED-WEAK | corpus exists; not independently probed in this lane | |
| 10.3 | type aliases; reject recursive alias | IMPLEMENTED+TESTED | `E_RECURSIVE_TYPE_ALIAS` registered | |
| 10.4 | **strict positivity MUST reject negative occurrence** | **MISSING** | `/tmp/probe/pos2.kp` `data Bad = MkBad (Bad -> Bad)` (spec's exact rejected example, line 8690) → exit 0; `/tmp/probe/pos3.kp` Rose negative occ → exit 0; `grep positiv src/` → none | §10.4 line 8685 MUST; soundness blocker |
| 10.4 | record parameter-positivity signature; mutual fixed-point | MISSING | no positivity machinery at all | §10.4 line 8673-8684 |

## §11 Universes / cumulativity / rows / labels / propositional equality

| § | requirement | status | evidence/probe | note |
|---|---|---|---|---|
| 11.1 | stratified universes; no Type:Type | IMPLEMENTED+TESTED | `/tmp/probe/univ.kp` `let bad : Type = Type` → mismatch `Type1` vs `Type` | |
| 11.3 | universal quantification (`forall`) | IMPLEMENTED+TESTED | used in `dup`, `useErased`, `use` probes | |
| 11.3.1A | row `Lacks` constraints for open-record extension | IMPLEMENTED-WEAK | `E_ROW_EXTENSION_MISSING_LACKS_CONSTRAINT`/`kappa.row.lacks-failed` registered; corpus `records/`/`labels/` | not independently probed here |
| 11.4 | propositional equality; `refl` must match | IMPLEMENTED+TESTED | `/tmp/probe/eq2.kp` `refl : 1 = 2` → rejects `= Integer 1 1` vs `= Integer 1 2` | |
| 11.4 | equality match requires h-level (`E_EQUALITY_MATCH_REQUIRES_ISSET`) | UNCLEAR | portable alias not found in `Explain.registry`; emission unverified | §3.2.3 line ~"This diagnostic MUST use portable alias E_EQUALITY_MATCH_REQUIRES_ISSET" — alias appears unregistered |

## §12 Quantities / borrowing / regions / captures (QTT)

| § | requirement | status | evidence/probe | note |
|---|---|---|---|---|
| 12.1 | function types | IMPLEMENTED+TESTED | everywhere | |
| 12.2 | linear overuse rejected | IMPLEMENTED+TESTED | `/tmp/probe/lin.kp` `dup (1 x) = (x,x)` → `E_QTT_LINEAR_OVERUSE` | |
| 12.2 | linear drop rejected | IMPLEMENTED+TESTED | corpus `qtt/linear-drop.kp` `E_QTT_LINEAR_DROP` | |
| 12.2.1 | erased (q0) runtime use rejected | IMPLEMENTED+TESTED | `/tmp/probe/er.kp` `useErased (0 x) = x` → `E_QTT_ERASED_RUNTIME_USE` | |
| 12.3 | borrow lifetimes / escape | IMPLEMENTED+TESTED | `qtt/borrow-escape.kp` → `E_QTT_BORROW_ESCAPE` | |
| 12.4 | disjoint path borrowing / consume-after-borrow | IMPLEMENTED+TESTED | `E_QTT_BORROW_OVERLAP`/`E_QTT_PATH_CONSUMED` registered; corpus `qtt/` | |
| 12 | quantity is part of function-type identity | IMPLEMENTED+TESTED | `/tmp/probe/qid.kp` `(0 x)->` ≠ `(1 x)->` rejected | also §31.1 |

## §13 Records / variants / sealed / existentials

| § | requirement | status | evidence/probe | note |
|---|---|---|---|---|
| 13.1 | variant types; unknown member rejected | IMPLEMENTED+TESTED | corpus `variants/missing-member.kp`, `E_VARIANT_MEMBER` | |
| 13.2 | records; duplicate field rejected | IMPLEMENTED+TESTED | `/tmp/probe/dup.kp` → `E_RECORD_DUPLICATE_FIELD` (type and literal) | |
| 13.2 | projection of missing field rejected | IMPLEMENTED+TESTED | `/tmp/probe/proj.kp` `r.z` → `E_RECORD_PROJECTION_MISSING_FIELD` | |
| 13.2.10 | sealed signatures; opaque unfolding rejected | IMPLEMENTED-WEAK | `E_SEAL_*` codes registered; corpus `types/exists-*` | not independently probed |
| 13.2.11 | existential witness non-escape | IMPLEMENTED+TESTED | `/tmp/probe/esc2.kp` returning witness-typed value → rejected (witness type not in result scope) | leaks `@-1.⟨wit0⟩` into message (see 3.1.11) |

## §14 Traits / instances / coherence / deriving

| § | requirement | status | evidence/probe | note |
|---|---|---|---|---|
| 14.1-14.3 | traits, members, instances | IMPLEMENTED+TESTED | `/tmp/probe/impok.kp` resolves `Sh Integer`, runs → `5` | |
| 14.3 | coherence: overlapping instances rejected | IMPLEMENTED+TESTED | `/tmp/probe/coh.kp` two `instance Foo Integer` → `E_INSTANCE_INCOHERENT` | |
| 14.5 | declaration-level `derive` | INTENTIONALLY-UNSUPPORTED | `/tmp/probe/der.kp` `derive Eq/Show` → `E_UNSUPPORTED` | §14.5 line 14594: "Phase 0 keeps declaration-level deriving implementation-defined." Permitted. Portable path is §22 `std.deriving.shape` (out of this lane). |

## §15 Totality / termination

| § | requirement | status | evidence/probe | note |
|---|---|---|---|---|
| 15.1/15.2 | accepted termination-certified SCC MUST be well-founded (soundness) | IMPLEMENTED+TESTED | `/tmp/probe/loop.kp`/`sound.kp`: divergent `loopy` accepted only as **not conversion-reducible** (`W_TERMINATION_UNVERIFIED`); does NOT unfold in defeq → `refl : loopy 0 = 0` rejected, no hang | conservative tier (§15.2) + §14.703 ("total by default" applies to transparent/δ defs); sound |
| 15.3 | structural descent | IMPLEMENTED-WEAK | structural recursion accepted across corpus; W_TERMINATION_UNVERIFIED on non-structural | |
| 15.11 | explicit `decreases` parses (all forms) | IMPLEMENTED+TESTED | corpus `recursion/decreases-parses.kp` | |
| 15.x | accepting an unverified divergent def as runtime value | UNCLEAR-acceptable | accepted with warning, not certified, not δ | spec does not mandate rejection of un-certified runtime recursion; conservative acceptance is permitted |

## §16 Expression elaboration / subsumption / implicit resolution

| § | requirement | status | evidence/probe | note |
|---|---|---|---|---|
| 16.1 | variables & application; non-callable rejected | IMPLEMENTED+TESTED | `/tmp/probe/noncall.kp` `5 3` → `E_APPLICATION_NONCALLABLE` (alias `E_APPLICATION_NON_CALLABLE`) | |
| 16.1 | argument-type mismatch | IMPLEMENTED+TESTED | `/tmp/probe/argm.kp` `f True` → `E_APPLICATION_ARGUMENT_MISMATCH` (`kappa.application.argument-mismatch`) | |
| 16.2 | lambdas | IMPLEMENTED+TESTED | everywhere | |
| 16.3 | implicit resolution; unsolved rejected | IMPLEMENTED+TESTED | `/tmp/probe/imp.kp` → `E_UNSOLVED_IMPLICIT`; positive `impok.kp` solves | |
| 16.3.3 | ambiguous implicit candidates rejected | IMPLEMENTED+TESTED | `implicits/local_candidates.kp:32` → `E_IMPLICIT_AMBIGUOUS` | but no candidate-site related origins (see 3.1.1A) |
| 16.4 | `if` used as value needs `else` | IMPLEMENTED+TESTED | `/tmp/probe/ife.kp` `if b then 1` → `E_IF_MISSING_ELSE` | |
| 16.1.4 | quantity subsumption via elaboration eta (not defeq) | IMPLEMENTED-WEAK | corpus `qtt/pi-quantity-subsumption.kp` | not independently probed |

## §17 Match / exhaustiveness / flow-refinement / active patterns

| § | requirement | status | evidence/probe | note |
|---|---|---|---|---|
| 17.1 | non-exhaustive match rejected, with missing cases | IMPLEMENTED+TESTED | `/tmp/probe/exh.kp` (missing `Blue`) → `E_PATTERN_NON_EXHAUSTIVE` note `missing cases: Blue` | structured missing-case info is prose, not payload (§3.2 `kappa.pattern.non-exhaustive` payload MUST) |
| 17.2 | constructor pattern arity | IMPLEMENTED-WEAK | `E_PATTERN_CONSTRUCTOR_ARITY_MISMATCH` registered; not probed | |
| 17.3 | active patterns | IMPLEMENTED+TESTED | corpus `patterns/active_patterns.kp` PASS; `E_ACTIVE_PATTERN_*` codes registered | |
| 17 | flow/branch refinement | IMPLEMENTED-WEAK | corpus `refinement/`, `qtt/checked-div-branch-refinement.kp` | not independently probed |

## §30 Elaboration / KCore invariants

| § | requirement | status | evidence/probe | note |
|---|---|---|---|---|
| 30.1 | elaboration to KCore | IMPLEMENTED+TESTED | runs/checks succeed; KCore in `Core.hs` | |
| 30.2 | KCore is de Bruijn, canonical record/variant order | IMPLEMENTED+TESTED | `CRecordT` "canonical (lexicographic) field order", `CVariantT` canonical | |
| 30.2.3 | **every synthetic KCore node MUST carry provenance** (origins + introduction kind) | MISSING | `Core.hs:76-103` `Term` has no origin/provenance field | §30.2.3 line 33060 MUST (carrying); the *dump* part is §34 (profile-scoped) |
| 30.2.3A | erasure justifications per erased occurrence | MISSING | no `ErasureJustification`; KCore has no per-node erasure metadata | §30.2.3A line 33096 MUST; "before lowering to KBackendIR" → the audit-table form is §34/backend (profile-scoped), the KCore-justification form is core |

## §31 Definitional equality / normalization / erasure / canonicalization

| § | requirement | status | evidence/probe | note |
|---|---|---|---|---|
| 31.1 | β-reduction | IMPLEMENTED+TESTED | implicit in all evaluation | |
| 31.1 | δ-reduction of transparent conversion-reducible defs | IMPLEMENTED+TESTED | `/tmp/probe/delta.kp` `two=2; refl : two = 2` → accepted | |
| 31.1 | ι-reduction (match/if on known ctor) | IMPLEMENTED+TESTED | evaluation of corpus `match/` programs | |
| 31.1 | η for functions | IMPLEMENTED-WEAK | implied by passing corpus; not isolated here | |
| 31.1 | η for records; zero-field record ≡ Unit | IMPLEMENTED+TESTED | `/tmp/probe/eta.kp` `r = (x=r.x, y=r.y)` by `refl` → accepted | |
| 31.1 | quantity strictly invariant in defeq; eta preserves quantity | IMPLEMENTED+TESTED | `/tmp/probe/qid.kp` `(0 x)->` not defeq `(1 x)->` | |
| 31.1 | normalization fuel-bounded but sound (no false defeq) | IMPLEMENTED+TESTED | `sound.kp`: divergent `loopy` not claimed equal; terminates | |
| 31.2 | erasure deletes q0 binders / RuntimeErased / meta-phase | INTENTIONALLY-UNSUPPORTED(partial) | interpreter evaluates terms; no physical KBackendIR erasure pass | tree-walking interpreter — §27.7 makes backend profiles conforming-per-profile; physical erasure + KBackendIR verifier are backend (profile-scoped). Erasure soundness for evaluation is observed (q0 use already rejected statically by QTT). |
| 31.2 erasure audit / KBackendIR verifier | erasure audit trail before KBackendIR | INTENTIONALLY-UNSUPPORTED | no KBackendIR | §27.7 backend profile; no backend implemented |
| 31.3 | variant runtime representation (stable TagId) | INTENTIONALLY-UNSUPPORTED | interpreter representation; `CInject` tag by member identity | runtime-representation detail; backend-scoped (§27.7) — but tag-by-identity (not ordinal) is honored in `CVariantT`/`CInject` |
| 31.4 | record canonicalization | IMPLEMENTED+TESTED | `CRecordT`/`CRecordV` canonical field order | |

---

## Legitimate gaps (ranked)

In-scope (§3 core diagnostic contract; §10.4; §30.2.3 carrying), spec-grounded,
MUST/SHALL-level, each disproved by a probe. Profile-scoped items are excluded
(listed separately below).

### 1. No machine-readable JSON diagnostic output — §3.1.1 (line 493-496, 529-530) — BLOCKER
- **Required**: "A conforming implementation MUST support both: (1) a human-readable diagnostic renderer; and (2) machine-readable diagnostic output in JSON." JSON MUST expose fields observationally equivalent to {schemaVersion, code, family, severity, stage, phase, primary, message, labels, notes, helps, fixes, related, payload, explain, suppressed}.
- **Probe**: `kappa check --json /tmp/probe/tm.kp` → falls through to `usage:` (no flag). `grep -niE 'aeson|toJSON|encode|object \[|--json|--format' src app` → no JSON producer. The only output path is `renderDiagnostic` (prose).
- **Observed vs required**: prose-only `path:line:col: error[CODE] (family): message` vs a JSON record with the 16 conceptual fields. Tools cannot recover code/severity/range/family/related/fixes without parsing prose (also violates §3.1 line 500-502).
- **Fix locus**: `src/Kappa/Diagnostic.hs` (add JSON encoder over an enriched record using only boot packages — hand-rolled JSON), `app/Main.hs` (add `--json`/format selection to `cmdCheck`/`cmdRun`).

### 2. Strict positivity not enforced — §10.4 (line 8685, 8690) — BLOCKER (soundness)
- **Required**: "Implementations MUST reject non-strictly-positive `data` declarations." Spec lists `data Bad = MkBad (Bad -> Bad)` as a *rejected* example.
- **Probe**: `/tmp/probe/pos2.kp` `data Bad : Type = MkBad (Bad -> Bad)` → **exit 0 (accepted)**. `/tmp/probe/pos3.kp` `data Rose (a:Type):Type = Node a ((Rose a -> a) -> Rose a)` → **exit 0**. `grep -niE 'positiv' src/` → no occurrences.
- **Observed vs required**: accepted silently vs MUST-reject with a well-formedness error. A negative datatype admits a fixed point and lets one construct non-terminating/`⊥` inhabitants, breaking logical soundness of the dependent type theory.
- **Fix locus**: `src/Kappa/Check.hs` (data-declaration well-formedness, where constructor argument types are checked; add a positivity pass computing per-parameter positivity signatures per §10.4 and rejecting negative occurrences before admitting the `data`).

### 3. No related origins (multi-span) — §3.1.1A (line 535-616) — BLOCKER
- **Required**: type-mismatch MUST include actual-expr + expected-type sites; ambiguous-name/implicit MUST include all candidate sites; trait-coherence MUST include every surviving incoherent instance site; borrow/path MUST include intro + failing-use sites; machine renderer MUST preserve all related origins.
- **Probe**: `implicits/local_candidates.kp:32` `E_IMPLICIT_AMBIGUOUS` renders "two implicit candidates in the same scope" but neither candidate binder site (`left`,`right`) is a structured related origin; `/tmp/probe/coh.kp` `E_INSTANCE_INCOHERENT` blames one instance line only; `/tmp/probe/tm.kp` carries expected/actual only as prose notes.
- **Observed vs required**: single `primary` span + prose notes vs `related : List RelatedOrigin` with stable roles. `Diagnostic` (`Diagnostic.hs:48-59`) has no `related` field at all.
- **Fix locus**: `src/Kappa/Diagnostic.hs` (add `dRelated :: [RelatedOrigin]` with role enum), then thread sites at each producer in `src/Kappa/Check.hs` / `src/Kappa/Resolve.hs` / `src/Kappa/Usage.hs`.

### 4. No diagnostic payloads — §3.1.9 (line 1362-1405, 1498) and §3.2.x family payloads — MAJOR
- **Required**: payload MUST contain at least `kind`; for any §3.2 standardized family the payload MUST contain that family's required fields; `E_TYPE_MISMATCH` MUST expose an expected/actual payload when both sides exist.
- **Probe**: `/tmp/probe/tm.kp` mismatch carries expected/actual only in prose `note:` lines; `exhaustiveness` carries missing cases only in prose; the harness lists `assertDiagnosticPayload` as `structuredUnsupported` (`TestHarness.hs:177`) and the corpus has 0 payload assertions.
- **Observed vs required**: prose notes vs `payload : DiagnosticPayload` (e.g. `ExpectedActualPayload`).
- **Fix locus**: `src/Kappa/Diagnostic.hs` (add `dPayload`), producers in `src/Kappa/Check.hs`.

### 5. No provenance frames; KCore nodes carry no provenance — §3.1.5A (line 1120,1163-1168) + §30.2.3 (line 33060) — MAJOR
- **Required**: §3.1.5A — preserve provenance frames for generated syntax/inserted terms/implicit insertions/transports/derived decls; every synthetic origin MUST carry/reference a frame; every diagnostic from a generated obligation MUST expose the frame. §30.2.3 — every synthetic KCore node MUST carry provenance (origins + introduction kind).
- **Probe**: `Core.hs:76-103` — `Term` constructors carry no origin/provenance; `grep -niE 'provenance|frame' src/Kappa/Core.hs` → none; no `ProvenanceFrame` type anywhere.
- **Observed vs required**: synthetic nodes (implicit insertions, eta-coercions for quantity subsumption, etc.) are unannotated vs a `ProvenanceFrame` chain.
- **Fix locus**: `src/Kappa/Core.hs` (origin/provenance on synthetic terms or a side table keyed by node identity), `src/Kappa/Check.hs` (populate on insertion). Note the §30.2.3 *dump* (KCore dump) is §34 → profile-scoped; the *carrying* requirement is core.

### 6. No fix-its — §3.1.6 (line 1191-1271), §3.1.7 — MAJOR
- **Required**: `DiagnosticFix`/`SourceEdit` records with applicability; local-repair ranking.
- **Probe**: `Diagnostic.hs` has only `dHelps :: [Text]` (prose); no `fixes`; harness lists `assertDiagnosticFix*` unsupported; corpus has 0 fix assertions.
- **Observed vs required**: prose `help:` lines vs structured `fixes`.
- **Fix locus**: `src/Kappa/Diagnostic.hs` + producers.

### 7. Internal metavariable names leak into user-facing messages — §3.1.11 (line 1607-1611) — MAJOR
- **Required**: "Human-facing diagnostics MUST NOT expose raw internal fallback origins, sentinel names, generated metavariable helper names ... unstable binder IDs ... as the only explanation."
- **Probe**: `/tmp/probe/qid.kp` → `actual: (1 x : ?m1236) -> ?m1236`; `/tmp/probe/ctor.kp` → `actual: ?m1237 -> Pair Integer ?m1237`; `/tmp/probe/esc2.kp` → `actual: @-1.⟨wit0⟩`. The metavariable/internal token is the sole rendering of the actual type.
- **Observed vs required**: `?m1236`/`@-1.⟨wit0⟩` printed vs a stable explanatory phrase or solved type.
- **Fix locus**: `src/Kappa/Pretty.hs` (metavariable/rigid rendering), and zonk-before-render in `src/Kappa/Check.hs` mismatch reporting.

### 8. No root-cause suppression (`suppressed`) — §3.1.11 (line 1588-1594), §3.1.10 (line 1573) — MINOR
- **Required**: related cascade diagnostics SHOULD be suppressed into one root's `suppressed` field; suppressed MUST retain structured summary.
- **Probe**: `/tmp/probe/amb.kp` and `/tmp/probe/multi.kp` emit independent cascade errors; no `suppressed` representation exists.
- **Fix locus**: `src/Kappa/Diagnostic.hs` + `src/Kappa/Pipeline.hs` aggregation.

### 9. Registry entries are a thin subset of the conceptual entry — §3.1.2A (line 686-701) — MINOR
- **Required**: registry entry has defaultSeverity, stability, payloadSchema, introducedIn, deprecatedIn, replacedBy, owner.
- **Probe**: `ExplainEntry` (`Explain.hs:30-34`) = {code, family, explanation} only.
- **Fix locus**: `src/Kappa/Explain.hs`.

### 10. `kappa explain <family>` not wired into CLI — §3.1.13 (line 1747) — MINOR (SHOULD)
- **Required (SHOULD)**: support `kappa explain <diagnostic-family>`.
- **Probe**: `kappa explain kappa.type.mismatch` → "unknown diagnostic code", exit 1. `Explain.explainExists` already handles families but `cmdExplain` calls only `lookupCode`.
- **Fix locus**: `app/Main.hs` `cmdExplain`.

### 11. No typed recovery nodes (`RecoveryNode`) — §3.1.14A (line 1789-1832) — MINOR
- **Required**: recovery as typed frontend state with `RecoveryNode`s for the listed recoverable conditions.
- **Probe**: parser recovers by skipping to the next declaration (`recov.kp` shows cross-decl recovery) rather than inserting typed recovery nodes; no `RecoveryNode` type exists. Mitigated by §3.1.14A line 1830 ("Recovery MUST NOT cause an invalid program to be accepted") which **is** honored — every invalid probe exits 1.
- **Fix locus**: `src/Kappa/Parser.hs` + `src/Kappa/Parser/Monad.hs`.

### Probable-but-unconfirmed (listed for follow-up, not asserted as gaps)
- §3.2.3 / §11.4: portable alias `E_EQUALITY_MATCH_REQUIRES_ISSET` is **absent** from `Explain.registry` and from all of `src/` (`grep ISSET\|EQUALITY_MATCH src/` → none). §3.2.3 states this diagnostic "MUST use portable alias `E_EQUALITY_MATCH_REQUIRES_ISSET`". This becomes a confirmed §3.1.4/§3.2.3 MAJOR gap **iff** the implementation supports equality `match` requiring UIP/IsSet at all; if equality elimination is restricted to `subst`/`pathInd` (no source equality `match`), the diagnostic condition may be unreachable and the omission acceptable. Needs a probe that writes an equality `match` to determine which. Left as probable-unconfirmed.

## Profile-scoped / intentionally-unsupported (cited)

- **§14.5 declaration-level `derive`** → INTENTIONALLY-UNSUPPORTED. §14.5 line 14594: "Phase 0 keeps declaration-level deriving implementation-defined." `derive Eq/Show` → `E_UNSUPPORTED` is permitted. (Portable derivation is §22 `std.deriving.shape`, outside this lane.)
- **§31.2 physical erasure pass + erasure audit trail before KBackendIR; §31.2 KBackendIR legality verifier; §30.2.3A audit-table form** → profile-scoped. §27.7 makes backend profiles conforming-per-profile; this implementation is a frontend + tree-walking interpreter with no KBackendIR. Erasure *soundness* for evaluation is preserved (q0 runtime use is statically rejected by the QTT checker, e.g. `/tmp/probe/er.kp`).
- **§31.3 variant runtime tag representation** → backend-representation detail (§27.7); the interpreter tags by member identity (`CInject`), consistent with the "not by ordinal position" rule.
- **§30.2.3 KCore *dump* exposing provenance** (as opposed to *carrying* it) → §34 compiler-pipeline dump machinery, profile-scoped per the audit SCOPE RULE. (The *carrying* requirement is core and is listed as gap #5.)
