# Kappa spec compliance — remaining work to 100%

Single source of truth for what this implementation still needs to fully conform
to `docs/Spec.md` (the Kappa Language Specification). This replaces the former
`SPEC_COVERAGE.md` (per-section status table) and `SPEC_AUDIT_MATRIX.md`
(requirement matrix + ranked Gn worklist), both of which had become
substantially self-superseded.

**Status (verified 2026-06-23):** `kappa test tests/conformance` = **349/349**
pass (0 fail, 0 unsupported, 0 harness error). Every gap below was re-verified
against the *current* code in a parallel 9-group re-audit (see
[Methodology](#appendix-b-methodology)); fix loci are `file:line` at audit time.

## Scope and profile model

The spec is layered. The **portable `kappa-v1` profile core** — Parts I–IV, the
§3 diagnostic contract, §4 unsafe/debug, §28–§29 prelude/std modules, and §30–§33
core semantics — has no optionality clause and is what "100% compliance" means
for a single implementation. Backends (§27, §34.2–§34.5, §36 codegen), runtime
capability profiles (§27.6), config/build *tooling* (§35–§36), FFI/boundary
(§24–§26), and IDE/LSP (§37.3) are **profile-scoped**: the spec explicitly
sanctions a conforming implementation that does not provide them (e.g. §27.7
"a backend profile is conforming iff …"). Those are listed in §3 below for
completeness but are **not** required for core conformance.

## Status at a glance

| Bucket | Count | Meaning |
| --- | --- | --- |
| **Core MUST/SHALL gaps** (§1) | 30 | Required for portable-profile conformance. Do these. |
| **SHOULD gaps** (§2) | 12 | Recommended; non-conformance is permitted but discouraged. |
| **Profile-scoped / adjudication** (§3) | 22 | Sanctioned by an explicit profile clause, or spec-MUST-but-profile-gated (flagged). |
| **Optional / MAY** (§4) | 1 | Pure latitude. |
| **Open questions** (§5) | ~6 | Need a spec re-read or a targeted probe before classifying. |

> The prior docs listed ~59 items as gaps that are in fact **already
> implemented** (config/build mode, ranges, `try match`, `std.bytes`, the §4
> unsafe/debug suite, structured JSON diagnostics + payloads + fixes, postfix
> sections, `inout`, kind-qualified names, the numeric/collection prelude
> surface, …) and contained ~46 stale or mis-stated claims. Those are summarized
> in [Appendix A](#appendix-a-removed-since-the-prior-docs) so the deletions are
> auditable.

---

## 1. Core conformance gaps (portable `kappa-v1` profile)

These are the real "must do for 100%". Ordered soundness-first, then by subsystem.

### 1.1 Soundness / correctness — do first

All soundness items identified in the audit have been **resolved** this pass —
§11.1 universe stratification, §8.5.2 opaque cross-module leak, and
§16.4.4/§17.1.10 positive-lower-bound false rejects (see Appendix A). The
last is fixed *soundly and modularly* — the arithmetic operators borrow their
operands, so a relevant (`>=1`) value supplied to `+` is demanded (a borrow
reads it) while a relevant value supplied to a genuinely unrestricted parameter
is still correctly rejected (`QuantitySatisfies >=1 ω` does not hold, §12.2.1).
No unsound "assume the callee uses its argument" defaulting remains.

### 1.2 Type system & elaboration

| § | Gap | Fix locus | Effort |
| --- | --- | --- | --- |
| **§11.3.3** | Free lowercase type variables are **not** universalized in **block-local** named `let` signatures (only top-level). Local `let idf : a -> a = \x -> x` → `E_NAME_UNRESOLVED 'a'`. | universalization pass (currently top-level/instance-head only) | medium |
| **§11.4.2** | **Boolean→type coercion** `b ⟼ (b = True)` is unimplemented in all three forms: implicit binder `(@x : b)`, left of `b => T`, and a record/tuple field with a bare-boolean declared type (`ok : id == 1`). All three → `E_NOT_A_TYPE`. | `Check.hs` type-position elaboration (no `= True` coercion path) | medium |
| **§16.3.2** | **Named holes** don't share: every `?h` makes a fresh independent meta (`anyHole` ignores the name), so two `?h` at incompatible types aren't rejected. Also the unsolved-hole diagnostic doesn't report the expected type (no `EHole` case in the `check` direction). | `Check.hs:1889-1893` (`anyHole`), `Check.hs:3098-3115` (only-`infer` `EHole`) | medium |
| **§16.4.1** | **Exhaustiveness ignores flow refinement.** After `if e is C`, a `match e` covering only `C` in that branch is wrongly `E_PATTERN_NON_EXHAUSTIVE`. `checkExhaustive` consults `csDatas` and never `ctxRefines`. (Field projection on the refined value *does* work.) | `Check.hs:8146-8169` (`checkExhaustive`) | medium |
| **§16.4.2** | Flow refinement has **no `not` case.** `condRefines` handles `&&`/`||`/`is`/thunks but not `not`; `complementRefines` only fires on a bare `EIs (EVar _) _`. So `if not (b is Hole) then b.val else 0` doesn't refine. (Spec requires `if not a then t else f ≡ if a then f else t` before §16.4.1.) | `Check.hs:7845-7859` (`condRefines`), `Check.hs:7821-7823` (`negs`) | medium |
| **§17.1.9** | **Guard evidence** isn't pushed in plain-match arms: the guard term isn't added to `csBoolFacts` when checking the arm body, so `case _ if y <= x -> x - y` can't discharge the checked-sub proof. The `if`-path and try-match path do push it. | `Check.hs:8119-8120` (`checkMatchPlain.goCase`, no `withFact`) | medium |
| **§30.2.7** | No **inhabitance-summary** query. The only emptiness check (`scrutineeEmpty`) handles one case: a nullary data type with zero constructors. Missing: Subsingleton/Contractible/Finite, closed sum/product summaries, GADT family-argument refinement → Empty, proof-classification evidence (`IsEmpty`/`IsContr`/…), equality no-confusion. Bare `impossible` always rejects as reachable. *(Also unblocks §17.1.4.)* | `Check.hs:8133-8142` (`scrutineeEmpty`), `Check.hs:3451-3454` (`EImpossible` always errors) | large |

### 1.3 Effects, resources, collections

| § | Gap | Fix locus | Effort |
| --- | --- | --- | --- |
| **§19.5 / §19.1** | `bracket` uses the naive `ioBind acquire (\r -> finally (use r) (release r))` that §19.5 calls insufficient — it hands `use` an **owned** `a`, not a **borrowed** `& r` view, so the no-escape guarantee is unenforced. The method is named `bracketM` (spec: `bracket`), drops all `1`/`&` markers, and neither `MonadError` nor `MonadResource` declares the mandated `MonadFinally m =>` supertrait. | `Prelude.hs:912,917-918,1252-1253` | medium |
| **§32.2.19/.20/.21** | Eff-typed do-blocks reject `defer`/`using`/`var`/loop items (`elabEffDo` handles only `DoExpr/DoBind/DoLet/DoIf`). So a continuation captured by a handler clause has no do-scope exit-action frames, and the spec's mandated **masked-LIFO unwinding of a captured-then-abandoned segment** (and the per-clone copy / escape restriction) is unimplemented for the `Eff` carrier. | `Check.hs:7634-7680` (`elabEffDo` rejects other items), `Eval.hs:1067-1116` (`__effBind` tree, no exit-action stack) | medium |
| **§20.4.1 / §20.10.7** | **Borrowed generators** `for x in &coll` (`BorrowSourceIntoQuery`) and `for & pat in coll` / `for? & pat in coll` (`BorrowItemsIntoQuery`) are neither parsed nor lowered. The traits are declared (`Prelude.hs:2114,2118`) but dead. Depends on §12 borrow-region inference (rigid ρ), itself unimplemented. | `Parser.hs:3000` (no `&`-prefixed source/item), no dispatch in `Check.hs` for/comprehension lowering | large |

### 1.4 Prelude surface (§28.2 term/type/constructor namespaces)

| § | Gap | Fix locus | Effort |
| --- | --- | --- | --- |
| **§28.2** | Interruption/finalization combinators `poll`, `uninterruptible`, `mask`, `ensuring`, `acquireRelease` are absent (`E_NAME_UNRESOLVED`). The do-driven fiber/scope/promise/race/timeout/bracket surface *is* present. | add to `Prelude.hs` | medium |
| **§28.2** | Fiber-identity/label terms `fiberId`, `currentFiberId`, `getFiberLabel`, `setFiberLabel`, `locallyFiberLabel` absent (the `FiberId` type + `MkFiberId` exist at `Prelude.hs:1273`, no accessors). | add to `Prelude.hs` | medium |
| **§28.2** | `and`, `or`, `force` not exported as first-class terms (the n-ary `List Bool` folds + `force`; `(&&)`/`(||)`/keyword-`force` exist but aren't nameable values). | `Prelude.hs` (`force` keyword-only at `Parser.hs:1602`) | small |
| **§28.2** | `Iterator.next` is now declared, definable in instances, and usable in generic code (the associated `Item` projects from the evidence). Residual: at a **concrete** call the result field's `d.Item` type does not reduce to the instance's `Item` (postponed-evidence timing), so `r.item` of a concrete `next` result reads as the unreduced projection. | §14.2.1 use-site associated-member normalization / eager concrete trait-evidence solving | medium |
| **§28.2** | `DefectTag` type entirely absent (constructors `Panic`/`AssertionFailed`/`ArithmeticFault`/`StackOverflow`/`OutOfMemory`/`HostFailure`/`ForeignContractViolation`/`UnhandledChildFailure`/`OtherDefect`). | add to `Prelude.hs` | small |
| **§28.2** | `DefectInfo` wrong shape + ctor name: is `MkDefectInfo (message : String)`; spec wants `DefectInfo (tag : DefectTag) (message : Option String)`. | `Prelude.hs:1279-1280` | small |
| **§28.2** | `InterruptCause` ctor is `MkInterruptCause`; spec constructor namespace lists `InterruptCause.InterruptCause`. | `Prelude.hs:1276-1277` | small |
| **§28.2** | Of the 8 intrinsic row/var/eff solver traits only `LacksRec` is registered; `ContainsRec`/`StableUnderRecChange`/`RecTailSatisfies`/`ContainsVar`/`LacksVar`/`ContainsEff`/`LacksEff`/`SplitEff` are unresolvable. *(Their value beyond the prelude name — open rows/variants — is profile-scoped, §3.)* | `Prelude.hs`/`Builtins.hs` (only `LacksRec`) | medium |

### 1.5 Metaprogramming & reflection (§21–§22)

| § | Gap | Fix locus | Effort |
| --- | --- | --- | --- |
| **§21.5** | No **quotation-pattern matching** on `Syntax t` and no equivalent stable structural-inspection API (must distinguish v1 surface constructs). Only `renderSyntax`/`syntaxOrigin`/`normalizeSyntax`/`whnfSyntax`/`typeOfSyntax`/`defEqSyntax`/`headSymbolSyntax` exist — none destructure surface syntax. | no `inspectSyntax`/`SyntaxView`/`PQuote` in `Prelude.hs`/`Parser.hs` | large |
| **§21.6** | **Semantic-reflection value tier** `asCore`/`asCoreIn`/`reifyCore`/`inferType`/`whnf`/`normalize`/`tryProveDefEq`/`proveDefEq`/`defEq`/`headSymbol` all `E_NAME_UNRESOLVED`. `reifyCore` is one of only two re-entry points to object code, so the whole tier is non-functional (needs a faithful runtime `Core` representation carrying QTT/scope evidence). | `Prelude.hs` | large |
| **§21.6** | `transCoreEq`/`substCoreEq` not declared (deferral comment only); `reflCoreEq`/`symCoreEq` present but the `CoreEq` witness algebra is incomplete. | `Prelude.hs:1902-1910` | medium |
| **§21.6** | No typed scope-safe **constructor/destructor API** over reflected `Core` (vars/binders, global refs, app, lambda/let, Pi/Sigma, records/members/projections, ctors/field projections, match, universes/equality, variant injections/rows). Types `CoreCtx`/`Core`/`CoreEq`/`Symbol` are declared but have no inspect/build API. | `Prelude.hs` | large |
| **§21.6** | `lowerComprehension : RawComprehension a -> Elab (ComprehensionPlan a)` not provided; `RawComprehension`/`ComprehensionPlan` are opaque with no inspection API (custom sinks get an opaque token). | `Prelude.hs:167-168` | large |
| **§22** | `std.deriving.shape` missing the `Result`-returning `tryInspectAdt`/`tryInspectRecord`, the construction terms `constructAdt`/`constructRecord`/`matchRecord`, plus `requiredRuntimeFieldConstraints`/`requireRecordFieldInstances`/`fieldArgument`/`omitImplicitFieldArgument`. | `Prelude.hs:2173-2222` (`stdDerivingShapeSource`) | large |
| **§22** | `std.deriving.shape` missing types `ShapeErrorKind`/`ShapeError`/`ShapeParameter`/`FieldArgument`/`FieldConstraint`, and the shape records are reduced: `ShapeField` has only `sourceName`+`renderName` (no `origin`/`typeOrigin`/`fieldType`/`fieldTypeSyntax`/`quantity`/`implicit`/`compileTimeOnly`/`runtimeRelevant`); `ShapeConstructor`/`AdtShape` lack `symbol`/`origin`/`parameters`; `BoundField`/`BoundFieldPair` lack their Syntax fields. Blocks §22.3 runtime-relevant filtering and §22.4 per-field diagnostics. | `Prelude.hs:2155-2171,2180` | large |

### 1.6 Diagnostic contract (§3)

| § | Gap | Fix locus | Effort |
| --- | --- | --- | --- |
| **§3.1.7** | **Repair ranking** unimplemented as a mechanism: only the unresolved-name typo rename fix is ever produced, so the mandated ranking (local repair > rewrite > import > feature gate > unsafe escape; gate never primary when a local repair is plausible) is vacuously satisfied but not realized. | `Check.hs` fix producer (`closeSpellings`/editDistance only) | medium |

> §3.1.5A structured **provenance frames** are also a §3 MUST but depend on the
> KCore provenance store, which the audit ledger reads as profile-scoped — listed
> under [§3 adjudication](#3a-spec-must-but-profile-clause-scoped-flagged-for-adjudication).

---

## 2. SHOULD-level gaps

Recommended by the spec; a conforming implementation may decline them, but they
are the next tier after §1.

| § | Gap | Fix locus | Effort |
| --- | --- | --- | --- |
| §11.1 | **Universe polymorphism** `forall (u : Universe) (a : Type u). …` — no `Universe` intrinsic, `Type u` not callable. *(Distinct from the §1.1 stratification soundness fix.)* | `Check.hs` | large |
| §17.1.4 | A `-> impossible` arm is **never** accepted (always `E_IMPOSSIBLE_REACHABLE`), so a GADT-refined uninhabited case can't use it. Unblocked by §30.2.7. | `Check.hs:3451-3454` | medium |
| §17.1.7 / §7.4.1 | A constructor/variable-scrutinee `match` arm doesn't register `ctxRefines` for the scrutinee, so `match b case Full v -> b.val …` fails member projection (records `csFacts` only). | `Check.hs:8098-8124` (`goCase`) | medium |
| §15.14 | **Block-local recursive helpers** aren't run through the termination pass at all — a divergent local `let go k decreases k = go (k+1)` is accepted silently (no `W_TERMINATION_UNVERIFIED`), unlike the identical top-level def. | termination pass (top-level SCC only) | medium |
| §14.3.5 | No declaration-time **Paterson check**: `instance C a => C a = …` (premise identical to head) is accepted. Only a search-depth backstop (`>16`) + determinacy cut exist. | `Check.hs:2452-2471` | medium |
| §12.4.3 | First-class accessor/borrow descriptor ops use simplified `1`/ω binders instead of exact `(&[ρ] x : A)` borrow-marked domains. | `Prelude.hs:204` (`captureBorrowTy`) | medium |
| §28.1 / §28.2 | Conventional prefixed-string handlers `re"…"` (regex) and `b"…"` (bytes-from-string) absent (`E_NAME_UNRESOLVED` as prefix). *(Distinct `b'…'`/`g'…'` quoted-literal handlers do work.)* | `Prelude.hs` | medium |
| §29.4 | `std.unicode.collation` and `std.unicode.security` submodules not provided as modules (some security prims exist internally for source-hygiene lints only). | `Prelude.hs:2553`, `Pipeline.hs:91-110` | large |
| §35.10 | Config **tooling queries** (value-path/string-slice provenance, editable-range ranking, contributing-bindings/affected-values, provenance-preserving refactor) — only a whole-`buildConfig` `--provenance` dump exists. | `app/Main.hs:208-211`, `Build/Provenance.hs` | large |
| §3.1.13 | Explanation entries are 1–2 sentence prose; lack the minimal-invalid / corrected-example / common-causes / cascade-notes structure. | `Explain.hs` entries | medium |
| §3.1.4 | The declaration-skip recovery emits impl code `E_EXPECTED_SYNTAX_TOKEN` (family `kappa-hs.parse.error`, `portableCode=null`) instead of exposing the portable alias `E_RECOVERY_SKIPPED_INVALID_SYNTAX`. | `Parser.hs:101` (`recoveryDiag`) | small |
| §5.2 | Expression-continuing/statement-starting soft keywords (`then else in case do if match while for let var return break continue defer import …`) still terminate an unparenthesized application-argument run context-insensitively, so a bare same-named local in argument position misparses. Documented residual (KNOWN_SPEC_ISSUES #8/#10); the query/handler keyword family *is* resolved contextually. | `Parser.hs` `stopKeywords` vs `queryStopKeywords` | large |

---

## 3. Profile-scoped & adjudication-flagged

Not required for portable-profile conformance. Two buckets.

### 3a. Spec-MUST but profile-clause-scoped (flagged for adjudication)

These read as MUST in their own section but a profile clause (§27.7 backend,
§34 compiler-pipeline, §37.3 tooling tiers) is cited as permitting the omission.
§4.1 (line 4223) calls stage dumps "ordinary required tooling facilities," which
argues *against* full optionality — hence "adjudication".

| § | Gap | Note |
| --- | --- | --- |
| §3.1.5A | Structured **provenance frames** (`ProvenanceFrame` id/kind/step/inputs/output/explanation, acyclic chain, every synthetic origin + obligation carrying a frame). Only a single `desugared-from` related origin on the `!e` splice exists (`Check.hs:3428`). | diagnostic-facing slice done (was G10); full store profile-scoped via §34 |
| §30.2.3 | Every synthetic **KCore node** carrying origin + introduction-kind (desugaring/macro/implicit/coercion/borrow/reorder/place/handler-kernel/…). `Core.Term` has no such field. | KCore *dump* is §34 profile-scoped; the *carrying* requirement is the contested part |
| §30.2.3A | Per-erased-occurrence **erasure justification** class (`QuantityZero`/`AmbientDemandZero`/`RuntimeErasedEvidence`/…). Erased binders/args/fields are dropped silently in codegen. | tied to §31.2 |
| §31.2 | **Erasure audit table** + **KBackendIR legality verifier** (reject runtime terms referencing erased Type/Quantity/Region/proof/… except via a carrier). Erasure happens inline in C codegen, no audit artifact, no verifier. | KBackendIR itself is §34 backend-scoped; the audit-trail obligation is the core part |
| §34.1.3 | **Stage-dump / checkpoint** surface: request a snapshot at a named checkpoint, stop-before/after, list executed steps, verify invariants. No CLI/API exists. | `TestHarness.hs:180-199` documents the absence honestly |
| §34.1.5 | Two machine-readable stage-dump serializations (json + sexpr), self-describing/versioned, deterministic. None exist (depends on §34.1.3). | — |
| §34.1.6 | Command to **list the executed compilation steps** for a request. `fileTrace` is computed internally but not exposed. | `Pipeline.hs:208-212` |

### 3b. Genuinely profile-scoped (explicit citation, not portable-core)

| § | Area | Status |
| --- | --- | --- |
| §11.3.1 | `VarRow`/`Label` classifier types + the 7 unimplemented row/var/eff traits | only `LacksRec`; the rest unresolvable |
| §13.1.5 | Open / row-polymorphic **variant** rows `(\| a \| r \|)` + `LacksVar` | only closed unions; blocked on `VarRow` |
| §12.2.1 | `QuantitySatisfies` reified as a writable trait constraint | enforced operationally, not nameable |
| §28.2 / §18.1.11 | source-level `blocking` combinator | only an FFI-classification alias of the same name exists |
| §29.1 | `std.atomic` instances over std.ffi fixed-width/pointer-width ints; polymorphic `atomicFetch*` | only `Bool`+`Integer`; monomorphic over `Integer` |
| §29.2 | `std.supervisor` observable semantics (restart policies/strategies/intensity/cause) | full type/term surface; semantics are stubs |
| §29.7 | `std.config` unification surface (`input`/`ConfigPath`/`ConfigUnify`/`tryUnify`/`unify`/`<&>`/…) | only `ConfigInputKey`+`configInput` |
| §29.8 | `std.build` full enumerated schema (~120 types/~130 ctors) | representative subset; spec permits a concept-expressing subset |
| §3.1.14A | **Intra-declaration** typed `RecoveryNode`s (missing-expr-after-`=`/`->`, malformed field/binder/interpolation, …) | only 4 boundary sites emit recovery nodes |
| §30.2.5.1 | Semantic-object identity for escaped local nominal families + interface-representability check | identity is name-based (`GName`); depends on §34.1.9 |
| §33.1.1–.3 | Two-tier content-addressed hashing (Easy Hash / HardIdentity / persistent cache) | none; the only observable §33 MUST — coherence §33.2.1 — *is* satisfied. Persistent cache is a §33.1.2 *package-mode* MUST (§36 profile-scoped) |
| §34.3 | KBackendIR (typed lowered target-neutral IR + legality checkpoint) | KCore→C directly; no materialized KBackendIR |
| §36.13/.20/.24/.25 | jvm/dotnet/wasm backend profiles; Maven/NuGet/Python resolution | only native (zig/cc); others rejected honestly |
| §36.23 | registry/git/url dependency discovery | only path-dependency content identity resolved |
| §36.4 | full `ResolvedBuildPlan` (matrix/feature/provider/graph) | single-target `ResolvedExe` slice only |
| §37.3.1 | Tooling Core: LSP, analysis session, semantic queries, InfoView | batch compiler only; §37.3 tiers IDE support |

---

## 4. Optional / MAY

| § | Item | Note |
| --- | --- | --- |
| §10.2 | GADT-style constructor binder **defaults** (`C : (n:Nat) -> (xs : Vec n a = replicate n x) -> R`). Currently the `= expr` is swallowed by the propositional-`=` operator and mis-elaborates to `Bool = True`. The non-GADT field-default form works. | `Parser.hs:755` (`pCtorDecl`) |

---

## 5. Open questions (need a spec re-read or a probe)

- **§11.4 / §3.2.3 (U1)** — portable alias `E_EQUALITY_MATCH_REQUIRES_ISSET` is
  absent. A real §3.2.3 gap *iff* the impl supports equality `match` requiring
  UIP/IsSet; if equality elimination is `subst`/`pathInd`-only it's unreachable.
  Needs a probe writing an equality `match`.
- **Appendix G.1** — the `Applicative` method is declared `pureA`
  (`Prelude.hs:795`); confirm against the spec's required spelling and either
  rename or document the alias.
- **§24.9** — `decide`/`Dec (a = b)` returns a coarser result than the spec's
  `Dec (a = b)` (which carries the actual decision); align or document.
- **§3.1.10 (U2)** — obligation-provenance / diagnostic-selection determinism
  is observably stable but no obligation records are exposed; can't fully verify.
- **§33.2.1 (U6)** — harmless-overlap acceptance for canonically-identical,
  structurally-different instances isn't verified (conservative rejection is
  permitted by `semantic-if-available`).
- **§18.9 / §20.4 / §20.8 (U5)** — `inout` *is* implemented and tested; the
  remaining unknowns are borrowed generators (§20.4.1, see §1.3) and joins.

---

## Appendix A. Removed since the prior docs

The 9-group re-audit verified **~59** items the old docs listed as gaps/Partial/
MISSING are now **implemented** (dropped from the plan), and corrected **~46**
stale claims. The headline removals:

- **§14.3.4 associated static members in instances — FIXED.** An instance now
  *defines* an associated static member with `Name = expr` (no `let`; parsed by
  the bare-`pLetDef` path in `pInstanceMember`). `elabInstance` already checked
  each trait member against its instantiated declaration, so the definition is
  checked against the trait's `Member : Type` declaration: `Elem = a` is
  accepted, `Elem = 5` is rejected (`E_TYPE_EQUALITY_MISMATCH`), and a member
  the trait does not declare is rejected with the new
  `E_ASSOCIATED_MEMBER_UNDECLARED` / `kappa.associated.member-undeclared`. The
  member is projectable from evidence (`d.Elem`, §14.2.1) and coexists with term
  members. Tests: `traits/associated-member-{accept,undeclared-reject,malformed-reject}.kp`.
- **§16.4.4 / §17.1.10 positive-lower-bound false rejects — FIXED (soundly, via
  borrowing).** The arithmetic operators now **borrow** their operands
  (`(+) : … -> (& x : a) -> (& y : a) -> a`, likewise `(*)`), so `x + 1` *reads*
  `x` (a borrow touches it, discharging the `>=1` obligation per §12.4) without
  consuming it: `if b then x else x + 1` and `match o case Some y -> x+y case
  None -> x` with a `>=1` binder are Accepted, while `if b then x else 0` is
  still `E_QTT_LINEAR_DROP` and a relevant value supplied to a genuinely
  unrestricted parameter is still rejected (no unsound "assume-uses" default).
  The binder borrow marker is carried in core (**`CPi`/`VPi` gained a borrow
  field**), so `coreFnParams` reads it from the type rather than the surface AST
  (modular). Borrow-after-consume is now gated on a *definite* (consumable)
  consume, so re-reading an ω value after `let q = p` is no longer a false
  `E_QTT_PATH_CONSUMED`. Tests: `qtt/positive-lower-bound-through-branches.kp`,
  `qtt/positive-lower-bound-drop-reject.kp`, `qtt/linear-to-unrestricted-overuse.kp`.
  (The earlier `scaleC` touch-preservation and the H2 demand-inference attempt
  were reverted as unsound/non-modular.)
- **§8.5.2 `opaque` cross-module leak — FIXED.** `opaque let`/`opaque type`
  now records the def in `csOpaqueDefs`; an `opaqueSealPass` at the end of each
  module clears `gdReducible` for that module's opaque defs, so they stay
  transparent within the defining module but no longer δ-unfold during
  conversion downstream (a cross-module `proof : secret = 7` by `refl` is now
  rejected). Runtime evaluation is unaffected (`ecRuntime` unfolds every valued
  global). Tests: `modules-opaque-cross-module/` (reject),
  `modules-opaque-runtime/` (value still computes cross-module),
  `equality/opaque-def-in-module.kp` (transparent in-module).
- **§11.1 latent Type-in-Type — FIXED.** Type formers now compute a
  predicative `max`-of-component universe level (`Check.hs` record/Pi/tuple/
  option/forall/exists cases): a record/tuple/Pi/existential carrying a
  `Type`-valued component lands in `Type1`, and ascribing it to `Type0` is now
  rejected (`E_TYPE_EQUALITY_MISMATCH`); formers over only `Type0` components
  are unchanged. Regression tests: `types/universe-stratification.kp`,
  `types/universe-type-in-type-reject.kp`. (Universe *polymorphism* — bare
  `Type` absorbing the level — remains the §2 SHOULD; until then a Type-valued
  type written `: Type` must be written `: Type1`.)
- **§4 unsafe/debug — fully done** (was "Not implemented"): `UnsafeConfig`
  `allow_*` flags, `assertTerminates`/`assertReducible`/`assertTotal` +
  `unsafeAssertProof` parsed & gated, `unhide`/`clarify` build-gated, §4.7 audit
  ledger + `kappa audit` + `assertAuditLedger`. (Old worklist G13/G36.)
- **§35 config mode & §36 build system — implemented** (was "Not implemented"):
  `kappa build --manifest` parses `kappa.build`, value provenance, all config
  diagnostic codes, lockfile + lock-drift rejection, native build pipeline.
- **§3 diagnostic contract** — structured `--json` records (16-field surface),
  related origins, structured `payload`, `fixes`/`SourceEdit`, suppressed-cascade
  summaries, `kappa explain` with family listing, hole/metavar rendering as `_`,
  typed `RecoveryNode` payloads. (Old G3/G4/G9/G10-facing/G11/G12/G28/G29/G30/G31.)
- **§2.1** — feature-gate diagnostic now carries `activeProfile=kappa-v1` +
  gate provenance in a structured payload.
- **§28.2 prelude** — `Rational`, the `AdditiveMonoid`/`Semiring`/`Ring`/
  `FieldLike` hierarchy, surface collection terms (`arrayFromList`/`mapEmpty`/…),
  `for_`/`sequence_`, the `Equiv` bridge (`1 ~= 1` runs), the proof helpers
  (`measureRelation`/`lexRelation` resolve), `CheckedSub` (Nat partiality is
  by-design). (Old G15/G16/G17/G18/G19/G20/G21/G25.)
- **§29.5 `std.bytes`** registered; **§29.4 `std.unicode`** core present;
  **§28.2.2 `EuclideanSemiring`** shape corrected. (Old G14/G27, C3.)
- **§10.4 strict positivity** — `positivityPass` (both direct and
  parameter-positivity); `data Bad = MkBad (Bad -> Bad)` rejected. (Old G1/G8.)
- **§18.3.1 splices** — `let x = !e` works; `!f x` captures the whole spine.
  (Old G6/G7, C2.) **§20.2 ranges** iterable in `for`/comprehension via
  `NumericRange`/`Rangeable`. (Old G26.)
- **§5.5.1.1 / §5.5.3** postfix sections/application/chains; **§5.5.1** bare-`(op)`
  ambiguity rejection. (Old G5/G24.) **§6.3.4.1** `\$` escape. (G22.)
  **§8.3** `type T(..) as U` rejected. (G23.)
- **§7.1.1** kind-qualified name expressions, **§13.2.9** implicit record fields,
  **§18.9** `inout`, **§19.3** `try match`, **§11.2** classifier types
  (`Region`/`Quantity`/`RecRow`/`EffRow`/`EffLabel`) — all implemented.
- Conformance count corrected **242 → 349**.

Full per-item evidence is in the audit run (workflow `spec-compliance-consolidate`).

## Appendix B. Methodology

Each spec group below was audited by an independent agent that (a) enumerated
every claimed gap in the prior `SPEC_COVERAGE.md`/`SPEC_AUDIT_MATRIX.md`, and
(b) re-verified it against the current `src/Kappa/**`, `app/`, `tests/conformance/`,
and `examples/`, with `file:line` or probe evidence — classifying each as a
genuine remaining gap, a now-implemented item to drop, or a stale correction.

| Group | Spec sections |
| --- | --- |
| I | §1–§4 (principles, profiles/conformance, diagnostics, unsafe/debug) |
| II | §5–§9 (lexical, literals, names, modules, declarations) |
| III-a | §10–§13 (ADTs, universes/rows, functions/quantities/borrow, records/variants/sealed) |
| III-b | §14–§17 (traits, termination, expressions, patterns/flow) |
| IV | §18–§20 (effects/do, errors/resources, collections) |
| V–VI | §21–§26 (macros/staging, dynamics, boundary, FFI) |
| VII | §27–§29 (backend profiles, prelude, std modules) |
| VIII | §30–§33 (core semantics, defeq/erasure, runtime, identity) |
| IX–X | §34–§37 + appendices (pipeline, config, build, tooling) |
