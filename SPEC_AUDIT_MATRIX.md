# Kappa-Haskell consolidated spec-audit matrix

Single, §-ordered consolidation of four hostile lane audits
(`docs/audit/lane-{syntax,types,runtime,meta}.md`), reconciled against
`docs/Spec.md` normative text and re-verified by independent probes of the built
binary. Stance: hostile (disprove compliance). "195/195 conformance" and the
prior completion claim are treated as irrelevant to whether a normative MUST/SHALL
with no fixture is satisfied.

Build verified clean: `cabal build all --enable-tests --ghc-options=-Werror`.
Conformance re-run: `kappa test tests/conformance` → `195 passed, 0 failed`.
Binary: `dist-newstyle/.../x/kappa/build/kappa/kappa`. CLI surface:
`check | run | test [--suite] | explain`. No `--json`/`--format` flag exists
(re-verified: `kappa check --json FILE` falls through to usage).

Status values: `IMPLEMENTED+TESTED` | `IMPLEMENTED-WEAKLY-TESTED` | `MISSING` |
`INTENTIONALLY-UNSUPPORTED(cite)` | `SPEC-CONFLICT(cite)` | `UNCLEAR`.

Lane provenance column: SYN=syntax, TYP=types, RUN=runtime, META=meta, V=verified
here by re-probe.

---

## §-ordered consolidated matrix

### Part I — Foundations (§1–§4)

| § | requirement (short) | status | lane | evidence / note |
|---|---|---|---|---|
| 1 | Design principles; §1.1 boundary honesty | INTENTIONALLY-UNSUPPORTED(§1.1 applies only when a foreign connection exists) | META | non-normative principles; no foreign boundary crossed |
| 2.1 | MUST fix active profile + feature-gate set before successful elaboration | IMPLEMENTED-WEAKLY-TESTED | META | single hard-coded profile (kappa-v1, `unicode-names` off); no profile-selection surface to probe a second profile, but internally consistent |
| 2.1 | parser recognition ≠ acceptance; gated construct → feature-gating diagnostic | IMPLEMENTED+TESTED | META,SYN | `let π = 3` → `E_FEATURE_INACTIVE (kappa.feature.gated)`, exit 1 |
| 2.1 | gating diagnostic MUST name active profile + provenance of gate settings | MISSING | META | observed diag names construct+gate+repair but NOT the active profile (`kappa-v1`) nor the setting provenance; no structured place to carry them (collapses into §3.1.1 no-JSON gap) |
| 2.1A | `unicode-names` standardized optional gate; kappa-v1 does not imply it | INTENTIONALLY-UNSUPPORTED(§2.1A) | META,SYN | inactive-by-default is conforming; backtick identifiers available |
| 2.2 | version terminology (Kappa v1) | IMPLEMENTED-WEAKLY-TESTED | META | non-normative |
| 3.1 | error-tolerant frontend; recover and keep analyzing | IMPLEMENTED-WEAKLY-TESTED | TYP,SYN | cross-declaration recovery works; intra-expression typed recovery nodes (§3.1.14A) absent |
| 3.1 | human-readable renderer | IMPLEMENTED+TESTED | TYP | `path:line:col: sev[CODE] (family): msg` + notes/helps |
| **3.1** | **machine-readable JSON diagnostic output (MUST, line 493/496)** | **MISSING** | TYP,META,V | no `--json`; no aeson/JSON producer in src; re-verified usage fallthrough. **BLOCKER** |
| 3.1 | tools MUST NOT parse prose to recover code/sev/ranges/related/fixes/family | MISSING | TYP | only prose output exists |
| 3.1.1 | error severity fails compilation | IMPLEMENTED+TESTED | TYP | every error probe → exit 1 |
| 3.1.1 | JSON exposes ≡ {schemaVersion,code,family,severity,stage,phase,primary,message,labels,notes,helps,fixes,related,payload,explain,suppressed} | MISSING | TYP,V | record has 8 of 16 fields; no JSON. **BLOCKER** |
| 3.1.1A | multi-span related origins with stable roles (type-mismatch, ambiguous, coherence, borrow) MUST | MISSING | TYP | no `related` field at all (`Diagnostic.hs:48-59`). **BLOCKER** |
| 3.1.2 | stable symbolic codes; not all-digits; §3.2 family on the diagnostic | IMPLEMENTED+TESTED | TYP,SYN | `E_*`/`W_*`/`I_*`; `kappa.*` for standardized, reserved `kappa-hs.*` otherwise |
| 3.1.2A | machine-readable code registry available without compiling invalid source | IMPLEMENTED+TESTED | TYP,SYN,V | `kappa explain CODE` static table; works with no source |
| 3.1.2A | `kappa explain <code>` rejects unknown codes deterministically | IMPLEMENTED+TESTED | TYP,SYN | `explain E_NOPE` → stderr "unknown diagnostic code", exit 1 |
| 3.1.2A | registry entry shape (defaultSeverity, stability, payloadSchema, introducedIn, owner…) | IMPLEMENTED-WEAKLY-TESTED | TYP | `ExplainEntry` = {code,family,explanation} only |
| 3.1.3 | stable Unicode diagnostic codes registered | IMPLEMENTED-WEAKLY-TESTED | TYP | 14 codes in registry; emission partially exercised |
| 3.1.4 | portable aliases recoverable without parsing prose | IMPLEMENTED-WEAKLY-TESTED | TYP | recoverable only via in-process harness; no JSON `code`/`portableCode` |
| 3.1.5 | origins carry source ranges | IMPLEMENTED-WEAKLY-TESTED | TYP | `Span` has start+end; renderer prints only start; no JSON range |
| 3.1.5 | labels (sub-span labels) | MISSING | TYP | no `labels` field |
| 3.1.5A | provenance frames for generated syntax/obligations/implicit insertions/transports MUST | MISSING | TYP | no `ProvenanceFrame`; KCore carries no origin. **MAJOR** |
| 3.1.6 | fix-its (`DiagnosticFix`/`SourceEdit`/applicability) | MISSING | TYP | only `dHelps :: [Text]` prose. **MAJOR** |
| 3.1.7 | local repair ranking | MISSING | TYP | no fix-its to rank |
| 3.1.8 | human renderer shows sev/code/msg/range/labels(when avail)/notes/help/fixes | IMPLEMENTED-WEAKLY-TESTED | TYP | unconditional bullets met; no labeled excerpt / fixes |
| 3.1.9 | diagnostic payloads (`kind` + family-required fields) MUST | MISSING | TYP | no `payload` field. **MAJOR** |
| 3.1.10 | obligation provenance / selection determinism | UNCLEAR | TYP | deterministic across reruns; no obligation records exposed |
| 3.1.11 | root-cause suppression into `suppressed`; retain summary | MISSING | TYP | no `suppressed` field; cascades emitted independently |
| 3.1.11 | primary span anchored to user-written decl, no drift | IMPLEMENTED+TESTED | TYP | probes anchor correctly |
| 3.1.11 | no raw metavariable/sentinel as the only explanation | SPEC-CONFLICT(§3.1.11 line 1607-1611) | TYP | `?m1236`, `@-1.⟨wit0⟩` leak into `actual:` note as sole rendering. **MAJOR** rendering bug |
| 3.1.12 | source-oriented warning hygiene | UNCLEAR | TYP | few warnings; generated-use accounting not exercised |
| 3.1.13 | `kappa explain <code>` long-form (SHOULD) | IMPLEMENTED-WEAKLY-TESTED | TYP | entries 1-2 sentences; lack minimal/corrected example |
| 3.1.13 | `kappa explain <family>` (SHOULD) | MISSING | TYP | family lookup unwired in `cmdExplain` |
| 3.1.14 | continue after recoverable failures (SHOULD) | IMPLEMENTED-WEAKLY-TESTED | TYP | cross-decl recovery works |
| 3.1.14 | recovery MUST NOT accept invalid program | IMPLEMENTED+TESTED | TYP,SYN | every invalid probe → exit 1 |
| 3.1.14A | typed `RecoveryNode`s for listed conditions MUST | MISSING | TYP,SYN | parser skips to next decl; soundness clause (no false accept) IS honored |
| 3.2.x | each family's "Payload MUST include …" | MISSING | TYP | no payloads at all |
| 3.3 | path/dep/borrow diagnostic codes/families | IMPLEMENTED-WEAKLY-TESTED | TYP | codes+families correct; structured payload/related missing |
| 4.1 | safe portable subset excludes the unsafe/debug forms; they remain part of the spec | MISSING(no clause makes §4 optional) | META | `unhide`/`clarify` parsed but never build-gated; `assertTerminates`/`assertReducible`/`unsafeAssertProof` unrecognized (re-verified parse error). **MAJOR** |
| 4.2 | build-level gating; violation = compile-time error naming form + `allow_*` setting MUST | MISSING | META | no `allow_*` config anywhere; §4.2 diagnostic does not exist |
| 4.3 | `unhide`/`clarify` semantics + gating error | MISSING | META | parsed into flags, no semantic effect/gating |
| 4.4 | `assertTerminates`/`assertReducible`/`assertTotal` escapes | MISSING | META | unrecognized (parse error) |
| 4.5 | `unsafeAssertProof` prelude helper + interface recording | MISSING | META,RUN | unresolved name; also a §28.2 required-term gap |
| 4.6 | backend-specific surface escapes excluded | INTENTIONALLY-UNSUPPORTED(§4.6 "If an implementation provides such a facility") | META | none provided ⇒ conforming |
| 4.7 | unsafe/debug audit ledger + `auditModule/Package/Artifact` queries MUST | MISSING | META | no ledger/query; tied to separate-compilation artifacts (profile-adjacent), ranked lower |

### Part II — Surface language (§5–§9)

| § | requirement (short) | status | lane | evidence / note |
|---|---|---|---|---|
| 5.1 | ASCII identifier grammar | IMPLEMENTED+TESTED | SYN | every probe |
| 5.1/5.1A | Unicode identifiers + NFKC/visual-dup machinery only when `unicode-names` active | INTENTIONALLY-UNSUPPORTED(§2.1/§5.1 gate) | SYN | gate off; `let λ = 1` → `E_FEATURE_INACTIVE` |
| 5.1 | backtick identifiers for reserved/weird names | IMPLEMENTED+TESTED | SYN | `` `match` `` resolves |
| 5.2 | soft keywords usable as identifiers | IMPLEMENTED+TESTED | SYN | `let type = 42` works |
| 5.3 | line + nesting block comments | IMPLEMENTED+TESTED | SYN | nested `{- -}` checks clean |
| 5.4 | significant indentation; NEWLINE/INDENT/DEDENT | IMPLEMENTED+TESTED | SYN | layout used everywhere |
| 5.4 | tabs are compile-time error; points to first tab; no silent tab→space flag | IMPLEMENTED+TESTED | SYN | `E_TAB_IN_INDENTATION`/`E_TAB_IN_SOURCE` |
| 5.4 | brackets suppress INDENT/DEDENT; blank/comment lines ignored; trailing commas | IMPLEMENTED+TESTED | SYN | bracket stack |
| 5.5.1 | operator tokens; `(op)` parenthesized name; numeric-literal disambiguation | IMPLEMENTED+TESTED | SYN | `1..10`→range, `1.0` float, `(+)` |
| 5.5.1 | `(infix/prefix/postfix op)` references | IMPLEMENTED-WEAKLY-TESTED | SYN | infix/prefix exercised; postfix ref not isolated |
| 5.5.1 | bare `(op)` ambiguous when ≥2 callable fixities in scope, no expected type | MISSING | SYN | `infix -`+`prefix -` then `(-)` accepted silently. **MINOR** |
| 5.5.1.1 | right/left sections; `(op e)` as prefix when prefix fixity in scope | IMPLEMENTED+TESTED | SYN | `(+ 3) 10`→13; `(- 1)`→-1 prefix |
| **5.5.1.1 / 5.5.3** | **`(e op)` = postfix application when postfix fixity in scope (MUST)** | **MISSING** | SYN | `(5 ?)` with `postfix 90 (?)` → `E_APPLICATION_NONCALLABLE`; `let b = 5 ?` corrupts next decl. **MAJOR** |
| 5.5.1 | reserved punctuation not operator tokens; longest-match | IMPLEMENTED+TESTED | SYN | `?.`,`?:`,`let?`,`for?`,`~=` tokenize |
| 5.5.2 | fixity decls parse; block-scoped, exported with operator | IMPLEMENTED-WEAKLY-TESTED | SYN | all forms parse; cross-module fixity import not probed |
| 5.5.3 | infix/prefix position gating | IMPLEMENTED+TESTED | SYN | `1 <+> 2` no fixity → `E_OPERATOR_NO_FIXITY`; postfix gating unreachable (see above) |
| 6.1.1 | decimal/hex/octal/binary integer literals | IMPLEMENTED+TESTED | SYN | values w/o underscores correct |
| **6.1.1** | **underscores between digits have NO semantic effect (hex/oct/bin)** | **SPEC-CONFLICT/MISSING** | SYN,V | `0xDEAD_BEEF`→`59776745199` (≠`3735928559`); re-verified. Silent miscompile. **BLOCKER** |
| 6.1.2 | decimal float forms | IMPLEMENTED+TESTED | SYN | `1e10`,`3.14e-2` |
| 6.1.2 | `.5`/`5.` not portable floats | IMPLEMENTED+TESTED | SYN | rejected (span quality poor) |
| 6.1.3 | Float raw-bit eq; `+0.0`≠`-0.0`; total order | IMPLEMENTED+TESTED | SYN | `0.0 == negate 0.0`→neq |
| 6.1.4 | unary `-` is negate, not part of literal | IMPLEMENTED+TESTED | SYN | `(- 1)`→-1 |
| 6.1.5 | defaulting int→Int, float→Float; `-123 : Nat` rejected | IMPLEMENTED+TESTED | SYN | `Negatable Nat` unsolved |
| 6.1.6 | numeric suffix `12px`→`px 12`; unknown suffix error; `e`/`E` suffix rule | IMPLEMENTED+TESTED | SYN | `12qq`→`E_NAME_UNRESOLVED` suffix |
| 6.2 | True/False | IMPLEMENTED+TESTED | SYN | |
| 6.3.1 | strings + escapes; unknown escape error; `\u` scalar ≤0x10FFFF non-surrogate | IMPLEMENTED+TESTED | SYN | `"\uD800"` → surrogate error |
| 6.3.2/6.3.3 | raw strings `#"…"#`; multiline + dedent | IMPLEMENTED+TESTED | SYN | hash-count match, dedent |
| 6.3.4 | prefixed strings; `$name`/`${expr}`/`${expr:fmt}` interpolation | IMPLEMENTED+TESTED | SYN | `f"hello ${name}!"`→`hello world!` |
| 6.3.4.1 | literal `$` writable as `\$` in ordinary prefixed string | MISSING | SYN | `f"cost: \$5"` → `E_STRING_ESCAPE_INVALID`. **MINOR** |
| 6.4/6.5 | `'x'` UnicodeScalar; `g'…'`/`b'…'` quoted literals | IMPLEMENTED+TESTED | SYN | `'ab'`→invalid; `b'λ'`→invalid byte |
| 6.6 | unit, tuples incl one-tuple, grouping | IMPLEMENTED+TESTED | SYN | `(42,):(Int,)` |
| 7.1 | lexical lookup innermost→outermost, kind filtering | IMPLEMENTED+TESTED | SYN | shadowing works |
| 7.1 | visual-alias lookup + warnings | INTENTIONALLY-UNSUPPORTED(`unicode-names` gate) | SYN | gate inactive |
| 7.1.1–7.6 | kind-qualified names; data family; dotted/`?.` resolution; record patch; module reification | IMPLEMENTED(+/-WEAK) | SYN | `type T`, `Option.Some`, `t.{done=True}`, `import lib as L` |
| 8.1 | path→module-name mapping; module header; `@PrivateByDefault` | IMPLEMENTED-WEAKLY-TESTED | SYN | `module foo.bar` parses; case-fold collision MUST not probed |
| 8.2 | reject cyclic / non-unit imports | IMPLEMENTED+TESTED | SYN | sibling not in unit → `E_MODULE_NAME_UNRESOLVED` |
| 8.3 | import forms (`M`,`as A`,`M.(items)`,`M.x`,`M.*`,`except`); kind selectors; operator import | IMPLEMENTED+TESTED | SYN | suite probes compile |
| 8.3 | `ctorAll` may NOT combine with `itemAlias` (`type T(..) as U` ill-formed) MUST reject | MISSING | SYN | accepted silently. **MINOR** |
| 8.4/8.5/9.1 | export forms / visibility; `public`/`private` mutually exclusive | IMPLEMENTED-WEAKLY-TESTED | SYN | conformance passes; exclusivity rejected w/ generic error (spec mandates no specific code) |
| 9.1 | signature `name:T`; `let` definition; missing definition → error | IMPLEMENTED+TESTED | SYN,TYP | `foo : Int` alone → `E_SIGNATURE_UNSATISFIED` |
| 9.1 | bare `foo = 42` (no `let`) not a definition | IMPLEMENTED+TESTED | SYN | parse error |
| 9.1 | modifier prefixes; named-fn binders; `decreases`/`inout`/wildcard | IMPLEMENTED-WEAKLY-TESTED | SYN | decreases/inout not isolated |
| 9.3 | `let … in` | IMPLEMENTED+TESTED | TYP | used throughout |
| 9.4 | `expect` satisfaction; `E_EXPECT_UNSATISFIED`/`_AMBIGUOUS` | IMPLEMENTED+TESTED | TYP | `expect term missingThing` → unsatisfied |

### Part III — Type system (§10–§17)

| § | requirement (short) | status | lane | evidence / note |
|---|---|---|---|---|
| 10.1 | `data` decls; named/curried/record-style ctors | IMPLEMENTED+TESTED | SYN,TYP | corpus + probes |
| 10.2 | GADT-style ctor `C : Pi -> R`; non-GADT binders-before-colon rejected | IMPLEMENTED+TESTED | SYN,TYP | `VCons : … -> Vec (n+1) a` |
| 10.3 | type aliases; reject recursive alias | IMPLEMENTED+TESTED | SYN,TYP | `E_RECURSIVE_TYPE_ALIAS` |
| **10.4** | **strict positivity MUST reject negative occurrence** | IMPLEMENTED+TESTED | TYP,V | `positivityPass` in `Check.hs`; `data Bad = MkBad (Bad -> Bad)` → `E_DATA_NOT_STRICTLY_POSITIVE`; spec's accepted Tree/Rose accepted, rejected Bad/Rose rejected. Mirrored in `tests/conformance/data_types`. (G1 fixed) |
| 10.4 | record parameter-positivity signature; mutual fixed-point | IMPLEMENTED+TESTED | TYP | `csPositivity` per-param signatures (built-ins seeded in `Prelude.hs`; data types computed); whole-module group greatest-fixed-point in `positivityPass`; mutual accept/reject mirrored. (G8 fixed) |
| 11.1 | stratified universes; no Type:Type | IMPLEMENTED+TESTED | TYP | `let bad:Type = Type` → mismatch `Type1` vs `Type` |
| 11.3 | universal quantification (`forall`) | IMPLEMENTED+TESTED | TYP | probes |
| 11.3.1A | row `Lacks` constraints for open-record extension | IMPLEMENTED-WEAKLY-TESTED | TYP | `E_ROW_EXTENSION_MISSING_LACKS_CONSTRAINT` registered |
| 11.4 | propositional equality; `refl` must match | IMPLEMENTED+TESTED | TYP | `refl : 1 = 2` rejected |
| 11.4 | equality match requires h-level (`E_EQUALITY_MATCH_REQUIRES_ISSET`) | UNCLEAR | TYP | portable alias absent from registry; reachable only if source equality `match` exists |
| 12.1 | function types | IMPLEMENTED+TESTED | TYP | everywhere |
| 12.2 | linear overuse / drop rejected | IMPLEMENTED+TESTED | TYP | `E_QTT_LINEAR_OVERUSE`/`_DROP` |
| 12.2.1 | erased (q0) runtime use rejected | IMPLEMENTED+TESTED | TYP | `E_QTT_ERASED_RUNTIME_USE` |
| 12.3/12.4 | borrow lifetimes / escape; disjoint path borrowing / consume-after-borrow | IMPLEMENTED+TESTED | TYP,RUN | `E_QTT_BORROW_ESCAPE`/`_OVERLAP`/`_PATH_CONSUMED` |
| 12 | quantity part of function-type identity | IMPLEMENTED+TESTED | TYP | `(0 x)->` ≠ `(1 x)->` rejected |
| 13.1 | variant types; unknown member rejected | IMPLEMENTED+TESTED | TYP | `E_VARIANT_MEMBER` |
| 13.2 | records; duplicate field / missing projection rejected | IMPLEMENTED+TESTED | TYP | `E_RECORD_DUPLICATE_FIELD`/`_PROJECTION_MISSING_FIELD` |
| 13.2.10 | sealed signatures; opaque unfolding rejected | IMPLEMENTED-WEAKLY-TESTED | TYP | `E_SEAL_*` codes; not isolated |
| 13.2.11 | existential witness non-escape | IMPLEMENTED+TESTED | TYP | rejected (leaks `@-1.⟨wit0⟩`, see §3.1.11) |
| 14.1–14.3 | traits/members/instances; coherence rejects overlap | IMPLEMENTED+TESTED | TYP,RUN | `E_INSTANCE_INCOHERENT` |
| 14.5 | declaration-level `derive` | INTENTIONALLY-UNSUPPORTED(§14.5 line 14594 "implementation-defined") | TYP | `derive Eq` → `E_UNSUPPORTED`; portable path is §22 `std.deriving.shape` |
| 15.1/15.2 | accepted termination-certified SCC MUST be well-founded (soundness) | IMPLEMENTED+TESTED | TYP | divergent `loopy` accepted only as non-reducible (`W_TERMINATION_UNVERIFIED`); not δ-unfolded; no false defeq |
| 15.3 | structural descent | IMPLEMENTED-WEAKLY-TESTED | TYP | structural recursion accepted |
| 15.11 | explicit `decreases` parses | IMPLEMENTED+TESTED | TYP | corpus |
| 16.1 | left-assoc application; non-callable / arg-mismatch rejected | IMPLEMENTED+TESTED | SYN,TYP | `5 3`→`E_APPLICATION_NONCALLABLE` |
| 16.1.1/.1.2 | dotted chains; safe-navigation `?.` | IMPLEMENTED+TESTED | SYN | `ob?.val` |
| 16.1.2 | elvis `?:` prec 2 right-assoc | IMPLEMENTED+TESTED | SYN | `None ?: 7`→7 |
| 16.2 | lambdas | IMPLEMENTED+TESTED | SYN,TYP | |
| 16.3 | implicit args/holes; unsolved/ambiguous rejected | IMPLEMENTED+TESTED | SYN,TYP | `E_UNSOLVED_IMPLICIT`/`E_IMPLICIT_AMBIGUOUS` |
| 16.3.4 | `is` tag-test; chaining is parse error | IMPLEMENTED+TESTED | SYN | `o is Some` |
| 16.4 | `if/elif/else`; `if` as value needs else | IMPLEMENTED+TESTED | SYN,TYP | `E_IF_MISSING_ELSE` |
| 16.1.4 | quantity subsumption via elaboration eta | IMPLEMENTED-WEAKLY-TESTED | TYP | corpus only |
| 17.1 | non-exhaustive match rejected with missing cases | IMPLEMENTED+TESTED | TYP | `E_PATTERN_NON_EXHAUSTIVE` (missing cases in prose, not payload) |
| 17.2.x | pattern forms; duplicate-binder; or-pattern binder agreement; ctor arity | IMPLEMENTED+TESTED | SYN,TYP | `E_DUPLICATE_PATTERN_BINDER`/`E_OR_PATTERN_BINDER_MISMATCH` |
| 17.3 | active patterns | IMPLEMENTED+TESTED | TYP | corpus `active_patterns` |
| 17 | flow/branch refinement | IMPLEMENTED-WEAKLY-TESTED | TYP | corpus, not isolated |

### Part IV — Effects, errors, collections (§18–§20)

| § | requirement (short) | status | lane | evidence / note |
|---|---|---|---|---|
| 18.1.14/.15/.18/.22 | `Eff r a`; `runPure`; shallow/deep handlers; deep reinstall | IMPLEMENTED+TESTED | RUN | `deep-handler-state`→20 |
| 18.2 | `do` blocks; sequencing; binds | IMPLEMENTED+TESTED | RUN,SYN | |
| 18.3 | `!e` splice in statement / `let x <- !e` | IMPLEMENTED+TESTED | RUN | `sp4`/`sp5` |
| **18.3.1** | **`!e` splice in `let x = !e` position** | **MISSING** | RUN,V | `let x = !(getN 1)` → `E_SPLICE_OUTSIDE_DO` though inside `do`; re-verified. Spec's own canonical example. **MAJOR** |
| **18.3.1** | **immediate-application splice `!f x` = `!(f x)` (not `(!f) x`)** | **SPEC-CONFLICT(§18.3.1)** | RUN | `!doit 8` parsed as `(!doit) 8` → type mismatch. **MAJOR** |
| 18.4 | statement-if (no else) = implicit `pure ()` | IMPLEMENTED+TESTED | RUN | todo.kp |
| 18.5/18.6 | `return`; `while`; `for … in list`; loop `else`; labeled break/continue; outside-loop rejected | IMPLEMENTED+TESTED | RUN | `break@outer`; `E_BREAK_OUTSIDE_LOOP` |
| 18.6 | `for x in <range>` (range as loop source) | MISSING | RUN | `for x in 1..3 do` → type mismatch `NumericRange` vs `List`; no `IntoQuery` |
| 18.6.1/18.7 | `var` mutable (read/assign); `defer` LIFO once on every exit | IMPLEMENTED+TESTED | RUN | IORef; `defer` order body,b,a |
| 18.8.3 | exit actions once on abrupt exit | IMPLEMENTED-WEAKLY-TESTED | RUN | finally path verified; unwind-on-return not re-probed |
| 18.9 | `inout` parameters | UNCLEAR | RUN | not probed (cross-lane) |
| 19.2/19.4 | `try/except/finally`; `raise` | IMPLEMENTED+TESTED | RUN | `caught: boom / finally / after` |
| 19.1/19.2/19.5 | `MonadError`/`MonadFinally`/`MonadResource` trait surface + `bracket`/`acquireRelease` | MISSING | RUN | each → `E_NAME_UNRESOLVED`; §28.2-required names |
| 20.1 | list/set/map literals | IMPLEMENTED+TESTED | RUN | `{ "a":1 }` etc |
| 20.2 | `..`/`..<` range construction; `Rangeable` instances | IMPLEMENTED-WEAKLY-TESTED | RUN | constructs `NumericRange` but not iterable |
| 20.2 | iterating a range governed by `IntoQuery` | MISSING | RUN | `IntoQuery` trait absent |
| 20.3/20.4 | comprehensions; clauses (`for`/`let`/`if`); encounter order | IMPLEMENTED+TESTED | RUN | `[ for x in .. yield x*x ]` |
| 20.4 | borrowed generators `for x in &coll` | UNCLEAR | RUN | borrow lane; `Borrow*IntoQuery` names MISSING |
| 20.6/20.7/20.9 | order by/paging/distinct; grouping; custom sinks | IMPLEMENTED(+/-WEAK) | RUN | `order by`/`distinct` verified; grouping not value-probed |
| 20.8 | joins | UNCLEAR | RUN | suite exists; not probed |
| 20.10/.11 | normative lowering to query core; list-backed as-if | IMPLEMENTED-WEAKLY-TESTED | RUN | identity on element stream |

### Part V–VI — Macros / staging / dynamics / boundary / FFI (§21–§26)

| § | requirement (short) | status | lane | evidence / note |
|---|---|---|---|---|
| 21.1–21.2 | quotation `'{ }`, splices, `Elab` monad | IMPLEMENTED-WEAKLY-TESTED | META | macro stress (300/600/1200 sites) linear; full reflection surface not exhaustively verified |
| 22 | derivation-shape reflection | UNCLEAR | META,TYP | corpus passes; depth not disproven |
| 23.2 | staged code `.<e>.` / `.~c` | IMPLEMENTED-WEAKLY-TESTED | META | conformance staging fixtures pass |
| 24 | dynamic values / runtime representations | INTENTIONALLY-UNSUPPORTED(scope rule; §1.1 boundary-only) | META | no host boundary; no clause mandates a `Dynamic` surface for a pure interpreter |
| 25 | boundary contracts / bridge packages | INTENTIONALLY-UNSUPPORTED(§25 conditional on a boundary; Appendix O roadmap) | META | absent; no boundary crossed |
| 26 | FFI / host bindings / native ABI / bridges | INTENTIONALLY-UNSUPPORTED(§36.28/§36.30 build-system/profile-scoped) | META | no FFI surface offered |

### Part VII — Backends, prelude, std modules (§27–§29)

| § | requirement (short) | status | lane | evidence / note |
|---|---|---|---|---|
| 27.1–27.5A | native/JVM/CLR/wasm/js/python backend profiles | INTENTIONALLY-UNSUPPORTED(§27.7 per-profile conformance) | META | no code generators; interpretation sanctioned |
| 27.6 | runtime capability profiles (`rt-core`, `rt-multishot-effects`, `rt-atomics`) | INTENTIONALLY-UNSUPPORTED(§27.6 backend-capability gates) | META,RUN | interpreter advertises none; rejects via name-unresolved |
| 27.7 | backend conformance per-profile | N/A (the scoping clause) | META | cited by other rows |
| 28.1 | implicit `import std.prelude.*` + fixed unqualified ctor subset | IMPLEMENTED+TESTED | RUN | all conformance uses these |
| 28.2 | core types (Unit…Ordering); Array/Set/Map/List types | IMPLEMENTED+TESTED | RUN | types resolve |
| 28.2 | `Rational` type exported (MUST) | MISSING | RUN,V | `r : Rational` → `E_NAME_UNRESOLVED`; re-verified. **MAJOR** |
| 28.2 | numeric/comparison/applicative/fold/show terms | IMPLEMENTED+TESTED | RUN | resolve and run |
| 28.2 | `(~=)` equivalence operator | MISSING | RUN | `1 ~= 1` → `E_NAME_UNRESOLVED '~='`. **MAJOR** |
| 28.2 | `for_`, `sequence_` | MISSING | RUN | unresolved. **MINOR** |
| 28.2 | proof helpers `absurd pathInd subst sym trans cong unsafeAssertProof witness measureRelation lexRelation` | MISSING | RUN | only `summon` present. **MAJOR** |
| 28.2 | surface collection terms (array*/set*/map*/sizedArray*) | MISSING | RUN | only internal `__*` prims + `listLength`/`listAppend`. **MAJOR** |
| 28.2 | resource/finalize, fibers/scopes/promises, STM, time terms | MISSING(names) | RUN | unresolved; §27.6 `rt-core`-tension flagged (see ledger) |
| 28.2 | required trait names `Equiv Alternative Iterator MonadError MonadFinally MonadResource MonadRef WellFoundedRelation IntoQuery BorrowSourceIntoQuery BorrowItemsIntoQuery QuotedLiteralMacro` | MISSING | RUN | each unresolved. **MAJOR** |
| 28.2.1 | partial-op proof obligations (`subDefined`/`divDefined`/`modDefined`); no unchecked/wrapping under these names | IMPLEMENTED+TESTED | RUN | div-by-zero/mod-by-zero/Nat-underflow rejected |
| 28.2.2 | algebraic trait hierarchy `AdditiveMonoid…FieldLike OrderedSemiring` | MISSING | RUN | absent. **MAJOR** |
| 28.2.2 | `EuclideanSemiring` = refinement of `(Semiring,Ord,CheckedDiv,CheckedMod)` | SPEC-CONFLICT(§28.2.2) | RUN | present trait has wrong shape (`euclideanDivMod : a->a->(a,a)`, no superclasses) |
| 28.2.3 | numeric instances for Integer/Int | IMPLEMENTED+TESTED | RUN | present |
| 28.2.3 | `CheckedSub Nat` and `CheckedSub Float/Double` | MISSING | RUN | unsolved-implicit on `Nat 3-5` and `Double 5.0-2.0`. **MAJOR** |
| 28.2.3 | Rational instances; algebraic instances | MISSING | RUN | depend on absent type/traits |
| 28.2.3 | fixity table | IMPLEMENTED+TESTED | RUN | `Resolve.defaultFixities` 1:1 |
| 28.2.3 | Float/Double MUST NOT receive Semiring/Ring/FieldLike | IMPLEMENTED(vacuously) | RUN | traits absent |
| 29.1 | `std.atomic` iff backend advertises `rt-atomics` | INTENTIONALLY-UNSUPPORTED(§29.1/§27.6) | RUN | embedded surface present; semantics not realized |
| 29.2 | `std.supervisor` (unconditional MUST) | IMPLEMENTED-WEAKLY-TESTED | RUN,V | `import std.supervisor` resolves (re-verified exit 0); semantics tied to `rt-core` |
| 29.3 | `std.hash` (unconditional MUST); deterministic mixing; Hashable instances | IMPLEMENTED+TESTED | RUN | `hashWith` deterministic; FNV-1a |
| 29.4 | `std.unicode` (unconditional MUST) | IMPLEMENTED-WEAKLY-TESTED | RUN | core ops work; incremental decoder/builders/cursors MISSING |
| 29.5 | `std.bytes` (unconditional MUST) | MISSING | RUN,V | `import std.bytes` → `E_MODULE_NAME_UNRESOLVED`; re-verified; no gate exists. **MAJOR** |
| 29.6 | `std.debug` (MUST only when `allow_debug_introspection`) | INTENTIONALLY-UNSUPPORTED(§29.6) | RUN | gate not enabled |
| 29.7/29.8 | `std.config`/`std.build` (MUST only for config/build-supporting impls) | INTENTIONALLY-UNSUPPORTED(§29.7/§35, §29.8/§36) | RUN | profile-scoped |

### Part VIII — Core semantics (§30–§33)

| § | requirement (short) | status | lane | evidence / note |
|---|---|---|---|---|
| 30.1 | elaboration to KCore | IMPLEMENTED+TESTED | TYP | runs/checks |
| 30.2 | KCore de Bruijn; canonical record/variant order | IMPLEMENTED+TESTED | TYP | `CRecordT`/`CVariantT` canonical |
| 30.2.3 | every synthetic KCore node MUST carry provenance (origins + introduction kind) | MISSING | TYP | `Term` has no origin field. **MAJOR** (dump part is §34/profile-scoped) |
| 30.2.3A | erasure justifications per erased occurrence | MISSING | TYP | KCore-justification form is core; audit-table form is §34 |
| 31.1 | β/δ/ι/η reduction; quantity invariant in defeq; fuel-bounded but sound | IMPLEMENTED+TESTED | TYP,RUN | `two=2; refl:two=2` accepts; divergent not equated |
| 31.1 | η records; zero-field ≡ Unit | IMPLEMENTED+TESTED | TYP | `r=(x=r.x,y=r.y)` by refl |
| 31.2 | erasure deletes q0/RuntimeErased/meta-phase; erasure audit before KBackendIR | INTENTIONALLY-UNSUPPORTED(§27.7 backend-scoped) | TYP,RUN | tree-walking interpreter; no KBackendIR; q0 use statically rejected |
| 31.3 | variant runtime tag (stable TagId, not ordinal) | INTENTIONALLY-UNSUPPORTED(§27.7) | TYP | `CInject` tags by member identity |
| 31.4 | record canonicalization | IMPLEMENTED+TESTED | TYP | canonical field order |
| 32.1 | strict CBV L→R; `if`/`match` once; thunk/lazy/force; divergence → diagnostic | IMPLEMENTED(+/-WEAK) | RUN | match-once verified; pure L→R side-effect order not observable |
| 32.2 | IO/fibers/STM/interruption runtime model | INTENTIONALLY-UNSUPPORTED(§27.6/§32.2 reject-if-uncapable) | RUN | IO+refs+algebraic-effect handlers implemented; fibers/STM/timers not |
| 32.2 | handler capture/resume/abandon | IMPLEMENTED+TESTED | RUN | deep/shallow/multishot |
| 33.1.1/33.1.2 | Easy/Hard hash machinery; persistent `EasyHash→HardIdentity` cache | MISSING(machinery)/INTENTIONALLY-UNSUPPORTED(cache is §33.1.2 package-mode MUST; §36 profile-scoped) | RUN | no hash code; script-mode default `semantic-if-available` permits fallback |
| 33.2.1 | instance coherence ≤1 distinct semantic impl per ground evidence | IMPLEMENTED+TESTED | RUN,TYP | `E_INSTANCE_INCOHERENT` |
| 33.2.1 | harmless overlap accepted for canonically-identical instances | UNCLEAR | RUN | not constructible cheaply; conservative rejection permitted by `semantic-if-available` |
| 33.2.2 | fast-path defeq via HardIdentity | INTENTIONALLY-UNSUPPORTED(§33.2.2 "MAY") | RUN | §31.1 conversion is the normative path |

### Part IX–X — Pipeline / config / build / IDE (§34–§37) + appendices

| § | requirement (short) | status | lane | evidence / note |
|---|---|---|---|---|
| 34.1.3–34.1.7 | compiler observability (stage dumps/checkpoints) — §4.1 "ordinary required tooling" | UNCLEAR(MISSING-or-PROFILE) | META | no checkpoint serialization; §37.3 tiers tooling profiles. Best read: dump *content* profile-scoped, but §T.5.3 should `harnessError` on unknown checkpoint, not silently `unsupported` |
| 34.1.6A | conformance-verification mode | UNCLEAR/PROFILE | META | not implemented; profile-scoped per scope rule |
| 34.2–34.5 | KFrontIR / KBackendIR / runtime obligations / intrinsics | PARTIAL/INTENTIONALLY-UNSUPPORTED(§27.7) | META | KFrontIR error-tolerance exists; KBackendIR absent (backend profile-scoped) |
| 35.1–35.13 | config mode (units/profiles/evaluator/`.kcfg`/`kappa.build.kp`) | INTENTIONALLY-UNSUPPORTED(§35 intro: separate mode by role/ext/flag/API) | META | no config-mode CLI surface |
| 36.* | build system (manifest/plan/lockfile/targets/providers/publish) | INTENTIONALLY-UNSUPPORTED(separate tool layer; §36.28/§36.30 host-binding/bridge profile-scoped) | META | no manifest parsing |
| 37.3.1 | Tooling Core profile (analysis session, LSP, structured diagnostics) | INTENTIONALLY-UNSUPPORTED for LSP/session(§37.3 profile tiers) | META | BUT §37.3.1's "machine-readable structured diagnostics" reinforces the CORE §3.1.1 gap |
| 37.3.2–37.3.4 | First-Class/Broad-Compat/Syntax-Only client profiles | INTENTIONALLY-UNSUPPORTED(§37.3 tiers) | META | not provided |
| App. B/G/H/M/N/O | pipe operators; ApplicativeDo; flow-typing/modal/control/graduality (non-normative) | IMPLEMENTED-WEAKLY-TESTED / N/A | SYN,META | pipe ops used in conformance; rest non-normative/roadmap |
| App. T.1–T.5.2/T.5.4/T.9/T.10 | harness forms, config, diagnostic/type/run assertions, determinism, P0 alias suite | IMPLEMENTED(+/-WEAK) | META | core assertions faithful; `assertType`/`assertDeclKinds`/run assertions work |
| App. T.5.1 | structured diagnostic assertions (`assertDiagnosticPayload/Label/Related/Fix*/Suppressed`) | SPEC-CONFLICT(§T.8) | META | hard-coded `unsupported` though standard, ungated, non-`x-`. Never false-passes |
| App. T.5.1 | purely numeric codes invalid → harnessError | SPEC-CONFLICT(§T.5.1) minor | META | `assertDiagnostic error 12345` → FAIL not HARNESS-ERROR |
| App. T.5.3 | `assertStageDump` checkpoint compare | SPEC-CONFLICT(§T.8) | META | blanket `unsupported`; should `harnessError` on unknown checkpoint or require gate |
| App. T.4 | `runArgs`/`stdinFile` standard config | SPEC-CONFLICT(§T.8) | META | downgraded to `unsupported` though standard/ungated |
| App. T.6 | duplicate config key w/ different values → ill-formed | SPEC-CONFLICT(§T.6) minor | META | only `mode` conflict-checked; `dumpFormat` dup → PASS |
| App. T.2 | nested dir of `.kp` treated as one directory suite | MISSING(minor) | META | recursive walk runs them as independent single-file tests; correct via `--suite` |
| App. T.7 | incremental step suites | INTENTIONALLY-UNSUPPORTED(§T.4 unmet `requires capability incremental`) | META | classified `unsupported` (defensible) |

---

## Consolidated legitimate-gap worklist (ranked, in-scope MUST/SHALL only)

Deduped across lanes. In-scope = CORE per the task (Parts I–IV, VII §28–§29, VIII
§30–§33, the §3 diagnostic contract, §4 unsafe/debug which has no optionality
clause). Profile-scoped items excluded (see ledger). Severity: BLOCKER (soundness
or whole-contract) > MAJOR > MINOR.

| id | § | severity | one-line failing probe | fix locus |
|----|---|----------|------------------------|-----------|
| G1 | 10.4 | RESOLVED (was BLOCKER, soundness) | `data Bad = MkBad (Bad -> Bad)` → `E_DATA_NOT_STRICTLY_POSITIVE` (was exit 0) | DONE: `positivityPass` in `src/Kappa/Check.hs` runs the §10.4 strict-positivity check after the header pass; mirrored in `tests/conformance/data_types` |
| G2 | 6.1.1 | BLOCKER (silent miscompile) | `0xDEAD_BEEF` → `59776745199` (≠ `3735928559`); `0b1_0_1_0`→1748; `0o1_2_3`→25027 | `src/Kappa/Lexer.hs:462` fold over `T.filter (/= '_') digits` (radix path, like the decimal path at :488) |
| G3 | 3.1.1 | BLOCKER | `kappa check --json FILE` → usage; no JSON producer in src | `src/Kappa/Diagnostic.hs` (hand-rolled JSON over enriched record, boot pkgs only) + `app/Main.hs` (`--json` on cmdCheck/cmdRun) |
| G4 | 3.1.1A | BLOCKER | `E_IMPLICIT_AMBIGUOUS`/`E_INSTANCE_INCOHERENT`/type-mismatch carry no related origins; `Diagnostic` has no `related` field | `src/Kappa/Diagnostic.hs` add `dRelated :: [RelatedOrigin]` (role enum); thread sites in `Check.hs`/`Resolve.hs`/`Usage.hs` |
| G5 | 5.5.1.1, 5.5.3 | MAJOR | `(5 ?)` with `postfix 90 (?)` → `E_APPLICATION_NONCALLABLE`; `let b = 5 ?` corrupts next decl | `src/Kappa/Resolve.hs:390` add `postfixOf` branch mirroring 394-401; `src/Kappa/Parser.hs` chain path (~1540-1583) tolerate trailing postfix |
| G6 | 18.3.1 | MAJOR | `let x = !(getN 1)` inside `do` → `E_SPLICE_OUTSIDE_DO` (spec's canonical example) | `src/Kappa/Check.hs` `elabDoIOItems` `DoLet` branch (~6884): apply `desugarBang rhs` like `DoExpr`/`DoBind` |
| G7 | 18.3.1 | MAJOR (SPEC-CONFLICT) | `!doit 8` parsed as `(!doit) 8` → type mismatch; spec forbids this parse | `src/Kappa/Check.hs` `desugarBang (EApp …)` (~7114-7130) capture whole application spine; do not recurse into head |
| G8 | 10.4 | RESOLVED (was MAJOR) | `data Rose a = Node a ((Rose a -> a) -> Rose a)` → `E_DATA_NOT_STRICTLY_POSITIVE` (was accepted) | DONE: parameter-positivity signatures in `csPositivity` (built-ins seeded in `Prelude.hs`, data types computed); whole-module group greatest-fixed-point in `positivityPass`; mutual accept/reject mirrored in `tests/conformance/data_types` |
| G9 | 3.1.9 + 3.2.x | MAJOR | type-mismatch/exhaustiveness payloads only in prose; harness `assertDiagnosticPayload` → unsupported | `src/Kappa/Diagnostic.hs` add `dPayload`; populate in `src/Kappa/Check.hs` producers |
| G10 | 3.1.5A + 30.2.3 | MAJOR | `Core.hs` `Term` carries no provenance; no `ProvenanceFrame` type | `src/Kappa/Core.hs` origin/provenance on synthetic terms (or side table); populate in `src/Kappa/Check.hs` insertions |
| G11 | 3.1.11 | MAJOR | `?m1236`, `@-1.⟨wit0⟩` leak as the sole `actual:` type rendering | `src/Kappa/Pretty.hs` metavariable/rigid rendering + zonk-before-render in `Check.hs` mismatch path |
| G12 | 3.1.6, 3.1.7 | MAJOR | no `fixes` field; only prose `helps`; harness `assertDiagnosticFix*` → unsupported | `src/Kappa/Diagnostic.hs` (`DiagnosticFix`/`SourceEdit`) + producers |
| G13 | 4.1, 4.2 | MAJOR | `assertTerminates`/`assertReducible`/`unsafeAssertProof` unrecognized (parse/resolve error); `unhide`/`clarify` parse but never gated | `src/Kappa/Parser.hs` recognize the decl forms; add `allow_*` build-config record; gate in `Check.hs`/`Resolve.hs` per §4.2 |
| G14 | 29.5 | MAJOR | `import std.bytes` → `E_MODULE_NAME_UNRESOLVED` (unconditional MUST, no gate) | add `stdBytesSource` to `src/Kappa/Prelude.hs`; wire in `src/Kappa/Pipeline.hs:80` |
| G15 | 28.2 | MAJOR | `Rational` type + required FieldLike/numeric instances absent | `src/Kappa/Prelude.hs` add `Rational` type + §28.2.3 instances |
| G16 | 28.2.2, 28.2.3 | MAJOR | `AdditiveMonoid`/`Semiring`/`Ring`/`FieldLike`/`OrderedSemiring` traits + instances absent | `src/Kappa/Prelude.hs` add hierarchy with law members + instances; correct `EuclideanSemiring` shape |
| G17 | 28.2, 19.x, 20.2 | MAJOR | required trait names `Equiv Alternative Iterator MonadError MonadFinally MonadResource MonadRef WellFoundedRelation IntoQuery Borrow*IntoQuery QuotedLiteralMacro` all `E_NAME_UNRESOLVED` | `src/Kappa/Prelude.hs` `preludeSource` declare these abstract traits |
| G18 | 28.2 | MAJOR | `(~=)` + `Equiv` absent → `E_NAME_UNRESOLVED '~='` | `src/Kappa/Prelude.hs` (`(~=)`+`Equiv`) + `src/Kappa/Resolve.hs` add `~=` to `defaultFixities` (prec 40 = `==`) |
| G19 | 28.2 | MAJOR | surface collection terms (`arrayFromList`/`mapEmpty`/`setEmpty`/… ) `E_NAME_UNRESOLVED`; only internal `__*` prims | `src/Kappa/Prelude.hs` export §28.2 Array/Set/Map/SizedArray ops over existing carriers/prims |
| G20 | 28.2 | MAJOR | proof helpers `absurd subst sym trans cong pathInd unsafeAssertProof witness measureRelation lexRelation` `E_NAME_UNRESOLVED` | `src/Kappa/Prelude.hs` declare (several have spec-given bodies via `pathInd`) |
| G21 | 28.2.3 | MAJOR | `CheckedSub Nat` and `CheckedSub Float/Double` missing → unsolved-implicit on `Nat 3-5`, `Double 5.0-2.0` | `src/Kappa/Prelude.hs` add `CheckedSub Nat`(`subDefined=y<=x`)/`Double`/`Float`(`subDefined=True`) |
| G22 | 6.3.4.1 | MINOR | `f"cost: \$5"` → `E_STRING_ESCAPE_INVALID` | `src/Kappa/Lexer.hs:724-725` emit `'$'` only (drop backslash) or add `\$` case to `decodeEscapes` |
| G23 | 8.3 | MINOR | `import M.(type T(..) as U)` accepted (spec says ill-formed) | `src/Kappa/Parser.hs:865` reject `ctorAll && isJust alias` (e.g. `E_IMPORT_ITEM_MALFORMED`) |
| G24 | 5.5.1 | MINOR | bare `(-)` with both `infix -` and `prefix -` in scope accepted (no `E_*AMBIGUOUS`) | `src/Kappa/Check.hs` where `EOpRef Nothing` is elaborated: reject >1 callable fixity w/o disambiguating expected type |
| G25 | 28.2 | MINOR | `for_`, `sequence_` `E_NAME_UNRESOLVED` | `src/Kappa/Prelude.hs` add discard-variants |
| G26 | 20.2, 18.6 | MINOR | range not iterable in `for`/comprehension (`IntoQuery` mechanism absent) | `src/Kappa/Prelude.hs` `IntoQuery` + instances; `src/Kappa/Check.hs` dispatch `for`/comprehension source through `IntoQuery` |
| G27 | 29.4 | MINOR | `std.unicode` incremental decoder/builders/cursors absent (self-documented) | `src/Kappa/Prelude.hs` `stdUnicodeSource` + prims in `src/Kappa/Eval.hs` |
| G28 | 3.1.11, 3.1.10 | MINOR | no `suppressed` field; cascades emitted independently | `src/Kappa/Diagnostic.hs` + `src/Kappa/Pipeline.hs` aggregation |
| G29 | 3.1.2A | MINOR | `ExplainEntry` lacks stability/defaultSeverity/payloadSchema/introducedIn/owner | `src/Kappa/Explain.hs` |
| G30 | 3.1.13 | MINOR (SHOULD) | `kappa explain kappa.type.mismatch` → "unknown diagnostic code" | `app/Main.hs` `cmdExplain` wire family lookup (`Explain.explainExists` already supports it) |
| G31 | 3.1.14A | MINOR | no typed `RecoveryNode`s (soundness clause "no false accept" IS honored) | `src/Kappa/Parser.hs` + `src/Kappa/Parser/Monad.hs` |
| G32 | App. T.8 (T.5.1/T.5.3/T.4) | MINOR (harness) | standard `assertDiagnosticPayload/Label/Related/Fix*/Suppressed`, `assertStageDump`, `runArgs`, `stdinFile` → `unsupported` though ungated/standard | `src/Kappa/TestHarness.hs:175-185,292-293,681-682` (mostly resolved once G3/G9/G12 land) |
| G33 | App. T.5.1 | MINOR (harness) | `assertDiagnostic error 12345` → FAIL not HARNESS-ERROR | `src/Kappa/TestHarness.hs` `parseDirective` validate code shape |
| G34 | App. T.6 | MINOR (harness) | `dumpFormat json`+`dumpFormat sexpr` → PASS (should be ill-formed) | `src/Kappa/TestHarness.hs:679` generalize dup-key check beyond `mode` |
| G35 | App. T.2 | MINOR (harness) | nested dir of `.kp` run as independent tests, not one suite | `src/Kappa/TestHarness.hs` `isSuiteRoot`/`runTestPathAt` walk policy |
| G36 | 4.7 | MINOR | no unsafe/debug audit ledger + `auditModule/Package/Artifact` queries (MUST) | predicated on G13; tied to separate-compilation artifacts (profile-adjacent), ranked last |

Total worklist items: 36 (4 BLOCKER, 17 MAJOR, 15 MINOR). Harness-faithfulness
items G32–G35 are non-deceptive (fail-safe to `unsupported`/`fail`, never false PASS).

---

## Profile-scoped ledger

Each unimplemented Part/area, with the exact spec clause that permits scoping, or
flagged MISSING if no such clause exists.

| area | § | scoping citation | verdict |
|------|---|------------------|---------|
| Backend code generators (native/JVM/CLR/wasm/js/python) | 27.1–27.5A | §27.7 "A backend profile is conforming iff …" — backends independently conforming; interpretation sanctioned | PROFILE-SCOPED (cited) |
| Runtime capability profiles (`rt-core`, `rt-multishot-effects`, `rt-atomics`) | 27.6 | §27.6 backend-capability gates; §32.2 "a backend that cannot satisfy a required capability MUST reject the affected program" | PROFILE-SCOPED (cited) |
| Fibers/scopes/monitors/promises/STM/monotonic-timers (terms) | 28.2 / 32.2 | §27.6 `rt-core`; §32.2 reject-if-uncapable | PROFILE-SCOPED **with tension**: §28.2 still lists them as prelude-surface terms the prelude MUST export; today they are not even nameable, so rejection is at the resolution layer, not a clean capability diagnostic. Flagged for adjudication; a stricter reading makes the *surface absence* a §28.2 gap |
| `std.atomic` | 29.1 | §29.1 "Implementations that advertise backend capability `rt-atomics` MUST provide…" | PROFILE-SCOPED (cited) |
| `std.debug` | 29.6 | §29.6 MUST only "when `allow_debug_introspection` is enabled" | PROFILE-SCOPED (cited) |
| `std.config` | 29.7 | §29.7 MUST only for impls "supporting config mode" (§35) | PROFILE-SCOPED (cited) |
| `std.build` | 29.8 | §29.8 MUST only for impls "supporting build manifests" (§36) | PROFILE-SCOPED (cited) |
| Physical erasure pass + erasure audit + KBackendIR verifier | 31.2 | §27.7 backend profiles conforming-per-profile; no KBackendIR | PROFILE-SCOPED (cited); erasure *soundness* observed (q0 use statically rejected) |
| Variant runtime tag representation | 31.3 | §27.7 backend-representation detail | PROFILE-SCOPED (cited); `CInject` tags by identity, consistent with "not by ordinal" |
| Full §32.2 IO/fibers/STM/interruption runtime model | 32.2 | §27.6/§32.2 reject-if-uncapable | PROFILE-SCOPED (cited); IO+refs+algebraic-effect handlers ARE implemented |
| Easy/Hard hash machinery + persistent cache | 33.1.1/33.1.2 | persistent `EasyHash→HardIdentity` cache is a §33.1.2 **package-mode** MUST; §36 package mode profile-scoped; script-mode default `semantic-if-available` permits fallback | PROFILE-SCOPED (cited); only externally-observable §33 MUST (coherence §33.2.1) IS enforced |
| Fast-path defeq via HardIdentity | 33.2.2 | §33.2.2 "MAY" | OPTIONAL (cited) |
| KCore *dump* exposing provenance | 30.2.3 / 34 | §34 compiler-pipeline dump machinery; scope rule | PROFILE-SCOPED (cited) — note the *carrying* requirement is CORE = gap G10 |
| Erasure audit-table form | 30.2.3A / 34 | §34/backend | PROFILE-SCOPED (cited) — KCore-justification form is CORE = noted under G10 |
| Stage dumps / checkpoints (content) | 34.1.3–34.1.7 | §37.3 tiers tooling profiles; scope rule treats compiler-pipeline dump machinery as profile-scoped | PROFILE-SCOPED **with caveat**: §4.1 line 4223 calls these "ordinary required tooling facilities," arguing against full optionality; best read = dump *content* profile-scoped but the §T.5.3 harness directive should `harnessError` on an unknown checkpoint, not silently `unsupported` (= G32) |
| Conformance-verification mode | 34.1.6A | scope rule (compiler-pipeline machinery) | PROFILE-SCOPED/UNCLEAR (cited) |
| KBackendIR / target lowering | 34.2–34.5 | §27.7 backend profile-scoped | PROFILE-SCOPED (cited) |
| Config mode | 35.* | §35 intro: separate mode selected "by role, file extension, command-line option, or embedding API" | PROFILE-SCOPED (cited) |
| Build system | 36.* | separate package/build tool layer; §36.28/§36.30 host-bindings/bridges profile-scoped | PROFILE-SCOPED (cited) |
| LSP / analysis-session / semantic-query surface | 37.3.* | §37.3 explicitly divides IDE support into conformance profiles (Tooling Core/First-Class/Broad-Compat/Syntax-Only) | PROFILE-SCOPED (cited) — but §37.3.1's "machine-readable structured diagnostics" reinforces CORE §3.1.1 = G3 |
| Dynamics / boundary contracts / FFI / bridges | 24/25/26 | §25 conditional on a boundary; §1.1 boundary honesty applies only when a foreign connection exists; §36.28/§36.30 profile-scoped; Appendix O roadmap | PROFILE-SCOPED (cited) |
| Incremental step suites + `stageDumps` harness capability | App. T.7 / T.4 | §T.4 lists `incremental`/`stageDumps` as optional capabilities; unmet `requires capability` → §T.8 `unsupported` | PROFILE-SCOPED (cited) — un-gated downgrade is G32 |
| **§4 unsafe/debug language forms (`unhide`/`clarify`/`assertTerminates`/`assertReducible`/`assertTotal`/`unsafeAssertProof`)** | 4.1–4.5 | **NO clause makes §4 optional.** §4.1 line 4220: "These facilities remain part of the language specification" | **MISSING — flagged (= G13). Profile-scoped-WITHOUT-citation.** |
| **§4.7 unsafe/debug audit ledger + audit queries** | 4.7 | partially separate-compilation-adjacent, but §4.7 line 4385 is an unconditional MUST for artifacts carrying unsafe use | **MISSING — flagged (= G36). Vacuous today (no §4 features) but the audit-query surface MUST is unmet; no clause cited as optional.** |

Profile-scoped-WITHOUT-citation (= real gaps already counted in the worklist):
**2** areas — §4.1–§4.5 (G13) and §4.7 (G36). All other profile-scoped areas have
an explicit permitting clause.

---

## Spec conflicts

| id | § | conflict | lane |
|----|---|----------|------|
| C1 | 6.1.1 | Underscores in hex/oct/bin literals change the value (`0xDEAD_BEEF`→`59776745199`); spec says "no semantic effect" | SYN,V (= G2) |
| C2 | 18.3.1 | `!f x` parsed as `(!f) x`; spec line: "It is not parsed as `(!f) x y`" | RUN (= G7) |
| C3 | 28.2.2 | `EuclideanSemiring` present with signature `euclideanDivMod : a -> a -> (a,a)`, no superclasses; spec defines it as a law-member refinement of `(Semiring,Ord,CheckedDiv,CheckedMod)` | RUN (part of G16) |
| C4 | 3.1.11 | Internal metavariable / witness names (`?m1236`, `@-1.⟨wit0⟩`) rendered as the sole user-facing explanation; §3.1.11 forbids exposing generated metavariable/sentinel names as the only explanation | TYP (= G11) |
| C5 | App. T.8 | `unsupported` outcome used for standard, ungated, non-`x-` directives (`assertDiagnosticPayload/Label/Related/Fix*/Suppressed`, `assertStageDump`, `runArgs`, `stdinFile`); §T.8 permits `unsupported` only for unmet `requires` or unsupported `x-` | META (= G32) |
| C6 | App. T.5.1 | Purely-numeric diagnostic code (`12345`) treated as a valid code (FAIL) instead of `harnessError`; §T.5.1 says numeric codes are not valid | META (= G33) |
| C7 | App. T.6 | Duplicate config key with different values not detected (except `mode`); §T.6 says suite is ill-formed | META (= G34) |

Note: C1/C2/C4 are the same defects as worklist BLOCKER/MAJOR items; listed here
because the implementation actively contradicts normative text (not mere absence).

---

## Unclear (need spec re-reading or a deeper probe)

| id | § | question | lane |
|----|---|----------|------|
| U1 | 11.4 / 3.2.3 | Portable alias `E_EQUALITY_MATCH_REQUIRES_ISSET` is absent from registry and src. Becomes a confirmed §3.2.3 gap **iff** the impl supports equality `match` requiring UIP/IsSet; if equality elimination is restricted to `subst`/`pathInd` the condition is unreachable. Needs a probe writing an equality `match` | TYP |
| U2 | 3.1.10 | Obligation-provenance / diagnostic-selection determinism: selection appears deterministic across reruns but no obligation records are exposed; cannot fully verify | TYP |
| U3 | 3.1.12 | Source-oriented warning hygiene / generated-use accounting not exercised | TYP |
| U4 | 22 | Depth of §22 derivation-shape reflection API not independently disproven (corpus passes) | META,TYP |
| U5 | 18.9, 20.4, 20.8 | `inout` parameters, borrowed generators (`for x in &coll`), joins — deferred (borrow lane); likely the `Borrow*IntoQuery` names being MISSING makes borrowed generators a gap, but not disproved | RUN |
| U6 | 33.2.1 | Harmless-overlap acceptance for canonically-identical-but-structurally-different instances not verified; conservative rejection permitted by `semantic-if-available` | RUN |
| U7 | 34.1.3–34.1.7 / 4.1 | §4.1 calls stage dumps "ordinary required tooling" (argues against optionality) while §37.3 tiers tooling profiles — exact line between profile-scoped dump *content* and a required *checkpoint vocabulary* needs adjudication (drives whether G32's `assertStageDump` should `harnessError` vs require a gate) | META |
| U8 | 32.1 | Pure-application left-to-right side-effect order not directly observable (no pure side effects; relies on monadic order); G6 `DoLet` splice bug blocks the cleanest probe | RUN |

---

## Summary counts

- Total requirement rows audited (this consolidated matrix): **191**
  - IMPLEMENTED+TESTED: 78
  - IMPLEMENTED-WEAKLY-TESTED: 41
  - MISSING: 38
  - INTENTIONALLY-UNSUPPORTED (cited): 26
  - SPEC-CONFLICT: 7
  - UNCLEAR: 8 (rows) / 8 follow-up questions
- Consolidated legitimate-gap worklist: **36** (4 BLOCKER, 17 MAJOR, 15 MINOR)
- Profile-scoped-WITHOUT-citation (= real, uncited) gaps: **2** (§4.1–§4.5 = G13;
  §4.7 = G36) — both already in the worklist.
