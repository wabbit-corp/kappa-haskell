# Lane audit: RUNTIME / EVAL / STDLIB / EFFECTS

Scope: §18 (effects/do/abrupt-control/loops/var), §19 (errors try/except/finally/raise/MonadResource),
§20 (collections/ranges/comprehensions), §28 (Prelude), §29 (Required Standard Modules),
§32 (runtime semantics), §33 (content-addressed identity).

Stance: hostile. Every "IMPLEMENTED" row is backed by a probe (input + observed output). Every
MISSING/WEAK row gives the probe that exposes it. Profile-scoped non-implementation is only excused
with the exact permitting clause. Implementation evidence was gathered against the built binary
`dist-newstyle/.../kappa` (build clean, `cabal build all --enable-tests --ghc-options=-Werror` OK,
in-tree conformance `test tests/conformance` = 195/195 passed).

Probe files live under `/tmp/kp/`. Source loci cite files under `src/Kappa/`.

**Status refresh (2026-07-01):** this audit began as a hostile historical probe log, but rows that previously described
S2.3b and runtime-surface work as absent have been reconciled below. In particular, `let x = !e`, immediate-application
splice `!f x`, `MonadError`/`MonadFinally`/`MonadResource`, `bracket`, masking/finalization surface, STM surface, fiber
identity, and `std.atomic` no longer use the old unresolved-name / pre-S2.3b evidence. Remaining gaps in this document are
future-stage or non-S2.3b unless their row says otherwise.

Legend: IMPLEMENTED+TESTED | IMPLEMENTED-WEAKLY-TESTED | MISSING |
INTENTIONALLY-UNSUPPORTED(cite) | SPEC-CONFLICT(cite) | UNCLEAR.

---

## §18 Effects, do blocks, abrupt control, loops, var

| § | requirement (short) | status | evidence/probe | note |
|---|---|---|---|---|
| §18.1.14 | `Eff r a` carrier; `runPure : Eff <[]> a -> a` | IMPLEMENTED+TESTED | conformance `effects/deep-handler-state.kp` evaluates to 20 via `runPure` | effect kernel `evalEffPrim` in `Eval.hs` (`__effBind`, `__handleEff`, `runPure`) |
| §18.1.15/.18 | shallow vs deep handlers; nearest matching handler intercepts | IMPLEMENTED+TESTED | conformance `effects/deep-handler-state.kp` (deep), `effects/shallow-abandon.kp` pass in full suite | `__handleEff deepV ...` reinstall logic, `Eval.hs:727` |
| §18.1.22 | deep handler reinstalls itself around resumption | IMPLEMENTED+TESTED | `deep-handler-state` result 20 requires reinstall; passes | `reinstall cont`, `Eval.hs:747` |
| §32.2.14 | multi-shot resumption when quantity permits | PARTIAL / profile-scoped | conformance `effects/multishot-resumption.kp` / `multishot-capture-linear.kp` exercise the interpreter/spec-facing surface; native backends do not advertise `rt-multishot-effects` and reject reachable multi-shot. | one-shot native runtime only |
| §18.2 | `do` blocks; statement sequencing; binds | IMPLEMENTED+TESTED | `/tmp/kp/m1.kp` `m2.kp` `sp4.kp` run OK | IO/MonadRef do-kernel elaboration in `Check.hs`; `Interp.runScope` |
| §18.3.1 | `!e` monadic splice in **`let x = !e`** position | IMPLEMENTED+TESTED | `tests/conformance/do/splice-let-and-app-spine.kp` and sibling bang-splice regressions | `DoLet` now uses the same bind-lift machinery as statement/bind positions; the obsolete `E_SPLICE_OUTSIDE_DO` probe is historical |
| §18.3.1 | immediate-application splice `!f x` = `!(f x)`, "not `(!f) x`" | IMPLEMENTED+TESTED | `tests/conformance/do/splice-let-and-app-spine.kp` covers application-spine lifting | the old parse/lowering conflict is resolved by lifting the whole application spine |
| §18.3 | `!e` in statement (`DoExpr`) and `let x <- !e` (`DoBind`) | IMPLEMENTED+TESTED | `/tmp/kp/sp4.kp` (5,5) and `/tmp/kp/sp5.kp` (9,9) run OK | `desugarBang` applied in `DoExpr`/`DoBind` |
| §18.4 | `if cond then` (statement-if, no else) in do = implicit `pure ()` | IMPLEMENTED+TESTED | `examples/todo.kp:130` `if isPending t then ...`; runs | parser `pIf`/`elabDo` |
| §18.5 | `return` | IMPLEMENTED+TESTED | `Interp.hs` `KReturn` → `CplReturn`; example/conformance use it | `Interp.runScope:242` |
| §18.6 | `while cond do body` (pure `Bool` *and* monadic `m Bool` condition) | IMPLEMENTED+TESTED | `/tmp/kp/w1.kp` prints 10; pure form `conformance run/while-var.kp`; monadic form (Spec.md:20476) `conformance run/while-monadic-cond.kp` and user-monad var/while fixtures — the condition is re-run each iteration. `Check.DoWhile` accepts `Bool` directly or an action in the enclosing monad stored as `KCondAction`. | `Interp.whileLoop`; `Check.hs` `DoWhile` |
| §18.6 | `for pat in list do body` | IMPLEMENTED+TESTED | `/tmp/kp/f3.kp` prints 6; `/tmp/kp/doforlist.kp` 1/2/3 | `Interp.forLoop`, source iterated via `listElems` |
| §18.6 | `for x in <range>` (range as loop source) | IMPLEMENTED+TESTED | `tests/conformance/queries/range_iteration_run.kp` covers imperative `for` and comprehensions over ranges | `NumericRange` now lowers through the range/IntoQuery machinery |
| §18.6 loop `else` | loop `else` runs only on no-break completion | IMPLEMENTED+TESTED | `/tmp/kp/f2b.kp` prints "not found" then False | `Interp.runElse`, `CplBreak` suppresses else |
| §18.2.5/§18.8 | labeled `break@L` / `continue@L`; `L@ for ...` | IMPLEMENTED+TESTED | `/tmp/kp/lbl2.kp` (`outer@ for ...`, `break@outer`) prints 1 | `Interp.targets` matches label |
| §18.6 | `break`/`continue` outside loop rejected | IMPLEMENTED+TESTED | conformance `do/continue-outside-loop.kp`, `do/break-in-loop-else.kp` → `E_BREAK_OUTSIDE_LOOP` | compile-time check |
| §18.6.1 | `var` mutable variable; read/assign | IMPLEMENTED+TESTED | `/tmp/kp/m2.kp`, `w1.kp` mutate `var` correctly | Surface `var` elaborates through the selected `MonadRef` operations; the interpreter's `KVarItem`/`KAssign` execute the already-elaborated ref actions. |
| §18.7 | `defer` LIFO, exactly once, on every exit | IMPLEMENTED+TESTED | `/tmp/kp/defer.kp` → body,b,a | `Interp.runScope` `exitsRef`, `runExits` |
| §18.8.3 | exit actions run once on abrupt exit (return/break/raise) | IMPLEMENTED-WEAKLY-TESTED | `defer` runs on normal/finally path (`fin2.kp`); LIFO once verified | unwind-on-return not independently re-probed beyond finally path |
| §18.1 (IO) | `printString`/`printlnString`, `newRef`/`readRef`/`writeRef`, `ioBind`/`ioThen`, `catchIO`/`finallyIO`/`throwIO` | IMPLEMENTED+TESTED | every run-mode probe emits via these prims | `Interp.runPrimIO'` |
| §18.9 | `inout` parameters | UNCLEAR | not probed in this lane (binder/borrow feature; cross-lane) | `KItem` has no inout; flagged for types/borrow lane |

## §19 Errors: try/except/finally, raise, MonadResource

| § | requirement (short) | status | evidence/probe | note |
|---|---|---|---|---|
| §19.2 | `try / except pat -> h / finally -> f` | IMPLEMENTED+TESTED | conformance `run/try-except-finally.kp` → "caught: boom\nfinally\nafter" | `Interp` `catchIO`/`finallyIO` |
| §19.2 step6 | finally runs on success, handled, propagated, break, return; primary error wins | IMPLEMENTED-WEAKLY-TESTED | `/tmp/kp/fin2.kp` → got primary, fin, end (handler then finally) | finally-through-break/return paths not separately probed |
| §19.4 | `raise` | IMPLEMENTED+TESTED | `risky` uses `raise "boom"`; conformance passes | `raise = throwError` in prelude; `throwIO` runtime |
| §19.1 | `MonadError` trait surface | IMPLEMENTED+TESTED | `src/Kappa/Prelude.hs` declares `MonadError`; IO instance delegates to `throwIO`/`catchIO`; conformance exercises `raise` / `try` | no longer an unresolved-name gap |
| §19.2 | `MonadFinally` trait surface | IMPLEMENTED+TESTED | `src/Kappa/Prelude.hs` declares `MonadFinally`; IO instance delegates to `finallyIO`; `defer`/`finally` tests exercise the behavior | no longer an unresolved-name gap |
| §19.5 | `MonadResource` / `bracket` / scoped allocation | IMPLEMENTED+TESTED | `src/Kappa/Prelude.hs` declares `MonadResource` and `bracket`; native finalizer/bracket tests cover release-on-interrupt paths | `sandbox`/`unsandbox` remain a separate backend-support gap, not a `MonadResource` surface gap |

## §20 Collections, ranges, comprehensions

| § | requirement (short) | status | evidence/probe | note |
|---|---|---|---|---|
| §20.1 | list `[..]`, set `{| |}`, map `{ }` literals | IMPLEMENTED+TESTED | conformance `collections/map-literal.kp` (`{ "a":1 }`), `doforlist.kp` list literal | parser + carriers |
| §20.2 | `..` / `..<` range operators construct a range | IMPLEMENTED-WEAKLY-TESTED | `/tmp/kp/rng2.kp` shows `1 .. 5 : NumericRange Integer` constructed | constructs but cannot be iterated (see §18.6/§20.4 range rows) |
| §20.2 | `Rangeable` instances for Nat, Int, Integer, UnicodeScalar | IMPLEMENTED-WEAKLY-TESTED | embedded prelude has `Rangeable Integer/Nat/UnicodeScalar` | `Rangeable Int` follows from `Int = Integer` |
| §20.2 | iterating a range governed by `IntoQuery` | IMPLEMENTED+TESTED | `tests/conformance/queries/range_iteration_run.kp`; prelude declares `IntoQuery` instances for list/array/set/option/range | old unresolved-name/range-not-list probes are historical |
| §20.3 | list/set/map comprehension `[ for ... yield e ]` | IMPLEMENTED+TESTED | `/tmp/kp/compr2.kp` lowers `[ for x in .. yield x*x ]` to `List Integer` | `__queryFromList`/`__pipeMap` lowering, `Eval.hs:641` |
| §20.3.2 | encounter order preserved | IMPLEMENTED+TESTED | `/tmp/kp/enc.kp` distinct → `3,1,2` (first-occurrence order) | order-preserving list backing |
| §20.4 | `for pat in coll`, `let pat = e`, `if cond` clauses | IMPLEMENTED+TESTED | `collections/*` conformance; `enc.kp` | `RawComprehension` lowering |
| §20.4 | borrowed generators `for x in &coll`, `for & pat in coll` | UNCLEAR | not probed (borrow lane); `BorrowSourceIntoQuery`/`BorrowItemsIntoQuery` names now resolve | likely semantic gap; deferred to borrow lane |
| §20.6 | `order by`, paging, `distinct` | IMPLEMENTED+TESTED | `/tmp/kp/enc.kp` order by → `1,2,3`; distinct → 3 uniques | `__sortBy`, `__distinctBy` |
| §20.7 | grouping (`group by`) | IMPLEMENTED-WEAKLY-TESTED | `__groupBy`/`__groupInsert` present in prelude; conformance `queries/*` | not directly re-probed for output values |
| §20.8 | joins | UNCLEAR | not probed; `queries/*` suite exists | deferred |
| §20.9 | custom sinks (`FromComprehensionRaw`/`Plan`) | IMPLEMENTED+TESTED | conformance `collections/custom_sink.kp` exercises priority + `E_SINK_ITEM_MISMATCH` | traits present |
| §20.10/.11 | normative lowering to query core; list-backed as-if | IMPLEMENTED-WEAKLY-TESTED | `Eval.hs:641` `__queryFromList`/`__setFromList`/`__mapFromEntries` are identity on element stream | as-if collapse to lists; mode/quantity static-only |

## §28 Prelude

### §28 types / classifiers / constructors

| § | requirement (short) | status | evidence/probe | note |
|---|---|---|---|---|
| §28.2 | core types Unit, Void, Bool, Int, Nat, Integer, Double, Float, String, Byte, Bytes, UnicodeScalar, Grapheme, Ordering | IMPLEMENTED+TESTED | resolve & used across conformance | `Prelude.types` |
| §28.2 | **`Rational`** type exported | IMPLEMENTED+TESTED | `tests/conformance/prelude/rational_run.kp`; `Rational` is in the embedded prelude with numeric/algebraic instances | old unresolved-name probe is historical |
| §28.2 | `Array`, `SizedArray`, `Set`, `Map`, `List` types | IMPLEMENTED+TESTED (types) | `Array`/`Set`/`Map`/`List` resolve as types | `Prelude.types`; **but term ops absent, see below** |
| §28.1 | implicit `import std.prelude.*` + fixed unqualified ctor subset (True/False/None/Some/Ok/Err/Nil/(::)/LT/EQ/GT/refl) | IMPLEMENTED+TESTED | all conformance programs use these unqualified | `Pipeline.preludeScope` |
| §28.2 | `Eff`, `Code`, `ClosedCode`, `Variant`, `IO`, `UIO`, `STM`, `TVar`, `Duration`, `Instant`, `Fiber`, `Scope`, etc. types | IMPLEMENTED-WEAKLY-TESTED | `Eff`/`IO`/`STM`/`TVar`/`Duration`/`Instant` types present in `Prelude.types`; `Fiber`/`Scope`/`Monitor`/`Promise`/`FiberRef`/`FiberId` not all confirmed | concurrency carriers tied to §27.6 `rt-core` |
| §28.2 | `refl`, `=`, `Dec`, `Res`, `Match` and their ctors | IMPLEMENTED-WEAKLY-TESTED | `refl` unqualified import works | not all exhaustively probed |

### §28.2 terms (probed presence)

| § | requirement (short) | status | evidence/probe | note |
|---|---|---|---|---|
| §28.2 | `pure (>>=) (>>) map liftA2 (<*>) (|>) (<|)` | IMPLEMENTED+TESTED | resolve; pipeline ops used in conformance | |
| §28.2 | `not and or force (&&) (||)` | IMPLEMENTED-WEAKLY-TESTED | `not` present; `&&`/`||` fixities present | |
| §28.2 | `(==) (/=) compare (<) (<=) (>) (>=)` | IMPLEMENTED+TESTED | `/tmp/kp/cmp.kp` `compare 1 2` → LT | |
| §28.2 | **`(~=)`** equivalence operator | IMPLEMENTED+TESTED | `src/Kappa/Prelude.hs` declares `Equiv` and the Eq bridge; `Resolve.hs` gives `~=` the equality fixity | old unresolved-name probe is historical |
| §28.2 | numeric ops `zero one add (+) multiply (*) negate subDefined subtract (-) divDefined divide (/) modDefined modulo (%) nonZero` | IMPLEMENTED+TESTED | `/tmp/kp/intsub.kp` 3-5=-2; `/tmp/kp/intdiv.kp` 7/2=3; `/tmp/kp/fdiv.kp` 3.5 | proof obligations enforced (see §28.2.1) |
| §28.2 | `empty (<|>) orElse append (++) foldl foldr foldMap traverse filter filterMap sequence` | IMPLEMENTED+TESTED | `/tmp/kp/fold.kp` foldl→6; names resolve | |
| §28.2 | **`for_`, `sequence_`** | IMPLEMENTED-WEAKLY-TESTED | `src/Kappa/Prelude.hs` exports both as Foldable/Applicative helpers | direct conformance coverage is light |
| §28.2 | `fromInteger fromFloat fromString buildInterpolated f re b type` | IMPLEMENTED+TESTED | numeric/string literals + f-strings work (todo.kp) | |
| §28.2 | **`next`** (Iterator), **`toQuery`** | IMPLEMENTED-WEAKLY-TESTED | `tests/conformance/traits/iterator-next-*.kp`; prelude `IntoQuery` instances feed query lowering | borrowed-query semantics remain a borrow-lane concern |
| §28.2 | proof helpers **`absurd pathInd subst sym trans cong unsafeAssertProof witness measureRelation lexRelation`** | IMPLEMENTED-WEAKLY-TESTED | prelude exports these helpers; proof/equality conformance covers representative use | |
| §28.2 | `floatEq` | IMPLEMENTED+TESTED | resolves; `evalPurePrim "floatEq"` IEEE eq (`Eval.hs:558`) | |
| §28.2 | `runPure` | IMPLEMENTED+TESTED | conformance `deep-handler-state` | |
| §28.2 | resource/finalize: **`poll uninterruptible mask ensuring acquireRelease finally bracket`** | IMPLEMENTED+TESTED | `src/Kappa/Prelude.hs` exposes the masking/finalization surface; native tests cover masked finalizers and acquire/release | `sandbox`/`unsandbox` are tracked separately as native backend support work, not part of the resolved S2.3b mutable-var surface |
| §28.2 | fibers/scopes/promises: **`fork forkDaemon await join interrupt fiberId currentFiberId cede newScope forkIn shutdownScope monitor awaitMonitor demonitor newFiberRef newPromise`** | IMPLEMENTED+TESTED (surface/runtime) | conformance/native effects cover fork/await/scope/promise/monitor/fiber-id families | fiber labels remain separate gaps; this row is no longer a name-resolution gap |
| §28.2 | STM: **`atomically newTVar readTVar writeTVar retry check`** | IMPLEMENTED+TESTED | `src/Kappa/Prelude.hs` exposes the STM surface; native/runtime tests cover journaled STM and retry parking | `Alternative STM` remains future-stage/open in the runtime coverage map |
| §28.2 | refs `newRef readRef writeRef` | IMPLEMENTED+TESTED (runtime) | runtime prims exist; usable via `var` | surface terms resolve through `MonadRef`-shaped prims |
| §28.2 | ranges `range (..) (..<)` | IMPLEMENTED+TESTED | `range` resolves and `tests/conformance/queries/range_iteration_run.kp` iterates ranges | |
| §28.2 | **collection terms** `listLength listAppend arrayEmpty arraySingleton arrayFromList arrayToList arrayLength arrayGet arrayIndex setEmpty setSingleton setInsert setDelete setMember setSize mapEmpty mapSingleton mapInsert mapDelete mapLookup mapMember mapSize` | IMPLEMENTED+TESTED | prelude exports these terms; conformance covers map/set/array surfaces | old unresolved-name probe is historical |
| §28.2 | `sizedArrayLength sizedArrayIndex sizedArrayToArray arrayAsSized` | MISSING | not exported | remaining collection-surface gap, separate from S2.3b mutable vars |
| §28.2 | time: **`nowMonotonic nanos micros millis seconds minutes durationAdd durationSub durationCompare instantAdd instantDiff sleepFor sleepUntil timeout race`** | IMPLEMENTED+TESTED | `test/native/cases/timer-duration.kp`, `timeout.kp`, and `race.kp`; prelude exposes duration/instant wrappers | remaining timer issues are runtime edge cases, not name-resolution gaps |
| §28.2 | staging `liftCode closeCode genlet runCode syntaxOrigin withSyntaxOrigin` | IMPLEMENTED-WEAKLY-TESTED | `liftCode`/`closeCode`/`genlet`/`runCode` resolve | staging lane |
| §28.2 | output `show printString printlnString print println` | IMPLEMENTED+TESTED | every run probe | |

### §28.2 traits (probed presence)

| § | requirement (short) | status | evidence/probe | note |
|---|---|---|---|---|
| §28.2 | `Eq Ord Show Functor Applicative Monad Foldable Traversable Filterable FilterMap Monoid Rangeable Shareable Lift FromInteger FromFloat FromString InterpolatedMacro FromComprehensionPlan FromComprehensionRaw` | IMPLEMENTED+TESTED | `/tmp/kp` trait batch → present | |
| §28.2 | numeric op traits `Zero One Add Mul Negatable CheckedSub CheckedDiv CheckedMod` | IMPLEMENTED+TESTED | trait batch → present; probes enforce contracts | |
| §28.2 | **`Equiv`** | IMPLEMENTED+TESTED | prelude trait + Eq bridge instance | pairs with `(~=)` |
| §28.2 | **`Alternative`** | IMPLEMENTED-WEAKLY-TESTED | prelude trait resolves; STM still lacks its specific instance | instance coverage remains separate |
| §28.2 | **`Iterator`** | IMPLEMENTED+TESTED | `tests/conformance/traits/iterator-next-*.kp` | |
| §28.2 | **`MonadError MonadFinally MonadResource`** | IMPLEMENTED+TESTED | declared in `src/Kappa/Prelude.hs` with IO instances and exercised by error/finalizer/resource tests | `MonadRef` is also present for surface mutable bindings |
| §28.2 | **`WellFoundedRelation`** | IMPLEMENTED-WEAKLY-TESTED | prelude exports the trait and relation helpers | checker use as arbitrary termination evidence remains limited |
| §28.2 | **`IntoQuery BorrowSourceIntoQuery BorrowItemsIntoQuery`** | IMPLEMENTED-WEAKLY-TESTED | prelude exports the traits; `IntoQuery` list/range path is tested | borrowed generator behavior remains deferred to borrow lane |
| §28.2 | **`QuotedLiteralMacro`** | IMPLEMENTED-WEAKLY-TESTED | prelude exports the trait name | macro semantics remain weakly exercised |
| §28.2 | proof traits `IsEmpty IsContr IsSubsingleton IsProp IsSet IsGroupoid IsNType RuntimeErased IsTrait QuantitySatisfies` and row traits | UNCLEAR | not all re-probed here (types/qtt lanes); `IsTrait` used by `summon` works | deferred to types lane |

### §28.2.1 numeric operation trait contracts & partial-operation domains

| § | requirement (short) | status | evidence/probe | note |
|---|---|---|---|---|
| §28.2.1 | `(-)` checked subtraction needs proof `subDefined x y = True` | IMPLEMENTED+TESTED | `/tmp/kp/natsub2.kp` (Nat 3-5) → `E_UNSOLVED_IMPLICIT = Bool (subDefined Nat .. 3 5) True` | proof obligation enforced |
| §28.2.1 | `(/)` requires `divDefined`; no unchecked div-by-zero | IMPLEMENTED+TESTED | `/tmp/kp/divzero.kp` (7/0) → `E_UNSOLVED_IMPLICIT ... divDefined Integer ... True` | enforced |
| §28.2.1 | `(%)` requires `modDefined`; no unchecked mod-by-zero | IMPLEMENTED+TESTED | `/tmp/kp/modzero.kp` (7%0) → unsolved `modDefined` proof | enforced |
| §28.2.1 | prelude MUST NOT provide unchecked/saturating/wrapping under these names | IMPLEMENTED+TESTED | `Nat` `(-)` requires `(y<=x)=True`; not saturating | matches §28.2.3 Nat rule |

### §28.2.2 algebraic numeric traits

| § | requirement (short) | status | evidence/probe | note |
|---|---|---|---|---|
| §28.2.2 | `AdditiveMonoid` trait | IMPLEMENTED-WEAKLY-TESTED | declared in the prelude and exercised by algebraic numeric fixtures | law members remain shallow |
| §28.2.2 | `AdditiveGroup MultiplicativeMonoid Semiring Ring FieldLike OrderedAdditive OrderedSemiring` | IMPLEMENTED-WEAKLY-TESTED | declared in the prelude and exercised by representative numeric instances | law members remain shallow |
| §28.2.2 | `EuclideanSemiring` = refines `(Semiring,Ord,CheckedDiv,CheckedMod)` with `divAndModSameDomain`,`divModIdentity` | IMPLEMENTED-WEAKLY-TESTED | current prelude uses the superclass-shaped trait; representative Nat instance exists | |

### §28.2.3 standard numeric instances, domains, fixities

| § | requirement (short) | status | evidence/probe | note |
|---|---|---|---|---|
| §28.2.3 | operation instances for Nat: Zero,One,Add,Mul,CheckedSub,CheckedDiv,CheckedMod | IMPLEMENTED+TESTED | `CheckedSub Nat` is now in the prelude; equality/sub-proof conformance covers the proof obligation | old `E_UNSOLVED_IMPLICIT CheckedSub Nat` probe is historical |
| §28.2.3 | operation instances for Integer/Int | IMPLEMENTED+TESTED | `Zero/One/Add/Mul/Negatable/CheckedSub/CheckedDiv/CheckedMod Integer` present (`Prelude.hs:612-629`) | Int via alias |
| §28.2.3 | operation instances for Rational | IMPLEMENTED+TESTED | `tests/conformance/prelude/rational_run.kp` | |
| §28.2.3 | `CheckedSub Float/Double` | IMPLEMENTED-WEAKLY-TESTED | `CheckedSub Double` is now in the prelude; Float remains a type alias / weak surface | old `CheckedSub Double` probe is historical |
| §28.2.3 | Float/Double MUST NOT receive Semiring/Ring/FieldLike | IMPLEMENTED+TESTED | algebraic traits exist; Float/Double are not given Semiring/Ring/FieldLike instances | |
| §28.2.3 | **algebraic** instances (AdditiveMonoid Nat, Semiring Nat, Ring Integer, FieldLike Rational, ...) | IMPLEMENTED-WEAKLY-TESTED | algebraic traits and core instances are declared in the prelude; `tests/conformance/prelude/algebraic_numeric.kp` exercises representative cases | law checking remains shallow |
| §28.2.3 | fixity table (`==`,`&&`,`||`,`..`,`::`,`++`,`+`,`-`,`*`,`/`,`%`,prefix `-`,`:&`,`|>`,`<|`) | IMPLEMENTED+TESTED | `Resolve.defaultFixities` matches the table 1:1 (precedences/assoc) | `Resolve.hs:42-66`; `?.`/`?:` handled built-in by parser |
| §28.2.3 | `(~=)` same precedence/assoc as `(==)` | IMPLEMENTED+TESTED | `Resolve.defaultFixities` puts `~=` with the equality operators | |

## §29 Required Standard Modules

| § | requirement (short) | status | evidence/probe | note |
|---|---|---|---|---|
| §29.1 | `std.atomic` provided **iff backend advertises `rt-atomics`** | IMPLEMENTED+PARTIAL | embedded `std.atomic` surface resolves; interpreter and native paths use atomic-cell operations | remaining gaps are fixed-width / polymorphic `AtomicValue` coverage, not atomic-cell semantics |
| §29.2 | `std.supervisor` — **unconditional MUST** | IMPLEMENTED-WEAKLY-TESTED | `/tmp/kp/sup.kp` `import std.supervisor` resolves (no error) | embedded `stdSupervisorSource`; observable supervision semantics tied to `rt-core` (not interpreted) — surface present |
| §29.3 | `std.hash` — **unconditional MUST**; deterministic mixing | IMPLEMENTED+TESTED | `/tmp/kp/hd2.kp` `hashWith defaultHashSeed 42` deterministic ("equal"); `import std.hash` OK | `stdHashSource`; FNV-1a `Eval.hs:674` |
| §29.3 | `Hashable` instances for Unit/Bool/Int/Integer/Nat/Double/String/Bytes/Byte/UnicodeScalar/Grapheme/Ordering | IMPLEMENTED-WEAKLY-TESTED | all instances in `stdHashSource` (`Prelude.hs:1361-1392`) | derivation/structural hashing not re-probed |
| §29.4 | `std.unicode` — **unconditional MUST** | IMPLEMENTED-WEAKLY-TESTED | `/tmp/kp/uni2.kp` `byteLength "abc"` → 3 | `stdUnicodeSource`; doc admits incremental decoder/cursors NOT provided (UCD 15.0.0) |
| §29.4 | incremental decoder / builders / cursors | MISSING | per source comment `Prelude.hs:1409-1414` "the incremental decoder/builders/cursors of §29.4 are not provided" | §29.4 lists these as required ops |
| §29.5 | **`std.bytes` — unconditional MUST** | IMPLEMENTED+TESTED | `tests/conformance/prelude/std_bytes_run.kp` and `std_bytes_sizedarray.kp`; embedded `stdBytesSource` is wired in `Pipeline.preludeState` | |
| §29.6 | `std.debug` — MUST **when `allow_debug_introspection` enabled** | INTENTIONALLY-UNSUPPORTED (§29.6) | `/tmp/kp/dbg.kp` `import std.debug` → `E_MODULE_NAME_UNRESOLVED` | gated on `allow_debug_introspection`; no such flag is enabled, so non-provision is permitted |
| §29.7 | `std.config` — MUST **for impls supporting config mode** | INTENTIONALLY-UNSUPPORTED (§29.7, §35) | not provided | config mode (§35) is profile-scoped; not implemented |
| §29.8 | `std.build` — MUST **for impls supporting build manifests** | INTENTIONALLY-UNSUPPORTED (§29.8, §36) | not provided | build system (§36) is profile-scoped; not implemented |

## §32 Runtime semantics

| § | requirement (short) | status | evidence/probe | note |
|---|---|---|---|---|
| §32.1 | strict CBV, left-to-right evaluation | IMPLEMENTED-WEAKLY-TESTED | `Eval.eval`/`Interp.runScope` are strict; do-sequencing observably L→R (`sp4.kp`); arg-order via splice not provable (DoLet splice bug) | pure-application L→R side-effect order not directly observable (no pure side effects); relies on monadic order |
| §32.1 | `if` evaluates cond then one branch; `match` evaluates scrutinee once then cases top-down; guards after match | IMPLEMENTED+TESTED | `reduceMatch`/`tryReduceMatch` `Eval.hs:290`; conformance match suite | |
| §32.1 | `thunk`/`lazy` not evaluated at construction; `force` per §16.2.2 | IMPLEMENTED-WEAKLY-TESTED | `VThunkV`/`VLazyV` closures, `vforce` `Eval.hs:195` | suspension lane overlap |
| §32.1 | runtime divergence surfaces a Kappa diagnostic (recursion depth / stack / heap) | IMPLEMENTED-WEAKLY-TESTED | `force` fuel → `__recursionDepth` (`Eval.hs:222`); `StackOverflow`/`HeapOverflow` caught (`Interp.hs:99`) | not re-probed here |
| §32.2 | IO/fibers/STM/interruption/handlers runtime model | IMPLEMENTED-WEAKLY-TESTED / PARTIAL | C native runtime implements fibers, interruption, masks, STM, refs, timers, and one-shot handlers; see `docs/RUNTIME-SPEC-COVERAGE.md` for remaining runtime gaps | no longer a blanket absent-concurrency row; LLVM parity remains profile-scoped |
| §32.2 (handlers/resumptions) | handler capture/resume/abandon | IMPLEMENTED+TESTED | conformance effects suite (deep/shallow/multishot) | algebraic-effect subset of §32.2 is implemented |

## §33 Content-addressed identity

| § | requirement (short) | status | evidence/probe | note |
|---|---|---|---|---|
| §33.1.1 | Easy Hash always computed (structural identity) | MISSING (machinery) / UNCLEAR (observable) | `grep -ri 'easyhash\|hardidentity\|harddigest\|coherence_mode' src/` → **no matches**; no hash machinery exists | not externally observable except via coherence/incremental; coherence met by other means (below) |
| §33.1.2 | HardIdentity/HardDigest on demand + persistent `EasyHash→HardIdentity` cache | MISSING (machinery) | no hashing code; persistent cache is **package-mode MUST** only | package mode (§36) profile-scoped/unimplemented; script-mode default `semantic-if-available` permits unavailability with fallback |
| §33.2.1 | instance coherence: ≤1 distinct semantic implementation per ground trait evidence | IMPLEMENTED+TESTED | `/tmp/kp/coh.kp` two `Show Foo` → `E_INSTANCE_INCOHERENT (§14.3, §33.2.1)` | enforced structurally without explicit Easy/Hard hashes |
| §33.2.1 | harmless overlap accepted for canonically-identical instances | UNCLEAR | not constructible cheaply; structurally-equal instances likely grouped; semantically-equal-but-structurally-different overlap acceptance not verified | could be over-rejection but `semantic-if-available` permits conservative rejection-with-warning |
| §33.2.2 | fast-path defeq via HardIdentity | INTENTIONALLY-UNSUPPORTED (§33.2.2 "MAY") | no hash machinery; defeq goes through §31.1 conversion (`Eval.convertible`) | this is an OPTIONAL optimization; §31.1 conversion is the normative path and is implemented |

---

## Legitimate gaps (ranked)

Only in-scope, spec-grounded, MUST/SHALL-level requirements DISPROVED by a probe. Profile-scoped
items are excluded (listed separately below).

### Resolved during S2.3b: §18.3.1 `let x = !e` and immediate-application splice

The historical gap entries for `let x = !(getN 1)` and `!doit 8` are resolved. The active regression coverage is in
`tests/conformance/do/splice-let-and-app-spine.kp` and sibling bang-splice fixtures. These are no longer counted as
legitimate gaps.

### Resolved after the original audit: §29.5 and §28.2 prelude surface

The historical gaps for `std.bytes`, `Rational`, the algebraic numeric trait hierarchy, the broad trait-name batch,
`(~=)`, proof helpers, `CheckedSub Nat`, `CheckedSub Double`, `for_`, `sequence_`, and range iteration are resolved in
the current prelude/checker. Active evidence includes `tests/conformance/prelude/std_bytes_run.kp`,
`tests/conformance/prelude/rational_run.kp`, `tests/conformance/prelude/algebraic_numeric.kp`,
`tests/conformance/queries/range_iteration_run.kp`, and the iterator/trait conformance fixtures. They are kept here only
as historical context and are no longer counted as current gaps.

### 8. §28.2 — remaining collection surface gap: SizedArray operations — MAJOR
- Spec: §28.2 mandates `arrayEmpty arraySingleton arrayFromList arrayToList arrayLength arrayGet arrayIndex setEmpty setSingleton setInsert setDelete setMember setSize mapEmpty mapSingleton mapInsert mapDelete mapLookup mapMember mapSize sizedArrayLength sizedArrayIndex sizedArrayToArray arrayAsSized`.
- Array, Set, and Map terms now resolve through the prelude. The remaining current gap in this row is the SizedArray
  surface (`sizedArrayLength`, `sizedArrayIndex`, `sizedArrayToArray`, `arrayAsSized`), which is outside S2.3b mutable
  `var` semantics.

### 13. §29.4 — `std.unicode` incremental decoder / builders / cursors missing — MINOR
- Spec: §29.4 lists incremental decoder, builders, and cursor operations as required `std.unicode` surface.
- Evidence: source self-documents the omission (`Prelude.hs:1409-1414`); core ops (`utf8Bytes`/`byteLength`/normalization) work (`/tmp/kp/uni2.kp`).
- Fix locus: `src/Kappa/Prelude.hs` `stdUnicodeSource` + supporting prims in `src/Kappa/Eval.hs`.

---

## Profile-scoped / intentionally-unsupported (cited)

These are NOT counted as gaps because a spec clause makes them conditional, OR the SCOPE RULE
(interpreter need not implement backends/concurrency runtime) plus §27.6/§32.2 rejection rule applies.
Caveat noted where §28.2 surface-presence still tensions with the runtime gating.

- **Fibers / scopes / monitors / promises / fiber-local state / monotonic timers** (`fork…demonitor`, `nowMonotonic`, `nanos`, `timeout`, `race`, …): the C native runtime and prelude surface implement these families, including `fiberId`/`currentFiberId` and source/native `blocking`; remaining gaps are tracked in `docs/RUNTIME-SPEC-COVERAGE.md` (for example fiber labels, per-do-block supervision, and LLVM profile parity).
- **STM** (`atomically`, `newTVar`, `readTVar`, `writeTVar`, `retry`, `check`): single-agent STM is implemented and exposed. Remaining STM gaps such as `Alternative STM` are tracked separately and are not S2.3b mutable-`var` blockers.
- **`std.atomic`** (§29.1): provision gated on backend capability `rt-atomics` ("Implementations that advertise backend capability `rt-atomics` MUST provide…"). The embedded surface, interpreter oracle, and native `krt2_atomic_*` path are present; remaining work is fixed-width / polymorphic instance coverage rather than the former plain-`Ref` semantic hole.
- **`std.debug`** (§29.6): MUST only "when `allow_debug_introspection` is enabled". No such mode is enabled; non-provision permitted.
- **`std.config`** (§29.7): MUST only for implementations "supporting config mode" (§35). Config mode is profile-scoped; not implemented.
- **`std.build`** (§29.8): MUST only for implementations "supporting build manifests" (§36). Build system is profile-scoped; not implemented.
- **§32.2 runtime model for IO/fibers/STM/interruption** (full): §32.2 + §27.6 permit rejection by a backend lacking the capability; the interpreter implements IO + refs + algebraic-effect handlers, not the concurrency kernel.
- **§33.1.1/§33.1.2 Easy/Hard hash machinery + persistent cache**: the persistent `EasyHash→HardIdentity` cache is a **package-mode** MUST (§33.1.2); package mode (§36) is profile-scoped/unimplemented. Script-mode default is `semantic-if-available`, which sanctions unavailability of `HardIdentity` with conservative fallback. The only externally-observable §33 MUST — instance coherence (§33.2.1) — IS enforced (`E_INSTANCE_INCOHERENT`). §33.2.2 fast-path defeq is explicitly "MAY".
- **§18.9 `inout`, §20.4 borrowed generators, §20.8 joins**: deferred to the types/borrow lane; not disproved here.

---

## Status Counts (Historical)

The counts below are the original hostile-audit snapshot and are kept only to make old references traceable. They are not
the current runtime/S2.3b status; use the refreshed rows above and `docs/RUNTIME-SPEC-COVERAGE.md` for current status.

- IMPLEMENTED+TESTED: 33
- IMPLEMENTED-WEAKLY-TESTED: 17
- MISSING: 24
- INTENTIONALLY-UNSUPPORTED (cited): 9
- SPEC-CONFLICT: 2 (§18.3.1 `!f x` parse; §28.2.2 `EuclideanSemiring` shape)
- UNCLEAR: 6

(Some rows enumerate multiple names; the MISSING count reflects distinct requirement rows, not the
~50 individually-probed missing prelude names.)
