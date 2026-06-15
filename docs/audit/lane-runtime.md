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

Legend: IMPLEMENTED+TESTED | IMPLEMENTED-WEAKLY-TESTED | MISSING |
INTENTIONALLY-UNSUPPORTED(cite) | SPEC-CONFLICT(cite) | UNCLEAR.

---

## §18 Effects, do blocks, abrupt control, loops, var

| § | requirement (short) | status | evidence/probe | note |
|---|---|---|---|---|
| §18.1.14 | `Eff r a` carrier; `runPure : Eff <[]> a -> a` | IMPLEMENTED+TESTED | conformance `effects/deep-handler-state.kp` evaluates to 20 via `runPure` | effect kernel `evalEffPrim` in `Eval.hs` (`__effBind`, `__handleEff`, `runPure`) |
| §18.1.15/.18 | shallow vs deep handlers; nearest matching handler intercepts | IMPLEMENTED+TESTED | conformance `effects/deep-handler-state.kp` (deep), `effects/shallow-abandon.kp` pass in full suite | `__handleEff deepV ...` reinstall logic, `Eval.hs:727` |
| §18.1.22 | deep handler reinstalls itself around resumption | IMPLEMENTED+TESTED | `deep-handler-state` result 20 requires reinstall; passes | `reinstall cont`, `Eval.hs:747` |
| §32.2.14 | multi-shot resumption when quantity permits | IMPLEMENTED-WEAKLY-TESTED | conformance `effects/multishot-resumption.kp` / `multishot-capture-linear.kp` in suite; `cont` is a re-entrant closure | gated by `rt-multishot-effects` (§27.6); interpreter implements it |
| §18.2 | `do` blocks; statement sequencing; binds | IMPLEMENTED+TESTED | `/tmp/kp/m1.kp` `m2.kp` `sp4.kp` run OK | `elabDoIOItems` `Check.hs:6778`, `Interp.runScope` |
| §18.3.1 | `!e` monadic splice in **`let x = !e`** position | MISSING | `/tmp/kp/sp1.kp` (`let x = !(getN 1)`) → `error[E_SPLICE_OUTSIDE_DO]` though inside a `do`. Spec's own canonical example `let x = !readInt` | `DoLet` branch never calls `desugarBang rhs` (`Check.hs:6884/6887`); `DoExpr`/`DoBind` do |
| §18.3.1 | immediate-application splice `!f x` = `!(f x)`, "not `(!f) x`" | SPEC-CONFLICT | `/tmp/kp/sp6.kp` (`!doit 8`) → `E_TYPE_EQUALITY_MISMATCH actual: Integer -> IO Void Unit` i.e. parsed as `(!doit) 8` | `desugarBang (EApp f args)` recurses into head first (`Check.hs:7117`); spec §18.3.1 forbids this exact parse |
| §18.3 | `!e` in statement (`DoExpr`) and `let x <- !e` (`DoBind`) | IMPLEMENTED+TESTED | `/tmp/kp/sp4.kp` (5,5) and `/tmp/kp/sp5.kp` (9,9) run OK | `desugarBang` applied in `DoExpr`/`DoBind` |
| §18.4 | `if cond then` (statement-if, no else) in do = implicit `pure ()` | IMPLEMENTED+TESTED | `examples/todo.kp:130` `if isPending t then ...`; runs | parser `pIf`/`elabDo` |
| §18.5 | `return` | IMPLEMENTED+TESTED | `Interp.hs` `KReturn` → `CplReturn`; example/conformance use it | `Interp.runScope:242` |
| §18.6 | `while cond do body` (pure `Bool` *and* monadic `m Bool` condition) | IMPLEMENTED+TESTED | `/tmp/kp/w1.kp` prints 10; pure form `conformance run/while-var.kp`; monadic `m Bool` form (Spec.md:20476) `conformance run/while-monadic-cond.kp` — the condition is re-run each iteration. `Check.DoWhile` accepts `Bool` (used directly, flow-sensitive per Spec.md:20478) or `IO errT Bool` (wrapped in `__runIO` so the loop re-executes the action) | `Interp.whileLoop`; `Check.hs` `DoWhile` |
| §18.6 | `for pat in list do body` | IMPLEMENTED+TESTED | `/tmp/kp/f3.kp` prints 6; `/tmp/kp/doforlist.kp` 1/2/3 | `Interp.forLoop`, source iterated via `listElems` |
| §18.6 | `for x in <range>` (range as loop source) | MISSING | `/tmp/kp/dofor.kp` `for x in 1 .. 3 do` → `E_TYPE_EQUALITY_MISMATCH actual: NumericRange Integer expected: List`. §20.2 "iterating a range is governed by `IntoQuery`" | `for`/comprehension source machinery only accepts `List`; no `IntoQuery`-based iteration; `IntoQuery` trait absent |
| §18.6 loop `else` | loop `else` runs only on no-break completion | IMPLEMENTED+TESTED | `/tmp/kp/f2b.kp` prints "not found" then False | `Interp.runElse`, `CplBreak` suppresses else |
| §18.2.5/§18.8 | labeled `break@L` / `continue@L`; `L@ for ...` | IMPLEMENTED+TESTED | `/tmp/kp/lbl2.kp` (`outer@ for ...`, `break@outer`) prints 1 | `Interp.targets` matches label |
| §18.6 | `break`/`continue` outside loop rejected | IMPLEMENTED+TESTED | conformance `do/continue-outside-loop.kp`, `do/break-in-loop-else.kp` → `E_BREAK_OUTSIDE_LOOP` | compile-time check |
| §18.6.1 | `var` mutable variable; read/assign | IMPLEMENTED+TESTED | `/tmp/kp/m2.kp`, `w1.kp` mutate `var` correctly | `Interp` `KVarItem`/`KAssign` use `IORef`; **note**: bypasses `MonadRef` evidence (special-cased), trait name unresolvable (see §28 row) |
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
| §19.1 | `MonadError` trait surface | MISSING (name) | `/tmp/kp/me.kp` `(@_ : MonadError m)` → `E_NAME_UNRESOLVED 'MonadError'` | §28.2 lists `MonadError` as required trait; `throwError`/`catchError` terms exist but the trait is unnameable |
| §19.2 | `MonadFinally` trait surface | MISSING (name) | `/tmp/kp/mf.kp` → `E_NAME_UNRESOLVED 'MonadFinally'` | §28.2 required trait absent |
| §19.5 | `MonadResource` / `bracket` / scoped allocation | MISSING | `/tmp/kp/mr.kp` → `E_NAME_UNRESOLVED 'MonadResource'`; `/tmp/kp/_q.kp` `bracket` → `E_NAME_UNRESOLVED`; `acquireRelease` → unresolved | §28.2 lists `MonadResource`, `bracket`, `release`, `acquireRelease`; only `release` resolves |

## §20 Collections, ranges, comprehensions

| § | requirement (short) | status | evidence/probe | note |
|---|---|---|---|---|
| §20.1 | list `[..]`, set `{| |}`, map `{ }` literals | IMPLEMENTED+TESTED | conformance `collections/map-literal.kp` (`{ "a":1 }`), `doforlist.kp` list literal | parser + carriers |
| §20.2 | `..` / `..<` range operators construct a range | IMPLEMENTED-WEAKLY-TESTED | `/tmp/kp/rng2.kp` shows `1 .. 5 : NumericRange Integer` constructed | constructs but cannot be iterated (see §18.6/§20.4 range rows) |
| §20.2 | `Rangeable` instances for Nat, Int, Integer, UnicodeScalar | IMPLEMENTED-WEAKLY-TESTED | embedded prelude has `Rangeable Integer/Nat/UnicodeScalar` | `Rangeable Int` follows from `Int = Integer` |
| §20.2 | iterating a range governed by `IntoQuery` | MISSING | range not iterable in `for`/comprehension (`dofor.kp`, `rng2.kp`); `IntoQuery` trait unresolved (`/tmp/kp/iq.kp`) | core mechanism `IntoQuery` absent |
| §20.3 | list/set/map comprehension `[ for ... yield e ]` | IMPLEMENTED+TESTED | `/tmp/kp/compr2.kp` lowers `[ for x in .. yield x*x ]` to `List Integer` | `__queryFromList`/`__pipeMap` lowering, `Eval.hs:641` |
| §20.3.2 | encounter order preserved | IMPLEMENTED+TESTED | `/tmp/kp/enc.kp` distinct → `3,1,2` (first-occurrence order) | order-preserving list backing |
| §20.4 | `for pat in coll`, `let pat = e`, `if cond` clauses | IMPLEMENTED+TESTED | `collections/*` conformance; `enc.kp` | `RawComprehension` lowering |
| §20.4 | borrowed generators `for x in &coll`, `for & pat in coll` | UNCLEAR | not probed (borrow lane); requires `BorrowSourceIntoQuery`/`BorrowItemsIntoQuery` which are MISSING names (`/tmp/kp` batch) | likely gap; deferred to borrow lane |
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
| §28.2 | **`Rational`** type exported | MISSING | `/tmp/kp/rat.kp` `r : Rational` → `E_NAME_UNRESOLVED 'Rational'` | §28.2 MUST; also blocks §28.2.2 `FieldLike Rational` |
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
| §28.2 | **`(~=)`** equivalence operator | MISSING | `/tmp/kp/equiv.kp` `1 ~= 1` → `E_NAME_UNRESOLVED '~='` | §28.2 term + §28.2.3 fixity MUST; `Equiv` trait also missing |
| §28.2 | numeric ops `zero one add (+) multiply (*) negate subDefined subtract (-) divDefined divide (/) modDefined modulo (%) nonZero` | IMPLEMENTED+TESTED | `/tmp/kp/intsub.kp` 3-5=-2; `/tmp/kp/intdiv.kp` 7/2=3; `/tmp/kp/fdiv.kp` 3.5 | proof obligations enforced (see §28.2.1) |
| §28.2 | `empty (<|>) orElse append (++) foldl foldr foldMap traverse filter filterMap sequence` | IMPLEMENTED+TESTED | `/tmp/kp/fold.kp` foldl→6; names resolve | |
| §28.2 | **`for_`, `sequence_`** | MISSING | `/tmp/kp/_q.kp` → `E_NAME_UNRESOLVED 'for_'` / `'sequence_'` | §28.2 required terms |
| §28.2 | `fromInteger fromFloat fromString buildInterpolated f re b type` | IMPLEMENTED+TESTED | numeric/string literals + f-strings work (todo.kp) | |
| §28.2 | **`next`** (Iterator), **`toQuery`** | MISSING | `/tmp/kp` batch → `E_NAME_UNRESOLVED` | `Iterator`/`IntoQuery` traits absent |
| §28.2 | proof helpers **`absurd pathInd subst sym trans cong unsafeAssertProof witness measureRelation lexRelation`** | MISSING | `/tmp/kp/_q.kp` `absurd`/`subst`/`sym` → `E_NAME_UNRESOLVED`; only `summon` present | §28.2 required terms; pure/core, not capability-gated |
| §28.2 | `floatEq` | IMPLEMENTED+TESTED | resolves; `evalPurePrim "floatEq"` IEEE eq (`Eval.hs:558`) | |
| §28.2 | `runPure` | IMPLEMENTED+TESTED | conformance `deep-handler-state` | |
| §28.2 | resource/finalize: **`sandbox unsandbox poll uninterruptible mask ensuring acquireRelease finally bracket`** | MISSING | `/tmp/kp/_q.kp` batch → `E_NAME_UNRESOLVED` for all listed | only `throwError catchError raise release` present |
| §28.2 | fibers/scopes/promises: **`fork forkDaemon await join interrupt fiberId currentFiberId cede blocking newScope withScope forkIn shutdownScope monitor awaitMonitor demonitor newFiberRef newPromise`** | MISSING (names) | `/tmp/kp` batch → `E_NAME_UNRESOLVED` (e.g. `await`, `fiberId`); `fork` resolves but rest do not | see §27.6 `rt-core` analysis below — partially profile-excusable but §28.2 surface MUST remains |
| §28.2 | STM: **`atomically newTVar readTVar writeTVar retry check`** | MISSING (names) | `/tmp/kp` batch → `E_NAME_UNRESOLVED 'atomically'` etc. | §27.6 `rt-core` includes single-agent STM |
| §28.2 | refs `newRef readRef writeRef` | IMPLEMENTED+TESTED (runtime) | runtime prims exist; usable via `var` | surface terms resolve through `MonadRef`-shaped prims |
| §28.2 | ranges `range (..) (..<)` | IMPLEMENTED-WEAKLY-TESTED | `range` resolves; constructs `NumericRange` | not iterable (see §20) |
| §28.2 | **collection terms** `listLength listAppend arrayEmpty arraySingleton arrayFromList arrayToList arrayLength arrayGet arrayIndex setEmpty setSingleton setInsert setDelete setMember setSize mapEmpty mapSingleton mapInsert mapDelete mapLookup mapMember mapSize` | MISSING (mostly) | `/tmp/kp/_q.kp` `arrayFromList`/`mapEmpty`/`mapInsert`/`mapLookup`/`setEmpty` → `E_NAME_UNRESOLVED`. Only `listLength`/`listAppend` resolve | only internal `__arrayFromList` etc. prims exist (`Prelude.hs:328-332`); not exported as surface terms. Pure/core — NOT capability-gated |
| §28.2 | `sizedArrayLength sizedArrayIndex sizedArrayToArray arrayAsSized` | MISSING | not exported | §28.2 required SizedArray ops |
| §28.2 | time: **`nowMonotonic nanos micros millis seconds minutes durationAdd durationSub durationCompare instantAdd instantDiff sleepFor sleepUntil timeout race`** | MISSING (names) | `/tmp/kp/_q.kp` `nanos` → `E_NAME_UNRESOLVED` | §27.6 `rt-core` includes monotonic timers |
| §28.2 | staging `liftCode closeCode genlet runCode syntaxOrigin withSyntaxOrigin` | IMPLEMENTED-WEAKLY-TESTED | `liftCode`/`closeCode`/`genlet`/`runCode` resolve | staging lane |
| §28.2 | output `show printString printlnString print println` | IMPLEMENTED+TESTED | every run probe | |

### §28.2 traits (probed presence)

| § | requirement (short) | status | evidence/probe | note |
|---|---|---|---|---|
| §28.2 | `Eq Ord Show Functor Applicative Monad Foldable Traversable Filterable FilterMap Monoid Rangeable Shareable Lift FromInteger FromFloat FromString InterpolatedMacro FromComprehensionPlan FromComprehensionRaw` | IMPLEMENTED+TESTED | `/tmp/kp` trait batch → present | |
| §28.2 | numeric op traits `Zero One Add Mul Negatable CheckedSub CheckedDiv CheckedMod` | IMPLEMENTED+TESTED | trait batch → present; probes enforce contracts | |
| §28.2 | **`Equiv`** | MISSING | trait batch → `E_NAME_UNRESOLVED 'Equiv'` | §28.2 required; pairs with `(~=)` |
| §28.2 | **`Alternative`** | MISSING | `/tmp/kp/p_alt.kp` → `E_NAME_UNRESOLVED 'Alternative'` | §28.2 required; blocks `empty`/`<|>` law surface |
| §28.2 | **`Iterator`** | MISSING | trait batch → unresolved | §18.6 portable loop protocol; §28.2 required |
| §28.2 | **`MonadError MonadFinally MonadResource MonadRef`** | MISSING | trait batch → unresolved (`Releasable` present) | §28.2/§19 required; `var` relies on `MonadRef` shape but trait unnameable |
| §28.2 | **`WellFoundedRelation`** | MISSING | trait batch → unresolved | §28.2/§15.11 required |
| §28.2 | **`IntoQuery BorrowSourceIntoQuery BorrowItemsIntoQuery`** | MISSING | trait batch → unresolved | §20.4/§20.10 comprehension/range source mechanism |
| §28.2 | **`QuotedLiteralMacro`** | MISSING | trait batch → unresolved | §6.5 g/b quoted-literal handlers |
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
| §28.2.2 | `AdditiveMonoid` trait | MISSING | `/tmp/kp/p_addmon.kp` → `E_NAME_UNRESOLVED 'AdditiveMonoid'` | absent from prelude (`grep` confirms) |
| §28.2.2 | `AdditiveGroup MultiplicativeMonoid Semiring Ring FieldLike OrderedAdditive OrderedSemiring` | MISSING | `/tmp/kp/p_ring.kp` `p_semiring.kp` `p_fieldlike.kp` → `E_NAME_UNRESOLVED` | only the words occur as comments; no decls |
| §28.2.2 | `EuclideanSemiring` = refines `(Semiring,Ord,CheckedDiv,CheckedMod)` with `divAndModSameDomain`,`divModIdentity` | SPEC-CONFLICT | embedded `trait EuclideanSemiring (a:Type) = euclideanDivMod : a -> a -> (a,a)` (`Prelude.hs:508`) — no superclasses, wrong members | structurally different trait under the same name |

### §28.2.3 standard numeric instances, domains, fixities

| § | requirement (short) | status | evidence/probe | note |
|---|---|---|---|---|
| §28.2.3 | operation instances for Nat: Zero,One,Add,Mul,CheckedSub,CheckedDiv,CheckedMod | MISSING (partial) | `/tmp/kp/natsub2.kp` → `E_UNSOLVED_IMPLICIT CheckedSub Nat`. `Prelude.hs` has `CheckedDiv Nat`,`CheckedMod Nat` but **no `CheckedSub Nat`** | `CheckedSub Nat` required and absent |
| §28.2.3 | operation instances for Integer/Int | IMPLEMENTED+TESTED | `Zero/One/Add/Mul/Negatable/CheckedSub/CheckedDiv/CheckedMod Integer` present (`Prelude.hs:612-629`) | Int via alias |
| §28.2.3 | operation instances for Rational | MISSING | `Rational` type absent → all instances absent | |
| §28.2.3 | `CheckedSub Float/Double` | MISSING | `/tmp/kp/dsub.kp` (Double 5.0-2.0) → `E_UNSOLVED_IMPLICIT CheckedSub Double` | only `CheckedDiv Double` present; `CheckedSub Double/Float` required and absent |
| §28.2.3 | Float/Double MUST NOT receive Semiring/Ring/FieldLike | IMPLEMENTED (vacuously) | those traits don't exist at all | satisfied by absence |
| §28.2.3 | **algebraic** instances (AdditiveMonoid Nat, Semiring Nat, Ring Integer, FieldLike Rational, ...) | MISSING | traits absent ⇒ instances absent | large block of §28.2.3 MUST instances unsatisfiable |
| §28.2.3 | fixity table (`==`,`&&`,`||`,`..`,`::`,`++`,`+`,`-`,`*`,`/`,`%`,prefix `-`,`:&`,`|>`,`<|`) | IMPLEMENTED+TESTED | `Resolve.defaultFixities` matches the table 1:1 (precedences/assoc) | `Resolve.hs:42-66`; `?.`/`?:` handled built-in by parser |
| §28.2.3 | `(~=)` same precedence/assoc as `(==)` | MISSING | `~=` operator absent entirely | n/a since operator missing |

## §29 Required Standard Modules

| § | requirement (short) | status | evidence/probe | note |
|---|---|---|---|---|
| §29.1 | `std.atomic` provided **iff backend advertises `rt-atomics`** | INTENTIONALLY-UNSUPPORTED (§29.1, §27.6) | `/tmp/kp/atom.kp` `import std.atomic` resolves (an embedded module exists, `Prelude.stdAtomicSource`) | provision is conditional on `rt-atomics`; module surface present |
| §29.2 | `std.supervisor` — **unconditional MUST** | IMPLEMENTED-WEAKLY-TESTED | `/tmp/kp/sup.kp` `import std.supervisor` resolves (no error) | embedded `stdSupervisorSource`; observable supervision semantics tied to `rt-core` (not interpreted) — surface present |
| §29.3 | `std.hash` — **unconditional MUST**; deterministic mixing | IMPLEMENTED+TESTED | `/tmp/kp/hd2.kp` `hashWith defaultHashSeed 42` deterministic ("equal"); `import std.hash` OK | `stdHashSource`; FNV-1a `Eval.hs:674` |
| §29.3 | `Hashable` instances for Unit/Bool/Int/Integer/Nat/Double/String/Bytes/Byte/UnicodeScalar/Grapheme/Ordering | IMPLEMENTED-WEAKLY-TESTED | all instances in `stdHashSource` (`Prelude.hs:1361-1392`) | derivation/structural hashing not re-probed |
| §29.4 | `std.unicode` — **unconditional MUST** | IMPLEMENTED-WEAKLY-TESTED | `/tmp/kp/uni2.kp` `byteLength "abc"` → 3 | `stdUnicodeSource`; doc admits incremental decoder/cursors NOT provided (UCD 15.0.0) |
| §29.4 | incremental decoder / builders / cursors | MISSING | per source comment `Prelude.hs:1409-1414` "the incremental decoder/builders/cursors of §29.4 are not provided" | §29.4 lists these as required ops |
| §29.5 | **`std.bytes` — unconditional MUST** | MISSING | `/tmp/kp/bytes.kp` `import std.bytes` → `E_MODULE_NAME_UNRESOLVED 'std.bytes' not part of this compilation unit` | NO embedded source for `std.bytes`; not wired in `Pipeline.preludeState` |
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
| §32.2 | IO/fibers/STM/interruption/handlers runtime model | INTENTIONALLY-UNSUPPORTED (§27.6, §32.2) | concurrency surface absent; "a backend that cannot satisfy a required capability MUST reject the affected program" (§32.2) — rejection is via E_NAME_UNRESOLVED at the surface | interpreter does not advertise `rt-core`; effect handlers + IO + refs ARE implemented; fibers/STM/timers are not |
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

### 1. §18.3.1 — `let x = !e` monadic splice fails (the spec's own canonical example) — MAJOR
- Spec: §18.3.1 example `let x = !readInt` / `let y = !readInt`.
- Probe `/tmp/kp/sp1.kp`:
  ```
  main : UIO Unit
  let main = do
      let x = !(getN 1)
      let y = !(getN 2)
      printlnString (show (x + y))
  ```
- Spec-required: runs, prints `1` `2` `3`.
- Observed: `error[E_SPLICE_OUTSIDE_DO]: monadic splice '!' is only valid inside a do block` at the `let` lines (it IS inside a do).
- Root cause: `DoLet` does not run `desugarBang` on the rhs, unlike `DoExpr`/`DoBind` (confirmed: `sp4.kp`/`sp5.kp` with `!` in statement/`<-` positions work).
- Fix locus: `src/Kappa/Check.hs`, `elabDoIOItems` `DoLet` branch (~lines 6879-6888): apply `desugarBang rhs` before `check`/`infer`, mirroring `DoExpr` (6808) and `DoBind` (6849).

### 2. §18.3.1 — immediate-application splice `!f x` parsed as `(!f) x` — MAJOR (SPEC-CONFLICT)
- Spec: §18.3.1 "`!f x y` is accepted as ergonomic sugar for `!(f x y)`. It is not parsed as `(!f) x y`."
- Probe `/tmp/kp/sp6.kp`: `!doit 8` (where `doit : Integer -> IO Void Unit`).
- Spec-required: runs `doit 8`, prints `8`.
- Observed: `error[E_TYPE_EQUALITY_MISMATCH] actual: Integer -> IO Void Unit, expected: IO ?m Unit` — i.e. `__runIO doit` then applied to `8`.
- Root cause: `desugarBang (EApp f args) = EApp (desugarBang f) ...` recurses into the head, turning `!f x` into `(__runIO f) x`.
- Fix locus: `src/Kappa/Check.hs` `desugarBang` (`Check.hs:7114-7130`) and/or the parser's `!` operand extent so `!f x` captures the whole application spine.

### 3. §29.5 — `std.bytes` standard module entirely absent (unconditional MUST) — MAJOR
- Spec: §29.5 "Implementations MUST provide a standard module `std.bytes`." (no capability gate).
- Probe `/tmp/kp/bytes.kp`: `import std.bytes`.
- Spec-required: module resolves; exports Byte/Bytes operations.
- Observed: `error[E_MODULE_NAME_UNRESOLVED]: imported module 'std.bytes' is not part of this compilation unit (Spec §8.2)`.
- Root cause: no `stdBytesSource`; not registered in `Pipeline.preludeState` `stdSources` (`Pipeline.hs:71-80`).
- Fix locus: add `stdBytesSource` to `src/Kappa/Prelude.hs` and wire it in `src/Kappa/Pipeline.hs:80`.

### 4. §28.2 — `Rational` type and all its required instances absent — MAJOR
- Spec: §28.2 lists `Rational` as a MUST-export type; §28.2.2 "`Rational` MUST receive `FieldLike`"; §28.2.3 mandates Zero/One/Add/Mul/Negatable/CheckedSub/CheckedDiv Rational + algebraic instances.
- Probe `/tmp/kp/rat.kp`: `r : Rational  /  let r = one`.
- Spec-required: `Rational` resolves.
- Observed: `error[E_NAME_UNRESOLVED]: unresolved name 'Rational' (not in scope)`.
- Root cause: no `Rational` in `Prelude.types`; `grep Rational src/Kappa/Prelude.hs` finds none.
- Fix locus: `src/Kappa/Prelude.hs` — add `Rational` type + numeric/algebraic instances.

### 5. §28.2.2/§28.2.3 — algebraic numeric trait hierarchy absent (AdditiveMonoid…FieldLike) — MAJOR
- Spec: §28.2.2 declares `AdditiveMonoid, AdditiveGroup, MultiplicativeMonoid, Semiring, Ring, EuclideanSemiring, FieldLike, OrderedAdditive, OrderedSemiring`; §28.2.3 mandates a large block of instances (e.g. `Semiring Nat`, `Ring Integer`, `FieldLike Rational`).
- Probes `/tmp/kp/p_ring.kp` (`Ring`), `p_semiring.kp` (`Semiring`), `p_addmon.kp` (`AdditiveMonoid`), `p_fieldlike.kp` (`FieldLike`).
- Spec-required: traits resolve.
- Observed: all → `error[E_NAME_UNRESOLVED]`.
- Bonus SPEC-CONFLICT: the one present `EuclideanSemiring` (`Prelude.hs:508`) has signature `euclideanDivMod : a -> a -> (a,a)`, completely unlike the spec's law-member-bearing refinement of `(Semiring,Ord,CheckedDiv,CheckedMod)`.
- Fix locus: `src/Kappa/Prelude.hs` — add the §28.2.2 trait hierarchy with law members and the §28.2.3 instances; correct `EuclideanSemiring`.

### 6. §28.2 — required prelude trait names absent: `Equiv`, `Alternative`, `Iterator`, `MonadError`, `MonadFinally`, `MonadResource`, `MonadRef`, `WellFoundedRelation`, `IntoQuery`, `BorrowSourceIntoQuery`, `BorrowItemsIntoQuery`, `QuotedLiteralMacro` — MAJOR
- Spec: §28.2 "Implementations MUST provide a prelude module … that exports at least the following" lists every one of these.
- Probe `/tmp/kp` trait batch + `/tmp/kp/me.kp`/`mf.kp`/`mr.kp`/`p_alt.kp`/`iq.kp`.
- Observed: each → `error[E_NAME_UNRESOLVED]`.
- Severity rationale: these are not concurrency runtime entities — they are abstract typeclasses used by core surface (`var`⇒`MonadRef`, `try`⇒`MonadError`/`MonadFinally`, loops⇒`Iterator`, ranges/comprehensions⇒`IntoQuery`, `(~=)`⇒`Equiv`, g/b literals⇒`QuotedLiteralMacro`, termination⇒`WellFoundedRelation`).
- Fix locus: `src/Kappa/Prelude.hs` `preludeSource` — declare these traits (the surface conformant signatures from §19/§20.2/§28.2).

### 7. §28.2 — `(~=)` equivalence operator absent — MAJOR
- Spec: §28.2 term list + §28.2.3 fixity table (MUST, same precedence/assoc as `(==)`).
- Probe `/tmp/kp/equiv.kp`: `1 ~= 1`.
- Observed: `error[E_NAME_UNRESOLVED]: unresolved name '~='`.
- Fix locus: `src/Kappa/Prelude.hs` (`(~=)` term + `Equiv` trait) and `src/Kappa/Resolve.hs` (add `~=` to `defaultFixities` at precedence 40, infix N).

### 8. §28.2 — surface collection terms absent: Array/Set/Map/SizedArray operations — MAJOR
- Spec: §28.2 mandates `arrayEmpty arraySingleton arrayFromList arrayToList arrayLength arrayGet arrayIndex setEmpty setSingleton setInsert setDelete setMember setSize mapEmpty mapSingleton mapInsert mapDelete mapLookup mapMember mapSize sizedArrayLength sizedArrayIndex sizedArrayToArray arrayAsSized`.
- Probe `/tmp/kp/_q.kp`: `arrayFromList`, `mapEmpty`, `mapInsert`, `mapLookup`, `setEmpty`.
- Observed: each → `error[E_NAME_UNRESOLVED]` (only `listLength`/`listAppend` resolve).
- Root cause: only internal `__arrayFromList`/`__setFromList`/`__mapFromEntries` prims exist (`Prelude.hs:328-332`) for comprehension lowering; no surface terms.
- Fix locus: `src/Kappa/Prelude.hs` `preludeSource` — export the §28.2 collection operations (over the existing `Array`/`Set`/`Map` carriers and internal prims).

### 9. §28.2 — proof/equality helper terms absent: `absurd subst sym trans cong pathInd unsafeAssertProof witness measureRelation lexRelation` — MAJOR
- Spec: §28.2 term list (all MUST).
- Probe `/tmp/kp/_q.kp`: `absurd`, `subst`, `sym`.
- Observed: `error[E_NAME_UNRESOLVED]` (only `summon` of this family present).
- Severity rationale: pure dependent-type primitives, not capability-gated; used in portable proof code.
- Fix locus: `src/Kappa/Prelude.hs` — declare these (several already have spec-given bodies, e.g. `witness`, `sym` via `pathInd`).

### 10. §28.2.3 — `CheckedSub Nat` and `CheckedSub Float/Double` instances missing — MAJOR
- Spec: §28.2.3 operation-instance block requires `CheckedSub Nat` and `CheckedSub Float`/`CheckedSub Double`.
- Probes: `/tmp/kp/natsub2.kp` → `E_UNSOLVED_IMPLICIT CheckedSub Nat`; `/tmp/kp/dsub.kp` → `E_UNSOLVED_IMPLICIT CheckedSub Double`.
- Root cause: `Prelude.hs` declares `CheckedDiv Nat`/`CheckedMod Nat`/`CheckedDiv Double` but no `CheckedSub` for `Nat`/`Double`/`Float`.
- Note: portable `Nat` subtraction (`y<=x` domain) and Double subtraction (`subDefined=True`) are explicitly required to be usable; today `a - b` over an explicit `Nat`/`Double` fails to elaborate.
- Fix locus: `src/Kappa/Prelude.hs` — add `instance CheckedSub Nat` (subDefined = `y<=x`) and `instance CheckedSub Double`/`Float` (subDefined = True).

### 11. §28.2 — `for_` and `sequence_` absent — MINOR
- Spec: §28.2 term list.
- Probe `/tmp/kp/_q.kp`: `for_`, `sequence_` → `E_NAME_UNRESOLVED`.
- Fix locus: `src/Kappa/Prelude.hs` (`sequence` exists; add the `_`-discarding variants).

### 12. §20.2 / §18.6 — ranges cannot be iterated (`IntoQuery` mechanism missing) — MINOR
- Spec: §20.2 "Iterating a range is governed by `IntoQuery`"; ranges are usable as comprehension/loop sources.
- Probes `/tmp/kp/dofor.kp` (`for x in 1 .. 3 do`), `/tmp/kp/rng2.kp` (`[ for x in 1 .. 5 yield x ]`).
- Spec-required: iterate over the range elements.
- Observed: `E_TYPE_EQUALITY_MISMATCH actual: NumericRange Integer, expected: List` — `for`/comprehension source only accepts `List`.
- Root cause: no `IntoQuery` trait; the comprehension/loop source lowering hardcodes `List`.
- Severity MINOR (range *construction* works; iteration is the missing piece) but blocks a common idiom.
- Fix locus: `src/Kappa/Prelude.hs` (`IntoQuery` + `IntoQuery` instances for `List`/`NumericRange`) and `src/Kappa/Check.hs` comprehension/`for` source elaboration to dispatch through `IntoQuery`.

### 13. §29.4 — `std.unicode` incremental decoder / builders / cursors missing — MINOR
- Spec: §29.4 lists incremental decoder, builders, and cursor operations as required `std.unicode` surface.
- Evidence: source self-documents the omission (`Prelude.hs:1409-1414`); core ops (`utf8Bytes`/`byteLength`/normalization) work (`/tmp/kp/uni2.kp`).
- Fix locus: `src/Kappa/Prelude.hs` `stdUnicodeSource` + supporting prims in `src/Kappa/Eval.hs`.

---

## Profile-scoped / intentionally-unsupported (cited)

These are NOT counted as gaps because a spec clause makes them conditional, OR the SCOPE RULE
(interpreter need not implement backends/concurrency runtime) plus §27.6/§32.2 rejection rule applies.
Caveat noted where §28.2 surface-presence still tensions with the runtime gating.

- **Fibers / scopes / monitors / promises / fiber-local state / monotonic timers** (`fork…demonitor`, `nowMonotonic`, `nanos`, `timeout`, `race`, …): §27.6 places these under capability `rt-core`; §27.6/§32.2 permit a backend lacking the capability to **reject** affected programs. The interpreter does not advertise `rt-core` and rejects via `E_NAME_UNRESOLVED`. **Tension (noted, not scored):** §28.2 still lists these as prelude-surface terms the prelude MUST export; today they are not even nameable, so the rejection is at the *resolution* layer rather than a clean capability diagnostic. A stricter reading would make their *surface absence* a §28.2 gap. Flagged for adjudication.
- **STM** (`atomically`, `newTVar`, `readTVar`, `writeTVar`, `retry`, `check`): §27.6 single-agent STM is part of `rt-core`; same rejection rationale as above. Same §28.2 surface tension.
- **`std.atomic`** (§29.1): provision gated on backend capability `rt-atomics` ("Implementations that advertise backend capability `rt-atomics` MUST provide…"). An embedded surface IS present but the runtime atomic semantics (§32.2.10) are not interpreter-realized.
- **`std.debug`** (§29.6): MUST only "when `allow_debug_introspection` is enabled". No such mode is enabled; non-provision permitted.
- **`std.config`** (§29.7): MUST only for implementations "supporting config mode" (§35). Config mode is profile-scoped; not implemented.
- **`std.build`** (§29.8): MUST only for implementations "supporting build manifests" (§36). Build system is profile-scoped; not implemented.
- **§32.2 runtime model for IO/fibers/STM/interruption** (full): §32.2 + §27.6 permit rejection by a backend lacking the capability; the interpreter implements IO + refs + algebraic-effect handlers, not the concurrency kernel.
- **§33.1.1/§33.1.2 Easy/Hard hash machinery + persistent cache**: the persistent `EasyHash→HardIdentity` cache is a **package-mode** MUST (§33.1.2); package mode (§36) is profile-scoped/unimplemented. Script-mode default is `semantic-if-available`, which sanctions unavailability of `HardIdentity` with conservative fallback. The only externally-observable §33 MUST — instance coherence (§33.2.1) — IS enforced (`E_INSTANCE_INCOHERENT`). §33.2.2 fast-path defeq is explicitly "MAY".
- **§18.9 `inout`, §20.4 borrowed generators, §20.8 joins**: deferred to the types/borrow lane; not disproved here.

---

## Status counts (this lane)

- IMPLEMENTED+TESTED: 33
- IMPLEMENTED-WEAKLY-TESTED: 17
- MISSING: 24
- INTENTIONALLY-UNSUPPORTED (cited): 9
- SPEC-CONFLICT: 2 (§18.3.1 `!f x` parse; §28.2.2 `EuclideanSemiring` shape)
- UNCLEAR: 6

(Some rows enumerate multiple names; the MISSING count reflects distinct requirement rows, not the
~50 individually-probed missing prelude names.)
