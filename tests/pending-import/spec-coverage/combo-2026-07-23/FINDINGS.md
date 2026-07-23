# Round-3 findings — consolidated compiler bug list (2026-07-23)

From the probe-first combination/DX/robustness campaign against clean `a0497523`.
Every entry is pinned by a test in this directory or `../../dx-issues/`; repro notes
below are abbreviated — the pinning test header has the full story.


## Soundness (checker accepts what must be rejected, or vice versa) (12)

- **Guard consumption of linear/affine values not accumulated into guard-failure fallthrough path (runtime double-consume)** `[combo-qtt-patterns]`
  tests/pending-import/spec-coverage/patterns-active/guard-consume-linear-fallthrough-reject.kp — `case Box r if spend r -> 1 / case Box r -> resVal r` with (1 b : Box) accepted with 0 errors; on the guard-false path `spend` (demands 1) and `resVal` both consume the same component. Param flavor: irre…

- **Guard usage of the case's own pattern binders is entirely untracked (same-case guard+body double consume accepted)** `[combo-qtt-patterns]`
  tests/pending-import/spec-coverage/patterns-active/guard-plus-body-linear-pattern-binder-reject.kp — `case Box r if spend r -> resVal r` (both demand 1 r) accepted with 0 errors; identical shape with r a linear function parameter is rejected with E_QTT_LINEAR_OVERUSE.

- **Field binders under a borrowed scrutinee are consumable (borrowed projections can satisfy quantity-1 demands, in bodies and guards)** `[combo-qtt-patterns]`
  tests/pending-import/spec-coverage/borrows-places/borrowed-match-projection-consume-reject.kp — (& t : Two), `case TA r -> resVal r` with resVal : (1 r : Res) -> Int accepted with 0 errors (direct borrowed-binder-to-linear is rejected, cf. conformance/qtt/borrow-qtt-030). Guard flavor: borrowed-sc…

- **Borrowed active-pattern call on a linear scrutinee is credited as its consumption: Hit-path linear leak accepted AND legal post-narrowing consume falsely rejected** `[combo-qtt-patterns]`
  tests/pending-import/spec-coverage/functions-quantities/borrowed-option-ap-hit-path-linear-leak-reject.kp (leak accepted: `case PosVal (n) -> n` with PosVal (& b : Buf), 1 b never consumed, 0 errors) and borrowed-option-ap-nonconsuming-narrowing-accept.kp (false E_QTT_LINEAR_OVERUSE on `case PosVal (_) …

- **Affine (<=1) Option active pattern: failed call + fallthrough re-use = two demands in [0,1], accepted** `[combo-qtt-patterns]`
  tests/pending-import/spec-coverage/functions-quantities/affine-option-ap-fallthrough-reject.kp — MaybeTake (<=1 b) : Option Int; `case MaybeTake (n) -> n / case rest -> bufValue rest` with (<=1 b) accepted with 0 errors; None path demands b twice (use-after-consume once RC lands).

- **As-pattern on a linear scrutinee double-owns whole and part; consuming both accepted** `[combo-qtt-patterns]`
  tests/pending-import/spec-coverage/patterns-active/as-pattern-linear-whole-and-part-reject.kp — (1 t : Two), `case whole @ (TA r) -> resVal r + twoVal whole` accepted with 0 errors; the linear component is consumed twice (directly and through whole).

- **`~` accepts a borrowed binding as inout argument: linear place consumed twice, write-back detaches alias from root** `[combo-borrows-records]`
  Pin: tests/pending-import/spec-coverage/borrows-places/inout-marker-on-borrowed-binder-linear.kp (and ...-through-borrowed-alias-projection.kp). Minimal: type Box = (1 tok : Token, tag : Int); in a do block, nested `do { let & v = box.tok; useToken ~v }` then `finish box` — checks with 0 errors, s…

- **Read/Borrow projector elimination ignores consumed-path state (use-after-move through projections and descriptors)** `[combo-borrows-records]`
  Pins: projection-read-of-consumed-path.kp, projector-descriptor-read-of-consumed-path.kp. type LinCell = (1 value : Token, tag : Int); projection linValue (place this : LinCell) : Token = yield this.value. After `let moved = takeToken cell.value`, the direct form `observeToken cell.value` is rejecte…

- **Opaque-data inhabitance leaks across module boundary: importer's case impossible accepted on opaque empty data** `[combo-existentials-match]`
  tests/pending-import/spec-coverage/adts/opaque-empty-data-cross-module-case-impossible/ — lib: `opaque data Never : Type`; main imports `type Never` and writes `match x case impossible` at `Never -> Int`. Observed: 0 errors. Expected: E_INDEXED_IMPOSSIBLE_REACHABLE — §30.2.7 keys the sum…

- **Erasure hole: quantity-0 existential payload field bound by open is runtime-matchable** `[combo-existentials-match]`
  tests/pending-import/spec-coverage/rows-packages-existentials/existential-open-erased-payload-field-match.kp — pkg : exists (a : Type). (0 hidden : Option Int); `open pkg as exists (a). (hidden = h) in match h case ...` observed: 0 errors. Expected: E_QTT_ERASED_RUNTIME_USE per §17.1.3/§31.2 (neither Option c…

- **List literal launders linear quantity: linear value duplicated and dropped through comprehension generators** `[combo-queries-linearity]`
  tests/pending-import/spec-coverage/queries-lowering/list-literal-linear-item-dup-through-query.kp — `let dupTok (1 a : Token) = let xs = [a] in foldl addInt 0 [ for t in xs, for u in xs, yield addInt (consumeToken t) (consumeToken u) ]` typechecks and RUNS, printing 2 (linear token consumed twice); …

- **Terminal map/set collection silently drops non-droppable linear items (on conflict keep last/first, set dedup)** `[combo-queries-linearity]`
  tests/pending-import/spec-coverage/queries-lowering/terminal-collection-drops-linear-items-rejected.kp — `{ for t in src, yield 1 : t, on conflict keep last }` with `(1 src : QueryCore (QueryMode OneShot QZeroOrMore) 1 Token)` typechecks (0 errors) though §20.10.10 requires conflict-losing values dr…


## Crashes (1)

- **Literal pattern at Rational scrutinee: check accepts, evaluation gets stuck (runtime crash)** `[combo-numerics-traits]`
  isZeroR : Rational -> Bool = match x case 0 -> True case _ -> False; run mode: 'runtime failure: unhandled IO primitive: printlnString/1 args=if match __rat 0 1 ...' — the exhaustive match takes no branch against the internal __rat value. Same-shape pattern at a user FromInteger type is rejected at …


## Wrong results / spec non-conformance (45)

- **Consuming total active patterns rejected wholesale at declaration, contradicting §17.3.5/§17.3.6.2; existing conformance test passes coincidentally** `[combo-qtt-patterns]`
  tests/pending-import/spec-coverage/patterns-active/consuming-total-view-grouped-accept.kp — `pattern See (1 w : Wrap) : View = ...` errors E_ACTIVE_PATTERN_LINEARITY_VIOLATION at the declaration; spec permits it with grouped-exhaustive or irrefutable subpatterns. Side effect: conformance/spec-cover…

- **>=1 demands made inside guards are not credited to the §17.1.10 branchwise join (false rejection of sound code)** `[combo-qtt-patterns]`
  tests/pending-import/spec-coverage/patterns-active/relevant-demand-in-guard-accept.kp — (>=1 x : Int), `match n case m if m > x -> m / case m -> m + x`: every completion path demands x, but the checker emits E_QTT_LINEAR_DROP (kappa.quantity.positive-lower-bound).

- **Record patch of an unrestricted root is treated as a consuming use, spuriously rejecting patches under live borrows** `[combo-borrows-records]`
  Pin: record-patch-unrestricted-root-under-live-borrow.kp. With p : Pair unrestricted, `let & l = p.left in p.{ right = 5 }` (or left = 10) → E_QTT_BORROW_OVERLAP "'p' is consumed while a live borrow ... exists", yet the patch's normative §13.2.5 elaboration `(left = 10, right = p.right)` is accepted…

- **`let &` record-pattern borrow gets a whole-record footprint instead of §12.4 pathwise decomposition** `[combo-borrows-records]`
  Pin: pattern-borrow-decomposed-pathwise-inout.kp. `let & (left = bl) = p` followed by `bump ~p.right` → E_QTT_BORROW_OVERLAP on p.right, though §12.4 explicitly says the pattern introduces borrows of the matched fields only ('not one undifferentiated borrow of all of r'). Baseline `let & bl = p.left…

- **return inside a finally clause is accepted and silently ignored** `[combo-effects-resources]`
  tests/pending-import/spec-coverage/loops-var-inout/finally-return-out-rejected.kp — `try (printlnString "body") finally -> do { return 42 }` inside `worker : UIO Int` compiles with 0 errors (the defer twin is rejected with E_DEFER_ABRUPT_CONTROL); at runtime the return is a no-op on both the normal…

- **surface try/finally hardcodes the IO carrier; rejected in Eff even though its normative elaboration typechecks** `[combo-effects-resources]`
  tests/pending-import/spec-coverage/errors-collections/eff-carrier-try-finally.kp — `try (Log.emit 1) finally -> Log.emit 2` in an `Eff <[Log : Log]>` do-block fails with E_TYPE_EQUALITY_MISMATCH "actual: Eff ... expected: IO _ _", while the §19.2 rule-5 elaboration of the same form (`do { defer (Log.e…

- **Witness-escape check is result-type-shape-dependent: constructor-applied types slip through** `[combo-existentials-match]`
  tests/pending-import/spec-coverage/rows-packages-existentials/existential-open-escape-match-constructor-result.kp — dead-local package p; `open p as exists (a). x in match x case Option.Some y -> Option.Some y ...` (inferred type Option a) accepted with 0 errors, while the same open returning `\(y : a) -> y` …

- **impossible/case-impossible verification ignores the active refinement context (flow HasCtor/LacksCtor, narrowing, contradictions) while exhaustiveness consults it** `[combo-gadt-flow]`
  tests/pending-import/spec-coverage/patterns-active/impossible-ignores-is-evidence.kp — minimal: 'if p is Box then match p case Box v -> v case Empty -> impossible else 0' gives E_IMPOSSIBLE_REACHABLE, while deleting the Empty arm outright is accepted (same remainder). Also manifests failure-side (e…

- **Family-argument equalities from an outer GADT constructor branch do not reach nested-match reachability (contradictory shared abstract index)** `[combo-gadt-flow]`
  tests/pending-import/spec-coverage/patterns-active/nested-match-contradictory-indices.kp — v w : Natural n; outer 'case Zero' forces n = Z, inner 'case Succ p -> impossible' on w still E_IMPOSSIBLE_REACHABLE (and omission is E_PATTERN_NON_EXHAUSTIVE). §17.1.2 requires the equalities to participate …

- **Guard-position constructor evidence entirely missing — even atomic is-test guards install no HasCtor (broader than the known operator-guard pin)** `[combo-gadt-flow]`
  tests/pending-import/spec-coverage/patterns-active/guard-atomic-is-evidence.kp — 'case Box w if q is Box -> w + q.value' gives E_UNRESOLVED_MEMBER and a nested 'match q case Box x' gives E_PATTERN_NON_EXHAUSTIVE; no §16.4.2 operators involved, so this is §16.4.1-in-guard-position (§17.1.9) missing …

- **Unique-remaining narrowing does not count index-refuted GADT constructors, inconsistently with index-aware exhaustiveness** `[combo-gadt-flow]`
  tests/pending-import/dx-issues/gadt-index-refuted-ctor-narrowing.kp — at Choice True (ctors Always/Also share size, Never : Choice False), 'if c is Always then c.size else c.size' and the match-residual form both fail E_UNRESOLVED_MEMBER in the negative branch: narrowing sees two remaining ctors, th…

- **Aliased kind-selector import ignores facet filter for same-spelling data families** `[combo-traits-modules]`
  tests/pending-import/spec-coverage/traits-instances/ctor-alias-selector-not-type-in-instance-head/ — `import lib.(ctor Pair as mkP)` (Pair a same-spelling data family) makes `mkP` usable as a TYPE: `v : mkP`, and `instance Sum mkP =` are both accepted with 0 errors. Spec §8.3.1 (L7333-L7334): with a…

- **Instance head at an opaque type alias keeps the abstract spelling instead of the §14.3.2 declaration-site-normalized head** `[combo-traits-modules]`
  tests/pending-import/dx-issues/opaque-alias-instance-head-identity/ — lib declares `opaque type Id = Int` and `instance Tag Id`. Downstream, goal `Tag Id` (via `tag (mkId 0)`) SOLVES and goal `Tag Int` (via `tag (5 : Int)`) is E_UNSOLVED_IMPLICIT ("could not resolve implicit argument of type Tag Int…

- **defer@L cannot target a labeled statement-position do block** `[combo-do-sugar]`
  let main = do { L@do { defer@L printlnString "d"; printlnString "body" }; printlnString "after" } -> E_LABEL_UNRESOLVED "defer@L does not target an enclosing labeled do-scope (explicit 'do' or loop)" at the defer. Expected per §18.7 (a do-scope is introduced by an explicit do block) + §18.2.5: sched…

- **Duplicate labels at the same lexical nesting level are silently accepted** `[combo-do-sugar]`
  Two sibling L@for loops (one containing break@L) and two sibling M@\ lambdas in one do block compile with 0 errors; §18.2.5 L24818 says this MUST be a compile-time error. Pinned: tests/pending-import/spec-coverage/do-blocks/duplicate-sibling-labels-error.kp (assertErrorCount 2)

- **return (abrupt-control) in let?-else failure arm parses as unresolved name** `[combo-do-sugar]`
  do { let? Some n = opt else _ -> return 0; ... } -> E_NAME_UNRESOLVED "unresolved name 'return'" (both inline and continuation-line else). §18.2.1 explicitly permits an abrupt-control do-item (return/break/continue) as failExpr. ALREADY PINNED by a prior campaign at tests/pending-import/spec-coverag…

- **Singleton comprehension consuming an outer linear rejected with E_QTT_LINEAR_OVERUSE** `[combo-queries-linearity]`
  tests/pending-import/spec-coverage/queries-lowering/singleton-comprehension-consumes-outer-linear.kp — `single : (1 tok : Token) -> List Int; let single tok = [ yield consumeToken tok ]` rejected "'tok' is consumed more often than its linear quantity permits" though §20.10.6 makes the empty clause s…

- **Quoted global references are captured by same-named splice-site locals (hygiene violation)** `[combo-strings-macros]`
  tests/pending-import/spec-coverage/macros-reflection/spliced-global-shadowed-at-splice-site.kp — `hidden = 5` at module level; macro quotes '{ addInt hidden 0 }; splicing under a local `let hidden = 999` yields 999 instead of 5 (both via $(...) and via a prefixed-string handler). §21.4 requires splic…

- **`f` prefix hardcoded in Check.hs elabString; in-scope user handler silently ignored** `[combo-strings-macros]`
  tests/pending-import/spec-coverage/literals/prefix-resolution-user-f-handler.kp — a module-level `f : Elab (InterpolatedMacro String)` returning "CUSTOM" is in scope, but f"x${n}y" evaluates to "x7y" via the hardcoded show-concat path (src/Kappa/Check.hs:13653 `(Just "f", _)`). §6.3.4 requir…

- **Union-typed union members are unconstructible (matchable dead arms)** `[combo-unions-transport]`
  tests/pending-import/spec-coverage/unions-records/union-of-union-member-uninhabitable.kp — type Inner = (| Integer | String |); type Outer = (| Inner | Bool |); both `let inj v = (| v : Inner |)` and `let inj v = v` at expected Outer fail E_TYPE_EQUALITY_MISMATCH (the injection expression itself e…

- **Constructor-forced equality on a Type-valued GADT index never refines the branch** `[combo-unions-transport]`
  tests/pending-import/spec-coverage/unions-records/gadt-union-index-branch-widen.kp — data Shape (u : Type) with SmallShape : Shape (| Integer | String |); matching it against Shape u leaves v : u unrefined so the §13.1.3 widening to the result union never applies; observed E_TYPE_EQUALITY_MISMATCH…

- **Exhaustiveness never refutes constructors via Type-valued index unification** `[combo-unions-transport]`
  tests/pending-import/spec-coverage/unions-records/gadt-union-index-impossible-arm.kp — classify : Shape (| String | Integer |) -> Integer with only the SmallShape arm is rejected E_PATTERN_NON_EXHAUSTIVE 'missing cases: BigShape', though BigShape's 3-member index cannot unify with the 2-member scr…

- **Fixity metadata dropped when an operator is re-exported** `[combo-crossmodule]`
  tests/pending-import/spec-coverage/lexical/operator-fixity-through-reexport — a declares `infix left 60 (+++)`; b does `export a.((+++))`; main does `import b.((+++))` and writes `2 +++ 3 +++ 4`. Observed: E_OPERATOR_NO_FIXITY (the term itself resolves fine), and after the error, recovery p…

- **Module re-export (export M / export M as A) not implemented** `[combo-crossmodule]`
  tests/pending-import/spec-coverage/modules-imports/module-reexport-qualified-access — b contains `export a as util`; main `import b.(util)` gives E_IMPORT_ITEM_NOT_FOUND "module 'b' does not export 'util'" and `b.util.answer` gives E_NAME_UNRESOLVED "module 'b' has no exported member 'util'". Unali…

- **Qualified references to imported effect labels rejected in all effect-label positions** `[combo-crossmodule]`
  tests/pending-import/spec-coverage/modules-imports/qualified-effect-label-cross-module — after `import elib`, the row annotation `comp : Eff <[elib.counterL : elib.Counter]> Int` is a PARSE error (E_RECOVERY_DECLARATION_SKIPPED "unexpected '<['"; any dotted name in row-label position fails, includi…

- **Type-kind import clobbers constructor resolution in term position (cross-kind collision)** `[combo-crossmodule]`
  tests/pending-import/spec-coverage/modules-imports/kind-selector-cross-kind-imports — `import a.(ctor Box)` (data Box with ctor Box) plus `import b.(type Box)` (type Box = Int): term-position `Box 5` resolves to b's reified alias facet and errors E_APPLICATION_NONCALLABLE. Per §7.1/§7.6 the ctor mu…

- **Numeric-literal suffixes silently discarded in pattern position (even unresolved ones)** `[combo-numerics-traits]`
  px : Nat -> Int; let px n = mulInt (natToInt n) 2; match n case 12px -> 111 case _ -> 999 — compiles clean and matches n==12 (not px 12 = 24), so 12px means 24 in expressions and 12 in patterns. Worse, case 12zz / case 2.5ww with zz/ww NOT IN SCOPE also compile with 0 errors, violating 6.1.6's MUST-…

- **List/Set collection literals do not propagate the demanded element type into literal elaboration; eager per-element defaulting is element-order-dependent** `[combo-numerics-traits]`
  intsAtRational : List Rational = [1, 2] rejected ('actual: List Integer, expected: List Rational') while 1 :: 2 :: Nil, (1,2) : (Rational, Rational), and Some 1 : Option Rational are all accepted; unannotated [2.5, 1] typechecks as List Float but [1, 2.5] errors with E_NUMERIC_LITERAL_DOMAIN_MISMATC…

- **IO-family do blocks accept bare pure final (and non-final) expression items, contra §18.2.2/§18.8.6, and inconsistently with user monads** `[dx-beginner-1]`
  tests/pending-import/spec-coverage/do-blocks/do-tail-pure-value-io-not-lifted.kp — `main : UIO Int = do { printInt 1; n }` with n : Int checks clean (observed: also runs; also a NON-final pure item `41 + 1; printInt 2` is accepted), though §18.2.2 types expression items as `expr : m a`, §18.8…

- **Harness: `kappa test <dir>/suite.ktest` vacuously passes, ignoring all sibling .kp sources** `[dx-beginner-2]`
  mkdir d; d/main.kp = `module main` + `let x = definitelyNotAName`; d/suite.ktest = `--! mode check` + `--! packageMode` + `--! assertNoErrors`. `kappa test d/suite.ktest` -> PASS (compiles nothing, 0 diagnostics); `kappa test d` -> FAIL with E_NAME_UNRESOLVED. Pointing CI or a user at the suite file…

- **Spec-required Array container instances missing (Functor/Foldable/Traversable/Filterable/FilterMap Array)** `[dx-prelude-ergonomics]`
  map (\x -> x*2) (arrayFromList (1::2::3::Nil)) — E_UNSOLVED_IMPLICIT Functor Array (and likewise for foldr/filter/filterMap/traverse). Rejects spec-conformant source; §28.2 L34525/L35025 make these MUST. Pin: tests/pending-import/spec-coverage/prelude/prelude-array-container-instances.kp

- **Eq/Ord/Show instances for Duration and Instant missing** `[dx-prelude-ergonomics]`
  millis 5 == micros 5000 — E_UNSOLVED_IMPLICIT Eq Duration; compare/show likewise, and same for Instant. §28.2 L34912-34919 requires all six. Pin: tests/pending-import/spec-coverage/prelude/prelude-duration-instant-eq-ord-show.kp

- **orElse bound to Option default-extractor instead of Alternative member; Alternative empty misspelled emptyA** `[dx-prelude-ergonomics]`
  Generic (@_ : Alternative f) -> f a -> f a -> f a body `orElse x y` is E_TYPE_EQUALITY_MISMATCH (prelude orElse : Option a -> a -> a); alt.orElse/alt.empty are E_UNRESOLVED_MEMBER. Spec L34532-34537 declares empty/(<|>)/orElse as the members. Pin: tests/pending-import/spec-coverage/prelude/prelude-alternative-empty-orelse-members.kp

- **pure is IO-only (member misspelled pureA) and (<*>) absent from prelude** `[dx-prelude-ergonomics]`
  pure 1 : Option Integer — E_TYPE_EQUALITY_MISMATCH against ioPure; (Some (\x -> x+1)) <*> (Some 1) — E_NAME_UNRESOLVED '<*>'. §14.1 L18096/L18104 declare both as Applicative members; §28.2 L33605 exports both. Pin: tests/pending-import/spec-coverage/prelude/prelude-pure-ap-applicative-members.kp

- **Applicative lacks §14.1 Functor superclass; map over Result unsolvable despite Applicative (Result e)** `[dx-prelude-ergonomics]`
  map (\x -> x+1) (Ok 41 : Result String Integer) — E_UNSOLVED_IMPLICIT Functor (Result String), while liftA2 over the same type solves. Spec: trait Functor f => Applicative (L18094) is the std.prelude declaration (L34902). Pin: tests/pending-import/spec-coverage/prelude/result-map-functor-superclass.kp

- **Successor and Max operation traits (succ/max) absent despite §28.2.1 canonical declarations** `[dx-prelude-ergonomics]`
  useMax : (@_ : Max a) -> a -> a -> a = max — E_NAME_UNRESOLVED for Successor, succ, Max, and max (4 errors). §28.2.1 L35062-35077 declares both traits; §28.2.3 L34939 requires their TypeLevel instances. Pin: tests/pending-import/spec-coverage/prelude/prelude-successor-max-trait-surface.kp

- **CRLF source: multiline-string bodies keep raw CR bytes (silent content divergence / spurious E_MULTILINE_STRING_BAD_INDENT)** `[dx-layout]`
  CRLF-encoded file with `let sample = """\r\nab\r\n"""` (flush closer): sample evaluates to "\r\nab\r\n" — phantom leading line plus CR after every line — where the LF-equivalent file gives "ab\n"; with an indented closing delimiter the same file is instead rejected with E_MULTILINE_STRING_BAD_INDENT…

- **Explicit @proof argument after auto-synthesized trait evidence is rejected (breaks existing conformance test at HEAD)** `[dx-runtime]`
  Pinned: tests/pending-import/spec-coverage/lambdas-implicits-flow/explicit-proof-implicit-after-evidence.kp. Minimal: `mydivop : forall (a : Type). (@_ : CheckedDiv a) -> (x : a) -> (y : a) -> (@_ : divDefined x y = True) -> a ; let mydivop x y @p = divide x y @p` -> E_APPLICATION_ARGUMENT_MISMATCH "an ex…

- **Duplicate `data` declarations silently merge into one type with the union of both constructor sets** `[dx-consistency]`
  tests/pending-import/spec-coverage/adts/duplicate-data-declarations-merge-rejected.kp — `data T = MkT (n : Integer)` then `data T = OtherT (b : Bool)`: zero diagnostics; `MkT 1 : T` and `OtherT True : T` both check, a match must cover BOTH ctors to be exhaustive, and the merged program r…

- **Duplicate `type` aliases silently accepted with last-wins semantics** `[dx-consistency]`
  tests/pending-import/spec-coverage/declarations/duplicate-type-alias-declarations-rejected.kp — `type T = Integer; type T = Bool; x : T; let x = True` checks clean: the later alias replaces the earlier one with no diagnostic, while the identical mistake with two `let x` gets E_DUPLICATE_DECLARAT…

- **Same-spelling constructors in two data types: later ctor silently shadows earlier in unqualified use** `[dx-consistency]`
  tests/pending-import/spec-coverage/adts/duplicate-ctor-spelling-across-datatypes-rejected.kp — `data A = Mk (n : Integer); data B = Mk (b : Bool)`: no duplicate report (§7.1/§7.2 require one); `Mk 1 : A` elaborates against B.Mk and blames the use with 'actual B / expected A' + a literal-…

- **Duplicate fixity declarations silently ignored (first-wins); parse depends on declaration order** `[dx-consistency]`
  tests/pending-import/spec-coverage/lexical/duplicate-fixity-declarations-collide.kp — with `infix left 70 (<+>)` then `infix left 30 (<+>)` and <+> = (*), `2 <+> 3 + 4` evaluates to 10; swapping the two fixity lines gives 14. No diagnostic either way; §5.5.1A says the declarations collide.

- **`trait T` displaces same-spelling `data T` in the binding group: type position resolves T to the trait** `[dx-consistency]`
  tests/pending-import/spec-coverage/names-resolution/trait-data-same-spelling-type-position-selects-type.kp — data T + trait T (spec: distinct kinds coexist; type position admits only `type` kind) then `useTy : T` fails E_NOT_A_TYPE 'this expression has type (0 a : Type) -> Type'. Sibling symptom of …

- **Backtick-identifier literal prefixes are never resolved (prefixed strings and prefixed quoted literals)** `[robust-literals]`
  let x : Byte = `b`'a' and let s : String = `f`"n = $n" each fail with E_NAME_UNRESOLVED for b/f (plus a nonsense "did you mean '%'" fix hint), while the unquoted spellings b'a' / f"..." compile; Spec 6.3.4 and 6.5 explicitly admit backtick identifiers as prefixes and 5.1 makes backticks the same nam…

- **Declared §15.4 Int `decreases` measures never combine with the §15.10 hidden phase in mutual SCCs** `[robust-scale]`
  Pinned at tests/pending-import/spec-coverage/proofs-deriving-totality/mutual-decreases-int-hidden-phase.kp. Minimal 2-member source: `k0 : Int -> Int` / `k1 : Int -> Int`; `let k0 n decreases n = if n <= 0 then 0 else k1 n`; `let k1 n decreases n = if n <= 0 then 1 else k0 (n - 1)`. Observed: both members g…


## Diagnostic quality (48)

- **Guard on a consuming Match-returning active-pattern case rejected with internal-elaboration diagnostic 'missing cases: Hit'** `[combo-qtt-patterns]`
  tests/pending-import/dx-issues/guard-on-consuming-match-active-pattern-diagnostic.kp — `case TakePositive (n) if n > 10 -> ...` over a 1 scrutinee: E_PATTERN_NON_EXHAUSTIVE at the match head naming the never-written Hit constructor; never mentions the guard, and adding cases (even a second identical…

- **`~` on a path rooted at a borrowed (&) parameter yields an unrelated closure-escape diagnostic** `[combo-borrows-records]`
  Scratchpad probe r3-combo-borrows-records/p3-tilde-on-borrowed-param.kp: `bad : (& p : Pair) -> UIO Unit` with `bump ~p.left` in do → E_QTT_BORROW_ESCAPE 'a closure capturing a borrowed binding escapes through the result (§12.3.2)' pointing at the call line, instead of any statement about ~ needing …

- **one-shot resumption cannot be wrapped by any standard masking/finalization combinator; diagnostic blames k overuse for a single use** `[combo-effects-resources]`
  tests/pending-import/dx-issues/oneshot-resumption-omega-combinators.kp — in a handler clause, `uninterruptible (k 5)`, `mask (\restore -> k 5)`, and `finally (k 5) fin` all fail with E_QTT_LINEAR_OVERUSE "'k' is consumed more often than its affine quantity permits" though k appears exactly once: the…

- **exists (@1 a : Type) accepted despite @0-only witness-spelling rule** `[combo-existentials-match]`
  tests/pending-import/spec-coverage/rows-packages-existentials/existential-witness-nonzero-quantity-spelling.kp — `type Bad : Type1 = exists (@1 a : Type). Option a` checks with 0 errors; Spec L17652-L17654 says only @0 is accepted. Benign today (witness elaborates as quantity-0 anyway) but silently contradict…

- **Ambiguous imported trait spelling in an instance head reported as E_INSTANCE_HEAD with no candidate listing** `[combo-traits-modules]`
  tests/pending-import/spec-coverage/traits-instances/ambiguous-imported-trait-instance-head/ — two modules each declare `trait Tag`, main wildcard-imports both and writes `instance Tag Bool`. Observed: error[E_INSTANCE_HEAD] "instance head must be a trait applied to type arguments" — misleading (it I…

- **return in expression position diagnosed as unresolved name with 'retry' auto-fix** `[combo-do-sugar]`
  do { let y = o ?: return (ioPure 0); ... } -> E_NAME_UNRESOLVED "unresolved name 'return' (not in scope)", help "did you mean 'retry'?", maybe-applicable fix replacing return with the STM retry primitive. The keyword-ness of return (§18.5 statement) is invisible in expression position and the sugges…

- **Missing-! on monadic elvis left cascades into three errors with no splice hint** `[combo-do-sugar]`
  do { let x = getOpt ?: 0 } with getOpt : UIO (Option Int) -> 3 errors: elvis operand E_TYPE_EQUALITY_MISMATCH, then E_NUMERIC_LITERAL_DOMAIN_MISMATCH trying to fit 0 to IO Void (Option Int), then E_APPLICATION_ARGUMENT_MISMATCH downstream; no hint to insert `!`. Pinned: tests/pending-import/dx-issue…

- **Splice referencing a row binder yields bogus E_NAME_UNRESOLVED with nonsense fix-it** `[combo-queries-linearity]`
  tests/pending-import/dx-issues/comprehension-bang-row-binder-unresolved-name.kp — `let ys = [ for x in [1,2,3], yield !(echoInt x) ]` inside do: reports "unresolved name 'x'", help "did you mean '%'?", auto-applicable replace-x-with-% fix. The splice was hoisted out of the comprehension past x's bin…

- **Compiler-internal gensyms leak into group-by error cascade with gensym-to-gensym fix suggestion** `[combo-queries-linearity]`
  tests/pending-import/dx-issues/group-by-wrapper-error-gensym-cascade.kp — `group by 1 { c = 1 using NoSuchWrapper } into g` emits, after the two legitimate NoSuchWrapper errors, a third: unresolved name '__x174', help "did you mean '__g171'?", fix "replace '__x174' with '__g171' [maybe-applicable]".

- **renderSyntax drops Interp fragments when rendering quoted prefixed strings** `[combo-strings-macros]`
  tests/pending-import/spec-coverage/macros-reflection/render-quoted-fstring-keeps-interpolation.kp — renderSyntax '{ f"v=${n}" } produces `"v="`; the interpolated expression vanishes entirely, violating §21.10 'faithful raw form derived from ordinary Syntax' (the quote demonstrably records the fragmen…

- **renderSyntax emits raw (unescaped) string-literal bodies that cannot parse back** `[combo-strings-macros]`
  tests/pending-import/dx-issues/render-syntax-string-literal-escaping.kp — renderSyntax '{ "a\nb\"c" } yields quote + decoded text (raw LF and raw inner double-quote) + quote; §21.10.1 SHOULD parse back under the same profile. DX pin encodes the canonical §6.3.1 re-escaped rendering.

- **break/continue/return inside suspension bodies report unresolved-name instead of a boundary diagnostic** `[combo-lazy-totality]`
  for i in 1 :: 2 :: Nil do\n let t = thunk (break) — observed: E_NAME_UNRESOLVED "unresolved name 'break'" (typo-shaped, offers no hint about the §16.2.2 closure-boundary rule); expected: E_BREAK_OUTSIDE_LOOP, matching what the compiler already emits for the analogous lambda boundary (conformance loo…

- **E_TYPE_EQUALITY_MISMATCH prints internal metavariable names ('@3') as the actual type** `[combo-unions-transport]`
  Any unrefined GADT type-variable index use: gadt-union-index-branch-widen.kp reports 'actual: @3 / expected: (| Bool | Integer | String |)' — the elaborator's numbered metavariable leaks into the user-facing message instead of the source-level name 'u' (or a note that the index was not refined).

- **List-of-union argument mismatch misdirects users to §16.1.8 transport evidence** `[combo-unions-transport]`
  tests/pending-import/dx-issues/union-list-widening-transport-misdirect.kp — passing List (| Integer | String |) where List (| Integer | String | Bool |) is expected yields E_APPLICATION_ARGUMENT_MISMATCH 'differs from the parameter type only in type indices, and no equality evidence licenses the tra…

- **handle-with-cases unusable as a parenthesized argument; declaration silently skipped** `[combo-crossmodule]`
  tests/pending-import/dx-issues/handle-expression-parenthesized-argument.kp — `let handled = runPure (deep handle State comp with\n case return x -> pure x\n case get _ k -> k 7)` yields E_RECOVERY_DECLARATION_SKIPPED "unexpected '(' at start of declaration" and drops the whole declaration; putting t…

- **Trait-qualified term-member projection (Trait.member) unsupported although spec examples and rules use it** `[combo-numerics-traits]`
  let px = FromInteger.fromInteger @Meters -> E_UNRESOLVED_MEMBER "'fromInteger' has no receiver-marked binder, so it is not eligible for method-call sugar (7.4)" + cascading E_APPLICATION_ARGUMENT_MISMATCH on @Meters; let lemma x y p = Eq.eqSound x y p -> E_UNRESOLVED_MEMBER "no member 'eqSound' on t…

- **Forgetting `do` before a two-statement body yields a remote parse error at the declaration head** `[dx-beginner-1]`
  tests/pending-import/dx-issues/missing-do-two-statement-body.kp — body `printInt 1 / printInt 2` (no do): E_RECOVERY_DECLARATION_SKIPPED "unexpected 'let' at start of declaration" at the `let main` line (4:1) + suppressed E_SIGNATURE_UNSATISFIED; nothing points at the second statement, nothing menti…

- **if missing `then` reports "unresolved name 'if'"** `[dx-beginner-1]`
  tests/pending-import/dx-issues/if-missing-then-unresolved-if.kp — `let r = if True 1 else 2`: soft-keyword demotion makes `if` an application head name, giving suppressed E_NAME_UNRESOLVED "unresolved name 'if' (not in scope)" under E_RECOVERY_DECLARATION_SKIPPED "unexpected 'else' at start of decla…

- **Parenthesized let missing `in` suggests replacing keyword `let` with `Set`** `[dx-beginner-1]`
  tests/pending-import/dx-issues/paren-let-missing-in-keyword-as-name.kp — `(let y = 1 <newline> y + 2)`: 3 errors, led by E_NAME_UNRESOLVED "unresolved name 'let'" with help "did you mean 'Set'?" and maybe-applicable fix "replace 'let' with 'Set'", plus E_APPLICATION_NONCALLABLE and a kind-level Type…

- **Expected/actual sides of one type-mismatch payload rendered in different naming environments (Int vs Integer)** `[dx-beginner-1]`
  tests/pending-import/dx-issues/type-mismatch-alias-rendering-consistency.kp — one-arg-short `add 1` at expected Int: payload /payload/actual = "Int -> Int" (alias kept) but /payload/expected = "Integer" (alias unfolded), no aka note, contra §3.1.8 SHOULDs (common local naming environment, preserve a…

- **Forgot-pure with compound do tail over Option produces a 3-error cascade led by unsolved Add (Option Integer)** `[dx-beginner-1]`
  tests/pending-import/dx-issues/do-tail-missing-pure-option-cascade.kp — `f : Option Int = do { let x <- Some 1; x + 1 }`: E_UNSOLVED_IMPLICIT `Add (Option Integer)`, then the real Integer-vs-Option-Integer mismatch, then E_NUMERIC_LITERAL_DOMAIN_MISMATCH on the literal. Bare-var tail correctly gives…

- **`=` instead of `==` in an if condition gives a bare Type-vs-Bool mismatch with no == repair hint** `[dx-beginner-1]`
  tests/pending-import/dx-issues/if-condition-assign-eq-hint.kp — `if x = 1 then 2 else 3`: x = 1 parses as the propositional-equality TYPE, so the only error is kappa.type.mismatch 'type mismatch' (actual Type / expected Bool); no mention of `==` in message, helps, or fixes despite §3.1.8 candidateRe…

- **kappa.name.unresolved diagnostics outside plain-identifier position carry payload {"kind":"none"} and no fix (fields, import items, aliased members, module paths, ctor patterns)** `[dx-beginner-2]`
  Pinned by the `*-typo-suggestion.kp` fixtures in tests/pending-import/spec-coverage/gates-profiles/ and tests/pending-import/spec-coverage/modules-imports/module-import-wrongcase-suggestion/. E.g. `(name = ..., age = ...).nma…

- **Every unresolved single-letter identifier suggests replacing it with the operator '%', and the maybe-applicable fix does not parse** `[dx-beginner-2]`
  `module main` + `let y = q` -> E_NAME_UNRESOLVED with help "did you mean '%'?" and fix replace 'q' with '%' [maybe-applicable]; applying it gives `let y = %` which fails with E_RECOVERY_DECLARATION_SKIPPED. Same for x, K (e.g. any typo'd single-letter qualifier). Pinned: tests/pending-import/dx-issu…

- **Unresolved constructor pattern cascades: pattern binder is left unbound and its body use produces a second unresolved-name error (with the absurd '%' suggestion)** `[dx-beginner-2]`
  `f : Option Integer -> Integer; let f o = match o case Sone x -> x case None -> 0` -> 2 errors: "unresolved constructor 'Sone'" (no suggestion of 'Some') plus "unresolved name 'x'" at the arm body suggesting '%'. The downstream error depends only on the failed ctor resolution and should be suppresse…

- **match/case/do rejected as bare function-parameter binders; whole declaration skipped with error anchored at the declaration's own 'let' (col 1)** `[dx-beginner-2]`
  `let applyM match x = x` (with signature) -> E_RECOVERY_DECLARATION_SKIPPED "unexpected 'let' at start of declaration" at line start; nothing points at 'match'. `effect` in the identical position parses fine (`let addOne effect = effect + 1` -> 0 errors), so §5.2's soft-keyword MUST is applied incon…

- **Lex error blackout: one stray character suppresses every other diagnostic in the file** `[dx-cascade]`
  module main; `bad : Int / let bad = "not an int"`; then `let mid x = x ;`; then `let after = NoSuchName`. Observed: only E_UNEXPECTED_CHARACTER(';') — the independent type mismatch ABOVE the stray char and unresolved name below are never reported (parse-stage recovery does not have this problem). Ex…

- **Unclosed-delimiter diagnostic never says where the delimiter was opened** `[dx-cascade]`
  `let broken = (1` followed by more declarations: E_EXPECTED_SYNTAX_TOKEN primary at EOF, label span ALSO at EOF ('a '(' opened earlier has no matching closing delimiter'), related [], payload kind 'none' — no span anywhere identifies the opener. Pinned: tests/pending-import/dx-issues/unclosed-paren-…

- **Unresolved import cascades: every use of names listed in the failed import re-errors** `[dx-cascade]`
  `import nosuch.mod.(thing, other)` + 3 uses => 4 errors (E_MODULE_NAME_UNRESOLVED + 3x E_NAME_UNRESOLVED at use sites, no commoning of the repeated 'thing'). Pinned: tests/pending-import/dx-issues/unresolved-import-use-site-cascade.kp

- **Instance head with unresolved trait name: misleading E_INSTANCE_HEAD plus per-call-site member cascade** `[dx-cascade]`
  `instance NoSuchTrait Pair = let render p = "hi"` + 2 calls to render => E_INSTANCE_HEAD 'instance head must be a trait applied to type arguments' (never mentions NoSuchTrait; same message as `instance Int Pair`) + E_NAME_UNRESOLVED('render') at each call site. Pinned: tests/pending-import/dx-issues…

- **Entire source-oriented warning-hygiene surface is unimplemented: unused locals/params/imports, shadowing, dead code after return/break, unreachable arms, and write-only vars are all silent** `[dx-warnings]`
  grep W_ codes in src/ shows no unused/shadow/dead-code lint (only backend-IR, unicode, termination, row-extension, macro, ownership advisories). Minimal sources all produce 0 diagnostics under `kappa check`: unused omega local/param; `let x = 1` shadowed by `let x = 2`; do-items after `return`/`brea…

- **E_QTT_LINEAR_DROP can be caused solely by a provably-dead (wildcard-shadowed) match arm, with no hint that the arm is unreachable** `[dx-warnings]`
  check: `data Flag : Type = On | Off; ok : Flag -> (1 x : Int) -> Int; let ok flag x = match flag; case _ -> x; case On -> 0` -> error E_QTT_LINEAR_DROP "'x' (linear) may be dropped" anchored on the binder, even though every runtime path consumes x exactly once; the drop only exists in the arm shadow…

- **Misleading did-you-mean fix-its for missing everyday prelude names** `[dx-prelude-ergonomics]`
  kappa check on `let lo = min 1 2` suggests "replace 'min' with 'sin' [maybe-applicable]"; `max` suggests 'map'; `reverse` suggests 'release'. Edit-distance-only suggestions steer users to semantically absurd replacements precisely where the prelude has ergonomic holes.

- **Leading UTF-8 BOM rejected as E_UNEXPECTED_CHARACTER quoting the invisible U+FEFF** `[dx-layout]`
  File whose first bytes are EF BB BF followed by `module main`: error[E_UNEXPECTED_CHARACTER]: unexpected character '\65279' — renders as an apparently-empty quoted character; the message never names the byte-order mark and the BOM is not skipped (most compilers skip it). Pinned: tests/pending-import…

- **match whose case arms dedent below the anchor (or with no cases at all) reports E_NAME_UNRESOLVED 'match' plus a fix-it renaming match to the Match constructor** `[dx-layout]`
  `let f n =` / ` match n` / `case 0 -> 1` / `case _ -> 2` (case at column 1): 3 errors, none about layout — 2x E_RECOVERY_DECLARATION_SKIPPED ("unexpected 'case' at start of declaration") + E_NAME_UNRESOLVED 'match' with help "did you mean 'Match'?" and a maybe-applicable fix replacing match with Mat…

- **Lambda backslash at end of line opens no continuation context; whole declaration skipped with an unrelated message** `[dx-layout]`
  `let f = \` / ` n -> n + 1`: E_RECOVERY_DECLARATION_SKIPPED "unexpected 'let' at start of declaration" on the lambda's own line + suppressed E_SIGNATURE_UNSATISFIED; neither mentions the lambda or layout. Contrast: `let f = \n ->` + indented body IS accepted (`->` is in the §5.4 introducer list). Pi…

- **Unsolved-implicit proof obligations render internal Core: gensym evidence binders, prefix '=', de Bruijn indices for user variables** `[dx-runtime]`
  Pinned: tests/pending-import/dx-issues/unsolved-implicit-proof-rendering.kp. `let litDiv = 10 / 0` -> error[E_UNSOLVED_IMPLICIT]: "could not resolve implicit argument of type = Bool (divDefined Integer __inst_CheckedDiv_12 10 0) True"; `let naiveDiv x y = x / y` -> same with "@1 @0" in place of the …

- **E_APPLICATION_ARGUMENT_MISMATCH carries no related origins (and payload kind none)** `[dx-consistency]`
  tests/pending-import/spec-coverage/gates-profiles/app-argument-mismatch-related-call-and-decl-sites.kp — `f : Integer -> Integer; f "hi"`: JSON shows related: [] though §3.1.1A mandates call-site + declaration/callable-type site; the same mistake via annotation (kappa.type.mismatch) does carry a r…

- **kappa.type.mismatch never includes the expected-type source origin (signature/branch two-location errors render one-location)** `[dx-consistency]`
  tests/pending-import/spec-coverage/gates-profiles/type-mismatch-related-expected-origin-signature.kp and if-branch-mismatch-related-expected-origin.kp — only a use-site related at the mismatching expression; nothing names the signature that supplied the expected type, and the expected-actual paylo…

- **Pattern-position unresolved constructor emits a bare diagnostic record (no related origins, no name payload)** `[dx-consistency]`
  tests/pending-import/spec-coverage/gates-profiles/unresolved-ctor-pattern-use-site-payload.kp — `case Rd ->` in a match: E_NAME_UNRESOLVED with related: [] and payload {"kind":"none"}; the same unresolved-name mistake in term/type position gets a use-site related and the name-unresolved payload.

- **Named-arg missing-field error cascades an unsuppressed generic partial-application mismatch** `[dx-consistency]`
  tests/pending-import/dx-issues/named-arg-missing-generic-mismatch-cascade.kp — `MkP { x = 1 }` produces E_NAMED_ARG_MISSING plus an independent E_TYPE_EQUALITY_MISMATCH '(y : Integer) -> P vs P' for the same root cause (SHOULD be suppressed per §3.1.10/§3.1.11); positional arity mistakes produce exa…

- **Unclosed-delimiter diagnostic lost entirely when the broken declaration is last in the file** `[robust-eof]`
  File ending `let x = (1 + 2` (with or without trailing newline): only E_RECOVERY_DECLARATION_SKIPPED "unexpected 'let' at start of declaration" (no labels/related/rootCause). Add any declaration after it and E_EXPECTED_SYNTAX_TOKEN "unclosed '(' at end of input (Spec §5.2)" appears alongside. Expect…

- **Block introducer `do` with no body reports E_NAME_UNRESOLVED 'do' instead of missing-block diagnostic** `[robust-eof]`
  `main : IO Unit` / `let main = do` then EOF -> E_NAME_UNRESOLVED "unresolved name 'do' (not in scope)". §3.1.14A lists 'missing indentation block after a block introducer' as a recoverable condition. Pin: tests/pending-import/dx-issues/do-introducer-then-eof-unresolved-do.kp (same soft-keyword-fallb…

- **Truncated `data ... =` at EOF blames its own 'data' keyword** `[robust-eof]`
  `data Foo : Type =` then EOF -> E_RECOVERY_DECLARATION_SKIPPED "unexpected 'data' at start of declaration" anchored at the (legal) head; nothing mentions the missing constructor list / expression after '='. Pin: tests/pending-import/dx-issues/data-decl-header-then-eof-misleading-skip.kp

- **Truncated `match` offers harmful maybe-applicable fix renaming the keyword to constructor 'Match'** `[robust-eof]`
  `let f n = match n` then EOF -> E_NAME_UNRESOLVED with help "did you mean 'Match'?" and fix "replace 'match' with 'Match'" [maybe-applicable]; applying the fix can never yield the intended program. Suggestion engine should suppress keyword-spelled candidates. Pin: tests/pending-import/dx-issues/matc…

- **Base-invalid trailing digit in a radix literal surfaces as an application type error** `[robust-literals]`
  let x : Integer = 0b12 -> E_APPLICATION_NONCALLABLE 'this expression is not callable / callee type: Integer' (lexed as (0b1) 2); same for 0o778. A first-digit error (0b2) already gets E_NUMERIC_LITERAL_MALFORMED 'expected binary digits'. Pin: tests/pending-import/dx-issues/radix-literal-trailing-inv…

- **Unicode scalar literal surrogate/out-of-range causes are conflated into the several-scalars message with a misleading g' suggestion** `[robust-literals]`
  let bad = '\u{D800}' (also '\uD800', '\u{110000}') -> E_UNICODE_INVALID_SCALAR_LITERAL 'must contain exactly one Unicode scalar value' + note recommending g'...', but g'\u{D800}' is equally invalid; the string path already distinguishes ('escape denotes a surrogate code point' / 'beyond U+10FFFF'). …

- **kappa.pattern.non-exhaustive diagnostics carry an empty payload (kind:none) despite §3.2.10 payload MUSTs** `[robust-scale]`
  Any non-exhaustive match, e.g. data with ctors A|B and a match covering only A; run `kappa check --json file.kp`. Observed JSON: "payload":{"kind":"none"}; the uncovered constructors appear only in a note/label string ('missing cases: ...'). §3.2.10 (L3655-L3661) says the payload MUST include scruti…


## Annoyances (15)

- **Splice in per-row comprehension clause silently hoisted to run once total (snapshot semantics)** `[combo-queries-linearity]`
  tests/pending-import/dx-issues/comprehension-bang-per-row-clause-silent-snapshot.kp — `[ for x in [1,2,3], if x > !(step r), yield x ]` accepted with no diagnostics; with a counting Ref the effect runs ONCE (counter 1 after 3 rows) and every row is filtered against the snapshot. Spec-unspecified (se…

- **Implicit obligations inside quotes solved at quotation time, not deferred to splice site** `[combo-strings-macros]`
  tests/pending-import/spec-coverage/macros-reflection/quote-defers-implicit-obligations.kp — `let mkShow e = pure '{ show ${e} }` with e : Syntax t (t rigid) fails E_UNSOLVED_IMPLICIT "Show @1" at the quote, though §21.1 defers implicit obligations to the splice site (where t = Integer solves). Blocks…

- **std.prelude missing conventional `re` and `b` prefixed-string handlers** `[combo-strings-macros]`
  tests/pending-import/spec-coverage/prelude/prelude-re-b-prefix-handlers.kp — re"[a-z]+" and b"payload" both fail E_NAME_UNRESOLVED; §6.3.4.5 (Spec L6156) and §28.1 (L33403) require std.prelude to supply f/re/b/type handlers when prefixed strings are supported.

- **`type"..."` is a built-in intrinsic that rejects all interpolation, contradicting §6.3.5 and the §6.3.4.1 example** `[combo-strings-macros]`
  tests/pending-import/spec-coverage/macros-reflection/type-prefix-interpolation.kp — `describe : type#"SizedArray #{n} Integer"# -> Nat` (same shape as spec example type#"Vec #{n} Int"#, L5998) fails E_PREFIX_HANDLER_TYPE "does not support ${…} interpolation". §6.3.5 says there is no built-in type int…

- **InterpolatedMacro Type ill-kinded — no type-producing handler (incl. the spec'd `type` signature) can be written** `[combo-strings-macros]`
  tests/pending-import/spec-coverage/macros-reflection/interpolated-macro-type-kind.kp — `instance InterpolatedMacro Type` / `myty : Elab (InterpolatedMacro Type)` fail E_APPLICATION_ARGUMENT_MISMATCH (actual Type1, expected Type). §6.3.5 declares `type : Elab (InterpolatedMacro Type)` and permits addi…

- **Parenthesized do block never parses as an expression — 'unresolved name do'** `[combo-lazy-totality]`
  let main = twice (do\n printInt 7) with twice : UIO Unit -> UIO Unit — observed: error E_NAME_UNRESOLVED "unresolved name 'do'"; expected: parses (do blocks are expressions of type m T per §18.2; §5.4 does not exclude grouped positions). Same failure for thunk (do x) and let _ <- (do ...). Notably t…

- **CLI: `kappa check <directory>` crashes with an uncaught GHC IOException instead of a usage error** `[dx-beginner-2]`
  `kappa check .` in any directory -> "kappa: Uncaught exception ...IOException: .: withBinaryFile: inappropriate type (is a directory)" with a HasCallStack backtrace; `kappa test` accepts directories, so this is a common slip.

- **Duplicated signature+definition pair reported twice as E_DUPLICATE_DECLARATION** `[dx-cascade]`
  Duplicate `f : Int -> Int / let f x = ...` pair => 2 identical E_DUPLICATE_DECLARATION errors (one per line of the pair), each with the same 'first declared here' related site. §3.1.11 lists duplicate declaration as one root cause. Pinned: tests/pending-import/dx-issues/duplicate-signature-definitio…

- **E_UNEXPECTED_CHARACTER has no diagnostic family (family: null)** `[dx-cascade]`
  `kappa check --json` on a file containing a stray ';' => diagnostic {code: E_UNEXPECTED_CHARACTER, family: null, stage: lex}; renders as `error[E_UNEXPECTED_CHARACTER]:` without the `(family)` every other diagnostic shows, and assertDiagnosticFamily cannot target it (cf. the tests/pending-import/har…

- **Nested list comprehensions check in exponential time (~2x per nesting level); depth 22 exceeds 90s** `[robust-nesting]`
  Generate xs : List Int = [ for x_i in <inner>, yield x_i ] wrapped around [1] d times; kappa check times: d=10 0.14s, d=14 0.82s, d=18 11.8s, d=22 >90s (timeout). Breadth is fine: one comprehension with 50 generator clauses is instant, so the blowup is per-nesting-level (plan/desugaring duplication)…

- **Definitional equality of an alias type against its own spelling is exponential in alias nesting depth** `[robust-nesting]`
  type P0 = Int; type P{i} = (P{i-1}, P{i-1}) up to Pn; then idP : Pn -> Pn; let idP v = v. kappa check times: n=16 0.18s, n=18 0.45s, n=20 1.6s, n=22 6.2s, n=24 24.5s (~3.5-4x per level); n=30 unreachable. Isolation: the alias declarations alone are instant, and an UNUSED (Pn -> Int) parameter is ins…

- **Inference of iterated pair-doubling applications is exponential (no DAG sharing of inferred types)** `[robust-nesting]`
  pairUp : forall a. a -> (a, a); let deep = pairUp (pairUp (... 42)) applied d times, unannotated. kappa check: d=14 0.18s, d=16 0.48s, d=18 1.96s, d=20 8.25s, d=26 killed at 120s with heavy swapping (sys 16s). With hash-consing/sharing the result type is O(d) pointers; without it the checker materia…

- **Operator-chain checking is quadratic in chain length; mixed-precedence chains ~7x worse constant** `[robust-nesting]`
  let deep : Int = <chain of n terms>. Mixed +,*,-,* pattern: n=800 0.94s, n=1600 4.41s, n=3200 19.71s (~4.5x per doubling). All-'+' chain with variable operands: 0.30s/0.75s/2.73s at the same sizes — also quadratic, smaller constant; so both fixity resolution/association and something downstream scal…

- **Whitespace-only line containing a tab makes the file uncompilable** `[robust-eof]`
  Any file with a line consisting of a single tab (e.g. printf 'module main\n\t\nx : Int\nlet x = 1\n') -> E_TAB_IN_INDENTATION at the tab-only line; a whitespace-only FILE with a tab fails identically. Blank lines carry no indentation per §5.4; Python (the cited layout model) accepts these. Pin: test…

- **Float literals silently overflow to Infinity / underflow to 0.0 with no diagnostic** `[robust-literals]`
  let huge : Double = 1e309 (-> Infinity), let tiny : Double = 1e-324 (-> 0.0), also a 500-digit integer literal at Double -> Infinity; compiles with zero warnings. Spec is silent (see spec issue), but a typo'd exponent producing runtime Infinity deserves a warning. Pin: tests/pending-import/dx-issues…
