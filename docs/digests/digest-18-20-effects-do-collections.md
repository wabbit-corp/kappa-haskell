# Kappa Spec Digest: §18 Effects/do/Loops, §19 Errors, §20 Collections/Comprehensions (Spec.md 18159–23844)

## do blocks (§18.2)
Monadic interface: `pure`, `(>>=)`, `(>>)`.
General desugaring:
```kappa
do
    let x <- action1
    action2
    let y <- action3 x
    finalExpr
-- =>
action1 >>= \x -> action2 >> action3 x >>= \y -> finalExpr
```
Do-items: `let bindPat <- expr` (monadic bind, irrefutable); `x <- expr` (var assign: `let __tmp <- expr; writeRef (ref x) __tmp`); `x = expr` (var assign pure: write the hidden cell selected by `ref x`); `let bindPat = expr`; `let? pat = expr [else residuePat -> failExpr]`; expression item (`expr : m a`; discarded value must be droppable); `using pat <- expr` (acquire owned resource, borrowed binding, requires `trait Releasable m a = release : (1 resource : a) -> m Unit`); `defer e`; `return e`; `break`; `continue`; loops; if-without-else; local decls (signatures, named lets, data/type/trait/scoped effect/instance/derive/import/fixity).

`let?` plain requires `Alternative m` (failure → `empty`); residue must be droppable. else-form: `match expr; case pat -> do rest; case residuePat -> failExpr` (failExpr abrupt item or `m Void` via absurd).

`break`/`continue` only in loop bodies; do not cross user-written lambda boundaries. `return e` targets nearest enclosing NAMED function (incl. `let name = \... -> body`); intervening user lambda = error (label it). `return@L e`, `break@label`, `continue@label`, `defer@label`. Labels: `label@` prefix on block constructs; lambda labels `L@\x -> body`.

Monadic splicing `!` (§18.3): `!e` runs `e` inline in expression context; only inside do; `!f x y` = `!(f x y)`. Translation left-to-right, exactly once per operand, branch-local for if/match.

if-without-else in do (§18.4): `if cond then suite` ⇒ `if cond then do suite else pure ()`. Branch is fresh do-scope.

## Loops/var (§18.6)
```kappa
while cond do
    stmts
for x in xs do
    stmts
else do            -- optional, runs iff no break
    onNoBreak
```
`cond : Bool` (implicitly lifted) or `m Bool`.
```kappa
trait MonadRef (m : Type -> Type) =
    Ref : Type -> Type
    newRef : a -> m (Ref a)
    readRef : Ref a -> m a
    writeRef : Ref a -> a -> m Unit
trait Iterator (it : Type) =
    Item : Type
    next : (1 this : it) -> Option (item : Item, rest : it)
```
`var x = e` allocates a hidden `MonadRef` cell. In ordinary value position inside the same do-lifting context, `x` denotes the current value via a generated `readRef (ref x)`; the hidden cell is selected only by `ref x`. Explicit low-level reads/writes are `readRef (ref x)` / `writeRef (ref x) v`; `readRef x` / `writeRef x v` are ill-formed for mutable binding `x`. Assignment `x = val` / `x <- mval` writes the hidden cell. For-loop without break/continue/return/else MUST accept Foldable-style traversal; otherwise Iterator protocol.

## defer (§18.7)
`defer e` schedules `e : m Unit` at do-scope exit (normal, return, error, break/continue crossing). Requires `MonadFinally m`. LIFO; all attempted; first error wins; body error is primary. Do-scopes: explicit do, while/for body, loop else, if-suite branches.

## Completion kernel (§18.8)
```text
RetCtx = [(L1 : R1), ..., (Ln : Rn)]
Completion(RetCtx, A) = Normal A | Break Label | Continue Label | Return[Li] Ri
ExitAction(m) = Deferred (m Unit) | Release[A] ((1 r : A) -> m Unit) (1 r : A)
```
Items elaborate to `m (Completion(RetCtx, A))`. `lift : m A -> m Completion`; `bindC`/`thenC` propagate abrupt unchanged. `⟦return e⟧ = pure (Return[L] e)`; `⟦break⟧ = pure (Break L)`. While loop: cond false → run else (if no Break L) → Normal (); true → iteration in fresh do-scope; `Continue L`/`Normal` → next; `Break L` → exit Normal (skip else); others propagate.

## Effects (§18.1.14–18.1.22)
```kappa
effect State (s : Type) =
    1 get : Unit -> s
    1 put : s -> Unit
```
Operation quantity: default 1 (one-shot); 0 abortive; ω/>=1 multi-shot (needs rt-multishot-effects gate). `Eff : EffRow -> Type -> Type`; `runPure : Eff <[ ]> a -> a`. Handler:
```kappa
handle label expr with
  case return x -> e_ret
  case op1 x1 ... xn k -> e1
```
`expr : Eff <[label : E | r]> a`; exactly one return clause; one clause per op; `k : (1 _ : B) -> Eff <[label : E | r]> a` (shallow). `deep handle` reinstalls: `k : (1 _ : B) -> m b`; desugars to recursive driver __go over shallow handle. Handler matching by effect-label IDENTITY.

## IO model (§18.1.1–18.1.2)
`IO : Type -> Type -> Type`; `type UIO a = IO Void a`. IO e a: normal a | typed failure e | interrupted | defect.
```kappa
data Exit e a = Success a | Failure (Cause e)
data Cause e = Fail e | Interrupt InterruptCause | Defect DefectInfo | Both .. | Then ..
```
`IO e` is Functor/Applicative/Monad/MonadError/MonadFinally/MonadResource/MonadRef.

## try/except/finally (§19)
```kappa
trait MonadFinally m = finally : forall a. m a -> m Unit -> m a
trait MonadFinally m => MonadError m =
    Error : Type
    throwError : Error -> m a
    catchError : m a -> (Error -> m a) -> m a
```
`MonadError.Error (IO e) = e`. catchError catches only Fail branch (not interrupts/defects).
```kappa
try expr
  except pat1 if guard1 -> handler1
  except pat2           -> handler2
  finally               -> finalizer
```
Coverage over E: closed type → match exhaustiveness; open variant → catch-all or `except (| ..rest |)`; abstract → catch-all required. With finally ⇒ `do { defer finalizer; try expr except ... }`. `try match expr case ... except ... finally ...` desugars to try over `do { let __tmp <- expr; match __tmp ... }`. `raise` = prelude helper ≡ throwError.

## Collections (§20.1–20.2)
`[1, 2, 3]` list; `[]`; `{|1, 2, 3|}` set; `{| |}`; `{ "a": 1 }` map; `{}` empty map.
```kappa
trait Rangeable v = Range : Type; range : (from : v) -> (to : v) -> (exclusive : Bool) -> Range
```
`a .. b` → `range a b False`; `a ..< b` → `range a b True`. Instances for Nat/Int/Integer/UnicodeScalar.

## Comprehensions (§20.3–20.8)
`[ clauses..., yield v ]`, `{| ... |}`, `{ clauses..., yield k : v }`. Parsed as comprehension iff first token after opener ∈ {yield, for, for?}. Clauses separated by newlines or commas. Clauses: `for pat in coll` (irrefutable; `for?` refutable; `for x in &coll`, `for & pat in coll` borrowed); `let pat = e` / `let? pat = e`; `if cond`; `order by [asc|desc] expr | (asc e1, desc e2, ...)` (stable sort, Ord); `skip n`/`take n` (need ordered pipeline else E_QUERY_UNORDERED_PAGING); `distinct` / `distinct by e`; `group by keyExpr { field = expr using Wrapper | field = expr } into name`; `join pat in coll on cond`; `left join pat in coll on cond into name`. Map conflict: `on conflict keep last|keep first|combine using W|combine with f` (default keep last). Carrier prefixes: `Array [ ... ]`, `Query [ ... ]`, `Map k v { ... }`.

## Diagnostics
- `E_FEATURE_BACKEND_CAPABILITY_MISSING` (kappa.feature.gated) — multi-shot op without rt-multishot-effects.
- `E_QUERY_UNORDERED_PAGING` (kappa.query.orderedness) — skip/take on unordered pipeline.
