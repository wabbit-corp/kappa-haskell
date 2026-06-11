# Kappa Spec Digest: §16 Expressions & §17 Patterns (Spec.md lines 15252–18159)

Target audience: Haskell implementor of parser + typechecker + evaluator.

## 1. GRAMMAR BLOCKS (VERBATIM)

### 1.1 Application (§16.1)
```text
postfixExpr ::=
    atom chainSuffix*

applicationArg ::=
      postfixExpr
    | '@' postfixExpr
    | namedApplicationBlock

namedApplicationBlock ::=
    '{' namedApplicationItem (',' namedApplicationItem)* [','] '}'

namedApplicationItem ::=
      ident '=' expr
    | ident

applicationExpr ::=
    postfixExpr applicationArg*
```
- Surface application is left-associative: `f x y == (f x) y`.
- Application parses BEFORE infix/prefix/postfix operators, conditional, match, lambda, `let ... in`. So `f x + y` parses `(f x) + y`. Lower-precedence args must be parenthesized: `f (x + y)`, `f (if cond then x else y)`, `f (\x -> x + 1)`.
- `applicationArg` is deliberately NOT full `expr` (would steal infix operands). Operator parser consumes `applicationExpr` operands.
- `@e` arg = explicit implicit-argument application; only discharges an implicit binder. If next expected binder is explicit, or no remaining implicit binder: ill-formed.
- `namedApplicationBlock` recognized ONLY as application argument immediately after a callee; bare `{ ... }` stays ordinary expression grammar (map literals etc.). At most one per maximal application site; if present, must be the FINAL explicit argument form.

### 1.2 Dotted chains and safe navigation (§16.1.1.2)
```text
chainExpr   ::= atom chainSuffix*
chainSuffix ::= '.'  member applicationArg*
              | '?.' safeMember applicationArg*
```
- `?.` RHS restricted to member-access forms: record/package member projection, constructor-field projection, explicit dictionary member projection, method-call sugar, receiver-projection sugar. NOT reachable via `?.`: module qualification, static member selection on a type, projection sections, record patch.
- `?.` has same precedence/associativity as `.` (tightest, left-assoc); reserved token, not user-redefinable.
- Parenthesized operator members allowed: `d.(==)`, `d.(<=)`.

### 1.3 Receiver sections (§16.1.1.1)
```kappa
(.field)                 -- \__x -> __x.field
(.field1.field2)         -- \__x -> __x.field1.field2
(.degrees)               -- \__x -> __x.degrees
(.at i)                  -- \__x -> __x.at i
(.render options)        -- \__x -> __x.render options
(.writeTo file)          -- \__x -> __x.writeTo file
```
- A parenthesized expression whose content begins with `.` is a receiver section → unary lambda over fresh binder `__x`; body resolved as dotted form on `__x`. Module qualification, static member selection, record patch, row extension NOT admitted in receiver-section body.

### 1.4 Elvis (§16.1.2)
`e ?: d` for `e : Option T`, `d : T` desugars (directly, no library helper) to:
```kappa
match e
  case Option.Some __x -> __x
  case Option.None     -> d
```
Right-associative, precedence 2 (above `|>` at 1, below comparison/arithmetic). Reserved token.

### 1.5 Short-circuit `&&` `||` (§16.1.3)
- `a && b : Bool` iff both `Bool`; same `||`. Elaborate as ordinary application of prelude terms `(&&)`/`(||)` (defined over `Thunk Bool` + expected-type-directed suspension insertion). Observable behavior MUST be:
```kappa
a && b  ≡  if a then b else False
a || b  ≡  if a then True else b
```
Right operand evaluated only when required. They remain ordinary terms, not special forms.

### 1.6 Lambdas (§16.2)
Examples:
```kappa
\ x -> x
\ x y z -> f x y z
\ x (y : Int) z -> x + y + z
\ (x : Int) -> x
\ (x : Int) (y : Int) -> x + y
\ (@t : Type) (x : t) -> x
\ (@0 t : Type) (x : t) -> x
\ (1 x : Res) -> consume x
\() -> True
exit@\ x -> x
```
Grammar:
```text
lambda  ::= [label '@'] '\' binders '->' expr
binders ::= binder+
binder  ::= ident                            -- inferred type, quantity ω
          | '_'                              -- anonymous explicit binder, inferred type, quantity ω
          | '(' ')'                          -- anonymous explicit Unit binder, quantity ω
          | '(' explicitBinderBody ')'
          | '(' suspensionBinderBody ')'
          | '(' '@' binderPrefix? binderName ':' type ')'

suspensionBinderBody ::=
    binderPrefix? 'thunk' ident ':' type
  | binderPrefix? 'thunk' '_' ':' type
  | binderPrefix? 'lazy' ident ':' type
  | binderPrefix? 'lazy' '_' ':' type
```

### 1.7 Suspension expressions (§16.2.2)
```text
thunkExpr ::= 'thunk' expr
lazyExpr  ::= 'lazy' expr
forceExpr ::= 'force' expr
```
Typing: `expr : A ⟹ thunk expr : Thunk A`; `lazy expr : Need A` (needs implicit `Shareable A` + capture restriction: every computationally relevant captured free var unrestricted & not a borrowed view); `force : Thunk A -> A` and `Need A -> A`. `thunk`/`lazy` don't evaluate at construction; `force (thunk e)` evaluates each force; `force (lazy e)` memoizes (at most once). Both are closure boundaries for `return`/`break`/`continue`.

### 1.8 Implicit parameters (§16.3)
- `@` marks implicit parameter. Call sites supply explicitly via `@e` (e.g. `f @T x`).
- Default quantity of `(@x : T)`: `0` if `T` is a compile-time type (§11.1.6.1), else `ω`. Trait evidence types (`Eq a`, `Show a`, ...) are ordinary types → default `ω`. Override: `(@0 x : T)`, `(@& x : T)`, `(@&[s] x : T)`, `(@ω x : T)`.
- Implicits are LEXICAL, not dynamic; inner rebinding shadows outer candidates.

Trait-obligation sugar (§16.3.1): `C => T` ≡ `(@_ : C) -> T` requiring `IsTrait C`. Boolean special case: `b => T` (with `b : Bool`) elaborates to `(@0 _ : b = True) -> T`. `C1 => C2 => T` ≡ `(@_ : C1) -> (@_ : C2) -> T` (right-assoc).

### 1.9 Holes (§16.3.2)
- Expression-position `_` = fresh anonymous typed hole. (In lambda-binder position `_` is a wildcard binder, NOT a hole.)
- Named hole: `?ident`
- Repeated same-named holes in one declaration/local RHS share one metavariable and MUST elaborate at definitionally equal expected types, else fail (`kappa.hole.inconsistent`). Named holes do not escape the declaration. Any hole unsolved at end of elaboration of enclosing declaration = compile error. No placeholder-abstraction sugar in v1.

### 1.10 `is` tag-test expression (§16.3.4)
```text
tagTestExpr ::= expr 'is' ctor
ctor        ::= ctorName | typeName '.' ctorName
```
- Reserved, non-associative infix; precedence same as comparison operators. `a is C is D` is a parse error. RHS is a single constructor name only. Result `Bool`. Scrutinee type head must be `data` or constructor-based builtin (e.g. `Bool`); `C` must be a constructor of that type. Dynamic: evaluate `e` once; `True` iff top-level constructor is `C`.

### 1.11 Conditionals (§16.4)
```text
ifExpr ::= 'if' expr 'then' expr ('elif' expr 'then' expr)* 'else' expr
```
- Conditions are `Bool`. No `if let` in v1. Outside `do`, final `else` required; inside `do`, `else`-less `if` allowed as sugar (§18.4). `elif c then e` ≡ `else if c then e`. All branches same type.

### 1.12 `match` (§17.1, §17.1.5)
```kappa
match expr
  case pattern1 if guard1 -> expr1
  case pattern2           -> expr2
```
```text
matchCase ::= 'case' pattern ['if' expr] '->' expr
            | 'case' 'impossible'
```
- `match` is an expression. Parser MUST accept both aligned and indented `case` clauses. All branches same type. May end with final `case impossible`.
- Branch body `impossible` (§17.1.4): `case pat -> impossible` accepted only if compiler proves case unreachable.
- `case impossible` (§17.1.5): only as FINAL case; no binders, no guard; accepted only if the uncovered remainder after preceding cases/guards is unreachable.

### 1.13 Pattern forms (§17.2.1, COMPLETE)
* Wildcard: `_`
* Binder: `x`
* Literal: numeric, string, `True`, `False`, `()`
* As-pattern: `name@pat`
* Constructor patterns: prefix `Just x`; qualified `Option.Some x`; infix constructor patterns when ctor is an operator with fixity in scope (e.g. `x :: xs`)
* Tuple patterns: `(p1, p2)`, `(p1, p2, p3)`, `(p,)` one-tuple
* Anonymous record patterns:
  ```text
  recordPat      ::= '(' recordPatField (',' recordPatField)* [',' recordPatRest] [','] ')'
                   | '(' recordPatRest [','] ')'
  recordPatField ::= ['@'] ident '=' pattern
  recordPatRest  ::= '..' | '..' ident
  ```
  At most one record-rest item, must be last. `..rest` capture requires remaining prefix extends `home(r)`, else `kappa.row.context-mismatch`.
* Active pattern applications: `RegexMatch emailRegex (user :: domain :: Nil)` — head resolves to `pattern` declaration; args before final parenthesized subpattern are ordinary terms.
* Constructor patterns with named arguments: `User { name = n, age = a }`, `User { name, age }` (punning)
* Typed patterns: `(p : T)`
* Variant patterns:
  ```text
  variantPat ::= '(|' ident ':' type '|)'
               | '(|' ident '|)'
               | '(|' '_' ':' type '|)'
               | '(|' '..' ident '|)'
  ```
* Or-patterns: `p1 | p2 | p3` — try left-to-right.

Or-pattern validity (§17.2.3): each alternative binds the SAME set of names; definitionally equal types and identical quantities across alternatives.

Scoping (§17.2.2): pattern names scope over guard, branch body. Duplicate binders in one pattern = error. Prefix pattern-application head must be a data constructor or `pattern`-declared function — never an ordinary function.

### 1.14 Active pattern declaration (§17.3.1)
```text
patternDecl ::= [public|private] 'pattern' ident binder* ':' resultType '=' expr
```
- Ordinary pure term-level function; ≥1 explicit binder; LAST explicit binder is the scrutinee; preceding explicit params are pattern arguments. Result type for pattern-head use must elaborate to: `Option T`, `Match a r`, a `data` type, or a variant type.

## 2. LAMBDA BINDER FORMS (§16.2) — EXHAUSTIVE
1. `x` — bare ident, inferred type, quantity ω.
2. `_` — wildcard binder; distinct wildcards = distinct params; NOT a hole.
3. `()` — one explicit anonymous binder of type `Unit`, quantity ω.
4. `(x : T)` — typed; `(q x : T)` — quantity-annotated (`0`, `1`, `ω`, `&`, `&[s]`, `<=1`, `>=1`).
5. `(@x : T)`, `(@q x : T)` — implicit binders.
6. Suspension binders: `(thunk x : A)`, `(lazy x : A)`, with optional quantity. `(& thunk x : A) ≜ (ω & x : Thunk A)`.
7. Receiver markers: `(this : T)`, `(this x : T)`, `(q this : T)`, `(q this x : T)`.
8. Optional leading `label@` labels lambda for `return@L`. Body: single expr or indented pure block suite (→ `block ...`).

Closure capture (§16.2.1): linear (`1`) capture contaminates closure to quantity 1; `0`-captures must not appear in computationally relevant positions; `ω` closure use requires all relevant captures `ω`.

## 3. KEY ELABORATION RULES (COMPRESSED)

### 3.1 Application-spine pipeline (§16.1.7.1)
Each maximal application site elaborated as ONE ordered spine against callee's Pi telescope, left-to-right. Per next binder:
- Implicit binder: surface `@payload` consumes it (classifier-directed: elaborate payload against demanded type; never classify by token spelling). Otherwise synthesize via implicit resolution §16.3.3.
- Explicit binder: `@e` here ill-formed; no remaining arg → partial application; else:
  0. Expected-type-directed suspension insertion (`Thunk T` → try `e : Thunk T` else insert `thunk e`; same for `Need`/`lazy`).
  1. Outermost borrow introduction for `&` binders when `e` is a borrowable place.
  2. Exact unification + quantity satisfaction.
  3. Arrow subsumption (outermost binder quantity only, contravariant).
- Equality-based transport insertion (§16.1.8) only after 0–3 fail; deterministic finite subst plans; no unbounded search.

### 3.2 Named function application (§16.1.7)
Callee must preserve named-call metadata. Elaborate in BINDER order against remaining explicit named binders. Supplied `fi = ei` → check; bare `fi` → `fi = fi`; missing → error. Result: positional application. No partial application — block supplies whole remaining explicit suffix. No defaults for ordinary functions (constructor defaults are separate).

### 3.3 Safe-navigation elaboration (§16.1.1.2)
Split chain at leftmost `?.`: prefix `P : Option T`, residual `R`; fresh `__x : T`; `body = desugar(__x R)`. If `body : Option U` → flatten; if `body : U` → wrap `Option.Some body`. Result always un-nested `Option U`. Unsolved residual type metavariable → fail `E_SAFE_NAV_GENERIC_AMBIGUOUS`; MUST NOT default.

### 3.4 Implicit resolution (§16.3.3)
Order: (1) Local implicit context, innermost→outermost (implicit binders; `let (@q x : T) =`; local bindings whose type satisfies `IsTrait`; implicit record-field projections; erased branch evidence; local instances; supertrait projections of local evidence). Imported top-level bindings NOT searched. At first level with candidates: exactly one → use; multiple without `IsTrait G` → ambiguous fail; multiple with `IsTrait G` → coherent, deterministic representative. (2) Trait evidence resolution (§14.3.1) if `IsTrait G`. (3) Boolean proposition normalization: `G = (b = True)`, `b` normalizes to `True` → `refl`. (4) Equality reflection via `Eq.eqSound`. All fail → unsolved implicit goal error.

### 3.5 Flow typing (§16.4.1–16.4.2 summary)
- `if cond` success branch gets erased `@p : cond = True`; failure `cond = False`. Condition `e is C`: success `HasCtor e ⟨C⟩` (enables field projection, unreachable-case pruning); failure `LacksCtor e ⟨C⟩`. All-but-one ruled out ⇒ derive `HasCtor` for remainder.
- `&&`/`||`/`not` recursively lowered (by resolved semantic identity, not spelling): `if a && b then t else f ≡ if a then (if b then t else f) else f`, etc.
- Stable aliases: `let x = s` introduces erased `@alias : x = s`; transports refinement evidence.
- Positive lower bounds: `>=1` variables must be demanded in every reachable branch.

## 4. EXHAUSTIVENESS / REACHABILITY (§17.1.x)
- Closed types: `match` must be exhaustive. Open/infinite domains (`Int`): require catch-all.
- GADTs: branch matching refines indices; definitional equality/index unification detects unreachable cases; MAY use inhabitance summaries (§30.2.7); `Empty` ⇒ unreachable.
- Index refinement (§17.1.2): constructor branches introduce index equalities forced by ctor declaration.
- Erased scrutinees (§17.1.3): discriminating quantity-`0` scrutinee only when constructor already forced by non-erased info.
- Boolean matches (§17.1.6): `case True` body under `@p : b = True`.
- Constructor branches (§17.1.7): branch under `@p : HasCtor s ⟨C⟩`; unguarded catch-all after unguarded ctor branches gets `LacksCtor` for each excluded ctor. GUARDED branches contribute NO negative evidence.
- Guards (§17.1.9): guard `Bool`, body under `@p : guard = True`.
- Narrowing is non-consuming (§17.1.8): scrutinee evaluation for match doesn't consume; branch consumptions joined by control flow.
- Active patterns: `Option T` partial — `Some v` matches subpattern, `None` fails. `Match a r` (`data Match a r = Hit a | Miss r`) threads residue to next case. Total active patterns (data/variant result): grouped cases with same head+args evaluate view exactly once.

## 5. DIAGNOSTIC CODES
- `E_SAFE_NAV_GENERIC_AMBIGUOUS` (family `kappa.type.mismatch`) — `?.` wrap-vs-flatten undecidable.
- `W_SAFE_NAV_REDUNDANT_RECEIVER_PRESENT` — flow facts prove receiver always `Some`.
- `E_PROOF_RELEVANT_TRANSPORT_NOT_LOWERABLE` — transport in runtime-relevant position not lowerable.
- Family `kappa.type.transport-failed` — equality transport rejected.
- Family `kappa.hole.inconsistent` — named hole with incompatible expected types.
- Family `kappa.row.context-mismatch` — `..rest` capture with non-detachable dependent tail.

## 6. PARSER PITFALLS
- Two `_` meanings: expression = hole; binder/pattern = wildcard. Multiple `@` meanings: `@e` explicit implicit arg; `name@pat` as-pattern; `label@\` labeled lambda; `(@x : T)` implicit binder; `(@p = proof,...)` implicit record-pattern field.
- `{...}` after callee = namedApplicationBlock; elsewhere = map literal.
- `(.foo ...)` = receiver section. `(p,)` one-tuple vs `(x = px,)` one-field record pattern. `?ident` = named hole.
- Reserved precedences: `.`/`?.` tightest left-assoc; `is` non-assoc at comparison level; `?:` right-assoc at 2; `|>` at 1.
