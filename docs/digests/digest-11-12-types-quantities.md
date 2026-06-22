# Kappa Spec Digest: §11 Universes/Rows/Propositions + §12 Functions/Quantities/Borrowing (Spec.md 8704–11847)

## 1. Grammar (verbatim)

### Intrinsic compile-time types
```text
Universe : Type0
Quantity : Type0
Region   : Type0
RecRow   : Type0
VarRow   : Type0
EffRow   : Type0
Label    : Type0
EffLabel : Type0
```
Rows of different row types never unify.

### Universe syntax
- `Type0`, `Type1`, ... fixed levels; `Type u : Type (u+1)`.
- Bare `Type` — each occurrence is a fresh universe metavariable.
- `Type u` with `u : Universe` user-bound.
- `*` is sugar for `Type`.

### Suspensions (§11.2)
`Thunk : Type -> Type` (by-name), `Need : Type -> Type` (by-need, memoized, requires `Shareable A`).
Binder sugar: `(thunk x : A)` ≡ `(x : Thunk A)`; `(lazy x : A)` ≡ `(x : Need A)`; with quantity `(q thunk x : A)`.

### forall (§11.3)
```kappa
forall a. T        ==   (@0 a : Type) -> T
forall (a : S). T  ==   (@0 a : S) -> T
```
May quantify over Quantity, Region, Universe, RecRow, VarRow, EffRow, Label, EffLabel.

### Effect rows (§11.3.2)
```kappa
<[ ]>
<[label1 : E1, label2 : E2]>
<[label1 : E1, label2 : E2 | r]>
```
Labels unique within row; equality modulo permutation; open row implies `LacksEff r l`.

### Intrinsic row solver traits (§11.3.1)
```kappa
intrinsic trait ContainsRec          (r : RecRow) (l : Label) (a : Type)
intrinsic trait LacksRec             (r : RecRow) (l : Label)
intrinsic trait StableUnderRecChange (r : RecRow) (l : Label)
intrinsic trait RecTailSatisfies     (r : RecRow) (q : Quantity)
intrinsic trait ContainsVar (r : VarRow) (a : Type)
intrinsic trait LacksVar    (r : VarRow) (a : Type)
intrinsic trait ContainsEff (r : EffRow) (l : EffLabel) (e : Type)
intrinsic trait LacksEff    (r : EffRow) (l : EffLabel)
intrinsic trait SplitEff    (r : EffRow) (l : EffLabel) (e : Type) (rest : EffRow)
```

### Function types with quantities (§12.1)
Right-associative arrows. `A -> B == (_ : A) -> B`, default quantity ω.
```kappa
(0 x : A) -> B
(1 x : A) -> B
(<=1 x : A) -> B
(>=1 x : A) -> B
(ω x : A) -> B
(q x : A) -> B          -- q a variable of type Quantity
(& x : A) -> B          -- sugar for (ω & x : A) -> B
(&[ρ] x : A) -> B       -- sugar for (ω &[ρ] x : A) -> B
(1 & x : A) -> B
(q & x : A) -> B
(q &[ρ] x : A) -> B
(thunk x : A) -> B
(lazy x : A) -> B
(x : A) -> B            -- defaults to (ω x : A) -> B
```
Quantity precedes borrow marker; `& q x` invalid.

### Shared binder prefixes (§12.1.1) — VERBATIM
```text
quantity ::=
    '0'
  | '1'
  | 'ω'
  | '<=1'
  | '>=1'
  | quantityExpr

borrowMarker ::=
    '&'
  | '&' '[' regionRef ']'

binderPrefix ::=
    quantity
  | borrowMarker
  | quantity borrowMarker

explicitBinderBody ::=
    binderPrefix? ident ':' type
  | binderPrefix? '_' ':' type
  | binderPrefix? 'this' ':' type
  | binderPrefix? 'this' ident ':' type

binderName ::= ident | '_'

implicitBinderBody ::=
    '@' binderPrefix? binderName ':' type
```
Valid: `(1 & x : A)`, `(@1 & evidence : C)`. Invalid: `(& 1 x : A)`.

### Captures (§12.3.1)
```text
typeCapture ::= typeApp [ 'captures' '(' regionRef (',' regionRef)* ')' ]
typeArrow   ::= typeCapture ('->' typeArrow)?
regionRef   ::= ident
```

### Propositional equality (§11.4.1)
```kappa
data (=) (@0 a : Type) (x : a) (y : a) : Type =
    refl : x = x
```
`pathInd`, `subst` eliminators (expect terms). `pathInd base refl ⟶ base`; `subst refl v ⟶ v`. Intensional; no UIP. Equality matches needing K require `IsProp (x = y)`/`IsSet a` else `E_EQUALITY_MATCH_REQUIRES_ISSET`.

### Trait obligation arrow (§11.1.4)
`C => R` requires `IsTrait C`; elaborates to `(@_ : C) -> R`.

### Boolean-to-type coercion (§11.4.2) — exactly three positions
1. `(@x : b)` ⇒ `(@0 x : b = True)`
2. `b => T` ⇒ `(@0 _ : b = True) -> T`
3. record/tuple field with bare boolean type: `ok : id == 1` ⇒ `ok : (id == 1) = True`

## 2. Quantity semantics (§12.2)
Quantities are intervals over ℕ∞:
```text
0      ≜ [0,0]     Erased
1      ≜ [1,1]     Linear
ω      ≜ [0,∞]     Unrestricted
<=1    ≜ [0,1]     Affine
>=1    ≜ [1,∞]     Relevant
```
Satisfaction `q_cap ⊑ q_dem` iff `q_dem ⊆ q_cap` (interval containment):
```text
q_cap ⊑ q_dem |  0   1   <=1  >=1   ω
--------------+-----------------------
0             | yes no  no   no    no
1             | no  yes no   no    no
<=1           | yes yes yes  no    no
>=1           | no  yes no   yes   no
ω             | yes yes yes  yes   yes
```
Algebra: `[a,b]+[c,d]=[a+c,b+d]`; `[a,b]·[c,d]=[a·c,b·d]`; join = `[min,max]`. Sequential adds; branches join; unreachable contributes nothing. Ambient demand δ∈{0,1}: type positions δ=0, so applications under erased context are erased. Droppable: `0, <=1, ω`; NOT droppable: `1, >=1`. Wildcard `_` never discharges `1`. `QuantitySatisfies q_cap q_dem` is the solver-owned intrinsic trait; user instances rejected; deterministic; no defaulting of `?q`.

Positive lower bounds (§12.2.5): `1`/`>=1` checked per completion kind at scope exit.

## 3. Borrowing essentials (§12.3, §12.4)
- Borrowed binding tethered to root's lexical scope via fresh rigid region (skolem). `&` = fresh anonymous region; `&[s]` = explicit in-scope `s : Region`.
- `let & pat = expr` with non-place expr: insert hidden temp `let 1 __tmp = expr; let & pat = __tmp`.
- Skolem escape: value mentioning rigid ρ may not escape its scope (return, outer var, outliving structure).
- Borrow introduction: at borrow-demanding positions, compiler may insert temporary borrow of a borrowable stable place; ends when demanding context finishes.
- Stable places: root binder + record/constructor field selections. `let y = e` does NOT preserve place identity.
- Path-sensitive record borrows: borrowing `r.f` locks footprint = path + dependency closure; disjoint sibling borrows coexist; shared borrows coexist.
- `T captures (s̄)` = upper bound on hidden region environment; compile-time only; structural inference; subsumption S ⊆ S' typing rule not defeq.
- First-class: `Projector/Getter/Opener/Setter/Sinker : Type -> Type -> Type`, `BorrowView : Region -> Type -> Type`, `data Zipper whole focus replace = Zipper (focus : focus) (1 fill : replace -> whole)`.

## 4. Key inference rules
- Universe cumulativity: `u ≤ v` ⇒ `Type u` usable at `Type v`. Constraints `?u ≤ ?v`; unconstrained metavar in no exported type MAY instantiate to least level (order-independent only); else error `kappa.type.unsolved-metavariable`.
- NEVER default: kind/classifier variables, row variables (no silent `<[ ]>`), region variables, quantity variables (except grammar's omitted ⇒ ω).
- Implicit universalization (§11.3.3): identifier is lowercase-generalizable iff ordinary unquoted ident, not backtick/operator, NOT already bound, first char ASCII [a-z] (unicode-names inactive). Leading `_` ⇒ not generalizable. Header params: unannotated lowercase param gets inferred annotation, default `Type`. Free occurrences auto-generalize ONLY in: term signatures/param-result annotations of named let; trait member sigs; effect op sigs; GADT ctor sigs; instance premises/heads. Order: first left-to-right occurrence. `trait Functor f = map : (a -> b) -> f a -> f b` ⇒ `trait Functor (f : Type -> Type) = map : forall (a b : Type). ...`.
- Contextual row tails (§11.3.1A): each `r : RecRow` has hidden home prefix home(r); occurrence valid iff home(r) ⊑ occurrence prefix; explicit labels generate `LacksRec r label`; ambiguous home ⇒ `kappa.row.context-mismatch`.

## 5. Diagnostics
- `E_PROOF_RELEVANT_TRANSPORT_NOT_LOWERABLE` (kappa.equality.transport-not-lowerable)
- `E_EQUALITY_MATCH_REQUIRES_ISSET` (kappa.equality.match-requires-hlevel)
- `kappa.type.unsolved-metavariable`, `kappa.row.context-mismatch`

## 6. Skippable in v1 (reserved lanes)
§11.1.5 custom type errors; §11.5 cubical paths gate; §12.2.8-12.2.10 modal/coeffect/dependent multiplicities lanes.
