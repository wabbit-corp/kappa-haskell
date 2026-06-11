# Kappa Spec Digest: §13 Records/Variants/Existentials + §14 Traits (Spec.md 11847–14688)

## A. Union (variant) types §13.1 [CORE]
```text
unionType ::= '(|' type ('|' type)* '|)'
            | '(|' type ('|' type)* '|' rowVar '|)'
```
`Variant : VarRow -> Type`. Arms are TYPES (no tag namespace); nullary arms need singleton types (`data Missing : Type = Missing`) or `Unit`. Row equality modulo permutation + duplicate removal by MemberId; canonical order = lexicographic serialized MemberId.

Injection: `(| 42 : Int |)`, `(| "hello" |)` (inferred when unambiguous). Typing: `(| e : T |) : Variant r` if `ContainsVar r T`.
Expected-type-directed injection/widening (§13.1.3): expected `Variant r`, expr `T`, `ContainsVar r T` ⇒ insert injection; expr `Variant r₁` with `r₁ ⊆ r₂` ⇒ widening coercion (zero-cost, same tag identity). NOT ambient subtyping.

Elimination via match:
```kappa
match u
  case (| x : Int |)     -> x + 1
  case (| s |)           -> String.length s
  case (| ..rest |)      -> default rest      -- open union residual; rest : Variant r
```
```text
variantPat ::= '(|' ident ':' type '|)' | '(|' ident '|)' | '(|' '_' ':' type '|)' | '(|' '..' ident '|)'
```
Variant row polymorphism: `project : forall (r : VarRow) (a : Type). LacksVar r a => (| a | r |) -> Option a`.

Optional sugar §13.1.9: postfix `T?` = `Option T`. Binds tighter than type application: `List Int?` = `List (Option Int)`; `Int??` = `Option (Option Int)`.
```text
typeAtom; typePostfix ::= typeAtom ('?')*; typeApp ::= typePostfix typePostfix*;
typeCapture ::= typeApp ['captures' '(' regionRef (',' regionRef)* ')']; typeArrow ::= typeCapture ('->' typeArrow)?
```

## B. Records §13.2 [CORE]
Types: `(x : Int, y : Int)` closed; `(name : String | r)` open. One-field: `(x : T,)`. Zero-field closed record = Unit.
```text
recordFieldDecl ::= [ 'opaque' ] [ '@' ] binderPrefix? [ 'thunk' | 'lazy' ] ident ':' type
```
Dependent telescopes: later fields reference earlier as `this.label` (bare label when unambiguous); topo-sort canonical order for defeq; SOURCE order for runtime evaluation. Quantity default ω; opaque defaults 0.

Values: `(x = 1, y = 2)`; punning `(name, age = 33)`; one-field `(x = 1,)`. Runtime: evaluate field exprs exactly once in source order; assemble in canonical order.

Projection `rec.ℓ`: `ContainsRec r ℓ T`. Path-sensitive consumption: projecting quantity-1 field consumes only that path; siblings usable; restore via update.

Record patch §13.2.5:
```text
recordPatch ::= expr '.{' patchItem (',' patchItem)* '}'
patchItem   ::= ordinaryUpdateField | projectionUpdateField | extensionField
ordinaryUpdateField ::= updatePath '=' expr
projectionUpdateField ::= projectionSection '=' expr
extensionField ::= ident ':=' expr
updatePath ::= updatePathSegment ('.' updatePathSegment)*
updatePathSegment ::= ['@'] ident
```
NO punning in patches. Nested: `r.{ a.b = x, a.c = y }` ≡ `r.{ a = r.a.{ b = x, c = y } }`. Elaboration: scrutinee once; RHSs once in source order; reassemble as full literal in canonical order, re-typecheck against original type. `this` = evolving updated prefix. `:=` row extension: closed receiver containing ℓ ⇒ error "use update"; open receiver needs `LacksRec r ℓ`; result `(fields, ℓ : typeof e | r)`. Open-tail preservation needs `StableUnderRecChange r l` else `kappa.record.open-tail-invalidated`.

Row polymorphism §13.2.7 canonical signatures:
```kappa
forgetExtras : RecTailSatisfies r 0 => (1 rec : (name : String | r)) -> (name : String)
addAge      : LacksRec r age => (1 rec : (name : String | r)) -> (name : String, age : Int | r)
getName     : (& rec : (name : String | r)) -> String
rename      : StableUnderRecChange r name => (1 rec : (name : String | r)) -> String -> (name : String | r)
duplicateExtras : RecTailSatisfies r ω => (rec : (name : String | r)) -> ((name : String | r), (name : String | r))
```

Records as parameters §13.2.8: `let f (x : A, y : B) : R = ...` is sugar for single record arg + unpacking; type `(x : A, y : B) -> R` NOT curried.

Implicit record fields §13.2.9: `(id : Int, @ok : id > 0)`, `(a : Type, @tc : Eq a, value : a)`. `@label : T` where T is trait evidence, compile-time type, or boolean prop. Construction: omitted @ fields synthesized via implicit resolution. Binding a record auto-unpacks implicit fields into local implicit context.

Sealed packages §13.2.10 [EXOTIC]: `sealExpr ::= 'seal' expr 'as' type`. S must be closed record type; opaque members make it a signature type; seal is the only intro form. Pure, non-generative.

Existentials §13.2.11 [EXOTIC]:
```text
existsType   ::= 'exists' existsBinder+ '.' type
existsBinder ::= ident | '(' ident ':' type ')' | '(' '@0' ident ':' type ')'
sealExistsExpr ::= 'seal' 'exists' '(' witnessAssign (',' witnessAssign)* ')' '.' expr 'as' existsType
witnessAssign  ::= ident '=' expr
openExistsExpr ::= 'open' expr 'as' 'exists' '(' ident (',' ident)* ')' '.' pattern 'in' expr
```
Sugar over sealed packages; witnesses opaque 0 (erased).

## C. Traits §14 [CORE]
Headers: `trait Eq a = ...`; `trait Eq a => Ord a = ...`; `trait C1, ..., Cn => Tr args = ...`. Unannotated params default Type.
Key prelude traits (members):
```kappa
trait Equiv (a : Type) = (~=) : (& x : a) -> (& y : a) -> Bool  (+ laws equivRefl/Sym/Trans)
trait Eq (a : Type) =
    (==) : (& x : a) -> (& y : a) -> Bool
    eqSound : (& x : a) -> (& y : a) -> ((x == y) = True -> x = y)
    eqComplete : (& x : a) -> (& y : a) -> (x = y -> (x == y) = True)
    eqIsSet : IsSet a
trait Eq a => Ord (a : Type) = compare : (& x : a) -> (& y : a) -> Ordering  (+ laws)
trait Functor (f : Type -> Type) = map : forall a b. (a -> b) -> f a -> f b (+ laws)
trait Functor f => Applicative f = pure, liftA2 (+ default (<*>), laws)
trait Applicative m => Monad m = (>>=) (+ default (>>), laws)
trait Eq a => Hashable a = hashInto : (& value : a) -> (1 state : std.hash.HashState) -> std.hash.HashState
```
Helpers (free-standing, not members): `(/=)`, `(<)`, `(<=)`, `(>)`, `(>=)` via compare.
Trait = abstract evidence record family; public eliminators only (`d.(==) 1 2`); no construction/match/update by users.

Intrinsic traits §14.1.2: `IsTrait, ContainsRec, LacksRec, StableUnderRecChange, RecTailSatisfies, ContainsVar, LacksVar, ContainsEff, LacksEff, SplitEff`. Solver traits in resolution: + `IsSubsingleton, IsProp, RuntimeErased, QuantitySatisfies, IsNType`. §14.4: `IsEmpty (absurd), IsContr, IsSubsingleton (allEqual), IsProp, IsSet, IsGroupoid, IsNType, RuntimeErased`. Compiler synthesizes `IsTrait (Tr args)` for every well-formed full trait application.

Members §14.2: required `name : Type`; default `let name : Type = expr`. Member `m : τ` of `trait Tr params` introduces `m : forall params. forall us. Tr params => τ`. Associated statics: `[opaque] Name : S` with S compile-time.

Instances §14.3:
```kappa
instance Eq a => Eq (Option a) =
    (==) : Option a -> Option a -> Bool
    let (==) this that = ...
instance Iterator (List a) =
    let Item = a
    let next this = ...
```
No public/private/export on instances; visibility GLOBAL over compilation-unit module closure; orphans permitted (SHOULD warn). Local instances only via block scope.

Resolution §14.3.1: (1) local implicit context first; (2) intrinsic solver traits; (3) global instances: normalize goal & heads, collect candidates whose heads unify; (4) recursively solve premises; (5) discard failures; (6) coherence: 0 ⇒ unsolved; 1 ⇒ use; >1 ⇒ equivalent (hash-compared) ⇒ deterministic representative (module identity, provider, path, offset ordering), else incoherent error. Collection MUST NOT depend on import/iteration order.

Normalization §14.3.2: normalize transparent aliases/compile-time defs; preserve opacity. Supertraits §14.3.3: evidence provides coherent supertrait evidence; projection is local-implicit-resolution-only (Ord T does NOT create global Eq T candidate). Refinement graph must be acyclic. Instance termination §14.3.5: Paterson conditions (premise not identical to head; per-variable occurrences ≤ head; total size strictly smaller).

Deriving §14.5: `derive Eq Foo` minimal form. Phase 0: declaration-level deriving implementation-defined; portable mechanism = std.deriving.shape body macros. `derive Eq T` only if eqSound/eqComplete synthesizable. Hashable derivable when Eq-participating fields Hashable; ADTs hash ctor tag then fields.

## D. Diagnostics (families; no E_/W_ codes in §13–14)
- `kappa.record.open-tail-invalidated`
- `kappa.associated.normalization-blocked`
- `kappa.associated.member-undeclared`

## E. Core vs exotic
CORE: unions+injection+match; T?; closed records/literals/punning/projection; .{ } update with =; := extension; row polymorphism ContainsRec/LacksRec; records-as-params; trait decls/members/defaults/supertraits; instances; resolution 1–6; IsTrait synthesis; derive Eq.
EXOTIC: dependent telescopes this.label; opaque members/signatures; seal; exists; projection-section updates; StableUnderRecChange/RecTailSatisfies solving; partial consumption tracking; implicit @ fields with proofs; Hashable derivation details.
