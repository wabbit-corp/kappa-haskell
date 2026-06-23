# Concepts — read this first

This is the primer for reading the Kappa compiler **as if it were a book**. The
source files assume you already know the ideas below; this page introduces each
one in plain language with a tiny example, so the code can just *point back here*
("see CONCEPTS.md → de Bruijn levels") instead of re-explaining or — worse —
citing a spec section number as if that were an explanation.

You do **not** need to read the [language spec](Spec.md) to understand the
compiler. The spec is the legal contract; this code is one implementation of it.
Comments cite spec sections (like `§16.3.3`) so an auditor can find the rule —
treat those as footnotes, not as the explanation.

---

## How to read the compiler (a reading order)

A compiler is a pipeline: it turns **source text** into something it can check
and run. Read the files in the order the data flows through them.

```text
  source text
      │   Lexer.hs            "scanning": text → a flat list of tokens
      ▼
   tokens                     Token.hs defines what a token is
      │   Parser.hs           "parsing": tokens → a surface syntax tree (AST)
      ▼
  surface AST                 Syntax.hs defines the tree shape
      │   Resolve.hs          attach fixities, re-associate operators, scope names
      ▼
 resolved AST
      │   Check.hs            "elaboration": AST → Core, while type-checking
      ▼
   Core term                  Core.hs defines the small, explicit core calculus
      │   Eval.hs             normalize / compare core terms (used during checking)
      │   Usage.hs            check linear/affine usage (quantities)
      │   Termination.hs      check recursive definitions actually terminate
      ▼
 checked program
      │   Interp.hs           run main() with a tree-walking interpreter
      │   Backend/C.hs        …or compile to C and link a native binary
      ▼
   output
```

`Pipeline.hs` is the conductor that runs these phases in order.

**Suggested chapter-by-chapter reading order:**

| # | File | What you learn |
|---|------|----------------|
| 0 | **this file** | the vocabulary every other file assumes |
| 1 | [`Token.hs`](../src/Kappa/Token.hs) | the "alphabet" — what a token is |
| 2 | [`Parser/Monad.hs`](../src/Kappa/Parser/Monad.hs) | what a parser *is*, mechanically, in ~290 lines |
| 3 | [`Syntax.hs`](../src/Kappa/Syntax.hs) | the surface tree — the data dictionary for everything downstream |
| 4 | [`Lexer.hs`](../src/Kappa/Lexer.hs) | turning text into tokens (layout, indentation, strings) |
| 5 | [`Parser.hs`](../src/Kappa/Parser.hs) | turning tokens into the tree |
| 6 | [`Resolve.hs`](../src/Kappa/Resolve.hs) | resolving names and operator precedence |
| 7 | [`Core.hs`](../src/Kappa/Core.hs) + [`CoreOps.hs`](../src/Kappa/CoreOps.hs) | the small explicit core language |
| 8 | [`Eval.hs`](../src/Kappa/Eval.hs) | running core terms (normalization by evaluation) |
| 9 | [`Check.hs`](../src/Kappa/Check.hs) | the heart: bidirectional type checking + elaboration |
| 10 | [`Usage.hs`](../src/Kappa/Usage.hs) | quantitative (linear/affine) usage checking |
| 11 | [`Termination.hs`](../src/Kappa/Termination.hs) | proving recursion terminates |
| 12 | [`Interp.hs`](../src/Kappa/Interp.hs) | the runtime interpreter |
| 13 | [`Pipeline.hs`](../src/Kappa/Pipeline.hs) | how all the phases are wired together |

The best *first* file to read is `Token.hs`: it's short, nearly every
constructor has a concrete example, and it has no control flow to trip over.

---

## The core ideas

### Surface syntax vs. core
There are **two** representations of a program:

- The **surface AST** ([`Syntax.hs`](../src/Kappa/Syntax.hs), the `Expr` type)
  is what the parser builds. It's close to what you typed: sugar, operator
  chains, named arguments, `do`-blocks.
- The **core** ([`Core.hs`](../src/Kappa/Core.hs), the `Term` type) is small,
  explicit, and uniform. Sugar has been desugared, names resolved, implicit
  arguments inserted.

The type checker ([`Check.hs`](../src/Kappa/Check.hs)) does both jobs at once:
it checks types *and* **elaborates** the surface AST into a core `Term`. This
combined pass is the norm for dependently typed languages.

### Dependent types and universes
Kappa is **dependently typed**: types can mention values, and types are
themselves ordinary terms. Types live in a tower of **universes** (so the
type of a type isn't itself):

```text
  3       : Int        : Type   (= Type0)
  Int     : Type       : Type1
  Type    : Type1      : Type2   …
```

In the code a universe is `CSort n` (`Type` is `CSort 0`, `Type1` is `CSort 1`).
**Cumulativity** means anything in `Type` also fits where `Type1` is expected.

### Bidirectional type checking: `infer` vs. `check`
Instead of one "typecheck" function, there are two, which call each other. This
is **bidirectional typing**, and it's why the two big functions in `Check.hs`
are `infer` and `check`:

- `infer e` — *"I don't know the type; figure it out from `e`."* Used where the
  term tells you its type (a variable, a literal, an application).
- `check e t` — *"I expect `e` to have type `t`; verify it."* Used where the
  context already knows the type (a lambda checked against a function type, the
  body of a typed `let`).

The two trade off: `check` can handle things `infer` can't (e.g. a bare lambda),
because it gets the expected type as extra information. When `check` has no rule
for the `(term, type)` pair it falls through to `infer` (inserting any implicit
arguments) and unifies the inferred type with the expectation.

### de Bruijn indices vs. levels — *the* thing to understand
Variables are not stored by name. They're stored by **counting binders**, which
makes terms with renamed variables automatically equal. There are two ways to
count, and the codebase uses **both on purpose**:

- **de Bruijn index** (used in `Term`, e.g. `CVar 0`): count *outward* from the
  use site. `0` = the nearest enclosing binder. Good for terms, because a
  subterm's indices don't change when you wrap more binders around the outside.
- **de Bruijn level** (used in `Value`, e.g. `VRigid 0 …`): count *inward* from
  the top. `0` = the outermost binder. Good for values during evaluation,
  because a variable's level doesn't change as you push *into* more binders.

To convert one to the other you need the current depth `n`:
`index = n - 1 - level`. That single formula is the source of every
`lvl - 1 - l` you'll see in `Eval.hs`. Example, inside `\x. \y. x` (depth 2):
`x` has level `0` and index `1`; `y` has level `1` and index `0`.

### Normalization by evaluation (NbE)
To decide whether two types are equal, the checker has to **reduce** them to a
canonical form first (e.g. `(\x. x) Int` and `Int` should be considered equal).
The trick used here is **normalization by evaluation**:

```text
   Term  ──eval──▶  Value  ──quote──▶  Term (now normalized)
 (syntax)         (semantic)            (syntax again)
```

- `eval` ([`Eval.hs`](../src/Kappa/Eval.hs)) turns a `Term` into a `Value`,
  using real Haskell functions/closures to do β-reduction "for free."
- `quote` reads a `Value` back into a normalized `Term`.
- `force` pushes a value just far enough to see its head constructor (resolving
  any solved metavariables and unfolding definitions as needed).
- `convertible` compares two values for definitional equality.

`Value` is the semantic domain: it has closures, neutral terms (a neutral
head — `VRigid` / `VFlex` / `VGlobN` — applied to a **spine** of arguments,
plus stuck eliminators like `VMatchN` / `VProjN` / `VIfN`), and
fully-evaluated data.

### Definitional equality: β, δ, ι, η
Two terms are "the same" to the type checker if they reduce to the same normal
form. The reduction rules have traditional Greek names you'll see in comments:

| rule | meaning | example |
|------|---------|---------|
| **β** (beta) | apply a lambda | `(\x. x+1) 4` → `5` |
| **δ** (delta) | unfold a definition | `id` → `\x. x` |
| **ι** (iota) | run a pattern match / projection | `fst (a, b)` → `a` |
| **η** (eta) | a function/record *is* its expansion | `f` ≡ `\x. f x`; a record ≡ its fields |

### Metavariables, flex vs. rigid, unification
When the checker doesn't yet know a type (e.g. an implicit argument), it invents
a **metavariable** — a "hole" to be solved later. **Unification** is the process
of making two types equal by solving metavariables.

- **flex** (`VFlex`): a *neutral term headed by an unsolved metavariable* — it
  could still become anything once the meta is solved.
- **rigid** (`VRigid`): a *neutral term headed by a real bound variable* — it's
  stuck and can't reduce further.
- **occurs check**: refuse to solve `?m := …?m…` (a meta containing itself),
  which would create an infinite type.

### Telescopes, spines, closures
- **telescope**: a sequence of binders where each may depend on the previous,
  e.g. `(n : Nat) (xs : Vec n)`.
- **spine**: a function applied to a list of arguments, kept as a list
  (`VRigid f [arg1, arg2, …]`) so the evaluator can pattern-match on the head.
- **closure**: a not-yet-evaluated function body bundled with the environment it
  captured — lets `eval` defer going under a binder until an argument arrives.

### Quantities — quantitative type theory (linear/affine usage)
Kappa's type system tracks **how many times** each variable is used. A binder
carries a **quantity** `Q` ([`Core.hs`](../src/Kappa/Core.hs)), and
[`Usage.hs`](../src/Kappa/Usage.hs) enforces it. Read each as a usage interval
`[min..max]`:

| `Q` | interval | name | intuition |
|-----|----------|------|-----------|
| `Q0` | `0` | erased | compile-time only; gone at runtime |
| `Q1` | `1` | linear | used **exactly once** (e.g. a file handle you must close) |
| `QW` | `0..∞` | unrestricted | use freely — ordinary values |
| `QLe1` | `0..1` | affine | at most once |
| `QGe1` | `1..∞` | relevant | at least once |

This is what lets the compiler guarantee a resource is used exactly once, or
that an erased proof never costs anything at runtime.

### Totality: termination and strict positivity
Kappa wants functions to be **total** (always return, never loop forever) so
that types-as-propositions stay sound. Two checks enforce this:

- **Termination** ([`Termination.hs`](../src/Kappa/Termination.hs)): every
  recursive call must make some argument *strictly smaller* on a well-founded
  ordering. The module proves this with **size-change** analysis backed by
  lightweight arithmetic reasoning over linear forms and integer intervals.
- **Strict positivity**: a data type can't recursively refer to itself in a
  "negative" position (left of an arrow), which would let you smuggle in
  non-termination. Checked in `Check.hs`.

### Effects and the do-kernel
Effectful code (I/O, state, concurrency) is typed. `do`-blocks are kept as a
structured **do-kernel** of items (`KItem` in `Core.hs`, the `K*` constructors)
rather than being desugared away, so the interpreter can execute control flow,
loops, and abrupt exits faithfully.

### Diagnostics are part of the contract
A compile error here is not a stack trace — it's a structured record
([`Diagnostic.hs`](../src/Kappa/Diagnostic.hs)) with a stable code (e.g.
`E_TYPE_MISMATCH`), a source span, and a human message. The same record renders
as either human prose or JSON. `kappa explain CODE` prints the registry entry.

---

## Naming cheat-sheet

Once you know the conventions the terse names read fine. The prefixes are
consistent across the whole codebase:

| pattern | means | examples |
|---------|-------|----------|
| `C…` | a **core** `Term` constructor | `CVar`, `CLam`, `CPi`, `CApp` |
| `V…` | a runtime/NbE **value** | `VRigid`, `VFlex`, `VPi`, `VRecordV` |
| `K…` | a **do-kernel** item | (see `KItem` in `Core.hs`) |
| `E…` | a **surface expression** (AST) | `EVar`, `EApp`, `ELambda`, `EArrow` |
| `Tok…` | a **token** | `TokArrow`, `TokIndent` |
| `p…` | a **parser** function | `pExpr`, `pDecl`, `pParenExpr` |
| `r…` / `go…` | a **resolver** / recursion traversal worker | `rExpr`, `goElem` |
| `prel…` | a **prelude/builtin** global name (defined in `Builtins.hs`) | `prelUnit` |
| `ctx` | the typing **context** (what's in scope + its types) | |
| `sp` | a source **span** (file + start/end position) | |
| `clo` | a **closure** | |
| `lvl` | a de Bruijn **level**; `idx`/index counts the other way | |
| `q`, `qa`, `qe` | a **quantity** (`Q`) in some role | |

If you only remember two things: **`C…` = syntax, `V…` = semantics**, and
**index counts from the use site, level counts from the top.**
