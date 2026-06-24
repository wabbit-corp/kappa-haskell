# Worker-Discovered Issues

Triage notes harvested from local Claude Code Kappa transcripts and memories.
This is not a replacement for `SPEC_COMPLIANCE.md`; it records issues that were
easy to leave stranded in worker output or memory-only notes.

## Open / under-documented

### Parser: `in if ... then ...` can orphan `else`

Status: open parser/layout bug.

Minimal repro:

```kappa
module bug_inif

f : Int -> Int
let f x =
    let y = x
    in if y > 0 then y
       else 0
```

Current behavior: the parser treats the `if` as complete after the inline
`then` branch, emits `E_IF_MISSING_ELSE` at the `if`, then reports
`E_UNEXPECTED_INDENTATION` on the `else` line.

Worker context: this broke generated Delve code in `freeSpawnPos`; the workaround
was either to drop `in` and make the `if` the block result, or to put `in` on its
own line before a normal multiline `if`.

Fix direction: make the parser keep the value `if` open across an indented
`else` in this shape, or emit a targeted diagnostic/fix-it rather than the
misleading do-statement-style `if without else` cascade.

### Parser: `effect` is not reliably usable as a soft identifier

Status: open contextual-keyword / diagnostic bug.

The lexer emits `effect` as `TokIdent`, but declaration and do-item parsing
treat unbackticked `effect` at statement start as an effect declaration keyword.
Concrete repros:

```kappa
module effect_top

effect : Int
let effect = 1
```

```kappa
module effect_do

main : UIO Unit
let main = do
    effect <- pure 1
    printlnString (showInt effect)
```

Current behavior: the top-level form reports `unexpected 'effect' at start of
declaration`; the do-bind form reports parse errors for the indented statements
and an `E_NAME_UNRESOLVED` on the enclosing `do`. Backticks work, and parameter
positions such as `let f effect = ...` currently parse, so the problem is
contextual, not lexical.

Worker context: this was discovered while editing Delve spell/effect code and
was stored only in Claude memory as "reserved `effect` misparses as unresolved
`do`."

Fix direction: make `effect` keyword recognition context-sensitive enough to
distinguish declaration syntax from ordinary binding names, or reject with a
diagnostic that points at the `effect` binder and suggests backticks/renaming.

### Parser ergonomics: leading operator continuation gives a remote error

Status: open ergonomics/diagnostic issue; may or may not be a spec violation.

Minimal repro:

```kappa
module bug_or

g : Bool -> Bool -> Bool
let g a b =
    a
    || b
```

Current behavior: `a` is accepted as the whole body, `|| b` is not treated as a
continuation, and the diagnostic appears later as `E_EXPECTED_SYNTAX_TOKEN`
against the next declaration/signature context.

Worker context: a Delve worker introduced a leading `||` in `commandActed`; the
full source check caught it, but the useful fact was only preserved in memory as
"no leading binary operators on continuation lines."

Fix direction: either support operator-led continuation lines, or add a targeted
layout diagnostic when an indented line starts with an infix operator after a
complete expression.

## Already Documented / Not New

- `kappa build --manifest --check` does not validate target source modules. This
  looked like "check missed layout errors" in a worker thread, but the build docs
  already state that `--check` stops at manifest/config evaluation; full target
  builds are the source/type/codegen gate.
- The totality/proof-search hang family is covered by
  `docs/INDEPENDENT_TOTALITY_HANG_REVIEW.md` and the
  `tests/conformance/recursion/decreases-div-*` fixtures. The older memory note
  about `divInt` in `decreases` spinning for minutes appears superseded by the
  later documented investigation and tests.
- The native runtime limitation where non-tail IO binds lower through inline
  `krun_io` is documented in `examples/packages/kappa-runtime/REVIEW.md`,
  `DESIGN.md`, and `INTEGRATION.md` as the v2 CPS-conversion work.

## Fixed Findings Worth Remembering

- A native-build termination hang was fixed by changing
  `Check.unfoldReducibleGlobal` to return the recorded core body rather than
  quoting the evaluated global value inside the fuel-bounded proof reducer.
- In the experimental `kappart2` runtime, `deliver_interrupt` had to return
  whether the fiber should keep stepping into finalizers; otherwise interruption
  could drop a fiber mid-unwind.
