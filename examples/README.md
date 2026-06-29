# Examples

Run an example directly:

```
cabal run -v0 kappa -- run examples/todo.kp
```

or run the whole directory as an Appendix-T suite (each example carries
`--!` golden directives, including an exact `assertStdout` transcript):

```
cabal run -v0 kappa -- test examples
```

## `todo.kp` — console todo-list manager

A small but complete console program (~130 lines) exercising a wide slice
of the implemented language:

| Feature | Where |
| --- | --- |
| `data` declarations | `Priority` (`Low`/`Medium`/`High`) |
| Trait instances for a user type | `instance Show Priority`, `instance Eq Priority` |
| Record types, projection, `.{ }` functional patch | `Task` alias, `renderTask`, `markDone` |
| `Option` | `markDone : String -> List Task -> Option (List Task)` |
| Lists: `::`/`Nil`, `filter`, `foldl`, `listLength` | task list construction and stats |
| `for` loops with `var` mutable state | `printTasks`, open-task count |
| `while` loops | `rule` (horizontal-rule printer) |
| Typed IO errors, `raise`, `try`/`except` | `completeOrFail`, `attempt`, `main` |
| Monadic bind `let x <- e` and `Ref` cells | `attempt`, the task store in `main` |
| String interpolation `f"… ${e} …"` | throughout |
| Tuple/constructor patterns, `match` | `weight`, `Eq Priority`, `markDone` |

## Native HTTP demos

The portable example is still `todo.kp`: it runs through the interpreter and
stays inside the spec's normative prelude surface. Networking is not part of
that portable library surface (§28.2 / §29).

Native HTTP examples live under `examples/native/http_sqlite` and
`examples/native/http_uv`. They use native manifests, backend profiles, and
host bindings, so they are examples of the native runtime/FFI surface rather
than programs that should run through plain `kappa run`.
