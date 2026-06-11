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

## Why there is no HTTP-server demo

A network demo would not be spec-honest for this implementation, and the
spec itself does not require one to exist:

* **Networking is not part of the language's normative library surface.**
  The prelude's normative minimum (§28.2) contains console output
  (`printString`, `printlnString`, `print`, `println`), refs, errors,
  collections, time, and fibers — no sockets or HTTP. The required
  standard modules (§29) are `std.atomic`, `std.supervisor`, `std.hash`,
  `std.unicode`, `std.bytes`, `std.debug`, `std.config`, and `std.build`
  — again, no networking module.
* **Network access lives behind runtime capability profiles and host
  bindings.** Per §27 (backend profiles and runtime capability profiles)
  and §26 (FFI / host bindings), anything like sockets would arrive as a
  backend-specific capability or a `host.*` binding module, and programs
  needing it are rejected when the selected backend lacks the capability
  (§2.1 / §3.2.1). This implementation is a tree-walking interpreter with
  no backend profiles, no FFI, and no fiber runtime (§18.1.4 fibers are
  unimplemented), so it has no spec-sanctioned route to expose sockets.
* **Console IO is the spec-compliant demo surface.** `printString` /
  `printlnString` are the §28.2 primitive output operations this
  implementation provides, so a console program is the largest
  end-to-end demo that stays inside the implemented, spec-backed
  surface. `todo.kp` is therefore a console program that instead goes
  deep on the language itself: data types, records, traits, Option,
  loops, typed errors, and interpolation.
