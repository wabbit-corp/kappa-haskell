# Delve: a native Linux terminal roguelike in Kappa

Delve is a NetHack/ADOM-inspired terminal roguelike source tree for Kappa.

It is terminal-only, Linux-only, native-backend only. The terminal layer uses POSIX `termios` through a checked-in native shim exposed as `host.native.delve_terminal.Raw`. There is no curses dependency. Apparently one can still draw a dungeon with bytes, which is how the ancients intended us to suffer.

## Controls

```text
h j k l         cardinal movement
y u b n         diagonal movement
arrow keys      cardinal movement
.               wait
g or ,          pick up item
i               inventory
e               use first item
d               drop first item
>               descend
<               ascend
?               help
q               quit
```

## Source layout

```text
src/delve/core.kp                  game data model
src/delve/rng.kp                   deterministic RNG
src/delve/grid.kp                  map indexing and tile access
src/delve/content.kp               monsters/items/prototypes
src/delve/gen.kp                   procedural dungeon generation
src/delve/fov.kp                   visibility and remembered terrain
src/delve/combat.kp                attacks, damage, XP
src/delve/inventory.kp             pickup/drop/use inventory actions
src/delve/ai.kp                    monster turns
src/delve/input.kp                 key-to-command mapping
src/delve/render.kp                ANSI terminal renderer
src/delve/engine.kp                turn loop
src/delve/terminal.kp              expect terminal facade
src/delve/terminal.native.linux.kp native Linux terminal fragment
src/delve/main.kp                  entry point
native/delve_terminal.c            POSIX terminal shim
native/delve_terminal.h            C ABI header
bindings/delve-terminal.summary    trusted binding summary
build.kp                           native Linux target manifest
```

## Build intent

A Kappa implementation would build the `delve` target with fragment tags:

```text
native linux
```

The common file `src/delve/terminal.kp` declares the terminal API with `expect`; the selected file `src/delve/terminal.native.linux.kp` supplies the implementation for the same path-derived module. The C shim is part of the native host binding provider.

## Status

This is source-level Kappa. I could not compile it here because there is no Kappa compiler/runtime in this environment. The project is structured so that implementation-specific friction should be concentrated in:

```text
src/delve/terminal.native.linux.kp
bindings/delve-terminal.summary
native/delve_terminal.c
```

The gameplay logic is intentionally ordinary Kappa, not native bindings wearing a trench coat.
