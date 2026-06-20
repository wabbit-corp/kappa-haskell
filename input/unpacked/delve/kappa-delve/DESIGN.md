# Delve design

Delve is a native Linux terminal roguelike written as Kappa source plus one tiny POSIX terminal shim.

The split is intentional:

- `delve.terminal.kp` is the backend-neutral facade used by the game.
- `delve.terminal.native.linux.kp` satisfies that facade using `host.native.delve_terminal.Raw`.
- `native/delve_terminal.c` is the C ABI shim for termios, ANSI terminal output, key reads, and screen size.
- Everything else is pure Kappa game logic.

## Game loop

1. Open terminal in raw mode.
2. Generate dungeon from deterministic seed.
3. Render ANSI frame.
4. Read a key.
5. Convert key to command.
6. Apply player command.
7. If the command costs a turn, run hunger and monsters.
8. Repeat until `Quit`, `Dead`, or `Won`.

## Included systems

- procedural room-and-corridor dungeon generation;
- deterministic RNG;
- eight-way movement;
- doors, stairs, traps, water, lava;
- field-of-view and remembered map;
- items and inventory;
- healing and food;
- monsters with simple chase/wander AI;
- melee combat, defense, XP, leveling;
- native terminal raw mode;
- ANSI renderer;
- Kappa/native build manifest and trusted binding summary.

## Deliberate omissions

- no curses dependency;
- no tiles, UI toolkit, or graphics;
- no network;
- no real save/load yet;
- no full NetHack object-identification system;
- no ADOM-style overworld;
- no spellbook system yet.

Those are content expansions. The architectural point is already there: a turn-based terminal roguelike whose core is portable Kappa and whose deployment target is native Linux.
