# Delve: config-driven native roguelike in Kappa

Delve is a terminal-only native roguelike source tree for Kappa. The package has Linux and macOS native targets. It keeps every previously added feature: star signs, corruption, mutations, item identity/beatitude, altars, wards, companions, pilgrims, lore stones, combat tactics, targeted attacks, wounds, wands, scrolls, potions, chaos vents, corpse drops, deterministic generation, FOV, and the native terminal loop.

This pass makes Delve **content-pack driven** and **ECS-ish**:

```text
assets/delve/pack.json      content-pack manifest, save path, rules
assets/delve/worldgen.json  map size limits, rooms, feature and spawn chances
assets/delve/actors.json    actor blueprints: stats, glyphs, factions, tags, inventory
assets/delve/items.json     item blueprints: glyphs, classes, power, charges, ID defaults
assets/delve/spawns.json    weighted monster/item spawn tables by depth
assets/delve/systems.json   tactics, star signs, mutations, faith definitions
assets/delve/lore.json      lore/rumor text
```

The Kappa engine loads those JSON files through `delve.config`, validates them into a typed `ContentPack`, and then runs the game against that typed pack. Raw JSON never leaks into combat, rendering, inventory, generation, or AI.

The bundled parser implements the Delve JSON profile used by these assets: objects, arrays, UTF-8 strings, integers, booleans, and null. Unsupported escapes fail as typed `JsonError` values rather than being silently guessed.

## New runtime features

```text
main menu             new game / continue / quit
JSON save/load        versioned save file at the configured path
file facade           read/write/exists/mkdir behind expect + native Linux fragment
content packs         JSON-driven actors/items/spawns/worldgen/systems/lore
ECS mirror            Entity + Component projection synchronized from authoritative game state
resource roots        assets/ and saves/ recorded in the build manifest
```

## Controls

```text
Main menu:
  n / Enter   start new game
  c           continue saved game
  q / Esc     quit

In game:
  h j k l     cardinal movement / bump attack
  y u b n     diagonal movement / bump attack
  arrows      cardinal movement
  .           wait
  a           aimed adjacent attack
  C           cycle tactics
  g or ,      pick up item
  i           inventory
  @           character sheet
  e           use first item
  z           zap first wand
  t           throw first item at first visible hostile
  d           drop first item
  o / c       open / close nearby door
  p           pray / offer first carried corpse on altar
  E           engrave a ward on your tile
  T           talk to adjacent friendly/neutral creature
  > / <       stairs
  ?           help
  S           save and quit
  q           quit
```

## Source layout

```text
src/delve/core.kp                  shared game model, ContentPack schema, ECS types
src/delve/json.kp                  strict JSON reader/writer used by configs and saves
src/delve/config.kp                content-pack JSON loader and validator
src/delve/files.kp                 expect file facade
src/delve/files.native.linux.kp    native Linux file facade fragment
src/delve/files.native.macos.kp    native macOS file facade fragment
src/delve/ecs.kp                   entity/component mirror synchronized from game state
src/delve/save.kp                  versioned JSON save/load
src/delve/content.kp               typed content-pack lookup helpers
src/delve/gen.kp                   config-driven dungeon generation
src/delve/ai.kp                    hostile/friendly/neutral actor turns
src/delve/combat.kp                tactics-aware attacks, wounds, XP
src/delve/corruption.kp            corruption clock and mutations
src/delve/faith.kp                 altars, prayer, offerings, cleansing
src/delve/knowledge.kp             item identification and beatitude display
src/delve/tactics.kp               combat stance config lookup
src/delve/interact.kp              engraving, talking, aimed attacks
src/delve/inventory.kp             pickup/drop/use inventory actions
src/delve/input.kp                 menu/game key mapping
src/delve/render.kp                ANSI menu/map/status rendering
src/delve/engine.kp                main menu, command loop, save/load integration
src/delve/terminal.kp              expect terminal facade
src/delve/terminal.native.linux.kp native Linux terminal fragment
src/delve/terminal.native.macos.kp native macOS terminal fragment
native/delve_terminal.c            POSIX terminal + file shim
native/delve_terminal.h            C ABI header
bindings/delve-terminal.summary    trusted binding summary
build.kp                           native Linux target manifest
```

## Build intent

Build the Linux target with:

```text
kappa build --manifest examples/packages/delve --target delve-linux -o delve
```

Build the macOS arm64 target with Homebrew `bdw-gc`, `gmp`, and `pkg-config` installed:

```text
KAPPA_CC="cc $(pkg-config --cflags --libs bdw-gc gmp)" \
  kappa build --manifest examples/packages/delve --target delve-macos-arm64 -o delve
```

The release archives currently contain dynamically linked executables. Linux systems need compatible `libgc` and `libgmp` runtime libraries installed. macOS systems need Homebrew `bdw-gc` and `gmp` runtime libraries unless the binaries are rebuilt with a static or bundled dependency strategy.

The native boundary is still tiny. `terminal.kp` and `files.kp` declare backend-neutral facades with `expect`; selected `.native.*.kp` fragments satisfy them through `host.native.delve_terminal.Raw`. The build manifest records `assets` and `saves` as resource roots so JSON packs and save paths are explicit build/deployment inputs.

## Status

The macOS and Linux targets are intended to compile through the native Kappa backend. The test target prints a `DELVE TESTS: ALL PASS` sentinel; CI treats that sentinel as part of the release gate rather than trusting process exit alone.
