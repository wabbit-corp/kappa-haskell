# Delve design: content packs, ECS mirror, save/load, menu

This pass turns Delve from a hardcoded roguelike prototype into a data-driven native game shell.

## Goals

- Preserve every previously implemented gameplay feature.
- Move tunable content into JSON assets.
- Keep raw JSON out of gameplay systems by decoding into typed Kappa records first.
- Add an ECS-ish component surface without rewriting every mature system at once.
- Add a main menu and versioned JSON save/load.
- Keep terminal/file I/O behind `expect` facades and native Linux fragments.

## Content-pack model

`assets/delve/pack.json` is the root manifest. It points to actor, item, spawn, worldgen, systems, and lore files and carries save/rules settings.

The config loader performs this pipeline:

```text
JSON text
  -> JsonValue
  -> validated ContentPack
  -> typed gameplay helpers
  -> game state
```

The engine never pattern matches on `JsonValue`. That keeps config parsing at the boundary and makes combat, AI, inventory, generation, rendering, corruption, and save/load ordinary typed Kappa code.

The Delve JSON profile intentionally stays small: objects, arrays, UTF-8 strings, integers, booleans, and null. The parser rejects unsupported escapes and malformed files before the pack becomes a `ContentPack`.

## ECS-ish model

Delve keeps `Actor`, `Item`, `GroundItem`, and `Level` as the authoritative gameplay model for this pass. After generation/load/turn processing, `delve.ecs.sync` builds an `EcsWorld` mirror:

```text
Entity(id, blueprintId, components)
Component = PositionC | RenderC | StatsC | ActorC | ItemC | InventoryC | AIStateC | TagsC
```

The mirror uses content-pack blueprint IDs and actor tags, so future systems can query components without depending on handwritten actor lists. Rewriting all systems at once would add churn without improving the gameplay model.

## Save/load

Saves are JSON and versioned by the content pack's `SaveConfig`:

```text
format_version
pack_id
pack_version
rng
player
level
rumors
ecs summary
```

Saves store stable content IDs and enum spellings, not host handles or terminal state. Loading decodes into typed values and re-syncs the ECS mirror.

## Menu

The game boots into `MainMenu`. Menu input is separate from in-game input:

```text
n / Enter -> new game
c         -> continue saved game
q / Esc   -> quit
```

A missing or malformed save produces a typed `GameError` and returns to the menu with a message rather than corrupting the world.

## Copy style

Player-facing messages should describe the gameplay effect first. Flavor is allowed when it is concrete and non-meta; avoid jokes based on implementation details, bureaucracy, or generic sarcasm.

## Native boundary

The native shim exposes only:

```text
terminal open/close/read/write/size/seed
file read/write/exists/ensure-directory
```

`delve.terminal` and `delve.files` are portable facades. The native/Linux fragments are the only modules importing `host.native.delve_terminal.Raw`.

## Correctness notes

- Content tuning lives in JSON assets.
- Save/load is versioned and content-pack aware.
- ECS entities are derived from authoritative state, avoiding split-brain mutation.
- File I/O and terminal I/O report typed `GameError` failures.
- Config validation rejects missing required blueprints, empty spawn tables, invalid room sizes, invalid map bounds, and malformed IDs before gameplay begins.
- Existing roguelike feature code remains in ordinary Kappa modules and is not hidden behind host calls.
