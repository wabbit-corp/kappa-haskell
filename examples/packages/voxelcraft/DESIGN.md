# Voxelcraft design

## Scope

This package starts a native voxel game instead of attempting to ship a full
Minecraft implementation in one step. The current core is deliberately narrow:

- one deterministic 8x16x8 terrain chunk;
- block kinds for air, terrain, water, wood/leaves, glass, and torchlight;
- a Kappa-side face mesher that counts visible cube faces and derives vertex and
  index counts;
- a Kappa-side live frame loop that polls input, updates the fixed-point
  player camera, and emits visible terrain faces near the player;
- an SDL3 native renderer facade with Vulkan and Metal-oriented package targets;
- tests that validate world generation and mesh invariants.

## Module layout

```text
src/voxelcraft/core.kp                 block, world, player, mesh data
src/voxelcraft/world.kp                deterministic chunk generation
src/voxelcraft/mesh.kp                 visible-face mesh accounting
src/voxelcraft/input.kp                native input bitmask decoded to Kappa data
src/voxelcraft/player.kp               fixed-point player/camera simulation
src/voxelcraft/game_loop.game.kp       Kappa-owned live frame loop and face emission
src/voxelcraft/renderer.game.kp        backend-neutral renderer facade
src/voxelcraft/renderer.native.*.kp    Linux Vulkan / macOS Metal overlays
src/voxelcraft/main.game.kp            native game entrypoint
native/voxel_renderer.h/.c             flat native renderer ABI
test/voxelcraft/*.test.kp              pure test executable modules
```

## Renderer boundary

The Kappa code talks to `host.native.voxel_renderer.Raw` through a small facade:
open a renderer, query its backend name, poll one input frame, begin a mesh,
push visible face descriptors, draw one frame, and close it. The C shim keeps
the ABI to `int`, `void *`, and C strings so `generateAllFromHeader` can derive
and pin the raw surface without hand-written symbol declarations.

The current native implementation is a windowed SDL3 renderer. It projects,
sorts, and draws face descriptors supplied by Kappa. On macOS the renderer runs
as a main-thread helper process because AppKit event polling cannot happen on
Kappa's worker thread; the Kappa parent still owns player updates and live mesh
generation and sends render commands over a small pipe protocol.
