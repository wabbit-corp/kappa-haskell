#ifndef VOXEL_RENDERER_H
#define VOXEL_RENDERER_H

#ifdef __cplusplus
extern "C" {
#endif

/* Flat conservative ABI used by the Kappa host binding. The implementation
 * owns SDL3 window/input/drawing primitives; Kappa owns the game loop,
 * player update, terrain, and visible-face generation. prefer_metal selects
 * a Metal-capable window where the platform supports it, otherwise Vulkan is
 * preferred. */
void *vc_renderer_create(int width, int height, int prefer_metal);
const char *vc_renderer_backend(void *handle);
int vc_renderer_present(void *handle, int vertex_count, int index_count, int chunk_count);
int vc_renderer_should_spawn_helper(void);
int vc_renderer_spawn_helper(void *handle, int seed);
int vc_renderer_open_window(void *handle);
int vc_renderer_poll(void *handle);
int vc_renderer_mouse_dx(void *handle);
int vc_renderer_mouse_dy(void *handle);
int vc_renderer_dt_ms(void *handle);
int vc_renderer_begin_mesh(void *handle);
int vc_renderer_push_face(void *handle, int x, int y, int z, int face_dir, int block_kind, int shade);
int vc_renderer_draw_frame(void *handle, int x_mm, int y_mm, int z_mm, int yaw_units, int pitch_units, int terrain_height, int visible_faces, int solid_blocks, int chunk_count);
int vc_renderer_run(void *handle, int seed);
int vc_renderer_destroy(void *handle);
const char *vc_renderer_last_error(void);

#ifdef __cplusplus
}
#endif

#endif /* VOXEL_RENDERER_H */
