#define SDL_MAIN_HANDLED
#include <SDL3/SDL_main.h>
#include <SDL3/SDL.h>

#include "voxel_renderer.h"

#include <errno.h>
#include <math.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#if defined(__APPLE__)
#include <mach-o/dyld.h>
#endif

#if !defined(_WIN32)
#include <spawn.h>
#include <sys/wait.h>
#include <unistd.h>
extern char **environ;
#endif

#define VC_INPUT_QUIT 1
#define VC_INPUT_FORWARD 2
#define VC_INPUT_BACK 4
#define VC_INPUT_LEFT 8
#define VC_INPUT_RIGHT 16
#define VC_INPUT_UP 32
#define VC_INPUT_DOWN 64
#define VC_INPUT_FAST 128
#define VC_INPUT_TURN_LEFT 256
#define VC_INPUT_TURN_RIGHT 512
#define VC_INPUT_LOOK_UP 1024
#define VC_INPUT_LOOK_DOWN 2048
#define VC_INPUT_MOUSE_LOCKED 4096

#define VC_ANGLE_UNITS 4096.0f
#define VC_PI 3.14159265358979323846f

typedef struct QueuedFace {
    int x;
    int y;
    int z;
    int face_dir;
    int block_kind;
    int shade;
} QueuedFace;

typedef struct VcRenderer {
    int width;
    int height;
    int prefer_metal;
    int frames;
    int chunks;
    int vertex_count;
    int index_count;
    int solid_blocks;
    int visible_faces;
    int terrain_height;
    int input_flags;
    int mouse_dx;
    int mouse_dy;
    int dt_ms;
    int mouse_locked;
    int requested_quit;
    int auto_frames;
    int proxy;
#if !defined(_WIN32)
    pid_t proxy_pid;
#endif
    FILE *proxy_read;
    FILE *proxy_write;
    Uint64 last_ticks;
    Uint64 last_poll_done;
    float x;
    float y;
    float z;
    float yaw;
    float pitch;
    QueuedFace *queued_faces;
    int queued_count;
    int queued_capacity;
    SDL_Window *window;
    SDL_Renderer *renderer;
    char backend[96];
} VcRenderer;

typedef struct ScreenPoint {
    float x;
    float y;
    float z;
    int ok;
} ScreenPoint;

typedef struct RenderFace {
    SDL_FPoint p[4];
    SDL_FColor color;
    float depth;
} RenderFace;

typedef struct FaceList {
    RenderFace *items;
    int count;
    int capacity;
} FaceList;

static char g_last_error[256] = "ok";
static int g_preinit_attempted = 0;
static int g_preinit_ok = 0;
static int g_preinit_width = 0;
static int g_preinit_height = 0;
static int g_preinit_prefer_metal = 0;
static SDL_Window *g_preinit_window = NULL;
static SDL_Renderer *g_preinit_renderer = NULL;
static char g_preinit_backend[96] = "";
static char g_preinit_error[256] = "ok";

static void set_error(const char *message) {
    if (!message || !message[0]) message = "unknown renderer error";
    snprintf(g_last_error, sizeof(g_last_error), "%s", message);
}

static float clampf(float lo, float hi, float v) {
    return v < lo ? lo : (v > hi ? hi : v);
}

static int clampi(int lo, int hi, int v) {
    return v < lo ? lo : (v > hi ? hi : v);
}

static float angle_units_to_rad(int units) {
    return ((float)units / VC_ANGLE_UNITS) * (2.0f * VC_PI);
}

static double perf_ms(Uint64 a, Uint64 b) {
    return ((double)(b - a) * 1000.0) / (double)SDL_GetPerformanceFrequency();
}

static int profile_enabled(void) {
    static int cached = -1;
    if (cached < 0) cached = getenv("VC_PROFILE") ? 1 : 0;
    return cached;
}

static int profile_frame_selected(int frame) {
    return profile_enabled() && (getenv("VC_PROFILE_EVERY") || frame < 12 || (frame % 60) == 0);
}

static void draw_rect(SDL_Renderer *r, float x, float y, float w, float h) {
    SDL_FRect rect = { x, y, w, h };
    SDL_RenderFillRect(r, &rect);
}

static void draw_text(SDL_Renderer *r, float x, float y, const char *text, Uint8 cr, Uint8 cg, Uint8 cb) {
    SDL_SetRenderDrawColor(r, cr, cg, cb, 255);
    SDL_RenderDebugText(r, x, y, text);
}

static void set_mouse_locked(VcRenderer *vc, int locked) {
    if (!vc || !vc->window) return;
    if (locked) {
        SDL_RaiseWindow(vc->window);
        SDL_SetWindowMouseGrab(vc->window, true);
    }
    bool ok = SDL_SetWindowRelativeMouseMode(vc->window, locked ? true : false);
    if (ok) {
        vc->mouse_locked = locked ? 1 : 0;
    }
    if (!locked || !ok) SDL_SetWindowMouseGrab(vc->window, false);
}

static void draw_crosshair(SDL_Renderer *r, int w, int h) {
    float cx = (float)w * 0.5f;
    float cy = (float)h * 0.5f;
    SDL_SetRenderDrawColor(r, 235, 242, 248, 220);
    SDL_RenderLine(r, cx - 10.0f, cy, cx - 3.0f, cy);
    SDL_RenderLine(r, cx + 3.0f, cy, cx + 10.0f, cy);
    SDL_RenderLine(r, cx, cy - 10.0f, cx, cy - 3.0f);
    SDL_RenderLine(r, cx, cy + 3.0f, cx, cy + 10.0f);
}

static void draw_hotbar(SDL_Renderer *r, int w, int h) {
    const Uint8 colors[6][3] = {
        {92, 166, 74}, {126, 86, 48}, {112, 118, 122},
        {203, 184, 112}, {52, 112, 185}, {224, 176, 64}
    };
    float slot = 42.0f;
    float start = ((float)w - slot * 6.0f) * 0.5f;
    float y = (float)h - 58.0f;
    for (int i = 0; i < 6; i++) {
        SDL_SetRenderDrawColor(r, 28, 32, 36, 230);
        draw_rect(r, start + i * slot, y, slot - 4.0f, slot - 4.0f);
        SDL_SetRenderDrawColor(r, colors[i][0], colors[i][1], colors[i][2], 255);
        draw_rect(r, start + i * slot + 8.0f, y + 8.0f, slot - 20.0f, slot - 20.0f);
    }
    SDL_SetRenderDrawColor(r, 245, 245, 235, 255);
    SDL_FRect selected = { start - 3.0f, y - 3.0f, slot + 2.0f, slot + 2.0f };
    SDL_RenderFillRect(r, &selected);
    SDL_SetRenderDrawColor(r, 92, 166, 74, 255);
    draw_rect(r, start + 8.0f, y + 8.0f, slot - 20.0f, slot - 20.0f);
}

static ScreenPoint project_point(const VcRenderer *vc, float wx, float wy, float wz, int w, int h, float focal) {
    float dx = wx - vc->x;
    float dy = wy - vc->y;
    float dz = wz - vc->z;
    float sy = sinf(vc->yaw);
    float cy = cosf(vc->yaw);
    float sp = sinf(vc->pitch);
    float cp = cosf(vc->pitch);
    float cam_x = dx * cy - dz * sy;
    float cam_z0 = dx * sy + dz * cy;
    float cam_y0 = dy;
    float cam_y = cam_y0 * cp - cam_z0 * sp;
    float cam_z = cam_y0 * sp + cam_z0 * cp;
    ScreenPoint p;
    p.z = cam_z;
    p.ok = cam_z > 0.18f;
    p.x = ((float)w * 0.5f) + (cam_x * focal / cam_z);
    p.y = ((float)h * 0.5f) - (cam_y * focal / cam_z);
    return p;
}

static int face_cmp_far_to_near(const void *a, const void *b) {
    const RenderFace *fa = (const RenderFace *)a;
    const RenderFace *fb = (const RenderFace *)b;
    if (fa->depth < fb->depth) return 1;
    if (fa->depth > fb->depth) return -1;
    return 0;
}

static void face_list_free(FaceList *faces) {
    free(faces->items);
    faces->items = NULL;
    faces->count = 0;
    faces->capacity = 0;
}

static int face_list_push(FaceList *faces, RenderFace face) {
    if (faces->count >= faces->capacity) {
        int next = faces->capacity == 0 ? 512 : faces->capacity * 2;
        RenderFace *items = (RenderFace *)realloc(faces->items, (size_t)next * sizeof(RenderFace));
        if (!items) return 0;
        faces->items = items;
        faces->capacity = next;
    }
    faces->items[faces->count++] = face;
    return 1;
}

static void add_projected_face(FaceList *faces, const VcRenderer *vc, int w, int h, float focal,
                               float x0, float y0, float z0,
                               float x1, float y1, float z1,
                               float x2, float y2, float z2,
                               float x3, float y3, float z3,
                               SDL_FColor color) {
    ScreenPoint p0 = project_point(vc, x0, y0, z0, w, h, focal);
    ScreenPoint p1 = project_point(vc, x1, y1, z1, w, h, focal);
    ScreenPoint p2 = project_point(vc, x2, y2, z2, w, h, focal);
    ScreenPoint p3 = project_point(vc, x3, y3, z3, w, h, focal);
    if (!p0.ok || !p1.ok || !p2.ok || !p3.ok) return;

    float min_x = fminf(fminf(p0.x, p1.x), fminf(p2.x, p3.x));
    float max_x = fmaxf(fmaxf(p0.x, p1.x), fmaxf(p2.x, p3.x));
    float min_y = fminf(fminf(p0.y, p1.y), fminf(p2.y, p3.y));
    float max_y = fmaxf(fmaxf(p0.y, p1.y), fmaxf(p2.y, p3.y));
    if (max_x < -80.0f || min_x > (float)w + 80.0f || max_y < -80.0f || min_y > (float)h + 80.0f) return;

    RenderFace face;
    face.p[0].x = p0.x; face.p[0].y = p0.y;
    face.p[1].x = p1.x; face.p[1].y = p1.y;
    face.p[2].x = p2.x; face.p[2].y = p2.y;
    face.p[3].x = p3.x; face.p[3].y = p3.y;
    face.color = color;
    face.depth = (p0.z + p1.z + p2.z + p3.z) * 0.25f;
    (void)face_list_push(faces, face);
}

static void draw_face(SDL_Renderer *renderer, const RenderFace *face) {
    SDL_Vertex vertices[4];
    int indices[6] = {0, 1, 2, 0, 2, 3};
    for (int i = 0; i < 4; i++) {
        vertices[i].position = face->p[i];
        vertices[i].color = face->color;
        vertices[i].tex_coord.x = 0.0f;
        vertices[i].tex_coord.y = 0.0f;
    }
    SDL_RenderGeometry(renderer, NULL, vertices, 4, indices, 6);
}

static SDL_FColor face_color(int block_kind, int shade_percent) {
    Uint8 r = 200, g = 80, b = 200;
    switch (block_kind) {
        case 1: r = 92; g = 166; b = 74; break;
        case 2: r = 126; g = 86; b = 48; break;
        case 3: r = 112; g = 118; b = 122; break;
        case 4: r = 203; g = 184; b = 112; break;
        case 5: r = 52; g = 112; b = 185; break;
        case 6: r = 120; g = 76; b = 38; break;
        case 7: r = 62; g = 138; b = 64; break;
        case 8: r = 140; g = 210; b = 232; break;
        case 9: r = 224; g = 176; b = 64; break;
        default: break;
    }
    float shade = (float)clampi(25, 140, shade_percent) / 100.0f;
    SDL_FColor out;
    out.r = clampf(0.0f, 1.0f, ((float)r * shade) / 255.0f);
    out.g = clampf(0.0f, 1.0f, ((float)g * shade) / 255.0f);
    out.b = clampf(0.0f, 1.0f, ((float)b * shade) / 255.0f);
    out.a = block_kind == 5 ? 0.88f : 1.0f;
    return out;
}

static void add_queued_face(FaceList *faces, const VcRenderer *vc, int w, int h, float focal, const QueuedFace *q) {
    float x = (float)q->x;
    float y = (float)q->y;
    float z = (float)q->z;
    SDL_FColor color = face_color(q->block_kind, q->shade);

    switch (q->face_dir) {
        case 0:
            add_projected_face(faces, vc, w, h, focal,
                               x, y + 1.0f, z,
                               x + 1.0f, y + 1.0f, z,
                               x + 1.0f, y + 1.0f, z + 1.0f,
                               x, y + 1.0f, z + 1.0f,
                               color);
            break;
        case 1:
            add_projected_face(faces, vc, w, h, focal,
                               x, y, z,
                               x + 1.0f, y, z,
                               x + 1.0f, y + 1.0f, z,
                               x, y + 1.0f, z,
                               color);
            break;
        case 2:
            add_projected_face(faces, vc, w, h, focal,
                               x + 1.0f, y, z + 1.0f,
                               x, y, z + 1.0f,
                               x, y + 1.0f, z + 1.0f,
                               x + 1.0f, y + 1.0f, z + 1.0f,
                               color);
            break;
        case 3:
            add_projected_face(faces, vc, w, h, focal,
                               x, y, z + 1.0f,
                               x, y, z,
                               x, y + 1.0f, z,
                               x, y + 1.0f, z + 1.0f,
                               color);
            break;
        case 4:
            add_projected_face(faces, vc, w, h, focal,
                               x + 1.0f, y, z,
                               x + 1.0f, y, z + 1.0f,
                               x + 1.0f, y + 1.0f, z + 1.0f,
                               x + 1.0f, y + 1.0f, z,
                               color);
            break;
        case 5:
            add_projected_face(faces, vc, w, h, focal,
                               x, y, z + 1.0f,
                               x + 1.0f, y, z + 1.0f,
                               x + 1.0f, y, z,
                               x, y, z,
                               color);
            break;
        default:
            break;
    }
}

static int ensure_queued_capacity(VcRenderer *vc, int needed) {
    if (needed <= vc->queued_capacity) return 1;
    int next = vc->queued_capacity == 0 ? 1024 : vc->queued_capacity;
    while (next < needed) next *= 2;
    QueuedFace *items = (QueuedFace *)realloc(vc->queued_faces, (size_t)next * sizeof(QueuedFace));
    if (!items) {
        set_error("out of memory growing renderer mesh queue");
        return 0;
    }
    vc->queued_faces = items;
    vc->queued_capacity = next;
    return 1;
}

static int render_scene(VcRenderer *vc) {
    Uint64 t0 = SDL_GetPerformanceCounter();
    int w = vc->width;
    int h = vc->height;
    SDL_GetCurrentRenderOutputSize(vc->renderer, &w, &h);
    if (w <= 0) w = vc->width;
    if (h <= 0) h = vc->height;

    float focal = (float)h * 0.86f;
    float horizon = ((float)h * 0.5f) + sinf(vc->pitch) * focal;
    SDL_SetRenderDrawColor(vc->renderer, 132, 185, 230, 255);
    SDL_RenderClear(vc->renderer);
    float horizon_clamped = clampf(0.0f, (float)h, horizon);
    SDL_SetRenderDrawColor(vc->renderer, 166, 211, 238, 255);
    draw_rect(vc->renderer, 0.0f, 0.0f, (float)w, horizon_clamped);
    SDL_SetRenderDrawColor(vc->renderer, 77, 116, 74, 255);
    draw_rect(vc->renderer, 0.0f, horizon_clamped, (float)w, (float)h - horizon_clamped);

    FaceList faces;
    faces.items = NULL;
    faces.count = 0;
    faces.capacity = 0;
    const float max_mesh_dist = 26.0f;
    const float max_mesh_dist2 = max_mesh_dist * max_mesh_dist;
    for (int i = 0; i < vc->queued_count; i++) {
        float qx = ((float)vc->queued_faces[i].x + 0.5f) - vc->x;
        float qz = ((float)vc->queued_faces[i].z + 0.5f) - vc->z;
        if ((qx * qx + qz * qz) > max_mesh_dist2) continue;
        add_queued_face(&faces, vc, w, h, focal, &vc->queued_faces[i]);
    }
    Uint64 t_project = SDL_GetPerformanceCounter();
    qsort(faces.items, (size_t)faces.count, sizeof(RenderFace), face_cmp_far_to_near);
    Uint64 t_sort = SDL_GetPerformanceCounter();
    for (int i = 0; i < faces.count; i++) draw_face(vc->renderer, &faces.items[i]);
    Uint64 t_draw = SDL_GetPerformanceCounter();
    int drawn_faces = faces.count;
    face_list_free(&faces);

    draw_crosshair(vc->renderer, w, h);
    draw_hotbar(vc->renderer, w, h);

    char hud[256];
    snprintf(hud, sizeof(hud), "Click captures mouse  Esc releases  Esc again quits  WASD walk  arrows look  Space/E up  Q down");
    draw_text(vc->renderer, 14.0f, 14.0f, hud, 245, 248, 245);
    snprintf(hud, sizeof(hud), "backend=%s  pos=%.1f %.1f %.1f  mesh=%d verts/%d idx  chunks=%d",
             vc->backend, vc->x, vc->y, vc->z, vc->vertex_count, vc->index_count, vc->chunks);
    draw_text(vc->renderer, 14.0f, 30.0f, hud, 224, 238, 224);
    snprintf(hud, sizeof(hud), "height=%d  kappa_faces=%d queued=%d drawn=%d mouse=%s",
             vc->terrain_height, vc->visible_faces, vc->queued_count, drawn_faces, vc->mouse_locked ? "locked" : "free");
    draw_text(vc->renderer, 14.0f, 46.0f, hud, 224, 238, 224);

    SDL_RenderPresent(vc->renderer);
    Uint64 t_present = SDL_GetPerformanceCounter();
    if (profile_frame_selected(vc->frames)) {
        fprintf(stderr,
                "VC_PROFILE frame=%d queued=%d drawn=%d project_ms=%.3f sort_ms=%.3f draw_ms=%.3f present_ms=%.3f total_ms=%.3f\n",
                vc->frames, vc->queued_count, drawn_faces,
                perf_ms(t0, t_project), perf_ms(t_project, t_sort), perf_ms(t_sort, t_draw),
                perf_ms(t_draw, t_present), perf_ms(t0, t_present));
        fflush(stderr);
    }
    return 0;
}

static int init_sdl_renderer(VcRenderer *vc) {
    SDL_SetMainReady();
    SDL_SetHint(SDL_HINT_WINDOW_ACTIVATE_WHEN_SHOWN, "1");
    SDL_SetHint(SDL_HINT_WINDOW_ACTIVATE_WHEN_RAISED, "1");
    if (!SDL_Init(SDL_INIT_VIDEO)) {
        set_error(SDL_GetError());
        return -1;
    }

    SDL_WindowFlags flags = SDL_WINDOW_RESIZABLE | (vc->prefer_metal ? SDL_WINDOW_METAL : SDL_WINDOW_VULKAN);
    vc->window = SDL_CreateWindow("Voxelcraft", vc->width, vc->height, flags);
    if (!vc->window) {
        vc->window = SDL_CreateWindow("Voxelcraft", vc->width, vc->height, SDL_WINDOW_RESIZABLE);
    }
    if (!vc->window) {
        set_error(SDL_GetError());
        SDL_Quit();
        return -2;
    }

    vc->renderer = SDL_CreateRenderer(vc->window, vc->prefer_metal ? "metal" : "vulkan");
    if (!vc->renderer) vc->renderer = SDL_CreateRenderer(vc->window, NULL);
    if (!vc->renderer) {
        set_error(SDL_GetError());
        SDL_DestroyWindow(vc->window);
        vc->window = NULL;
        SDL_Quit();
        return -3;
    }

    SDL_SetRenderVSync(vc->renderer, 1);
    SDL_ShowWindow(vc->window);
    SDL_RaiseWindow(vc->window);
    const char *name = SDL_GetRendererName(vc->renderer);
    snprintf(vc->backend, sizeof(vc->backend), "sdl3-%s", name && name[0] ? name : (vc->prefer_metal ? "metal" : "renderer"));
    vc->last_ticks = SDL_GetTicks();
    vc->dt_ms = 16;
    vc->frames = 0;
    vc->requested_quit = 0;
    const char *auto_env = getenv("VC_AUTORUN_FRAMES");
    vc->auto_frames = auto_env && auto_env[0] ? atoi(auto_env) : 0;
    set_error("ok");
    return 0;
}

static void teardown_sdl_renderer(VcRenderer *vc) {
    if (vc->mouse_locked) set_mouse_locked(vc, 0);
    if (vc->renderer) SDL_DestroyRenderer(vc->renderer);
    if (vc->window) SDL_DestroyWindow(vc->window);
    vc->renderer = NULL;
    vc->window = NULL;
    vc->mouse_locked = 0;
    SDL_Quit();
}

static int env_int(const char *name, int fallback) {
    const char *value = getenv(name);
    return value && value[0] ? atoi(value) : fallback;
}

static int current_executable_path(char *buf, size_t size) {
#if defined(__APPLE__)
    uint32_t n = (uint32_t)size;
    if (_NSGetExecutablePath(buf, &n) == 0) return 0;
    return -1;
#elif defined(__linux__)
    ssize_t n = readlink("/proc/self/exe", buf, size - 1);
    if (n > 0 && (size_t)n < size) {
        buf[n] = '\0';
        return 0;
    }
    return -1;
#else
    (void)buf;
    (void)size;
    return -1;
#endif
}

static int env_has_key(const char *entry, const char *key) {
    size_t n = strlen(key);
    return strncmp(entry, key, n) == 0 && entry[n] == '=';
}

static char *dup_text(const char *text) {
    size_t n = strlen(text) + 1;
    char *out = (char *)malloc(n);
    if (out) memcpy(out, text, n);
    return out;
}

static char *env_pair(const char *key, int value) {
    char buf[96];
    snprintf(buf, sizeof(buf), "%s=%d", key, value);
    return dup_text(buf);
}

static int helper_env_enabled(void) {
    const char *helper = getenv("VC_SDL_HELPER");
    return helper && strcmp(helper, "1") == 0;
}

static int render_helper_env_enabled(void) {
    const char *helper = getenv("VC_SDL_RENDER_HELPER");
    return helper && strcmp(helper, "1") == 0;
}

static int should_use_render_proxy(void) {
#if defined(__APPLE__)
    return !getenv("VC_DIRECT_SDL") && !render_helper_env_enabled() && !helper_env_enabled();
#else
    return 0;
#endif
}

static int proxy_write_line(VcRenderer *vc, const char *fmt, ...) {
    if (!vc || !vc->proxy_write) {
        set_error("renderer proxy is not open");
        return -1;
    }
    va_list args;
    va_start(args, fmt);
    int rc = vfprintf(vc->proxy_write, fmt, args);
    va_end(args);
    if (rc < 0 || fputc('\n', vc->proxy_write) == EOF || fflush(vc->proxy_write) == EOF) {
        set_error("failed writing to renderer proxy");
        return -1;
    }
    return 0;
}

static int proxy_read_line(VcRenderer *vc, char *buf, size_t size) {
    if (!vc || !vc->proxy_read || !fgets(buf, (int)size, vc->proxy_read)) {
        set_error("renderer proxy closed unexpectedly");
        return -1;
    }
    return 0;
}

static int proxy_poll(VcRenderer *vc) {
    char line[256];
    Uint64 t0 = SDL_GetPerformanceCounter();
    if (proxy_write_line(vc, "POLL") != 0) return VC_INPUT_QUIT;
    if (proxy_read_line(vc, line, sizeof(line)) != 0) return VC_INPUT_QUIT;
    Uint64 t1 = SDL_GetPerformanceCounter();
    int flags = VC_INPUT_QUIT;
    int dx = 0;
    int dy = 0;
    int dt = 16;
    if (sscanf(line, "I %d %d %d %d", &flags, &dx, &dy, &dt) != 4) {
        set_error("bad renderer proxy input response");
        return VC_INPUT_QUIT;
    }
    vc->input_flags = flags;
    vc->mouse_dx = dx;
    vc->mouse_dy = dy;
    vc->dt_ms = dt;
    vc->last_poll_done = t1;
    if (profile_frame_selected(vc->frames)) {
        fprintf(stderr, "VC_PROFILE_PARENT frame=%d poll_roundtrip_ms=%.3f\n", vc->frames, perf_ms(t0, t1));
        fflush(stderr);
    }
    return flags;
}

static int proxy_draw(VcRenderer *vc, int x_mm, int y_mm, int z_mm, int yaw_units, int pitch_units, int terrain_height, int visible_faces, int solid_blocks, int chunk_count) {
    char line[256];
    Uint64 t0 = SDL_GetPerformanceCounter();
    double kappa_ms = vc->last_poll_done ? perf_ms(vc->last_poll_done, t0) : 0.0;
    if (proxy_write_line(vc, "DRAW %d %d %d %d %d %d %d %d %d", x_mm, y_mm, z_mm, yaw_units, pitch_units, terrain_height, visible_faces, solid_blocks, chunk_count) != 0) return -1;
    if (proxy_read_line(vc, line, sizeof(line)) != 0) return -1;
    Uint64 t1 = SDL_GetPerformanceCounter();
    int code = -1;
    if (sscanf(line, "D %d", &code) != 1) {
        set_error("bad renderer proxy draw response");
        return -1;
    }
    if (profile_frame_selected(vc->frames)) {
        fprintf(stderr, "VC_PROFILE_PARENT frame=%d kappa_between_poll_and_draw_ms=%.3f draw_roundtrip_ms=%.3f\n", vc->frames, kappa_ms, perf_ms(t0, t1));
        fflush(stderr);
    }
    vc->frames += 1;
    return code;
}

static int spawn_render_proxy(VcRenderer *vc) {
#if defined(_WIN32)
    (void)vc;
    set_error("renderer proxy is not implemented on Windows targets");
    return -1;
#else
    char exe[4096];
    if (current_executable_path(exe, sizeof(exe)) != 0) {
        set_error("could not locate current executable for renderer proxy");
        return -1;
    }

    int to_child[2];
    int from_child[2];
    if (pipe(to_child) != 0 || pipe(from_child) != 0) {
        snprintf(g_last_error, sizeof(g_last_error), "pipe failed: %s", strerror(errno));
        return -1;
    }

    const char *owned[] = {
        "VC_SDL_RENDER_HELPER", "VC_RENDER_READ_FD", "VC_RENDER_WRITE_FD",
        "VC_WIDTH", "VC_HEIGHT", "VC_PREFER_METAL"
    };
    int base_count = 0;
    for (char **e = environ; e && *e; ++e) {
        int skip = 0;
        for (size_t i = 0; i < sizeof(owned) / sizeof(owned[0]); i++) {
            if (env_has_key(*e, owned[i])) skip = 1;
        }
        if (!skip) base_count++;
    }

    char **envp = (char **)calloc((size_t)base_count + 8, sizeof(char *));
    if (!envp) {
        set_error("out of memory building renderer proxy environment");
        close(to_child[0]); close(to_child[1]); close(from_child[0]); close(from_child[1]);
        return -1;
    }

    int out = 0;
    for (char **e = environ; e && *e; ++e) {
        int skip = 0;
        for (size_t i = 0; i < sizeof(owned) / sizeof(owned[0]); i++) {
            if (env_has_key(*e, owned[i])) skip = 1;
        }
        if (!skip) envp[out++] = *e;
    }
    envp[out++] = dup_text("VC_SDL_RENDER_HELPER=1");
    envp[out++] = env_pair("VC_RENDER_READ_FD", to_child[0]);
    envp[out++] = env_pair("VC_RENDER_WRITE_FD", from_child[1]);
    envp[out++] = env_pair("VC_WIDTH", vc->width);
    envp[out++] = env_pair("VC_HEIGHT", vc->height);
    envp[out++] = env_pair("VC_PREFER_METAL", vc->prefer_metal);
    envp[out] = NULL;

    char *argv[] = { exe, NULL };
    pid_t pid = 0;
    int rc = posix_spawn(&pid, exe, NULL, NULL, argv, envp);
    for (int i = base_count; i < out; i++) free(envp[i]);
    free(envp);
    if (rc != 0) {
        snprintf(g_last_error, sizeof(g_last_error), "posix_spawn renderer proxy failed: %s", strerror(rc));
        close(to_child[0]); close(to_child[1]); close(from_child[0]); close(from_child[1]);
        return -1;
    }

    close(to_child[0]);
    close(from_child[1]);
    vc->proxy_pid = pid;
    vc->proxy_write = fdopen(to_child[1], "w");
    vc->proxy_read = fdopen(from_child[0], "r");
    if (!vc->proxy_write || !vc->proxy_read) {
        set_error("fdopen failed for renderer proxy");
        if (vc->proxy_write) fclose(vc->proxy_write); else close(to_child[1]);
        if (vc->proxy_read) fclose(vc->proxy_read); else close(from_child[0]);
        return -1;
    }
    setvbuf(vc->proxy_write, NULL, _IOFBF, 1024 * 1024);
    setvbuf(vc->proxy_read, NULL, _IOLBF, 0);

    char line[256];
    if (proxy_read_line(vc, line, sizeof(line)) != 0) return -1;
    if (strncmp(line, "READY ", 6) == 0) {
        line[strcspn(line, "\r\n")] = '\0';
        snprintf(vc->backend, sizeof(vc->backend), "%s", line + 6);
        vc->proxy = 1;
        set_error("ok");
        return 0;
    }
    if (strncmp(line, "ERR ", 4) == 0) {
        line[strcspn(line, "\r\n")] = '\0';
        set_error(line + 4);
        return -1;
    }
    set_error("bad renderer proxy ready response");
    return -1;
#endif
}

static void close_render_proxy(VcRenderer *vc) {
    if (!vc || !vc->proxy) return;
    (void)proxy_write_line(vc, "CLOSE");
    if (vc->proxy_write) fclose(vc->proxy_write);
    if (vc->proxy_read) fclose(vc->proxy_read);
    vc->proxy_write = NULL;
    vc->proxy_read = NULL;
#if !defined(_WIN32)
    if (vc->proxy_pid > 0) {
        int status = 0;
        while (waitpid(vc->proxy_pid, &status, 0) < 0 && errno == EINTR) {}
        vc->proxy_pid = 0;
    }
#endif
    vc->proxy = 0;
}

static void render_proxy_loop(void) {
    int read_fd = env_int("VC_RENDER_READ_FD", -1);
    int write_fd = env_int("VC_RENDER_WRITE_FD", -1);
    FILE *in = read_fd >= 0 ? fdopen(read_fd, "r") : NULL;
    FILE *out = write_fd >= 0 ? fdopen(write_fd, "w") : NULL;
    if (!in || !out) exit(72);
    setvbuf(out, NULL, _IOLBF, 0);

    VcRenderer vc;
    memset(&vc, 0, sizeof(vc));
    vc.width = env_int("VC_WIDTH", 1280);
    vc.height = env_int("VC_HEIGHT", 720);
    vc.prefer_metal = env_int("VC_PREFER_METAL", 0);
    snprintf(vc.backend, sizeof(vc.backend), "sdl3-helper");
    if (init_sdl_renderer(&vc) != 0) {
        fprintf(out, "ERR %s\n", g_last_error);
        fflush(out);
        exit(70);
    }
    fprintf(out, "READY %s\n", vc.backend);
    fflush(out);

    char line[256];
    while (fgets(line, sizeof(line), in)) {
        if (strncmp(line, "POLL", 4) == 0) {
            int flags = vc_renderer_poll(&vc);
            fprintf(out, "I %d %d %d %d\n", flags, vc.mouse_dx, vc.mouse_dy, vc.dt_ms);
            fflush(out);
        } else if (strncmp(line, "BEGIN", 5) == 0) {
            (void)vc_renderer_begin_mesh(&vc);
        } else if (strncmp(line, "FACE ", 5) == 0) {
            int x, y, z, face_dir, block_kind, shade;
            if (sscanf(line, "FACE %d %d %d %d %d %d", &x, &y, &z, &face_dir, &block_kind, &shade) == 6) {
                (void)vc_renderer_push_face(&vc, x, y, z, face_dir, block_kind, shade);
            }
        } else if (strncmp(line, "DRAW ", 5) == 0) {
            int x_mm, y_mm, z_mm, yaw, pitch, terrain_height, visible_faces, solid_blocks, chunk_count;
            if (sscanf(line, "DRAW %d %d %d %d %d %d %d %d %d", &x_mm, &y_mm, &z_mm, &yaw, &pitch, &terrain_height, &visible_faces, &solid_blocks, &chunk_count) == 9) {
                int code = vc_renderer_draw_frame(&vc, x_mm, y_mm, z_mm, yaw, pitch, terrain_height, visible_faces, solid_blocks, chunk_count);
                fprintf(out, "D %d\n", code);
                fflush(out);
            } else {
                fprintf(out, "D -1\n");
                fflush(out);
            }
        } else if (strncmp(line, "CLOSE", 5) == 0) {
            break;
        }
    }

    if (vc.renderer || vc.window) teardown_sdl_renderer(&vc);
    free(vc.queued_faces);
    fclose(in);
    fclose(out);
    exit(0);
}

static void vc_helper_constructor(void) __attribute__((constructor));
static void vc_helper_constructor(void) {
    if (render_helper_env_enabled()) render_proxy_loop();
    if (!helper_env_enabled()) return;
    g_preinit_attempted = 1;
    g_preinit_width = env_int("VC_WIDTH", 1280);
    g_preinit_height = env_int("VC_HEIGHT", 720);
    g_preinit_prefer_metal = env_int("VC_PREFER_METAL", 0);
    SDL_SetMainReady();
    SDL_SetHint(SDL_HINT_WINDOW_ACTIVATE_WHEN_SHOWN, "1");
    SDL_SetHint(SDL_HINT_WINDOW_ACTIVATE_WHEN_RAISED, "1");
    if (!SDL_Init(SDL_INIT_VIDEO)) {
        snprintf(g_preinit_error, sizeof(g_preinit_error), "%s", SDL_GetError());
        return;
    }

    SDL_WindowFlags flags = SDL_WINDOW_RESIZABLE | (g_preinit_prefer_metal ? SDL_WINDOW_METAL : SDL_WINDOW_VULKAN);
    g_preinit_window = SDL_CreateWindow("Voxelcraft", g_preinit_width, g_preinit_height, flags);
    if (!g_preinit_window) {
        g_preinit_window = SDL_CreateWindow("Voxelcraft", g_preinit_width, g_preinit_height, SDL_WINDOW_RESIZABLE);
    }
    if (!g_preinit_window) {
        snprintf(g_preinit_error, sizeof(g_preinit_error), "%s", SDL_GetError());
        SDL_Quit();
        return;
    }

    g_preinit_renderer = SDL_CreateRenderer(g_preinit_window, g_preinit_prefer_metal ? "metal" : "vulkan");
    if (!g_preinit_renderer) g_preinit_renderer = SDL_CreateRenderer(g_preinit_window, NULL);
    if (!g_preinit_renderer) {
        snprintf(g_preinit_error, sizeof(g_preinit_error), "%s", SDL_GetError());
        SDL_DestroyWindow(g_preinit_window);
        g_preinit_window = NULL;
        SDL_Quit();
        return;
    }

    SDL_SetRenderVSync(g_preinit_renderer, 1);
    SDL_ShowWindow(g_preinit_window);
    SDL_RaiseWindow(g_preinit_window);
    const char *name = SDL_GetRendererName(g_preinit_renderer);
    snprintf(g_preinit_backend, sizeof(g_preinit_backend), "sdl3-%s", name && name[0] ? name : (g_preinit_prefer_metal ? "metal" : "renderer"));
    g_preinit_ok = 1;
}

void *vc_renderer_create(int width, int height, int prefer_metal) {
    VcRenderer *vc = (VcRenderer *)calloc(1, sizeof(VcRenderer));
    if (!vc) {
        set_error("out of memory allocating renderer");
        return NULL;
    }
    if (helper_env_enabled() && g_preinit_ok && g_preinit_window && g_preinit_renderer) {
        vc->width = g_preinit_width;
        vc->height = g_preinit_height;
        vc->prefer_metal = g_preinit_prefer_metal;
        vc->window = g_preinit_window;
        vc->renderer = g_preinit_renderer;
        snprintf(vc->backend, sizeof(vc->backend), "%s", g_preinit_backend);
        g_preinit_window = NULL;
        g_preinit_renderer = NULL;
        vc->last_ticks = SDL_GetTicks();
        vc->dt_ms = 16;
        const char *auto_env = getenv("VC_AUTORUN_FRAMES");
        vc->auto_frames = auto_env && auto_env[0] ? atoi(auto_env) : 0;
    } else {
        vc->width = width > 0 ? width : env_int("VC_WIDTH", 1280);
        vc->height = height > 0 ? height : env_int("VC_HEIGHT", 720);
        vc->prefer_metal = prefer_metal != 0 || env_int("VC_PREFER_METAL", 0) != 0;
        snprintf(vc->backend, sizeof(vc->backend), "%s", vc->prefer_metal ? "sdl3-metal-window" : "sdl3-vulkan-window");
    }
    vc->x = 4.5f;
    vc->z = 4.5f;
    vc->y = 10.0f;
    vc->yaw = angle_units_to_rad(424);
    vc->pitch = angle_units_to_rad(-143);
    vc->dt_ms = 16;
    set_error("ok");
    return vc;
}

const char *vc_renderer_backend(void *handle) {
    VcRenderer *vc = (VcRenderer *)handle;
    if (!vc) {
        set_error("renderer handle is null");
        return "missing";
    }
    return vc->backend;
}

int vc_renderer_present(void *handle, int vertex_count, int index_count, int chunk_count) {
    VcRenderer *vc = (VcRenderer *)handle;
    if (!vc) {
        set_error("renderer handle is null");
        return -1;
    }
    if (vertex_count < 0 || index_count < 0 || chunk_count < 0) {
        set_error("negative mesh counts are invalid");
        return -2;
    }
    vc->vertex_count = vertex_count;
    vc->index_count = index_count;
    vc->chunks = chunk_count;
    set_error("ok");
    return 0;
}

int vc_renderer_should_spawn_helper(void) {
    return 0;
}

int vc_renderer_spawn_helper(void *handle, int seed) {
    VcRenderer *vc = (VcRenderer *)handle;
    if (!vc) {
        set_error("renderer handle is null");
        return -1;
    }
#if defined(_WIN32)
    (void)seed;
    set_error("SDL helper process is not implemented on Windows targets");
    return -1;
#else
    char exe[4096];
    if (current_executable_path(exe, sizeof(exe)) != 0) {
        set_error("could not locate current executable for SDL helper");
        return -1;
    }

    const char *owned[] = {
        "VC_SDL_HELPER", "VC_WIDTH", "VC_HEIGHT", "VC_PREFER_METAL",
        "VC_SEED", "VC_VERTEX_COUNT", "VC_INDEX_COUNT", "VC_CHUNKS"
    };
    int base_count = 0;
    for (char **e = environ; e && *e; ++e) {
        int skip = 0;
        for (size_t i = 0; i < sizeof(owned) / sizeof(owned[0]); i++) {
            if (env_has_key(*e, owned[i])) skip = 1;
        }
        if (!skip) base_count++;
    }

    char **envp = (char **)calloc((size_t)base_count + 10, sizeof(char *));
    if (!envp) {
        set_error("out of memory building SDL helper environment");
        return -1;
    }

    int out = 0;
    for (char **e = environ; e && *e; ++e) {
        int skip = 0;
        for (size_t i = 0; i < sizeof(owned) / sizeof(owned[0]); i++) {
            if (env_has_key(*e, owned[i])) skip = 1;
        }
        if (!skip) envp[out++] = *e;
    }
    envp[out++] = dup_text("VC_SDL_HELPER=1");
    envp[out++] = env_pair("VC_WIDTH", vc->width);
    envp[out++] = env_pair("VC_HEIGHT", vc->height);
    envp[out++] = env_pair("VC_PREFER_METAL", vc->prefer_metal);
    envp[out++] = env_pair("VC_SEED", seed);
    envp[out++] = env_pair("VC_VERTEX_COUNT", vc->vertex_count);
    envp[out++] = env_pair("VC_INDEX_COUNT", vc->index_count);
    envp[out++] = env_pair("VC_CHUNKS", vc->chunks);
    envp[out] = NULL;

    char *argv[] = { exe, NULL };
    pid_t pid = 0;
    int rc = posix_spawn(&pid, exe, NULL, NULL, argv, envp);
    for (int i = base_count; i < out; i++) free(envp[i]);
    free(envp);
    if (rc != 0) {
        snprintf(g_last_error, sizeof(g_last_error), "posix_spawn failed: %s", strerror(rc));
        return -1;
    }

    int status = 0;
    while (waitpid(pid, &status, 0) < 0) {
        if (errno != EINTR) {
            snprintf(g_last_error, sizeof(g_last_error), "waitpid failed: %s", strerror(errno));
            return -1;
        }
    }
    if (WIFEXITED(status) && WEXITSTATUS(status) == 0) {
        set_error("ok");
        return 0;
    }
    snprintf(g_last_error, sizeof(g_last_error), "SDL helper exited with status %d", status);
    return -1;
#endif
}

int vc_renderer_open_window(void *handle) {
    VcRenderer *vc = (VcRenderer *)handle;
    if (!vc) {
        set_error("renderer handle is null");
        return -1;
    }
    if (vc->proxy) return 0;
    if (should_use_render_proxy()) return spawn_render_proxy(vc);
    if (vc->window && vc->renderer) return 0;
    if (helper_env_enabled() && g_preinit_attempted && !g_preinit_ok) {
        set_error(g_preinit_error);
        return -4;
    }
    return init_sdl_renderer(vc);
}

int vc_renderer_poll(void *handle) {
    VcRenderer *vc = (VcRenderer *)handle;
    if (vc && vc->proxy) return proxy_poll(vc);
    if (!vc || !vc->window) {
        set_error("renderer window is not open");
        return VC_INPUT_QUIT;
    }
    if (vc->requested_quit) {
        vc->input_flags = VC_INPUT_QUIT;
        return vc->input_flags;
    }

    vc->mouse_dx = 0;
    vc->mouse_dy = 0;
    SDL_Event event;
    while (SDL_PollEvent(&event)) {
        if (event.type == SDL_EVENT_QUIT) {
            vc->requested_quit = 1;
        } else if (event.type == SDL_EVENT_KEY_DOWN && event.key.scancode == SDL_SCANCODE_ESCAPE) {
            if (vc->mouse_locked) {
                set_mouse_locked(vc, 0);
            } else {
                vc->requested_quit = 1;
            }
        } else if (event.type == SDL_EVENT_MOUSE_BUTTON_DOWN && event.button.button == SDL_BUTTON_LEFT) {
            set_mouse_locked(vc, 1);
        } else if (event.type == SDL_EVENT_MOUSE_MOTION && vc->mouse_locked) {
            vc->mouse_dx += (int)event.motion.xrel;
            vc->mouse_dy += (int)event.motion.yrel;
        }
    }

    Uint64 now = SDL_GetTicks();
    Uint64 elapsed = vc->last_ticks == 0 ? 16 : now - vc->last_ticks;
    vc->last_ticks = now;
    vc->dt_ms = clampi(1, 50, (int)elapsed);

    if (vc->requested_quit) {
        vc->input_flags = VC_INPUT_QUIT;
        return vc->input_flags;
    }

    int nkeys = 0;
    const bool *keys = SDL_GetKeyboardState(&nkeys);
    int flags = 0;
#define KEY_DOWN(sc) (keys && ((int)(sc)) >= 0 && ((int)(sc)) < nkeys && keys[(int)(sc)])
    if (KEY_DOWN(SDL_SCANCODE_W)) flags |= VC_INPUT_FORWARD;
    if (KEY_DOWN(SDL_SCANCODE_S)) flags |= VC_INPUT_BACK;
    if (KEY_DOWN(SDL_SCANCODE_A)) flags |= VC_INPUT_LEFT;
    if (KEY_DOWN(SDL_SCANCODE_D)) flags |= VC_INPUT_RIGHT;
    if (KEY_DOWN(SDL_SCANCODE_SPACE) || KEY_DOWN(SDL_SCANCODE_E)) flags |= VC_INPUT_UP;
    if (KEY_DOWN(SDL_SCANCODE_Q)) flags |= VC_INPUT_DOWN;
    if (KEY_DOWN(SDL_SCANCODE_LSHIFT) || KEY_DOWN(SDL_SCANCODE_RSHIFT)) flags |= VC_INPUT_FAST;
    if (KEY_DOWN(SDL_SCANCODE_LEFT)) flags |= VC_INPUT_TURN_LEFT;
    if (KEY_DOWN(SDL_SCANCODE_RIGHT)) flags |= VC_INPUT_TURN_RIGHT;
    if (KEY_DOWN(SDL_SCANCODE_UP)) flags |= VC_INPUT_LOOK_UP;
    if (KEY_DOWN(SDL_SCANCODE_DOWN)) flags |= VC_INPUT_LOOK_DOWN;
#undef KEY_DOWN
    if (getenv("VC_AUTOWALK")) flags |= VC_INPUT_FORWARD;
    if (vc->mouse_locked) flags |= VC_INPUT_MOUSE_LOCKED;
    vc->input_flags = flags;
    return vc->input_flags;
}

int vc_renderer_mouse_dx(void *handle) {
    VcRenderer *vc = (VcRenderer *)handle;
    return vc ? vc->mouse_dx : 0;
}

int vc_renderer_mouse_dy(void *handle) {
    VcRenderer *vc = (VcRenderer *)handle;
    return vc ? vc->mouse_dy : 0;
}

int vc_renderer_dt_ms(void *handle) {
    VcRenderer *vc = (VcRenderer *)handle;
    return vc ? vc->dt_ms : 16;
}

int vc_renderer_begin_mesh(void *handle) {
    VcRenderer *vc = (VcRenderer *)handle;
    if (!vc) {
        set_error("renderer handle is null");
        return -1;
    }
    if (vc->proxy) return proxy_write_line(vc, "BEGIN");
    vc->queued_count = 0;
    set_error("ok");
    return 0;
}

int vc_renderer_push_face(void *handle, int x, int y, int z, int face_dir, int block_kind, int shade) {
    VcRenderer *vc = (VcRenderer *)handle;
    if (!vc) {
        set_error("renderer handle is null");
        return -1;
    }
    if (vc->proxy) {
        if (!vc->proxy_write || fprintf(vc->proxy_write, "FACE %d %d %d %d %d %d\n", x, y, z, face_dir, block_kind, shade) < 0) {
            set_error("failed writing face to renderer proxy");
            return -1;
        }
        return 0;
    }
    if (face_dir < 0 || face_dir > 5 || block_kind < 0 || block_kind > 9) {
        set_error("invalid Kappa face descriptor");
        return -2;
    }
    if (!ensure_queued_capacity(vc, vc->queued_count + 1)) return -3;
    QueuedFace *q = &vc->queued_faces[vc->queued_count++];
    q->x = x;
    q->y = y;
    q->z = z;
    q->face_dir = face_dir;
    q->block_kind = block_kind;
    q->shade = shade;
    return 0;
}

int vc_renderer_draw_frame(void *handle, int x_mm, int y_mm, int z_mm, int yaw_units, int pitch_units, int terrain_height, int visible_faces, int solid_blocks, int chunk_count) {
    VcRenderer *vc = (VcRenderer *)handle;
    if (vc && vc->proxy) return proxy_draw(vc, x_mm, y_mm, z_mm, yaw_units, pitch_units, terrain_height, visible_faces, solid_blocks, chunk_count);
    if (!vc || !vc->renderer) {
        set_error("renderer window is not open");
        return -1;
    }
    vc->x = (float)x_mm / 1000.0f;
    vc->y = (float)y_mm / 1000.0f;
    vc->z = (float)z_mm / 1000.0f;
    vc->yaw = angle_units_to_rad(yaw_units);
    vc->pitch = angle_units_to_rad(pitch_units);
    vc->terrain_height = terrain_height;
    vc->visible_faces = visible_faces;
    vc->solid_blocks = solid_blocks;
    vc->chunks = chunk_count;
    vc->vertex_count = visible_faces * 4;
    vc->index_count = visible_faces * 6;
    render_scene(vc);
    vc->frames += 1;
    if (vc->auto_frames > 0 && vc->frames >= vc->auto_frames) vc->requested_quit = 1;
    SDL_Delay(1);
    set_error("ok");
    return vc->requested_quit ? 1 : 0;
}

int vc_renderer_run(void *handle, int seed) {
    if (vc_renderer_should_spawn_helper()) return vc_renderer_spawn_helper(handle, seed);
    (void)handle;
    (void)seed;
    set_error("vc_renderer_run is superseded by the Kappa frame loop");
    return -1;
}

int vc_renderer_destroy(void *handle) {
    VcRenderer *vc = (VcRenderer *)handle;
    if (!vc) return 0;
    if (vc->proxy) close_render_proxy(vc);
    if (vc->renderer || vc->window) teardown_sdl_renderer(vc);
    free(vc->queued_faces);
    free(vc);
    set_error("ok");
    return 0;
}

const char *vc_renderer_last_error(void) {
    return g_last_error;
}
