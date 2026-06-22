/* delve_audio.c — self-contained chiptune synthesizer + miniaudio playback.
 *
 * Implements the conservative `delve_audio_*` ABI from delve_audio_adapter.h.
 * The synth (square / triangle / LFSR-noise + AD envelope) renders SFX and a
 * longform "Sweden"-style theme (chiptuned from 1_snowy_valley) into in-memory
 * 16-bit PCM once, at init. miniaudio provides the audio device; its callback
 * mixes active SFX voices plus the looping music track.
 *
 * miniaudio is a single vendored header (no third-party LINK dependency): on
 * Linux it runtime-loads ALSA/PulseAudio, on macOS it links system frameworks
 * (declared below via Mach-O .linker_option directives, so no -framework is
 * needed on the cc line and the build manifest stays pure). It fails SOFT when
 * there is no device — so the binary LOADS on machines with no audio hardware
 * at all; init just returns nonzero and every other call becomes a no-op.
 */

/* Apple: self-contained framework linking (no -framework on the cc line). */
#if defined(__APPLE__)
__asm__(".linker_option \"-framework\", \"CoreFoundation\"");
__asm__(".linker_option \"-framework\", \"CoreAudio\"");
__asm__(".linker_option \"-framework\", \"AudioToolbox\"");
#endif

#include "delve_audio_adapter.h"

/* Trim miniaudio to playback only, and to this platform's backend(s). */
#define MA_NO_DECODING
#define MA_NO_ENCODING
#define MA_NO_GENERATION
#define MA_NO_RESOURCE_MANAGER
#define MA_NO_NODE_GRAPH
#define MA_NO_ENGINE
#define MA_ENABLE_ONLY_SPECIFIC_BACKENDS
#if defined(__APPLE__)
#define MA_ENABLE_COREAUDIO
#else
#define MA_ENABLE_ALSA
#define MA_ENABLE_PULSEAUDIO
#define MA_ENABLE_JACK
#endif
#define MINIAUDIO_IMPLEMENTATION
#include "miniaudio.h"

#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

#define SR       22050           /* sample rate (Hz) */
#define MAXSAMP  (SR * 50)       /* max samples per clip (music loops are long) */
#define NVOICE   12              /* simultaneous SFX voices */

/* ── synth ──────────────────────────────────────────────────────────────── */

/* Render one note (mono) into buf at *pos. wave: 0=square, 1=triangle, 2=noise.
 * vol 0 produces a silent rest. */
static void note(int16_t *buf, int *pos, int cap, int wave,
                 double freq, int ms, double vol, double duty) {
    int n = (int)((double)ms * SR / 1000.0);
    if (n <= 0) return;
    static uint32_t lfsr = 0xACE1u;
    double phase = 0.0;
    double dphase = freq / (double)SR;
    int atk = n / 12;
    if (atk < 1) atk = 1;
    for (int i = 0; i < n && *pos < cap; i++) {
        double s;
        if (wave == 2) {
            int bit = (lfsr ^ (lfsr >> 1)) & 1u;
            lfsr = (lfsr >> 1) | ((uint32_t)bit << 15);
            s = (lfsr & 1u) ? 1.0 : -1.0;
        } else if (wave == 1) {
            double p = phase - floor(phase);
            s = 4.0 * fabs(p - 0.5) - 1.0;
        } else {
            double p = phase - floor(phase);
            s = (p < duty) ? 1.0 : -1.0;
        }
        phase += dphase;
        double env = (i < atk) ? (double)i / atk
                               : 1.0 - (double)(i - atk) / (double)(n - atk);
        if (env < 0.0) env = 0.0;
        int sample = (int)(s * vol * env * 0.6 * 32767.0);
        if (sample > 32767)  sample = 32767;
        if (sample < -32768) sample = -32768;
        buf[(*pos)++] = (int16_t)sample;
    }
}

/* Equal-tempered MIDI note -> frequency (A4 = midi 69 = 440 Hz). */
static double midi2freq(int m) {
    return 440.0 * pow(2.0, (double)(m - 69) / 12.0);
}

/* Like note(), but MIXES (adds) into buf at an absolute sample offset, so a
 * melody and a bass voice can overlap. The caller zeroes the buffer first. */
static void note_mix(int16_t *buf, int off, int cap, int wave,
                     double freq, int ms, double vol, double duty) {
    int n = (int)((double)ms * SR / 1000.0);
    if (n <= 0) return;
    static uint32_t lfsr = 0x1234u;
    double phase = 0.0, dphase = freq / (double)SR;
    int atk = n / 12;
    if (atk < 1) atk = 1;
    for (int i = 0; i < n; i++) {
        int idx = off + i;
        if (idx < 0) continue;
        if (idx >= cap) break;
        double s;
        if (wave == 2) {
            int bit = (lfsr ^ (lfsr >> 1)) & 1u;
            lfsr = (lfsr >> 1) | ((uint32_t)bit << 15);
            s = (lfsr & 1u) ? 1.0 : -1.0;
        } else if (wave == 1) {
            double p = phase - floor(phase);
            s = 4.0 * fabs(p - 0.5) - 1.0;
        } else {
            double p = phase - floor(phase);
            s = (p < duty) ? 1.0 : -1.0;
        }
        phase += dphase;
        double env = (i < atk) ? (double)i / atk
                               : 1.0 - (double)(i - atk) / (double)(n - atk);
        if (env < 0.0) env = 0.0;
        int mixed = (int)buf[idx] + (int)(s * vol * env * 0.6 * 32767.0);
        if (mixed > 32767)  mixed = 32767;
        if (mixed < -32768) mixed = -32768;
        buf[idx] = (int16_t)mixed;
    }
}

/* Render SFX `id` into buf; returns the number of mono samples written. */
static int render_sfx(int id, int16_t *buf, int cap) {
    int pos = 0;
    switch (id) {
    case DELVE_SFX_HIT:
        note(buf, &pos, cap, 0, 180.0,  40, 0.7, 0.50);
        note(buf, &pos, cap, 2,   0.0,  30, 0.5, 0.50);
        break;
    case DELVE_SFX_HURT:
        note(buf, &pos, cap, 0, 300.0,  40, 0.6, 0.25);
        note(buf, &pos, cap, 0, 200.0,  90, 0.6, 0.25);
        break;
    case DELVE_SFX_KILL:
        note(buf, &pos, cap, 0, 392.0,  50, 0.6, 0.50);
        note(buf, &pos, cap, 0, 294.0,  50, 0.6, 0.50);
        note(buf, &pos, cap, 2,   0.0,  90, 0.5, 0.50);
        break;
    case DELVE_SFX_PICKUP:
        note(buf, &pos, cap, 1, 659.0,  60, 0.6, 0.50);
        note(buf, &pos, cap, 1, 880.0,  90, 0.6, 0.50);
        break;
    case DELVE_SFX_STAIRS:
        note(buf, &pos, cap, 1, 330.0, 120, 0.6, 0.50);
        note(buf, &pos, cap, 1, 220.0, 170, 0.6, 0.50);
        break;
    case DELVE_SFX_LEVELUP:
        note(buf, &pos, cap, 0, 523.0,  70, 0.6, 0.50);
        note(buf, &pos, cap, 0, 659.0,  70, 0.6, 0.50);
        note(buf, &pos, cap, 0, 784.0,  70, 0.6, 0.50);
        note(buf, &pos, cap, 0, 1047.0, 150, 0.6, 0.50);
        break;
    case DELVE_SFX_WARD:
        note(buf, &pos, cap, 1, 880.0,  60, 0.4, 0.50);
        note(buf, &pos, cap, 1, 988.0,  60, 0.4, 0.50);
        note(buf, &pos, cap, 1, 1175.0, 130, 0.4, 0.50);
        break;
    case DELVE_SFX_ZAP:
        note(buf, &pos, cap, 2,   0.0,  60, 0.6, 0.50);
        note(buf, &pos, cap, 0, 150.0,  70, 0.6, 0.12);
        break;
    case DELVE_SFX_CHAOS:
        note(buf, &pos, cap, 0, 196.0, 100, 0.5, 0.50);
        note(buf, &pos, cap, 0, 233.0, 100, 0.5, 0.50);
        note(buf, &pos, cap, 2,   0.0,  90, 0.5, 0.50);
        break;
    case DELVE_SFX_DEATH:
        note(buf, &pos, cap, 1, 440.0, 200, 0.6, 0.50);
        note(buf, &pos, cap, 1, 349.0, 200, 0.6, 0.50);
        note(buf, &pos, cap, 1, 262.0, 400, 0.6, 0.50);
        break;
    case DELVE_SFX_WIN:
        note(buf, &pos, cap, 0, 523.0, 120, 0.6, 0.50);
        note(buf, &pos, cap, 0, 659.0, 120, 0.6, 0.50);
        note(buf, &pos, cap, 0, 784.0, 120, 0.6, 0.50);
        note(buf, &pos, cap, 0, 1047.0, 320, 0.6, 0.50);
        break;
    default:
        break;
    }
    return pos;
}

/* ── Sweden-style longform theme (chiptuned from 1_snowy_valley) ──────────
 * Lead motifs (octaves 4-5) over a passacaglia bass, as MIDI note numbers
 * (-1 = rest). The bass is raised one octave for small-speaker audibility. The
 * arrangement evolves: intro -> Sweden theme -> minor drift -> pivot -> C-major
 * scene -> coda, so the loop runs ~47 s before it repeats. Slow + triangle
 * lead = the original's contemplative, melancholic feel (not chiptune-cheery). */
static const int mIntro[8]  = {79,76,71,69, 78,76,73,71};
static const int mSwed[16]  = {81,78,76,78, 76,73,71,73, 74,69,66,69, 71,66,64,66};
static const int mMinor[16] = {78,74,71,74, 74,71,69,71, 81,78,76,78, 76,73,71,73};
static const int mPivot[16] = {71,66,62,66, 71,67,64,67, 73,69,64,69, 71,66,62,66};
static const int mC[16]     = {76,79,83,79, 74,71,69,71, 72,69,67,69, 69,64,62,64};
static const int mCoda[8]   = {81,-1,76,-1, 74,-1,71,-1};
static const int bIntro[4]  = {28,31,26,33};
static const int bSwed[4]   = {38,33,35,31};
static const int bMinor[4]  = {35,31,38,33};
static const int bPivot[4]  = {31,36,38,33};
static const int bC[4]      = {36,31,33,29};

typedef struct { const int *mel; int mlen; const int *bass; } Section;

/* Render an arrangement: a slightly-legato lead melody (notes ring ~1/3 past
 * the step) over a triangle bass (4 roots per section). */
static int render_song(int16_t *buf, int cap, const Section *secs, int nsec,
                       int notedur, int leadwave, double leadduty) {
    memset(buf, 0, (size_t)cap * sizeof(int16_t));
    int dsamp  = (int)((double)notedur * SR / 1000.0);
    int leadms = notedur + notedur / 3;       /* legato overlap = sadder, flowing */
    int pos = 0;
    for (int s = 0; s < nsec; s++) {
        int secStart = pos;
        for (int i = 0; i < secs[s].mlen; i++) {
            if (secs[s].mel[i] > 0)
                note_mix(buf, pos, cap, leadwave, midi2freq(secs[s].mel[i]),
                         leadms, 0.40, leadduty);
            pos += dsamp;
        }
        int per = secs[s].mlen / 4;
        if (per < 1) per = 1;
        for (int b = 0; b < 4; b++) {
            if (secs[s].bass[b] > 0)
                note_mix(buf, secStart + b * per * dsamp, cap, 1,
                         midi2freq(secs[s].bass[b] + 12), per * notedur - 24, 0.5, 0.5);
        }
    }
    return pos;
}

/* Render looping music `id` into buf; returns the number of mono samples. */
static int render_music(int id, int16_t *buf, int cap) {
    static const Section dungeon[8] = {
        {mIntro,8,bIntro}, {mSwed,16,bSwed}, {mSwed,16,bSwed}, {mMinor,16,bMinor},
        {mPivot,16,bPivot}, {mC,16,bPivot}, {mC,16,bC}, {mCoda,8,bSwed}
    };
    static const Section menu[3] = {
        {mIntro,8,bIntro}, {mSwed,16,bSwed}, {mMinor,16,bMinor}
    };
    static const Section danger[2] = {
        {mMinor,16,bMinor}, {mPivot,16,bPivot}
    };
    /* triangle lead + slow tempo for the calm tracks; a faster pulse for danger */
    if (id == DELVE_MUSIC_DUNGEON) return render_song(buf, cap, dungeon, 8, 420, 1, 0.50);
    if (id == DELVE_MUSIC_MENU)    return render_song(buf, cap, menu, 3, 460, 1, 0.50);
    return render_song(buf, cap, danger, 2, 210, 0, 0.30);
}

/* ── mixing state + device ──────────────────────────────────────────────── */

typedef struct { const int16_t *buf; int len; int pos; int active; } Voice;

static int16_t *g_sfx[DELVE_SFX_COUNT];
static int      g_sfx_len[DELVE_SFX_COUNT];
static int16_t *g_music[DELVE_MUSIC_COUNT];
static int      g_music_n[DELVE_MUSIC_COUNT];

static Voice          g_voices[NVOICE];
static const int16_t *g_mus_buf = NULL;
static int            g_mus_len = 0;
static int            g_mus_pos = 0;
static int            g_mus_on  = 0;

static ma_device g_device;
static ma_mutex  g_lock;
static int       g_enabled = 0;

static void render_all(void) {
    static int16_t tmp[MAXSAMP];
    for (int i = 0; i < DELVE_SFX_COUNT; i++) {
        int n = render_sfx(i, tmp, MAXSAMP);
        g_sfx[i] = (int16_t *)malloc((size_t)n * sizeof(int16_t));
        if (g_sfx[i]) memcpy(g_sfx[i], tmp, (size_t)n * sizeof(int16_t));
        g_sfx_len[i] = g_sfx[i] ? n : 0;
    }
    for (int i = 0; i < DELVE_MUSIC_COUNT; i++) {
        int n = render_music(i, tmp, MAXSAMP);
        g_music[i] = (int16_t *)malloc((size_t)n * sizeof(int16_t));
        if (g_music[i]) memcpy(g_music[i], tmp, (size_t)n * sizeof(int16_t));
        g_music_n[i] = g_music[i] ? n : 0;
    }
}

/* miniaudio data callback (s16 stereo). Mixes active SFX voices + looping music.
 * Runs on miniaudio's audio thread; shared state is guarded by g_lock. */
static void mix_cb(ma_device *dev, void *out, const void *in, ma_uint32 frames) {
    (void)dev; (void)in;
    int16_t *o = (int16_t *)out;
    ma_mutex_lock(&g_lock);
    for (ma_uint32 f = 0; f < frames; f++) {
        int acc = 0;
        for (int v = 0; v < NVOICE; v++) {
            if (g_voices[v].active) {
                acc += ((int)g_voices[v].buf[g_voices[v].pos] * 160) >> 8;
                if (++g_voices[v].pos >= g_voices[v].len) g_voices[v].active = 0;
            }
        }
        if (g_mus_on && g_mus_len > 0) {
            acc += ((int)g_mus_buf[g_mus_pos] * 100) >> 8;
            if (++g_mus_pos >= g_mus_len) g_mus_pos = 0;
        }
        if (acc > 32767)  acc = 32767;
        if (acc < -32768) acc = -32768;
        o[2 * f]     = (int16_t)acc;
        o[2 * f + 1] = (int16_t)acc;
    }
    ma_mutex_unlock(&g_lock);
}

/* ── public ABI ─────────────────────────────────────────────────────────── */

int delve_audio_init(void) {
    if (getenv("DELVE_NO_AUDIO")) return 1;
    render_all();
    ma_device_config cfg = ma_device_config_init(ma_device_type_playback);
    cfg.playback.format   = ma_format_s16;
    cfg.playback.channels = 2;
    cfg.sampleRate        = SR;
    cfg.dataCallback      = mix_cb;
    if (ma_device_init(NULL, &cfg, &g_device) != MA_SUCCESS) return 3;
    if (ma_mutex_init(&g_lock) != MA_SUCCESS) {
        ma_device_uninit(&g_device);
        return 4;
    }
    if (ma_device_start(&g_device) != MA_SUCCESS) {
        ma_mutex_uninit(&g_lock);
        ma_device_uninit(&g_device);
        return 5;
    }
    g_enabled = 1;
    return 0;
}

int delve_audio_play_sfx(int id) {
    if (!g_enabled || id < 0 || id >= DELVE_SFX_COUNT || g_sfx_len[id] <= 0) return 0;
    ma_mutex_lock(&g_lock);
    int slot = -1;
    for (int v = 0; v < NVOICE; v++) {
        if (!g_voices[v].active) { slot = v; break; }
    }
    if (slot < 0) slot = 0; /* steal */
    g_voices[slot].buf = g_sfx[id];
    g_voices[slot].len = g_sfx_len[id];
    g_voices[slot].pos = 0;
    g_voices[slot].active = 1;
    ma_mutex_unlock(&g_lock);
    return 0;
}

int delve_audio_play_music(int id) {
    if (!g_enabled || id < 0 || id >= DELVE_MUSIC_COUNT || g_music_n[id] <= 0) return 0;
    ma_mutex_lock(&g_lock);
    g_mus_buf = g_music[id];
    g_mus_len = g_music_n[id];
    g_mus_pos = 0;
    g_mus_on  = 1;
    ma_mutex_unlock(&g_lock);
    return 0;
}

int delve_audio_stop_music(void) {
    if (!g_enabled) return 0;
    ma_mutex_lock(&g_lock);
    g_mus_on = 0;
    ma_mutex_unlock(&g_lock);
    return 0;
}

int delve_audio_shutdown(void) {
    if (g_enabled) {
        ma_device_uninit(&g_device);   /* stops the callback thread first */
        ma_mutex_uninit(&g_lock);
        g_enabled = 0;
    }
    return 0;
}

/* ── standalone synth test (no Kappa) ──────────────────────────────────────
 * cc -DDELVE_AUDIO_STANDALONE delve_audio.c -lpthread -lm -o /tmp/datest
 * Renders every clip to /tmp/dtest_*.wav for inspection (and, with any
 * argument, opens the device and plays the WIN jingle). */
#ifdef DELVE_AUDIO_STANDALONE
#include <stdio.h>
static void dump_wav(const char *path, const int16_t *buf, int n) {
    FILE *f = fopen(path, "wb");
    if (!f) return;
    uint32_t data = (uint32_t)n * 2u, riff = 36u + data, sr = SR, br = SR * 2u, sub1 = 16u;
    uint16_t pcm = 1, ch = 1, align = 2, bps = 16;
    fwrite("RIFF", 1, 4, f); fwrite(&riff, 4, 1, f); fwrite("WAVE", 1, 4, f);
    fwrite("fmt ", 1, 4, f); fwrite(&sub1, 4, 1, f);
    fwrite(&pcm, 2, 1, f); fwrite(&ch, 2, 1, f); fwrite(&sr, 4, 1, f);
    fwrite(&br, 4, 1, f); fwrite(&align, 2, 1, f); fwrite(&bps, 2, 1, f);
    fwrite("data", 1, 4, f); fwrite(&data, 4, 1, f);
    fwrite(buf, 2, (size_t)n, f);
    fclose(f);
}
int main(int argc, char **argv) {
    static int16_t buf[MAXSAMP];
    char path[64];
    for (int i = 0; i < DELVE_SFX_COUNT; i++) {
        int n = render_sfx(i, buf, MAXSAMP);
        snprintf(path, sizeof path, "/tmp/dtest_sfx_%d.wav", i);
        dump_wav(path, buf, n);
        printf("sfx %2d: %5d samples (%.0f ms)\n", i, n, 1000.0 * n / SR);
    }
    for (int i = 0; i < DELVE_MUSIC_COUNT; i++) {
        int n = render_music(i, buf, MAXSAMP);
        snprintf(path, sizeof path, "/tmp/dtest_music_%d.wav", i);
        dump_wav(path, buf, n);
        printf("music %d: %6d samples (%.1f s)\n", i, n, (double)n / SR);
    }
    if (argc > 1) {
        int r = delve_audio_init();
        printf("init=%d (0=device opened)\n", r);
        if (r == 0) { delve_audio_play_music(DELVE_MUSIC_DUNGEON); ma_sleep(4000); delve_audio_shutdown(); }
    }
    return 0;
}
#endif
