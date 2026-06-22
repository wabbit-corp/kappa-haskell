/* delve_audio_adapter.h — conservative-ABI surface for delve's chiptune audio.
 *
 * This header is the SINGLE source of truth for the host.native.delve_audio
 * raw surface: the build plan generates it by PREPROCESSING + PARSING this
 * header (generateAllFromHeader "…/delve_audio_adapter.h" "delve_audio_").
 * The implementation (delve_audio.c) includes this header so its definitions
 * are checked against these prototypes.
 *
 * Every prototype is conservatively representable (only `int`), so the broad
 * generator binds all of them as `Integer`-returning calls.
 *
 * Design: a self-contained chiptune synthesizer (square / triangle / noise +
 * AD envelope) renders short 8-bit-style SFX and a longform theme to 16-bit PCM
 * once at init; the vendored header-only miniaudio library (native/miniaudio.h)
 * provides the audio device and its callback mixes the result. miniaudio adds
 * NO third-party LINK dependency — it runtime-loads ALSA/PulseAudio on Linux
 * and self-links the macOS CoreAudio frameworks from the shim source — and it
 * fails soft with no device, so the binary loads on machines with no audio
 * hardware at all. All calls are non-blocking and degrade to no-ops when audio
 * is unavailable or the DELVE_NO_AUDIO environment variable is set.
 */
#ifndef DELVE_AUDIO_ADAPTER_H
#define DELVE_AUDIO_ADAPTER_H

#ifdef __cplusplus
extern "C" {
#endif

/* Sound-effect ids — must match `delve.audio` on the Kappa side. */
#define DELVE_SFX_HIT      0
#define DELVE_SFX_HURT     1
#define DELVE_SFX_KILL     2
#define DELVE_SFX_PICKUP   3
#define DELVE_SFX_STAIRS   4
#define DELVE_SFX_LEVELUP  5
#define DELVE_SFX_WARD     6
#define DELVE_SFX_ZAP      7
#define DELVE_SFX_CHAOS    8
#define DELVE_SFX_DEATH    9
#define DELVE_SFX_WIN      10
#define DELVE_SFX_COUNT    11

/* Music-track ids. */
#define DELVE_MUSIC_DUNGEON 0
#define DELVE_MUSIC_MENU    1
#define DELVE_MUSIC_DANGER  2
#define DELVE_MUSIC_COUNT   3

/* Render all SFX/music to temp WAVs and prepare playback. Returns 0 when audio
 * is enabled, or a nonzero code when it is unavailable/disabled (the caller
 * then simply skips further calls — every other entry point is a safe no-op
 * when audio is off). */
int delve_audio_init(void);

/* Play a one-shot sound effect by id. No-op for an out-of-range id or when
 * audio is off. Returns 0. Fire-and-forget: never blocks on playback. */
int delve_audio_play_sfx(int id);

/* Start (or replace) the looping background-music track. Returns 0. */
int delve_audio_play_music(int id);

/* Stop background music. Returns 0. */
int delve_audio_stop_music(void);

/* Stop everything and release the audio subsystem. Returns 0. */
int delve_audio_shutdown(void);

#ifdef __cplusplus
}
#endif

#endif /* DELVE_AUDIO_ADAPTER_H */
