#include "delve_terminal.h"

#ifndef WIN32_LEAN_AND_MEAN
#define WIN32_LEAN_AND_MEAN
#endif
#include <windows.h>

#include <direct.h>
#include <errno.h>
#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>

#ifndef EOVERFLOW
#define EOVERFLOW EFBIG
#endif

#ifndef ENOTDIR
#define ENOTDIR ENOENT
#endif

#define DELVE_KEY_UP 1000
#define DELVE_KEY_DOWN 1001
#define DELVE_KEY_LEFT 1002
#define DELVE_KEY_RIGHT 1003
#define DELVE_KEY_RESIZE 1004

struct delve_terminal_handle {
    HANDLE input;
    HANDLE output;
    DWORD saved_input_mode;
    DWORD saved_output_mode;
    int cols;
    int rows;
    int cursor_x;
    int cursor_y;
    WORD attr;
    CHAR_INFO *cells;
};

static WORD default_attr(void) {
    return FOREGROUND_RED | FOREGROUND_GREEN | FOREGROUND_BLUE;
}

static int win_error(void) {
    DWORD e = GetLastError();
    return e == 0 ? EIO : (int)e;
}

static int query_size(HANDLE output, int *cols, int *rows) {
    CONSOLE_SCREEN_BUFFER_INFO info;
    if (!GetConsoleScreenBufferInfo(output, &info)) {
        *cols = 80;
        *rows = 24;
        return win_error();
    }
    int w = (int)(info.srWindow.Right - info.srWindow.Left + 1);
    int h = (int)(info.srWindow.Bottom - info.srWindow.Top + 1);
    *cols = w > 0 ? w : 80;
    *rows = h > 0 ? h : 24;
    return 0;
}

static void clear_cells(delve_terminal_handle *h) {
    if (!h || !h->cells) return;
    int n = h->cols * h->rows;
    for (int i = 0; i < n; i++) {
        h->cells[i].Char.UnicodeChar = L' ';
        h->cells[i].Attributes = h->attr;
    }
    h->cursor_x = 0;
    h->cursor_y = 0;
}

static int resize_cells(delve_terminal_handle *h) {
    int cols = 80;
    int rows = 24;
    (void)query_size(h->output, &cols, &rows);
    if (cols == h->cols && rows == h->rows && h->cells) return 0;
    CHAR_INFO *next = (CHAR_INFO *)calloc((size_t)cols * (size_t)rows, sizeof(CHAR_INFO));
    if (!next) return ENOMEM;
    free(h->cells);
    h->cells = next;
    h->cols = cols;
    h->rows = rows;
    clear_cells(h);
    return 0;
}

static void set_cursor_visible(HANDLE output, int visible) {
    CONSOLE_CURSOR_INFO info;
    if (!GetConsoleCursorInfo(output, &info)) return;
    info.bVisible = visible ? TRUE : FALSE;
    (void)SetConsoleCursorInfo(output, &info);
}

int delve_open_terminal(delve_terminal_handle **out) {
    if (!out) return EINVAL;
    *out = NULL;
    delve_terminal_handle *h = (delve_terminal_handle *)calloc(1, sizeof(*h));
    if (!h) return ENOMEM;

    h->input = GetStdHandle(STD_INPUT_HANDLE);
    h->output = GetStdHandle(STD_OUTPUT_HANDLE);
    if (h->input == INVALID_HANDLE_VALUE || h->output == INVALID_HANDLE_VALUE) {
        int rc = win_error();
        free(h);
        return rc;
    }
    if (!GetConsoleMode(h->input, &h->saved_input_mode)) {
        int rc = win_error();
        free(h);
        return rc;
    }
    if (!GetConsoleMode(h->output, &h->saved_output_mode)) {
        int rc = win_error();
        free(h);
        return rc;
    }

    DWORD input_mode = ENABLE_WINDOW_INPUT | ENABLE_PROCESSED_INPUT;
    (void)SetConsoleMode(h->input, input_mode);
    (void)SetConsoleMode(h->output, h->saved_output_mode | ENABLE_PROCESSED_OUTPUT);
    h->attr = default_attr();
    int rc = resize_cells(h);
    if (rc != 0) {
        free(h);
        return rc;
    }
    set_cursor_visible(h->output, 0);
    *out = h;
    return 0;
}

int delve_close_terminal(delve_terminal_handle *h) {
    if (!h) return 0;
    set_cursor_visible(h->output, 1);
    (void)SetConsoleMode(h->input, h->saved_input_mode);
    (void)SetConsoleMode(h->output, h->saved_output_mode);
    free(h->cells);
    free(h);
    return 0;
}

int delve_read_key(delve_terminal_handle *h, int *out_code) {
    if (!h || !out_code) return EINVAL;
    INPUT_RECORD rec;
    DWORD got = 0;
    for (;;) {
        if (!ReadConsoleInputW(h->input, &rec, 1, &got)) return win_error();
        if (got == 0) continue;
        if (rec.EventType == WINDOW_BUFFER_SIZE_EVENT) {
            *out_code = DELVE_KEY_RESIZE;
            return 0;
        }
        if (rec.EventType != KEY_EVENT || !rec.Event.KeyEvent.bKeyDown) continue;
        KEY_EVENT_RECORD key = rec.Event.KeyEvent;
        switch (key.wVirtualKeyCode) {
            case VK_UP: *out_code = DELVE_KEY_UP; return 0;
            case VK_DOWN: *out_code = DELVE_KEY_DOWN; return 0;
            case VK_LEFT: *out_code = DELVE_KEY_LEFT; return 0;
            case VK_RIGHT: *out_code = DELVE_KEY_RIGHT; return 0;
            case VK_ESCAPE: *out_code = 27; return 0;
            case VK_RETURN: *out_code = 13; return 0;
            case VK_BACK: *out_code = 127; return 0;
            default: break;
        }
        WCHAR ch = key.uChar.UnicodeChar;
        if (ch >= 32 && ch < 127) {
            *out_code = (int)ch;
            return 0;
        }
    }
}

static WORD rgb_attr(int r, int g, int b, int bold) {
    WORD a = 0;
    if (r > 72) a |= FOREGROUND_RED;
    if (g > 72) a |= FOREGROUND_GREEN;
    if (b > 72) a |= FOREGROUND_BLUE;
    if (bold || r > 176 || g > 176 || b > 176) a |= FOREGROUND_INTENSITY;
    return a ? a : default_attr();
}

static int parse_int(const char *text, int len, int *pos) {
    int n = 0;
    int seen = 0;
    while (*pos < len && text[*pos] >= '0' && text[*pos] <= '9') {
        seen = 1;
        n = n * 10 + (text[*pos] - '0');
        (*pos)++;
    }
    return seen ? n : -1;
}

static void apply_sgr(delve_terminal_handle *h, int *params, int count) {
    if (count == 0) {
        h->attr = default_attr();
        return;
    }
    int bold = (h->attr & FOREGROUND_INTENSITY) ? 1 : 0;
    for (int i = 0; i < count; i++) {
        int p = params[i];
        if (p == 0) {
            h->attr = default_attr();
            bold = 0;
        } else if (p == 1) {
            h->attr |= FOREGROUND_INTENSITY;
            bold = 1;
        } else if (p == 22) {
            h->attr &= (WORD)~FOREGROUND_INTENSITY;
            bold = 0;
        } else if (p >= 30 && p <= 37) {
            static const WORD base[8] = {
                0,
                FOREGROUND_RED,
                FOREGROUND_GREEN,
                FOREGROUND_RED | FOREGROUND_GREEN,
                FOREGROUND_BLUE,
                FOREGROUND_RED | FOREGROUND_BLUE,
                FOREGROUND_GREEN | FOREGROUND_BLUE,
                FOREGROUND_RED | FOREGROUND_GREEN | FOREGROUND_BLUE
            };
            h->attr = base[p - 30] | (bold ? FOREGROUND_INTENSITY : 0);
        } else if (p >= 90 && p <= 97) {
            static const WORD base[8] = {
                0,
                FOREGROUND_RED,
                FOREGROUND_GREEN,
                FOREGROUND_RED | FOREGROUND_GREEN,
                FOREGROUND_BLUE,
                FOREGROUND_RED | FOREGROUND_BLUE,
                FOREGROUND_GREEN | FOREGROUND_BLUE,
                FOREGROUND_RED | FOREGROUND_GREEN | FOREGROUND_BLUE
            };
            h->attr = base[p - 90] | FOREGROUND_INTENSITY;
            bold = 1;
        } else if (p == 39) {
            h->attr = default_attr() | (bold ? FOREGROUND_INTENSITY : 0);
        } else if (p == 38 && i + 4 < count && params[i + 1] == 2) {
            h->attr = rgb_attr(params[i + 2], params[i + 3], params[i + 4], bold);
            i += 4;
        }
    }
}

static void clear_line(delve_terminal_handle *h) {
    if (!h || !h->cells || h->cursor_y < 0 || h->cursor_y >= h->rows) return;
    for (int x = h->cursor_x; x < h->cols; x++) {
        int idx = h->cursor_y * h->cols + x;
        h->cells[idx].Char.UnicodeChar = L' ';
        h->cells[idx].Attributes = h->attr;
    }
}

static int handle_csi(delve_terminal_handle *h, const char *text, int len, int *pos) {
    int params[16];
    int count = 0;
    int question = 0;
    if (*pos < len && text[*pos] == '?') {
        question = 1;
        (*pos)++;
    }
    while (*pos < len && count < 16) {
        int value = parse_int(text, len, pos);
        params[count++] = value < 0 ? 0 : value;
        if (*pos >= len || text[*pos] != ';') break;
        (*pos)++;
    }
    if (*pos >= len) return 0;
    char final = text[(*pos)++];
    if (question && final == 'l' && count > 0 && params[0] == 25) {
        set_cursor_visible(h->output, 0);
        return 1;
    }
    if (question && final == 'h' && count > 0 && params[0] == 25) {
        set_cursor_visible(h->output, 1);
        return 1;
    }
    if (final == 'm') {
        apply_sgr(h, params, count);
    } else if (final == 'J') {
        if (count == 0 || params[0] == 2 || params[0] == 0) clear_cells(h);
    } else if (final == 'K') {
        clear_line(h);
    } else if (final == 'H' || final == 'f') {
        int row = count > 0 && params[0] > 0 ? params[0] - 1 : 0;
        int col = count > 1 && params[1] > 0 ? params[1] - 1 : 0;
        if (row < 0) row = 0;
        if (col < 0) col = 0;
        if (row >= h->rows) row = h->rows - 1;
        if (col >= h->cols) col = h->cols - 1;
        h->cursor_y = row;
        h->cursor_x = col;
    }
    return 1;
}

static int utf8_decode(const unsigned char *s, int len, int *pos, WCHAR *out) {
    unsigned char c = s[(*pos)++];
    if (c < 0x80) {
        *out = (WCHAR)c;
        return 1;
    }
    uint32_t cp = 0;
    int need = 0;
    if ((c & 0xE0) == 0xC0) { cp = c & 0x1F; need = 1; }
    else if ((c & 0xF0) == 0xE0) { cp = c & 0x0F; need = 2; }
    else if ((c & 0xF8) == 0xF0) { cp = c & 0x07; need = 3; }
    else { *out = L'?'; return 1; }
    if (*pos + need > len) { *out = L'?'; *pos = len; return 1; }
    for (int i = 0; i < need; i++) {
        unsigned char b = s[(*pos)++];
        if ((b & 0xC0) != 0x80) { *out = L'?'; return 1; }
        cp = (cp << 6) | (uint32_t)(b & 0x3F);
    }
    *out = cp <= 0xFFFF ? (WCHAR)cp : L'?';
    return 1;
}

static void put_wchar(delve_terminal_handle *h, WCHAR ch) {
    if (ch == L'\r') {
        h->cursor_x = 0;
        return;
    }
    if (ch == L'\n') {
        h->cursor_x = 0;
        h->cursor_y++;
        return;
    }
    if (h->cursor_y < 0 || h->cursor_y >= h->rows) return;
    if (h->cursor_x >= h->cols) {
        h->cursor_x = 0;
        h->cursor_y++;
    }
    if (h->cursor_y < 0 || h->cursor_y >= h->rows) return;
    if (h->cursor_x < 0) h->cursor_x = 0;
    int idx = h->cursor_y * h->cols + h->cursor_x;
    h->cells[idx].Char.UnicodeChar = ch;
    h->cells[idx].Attributes = h->attr;
    h->cursor_x++;
}

static int flush_cells(delve_terminal_handle *h) {
    if (!h || !h->cells) return EINVAL;
    COORD size;
    size.X = (SHORT)h->cols;
    size.Y = (SHORT)h->rows;
    COORD origin;
    origin.X = 0;
    origin.Y = 0;
    SMALL_RECT rect;
    rect.Left = 0;
    rect.Top = 0;
    rect.Right = (SHORT)(h->cols - 1);
    rect.Bottom = (SHORT)(h->rows - 1);
    if (!WriteConsoleOutputW(h->output, h->cells, size, origin, &rect)) return win_error();
    return 0;
}

int delve_write_all(delve_terminal_handle *h, const char *text, int len) {
    if (!h || !text || len < 0) return EINVAL;
    int rc = resize_cells(h);
    if (rc != 0) return rc;
    int pos = 0;
    while (pos < len) {
        unsigned char c = (unsigned char)text[pos];
        if (c == 0x1b && pos + 1 < len && text[pos + 1] == '[') {
            pos += 2;
            if (handle_csi(h, text, len, &pos)) continue;
        }
        WCHAR ch = L'?';
        (void)utf8_decode((const unsigned char *)text, len, &pos, &ch);
        put_wchar(h, ch);
    }
    return flush_cells(h);
}

int delve_get_size(delve_terminal_handle *h, delve_size *out_size) {
    if (!h || !out_size) return EINVAL;
    int cols = 80;
    int rows = 24;
    int rc = query_size(h->output, &cols, &rows);
    out_size->cols = cols;
    out_size->rows = rows;
    return rc == 0 ? 0 : rc;
}

uint64_t delve_monotonic_seed(void) {
    LARGE_INTEGER counter;
    if (!QueryPerformanceCounter(&counter)) counter.QuadPart = 0;
    return (uint64_t)counter.QuadPart ^ ((uint64_t)GetCurrentProcessId() << 32);
}

const char *delve_strerror(int code) {
    static char buf[512];
    DWORD flags = FORMAT_MESSAGE_FROM_SYSTEM | FORMAT_MESSAGE_IGNORE_INSERTS;
    DWORD n = FormatMessageA(flags, NULL, (DWORD)code, 0, buf, (DWORD)sizeof(buf), NULL);
    if (n > 0) {
        while (n > 0 && (buf[n - 1] == '\r' || buf[n - 1] == '\n' || buf[n - 1] == ' ')) {
            buf[--n] = '\0';
        }
        return buf;
    }
    return strerror(code);
}

int delve_read_text_file(const char *path, char **out_text, int *out_len) {
    if (!path || !out_text || !out_len) return EINVAL;
    *out_text = NULL;
    *out_len = 0;
    FILE *fp = fopen(path, "rb");
    if (!fp) return errno ? errno : EIO;
    if (fseek(fp, 0, SEEK_END) != 0) {
        int rc = errno ? errno : EIO;
        fclose(fp);
        return rc;
    }
    long len = ftell(fp);
    if (len < 0 || len > INT_MAX) {
        fclose(fp);
        return len < 0 ? (errno ? errno : EIO) : EOVERFLOW;
    }
    if (fseek(fp, 0, SEEK_SET) != 0) {
        int rc = errno ? errno : EIO;
        fclose(fp);
        return rc;
    }
    char *buf = (char *)malloc((size_t)len + 1u);
    if (!buf) {
        fclose(fp);
        return ENOMEM;
    }
    size_t got = fread(buf, 1, (size_t)len, fp);
    if (got != (size_t)len) {
        int rc = ferror(fp) ? (errno ? errno : EIO) : EIO;
        free(buf);
        fclose(fp);
        return rc;
    }
    if (fclose(fp) != 0) {
        int rc = errno ? errno : EIO;
        free(buf);
        return rc;
    }
    buf[len] = '\0';
    *out_text = buf;
    *out_len = (int)len;
    return 0;
}

int delve_write_text_file(const char *path, const char *text, int len) {
    if (!path || !text || len < 0) return EINVAL;
    FILE *fp = fopen(path, "wb");
    if (!fp) return errno ? errno : EIO;
    size_t written = fwrite(text, 1, (size_t)len, fp);
    if (written != (size_t)len) {
        int rc = errno ? errno : EIO;
        fclose(fp);
        return rc;
    }
    if (fclose(fp) != 0) return errno ? errno : EIO;
    return 0;
}

int delve_file_exists(const char *path, int *out_exists) {
    if (!path || !out_exists) return EINVAL;
    struct _stat st;
    if (_stat(path, &st) == 0) {
        *out_exists = 1;
        return 0;
    }
    if (errno == ENOENT) {
        *out_exists = 0;
        return 0;
    }
    return errno ? errno : EIO;
}

int delve_ensure_directory(const char *path) {
    if (!path) return EINVAL;
    DWORD attrs = GetFileAttributesA(path);
    if (attrs != INVALID_FILE_ATTRIBUTES) {
        return (attrs & FILE_ATTRIBUTE_DIRECTORY) ? 0 : ENOTDIR;
    }
    if (CreateDirectoryA(path, NULL)) return 0;
    DWORD e = GetLastError();
    if (e == ERROR_ALREADY_EXISTS) return 0;
    return e == 0 ? EIO : (int)e;
}

void delve_free_string(char *text) {
    free(text);
}
