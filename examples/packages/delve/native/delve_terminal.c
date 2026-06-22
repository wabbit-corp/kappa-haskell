#define _POSIX_C_SOURCE 200809L
#include "delve_terminal.h"

#include <errno.h>
#include <poll.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <termios.h>
#include <time.h>
#include <unistd.h>
#include <sys/ioctl.h>
#include <sys/stat.h>

struct delve_terminal_handle {
    int in_fd;
    int out_fd;
    struct termios saved;
    int raw_enabled;
};

static int set_raw(int fd, struct termios *saved) {
    struct termios raw;
    if (tcgetattr(fd, saved) < 0) return errno ? errno : EIO;
    raw = *saved;
    raw.c_iflag &= (tcflag_t)~(BRKINT | ICRNL | INPCK | ISTRIP | IXON);
    raw.c_oflag &= (tcflag_t)~(OPOST);
    raw.c_cflag |= (CS8);
    raw.c_lflag &= (tcflag_t)~(ECHO | ICANON | IEXTEN | ISIG);
    raw.c_cc[VMIN] = 0;
    raw.c_cc[VTIME] = 1;
    if (tcsetattr(fd, TCSAFLUSH, &raw) < 0) return errno ? errno : EIO;
    return 0;
}

int delve_open_terminal(delve_terminal_handle **out) {
    if (!out) return EINVAL;
    delve_terminal_handle *h = (delve_terminal_handle *)calloc(1, sizeof(*h));
    if (!h) return ENOMEM;
    h->in_fd = STDIN_FILENO;
    h->out_fd = STDOUT_FILENO;
    int rc = set_raw(h->in_fd, &h->saved);
    if (rc != 0) { free(h); return rc; }
    h->raw_enabled = 1;
    *out = h;
    return 0;
}

int delve_close_terminal(delve_terminal_handle *h) {
    if (!h) return 0;
    int rc = 0;
    const char *show = "\x1b[?25h\x1b[0m\n";
    (void)write(h->out_fd, show, (unsigned)strlen(show));
    if (h->raw_enabled && tcsetattr(h->in_fd, TCSAFLUSH, &h->saved) < 0) rc = errno ? errno : EIO;
    free(h);
    return rc;
}

static int read_byte(int fd, unsigned char *b) {
    for (;;) {
        struct pollfd pfd = { .fd = fd, .events = POLLIN, .revents = 0 };
        int pr = poll(&pfd, 1, -1);
        if (pr < 0) {
            if (errno == EINTR) continue;
            return errno ? errno : EIO;
        }
        ssize_t n = read(fd, b, 1);
        if (n == 1) return 0;
        if (n < 0 && errno == EINTR) continue;
        if (n < 0) return errno ? errno : EIO;
    }
}

int delve_read_key(delve_terminal_handle *h, int *out_code) {
    if (!h || !out_code) return EINVAL;
    unsigned char c = 0;
    int rc = read_byte(h->in_fd, &c);
    if (rc != 0) return rc;
    if (c == 0x1b) {
        unsigned char seq[2] = {0,0};
        struct pollfd pfd = { .fd = h->in_fd, .events = POLLIN, .revents = 0 };
        if (poll(&pfd, 1, 20) <= 0) { *out_code = 27; return 0; }
        if (read(h->in_fd, &seq[0], 1) != 1) { *out_code = 27; return 0; }
        if (poll(&pfd, 1, 20) <= 0) { *out_code = 27; return 0; }
        if (read(h->in_fd, &seq[1], 1) != 1) { *out_code = 27; return 0; }
        if (seq[0] == '[') {
            switch (seq[1]) {
                case 'A': *out_code = 1000; return 0;
                case 'B': *out_code = 1001; return 0;
                case 'D': *out_code = 1002; return 0;
                case 'C': *out_code = 1003; return 0;
                default: *out_code = 27; return 0;
            }
        }
        *out_code = 27;
        return 0;
    }
    *out_code = (int)c;
    return 0;
}

int delve_write_all(delve_terminal_handle *h, const char *text, int len) {
    if (!h || !text || len < 0) return EINVAL;
    int sent = 0;
    while (sent < len) {
        ssize_t n = write(h->out_fd, text + sent, (size_t)(len - sent));
        if (n < 0) {
            if (errno == EINTR) continue;
            return errno ? errno : EIO;
        }
        sent += (int)n;
    }
    return 0;
}

int delve_get_size(delve_terminal_handle *h, delve_size *out_size) {
    if (!h || !out_size) return EINVAL;
    struct winsize ws;
    if (ioctl(h->out_fd, TIOCGWINSZ, &ws) < 0) return errno ? errno : EIO;
    out_size->cols = ws.ws_col > 0 ? ws.ws_col : 80;
    out_size->rows = ws.ws_row > 0 ? ws.ws_row : 24;
    return 0;
}

uint64_t delve_monotonic_seed(void) {
#ifdef CLOCK_MONOTONIC
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ((uint64_t)ts.tv_sec << 32) ^ (uint64_t)ts.tv_nsec ^ (uint64_t)getpid();
#else
    return ((uint64_t)time(NULL) << 32) ^ (uint64_t)getpid();
#endif
}

const char *delve_strerror(int code) {
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
    if (len < 0) {
        int rc = errno ? errno : EIO;
        fclose(fp);
        return rc;
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
    struct stat st;
    if (stat(path, &st) == 0) {
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
    struct stat st;
    if (stat(path, &st) == 0) {
        return S_ISDIR(st.st_mode) ? 0 : ENOTDIR;
    }
    if (errno != ENOENT) return errno ? errno : EIO;
    if (mkdir(path, 0775) == 0) return 0;
    if (errno == EEXIST) return 0;
    return errno ? errno : EIO;
}

void delve_free_string(char *text) {
    free(text);
}
