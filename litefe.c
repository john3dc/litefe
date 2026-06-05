/*
 * litefe - a minimal terminal text editor.
 *
 * Single file, depends only on libc (no ncurses). Real selection with
 * copy / cut / paste, multi-level undo / redo, find and goto-line, mouse
 * support. A coloured header bar, a status line, an overlay window for every
 * prompt, and a coloured key bar.
 *
 * Build:  cc -O2 -Wall -o litefe litefe.c
 * Keys:   press Ctrl-H inside the program.
 *
 * Shortcuts:
 *   Ctrl-S save   Ctrl-Q quit   Ctrl-G goto line   Ctrl-H help
 *   Ctrl-C copy   Ctrl-X cut    Ctrl-V paste   Ctrl-A select all
 *   Ctrl-Z undo   Ctrl-Y redo   Ctrl-D dup line   Ctrl-K cut line
 *   Ctrl-F find   Ctrl-N / F3 find next   Ctrl-E encoding view
 *   Ctrl-B mouse mode   Ctrl-T set mark   Shift/Ctrl+arrows select / word jump
 */
#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <fcntl.h>
#include <sys/stat.h>
#include <sys/ioctl.h>
#include <sys/types.h>
#include <termios.h>
#include <signal.h>
#include <errno.h>
#include <limits.h>
#include <ctype.h>
#include <strings.h>
#include <wchar.h>
#include <locale.h>
#include <langinfo.h>
#include <stdarg.h>
#include <poll.h>

#ifndef PATH_MAX
#define PATH_MAX 4096
#endif

#define DEF_TABW 4

/* ------------------------------------------------------------------ */
/* Terminal globals                                                   */
/* ------------------------------------------------------------------ */
static struct termios g_orig, g_raw;
static int g_have_orig = 0, g_in_tui = 0;
static volatile sig_atomic_t g_resized = 1;
static int g_rows = 24, g_cols = 80;
static int g_utf8 = 1;

/* configurable behaviour (set from env in main) */
static int g_tabw = DEF_TABW;   /* LITEFE_TAB: display width of a tab */
static int g_expandtab = 0;     /* LITEFE_EXPANDTAB: insert spaces instead of a tab */
static int g_crlf = 0;          /* per-file: write CRLF line endings (detected on load) */
static int g_mouse = 0;         /* LITEFE_MOUSE / Ctrl-B: grab the mouse for in-app use;
                                   off (default) leaves it to the terminal (native menu). */
static int g_altscreen = 1;     /* LITEFE_ALTSCREEN=0: stay on the normal screen (leave the
                                   editor text in place on exit, like nano). */

static void leave_tui(void);
static void render(void);
static int  read_key(void);
static void die(const char *m) { leave_tui(); fprintf(stderr, "litefe: %s\n", m); exit(1); }
static void *xmalloc(size_t n)  { void *p = malloc(n);     if (!p) die("out of memory"); return p; }
static void *xrealloc(void *p, size_t n) { void *q = realloc(p, n); if (!q) die("out of memory"); return q; }
static char *xstrdup(const char *s) { char *p = strdup(s); if (!p) die("out of memory"); return p; }

/* ------------------------------------------------------------------ */
/* Dynamic string buffer                                              */
/* ------------------------------------------------------------------ */
typedef struct { char *p; size_t len, cap; } Buf;

static void buf_reserve(Buf *b, size_t need) {
    if (b->len + need + 1 > b->cap) {
        size_t nc = b->cap ? b->cap * 2 : 4096;
        while (nc < b->len + need + 1) nc *= 2;
        b->p = xrealloc(b->p, nc);
        b->cap = nc;
    }
}
static void buf_add(Buf *b, const char *s, size_t n) {
    buf_reserve(b, n);
    memcpy(b->p + b->len, s, n);
    b->len += n;
    b->p[b->len] = 0;
}
static void buf_s(Buf *b, const char *s) { buf_add(b, s, strlen(s)); }
static void buf_pad(Buf *b, int n) { while (n-- > 0) buf_add(b, " ", 1); }
static void buf_printf(Buf *b, const char *fmt, ...) {
    char tmp[1024];
    va_list ap; va_start(ap, fmt);
    int n = vsnprintf(tmp, sizeof tmp, fmt, ap);
    va_end(ap);
    if (n < 0) return;
    if ((size_t)n >= sizeof tmp) n = sizeof tmp - 1;
    buf_add(b, tmp, (size_t)n);
}

/* ------------------------------------------------------------------ */
/* Small helpers                                                      */
/* ------------------------------------------------------------------ */
static void wr(const char *s) { ssize_t r = write(STDOUT_FILENO, s, strlen(s)); (void)r; }
static int utf8_len(unsigned char c) { return c >= 0xF0 ? 4 : c >= 0xE0 ? 3 : c >= 0xC0 ? 2 : 1; }

/* Put text on the terminal's (system) clipboard via OSC 52, so a copy here can
   be pasted into other apps on the desktop. Terminals that don't support it
   ignore the sequence. */
static void osc52_copy(const char *data, int len) {
    if (len <= 0 || len > 100000) return;
    static const char *B = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
    Buf o = {0};
    buf_s(&o, "\x1b]52;c;");
    int i = 0;
    for (; i + 3 <= len; i += 3) {
        unsigned v = (unsigned char)data[i] << 16 | (unsigned char)data[i+1] << 8 | (unsigned char)data[i+2];
        char q[4] = { B[v>>18 & 63], B[v>>12 & 63], B[v>>6 & 63], B[v & 63] };
        buf_add(&o, q, 4);
    }
    int rem = len - i;
    if (rem == 1) {
        unsigned v = (unsigned char)data[i] << 16;
        char q[4] = { B[v>>18 & 63], B[v>>12 & 63], '=', '=' }; buf_add(&o, q, 4);
    } else if (rem == 2) {
        unsigned v = (unsigned char)data[i] << 16 | (unsigned char)data[i+1] << 8;
        char q[4] = { B[v>>18 & 63], B[v>>12 & 63], B[v>>6 & 63], '=' }; buf_add(&o, q, 4);
    }
    buf_s(&o, "\x07");
    ssize_t w = write(STDOUT_FILENO, o.p, o.len); (void)w;
    free(o.p);
}

static void path_base(const char *p, char *out, size_t n) {
    const char *s = strrchr(p, '/');
    snprintf(out, n, "%s", s ? s + 1 : p);
}
static void abbrev_home(const char *path, char *out, size_t n) {
    const char *home = getenv("HOME");
    size_t hl = home ? strlen(home) : 0;
    if (hl && strncmp(path, home, hl) == 0 && (path[hl] == '/' || path[hl] == 0))
        snprintf(out, n, "~%s", path + hl);
    else
        snprintf(out, n, "%s", path);
}

/* ------------------------------------------------------------------ */
/* Unicode-aware width                                                */
/* ------------------------------------------------------------------ */
static int str_width(const char *s) {
    mbstate_t ps; memset(&ps, 0, sizeof ps);
    size_t len = strlen(s);
    const char *p = s;
    int w = 0;
    while (*p) {
        wchar_t wc;
        size_t k = mbrtowc(&wc, p, len - (p - s), &ps);
        if (k == (size_t)-1 || k == (size_t)-2) { p++; w++; memset(&ps, 0, sizeof ps); continue; }
        if (k == 0) break;
        int cw = wcwidth(wc);
        if (cw < 0) cw = 1;
        w += cw; p += k;
    }
    return w;
}
static int buf_add_trunc(Buf *b, const char *s, int maxw) {
    if (maxw <= 0) return 0;
    mbstate_t ps; memset(&ps, 0, sizeof ps);
    size_t len = strlen(s);
    const char *p = s;
    int w = 0;
    while (*p) {
        wchar_t wc;
        size_t k = mbrtowc(&wc, p, len - (p - s), &ps);
        if (k == (size_t)-1 || k == (size_t)-2) { k = 1; wc = (unsigned char)*p; memset(&ps, 0, sizeof ps); }
        if (k == 0) break;
        int cw = wcwidth(wc);
        if (cw < 0) cw = 1;
        if (w + cw > maxw) break;
        buf_add(b, p, k);
        w += cw; p += k;
    }
    return w;
}
static int buf_add_tail(Buf *b, const char *s, int maxw) {
    int total = str_width(s);
    if (total <= maxw) { buf_s(b, s); return total; }
    int skip = total - maxw;
    mbstate_t ps; memset(&ps, 0, sizeof ps);
    size_t len = strlen(s);
    const char *p = s;
    int w = 0;
    while (*p && w < skip) {
        wchar_t wc;
        size_t k = mbrtowc(&wc, p, len - (p - s), &ps);
        if (k == (size_t)-1 || k == (size_t)-2) { k = 1; wc = (unsigned char)*p; memset(&ps, 0, sizeof ps); }
        if (k == 0) break;
        int cw = wcwidth(wc); if (cw < 0) cw = 1;
        w += cw; p += k;
    }
    buf_s(b, p);
    return str_width(p);
}

/* ------------------------------------------------------------------ */
/* Text encoding (how stored bytes are interpreted for display)        */
/* ------------------------------------------------------------------ */
enum { ENC_UTF8 = 0, ENC_LATIN1, ENC_CP1252 };
static int g_enc = ENC_UTF8;
static int g_enc_forced = 0;       /* LITEFE_ENC pinned it -> don't auto-detect */
static const char *enc_name(void) {
    return g_enc == ENC_LATIN1 ? "Latin-1" : g_enc == ENC_CP1252 ? "CP1252" : "UTF-8";
}
/* CP1252 (Windows "ANSI") mapping for 0x80..0x9F to Unicode; 0 = undefined */
static const unsigned cp1252_hi[32] = {
    0x20AC,0x0081,0x201A,0x0192,0x201E,0x2026,0x2020,0x2021,
    0x02C6,0x2030,0x0160,0x2039,0x0152,0x008D,0x017D,0x008F,
    0x0090,0x2018,0x2019,0x201C,0x201D,0x2022,0x2013,0x2014,
    0x02DC,0x2122,0x0161,0x203A,0x0153,0x009D,0x017E,0x0178
};
static unsigned byte_to_cp(unsigned char c) {   /* single-byte encodings only */
    if (g_enc == ENC_CP1252 && c >= 0x80 && c <= 0x9F) return cp1252_hi[c - 0x80];
    return c;                                    /* Latin-1 = identity */
}
static int utf8_encode(unsigned cp, char *out) {
    if (cp < 0x80)      { out[0] = (char)cp; return 1; }
    if (cp < 0x800)     { out[0] = 0xC0 | cp >> 6;   out[1] = 0x80 | (cp & 0x3F); return 2; }
    if (cp < 0x10000)   { out[0] = 0xE0 | cp >> 12;  out[1] = 0x80 | (cp >> 6 & 0x3F); out[2] = 0x80 | (cp & 0x3F); return 3; }
    out[0] = 0xF0 | cp >> 18; out[1] = 0x80 | (cp >> 12 & 0x3F);
    out[2] = 0x80 | (cp >> 6 & 0x3F); out[3] = 0x80 | (cp & 0x3F); return 4;
}
/* number of bytes the char at p occupies, in the current encoding */
static int enc_charlen(const char *p) {
    return g_enc == ENC_UTF8 ? utf8_len((unsigned char)*p) : 1;
}
/* emit the char at p (bl bytes) to out, transcoding single-byte encodings to
   UTF-8 so they show correctly on a UTF-8 terminal */
static void emit_char(Buf *out, const char *p, int bl) {
    if (g_enc == ENC_UTF8 || !g_utf8) { buf_add(out, p, bl); return; }
    unsigned cp = byte_to_cp((unsigned char)*p);
    char u[4]; int n = utf8_encode(cp, u);
    buf_add(out, u, n);
}

/* width (display columns) and byte length of the char at p, with tabs
   expanded relative to the current column. */
static int char_w(const char *p, int avail, int col, int *blen) {
    unsigned char c = (unsigned char)*p;
    if (c == '\t') { *blen = 1; return g_tabw - (col % g_tabw); }
    if (c < 0x20)  { *blen = 1; return 2; }         /* control chars show as spaces */
    if (g_enc != ENC_UTF8) { *blen = 1; return 1; }   /* single-byte: one byte = one column */
    wchar_t wc; mbstate_t ps; memset(&ps, 0, sizeof ps);
    size_t k = mbrtowc(&wc, p, avail, &ps);
    if (k == (size_t)-1 || k == (size_t)-2 || k == 0) { *blen = 1; return 1; }
    int w = wcwidth(wc); if (w < 0) w = 1;
    *blen = (int)k; return w;
}

/* ------------------------------------------------------------------ */
/* Colours                                                            */
/* ------------------------------------------------------------------ */
#define C_RESET "\x1b[0m"
#define C_SEP   "\x1b[38;5;240m"
#define C_GUT   "\x1b[38;5;240m"
#define C_GUTC  "\x1b[1;36m"
#define C_SEL   "\x1b[48;5;24m"   /* selection: blue background (distinct from the cursor) */
#define C_CUR   "\x1b[7m"         /* cursor: reverse video */

/* ------------------------------------------------------------------ */
/* Terminal raw mode + alt screen + mouse                             */
/* ------------------------------------------------------------------ */
static void leave_tui(void) {
    if (!g_in_tui) return;
    if (g_have_orig) tcsetattr(STDIN_FILENO, TCSAFLUSH, &g_orig);
    wr("\x1b[?1002l\x1b[?1006l\x1b[?1l\x1b>\x1b[?7h\x1b[?25h");   /* incl. rmkx (normal cursor keys) */
    if (g_altscreen) wr("\x1b[?1049l");
    else             wr("\r\n");          /* like nano: leave our text in place */
    g_in_tui = 0;
}
/* In-app: grab the mouse (1002 = drag, 1006 = SGR coords); the wheel arrives as
   events. Desktop: don't grab, so the terminal's native selection / right-click
   menu keep working -- wheel-scroll then comes from application-cursor-keys mode
   (enter_tui), which makes the terminal forward the wheel as Up/Down arrows. */
static void mouse_set(int on) {
    wr(on ? "\x1b[?1002h\x1b[?1006h" : "\x1b[?1002l\x1b[?1006l");
}
static void enter_tui(void) {
    if (g_have_orig) tcsetattr(STDIN_FILENO, TCSAFLUSH, &g_raw);
    /* hardware cursor stays hidden; we draw our own block cursor */
    if (g_altscreen) wr("\x1b[?1049h");
    wr("\x1b[?1h\x1b=");         /* application cursor keys: lets terminals (e.g. macOS
                                    Terminal.app) forward the mouse wheel as Up/Down arrows */
    wr("\x1b[?7l\x1b[?25l\x1b[2J");
    mouse_set(g_mouse);
    g_in_tui = 1;
}
static void on_signal(int sig) { leave_tui(); _exit(128 + sig); }
static void on_winch(int sig) { (void)sig; g_resized = 1; }

static int term_init(void) {
    if (!isatty(STDIN_FILENO) || !isatty(STDOUT_FILENO)) return -1;
    if (tcgetattr(STDIN_FILENO, &g_orig) < 0) return -1;
    g_have_orig = 1;
    g_raw = g_orig;
    g_raw.c_lflag &= ~(ECHO | ICANON | ISIG | IEXTEN);
    g_raw.c_iflag &= ~(IXON | ICRNL | BRKINT | INPCK | ISTRIP);
    g_raw.c_oflag &= ~(OPOST);
    g_raw.c_cflag |= CS8;
    g_raw.c_cc[VMIN] = 1;
    g_raw.c_cc[VTIME] = 0;

    atexit(leave_tui);
    struct sigaction sa = {0};
    sa.sa_handler = on_signal;
    sigaction(SIGINT, &sa, NULL);
    sigaction(SIGTERM, &sa, NULL);
    sigaction(SIGHUP, &sa, NULL);
    struct sigaction sw = {0};
    sw.sa_handler = on_winch;        /* no SA_RESTART: interrupts read() */
    sigaction(SIGWINCH, &sw, NULL);
    signal(SIGPIPE, SIG_IGN);

    enter_tui();
    return 0;
}
static void get_size(void) {
    struct winsize ws;
    if (ioctl(STDOUT_FILENO, TIOCGWINSZ, &ws) == 0 && ws.ws_row > 0 && ws.ws_col > 0) {
        g_rows = ws.ws_row; g_cols = ws.ws_col;
    }
    if (g_rows < 5)  g_rows = 5;
    if (g_cols < 20) g_cols = 20;
}

/* ------------------------------------------------------------------ */
/* Keyboard                                                           */
/* ------------------------------------------------------------------ */
enum {
    K_RESIZE = -2, K_EOF = -1,
    K_UP = 1000, K_DOWN, K_LEFT, K_RIGHT,
    K_HOME, K_END, K_PGUP, K_PGDN, K_DEL,
    K_F1, K_F2, K_F3, K_F4, K_F5, K_F6, K_F7, K_F8, K_F9, K_F10,
    K_MOUSE,
    K_SUP, K_SDOWN, K_SLEFT, K_SRIGHT, K_SHOME, K_SEND,    /* Shift + nav */
    K_CLEFT, K_CRIGHT, K_CUP, K_CDOWN,                     /* Ctrl  + nav */
    K_ESC = 27, K_ENTER = 13, K_BS = 127, K_TAB = 9
};
static int g_mx, g_my, g_mbtn, g_mrelease;   /* last mouse event */
static int read_key(void) {
    unsigned char c;
    int r;
    while ((r = read(STDIN_FILENO, &c, 1)) < 0) {
        if (errno == EINTR) { if (g_resized) return K_RESIZE; continue; }
        return K_EOF;
    }
    if (r == 0) return K_EOF;
    if (c != 0x1b) return c;

    struct pollfd pf = { STDIN_FILENO, POLLIN, 0 };
    if (poll(&pf, 1, 50) <= 0) return K_ESC;
    unsigned char a;
    if (read(STDIN_FILENO, &a, 1) != 1) return K_ESC;

    if (a == 'O') {
        if (poll(&pf, 1, 50) <= 0) return K_ESC;
        unsigned char b;
        if (read(STDIN_FILENO, &b, 1) != 1) return K_ESC;
        switch (b) {
            case 'P': return K_F1; case 'Q': return K_F2;
            case 'R': return K_F3; case 'S': return K_F4;
            case 'H': return K_HOME; case 'F': return K_END;
            case 'A': return K_UP; case 'B': return K_DOWN;
            case 'C': return K_RIGHT; case 'D': return K_LEFT;
        }
        return K_ESC;
    }
    if (a != '[') return K_ESC;
    if (poll(&pf, 1, 50) <= 0) return K_ESC;
    unsigned char b;
    if (read(STDIN_FILENO, &b, 1) != 1) return K_ESC;

    if (b == '<') {                 /* SGR mouse: ESC [ < btn ; x ; y (M|m) */
        int v[3] = {0, 0, 0}, idx = 0;
        for (;;) {
            if (poll(&pf, 1, 50) <= 0) return K_ESC;
            unsigned char t;
            if (read(STDIN_FILENO, &t, 1) != 1) return K_ESC;
            if (t >= '0' && t <= '9') { if (idx < 3) v[idx] = v[idx] * 10 + (t - '0'); }
            else if (t == ';') { if (++idx > 2) return K_ESC; }
            else if (t == 'M' || t == 'm') { g_mrelease = (t == 'm'); break; }
            else return K_ESC;
        }
        g_mbtn = v[0]; g_mx = v[1]; g_my = v[2];
        return K_MOUSE;
    }

    if (b >= '0' && b <= '9') {
        int par[3] = {0, 0, 0}, np = 0;
        par[0] = b - '0';
        unsigned char fin;
        for (;;) {
            if (poll(&pf, 1, 50) <= 0) return K_ESC;
            unsigned char t;
            if (read(STDIN_FILENO, &t, 1) != 1) return K_ESC;
            if (t >= '0' && t <= '9') { if (par[np] < 9999) par[np] = par[np] * 10 + (t - '0'); }
            else if (t == ';') { if (np < 2) np++; }
            else { fin = t; break; }
        }
        int mod = (np >= 1) ? par[1] : 0;       /* 2 = Shift, 3 = Alt, 5 = Ctrl */
        if (fin == '~') {
            switch (par[0]) {
                case 1: case 7: return K_HOME;
                case 4: case 8: return K_END;
                case 3:  return K_DEL;
                case 5:  return K_PGUP;
                case 6:  return K_PGDN;
                case 11: return K_F1;  case 12: return K_F2;
                case 13: return K_F3;  case 14: return K_F4;
                case 15: return K_F5;  case 17: return K_F6;
                case 18: return K_F7;  case 19: return K_F8;
                case 20: return K_F9;  case 21: return K_F10;
            }
            return K_ESC;
        }
        switch (fin) {
            case 'A': return mod == 2 ? K_SUP    : mod == 5 ? K_CUP    : K_UP;
            case 'B': return mod == 2 ? K_SDOWN  : mod == 5 ? K_CDOWN  : K_DOWN;
            case 'C': return mod == 2 ? K_SRIGHT : mod == 5 ? K_CRIGHT : K_RIGHT;
            case 'D': return mod == 2 ? K_SLEFT  : mod == 5 ? K_CLEFT  : K_LEFT;
            case 'H': return mod == 2 ? K_SHOME : K_HOME;
            case 'F': return mod == 2 ? K_SEND  : K_END;
        }
        return K_ESC;
    }
    switch (b) {
        case 'A': return K_UP;   case 'B': return K_DOWN;
        case 'C': return K_RIGHT; case 'D': return K_LEFT;
        case 'H': return K_HOME; case 'F': return K_END;
    }
    return K_ESC;
}

/* ------------------------------------------------------------------ */
/* Document model                                                     */
/* ------------------------------------------------------------------ */
typedef struct { char *b; int len, cap; } Line;

enum { ED_TYPE = 1, ED_ERASE, ED_OTHER };   /* undo coalescing kinds */

static struct {
    Line *line;
    int   nlines, cap;
    int   cx, cy;            /* cursor: byte offset cx within line cy */
    int   rowoff, coloff;    /* scroll (coloff in display columns) */
    int   goalcol;           /* desired display column for vertical moves */
    char  path[PATH_MAX];
    int   named;
    int   dirty;
    int   sel;               /* selection active */
    int   mark;              /* mark mode: plain arrows extend the selection
                                (for terminals that don't send Shift+arrow, e.g. macOS Terminal.app) */
    int   ax, ay;            /* selection anchor */
    char *clip; int cliplen;
    char  find[256];
    int   mdown;             /* mouse button held (dragging) */
} E;

static char g_msg[256] = "";
static int  g_running = 1;
static void msg(const char *fmt, ...) {
    va_list ap; va_start(ap, fmt);
    vsnprintf(g_msg, sizeof g_msg, fmt, ap);
    va_end(ap);
}

static void line_ensure(Line *l, int need) {
    if (need + 1 > l->cap) {
        int nc = l->cap ? l->cap * 2 : 16;
        while (nc < need + 1) nc *= 2;
        l->b = xrealloc(l->b, nc); l->cap = nc;
    }
}
static void doc_ensure(int need) {
    if (need > E.cap) {
        int nc = E.cap ? E.cap * 2 : 64;
        while (nc < need) nc *= 2;
        E.line = xrealloc(E.line, nc * sizeof(Line)); E.cap = nc;
    }
}
static void doc_insert_line(int at, const char *s, int n) {
    doc_ensure(E.nlines + 1);
    memmove(&E.line[at + 1], &E.line[at], (E.nlines - at) * sizeof(Line));
    Line *l = &E.line[at]; l->b = NULL; l->len = 0; l->cap = 0;
    line_ensure(l, n);
    memcpy(l->b, s, n); l->len = n; l->b[n] = 0;
    E.nlines++;
}
static void doc_remove_line(int at) {
    free(E.line[at].b);
    memmove(&E.line[at], &E.line[at + 1], (E.nlines - at - 1) * sizeof(Line));
    E.nlines--;
}
static void line_insert(Line *l, int at, const char *s, int n) {
    line_ensure(l, l->len + n);
    memmove(l->b + at + n, l->b + at, l->len - at);
    memcpy(l->b + at, s, n);
    l->len += n; l->b[l->len] = 0;
}
static void line_delete(Line *l, int at, int n) {
    memmove(l->b + at, l->b + at + n, l->len - at - n);
    l->len -= n; l->b[l->len] = 0;
}

static char *doc_text(int *outlen) {
    int total = 1;
    for (int i = 0; i < E.nlines; i++) total += E.line[i].len + 1;
    char *s = xmalloc(total); int p = 0;
    for (int i = 0; i < E.nlines; i++) {
        memcpy(s + p, E.line[i].b, E.line[i].len); p += E.line[i].len;
        if (i < E.nlines - 1) s[p++] = '\n';
    }
    s[p] = 0; if (outlen) *outlen = p; return s;
}
static void doc_set_text(const char *s, int len) {
    for (int i = 0; i < E.nlines; i++) free(E.line[i].b);
    free(E.line); E.line = NULL; E.cap = 0; E.nlines = 0;
    int start = 0;
    for (;;) {
        const char *nl = memchr(s + start, '\n', len - start);
        int end = nl ? (int)(nl - s) : len;
        int seg = end;
        if (seg > start && s[seg - 1] == '\r') seg--;   /* strip CR of a CRLF line */
        doc_insert_line(E.nlines, s + start, seg - start);
        if (!nl) break;
        start = end + 1;
        if (start > len) break;
    }
    if (E.nlines == 0) doc_insert_line(0, "", 0);
}

/* ------------------------------------------------------------------ */
/* Column / byte conversions                                          */
/* ------------------------------------------------------------------ */
static int col_of(Line *l, int cx) {
    int col = 0, i = 0;
    while (i < cx && i < l->len) {
        int bl, w = char_w(l->b + i, l->len - i, col, &bl);
        col += w; i += bl;
    }
    return col;
}
static int cx_of_col(Line *l, int want) {
    int col = 0, i = 0;
    while (i < l->len) {
        if (col >= want) break;
        int bl, w = char_w(l->b + i, l->len - i, col, &bl);
        col += w; i += bl;
    }
    return i;
}
static int prev_cx(Line *l, int cx) {
    if (cx <= 0) return 0;
    cx--;
    if (g_enc == ENC_UTF8)
        while (cx > 0 && ((unsigned char)l->b[cx] & 0xC0) == 0x80) cx--;
    return cx;
}
static int next_cx(Line *l, int cx) {
    if (cx >= l->len) return l->len;
    cx += enc_charlen(l->b + cx);
    if (cx > l->len) cx = l->len;
    return cx;
}
static void clamp_cursor(void) {
    if (E.cy < 0) E.cy = 0;
    if (E.cy > E.nlines - 1) E.cy = E.nlines - 1;
    Line *l = &E.line[E.cy];
    if (E.cx < 0) E.cx = 0;
    if (E.cx > l->len) E.cx = l->len;
    if (g_enc == ENC_UTF8)
        while (E.cx > 0 && ((unsigned char)l->b[E.cx] & 0xC0) == 0x80) E.cx--;
}

/* ------------------------------------------------------------------ */
/* Undo / redo (whole-buffer snapshots, coalesced runs)               */
/* ------------------------------------------------------------------ */
typedef struct { char *text; int len, cx, cy; } Snap;
#define USTACK 256
static Snap u_st[USTACK]; static int u_n = 0;
static Snap r_st[USTACK]; static int r_n = 0;
static int  last_kind = 0;

static void snap_push(Snap *st, int *n, char *text, int len, int cx, int cy) {
    if (*n == USTACK) { free(st[0].text); memmove(st, st + 1, (USTACK - 1) * sizeof(Snap)); (*n)--; }
    st[*n].text = text; st[*n].len = len; st[*n].cx = cx; st[*n].cy = cy; (*n)++;
}
static void redo_clear(void) {
    for (int i = 0; i < r_n; i++) free(r_st[i].text);
    r_n = 0;
}
/* call before a mutating edit; coalesces consecutive same-kind edits */
static void begin_edit(int kind) {
    if (!((kind == ED_TYPE || kind == ED_ERASE) && kind == last_kind)) {
        int len; char *t = doc_text(&len);
        snap_push(u_st, &u_n, t, len, E.cx, E.cy);
        redo_clear();
    }
    last_kind = (kind == ED_TYPE || kind == ED_ERASE) ? kind : 0;
    E.dirty = 1;
}
static void break_undo(void) { last_kind = 0; }

static void do_undo(void) {
    if (u_n == 0) { msg("Nothing to undo"); return; }
    int len; char *cur = doc_text(&len);
    snap_push(r_st, &r_n, cur, len, E.cx, E.cy);
    Snap s = u_st[--u_n];
    doc_set_text(s.text, s.len);
    E.cx = s.cx; E.cy = s.cy; free(s.text);
    clamp_cursor(); E.dirty = 1; last_kind = 0;
    msg("Undo");
}
static void do_redo(void) {
    if (r_n == 0) { msg("Nothing to redo"); return; }
    int len; char *cur = doc_text(&len);
    snap_push(u_st, &u_n, cur, len, E.cx, E.cy);
    Snap s = r_st[--r_n];
    doc_set_text(s.text, s.len);
    E.cx = s.cx; E.cy = s.cy; free(s.text);
    clamp_cursor(); E.dirty = 1; last_kind = 0;
    msg("Redo");
}

/* ------------------------------------------------------------------ */
/* Selection                                                          */
/* ------------------------------------------------------------------ */
static void sel_norm(int *y0, int *x0, int *y1, int *x1) {
    if (E.ay < E.cy || (E.ay == E.cy && E.ax <= E.cx)) {
        *y0 = E.ay; *x0 = E.ax; *y1 = E.cy; *x1 = E.cx;
    } else {
        *y0 = E.cy; *x0 = E.cx; *y1 = E.ay; *x1 = E.ax;
    }
}
static char *sel_text(int *outlen) {
    int y0, x0, y1, x1; sel_norm(&y0, &x0, &y1, &x1);
    Buf b = {0};
    if (y0 == y1) {
        buf_add(&b, E.line[y0].b + x0, x1 - x0);
    } else {
        buf_add(&b, E.line[y0].b + x0, E.line[y0].len - x0); buf_s(&b, "\n");
        for (int i = y0 + 1; i < y1; i++) { buf_add(&b, E.line[i].b, E.line[i].len); buf_s(&b, "\n"); }
        buf_add(&b, E.line[y1].b, x1);
    }
    if (outlen) *outlen = (int)b.len;
    return b.p ? b.p : xstrdup("");
}
static void sel_delete(void) {
    int y0, x0, y1, x1; sel_norm(&y0, &x0, &y1, &x1);
    if (y0 == y1) {
        line_delete(&E.line[y0], x0, x1 - x0);
    } else {
        Line *L = &E.line[y0];
        L->len = x0; L->b[x0] = 0;
        line_insert(L, L->len, E.line[y1].b + x1, E.line[y1].len - x1);
        for (int i = y1; i > y0; i--) doc_remove_line(i);
    }
    E.cy = y0; E.cx = x0; E.sel = 0; E.mark = 0;
}
static void sel_start(int extend) {
    if (extend) { if (!E.sel) { E.sel = 1; E.ax = E.cx; E.ay = E.cy; } }
    else E.sel = 0;
}

/* ------------------------------------------------------------------ */
/* Text insertion (clipboard / paste, may contain newlines)           */
/* ------------------------------------------------------------------ */
static void insert_text(const char *s, int n) {
    int i = 0;
    for (;;) {
        const char *nl = memchr(s + i, '\n', n - i);
        int end = nl ? (int)(nl - s) : n;
        line_insert(&E.line[E.cy], E.cx, s + i, end - i);
        E.cx += end - i;
        if (!nl) break;
        Line *L = &E.line[E.cy];
        int taillen = L->len - E.cx;
        doc_insert_line(E.cy + 1, L->b + E.cx, taillen);
        L->len = E.cx; L->b[E.cx] = 0;
        E.cy++; E.cx = 0;
        i = end + 1;
    }
}

/* ------------------------------------------------------------------ */
/* Editing operations                                                 */
/* ------------------------------------------------------------------ */
static void ed_insert_byte(int c) {
    if (E.sel) { begin_edit(ED_OTHER); sel_delete(); }
    else begin_edit(ED_TYPE);
    char ch = (char)c;
    line_insert(&E.line[E.cy], E.cx, &ch, 1);
    E.cx++;
    E.goalcol = -1;
}
static void ed_insert_tab(void) {
    if (!g_expandtab) { ed_insert_byte('\t'); return; }   /* a real tab */
    int col = col_of(&E.line[E.cy], E.cx);
    int spaces = g_tabw - (col % g_tabw);                 /* fill to the next tab stop */
    if (E.sel) { begin_edit(ED_OTHER); sel_delete(); }
    else begin_edit(ED_TYPE);
    for (int i = 0; i < spaces; i++) { char sp = ' '; line_insert(&E.line[E.cy], E.cx, &sp, 1); E.cx++; }
    E.goalcol = -1;
}
static void ed_newline(void) {
    if (E.sel) { begin_edit(ED_OTHER); sel_delete(); }
    else begin_edit(ED_OTHER);
    Line *L = &E.line[E.cy];
    int taillen = L->len - E.cx;
    doc_insert_line(E.cy + 1, L->b + E.cx, taillen);
    L->len = E.cx; L->b[E.cx] = 0;
    E.cy++; E.cx = 0; E.goalcol = -1;
}
static void ed_backspace(void) {
    if (E.sel) { begin_edit(ED_OTHER); sel_delete(); E.goalcol = -1; return; }
    if (E.cx == 0 && E.cy == 0) return;
    begin_edit(ED_ERASE);
    if (E.cx > 0) {
        int p = prev_cx(&E.line[E.cy], E.cx);
        line_delete(&E.line[E.cy], p, E.cx - p);
        E.cx = p;
    } else {
        int prevlen = E.line[E.cy - 1].len;
        line_insert(&E.line[E.cy - 1], prevlen, E.line[E.cy].b, E.line[E.cy].len);
        doc_remove_line(E.cy);
        E.cy--; E.cx = prevlen;
    }
    E.goalcol = -1;
}
static void ed_delete(void) {
    if (E.sel) { begin_edit(ED_OTHER); sel_delete(); E.goalcol = -1; return; }
    Line *L = &E.line[E.cy];
    if (E.cx < L->len) {
        begin_edit(ED_ERASE);
        int nx = next_cx(L, E.cx);
        line_delete(L, E.cx, nx - E.cx);
    } else if (E.cy < E.nlines - 1) {
        begin_edit(ED_ERASE);
        line_insert(L, L->len, E.line[E.cy + 1].b, E.line[E.cy + 1].len);
        doc_remove_line(E.cy + 1);
    }
    E.goalcol = -1;
}
static void ed_copy(void) {
    free(E.clip);
    if (E.sel) { int n; E.clip = sel_text(&n); E.cliplen = n; msg("Copied selection"); }
    else {
        Line *L = &E.line[E.cy];
        if (E.cx < L->len) {                 /* no selection: the char under the cursor */
            int n = next_cx(L, E.cx) - E.cx;
            E.clip = xmalloc(n + 1);
            memcpy(E.clip, L->b + E.cx, n); E.clip[n] = 0; E.cliplen = n;
            msg("Copied 1 char");
        } else {                             /* end of line: the line break */
            E.clip = xstrdup("\n"); E.cliplen = 1;
            msg("Copied newline");
        }
    }
    osc52_copy(E.clip, E.cliplen);           /* also to the system clipboard */
}
static void ed_cut(void) {
    free(E.clip);
    if (E.sel) {
        int n; E.clip = sel_text(&n); E.cliplen = n;
        begin_edit(ED_OTHER); sel_delete();
        msg("Cut selection");
    } else {                                /* no selection: cut current line */
        begin_edit(ED_OTHER);
        Line *L = &E.line[E.cy];
        E.cliplen = L->len + 1;
        E.clip = xmalloc(E.cliplen + 1);
        memcpy(E.clip, L->b, L->len); E.clip[L->len] = '\n'; E.clip[E.cliplen] = 0;
        if (E.nlines == 1) { L->len = 0; L->b[0] = 0; }
        else { doc_remove_line(E.cy); if (E.cy >= E.nlines) E.cy = E.nlines - 1; }
        E.cx = 0;
        msg("Cut line");
    }
    osc52_copy(E.clip, E.cliplen);           /* also to the system clipboard */
    E.goalcol = -1;
}
static void ed_paste(void) {
    if (!E.clip || E.cliplen == 0) { msg("Clipboard empty"); return; }
    begin_edit(ED_OTHER);
    if (E.sel) sel_delete();
    insert_text(E.clip, E.cliplen);
    E.goalcol = -1;
}
static void ed_dup_line(void) {
    begin_edit(ED_OTHER);
    Line *L = &E.line[E.cy];
    doc_insert_line(E.cy + 1, L->b, L->len);
    E.cy++;
    E.goalcol = -1;
}
static void ed_select_all(void) {
    E.ay = 0; E.ax = 0;
    E.cy = E.nlines - 1; E.cx = E.line[E.cy].len;
    E.sel = 1;
}

/* ------------------------------------------------------------------ */
/* Movement                                                           */
/* ------------------------------------------------------------------ */
static void move_left(int extend) {
    if (!extend && E.sel) {                  /* collapse to the left edge */
        int y0, x0, y1, x1; sel_norm(&y0, &x0, &y1, &x1);
        E.cy = y0; E.cx = x0; E.sel = 0; E.goalcol = -1; return;
    }
    sel_start(extend);
    if (E.cx > 0) E.cx = prev_cx(&E.line[E.cy], E.cx);
    else if (E.cy > 0) { E.cy--; E.cx = E.line[E.cy].len; }
    E.goalcol = -1;
}
static void move_right(int extend) {
    if (!extend && E.sel) {                  /* collapse to the right edge */
        int y0, x0, y1, x1; sel_norm(&y0, &x0, &y1, &x1);
        E.cy = y1; E.cx = x1; E.sel = 0; E.goalcol = -1; return;
    }
    sel_start(extend);
    if (E.cx < E.line[E.cy].len) E.cx = next_cx(&E.line[E.cy], E.cx);
    else if (E.cy < E.nlines - 1) { E.cy++; E.cx = 0; }
    E.goalcol = -1;
}
static void move_vert(int dir, int extend) {
    sel_start(extend);
    int col = (E.goalcol >= 0) ? E.goalcol : col_of(&E.line[E.cy], E.cx);
    E.goalcol = col;
    int ny = E.cy + dir;
    if (ny < 0) ny = 0;
    if (ny > E.nlines - 1) ny = E.nlines - 1;
    E.cy = ny;
    E.cx = cx_of_col(&E.line[E.cy], col);
}
static void move_home(int extend) { sel_start(extend); E.cx = 0; E.goalcol = -1; }
static void move_end(int extend)  { sel_start(extend); E.cx = E.line[E.cy].len; E.goalcol = -1; }

static int is_word(unsigned char c) { return isalnum(c) || c == '_' || c >= 0x80; }
static void move_word(int dir, int extend) {
    sel_start(extend);
    Line *l = &E.line[E.cy];
    if (dir > 0) {
        int i = E.cx;
        if (i >= l->len) { move_right(extend); return; }
        while (i < l->len && !is_word((unsigned char)l->b[i])) i += utf8_len((unsigned char)l->b[i]);
        while (i < l->len &&  is_word((unsigned char)l->b[i])) i += utf8_len((unsigned char)l->b[i]);
        E.cx = i;
    } else {
        int i = E.cx;
        if (i <= 0) { move_left(extend); return; }
        i = prev_cx(l, i);
        while (i > 0 && !is_word((unsigned char)l->b[i])) i = prev_cx(l, i);
        while (i > 0 &&  is_word((unsigned char)l->b[prev_cx(l, i)])) i = prev_cx(l, i);
        E.cx = i;
    }
    E.goalcol = -1;
}

/* ------------------------------------------------------------------ */
/* File I/O                                                           */
/* ------------------------------------------------------------------ */
/* heuristic: is the buffer valid UTF-8? (pure ASCII counts as yes) */
static int looks_utf8(const char *s, int n) {
    int i = 0;
    while (i < n) {
        unsigned char c = (unsigned char)s[i];
        if (c < 0x80) { i++; continue; }
        int need = c >= 0xF0 ? 3 : c >= 0xE0 ? 2 : c >= 0xC0 ? 1 : -1;
        if (need < 0 || i + need >= n) return 0;
        for (int j = 1; j <= need; j++)
            if (((unsigned char)s[i + j] & 0xC0) != 0x80) return 0;
        i += need + 1;
    }
    return 1;
}
static void load_file(const char *path) {
    snprintf(E.path, sizeof E.path, "%s", path);
    E.named = 1;
    int fd = open(path, O_RDONLY);
    if (fd < 0) {
        doc_set_text("", 0);
        E.cx = E.cy = 0; E.rowoff = E.coloff = 0; E.dirty = 0;
        msg(errno == ENOENT ? "New file" : "Open failed: %s", strerror(errno));
        return;
    }
    Buf b = {0};
    char tmp[65536]; ssize_t r;
    while ((r = read(fd, tmp, sizeof tmp)) > 0) buf_add(&b, tmp, r);
    close(fd);
    int len = (int)b.len;
    g_crlf = 0;                                     /* detect Windows line endings */
    const char *firstnl = b.p ? memchr(b.p, '\n', len) : NULL;
    if (firstnl && firstnl > b.p && firstnl[-1] == '\r') g_crlf = 1;
    if (!g_enc_forced)                              /* auto-pick encoding for display */
        g_enc = looks_utf8(b.p ? b.p : "", len) ? ENC_UTF8 : ENC_CP1252;
    if (len > 0 && b.p[len - 1] == '\n') len--;     /* drop one trailing newline */
    doc_set_text(b.p ? b.p : "", len);
    free(b.p);
    E.cx = E.cy = 0; E.rowoff = E.coloff = 0; E.dirty = 0;
    /* no startup message: the status line already shows the name, line count,
       line ending and encoding, so a banner here would just be redundant. */
}

static int overlay_prompt(const char *title, char *buf, size_t bufsz, const char *initial);

static int do_save(void) {
    if (!E.named || E.path[0] == 0) {
        char p[PATH_MAX] = "";
        if (!overlay_prompt("Save as", p, sizeof p, "") || !p[0]) { msg("Save cancelled"); return 0; }
        snprintf(E.path, sizeof E.path, "%s", p); E.named = 1;
    }
    int fd = open(E.path, O_WRONLY | O_CREAT | O_TRUNC, 0644);
    if (fd < 0) { msg("Save failed: %s", strerror(errno)); return 0; }
    Buf b = {0};
    const char *eol = g_crlf ? "\r\n" : "\n";
    for (int i = 0; i < E.nlines; i++) { buf_add(&b, E.line[i].b, E.line[i].len); buf_s(&b, eol); }
    ssize_t w = write(fd, b.p ? b.p : "", b.len);
    int ok = (w == (ssize_t)b.len);
    close(fd); free(b.p);
    if (!ok) { msg("Save failed: short write"); return 0; }
    E.dirty = 0; break_undo();
    char base[256]; path_base(E.path, base, sizeof base);
    msg("Saved \"%s\" (%d line%s)", base, E.nlines, E.nlines == 1 ? "" : "s");
    return 1;
}

/* ------------------------------------------------------------------ */
/* Search                                                             */
/* ------------------------------------------------------------------ */
static int line_find_ci(Line *l, int from, const char *needle) {
    int nl = (int)strlen(needle);
    if (nl == 0) return -1;
    for (int i = from; i + nl <= l->len; i++) {
        int j = 0;
        while (j < nl && tolower((unsigned char)l->b[i + j]) == tolower((unsigned char)needle[j])) j++;
        if (j == nl) return i;
    }
    return -1;
}
static void find_from(int sy, int sx) {
    if (!E.find[0]) return;
    int nl = (int)strlen(E.find);
    for (int d = 0; d <= E.nlines; d++) {
        int ln = (sy + d) % E.nlines;
        int start = (d == 0) ? sx : 0;
        int pos = line_find_ci(&E.line[ln], start, E.find);
        if (pos >= 0) {
            E.cy = ln; E.ay = ln; E.ax = pos;
            E.cx = pos + nl; E.sel = 1; E.goalcol = -1;
            msg("Found \"%s\"", E.find);
            return;
        }
        if (d == E.nlines) break;
    }
    msg("\"%s\" not found", E.find);
}
static void ed_find(void) {
    char q[256]; snprintf(q, sizeof q, "%s", E.find);
    if (!overlay_prompt("Find", q, sizeof q, E.find) || !q[0]) return;
    snprintf(E.find, sizeof E.find, "%s", q);
    find_from(E.cy, E.cx);
}
static void ed_find_next(void) {
    if (!E.find[0]) { ed_find(); return; }
    find_from(E.cy, E.cx);
}
static void ed_goto(void) {
    char q[32] = "";
    if (!overlay_prompt("Go to line", q, sizeof q, "") || !q[0]) return;
    int n = atoi(q);
    if (n < 1) n = 1;
    if (n > E.nlines) n = E.nlines;
    E.cy = n - 1; E.cx = 0; E.sel = 0; E.goalcol = -1;
    break_undo();
}

/* ------------------------------------------------------------------ */
/* Overlays (window prompts)                                          */
/* ------------------------------------------------------------------ */
static void overlay_frame(Buf *o, int bw, int bh, int *bx, int *by) {
    if (bw > g_cols) bw = g_cols;
    if (bh > g_rows) bh = g_rows;
    int x = (g_cols - bw) / 2 + 1, y = (g_rows - bh) / 2 + 1;
    if (x < 1) x = 1;
    if (y < 1) y = 1;
    const char *tl = g_utf8 ? "╭" : "+", *tr = g_utf8 ? "╮" : "+";
    const char *bl = g_utf8 ? "╰" : "+", *brc = g_utf8 ? "╯" : "+";
    const char *hz = g_utf8 ? "─" : "-", *vt = g_utf8 ? "│" : "|";
    buf_printf(o, "\x1b[%d;%dH\x1b[0m%s", y, x, tl);
    for (int i = 0; i < bw - 2; i++) buf_s(o, hz);
    buf_s(o, tr);
    for (int r = 1; r < bh - 1; r++) {
        buf_printf(o, "\x1b[%d;%dH%s", y + r, x, vt);
        for (int i = 0; i < bw - 2; i++) buf_s(o, " ");
        buf_s(o, vt);
    }
    buf_printf(o, "\x1b[%d;%dH%s", y + bh - 1, x, bl);
    for (int i = 0; i < bw - 2; i++) buf_s(o, hz);
    buf_s(o, brc);
    *bx = x; *by = y;
}
#define BTN_OK_W 6
#define BTN_CANCEL_W 10
static void draw_buttons(Buf *o, int bx, int bw, int btnrow, int focus,
                         int *okcol, int *cancelcol) {
    int oc = bx + 2;
    int cc = bx + bw - 2 - BTN_CANCEL_W;
    int fok = (focus == 0), fcn = (focus == 1);
    buf_printf(o, "\x1b[%d;%dH%s  OK  \x1b[0m", btnrow, oc,
               fok ? "\x1b[1;30;42m" : "\x1b[30;47m");
    buf_printf(o, "\x1b[%d;%dH%s  Cancel  \x1b[0m", btnrow, cc,
               fcn ? "\x1b[1;30;42m" : "\x1b[30;47m");
    if (okcol) *okcol = oc;
    if (cancelcol) *cancelcol = cc;
}
static int overlay_prompt(const char *title, char *buf, size_t bufsz, const char *initial) {
    snprintf(buf, bufsz, "%s", initial ? initial : "");
    size_t len = strlen(buf);
    size_t cpos = len;
    int focus = -1;
    int bw = 56, bh = 8;
    for (;;) {
        render();
        Buf o = {0};
        int bx, by, okcol, cancelcol;
        overlay_frame(&o, bw, bh, &bx, &by);
        int ix = bx + 2, fieldw = bw - 4, btnrow = by + 5;
        buf_printf(&o, "\x1b[%d;%dH\x1b[1;36m%s\x1b[0m", by + 1, ix, title);
        buf_printf(&o, "\x1b[%d;%dH", by + 3, ix);
        if (focus == -1) {
            char before[1024];
            size_t bl = cpos < sizeof before ? cpos : sizeof before - 1;
            memcpy(before, buf, bl); before[bl] = 0;
            int wbefore = buf_add_tail(&o, before, fieldw - 1);
            const char *after = buf + cpos;
            int cclen = after[0] ? utf8_len((unsigned char)after[0]) : 0;
            buf_s(&o, "\x1b[7m");
            if (cclen) buf_add(&o, after, cclen); else buf_s(&o, " ");
            buf_s(&o, "\x1b[0m");
            int rem = fieldw - wbefore - 1;
            if (rem > 0 && cclen) buf_add_trunc(&o, after + cclen, rem);
        } else {
            buf_add_tail(&o, buf, fieldw);
        }
        draw_buttons(&o, bx, bw, btnrow, focus == -1 ? 0 : focus, &okcol, &cancelcol);
        ssize_t w = write(STDOUT_FILENO, o.p, o.len); (void)w;
        free(o.p);

        int k = read_key();
        if (k == K_RESIZE) { get_size(); continue; }
        if (k == K_ESC || k == K_EOF) { g_resized = 1; return 0; }

        if (focus != -1) {
            if (k == K_ENTER || k == '\n' || k == ' ') { g_resized = 1; return focus == 0; }
            else if (k == K_LEFT)  focus = 0;
            else if (k == K_RIGHT) focus = 1;
            else if (k == K_TAB)   focus = (focus == 0) ? 1 : -1;
            else if (k == K_UP)    focus = -1;
            else if (k == K_MOUSE && !g_mrelease && (g_mbtn & 0x3) == 0 && g_my == btnrow) {
                if (g_mx >= okcol && g_mx < okcol + BTN_OK_W) { g_resized = 1; return 1; }
                if (g_mx >= cancelcol && g_mx < cancelcol + BTN_CANCEL_W) { g_resized = 1; return 0; }
            } else if (k >= 32 && k < 256 && len + 1 < bufsz) {
                focus = -1;
                memmove(buf + cpos + 1, buf + cpos, len - cpos + 1);
                buf[cpos] = (char)k; len++; cpos++;
            }
            continue;
        }

        if (k == K_ENTER || k == '\n') { g_resized = 1; return 1; }
        else if (k == K_DOWN || k == K_TAB) focus = 0;
        else if (k == K_LEFT)  { if (cpos > 0) { do { cpos--; } while (cpos > 0 && ((unsigned char)buf[cpos] & 0xC0) == 0x80); } }
        else if (k == K_RIGHT) { if (cpos < len) { cpos += utf8_len((unsigned char)buf[cpos]); if (cpos > len) cpos = len; } }
        else if (k == K_HOME)  cpos = 0;
        else if (k == K_END)   cpos = len;
        else if (k == K_BS || k == 8) {
            if (cpos > 0) {
                size_t s0 = cpos;
                do { s0--; } while (s0 > 0 && ((unsigned char)buf[s0] & 0xC0) == 0x80);
                memmove(buf + s0, buf + cpos, len - cpos + 1);
                len -= (cpos - s0); cpos = s0;
            }
        }
        else if (k == K_DEL) {
            if (cpos < len) {
                size_t nl = utf8_len((unsigned char)buf[cpos]);
                if (cpos + nl > len) nl = len - cpos;
                memmove(buf + cpos, buf + cpos + nl, len - cpos - nl + 1);
                len -= nl;
            }
        }
        else if (k == K_MOUSE && !g_mrelease && (g_mbtn & 0x3) == 0 && g_my == btnrow) {
            if (g_mx >= okcol && g_mx < okcol + BTN_OK_W) { g_resized = 1; return 1; }
            if (g_mx >= cancelcol && g_mx < cancelcol + BTN_CANCEL_W) { g_resized = 1; return 0; }
        }
        else if (k >= 32 && k < 256 && len + 1 < bufsz) {
            memmove(buf + cpos + 1, buf + cpos, len - cpos + 1);
            buf[cpos] = (char)k; len++; cpos++;
        }
    }
}
/* Three-way: returns 0 = first, 1 = second, -1 = cancel (Esc). */
static int choice_overlay(const char *title, const char *la, const char *lb) {
    char A[40], B[40];
    snprintf(A, sizeof A, "  %s  ", la);
    snprintf(B, sizeof B, "  %s  ", lb);
    int aw = (int)strlen(A), bw2 = (int)strlen(B);
    int bw = 52, bh = 7, focus = 0;
    for (;;) {
        render();
        Buf o = {0};
        int bx, by;
        overlay_frame(&o, bw, bh, &bx, &by);
        int ix = bx + 2, acol = ix, bcol = bx + bw - 2 - bw2, btnrow = by + 4;
        buf_printf(&o, "\x1b[%d;%dH\x1b[1;36m%s\x1b[0m", by + 1, ix, title);
        buf_printf(&o, "\x1b[%d;%dH%s%s\x1b[0m", btnrow, acol, focus == 0 ? "\x1b[1;30;42m" : "\x1b[30;47m", A);
        buf_printf(&o, "\x1b[%d;%dH%s%s\x1b[0m", btnrow, bcol, focus == 1 ? "\x1b[1;30;42m" : "\x1b[30;47m", B);
        ssize_t w = write(STDOUT_FILENO, o.p, o.len); (void)w;
        free(o.p);
        int k = read_key();
        if (k == K_RESIZE) { get_size(); continue; }
        if (k == K_ESC || k == K_EOF) { g_resized = 1; return -1; }
        if (k == K_ENTER || k == '\n' || k == ' ') { g_resized = 1; return focus; }
        else if (k == K_LEFT)  focus = 0;
        else if (k == K_RIGHT) focus = 1;
        else if (k == K_TAB) focus ^= 1;
        else if (k >= 32 && k < 127) {              /* first-letter shortcuts (y/n, s/q, ...) */
            int kk = tolower(k);
            if (kk == tolower((unsigned char)la[0])) { g_resized = 1; return 0; }
            if (kk == tolower((unsigned char)lb[0])) { g_resized = 1; return 1; }
        }
        else if (k == K_MOUSE && !g_mrelease && (g_mbtn & 0x3) == 0 && g_my == btnrow) {
            if (g_mx >= acol && g_mx < acol + aw)  { g_resized = 1; return 0; }
            if (g_mx >= bcol && g_mx < bcol + bw2) { g_resized = 1; return 1; }
        }
    }
}

/* prompt to save when there are unsaved changes; returns 1 = proceed, 0 = stay.
   Yes (y) = save then go, No (n) = discard and go, Esc = cancel. */
static int maybe_discard(const char *what) {
    (void)what;
    if (!E.dirty) return 1;
    int c = choice_overlay("Save changes before quitting?  (Esc = cancel)", "Yes", "No");
    if (c == -1) return 0;                 /* cancel -> stay */
    if (c == 0) return do_save();          /* yes -> save, proceed only if it worked */
    return 1;                              /* no -> discard */
}
/* ------------------------------------------------------------------ */
/* Rendering                                                          */
/* ------------------------------------------------------------------ */
static int gutter_w(void) {
    if (!g_mouse) return 0;        /* desktop-mouse mode: no gutter, so a native
                                      terminal drag-select doesn't copy line numbers */
    int d = 1, n = E.nlines;
    while (n >= 10) { n /= 10; d++; }
    if (d < 3) d = 3;
    return d + 1;                  /* digits + one trailing space */
}

static void render_text_row(Buf *out, int ln, int gw, int textw) {
    /* gutter (suppressed when gw == 0, i.e. desktop-mouse mode) */
    if (gw > 0) {
        int cur = (ln == E.cy);
        buf_s(out, cur ? C_GUTC : C_GUT);
        buf_printf(out, "%*d ", gw - 1, ln + 1);
        buf_s(out, C_RESET);
    }

    Line *l = &E.line[ln];

    /* selected byte interval [a,b) for this line, -1 = none */
    int a = -1, b = -1, fullsel = 0;
    if (E.sel) {
        int y0, x0, y1, x1; sel_norm(&y0, &x0, &y1, &x1);
        if (ln >= y0 && ln <= y1) {
            a = (ln == y0) ? x0 : 0;
            b = (ln == y1) ? x1 : l->len;
            if (ln < y1) fullsel = 1;            /* newline is part of selection */
        }
    }

    /* per-cell style: 0 = normal, 1 = selection (blue bg), 2 = cursor (reverse).
       The cursor is drawn only when nothing is selected, so the two never mix. */
    const char *STY[3] = { C_RESET, C_SEL, C_CUR };
    int style = 0, col = 0, i = 0;
    int left = E.coloff, right = E.coloff + textw;
    while (i < l->len) {
        int bl, w = char_w(l->b + i, l->len - i, col, &bl);
        int startcol = col;
        if (startcol + w <= left) { col += w; i += bl; continue; }
        if (startcol >= right) break;

        int sel_here = (a >= 0 && i >= a && i < b);
        int cursor_here = (!E.sel && ln == E.cy && i == E.cx);
        int want = sel_here ? 1 : cursor_here ? 2 : 0;
        if (want != style) { buf_s(out, STY[want]); style = want; }

        int leftclip = left - startcol; if (leftclip < 0) leftclip = 0;
        int vis = w - leftclip;
        if (startcol + w > right) vis -= (startcol + w - right);
        if (vis < 0) vis = 0;

        unsigned char ch = (unsigned char)l->b[i];
        if (ch == '\t' || ch < 0x20 || leftclip > 0 || startcol + w > right) {
            for (int s = 0; s < vis; s++) buf_s(out, " ");   /* tabs/clipped/control as spaces */
        } else {
            emit_char(out, l->b + i, bl);
        }
        col += w; i += bl;
    }
    /* a block at the line end: cursor (no selection) or the selected newline */
    int tail = 0;
    if (!E.sel && ln == E.cy && E.cx >= l->len) tail = 2;
    else if (fullsel) tail = 1;
    if (tail && col >= left && col < right) {
        if (tail != style) { buf_s(out, STY[tail]); style = tail; }
        buf_s(out, " ");
    }
    if (style) buf_s(out, C_RESET);
    buf_s(out, "\x1b[K\r\n");
}

/* clickable key-bar regions, filled in during render() */
typedef struct { int col, w, act; } KbHit;
static KbHit g_kbhit[16];
static int   g_kbhit_n;

static void render(void) {
    int W = g_cols, H = g_rows;
    int body = H - 3;                       /* header + status + keybar */
    if (body < 1) body = 1;
    int gw = gutter_w();
    int textw = W - gw; if (textw < 1) textw = 1;

    /* keep cursor visible */
    if (E.cy < E.rowoff) E.rowoff = E.cy;
    if (E.cy >= E.rowoff + body) E.rowoff = E.cy - body + 1;
    if (E.rowoff < 0) E.rowoff = 0;
    int curcol = col_of(&E.line[E.cy], E.cx);
    if (curcol < E.coloff) E.coloff = curcol;
    if (curcol >= E.coloff + textw) E.coloff = curcol - textw + 1;
    if (E.coloff < 0) E.coloff = 0;

    Buf out = {0};
    buf_s(&out, "\x1b[H");

    /* header bar */
    {
        char disp[PATH_MAX];
        abbrev_home(E.named ? E.path : "[No Name]", disp, sizeof disp);
        char head[PATH_MAX + 32];
        snprintf(head, sizeof head, " litefe - %s%s", disp, E.dirty ? "  *" : "");
        buf_s(&out, "\x1b[30;46m");
        int used = buf_add_trunc(&out, head, W);
        buf_pad(&out, W - used);
        buf_s(&out, C_RESET);
        buf_s(&out, "\x1b[K\r\n");
    }

    /* body */
    for (int r = 0; r < body; r++) {
        int ln = E.rowoff + r;
        if (ln < E.nlines) {
            render_text_row(&out, ln, gw, textw);
        } else {
            if (gw > 0) {                        /* no ~ in desktop mode, so a native
                                                    drag-select copies clean empty lines */
                buf_s(&out, C_GUT);
                buf_printf(&out, "%*s ", gw - 1, "~");
                buf_s(&out, C_RESET);
            }
            buf_s(&out, "\x1b[K\r\n");
        }
    }

    /* status line */
    {
        Buf S = {0};
        /* left side: only transient messages (Copied/Saved/...); the file name
           already lives in the header bar, so don't repeat it here. */
        if (g_msg[0]) { buf_add(&S, " ", 1); buf_s(&S, g_msg); }
        else buf_add(&S, " ", 1);
        char right[160];
        snprintf(right, sizeof right, "Ln %d/%d  Col %d  %s  %s ",
                 E.cy + 1, E.nlines, curcol + 1,
                 g_crlf ? "CRLF" : "LF", enc_name());
        char selinfo[48] = "";
        if (E.sel) { int n; char *t = sel_text(&n); free(t);
                     snprintf(selinfo, sizeof selinfo, "%s[sel %d] ", E.mark ? "MARK " : "", n); }
        else if (E.mark) snprintf(selinfo, sizeof selinfo, "MARK ");

        buf_s(&out, "\x1b[30;46m");          /* same colour as the header bar */
        char rfull[220];
        snprintf(rfull, sizeof rfull, "%s%s", selinfo, right);
        int lwid = str_width(S.p ? S.p : "");
        int rwid = str_width(rfull);
        Buf F = {0};
        if (lwid + rwid + 1 <= W) {
            buf_s(&F, S.p ? S.p : "");
            buf_pad(&F, W - lwid - rwid);
            buf_s(&F, rfull);
        } else {
            buf_add_trunc(&F, S.p ? S.p : "", W);
        }
        buf_add(&out, F.p ? F.p : "", F.len);
        buf_s(&out, "\x1b[0m\x1b[K\r\n");
        free(S.p); free(F.p);
    }

    /* key bar */
    {
        static const struct { const char *key, *lab; int act; } KB[] = {
            {"^S","Save",19},{"^F","Find",6},{"^G","Goto",7},
            {"^T","Sel",20},{"^B","Mode",2},{"^Z","Undo",26},{"^Y","Redo",25},
            {"^C","",3},{"^X","",24},{"^V","",22},{"^D","",4},{"^K","",11},{0,0,0}
        };
        const char *bar = "\x1b[1;36m";
        const char *dim = "\x1b[38;5;250m";
        const char *vt  = g_utf8 ? "│" : "|";
        int rightw = 6;                     /* "│ ^Q" + margin */
        int limit = W - rightw - 1;
        Buf K = {0};
        int col = 1;
        g_kbhit_n = 0;
        buf_s(&K, " ");
        for (int i = 0; KB[i].key; i++) {
            int klen = (int)strlen(KB[i].key), llen = (int)strlen(KB[i].lab);
            int w = klen + (llen ? 1 + llen : 0);     /* "^C" alone, or "^S Save" */
            int need = (i ? 3 : 0) + w;
            if (col + need > limit) break;
            if (i) { buf_s(&K, C_SEP); buf_s(&K, " "); buf_s(&K, vt); buf_s(&K, " "); buf_s(&K, C_RESET); col += 3; }
            g_kbhit[g_kbhit_n++] = (KbHit){ col + 1, w, KB[i].act };  /* screen col = consumed+1 */
            buf_s(&K, bar); buf_s(&K, KB[i].key); buf_s(&K, C_RESET);
            if (llen) { buf_s(&K, " "); buf_s(&K, dim); buf_s(&K, KB[i].lab); buf_s(&K, C_RESET); }
            col += w;
        }
        if (W - rightw - col > 0) { buf_pad(&K, W - rightw - col); col = W - rightw; }
        buf_s(&K, C_SEP); buf_s(&K, vt); buf_s(&K, " "); buf_s(&K, C_RESET);
        g_kbhit[g_kbhit_n++] = (KbHit){ col + 3, 2, 17 };   /* "^Q", after "│ " */
        buf_s(&K, bar); buf_s(&K, "^Q"); buf_s(&K, C_RESET);
        buf_add(&out, K.p ? K.p : "", K.len);
        buf_s(&out, "\x1b[K");
        free(K.p);
    }

    ssize_t w = write(STDOUT_FILENO, out.p, out.len); (void)w;
    free(out.p);
}

/* ------------------------------------------------------------------ */
/* Help                                                               */
/* ------------------------------------------------------------------ */
static void show_help(void) {
    static const char *h[] = {
        "  litefe  -  minimal text editor",
        "",
        "  Ctrl-S  save            Ctrl-Q  quit",
        "  Ctrl-G  go to line      Ctrl-H  this help",
        "  Ctrl-F  find            Ctrl-N / F3  find next",
        "",
        "  Ctrl-C  copy            Ctrl-X  cut",
        "  Ctrl-V  paste           Ctrl-A  select all",
        "  Ctrl-Z  undo            Ctrl-Y  redo",
        "  Ctrl-D  duplicate line  Ctrl-K  cut line",
        "",
        "  arrows / Home / End / PgUp / PgDn   move",
        "  Shift + arrows / Home / End         select",
        "  Ctrl + Left / Right                 jump word",
        "  Ctrl-T set mark, then move to select (works",
        "         when the terminal eats Shift+arrow, e.g.",
        "         macOS Terminal.app); Esc cancels the mark.",
        "",
        "  Ctrl-B toggles the mouse mode:",
        "    Desktop (default): the terminal owns the mouse,",
        "      so native drag-select / right-click menu work;",
        "      line numbers are hidden so a copy stays clean.",
        "    In-app: click = place cursor, drag = select,",
        "      wheel = scroll, line numbers shown.",
        "  No selection: Ctrl-C copies the char under the",
        "         cursor; Ctrl-K cuts the whole line.",
        "  Copy/cut also go to the system clipboard (OSC 52).",
        "",
        "  Tab width: $LITEFE_TAB (default 4); $LITEFE_EXPANDTAB=1",
        "  inserts spaces. CRLF/LF is detected and kept.",
        "  Ctrl-E cycles the encoding view: UTF-8 / Latin-1 /",
        "  CP1252 (Windows ANSI). $LITEFE_ENC presets it.",
        "",
        "  -- press any key --",
        NULL
    };
    Buf b = {0};
    buf_s(&b, "\x1b[2J\x1b[H");
    for (int i = 0; h[i]; i++) {
        buf_s(&b, i == 0 ? "\x1b[1;36m" : "\x1b[0m");
        buf_s(&b, h[i]);
        buf_s(&b, "\x1b[0m\r\n");
    }
    ssize_t r = write(STDOUT_FILENO, b.p, b.len); (void)r;
    free(b.p);
    read_key();
    g_resized = 1;
}

/* ------------------------------------------------------------------ */
/* Mouse                                                              */
/* ------------------------------------------------------------------ */
static void mouse_to_pos(int *ly, int *lx) {
    int gw = gutter_w();
    int row = g_my - 2;                     /* body starts at screen row 2 */
    if (row < 0) row = 0;
    int body = g_rows - 3; if (body < 1) body = 1;
    if (row >= body) row = body - 1;
    int ln = E.rowoff + row;
    if (ln < 0) ln = 0;
    if (ln > E.nlines - 1) ln = E.nlines - 1;
    int want = (g_mx - 1) - gw + E.coloff;
    if (want < 0) want = 0;
    *ly = ln;
    *lx = cx_of_col(&E.line[ln], want);
}
static void dispatch_key(int k);
static void handle_mouse(void) {
    if (g_mbtn & 64) {                       /* wheel */
        int dir = (g_mbtn & 1) ? 1 : -1;
        E.cy += dir * 3;
        clamp_cursor();
        E.goalcol = -1; E.sel = 0;
        return;
    }
    int motion = g_mbtn & 0x20;
    int btn = g_mbtn & 0x3;
    if (motion) {
        if (E.mdown && btn == 0) {           /* dragging with left button */
            int ly, lx; mouse_to_pos(&ly, &lx);
            if (!E.sel && (ly != E.ay || lx != E.ax)) E.sel = 1;
            E.cy = ly; E.cx = lx; E.goalcol = -1;
        }
        return;
    }
    if (g_mrelease) { E.mdown = 0; return; }

    if (btn == 0 && g_my == g_rows) {        /* click on the bottom key bar */
        for (int i = 0; i < g_kbhit_n; i++)
            if (g_mx >= g_kbhit[i].col && g_mx < g_kbhit[i].col + g_kbhit[i].w) {
                dispatch_key(g_kbhit[i].act);
                return;
            }
        return;
    }
    if (btn != 0) return;                    /* right/middle: leave to the terminal */
    if (g_my < 2 || g_my > g_rows - 3) return;   /* otherwise: only the text body */
    {                                        /* left press */
        int ly, lx; mouse_to_pos(&ly, &lx);
        E.cy = ly; E.cx = lx;
        E.ax = lx; E.ay = ly; E.sel = 0; E.mdown = 1;
        E.goalcol = -1; break_undo();
    }
}

static void dispatch_key(int k) {
    switch (k) {
        case K_RESIZE: g_resized = 1; break;
        case K_EOF: g_running = 0; break;
        case K_MOUSE: handle_mouse(); break;

        /* navigation — plain arrows extend the selection while mark mode is on */
        case K_LEFT:   move_left(E.mark);  break;
        case K_RIGHT:  move_right(E.mark); break;
        case K_UP:     move_vert(-1, E.mark); break;
        case K_DOWN:   move_vert(1, E.mark);  break;
        case K_SLEFT:  move_left(1);  break;
        case K_SRIGHT: move_right(1); break;
        case K_SUP:    move_vert(-1, 1); break;
        case K_SDOWN:  move_vert(1, 1);  break;
        case K_CLEFT:  move_word(-1, E.mark); break;
        case K_CRIGHT: move_word(1, E.mark);  break;
        case K_CUP:    move_vert(-1, E.mark); break;
        case K_CDOWN:  move_vert(1, E.mark);  break;
        case K_HOME:   move_home(E.mark);  break;
        case K_END:    move_end(E.mark);   break;
        case K_SHOME:  move_home(1);  break;
        case K_SEND:   move_end(1);   break;
        case K_PGUP:   { int b = g_rows - 4; for (int i = 0; i < b; i++) move_vert(-1, E.mark); break; }
        case K_PGDN:   { int b = g_rows - 4; for (int i = 0; i < b; i++) move_vert(1, E.mark);  break; }

        /* editing */
        case K_ENTER: case '\n': ed_newline(); break;
        case K_BS: ed_backspace(); break;          /* 127/DEL; byte 8 (^H) is Help below */
        case K_DEL: ed_delete(); break;
        case K_TAB: ed_insert_tab(); break;

        /* commands (control bytes) */
        case 19: do_save(); break;                 /* ^S */
        case 17: if (maybe_discard("Quit")) g_running = 0; break; /* ^Q */
        case 7:  ed_goto(); break;                 /* ^G */
        case 6:  ed_find(); break;                 /* ^F */
        case 14: case K_F3: ed_find_next(); break; /* ^N / F3 */
        case 3:  ed_copy(); E.mark = 0; break;     /* ^C */
        case 24: ed_cut();  E.mark = 0; break;     /* ^X */
        case 20:                                   /* ^T = set/clear mark (layout-independent) */
            if (E.mark || E.sel) { E.mark = 0; E.sel = 0; msg("Mark cleared"); }
            else { E.mark = 1; E.sel = 1; E.ax = E.cx; E.ay = E.cy;
                   msg("Mark set — move with arrows to select, Ctrl-C/Ctrl-X, Esc cancels"); }
            break;
        case K_ESC: E.mark = 0; E.sel = 0; break;  /* cancel mark / selection */
        case 22: ed_paste(); break;                /* ^V */
        case 1:  ed_select_all(); break;           /* ^A */
        case 26: do_undo(); break;                 /* ^Z */
        case 25: do_redo(); break;                 /* ^Y */
        case 4:  ed_dup_line(); break;             /* ^D */
        case 11: E.sel = 0; ed_cut(); break;       /* ^K cut line */
        case 5:  g_enc = (g_enc + 1) % 3; clamp_cursor();   /* ^E cycle encoding view */
                 msg("Encoding view: %s", enc_name()); break;
        case 12: g_resized = 1; break;             /* ^L redraw */
        case 2:                                    /* ^B toggle mouse mode */
            g_mouse = !g_mouse; mouse_set(g_mouse);
            break;
        case 8: show_help(); break;                /* ^H help (Backspace is 127/DEL) */

        default:
            if (k >= 32 && k < 256) ed_insert_byte(k);
            break;
    }
}

/* ------------------------------------------------------------------ */
/* Main                                                               */
/* ------------------------------------------------------------------ */
int main(int argc, char **argv) {
    setlocale(LC_ALL, "");
    const char *cs = nl_langinfo(CODESET);
    g_utf8 = cs && (strstr(cs, "UTF") || strstr(cs, "utf"));

    const char *t = getenv("LITEFE_TAB");                        /* tab width */
    if (t && *t) { int v = atoi(t); if (v >= 1 && v <= 16) g_tabw = v; }
    const char *xt = getenv("LITEFE_EXPANDTAB");                 /* tabs -> spaces */
    g_expandtab = xt && xt[0] && strcmp(xt, "0") != 0;
    const char *mo = getenv("LITEFE_MOUSE");                     /* in-app mouse (default off) */
    g_mouse = mo && mo[0] && strcmp(mo, "0") != 0;
    const char *as = getenv("LITEFE_ALTSCREEN");                 /* 0 = stay on normal screen */
    if (as && as[0]) g_altscreen = strcmp(as, "0") != 0;
    const char *e = getenv("LITEFE_ENC");                        /* encoding view */
    if (e && e[0]) {
        g_enc_forced = 1;
        if (!strcasecmp(e, "latin1") || !strcasecmp(e, "iso-8859-1") || !strcasecmp(e, "8859-1"))
            g_enc = ENC_LATIN1;
        else if (!strcasecmp(e, "cp1252") || !strcasecmp(e, "ansi") || !strcasecmp(e, "windows-1252") || !strcasecmp(e, "1252"))
            g_enc = ENC_CP1252;
        else
            g_enc = ENC_UTF8;                                 /* utf8 / utf-8 / anything else */
    }

    if (argc > 1 && (strcmp(argv[1], "-h") == 0 || strcmp(argv[1], "--help") == 0)) {
        printf("litefe - minimal terminal text editor\n"
               "usage: litefe [file]\n"
               "keys:  Ctrl-H inside the program. Ctrl-S save, Ctrl-Q quit.\n"
               "env:   LITEFE_TAB=N (tab width, default 4)\n"
               "       LITEFE_EXPANDTAB=1 (insert spaces instead of a tab)\n"
               "       LITEFE_ENC=utf8|latin1|cp1252 (encoding view; Ctrl-E cycles)\n"
               "       LITEFE_MOUSE=1 (grab the mouse for in-app use; Ctrl-B toggles)\n"
               "Mouse is off by default so the terminal's own right-click menu works.\n"
               "CRLF/LF line endings are detected on load and preserved.\n");
        return 0;
    }

    E.goalcol = -1;
    if (argc > 1) load_file(argv[1]);
    else { doc_set_text("", 0); E.named = 0; E.dirty = 0; msg("New buffer  -  press Ctrl-H for help"); }

    if (term_init() < 0) {
        fprintf(stderr, "litefe: not a terminal (needs an interactive tty)\n");
        return 1;
    }

    while (g_running) {
        if (g_resized) { get_size(); g_resized = 0; }
        render();
        int k = read_key();
        if (k != K_RESIZE && k != K_MOUSE) g_msg[0] = 0;
        dispatch_key(k);
        clamp_cursor();
    }

    leave_tui();
    free(E.clip);
    return 0;
}
