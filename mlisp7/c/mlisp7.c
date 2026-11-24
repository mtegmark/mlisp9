/* mlisp7: the native mLISP interpreter in C: mlisp.c, the MLISP interpreter below, with its -7 mLISP mode switched on by
   default, so  ./mlisp7 "<definitions...program>" raw...  runs mLISP macro notation directly (binary programs take the
   pair {x,y}, ternary ones {x,{y,z}}; the inputs are packed). Build: cc -O2 -o mlisp7 mlisp7.c */
#define MLISP7_DEFAULT 1
/* mlisp: MLISP in C, a faithful port of html/mlisp.py (same semantics, same CLI).
   Usage: ./mlisp [-7] [-n REPS] '<definitions...program>' [raw_i] [raw_j] [raw_k]
   Prints "RESULT <raw|defined|undefined|error>" and "TIME_NS <total for all reps>".
   With -7 the text is mLISP macro notation (KERNEL .ml7 style): each definition
   and the final program are macro-expanded (binary i=ea j=eb, ternary i=ea j=eba
   k=ebb), embedded e -> i, and the raw inputs of a binary/ternary program are
   packed into {x,y} / {x,{y,z}}. mlisp7.c builds the same code with -7 the
   default, giving a native mLISP interpreter (./mlisp7). */
#ifndef MLISP7_DEFAULT
#define MLISP7_DEFAULT 0
#endif
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <setjmp.h>
#include <time.h>

/* ---------- arenas ---------- */
typedef struct Block { struct Block *next; size_t used; char data[1 << 20]; } Block;
typedef struct { Block *head, *cur; } Arena;
static void *aalloc(Arena *A, size_t n) {
    n = (n + 15) & ~15UL;
    if (!A->cur || A->cur->used + n > sizeof A->cur->data) {
        if (A->cur && A->cur->next) { A->cur = A->cur->next; A->cur->used = 0; }
        else { Block *b = malloc(sizeof(Block)); b->next = NULL; b->used = 0;
               if (A->cur) A->cur->next = b; else A->head = b; A->cur = b; }
    }
    void *p = A->cur->data + A->cur->used; A->cur->used += n; return p;
}
static void areset(Arena *A) { A->cur = A->head; if (A->cur) A->cur->used = 0; }
static Arena VAL, RUNA;          /* persistent values; per-rep trees+values */

/* ---------- values ---------- */
typedef struct V { struct V *a, *b; } V;      /* atom = NULL */
static V *pair(Arena *A, V *x, V *y) { V *v = aalloc(A, sizeof(V)); v->a = x; v->b = y; return v; }

/* ---------- expressions ---------- */
enum { OP0, OPI, OPJ, OPK, OPA, OPB, OPC, OPD, OPF, OPDEF };
typedef struct E { int op; int defid; int n; struct E *x[3]; } E;

/* ---------- definitions ---------- */
#define MAXD 4096
static int d_ar[MAXD]; static E *d_tree[MAXD]; static int n_defs;
static uint16_t defmap[0x10000];              /* codepoint -> def id + 1 */
static uint32_t defined_cps[MAXD];            /* to reset between reps */
static void defs_reset(void) { for (int t = 0; t < n_defs; t++) defmap[defined_cps[t]] = 0; n_defs = 0; }

/* ---------- utf-8 ---------- */
static uint32_t *utf8_decode(const char *s, int *out_len) {
    int cap = (int)strlen(s) + 1; uint32_t *cp = malloc(cap * 4); int n = 0;
    for (const unsigned char *p = (const unsigned char *)s; *p; ) {
        uint32_t c; int k;
        if (*p < 0x80) { c = *p; k = 1; }
        else if ((*p >> 5) == 6) { c = *p & 31; k = 2; }
        else if ((*p >> 4) == 14) { c = *p & 15; k = 3; }
        else { c = *p & 7; k = 4; }
        for (int t = 1; t < k; t++) c = (c << 6) | (p[t] & 63);
        p += k; cp[n++] = c;
    }
    cp[n] = 0; *out_len = n; return cp;
}

/* ---------- errors ---------- */
static jmp_buf run_jb; static const char *run_err;   /* parse/definition error */
static jmp_buf ev_jb;                                /* Undefined */

/* ---------- parsing ---------- */
static int arity_of_prog(const uint32_t *p, int len) {
    int a = 0;
    for (int t = 0; t < len; t++) { if (p[t]=='i'&&a<1)a=1; if (p[t]=='j'&&a<2)a=2; if (p[t]=='k')a=3; }
    return a;
}
static E *enode(int op, int defid, int n) { E *e = aalloc(&RUNA, sizeof(E)); e->op = op; e->defid = defid; e->n = n; return e; }
static E *parse(const uint32_t *p, int len, int farity, int *ok) {
    static E *stack[1 << 16]; int sp = 0;
    for (int t = 0; t < len; t++) {
        uint32_t ch = p[t]; int op = -1, defid = -1, n = 0;
        switch (ch) {
            case '0': op = OP0; n = 0; break;
            case 'i': op = OPI; n = 0; break;
            case 'j': op = OPJ; n = 0; break;
            case 'k': op = OPK; n = 0; break;
            case 'a': op = OPA; n = 1; break;
            case 'b': op = OPB; n = 1; break;
            case 'c': op = OPC; n = 2; break;
            case 'd': op = OPD; n = 3; break;
            case 'f': op = OPF; n = farity; break;
            default: {
                int id = (ch < 0x10000) ? defmap[ch] : 0;
                if (!id) { *ok = 0; return NULL; }                 /* unknown symbol */
                op = OPDEF; defid = id - 1; n = d_ar[defid];
            }
        }
        if (sp < n) { *ok = 0; return NULL; }                      /* needs more arguments */
        E *e = enode(op, defid, n);
        for (int t2 = 0; t2 < n; t2++) e->x[t2] = stack[sp - n + t2];
        sp -= n; stack[sp++] = e;
    }
    if (sp != 1) { *ok = 0; return NULL; }
    *ok = 1; return stack[0];
}

/* ---------- evaluation ---------- */
static V *ev(E *e, V **env, E *fdef, int far) {
    switch (e->op) {
        case OP0: return NULL;
        case OPI: return env[0];
        case OPJ: return env[1];
        case OPK: return env[2];
        case OPD: return ev(ev(e->x[0], env, fdef, far) != NULL ? e->x[1] : e->x[2], env, fdef, far);
        case OPA: { V *v = ev(e->x[0], env, fdef, far); if (!v) longjmp(ev_jb, 1); return v->a; }
        case OPB: { V *v = ev(e->x[0], env, fdef, far); if (!v) longjmp(ev_jb, 1); return v->b; }
        case OPC: { V *x = ev(e->x[0], env, fdef, far); V *y = ev(e->x[1], env, fdef, far); return pair(&RUNA, x, y); }
        case OPF: {
            V *nv[3] = {NULL, NULL, NULL};
            for (int t = 0; t < e->n; t++) nv[t] = ev(e->x[t], env, fdef, far);
            return ev(fdef, nv, fdef, far);
        }
        default: {
            V *nv[3] = {NULL, NULL, NULL};
            for (int t = 0; t < e->n; t++) nv[t] = ev(e->x[t], env, fdef, far);
            E *body = d_tree[e->defid];
            return ev(body, nv, body, d_ar[e->defid]);
        }
    }
}

/* ---------- run(text, inputs) ---------- */
/* returns: 0 value computed (in *out), 1 definitions only, 2 undefined, 3 error */
static int run(const uint32_t *cp, int len, V **inputs, int n_inputs, V **out) {
    defs_reset(); areset(&RUNA);
    int start = 0, last_hash = -1;
    for (int t = 0; t < len; t++) if (cp[t] == '#') last_hash = t;
    /* definitions */
    int pos = 0;
    while (1) {
        int h = -1;
        for (int t = pos; t < len; t++) if (cp[t] == '#') { h = t; break; }
        if (h < 0) break;
        if (h - pos < 2) return 3;                                  /* needs symbol+program */
        uint32_t sym = cp[pos]; const uint32_t *body = cp + pos + 1; int blen = h - pos - 1;
        int ar = arity_of_prog(body, blen), ok = 0;
        E *tree = parse(body, blen, ar, &ok);
        if (!ok) return 3;
        if (sym >= 0x10000 || n_defs >= MAXD) return 3;
        if (!defmap[sym]) defined_cps[n_defs] = sym, defmap[sym] = ++n_defs;   /* new id */
        else { int id = defmap[sym] - 1; d_ar[id] = ar; d_tree[id] = tree; pos = h + 1; continue; }
        d_ar[n_defs - 1] = ar; d_tree[n_defs - 1] = tree;
        pos = h + 1;
    }
    const uint32_t *prog = cp + (last_hash + 1); int plen = len - (last_hash + 1);
    if (plen == 0) return 1;
    int base_ar = arity_of_prog(prog, plen);
    static uint32_t buf[1 << 16];
    for (int pre = 0; pre <= (n_inputs < 3 ? n_inputs : 3); pre++) {
        for (int t = 0; t < pre; t++) buf[t] = "ijk"[t];
        memcpy(buf + pre, prog, plen * 4);
        int ar = base_ar > pre ? base_ar : pre, ok = 0;
        E *tree = parse(buf, plen + pre, ar, &ok);
        if (!ok) { if (pre == 3 || pre == n_inputs) return 3; continue; }
        V *env[3] = {NULL, NULL, NULL};
        for (int t = 0; t < n_inputs && t < 3; t++) env[t] = inputs[t];
        if (setjmp(ev_jb)) return 2;
        *out = ev(tree, env, tree, ar);
        return 0;
    }
    return 3;
}

/* ---------- raw values ---------- */
static V *value(const char *s) {
    static V *stack[1 << 20]; int sp = 0;
    for (; *s; s++) {
        if (*s == '0') stack[sp++] = NULL;
        else if (*s == 'c' || *s == '|') { if (sp < 2) { fprintf(stderr, "bad raw value\n"); exit(1); }
            V *y = stack[--sp], *x = stack[--sp]; stack[sp++] = pair(&VAL, x, y); }
    }
    if (sp != 1) { fprintf(stderr, "bad raw value\n"); exit(1); }
    return stack[0];
}
static char *obuf; static size_t ocap, olen;
static void oput(char c) { if (olen + 1 >= ocap) { ocap = ocap ? ocap * 2 : 1 << 16; obuf = realloc(obuf, ocap); } obuf[olen++] = c; }
static void raw(V *v) { if (!v) { oput('0'); return; } raw(v->a); raw(v->b); oput('c'); }

/* ---------- mLISP (-7): macro expansion + embedding ---------- */
static int arity7(const uint32_t *p, int n) {
    int hask = 0, hasij = 0, hasef = 0;
    for (int t = 0; t < n; t++) {
        if (p[t] == 'k') hask = 1;
        if (p[t] == 'i' || p[t] == 'j') hasij = 1;
        if (p[t] == 'e' || p[t] == 'f') hasef = 1;
    }
    return hask ? 3 : hasij ? 2 : hasef ? 1 : 0;
}
static int put7(uint32_t *out, int w, uint32_t ch, int ar) {
    const char *s = NULL;
    if (ar >= 3) s = ch == 'i' ? "ia" : ch == 'j' ? "iba" : ch == 'k' ? "ibb" : NULL;
    else if (ar == 2) s = ch == 'i' ? "ia" : ch == 'j' ? "ib" : NULL;
    if (s) { while (*s) out[w++] = (uint32_t)*s++; return w; }
    out[w++] = ch == 'e' ? 'i' : ch;
    return w;
}
static uint32_t *expand7(const uint32_t *cp, int len, int *out_len, int *top_ar) {
    uint32_t *out = malloc((len * 3 + 16) * sizeof(uint32_t));
    int w = 0, pos = 0;
    while (pos < len) {
        int h = pos;
        while (h < len && cp[h] != '#') h++;
        int isdef = h < len;
        int start = pos + (isdef ? 1 : 0);
        int ar = arity7(cp + start, h - start);
        if (isdef) out[w++] = cp[pos];
        for (int t = start; t < h; t++) w = put7(out, w, cp[t], ar);
        if (isdef) out[w++] = '#';
        else *top_ar = ar;
        pos = h + 1;
    }
    *out_len = w;
    return out;
}

int main(int argc, char **argv) {
    int reps = 1, ai = 1, mode7 = MLISP7_DEFAULT;
    while (ai < argc && argv[ai][0] == '-') {
        if (!strcmp(argv[ai], "-7")) { mode7 = 1; ai++; }
        else if (!strcmp(argv[ai], "-n")) { reps = atoi(argv[ai + 1]); ai += 2; }
        else break;
    }
    if (ai >= argc) { fprintf(stderr, "usage: mlisp [-n N] text [raw...]\n"); return 1; }
    char *txt = strdup(argv[ai]); { char *w = txt; for (char *r = txt; *r; r++) if (*r != ' ' && *r != '\n' && *r != '\t') *w++ = *r; *w = 0; }
    int len; uint32_t *cp = utf8_decode(txt, &len); ai++;
    int top_ar = -1;
    if (mode7) cp = expand7(cp, len, &len, &top_ar);
    V *inputs[3] = {NULL, NULL, NULL}; int n_inputs = 0;
    for (; ai < argc && n_inputs < 3; ai++) inputs[n_inputs++] = value(argv[ai]);
    if (mode7 && top_ar >= 2 && n_inputs >= top_ar) {   /* pack {x,y} / {x,{y,z}} */
        V *z = top_ar >= 3 ? pair(&VAL, inputs[1], inputs[2]) : inputs[1];
        inputs[0] = pair(&VAL, inputs[0], z); n_inputs = 1;
    }
    V *out = NULL; int st = 0;
    struct timespec t0, t1; clock_gettime(CLOCK_MONOTONIC, &t0);
    for (int r = 0; r < reps; r++) st = run(cp, len, inputs, n_inputs, &out);
    clock_gettime(CLOCK_MONOTONIC, &t1);
    long long ns = (t1.tv_sec - t0.tv_sec) * 1000000000LL + (t1.tv_nsec - t0.tv_nsec);
    printf("RESULT ");
    if (st == 0) { olen = 0; raw(out); oput('\0'); fputs(obuf, stdout); }
    else fputs(st == 1 ? "defined" : st == 2 ? "undefined" : "error", stdout);
    printf("\nTIME_NS %lld\n", ns);
    return 0;
}
