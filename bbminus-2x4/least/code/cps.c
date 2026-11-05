// cps.c: n-gram closed position set decider with optional tape-cell annotations, for machines given on stdin.
// Proves a machine never reaches an undefined transition from TAPE (after PRESIM steps of direct simulation).
// Annotation modes (they only add information; the run projects onto the plain run):
//   0 none; 1 each cell remembers its own last H (state,symbol) updates; 2 the head carries the last H (state,symbol)
//   transitions, written into each cell; 3 like 2 but an LRU list of distinct transitions.
// Usage: cps TAPE "n,mode,H,presim[,maxcfg] ..." < machines > results.   Output: D <tm> <n> <mode> <H> <presim> <configs> | U <tm>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <omp.h>
#include "tape.h"
#define NS 2
#ifndef NY
#define NY 4
#endif
#define MAXN 12
typedef struct { int8_t w, d, s; } Tr;
typedef struct { Tr t[NS][NY]; } M;
static Tape TP;
typedef unsigned __int128 u128;
// generic open-addressing hash set of fixed-size keys
typedef struct { uint64_t *k; size_t cap, n; int w; } HS;
static uint64_t hmix(const uint64_t *k, int w) { uint64_t h = 0x9E3779B97F4A7C15ull; for (int i = 0; i < w; i++) { h ^= k[i]; h *= 0xff51afd7ed558ccdull; h ^= h >> 29; } return h; }
static void hs_init(HS *s, int w, size_t cap) { s->w = w; s->cap = cap; s->n = 0; s->k = calloc(cap * (w + 1), 8); }
static void hs_free(HS *s) { free(s->k); s->k = 0; }
static int hs_add(HS *s, const uint64_t *key); 
static void hs_grow(HS *s) { HS o = *s; hs_init(s, o.w, o.cap * 2); for (size_t i = 0; i < o.cap; i++) { uint64_t *e = o.k + i * (o.w + 1); if (e[0]) hs_add(s, e + 1); } free(o.k); }
static int hs_add(HS *s, const uint64_t *key) { // 1 if new
  if ((s->n + 1) * 2 > s->cap) hs_grow(s);
  size_t i = hmix(key, s->w) & (s->cap - 1);
  for (;;) { uint64_t *e = s->k + i * (s->w + 1); if (!e[0]) { e[0] = 1; memcpy(e + 1, key, s->w * 8); s->n++; return 1; } if (!memcmp(e + 1, key, s->w * 8)) return 0; i = (i + 1) & (s->cap - 1); }
}
// Interning of annotated cells: id -> (sym, tag). tag = small array of up to 16 bytes.
typedef struct { uint8_t sym, len; uint8_t a[16]; } Cell;
typedef struct { Cell *c; int n, cap; int *tab; int tcap; } Intern;
static uint64_t cellh(const Cell *c) { uint64_t h = c->sym * 131 + c->len; for (int i = 0; i < c->len; i++) h = h * 1000003 + c->a[i]; return h * 0x9E3779B97F4A7C15ull; }
static int cell_id(Intern *I, const Cell *c) {
  size_t i = cellh(c) & (I->tcap - 1);
  while (I->tab[i] >= 0) { Cell *o = &I->c[I->tab[i]]; if (o->sym == c->sym && o->len == c->len && !memcmp(o->a, c->a, c->len)) return I->tab[i]; i = (i + 1) & (I->tcap - 1); }
  if (I->n == I->cap) return -1;
  I->c[I->n] = *c; I->tab[i] = I->n; return I->n++;
}
static void intern_init(Intern *I, int cap) { I->cap = cap; I->n = 0; I->c = malloc(cap * sizeof(Cell)); I->tcap = cap * 4; I->tab = malloc(I->tcap * sizeof(int)); memset(I->tab, -1, I->tcap * sizeof(int)); }
static void intern_free(Intern *I) { free(I->c); free(I->tab); }
static void tag_update(int mode, int H, Cell *tag, int code) { // push code to front of tag per mode
  if (mode == 3) { int p = -1; for (int i = 0; i < tag->len; i++) if (tag->a[i] == code) { p = i; break; }
    if (p < 0) { int l = tag->len < H ? tag->len + 1 : H; for (int i = l - 1; i > 0; i--) tag->a[i] = tag->a[i-1]; tag->len = l; }
    else for (int i = p; i > 0; i--) tag->a[i] = tag->a[i-1];
    if (H > 0) tag->a[0] = code; }
  else { int l = tag->len < H ? tag->len + 1 : H; for (int i = l - 1; i > 0; i--) tag->a[i] = tag->a[i-1]; tag->len = l; if (H > 0) tag->a[0] = code; }
}
typedef struct { uint16_t s, carry, c; uint16_t l[MAXN], r[MAXN]; } Cfg;
#define CW ((sizeof(Cfg) + 7) / 8)
// sets of grams: key = n cell ids packed into words
#define GW ((2 * MAXN + 7) / 8)
static void gkey(const uint16_t *g, int n, uint64_t *k) { memset(k, 0, GW * 8); memcpy(k, g, n * 2); }
// prefix index: for gram (p0..p_{n-2}, x): map prefix to list of x. Done with linear scan over gram list per prefix hash.
typedef struct { uint16_t *g; int n, cap; int gn; HS set; } GS;
static void gs_init(GS *s, int gn) { s->gn = gn; s->cap = 64; s->n = 0; s->g = malloc(s->cap * gn * 2); hs_init(&s->set, GW, 256); }
static void gs_free(GS *s) { free(s->g); hs_free(&s->set); }
static int gs_add(GS *s, const uint16_t *g) { uint64_t k[GW]; gkey(g, s->gn, k); if (!hs_add(&s->set, k)) return 0; if (s->n == s->cap) { s->cap *= 2; s->g = realloc(s->g, s->cap * s->gn * 2); } memcpy(s->g + s->n * s->gn, g, s->gn * 2); s->n++; return 1; }
static int cps(const M *m, int n, int mode, int H, long presim, long maxcfg, long *ncfg) {
  // presim on a plain tape, tracking annotations alongside
  int span = TP.nmid + TP.nlp + TP.nrp; size_t tn = 2 * presim + 4 * span + 4 * n + 64, c = tn / 2; uint16_t *tp = calloc(tn, 2);
  Intern I; intern_init(&I, 4096); Intern CI; intern_init(&CI, 4096);
  HS seen; hs_init(&seen, CW, 1024); Cfg *list = malloc(1024 * sizeof(Cfg)); long lcap = 1024, ln = 0;
  GS GL, GR; gs_init(&GL, n); gs_init(&GR, n); int res = 0;
  Cell zero; memset(&zero, 0, sizeof zero); int z = cell_id(&I, &zero); Cell nocarry = zero; int nc = cell_id(&CI, &nocarry);
  for (size_t i = 0; i < tn; i++) { Cell x = zero; x.sym = tape_at(&TP, (long)i - (long)c); tp[i] = cell_id(&I, &x); }
  size_t h = c; int st = 0, carry = nc; size_t lo = c - TP.head, hi = c - TP.head + TP.nmid - 1; if (h<lo) lo=h; if (h>hi) hi=h;
#define STEP_ANN(curc, curcarry, S, W, outcell, outcarry) do { \
    Cell cc = I.c[curc]; Cell car = CI.c[curcarry]; int code = (S) * NY + cc.sym; Cell nw; memset(&nw, 0, sizeof nw); nw.sym = (W); \
    if (mode == 1) { nw.len = cc.len; memcpy(nw.a, cc.a, cc.len); tag_update(0, H, &nw, code); outcarry = curcarry; } \
    else if (mode == 2 || mode == 3) { tag_update(mode == 3 ? 3 : 0, H, &car, code); nw.len = car.len; memcpy(nw.a, car.a, car.len); car.sym = 0; outcarry = cell_id(&CI, &car); } \
    else outcarry = curcarry; \
    outcell = cell_id(&I, &nw); } while (0)
  for (long t = 0; t < presim; t++) {
    int ci = tp[h]; int sy = I.c[ci].sym; const Tr *x = &m->t[st][sy];
    if (x->s < 0) goto done; // reached an undefined transition: not decided here
    int oc, oca; STEP_ANN(ci, carry, st, x->w, oc, oca);
    if (oc < 0 || oca < 0) goto done;
    tp[h] = oc; carry = oca; h += x->d; st = x->s; if (h < lo) lo = h; if (h > hi) hi = h;
  }
  { // initial grams: windows of the stacks, then the infinite tail of blanks
    long lenL = (long)h - (long)lo + TP.nlp, lenR = (long)hi - (long)h + TP.nrp;
    if (lo < (size_t)(n + TP.nlp + 1) || hi + n + TP.nrp + 1 >= tn) goto done;
    for (long i = 0; i <= lenL; i++) { uint16_t g[MAXN]; for (int j = 0; j < n; j++) g[j] = tp[h - 1 - i - j]; gs_add(&GL, g); }
    for (long i = 0; i <= lenR; i++) { uint16_t g[MAXN]; for (int j = 0; j < n; j++) g[j] = tp[h + 1 + i + j]; gs_add(&GR, g); }
    Cfg s0; memset(&s0, 0, sizeof s0); s0.s = st; s0.carry = carry; s0.c = tp[h]; for (int j = 0; j < n; j++) { s0.l[j] = tp[h - 1 - j]; s0.r[j] = tp[h + 1 + j]; }
    hs_add(&seen, (uint64_t *)&s0); list[ln++] = s0;
  }
  int changed = 1;
  while (changed) { changed = 0;
    for (long i = 0; i < ln; i++) {
      Cfg q = list[i]; int sy = I.c[q.c].sym; const Tr *x = &m->t[q.s][sy];
      if (x->s < 0) goto done; // abstract halt
      int oc, oca; STEP_ANN(q.c, q.carry, q.s, x->w, oc, oca);
      if (oc < 0 || oca < 0 || oc > 65000) goto done;
      Cfg nx; memset(&nx, 0, sizeof nx); nx.s = x->s; nx.carry = oca;
      const uint16_t *pop = x->d > 0 ? q.r : q.l, *keep = x->d > 0 ? q.l : q.r; GS *gpop = x->d > 0 ? &GR : &GL, *gpush = x->d > 0 ? &GL : &GR;
      uint16_t *npop = x->d > 0 ? nx.r : nx.l, *nkeep = x->d > 0 ? nx.l : nx.r;
      nkeep[0] = oc; for (int j = 1; j < n; j++) nkeep[j] = keep[j-1];
      if (gs_add(gpush, nkeep)) changed = 1;
      nx.c = pop[0]; for (int j = 0; j + 1 < n; j++) npop[j] = pop[j+1];
      for (int g = 0; g < gpop->n; g++) { const uint16_t *gg = gpop->g + g * n; int ok = 1; for (int j = 0; j + 1 < n; j++) if (gg[j] != pop[j+1]) { ok = 0; break; } if (!ok) continue;
        npop[n-1] = gg[n-1];
        if (hs_add(&seen, (uint64_t *)&nx)) { changed = 1; if (ln == lcap) { lcap *= 2; list = realloc(list, lcap * sizeof(Cfg)); } list[ln++] = nx; if (ln > maxcfg) goto done; }
      }
    }
  }
  res = 1; *ncfg = ln;
done:
  free(tp); intern_free(&I); intern_free(&CI); hs_free(&seen); free(list); gs_free(&GL); gs_free(&GR);
  return res;
}
static int parse(const char *s, M *m) { for (int a = 0; a < NS; a++) for (int b = 0; b < NY; b++) { const char *p = s + a * (3 * NY + 1) + b * 3; if (p[0] == '-') m->t[a][b].s = -1; else { m->t[a][b].w = p[0] - '0'; m->t[a][b].d = p[1] == 'R' ? 1 : -1; m->t[a][b].s = p[2] - 'A'; } } return 1; }
typedef struct { int n, mode, H; long presim, maxcfg; } P;
int main(int ac, char **av) {
  tape_parse(av[1], &TP);
  P ps[256]; int np = 0; char *tok = strtok(av[2], " "); while (tok) { P q = {0}; q.maxcfg = 20000; sscanf(tok, "%d,%d,%d,%ld,%ld", &q.n, &q.mode, &q.H, &q.presim, &q.maxcfg); ps[np++] = q; tok = strtok(0, " "); }
  size_t cap = 1 << 20, nm = 0; char (*names)[32] = malloc(cap * 32); char buf[256];
  while (fgets(buf, sizeof buf, stdin)) { char *b = buf; if (b[0] == 'S' && b[1] == ' ') b += 2; b[strcspn(b, "\n ")] = 0; if (nm == cap) { cap *= 2; names = realloc(names, cap * 32); } strncpy(names[nm++], b, 31); }
  long dec[256] = {0}, und = 0;
#pragma omp parallel for schedule(dynamic, 64)
  for (size_t i = 0; i < nm; i++) { M m; parse(names[i], &m); char out[128]; int found = 0; long nc = 0;
    for (int k = 0; k < np && !found; k++) { if (cps(&m, ps[k].n, ps[k].mode, ps[k].H, ps[k].presim, ps[k].maxcfg, &nc)) { found = 1;
#pragma omp atomic
        dec[k]++;
        snprintf(out, sizeof out, "D %s %d %d %d %ld %ld\n", names[i], ps[k].n, ps[k].mode, ps[k].H, ps[k].presim, nc); } }
    if (!found) { snprintf(out, sizeof out, "U %s\n", names[i]);
#pragma omp atomic
      und++; }
#pragma omp critical
    fputs(out, stdout);
  }
  for (int k = 0; k < np; k++) fprintf(stderr, "n=%d mode=%d H=%d presim=%ld: %ld\n", ps[k].n, ps[k].mode, ps[k].H, ps[k].presim, dec[k]);
  fprintf(stderr, "undecided %ld of %zu\n", und, nm);
  return 0;
}
