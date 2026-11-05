// runlang.c: closed tape language from one deterministic automaton used on both sides of the head. Left words are read from the
// far left, right words from the far right. Cells are grouped into blocks of B cells at fixed tape coordinates; an automaton
// state is the unfinished block plus the last K runs of whole blocks, each a block value and its run length mod M (1..M); the
// infinite blank tail is a run with no length. Invariant: each side's word follows only automaton edges in that side's edge set.
// Pushing a cell adds its edge; popping a cell follows any edge of the set into the current state. An abstract configuration is
// (left state, machine state, head symbol, right state). The closure must contain no undefined transition.
// OFF = -1 anchors the block grid at the first nonblank cell of each word instead of at fixed tape coordinates.
// C is a bit mask of symbols; the state also holds the parity of the number of cells of those symbols in the word.
// Usage: runlang TAPE "K,M,B,OFF,C[,maxcfg] ..." < machines.  Output: D <tm> <K> <M> <B> <OFF> <C> <configs> | U <tm>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <omp.h>
#include "tape.h"
#define NY 4
typedef struct { int8_t w, d, s; } Tr;
typedef struct { Tr t[2][NY]; } M;
static Tape TP;
typedef struct { uint64_t a, b; } K128;
typedef struct { K128 *k; int *v; size_t cap, n; } Map;
static uint64_t h128(K128 x) { uint64_t h = x.a * 0x9E3779B97F4A7C15ull; h ^= h >> 31; h += x.b; h *= 0xff51afd7ed558ccdull; h ^= h >> 33; return h; }
static void map_init(Map *m, size_t cap) { m->cap = cap; m->n = 0; m->k = malloc(cap * sizeof(K128)); m->v = malloc(cap * sizeof(int)); memset(m->v, -1, cap * sizeof(int)); }
static void map_free(Map *m) { free(m->k); free(m->v); }
static int map_get(Map *m, K128 key, int ins) { // returns existing value, or inserts ins and returns it
  if ((m->n + 1) * 2 > m->cap) { Map o = *m; map_init(m, o.cap * 2); for (size_t i = 0; i < o.cap; i++) if (o.v[i] >= 0) map_get(m, o.k[i], o.v[i]); map_free(&o); }
  size_t i = h128(key) & (m->cap - 1); while (m->v[i] >= 0) { if (m->k[i].a == key.a && m->k[i].b == key.b) return m->v[i]; i = (i + 1) & (m->cap - 1); }
  m->k[i] = key; m->v[i] = ins; m->n++; return ins;
}
// Run list kept in a 128-bit integer: base alpha*(M+1) digits, lowest digit is the newest run.
typedef unsigned __int128 u128;
typedef struct { int K, Mo, B, anch, C; u128 base, top; Map map; u128 *codes; int *next; int n, cap; } Dfa;
static K128 kk(u128 x) { K128 r = { (uint64_t)(x >> 64), (uint64_t)x }; return r; }
static u128 runs_step(const Dfa *d, u128 runs, int v) {
  int last = (int)(runs % d->base), ll = last / (d->Mo + 1), lc = last % (d->Mo + 1);
  if (ll == v && lc == 0) return runs; // blank tail stays
  if (ll == v) return runs - last + ll * (d->Mo + 1) + (lc % d->Mo + 1);
  return ((runs * d->base) % (d->top * d->base)) + v * (d->Mo + 1) + 1;
}
static int d_state(Dfa *d, u128 code) { if (d->n == d->cap) { d->cap *= 2; d->codes = realloc(d->codes, d->cap * sizeof(u128)); d->next = realloc(d->next, d->cap * 4 * sizeof(int)); }
  int id = map_get(&d->map, kk(code), d->n); if (id == d->n) { d->codes[d->n] = code; for (int a = 0; a < 4; a++) d->next[d->n * 4 + a] = -1; d->n++; } return id; }
// code = (runs * (4^B * B) + partial * B + phase) * 2 + count parity
static int d_next(Dfa *d, int q, int a) { int t = d->next[q * 4 + a]; if (t >= 0) return t;
  if (d->anch && q == 0 && a == 0) { d->next[0] = 0; return 0; }
  int pow4B = 1 << (2 * d->B); u128 sub = (u128)pow4B * d->B, c = d->codes[q] / 2; int cn = (int)(d->codes[q] % 2) ^ ((d->C >> a) & 1); u128 runs = c / sub; int rem = (int)(c % sub), ph = rem % d->B, part = rem / d->B; u128 nc;
  if (ph + 1 == d->B) nc = runs_step(d, runs, part | (a << (2 * ph))) * sub; else nc = runs * sub + (part | (a << (2 * ph))) * d->B + ph + 1;
  t = d_state(d, nc * 2 + cn); d->next[q * 4 + a] = t; return t; }
typedef struct { int *head; int *inc; uint8_t *on; int cap; } Edges; // per side: edges indexed q*4+a; head[target] lists edges into target
static void e_init(Edges *E, int cap) { E->cap = cap; E->on = calloc(cap * 4, 1); E->inc = malloc(cap * 4 * sizeof(int)); E->head = malloc(cap * sizeof(int)); memset(E->head, -1, cap * sizeof(int)); }
static void e_free(Edges *E) { free(E->on); free(E->inc); free(E->head); }
static void e_fit(Edges *E, int n) { if (n <= E->cap) return; int c = E->cap; while (c < n) c *= 2; E->on = realloc(E->on, c * 4); memset(E->on + E->cap * 4, 0, (c - E->cap) * 4); E->inc = realloc(E->inc, c * 4 * sizeof(int)); E->head = realloc(E->head, c * sizeof(int)); memset(E->head + E->cap, -1, (c - E->cap) * sizeof(int)); E->cap = c; }
static int e_add(Edges *E, Dfa *d, int q, int a) { int t = d_next(d, q, a); e_fit(E, d->n); int e = q * 4 + a; if (E->on[e]) return 0; E->on[e] = 1; E->inc[e] = E->head[t]; E->head[t] = e; return 1; }
typedef struct { uint64_t *k; size_t cap, n; } HS;
static int hs_add(HS *s, uint64_t x) { if ((s->n + 1) * 2 > s->cap) { HS o = *s; s->cap *= 2; s->n = 0; s->k = malloc(s->cap * 8); memset(s->k, 0xff, s->cap * 8); for (size_t i = 0; i < o.cap; i++) if (o.k[i] != ~0ull) hs_add(s, o.k[i]); free(o.k); }
  size_t i = (x * 0x9E3779B97F4A7C15ull) & (s->cap - 1); while (s->k[i] != ~0ull) { if (s->k[i] == x) return 0; i = (i + 1) & (s->cap - 1); } s->k[i] = x; s->n++; return 1; }
static int decide(const M *m, int K, int Mo, int B, int off, int C, long maxcfg, long *out) {
  Dfa D; D.K = K; D.Mo = Mo; D.B = B; D.base = ((u128)1 << (2 * B)) * (Mo + 1); D.top = 1; for (int i = 1; i < K; i++) D.top *= D.base; map_init(&D.map, 1024); D.cap = 256; D.n = 0; D.codes = malloc(D.cap * sizeof(u128)); D.next = malloc(D.cap * 4 * sizeof(int));
  D.anch = off < 0; D.C = C;
  for (int p = 0; p < (D.anch ? 1 : B); p++) d_state(&D, (u128)p * 2);
  Edges EL, ER; e_init(&EL, 256); e_init(&ER, 256); int res = 0; int changed = 0;
  // Blank tail edges at every phase, then the finite part. Coordinates: head 0, first left read -nl, first right read +nr.
  for (int p = 0; p < (D.anch ? 1 : B); p++) { e_add(&EL, &D, p, 0); e_add(&ER, &D, p, 0); }
  int nl = TP.head, nr = TP.nmid - TP.head - 1; int q = D.anch ? 0 : ((-nl - off) % B + B) % B;
  for (int i = 0; i < nl; i++) { e_add(&EL, &D, q, TP.mid[i]); q = d_next(&D, q, TP.mid[i]); } int q0l = q;
  // Right words read towards decreasing coordinates. A block ends, on the right side, where a left-side block begins.
  q = D.anch ? 0 : (((off + B - 1 - nr) % B) + B) % B;
  for (int i = 0; i < nr; i++) { int a = TP.mid[TP.nmid - 1 - i]; e_add(&ER, &D, q, a); q = d_next(&D, q, a); } int q0r = q;
  HS seen; seen.cap = 1 << 10; seen.n = 0; seen.k = malloc(seen.cap * 8); memset(seen.k, 0xff, seen.cap * 8); size_t scap = 1 << 10, sn = 0; uint64_t *list = malloc(scap * 8);
  uint64_t st0 = ((uint64_t)q0l << 36) | ((uint64_t)q0r << 8) | (0 << 4) | TP.mid[TP.head]; hs_add(&seen, st0); list[sn++] = st0;
  do { changed = 0;
    for (size_t i = 0; i < sn; i++) {
      uint64_t x = list[i]; int ql = x >> 36, qr = (x >> 8) & 0xfffffff, s = (x >> 4) & 15, c = x & 15; const Tr *t = &m->t[s][c];
      if (t->s < 0) goto done;
      int right = t->d > 0; Edges *Ep = right ? &EL : &ER, *Eo = right ? &ER : &EL; int pq = right ? ql : qr, oq = right ? qr : ql;
      if (e_add(Ep, &D, pq, t->w)) changed = 1;
      int npush = d_next(&D, pq, t->w); e_fit(Eo, D.n);
      for (int e = Eo->head[oq]; e >= 0; e = Eo->inc[e]) { int from = e / 4, a = e % 4;
        uint64_t y = right ? ((uint64_t)npush << 36) | ((uint64_t)from << 8) | (t->s << 4) | a : ((uint64_t)from << 36) | ((uint64_t)npush << 8) | (t->s << 4) | a;
        if (hs_add(&seen, y)) { changed = 1; if ((long)seen.n > maxcfg) goto done; if (sn == scap) { scap *= 2; list = realloc(list, scap * 8); } list[sn++] = y; } }
    }
  } while (changed);
  res = 1; *out = seen.n;
done: free(seen.k); free(list); e_free(&EL); e_free(&ER); map_free(&D.map); free(D.codes); free(D.next); return res;
}
static void parse(const char *s, M *m) { for (int a = 0; a < 2; a++) for (int b = 0; b < NY; b++) { const char *p = s + a * 13 + b * 3; if (p[0] == '-') m->t[a][b].s = -1; else { m->t[a][b].w = p[0] - '0'; m->t[a][b].d = p[1] == 'R' ? 1 : -1; m->t[a][b].s = p[2] - 'A'; } } }
int main(int ac, char **av) {
  tape_parse(av[1], &TP); if (!tape_uniform_blank(&TP)) { fprintf(stderr, "finite tapes only\n"); return 2; }
  struct { int K, Mo, B, off, C; long maxcfg; long dec; } ps[4096]; int np = 0; char *tok = strtok(av[2], " ");
  while (tok) { ps[np].maxcfg = 3000000; ps[np].dec = 0; ps[np].B = 1; ps[np].off = 0; ps[np].C = 0; sscanf(tok, "%d,%d,%d,%d,%d,%ld", &ps[np].K, &ps[np].Mo, &ps[np].B, &ps[np].off, &ps[np].C, &ps[np].maxcfg); np++; tok = strtok(0, " "); }
  size_t cap = 1 << 16, nm = 0; char (*names)[32] = malloc(cap * 32); char buf[256];
  while (fgets(buf, sizeof buf, stdin)) { buf[strcspn(buf, "\n ")] = 0; if (nm == cap) { cap *= 2; names = realloc(names, cap * 32); } strncpy(names[nm++], buf, 31); }
  long und = 0;
#pragma omp parallel for schedule(dynamic, 1)
  for (size_t i = 0; i < nm; i++) { M m; parse(names[i], &m); char out[128]; int found = 0; long nc = 0;
    for (int k = 0; k < np && !found; k++) if (decide(&m, ps[k].K, ps[k].Mo, ps[k].B, ps[k].off, ps[k].C, ps[k].maxcfg, &nc)) { found = 1;
#pragma omp atomic
      ps[k].dec++;
      snprintf(out, sizeof out, "D %s %d %d %d %d %d %ld\n", names[i], ps[k].K, ps[k].Mo, ps[k].B, ps[k].off, ps[k].C, nc); }
    if (!found) { snprintf(out, sizeof out, "U %s\n", names[i]);
#pragma omp atomic
      und++; }
#pragma omp critical
    { fputs(out, stdout); fflush(stdout); }
  }
  for (int k = 0; k < np; k++) if (ps[k].dec) fprintf(stderr, "K=%d M=%d B=%d off=%d C=%d: %ld\n", ps[k].K, ps[k].Mo, ps[k].B, ps[k].off, ps[k].C, ps[k].dec);
  fprintf(stderr, "undecided %ld of %zu\n", und, nm);
  return 0;
}
