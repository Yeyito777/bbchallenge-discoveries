// seedcheck.c: for each tape, try a list of known long runners under all symbol relabellings of {1,2,3}, mirroring and
// state swap. A variant that halts at or beyond THRESHOLD within CAP steps kills the tape. Usage: seedcheck THRESHOLD CAP SEEDS < tapes
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <omp.h>
#include "tape.h"
typedef struct { int8_t w, d, s; } Tr;
typedef struct { Tr t[2][4]; } M;
static const int PERM[6][3] = {{1,2,3},{1,3,2},{2,1,3},{2,3,1},{3,1,2},{3,2,1}};
static void parse(const char *p0, M *m) { for (int a = 0; a < 2; a++) for (int b = 0; b < 4; b++) { const char *p = p0 + a * 13 + b * 3; if (p[0] == '-') m->t[a][b].s = -1; else { m->t[a][b].w = p[0] - '0'; m->t[a][b].d = p[1] == 'R' ? 1 : -1; m->t[a][b].s = p[2] - 'A'; } } }
static void code(const M *m, char *o) { char *p = o; for (int s = 0; s < 2; s++) { if (s) *p++ = '_'; for (int y = 0; y < 4; y++) { const Tr *x = &m->t[s][y]; if (x->s < 0) { *p++ = '-'; *p++ = '-'; *p++ = '-'; } else { *p++ = '0' + x->w; *p++ = x->d > 0 ? 'R' : 'L'; *p++ = 'A' + x->s; } } } *p = 0; }
static void variant(const M *a, int perm, int mir, int swap, M *o) { int map[4] = {0, PERM[perm][0], PERM[perm][1], PERM[perm][2]};
  for (int s = 0; s < 2; s++) for (int y = 0; y < 4; y++) { Tr x = a->t[s][y]; if (x.s >= 0) { x.w = map[x.w]; if (mir) x.d = -x.d; if (swap) x.s = 1 - x.s; } o->t[swap ? 1 - s : s][map[y]] = x; } }
static long run(const M *m, const Tape *T, long cap, uint8_t *tp, size_t tn) { // returns halting step, 0 at the cap, -1 when the run left the buffer
  size_t c = tn / 2, h = c; int st = 0; long i = 0; size_t lo = c, hi = c;
  // lazily materialised background: window grows as needed
  size_t filled_lo = c - 300, filled_hi = c + 300; for (size_t x = filled_lo; x <= filled_hi; x++) tp[x] = tape_at(T, (long)x - (long)c);
  for (; i < cap; i++) { const Tr *x = &m->t[st][tp[h]]; if (x->s < 0) return i + 1; tp[h] = x->w; h += x->d; st = x->s;
    if (h <= filled_lo) { if (filled_lo < 5000) return -1; size_t nl = filled_lo - 4096; for (size_t q = nl; q < filled_lo; q++) tp[q] = tape_at(T, (long)q - (long)c); filled_lo = nl; }
    if (h >= filled_hi) { if (filled_hi + 5000 > tn) return -1; size_t nh = filled_hi + 4096; for (size_t q = filled_hi + 1; q <= nh; q++) tp[q] = tape_at(T, (long)q - (long)c); filled_hi = nh; } }
  (void)lo; (void)hi; return 0;
}
int main(int ac, char **av) {
  long th = atol(av[1]), cap = atol(av[2]); M *seeds = malloc(1000 * sizeof(M)); int ns = 0; char buf[256]; FILE *f = fopen(av[3], "r");
  while (fgets(buf, sizeof buf, f)) if (strlen(buf) >= 25) parse(buf, &seeds[ns++]);
  char tapes[4096][128]; int nt = 0; while (fgets(buf, sizeof buf, stdin)) { buf[strcspn(buf, "\n")] = 0; if (buf[0]) strcpy(tapes[nt++], buf); }
  size_t tn = 2 * (size_t)cap + 20000; if (tn > (1ull << 28)) tn = 1ull << 28;
#pragma omp parallel
  { uint8_t *tp = malloc(tn);
#pragma omp for schedule(dynamic, 1)
    for (int t = 0; t < nt; t++) { Tape T; tape_parse(tapes[t], &T); int dead = 0; char out[256]; long best = 0; char bc[40] = ""; int nlong = 0;
      for (int s = 0; s < ns && !dead; s++) for (int p = 0; p < 6 && !dead; p++) for (int mi = 0; mi < 2 && !dead; mi++) for (int sw = 0; sw < 2 && !dead; sw++) {
        M v; memset(&v, 0, sizeof v); variant(&seeds[s], p, mi, sw, &v); long r = run(&v, &T, cap, tp, tn);
        if (r == 0 || r == -1) nlong++;
        if (r > best) { best = r; code(&v, bc); } if (r >= th) dead = 1; }
      snprintf(out, sizeof out, "%s %s %ld %s %d\n", tapes[t], dead ? "DEAD" : "OPEN", best, bc, nlong);
#pragma omp critical
      { fputs(out, stdout); fflush(stdout); } }
  }
  return 0;
}
