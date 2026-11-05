// tree.c: TNF-style enumeration of 2-state 4-symbol TMs on a finite starting tape.
// A node is a partial machine. It runs from the tape in state A until it reaches an undefined transition
// (a halting node, with children), repeats a Lin recurrence (leaf), or reaches the step cap (survivor).
// Normalisation: states in first-use order; a symbol not on the tape and not yet written is interchangeable
// with other such symbols, so only the lowest is tried. No left/right reduction.
// Ledger line per node: H <steps> <tm> | C <t0> <period> <shift> <tm> | S <tm>.
// Usage: tree TAPE CAP LEDGER_PATH_OR_- [LIN(0/1)] [ROOTS_FILE]    TAPE like 2[0] or [3] or 1[0]
// With ROOTS_FILE, the search starts from those partial machines (one per line) instead of the empty machine.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <omp.h>
#include <unistd.h>
#include "tape.h"
#define NS 2
#ifndef NY
#define NY 4
#endif
typedef struct { int8_t w, d, s; } Tr; // s<0: undefined
typedef struct { Tr t[NS][NY]; int def, maxs, seen; } M;
static Tape TP; static uint8_t *tape0; static int t0blank; static long cap; static int lin = 1;
static FILE *led; static long n_halt, n_cyc, n_surv; static long *hist; static long tmax;
static size_t tn; // tape size per worker
#define TOP 12
static long top[TOP]; static char topc[TOP][40];
static void code(const M *m, char *o) {
  char *p = o;
  for (int s = 0; s < NS; s++) {
    if (s) *p++ = '_';
    for (int y = 0; y < NY; y++) {
      const Tr *x = &m->t[s][y];
      if (x->s < 0) { *p++ = '-'; *p++ = '-'; *p++ = '-'; }
      else { *p++ = '0' + x->w; *p++ = x->d > 0 ? 'R' : 'L'; *p++ = 'A' + x->s; }
    }
  }
  *p = 0;
}
typedef struct { uint8_t *tp, *sv; size_t svcap; char *buf; size_t blen; } W;
static void w_init(W *w) { w->tp = t0blank ? calloc(tn, 1) : malloc(tn); if (!t0blank) memcpy(w->tp, tape0, tn); w->svcap = 1 << 16; w->sv = malloc(w->svcap); w->buf = malloc(1 << 20); w->blen = 0; }
static void w_restore(W *w, size_t lo, size_t hi) { if (t0blank) memset(w->tp + lo, 0, hi - lo + 1); else memcpy(w->tp + lo, tape0 + lo, hi - lo + 1); }
#define BUFSZ (1<<20)
static void flushw(W *w) { if (led && w->blen) {
#pragma omp critical(ledger)
  fwrite(w->buf, 1, w->blen, led);
  } w->blen = 0; }
static int sonly; static long abort_at;
static void emit(W *w, const char *line) { if (!led || (sonly && line[0] != 'S')) return; size_t l = strlen(line); if (w->blen + l > BUFSZ) flushw(w); memcpy(w->buf + w->blen, line, l); w->blen += l; }
// Returns: 1 halting node (steps in *ret, st/sym in q), 0 stop
static void go(M *m, int depth, W *w);
static void expand(M *m, int qs, int qy, int depth, W *wk) {
  int smax = m->maxs + 1 < NS ? m->maxs + 1 : NS - 1;
  int ynew = -1; for (int y = 1; y < NY; y++) if (!(m->seen >> y & 1)) { ynew = y; break; }
  for (int wr = 0; wr < NY; wr++) {
    if (!(m->seen >> wr & 1) && wr != ynew) continue;
    for (int d = -1; d <= 1; d += 2) for (int s = 0; s <= smax; s++) {
      M n = *m; n.t[qs][qy] = (Tr){wr, d, s}; n.def++; if (s > n.maxs) n.maxs = s; n.seen |= 1 << wr;
      if (depth < 3) {
#pragma omp task firstprivate(n, depth)
        { static __thread W tw; if (!tw.tp) w_init(&tw);
          M k = n; go(&k, depth + 1, &tw); flushw(&tw); }
      } else go(&n, depth + 1, wk);
    }
  }
}
static void go(M *m, int depth, W *wk) {
  uint8_t *tp = wk->tp; size_t c = tn / 2;
  size_t h = c, vlo = c - TP.head, vhi = c - TP.head + TP.nmid - 1; if (h<vlo) vlo=h; if (h>vhi) vhi=h;
  int st = 0; long i = 0;
  // Lin recurrence state
  long t0 = 0, next = 16; size_t h0 = h; int s0 = st; size_t svlo = vlo, svhi = vhi; size_t wlo = h, whi = h; // window visited since t0
  memcpy(wk->sv, tp + vlo, vhi - vlo + 1);
  char line[128], cs[40]; const Tr *x;
  for (;;) {
    if (i >= cap) break;
    x = &m->t[st][tp[h]];
    if (x->s < 0) goto halted;
    tp[h] = x->w; h += x->d; st = x->s; i++;
    if (h < vlo) vlo = h; if (h > vhi) vhi = h;
    if (lin) {
      if (h < wlo) wlo = h; if (h > whi) whi = h;
      if (st == s0) {
        long d = (long)h - (long)h0;
        // Beyond the window on the side of travel the tape at t0 must be invariant under the shift (see RESULT.md).
#define T0AT(y) (((y) >= svlo && (y) <= svhi) ? wk->sv[(y) - svlo] : (t0blank ? 0 : tape0[y]))
        int ok = 1;
        if (d > 0) { if (d % TP.nrp) ok = 0; for (size_t y = whi + 1; y <= svhi && ok; y++) if (T0AT(y) != T0AT(y + d)) ok = 0; }
        else if (d < 0) { if ((-d) % TP.nlp) ok = 0; for (size_t y = svlo; y < wlo && ok; y++) if (T0AT(y) != T0AT((size_t)((long)y + d))) ok = 0; }
        if (ok) for (size_t y = wlo; y <= whi; y++) {
          if (tp[(size_t)((long)y + d)] != T0AT(y)) { ok = 0; break; }
        }
        if (ok) {
          code(m, cs); snprintf(line, sizeof line, "C %ld %ld %ld %s\n", t0, i - t0, d, cs); emit(wk, line);
#pragma omp atomic
          n_cyc++;
          w_restore(wk, vlo, vhi);
          return;
        }
      }
      if (i == next) {
        t0 = i; next = i * 2; h0 = h; s0 = st; wlo = whi = h; svlo = vlo; svhi = vhi;
        size_t n = vhi - vlo + 1; if (n > wk->svcap) { wk->svcap = n * 2; free(wk->sv); wk->sv = malloc(wk->svcap); }
        memcpy(wk->sv, tp + vlo, n);
      }
    }
  }
  code(m, cs); snprintf(line, sizeof line, "S %s\n", cs); emit(wk, line);
#pragma omp atomic
  n_surv++;
  w_restore(wk, vlo, vhi);
  return;
halted:;
  long steps = i + 1;
  if (abort_at && steps >= abort_at) { code(m, cs);
#pragma omp critical(topq)
    { printf("ABORT halter %ld %s\n", steps, cs); fflush(stdout); _exit(3); } }
  code(m, cs); snprintf(line, sizeof line, "H %ld %s\n", steps, cs); emit(wk, line);
#pragma omp atomic
  n_halt++;
  if (steps < tmax)
#pragma omp atomic
    hist[steps]++;
#pragma omp critical(topq)
  { int k = TOP - 1; if (steps > top[k]) { while (k > 0 && top[k-1] < steps) { top[k] = top[k-1]; memcpy(topc[k], topc[k-1], 40); k--; } top[k] = steps; strcpy(topc[k], cs); } }
  int qs = st, qy = tp[h];
  w_restore(wk, vlo, vhi);
  if (m->def >= NS * NY - 1) return; // the 8th transition defined leaves no way to halt
  expand(m, qs, qy, depth, wk);
}
int main(int ac, char **av) {
  char *s = av[1]; tape_parse(s, &TP); t0blank = tape_uniform_blank(&TP);
  sonly = getenv("LEDGER_S_ONLY") != 0; if (getenv("ABORT_AT")) abort_at = atol(getenv("ABORT_AT"));
  cap = atol(av[2]); tn = 2 * (size_t)cap + 1024;
  if (!t0blank) { tape0 = malloc(tn); for (size_t i = 0; i < tn; i++) tape0[i] = tape_at(&TP, (long)i - (long)(tn / 2)); }
  else { tape0 = calloc(tn, 1); for (int i = 0; i < TP.nmid; i++) tape0[tn / 2 + i - TP.head] = TP.mid[i]; t0blank = 0; }
  if (strcmp(av[3], "-")) led = fopen(av[3], "w");
  if (ac > 4) lin = atoi(av[4]);
  tmax = cap + 2; hist = calloc(tmax, sizeof(long));
  M m; memset(&m, 0, sizeof m); for (int a = 0; a < NS; a++) for (int b = 0; b < NY; b++) m.t[a][b].s = -1; m.seen = tape_symbols(&TP);
  if (ac > 5) {
    FILE *f = fopen(av[5], "r"); char buf[64]; size_t nr = 0, rc = 1024; M *rs = malloc(rc * sizeof(M));
    while (fgets(buf, sizeof buf, f)) {
      M r = m; for (int a = 0; a < NS; a++) for (int b = 0; b < NY; b++) { char *p = buf + a * (3 * NY + 1) + b * 3; if (p[0] == '-') continue;
        r.t[a][b] = (Tr){p[0] - '0', p[1] == 'R' ? 1 : -1, p[2] - 'A'}; r.def++; r.seen |= 1 << (p[0] - '0'); if (p[2] - 'A' > r.maxs) r.maxs = p[2] - 'A'; }
      if (nr == rc) { rc *= 2; rs = realloc(rs, rc * sizeof(M)); } rs[nr++] = r;
    }
#pragma omp parallel
    { W w; w_init(&w);
#pragma omp for schedule(dynamic, 1)
      for (size_t i = 0; i < nr; i++) go(&rs[i], 9, &w);
      flushw(&w);
    }
  } else
#pragma omp parallel
#pragma omp single
  { W w; w_init(&w);
    go(&m, 0, &w); flushw(&w);
#pragma omp taskwait
  }
  if (led) fclose(led);
  printf("tape %s cap %ld lin %d: halting %ld cyclers %ld survivors %ld total %ld\n", s, cap, lin, n_halt, n_cyc, n_surv, n_halt + n_cyc + n_surv);
  for (int i = 0; i < TOP; i++) printf("  %ld %s\n", top[i], topc[i]);
  return 0;
}
