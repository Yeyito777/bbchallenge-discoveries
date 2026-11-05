// dfasearch.c: searches for a closed tape language given by two small deterministic automata, one per side of the head, by
// depth-first search over their transition tables (in the spirit of Blanchard's Finite Automata Reduction).
// Left words are read from the far left, right words from the far right, state 0 is the blank tail (0 -0-> 0).
// Abstract configuration: (left state, machine state, head symbol, right state). Invariant: a word's path uses only edges in
// the side's edge set. Pushing adds an edge; popping follows any edge of the set into the current state. A table entry is
// assigned only when the closure needs it, trying each existing state and one new state.
// Usage: dfasearch TAPE MAXSTATES NODEBUDGET < machines.  Output: D <tm> <n> <left table> <right table> | U <tm>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <omp.h>
#include "tape.h"
#define MAXQ 24
typedef struct { int8_t w, d, s; } Tr;
typedef struct { Tr t[2][4]; } M;
static Tape TP;
typedef struct { int8_t nx[2][MAXQ][4]; int8_t used[2]; } Tab; // used: number of states in use per side
typedef struct { long nodes, budget; int n; } Ctx;
static int nl, nr; static uint8_t wl[256], wr[256], h0;
// Closure. Returns 1 closed, 0 contradiction, 2 needs assignment of (side,q,a).
static int closure(const M *m, const Tab *T, int n, int *need) {
  static __thread uint8_t *seen; static __thread uint32_t *list; static __thread uint8_t *E;
  if (!seen) { seen = malloc(MAXQ * MAXQ * 8); list = malloc(4 * MAXQ * MAXQ * 8); E = malloc(2 * MAXQ * 4); }
  memset(seen, 0, n * MAXQ * 8); memset(E, 0, 2 * MAXQ * 4); int sn = 0;
#define NEED(si, q, a) do { need[0] = si; need[1] = q; need[2] = a; return 2; } while (0)
  E[0] = 1; E[MAXQ * 4] = 1; // blank tail edges
  int ql = 0, qr = 0;
  for (int i = 0; i < nl; i++) { int t = T->nx[0][ql][wl[i]]; if (t < 0) NEED(0, ql, wl[i]); E[ql * 4 + wl[i]] = 1; ql = t; }
  for (int i = 0; i < nr; i++) { int t = T->nx[1][qr][wr[i]]; if (t < 0) NEED(1, qr, wr[i]); E[MAXQ * 4 + qr * 4 + wr[i]] = 1; qr = t; }
#define KEY(a, s, c, b) (((a) * MAXQ + (b)) * 8 + (s) * 4 + (c))
  uint32_t k0 = KEY(ql, 0, h0, qr); seen[k0] = 1; list[sn++] = k0; int changed = 1;
  while (changed) { changed = 0;
    for (int i = 0; i < sn; i++) { uint32_t x = list[i]; int c = x & 3, s = (x >> 2) & 1; int ab = x >> 3, a = ab / MAXQ, b = ab % MAXQ; const Tr *t = &m->t[s][c];
      if (t->s < 0) return 0;
      int right = t->d > 0, side = right ? 0 : 1, oside = 1 - side, pq = right ? a : b, oq = right ? b : a;
      int np = T->nx[side][pq][t->w]; if (np < 0) NEED(side, pq, t->w);
      uint8_t *ep = E + side * MAXQ * 4 + pq * 4 + t->w; if (!*ep) { *ep = 1; changed = 1; }
      // edges into oq on the other side: scan the table (small)
      for (int f = 0; f < T->used[oside]; f++) for (int y = 0; y < 4; y++) if (T->nx[oside][f][y] == oq && E[oside * MAXQ * 4 + f * 4 + y]) {
        uint32_t nk = right ? KEY(np, t->s, y, f) : KEY(f, t->s, y, np);
        if (!seen[nk]) { seen[nk] = 1; list[sn++] = nk; changed = 1; } }
    }
  }
  return 1;
}
static int dfs(const M *m, Tab *T, Ctx *C) {
  if (++C->nodes > C->budget) return -1;
  int need[3]; int r = closure(m, T, C->n, need);
  if (r == 1) return 1; if (r == 0) return 0;
  int si = need[0], q = need[1], a = need[2], u = T->used[si];
  int lim = u < C->n ? u + 1 : C->n;
  for (int t = 0; t < lim; t++) { T->nx[si][q][a] = t; int ou = T->used[si]; if (t == u) T->used[si] = u + 1;
    int rr = dfs(m, T, C); if (rr != 0) return rr;
    T->used[si] = ou; }
  T->nx[si][q][a] = -1; return 0;
}
static void parse(const char *s, M *m) { for (int a = 0; a < 2; a++) for (int b = 0; b < 4; b++) { const char *p = s + a * 13 + b * 3; if (p[0] == '-') m->t[a][b].s = -1; else { m->t[a][b].w = p[0] - '0'; m->t[a][b].d = p[1] == 'R' ? 1 : -1; m->t[a][b].s = p[2] - 'A'; } } }
static void tabstr(const Tab *T, int si, int n, char *o) { char *p = o; for (int q = 0; q < n; q++) { if (q) *p++ = '/'; for (int a = 0; a < 4; a++) { int t = T->nx[si][q][a]; *p++ = t < 0 ? '-' : (t < 10 ? '0' + t : 'a' + t - 10); } } *p = 0; }
int main(int ac, char **av) {
  tape_parse(av[1], &TP); if (!tape_uniform_blank(&TP)) { fprintf(stderr, "finite tapes only\n"); return 2; }
  int maxn = atoi(av[2]); long budget = atol(av[3]);
  nl = TP.head; for (int i = 0; i < nl; i++) wl[i] = TP.mid[i]; nr = TP.nmid - TP.head - 1; for (int i = 0; i < nr; i++) wr[i] = TP.mid[TP.nmid - 1 - i]; h0 = TP.mid[TP.head];
  size_t cap = 1 << 16, nm = 0; char (*names)[32] = malloc(cap * 32); char buf[256];
  while (fgets(buf, sizeof buf, stdin)) { buf[strcspn(buf, "\n ")] = 0; if (nm == cap) { cap *= 2; names = realloc(names, cap * 32); } strncpy(names[nm++], buf, 31); }
  long und = 0, byN[MAXQ] = {0};
#pragma omp parallel for schedule(dynamic, 1)
  for (size_t i = 0; i < nm; i++) { M m; parse(names[i], &m); char out[1024]; int found = 0;
    for (int n = 1; n <= maxn && !found; n++) { Tab T; memset(T.nx, -1, sizeof T.nx); T.nx[0][0][0] = 0; T.nx[1][0][0] = 0; T.used[0] = T.used[1] = 1; Ctx C = {0, budget, n};
      int r = dfs(&m, &T, &C);
      if (r == 1) { found = 1; char a[512], b[512]; tabstr(&T, 0, n, a); tabstr(&T, 1, n, b); snprintf(out, sizeof out, "D %s %d %s %s\n", names[i], n, a, b);
#pragma omp atomic
        byN[n]++; } }
    if (!found) { snprintf(out, sizeof out, "U %s\n", names[i]);
#pragma omp atomic
      und++; }
#pragma omp critical
    { fputs(out, stdout); fflush(stdout); }
  }
  for (int n = 1; n <= maxn; n++) if (byN[n]) fprintf(stderr, "n=%d: %ld\n", n, byN[n]);
  fprintf(stderr, "undecided %ld of %zu\n", und, nm);
  return 0;
}
