// repwl.c: Repeated Word List closed-graph decider (after mxdys's RepWL_ES), from a non-blank start tape.
// The tape is two stacks of tokens (word of L cells, exponent e); exponent T means "at least T", below T is exact.
// The set of abstract configurations reachable by block simulation must close with no undefined transition reached.
// Usage: repwl TAPE "L,T,K,presim[,maxcfg,maxtok] ..." < machines > results.  K = head offset inside its first block.
// Output: D <tm> <L> <T> <K> <presim> <configs> | U <tm>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <omp.h>
#include "tape.h"
#define NS 2
#define NY 4
typedef struct { int8_t w, d, s; } Tr;
typedef struct { Tr t[NS][NY]; } M;
static Tape TP;
typedef struct { uint32_t w; uint32_t e; } Tok;
#define MAXTOK 256
typedef struct { uint8_t s, side; uint16_t nl, nr; Tok l[MAXTOK], r[MAXTOK]; } Cfg; // stack tops at the end of each array
typedef struct { uint8_t **e; uint32_t *len; size_t cap, n; } SS;
static uint64_t fnv(const uint8_t *p, size_t n) { uint64_t h = 1469598103934665603ull; for (size_t i = 0; i < n; i++) { h ^= p[i]; h *= 1099511628211ull; } return h; }
static void ss_init(SS *s, size_t cap) { s->cap = cap; s->n = 0; s->e = calloc(cap, sizeof(uint8_t *)); s->len = calloc(cap, 4); }
static void ss_free(SS *s) { for (size_t i = 0; i < s->cap; i++) free(s->e[i]); free(s->e); free(s->len); }
static int ss_add(SS *s, const uint8_t *p, uint32_t n);
static void ss_grow(SS *s) { SS o = *s; ss_init(s, o.cap * 2); for (size_t i = 0; i < o.cap; i++) if (o.e[i]) { size_t j = fnv(o.e[i], o.len[i]) & (s->cap - 1); while (s->e[j]) j = (j + 1) & (s->cap - 1); s->e[j] = o.e[i]; s->len[j] = o.len[i]; s->n++; } free(o.e); free(o.len); }
static int ss_add(SS *s, const uint8_t *p, uint32_t n) { if ((s->n + 1) * 2 > s->cap) ss_grow(s); size_t j = fnv(p, n) & (s->cap - 1); while (s->e[j]) { if (s->len[j] == n && !memcmp(s->e[j], p, n)) return 0; j = (j + 1) & (s->cap - 1); } s->e[j] = malloc(n); memcpy(s->e[j], p, n); s->len[j] = n; s->n++; return 1; }
static uint32_t ser(const Cfg *c, uint8_t *o) { uint8_t *p = o; *p++ = c->s; *p++ = c->side; memcpy(p, &c->nl, 2); p += 2; memcpy(p, &c->nr, 2); p += 2; memcpy(p, c->l, c->nl * sizeof(Tok)); p += c->nl * sizeof(Tok); memcpy(p, c->r, c->nr * sizeof(Tok)); p += c->nr * sizeof(Tok); return p - o; }
static void deser(const uint8_t *o, Cfg *c) { const uint8_t *p = o; c->s = *p++; c->side = *p++; memcpy(&c->nl, p, 2); p += 2; memcpy(&c->nr, p, 2); p += 2; memcpy(c->l, p, c->nl * sizeof(Tok)); p += c->nl * sizeof(Tok); memcpy(c->r, p, c->nr * sizeof(Tok)); }
static int pushw(Tok *st, uint16_t *n, uint32_t w, uint32_t tail, int T, int maxtok) { // merge; returns 0 on overflow
  if (*n == 0 && w == tail) return 1;
  if (*n && st[*n - 1].w == w) { uint32_t e = st[*n - 1].e; st[*n - 1].e = e + 1 >= (uint32_t)T ? (uint32_t)T : e + 1; return 1; }
  if (*n >= maxtok) return 0;
  st[*n].w = w; st[*n].e = 1 >= T ? (uint32_t)T : 1; (*n)++; return 1;
}
static void strip(Tok *st, uint16_t *n, uint32_t tail) { while (*n && st[0].w == tail) { memmove(st, st + 1, (*n - 1) * sizeof(Tok)); (*n)--; } }
// block simulation: returns 1 exit right, -1 exit left, 0 fail (undefined or too long). word packed little-endian: cell i at bits 2i.
static int blocksim(const M *m, uint32_t *w, int L, int *st, int off, long B) {
  uint32_t x = *w; int s = *st, p = off;
  for (long i = 0; i < B; i++) { int y = (x >> (2 * p)) & 3; const Tr *t = &m->t[s][y]; if (t->s < 0) return 0; x = (x & ~(3u << (2 * p))) | ((uint32_t)t->w << (2 * p)); s = t->s; p += t->d;
    if (p < 0) { *w = x; *st = s; return -1; } if (p >= L) { *w = x; *st = s; return 1; } }
  return 0;
}
static int run(const M *m, int L, int T, int K, long presim, long maxcfg, int maxtok, long *out) {
  if (L % TP.nlp || L % TP.nrp) return 0;
  int span = TP.nmid + TP.nlp + TP.nrp; size_t tn = 2 * presim + 8 * L + 4 * span + 64, c = tn / 2; uint8_t *tp = malloc(tn); int res = 0;
  for (size_t i = 0; i < tn; i++) tp[i] = tape_at(&TP, (long)i - (long)c);
  size_t h = c, lo = c - TP.head, hi = c - TP.head + TP.nmid - 1; int st = 0; if (h<lo) lo=h; if (h>hi) hi=h;
  for (long t = 0; t < presim; t++) { const Tr *x = &m->t[st][tp[h]]; if (x->s < 0) { free(tp); return 0; } tp[h] = x->w; h += x->d; st = x->s; if (h < lo) lo = h; if (h > hi) hi = h; }
  Cfg *cur = malloc(sizeof(Cfg)), *nx = malloc(sizeof(Cfg)); uint8_t *buf = malloc(sizeof(Cfg) + 16);
  SS seen; ss_init(&seen, 1024); size_t qcap = 1024, qn = 0, qh = 0; uint8_t **q = malloc(qcap * sizeof *q); uint32_t *ql = malloc(qcap * 4);
  // first block contains the head at offset K
  long b0 = (long)h - K; uint32_t w0 = 0; for (int i = 0; i < L; i++) w0 |= (uint32_t)tp[b0 + i] << (2 * i);
  Cfg *ini = malloc(sizeof(Cfg)); ini->nl = ini->nr = 0; ini->s = st;
  uint32_t tailR, tailL;
  { long p = b0 + L; long last = (long)hi; long top = p; while (top <= last) top += L; // right stack: push far blocks first
    tailR = 0; for (int i = 0; i < L; i++) tailR |= (uint32_t)tp[top + i] << (2 * i);
    for (long b = top - L; b >= p; b -= L) { uint32_t x = 0; for (int i = 0; i < L; i++) x |= (uint32_t)tp[b + i] << (2 * i); if (!pushw(ini->r, &ini->nr, x, tailR, T, maxtok)) goto done; }
    long q2 = b0 - L; long low = q2; while (low + L - 1 >= (long)lo) low -= L; // left stack: low is the first block wholly past the finite part
    tailL = 0; for (int i = 0; i < L; i++) tailL |= (uint32_t)tp[low + i] << (2 * i);
    for (long b = low + L; b <= q2; b += L) { uint32_t x = 0; for (int i = 0; i < L; i++) x |= (uint32_t)tp[b + i] << (2 * i); if (!pushw(ini->l, &ini->nl, x, tailL, T, maxtok)) goto done; }
    strip(ini->l, &ini->nl, tailL); strip(ini->r, &ini->nr, tailR); }
  { int s1 = st; int ex = blocksim(m, &w0, L, &s1, K, 100000); if (!ex) goto done;
    ini->s = s1; if (ex > 0) { if (!pushw(ini->l, &ini->nl, w0, tailL, T, maxtok)) goto done; ini->side = 1; } else { if (!pushw(ini->r, &ini->nr, w0, tailR, T, maxtok)) goto done; ini->side = 0; }
    uint32_t n = ser(ini, buf); ss_add(&seen, buf, n); q[qn] = malloc(n); memcpy(q[qn], buf, n); ql[qn++] = n; }
  while (qh < qn) {
    deser(q[qh++], cur);
    Tok *ps = cur->side ? cur->r : cur->l; uint16_t *pn = cur->side ? &cur->nr : &cur->nl;
    int branches = 1; uint32_t ptail = cur->side ? tailR : tailL; Tok top = {0, 0}; int empty = *pn == 0; if (!empty) { top = ps[*pn - 1]; if (top.e == (uint32_t)T) branches = 2; }
    for (int b = 0; b < branches; b++) {
      *nx = *cur; Tok *ns = nx->side ? nx->r : nx->l; uint16_t *nn = nx->side ? &nx->nr : &nx->nl; uint32_t w = ptail;
      if (!empty) { w = top.w; if (branches == 2 && b == 1) { /* stays at T+ */ } else { uint32_t e = top.e - 1; if (e == 0) (*nn)--; else ns[*nn - 1].e = e; } strip(ns, nn, ptail); }
      int s1 = cur->s; int ex = blocksim(m, &w, L, &s1, cur->side ? 0 : L - 1, 100000); if (!ex) goto done;
      nx->s = s1;
      if (ex > 0) { if (!pushw(nx->l, &nx->nl, w, tailL, T, maxtok)) goto done; nx->side = 1; } else { if (!pushw(nx->r, &nx->nr, w, tailR, T, maxtok)) goto done; nx->side = 0; }
      uint32_t n = ser(nx, buf);
      if (ss_add(&seen, buf, n)) { if ((long)seen.n > maxcfg) goto done; if (qn == qcap) { qcap *= 2; q = realloc(q, qcap * sizeof *q); ql = realloc(ql, qcap * 4); } q[qn] = malloc(n); memcpy(q[qn], buf, n); ql[qn++] = n; }
    }
  }
  res = 1; *out = (long)seen.n;
done:
  free(tp); free(cur); free(nx); free(buf); free(ini); ss_free(&seen); for (size_t i = 0; i < qn; i++) free(q[i]); free(q); free(ql);
  return res;
}
static void parse(const char *s, M *m) { for (int a = 0; a < NS; a++) for (int b = 0; b < NY; b++) { const char *p = s + a * 13 + b * 3; if (p[0] == '-') m->t[a][b].s = -1; else { m->t[a][b].w = p[0] - '0'; m->t[a][b].d = p[1] == 'R' ? 1 : -1; m->t[a][b].s = p[2] - 'A'; } } }
typedef struct { int L, T, K; long presim, maxcfg; int maxtok; } P;
int main(int ac, char **av) {
  tape_parse(av[1], &TP);
  P ps[1024]; int np = 0; char *tok = strtok(av[2], " "); while (tok) { P q = {0}; q.maxcfg = 20000; q.maxtok = 64; sscanf(tok, "%d,%d,%d,%ld,%ld,%d", &q.L, &q.T, &q.K, &q.presim, &q.maxcfg, &q.maxtok); ps[np++] = q; tok = strtok(0, " "); }
  size_t cap = 1 << 16, nm = 0; char (*names)[32] = malloc(cap * 32); char buf[256];
  while (fgets(buf, sizeof buf, stdin)) { buf[strcspn(buf, "\n ")] = 0; if (nm == cap) { cap *= 2; names = realloc(names, cap * 32); } strncpy(names[nm++], buf, 31); }
  long dec[1024] = {0}, und = 0;
#pragma omp parallel for schedule(dynamic, 1)
  for (size_t i = 0; i < nm; i++) { M m; parse(names[i], &m); char out[128]; int found = 0; long nc = 0;
    for (int k = 0; k < np && !found; k++) if (run(&m, ps[k].L, ps[k].T, ps[k].K, ps[k].presim, ps[k].maxcfg, ps[k].maxtok, &nc)) { found = 1;
#pragma omp atomic
      dec[k]++;
      snprintf(out, sizeof out, "D %s %d %d %d %ld %ld\n", names[i], ps[k].L, ps[k].T, ps[k].K, ps[k].presim, nc); }
    if (!found) { snprintf(out, sizeof out, "U %s\n", names[i]);
#pragma omp atomic
      und++; }
#pragma omp critical
    { fputs(out, stdout); fflush(stdout); }
  }
  for (int k = 0; k < np; k++) if (dec[k]) fprintf(stderr, "L=%d T=%d K=%d presim=%ld: %ld\n", ps[k].L, ps[k].T, ps[k].K, ps[k].presim, dec[k]);
  fprintf(stderr, "undecided %ld of %zu\n", und, nm);
  return 0;
}
