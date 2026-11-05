// prefixes.c: wang/code/check_cert.c plus one line: print the labels of cells 0..P-1 at every reset node,
// in walk order, to stderr (the list each shard's Rocq check compares against).
// check_cert.c: fast standalone checker for wt_lazy certificates, same logic as check_cert.py.
// Union-find over colours, full walk of the tree, every leaf's torus re-derived from the equalities.
// Reads the tree as a stream, so a compressed tree can be piped: xz -dc P.tree.xz | check_cert P -
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define MAXC 32
static int n, D, ntori, order[400][2], idx[20][20];
static int **tp, *tlen;
static signed char labels[400];
static unsigned long long nodes, leaves;
static FILE *tree;
static inline int fnd(const signed char *u, int x) { while (u[x] != x) x = u[x]; return x; }
static inline unsigned token(void) {
  unsigned x = 0; int sh = 0;
  for (;;) {
    int b = getc_unlocked(tree);
    if (b == EOF) { puts("FAIL: tree ended early"); exit(1); }
    x |= (unsigned)(b & 0x7f) << sh;
    sh += 7;
    if (!(b & 0x80)) return x;
  }
}
// Symmetric skip for order "ringsym"; check_cert.py explains why it is sound.
static int use_sym;
static short images[7][400];
static int skipped(int pos) {
  for (int g = 0; g < 7; g++) {
    signed char rename[8];
    memset(rename, -1, sizeof rename);
    int next = 0;
    for (int i = 0; i < pos; i++) {
      int q = images[g][i];
      if (q >= pos) break;
      int l = labels[q];
      if (rename[l] < 0) rename[l] = next++;
      if (rename[l] < labels[i]) return 1;
      if (rename[l] > labels[i]) break;
    }
  }
  return 0;
}
// Repeat skip, explained in check_cert.py: exact 256-bit state, never a hash of it.
typedef unsigned __int128 u128;
typedef struct { u128 rel; u128 fk[2]; } skey;
static skey *seen_tab;
static unsigned long long seen_n, seen_cap;
static short front[401][80];
static int front_n[401];
static inline unsigned long long key_hash(const skey *k) {
  unsigned long long w[6] = {(unsigned long long)k->rel, (unsigned long long)(k->rel >> 64), (unsigned long long)k->fk[0],
                             (unsigned long long)(k->fk[0] >> 64), (unsigned long long)k->fk[1], (unsigned long long)(k->fk[1] >> 64)}, h = 0;
  for (int i = 0; i < 6; i++) { h = (h ^ w[i]) * 0x517cc1b727220a95ULL; h = h << 5 | h >> 59; }
  return h ^ (h >> 29);
}
static void seen_grow(void);
static int seen_insert(const skey *k) {  // returns 1 if already present; fk has a nonzero tag, so 0 means empty
  if ((seen_n + 1) * 10 > seen_cap * 7) seen_grow();
  unsigned long long h = key_hash(k) & (seen_cap - 1);
  while (seen_tab[h].fk[0]) {
    if (seen_tab[h].fk[0] == k->fk[0] && seen_tab[h].fk[1] == k->fk[1] && seen_tab[h].rel == k->rel) return 1;
    h = (h + 1) & (seen_cap - 1);
  }
  seen_tab[h] = *k;
  seen_n++;
  return 0;
}
static void seen_grow(void) {
  skey *old = seen_tab;
  unsigned long long oc = seen_cap;
  seen_cap = oc ? oc * 2 : 1ULL << 20;
  seen_tab = calloc(seen_cap, sizeof(skey));
  if (!seen_tab) { puts("out of memory"); exit(2); }
  seen_n = 0;
  for (unsigned long long i = 0; i < oc; i++) if (old[i].fk[0]) seen_insert(&old[i]);
  free(old);
}
static void relations(const signed char *uf, unsigned char *h, unsigned char *v) {
  int root[MAXC];
  for (int i = 0; i < 4 * n; i++) root[i] = fnd(uf, i);
  memset(h, 0, 8);
  memset(v, 0, 8);
  for (int i = 0; i < n; i++)
    for (int j = 0; j < n; j++) {
      if (root[i] == root[n + j]) h[i] |= 1 << j;
      if (root[2 * n + i] == root[3 * n + j]) v[i] |= 1 << j;
    }
}
static inline u128 pack2(const unsigned char *a, const unsigned char *b) {
  u128 rel = 0;
  for (int i = 0; i < 8; i++) rel |= (u128)a[i] << (8 * i) | (u128)b[i] << (64 + 8 * i);
  return rel;
}
static void state_key(int pos, int k, const unsigned char *h, const unsigned char *v, skey *out) {
  unsigned char hi[8] = {0}, vi[8] = {0};
  for (int i = 0; i < n; i++)
    for (int j = 0; j < n; j++) {
      if (h[i] >> j & 1) hi[j] |= 1 << i;
      if (v[i] >> j & 1) vi[j] |= 1 << i;
    }
  signed char map[8];
  memset(map, -1, sizeof map);
  int next = 0, sh = 15;
  u128 fk[2] = {(u128)pos | (u128)k << 10 | (u128)1 << 14, 0};
  for (int i = 0; i < front_n[pos]; i++) {
    int l = labels[(int)front[pos][i]];
    if (map[l] < 0) map[l] = next++;
    fk[sh / 128] |= (u128)map[l] << (sh % 128);
    sh += 3;
    if (sh % 128 > 125) sh += 128 - sh % 128;
  }
  signed char known[8];
  memcpy(known, map, 8);
#define RENAMED(m) ({ unsigned long long o_ = 0; for (int j_ = 0; j_ < n; j_++) if ((m) >> j_ & 1 && known[j_] >= 0) o_ |= 1ULL << known[j_]; o_; })
  struct { unsigned long long sig; int l; } rest[8];
  int nrest = 0;
  for (int l = 0; l < k; l++)
    if (map[l] < 0) {
      rest[nrest].sig = RENAMED(h[l]) | RENAMED(hi[l]) << 8 | RENAMED(v[l]) << 16 | RENAMED(vi[l]) << 24 |
                        (unsigned long long)__builtin_popcount(h[l]) << 32 | (unsigned long long)__builtin_popcount(hi[l]) << 36 |
                        (unsigned long long)__builtin_popcount(v[l]) << 40 | (unsigned long long)__builtin_popcount(vi[l]) << 44;
      rest[nrest++].l = l;
    }
  for (int a = 1; a < nrest; a++)  // insertion sort, stable on label order
    for (int b = a; b > 0 && rest[b - 1].sig > rest[b].sig; b--) {
      unsigned long long ts = rest[b].sig; int tl = rest[b].l;
      rest[b] = rest[b - 1];
      rest[b - 1].sig = ts; rest[b - 1].l = tl;
    }
  for (int a = 0; a < nrest; a++) map[rest[a].l] = next++;
  for (int l = k; l < n; l++) map[l] = l;
  unsigned char h2[8] = {0}, v2[8] = {0};
  for (int i = 0; i < n; i++)
    for (int j = 0; j < n; j++) {
      if (h[i] >> j & 1) h2[(int)map[i]] |= 1 << map[j];
      if (v[i] >> j & 1) v2[(int)map[i]] |= 1 << map[j];
    }
  out->rel = pack2(h2, v2);
  out->fk[0] = fk[0];
  out->fk[1] = fk[1];
}
// answers per relation pair; value 0 marks an empty slot, so answers are stored +1
typedef struct { u128 rel; int val; } rslot;
typedef struct { rslot *tab; unsigned long long n, cap; } rtable;
static rtable rel_answer, gate_answer, final_answer, visits;
static int reset_pos, shards = 1, shard, gate_t;
static unsigned long long counter, nclosed, digest = 0xcbf29ce484222325ULL;
static rslot *rt_find(rtable *t, u128 rel) {
  if ((t->n + 1) * 10 > t->cap * 7) {
    rslot *old = t->tab;
    unsigned long long oc = t->cap;
    t->cap = oc ? oc * 2 : 1ULL << 16;
    t->tab = calloc(t->cap, sizeof(rslot));
    if (!t->tab) { puts("out of memory"); exit(2); }
    for (unsigned long long i = 0; i < oc; i++)
      if (old[i].val) {
        skey kk = {old[i].rel, {0, 0}};
        unsigned long long h = key_hash(&kk) & (t->cap - 1);
        while (t->tab[h].val) h = (h + 1) & (t->cap - 1);
        t->tab[h] = old[i];
      }
    free(old);
  }
  skey kk = {rel, {0, 0}};
  unsigned long long h = key_hash(&kk) & (t->cap - 1);
  while (t->tab[h].val && t->tab[h].rel != rel) h = (h + 1) & (t->cap - 1);
  return &t->tab[h];
}
static int rt_get(rtable *t, u128 rel) { rslot *s = rt_find(t, rel); return s->val ? s->val - 1 : -1; }
static void rt_put(rtable *t, u128 rel, int x) {
  rslot *s = rt_find(t, rel);
  if (!s->val) t->n++;
  s->rel = rel;
  s->val = x + 1;
}
static void rt_clear(rtable *t) { if (t->cap && t->n) memset(t->tab, 0, t->cap * sizeof(rslot)); t->n = 0; }
static void clear_all(void) {
  rt_clear(&rel_answer);
  rt_clear(&gate_answer);
  rt_clear(&final_answer);
  rt_clear(&visits);
  if (seen_cap && seen_n) memset(seen_tab, 0, seen_cap * sizeof(skey));
  seen_n = 0;
}
// exact square test: arc consistency on tile masks, branching on the smallest domain
static unsigned char img[4][256];
static int propagate(unsigned char *dom, short *stack, int sp) {
  while (sp) {
    int x = stack[--sp], r = x / D, c = x % D, dx = dom[x];
    static const int off[4][2] = {{0, 1}, {0, -1}, {1, 0}, {-1, 0}};
    for (int e = 0; e < 4; e++) {
      int rr = r + off[e][0], cc = c + off[e][1];
      if (rr < 0 || cc < 0 || rr >= D || cc >= D) continue;
      int y = rr * D + cc;
      unsigned char m = dom[y] & img[e][dx];
      if (m != dom[y]) {
        if (!m) return 0;
        dom[y] = m;
        stack[sp++] = y;
      }
    }
  }
  return 1;
}
static int fills(const unsigned char *dom) {
  int best = -1, bc = 99, m2 = D * D;
  for (int x = 0; x < m2; x++) {
    int c = __builtin_popcount(dom[x]);
    if (c > 1 && c < bc) { bc = c; best = x; if (c == 2) break; }
  }
  if (best < 0) return 1;
  for (unsigned m = dom[best]; m; m &= m - 1) {
    unsigned char d2[400];
    short stack[8 * 400];
    memcpy(d2, dom, m2);
    d2[best] = m & -m;
    stack[0] = best;
    if (propagate(d2, stack, 1) && fills(d2)) return 1;
  }
  return 0;
}
static int refuses(const unsigned char *h, const unsigned char *v) {
  unsigned char hi[8] = {0}, vi[8] = {0};
  for (int i = 0; i < n; i++)
    for (int j = 0; j < n; j++) {
      if (h[i] >> j & 1) hi[j] |= 1 << i;
      if (v[i] >> j & 1) vi[j] |= 1 << i;
    }
  for (int m = 0; m < 1 << n; m++) {
    unsigned char a = 0, b = 0, c = 0, e = 0;
    for (int t = 0; t < n; t++)
      if (m >> t & 1) { a |= h[t]; b |= hi[t]; c |= v[t]; e |= vi[t]; }
    img[0][m] = a; img[1][m] = b; img[2][m] = c; img[3][m] = e;
  }
  unsigned char dom[400];
  short stack[8 * 400];
  int m2 = D * D;
  memset(dom, (1 << n) - 1, m2);
  for (int i = 0; i < m2; i++) stack[i] = i;
  return !(propagate(dom, stack, m2) && fills(dom));
}
static void claim(const signed char *uf, unsigned tok);
static void cover(const signed char *uf, int a, int b, u128 *done, int *ndone) {
  signed char u[MAXC];
  memcpy(u, uf, 4 * n);
  int x = fnd(u, a), y = fnd(u, b);
  if (x != y) u[x] = y;
  unsigned char h2[8], v2[8];
  relations(u, h2, v2);
  u128 rel = pack2(h2, v2);
  for (int i = 0; i < *ndone; i++) if (done[i] == rel) return;
  done[(*ndone)++] = rel;
  int r = rt_get(&rel_answer, rel);
  if (r < 0) {
    unsigned tok = token();
    if (!tok) { puts("FAIL: a merge above a closed pair is unsettled"); exit(1); }
    rt_put(&rel_answer, rel, tok);
    claim(u, tok);
  } else if (!r) {
    int g = rt_get(&gate_answer, rel);
    if (g < 0) {
      unsigned tok = token();
      if (!tok) { puts("FAIL: a merge above a closed pair is unsettled"); exit(1); }
      rt_put(&gate_answer, rel, tok);
      claim(u, tok);
    } else if (!g) { puts("FAIL: a merge above a closed pair is unsettled"); exit(1); }
  }
}
static void claim(const signed char *uf, unsigned tok) {
  if (tok == 1) {
    nclosed++;
    unsigned char h[8], v[8];
    relations(uf, h, v);
    if (!refuses(h, v)) { puts("FAIL: a pair claimed closed tiles the square"); exit(1); }
    u128 done[128];
    int ndone = 0;
    for (int i = 0; i < n; i++)
      for (int j = 0; j < n; j++)
        if (!(h[i] >> j & 1)) cover(uf, i, n + j, done, &ndone);
    for (int i = 0; i < n; i++)
      for (int j = 0; j < n; j++)
        if (!(v[i] >> j & 1)) cover(uf, 2 * n + i, 3 * n + j, done, &ndone);
  } else if (tok) {
    if ((int)tok - 2 >= ntori) { puts("FAIL: torus id out of range"); exit(1); }
    int *t = tp[tok - 2];
    for (int i = 0; i < tlen[tok - 2]; i += 2)
      if (fnd(uf, t[i]) != fnd(uf, t[i + 1])) { printf("FAIL: torus %u not implied\n", tok - 2); exit(1); }
  }
}
static void node(int pos, int k, const signed char *uf);
static void walk(int pos, int k, const signed char *uf) {
  if (use_sym && skipped(pos)) return;
  if (pos == reset_pos) {
    clear_all();
    counter++;
    // every shard must see the same list of these nodes, or the shares would not cover the tree
    for (int i = 0; i < pos; i++) fprintf(stderr, i ? " %d" : "%d", labels[i]);
    fputc('\n', stderr);
    for (int i = 0; i < pos; i++) digest = (digest ^ (unsigned char)labels[i]) * 0x100000001b3ULL;
    digest = (digest ^ 255) * 0x100000001b3ULL;
    if ((long long)(counter % shards) == shard) {
      node(pos, k, uf);
      clear_all();
    }
    return;
  }
  node(pos, k, uf);
}
static void node(int pos, int k, const signed char *uf) {
  nodes++;
  unsigned char h[8], v[8];
  relations(uf, h, v);
  u128 rel = pack2(h, v);
  int ans = rt_get(&rel_answer, rel);
  if (ans < 0) {
    ans = token();
    rt_put(&rel_answer, rel, ans);
    claim(uf, ans);
  }
  if (!ans) {
    rslot *s = rt_find(&visits, rel);
    if (!s->val) { visits.n++; s->rel = rel; s->val = 1; }
    s->val++;
    int count = s->val - 1;
    int g = rt_get(&gate_answer, rel);
    if (g >= 0) ans = g;
    else if (gate_t && count >= gate_t) {
      ans = token();
      rt_put(&gate_answer, rel, ans);
      claim(uf, ans);
    }
  }
  if (!ans && pos == D * D) {
    ans = rt_get(&final_answer, rel);
    if (ans < 0) {
      ans = token();
      rt_put(&final_answer, rel, ans);
      claim(uf, ans);
    }
    if (!ans) { puts("FAIL: complete fill with no torus"); exit(1); }
  }
  if (ans) { leaves++; return; }
  skey key;
  state_key(pos, k, h, v, &key);
  if (seen_insert(&key)) return;
  int r = order[pos][0], c = order[pos][1];
  int top = k < n - 1 ? k : n - 1;
  for (int t = 0; t <= top; t++) {
    signed char u[MAXC];
    memcpy(u, uf, 4 * n);
    static const int dr[4] = {0, 0, -1, 1}, dc[4] = {-1, 1, 0, 0};
    for (int e = 0; e < 4; e++) {
      int rr = r + dr[e], cc = c + dc[e];
      if (rr < 0 || cc < 0 || rr >= D || cc >= D) continue;
      int q = idx[rr][cc];
      if (q >= pos) continue;
      int o = labels[q], x, y;
      if (e == 0) { x = o; y = n + t; }                 // neighbour on the left: its E meets my W
      else if (e == 1) { x = n + o; y = t; }            // neighbour on the right: its W meets my E
      else if (e == 2) { x = 2 * n + o; y = 3 * n + t; }  // neighbour above: its S meets my N
      else { x = 3 * n + o; y = 2 * n + t; }            // neighbour below: its N meets my S
      x = fnd(u, x); y = fnd(u, y);
      if (x != y) u[x] = y;
    }
    labels[pos] = t;
    walk(pos + 1, t == k ? k + 1 : k, u);
  }
}
int main(int ac, char **av) {
  if (ac < 2) { fprintf(stderr, "usage: %s PREFIX [-]\n", av[0]); return 2; }
  char path[1024], kind[16];
  snprintf(path, sizeof path, "%s.tori", av[1]);
  FILE *f = fopen(path, "r");
  if (!f) { perror(path); return 2; }
  if (fscanf(f, "wt-cert 3 n %d D %d order %15s tori %d reset %d shards %d shard %d gate %d", &n, &D, kind, &ntori, &reset_pos, &shards, &shard, &gate_t) != 8 || n > 8 || D > 20) { puts("bad header"); return 2; }
  if (!reset_pos) reset_pos = -1;
  tp = malloc(ntori * sizeof(int *));
  tlen = malloc(ntori * sizeof(int));
  for (int i = 0; i < ntori; i++) {
    int a, b, s;
    if (fscanf(f, "%d %d %d", &a, &b, &s) != 3 || a < 1 || b < 1 || s < 0 || s >= b) { puts("bad torus"); return 2; }
    int *g = malloc(a * b * sizeof(int));
    for (int j = 0; j < a * b; j++) if (fscanf(f, "%d", &g[j]) != 1 || g[j] < 0 || g[j] >= n) { puts("bad torus"); return 2; }
    int *t = malloc(4 * a * b * sizeof(int)), m = 0;
    for (int r = 0; r < a; r++)
      for (int c = 0; c < b; c++) {
        int x = g[r * b + c], right = g[r * b + (c + 1) % b];
        int below = r + 1 < a ? g[(r + 1) * b + c] : g[(c + s) % b];
        t[m++] = x; t[m++] = n + right;
        t[m++] = 2 * n + x; t[m++] = 3 * n + below;
      }
    tp[i] = t; tlen[i] = m;
    free(g);
  }
  fclose(f);
  int p = 0;
  if (!strcmp(kind, "scan")) { for (int r = 0; r < D; r++) for (int c = 0; c < D; c++) { order[p][0] = r; order[p][1] = c; p++; } }
  else if (!strcmp(kind, "shell")) {
    for (int k = 0; k < D; k++) {
      for (int r = 0; r < k; r++) { order[p][0] = r; order[p][1] = k; p++; }
      for (int c = 0; c <= k; c++) { order[p][0] = k; order[p][1] = c; p++; }
    }
  } else if (!strcmp(kind, "ring") || !strcmp(kind, "ringsym")) {
    int lo = D % 2 ? D / 2 : D / 2 - 1, hi = D / 2;
    for (;;) {
      if (lo == hi) { order[p][0] = lo; order[p][1] = lo; p++; }
      else {
        for (int c = lo; c < hi; c++) { order[p][0] = lo; order[p][1] = c; p++; }
        for (int r = lo; r < hi; r++) { order[p][0] = r; order[p][1] = hi; p++; }
        for (int c = hi; c > lo; c--) { order[p][0] = hi; order[p][1] = c; p++; }
        for (int r = hi; r > lo; r--) { order[p][0] = r; order[p][1] = lo; p++; }
      }
      if (lo == 0) break;
      lo--; hi++;
    }
    use_sym = !strcmp(kind, "ringsym");
  } else { puts("bad order"); return 2; }
  if (p != D * D) { puts("bad order size"); return 2; }
  for (int i = 0; i < p; i++) idx[order[i][0]][order[i][1]] = i;
  for (int pos = 0; pos <= p; pos++) {
    for (int q = 0; q < pos; q++) {
      int r = order[q][0], c = order[q][1], open = 0;
      if (c > 0 && idx[r][c - 1] >= pos) open = 1;
      if (c + 1 < D && idx[r][c + 1] >= pos) open = 1;
      if (r > 0 && idx[r - 1][c] >= pos) open = 1;
      if (r + 1 < D && idx[r + 1][c] >= pos) open = 1;
      if (open) {
        if (front_n[pos] >= 80) { puts("frontier too long"); return 2; }
        front[pos][front_n[pos]++] = q;
      }
    }
  }
  for (int i = 0; i < p; i++) {
    int r = order[i][0], c = order[i][1], m = D - 1;
    images[0][i] = idx[r][m - c];
    images[1][i] = idx[m - r][c];
    images[2][i] = idx[m - r][m - c];
    images[3][i] = idx[c][r];
    images[4][i] = idx[c][m - r];
    images[5][i] = idx[m - c][r];
    images[6][i] = idx[m - c][m - r];
  }
  if (ac > 2 && !strcmp(av[2], "-")) tree = stdin;
  else {
    snprintf(path, sizeof path, "%s.tree", av[1]);
    tree = fopen(path, "rb");
    if (!tree) { perror(path); return 2; }
  }
  signed char uf[MAXC];
  for (int i = 0; i < 4 * n; i++) uf[i] = i;
  walk(0, 0, uf);
  if (getc(tree) != EOF) { puts("FAIL: trailing bytes"); return 1; }
  printf("OK n=%d D=%d order=%s nodes=%llu leaves=%llu closed=%llu tori=%d shard=%d/%d reset=%d subtrees=%llu digest=%016llx\n", n, D, kind, nodes, leaves, nclosed, ntori, shard, shards, reset_pos, counter, digest);
  if (shards == 1) printf("every %d-tile set that tiles a %dx%d square tiles the plane, so BB_WT(%d) < %d\n", n, D, D, n, D);
  else printf("this shard passes; the claim for n=%d, D=%d needs all %d shards\n", n, D, shards);
  return 0;
}
