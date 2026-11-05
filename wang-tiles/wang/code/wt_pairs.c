// wt_pairs.c: Implementation A of BB_WT.  Brute force over adjacency-relation pairs (H,V).
//
// An n-tile Wang set matters only through H = {(i,j): E_i == W_j} and V = {(i,j): S_i == N_j}.
// H and V are each a disjoint union of bicliques.  This program walks every pair up to symmetry
// and classifies each one as "tiles a torus" (score 0) or "refuses the (d+1)x(d+1) square" (score d).
// Anything it cannot classify within its budgets is printed as "unres" and never counted.
//
// usage: wt_pairs N MODE OUTDIR WORKERS [TOPMIN] [SOFTCAP]
//   MODE 0: H runs over S_n orbit reps, V over all relations, weight = |orbit of H|
//   MODE 1: full dihedral reduction as well (see the weights in run_class)
// Every class writes OUTDIR/cNNNNNN.txt atomically, so a killed run resumes where it stopped.
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <unistd.h>

#define MAXN 7
#define HARDCAP 30
typedef uint64_t rel_t;  // byte i = bitmask of j with (i,j) in the relation
typedef unsigned __int128 u128;

static int n, full;
static rel_t *rels;
static long nrels, caprels;

// ---- relation generation: E_i gets none/old block/new block, W_j gets none/block, no empty block
static int blockE[MAXN], blockW[MAXN];
static void emit_rel(void) {
  rel_t r = 0;
  for (int i = 0; i < n; i++)
    if (blockE[i] >= 0)
      for (int j = 0; j < n; j++)
        if (blockW[j] == blockE[i]) r |= (rel_t)1 << (8 * i + j);
  if (nrels == caprels) {
    caprels = caprels ? caprels * 2 : 1024;
    rels = realloc(rels, caprels * sizeof(rel_t));
  }
  rels[nrels++] = r;
}
static void gen_w(int j, int k, unsigned used) {
  if (j == n) {
    if (used == (1u << k) - 1) emit_rel();
    return;
  }
  blockW[j] = -1;
  gen_w(j + 1, k, used);
  for (int b = 0; b < k; b++) {
    blockW[j] = b;
    gen_w(j + 1, k, used | 1u << b);
  }
}
static void gen_e(int i, int k) {
  if (i == n) {
    gen_w(0, k, 0);
    return;
  }
  blockE[i] = -1;
  gen_e(i + 1, k);
  for (int b = 0; b <= k; b++) {
    blockE[i] = b;
    gen_e(i + 1, b == k ? k + 1 : k);
  }
}
static long closed_form(int m) {
  long s[12][12];
  memset(s, 0, sizeof s);
  s[0][0] = 1;
  for (int a = 1; a <= m + 1; a++)
    for (int b = 1; b <= a; b++) s[a][b] = b * s[a - 1][b] + s[a - 1][b - 1];
  long total = 0, fact = 1;
  for (int k = 0; k <= m; k++) {
    if (k) fact *= k;
    total += fact * s[m + 1][k + 1] * s[m + 1][k + 1];
  }
  return total;
}
static int cmp_rel(const void *a, const void *b) {
  rel_t x = *(const rel_t *)a, y = *(const rel_t *)b;
  return x < y ? -1 : x > y;
}
static rel_t rel_transpose(rel_t r) {
  rel_t o = 0;
  for (int i = 0; i < n; i++)
    for (int j = 0; j < n; j++)
      if (r >> (8 * i + j) & 1) o |= (rel_t)1 << (8 * j + i);
  return o;
}
static rel_t rel_permute(rel_t r, const int *p) {
  rel_t o = 0;
  for (int i = 0; i < n; i++)
    for (int j = 0; j < n; j++)
      if (r >> (8 * i + j) & 1) o |= (rel_t)1 << (8 * p[i] + p[j]);
  return o;
}
static long rel_index(rel_t r) {
  long lo = 0, hi = nrels - 1;
  while (lo <= hi) {
    long m = (lo + hi) / 2;
    if (rels[m] == r) return m;
    if (rels[m] < r) lo = m + 1;
    else hi = m - 1;
  }
  fprintf(stderr, "relation not found: closure bug\n");
  exit(2);
}

// ---- classes
static int perms[5040][MAXN], nperms;
static uint32_t *class_of;
static long nclasses;
static rel_t *class_rep;
static long *class_size;
static void build_perms(void) {
  int p[MAXN];
  for (int i = 0; i < n; i++) p[i] = i;
  for (;;) {
    memcpy(perms[nperms++], p, sizeof(int) * n);
    int i = n - 2;
    while (i >= 0 && p[i] > p[i + 1]) i--;
    if (i < 0) break;
    int j = n - 1;
    while (p[j] < p[i]) j--;
    int t = p[i]; p[i] = p[j]; p[j] = t;
    for (int a = i + 1, b = n - 1; a < b; a++, b--) { t = p[a]; p[a] = p[b]; p[b] = t; }
  }
}
static void build_classes(void) {
  class_of = malloc(nrels * sizeof(uint32_t));
  memset(class_of, 0xff, nrels * sizeof(uint32_t));
  long cap = 1 << 16;
  class_rep = malloc(cap * sizeof(rel_t));
  class_size = malloc(cap * sizeof(long));
  for (long i = 0; i < nrels; i++) {
    if (class_of[i] != 0xffffffffu) continue;
    if (nclasses == cap) {
      cap *= 2;
      class_rep = realloc(class_rep, cap * sizeof(rel_t));
      class_size = realloc(class_size, cap * sizeof(long));
    }
    long size = 0;
    rel_t base[2] = {rels[i], rel_transpose(rels[i])};
    for (int t = 0; t < (full ? 2 : 1); t++)
      for (int k = 0; k < nperms; k++) {
        long x = rel_index(rel_permute(base[t], perms[k]));
        if (class_of[x] == 0xffffffffu) {
          class_of[x] = nclasses;
          size++;
        }
      }
    class_rep[nclasses] = rels[i];
    class_size[nclasses] = size;
    nclasses++;
  }
  long sum = 0;
  for (long c = 0; c < nclasses; c++) sum += class_size[c];
  if (sum != nrels) {
    fprintf(stderr, "class sizes sum %ld != %ld\n", sum, nrels);
    exit(2);
  }
}

// ---- solver state for one pair
static uint8_t H[MAXN], V[MAXN], Hi[MAXN], Vi[MAXN];  // right-of, below, and their inverses
static uint8_t grid[HARDCAP + 2][HARDCAP + 2];
static long budget;

static inline void load_rel(rel_t r, uint8_t *a) { for (int i = 0; i < n; i++) a[i] = r >> (8 * i) & 0xff; }
static inline void invert(const uint8_t *a, uint8_t *b) {
  for (int i = 0; i < n; i++) b[i] = 0;
  for (int i = 0; i < n; i++)
    for (unsigned m = a[i]; m; m &= m - 1) b[__builtin_ctz(m)] |= 1 << i;
}
// tiles that can still have a neighbour on all four sides, iterated: a plane tiling lives inside this
static unsigned core_mask(void) {
  unsigned a = (1u << n) - 1;
  for (;;) {
    unsigned b = a;
    for (unsigned m = a; m; m &= m - 1) {
      int t = __builtin_ctz(m);
      if (!(H[t] & a) || !(Hi[t] & a) || !(V[t] & a) || !(Vi[t] & a)) b &= ~(1u << t);
    }
    if (b == a) return a;
    a = b;
  }
}
// rectangular a x b torus, tiles restricted to mask. returns 1 found, 0 none, -1 out of budget
static unsigned tmask;
static int torus_dfs(int a, int b, int r, int c) {
  if (c == b) { c = 0; r++; }
  if (r == a) return 1;
  if (--budget < 0) return -1;
  unsigned m = tmask;
  if (c) m &= H[grid[r][c - 1]];
  if (r) m &= V[grid[r - 1][c]];
  for (; m; m &= m - 1) {
    int t = __builtin_ctz(m);
    grid[r][c] = t;
    if (c == b - 1 && !(H[t] >> grid[r][0] & 1)) continue;
    if (r == a - 1 && !(V[t] >> grid[0][c] & 1)) continue;
    int x = torus_dfs(a, b, r, c + 1);
    if (x) return x;
  }
  return 0;
}
static void torus_verify(int a, int b) {
  for (int r = 0; r < a; r++)
    for (int c = 0; c < b; c++) {
      int t = grid[r][c];
      if (!(H[t] >> grid[r][(c + 1) % b] & 1) || !(V[t] >> grid[(r + 1) % a][c] & 1)) {
        fprintf(stderr, "TORUS VERIFY FAIL\n");
        exit(3);
      }
    }
}
static int torus_try(int a, int b, long nodes) {
  budget = nodes;
  int x = torus_dfs(a, b, 0, 0);
  if (x == 1) torus_verify(a, b);
  return x;
}

// exact failure memo for the square fill; the key is the whole profile, never a hash of it
#define MB 20
static u128 *memo_key;
static uint32_t *memo_stamp;
static uint32_t stamp;
static long memo_used;
static inline int memo_seen(u128 k) {
  uint64_t h = ((uint64_t)k ^ (uint64_t)(k >> 64) * 0xC2B2AE3D27D4EB4FULL) * 0x9E3779B97F4A7C15ULL >> (64 - MB);
  for (;;) {
    if (memo_stamp[h] != stamp) {
      if (memo_used > (3L << (MB - 2))) return 0;  // table full: forget it, costs time only
      memo_stamp[h] = stamp;
      memo_key[h] = k;
      memo_used++;
      return 0;
    }
    if (memo_key[h] == k) return 1;
    h = (h + 1) & ((1u << MB) - 1);
  }
}
static int fill_dfs(int d, int r, int c, int use_memo) {
  if (c == d) { c = 0; r++; }
  if (r == d) return 1;
  if (--budget < 0) return -1;
  if (use_memo && r > 0) {
    u128 k = ((u128)r << 96) | ((u128)c << 104);
    for (int i = 0; i < d; i++) k |= (u128)(i < c ? grid[r][i] : grid[r - 1][i]) << (3 * i);
    if (memo_seen(k)) return 0;
  }
  unsigned m = (1u << n) - 1;
  if (c) m &= H[grid[r][c - 1]];
  if (r) m &= V[grid[r - 1][c]];
  for (; m; m &= m - 1) {
    grid[r][c] = __builtin_ctz(m);
    int x = fill_dfs(d, r, c + 1, use_memo);
    if (x) return x;
  }
  return 0;
}
static void fill_verify(int d) {
  for (int r = 0; r < d; r++)
    for (int c = 0; c < d; c++) {
      int t = grid[r][c];
      if ((c + 1 < d && !(H[t] >> grid[r][c + 1] & 1)) || (r + 1 < d && !(V[t] >> grid[r + 1][c] & 1))) {
        fprintf(stderr, "FILL VERIFY FAIL\n");
        exit(3);
      }
    }
}
static int fill(int d, long nodes) {
  budget = nodes;
  int um = d >= 4;
  if (um) { stamp++; memo_used = 0; }
  int x = fill_dfs(d, 0, 0, um);
  if (x == 1) fill_verify(d);
  return x;
}

// Width-b cylinder test: rows are closed H-walks of length b, row s may sit below row r if V allows it
// column by column.  Rows with no surviving successor are deleted until nothing changes.  If any row is
// left there is an infinite descending path through a finite graph, hence a cycle, hence an (a x b)
// torus, which is extracted and checked.  Complete for width b at any height, up to its row cap.
#define CYLBITS 18
#define CYLCAP (1L << (CYLBITS - 1))
static uint64_t *cyl_rows;
static long cyl_nrows;
static uint64_t *cyl_tab_key;
static int32_t *cyl_tab_val;
static uint8_t *cyl_alive;
static inline long cyl_slot(uint64_t k) {
  uint64_t h = k * 0x9E3779B97F4A7C15ULL >> (64 - CYLBITS);
  while (cyl_tab_val[h] >= 0 && cyl_tab_key[h] != k) h = (h + 1) & ((1L << CYLBITS) - 1);
  return h;
}
static const uint8_t *cR, *cD;  // along-the-row and down-the-column relations
static unsigned ccore;
static int cyl_gen(int b, int i, int first, int prev, uint64_t key) {
  if (i == b) {
    if (!(cR[prev] >> first & 1)) return 0;
    if (cyl_nrows >= CYLCAP) return -1;
    long h = cyl_slot(key);
    cyl_tab_key[h] = key;
    cyl_tab_val[h] = cyl_nrows;
    cyl_rows[cyl_nrows++] = key;
    return 0;
  }
  for (unsigned m = i ? ccore & cR[prev] : ccore; m; m &= m - 1) {
    int t = __builtin_ctz(m);
    if (cyl_gen(b, i + 1, i ? first : t, t, key | (uint64_t)t << (3 * i))) return -1;
  }
  return 0;
}
// is there an alive row below `row`?  writes it to *out
static int cyl_succ(int b, uint64_t row, int i, int first, int prev, uint64_t key, uint64_t *out) {
  if (--budget < 0) return -1;
  if (i == b) {
    if (!(cR[prev] >> first & 1)) return 0;
    long h = cyl_slot(key);
    if (cyl_tab_val[h] < 0 || !cyl_alive[cyl_tab_val[h]]) return 0;
    *out = key;
    return 1;
  }
  unsigned m = ccore & cD[row >> (3 * i) & 7];
  if (i) m &= cR[prev];
  for (; m; m &= m - 1) {
    int t = __builtin_ctz(m);
    int x = cyl_succ(b, row, i + 1, i ? first : t, t, key | (uint64_t)t << (3 * i), out);
    if (x) return x;
  }
  return 0;
}
static int cylinder(const uint8_t *R, const uint8_t *D, unsigned core, int b, long nodes) {
  if (b > 21) return -1;
  cR = R; cD = D; ccore = core;
  memset(cyl_tab_val, 0xff, sizeof(int32_t) << CYLBITS);
  cyl_nrows = 0;
  if (cyl_gen(b, 0, 0, 0, 0)) return -1;
  budget = nodes;
  memset(cyl_alive, 1, cyl_nrows);
  long alive = cyl_nrows;
  uint64_t out;
  for (int changed = 1; changed && alive;) {
    changed = 0;
    for (long i = 0; i < cyl_nrows; i++) {
      if (!cyl_alive[i]) continue;
      int x = cyl_succ(b, cyl_rows[i], 0, 0, 0, 0, &out);
      if (x < 0) return -1;
      if (!x) { cyl_alive[i] = 0; alive--; changed = 1; }
    }
  }
  if (!alive) return 0;
  // walk down until a row repeats, then check the cycle as a torus
  long start = 0;
  while (!cyl_alive[start]) start++;
  static uint64_t *path;
  if (!path) path = malloc(sizeof(uint64_t) * (CYLCAP + 1));
  long len = 0;
  uint64_t cur = cyl_rows[start];
  for (;;) {
    long rep = -1;
    for (long i = len - 1; i >= 0; i--) if (path[i] == cur) { rep = i; break; }
    if (rep >= 0) {
      long a = len - rep;
      for (long y = 0; y < a; y++) {
        uint64_t r0 = path[rep + y], r1 = path[rep + (y + 1) % a];
        for (int c = 0; c < b; c++) {
          int t = r0 >> (3 * c) & 7, right = r0 >> (3 * ((c + 1) % b)) & 7, below = r1 >> (3 * c) & 7;
          if (!(R[t] >> right & 1) || !(D[t] >> below & 1)) { fprintf(stderr, "CYLINDER VERIFY FAIL\n"); exit(3); }
        }
      }
      return 1;
    }
    path[len++] = cur;
    budget = nodes;
    if (cyl_succ(b, cur, 0, 0, 0, 0, &out) != 1) { fprintf(stderr, "CYLINDER WALK FAIL\n"); exit(3); }
    cur = out;
  }
}
// returns score >= 1, 0 for torus found, -1 unresolved
static int softcap;
static int tori_width(unsigned core, int b) {
  return cylinder(H, V, core, b, 20000000L) == 1 || cylinder(V, H, core, b, 20000000L) == 1;
}
static int classify(void) {
  unsigned core = core_mask();
  if (core) {
    tmask = core;
    for (int a = 1; a <= 3; a++)
      for (int b = 1; b <= 3; b++)
        if (torus_try(a, b, 20000) == 1) return 0;
  }
  for (int d = 2; d <= HARDCAP; d++) {
    int x = fill(d, 200000000L);
    if (x == 0) return d - 1;
    if (core && x < 0) {
      for (int b = 1; b <= 21; b++)
        if (tori_width(core, b)) return 0;
      return -1;
    }
    if (x < 0) return -1;
    if (core && d == softcap) {
      for (int b = 1; b <= d; b++)
        if (tori_width(core, b)) return 0;
    } else if (core && d > softcap && tori_width(core, d)) return 0;
  }
  return -1;
}

// ---- driver
typedef struct { rel_t v; uint32_t cls; uint32_t mult; } vent;
static vent *vlist;
static long nvlist;
static long *vstart;
static int topmin;
static void print_rel(FILE *f, rel_t r) {
  for (int i = 0; i < n; i++) fprintf(f, "%s%x", i ? "," : "", (unsigned)(r >> (8 * i) & 0xff));
}
static void build_vlist(void) {
  vlist = malloc(nrels * sizeof(vent));
  for (long i = 0; i < nrels; i++) {
    rel_t t = full ? rel_transpose(rels[i]) : rels[i];
    if (full && t < rels[i]) continue;
    vlist[nvlist].v = rels[i];
    vlist[nvlist].cls = class_of[i];
    vlist[nvlist].mult = (full && t != rels[i]) ? 2 : 1;
    nvlist++;
  }
  // bucket by class so MODE 1 only pays for class(V) >= class(H)
  long *cnt = calloc(nclasses + 1, sizeof(long));
  for (long i = 0; i < nvlist; i++) cnt[vlist[i].cls + 1]++;
  for (long c = 0; c < nclasses; c++) cnt[c + 1] += cnt[c];
  vstart = malloc((nclasses + 1) * sizeof(long));
  memcpy(vstart, cnt, (nclasses + 1) * sizeof(long));
  vent *sorted = malloc(nvlist * sizeof(vent));
  for (long i = 0; i < nvlist; i++) sorted[cnt[vlist[i].cls]++] = vlist[i];
  free(vlist);
  vlist = sorted;
  free(cnt);
}
static void run_class(long c, const char *outdir) {
  char path[480], tmp[512];
  snprintf(path, sizeof path, "%s/c%06ld.txt", outdir, c);
  if (access(path, F_OK) == 0) return;
  snprintf(tmp, sizeof tmp, "%s.tmp%d", path, getpid());
  FILE *f = fopen(tmp, "w");
  if (!f) { perror(tmp); exit(1); }
  uint64_t hist[HARDCAP + 2] = {0}, plane = 0, pairs = 0, unres = 0;
  load_rel(class_rep[c], H);
  invert(H, Hi);
  for (long i = full ? vstart[c] : 0; i < nvlist; i++) {
    int same = !full || vlist[i].cls == (uint32_t)c;
    uint64_t w = (uint64_t)class_size[c] * vlist[i].mult * (same ? 1 : 2);
    load_rel(vlist[i].v, V);
    invert(V, Vi);
    int s = classify();
    pairs++;
    if (s == 0) plane += w;
    else if (s > 0) {
      hist[s] += w;
      if (s >= topmin) {
        fprintf(f, "top %d %lu H ", s, (unsigned long)w);
        print_rel(f, class_rep[c]);
        fprintf(f, " V ");
        print_rel(f, vlist[i].v);
        fputc('\n', f);
      }
    } else {
      unres += w;
      fprintf(f, "unres %lu H ", (unsigned long)w);
      print_rel(f, class_rep[c]);
      fprintf(f, " V ");
      print_rel(f, vlist[i].v);
      fputc('\n', f);
    }
  }
  fprintf(f, "pairs %lu\nplane %lu\nunresolved %lu\n", (unsigned long)pairs, (unsigned long)plane, (unsigned long)unres);
  for (int s = 1; s <= HARDCAP; s++)
    if (hist[s]) fprintf(f, "score %d %lu\n", s, (unsigned long)hist[s]);
  fprintf(f, "done\n");
  if (fclose(f)) { perror(tmp); exit(1); }
  rename(tmp, path);
}
int main(int ac, char **av) {
  if (ac < 5) {
    fprintf(stderr, "usage: %s N MODE OUTDIR WORKERS [TOPMIN] [SOFTCAP]\n", av[0]);
    return 1;
  }
  n = atoi(av[1]);
  full = atoi(av[2]);
  const char *outdir = av[3];
  int workers = atoi(av[4]);
  topmin = ac > 5 ? atoi(av[5]) : 1 << 30;
  softcap = ac > 6 ? atoi(av[6]) : n + 2;
  mkdir(outdir, 0755);
  gen_e(0, 0);
  qsort(rels, nrels, sizeof(rel_t), cmp_rel);
  for (long i = 1; i < nrels; i++)
    if (rels[i] == rels[i - 1]) { fprintf(stderr, "duplicate relation\n"); return 2; }
  if (nrels != closed_form(n)) { fprintf(stderr, "relations %ld != closed form %ld\n", nrels, closed_form(n)); return 2; }
  build_perms();
  build_classes();
  build_vlist();
  fprintf(stderr, "n=%d relations=%ld classes=%ld vlist=%ld\n", n, nrels, nclasses, nvlist);
  long *next = mmap(NULL, sizeof(long), PROT_READ | PROT_WRITE, MAP_SHARED | MAP_ANONYMOUS, -1, 0);
  *next = 0;
  for (int w = 0; w < workers; w++) {
    if (fork() == 0) {
      memo_key = malloc(sizeof(u128) << MB);
      memo_stamp = calloc(1L << MB, sizeof(uint32_t));
      cyl_rows = malloc(sizeof(uint64_t) * CYLCAP);
      cyl_alive = malloc(CYLCAP);
      cyl_tab_key = malloc(sizeof(uint64_t) << CYLBITS);
      cyl_tab_val = malloc(sizeof(int32_t) << CYLBITS);
      for (;;) {
        long c = __atomic_fetch_add(next, 1, __ATOMIC_RELAXED);
        if (c >= nclasses) _exit(0);
        run_class(c, outdir);
      }
    }
  }
  int st, bad = 0;
  while (wait(&st) > 0)
    if (!WIFEXITED(st) || WEXITSTATUS(st)) bad = 1;
  fprintf(stderr, "finished, %s\n", bad ? "A WORKER FAILED" : "all workers ok");
  return bad;
}
