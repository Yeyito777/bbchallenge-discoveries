// macrosim.cpp TM TAPE MAXSTEPS BLOCK [PRINTEVERY]: run-compressed block simulation with chain steps. Prints the exact halting step.
// Tape: two stacks of (block, count). A block seen from one side in a state is simulated once and memoised; if the head leaves it on
// the far side in the same state, the whole run is rewritten at once.
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cstdint>
#include <vector>
#include <string>
typedef unsigned __int128 u128;
static int W[2][4], D[2][4], N[2][4]; static int B;
struct R { int nb; int8_t st; int8_t dir; int32_t steps; int8_t done; int8_t halted; };
static std::vector<R> memo;
static R &sim(int b, int st, int dir) { // dir = 1: entered from the left, head on cell 0
  size_t k = ((size_t)b << 2) | (st << 1) | (dir > 0);
  R &r = memo[k]; if (r.done) return r; r.done = 1;
  int p = dir > 0 ? 0 : B - 1, s = st, x = b; long n = 0;
  for (;;) { int y = (x >> (2 * p)) & 3; if (N[s][y] < 0) { r.halted = 1; r.nb = x; r.st = s; r.steps = n + 1; r.dir = p; return r; }
    x = (x & ~(3 << (2 * p))) | (W[s][y] << (2 * p)); p += D[s][y]; s = N[s][y]; n++;
    if (n > 100000000) { printf("loop inside block\n"); exit(0); }
    if (p < 0) { r.nb = x; r.st = s; r.dir = -1; r.steps = n; return r; } if (p >= B) { r.nb = x; r.st = s; r.dir = 1; r.steps = n; return r; } }
}
struct Tok { int b; u128 c; };
static void push(std::vector<Tok> &v, int b, u128 c) { if (!v.empty() && v.back().b == b) v.back().c += c; else v.push_back({b, c}); }
static void pr(u128 x, char *o) { char t[64]; int i = 0; if (!x) t[i++] = '0'; while (x) { t[i++] = '0' + (int)(x % 10); x /= 10; } int j = 0; while (i) o[j++] = t[--i]; o[j] = 0; }
int main(int ac, char **av) {
  char *c = av[1]; for (int a = 0; a < 2; a++) for (int b = 0; b < 4; b++) { char *p = c + a * 13 + b * 3; if (p[0] == '-') N[a][b] = -1; else { W[a][b] = p[0] - '0'; D[a][b] = p[1] == 'R' ? 1 : -1; N[a][b] = p[2] - 'A'; } }
  std::vector<int> T; int hd = 0; for (char *p = av[2]; *p; p++) { if (*p == '[') { hd = T.size(); continue; } if (*p == ']') continue; T.push_back(*p - '0'); }
  double mx = atof(av[3]); B = atoi(av[4]); long every = ac > 5 ? atol(av[5]) : 0; memo.assign((size_t)1 << (2 * B + 2), R{0,0,0,0,0,0});
  // Lay out the start tape so that the head starts inside a real block; the first few steps are simulated cell by cell.
  long off = 0; std::vector<int> cells(4096, 0); int org = 2048; for (size_t i = 0; i < T.size(); i++) cells[org + i - hd] = T[i];
  long h = org; int st = 0; u128 steps = 0;
  // align: run plain steps until the head crosses a block boundary (grid anchored at org)
  long bh = (h % B + B) % B;
  int dirIn; std::vector<Tok> L, Rr; int cur;
  for (;;) { int y = cells[h]; if (N[st][y] < 0) { printf("HALT at step %llu\n", (unsigned long long)steps + 1); return 0; }
    cells[h] = W[st][y]; int d = D[st][y]; st = N[st][y]; h += d; steps++;
    if (h % B == 0 && d > 0) { dirIn = 1; break; } if ((h + 1) % B == 0 && d < 0) { dirIn = -1; break; } }
  long bl = h - ((h % B + B) % B); // block start containing the head
  for (long b = 0; b + B <= bl; b += B) { int v = 0; for (int i = 0; i < B; i++) v |= cells[b + i] << (2 * i); if (v || !L.empty()) push(L, v, 1); }
  for (long b = (4096 / B - 1) * B; b >= bl + B; b -= B) { int v = 0; for (int i = 0; i < B; i++) v |= cells[b + i] << (2 * i); if (v || !Rr.empty()) push(Rr, v, 1); }
  { int v = 0; for (int i = 0; i < B; i++) v |= cells[bl + i] << (2 * i); cur = v; }
  (void)off; (void)bh; long iters = 0; int dir = dirIn; char buf[64];
  for (;;) {
    R &r = sim(cur, st, dir);
    if (r.halted) { steps += r.steps; pr(steps, buf); printf("HALT at step %s state %c\n", buf, 'A' + r.st); return 0; }
    std::vector<Tok> &ahead = r.dir > 0 ? Rr : L, &behind = r.dir > 0 ? L : Rr;
    // chain: leaving in the entering direction, same state, and the next run is the same block
    if (r.dir == dir && r.st == st && !ahead.empty() && ahead.back().b == cur) {
      u128 n = ahead.back().c + 1; steps += n * r.steps; push(behind, r.nb, n); ahead.pop_back(); dir = r.dir;
      if (!ahead.empty()) { cur = ahead.back().b; if (--ahead.back().c == 0) ahead.pop_back(); } else cur = 0;
    } else {
      steps += r.steps; push(behind, r.nb, 1); st = r.st; dir = r.dir;
      if (!ahead.empty()) { cur = ahead.back().b; if (--ahead.back().c == 0) ahead.pop_back(); } else cur = 0;
    }
    iters++;
    if (every && iters % every == 0) { pr(steps, buf); size_t nl = L.size(), nr = Rr.size(); printf("%s iters %ld tokens %zu %zu\n", buf, iters, nl, nr); fflush(stdout); }
    if ((double)steps > mx) { pr(steps, buf); printf("no halt by step %s, iters %ld tokens %zu %zu\n", buf, iters, L.size(), Rr.size()); return 0; }
  }
}
