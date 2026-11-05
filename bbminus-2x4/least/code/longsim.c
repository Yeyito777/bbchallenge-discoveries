// longsim.c: direct simulation with periodic run-length tape prints. Usage: longsim TM TAPE MAXSTEPS PRINTS_PER_DOUBLING
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
int main(int ac, char **av) {
  int8_t W[2][4], D[2][4], N[2][4]; char *c = av[1];
  for (int a = 0; a < 2; a++) for (int b = 0; b < 4; b++) { char *p = c + a * 13 + b * 3; if (p[0] == '-') N[a][b] = -1; else { W[a][b] = p[0] - '0'; D[a][b] = p[1] == 'R' ? 1 : -1; N[a][b] = p[2] - 'A'; } }
  size_t tn = 1ull << 28, ctr = tn / 2; uint8_t *tp = calloc(tn, 1); int L0 = 0, H0 = 0; char *s = av[2]; uint8_t T[64];
  for (char *p = s; *p; p++) { if (*p == '[') { H0 = L0; continue; } if (*p == ']') continue; T[L0++] = *p - '0'; }
  for (int i = 0; i < L0; i++) tp[ctr + i - H0] = T[i];
  long mx = atol(av[3]); double f = atof(av[4]); double nextd = 1000; size_t h = ctr, lo = ctr - H0, hi = ctr - H0 + L0 - 1; int st = 0; long i = 0;
  for (; i < mx; i++) {
    int y = tp[h]; if (N[st][y] < 0) { printf("HALT at step %ld state %c symbol %d\n", i + 1, 'A' + st, y); return 0; }
    tp[h] = W[st][y]; h += D[st][y]; st = N[st][y]; if (h < lo) lo = h; if (h > hi) { hi = h; }
    if (h <= 8 || h >= tn - 8) { printf("tape limit at %ld\n", i); return 1; }
    if (i >= (long)nextd) { nextd *= f; printf("%ld %c off=%ld:", i, 'A' + st, (long)h - (long)lo);
      for (size_t x = lo; x <= hi; ) { size_t j = x; while (j <= hi && tp[j] == tp[x]) j++; if (j - x > 1) printf(" %d^%zu", tp[x], j - x); else printf(" %d", tp[x]); x = j; if (x > lo + 4000) { printf(" ..."); break; } }
      printf("\n"); }
  }
  printf("no halt in %ld\n", mx);
  return 0;
}
