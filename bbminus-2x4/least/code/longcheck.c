// longcheck.c TAPE CAP < machines: direct simulation of machines with a non-halting record. Any halt within CAP steps is an error.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <omp.h>
#include "tape.h"
int main(int ac, char **av) {
  Tape T; tape_parse(av[1], &T); long cap = atol(av[2]); size_t tn = 2 * (size_t)cap + 4096; if (tn > (1ull << 30)) tn = 1ull << 30;
  size_t mc = 1 << 20, nm = 0; char (*names)[32] = malloc(mc * 32); char buf[128];
  while (fgets(buf, sizeof buf, stdin)) { buf[strcspn(buf, "\n ")] = 0; if (nm == mc) { mc *= 2; names = realloc(names, mc * 32); } strncpy(names[nm++], buf, 31); }
  long halts = 0, runs = 0;
#pragma omp parallel
  { uint8_t *tp = calloc(tn, 1);
#pragma omp for schedule(dynamic, 16)
    for (size_t i = 0; i < nm; i++) { int8_t W[2][4], D[2][4], N[2][4]; const char *c = names[i];
      for (int a = 0; a < 2; a++) for (int b = 0; b < 4; b++) { const char *p = c + a * 13 + b * 3; if (p[0] == '-') N[a][b] = -1; else { W[a][b] = p[0] - '0'; D[a][b] = p[1] == 'R' ? 1 : -1; N[a][b] = p[2] - 'A'; } }
      size_t h = tn / 2, lo = h, hi = h; for (int k = 0; k < T.nmid; k++) tp[h + k - T.head] = T.mid[k]; lo = h - T.head; hi = h - T.head + T.nmid - 1; int st = 0; long t = 0;
      for (; t < cap; t++) { int y = tp[h]; if (N[st][y] < 0) { 
#pragma omp critical
          { printf("HALT %s at step %ld\n", c, t + 1); fflush(stdout); }
#pragma omp atomic
          halts++;
          break; }
        tp[h] = W[st][y]; h += D[st][y]; st = N[st][y]; if (h < lo) lo = h; if (h > hi) hi = h; if (h < 8 || h > tn - 8) break; }
      memset(tp + lo, 0, hi - lo + 1);
#pragma omp atomic
      runs++; }
  }
  printf("%ld machines simulated to %ld steps, %ld halted\n", runs, cap, halts); return halts != 0;
}
