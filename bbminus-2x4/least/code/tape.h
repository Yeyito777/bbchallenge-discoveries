// tape.h: start tape syntax shared by tree.c, cps.c, repwl.c.
//   [(LEFTPERIOD)] CELLS [HEAD] CELLS [(RIGHTPERIOD)]     e.g. 2[0]   (0123)[0]123(0123)
// Everything else is blank; a period word repeats forever in tape order, its last letter nearest to the finite part
// on the left side and its first letter nearest on the right side.
#ifndef TAPE_H
#define TAPE_H
#include <stdint.h>
#include <string.h>
typedef struct { uint8_t lp[64], rp[64], mid[256]; int nlp, nrp, nmid, head; } Tape;
static void tape_parse(const char *s, Tape *t) {
  memset(t, 0, sizeof *t); const char *p = s; t->nlp = t->nrp = 1;
  if (*p == '(') { p++; t->nlp = 0; while (*p != ')') t->lp[t->nlp++] = *p++ - '0'; p++; }
  while (*p && *p != '(') { if (*p == '[') { t->head = t->nmid; p++; continue; } if (*p == ']') { p++; continue; } t->mid[t->nmid++] = *p++ - '0'; }
  if (*p == '(') { p++; t->nrp = 0; while (*p != ')') t->rp[t->nrp++] = *p++ - '0'; }
}
// Cell at position x relative to the head.
static inline uint8_t tape_at(const Tape *t, long x) {
  long i = x + t->head;
  if (i >= 0 && i < t->nmid) return t->mid[i];
  if (i >= t->nmid) return t->rp[(i - t->nmid) % t->nrp];
  long k = -1 - i; return t->lp[t->nlp - 1 - k % t->nlp];
}
static int tape_uniform_blank(const Tape *t) { for (int i = 0; i < t->nlp; i++) if (t->lp[i]) return 0; for (int i = 0; i < t->nrp; i++) if (t->rp[i]) return 0; return 1; }
static int tape_symbols(const Tape *t) { int m = 1; for (int i = 0; i < t->nmid; i++) m |= 1 << t->mid[i]; for (int i = 0; i < t->nlp; i++) m |= 1 << t->lp[i]; for (int i = 0; i < t->nrp; i++) m |= 1 << t->rp[i]; return m; }
#endif
