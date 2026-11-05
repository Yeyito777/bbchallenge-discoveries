#!/usr/bin/env python3
# halt_check.py: plain Python simulator (dict tape). Lines of TAPE TM on stdin; prints the step at which each machine first
# reaches an undefined transition, counting that step. Finite tapes only.
import re, sys
for line in sys.stdin:
    if not line.strip(): continue
    tape, c = line.split()[:2]
    r = [c[i:i + 3] for i in (0, 3, 6, 9, 13, 16, 19, 22)]
    tr = {(i // 4, i % 4): (int(x[0]), 1 if x[1] == 'R' else -1, ord(x[2]) - 65) for i, x in enumerate(r) if x[0] != '-'}
    m = re.fullmatch(r'(\d*)\[(\d)\](\d*)', tape); t = {}
    for i, ch in enumerate(m[1]): t[i - len(m[1])] = int(ch)
    t[0] = int(m[2])
    for i, ch in enumerate(m[3]): t[i + 1] = int(ch)
    h = s = n = 0
    while True:
        k = (s, t.get(h, 0)); n += 1
        if k not in tr: break
        w, d, s = tr[k]; t[h] = w; h += d
    print(tape, c, n)
