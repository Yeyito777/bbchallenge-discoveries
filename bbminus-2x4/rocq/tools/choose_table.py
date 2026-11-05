#!/usr/bin/env python3
"""Choose one decider per holdout machine from parameter-sweep results.

usage: choose_table.py ALL_UNK SWEEPDIR... > ASSIGN

A sweep result is SPEC.unk (machines left undecided) and SPEC.log (with the summary line, written at the end).
Specs whose log has no summary line (timed out) are ignored. Specs are preferred in the order cheap-first
listed in PREF; machines no spec decides get `aut` (closed automaton certificate).
"""
import os
import sys

allm = [l.strip() for l in open(sys.argv[1]) if l.strip()]
decided = {}
for d in sys.argv[2:]:
    for f in os.listdir(d):
        if not f.endswith('.log'):
            continue
        spec = f[:-4]
        log = open(os.path.join(d, f)).read()
        if 'unknown' not in log:
            continue
        unk = set(l.strip() for l in open(os.path.join(d, spec + '.unk')) if l.strip())
        decided[spec.replace('_', ' ')] = set(allm) - unk


def cost(spec):
    p = spec.split()
    k = p[0]
    a = [int(v) for v in p[1:]]
    base = {'ng2': 0, 'ng1': 1, 'lru': 2, 'rwl': 3}[k]
    return (base, sum(a[:-1]), a[-1])


specs = sorted(decided, key=cost)
assign = {}
for m in allm:
    for s in specs:
        if m in decided[s]:
            assign[m] = s
            break
    else:
        assign[m] = 'aut'
from collections import Counter
c = Counter(assign.values())
for s, n in sorted(c.items(), key=lambda x: -x[1]):
    print(f'{n:5d} {s}', file=sys.stderr)
for m in allm:
    print(m, assign[m])
