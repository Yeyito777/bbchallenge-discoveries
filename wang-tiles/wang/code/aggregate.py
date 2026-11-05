#!/usr/bin/env python3
"""Sum per-class outputs of wt_pairs (or wt_csp) and check the labelled total equals relations^2."""
import glob
import os
import sys
from collections import Counter

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gate_counts import formula

n, d = int(sys.argv[1]), sys.argv[2]
hist = Counter()
plane = unres = pairs = files = 0
top = []
unres_lines = []
for p in sorted(glob.glob(os.path.join(d, "c*.txt"))):
    lines = open(p).read().split("\n")
    if "done" not in lines:
        raise SystemExit(f"incomplete {p}")
    files += 1
    for l in lines:
        w = l.split()
        if not w:
            continue
        if w[0] == "pairs":
            pairs += int(w[1])
        elif w[0] == "plane":
            plane += int(w[1])
        elif w[0] == "unresolved":
            unres += int(w[1])
        elif w[0] == "score":
            hist[int(w[1])] += int(w[2])
        elif w[0] == "top":
            top.append(l)
        elif w[0] == "unres":
            unres_lines.append(l)
total = plane + unres + sum(hist.values())
expect = formula(n) ** 2
print(f"n={n} files={files} pairs_run={pairs} labelled_total={total} expect={expect} {'OK' if total == expect else 'MISMATCH'}")
print(f"plane {plane}")
for s in sorted(hist):
    print(f"score {s} {hist[s]}")
print(f"unresolved {unres}")
print(f"best {max(hist) if hist else 0}")
if len(sys.argv) > 3:
    with open(sys.argv[3], "w") as f:
        for l in top + unres_lines:
            f.write(l + "\n")
