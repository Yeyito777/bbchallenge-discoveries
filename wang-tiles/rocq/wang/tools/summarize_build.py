#!/usr/bin/env python3
"""Summarize a `make TIMED=1` log: time (coqc plus coqnative) and peak memory per kind of file.

usage: summarize_build.py LOG"""
import re
import sys

# one row per .vo: the time of coqc plus that of coqnative (the .vo.native line), the larger peak memory
acc = {}
for l in open(sys.argv[1]):
    m = re.match(r"(\S+\.vo)(\.native)? \(real: ([\d.]+), user: ([\d.]+), sys: [\d.]+, mem: (\d+) ko\)", l)
    if m:
        t, mem = acc.get(m.group(1), (0.0, 0.0))
        acc[m.group(1)] = (t + float(m.group(3)), max(mem, int(m.group(5)) / 1e6))
rows = [(k, t, mem) for k, (t, mem) in acc.items()]
kinds = [
    ("n7/Check7_j000.vo", "job 0 check (largest subtree)"),
    ("n7/Check7_j001.vo", "job 1 check (second largest)"),
    ("n7/Check7_j", "other job checks"),
    ("n7/Job7_", "job data files"),
    ("n7/Tori7", "torus table files"),
    ("n7/Wang7_Prefixes.vo", "reference list"),
    ("n7/Jobs7.vo", "job list (loads every job)"),
    ("WangTiles_Theorem7.vo", "BB_WT_7"),
    ("WangTiles_Theorem.vo", "n = 5, 6 checks and champions"),
    ("", "all other files"),
]
done = set()
print("| Files | Count | Time each (s) | Sum (s) | Peak memory (GB) |")
print("|---|---|---|---|---|")
for pre, name in kinds:
    sel = [r for r in rows if r[0] not in done and r[0].startswith(pre)]
    if not sel:
        continue
    done.update(r[0] for r in sel)
    t = sorted(r[1] for r in sel)
    m = max(r[2] for r in sel)
    each = "%.0f" % t[0] if len(t) == 1 else "%.0f–%.0f, median %.0f" % (t[0], t[-1], t[len(t) // 2])
    print("| %s | %d | %s | %.0f | %.2f |" % (name, len(sel), each, sum(t), m))
print()
print("total %.0f core-seconds (%.1f core-hours), %d files" % (sum(r[1] for r in rows), sum(r[1] for r in rows) / 3600, len(rows)))
