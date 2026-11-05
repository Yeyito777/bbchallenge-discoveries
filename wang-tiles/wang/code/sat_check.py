#!/usr/bin/env python3
"""Re-solve champion squares with an off-the-shelf SAT solver (needs python-sat).

usage: sat_check.py FILE D [FILE D ...]   each FILE line is a tile list in wiki format, '#' starts a comment
       sat_check.py --wiki                the wiki's champions, each at its listed score

For each set: dxd must be SAT, with the model checked edge by edge, and (d+1)x(d+1) must be UNSAT.
"""
import os
import sys

from pysat.solvers import Cadical153

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gate_champions import CHAMPS, parse


def solve(tiles, d):
    n = len(tiles)
    var = lambda r, c, t: r * d * n + c * n + t + 1
    with Cadical153() as s:
        for r in range(d):
            for c in range(d):
                s.add_clause([var(r, c, t) for t in range(n)])
                for a in range(n):
                    for b in range(n):
                        if c + 1 < d and tiles[a][1] != tiles[b][3]:
                            s.add_clause([-var(r, c, a), -var(r, c + 1, b)])
                        if r + 1 < d and tiles[a][2] != tiles[b][0]:
                            s.add_clause([-var(r, c, a), -var(r + 1, c, b)])
        if not s.solve():
            return None
        m = set(x for x in s.get_model() if x > 0)
    g = [[next(t for t in range(n) if var(r, c, t) in m) for c in range(d)] for r in range(d)]
    for r in range(d):
        for c in range(d):
            t = tiles[g[r][c]]
            assert c + 1 == d or t[1] == tiles[g[r][c + 1]][3]
            assert r + 1 == d or t[2] == tiles[g[r + 1][c]][0]
    return g


def main():
    jobs = []
    if sys.argv[1] == "--wiki":
        jobs = [(s, d) for d, s in CHAMPS.values()]
    else:
        for i in range(1, len(sys.argv), 2):
            d = int(sys.argv[i + 1])
            for line in open(sys.argv[i]):
                line = line.split("#")[0].strip()
                if line:
                    jobs.append((line, d))
    bad = 0
    for s, d in jobs:
        tiles = parse(s)
        a = solve(tiles, d) is not None
        b = solve(tiles, d + 1) is None
        bad += not (a and b)
        print(f"n={len(tiles)} d={d} sat_at_d={a} unsat_at_d+1={b}  {s}", flush=True)
    print(f"{len(jobs)} sets checked, {bad} bad")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
