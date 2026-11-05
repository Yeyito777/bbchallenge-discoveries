#!/usr/bin/env python3
"""Hill-climb step: try every extra tile over a set's colours plus fresh ones, and report the exact scores.

usage: extend_one_tile.py "TILES" D MAXD   (needs python-sat for the all-tiles-used check)
Prints every non-plane extension with a score above D, and one extension with score D that has a DxD
tiling using all of its tiles.  A set still tiling MAXD x MAXD is listed as "unsettled" and not claimed.
"""
import itertools
import os
import sys

from pysat.solvers import Cadical153

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gate_champions import parse, square


def uses_all(tiles, d):
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
        for t in range(n):
            s.add_clause([var(r, c, t) for r in range(d) for c in range(d)])
        return s.solve()


def main():
    base = parse(sys.argv[1])
    d0, maxd = int(sys.argv[2]), int(sys.argv[3])
    cols = sorted(set(c for t in base for c in t))
    fresh = [max(cols) + 1 + i for i in range(4)]
    tried = same = unsettled = 0
    example = None
    for t in itertools.product(cols + fresh, repeat=4):
        if t in base:
            continue
        fs = []
        for x in t:
            if x in fresh and x not in fs:
                fs.append(x)
        if fs != fresh[: len(fs)]:
            continue  # fresh colours are interchangeable
        tried += 1
        s = base + [t]
        d = d0
        while d < maxd and square(s, d + 1) is not None:
            d += 1
        if d >= maxd:
            unsettled += 1
        elif d > d0:
            print("HIGHER", d, " ".join("[" + ",".join(map(str, x)) + "]" for x in s), flush=True)
        else:
            same += 1
            if example is None and uses_all(s, d0):
                example = s
                print("USES_ALL", d0, " ".join("[" + ",".join(map(str, x)) + "]" for x in s), flush=True)
    print(f"tried {tried} extensions: same score {same}, unsettled at {maxd}x{maxd} {unsettled}")


if __name__ == "__main__":
    main()
