#!/usr/bin/env python3
"""Gate: score the wiki's BB_WT champions (revid 8879) directly from their colours.

Tile format as on the wiki: [TOP,RIGHT,BOTTOM,LEFT].  For each champion: build an explicit dxd tiling,
check it edge by edge, and show the (d+1)x(d+1) square is refused by an exact constraint search, with
no symmetry or colour tricks.  A set listed with score d must also refuse every larger square, which
follows from refusing d+1.
"""
import sys

CHAMPS = {
    1: (1, "[1,0,0,0]"),
    2: (2, "[1,0,2,0] [2,0,3,0]"),
    3: (3, "[1,0,2,0] [2,0,3,0] [3,0,4,0]"),
    4: (4, "[1,0,2,0] [2,0,3,0] [3,0,4,0] [4,0,5,0]"),
    5: (6, "[1,0,2,0] [2,0,3,0] [3,0,4,0] [4,6,1,5] [4,5,2,6]"),
    6: (8, "[1,0,2,0] [2,0,3,0] [3,0,4,0] [4,0,5,0] [5,7,1,6] [5,6,2,7]"),
    7: (11, "[1,0,2,0] [2,0,3,0] [3,0,4,0] [4,0,5,0] [5,7,1,6] [5,6,2,7] [4,6,3,7]"),
    8: (14, "[1,0,2,0] [2,0,3,0] [3,0,4,0] [4,0,5,0] [5,0,6,0] [6,8,1,7] [6,7,2,8] [5,7,3,8]"),
    9: (17, "[1,0,2,0] [2,0,3,0] [3,0,4,0] [4,0,5,0] [5,0,6,0] [6,0,7,0] [7,9,1,8] [7,8,2,9] [6,8,3,9]"),
}


def parse(s):
    return [tuple(int(x) for x in t.strip("[]").split(",")) for t in s.split()]


def square(tiles, d):
    """Return a dxd tiling or None: arc consistency on tile-set domains, branch on the smallest domain."""
    n = len(tiles)
    right = [sum(1 << j for j in range(n) if tiles[i][1] == tiles[j][3]) for i in range(n)]
    left = [sum(1 << j for j in range(n) if tiles[j][1] == tiles[i][3]) for i in range(n)]
    below = [sum(1 << j for j in range(n) if tiles[i][2] == tiles[j][0]) for i in range(n)]
    above = [sum(1 << j for j in range(n) if tiles[j][2] == tiles[i][0]) for i in range(n)]
    sys.setrecursionlimit(10000)

    def image(mask, table):
        out = 0
        i = 0
        while mask:
            if mask & 1:
                out |= table[i]
            mask >>= 1
            i += 1
        return out

    def propagate(dom, todo):
        while todo:
            x = todo.pop()
            r, c = divmod(x, d)
            for ok, y, table in (
                (c + 1 < d, x + 1, right),
                (c > 0, x - 1, left),
                (r + 1 < d, x + d, below),
                (r > 0, x - d, above),
            ):
                if ok:
                    m = dom[y] & image(dom[x], table)
                    if m != dom[y]:
                        if not m:
                            return False
                        dom[y] = m
                        todo.append(y)
        return True

    def rec(dom):
        best, bc = -1, n + 1
        for x, m in enumerate(dom):
            k = bin(m).count("1")
            if 1 < k < bc:
                best, bc = x, k
        if best < 0:
            return dom
        m = dom[best]
        for t in range(n):
            if m >> t & 1:
                dom2 = dom[:]
                dom2[best] = 1 << t
                if propagate(dom2, [best]):
                    got = rec(dom2)
                    if got:
                        return got
        return None

    dom = [(1 << n) - 1] * (d * d)
    if not propagate(dom, list(range(d * d))):
        return None
    got = rec(dom)
    return [m.bit_length() - 1 for m in got] if got else None


def main():
    good = True
    print("n claimed tiles_dxd refuses_(d+1)x(d+1)")
    for n, (d, s) in CHAMPS.items():
        tiles = parse(s)
        assert len(tiles) == n and len(set(tiles)) == n
        g = square(tiles, d)
        ok = g is not None
        if ok:
            for r in range(d):
                for c in range(d):
                    t = tiles[g[r * d + c]]
                    if c + 1 < d:
                        ok &= t[1] == tiles[g[r * d + c + 1]][3]
                    if r + 1 < d:
                        ok &= t[2] == tiles[g[(r + 1) * d + c]][0]
        refused = square(tiles, d + 1) is None
        good &= ok and refused
        print(n, d, ok, refused, flush=True)
    print("ALL OK" if good else "GATE FAILED")
    return 0 if good else 1


if __name__ == "__main__":
    sys.exit(main())
