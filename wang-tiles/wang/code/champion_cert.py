#!/usr/bin/env python3
"""Champion certificates that need no search code.

usage: champion_cert.py write NAME "TILES" D OUTDIR   write NAME.tiles, NAME.d{D}.tiling, NAME.d{D+1}.cnf
       champion_cert.py check NAME.tiles D DIR        check tiling edge by edge, regenerate the CNF and compare

Tiles are in the wiki's format [TOP,RIGHT,BOTTOM,LEFT].  In the CNF, variable r*d*n + c*n + t + 1 means cell
(r,c) holds tile t.  Each cell gets one at-least-one clause, and each pair of neighbouring cells gets a
binary clause for every tile pair whose touching colours differ.  So the CNF is satisfiable exactly when
the set tiles a dxd square.  Standard library only.
"""
import os
import sys


def parse(s):
    return [tuple(int(x) for x in t.strip("[]").split(",")) for t in s.split()]


def cnf_text(tiles, d):
    n = len(tiles)
    var = lambda r, c, t: r * d * n + c * n + t + 1
    clauses = []
    for r in range(d):
        for c in range(d):
            clauses.append([var(r, c, t) for t in range(n)])
            for a in range(n):
                for b in range(n):
                    if c + 1 < d and tiles[a][1] != tiles[b][3]:
                        clauses.append([-var(r, c, a), -var(r, c + 1, b)])
                    if r + 1 < d and tiles[a][2] != tiles[b][0]:
                        clauses.append([-var(r, c, a), -var(r + 1, c, b)])
    out = [f"p cnf {d * d * n} {len(clauses)}"]
    out += [" ".join(map(str, cl)) + " 0" for cl in clauses]
    return "\n".join(out) + "\n"


def check_tiling(tiles, grid, d):
    assert len(grid) == d and all(len(row) == d for row in grid), "tiling has the wrong shape"
    for r in range(d):
        for c in range(d):
            t = tiles[grid[r][c]]
            if c + 1 < d:
                assert t[1] == tiles[grid[r][c + 1]][3], f"bad horizontal edge at {r},{c}"
            if r + 1 < d:
                assert t[2] == tiles[grid[r + 1][c]][0], f"bad vertical edge at {r},{c}"


def main():
    if sys.argv[1] == "write":
        sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
        from gate_champions import square

        name, s, d, out = sys.argv[2], sys.argv[3], int(sys.argv[4]), sys.argv[5]
        tiles = parse(s)
        g = square(tiles, d)
        assert g is not None, "no tiling"
        grid = [g[r * d : (r + 1) * d] for r in range(d)]
        check_tiling(tiles, grid, d)
        with open(os.path.join(out, name + ".tiles"), "w") as f:
            f.write(s.strip() + "\n")
        with open(os.path.join(out, f"{name}.d{d}.tiling"), "w") as f:
            for row in grid:
                f.write(" ".join(map(str, row)) + "\n")
        with open(os.path.join(out, f"{name}.d{d + 1}.cnf"), "w") as f:
            f.write(cnf_text(tiles, d + 1))
        return 0
    path, d, cdir = sys.argv[2], int(sys.argv[3]), sys.argv[4]
    name = os.path.basename(path)[: -len(".tiles")]
    tiles = parse(open(path).read())
    grid = [list(map(int, l.split())) for l in open(os.path.join(cdir, f"{name}.d{d}.tiling"))]
    check_tiling(tiles, grid, d)
    used = sorted(set(x for row in grid for x in row))
    same = open(os.path.join(cdir, f"{name}.d{d + 1}.cnf")).read() == cnf_text(tiles, d + 1)
    print(f"{name}: {len(tiles)} tiles, {d}x{d} tiling valid, uses tiles {used}, {d + 1}x{d + 1} CNF matches the tiles: {same}")
    return 0 if same else 1


if __name__ == "__main__":
    sys.exit(main())
