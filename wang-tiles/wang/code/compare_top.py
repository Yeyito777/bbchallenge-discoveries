#!/usr/bin/env python3
"""Compare implementation A's top-scoring pairs with implementation B's holdouts at the same level.

usage: compare_top.py N D A_TOP_FILE B_HOLD_FILE OUT_FILE

A lists pairs (H,V) with score >= its threshold; B lists the minimal pairs that fill DxD with no torus.
Checks, all up to tile relabelling and the eight square symmetries:
  every B holdout refuses (D+1)x(D+1) and is one of A's score-D sets;
  every score-D set of A contains some B holdout as a sub-relation (a set with more equalities);
  the labelled count of A's list equals the sum of the orbit sizes of its symmetry classes.
Each class is rescored here from scratch and printed with an explicit colouring in the wiki's format.
"""
import itertools
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from gate_champions import square


def parse_rel(s):
    return tuple(int(x, 16) for x in s.split(","))


def transpose(r, n):
    return tuple(sum(1 << i for i in range(n) if r[i] >> j & 1) for j in range(n))


def permute(r, p, n):
    o = [0] * n
    for i in range(n):
        for j in range(n):
            if r[i] >> j & 1:
                o[p[i]] |= 1 << p[j]
    return tuple(o)


def images(h, v, n):
    ht, vt = transpose(h, n), transpose(v, n)
    return [(h, v), (ht, v), (h, vt), (ht, vt), (v, h), (vt, h), (v, ht), (vt, ht)]


def canon(h, v, n, perms):
    best = None
    for a, b in images(h, v, n):
        for p in perms:
            x = (permute(a, p, n), permute(b, p, n))
            if best is None or x < best:
                best = x
    return best


def labelled_orbit(h, v, n, perms):
    """Labelled pairs in the class: all relabellings of all eight images."""
    return {(permute(a, p, n), permute(b, p, n)) for a, b in images(h, v, n) for p in perms}


def to_tiles(h, v, n):
    """A colouring realising (H,V): each block of the relation gets its own colour, other ends fresh."""
    next_col = [0]

    def colours(r):
        ends_out, ends_in = {}, {}
        for i in range(n):
            if r[i]:
                key = r[i]
                if key not in ends_in:
                    ends_in[key] = next_col[0]
                    next_col[0] += 1
                ends_out[i] = ends_in[key]
        col_in = {}
        for key, c in ends_in.items():
            for j in range(n):
                if key >> j & 1:
                    col_in[j] = c
        for i in range(n):
            if i not in ends_out:
                ends_out[i] = next_col[0]
                next_col[0] += 1
            if i not in col_in:
                col_in[i] = next_col[0]
                next_col[0] += 1
        return ends_out, col_in

    right, left = colours(h)
    bottom, top = colours(v)
    return [(top[i], right[i], bottom[i], left[i]) for i in range(n)]


def relation_of(tiles):
    n = len(tiles)
    h = tuple(sum(1 << j for j in range(n) if tiles[i][1] == tiles[j][3]) for i in range(n))
    v = tuple(sum(1 << j for j in range(n) if tiles[i][2] == tiles[j][0]) for i in range(n))
    return h, v


def contains(big, small, n, perms):
    (bh, bv), (sh, sv) = big, small
    for p in perms:
        ph, pv = permute(sh, p, n), permute(sv, p, n)
        if all(ph[i] & ~bh[i] == 0 and pv[i] & ~bv[i] == 0 for i in range(n)):
            return True
    return False


def main():
    n, d = int(sys.argv[1]), int(sys.argv[2])
    perms = list(itertools.permutations(range(n)))
    top = {}
    labelled = 0
    for line in open(sys.argv[3]):
        w = line.split()
        if w[0] != "top" or int(w[1]) != d:
            continue
        h, v = parse_rel(w[4]), parse_rel(w[6])
        labelled += int(w[2])
        top[canon(h, v, n, perms)] = (h, v)
    holds = {}
    for line in open(sys.argv[4]):
        w = line.split()
        h, v = parse_rel(w[2]), parse_rel(w[4])
        if w[6] != str(d) or w[7] != "refused":
            raise SystemExit(f"B holdout not a clean score-{d} set: {line}")
        holds[canon(h, v, n, perms)] = (h, v)
    sum_orbits = sum(len(labelled_orbit(h, v, n, perms)) for h, v in top)
    print(f"n={n} D={d} A: classes={len(top)} labelled={labelled} sum_of_orbits={sum_orbits}")
    print(f"n={n} D={d} B: minimal classes={len(holds)}")
    ok = sum_orbits == labelled
    missing = [c for c in holds if c not in top]
    print("B classes missing from A:", len(missing))
    ok &= not missing
    uncovered = [c for c in top if not any(contains(c, s, n, perms) for s in holds)]
    print("A classes not above any B holdout:", len(uncovered))
    ok &= not uncovered
    with open(sys.argv[5], "w") as f:
        for c in sorted(top):
            tiles = to_tiles(c[0], c[1], n)
            assert relation_of(tiles) == c, "colouring does not realise the relation"
            good = square(tiles, d) is not None and square(tiles, d + 1) is None
            ok &= good
            kind = "minimal" if c in holds else "above-minimal"
            f.write(" ".join("[" + ",".join(map(str, t)) + "]" for t in tiles) + f"  # {kind} H={c[0]} V={c[1]}\n")
    print("rescored every class from its colouring, wrote", sys.argv[5])
    print("AGREE" if ok else "DISAGREE")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
