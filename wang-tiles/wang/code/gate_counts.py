#!/usr/bin/env python3
"""Gate: count adjacency relations of n Wang tiles from first principles.

Colour every one of the 2n ends (E_0..E_{n-1}, W_0..W_{n-1}) in every possible way, i.e. walk all
set partitions of 2n items, derive the relation {(i,j): E_i == W_j} and count distinct relations.
Compare with the closed form sum_k k! S(n+1,k+1)^2.  Nothing here assumes the biclique structure.
"""
import sys
from math import factorial


def stirling2_table(m):
    s = [[0] * (m + 2) for _ in range(m + 2)]
    s[0][0] = 1
    for a in range(1, m + 1):
        for b in range(1, a + 1):
            s[a][b] = b * s[a - 1][b] + s[a - 1][b - 1]
    return s


def formula(n):
    s = stirling2_table(n + 1)
    return sum(factorial(k) * s[n + 1][k + 1] ** 2 for k in range(n + 1))


def count_by_partition(n):
    seen = set()
    colour = [0] * (2 * n)
    bell = 0

    def rec(pos, used):
        nonlocal bell
        if pos == 2 * n:
            bell += 1
            rel = 0
            for i in range(n):
                for j in range(n):
                    if colour[i] == colour[n + j]:
                        rel |= 1 << (i * n + j)
            seen.add(rel)
            return
        for c in range(used + 1):
            colour[pos] = c
            rec(pos + 1, max(used, c + 1))

    rec(0, 0)
    return bell, len(seen)


if __name__ == "__main__":
    maxn = int(sys.argv[1]) if len(sys.argv) > 1 else 6
    print("n bell(2n) distinct_relations closed_form")
    ok = True
    for n in range(1, maxn + 1):
        b, d = count_by_partition(n)
        f = formula(n)
        ok &= d == f
        print(n, b, d, f, "OK" if d == f else "MISMATCH", flush=True)
    for n in range(maxn + 1, 9):
        print(n, "-", "-", formula(n))
    sys.exit(0 if ok else 1)
