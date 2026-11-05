#!/usr/bin/env python3
"""Standalone checker for a wt_lazy certificate.  Standard library only, trusts no search code.

Claim checked: every set of N Wang tiles that tiles a DxD square also tiles the plane.

Why walking the tree proves it.  Suppose some N-tile set tiles DxD but not the plane.  Over all such sets
and all their tilings, name tiles 0,1,2,... by first appearance along the fill order, and pick the tiling
F that reads smallest as a label sequence.  Each cell of F picks an old name or the next new one, and all
of those options are walked here in ascending order, with the colour equalities that adjacency forces.
The real set satisfies those equalities along F.  There are three ways the walk could leave F's path:
  1. A torus.  Its adjacencies all follow from the equalities on the path, so the real set tiles that
     torus, hence the plane.  Contradiction.
  2. A symmetric skip (order "ringsym").  Some rotated, reflected or transposed image of F reads smaller on
     the cells placed so far, so the whole image reads smaller.  It is a tiling by the image set, which also
     fails to tile the plane.  This contradicts the choice of F.
  3. A repeat skip.  An earlier node at the same position had the same state after renaming labels by a
     permutation that fixes the unused labels.  Renaming the rest of F the same way and attaching it to the
     earlier node gives a tiling by an equivalent set (the same equalities up to renaming).  Its prefix came
     earlier in the ascending walk, so it reads smaller.  This contradicts the choice of F.
The walk ends on F's path only at a complete fill with no torus, which is a failure below.  So if this
program prints OK, no such set exists.  The skips are decided here, not read from the certificate.

Colours: E_i=i, W_i=n+i (right/left edges), S_i=2n+i, N_i=3n+i (bottom/top edges).
Tree format: LEB128 tokens: 0 = nothing claimed, 1 = closed (below), k>=2 = torus k-2.  Claims are checked
as soon as they are read.  A relation pair gets one token at its first visit.  If the header sets "gate T>0",
an unsettled pair gets one more token at its T-th visit, and one more at a complete fill, where 0 is a failure.
If the header sets "reset P", all these tables and the repeat-skip table are cleared around each node at
position P.  With "shards W", only every W-th such node is walked here, so the claim needs all W shards to pass with the
same reset position, subtree count and digest (the digest covers the prefix of every such node, so all shards
agree on the list of nodes they are sharing out).
Closed: the pair refuses DxD, which is checked here by exact search, and every pair one colour merge above it
is settled, each by a torus or by being closed itself, in a fixed order.  A set satisfying a closed pair's
equalities either has exactly those adjacencies, so it cannot tile DxD, or satisfies one more merge and
then tiles the plane, or is covered the same way one level up.  This can be a fourth way out of F's path.
Torus line: a b s g... : a rows, b columns, row a is row 0 shifted by s columns.
"""
import sys

sys.setrecursionlimit(100000)


def order_cells(d, kind):
    if kind == "scan":
        return [(r, c) for r in range(d) for c in range(d)]
    if kind == "shell":
        out = []
        for k in range(d):
            out += [(r, k) for r in range(k)]
            out += [(k, c) for c in range(k + 1)]
        return out
    assert kind in ("ring", "ringsym")
    lo = d // 2 if d % 2 else d // 2 - 1
    hi = d // 2
    out = []
    while True:
        if lo == hi:
            out.append((lo, lo))
        else:
            out += [(lo, c) for c in range(lo, hi)]
            out += [(r, hi) for r in range(lo, hi)]
            out += [(hi, c) for c in range(hi, lo, -1)]
            out += [(r, lo) for r in range(hi, lo, -1)]
        if lo == 0:
            return out
        lo -= 1
        hi += 1


def find(uf, x):
    while uf[x] != x:
        x = uf[x]
    return x


def main():
    prefix = sys.argv[1]
    with open(prefix + ".tori") as f:
        head = f.readline().split()
        assert head[:2] == ["wt-cert", "3"]
        n, d, kind, ntori = int(head[3]), int(head[5]), head[7], int(head[9])
        reset_pos, shards, shard, gate_t = int(head[11]) or -1, int(head[13]), int(head[15]), int(head[17])
        tori = []
        for line in f:
            w = list(map(int, line.split()))
            a, b, s, g = w[0], w[1], w[2], w[3:]
            assert a >= 1 and b >= 1 and 0 <= s < b and len(g) == a * b and all(0 <= x < n for x in g)
            pairs = []
            for r in range(a):
                for c in range(b):
                    x = g[r * b + c]
                    right = g[r * b + (c + 1) % b]
                    below = g[(r + 1) * b + c] if r + 1 < a else g[(c + s) % b]
                    pairs.append((x, n + right))
                    pairs.append((2 * n + x, 3 * n + below))
            tori.append(sorted(set(pairs)))
        assert len(tori) == ntori
    data = open(prefix + ".tree", "rb").read()
    cells = order_cells(d, kind)
    assert sorted(cells) == [(r, c) for r in range(d) for c in range(d)]
    index = {cell: i for i, cell in enumerate(cells)}
    labels = [0] * (d * d)
    m = d - 1
    symmetries = (
        lambda r, c: (r, m - c),
        lambda r, c: (m - r, c),
        lambda r, c: (m - r, m - c),
        lambda r, c: (c, r),
        lambda r, c: (c, m - r),
        lambda r, c: (m - c, r),
        lambda r, c: (m - c, m - r),
    )
    images = [[index[f(r, c)] for r, c in cells] for f in symmetries] if kind == "ringsym" else []

    frontier = []
    for pos in range(d * d + 1):
        f = []
        for q in range(pos):
            r, c = cells[q]
            if any(0 <= r + a < d and 0 <= c + b < d and index[(r + a, c + b)] >= pos for a, b in ((0, -1), (0, 1), (-1, 0), (1, 0))):
                f.append(q)
        frontier.append(f)
    seen = set()

    def relations(uf):
        roots = [find(uf, i) for i in range(4 * n)]
        h = [sum(1 << j for j in range(n) if roots[i] == roots[n + j]) for i in range(n)]
        v = [sum(1 << j for j in range(n) if roots[2 * n + i] == roots[3 * n + j]) for i in range(n)]
        return h, v

    def state_key(pos, k, h, v):
        """Any permutation fixing the unused labels is sound here; this one must only match wt_lazy."""
        hi = [sum(1 << i for i in range(n) if h[i] >> j & 1) for j in range(n)]
        vi = [sum(1 << i for i in range(n) if v[i] >> j & 1) for j in range(n)]
        name = {}
        fr = []
        for q in frontier[pos]:
            fr.append(name.setdefault(labels[q], len(name)))
        known = dict(name)

        def renamed(mask):
            return sum(1 << known[j] for j in range(n) if mask >> j & 1 and j in known)

        rest = []
        for l in range(k):
            if l not in name:
                sig = (
                    renamed(h[l])
                    | renamed(hi[l]) << 8
                    | renamed(v[l]) << 16
                    | renamed(vi[l]) << 24
                    | bin(h[l]).count("1") << 32
                    | bin(hi[l]).count("1") << 36
                    | bin(v[l]).count("1") << 40
                    | bin(vi[l]).count("1") << 44
                )
                rest.append((sig, l))
        for _, l in sorted(rest):
            name[l] = len(name)
        for l in range(k, n):
            name[l] = l
        h2, v2 = [0] * n, [0] * n
        for i in range(n):
            for j in range(n):
                if h[i] >> j & 1:
                    h2[name[i]] |= 1 << name[j]
                if v[i] >> j & 1:
                    v2[name[i]] |= 1 << name[j]
        return pos, k, tuple(fr), tuple(h2), tuple(v2)

    def skipped(pos):
        for img in images:
            rename = {}
            for i in range(pos):
                q = img[i]
                if q >= pos:
                    break
                x = rename.setdefault(labels[q], len(rename))
                if x < labels[i]:
                    return True
                if x > labels[i]:
                    break
        return False

    pos_tok = 0
    stats = {"nodes": 0, "leaves": 0}

    def token():
        nonlocal pos_tok
        x = sh = 0
        while True:
            b = data[pos_tok]
            pos_tok += 1
            x |= (b & 0x7F) << sh
            sh += 7
            if not b & 0x80:
                return x

    rel_answer, gate_answer, final_answer, visits = {}, {}, {}, {}
    counter = [0]
    digest = [0xCBF29CE484222325]

    def clear():
        rel_answer.clear()
        gate_answer.clear()
        final_answer.clear()
        visits.clear()
        seen.clear()

    def refuses(h, v):
        """Exact: arc consistency on tile masks, branching on the smallest domain."""
        hi = [sum(1 << i for i in range(n) if h[i] >> j & 1) for j in range(n)]
        vi = [sum(1 << i for i in range(n) if v[i] >> j & 1) for j in range(n)]

        def image(mask, table):
            out, i = 0, 0
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
                for ok, y, table in ((c + 1 < d, x + 1, h), (c > 0, x - 1, hi), (r + 1 < d, x + d, v), (r > 0, x - d, vi)):
                    if ok:
                        m = dom[y] & image(dom[x], table)
                        if m != dom[y]:
                            if not m:
                                return False
                            dom[y] = m
                            todo.append(y)
            return True

        def fills(dom):
            best, bc = -1, n + 1
            for x, m in enumerate(dom):
                c = bin(m).count("1")
                if 1 < c < bc:
                    best, bc = x, c
            if best < 0:
                return True
            for t in range(n):
                if dom[best] >> t & 1:
                    d2 = dom[:]
                    d2[best] = 1 << t
                    if propagate(d2, [best]) and fills(d2):
                        return True
            return False

        dom = [(1 << n) - 1] * (d * d)
        return not (propagate(dom, list(range(d * d))) and fills(dom))

    def claim(uf, tok):
        if tok == 1:
            verify_closed(uf)
        elif tok:
            if tok - 2 >= ntori:
                raise SystemExit("FAIL: torus id out of range")
            for p, q in tori[tok - 2]:
                if find(uf, p) != find(uf, q):
                    raise SystemExit(f"FAIL: torus {tok - 2} is not implied")

    def verify_closed(uf):
        h, v = relations(uf)
        if not refuses(h, v):
            raise SystemExit("FAIL: a pair claimed closed tiles the square")
        done = set()
        for base, other, rel in ((0, n, h), (2 * n, 3 * n, v)):
            for i in range(n):
                for j in range(n):
                    if rel[i] >> j & 1:
                        continue
                    u = uf[:]
                    x, y = find(u, base + i), find(u, other + j)
                    if x != y:
                        u[x] = y
                    h2, v2 = relations(u)
                    key = (tuple(h2), tuple(v2))
                    if key in done:
                        continue
                    done.add(key)
                    if key not in rel_answer:
                        tok = token()
                        if not tok:
                            raise SystemExit("FAIL: a merge above a closed pair is unsettled")
                        rel_answer[key] = tok
                        claim(u, tok)
                    elif not rel_answer[key]:
                        if key not in gate_answer:
                            tok = token()
                            if not tok:
                                raise SystemExit("FAIL: a merge above a closed pair is unsettled")
                            gate_answer[key] = tok
                            claim(u, tok)
                        elif not gate_answer[key]:
                            raise SystemExit("FAIL: a merge above a closed pair is unsettled")

    def walk(pos, k, uf):
        if skipped(pos):
            return
        if pos == reset_pos:
            clear()
            counter[0] += 1
            for x in labels[:pos]:
                digest[0] = ((digest[0] ^ x) * 0x100000001B3) & (2**64 - 1)
            digest[0] = ((digest[0] ^ 255) * 0x100000001B3) & (2**64 - 1)
            if counter[0] % shards == shard:
                node(pos, k, uf)
                clear()
            return
        node(pos, k, uf)

    def node(pos, k, uf):
        stats["nodes"] += 1
        h, v = relations(uf)
        rel = (tuple(h), tuple(v))
        ans = rel_answer.get(rel)
        if ans is None:
            ans = token()
            rel_answer[rel] = ans
            claim(uf, ans)
        if not ans:
            visits[rel] = visits.get(rel, 0) + 1
            if rel in gate_answer:
                ans = gate_answer[rel]
            elif gate_t and visits[rel] >= gate_t:
                ans = token()
                gate_answer[rel] = ans
                claim(uf, ans)
        if not ans and pos == d * d:
            ans = final_answer.get(rel)
            if ans is None:
                ans = token()
                final_answer[rel] = ans
                claim(uf, ans)
            if not ans:
                raise SystemExit("FAIL: complete fill with no torus: " + "".join(map(str, labels)))
        if ans:
            stats["leaves"] += 1
            return
        key = state_key(pos, k, h, v)
        if key in seen:
            return
        seen.add(key)
        r, c = cells[pos]
        for t in range(min(k, n - 1) + 1):
            u = uf[:]
            for dr, dc, a_edge, b_edge in ((0, -1, "E", "W"), (0, 1, "W", "E"), (-1, 0, "S", "N"), (1, 0, "N", "S")):
                q = index.get((r + dr, c + dc))
                if q is None or q >= pos:
                    continue
                other = labels[q]
                off = {"E": 0, "W": n, "S": 2 * n, "N": 3 * n}
                # the neighbour's a_edge meets this cell's b_edge
                x, y = find(u, off[a_edge] + other), find(u, off[b_edge] + t)
                if x != y:
                    u[x] = y
            labels[pos] = t
            walk(pos + 1, k + 1 if t == k else k, u)

    walk(0, 0, list(range(4 * n)))
    if pos_tok != len(data):
        raise SystemExit("FAIL: trailing bytes in tree")
    print(f"OK n={n} D={d} order={kind} nodes={stats['nodes']} leaves={stats['leaves']} tori={ntori} shard={shard}/{shards} reset={head[11]} subtrees={counter[0]} digest={digest[0]:016x}")
    if shards == 1:
        print(f"every {n}-tile set that tiles a {d}x{d} square tiles the plane, so BB_WT({n}) < {d}")
    else:
        print(f"this shard passes; the claim for n={n}, D={d} needs all {shards} shards")


main()
