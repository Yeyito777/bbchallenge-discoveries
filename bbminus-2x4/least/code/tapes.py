# tapes.py MAXR: one representative per class of finite tapes l..l[c]r..r up to relabelling {1,2,3} and mirroring, radius<=MAXR.
import itertools, sys
R = int(sys.argv[1]); seen = {}
def canon(t):
    best = None
    for p in itertools.permutations((1, 2, 3)):
        m = {0: 0, 1: p[0], 2: p[1], 3: p[2]}
        a = tuple(m[x] for x in t); b = a[::-1]
        for x in (a, b):
            if best is None or x < best: best = x
    return best
out = []
for r in range(R + 1):
    for t in itertools.product(range(4), repeat=2 * r + 1):
        # skip tapes equal to a smaller radius one
        if r and t[0] == 0 and t[-1] == 0: continue
        c = canon(t)
        if c in seen: continue
        seen[c] = 1
        # write with the larger-looking side on the left
        s = ''.join(map(str, c[:r])) + '[' + str(c[r]) + ']' + ''.join(map(str, c[r + 1:]))
        out.append(s)
print('\n'.join(out))
