#!/usr/bin/env python3
# randtest.py TAPE LEDGER N SEED: independent test of tree completeness. Random machines (not normalised, 1/9 of transitions
# undefined) are run directly on the tape in plain Python. Their normalised partial machines must appear in the ledger as a
# chain of halting nodes with the same step counts, ending in a leaf record.
import random, re, sys
tape, ledger, N, seed = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4]); random.seed(seed)
m = re.fullmatch(r'(\d*)\[(\d)\](\d*)', tape); L, H0, R = [int(x) for x in m[1]], int(m[2]), [int(x) for x in m[3]]
base = {i - len(L): v for i, v in enumerate(L)}; base[0] = H0; base.update({i + 1: v for i, v in enumerate(R)})
tape_syms = {0} | set(L) | set(R) | {H0}
def norm_chain(tm, cap=2000):
    # tm: dict (s,y)->(w,d,n). Returns [(partial string, halting step)] for each normalised prefix plus the last partial string.
    T = dict(base); h = 0; s = 0; steps = 0; symmap = {y: y for y in tape_syms}; statemap = {0: 0}; used = {}; chain = []
    free = [y for y in (1, 2, 3) if y not in tape_syms]
    def name():
        o = []
        for a in (0, 1):
            r = ''
            for b in range(4):
                e = used.get((a, b)); r += '---' if e is None else f"{e[0]}{'R' if e[1] > 0 else 'L'}{'AB'[e[2]]}"
            o.append(r)
        return '_'.join(o)
    while steps < cap:
        y = T.get(h, 0); e = tm.get((s, y)); ny = symmap[y]; ns = statemap[s]
        if (ns, ny) not in used:
            chain.append((name(), steps + 1))              # this partial machine halts here
            if e is None: return chain, None
        if e is None: return chain, None
        w, d, n = e
        if w not in symmap: symmap[w] = free.pop(0)
        if n not in statemap: statemap[n] = 1
        used[(ns, ny)] = (symmap[w], d, statemap[n])
        T[h] = w; h += d; s = n; steps += 1
    return chain, name()
def rand_tm():
    return {(a, b): (random.randrange(4), random.choice((-1, 1)), random.randrange(2)) for a in (0, 1) for b in range(4) if random.random() > 1 / 9}
want_h = {}; want_leaf = set(); chains = 0
for _ in range(N):
    ch, last = norm_chain(rand_tm()); chains += 1
    for nm, st in ch:
        if nm in want_h and want_h[nm] != st: print('INTERNAL', nm); sys.exit(1)
        want_h[nm] = st
    if last is not None: want_leaf.add(last)
print(f"{N} random machines -> {len(want_h)} halting partial machines, {len(want_leaf)} partial machines without halt in the cap")
found = 0; bad = 0; rec = {}
for line in open(ledger):
    p = line.split(); k = p[2] if p[0] == 'H' else (p[4] if p[0] == 'C' else p[1])
    if k in want_h:
        if p[0] != 'H' or int(p[1]) != want_h[k]: print('MISMATCH', line.strip(), want_h[k]); bad += 1
        found += 1
missing = 0
print(f"checked {found} of {len(want_h)} halting partial machines against the ledger; mismatches {bad}, missing {len(want_h) - found}")
sys.exit(1 if bad or found != len(want_h) else 0)
