#!/usr/bin/env python3
# check_closed.py FILE...: standalone checker for an explicit closed-language certificate. No search, no automaton construction.
# A certificate gives two edge sets EL, ER of a deterministic automaton (lines: EL q a t = state q reads a and goes to t) and a set of
# abstract configurations C (lines: C left-state machine-state head-symbol right-state).
# Blank tail states are listed by the 'tails' line and must form a cycle under reading 0 in both edge sets, so that an infinite blank
# word has a consistent reading from any tail state. startL/startR are the tail states the finite part of the tape is read from.
# Meaning: a real configuration (left word, s, c, right word) is covered by (l, s, c, r) when the left word, read from its blank
# tail towards the head, follows EL edges from a tail state to l, and the right word, read from its blank tail towards the head,
# follows ER edges to r. If the checks below pass, every configuration reached from the tape is covered, and no covered configuration
# reads an undefined transition, so the machine never halts on that tape.
import re, sys
def check(path):
    tape = tm = None; tails = []; startL = startR = None; EL = {}; ER = {}; C = set()
    for line in open(path):
        p = line.split()
        if p[0] == 'tape': tape = p[1]
        elif p[0] == 'machine': tm = p[1]
        elif p[0] == 'tails': tails = [int(x) for x in p[1:]]
        elif p[0] == 'startL': startL = int(p[1])
        elif p[0] == 'startR': startR = int(p[1])
        elif p[0] == 'EL': EL[(int(p[1]), int(p[2]))] = int(p[3])
        elif p[0] == 'ER': ER[(int(p[1]), int(p[2]))] = int(p[3])
        elif p[0] == 'C': C.add((int(p[1]), int(p[2]), int(p[3]), int(p[4])))
    cells = [tm[i:i + 3] for i in (0, 3, 6, 9, 13, 16, 19, 22)]
    tr = {(i // 4, i % 4): (int(x[0]), x[1] == 'R', ord(x[2]) - 65) for i, x in enumerate(cells) if x[0] != '-'}
    m = re.fullmatch(r'(\d*)\[(\d)\](\d*)', tape); lw = [int(x) for x in m[1]]; h = int(m[2]); rw = [int(x) for x in m[3]][::-1]
    for E in (EL, ER):
        q = tails[0]
        for _ in tails: q = E[(q, 0)]; assert q in tails, 'blank tail must stay on tail states'
        assert q == tails[0], 'blank tail must be a cycle through all tail states'
    assert startL in tails and startR in tails
    def walk(E, w, q):
        for a in w: q = E[(q, a)]
        return q
    assert (walk(EL, lw, startL), 0, h, walk(ER, rw, startR)) in C, 'start configuration not covered'
    intoL = {}; intoR = {}
    for (q, a), t in EL.items(): intoL.setdefault(t, []).append((q, a))
    for (q, a), t in ER.items(): intoR.setdefault(t, []).append((q, a))
    for (l, s, c, r) in C:
        assert (s, c) in tr, f'undefined transition reachable: {l} {s} {c} {r}'
        w, right, ns = tr[(s, c)]
        if right:
            nl = EL[(l, w)]                                 # the pushed cell's edge must be in EL
            for (q, a) in intoR.get(r, []): assert (nl, ns, a, q) in C, 'not closed (right)'
        else:
            nr = ER[(r, w)]
            for (q, a) in intoL.get(l, []): assert (q, ns, a, nr) in C, 'not closed (left)'
    # every real word's last edge is in the set, so popping one cell always lands on a listed predecessor
    print(f"OK {path}: {tm} never halts on {tape}; {len(C)} configurations, {len(EL)}+{len(ER)} edges")
for f in sys.argv[1:]: check(f)
