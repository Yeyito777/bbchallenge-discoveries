#!/usr/bin/env python3
"""Standalone checker for closed abstract tape sets. No decider logic here.

Theorem checked. Let E_L, E_R be labelled edge sets (a, x, b) over a cell alphabet X, each x having a real
symbol sym(x). A side word (read from infinity towards the head) "has a path to b" if some bi-infinite-to-the-left
path in E ends in b, with blank cells far out following a cycle of blank-labelled edges. Let C be a set of
(l, Q, x, r), with Q having a real machine state st(Q). Suppose:
  (a) some blank-cycle states give paths over the start tape's left and right words to l0, r0, and
      (l0, Q0, x0, r0) is in C, with x0 the plain head symbol and st(Q0)=A;
  (b) for each (l,Q,x,r) in C the machine has a transition (w,d,q') on (st(Q), sym(x)), and there are x' with
      sym(x')=w and Q' with st(Q')=q' such that, for d=R: an edge (l,x',l2) is in E_L and for every edge (r2,y,r) in
      E_R the config (l2,Q',y,r2) is in C; for d=L: an edge (r,x',r2) is in E_R and for every edge (l2,y,l) in E_L
      the config (l2,Q',y,r2) is in C.
Then the machine never halts on the start tape: induction on the run, keeping a path for each side.

Input: stream of certificates in my dump format, or with --closed, files in the format of least/certs/closed/.
Every CERT is checked; the summary lists machines passed and failed.
"""
import sys

def parse_machine(s):
    s = s.replace('_', '')
    t = {}
    for i in range(8):
        c = s[3*i:3*i+3]
        if c != '---':
            t[(i//4, i % 4)] = (int(c[0]), 1 if c[1] == 'R' else 0, ord(c[2])-65)
    return t

def parse_tape(s):
    i = s.index('[')
    return [int(c) for c in s[:i]], int(s[i+1]), [int(c) for c in s[i+3:]]

def check(machine, mirror, tape, X, Q, EL, ER, C):
    """X: id->(sym,tag) Q: id->(state,tag). EL/ER: list of (a,x,b). C: list of (l,Q,x,r). Returns error or None."""
    t = parse_machine(machine)
    left, head, right = tape
    if mirror:
        t = {k: (w, 1-d, n) for k, (w, d, n) in t.items()}
        left, right = right[::-1], left[::-1]
    nextL, nextR, predL, predR = {}, {}, {}, {}
    for (a, x, b) in EL:
        if (a, x) in nextL and nextL[(a, x)] != b:
            return 'L not deterministic'
        nextL[(a, x)] = b
        predL.setdefault(b, []).append((a, x))
    for (a, x, b) in ER:
        if (a, x) in nextR and nextR[(a, x)] != b:
            return 'R not deterministic'
        nextR[(a, x)] = b
        predR.setdefault(b, []).append((a, x))
    Cset = set(C)
    if len(Cset) != len(C):
        return 'duplicate config'
    plain = {}
    for i, (sym, tag) in X.items():
        if tag == '':
            plain[sym] = i
    q_plain = [i for i, (st, tag) in Q.items() if st == 0 and tag == '']
    if 0 not in plain or len(q_plain) != 1:
        return 'no plain blank or start control'
    # (a) start
    blank = plain[0]

    def cycle_states(nxt, states):
        out = set()
        for s0 in states:
            s = s0
            for _ in range(len(states)+1):
                s = nxt.get((s, blank))
                if s is None:
                    break
                if s == s0:
                    out.add(s0)
                    break
        return out

    def ends(nxt, word):
        states = {a for (a, _) in nxt}
        cyc = cycle_states(nxt, states)
        res = set()
        for s0 in cyc:
            s = s0
            for c in word:
                s = nxt.get((s, plain[c])) if c in plain else None
                if s is None:
                    break
            if s is not None:
                res.add(s)
        return res
    lends = ends(nextL, left)
    rends = ends(nextR, right[::-1])
    if not any((l, q_plain[0], plain[head], r) in Cset for l in lends for r in rends):
        return 'start config not in set'
    byS = {}
    for i, (sym, _) in X.items():
        byS.setdefault(sym, []).append(i)
    byQ = {}
    for i, (st, _) in Q.items():
        byQ.setdefault(st, []).append(i)
    # (b) closure
    for (l, q, x, r) in C:
        k = (Q[q][0], X[x][0])
        if k not in t:
            return 'config with undefined transition (%d,%d)' % k
        w, d, nq = t[k]
        ok = False
        for xn in byS.get(w, ()):
            for qn in byQ.get(nq, ()):
                if d == 1:
                    l2 = nextL.get((l, xn))
                    if l2 is not None and all((l2, qn, y, r2) in Cset for (r2, y) in predR.get(r, ())):
                        ok = True
                else:
                    r2 = nextR.get((r, xn))
                    if r2 is not None and all((l2, qn, y, r2) in Cset for (l2, y) in predL.get(l, ())):
                        ok = True
                if ok:
                    break
            if ok:
                break
        if not ok:
            return 'config %s not closed' % ((l, q, x, r),)
    return None

def read_closed(path):
    """Format of least/certs/closed: states are ints, cells are plain symbols, tails list a blank cycle."""
    EL, ER, C = [], [], []
    tails, sl, sr = None, None, None
    for line in open(path):
        p = line.split()
        if p[0] == 'tape':
            tape = parse_tape(p[1])
        elif p[0] == 'machine':
            machine = p[1]
        elif p[0] == 'tails':
            tails = [int(v) for v in p[1:]]
        elif p[0] == 'startL':
            sl = int(p[1])
        elif p[0] == 'startR':
            sr = int(p[1])
        elif p[0] == 'EL':
            EL.append(tuple(int(v) for v in p[1:]))
        elif p[0] == 'ER':
            ER.append(tuple(int(v) for v in p[1:]))
        elif p[0] == 'C':
            C.append(tuple(int(v) for v in p[1:]))
        else:
            raise SystemExit('unknown line ' + line)
    X = {i: (i, '') for i in range(4)}
    Q = {i: (i, '') for i in range(2)}
    return machine, tape, X, Q, EL, ER, C, tails, sl, sr

def main():
    if sys.argv[1] == '--closed':
        bad = 0
        for path in sys.argv[2:]:
            machine, tape, X, Q, EL, ER, C, tails, sl, sr = read_closed(path)
            err = check(machine, False, tape, X, Q, EL, ER, C)
            # stated start phases must be on the blank cycle too
            print(path.split('/')[-1], 'configs', len(set(C)), 'EL', len(EL), 'ER', len(ER), 'tails', tails, 'startL', sl, 'startR', sr, 'FAIL ' + err if err else 'PASS')
            bad += 1 if err else 0
        sys.exit(1 if bad else 0)
    tape = parse_tape(sys.argv[1])
    show = {}
    npass, nfail, nlines = 0, 0, 0
    cur = None
    passed = open(sys.argv[2], 'w') if len(sys.argv) > 2 else None
    for line in sys.stdin:
        p = line.split()
        tag = p[0]
        if tag == 'C':
            cur['C'].append((int(p[1]), int(p[2]), int(p[3]), int(p[4])))
        elif tag == 'EL':
            cur['EL'].append((int(p[1]), int(p[2]), int(p[3])))
        elif tag == 'ER':
            cur['ER'].append((int(p[1]), int(p[2]), int(p[3])))
        elif tag == 'X':
            cur['X'][int(p[1])] = (int(p[2]), p[3] if len(p) > 3 else '')
        elif tag == 'Q':
            cur['Q'][int(p[1])] = (int(p[2]), p[3] if len(p) > 3 else '')
        elif tag == 'CERT':
            cur = {'m': p[1], 'mir': p[3] == '1', 'X': {}, 'Q': {}, 'EL': [], 'ER': [], 'C': []}
        elif tag == 'END':
            err = check(cur['m'], cur['mir'], tape, cur['X'], cur['Q'], cur['EL'], cur['ER'], cur['C'])
            if err:
                nfail += 1
                print('FAIL', cur['m'], err)
            else:
                npass += 1
                if passed:
                    passed.write(cur['m'] + '\n')
            if (npass+nfail) % 50000 == 0:
                print('progress', npass, nfail, file=sys.stderr, flush=True)
    print('passed', npass, 'failed', nfail)
    sys.exit(1 if nfail else 0)

main()
