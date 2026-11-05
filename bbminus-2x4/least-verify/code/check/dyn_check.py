#!/usr/bin/env python3
"""Dynamic test of certificate semantics: run the real machine and, at every step, map the real config into the
certificate through the side automata, then require it to be in C. This is what the theorem in check_cert.py says
must hold, tested on real runs. A certificate that lost configs (for instance a blank tail with no predecessor)
would fail here once the head reaches the lost region.
usage: dyn_check.py TAPE STEPS KEEP_EVERY < dump"""
import sys
from check_cert_lib import parse_machine, parse_tape

def bin_tag(h):
    return bytes.fromhex(h) if h else b''

def run(c, tape, steps):
    t = parse_machine(c['m'])
    left, head, right = tape
    fam = c['fam'].split(',')
    cellh, cellq, headh = int(fam[8]), int(fam[9]), int(fam[10])
    nextL, nextR = {}, {}
    predL, predR = {}, {}
    for a, x, b in c['EL']:
        nextL[(a, x)] = b
        predL.setdefault(b, []).append((a, x))
    for a, x, b in c['ER']:
        nextR[(a, x)] = b
        predR.setdefault(b, []).append((a, x))
    C = set(c['C'])
    xid = {v: k for k, v in c['X'].items()}
    qid = {v: k for k, v in c['Q'].items()}
    blank = xid[(0, b'')]

    def tail(nxt, states):
        res = []
        for s0 in states:
            s = s0
            ok = False
            for _ in range(len(states)+1):
                s = nxt.get((s, blank))
                if s is None:
                    break
                if s == s0:
                    ok = True
                    break
            if ok:
                res.append(s0)
        return res

    def pathfor(nxt, states, word):
        for s0 in tail(nxt, states):
            p = [s0]
            s = s0
            for w in word:
                s = nxt.get((s, xid[(w, b'')]))
                if s is None:
                    break
                p.append(s)
            if s is not None:
                yield s0, p
    q = 0
    hist = b''
    e0 = xid[(head, b'')]
    found = None
    lstates = {a for a, _ in nextL}
    rstates = {a for a, _ in nextR}
    for s0l, pl in pathfor(nextL, lstates, left):
        for s0r, pr in pathfor(nextR, rstates, right[::-1]):
            if (pl[-1], qid[(0, b'')], e0, pr[-1]) in C:
                found = (pl, pr)
    if not found:
        return 'start not in C'
    pl, pr = found
    # stacks of (state after the cell, cell). The first entry of each list is the tail state.
    lcells = [xid[(w, b'')] for w in left]
    rcells = [xid[(w, b'')] for w in right[::-1]]
    e = e0

    def tail_pred(nxt, s):
        for a in tail(nxt, {x for x, _ in nxt}):
            if nxt.get((a, blank)) == s:
                return a
        return None
    cq = 0
    for n in range(steps):
        a = c['X'][e][0]
        qctl = qid[(q, hist)]
        cfg = (pl[-1], qctl, e, pr[-1])
        if cfg not in C:
            return 'real config at step %d not in C' % n
        k = (q, a)
        if k not in t:
            return 'real run reached undefined at step %d' % n
        w, d, nq = t[k]
        tag = b''
        if cellh:
            old = bytes([a]) + c['X'][e][1]
            tag = old[:cellh]
        if cellq == 1:
            tag += bytes([q+100])
        elif cellq == 2:
            tag += bytes([q+100+10*d])
        ne = xid.get((w, tag))
        if ne is None:
            return 'no ext for write at %d' % n
        if headh:
            hist = (bytes([q << 4 | a]) + hist)[:headh]
        q = nq
        if d == 1:
            s = nextL.get((pl[-1], ne))
            if s is None:
                return 'no L edge at %d' % n
            pl.append(s)
            lcells.append(ne)
            if not rcells:
                # the right path is in its blank tail: extend the tail one step outwards
                s0 = tail_pred(nextR, pr[0])
                if s0 is None:
                    return 'R tail has no predecessor at %d' % n
                pr.insert(0, s0)
                rcells.insert(0, blank)
            e = rcells.pop()
            pr.pop()
        else:
            s = nextR.get((pr[-1], ne))
            if s is None:
                return 'no R edge at %d' % n
            pr.append(s)
            rcells.append(ne)
            if not lcells:
                s0 = tail_pred(nextL, pl[0])
                if s0 is None:
                    return 'L tail has no predecessor at %d' % n
                pl.insert(0, s0)
                lcells.insert(0, blank)
            e = lcells.pop()
            pl.pop()
    return None

def main():
    tape = parse_tape(sys.argv[1])
    steps = int(sys.argv[2])
    keep = int(sys.argv[3])
    cur = None
    npass = nfail = nskip = idx = 0
    for line in sys.stdin:
        p = line.split()
        tag = p[0]
        if tag == 'CERT':
            idx += 1
            take = (idx % keep == 0) or p[2].startswith('r,')
            cur = {'m': p[1], 'fam': p[2], 'X': {}, 'Q': {}, 'EL': [], 'ER': [], 'C': []} if take else None
        elif cur is None:
            continue
        elif tag == 'C':
            cur['C'].append((int(p[1]), int(p[2]), int(p[3]), int(p[4])))
        elif tag == 'EL':
            cur['EL'].append((int(p[1]), int(p[2]), int(p[3])))
        elif tag == 'ER':
            cur['ER'].append((int(p[1]), int(p[2]), int(p[3])))
        elif tag == 'X':
            cur['X'][int(p[1])] = (int(p[2]), bin_tag(p[3] if len(p) > 3 else ''))
        elif tag == 'Q':
            cur['Q'][int(p[1])] = (int(p[2]), bin_tag(p[3] if len(p) > 3 else ''))
        elif tag == 'END':
            err = run(cur, tape, steps)
            if err:
                nfail += 1
                print('FAIL', cur['m'], cur['fam'], err)
            else:
                npass += 1
            if (npass+nfail) % 2000 == 0:
                print('progress', npass, nfail, file=sys.stderr, flush=True)
    print('real-run tracking: passed', npass, 'failed', nfail, 'steps per machine', steps)

main()
