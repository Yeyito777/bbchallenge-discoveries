#!/usr/bin/env python3
"""Plain Python simulator (dict tape), no shared code with the Go tools.
Input lines: machine H N   or   machine C   . Mode H: must halt at exactly step N, counting the halting step.
Mode C: looks for a repeat of (state, tape relative to head) by a direct method: at each doubling checkpoint,
record the full tape relative to the head with blanks stripped, and compare whole configs except that the side
being moved into is required to be... see below. Reports machines with no detection."""
import sys

def parse(s):
    s = s.replace('_', '')
    t = [None]*8
    for i in range(8):
        c = s[3*i:3*i+3]
        if c != '---':
            t[i] = (int(c[0]), 1 if c[1] == 'R' else -1, ord(c[2])-65)
    return t

def start():
    tape = {}
    for x, c in zip(range(-3, 4), '1101011'):
        if c != '0':
            tape[x] = int(c)
    return tape

def run_h(s, limit):
    t = parse(s)
    tape = start()
    h, q, n = 0, 0, 0
    while n < limit:
        n += 1
        e = t[q*4+tape.get(h, 0)]
        if e is None:
            return n
        if e[0]:
            tape[h] = e[0]
        else:
            tape.pop(h, None)
        h += e[1]
        q = e[2]
    return None

def run_c(s, cap=1 << 16):
    """Proof by unrolling: after the machine has run past t0, find p, d such that the read trace of [t0, t0+p)
    equals that of [t0+p, t0+2p) shifted by d, every cell ahead is blank, and the tape behind agrees on the read
    window. Implemented with explicit copies of the tape at each candidate."""
    t = parse(s)
    tape = start()
    h, q, n = 0, 0, 0
    t0 = 0
    while t0 < cap:
        snap = dict(tape)
        h0, q0 = h, q
        lo = hi = h
        upto = max(32, 2*t0)
        while n < upto:
            a = tape.get(h, 0)
            e = t[q*4+a]
            if e is None:
                return 'halt'
            lo, hi = min(lo, h), max(hi, h)
            if e[0]:
                tape[h] = e[0]
            else:
                tape.pop(h, None)
            h += e[1]
            q = e[2]
            n += 1
            if q != q0:
                continue
            d = h-h0
            if any(tape.get(x+d, 0) != snap.get(x, 0) for x in range(lo, hi+1)):
                continue
            if d > 0 and any(x > hi for x in snap):
                continue
            if d < 0 and any(x < lo for x in snap):
                continue
            return (t0, n-t0, d)
        t0 = n
    return None

def main():
    mode = sys.argv[1]
    n = bad = 0
    for line in sys.stdin:
        p = line.split()
        m = p[0]
        if mode == 'H':
            want = int(p[2])
            got = run_h(m, want+1)
            if got != want:
                bad += 1
                print('BAD', m, want, got)
        else:
            got = run_c(m)
            if got is None or got == 'halt':
                bad += 1
                print('BAD', m, got)
        n += 1
    print('mode', mode, 'checked', n, 'bad', bad)
main()
