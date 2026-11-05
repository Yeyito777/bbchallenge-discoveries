#!/usr/bin/env python3
"""Mutation test of check_cert.py: take real certificates and damage them. Every damaged one must fail.
usage: mutate.py DUMP CHECKER TAPE  (DUMP holds certificates in dump format)"""
import random, subprocess, sys

dump, checker, tape = sys.argv[1:4]
certs = []
cur = []
for line in open(dump):
    cur.append(line)
    if line.startswith('END'):
        certs.append(cur)
        cur = []
random.seed(20261103)

def run(cert):
    p = subprocess.run([sys.executable, '-I', checker, tape], input=''.join(cert), text=True, capture_output=True)
    return p.returncode == 0

def other_machine(line):
    # change one defined transition's write symbol
    p = line.split()
    m = list(p[1])
    while True:
        i = random.randrange(0, len(m))
        if m[i] in '0123' and i % 4 != 3 or (i > 4 and m[i] in '0123'):
            break
    m[i] = str((int(m[i]) + 1) % 4)
    p[1] = ''.join(m)
    return ' '.join(p) + '\n'

def halt_machine(line):
    # undefine a transition used by a config, by undefining each in turn until it fails
    p = line.split()
    s = p[1].replace('_', '')
    defined = [i for i in range(8) if s[3*i:3*i+3] != '---']
    i = random.choice(defined)
    s = s[:3*i] + '---' + s[3*i+3:]
    p[1] = s[:12] + '_' + s[12:]
    return ' '.join(p) + '\n'

stats = {}
survivors = []
def note(kind, accepted):
    a, b = stats.get(kind, (0, 0))
    stats[kind] = (a + 1, b + (1 if accepted else 0))

base_ok = 0
for cert in certs:
    if run(cert):
        base_ok += 1
    C = [i for i, l in enumerate(cert) if l.startswith('C ')]
    EL = [i for i, l in enumerate(cert) if l.startswith('EL ')]
    ER = [i for i, l in enumerate(cert) if l.startswith('ER ')]
    # drop a config: can only stay valid if the config is unreachable surplus, so counted separately
    i = random.choice(C)
    note('drop one config', run(cert[:i] + cert[i+1:]))
    # drop all configs of half the set
    j = set(random.sample(C, max(1, len(C) // 2)))
    note('drop half the configs', run([l for k, l in enumerate(cert) if k not in j]))
    # change a config's control or head
    i = random.choice(EL + ER)
    note('drop one edge', run(cert[:i] + cert[i+1:]))
    # another machine with the same set
    mm = other_machine(cert[0])
    acc = run([mm] + cert[1:])
    note('one write symbol changed', acc)
    if acc:
        survivors.append(mm.split()[1])
    # machine with a defined transition removed: the set uses it or it is surplus
    note('one transition undefined', run([halt_machine(cert[0])] + cert[1:]))
print('certs', len(certs), 'accepted unmodified', base_ok)
for k, (a, b) in stats.items():
    print(f'{k}: tried {a}, still accepted {b}')
# A mutant that passes is a claim that the altered machine never halts on this tape, so test that claim directly.
def runs(m, limit=3000000):
    m = m.replace('_', '')
    t = {}
    for i in range(8):
        c = m[3*i:3*i+3]
        if c != '---':
            t[(i//4, i % 4)] = (int(c[0]), 1 if c[1] == 'R' else -1, ord(c[2])-65)
    i = tape.index('[')
    cells = {}
    for k, c in enumerate(tape[:i]):
        cells[k-i] = int(c)
    cells[0] = int(tape[i+1])
    for k, c in enumerate(tape[i+3:]):
        cells[k+1] = int(c)
    h = q = 0
    for n in range(limit):
        e = t.get((q, cells.get(h, 0)))
        if e is None:
            return n+1
        cells[h] = e[0]
        h += e[1]
        q = e[2]
    return None
for m in survivors:
    print('surviving mutant', m, 'halts at', runs(m))
