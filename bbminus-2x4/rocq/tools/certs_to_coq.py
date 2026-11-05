#!/usr/bin/env python3
"""Convert closed automaton certificates (least-verify/certs/T_certs.xz dump format) into Rocq terms.

usage: certs_to_coq.py MACHINES CERTS.xz OUT.v [MODULE_COMMENT]

For each machine listed in MACHINES (one per line), takes its certificate from CERTS.xz and writes
`(key, {| ac_X := ...; ... |})` entries (key: the 8 transitions) into OUT.v as `Definition aut_certs : list (TM_key * AutCert)`.
A certificate for the mirrored machine is converted to one for the machine itself: the left and right
automata are exchanged and so are the l/r components of every configuration (the start tape 110[1]011
is its own mirror image). Ids are shifted by one to become positives. Nothing here is trusted: Rocq
re-checks every certificate with `closed_aut_decider`.
"""
import lzma
import os
import sys

SYM = 'Σ'


def trans_name(t):
    if t == '---':
        return 'HR1'
    w, d, s = t[0], t[1], t[2]
    return f'{s}{d}{w}'


def make_tm(m):
    """The machine's key for `find_entry`: its 8 transitions A0..A3 B0..B3."""
    s = m.replace('_', '')
    return '(' + '::'.join(trans_name(s[3 * i:3 * i + 3]) for i in range(8)) + '::nil)'


BLOCK = 500


def plist(items):
    """A list literal; long lists become `concat` of blocks so that coqc's parser stays within a default stack."""
    if not items:
        return 'nil'
    if len(items) <= BLOCK:
        return '::'.join(items) + '::nil'
    blocks = ['(' + '::'.join(items[i:i + BLOCK]) + '::nil)' for i in range(0, len(items), BLOCK)]
    return 'concat (' + '::\n'.join(blocks) + '::nil)'


def emit(m, cert):
    X = [f'({k + 1},{SYM}{v})' for k, v in sorted(cert['X'].items())]
    Q = [f'({k + 1},St{v})' for k, v in sorted(cert['Q'].items())]
    EL, ER, C = cert['EL'], cert['ER'], cert['C']
    if cert['mir']:
        EL, ER = ER, EL
        C = [(r, q, x, l) for (l, q, x, r) in C]
    el = [f'({a + 1},{x + 1},{b + 1})' for (a, x, b) in EL]
    er = [f'({a + 1},{x + 1},{b + 1})' for (a, x, b) in ER]
    cl = [str(v + 1) for v in blank_cycle(EL, cert['blank'])]
    cr = [str(v + 1) for v in blank_cycle(ER, cert['blank'])]
    cc = [f'({l + 1},{q + 1},{x + 1},{r + 1})' for (l, q, x, r) in C]
    return (f'(* {m} *)\n({make_tm(m)},\n{{| ac_X:={plist(X)};\n   ac_Q:={plist(Q)};\n'
            f'   ac_EL:={plist(el)};\n   ac_ER:={plist(er)};\n   ac_CL:={plist(cl)};\n   ac_CR:={plist(cr)};\n'
            f'   ac_C:={plist(cc)} |}})')


def blank_cycle(E, blank):
    """States on a cycle of edges labelled with the plain blank cell (as check_cert.py)."""
    nxt = {}
    for (a, x, b) in E:
        if x == blank:
            nxt[a] = b
    out = []
    states = sorted({a for (a, _, _) in E} | {b for (_, _, b) in E})
    for s0 in states:
        s = s0
        for _ in range(len(states) + 1):
            s = nxt.get(s)
            if s is None:
                break
            if s == s0:
                out.append(s0)
                break
    return out


def main():
    want = [l.strip() for l in open(sys.argv[1]) if l.strip()]
    wanted = set(want)
    if not want:
        found = {}
    found = {}
    cur = None
    with lzma.open(sys.argv[2], 'rt') as f:
        for line in f:
            p = line.split()
            tag = p[0]
            if tag == 'CERT':
                cur = {'m': p[1], 'mir': p[3] == '1', 'X': {}, 'Q': {}, 'EL': [], 'ER': [], 'C': []} if p[1] in wanted else None
            elif cur is None:
                continue
            elif tag == 'C':
                cur['C'].append(tuple(int(v) for v in p[1:5]))
            elif tag == 'EL':
                cur['EL'].append(tuple(int(v) for v in p[1:4]))
            elif tag == 'ER':
                cur['ER'].append(tuple(int(v) for v in p[1:4]))
            elif tag == 'X':
                cur['X'][int(p[1])] = int(p[2])
                if int(p[2]) == 0 and len(p) == 3:
                    cur['blank'] = int(p[1])
            elif tag == 'Q':
                cur['Q'][int(p[1])] = int(p[2])
            elif tag == 'END':
                found[cur['m']] = cur
                cur = None
    missing = [m for m in want if m not in found]
    if missing:
        sys.exit('missing certificates: ' + ' '.join(missing))
    nchunks = int(sys.argv[4]) if len(sys.argv) > 4 else 1
    # balance chunks by number of configurations
    chunks = [[] for _ in range(nchunks)]
    sizes = [0] * nchunks
    for m in sorted(want, key=lambda m: -len(found[m]['C'])):
        k = sizes.index(min(sizes))
        chunks[k].append(m)
        sizes[k] += len(found[m]['C']) + len(found[m]['EL']) + len(found[m]['ER'])
    hdr = ('Require Import List.\nRequire Import ZArith.\n\n'
           'From BBminus2x4 Require Import BBminus2x4_Statement.\nFrom BBminus2x4 Require Import TM.\n'
           'From BBminus2x4 Require Import BB2x4_Make_TM.\nFrom BBminus2x4 Require Import Verifier_ClosedAut.\nFrom BBminus2x4 Require Import Decider_Table.\n\n'
           'Set Warnings "-abstract-large-number".\nLocal Open Scope positive_scope.\n\n')
    gen = '(generated by tools/certs_to_coq.py from least-verify/certs/T_certs.xz)'
    base = sys.argv[3][:-2]
    names = []
    for k, ms in enumerate(chunks):
        if nchunks == 1:
            break
        name = os.path.basename(base) + f'_{k}'
        names.append(name)
        with open(base + f'_{k}.v', 'w') as out:
            out.write(f'(** Closed automaton certificates, part {k} {gen}. *)\n\n' + hdr)
            out.write(f'Definition aut_certs_{k} : list (TM_key * AutCert) :=\n')
            out.write(''.join(emit(m, found[m]) + '::\n' for m in ms))
            out.write('nil.\n')
    with open(sys.argv[3], 'w') as out:
        out.write('(** Closed automaton certificates for single machines ' + gen + '.\n'
                  '  Each is re-checked by `closed_aut_decider`. *)\n\n' + hdr)
        if nchunks == 1:
            out.write('Definition aut_certs : list (TM_key * AutCert) :=\n')
            out.write(''.join(emit(m, found[m]) + '::\n' for m in want))
            out.write('nil.\n')
        else:
            for name in names:
                out.write(f'From BBminus2x4 Require Import {name}.\n')
            out.write('\nDefinition aut_certs : list (TM_key * AutCert) :=\n  ' +
                      ' ++ '.join(f'aut_certs_{k}' for k in range(nchunks)) + '.\n')
    tot = sum(len(found[m]['C']) for m in want)
    print(f'{len(want)} certificates, {tot} configurations', file=sys.stderr)


main()
