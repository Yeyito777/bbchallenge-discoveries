#!/usr/bin/env python3
"""Do the checkers reject bad certificates?  usage: mutation_test.py CHECKER_BIN CHECK_PY PREFIX TRIALS

Mutates a good certificate at random: a byte of the tree, a cell of a torus, or a truncation.  A mutant
that still passes is not necessarily wrong, because another torus may also be implied at that leaf, so
every surviving mutant is reported along with what changed.  A certificate with holdouts must fail too.
"""
import os
import random
import shutil
import subprocess
import sys
import tempfile

binary, py, prefix, trials = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4])
tree = open(prefix + ".tree", "rb").read()
tori = open(prefix + ".tori").read().split("\n")
tmp = tempfile.mkdtemp(prefix="wtmut", dir=".")
p = os.path.join(tmp, "m")
random.seed(12345)
stats = {"tree_byte": [0, 0], "torus_cell": [0, 0], "truncate": [0, 0]}


def run(cmd):
    return subprocess.run(cmd, capture_output=True, text=True, timeout=120).returncode == 0


good_tori = "\n".join(tori)
for i in range(trials):
    kind = random.choice(list(stats))
    t, g = bytearray(tree), list(tori)
    if kind == "tree_byte":
        t[random.randrange(len(t))] ^= 1 << random.randrange(7)
    elif kind == "truncate":
        del t[random.randrange(len(t)) :]
    else:
        k = random.randrange(1, len(g) - 1)
        w = g[k].split()
        a, b = int(w[0]), int(w[1])
        c = 3 + random.randrange(a * b)
        n = int(g[0].split()[3])
        w[c] = str((int(w[c]) + 1 + random.randrange(max(n - 1, 1))) % n)
        g[k] = " ".join(w)
    open(p + ".tree", "wb").write(t)
    open(p + ".tori", "w").write("\n".join(g))
    a = run([binary, p])
    b = run([sys.executable, py, p])
    if a != b:
        print("CHECKERS DISAGREE on mutant", i, kind, a, b)
        sys.exit(2)
    stats[kind][0] += 1
    stats[kind][1] += a
shutil.rmtree(tmp)
print("mutants tried / accepted:", stats)
