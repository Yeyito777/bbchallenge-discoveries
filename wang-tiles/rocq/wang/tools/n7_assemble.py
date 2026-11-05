#!/usr/bin/env python3
"""Assemble the version-4 n = 7 jobs from the per-subtree token files written by tools/c/recut.

usage: n7_assemble.py SEGDIR PREFIXES TORIDIR OUTDIR JOBS

SEGDIR holds top_CCCCC.bin (tokens read above the reset level before reset node C, from shard 0;
C = 1..5520, the last one after the last reset node) and sub_CCCCC.bin (the tokens of subtree C).
PREFIXES is tools/c/prefixes_n7.txt (the labels of cells 0..9 at each reset node, in walk order).
The subtrees are shared out over JOBS jobs, largest first, each to the least loaded job, by node
count from SEGDIR/sizes.txt. Writes OUTDIR/refs7.txt (header, then "owner labels..." per reset node),
OUTDIR/tori7.txt (from TORIDIR/tori7.txt with a header), OUTDIR/job_JJJ.tree, OUTDIR/job_JJJ.used
(the global ids of the tori the job uses) and OUTDIR/caches.txt (the cache size of each job: a power of
two at least three times the largest number of relation pairs in one of its subtrees, from
SEGDIR/rels.txt)."""
import os
import sys

seg, prefixes, toridir, out, jobs = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4], int(sys.argv[5])
os.makedirs(out, exist_ok=True)
pre = [l.split() for l in open(prefixes).read().split("\n") if l.strip()]
N = len(pre)
size = {}
for l in open(os.path.join(seg, "sizes.txt")):
    c, nodes = l.split()
    size[int(c)] = int(nodes)
assert sorted(size) == list(range(1, N + 1)), "every reset node must be walked by exactly one v3 shard"
load = [0] * jobs
owner = {}
for c in sorted(size, key=lambda c: (-size[c], c)):
    j = min(range(jobs), key=lambda j: (load[j], j))
    owner[c] = j
    load[j] += size[c]
with open(os.path.join(out, "refs7.txt"), "w") as f:
    f.write("wt-refs 4 n 7 D 17 order ringsym reset 10 jobs %d gate 500 refs %d\n" % (jobs, N))
    for c in range(1, N + 1):
        f.write("%d %s\n" % (owner[c], " ".join(pre[c - 1])))
tori = [l for l in open(os.path.join(toridir, "tori7.txt")).read().split("\n") if l.strip()]
with open(os.path.join(out, "tori7.txt"), "w") as f:
    f.write("wt-tori 4 n 7 count %d\n" % len(tori))
    f.write("\n".join(tori) + "\n")
rd = lambda name: open(os.path.join(seg, name), "rb").read()
outs = [open(os.path.join(out, "job_%03d.tree" % j), "wb") for j in range(jobs)]
for c in range(1, N + 2):
    t = rd("top_%05d.bin" % c)
    for f in outs:
        f.write(t)
    if c <= N:
        outs[owner[c]].write(rd("sub_%05d.bin" % c))
for f in outs:
    f.close()
# the global ids of the tori each job uses (from tools/c/recut's .ids files)
ids = lambda name: [int(x) for x in open(os.path.join(seg, name)).read().split()]
used = [set() for _ in range(jobs)]
for c in range(1, N + 2):
    t = ids("top_%05d.ids" % c)
    for u in used:
        u.update(t)
    if c <= N:
        used[owner[c]].update(ids("sub_%05d.ids" % c))
for j in range(jobs):
    open(os.path.join(out, "job_%03d.used" % j), "w").write("".join("%d\n" % x for x in sorted(used[j])))
# cache size per job: the largest number of relation pairs in one of its subtrees, from SEGDIR/rels.txt
rels = {}
for l in open(os.path.join(seg, "rels.txt")):
    c, r = l.split()
    rels[int(c)] = int(r)
with open(os.path.join(out, "caches.txt"), "w") as f:
    for j in range(jobs):
        m = max([rels[c] for c in owner if owner[c] == j] + [1])
        size = 1 << 14
        while size < 3 * m:
            size *= 2
        f.write("%d %d\n" % (j, size))
with open(os.path.join(out, "jobs.txt"), "w") as f:
    for j in range(jobs):
        f.write("%d %d %d\n" % (j, load[j], os.path.getsize(os.path.join(out, "job_%03d.tree" % j))))
print("jobs", jobs, "max load", max(load), "min load", min(load))
