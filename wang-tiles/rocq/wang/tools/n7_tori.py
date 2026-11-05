#!/usr/bin/env python3
"""Merge the torus tables of the 64 v3 shards into one global table.

usage: n7_tori.py CERTDIR OUTDIR
Reads CERTDIR/n7_D17_sNNN.tori.xz, writes OUTDIR/tori7.txt (one torus per line, "a b s cells...",
in order of first appearance over shards 0..63) and OUTDIR/map_sNNN.txt (for each local torus id
of shard NNN, its global id)."""
import lzma
import os
import sys

certs, out = sys.argv[1], sys.argv[2]
os.makedirs(out, exist_ok=True)
ids, table = {}, []
for s in range(64):
    lines = lzma.open(os.path.join(certs, "n7_D17_s%03d.tori.xz" % s), "rt").read().split("\n")
    assert lines[0].startswith("wt-cert 3 n 7 D 17 order ringsym"), lines[0]
    m = []
    for l in lines[1:]:
        if not l.strip():
            continue
        key = " ".join(l.split())
        if key not in ids:
            ids[key] = len(table)
            table.append(key)
        m.append(ids[key])
    open(os.path.join(out, "map_s%03d.txt" % s), "w").write("\n".join(map(str, m)) + "\n")
open(os.path.join(out, "tori7.txt"), "w").write("\n".join(table) + "\n")
print("global tori", len(table))
