#!/usr/bin/env python3
"""Cut the 712 segments of the traversal into chunks at the states the C runs sampled (every 2^24 phases).
usage: mkchunks.py SEGLIST SAMPLEDIR... > chunks.tsv
Output: chunk_id seg_id z B z1 Y, with z = a0 of the reset state. A wrong sample would only make its chunk fail."""
import sys,os
seglist=sys.argv[1]; dirs=sys.argv[2:]
cid=0
for line in open(seglist):
    i,a0,b,a1,y=line.split()
    pts=set()
    for d in dirs:
        p=f'{d}/seg_{i}.txt'
        if os.path.exists(p):
            for s in open(p):
                f=s.split()
                if len(f)==3 and int(b)<int(f[2])<int(y): pts.add((int(f[2]),f[1]))
    prev=(int(b),a0)
    for B,z in sorted(pts):
        print(cid,i,prev[1],prev[0],z,B); cid+=1; prev=(B,z)
    print(cid,i,prev[1],prev[0],a1,y); cid+=1
