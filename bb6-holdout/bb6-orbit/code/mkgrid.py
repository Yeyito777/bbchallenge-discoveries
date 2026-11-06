#!/usr/bin/env python3
# Build segment list: profile of phases across an odd scale, scaled up. usage: mkgrid.py profile.txt Kprofile Kstart Kend Bstar per_seg phases_at_K59
import sys,subprocess
prof=[int(l.split()[2]) for l in open(sys.argv[1])]
Kp=int(sys.argv[2]); Ks=int(sys.argv[3]); Ke=int(sys.argv[4]); Bstar=int(sys.argv[5]); per=float(sys.argv[6]); N59=float(sys.argv[7])
pts=[b for b in prof if b>>(Kp-1)==1]
pts.sort()
fr=[b/2**Kp for b in pts]
grid=[]
for K in range(Ks,Ke+1,2):
    N=N59*2**((K-59)/2); n=max(1,int(N/per))
    for i in range(n):
        f=fr[int(i*len(fr)/n)]
        X=int(f*2**60)<<(K-60)
        if X<Bstar: grid.append(X)
for X in grid: print(X)
