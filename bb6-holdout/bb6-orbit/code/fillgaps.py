#!/usr/bin/env python3
# Extra grid points inside segments whose estimated phase count is too large. usage: fillgaps.py seglist profile N59 limit
import sys,bisect
L=[l.split() for l in open(sys.argv[1])]
pts=sorted(int(l.split()[2]) for l in open(sys.argv[2]) if int(l.split()[2])>>50==1)
fr=[b/2**51 for b in pts]; N59=float(sys.argv[3]); lim=float(sys.argv[4])
def cum(B):
    K=B.bit_length(); c=0; k=K-2 if K%2==1 else K-1
    while k>=1: c+=N59*2**((k-59)/2); k-=2
    if K%2==1: c+=N59*2**((K-59)/2)*bisect.bisect_left(fr,B/2**K)/len(fr)
    return c
def inv(c0):
    # B with cum(B)=c0, by bisection on the real line
    lo,hi=2,1<<100
    for _ in range(400):
        m=(lo+hi)//2
        if cum(m)<c0: lo=m
        else: hi=m
        if hi-lo<=2**30: break
    return lo
for x in L[1:]:
    b0,b1=int(x[2]),int(x[4]); e=cum(b1)-cum(b0)
    if e>lim:
        n=int(e/(lim/4))
        c0=cum(b0)
        for i in range(1,n): print(inv(c0+e*i/n))
