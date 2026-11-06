#!/usr/bin/env python3
"""Estimated phase counts along the orbit. Scales with K = 1 and K = 3 mod 4 have different shapes, so each uses its own measured profile."""
import bisect,os
D=os.path.dirname(os.path.abspath(__file__))+'/../data/'
def _p(f,K):
    v=sorted(int(l.split()[2]) for l in open(D+f) if int(l.split()[2])>>(K-1)==1)
    return [b/2**K for b in v]
P={3:(_p('prof51.txt',51),51),1:(_p('prof53.txt',53),53)}
N={3:(1,),1:(1,)}
def setN(n3,n1): N[3]=(n3,); N[1]=(n1,)
def scaleN(K):
    r=K%4
    if r not in(1,3): return 0.0
    n=N[r][0]; K0=P[r][1]
    return n*2**((K-K0)/2)
def cum(B):
    K=B.bit_length(); c=0.0
    for k in range(1,K):
        c+=scaleN(k)
    if K%2==1:
        fr=P[K%4][0]; c+=scaleN(K)*bisect.bisect_left(fr,B/2**K)/len(fr)
    return c
def inv(c0,lo=2,hi=1<<100):
    while hi-lo>2**20:
        m=(lo+hi)//2
        if cum(m)<c0: lo=m
        else: hi=m
    return lo
