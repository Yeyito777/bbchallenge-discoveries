#!/usr/bin/env python3
"""Lean-certified high-level map highLevelNext for J(u,w) (google-deepmind/cryptids, commit c86f158), transcribed literally.
Compared with the A-map: J(0,w) and A(6,w+1) are the same tape, so from a shared tape the two maps must next agree on every
later shared tape. Tests that on many starts, up to huge values."""
import sys,random
def J_next(u,w):
    m=w//2
    if w>=2*u+3: return (2*u+3,w-2*u-3)
    if w==2*u+2: return (0,4*u+18)
    if w==2*u+1: return (11,4*u+2)
    if w==2*u: return (0,4*u+12)
    d=u-m
    if w%2==0:
        if d==1: return (0,2*w+12)
        if d%2==0: return (11,2*u+w-2)
        return (0,2*u+w+10)
    if d==1: return None
    if d==2: return (0,2*w+8)
    if d%2==0:
        if w==1: return (11,2*u+10)
        return (d+7,2*w-4)
    return (d+3,2*w)
def A_next(a,b):
    if b==a+3: return None
    if b>a+3: return (2*a+6,b-a-3)
    if b==1: return (6,a+7) if a%4==2 else (22,a-2)
    if b==3: return (6,a+13) if a%4==2 else (a+8,2)
    if b%2:
        if b==a+1: return (6,a+b+2)
        return (a-b+11,2*b-4) if ((a-b+5)//2)%2 else (a-b+19,2*b-8)
    return (6,a+b+7) if ((a-b)//2)%2 else (22,a+b-2)
def next_shared_A(a,b):
    n=0
    while True:
        r=A_next(a,b); n+=1
        if r is None: return None,n
        a,b=r
        if a==6: return (a,b),n
        if n>6000: return 'long',n
def next_shared_J(u,w):
    n=0
    while True:
        r=J_next(u,w); n+=1
        if r is None: return None,n
        u,w=r
        if u==0: return (u,w),n
        if n>6000: return 'long',n
if __name__=='__main__':
    # J(0,0) orbit equals A(6,1) orbit at every shared tape
    a,b=6,1; u,w=0,0; ok=0
    for i in range(int(sys.argv[1])):
        ra,_=next_shared_A(a,b); rj,_=next_shared_J(u,w)
        if ra is None or rj is None:
            print('halt at',i,ra,rj); break
        if ra[1]!=rj[1]+1: print('MISMATCH on orbit',a,b,u,w,ra,rj); sys.exit(1)
        a,b=ra; u,w=rj; ok+=1
    print('orbit shared tapes agree',ok,'last A',a,b)
    random.seed(5); bad=0; total=0; deep=0; halts=0; longs=0
    for i in range(int(sys.argv[2])):
        K=random.choice([random.randint(6,40),random.randint(40,400),random.randint(400,4000)])
        w=random.randrange(2**(K-1),2**K)
        # half the tests aim at long tails: start near the Cantor point of a level, where the words are deep
        if i%2:
            k=random.randint(1,K-5); a=12*2**k-6; Sk=12*(2**k-1)-3*k
            depth=random.randint(0,min(k,60))
            w=Sk+ (a*(4**depth-1))//(3*4**depth) *2 + random.randrange(-50,50) + 18
            if w<5: w=5
        ra,na=next_shared_A(6,w+1); rj,nj=next_shared_J(0,w)
        total+=1; deep+=na>k if i%2 else 0
        if (ra is None)!=(rj is None): bad+=1; print('HALT MISMATCH',w); continue
        if ra is None: halts+=1; continue
        if ra=='long' or rj=='long':
            if ra!=rj: bad+=1; print('LONG MISMATCH',w)
            else: longs+=1
            continue
        if ra[1]!=rj[1]+1: bad+=1; print('MISMATCH',w,ra,rj)
    print('random shared-tape tests',total,'mismatches',bad,'both halted',halts,'both long',longs)
