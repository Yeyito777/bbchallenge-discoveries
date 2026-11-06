#!/usr/bin/env python3
"""Ties the A-map to the Lean-certified map. Claim: for u>=3, J(u,w) and A(2u,w+4) are one orbit: A(a,b) reaches J(a/2,b-4) on the raw
machine, and A-map iteration from A(2u,w+4) lands exactly on the A-image of highLevelNext(J(u,w)). J(0,w) is the tape A(6,w+1).
Halt of T at (u,w) is the A-state (2u,2u+3), the halt form.
Both maps are piecewise affine, with guards that are linear with small coefficients plus residues mod 8. The exhaustive grid below takes
every (u,w) with u,w up to N, far past all the constants, so every guard region is sampled at non-collinear points; agreement there means
the two affine pieces coincide on the whole region. Huge random tests then probe it directly."""
import sys,random
sys.path.insert(0,'.')
from leanmap import J_next,A_next
def img(u,w): return (6,w+1) if u==0 else (2*u,w+4)
def check(u,w):
    # T(J(u,w)) against A-map from img(u,w). Takes up to 3 letters: one T step is a D, or a D and a small-b letter, or one reset letter.
    r=J_next(u,w)
    a,b=img(u,w)
    if u==0:  # J(0,w) -> J(3,w-3) when w>=3: same A state (6,w+1) on both sides
        if r is None: return 'T-halts-at-u0'
        if w>=3: return None if img(*r)==(a,b) else ('u0',u,w,r,a,b)
    if r is None:
        return None if b==a+3 else ('halt',u,w,a,b)
    target=img(*r)
    x,y=a,b
    for i in range(4):
        s=A_next(x,y)
        if s is None: return ('A-halt-early',u,w)
        x,y=s
        if (x,y)==target: return None
    return ('nomatch',u,w,r,target,(x,y))
N=int(sys.argv[1]); M=int(sys.argv[2])
bad=0;tot=0
for u in range(1,N):
    for w in range(0,2*N):
        tot+=1
        e=check(u,w)
        if e: bad+=1; print(e) if bad<20 else 0
for w in range(3,2*N):
    tot+=1; e=check(0,w)
    if e: bad+=1; print(e) if bad<20 else 0
print('grid',N,'tests',tot,'fail',bad)
random.seed(11); bad2=0
for i in range(M):
    K=random.choice([20,64,128,300,1000,4000])
    u=random.randrange(1,2**K)
    mode=i%4
    if mode==0: w=random.randrange(0,2**K)
    elif mode==1: w=max(0,2*u+random.randint(-40,40))
    elif mode==2: w=max(0,2*u//3+random.randint(-40,40))
    else: w=random.randint(0,40)
    e=check(u,w)
    if e: bad2+=1; print(e) if bad2<20 else 0
print('random',M,'fail',bad2)
# Orbit: every J state on the Lean orbit from J(0,0) has its image on the A orbit from A(6,1), in order.
a,b=6,1;u,w=0,0; n=0; J=0
for i in range(int(sys.argv[3])):
    r=J_next(u,w)
    if r is None: print('T halt'); break
    u,w=r; t=img(u,w); J+=1
    while (a,b)!=t:
        s=A_next(a,b); n+=1
        if s is None: print('A halt'); break
        a,b=s
        if n>4*int(sys.argv[3])+100: print('LOST',u,w,a,b); sys.exit(1)
print('orbit: J steps',J,'A applications',n,'final A',a,b)
