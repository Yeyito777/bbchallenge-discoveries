# Sweep-level exploration: at each first crossing of level k in each a0 family, print r and residues
import sys
def S(a0,k): return (a0+6)*(2**k-1)-3*k
def A(a0,k): return (a0+6)*2**k-6
def br(a,b):
    if b==a+3: return 'H'
    if b>a+3: return 'D'
    if b==1: return 'p' if a%4==2 else 'q'
    if b==3: return 'r' if a%4==2 else 's'
    if b%2:
        if b==a+1: return 't'
        return 'u' if ((a-b+5)//2)%2 else 'v'
    return 'w' if ((a-b)//2)%2 else 'x'
def ap(k,a,b):
    return {'D':(2*a+6,b-a-3),'p':(6,a+7),'q':(22,a-2),'r':(6,a+13),'s':(a+8,2),'t':(6,a+b+2),'u':(a-b+11,2*b-4),'v':(a-b+19,2*b-8),'w':(6,a+b+7),'x':(22,a+b-2)}[k]
a,b=6,1;n=0
seen={}
N=int(sys.argv[1])
from collections import Counter
cls=Counter()
while n<N:
    a0,B=a,b
    w='';
    while True:
        k=br(a,b); w+=k
        a,b=ap(k,a,b); n+=1
        if a in(6,22): break
    if a0 in (6,22):
        kk=len(w)-len(w.lstrip('D'))
        key=(a0,kk)
        cls[(a0,kk%4,B%4, )]+=1
        if key not in seen:
            seen[key]=1
            r=B-S(a0,kk)
            print(f"a0={a0} k={kk} B={B} r={r} B%4={B%4} (k+1)%4... S_k%4={S(a0,kk)%4} r%4={r%4} word={w.lstrip('D')[:30]}")
for x in sorted(cls): print(x,cls[x])
