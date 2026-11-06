#!/usr/bin/env python3
# Raw TM from A(a,a+3): the tape at the halt, as runs, relative to the leftmost 1. Checks one closed form for every even a in range, then prints it for the real a.
import re
W=[[1,0],[1,1],[0,0],[1,None],[0,1],[1,1]];M=[[1,-1],[1,1],[1,1],[-1,0],[-1,-1],[1,-1]];N=[[1,5],[2,0],[3,1],[4,None],[0,4],[3,0]]
def run(a,b):
    t={};pos=0
    for i in range(a): t[-1-i]=1
    for i in range(b+1): t[i]=1
    t[b+2]=1
    s=0;n=0
    while True:
        c=t.get(pos,0)
        if N[s][c] is None:
            k=[x for x,v in t.items() if v]; lo,hi=min(k),max(k)
            return ''.join(str(t.get(i,0)) for i in range(lo,hi+1)),pos-lo,s,c,n
        t[pos]=W[s][c]; pos+=M[s][c]; s=N[s][c]; n+=1
for a in (6,8,10,12,22,50):
    tape,p,s,c,n=run(a,a+3)
    print(a,'head offset',p,'state','ABCDEF'[s],'reads',c,'steps',n,'tape',re.sub(r'(10)+',lambda m:'(10)^%d '%(len(m[0])//2),tape) if a>10 else tape)

ok=True
for a in range(6,800,2):
    tape,p,s,c,n=run(a,a+3)
    if not (tape=='11111'+'10'*(a+3)+'1' and p==len(tape)-1 and s==3 and c==1 and n==a*a+7*a+41 and tape.count('1')==a+9): ok=False; print('fails at',a)
print('closed form 0^inf 1^5 (10)^(a+3) D>1 0^inf, steps a^2+7a+41, ones a+9, holds for every even a in 6..798:',ok)
