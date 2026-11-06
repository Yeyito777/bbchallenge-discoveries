#!/usr/bin/env python3
# Raw TM from A(a,a+3) to the halt: exact steps and ones for many a, against cost a^2+7a+41 and a formula for ones.
W=[[1,0],[1,1],[0,0],[1,None],[0,1],[1,1]];M=[[1,-1],[1,1],[1,1],[-1,0],[-1,-1],[1,-1]];N=[[1,5],[2,0],[3,1],[4,None],[0,4],[3,0]]
def run(a,b):
    t={};pos=0
    for i in range(a): t[-1-i]=1
    for i in range(b+1): t[i]=1
    t[b+2]=1
    s=0;n=0
    while True:
        c=t.get(pos,0)
        if N[s][c] is None: return n,sum(t.values()),s,c
        t[pos]=W[s][c]; pos+=M[s][c]; s=N[s][c]; n+=1
ok=True;pts=[]
for a in range(6,1400,2):
    n,o,s,c=run(a,a+3)
    pts.append((a,o))
    if n!=a*a+7*a+41: ok=False; print('steps',a,n)
    if o!=a+9: ok=False; print("ones",a,o)
print('steps a^2+7a+41 and ones a+9 hold for even a<1400:',ok)
print('sample a,ones:',pts[:5],pts[-1], 'halting transition is D reading 1, counted at the D state with symbol read 1')
