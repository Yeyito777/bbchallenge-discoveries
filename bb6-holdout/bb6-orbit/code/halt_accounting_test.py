#!/usr/bin/env python3
"""Checks the one branch of the accounting that fires only once: a sweep ending in the halt form, and the final step and ones count.
Starts: the corpus case A(6,35) (halts at A(186,189), application 55), and the small analogues of the real halt, reset states (a0,B) that reach
the halt form by plain doubling. For each: seg gives applications and the telescoped step total; a raw TM from the same tape gives the true steps and ones."""
import subprocess,re,sys,os
W=[[1,0],[1,1],[0,0],[1,None],[0,1],[1,1]];M=[[1,-1],[1,1],[1,1],[-1,0],[-1,-1],[1,-1]];N=[[1,5],[2,0],[3,1],[4,None],[0,4],[3,0]]
def raw(a,b):
    t={};pos=0
    for i in range(a): t[-1-i]=1
    for i in range(b+1): t[i]=1
    t[b+2]=1
    s=0;n=0
    while True:
        c=t.get(pos,0)
        if N[s][c] is None: return n,sum(t.values())
        t[pos]=W[s][c]; pos+=M[s][c]; s=N[s][c]; n+=1
def seg(a0,B):
    o='/tmp/hat_%d.txt'%os.getpid()
    if os.path.exists(o): os.remove(o)
    subprocess.run(['./seg_x',str(a0),str(B),str(a0),str(B+10**7),o],stderr=subprocess.DEVNULL)
    L=open(o).read().split('\n'); h=[x for x in L if x.startswith('halt')]
    if not h: return None
    q=h[0].split(); a=int(q[2]); b=int(q[4]); offn=int(q[6]); six=int(L[1].split()[1])
    tot6=2*(a*a-a0*a0)+six+6*(a*a+7*a+41); assert tot6%6==0
    return a,b,offn,tot6//6,a+9
bad=0;cnt=0;cases=[(6,35)]
for k in range(1,11):
    for z,a0 in ((0,6),(1,22)):
        q=a0+6; a=q*2**k-6; S=q*(2**k-1)-3*k; cases.append((a0,S+a+3))
for a0,B in cases:
    r=seg(a0,B)
    if r is None: print('no halt from seg',a0,B); continue
    st,on=raw(a0,B); cnt+=1
    ok=(st==r[3] and on==r[4] and r[1]==r[0]+3)
    bad+=not ok
    print(f'A({a0},{B}) halt form A({r[0]},{r[1]}) apps {r[2]} seg steps {r[3]} raw steps {st} ones {r[4]}/{on} {"ok" if ok else "MISMATCH"}')
print('cases',cnt,'mismatches',bad)
