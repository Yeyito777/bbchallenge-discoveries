#!/usr/bin/env python3
"""Put the results of a chain run together and compare them with the C traversal.
usage: assemble.py CHUNKS SEGLIST SEGDIR RESULT_FILES...
Checks: every chunk has a result and none failed; the chunks link from A(6,1); per segment, applications and the cost
total agree with what seg.c wrote; then prints the totals that bb6_holdout_steps in theories/Statement.v asks for."""
import sys,re
ch=[l.split() for l in open(sys.argv[1])]
L=[l.split() for l in open(sys.argv[2])]; D=sys.argv[3]
res={}
for f in sys.argv[4:]:
    for l in open(f):
        x=l.split()
        if len(x)>=3 and x[-1]!='FAIL' and x[2] in('OK','HALT'): res[x[0]]=x
        elif len(x)>=3 and x[2]=='FAIL': print('FAILED chunk',x[0],'segment',x[1])
M=2**315
missing=[c[0] for c in ch if c[0] not in res]
print('chunks',len(ch),'with results',len(ch)-len(missing))
assert ch[0][2:4]==['6','1'],'chain does not start at A(6,1)'
for c,d in zip(ch,ch[1:]): assert c[4:6]==d[2:4],('link',c[0])
apps=0; acc=0; secs=0.0; final=None; perseg={}
for c in ch:
    if c[0] not in res: continue
    r=res[c[0]]
    if r[2]=='OK': n,a=int(r[3]),int(r[4]); secs+=float(r[5])
    else: final=int(r[3]); n,a=int(r[4]),int(r[5]); secs+=float(r[6])
    apps+=n; acc=(acc+a)%M
    s=perseg.setdefault(c[1],[0,0,0]); s[0]+=n; s[1]=(s[1]+a)%M; s[2]+=1
print('compute seconds',round(secs),'core-hours',round(secs/3600,1))
bad=0;checked=0
nchunks={}
for c in ch: nchunks[c[1]]=nchunks.get(c[1],0)+1
for (i,a0,b,a1,y) in L:
    if i not in perseg or perseg[i][2]!=nchunks[i]: continue
    T=open(f'{D}/seg_{i}.txt').read().split('\n')
    m=re.search(r'apps (\d+) ',T[0]); n=int(m[1]); six=int(T[1].split()[1])
    if i==L[-1][0]:
        h=[x.split() for x in T if x.startswith('halt ')][0]; n=int(h[6])
    checked+=1
    if n!=perseg[i][0] or six%M!=perseg[i][1]:
        bad+=1; print('segment',i,'differs from seg.c: apps',perseg[i][0],'vs',n)
print('segments complete',checked,'of',len(L),'differing from seg.c',bad)
if not missing:
    a=final; R=acc if acc<M//2 else acc-M
    N=(6*35+2*(a*a-36)+R+6*(a*a+7*a+41))//6
    assert (6*35+2*(a*a-36)+R+6*(a*a+7*a+41))%6==0
    print('halt form a =',a,'= 28*2^85-6:',a==28*2**85-6)
    print('rule applications',apps)
    print('cost total R',R)
    print('steps from blank, not counting the halting transition',N)
