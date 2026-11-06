#!/usr/bin/env python3
"""Split oversized unfinished segments at merged states, so no single segment holds up a parallel run. Merging takes milliseconds.
A split point is only a proposal: it counts once the two neighbouring segments link exactly in the chain check.
usage: resplit.py LIST THRESH_PHASES PIECE_PHASES OUT [dirs with results and checkpoints...]; piece ids are 1000000+1000*id+i."""
import sys,os,re,struct,subprocess
sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
import est
est.setN(3108385,8194580)
SHRINK=0.82  # measured actual/estimated phases near K=79
L=[l.split() for l in open(sys.argv[1])]; TH=float(sys.argv[2]); PC=float(sys.argv[3]); OUT=sys.argv[4]; dirs=sys.argv[5:]
here=os.path.dirname(os.path.abspath(__file__))
def has(i): return any(os.path.exists(f'{d}/seg_{i}.txt') for d in dirs)
def ckB(i):
    b=None
    for d in dirs:
        p=f'{d}/seg_{i}.txt.ck'
        if os.path.exists(p):
            v=int.from_bytes(open(p,'rb').read(20)[4:20],'little')
            b=v if b is None else max(b,v)
    return b
out=[];nsplit=0
for x in L:
    i,a0,b,a1,y=x
    bb,yy=int(b),int(y)
    if has(i) or int(i)>=1000000: out.append(x); continue
    ck=ckB(i); lo=ck if ck else bb
    e=(est.cum(yy)-est.cum(lo))*SHRINK
    if e<=TH: out.append(x); continue
    n=int(e/PC)+1; c0=est.cum(lo); pts=[]
    for j in range(1,n):
        X=est.inv(c0+(est.cum(yy)-c0)*j/n)
        r=subprocess.run([here+'/cftp','merge',str(X),'4096',str(yy)],capture_output=True,text=True,timeout=600).stdout
        m=re.search(r'n=1 a0=(\d+) mergeB=(\d+)',r)
        if m and lo<int(m[2])<yy: pts.append((int(m[2]),m[1]))
    pts=sorted(set(pts)); nsplit+=1
    print(f'seg {i} bits {bb.bit_length()} est {e:.3g} ck {bool(ck)} pieces {len(pts)+1}',file=sys.stderr)
    # the first piece keeps the original id, so its checkpoint stays valid
    cur=(a0,b); pid=i
    for k,(B,aa) in enumerate(pts):
        out.append([pid,cur[0],cur[1],aa,str(B)]); cur=(aa,str(B)); pid=str(1000000+1000*int(i)+k)
    out.append([pid,cur[0],cur[1],a1,y])
with open(OUT,'w') as f:
    for x in out: f.write(' '.join(x)+'\n')
E=[(est.cum(int(x[4]))-est.cum(int(x[2])))*SHRINK for x in out if not has(x[0])]
print(f'split {nsplit} segments; list {len(out)}; remaining {len(E)}; est phases {sum(E):.4g}; max {max(E):.3g}',file=sys.stderr)
