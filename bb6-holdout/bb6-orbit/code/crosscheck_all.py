#!/usr/bin/env python3
"""One randomly chosen stretch from every segment: seg_x for exact totals, then seg2.py G (applications and steps must match) and J (Lean map, same end).
usage: crosscheck_all.py SEGLIST SAMPLEDIR WORKERS SEED OUTLOG. Resumable: segments already in OUTLOG are skipped."""
import sys,os,random,subprocess,re,time
from multiprocessing import Pool
LIST,SD,W,SEED,OUT=sys.argv[1],sys.argv[2],int(sys.argv[3]),int(sys.argv[4]),sys.argv[5]
def job(x):
    i,a0,b,a1,y=x; rnd=random.Random(SEED*1000003+int(i)); t0=time.time()
    pts=[(a0,b)]; p=f'{SD}/seg_{i}.txt'
    if os.path.exists(p):
        s=set(l.split()[1]+' '+l.split()[2] for l in open(p) if len(l.split())==3)
        pts+=sorted(((q.split()[0],q.split()[1]) for q in s),key=lambda v:int(v[1]))
    if i!='489': pts.append((a1,y))
    k=rnd.randrange(max(1,len(pts)-1)); A,B=pts[k]; A1,Y=pts[min(k+1,len(pts)-1)]
    if i=='489' and k==len(pts)-1: A,B=pts[k-1]; A1,Y=pts[k]
    tag=f'/tmp/xa_{os.getpid()}'
    for f in (tag+'.t',tag+'.f',tag+'.t.ck'):
        if os.path.exists(f): os.remove(f)
    subprocess.run(['./seg_x',A,B,A1,Y,tag+'.t',tag+'.f'],env=dict(os.environ,SEG_SAMPLE_MASK=os.environ.get('XC_MASK',str(2**18-1)),SEG_CK_SECS='100000'),stderr=subprocess.DEVNULL)
    F=[l.split() for l in open(tag+'.f')] if os.path.exists(tag+'.f') else []
    pos=[(A,B,'0')]+[(q[1],q[2],q[0]) for q in F]+[(A1,Y,None)]
    pos=[p for n_,p in enumerate(pos) if n_==0 or p[1]!=pos[n_-1][1]]  # an interval can end on its last fine sample
    j=rnd.randrange(len(pos)-1); A,B=pos[j][:2]; A1,Y=pos[j+1][:2]
    for f in (tag+'.t',tag+'.f'):
        if os.path.exists(f): os.remove(f)
    subprocess.run(['./seg_x',A,B,A1,Y,tag+'.t'],stderr=subprocess.DEVNULL)
    h=open(tag+'.t').read().split('\n'); m=re.search(r' ok (\d) apps (\d+) phases (\d+)',h[0]); six=int(h[1].split()[1])
    steps6=2*(int(A1)**2-int(A)**2)+six
    g=subprocess.run(['python3','seg2.py','G',A,B,A1,Y],capture_output=True,text=True).stdout
    mg=re.search(r'G ok .* apps (\d+) steps2 (\d+)',g)
    okg=bool(mg) and int(mg[1])==int(m[2]) and 3*int(mg[2])==steps6
    okj=' ok ' in subprocess.run(['python3','seg2.py','J',A,B,A1,Y],capture_output=True,text=True).stdout
    return f"seg={i} a0={A} B={B} a1={A1} Y={Y} apps={m[2]} phases={m[3]} seg_ok={m[1]=='1'} G={okg} J={okj} secs={time.time()-t0:.0f}"
done=set()
if os.path.exists(OUT): done={re.match(r'seg=(\d+)',l)[1] for l in open(OUT)}
L=[l.split() for l in open(LIST)]; L=[x for x in L if x[0] not in done]
random.Random(SEED).shuffle(L)
with Pool(W) as P, open(OUT,'a') as o:
    for r in P.imap_unordered(job,L):
        o.write(r+'\n'); o.flush()
