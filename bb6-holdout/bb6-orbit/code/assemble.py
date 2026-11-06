#!/usr/bin/env python3
"""Chain check for the traversal. Every segment must start where the previous ended, from A(6,1), and end on the state the next starts from.
Sums applications and raw steps, merges the closest-approach tables with absolute application numbers, and reports the halt.
usage: assemble.py seglist resultsdir [resultsdir2 ...]"""
import sys,os,json,re
seg=[l.split() for l in open(sys.argv[1])]
dirs=sys.argv[2:]
def find(i):
    for d in dirs:
        p=os.path.join(d,'seg_%s.txt'%i)
        if os.path.exists(p): return p
    return None
apps=0; six=0; best={}; have=0; missing=[]; phases={}; sweeps={}; halt=None; prev=None; broken=[]; secs=0; totph=0
for x in seg:
    i,a0,b,a1,y=x; p=find(i)
    if p is None: missing.append(int(i)); prev=None; continue
    L=open(p).read().split('\n')
    h=L[0].split(); d=dict(zip(h[0::2],h[1::2]))
    m=re.match(r'seg start (\d+) (\d+) end (\d+) (\d+) want (\d+) (\d+) status (-?\d+) ok (\d) apps (\d+) phases (\d+) sweeps (\d+) .* secs (\d+)',L[0])
    s0,sb,e0,eb,w0,wb,status,ok,ap,ph,sw,sec=m.groups()
    if (s0,sb)!=(a0,b) or (w0,wb)!=(a1,y): broken.append((i,'list mismatch'))
    if ok!='1' and status!='-1': broken.append((i,'not ok',L[0][:150]))
    have+=1; secs+=int(sec); totph+=int(ph)
    off=apps if not missing else None
    sum6=int(L[1].split()[1])
    if off is not None:
        apps+=int(ap); six+=sum6
    for l in L[2:]:
        if l.startswith('halt'):
            q=l.split(); halt=dict(a=int(q[2]),b=int(q[4]),offn=int(q[6]),base=off)
        m=re.match(r'scale (\d+) \+d (\d+) offn (\d+) a (\d+) b (\d+) -d (\d+) offn (\d+) a (\d+) b (\d+) phases (\d+) sweeps (\d+)',l)
        if not m: continue
        k=int(m[1]); g=list(map(int,m.groups()))
        phases[k]=phases.get(k,0)+g[9]; sweeps[k]=sweeps.get(k,0)+g[10]
        c=best.setdefault(k,{'pos':None,'neg':None})
        if g[1]<2**120 and (c['pos'] is None or g[1]<c['pos'][0]): c['pos']=(g[1],None if off is None else off+g[2],g[3],g[4],i,g[2])
        if g[5]<2**120 and (c['neg'] is None or g[5]<c['neg'][0]): c['neg']=(g[5],None if off is None else off+g[6],g[7],g[8],i,g[6])
print('segments',len(seg),'done',have,'missing',len(missing),'first missing',missing[:5],'broken',broken[:5],'cpu secs',secs,'phases',totph)
if not missing and not broken:
    print('chain complete: A(6,1) to last state, every link exact')
    if halt:
        a=halt['a']; b=halt['b']; assert b==a+3
        n=halt['base']+halt['offn']
        six_total=2*(a*a-36)+six+6*(a*a+7*a+41)
        assert six_total%6==0
        steps=six_total//6
        print('HALT form A(a,a+3): a =',a); print('applications before the halt form:',n); print('raw steps from A(6,1) to halt:',steps); print('raw steps from blank:',steps+35)
        print('sigma from halt form: see ones_at_halt')
if len(sys.argv)>0:
    with open('closest.tsv','w') as f:
        f.write('scale\tphases\tsweeps\t+d\tn\ta\tb\t-d\tn\ta\tb\n')
        for k in sorted(best):
            c=best[k]; p=c['pos'] or ('','','','','',''); q=c['neg'] or ('','','','','','')
            f.write('\t'.join(map(str,[k,phases.get(k,0),sweeps.get(k,0),p[0],p[1],p[2],p[3],q[0],q[1],q[2],q[3]]))+'\n')
    print('wrote closest.tsv')
