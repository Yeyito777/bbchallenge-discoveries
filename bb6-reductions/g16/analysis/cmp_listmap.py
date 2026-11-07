#!/usr/bin/env python3
# Compare listmap against the raw-derived event stream: gensim events converted to lists; every list with tail "6 4 1" in state A.
import subprocess,sys,re
from listmap import step
M=sys.argv[1];n=sys.argv[2]
out=subprocess.run(f"../code/gensim {M} -E {n} -T 100 | python3 ../code/unary.py",shell=True,capture_output=True,text=True).stdout.splitlines()
seq=[]
for l in out:
    p=l.split()
    if len(p)<4 or p[1]!='R':continue
    if p[-1].startswith('z1<') or p[-1].startswith('z'):
        pass
    toks=[x for x in p[3:] if re.match(r'^\d+$',x)]
    if len(toks)>=3 and toks[-3:]==['6','4','1'] and not any(x.startswith('z2') for x in p[3:-1]):
        seq.append(list(map(int,toks[:-3])))
print('states',len(seq),seq[:3],seq[-1][:6])
start=None
for i,s in enumerate(seq):
    if len(s)>=2:start=i;break
a=seq[start][:];ok=0;bad=0
for k in range(start+1,len(seq)):
    step(a)
    if a==seq[k]:ok+=1
    else:
        bad+=1;print('MISMATCH at',k,'pred',a[:12],'real',seq[k][:12]);a=seq[k][:]
        if bad>5:break
print('ok',ok,'bad',bad)
