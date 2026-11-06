#!/usr/bin/env python3
"""Standalone check of the stored traversal. No other files of this project are imported.
usage: check_chain.py SEGLIST SEGDIR
Checks: the list starts at A(6,1) and each entry ends where the next starts; each stored result matches its list entry and landed exactly on its target,
except the last, which must record the halt form; then sums applications and raw steps. It trusts the numbers seg wrote: replay_segment.sh reruns any segment."""
import sys,re
L=[l.split() for l in open(sys.argv[1])]; D=sys.argv[2]
assert L[0][1:3]==['6','1'],'does not start at A(6,1)'
for i in range(len(L)-1): assert L[i][3:5]==L[i+1][1:3],('list link',i)
apps=0; six=0; H=None; phases=0
for k,(i,a0,b,a1,y) in enumerate(L):
    T=open(f'{D}/seg_{i}.txt').read().split('\n')
    m=re.match(r'seg start (\d+) (\d+) end (\d+) (\d+) want (\d+) (\d+) status (-?\d+) ok (\d) apps (\d+) phases (\d+) ',T[0])
    assert m,('format',i)
    s0,sb,e0,eb,w0,wb,st,ok,ap,ph=m.groups()
    assert [s0,sb,w0,wb]==[a0,b,a1,y],('entry',i)
    assert T[1].startswith('sum6R '),('sum',i)
    h=[x.split() for x in T if x.startswith('halt ')]
    if k<len(L)-1:
        assert st=='0' and ok=='1' and [e0,eb]==[a1,y] and not h,('segment',i)
    else:
        assert st=='-1' and len(h)==1 and int(eb)<=int(y),('last',i)
        H=(int(h[0][2]),int(h[0][4]),apps+int(h[0][6]))
    apps+=int(ap); six+=int(T[1].split()[1]); phases+=int(ph)
a,b,n=H
assert b==a+3
six_total=2*(a*a-36)+six+6*(a*a+7*a+41)   # 6*steps = 2*(a_end^2-a_start^2) + sum of 6R, plus the last rule a^2+7a+41
assert six_total%6==0
steps=six_total//6
print('segments',len(L),'all linked; phases',phases)
print('halt form A(a,a+3): a =',a,'= 28*2^85-6:',a==28*2**85-6)
print('rule applications from A(6,1) to the halt form:',n)
print('raw steps from A(6,1) to the halting configuration:',steps)
print('raw steps from blank, not counting the halting transition (35 to reach A(6,1)):',steps+35)
print('raw steps from blank, counting the halting transition:',steps+36)
print('ones at the halt:',a+9)
print('halt tape: 0^inf 1^5 (10)^%d D>1 0^inf'%(a+3))
