#!/usr/bin/env python3
import sys
from lsim import T
def show(tape,lo,hi,p,s):
    a=''.join(str(tape.get(i,0)) for i in range(lo,p));b=str(tape.get(p,0));c=''.join(str(tape.get(i,0)) for i in range(p+1,hi+1))
    def comp(x):
        # runs: 1^n as n, zeros: single as ' ', multiple as zK
        out=[];i=0
        while i<len(x):
            j=i
            while j<len(x) and x[j]==x[i]:j+=1
            n=j-i
            if x[i]=='1':out.append(str(n))
            else:
                if n>1:out.append('z%d'%n)
                else:out.append('.')
            i=j
        return ' '.join(out)
    return comp(a)+' <%s:%s> '%(s,b)+comp(c)
lst=list(map(int,sys.argv[1].split(',')));Tmax=int(sys.argv[2]);q0=int(sys.argv[3]) if len(sys.argv)>3 else 3
tape={};q=0
for i,a in enumerate(lst):
    for j in range(a):tape[q]=1;q+=1
    if i<len(lst)-1:tape[q]=0;q+=1
p=q;lo=0;hi=q;s='A';t=0;d=0;ext=p
while t<Tmax:
    b=tape.get(p,0);tr=T[(s,b)]
    if tr is None:print('HALT',t,show(tape,lo,hi,p,s));break
    tape[p]=tr[0];p+=tr[1];s=tr[2];t+=1
    lo=min(lo,p);hi=max(hi,p)
    rev=False
    if d>=0 and p>=ext:ext=p;d=1
    elif d<=0 and p<=ext:ext=p;d=-1
    elif d==1 and ext-p>q0:rev=True;d=-1;ext=p
    elif d==-1 and p-ext>q0:rev=True;d=1;ext=p
    if rev:print(t,show(tape,lo,hi,p,s))
