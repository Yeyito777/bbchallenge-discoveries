import sys
from lsim import T,tolist
def runp(P,ent,maxT=3000000,nev=6):
    # tape: <F> blank, 1^P, 0 0, 1, 0, entries..., head F on the blank left of 1^P
    tape={};q=1
    for j in range(P):tape[q]=1;q+=1
    q+=2
    tape[q]=1;q+=1
    for e in ent:
        q+=1
        for j in range(e):tape[q]=1;q+=1
    p=0;lo=0;hi=q;s='F';t=0;ev=[];aR=False;aL=False
    while t<maxT and len(ev)<nev:
        b=tape.get(p,0);tr=T[(s,b)]
        if tr is None:
            ev.append(('HALT',t,tolist(tape,lo,hi)));break
        tape[p]=tr[0];p+=tr[1];s=tr[2];t+=1
        if p<lo:
            lo=p
            if aL:ev.append(('L',s,t,tolist(tape,lo,hi)));aL=False
        elif p>hi:
            hi=p
            if aR:ev.append(('R',s,t,tolist(tape,lo,hi)));aR=False
        if p>lo+3:aL=True
        if p<hi-3:aR=True
    return ev
for P in range(1,26):
    e=runp(P,[20,9,8,6,4,2],nev=3)
    print(P,[ (x[0],x[1],x[-1][:44]) if x[0]!='HALT' else ('HALT',x[1],x[2][:44]) for x in e])
