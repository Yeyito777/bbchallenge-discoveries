#!/usr/bin/env python3
# raw TM from a list tape 1^a1 0 1^a2 0 ... 1^ak with head on the blank after it, in a given state. Prints successive right-edge/left-edge configs as lists.
import sys
M='1RB1RA_1LC0RC_1RE0LD_0RE0LF_1RA---_1RB1LF'
def parse(m):
    t={}
    for i,r in enumerate(m.split('_')):
        for b in (0,1):
            x=r[3*b:3*b+3]
            t[(chr(65+i),b)]=None if x[2]=='-' else (int(x[0]),1 if x[1]=='R' else -1,x[2])
    return t
T=parse(M)
def tolist(tape,lo,hi):
    s=''.join(str(tape.get(i,0)) for i in range(lo,hi+1)).strip('0')
    res=[];
    i=0
    out=[]
    for part in s.replace('00',' z ').replace(' z 0',' z z ').split(' '):
        if part=='z':out.append('z');continue
        if part=='':continue
        out+= [str(len(q)) for q in part.split('0')]
    return ' '.join(out)
def run(lst,st='A',maxT=10**8,nev=12,verbose=True):
    tape={};q=0
    for i,a in enumerate(lst):
        for j in range(a):tape[q]=1;q+=1
        if i<len(lst)-1:tape[q]=0;q+=1
    p=q;lo=0;hi=q;s=st;t=0;ev=[];aR=False;aL=True
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
if __name__=='__main__':
    lst=list(map(int,sys.argv[1].split(',')))
    for e in run(lst,nev=int(sys.argv[2]) if len(sys.argv)>2 else 12):print(e)
