#!/usr/bin/env python3
# Numeric test of the macro rule statements on all 16 machines (mirrored ones flipped) before writing them in Rocq.
import random,sys
def parse(m,mir):
    t={}
    for i,r in enumerate(m.split('_')):
        for b in (0,1):
            x=r[3*b:3*b+3]
            if x[2] in '-Z':t[(chr(65+i),b)]=None
            else:
                d=1 if x[1]=='R' else -1
                t[(chr(65+i),b)]=(int(x[0]),d*(-1 if mir else 1),x[2])
    return t
def cells_to_cfg(parts):
    # parts: list of ints runs with separators given explicitly: we build dict from a string
    pass
class C: pass
def mk(s,head,st):
    # s string of 0/1, head index
    tape={i:int(c) for i,c in enumerate(s) if c=='1'}
    return tape,head,st
def norm(tape,head):
    ks=[k for k,v in tape.items() if v==1]
    if not ks:return ('',0)
    a,b=min(ks),max(ks)
    return (''.join(str(tape.get(i,0)) for i in range(a,b+1)),head-a)
def ones(n):return '1'*n
def LSs(ll):  # ll near first; returns string left to right ending just before separator to next
    return '0'.join(ones(a) for a in reversed(ll))
def FP(ll,p,r,y,rr,f):
    left=(LSs(ll)+'0' if ll else '')+ones(p)+'0'
    s=left+ones(r)
    head=len(s)-1
    s+='00'+ones(y)+''.join('0'+ones(e) for e in rr)
    return s,head,f
def Cf(s_,c,a):
    s=LSs(s_)+'0'+ones(6)+'0'+ones(4)+'0'+ones(c)
    head=len(s)
    return s+'0',head,a
def LSc(P,rr,f):
    s='0'+ones(P)+'001'+''.join('0'+ones(e) for e in rr)
    return s,0,f
def run(t,cfg,target,maxT=60000):
    s,h,st=cfg
    tape={i:int(c) for i,c in enumerate(s) if c=='1'}
    ts,th,tst=target if target else (None,None,None)
    tn=norm({i:int(c) for i,c in enumerate(ts) if c=='1'},th) if target else None
    tones=ts.count('1') if target else 0
    cnt=s.count('1')
    p=h;T=0
    while T<maxT:
        b=tape.get(p,0);tr=t[(st,b)]
        if tr is None:return ('HALT',T)
        cnt+=tr[0]-b
        tape[p]=tr[0];p+=tr[1];st=tr[2];T+=1
        if target and st==tst and cnt==tones and tape.get(p,0)==int(ts[th]) :
            if norm(tape,p)==tn:return ('OK',T)
    return ('NO',T)
random.seed(1)
def rr_rand(n=None,mn=3):
    return [random.randint(mn,12) for _ in range(random.randint(0,3) if n is None else n)]
res={}
for line in open('machines.txt'):
    m,mir,c,a=line.split();mir=int(mir);c=int(c)
    t=parse(m,mir)
    # roles
    f=[s for s in 'ABCDEF' if t[(s,1)] and t[(s,1)][0]==1 and t[(s,1)][1]==-1 and t[(s,1)][2]==s]
    fs=f[0]
    out={}
    tail=[6,4,2]
    for name in ['round','even','odd','top','ls','ls1','ls3','ls2','tail']:
        ok=0;bad=[]
        for it in range(30):
            ll=rr_rand(random.randint(0,3));p=random.randint(4,14);y=random.randint(1,10);rr=rr_rand()
            if name=='round':
                r=random.randint(2,10)
                cfg=FP(ll,p,r+2,y,rr+tail,fs);tg=FP(ll,p+1,r,y+1,rr+tail,fs)
            elif name=='even':
                q=random.randint(3,12);cfg=FP([q]+ll,p,2,y,rr+tail,fs);tg=FP(ll,q+1,p-2,2,[y+1]+rr+tail,fs)
            elif name=='odd':
                cfg=FP(ll,p,3,y,rr+tail,fs);tg=Cf(rr[::-1]+[y+4,p+2]+ll,c,a)
            elif name=='top':
                cfg=FP([],p,2,y,rr+tail,fs);tg=LSc(p,[y+1]+rr+tail,fs)
            elif name=='ls':
                P=random.randint(4,14);cfg=LSc(P,rr+tail,fs);tg=FP([],1,P-2,2,rr+tail,fs)
            elif name=='ls1':
                cfg=LSc(1,rr+tail,fs);tg=Cf(rr[::-1]+[4,1],c,a)
            elif name=='ls3':
                cfg=LSc(3,rr+tail,fs);tg=Cf(rr[::-1]+[5,2],c,a)
            elif name=='ls2':
                cfg=LSc(2,rr+tail,fs);tg=None
            elif name=='tail':
                x=random.randint(3,12);q=random.randint(1,12);cfg=Cf([x,q]+ll,c,a);tg=FP(ll,q+1,x+2,2,tail,fs)
            r_=run(t,cfg,tg)
            want='HALT' if name=='ls2' else 'OK'
            if r_[0]==want:ok+=1
            else:bad.append((r_,cfg[0][:50],tg[0][:50] if tg else ''))
        out[name]=(ok,bad[:1])
    print(m,'a=',a,'f=',fs,'c=',c,{k:v[0] for k,v in out.items()},[ (k,v[1]) for k,v in out.items() if v[0]<30][:2],flush=True)
