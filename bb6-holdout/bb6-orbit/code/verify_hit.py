#!/usr/bin/env python3
"""Independent check of a history-free run, in Python bigints.
Uses the G(c,b) form of the map (wiki), walks whole sweeps, and takes a jump only after re-walking the word at the
far end, so it shares no guard arithmetic with core.h. usage: verify_hit.py A0 Bstar lookback W [window_lo]
Starts every reset state with B in [X,X+W), X=Bstar-lookback-W, both a0. Prints the merge point and each trajectory's fate."""
import sys
def word(c,b):
    """one sweep from G(c,b) until c is 0 or 8 again. returns (letters, c', b', halted, (c,b)) """
    w=[]
    while True:
        if b==0: return w,None,None,True,(c,b)
        if b>=2*c+9: l='k'; c,b=2*c+6,b-2*c-9
        elif b==1:
            if c%2==0: l='b'; c,b=0,2*c+13
            else: l='c'; c,b=8,2*c+4
        elif b==3:
            if c%2==0: l='d'; c,b=0,2*c+19
            else: l='e'; c,b=c+4,2
        elif b%2==0:
            if (c+b//2)%2==0: l='f'; c,b=0,2*c+b+13
            else: l='g'; c,b=8,2*c+b+4
        elif (c+(b-1)//2)%2==0: l='h'; c,b=c-(b-1)//2+5,2*b-4
        elif b==2*c+7: l='j'; c,b=0,2*c+b+8
        else: l='i'; c,b=c-(b-1)//2+9,2*b-8
        w.append(l)
        if c==0 or c==8: return w,c,b,False,None
        if len(w)>20000: raise SystemExit("long tail")
class Tr:
    __slots__=('c','b','hist','halt','n')
    def __init__(s,c,b): s.c,s.b=c,b; s.hist=[]; s.halt=None; s.n=0
def step(t,Y):
    w,c1,b1,h,hs=word(t.c,t.b)
    if h: t.halt=hs; t.n+=len(w); return
    key=(t.c,''.join(w))
    t.hist.append((key,t.c,t.b,len(w))); t.c,t.b=c1,b1; t.n+=len(w)
    if len(t.hist)>16: t.hist.pop(0)
    H=t.hist
    for P in (1,2,3,4):
        if len(H)<2*P: continue
        if any(H[-1-i][0]!=H[-1-i-P][0] for i in range(P)): continue
        if H[-P][1]!=t.c: continue
        D=t.b-H[-P][2]
        if D<=0 or D%4: continue
        cyc=H[-P:]
        def good(T):
            for (key,c,b,l) in cyc:
                wx,c2,b2,hh,_=word(c,b+P*0+D*(T+1))
                if hh or (c,''.join(wx))!=key: return False
            return True
        room=(Y-t.b)//D
        if room<8: break
        if not good(8): break
        T=8
        while T*2<room and good(T*2): T*=2
        lo,hi=T,min(T*2,room)
        while hi-lo>1:
            m=(lo+hi)//2
            if good(m): lo=m
            else: hi=m
        T=lo
        t.b+=T*D; t.n+=T*sum(x[3] for x in cyc); t.hist=[]
        break
def main():
    a0=int(sys.argv[1]); Bs=int(sys.argv[2]); L=int(sys.argv[3]); W=int(sys.argv[4])
    X=Bs-L-W; c0=(a0-6)//2
    tr=[Tr(cc,X+i) for i in range(W) for cc in (0,8)]
    print("X",X,"candidates",len(tr))
    steps=0; merged=None
    live=tr; halted=[]; 
    seen=set()
    while live:
        m=min(live,key=lambda t:t.b)
        step(m,Bs+10**6); steps+=1
        if m.halt is not None:
            halted.append(m); live.remove(m)
            print("halted: a=",2*m.halt[0]+6," b=",m.halt[1]," living",len(live)); continue
        for o in live:
            if o is not m and o.c==m.c and o.b==m.b:
                live.remove(m); break
        if len(live)==1 and merged is None:
            merged=(2*live[0].c+6,live[0].b); print("merged to A(%d,%d) after %d sweep-steps; lookback from B*: %d"%(merged[0],merged[1],steps,Bs-merged[1]),flush=True)
        if live and min(t.b for t in live)>Bs+10**5: print("passed B* without halting",[(t.c,t.b) for t in live][:5]); return
    print("all trajectories halted:",len(halted))
main()
