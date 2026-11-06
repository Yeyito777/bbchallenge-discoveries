#!/usr/bin/env python3
"""Second implementation of a traversal segment, Python bigints, sharing no code with seg.c.
Mode G: the wiki's G(c,b) map, costs summed per letter from the raw-step polynomials with no telescoping, reports applications and steps.
Mode J: the Lean-certified highLevelNext directly; reports only that the end state is reached. J(0,w)=A(6,w+1), J(11,w)=A(22,w+4), so w=B-4.
A jump repeats a sweep cycle only after re-walking its word at the far end, so guards are read from real walks.
usage: seg2.py G|J A0 B A1 Y [budget_seconds]"""
import sys,time
from fractions import Fraction as F
def G_word(c,b):
    """Sweep in G form. Returns letters, list of (a,b) at each letter in A coordinates, final (c,b) or None on halt."""
    w=[];tr=[]
    while True:
        a=2*c+6
        if b==0: return w,tr,None
        tr.append((a,b))
        if b>=2*c+9:
            # D letter of the A map, except b==2c+9 which leads to b==0
            w.append('k'); c,b=2*c+6,b-2*c-9
        elif b==1:
            if c%2==0: w.append('b'); c,b=0,2*c+13
            else: w.append('c'); c,b=8,2*c+4
        elif b==3:
            if c%2==0: w.append('d'); c,b=0,2*c+19
            else: w.append('e'); c,b=c+4,2
        elif b%2==0:
            if (c+b//2)%2==0: w.append('f'); c,b=0,2*c+b+13
            else: w.append('g'); c,b=8,2*c+b+4
        elif (c+(b-1)//2)%2==0: w.append('h'); c,b=c-(b-1)//2+5,2*b-4
        elif b==2*c+7: w.append('j'); c,b=0,2*c+b+8
        else: w.append('i'); c,b=c-(b-1)//2+9,2*b-8
        if c==0 or c==8: return w,tr,(c,b)
        if len(w)>50000: raise SystemExit('long tail at %d %d'%(c,b))
# raw steps of one letter from (a,b), doubled; A-map names: k=D (or the final step into b=0 when b==a+3 is handled as halt)
def cost2(l,a,b):
    if l=='k': return 2*(a*a+3*a+15)
    if l=='b': return 13*a+142
    if l=='c': return 13*a+406
    if l=='d': return 21*a+282
    if l=='e': return 11*a+88
    if l=='f': return 2*b*b+13*a-3*b+150
    if l=='g': return 2*b*b+13*a-3*b+414
    if l=='h': return 2*b*b+11*a-5*b+85
    if l=='i': return 2*b*b+19*a-13*b+231
    if l=='j': return 2*(a*a+5*a+41)
    raise ValueError(l)
def J_word(u,w):
    let=[]
    while True:
        m=w//2
        if w>=2*u+3: let.append('1'); u,w=2*u+3,w-2*u-3
        elif w==2*u+2: let.append('2'); u,w=0,4*u+18
        elif w==2*u+1: let.append('3'); u,w=11,4*u+2
        elif w==2*u: let.append('4'); u,w=0,4*u+12
        else:
            d=u-m
            if w%2==0:
                if d==1: let.append('5'); u,w=0,2*w+12
                elif d%2==0: let.append('6'); u,w=11,2*u+w-2
                else: let.append('7'); u,w=0,2*u+w+10
            else:
                if d==1: return let,[],None
                if d==2: let.append('8'); u,w=0,2*w+8
                elif d%2==0:
                    if w==1: let.append('9'); u,w=11,2*u+10
                    else: let.append('a'); u,w=d+7,2*w-4
                else: let.append('b'); u,w=d+3,2*w
        if u==0 or u==11: return let,[],(u,w)
        if len(let)>50000: raise SystemExit('long tail')
class Run:
    def __init__(s,mode,x,y,Y):
        s.mode=mode;s.x=x;s.y=y;s.Y=Y;s.apps=0;s.steps2=0;s.hist=[];s.sweeps=0;s.jumps=0;s.halt=None
        s.word=G_word if mode=='G' else J_word
    def step(s):
        w,tr,nx=s.word(s.x,s.y); s.sweeps+=1
        if nx is None:
            s.halt=(s.x,s.y,w,tr); return
        s.apps+=len(w)
        if s.mode=='G':
            for l,(a,b) in zip(w,tr): s.steps2+=cost2(l,a,b)
        key=(s.x,''.join(w))
        s.hist.append((key,s.x,s.y,w,tr)); s.x,s.y=nx
        if len(s.hist)>16: s.hist.pop(0)
        H=s.hist
        for P in (1,2,3,4,5,6):
            if len(H)<2*P or any(H[-1-i][0]!=H[-1-i-P][0] for i in range(P)) or H[-P][1]!=s.x: continue
            D=s.y-H[-P][2]
            if D<=0 or D%4: continue
            room=(s.Y-s.y)//D-1
            if room<4: break
            cyc=H[-P:]
            def good(T):
                for key,x0,y0,_,_ in cyc:
                    w2,_,nx2=s.word(x0,y0+D*(T+1))
                    if nx2 is None or (x0,''.join(w2))!=key: return False
                return True
            if not good(1): break
            T=1
            while T*2<=room and good(T*2): T*=2
            lo,hi=T,min(2*T,room+1)
            while hi-lo>1:
                m=(lo+hi)//2
                if good(m): lo=m
                else: hi=m
            T=lo
            if s.mode=='G':
                # exact sum over t=1..T for each letter: a,b affine in t, cost quadratic, so the sum is a cubic through 4 points
                for key,x0,y0,w0,tr0 in cyc:
                    _,tr1,_=s.word(x0,y0+D)
                    for l,(a0,b0),(a1,b1) in zip(w0,tr0,tr1):
                        da,db=a1-a0,b1-b0
                        f=lambda t:cost2(l,a0+t*da,b0+t*db)
                        # f(t)=c0+c1 t+c2 t^2 with c from f(1),f(2),f(3)
                        f1,f2,f3=f(1),f(2),f(3)
                        c2=(f3-2*f2+f1)//2; c1=f2-f1-3*c2; c0=f1-c1-c2
                        assert f(4)==c0+4*c1+16*c2
                        s.steps2+=c0*T+c1*T*(T+1)//2+c2*T*(T+1)*(2*T+1)//6
            s.apps+=T*sum(len(c[3]) for c in cyc)
            s.y+=T*D; s.hist=[]; s.jumps+=1
            break
def main():
    mode=sys.argv[1]; a0=int(sys.argv[2]); B=int(sys.argv[3]); a1=int(sys.argv[4]); Y=int(sys.argv[5])
    if mode=='G': x,y,xe,ye=(a0-6)//2,B,(a1-6)//2,Y
    else:
        x,y=(0,B-1) if a0==6 else (11,B-4); xe,ye=(0,Y-1) if a1==6 else (11,Y-4)
    r=Run(mode,x,y,ye); t0=time.time()
    while r.y<ye and r.halt is None: r.step()
    if r.halt:
        if mode=='G':
            c,b,w,tr=r.halt; r.apps+=len(w)-0
            for l,(a,bb) in zip(w,tr): r.steps2+=cost2(l,a,bb)
            print('halted in sweep from',c,b,'letters',len(w),'apps',r.apps,'steps2 before halt',r.steps2)
        else: print('halted J',r.halt[0],r.halt[1])
        return
    ok=(r.x,r.y)==(xe,ye)
    print(mode,'ok' if ok else 'MISMATCH',(r.x,r.y),'apps',r.apps,'steps2',r.steps2,'sweeps',r.sweeps,'jumps',r.jumps,'secs %.1f'%(time.time()-t0))
    sys.exit(0 if ok else 1)
main()
