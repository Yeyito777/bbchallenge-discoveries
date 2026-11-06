#!/usr/bin/env python3
# Fit exact raw-step polynomials per rule branch from tm_check VERBOSE rows, split by a mod 4, b mod 4, then report the coarsest split that fits.
import sys, itertools
from fractions import Fraction as F
rows=[tuple(map(int,l.split())) for l in open(sys.argv[1]) if len(l.split())==6]
by={}
for k,a,b,pa,pb,st in rows: by.setdefault(k,[]).append((a,b,st))
def solve(pts):
    # monomials 1,a,b,a2,ab,b2
    mons=lambda a,b:[1,a,b,a*a,a*b,b*b]
    M=[]
    for a,b,s in pts: M.append([F(x) for x in mons(a,b)]+[F(s)])
    # gaussian elimination, free vars set 0
    n=6; piv=[];r=0
    for c in range(n):
        p=None
        for i in range(r,len(M)):
            if M[i][c]!=0: p=i;break
        if p is None: continue
        M[r],M[p]=M[p],M[r]
        pv=M[r][c]; M[r]=[x/pv for x in M[r]]
        for i in range(len(M)):
            if i!=r and M[i][c]!=0:
                f=M[i][c]; M[i]=[x-f*y for x,y in zip(M[i],M[r])]
        piv.append(c); r+=1
    for i in range(r,len(M)):
        if M[i][n]!=0: return None
    sol=[F(0)]*n
    for i,c in enumerate(piv): sol[c]=M[i][n]
    return sol
names={0:'H',1:'D',2:'p',3:'q',4:'r',5:'s',6:'t',7:'u',8:'v',9:'w',10:'x'}
for k in sorted(by):
    pts=by[k]
    done=False
    for ma,mb in [(1,1),(2,1),(1,2),(4,1),(1,4),(2,2),(4,2),(2,4),(4,4),(8,4),(4,8),(8,8)]:
        cl={}
        for a,b,s in pts: cl.setdefault((a%ma,b%mb),[]).append((a,b,s))
        out={}
        ok=True
        for key,v in cl.items():
            s=solve(v)
            if s is None: ok=False;break
            out[key]=s
        if ok:
            print(names[k],'mod',(ma,mb),'n=',len(pts))
            for key in sorted(out): print('  ',key,'1,a,b,a2,ab,b2 =',[str(x) for x in out[key]], 'pts',len(cl[key]))
            done=True;break
    if not done: print(names[k],'NO FIT',len(pts))
