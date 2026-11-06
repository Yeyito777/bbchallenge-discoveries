# From raw TM, print every A-form and J-form tape in order, starting at A(a,b).
import sys
W=[[1,0],[1,1],[0,0],[1,None],[0,1],[1,1]];M=[[1,-1],[1,1],[1,1],[-1,0],[-1,-1],[1,-1]];N=[[1,5],[2,0],[3,1],[4,None],[0,4],[3,0]]
def run(a,b,lim=3000000):
    t={};pos=0
    for i in range(a): t[-1-i]=1
    for i in range(b+1): t[i]=1
    t[b+2]=1
    s=0;n=0;out=[]
    def tape():
        ks=[k for k,v in t.items() if v]; lo=min(ks);hi=max(ks)
        return ''.join(str(t.get(i,0)) for i in range(lo,pos)),''.join(str(t.get(i,0)) for i in range(pos,hi+1))
    while n<lim:
        c=t.get(pos,0)
        if s==0 and c==1:
            L,R=tape()
            import re
            mr=re.fullmatch(r'(1+)01',R)
            if mr:
                mj=re.fullmatch(r'11111((?:10)*)1',L)
                if set(L)<={'1'} : out.append(('A',len(L),len(mr[1])-1,n))
                if mj: out.append(('J',len(mj[1])//2,len(mr[1])-2,n))
        if N[s][c] is None: out.append(('H',n)); break
        t[pos]=W[s][c]; pos+=M[s][c]; s=N[s][c]; n+=1
        if len(out)>12: break
    return out
for a,b in [(6,41),(22,61),(22,201),(18,101)]:
    print((a,b),run(a,b))
