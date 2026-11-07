import sys
exec(open('ruletest.py').read().split("random.seed(1)")[0])
def comp(x):
    out=[];i=0
    while i<len(x):
        j=i
        while j<len(x) and x[j]==x[i]:j+=1
        n=j-i
        out.append(str(n) if x[i]=='1' else ('.' if n==1 else 'z%d'%n))
        i=j
    return ' '.join(out)
def trace(t,cfg,n=60,every=1):
    s,h,st=cfg
    tape={i:int(c) for i,c in enumerate(s) if c=='1'}
    p=h;T=0
    lo=min(tape);hi=max(tape)
    for T in range(n):
        lo=min(lo,p);hi=max(hi,p)
        a=''.join(str(tape.get(i,0)) for i in range(lo,p));b=tape.get(p,0);c=''.join(str(tape.get(i,0)) for i in range(p+1,hi+1))
        print(T,comp(a),'<%s:%d>'%(st,b),comp(c))
        tr=t[(st,b)]
        if tr is None:print('HALT');return
        tape[p]=tr[0];p+=tr[1];st=tr[2]
m=sys.argv[1];mir=int(sys.argv[2]);f=sys.argv[3];t=parse(m,mir)
mode=sys.argv[4]
if mode=='even':trace(t,FP([9],7,2,4,[5,6,4,2],f),int(sys.argv[5]))
if mode=='odd':trace(t,FP([9],7,3,4,[5,6,4,2],f),int(sys.argv[5]))
if mode=='ls2':trace(t,LSc(2,[5,6,4,2],f),int(sys.argv[5]))
if mode=='ev1':trace(t,FP([9],8,1,5,[5,6,4,2],f),int(sys.argv[5]))
if mode=='top1':trace(t,FP([],8,1,5,[5,6,4,2],f),int(sys.argv[5]))
if mode=='top1odd':trace(t,FP([],9,1,5,[5,6,4,2],f),int(sys.argv[5]))
