import sys
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
def comp(x):
    out=[];i=0
    while i<len(x):
        j=i
        while j<len(x) and x[j]==x[i]:j+=1
        n=j-i
        out.append(str(n) if x[i]=='1' else ('.' if n==1 else 'z%d'%n))
        i=j
    return ' '.join(out)
def show(tape,lo,hi,p,s):
    a=''.join(str(tape.get(i,0)) for i in range(lo,p));b=str(tape.get(p,0));c=''.join(str(tape.get(i,0)) for i in range(p+1,hi+1))
    return comp(a)+' <%s:%s> '%(s,b)+comp(c)
m,mir=sys.argv[1],int(sys.argv[2]);T0=int(sys.argv[3]);n=int(sys.argv[4]);q0=int(sys.argv[5]) if len(sys.argv)>5 else 2
t=parse(m,mir);tape={};p=0;s='A';T=0;lo=hi=0;d=0;ext=0;c=0
while c<n:
    b=tape.get(p,0);tr=t[(s,b)]
    if tr is None:print('HALT',T);break
    tape[p]=tr[0];p+=tr[1];s=tr[2];T+=1
    lo=min(lo,p);hi=max(hi,p)
    rev=False
    if d>=0 and p>=ext:ext=p;d=1
    elif d<=0 and p<=ext:ext=p;d=-1
    elif d==1 and ext-p>q0:rev=True;d=-1;ext=p
    elif d==-1 and p-ext>q0:rev=True;d=1;ext=p
    if rev and T>T0:
        print(T,show(tape,lo,hi,p,s)[:110]);c+=1
