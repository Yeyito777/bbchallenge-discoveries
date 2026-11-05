# closure_search.py TM TAPE K M B N C [Q] [--dump FILE]: Python implementation of the anchored run-language closure, separate from
# runlang.c and the Rust verifier. K runs of B-cell blocks, lengths mod M, parity of the count of symbols in mask C.
# Prints CLOSED and the number of abstract configurations, or the path to an abstract halt.
# Optionally dumps the automaton, edge sets and closed set for check_closed.py.
import sys,re
c,tape,K,M,B=sys.argv[1],sys.argv[2],int(sys.argv[3]),int(sys.argv[4]),int(sys.argv[5])
r=[c[i:i+3] for i in (0,3,6,9,13,16,19,22)]
tr={}
for i,x in enumerate(r):
    if x[0]!='-': tr[(i//4,i%4)]=(int(x[0]),1 if x[1]=='R' else -1,ord(x[2])-65)
m=re.match(r'(\d*)\[(\d)\](\d*)',tape); L=[int(x) for x in m[1]];h0=int(m[2]);R=[int(x) for x in m[3]][::-1]
C=int(sys.argv[7]) if len(sys.argv)>7 else 0
Q=int(sys.argv[8]) if len(sys.argv)>8 else 2
OFF=-1
if '--off' in sys.argv: OFF=int(sys.argv[sys.argv.index('--off')+1])
TAIL=(tuple([('T',0)]*K),(),0)
ZERO=tuple([0]*B)
def tailp(p): return (tuple([('T',0)]*K),tuple([0]*p),0)
def step(q,a):
    runs,part,cn=q
    if OFF<0 and q==TAIL and a==0: return q
    if C>>a&1: cn=(cn+1)%Q
    part=part+(a,)
    if len(part)<B: return (runs,part,cn)
    l=runs[-1]
    if OFF>=0 and l[0]=='T' and part==ZERO: return (runs,(),cn)
    if l[0]==part: return (runs[:-1]+((part,l[1]%M+1),),(),cn)
    return (runs[1:]+((part,1),),(),cn)
EL={};ER={};intoL={};intoR={}
def add(E,into,q,a):
    t=step(q,a)
    if (q,a) in E: return False
    E[(q,a)]=1; into.setdefault(t,[]).append((q,a)); return True
for p in (range(B) if OFF>=0 else [0]):
    add(EL,intoL,tailp(p),0); add(ER,intoR,tailp(p),0)
q=TAIL if OFF<0 else tailp((-len(L)-OFF)%B)
for a in L: add(EL,intoL,q,a); q=step(q,a)
ql=q; q=TAIL if OFF<0 else tailp((OFF+B-1-len(R))%B)
for a in R: add(ER,intoR,q,a); q=step(q,a)
qr=q
start=(ql,0,h0,qr); seen={start:None}; lst=[start]; ch=True
def fL(q): return ''
def fL_(q): return ' '.join(('T' if a=='T' else ''.join(map(str,a)))+(f"^{n}" if n else '') for a,n in q[0] if a!='T')+' +'+''.join(map(str,q[1]))+' c%d'%q[2]
def fR(q): return ''
def fR_(q): return 'c%d '%q[2]+''.join(map(str,q[1][::-1]))+'+ '+' '.join(('T' if a=='T' else ''.join(map(str,a[::-1])))+(f"^{n}" if n else '') for a,n in q[0][::-1] if a!='T')
N=int(sys.argv[6]) if len(sys.argv)>6 else 25
while ch:
    ch=False
    for x in list(lst):
        ql,s,cc,qr=x
        if (s,cc) not in tr:
            path=[];y=x
            while y is not None: path.append(y);y=seen[y]
            print('ABSTRACT HALT, path',len(path),'configs',len(seen))
            for y in path[::-1][-N:]: print('  ',fL(y[0]),' [','AB'[y[1]],y[2],'] ',fR(y[3]))
            sys.exit()
        w,d,ns=tr[(s,cc)]
        if d>0:
            if add(EL,intoL,ql,w): ch=True
            nq=step(ql,w)
            for (fr,a) in list(intoR.get(qr,[])):
                y=(nq,ns,a,fr)
                if y not in seen: seen[y]=x;lst.append(y);ch=True
        else:
            if add(ER,intoR,qr,w): ch=True
            nq=step(qr,w)
            for (fr,a) in list(intoL.get(ql,[])):
                y=(fr,ns,a,nq)
                if y not in seen: seen[y]=x;lst.append(y);ch=True
print('CLOSED',len(seen))
if '--dump' in sys.argv:
    f=open(sys.argv[sys.argv.index('--dump')+1],'w'); ids={}
    def I(q):
        if q not in ids: ids[q]=len(ids)
        return ids[q]
    tails=[tailp(p) for p in (range(B) if OFF>=0 else [0])]
    for t_ in tails: I(t_)
    q0l=TAIL if OFF<0 else tailp((-len(L)-OFF)%B); q0r=TAIL if OFF<0 else tailp((OFF+B-1-len(R))%B)
    f.write(f"tape {tape}\nmachine {c}\ntails {' '.join(str(I(t_)) for t_ in tails)}\nstartL {I(q0l)}\nstartR {I(q0r)}\n")
    for (q,a) in list(EL): f.write(f"EL {I(q)} {a} {I(step(q,a))}\n")
    for (q,a) in list(ER): f.write(f"ER {I(q)} {a} {I(step(q,a))}\n")
    for (a,s_,cc,b) in seen: f.write(f"C {I(a)} {s_} {cc} {I(b)}\n")
    f.close()
