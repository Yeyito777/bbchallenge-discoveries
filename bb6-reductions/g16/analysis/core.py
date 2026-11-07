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
out={}
for l in open('g16fam2.txt'):
    m,mir,c,st=l.split();mir=int(mir)
    t=parse(m,mir)
    tape={};p=0;s='A';T=0;used={}
    start=None
    # raw run; collect transitions used after T0, and the core table relabelled by first use from the family state at a right-edge event
    T0=200000;hi=0
    seq=[]
    while T<400000:
        b=tape.get(p,0);tr=t[(s,b)]
        if tr is None:break
        if T>T0:
            used[(s,b)]=tr
        tape[p]=tr[0];p+=tr[1];s=tr[2];T+=1
    unusedhalt=[k for k,v in t.items() if v is None]
    # canonical relabel: BFS from family state st
    names={st:'a'};order=[st];i=0;canon=[]
    for q in order:
        for b in (0,1):
            if (q,b) in used:
                w,d,n=used[(q,b)]
                if n not in names:
                    names[n]=chr(97+len(names));order.append(n)
    tab=[]
    for q in order:
        row=[]
        for b in (0,1):
            if (q,b) in used:
                w,d,n=used[(q,b)];row.append('%d%s%s'%(w,'R' if d>0 else 'L',names[n]))
            elif t[(q,b)] is None:row.append('HALT')
            else:row.append('..')
        tab.append(names[q]+':'+','.join(row))
    key=' '.join(tab)
    out.setdefault(key,[]).append((m,mir,c,st,len(used),''.join(order),[k for k in t if k not in used and t[k] is not None]))
for k,v in out.items():
    print(k)
    for x in v:print('   ',x)
