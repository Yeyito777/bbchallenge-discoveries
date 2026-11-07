exec(open('ruletest.py').read().split("random.seed(1)")[0])
random.seed(2)
def rr_rand(n=None,mn=3):
    return [random.randint(mn,12) for _ in range(random.randint(0,3) if n is None else n)]
tail=[6,4,2]
for line in open('machines.txt'):
    m,mir,c,a=line.split();mir=int(mir);c=int(c)
    t=parse(m,mir)
    f=[s for s in 'ABCDEF' if t[(s,1)] and t[(s,1)][0]==1 and t[(s,1)][1]==-1 and t[(s,1)][2]==s][0]
    out={}
    for name in ['round','even','odd','top','ls','lssmall','halt','tail','start']:
        ok=0;tot=0;bad=[]
        for it in range(25 if name!='start' else 1):
            ll=rr_rand(random.randint(0,3));p=random.randint(4,14);y=random.randint(1,10);rr=rr_rand()
            tgs=[]
            if name=='round':
                r=random.randint(1,10);tgs=[(FP(ll,p,r+2,y,rr+tail,f),FP(ll,p+1,r,y+1,rr+tail,f))]
            elif name=='even':
                q=random.randint(1,12)
                if c==1:tgs=[(FP([q]+ll,p,2,y,rr+tail,f),FP(ll,q+1,p-2,2,[y+1]+rr+tail,f))]
                else:tgs=[(FP([q]+ll,p,1,y,rr+tail,f),FP(ll,q,p,1,[y]+rr+tail,f))]
            elif name=='odd':
                if c==1:tgs=[(FP(ll,p,3,y,rr+tail,f),Cf(rr[::-1]+[y+4,p+2]+ll,c,a))]
                else:tgs=[(FP(ll,p,2,y,rr+tail,f),Cf(rr[::-1]+[y+3,p+1]+ll,c,a))]
            elif name=='top':
                if c==1:tgs=[(FP([],p,2,y,rr+tail,f),LSc(p,[y+1]+rr+tail,f))]
                else:tgs=[(FP([],p,1,y,rr+tail,f),LSc(p,[y]+rr+tail,f))]
            elif name=='ls':
                P=random.randint(4,14);tgs=[(LSc(P,rr+tail,f),FP([],1,P-2,2,rr+tail,f))]
            elif name=='lssmall':
                if c==1:tgs=[(LSc(1,rr+tail,f),Cf(rr[::-1]+[4,1],c,a)),(LSc(3,rr+tail,f),Cf(rr[::-1]+[5,2],c,a))]
                else:tgs=[(LSc(2,rr+tail,f),Cf(rr[::-1]+[4,1],c,a))]
            elif name=='halt':
                tgs=[(LSc(2 if c==1 else 3,rr+tail,f),None)]
            elif name=='tail':
                x=random.randint(3,12);q=random.randint(1,12)
                if c==1:tgs=[(Cf([x,q]+ll,c,a),FP(ll,q+1,x+2,2,tail,f))]
                else:tgs=[(Cf([x,q]+ll,c,a),FP(ll,q,x+5,1,tail,f))]
            elif name=='start':
                tgs=[(('0',0,'A'),Cf([9,10],c,a))]
            for cfg,tg in tgs:
                r_=run(t,cfg,tg);tot+=1
                if r_[0]==('HALT' if tg is None else 'OK'):ok+=1
                else:bad.append((r_,cfg[0][:40]))
        out[name]=(ok,tot,bad[:1])
    print(m,mir,a,f,c,{k:'%d/%d'%(v[0],v[1]) for k,v in out.items()},[(k,v[2]) for k,v in out.items() if v[0]<v[1]],flush=True)
