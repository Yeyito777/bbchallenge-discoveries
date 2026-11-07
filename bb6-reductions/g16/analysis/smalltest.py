import random,sys
from lsim import run
from listmap import step
random.seed(3)
# which first-run values at the top cause trouble? states (a1,a2=a1+3 as produced by the odd case, entries) with tail 6,4,1
res={}
for a1 in range(1,12):
    for tr in range(30):
        ent=[random.randint(5,40) for _ in range(random.randint(1,3))]
        lst=[a1,a1+3]+ent+[6,4,1]
        ev=run(lst,nev=4000,maxT=2000000)
        h=[e for e in ev if e[0]=='HALT']
        res.setdefault(a1,[0,0,None])
        res[a1][1]+=1
        if h:
            res[a1][0]+=1
            if res[a1][2] is None:res[a1][2]=(lst,h[0][1],h[0][2][:60])
for k in sorted(res):print(k,res[k])
