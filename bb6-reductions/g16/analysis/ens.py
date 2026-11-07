# ensemble: random stacks, first top event; how often is P+2 a power of two, compared to chance?
import random,collections,math
random.seed(5)
def run(a):
    n=0
    while True:
        n+=1
        if n>20000:return None,n
        m=len(a); r=a[0]+2; i=0
        while True:
            if r&1:
                a[i+1]+=(r+3)//2; a[i]=(r+9)//2; break
            a[i]=r//2+2
            if i==m-2:
                return a[m-1]+r//2,n
            r=a[i+1]+r//2-2; i+=1
trap=0;hits=collections.Counter();tot=collections.Counter();exp=collections.Counter();ex={}
for it in range(40000):
    L=random.randint(2,7)
    a=[random.randint(3,120) for _ in range(L)]
    a0=a[:]
    P,n=run(a)
    if P is None:
        trap=trap+1;continue
    Q=P+2
    b=int(math.log2(Q))
    tot[b]+=1
    if Q&(Q-1)==0:
        hits[b]+=1; ex.setdefault(b,(a0,n))
print('no top event in 20000 steps',trap)
for b in sorted(tot):
    print(b,tot[b],'hits',hits[b],'chance ~ %.1f'%(tot[b]/(2**b)),ex.get(b))
