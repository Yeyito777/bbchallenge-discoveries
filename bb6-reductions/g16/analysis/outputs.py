# process outputs per period by level (how many carries leave level j per period of level j).
per=[4,8,32,64,128,512,2048,4096,8192,32768,131072,655360]
a=[9,10]
N=1<<21
ev=[[] for _ in per]
def step(a,t):
    m=len(a); r=a[0]+2; i=0
    while True:
        if r&1:
            a[i+1]+=(r+3)//2; a[i]=(r+9)//2; return
        a[i]=r//2+2
        if i<len(ev): ev[i].append(t)
        if i==m-2:
            P=a[m-1]+r//2; a.pop()
            while P%2==0:
                a.append(P//2+1); P=P//2-1
            a.append((P+1)//2+3); a.append((P+1)//2); return
        r=a[i+1]+r//2-2; i+=1
for t in range(N): step(a,t)
for j,p in enumerate(per):
    c=sum(1 for x in ev[j] if N-p<=x<N)
    print('level',j,'period',p,'carries per period',c,'carry rate %.5f'%(c/p),'2^-(j+1)=%.5f'%(2.0**-(j+1)))
