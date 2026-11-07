# level sequences of the list map: find eventual period of each level counted from the right (a[0] = just above the tail).
a=[9,10]  # reversed
def step(a):
    m=len(a); r=a[0]+2; i=0
    while True:
        if r&1:
            a[i+1]+=(r+3)//2; a[i]=(r+9)//2; return
        a[i]=r//2+2
        if i==m-2:
            P=a[m-1]+r//2; a.pop()
            while P%2==0:
                a.append(P//2+1); P=P//2-1
            a.append((P+1)//2+3); a.append((P+1)//2); return
        r=a[i+1]+r//2-2; i+=1
N=1<<22
L=16
seq=[[] for _ in range(L)]
for t in range(N):
    step(a)
    for j in range(L):
        seq[j].append(a[j] if j<len(a) else -1)
def period(s):
    # eventual period: search smallest p such that the last half is p-periodic
    n=len(s);tail=s[n//2:]
    for p in range(1,n//4):
        if all(tail[i]==tail[i+p] for i in range(0,min(len(tail)-p,4*p+1000))):
            if all(tail[i]==tail[i+p] for i in range(len(tail)-p)):
                # find start of periodicity
                st=n//2
                while st>0 and s[st-1]==s[st-1+p]:st-=1
                return p,st
    return None,None
for j in range(L):
    p,st=period(seq[j])
    print('level',j,'range',min(seq[j][N//2:]),max(seq[j][N//2:]),'period',p,'from step',st)
