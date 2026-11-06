#!/usr/bin/env python3
# Second, independent rule-map walk (the G(c,b) form of the map from the wiki, in Python bigints).
import sys
def step(c,b):
    if b==0: return None
    if b>=2*c+9: return (2*c+6,b-2*c-9)
    if b==1: return (0,2*c+13) if c%2==0 else (8,2*c+4)
    if b==3: return (0,2*c+19) if c%2==0 else (c+4,2)
    if b%2==0: return (0,2*c+b+13) if (c+b//2)%2==0 else (8,2*c+b+4)
    if (c+(b-1)//2)%2==0: return (c-(b-1)//2+5,2*b-4)
    if b==2*c+7: return (0,2*c+b+8)
    return (c-(b-1)//2+9,2*b-8)
c,b=0,1
want={1241263,int(sys.argv[2]) if len(sys.argv)>2 else -1}
N=int(sys.argv[1]); n=0
while n<=N:
    if n in want: print("n",n,"A",2*c+6,b,"d",b-(2*c+6)-3)
    r=step(c,b)
    if r is None: print("HALT",n,2*c+6,b); break
    c,b=r; n+=1
print("end",n,2*c+6,b)
