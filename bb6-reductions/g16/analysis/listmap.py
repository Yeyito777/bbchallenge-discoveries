#!/usr/bin/env python3
# The list map of the 16-machine group. State: stack a[0..m-1] above the fixed tail (8,6,3). One step:
#   r = a[m-1]+2; for i=m-1 down: if r odd: a[i-1]+=(r+3)/2; a[i]=(r+9)/2; stop. If r even: a[i]=r/2+2; r=a[i-1]+r/2-2; continue.
#   top: when i=0 is reached with r even for a[1] level: P=a[0]+r_1/2 and first-run stage.
import sys
def step(a,log=None):
    m=len(a)
    r=a[m-1]+2
    i=m-1
    while True:
        if r%2==1:
            if i==0:
                raise Exception('odd at top r=%d list %s'%(r,a[:4]))
            a[i-1]+=(r+3)//2
            a[i]=(r+9)//2
            return None
        a[i]=r//2+2
        if i==0:
            raise Exception('even at top')
        if i==1:
            P=a[0]+r//2
            return top(a,P,log)
        r=a[i-1]+r//2-2
        i-=1
def top(a,P,log):
    # a[1:] are entries; first run replaced
    P0=P
    ent=[]
    while P%2==0:
        ent.append(P//2+1)
        P=P//2-1
    new=[(P+1)//2,(P+1)//2+3]+ent[::-1]+a[1:]
    a[:]=new
    return P0
if __name__=='__main__':
    # compare with gensim event stream (R A events ending 8 6 3 preceding... ) from a file of unary lists
    pass
