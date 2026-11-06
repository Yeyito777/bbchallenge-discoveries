#!/usr/bin/env python3
# Shows the last sweep before the halt, from the reset state B*, and the residues that allow it.
B=2166395068749415481073467106; a,b=22,B
def st(a,b):
    if b>a+3: return 'D',2*a+6,b-a-3
    if b==1: return ('p',6,a+7) if a%4==2 else ('q',22,a-2)
    if b==3: return ('r',6,a+13) if a%4==2 else ('s',a+8,2)
    if b%2:
        if b==a+1: return 't',6,a+b+2
        return ('u',a-b+11,2*b-4) if ((a-b+5)//2)%2 else ('v',a-b+19,2*b-8)
    return ('w',6,a+b+7) if ((a-b)//2)%2 else ('x',22,a+b-2)
w=''; ga,gb=0,1
while b!=a+3:
    c,na,nb=st(a,b); w+=c
    ga,gb={'D':(2*ga,gb-ga),'u':(ga-gb,2*gb),'v':(ga-gb,2*gb)}[c]
    a,b=na,nb
print('word',w,'letters',len(w)); print('halt form A(a,a+3) a =',a,'b =',b)
print('b-a-3 slope in B =',gb-ga,'B mod 4 =',B%4,'ones at halt a+9 =',a+9,'steps of last rule a^2+7a+41 =',a*a+7*a+41)
