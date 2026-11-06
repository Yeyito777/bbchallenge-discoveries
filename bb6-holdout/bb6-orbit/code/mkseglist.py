#!/usr/bin/env python3
# Merged states to an ordered segment list. Line: id a0 B a1 Y. First segment starts at A(6,1), last runs to the halt candidate.
import sys
st=set()
for f in sys.argv[3:]:
    for l in open(f):
        p=l.split()
        if len(p)>=3 and p[1] in('6','22'): st.add((int(p[2]),int(p[1])))
st=sorted(st)
Bstar=int(sys.argv[1]); a_star=int(sys.argv[2])
st=[(b,a) for b,a in st if b<Bstar]
chain=[(1,6)]+st+[(Bstar+1,a_star)]
for i in range(len(chain)-1):
    print(i,chain[i][1],chain[i][0],chain[i+1][1],chain[i+1][0])
