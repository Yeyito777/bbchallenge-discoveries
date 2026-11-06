#!/usr/bin/env python3
"""Write one Rocq file per chunk: the extracted checker's result for that chunk, restated as a kernel-checked lemma.
usage: mkspot.py CHUNKS OUTDIR SEED COUNT RESULT_FILES...   The halting chunk is always included."""
import sys,random
chunks=[l.split() for l in open(sys.argv[1])]; out=sys.argv[2]; rng=random.Random(int(sys.argv[3])); cnt=int(sys.argv[4])
res={}
for f in sys.argv[5:]:
    for l in open(f):
        x=l.split()
        if len(x)>=6 and x[2] in('OK','HALT'): res[x[0]]=x
P=2**63
W=lambda n:f'(mkW {n>>63} {n%P})'
V=lambda n:'(mkV '+' '.join(str((n>>(63*i))%P) for i in range(5))+')'
Z=lambda s:'true' if s=='22' else 'false'
HEAD='From Coq Require Import Uint63.\nFrom BB6 Require Import Num Vec Check.\n'
pick=rng.sample(chunks[:-1],cnt)+[chunks[-1]]
for c in pick:
    r=res[c[0]]
    if c[4]=='H':
        body=f'check_final {Z(c[2])} {W(int(c[3]))} = Some ({W(int(r[3]))}, {W(int(r[4]))}, {V(int(r[5]))})'
        val=f'Some ({W(int(r[3]))}, {W(int(r[4]))}, {V(int(r[5]))})'
    else:
        body=f'check_seg {Z(c[2])} {W(int(c[3]))} {Z(c[4])} {W(int(c[5]))} = Some ({W(int(r[3]))}, {V(int(r[4]))})'
        val=f'Some ({W(int(r[3]))}, {V(int(r[4]))})'
    open(f'{out}/Spot{c[0]}.v','w').write(HEAD+f'Lemma chunk : {body}.\nProof. native_cast_no_check (eq_refl ({val})). Time Qed.\n')
    print(c[0],c[1],c[2],c[3])
