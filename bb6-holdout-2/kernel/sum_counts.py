#!/usr/bin/env python3
# Adds up the per-job raw-step counts. Needs C and Rust counts for every job and requires them equal.
# Total from blank to the halting configuration = 2 (blank to A(0,1,0)) + 12 (first rule) + sum of jobs (the last includes the
# halting stretch). busycoq's halts_in counts the same way: steps to a configuration with no transition.
import os,sys
K=sys.argv[1] if len(sys.argv)>1 else '.'
jobs=[l.split()[0] for l in open(f'{K}/jobs.txt')]
tot=2+12;bad=0
for j in jobs:
    c=open(f'{K}/counts/{j}.c.txt').read().split(); r=open(f'{K}/counts/{j}.r.txt').read().split()
    if c!=r: bad+=1; print('DIFF',j,c,r)
    tot+=int(c[3])
print('jobs',len(jobs),'C/Rust differences',bad)
print('raw steps from blank to the halting configuration (halting transition not counted):',tot)
print('counting the halting transition:',tot+1)
