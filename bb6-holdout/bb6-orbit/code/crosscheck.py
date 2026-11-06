#!/usr/bin/env python3
"""Sampled check of seg against seg2.py. Picks a stretch between two consecutive sample points of a finished segment, runs seg on that stretch
for exact totals, then seg2.py in G mode (applications and steps must match) and J mode (Lean map must reach the same end). Appends to crosscheck.log.
usage: crosscheck.py seed count"""
import sys,os,random,subprocess,glob,re,time
random.seed(int(sys.argv[1])); count=int(sys.argv[2])
done=0
while done<count:
    fs=[f for f in glob.glob('samples/seg_*.txt') if os.path.getsize(f)>0 and os.path.exists(f.replace('samples/','results/'))]
    if not fs: time.sleep(300); continue
    fs.sort(key=lambda f:int(re.search(r'(\d+)\.txt',f)[1]))
    f=random.choice(fs); L=sorted(set(open(f).read().strip().split('\n')),key=lambda x:int(x.split()[2]))
    if len(L)<2: time.sleep(30); continue
    i=random.randrange(len(L)-1); n0,a0,b0=L[i].split(); n1,a1,b1=L[i+1].split()
    out='/tmp/xc_%d.txt'%os.getpid(); fine='/tmp/xcf_%d.txt'%os.getpid()
    for p in (out,fine,out+'.ck'):
        if os.path.exists(p): os.remove(p)
    # narrow the 2^24-phase interval to a random 2^18-phase stretch so the Python side finishes in minutes
    subprocess.run(['./seg_x',a0,b0,a1,b1,out,fine],env=dict(os.environ,SEG_SAMPLE_MASK=str(2**18-1)))
    F=open(fine).read().strip().split('\n'); os.remove(out)
    j_=random.randrange(len(F)-1); n0,a0,b0=F[j_].split(); n1,a1,b1=F[j_+1].split()
    t0=time.time(); r=subprocess.run(['./seg_x',a0,b0,a1,b1,out]); h=open(out).read().split('\n')
    m=re.search(r' ok (\d) apps (\d+) phases (\d+)',h[0]); six=int(h[1].split()[1])
    steps6=2*(int(a1)**2-int(a0)**2)+six
    ok_seg=m[1]=='1' and int(m[2])==int(n1)-int(n0)
    g=subprocess.run(['python3','seg2.py','G',a0,b0,a1,b1],capture_output=True,text=True).stdout
    mg=re.search(r'G ok .* apps (\d+) steps2 (\d+)',g)
    ok_g=bool(mg) and int(mg[1])==int(m[2]) and 3*int(mg[2])==steps6
    j=subprocess.run(['python3','seg2.py','J',a0,b0,a1,b1],capture_output=True,text=True).stdout
    ok_j=' ok ' in j
    with open('crosscheck.log','a') as o:
        o.write(f"{f} i={i} a0={a0} B={b0} a1={a1} Y={b1} apps={m[2]} phases={m[3]} seg_links={ok_seg} G={ok_g} J={ok_j} secs={time.time()-t0:.0f}\n")
    done+=1
