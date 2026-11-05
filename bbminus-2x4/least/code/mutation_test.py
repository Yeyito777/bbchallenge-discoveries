import random,subprocess,sys
R,led,tape,th=sys.argv[1:5]
L=open(led).read().split('\n'); L=[x for x in L if x]
random.seed(1)
by={k:[i for i,x in enumerate(L) if x.startswith(k+' ')] for k in 'HCPW'}
def run(lines):
    open('/tmp/least/m.txt','w').write('\n'.join(lines)+'\n')
    p=subprocess.run([R,tape,th,'/tmp/least/m.txt'],capture_output=True,text=True,env={'CHECK_THREADS':'2'})
    return p.returncode,[l for l in p.stdout.split('\n') if 'VERDICT' in l], p.stderr[:120]
def show(name,lines): print(name,run(lines))
for k in range(3):
    i=random.choice(by['H']);m=list(L);p=m[i].split();p[1]=str(int(p[1])+1);m[i]=' '.join(p);show('H+1',m)
    i=random.choice(by['C']);m=list(L);p=m[i].split();p[2]=str(int(p[2])+1);m[i]=' '.join(p);show('C period+1',m)
    i=random.choice(by['C']);m=list(L);p=m[i].split();p[0]='W';m[i]=f"P {p[4]} 1 0 0 0";show('C->weak P (may be valid)',m)
    i=random.choice(by['C']);m=list(L);del m[i];show('missing C',m)
    i=random.choice(by['H']);m=list(L);p=m[i].split();m[i]=f"P {p[2]} 2 0 0 0";show('halter claimed CPS',m)
    i=random.choice(by['H']);m=list(L);p=m[i].split();m[i]=f"W {p[2]} 2 2 0 0";show('halter claimed RepWL',m)
    i=random.choice(by['H']);m=list(L);p=m[i].split();m[i]=f"C 4 4 0 {p[2]}";show('halter claimed cycler',m)
m=list(L);m.append("H 5 1RB---------_------------");show('extra record',m)
