# Raw TM check of the halting stretch formula: from A(a,b,3a+4), steps to the configuration with no transition = drain(a,b)+8(2a+b)+33.
import sys
M="1RB---_0RC0RD_1LD1RB_0LE0LC_1RA0LF_1LD1LE"
T={}
for i,s in enumerate(M.split('_')):
    for j in range(2):
        x=s[3*j:3*j+3]; T[(chr(65+i),j)]=None if x[2]=='-' else (int(x[0]),1 if x[1]=='R' else -1,x[2])
def run(a,b,c):
    tape={};pos=0
    l=[1]*a+[1,0]*b
    for i,x in enumerate(reversed(l)): tape[-1-i]=x
    for i in range(c): tape[i]=1
    q='C';n=0
    while True:
        t=T[(q,tape.get(pos,0))]
        if t is None: return n,sum(tape.values())
        tape[pos]=t[0];pos+=t[1];q=t[2];n+=1
bad=0;cnt=0
for a in range(0,40):
    for b in (1,2):
        n,ones=run(a,b,3*a+4); B=2*a+b
        f=4*b*a+4*a*(a-1)+9*a+8*B+33
        cnt+=1
        if n!=f: bad+=1; print('MISMATCH',a,b,n,f)
        if a<3: print('a',a,'b',b,'steps',n,'ones',ones)
print('halting stretch checked',cnt,'cases, mismatches',bad)
