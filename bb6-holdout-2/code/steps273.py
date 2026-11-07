# Raw steps per c273 map rule, derived from the step counts in rocq/Rules273.v (R_drain 4b+9 per drain at current b, R_c0, R_c1,
# R_c2_step, R_c2_zero, R_reset, and the stepping in R_halt4). Checked here against the raw-TM log of the first 6,998 rules from blank.
# usage: python3 -I steps273.py raw_c273.txt.gz
import gzip,sys
def drain(k,b): return 4*b*k+4*k*(k-1)+9*k               # k applications of R_drain, b grows by 2 each
def rule(a,b,c):
    e=c-3*a-3
    if e<0:
        k,r=divmod(c,3); a0=a-k; B=b+2*k
        if r==0:
            if B==1: return None                            # only A(0,1,0): handled by start_steps
            t=a0*(4*B+1)+6*B+6
        elif r==1: t=2+a0*(4*B+5)+6*B+12
        elif a0==0: t=6*B+24
        else: t=(4*B+15)+(a0-1)*(4*B+9)+6*B+18
        return drain(k,b)+t,(4*k+2*b+2*r+1,1,a-k+1)
    if e<=1: return None
    return drain(a,b)+6*(2*a+b)+25,(4*a+2*b+4,2,e-2)
def halt_steps(a,b,c):
    # c=3a+4: a drains, then R_halt4 from Lf 0 (2a+b): 5 + 2B + 3 + 4(B+2) + 8 + 2(B+4) + 1 = 8B+33 steps to the
    # configuration with no transition (A reading 1); the halting transition itself is not counted.
    assert c==3*a+4
    B=2*a+b
    return drain(a,b)+8*B+33
START_STEPS=2     # blank -> A(0,1,0)
if __name__=='__main__':
    rows=[tuple(map(int,l.split())) for l in gzip.open(sys.argv[1],'rt')]
    s=(0,1,0); bad=0
    # A(0,1,0) -> A(3,1,1) is the one rule outside the formulas; take its cost from the log and check the rest
    for i in range(1,len(rows)-1):
        if i==1: s=(3,1,1)
        t,ns=rule(*s)
        if rows[i][1]+t!=rows[i+1][1]: bad+=1
        s=ns
    print('rules checked',len(rows)-2,'mismatches',bad,'first rule cost from log',rows[1][1]-rows[0][1],'start at raw step',rows[0][1])
