// Exact raw-step total over c273 map steps, faster form of stepcount273.c (same per-rule counts, see steps273.py).
// The r=2 case with a0=0 is the same formula as a0>=1, so the tail is a0*(4B+c1[r]) + 6B + c0[r] with c1={1,5,9}, c0={6,14,24}.
// usage: count273 a b c N [halt]   N map steps from (a,b,c); with "halt", N must end on the halting state and the halting
// stretch drain(a,b)+8(2a+b)+33 is added. Prints: end state, raw-step sum (decimal, 256-bit).
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef unsigned __int128 u128; typedef uint64_t u64;
typedef struct { u128 lo, hi; } u256;
static inline void add(u256*s,u128 x){ u128 o=s->lo; s->lo+=x; s->hi+=(s->lo<o); }
static void pr(u256 s){ char buf[100]; int n=0; u64 w[4]={(u64)s.lo,(u64)(s.lo>>64),(u64)s.hi,(u64)(s.hi>>64)}; int z;
  do{ u128 r=0; for(int i=3;i>=0;i--){ u128 cur=(r<<64)|w[i]; w[i]=(u64)(cur/10); r=cur%10; } buf[n++]='0'+(int)r; z=!(w[0]|w[1]|w[2]|w[3]); }while(!z);
  while(n)putchar(buf[--n]); }
int main(int ac,char**av){
  u64 a=strtoull(av[1],0,10),b=strtoull(av[2],0,10),c=strtoull(av[3],0,10),N=strtoull(av[4],0,10);
  int halt=ac>5&&!strcmp(av[5],"halt");
  static const u64 c1[3]={1,5,9},c0[3]={6,14,24};
  u256 S={0,0};
  for(u64 i=0;i<N;i++){
    if(c<3*a+3){
      u64 k=c/3,r=c-3*k,a0=a-k,B=b+2*k;
      if(r==0&&B==1){ fprintf(stderr,"A(a,1,0) at step %llu: the start rule is outside the formulas\n",(unsigned long long)i); return 2; }
      add(&S,(u128)k*(4*b+4*k+5)+(u128)a0*(4*B+c1[r])+6*(u128)B+c0[r]);
      u64 na=4*k+2*b+2*r+1; c=a-k+1; a=na; b=1;
    } else {
      if(c<3*a+5){ fprintf(stderr,"halting state reached early at step %llu\n",(unsigned long long)i); return 3; }
      add(&S,(u128)a*(4*b+4*a+5)+12*(u128)a+6*b+25);
      u64 na=4*a+2*b+4; c=c-3*a-5; a=na; b=2;
    }
  }
  if(halt){ if(c!=3*a+4){fprintf(stderr,"not at a c=3a+4 halting state\n");return 4;} add(&S,(u128)a*(4*b+4*a+5)+8*(2*(u128)a+b)+33); }
  printf("%llu %llu %llu ",(unsigned long long)a,(unsigned long long)b,(unsigned long long)c); pr(S); printf("\n");
  return 0;
}
