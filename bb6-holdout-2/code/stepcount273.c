// Exact raw-step total for c273 map steps, per rule from the counts in rocq/Rules273.v (see steps273.py for the derivation).
// usage: stepcount273 a b c N      runs N map steps from (a,b,c) (or until the halt rule), prints end state and the raw-step sum
// as an exact decimal (256-bit accumulator). With N larger than the distance to the halt, adds the halting stretch and says so.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef unsigned __int128 u128; typedef uint64_t u64;
typedef struct { u128 lo, hi; } u256;
static inline void add(u256*s,u128 x){ u128 o=s->lo; s->lo+=x; if(s->lo<o) s->hi++; }
static void pr(u256 s){ // decimal
  char buf[100]; int n=0; u64 w[4]={(u64)s.lo,(u64)(s.lo>>64),(u64)s.hi,(u64)(s.hi>>64)};
  int z; do{ u128 r=0; for(int i=3;i>=0;i--){ u128 cur=(r<<64)|w[i]; w[i]=(u64)(cur/10); r=cur%10; } buf[n++]='0'+(int)r; z=!(w[0]|w[1]|w[2]|w[3]); }while(!z);
  while(n)putchar(buf[--n]);
}
static inline u128 drain(u128 k,u128 b){ return 4*b*k+4*k*(k-1)+9*k; }
int main(int ac,char**av){
  u64 a=strtoull(av[1],0,10),b=strtoull(av[2],0,10),c=strtoull(av[3],0,10),N=strtoull(av[4],0,10);
  u256 S={0,0}; u64 i; int halted=0;
  for(i=0;i<N;i++){
    int64_t e=(int64_t)c-3*(int64_t)a-3;
    if(e<0){
      u64 k=c/3,r=c%3,a0=a-k; u128 B=(u128)b+2*k, t;
      if(r==0){ if(B==1){ if(a0!=0){fprintf(stderr,"unreachable A(a,1,0) with a>0\n");return 2;} t=12-drain(k,b); /* A(0,1,0)->A(3,1,1): 12 raw steps, k=0 */ }
               else t=(u128)a0*(4*B+1)+6*B+6; }
      else if(r==1) t=2+(u128)a0*(4*B+5)+6*B+12;
      else if(a0==0) t=6*B+24;
      else t=(4*B+15)+(u128)(a0-1)*(4*B+9)+6*B+18;
      add(&S,drain(k,b)+t);
      u64 na=4*k+2*b+2*r+1, nc=a-k+1; a=na; b=1; c=nc;
    } else if(e<=1){
      if(e==0){fprintf(stderr,"halt rule c=3a+3: stretch formula not derived here\n");return 3;}
      u128 B=2*(u128)a+b; add(&S,drain(a,b)+8*B+33); halted=1; break;
    } else {
      add(&S,drain(a,b)+6*(2*(u128)a+b)+25);
      u64 na=4*a+2*b+4, nc=(u64)e-2; a=na; b=2; c=nc;
    }
  }
  printf("%s %llu map steps, end state %llu %llu %llu, raw steps ",halted?"HALTED after":"ran",(unsigned long long)i,(unsigned long long)a,(unsigned long long)b,(unsigned long long)c); pr(S); printf("\n");
  return 0;
}
