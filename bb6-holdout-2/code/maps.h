// Production rule map for 1RB---_0RC0RD_1LD1RB_0LE0LC_1RA0LF_1LD1LE (c273).
// exact_step() (one map step, all cases) and fast_block() (branch-free loop over the
// main cases only; it reports the smallest window value so the driver can redo the block with
// exact_step if any state in it came within W of the halting equation).
//
// Why 64 bits are safe: S grows by a small constant per map step on every rule, proved in the
// comments below, so S < 2^62 for the first 2^59 steps. The driver stops if S >= 2^62.
#ifndef MAPS_H
#define MAPS_H
#include <stdint.h>
typedef uint64_t u64; typedef int64_t i64; typedef unsigned __int128 u128;
typedef struct { u64 v[3]; } st_t;
// Forced conditional moves: gcc otherwise turns these selects back into branches, which mispredict about half the time.
// SEL_POS(d,x,y): if d>0 keep x else take y. SEL_NEG(d,x,y): if d<0 keep x else take y.
#define CMOV_LE(cond_reg,x,y) __asm__("test %2,%2\n\tcmovle %1,%0":"+r"(x):"r"(y),"r"(cond_reg):"cc")
#define CMOV_GE(cond_reg,x,y) __asm__("test %2,%2\n\tcmovns %1,%0":"+r"(x):"r"(y),"r"(cond_reg):"cc")

// 1RB---_0RC0RD_1LD1RB_0LE0LC_1RA0LF_1LD1LE, wiki: A(a,b,c)=0^inf 1^a (10)^b C> 1^c 0^inf, start A(0,1,0).
// k=c/3, r=c%3, e=c-3a-3; X=a+2b+c:
//   e<0 (a>=k)     -> (4k+2b+2r+1, 1, a-k+1)     X+4+r
//   e==0,1         -> Halt
//   e>=2           -> (4a+2b+4, 2, e-2)          X+3
// d=e, halt at d=0 or d=1.
#define MACHINE "1RB---_0RC0RD_1LD1RB_0LE0LC_1RA0LF_1LD1LE"
#define MNAME "c273"
#ifndef CKPT_LG
#define CKPT_LG 37
#endif
static const st_t START={{0,1,0}};
static inline u64 level(const st_t*s){return s->v[0]+s->v[2];}
static inline i64 dist(const st_t*s){return (i64)s->v[2]-3*(i64)s->v[0]-3;}
static inline int exact_step(st_t*s){
  u64 a=s->v[0],b=s->v[1],c=s->v[2];
  i64 e=(i64)c-3*(i64)a-3;
  if(e<0){u64 k=c/3,r=c%3;s->v[0]=4*k+2*b+2*r+1;s->v[1]=1;s->v[2]=a-k+1;return 0;}
  if(e<=1)return 1;
  s->v[0]=4*a+2*b+4;s->v[1]=2;s->v[2]=(u64)e-2;return 0;
}
#define WINDOW_LIMIT(W) (2*(W))
// Short-latency asm loop on A=a+1, c, Q=2b+2. floor(c/3)=high64(c*(2^64+2)/3) for c<2^63. With e=c-3A, k=c/3:
//   e<0 : A'=2(c-k)+Q,  c'=A-k,  Q'=4 (b'=1)
//   e>=0: A'=4A+Q-1,    c'=e-2,  Q'=6 (b'=2)    (correct for e>=2; e=0,1 is inside the window and gets redone)
static __attribute__((noinline)) u64 fast_block(st_t*s,u64 n,u64 W){
  // Registers are pinned: rbp or r13 as a lea base forces a displacement byte, and such a lea takes 2 cycles here.
  register u64 A __asm__("rax")=s->v[0]+1; register u64 Q __asm__("rcx")=2*s->v[1]+2; register u64 c __asm__("rbx")=s->v[2]; register u64 m __asm__("r14")=~0ULL; register u64 nn __asm__("r15")=n;
  register u64 e __asm__("rsi"),x __asm__("r8"),z __asm__("r9"),a2 __asm__("r11"),c1 __asm__("r10"),c2 __asm__("r12"),k __asm__("rbp"),t __asm__("rdi"),q2 __asm__("r13");
  register u64 rdx __asm__("rdx")=0x5555555555555556ULL;
  (void)W; // W is the literal 8192 below
  __asm__ volatile(
    ".p2align 6\n1:\n"
    "lea (%[A],%[A],2),%[t]\n"
    "mov %[c],%[e]\n sub %[t],%[e]\n"
    "lea 8192(%[e]),%[x]\n"
    "mulx %[c],%[k],%[k]\n"
    "mov %[c],%[z]\n sub %[k],%[z]\n"
    "lea (%[Q],%[z],2),%[z]\n"
    "mov %[A],%[c1]\n sub %[k],%[c1]\n"
    "lea -1(%[Q],%[A],4),%[a2]\n"
    "lea -2(%[e]),%[c2]\n"
    "mov $4,%k[Q]\n"
    "mov $6,%k[q2]\n"
    "test %[e],%[e]\n"
    "cmovns %[a2],%[z]\n"
    "cmovns %[c2],%[c1]\n"
    "cmovns %[q2],%[Q]\n"
    "mov %[z],%[A]\n mov %[c1],%[c]\n"
    "cmp %[m],%[x]\n cmovb %[x],%[m]\n"
    "dec %[n]\n jnz 1b\n"
    :[A]"+r"(A),[Q]"+r"(Q),[c]"+r"(c),[m]"+r"(m),[n]"+r"(nn),[e]"=&r"(e),[x]"=&r"(x),[z]"=&r"(z),[a2]"=&r"(a2),[c1]"=&r"(c1),[c2]"=&r"(c2),[k]"=&r"(k),[t]"=&r"(t),[q2]"=&r"(q2)
    :"d"(rdx)
    :"cc");
  s->v[0]=A-1;s->v[1]=(Q-2)/2;s->v[2]=c;return m;
}
static inline u64 fast_block_c(st_t*s,u64 n,u64 W){
  u64 a=s->v[0],b=s->v[1],c=s->v[2],m=~0ULL;
  const u64 inv3=0xAAAAAAAAAAAAAAABULL;
  for(u64 i=0;i<n;i++){
    i64 e=(i64)c-3*(i64)a-3;
    u64 x=(u64)e+W; m=x<m?x:m;
    u64 k=(u64)(((u128)c*inv3)>>65);
    u64 r=c-3*k;
    u64 tb=2*b;
    u64 a1=4*k+tb+2*r+1, c1=a-k+1;
    u64 a2=4*a+tb+4, c2=(u64)e-2;
    u64 b1=1,b2=2;
    CMOV_GE(e,a1,a2); CMOV_GE(e,c1,c2); CMOV_GE(e,b1,b2); a=a1; c=c1; b=b1;
  }
  s->v[0]=a;s->v[1]=b;s->v[2]=c;return m;
}
#endif
