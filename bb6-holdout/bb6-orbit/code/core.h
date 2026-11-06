// Phase engine for the rule map, shared by the production tools.
// A reset state is (a0,B), a0 in {6,22}. An Entry records the branch word of one sweep from a reset state.
// Lemma used: along a fixed word every a,b is affine in B with integer slope, and a+b = B + constant, so B' = B + delta
// with delta constant. If B2 = B (mod 4) and B <= B2 <= hi the word is the same: the residue guards read only b mod 2,
// a mod 4 and (a-b) mod 4, and the comparison guards are monotone in B, which is what hi records.
// A halt excludes every guard, so it is never inside a domain other than as the walked point itself.
#include <stdint.h>
#include <string.h>
typedef uint64_t u64;
#ifdef BIGBITS
typedef signed _BitInt(BIGBITS) I; typedef unsigned _BitInt(BIGBITS) U;
#define IBITS BIGBITS
static inline int bl(U x){ u64 w[BIGBITS/64]; memcpy(w,&x,sizeof w); for(int i=BIGBITS/64-1;i>=0;i--) if(w[i]) return 64*(i+1)-__builtin_clzll(w[i]); return 0; }
#else
typedef __int128 I; typedef unsigned __int128 U;
#define IBITS 128
static inline int bl(U x){ u64 h=x>>64; if(h) return 128-__builtin_clzll(h); u64 l=x; return l?64-__builtin_clzll(l):0; }
#endif
#define ICAP ((I)1<<(IBITS-3))
static char *ps(I x,char*b){ char t[IBITS/2]; int n=0; int neg=x<0; U u=neg?-(U)x:(U)x; if(!u) t[n++]='0'; while(u){t[n++]='0'+(int)(u%10);u/=10;} int m=0; if(neg)b[m++]='-'; while(n)b[m++]=t[--n]; b[m]=0; return b; }
static I parseI(const char*s){ I v=0; for(;*s;s++) v=v*10+(*s-'0'); return v; }
static I SK[2][IBITS],AK[2][IBITS];
static void core_init(void){ for(int z=0;z<2;z++){ I a=z?22:6,s=0; for(int k=0;k<IBITS;k++){ SK[z][k]=ICAP; AK[z][k]=ICAP; }
    for(int k=0;k<IBITS-8;k++){ AK[z][k]=a; SK[z][k]=s; s+=a+3; a=2*a+6; if(bl(a)>IBITS-4) { break; } } } }
static inline int kfor(int z,I B){ // smallest k with B<=S_{k+1}. Chain sums: S_k ~ (a0+6) 2^k.
  int k=bl(B)-(z?5:4)-1; if(k<0)k=0; while(k>0&&B<=SK[z][k]) k--; while(B>SK[z][k+1]) k++; return k; }
enum {cD=1,cP,cQ,cR,cS,cT,cU,cV,cW,cX,cH};
typedef struct { I B0,hi,delta; int na0; int k; int len; int valid; } Entry;
#define HALTED (-1)
#define NORESET (-2)
#ifndef TAILCAP
#define TAILCAP 100000
#endif
// Optional hook: called for every tail element with position, a, b, slopes.
#ifndef ELEM_HOOK
#define ELEM_HOOK(e,pos,a,b,ga,gb,code)
#endif
// Walk one sweep from (a0,B). Fills e. Returns na0 (6/22), HALTED or NORESET. On HALTED *ha,*hb hold the halting pair.
static int walk(int a0,I B,Entry*e,I*ha,I*hb){
  int z=(a0==22); int k=kfor(z,B); I a=AK[z][k],b=B-SK[z][k];
  I ga=0,gb=1,hi=ICAP; int len=k,big=0;
  for(int steps=0;;steps++){
    I d=b-a-3; int c;
    if(d==0){ *ha=a;*hb=b; e->len=len; return HALTED; }
    if(steps>=TAILCAP){ *ha=a;*hb=b; e->len=len; return NORESET; }
    if(!big&&bl(gb<0?-gb:gb)>IBITS-28) { big=1; hi=B; }
    #define BOUND(g,s) do{ I s_=(s); if(s_<0){ I q=(g)/(-s_); if(B+q<hi) hi=B+q; } }while(0)
    I na,nb,nga,ngb;
    if(d>0){ c=cD; if(!big) BOUND(d-1,gb-ga); na=2*a+6; nb=d; nga=2*ga; ngb=gb-ga; }
    else if(b==1||b==3){ hi=B; big=1; nga=ngb=0;
      if(b==1){ if(((int)a&3)==2){c=cP;na=6;nb=a+7;} else {c=cQ;na=22;nb=a-2;} }
      else { if(((int)a&3)==2){c=cR;na=6;nb=a+13;} else {c=cS;na=a+8;nb=2;} } }
    else if((int)b&1){
      if(b==a+1){ c=cT; hi=B; big=1; na=6; nb=a+b+2; nga=ngb=0; }
      else { if(!big){ BOUND(b-5,gb); BOUND(a-1-b,ga-gb); }
        if(((int)(a-b+5)&3)==2){c=cU;na=a-b+11;nb=2*b-4;} else {c=cV;na=a-b+19;nb=2*b-8;}
        nga=ga-gb; ngb=2*gb; } }
    else { if(!big){ BOUND(b-2,gb); BOUND(a+2-b,ga-gb); }
      nga=ngb=0;
      if(((int)(a-b)&3)==2){c=cW;na=6;nb=a+b+7;} else {c=cX;na=22;nb=a+b-2;} }
    ELEM_HOOK(e,len,a,b,ga,gb,c);
    len++; a=na;b=nb;ga=nga;gb=ngb;
    if(a==6||a==22) break;
  }
  e->B0=B;e->hi=hi;e->delta=b-B;e->na0=(int)a;e->k=k;e->len=len;e->valid=1;
  return (int)a;
}
typedef struct { Entry e[2][4]; } Cache;
