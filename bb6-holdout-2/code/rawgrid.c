// Every rule branch against the raw TM, from a tape written directly from the map state: an exhaustive small grid, then random
// larger states. Each state must reach its map successor (exact cell compare), or halt where the map says halt.
// usage: rawgrid GRID_S NRANDOM RANDOM_S_MAX      c273. Prints per-branch counts.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include "maps.h"
typedef struct { unsigned char w; signed char dir; signed char next; } tr_t;
static tr_t T[6][2];
static void parse(const char*m){ for(int i=0;i<6;i++)for(int j=0;j<2;j++){ const char*p=m+7*i+3*j; if(p[2]=='-'){T[i][j].next=-1;T[i][j].w=0;T[i][j].dir=0;} else {T[i][j].w=p[0]-'0';T[i][j].dir=p[1]=='R'?1:-1;T[i][j].next=p[2]-'A';} } }
typedef struct { unsigned char sym; u64 len; } run_t;
typedef struct { int q; run_t L[16],R[16]; int nL,nR; u64 lenL,lenR; } exp_t;
static void addL(exp_t*E,int sym,u64 len){if(!len)return; if(E->nL&&E->L[E->nL-1].sym==sym)E->L[E->nL-1].len+=len; else {E->L[E->nL].sym=sym;E->L[E->nL].len=len;E->nL++;}}
static void addR(exp_t*E,int sym,u64 len){if(!len)return; if(E->nR&&E->R[E->nR-1].sym==sym)E->R[E->nR-1].len+=len; else {E->R[E->nR].sym=sym;E->R[E->nR].len=len;E->nR++;}}
static void render(const st_t*s,exp_t*E){
  E->nL=E->nR=0;
  E->q=2; for(u64 i=0;i<s->v[1];i++){addL(E,0,1);addL(E,1,1);} addL(E,1,s->v[0]); addR(E,1,s->v[2]);
  while(E->nL&&E->L[E->nL-1].sym==0)E->nL--; while(E->nR&&E->R[E->nR-1].sym==0)E->nR--;
  E->lenL=E->lenR=0; for(int i=0;i<E->nL;i++)E->lenL+=E->L[i].len; for(int i=0;i<E->nR;i++)E->lenR+=E->R[i].len;
}
#define TAPE (1ULL<<36)
static unsigned char*tape;
static int branch_of(const st_t*s){
  i64 e=dist(s); u64 c=s->v[2]; if(e<0)return c%3 + 3*(s->v[1]-1); if(e<=1)return 6+e; return 8+(s->v[1]-1);
}
static u64 stats[16]; static u64 fails=0;
// returns raw steps, or -1 on failure
static long long test(const st_t*s,u64 bound){
  exp_t Es,En; render(s,&Es); st_t nx=*s; int mh=exact_step(&nx); if(!mh)render(&nx,&En);
  u64 base=TAPE/2, pos=base; u64 lo,hi;
  // write start tape
  lo=hi=pos; u64 p=pos-1; for(int i=0;i<Es.nL;i++)for(u64 k=0;k<Es.L[i].len;k++,p--){tape[p]=Es.L[i].sym;}
  lo=pos-Es.lenL;
  p=pos; for(int i=0;i<Es.nR;i++)for(u64 k=0;k<Es.R[i].len;k++,p++){tape[p]=Es.R[i].sym;}
  hi=Es.lenR?pos+Es.lenR-1:pos;
  u64 wlo=lo,whi=hi; int q=Es.q; u64 raw=0; int res=0;
  for(;;){
    if(raw>0&&!mh&&q==En.q){
      // compare exactly
      int ok=1; u64 pp=pos-1;
      for(int i=0;i<En.nL&&ok;i++)for(u64 k=0;k<En.L[i].len;k++,pp--)if(tape[pp]!=En.L[i].sym){ok=0;break;}
      if(ok){ for(u64 x=wlo;x<=pp&&x>=wlo;x++){ if(tape[x]){ok=0;break;} if(x==pp)break; } }
      if(ok){ pp=pos; for(int i=0;i<En.nR&&ok;i++)for(u64 k=0;k<En.R[i].len;k++,pp++)if(tape[pp]!=En.R[i].sym){ok=0;break;}
        if(ok){ for(u64 x=pp;x<=whi;x++)if(tape[x]){ok=0;break;} } }
      if(ok){res=1;break;}
    }
    tr_t*t=&T[q][tape[pos]];
    if(t->next<0){res=mh?1:0;break;}
    tape[pos]=t->w; if(pos<wlo)wlo=pos; if(pos>whi)whi=pos;
    pos+=t->dir; q=t->next; raw++;
    if(raw>bound){res=0;break;}
  }
  // clean
  memset(tape+wlo-2,0,whi-wlo+5);
  if(!res){fails++;printf("FAIL state %llu %llu %llu mh=%d raw=%llu\n",(unsigned long long)s->v[0],(unsigned long long)s->v[1],(unsigned long long)s->v[2],mh,(unsigned long long)raw);return -1;}
  stats[branch_of(s)]++; return raw;
}
static u64 rs=0x123456789abcdefULL; static u64 rnd(){rs^=rs<<13;rs^=rs>>7;rs^=rs<<17;return rs;}
int main(int ac,char**av){
  parse(MACHINE); u64 G=strtoull(av[1],0,10),NR=strtoull(av[2],0,10),SM=strtoull(av[3],0,10);
  tape=mmap(0,TAPE,PROT_READ|PROT_WRITE,MAP_PRIVATE|MAP_ANONYMOUS|MAP_NORESERVE,-1,0);
  u64 tests=0;
  for(u64 S=0;S<=G;S++)for(u64 a=0;a<=S;a++)for(u64 b=1;b<=2;b++){st_t s={{a,b,S-a}}; test(&s,8*(S+20)*(S+20)+100000);tests++;}
  for(u64 i=0;i<NR;i++){u64 S=SM/2+rnd()%(SM/2),a=rnd()%S,b=1+(rnd()&1),c=S-a; if(i%4==0){c=3*a+rnd()%21;if(c>=10)c-=10;else c=0;} st_t s={{a,b,c}}; S=a+c; test(&s,8*(S+20)*(S+20)+100000);tests++;}
  printf("%s tests %llu fails %llu per-branch:",MACHINE,(unsigned long long)tests,(unsigned long long)fails); for(int i=0;i<16;i++)if(stats[i])printf(" %d:%llu",i,(unsigned long long)stats[i]); printf("\n");
  return fails?1:0;
}
