// Raw TM from blank against the production map, independent of the map code except for the expected sequence.
// One byte per cell, plain transition table. At every map step the predicted tape must appear, in order; exact cell compare.
// usage: rawcheck SECONDS OUTFILE    (c273)
// OUTFILE gets "mapstep rawstep" for every matched state, used to fit and test the step-count polynomials.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <sys/mman.h>
#include "maps.h"
typedef struct { unsigned char w; signed char dir; signed char next; } tr_t;
static tr_t T[6][2];
static void parse(const char*m){ for(int i=0;i<6;i++)for(int j=0;j<2;j++){ const char*p=m+7*i+3*j; if(p[2]=='-'){T[i][j].next=-1;T[i][j].w=0;T[i][j].dir=0;} else {T[i][j].w=p[0]-'0';T[i][j].dir=p[1]=='R'?1:-1;T[i][j].next=p[2]-'A';} } }
// expected config as run lists from the head outward
#define MAXRUN 1000000
typedef struct { unsigned char sym; u64 len; } run_t;
typedef struct { int q; run_t *L,*R; long nL,nR; u64 lenL,lenR; } exp_t;
static run_t LB[MAXRUN],RB[MAXRUN];
static exp_t E;
static void eclear(int q){E.q=q;E.L=LB;E.R=RB;E.nL=E.nR=0;}
static void addL(int sym,u64 len){if(!len)return; if(E.nL&&E.L[E.nL-1].sym==sym)E.L[E.nL-1].len+=len; else {if(E.nL>=MAXRUN)abort();E.L[E.nL].sym=sym;E.L[E.nL].len=len;E.nL++;}}
static void addR(int sym,u64 len){if(!len)return; if(E.nR&&E.R[E.nR-1].sym==sym)E.R[E.nR-1].len+=len; else {if(E.nR>=MAXRUN)abort();E.R[E.nR].sym=sym;E.R[E.nR].len=len;E.nR++;}}
static void norm(void){ while(E.nL&&E.L[E.nL-1].sym==0)E.nL--; while(E.nR&&E.R[E.nR-1].sym==0)E.nR--; E.lenL=E.lenR=0; for(long i=0;i<E.nL;i++)E.lenL+=E.L[i].len; for(long i=0;i<E.nR;i++)E.lenR+=E.R[i].len; }
static st_t mp;
static void render(void){
  st_t*s=&mp;
  eclear(2); for(u64 i=0;i<s->v[1];i++){addL(0,1);addL(1,1);} addL(1,s->v[0]); addR(1,s->v[2]);
  norm();
}
static void map_init(void){mp=START;}
// production fast path, one step at a time, unless the window says the exact path is needed: same split the long run uses
#ifdef CHUNK_STEPS
// production fast path over a whole chunk; the rawcheck only uses it to compare against exact steps, then steps exact
static int map_next(void){ return exact_step(&mp); }
#else
static int map_next(void){ st_t t=mp; u64 m=fast_block(&t,1,8192); if(m<=WINDOW_LIMIT(8192ULL)){ return exact_step(&mp);} mp=t; return 0; }
#endif
#define TAPE (1ULL<<34)
static double now(void){struct timespec t;clock_gettime(CLOCK_MONOTONIC,&t);return t.tv_sec+t.tv_nsec*1e-9;}
int main(int ac,char**av){
  double secs=atof(av[1]); FILE*out=fopen(av[2],"w");
  parse(MACHINE);
  unsigned char*tape=mmap(0,TAPE,PROT_READ|PROT_WRITE,MAP_PRIVATE|MAP_ANONYMOUS|MAP_NORESERVE,-1,0);
  u64 pos=TAPE/2,lo=pos,hi=pos; // lo..hi bounds the nonzero cells
  int q=0; u64 raw=0,matched=0; double t0=now(); int halted=0;
  map_init(); render();
  u64 tries=0;
  for(;;){
    // inner loop: run until state and head-relative extents match
    for(;;){
      if(q==E.q && (E.lenL? (pos-lo==E.lenL && tape[lo]) : (pos<=lo && !(tape[lo]&&lo<pos))) ){
        // right extent: hi is the last nonzero (lazy shrink below)
        while(hi>pos && !tape[hi])hi--;
        u64 rl= (hi>=pos && (hi>pos||tape[pos]))? hi-pos+1:0;
        if(rl==E.lenR){
          tries++;
          // exact compare, cell by cell, outward
          int ok=1; u64 p=pos-1; 
          for(long i=0;i<E.nL&&ok;i++){u64 l=E.L[i].len;for(u64 k=0;k<l;k++,p--)if(tape[p]!=E.L[i].sym){ok=0;break;}}
          if(ok&&E.lenL==0){ /* all left must be blank */ for(u64 x=lo;x<pos;x++)if(tape[x]){ok=0;break;} }
          p=pos; for(long i=0;i<E.nR&&ok;i++){u64 l=E.R[i].len;for(u64 k=0;k<l;k++,p++)if(tape[p]!=E.R[i].sym){ok=0;break;}}
          if(ok)break;
        }
      }
      if((raw&0xFFFFFFF)==0 && now()-t0>secs) goto done;
      tr_t*t=&T[q][tape[pos]];
      if(t->next<0){halted=1;goto done;}
      tape[pos]=t->w;
      if(t->w){ if(pos<lo)lo=pos; if(pos>hi)hi=pos; }
      else if(pos==lo){ while(lo<hi&&!tape[lo])lo++; }
      pos+=t->dir; q=t->next; raw++;
      if(pos<4096||pos>TAPE-4096){fprintf(stderr,"tape bound\n");goto done;}
    }
    fprintf(out,"%llu %llu\n",(unsigned long long)matched,(unsigned long long)raw);
    matched++;
    if(map_next()){ fprintf(stderr,"map says halt at map step %llu raw %llu\n",(unsigned long long)matched,(unsigned long long)raw); render(); /* stale */ break; }
    render();
  }
  done:
  fclose(out);
  printf("%s matched %llu map states through raw step %llu, %.0f s, raw halted=%d, %.0f M raw/s, state q=%d expected q=%d filter_hits=%llu\n",MACHINE,(unsigned long long)matched,(unsigned long long)raw,now()-t0,halted,raw/1e6/(now()-t0),q,E.q,(unsigned long long)tries);
  return 0;
}
