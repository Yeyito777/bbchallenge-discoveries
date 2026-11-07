// Long exact run of one rule map, resumable. Usage: hunt DIR [stop_level_lg]
// Files in DIR: ckpt.log (one line per checkpoint, last complete line is the resume point),
// near.log (every state with |d|<=W, S>=2^24 or |d|<=64), status.json, HALT (only on a halt).
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>
#include <fcntl.h>
#include <sys/stat.h>
#include "maps.h"
#define W 8192ULL
#define BLOCK (1ULL<<16)
static inline u64 rotl(u64 x,int k){return (x<<k)|(x>>(64-k));}
static inline u64 mix(u64 h,const st_t*s){
  for(int i=0;i<3;i++){h=rotl(h^s->v[i],23)*0x9E3779B97F4A7C15ULL;}
  return h;
}
static char dir[4096];
static const char* P(const char*n){static char b[4200];snprintf(b,sizeof b,"%s/%s",dir,n);return b;}
static double now(void){struct timespec t;clock_gettime(CLOCK_REALTIME,&t);return t.tv_sec+t.tv_nsec*1e-9;}
typedef struct { u64 n,hash,cnt,cnttot,nearoff; st_t s; } ck_t;
static u64 minabs[64]; static u64 nearn[64][17];
static int lg64(u64 x){return x?63-__builtin_clzll(x):0;}
static FILE* nearf;
static void record(u64 n,const st_t*s,i64 d,u64*cnt){
  (*cnt)++;
  u64 ad=d<0?-d:d; u64 S=level(s); int lg=lg64(S);
  if(ad<minabs[lg])minabs[lg]=ad;
  if(ad<=16)nearn[lg][ad]++;
  if(S>=(1ULL<<24)||ad<=64)
    fprintf(nearf,"%llu %llu %llu %llu %lld\n",(unsigned long long)n,(unsigned long long)s->v[0],(unsigned long long)s->v[1],(unsigned long long)s->v[2],(long long)d);
}
static void write_status(const ck_t*c,double rate,int halted){
  char tmp[4300]; snprintf(tmp,sizeof tmp,"%s/status.json.tmp",dir);
  FILE*f=fopen(tmp,"w"); if(!f)return;
  fprintf(f,"{\"machine\":\"%s\",\"name\":\"%s\",\"n\":%llu,\"level\":%llu,\"lg_level\":%.3f,\"state\":[%llu,%llu,%llu],\"near_total\":%llu,\"rate_per_s\":%.0f,\"halted\":%d,\"unix\":%.0f,\"min_abs_d_by_lg\":{",
    MACHINE,MNAME,(unsigned long long)c->n,(unsigned long long)level(&c->s),__builtin_log2((double)level(&c->s)),
    (unsigned long long)c->s.v[0],(unsigned long long)c->s.v[1],(unsigned long long)c->s.v[2],(unsigned long long)c->cnttot,rate,halted,now());
  int first=1;for(int i=0;i<64;i++)if(minabs[i]!=~0ULL){fprintf(f,"%s\"%d\":%llu",first?"":",",i,(unsigned long long)minabs[i]);first=0;}
  fprintf(f,"}}\n");fclose(f);
  char fin[4300];snprintf(fin,sizeof fin,"%s/status.json",dir);rename(tmp,fin);
}
static void ck_write(const ck_t*c){
  // n s0 s1 s2 hash cnt nearoff cnttot
  fflush(nearf); fsync(fileno(nearf));
  int fd=open(P("ckpt.log"),O_WRONLY|O_APPEND|O_CREAT,0644);
  char l[512];int m=snprintf(l,sizeof l,"%llu %llu %llu %llu %016llx %llu %llu %llu %.0f\n",(unsigned long long)c->n,(unsigned long long)c->s.v[0],(unsigned long long)c->s.v[1],(unsigned long long)c->s.v[2],(unsigned long long)c->hash,(unsigned long long)c->cnt,(unsigned long long)c->nearoff,(unsigned long long)c->cnttot,now());
  if(write(fd,l,m)!=m){perror("ckpt");exit(2);} fsync(fd);close(fd);
}
static int ck_read_last(ck_t*c){
  FILE*f=fopen(P("ckpt.log"),"r"); if(!f)return 0;
  char l[512],good[512];int have=0;
  while(fgets(l,sizeof l,f)){ if(strchr(l,'\n')){strcpy(good,l);have=1;} }
  fclose(f); if(!have)return 0;
  unsigned long long a[8];double t;
  if(sscanf(good,"%llu %llu %llu %llu %llx %llu %llu %llu %lf",&a[0],&a[1],&a[2],&a[3],&a[4],&a[5],&a[6],&a[7],&t)!=9){fprintf(stderr,"bad ckpt line\n");exit(2);}
  c->n=a[0];c->s.v[0]=a[1];c->s.v[1]=a[2];c->s.v[2]=a[3];c->hash=a[4];c->cnt=a[5];c->nearoff=a[6];c->cnttot=a[7];
  return 1;
}
static void rebuild_stats(u64 off){ // minabs/nearn are recomputed from near.log on resume; events below 2^24 with |d|>64 are not logged
  FILE*f=fopen(P("near.log"),"r"); if(!f)return;
  unsigned long long n,x,y,z;long long d;u64 pos=0;char l[256];
  while(pos<off&&fgets(l,sizeof l,f)){pos+=strlen(l);
    if(sscanf(l,"%llu %llu %llu %llu %lld",&n,&x,&y,&z,&d)==5){st_t s={{x,y,z}};u64 ad=d<0?-d:d;int lg=lg64(level(&s));if(ad<minabs[lg])minabs[lg]=ad;if(ad<=16)nearn[lg][ad]++;}}
  fclose(f);
}
static void do_halt(u64 at,const st_t*s,i64 d,u64 h,u64 cnt,u64 cnttot,const ck_t*c){
  fflush(nearf);
  FILE*f=fopen(P("HALT"),"w");
  fprintf(f,"machine %s\nmap_steps_done %llu\nstate %llu %llu %llu\nd %lld\nunix %.0f\n",MACHINE,(unsigned long long)at,(unsigned long long)s->v[0],(unsigned long long)s->v[1],(unsigned long long)s->v[2],(long long)d,now());
  fclose(f);
  ck_t hc=*c;hc.n=at;hc.s=*s;hc.hash=h;hc.cnt=cnt;hc.cnttot=cnttot+cnt;write_status(&hc,0,1);
}
int main(int ac,char**av){
  if(ac<2){fprintf(stderr,"usage: hunt DIR [stop_lg]\n");return 1;}
  strncpy(dir,av[1],sizeof dir-1); mkdir(dir,0755);
  int stoplg=ac>2?atoi(av[2]):62;
  for(int i=0;i<64;i++)minabs[i]=~0ULL;
  ck_t c; memset(&c,0,sizeof c);
  if(ck_read_last(&c)){
    if(truncate(P("near.log"),c.nearoff)!=0&&c.nearoff>0){perror("truncate near.log");return 2;}
    rebuild_stats(c.nearoff);
    fprintf(stderr,"resume n=%llu\n",(unsigned long long)c.n);
  } else {
    c.n=0;c.s=START;c.hash=0;c.cnt=0;c.cnttot=0;c.nearoff=0;
    nearf=fopen(P("near.log"),"a");ck_write(&c);fclose(nearf);
  }
  nearf=fopen(P("near.log"),"a"); setvbuf(nearf,NULL,_IOFBF,1<<20); fseek(nearf,0,SEEK_END);
  c.hash=0;c.cnt=0;
  st_t s=c.s; u64 n=c.n,h=0,cnt=0,cnttot=c.cnttot;
  const u64 interval=1ULL<<CKPT_LG;
  double t0=now(),tl=t0;u64 nl=n;
  for(;;){
#ifdef CHUNK_STEPS
    u64 chunks=BLOCK/CHUNK_STEPS, done=0;
    while(done<chunks){
      done+=fast_chunks(&s,chunks-done,CHUNK_T);
      if(done<chunks){ // this chunk was flagged and not committed: redo it with the exact rules
        u64 base=n+done*CHUNK_STEPS;
        for(u64 i=0;i<CHUNK_STEPS;i++){
          i64 d=dist(&s); u64 ad=d<0?-d:d;
          if(ad<=W) record(base+i,&s,d,&cnt);
          if(exact_step(&s)){ do_halt(base+i,&s,d,h,cnt,cnttot,&c); return 42; }
        }
        done++;
      }
    }
#else
    st_t s0=s;
    u64 m=fast_block(&s,BLOCK,W);
    if(m<=WINDOW_LIMIT(W)){
      s=s0;
      for(u64 i=0;i<BLOCK;i++){
        i64 d=dist(&s); u64 ad=d<0?-d:d;
        if(ad<=W) record(n+i,&s,d,&cnt);
        if(exact_step(&s)){ do_halt(n+i,&s,d,h,cnt,cnttot,&c); return 42; }
      }
    }
#endif
    n+=BLOCK;
    h=mix(h,&s);
    if((n&(interval-1))==0){
      double t=now(); double rate=(n-nl)/(t-tl);tl=t;nl=n;
      cnttot+=cnt;
      fflush(nearf);
      c.n=n;c.s=s;c.hash=h;c.cnt=cnt;c.cnttot=cnttot;c.nearoff=(u64)ftell(nearf);
      ck_write(&c);write_status(&c,rate,0);
      h=0;cnt=0;
      if(level(&s)>=(1ULL<<stoplg)||level(&s)>=(1ULL<<62)){fprintf(stderr,"frontier reached\n");return 0;}
    }
  }
}
