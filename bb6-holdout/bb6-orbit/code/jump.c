// Jumping simulator for the rule map of 1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA from A(6,1).
// A sweep runs from a reset state (a0 in {6,22}, B) to the next one. A jump repeats the last P sweeps T more times
// after proving every branch guard holds for all T repeats:
//   every (a,b) along a fixed branch word is affine in the repeat index t, because the word is a composition of
//   affine maps; comparisons are monotone in t, so the last t decides them; residue guards depend on b mod 2,
//   a mod 4 and (a-b) mod 4 only, which have period dividing 4 in t, so t=1..4 decide them.
// Halting (b==a+3) excludes every guard, so a halt cannot be jumped over.
// usage: jump [-p Pmax] [-t seconds] [-B maxbits] [-l logfile] [-c ckptfile] [-s samplefile]
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <unistd.h>
typedef __int128 I; typedef unsigned __int128 U; typedef uint64_t u64;
enum {cD=1,cP,cQ,cR,cS,cT,cU,cV,cW,cX,cH};
static inline int bl(U x){ u64 h=x>>64; if(h) return 128-__builtin_clzll(h); u64 l=x; return l?64-__builtin_clzll(l):0; }
static char *ps(I x,char*b){ char t[64]; int n=0; int neg=x<0; U u=neg?-(U)x:(U)x; if(!u) t[n++]='0'; while(u){t[n++]='0'+(int)(u%10);u/=10;} int m=0; if(neg)b[m++]='-'; while(n)b[m++]=t[--n]; b[m]=0; return b; }
static inline int branch(I a,I b){
  I d=b-a-3;
  if(d==0) return cH; if(d>0) return cD;
  if(b==1) return ((int)a&3)==2?cP:cQ;
  if(b==3) return ((int)a&3)==2?cR:cS;
  int dm=(int)(a-b)&3;
  if((int)b&1){ if(b==a+1) return cT; return ((dm+5)&3)==2?cU:cV; } // u=(a-b+5)/2 odd <=> a-b+5 == 2 mod 4
  return dm==2?cW:cX; // h=(a-b)/2 odd <=> a-b == 2 mod 4
}
static inline void apply(int k,I*A,I*B){ I a=*A,b=*B; switch(k){
  case cD:*A=2*a+6;*B=b-a-3;break;
  case cP:*A=6;*B=a+7;break; case cQ:*A=22;*B=a-2;break;
  case cR:*A=6;*B=a+13;break; case cS:*A=a+8;*B=2;break;
  case cT:*A=6;*B=a+b+2;break;
  case cU:*A=a-b+11;*B=2*b-4;break; case cV:*A=a-b+19;*B=2*b-8;break;
  case cW:*A=6;*B=a+b+7;break; case cX:*A=22;*B=a+b-2;break; }}
#define TAILMAX 4096
#define PMAXMAX 512
typedef struct { I a0,B; int k,tl; uint32_t h; I *ta,*tb; unsigned char *tc; } S;
#define RING 1024
static S R[RING]; static long idx=0; // number of sweeps in the current history window
static inline S* G(long back){ return &R[(idx-1-back)&(RING-1)]; } // G(0)=latest
static I SK[2][128], AK[2][128]; // chain tables: S_k, a_k for a0=6,22
static inline int kfor(int z,I B){ // smallest k with B<=S_{k+1}; D fires for j<k
  int k=0; while(B>SK[z][k+1]) k++; return k; }
#define SCALES 128
typedef struct { I dpos,npos,apos,bpos, dneg,nneg,aneg,bneg; } Best;
static Best best[SCALES];
static long long jumps_sc[SCALES],sweeps_sc[SCALES]; static double t_sc[SCALES];
static I n=0; static long long jumps=0,sweeps=0,sim_after=0;
static I curA=6,curB=1;
static FILE *logf=0,*samp=0; static long long logbytes=0;
static inline void putv(U v){ while(v>=128){ fputc((int)(v&127)|128,logf); v>>=7; logbytes++; } fputc((int)v,logf); logbytes++; }
static inline void note(int sc,I a,I b,I nn){ I d=b-a-3; Best*x=&best[sc];
  if(d>=0){ if(d<x->dpos){x->dpos=d;x->npos=nn;x->apos=a;x->bpos=b;} }
  else { I e=-d; if(e<x->dneg){x->dneg=e;x->nneg=nn;x->aneg=a;x->bneg=b;} } }
static void halt_report(I a,I b,I nn){ char x[64],y[64],z[64]; printf("HALT n=%s a=%s b=%s\n",ps(nn,x),ps(a,y),ps(b,z)); fflush(stdout); }
static void ckpt_write(const char*f){ if(!f) return; char t[512]; snprintf(t,512,"%s.tmp",f); FILE*c=fopen(t,"wb"); if(!c) return;
  if(logf) fflush(logf); if(samp) fflush(samp);
  fwrite(&curA,sizeof curA,1,c);fwrite(&curB,sizeof curB,1,c);fwrite(&n,sizeof n,1,c);fwrite(&jumps,8,1,c);fwrite(&sweeps,8,1,c);fwrite(&sim_after,8,1,c);
  fwrite(best,sizeof best,1,c);fwrite(jumps_sc,sizeof jumps_sc,1,c);fwrite(sweeps_sc,sizeof sweeps_sc,1,c);fwrite(t_sc,sizeof t_sc,1,c);fwrite(&logbytes,8,1,c);
  fclose(c); rename(t,f); }
static int ckpt_read(const char*f){ FILE*c=fopen(f,"rb"); if(!c) return 0;
  size_t ok=fread(&curA,sizeof curA,1,c);ok+=fread(&curB,sizeof curB,1,c);ok+=fread(&n,sizeof n,1,c);ok+=fread(&jumps,8,1,c);ok+=fread(&sweeps,8,1,c);ok+=fread(&sim_after,8,1,c);
  ok+=fread(best,sizeof best,1,c);ok+=fread(jumps_sc,sizeof jumps_sc,1,c);ok+=fread(sweeps_sc,sizeof sweeps_sc,1,c);ok+=fread(t_sc,sizeof t_sc,1,c);ok+=fread(&logbytes,8,1,c);
  fclose(c); return ok==11; }
static void dump_best(FILE*o){ char u[64],v[64],w[64],x[64];
  for(int i=0;i<SCALES;i++){ if(best[i].dpos==((I)1<<120)&&best[i].dneg==((I)1<<120)) continue;
    fprintf(o,"scale %d +d %s n %s a %s b %s",i,ps(best[i].dpos,u),ps(best[i].npos,v),ps(best[i].apos,w),ps(best[i].bpos,x));
    fprintf(o," | -d %s n %s a %s b %s | jumps %lld sweeps %lld t %.1f\n",ps(best[i].dneg,u),ps(best[i].nneg,v),ps(best[i].aneg,w),ps(best[i].bneg,x),jumps_sc[i],sweeps_sc[i],t_sc[i]); } }
int main(int ac,char**av){
  int Pmax=32; double tl=1e18; int maxbits=120; const char*logp=0,*ck=0,*sp=0; u64 sampevery=1<<14; int o;
  while((o=getopt(ac,av,"p:t:B:l:c:s:e:"))!=-1){ switch(o){ case 'p':Pmax=atoi(optarg);break; case 't':tl=atof(optarg);break; case 'B':maxbits=atoi(optarg);break;
    case 'l':logp=optarg;break; case 'c':ck=optarg;break; case 's':sp=optarg;break; case 'e':sampevery=strtoull(optarg,0,10);break; } }
  if(Pmax>PMAXMAX||Pmax*2+2>RING){puts("Pmax too big");return 2;}
  for(int i=0;i<RING;i++){ R[i].ta=malloc(sizeof(I)*TAILMAX); R[i].tb=malloc(sizeof(I)*TAILMAX); R[i].tc=malloc(TAILMAX); }
  for(int z=0;z<2;z++){ I a=z?22:6,s=0; for(int k=0;k<120;k++){ AK[z][k]=a; SK[z][k]=s; s+=a+3; a=2*a+6; if(a<0||s<0||bl(a)>124){ for(int q=k+1;q<128;q++){SK[z][q]=(I)1<<126;} break; } } }
  for(int i=0;i<SCALES;i++){ best[i].dpos=best[i].dneg=(I)1<<120; }
  int resumed=0; if(ck&&ckpt_read(ck)) resumed=1;
  if(logp){ if(resumed){ if(truncate(logp,logbytes)!=0){} logf=fopen(logp,"ab"); } else logf=fopen(logp,"wb"); }
  if(sp) samp=fopen(sp,resumed?"a":"w");
  long match[PMAXMAX+1]; long nextatt[PMAXMAX+1]; memset(match,0,sizeof match); memset(nextatt,0,sizeof nextatt);
  time_t t0=time(0),tlast=t0; double tbase=resumed?0:0; int lastsc=0; long long tick=0; int dead=0; long long jump_sample=0;
  I a0=curA,B=curB; idx=0; char x1[64],x2[64];
  while(1){
    if((++tick&0xFFFFF)==0){ time_t now=time(0); if(difftime(now,tlast)>=60){ tlast=now; curA=a0;curB=B; ckpt_write(ck); printf("B bits %d n bits %d jumps %lld sweeps %lld t %.0f\n",bl(B),bl(n),jumps,sweeps,difftime(now,t0)); fflush(stdout);} if(difftime(now,t0)>=tl) break; }
    int sc=bl(B);
    if(sc>=maxbits) break;
    if(sc!=lastsc){ lastsc=sc; t_sc[sc]=difftime(time(0),t0); }
    // one sweep
    S*s=&R[idx&(RING-1)]; idx++; sweeps++; sweeps_sc[sc]++; s->a0=a0; s->B=B;
    int z=(a0==22); int k=(a0==6||a0==22)?kfor(z,B):0;
    I a=(z||a0==6)?AK[z][k]:a0, b=(z||a0==6)?B-SK[z][k]:B;
    if(k>0){ // last chain element is the only near one for large B
      if(B<(1<<20)){ I ca=AK[z][0],cb=B; for(int j=0;j<k;j++){ note(sc,ca,cb,n+j); apply(cD,&ca,&cb);} }
      else { note(sc,AK[z][k-1],B-SK[z][k-1],n+k-1); }
    }
    I cnt=n+k; int tl_=0; uint32_t h=(uint32_t)(z*0x9E3779B1u)^((uint32_t)k*0x85EBCA6Bu);
    int reached=0;
    while(1){
      int c=branch(a,b);
      if(tl_>=TAILMAX){ printf("NO RESET: tail over %d at n=%s a bits %d b bits %d last code %d\n",TAILMAX,ps(cnt,x1),bl(a),bl(b),c); dead=1; break; }
      s->ta[tl_]=a;s->tb[tl_]=b;s->tc[tl_]=c;tl_++; h=(h^c)*16777619u;
      note(sc,a,b,cnt);
      if(c==cH){ halt_report(a,b,cnt); dead=2; break; }
      apply(c,&a,&b); cnt++;
      if(a==6||a==22) { reached=1; break; }
    }
    if(dead) { n=cnt; curA=a;curB=b; break; }
    (void)reached;
    s->k=k; s->tl=tl_; s->h=h;
    if(a%4==2&&b==2*a+18&&a>6){ printf("SINK at sweep start n=%s\n",ps(cnt,x1)); dead=3; }
    n=cnt; a0=a; B=b; sim_after++;
    if(bl(B)>122){ puts("int128 guard"); dead=4; break; }
    // period detection
    long i_=idx; int did=0;
    for(int P=1;P<=Pmax;P++){
      if(i_<=P){ match[P]=0; continue; }
      if(R[(i_-1)&(RING-1)].h==R[(i_-1-P)&(RING-1)].h) match[P]++; else match[P]=0;
      if(did) continue;
      if(match[P]>=P && i_>=nextatt[P] && i_>=2*P){
        I D=G(0)->B-G(P)->B; // current B minus start of last period equals D too
        if(B-G(P-1)->B!=D || D<=0 || G(P-1)->a0!=a0){ nextatt[P]=i_+P; continue; }
        // exact word comparison and T bound
        I T=(((U)1<<bl(B))-1-B)/D; int ok=1;
        // chain tail guard is covered by the first tail element; words must match exactly
        for(int i=0;i<P&&ok;i++){ S*u=G(i),*v=G(i+P); if(u->k!=v->k||u->tl!=v->tl||u->a0!=v->a0){ok=0;break;}
          if(u->k>0 && 0){}
          for(int j=0;j<u->tl;j++){ if(u->tc[j]!=v->tc[j]){ok=0;break;}
            I xa=u->ta[j],xb=u->tb[j],da=xa-v->ta[j],db=xb-v->tb[j]; int c=u->tc[j];
            #define BOUND(f0,df) do{ I f0_=(f0),df_=(df); if(df_<0){ I q=f0_/(-df_); if(q<T) T=q; } }while(0)
            switch(c){
              case cD: BOUND(xb-xa-4,db-da); break;
              case cU: case cV: BOUND(xb-5,db); BOUND(xa-1-xb,da-db); break;
              case cW: case cX: BOUND(xb-2,db); BOUND(xa+2-xb,da-db); break;
              default: break; }
            int lim=T<4?(int)T:4;
            for(int t=1;t<=lim;t++){ if(branch(xa+t*da,xb+t*db)!=c){ T=t-1; lim=t-1; break; } }
          }
        }
        if(!ok){ nextatt[P]=i_+P; continue; }
        // final assertion at t=T
        if(T>0){ for(int i=0;i<P;i++){ S*u=G(i),*v=G(i+P); for(int j=0;j<u->tl;j++){ I xa=u->ta[j],xb=u->tb[j],da=xa-v->ta[j],db=xb-v->tb[j];
            if(branch(xa+T*da,xb+T*db)!=u->tc[j]){ printf("ASSERT endpoint guard failed\n"); return 3; }
            // closest approach within the jump: |d| is monotone in t, so t=1 and t=T decide it. Word position p counts apps.
          } } }
        if(T<1){ nextatt[P]=i_+P; continue; }
        // near misses at endpoints, in forward order of position
        { I steps=0; for(int i=P-1;i>=0;i--){ S*u=G(i),*v=G(i+P); I pos=steps+u->k; for(int j=0;j<u->tl;j++){ I xa=u->ta[j],xb=u->tb[j],da=xa-v->ta[j],db=xb-v->tb[j];
              note(sc,xa+da,xb+db,n-0+0+pos+j); // t=1: first repeat begins at current n
              steps+=0; }
            if(u->k>0){ I la=AK[u->a0==22][u->k-1],lb=u->B-SK[u->a0==22][u->k-1]; note(sc,la,lb+D,n+steps+u->k-1); }
            steps+=u->k+u->tl; }
          I W=steps; I off=0; for(int i=P-1;i>=0;i--){ S*u=G(i),*v=G(i+P); I pos=off+u->k; for(int j=0;j<u->tl;j++){ I xa=u->ta[j],xb=u->tb[j],da=xa-v->ta[j],db=xb-v->tb[j];
              note(sc,xa+T*da,xb+T*db,n+(T-1)*W+pos+j); }
            if(u->k>0){ I la=AK[u->a0==22][u->k-1],lb=u->B-SK[u->a0==22][u->k-1]; note(sc,la,lb+T*D,n+(T-1)*W+off+u->k-1); }
            off+=u->k+u->tl; }
          n+=T*W;
        }
        B+=T*D; jumps++; jumps_sc[sc]++;
        if(logf){ putv((U)sim_after); putv((U)P); putv((U)T); }
        if(samp && ((u64)jumps%sampevery)==0){ fprintf(samp,"%s %d %s\n",ps(n,x1),(int)a0,ps(B,x2)); }
        sim_after=0; idx=0; memset(match,0,sizeof(long)*(Pmax+1)); memset(nextatt,0,sizeof(long)*(Pmax+1)); did=1;
      }
    }
    if(dead) break;
  }
  curA=a0;curB=B; ckpt_write(ck);
  dump_best(stdout);
  char xx[64],yy[64],zz[64]; printf("final n=%s a0=%s B=%s Bbits=%d jumps=%lld sweeps=%lld dead=%d t=%.0f\n",ps(n,xx),ps(a0,yy),ps(B,zz),bl(B),jumps,sweeps,dead,difftime(time(0),t0));
  if(logf) fclose(logf);
  return 0;
}
