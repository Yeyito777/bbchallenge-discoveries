// Production orbit runner (phase engine, __int128 with overflow guard). Starts at A(6,1) unless resumed.
// usage: orbit [-B maxbits] [-t seconds] [-c ckpt] [-s samplefile] [-e every] [-l log] [-w a0:B target check]
// Tracks the exact closest approach per scale (scale = bit length of the sweep's B) over every application.
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <unistd.h>
typedef struct { int pos; __int128 a,b,ga,gb; } Elem;
#define MAXEL 8192
static Elem *CUR; static int NCUR;
#define ELEM_HOOK(e,p,A,B_,GA,GB,c) do{ if(NCUR<MAXEL){ CUR[NCUR].pos=(p);CUR[NCUR].a=(A);CUR[NCUR].b=(B_);CUR[NCUR].ga=(GA);CUR[NCUR].gb=(GB);NCUR++; } }while(0)
#define TAILCAP 8000
#include "core.h"
#define SC 128
typedef struct { I dpos,npos,apos,bpos,dneg,nneg,aneg,bneg; } Best;
static Best best[SC]; static long long ph_sc[SC],sw_sc[SC]; static double t_sc[SC];
static I n=0; static long long phases=0,sweeps=0,walks=0,breakouts[8];
typedef struct { Entry e; Elem *el; int nel; } Slot;
static Slot slot[2][4];
static inline void note(int sc,I a,I b,I nn){ I d=b-a-3; Best*x=&best[sc];
  if(d>=0){ if(d<x->dpos){x->dpos=d;x->npos=nn;x->apos=a;x->bpos=b;} }
  else { I e=-d; if(e<x->dneg){x->dneg=e;x->nneg=nn;x->aneg=a;x->bneg=b;} } }
// record chain and tail approach for a sweep whose first application is number nn, with B = B0 + x
static inline void note_sweep(Slot*s,int z,int sc,I x,I nn,I B){
  int k=s->e.k;
  if(k>0){ if(B<(1<<20)){ I ca=AK[z][0],cb=B; for(int j=0;j<k;j++){ note(sc,ca,cb,nn+j); I na=2*ca+6; cb=cb-ca-3; ca=na; } }
           else note(sc,AK[z][k-1],B-SK[z][k-1],nn+k-1); }
  for(int i=0;i<s->nel;i++){ Elem*q=&s->el[i]; note(sc,q->a+q->ga*x,q->b+q->gb*x,nn+q->pos); }
}
static void dump(FILE*o){ char u[64],v[64],w[64],y[64]; for(int i=0;i<SC;i++){ if(best[i].dpos==((I)1<<120)&&best[i].dneg==((I)1<<120)) continue;
  fprintf(o,"scale %d +d %s n %s a %s b %s",i,ps(best[i].dpos,u),ps(best[i].npos,v),ps(best[i].apos,w),ps(best[i].bpos,y));
  fprintf(o," | -d %s n %s a %s b %s | phases %lld sweeps %lld t %.0f\n",ps(best[i].dneg,u),ps(best[i].nneg,v),ps(best[i].aneg,w),ps(best[i].bneg,y),ph_sc[i],sw_sc[i],t_sc[i]); } }
static int ckread(const char*f,int*a0,I*B){ FILE*c=fopen(f,"rb"); if(!c) return 0; size_t k=fread(a0,sizeof *a0,1,c);k+=fread(B,sizeof *B,1,c);k+=fread(&n,sizeof n,1,c);k+=fread(&phases,8,1,c);k+=fread(&sweeps,8,1,c);k+=fread(&walks,8,1,c);k+=fread(best,sizeof best,1,c);k+=fread(ph_sc,sizeof ph_sc,1,c);k+=fread(sw_sc,sizeof sw_sc,1,c);k+=fread(t_sc,sizeof t_sc,1,c);fclose(c);return k==10; }
static void ckwrite(const char*f,int a0,I B){ if(!f) return; char t[600]; snprintf(t,600,"%s.tmp",f); FILE*c=fopen(t,"wb"); if(!c) return; fwrite(&a0,sizeof a0,1,c);fwrite(&B,sizeof B,1,c);fwrite(&n,sizeof n,1,c);fwrite(&phases,8,1,c);fwrite(&sweeps,8,1,c);fwrite(&walks,8,1,c);fwrite(best,sizeof best,1,c);fwrite(ph_sc,sizeof ph_sc,1,c);fwrite(sw_sc,sizeof sw_sc,1,c);fwrite(t_sc,sizeof t_sc,1,c);fclose(c);rename(t,f); }
int main(int ac,char**av){ int maxbits=118; double tl=1e18; const char*ck=0,*sp=0,*wf=0; long long every=1<<14; int o; 
  while((o=getopt(ac,av,"B:t:c:s:e:w:"))!=-1) switch(o){ case 'B':maxbits=atoi(optarg);break; case 't':tl=atof(optarg);break; case 'c':ck=optarg;break; case 's':sp=optarg;break; case 'e':every=atoll(optarg);break; case 'w':wf=optarg;break; }
  core_init(); CUR=malloc(sizeof(Elem)*MAXEL);
  for(int z=0;z<2;z++) for(int m=0;m<4;m++){ slot[z][m].el=malloc(sizeof(Elem)*MAXEL); slot[z][m].e.valid=0; }
  for(int i=0;i<SC;i++) best[i].dpos=best[i].dneg=(I)1<<120;
  int a0=6; I B=1; if(ck) ckread(ck,&a0,&B); FILE*sf=sp?fopen(sp,ck?"a":"w"):0;
  // -w file: list of "a0 B" reset states to look up, ascending B. Reports whether the orbit visits each.
  FILE*wq=wf?fopen(wf,"r"):0; int wa=0; char wb[80]; I WB=(I)1<<125; long long wyes=0,wno=0; if(wq&&fscanf(wq,"%d %79s",&wa,wb)==2) WB=parseI(wb);
  time_t t0=time(0),tlast=t0; long long tick=0; int lastsc=0; char s1[64],s2[64],s3[64]; I ha,hb; int stop=0;
  while(!stop){
    if((++tick&0xFFFFF)==0){ time_t now=time(0); if(difftime(now,tlast)>=60){ tlast=now; ckwrite(ck,a0,B); if(sf)fflush(sf); printf("B bits %d n bits %d phases %lld sweeps %lld walks %lld t %.0f\n",bl(B),bl(n),phases,sweeps,walks,difftime(now,t0)); fflush(stdout);} if(difftime(now,t0)>=tl) break; }
    int sc=bl(B); if(sc>=maxbits) break; if(sc!=lastsc){ lastsc=sc; t_sc[sc]=difftime(time(0),t0); }
    // assemble the cycle from cached sweeps
    int az=a0; I bb=B; int z0=(a0==22),m0=(int)B&3; I D=0,L=0; int hops=0; Slot*cy[8]; I Bs[8]; int closed=0;
    while(hops<8){ int z=(az==22),m=(int)bb&3; Slot*s=&slot[z][m];
      { int seen=0; for(int i=0;i<hops;i++) if(cy[i]==s) seen=1; if(seen) break; } // a repeat that is not the first hop: no cycle through it
      if(!s->e.valid||bb>s->e.hi){ NCUR=0; Elem*sw=CUR; CUR=s->el; int r=walk(az,bb,&s->e,&ha,&hb); s->nel=NCUR; Elem*tmp=CUR; CUR=sw; (void)tmp; walks++;
        if(r<0){ // halting or no-reset state met at (az,bb): replay earlier hops then report
          for(int i=0;i<hops;i++){ note_sweep(cy[i],cy[i]->e.na0*0+((i==0?a0:cy[i-1]->e.na0)==22),bl(Bs[i]),Bs[i]-cy[i]->e.B0,n,Bs[i]); n+=cy[i]->e.len; }
          n+=s->e.len; { char s4[64]; printf("%s at n=%s a=%s b=%s from reset a0=%d B=%s\n",r==HALTED?"HALT":"NORESET",ps(n,s1),ps(ha,s2),ps(hb,s3),az,ps(bb,s4)); } a0=az;B=bb; stop=1; break; } }
      cy[hops]=s;Bs[hops]=bb;hops++; D+=s->e.delta; L+=s->e.len; bb+=s->e.delta; az=s->e.na0;
      if(az==a0&&((int)bb&3)==m0){ closed=1; break; }
    }
    if(stop) break;
    I T=0;
    if(closed){ T=(((U)1<<sc)-1-B)/D; for(int i=0;i<hops;i++){ I q=(cy[i]->e.hi-Bs[i])/D; if(q<T) T=q; } if(T<0)T=0; } 
    else hops=1,D=cy[0]->e.delta,L=cy[0]->e.len;
    I Tt=closed?T+1:1; // whole cycles taken
    if(wq){ // truncate at watched target so it can be tested exactly
      while(WB<B){ wno++; printf("NOT-VISITED a0=%d B=%s\n",wa,ps(WB,s1)); if(fscanf(wq,"%d %79s",&wa,wb)==2) WB=parseI(wb); else {WB=(I)1<<125;} }
      I endB=B+Tt*D;
      while(WB<endB){ int hit=0; for(int i=0;i<hops;i++){ int aa=(i==0)?a0:cy[i-1]->e.na0; if(aa==wa&&WB>=Bs[i]&&(WB-Bs[i])%D==0&&(WB-Bs[i])/D<Tt) hit=1; }
        if(hit) wyes++; else wno++; printf("%s a0=%d B=%s\n",hit?"VISITED":"NOT-VISITED",wa,ps(WB,s1));
        if(fscanf(wq,"%d %79s",&wa,wb)==2) WB=parseI(wb); else WB=(I)1<<125; }
      if(WB==(I)1<<125&&feof(wq)&&wq){ fclose(wq); wq=0; printf("watch list done yes=%lld no=%lld\n",wyes,wno); stop=2; }
    }
    // closest approach is at the first and last repeat of each word position: |d| is affine with a fixed sign in t.
    I W=L; I off=0; for(int i=0;i<hops;i++){ Slot*s=cy[i]; int z=((i==0?a0:cy[i-1]->e.na0)==22);
      note_sweep(s,z,sc,Bs[i]-s->e.B0,n+off,Bs[i]);
      if(Tt>1) note_sweep(s,z,sc,Bs[i]+T*D-s->e.B0,n+T*W+off,Bs[i]+T*D);
      off+=s->e.len; }
    n+=Tt*L; B+=Tt*D; az=(closed?a0:cy[0]->e.na0); a0=az; phases++; ph_sc[sc]++; sweeps+=hops; sw_sc[sc]+=hops;
    if(sf&&(phases%every)==0) fprintf(sf,"%s %d %s\n",ps(n,s1),a0,ps(B,s2));
    if(a0==6&&0){}
  }
  ckwrite(ck,a0,B); if(sf) fclose(sf);
  dump(stdout); printf("final n=%s a0=%d B=%s Bbits=%d phases=%lld sweeps=%lld walks=%lld stop=%d t=%.0f\n",ps(n,s1),a0,ps(B,s2),bl(B),phases,sweeps,walks,stop,difftime(time(0),t0));
  return 0; }
