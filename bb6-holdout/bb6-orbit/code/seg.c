// Fast orbit segment runner. Runs one exact stretch of the orbit from reset state (a0,B) to the reset state (a1,Y), which it
// must land on, and reports applications, phases and closest approach per scale. Same lemma as core.h, with one addition:
// consecutive sweeps in one residue slot share their word prefix, so a sweep re-walks only from the first element whose
// guard no longer holds. Each element's d=b-a-3 is affine with fixed sign while the element lives, so |d| is extreme at its
// first and last visit, and both are recorded.
// usage: seg A0 B A1 Y outfile [samplefile]
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <signal.h>
#include <unistd.h>
#include "core.h"
static volatile sig_atomic_t STOP=0; static void on_term(int s){ (void)s; STOP=1; }
#define MAXLV 2048
typedef struct { I a,b,ga,gb,hi,base,cU0,cU1,cW0,cW1; } Lev;
typedef struct { Lev *lv; int nlev,valid; I hi,delta; int na0,k,len; I lastB,lastn; int sc; I Bfirst;
  I fbase,U0,U1,W0,W1,ae,be,gae,gbe; int ca2,cb2; } Slot; // cost of one sweep times 6: CH + 4*B*U(y) + W(y) + ca2*ae(y)^2 + cb2*be(y)^2, y=B-fbase
static Slot slot[2][4];
typedef struct { I dpos,npos,apos,bpos,dneg,nneg,aneg,bneg; } Best;
static Best best[IBITS]; static long long ph_sc[IBITS],sw_sc[IBITS]; static I n=0; static long long phases=0,sweeps=0,letters=0,reused=0;
static long long slowT=0; static int halted=0; static I HA,HB,HN;
// 6*(raw steps): cost(letter) = Phi(a')-Phi(a)+R(letter) with Phi(a)=a^2/3, so 6*steps = 2*(a_end^2-a_start^2) + sum of 6R.
// 6R: D -30a+18; u 4bs-11a+29b+13; v 4bs-19a+37b-29; w 2a^2+6b^2+39a-9b+378; x 2a^2+6b^2+39a-9b+274;
//     p 2a^2+39a+354; q 2a^2+39a+250; r 2a^2+63a+774; s a+136; t 8a^2+30a+174. s=a+b.
typedef signed _BitInt(640) W; static W HALTCOST=0; static I CHT[2][IBITS];
// 384-bit two's complement accumulator with fast products; the total stays under 2^380 for B below 2^120.
typedef struct { u64 l[6]; } V;
static V ACC;
static inline V v_ext(I x){ V r; r.l[0]=(u64)x; r.l[1]=(u64)((unsigned __int128)x>>64); u64 sg=x<0?~0ULL:0; for(int i=2;i<6;i++) r.l[i]=sg; return r; }
static inline void v_addto(V*a,const V*b){ unsigned char c=0; for(int i=0;i<6;i++) c=__builtin_add_overflow(a->l[i],b->l[i],&a->l[i])|(__builtin_add_overflow(a->l[i],(u64)c,&a->l[i])); }
static inline V v_mul(I x,I y){ int neg=(x<0)^(y<0); unsigned __int128 X=x<0?-(unsigned __int128)x:(unsigned __int128)x,Y=y<0?-(unsigned __int128)y:(unsigned __int128)y;
  u64 xl=X,xh=X>>64,yl=Y,yh=Y>>64; unsigned __int128 ll=(unsigned __int128)xl*yl,lh=(unsigned __int128)xl*yh,hl=(unsigned __int128)xh*yl,hh=(unsigned __int128)xh*yh;
  unsigned __int128 mid=(ll>>64)+(u64)lh+(u64)hl; unsigned __int128 hi=hh+(lh>>64)+(hl>>64)+(mid>>64);
  V r; r.l[0]=(u64)ll; r.l[1]=(u64)mid; r.l[2]=(u64)hi; r.l[3]=(u64)(hi>>64); r.l[4]=0; r.l[5]=0;
  if(neg){ unsigned char c=1; for(int i=0;i<6;i++){ u64 t=~r.l[i]; c=__builtin_add_overflow(t,(u64)c,&r.l[i]); } } return r; }
static inline V v_mulu(const V*a,u64 m){ V r; unsigned __int128 carry=0; for(int i=0;i<6;i++){ unsigned __int128 t=(unsigned __int128)a->l[i]*m+carry; r.l[i]=(u64)t; carry=t>>64; } return r; }
static inline void v_add_W(V*a,W w){ u64 t[10]; unsigned _BitInt(640) u=(unsigned _BitInt(640))w; memcpy(t,&u,sizeof t); V b; for(int i=0;i<6;i++) b.l[i]=t[i]; v_addto(a,&b); }
static char *v_dec(V a,char*out){ // decimal of two's complement 384-bit
  unsigned _BitInt(640) u=0; int neg=(a.l[5]>>63)&1; if(neg){ unsigned char c=1; for(int i=0;i<6;i++){ u64 t=~a.l[i]; c=__builtin_add_overflow(t,(u64)c,&a.l[i]); } }
  for(int i=5;i>=0;i--) u=(u<<64)|a.l[i]; char t[300]; int q=0; if(u==0) t[q++]='0'; while(u>0){ t[q++]='0'+(int)(u%10); u/=10; } int n=0; if(neg) out[n++]='-'; while(q) out[n++]=t[--q]; out[n]=0; return out; }

static inline void note(int sc,I d,I a,I b,I nn){ if(__builtin_expect((u64)((U)d>>64)+1>1,1)) return; Best*x=&best[sc];
  if(d>=0){ if(d<x->dpos){x->dpos=d;x->npos=nn;x->apos=a;x->bpos=b;} }
  else { I e=-d; if(e<x->dneg){x->dneg=e;x->nneg=nn;x->aneg=a;x->bneg=b;} } }
static inline void drop_note(Slot*s,int j){ Lev*l=&s->lv[j]; I x=s->lastB-l->base; I a=l->a+l->ga*x,b=l->b+l->gb*x; note(s->sc,b-a-3,a,b,s->lastn+s->k+j); }
static void flush_slots(void){ for(int z=0;z<2;z++) for(int m=0;m<4;m++){ Slot*s=&slot[z][m]; if(s->valid){ for(int j=0;j<s->nlev;j++) drop_note(s,j); } s->valid=0; s->nlev=0; } }
// Prepare slot for B. Returns 0, or HALTED/NORESET.
static int prep(Slot*s,int a0,I B,I nnow,int sc){
  if(s->valid&&B<=s->hi&&s->sc==sc) return 0;
  int L=0; int z=(a0==22);
  if(s->valid&&s->sc==sc){ L=s->nlev; while(L>0&&B>s->lv[L-1].hi){ L--; drop_note(s,L); } }
  else if(s->valid){ for(int j=0;j<s->nlev;j++) drop_note(s,j); }
  reused+=L;
  I a,b,ga,gb,hi; int k; I U0=0,U1=0,W0=0,W1=0; int ca2=0,cb2=0; I ea=0,eb=0,ega=0,egb=0;
  if(L>0){ Lev*p=&s->lv[L-1]; I dl=B-p->base; U0=p->cU0+p->cU1*dl; U1=p->cU1; W0=p->cW0+p->cW1*dl; W1=p->cW1; }
  if(L==0){ k=kfor(z,B); s->k=k; a=AK[z][k]; b=B-SK[z][k]; ga=0; gb=1; hi=ICAP;
    if(k>0) note(sc,b,AK[z][k-1],b+AK[z][k-1]+3,nnow+k-1); }
  else { Lev*l=&s->lv[L]; I x=B-l->base; a=l->a+l->ga*x; b=l->b+l->gb*x; ga=l->ga; gb=l->gb; hi=s->lv[L-1].hi; k=s->k; }
  int j=L; int sing=0; int len=k+L;
  #define BOUND(g,sl) do{ I sl_=(sl); if(sl_<0){ I g_=(g); if(g_<-sl_) hi=B; else { I q=g_/(-sl_); if(B+q<hi) hi=B+q; } } }while(0)
  for(;;){
    I d=b-a-3; I na,nb,nga=0,ngb=0; int term=0;
    if(!sing){ if(j>=MAXLV-1){ HA=a;HB=b; return NORESET; } Lev*l=&s->lv[j]; l->a=a;l->b=b;l->ga=ga;l->gb=gb;l->base=B; }
    note(sc,d,a,b,nnow+len);
    if(d==0){ HA=a;HB=b;HN=nnow+len; HALTCOST=(W)U0*4*(W)B+(W)W0+(W)CHT[z][k]; return HALTED; }
    if(len-k>TAILCAP){ HA=a;HB=b; return NORESET; }
    if(d>0){ if(!sing){ BOUND(d-1,gb-ga); nga=2*ga; ngb=gb-ga; W1+=-30*ga; } na=2*a+6; nb=d; W0+=-30*a+18; }
    else if(b==1||b==3){ hi=B; ea=a;eb=b;ega=0;egb=0; cb2=0; ca2=2;
      if(b==1){ if(((int)a&3)==2){na=6;nb=a+7;W0+=39*a+354;} else {na=22;nb=a-2;W0+=39*a+250;} }
      else { if(((int)a&3)==2){na=6;nb=a+13;W0+=63*a+774;} else {na=a+8;nb=2;W0+=a+136;ca2=0;} } }
    else if((int)b&1){ if(b==a+1){ hi=B; na=6; nb=a+b+2; ea=a;eb=b;ega=0;egb=0;ca2=8;cb2=0;W0+=30*a+174; }
      else { I off=a+b-B; if(!sing){ BOUND(b-5,gb); BOUND(a-1-b,ga-gb); nga=ga-gb; ngb=2*gb; U1+=gb; }
        U0+=b;
        if(((int)(a-b+5)&3)==2){na=a-b+11;nb=2*b-4; W0+=4*off*b-11*a+29*b+13; if(!sing) W1+=4*off*gb-11*ga+29*gb; }
        else {na=a-b+19;nb=2*b-8; W0+=4*off*b-19*a+37*b-29; if(!sing) W1+=4*off*gb-19*ga+37*gb; } } }
    else { if(!sing){ BOUND(b-2,gb); BOUND(a+2-b,ga-gb); W1+=39*ga-9*gb; }
      ea=a;eb=b;ega=sing?0:ga;egb=sing?0:gb;ca2=2;cb2=6;
      if(((int)(a-b)&3)==2){na=6;nb=a+b+7;W0+=39*a-9*b+378;} else {na=22;nb=a+b-2;W0+=39*a-9*b+274;} }
    if(!sing){ Lev*l=&s->lv[j]; l->hi=hi; l->cU0=U0;l->cU1=U1;l->cW0=W0;l->cW1=W1; j++; if(hi==B) sing=1; }
    len++; letters++; a=na;b=nb;ga=nga;gb=ngb;
    if(a==6||a==22) break;
  }
  s->fbase=B;s->U0=U0;s->U1=U1;s->W0=W0;s->W1=W1;s->ae=ea;s->be=eb;s->gae=ega;s->gbe=egb;s->ca2=ca2;s->cb2=cb2;
  s->nlev=j; s->hi=hi; s->delta=b-B; s->na0=(int)a; s->len=len; s->valid=1; s->sc=sc; s->lastB=B; s->lastn=nnow;
  return 0; }

static inline void cost1(Slot*s,int z,I B){ I y=B-s->fbase; I U=s->U0+s->U1*y; I Wv=s->W0+s->W1*y+CHT[z][s->k];
  V t=v_ext(Wv); v_addto(&ACC,&t); V p=v_mul(B,U); p=v_mulu(&p,4); v_addto(&ACC,&p);
  if(s->ca2){ I x=s->ae+s->gae*y; p=v_mul(x,x); p=v_mulu(&p,s->ca2); v_addto(&ACC,&p); } if(s->cb2){ I x=s->be+s->gbe*y; p=v_mul(x,x); p=v_mulu(&p,s->cb2); v_addto(&ACC,&p); } }
// Sum over t=0..T-1 of the quadratic in t obtained from B+tD: c0*T + c1*T(T-1)/2 + c2*(T-1)T(2T-1)/6.
static void costT(Slot*s,int z,I B,I D,I T){ I y=B-s->fbase; I U0=s->U0+s->U1*y,U1=s->U1,W0=s->W0+s->W1*y+CHT[z][s->k],W1=s->W1,ae=s->ae+s->gae*y,gae=s->gae,be=s->be+s->gbe*y,gbe=s->gbe; int ca=s->ca2,cb=s->cb2;
  if(T<((I)1<<20)&&D<((I)1<<31)){ u64 Tu=(u64)T,s1=Tu*(Tu-1)/2,s2=(Tu-1)*Tu*(2*Tu-1)/6; V p,q;
    V c0=v_ext(W0); p=v_mul(B,U0); p=v_mulu(&p,4); v_addto(&c0,&p); if(ca){ p=v_mul(ae,ae); p=v_mulu(&p,ca); v_addto(&c0,&p); } if(cb){ p=v_mul(be,be); p=v_mulu(&p,cb); v_addto(&c0,&p); }
    V c1=v_ext(4*U0+W1); p=v_mul(B,U1); p=v_mulu(&p,4); v_addto(&c1,&p); if(ca){ p=v_mul(ae,gae); p=v_mulu(&p,2*ca); v_addto(&c1,&p); } if(cb){ p=v_mul(be,gbe); p=v_mulu(&p,2*cb); v_addto(&c1,&p); }
    c1=v_mulu(&c1,(u64)D);
    V c2=v_ext(4*U1); if(ca){ p=v_mul(gae,gae); p=v_mulu(&p,ca); v_addto(&c2,&p); } if(cb){ p=v_mul(gbe,gbe); p=v_mulu(&p,cb); v_addto(&c2,&p); }
    c2=v_mulu(&c2,(u64)D*(u64)D);
    q=v_mulu(&c0,Tu); v_addto(&ACC,&q); q=v_mulu(&c1,s1); v_addto(&ACC,&q); q=v_mulu(&c2,s2); v_addto(&ACC,&q); return; }
  W wU0=U0,wU1=U1,wW0=W0,wW1=W1,wae=ae,wgae=gae,wbe=be,wgbe=gbe,BB=B,DD=D,TT=T,wca=ca,wcb=cb;
  W c0=4*BB*wU0+wW0+wca*wae*wae+wcb*wbe*wbe; W c1=DD*(4*BB*wU1+4*wU0+wW1+2*wca*wae*wgae+2*wcb*wbe*wgbe); W c2=DD*DD*(4*wU1+wca*wgae*wgae+wcb*wgbe*wgbe);
  W s1=TT*(TT-1)/2, s2=(TT-1)*TT*(2*TT-1)/6; v_add_W(&ACC,c0*TT+c1*s1+c2*s2); }
static long long SAMPLE_MASK=0xFFFFFF; static double CK_SECS=300;
int main(int ac,char**av){ if(getenv("SEG_SAMPLE_MASK")) SAMPLE_MASK=atoll(getenv("SEG_SAMPLE_MASK")); if(getenv("SEG_CK_SECS")) CK_SECS=atof(getenv("SEG_CK_SECS")); signal(SIGTERM,on_term); signal(SIGINT,on_term); core_init(); { for(int z=0;z<2;z++){ I acc=0; CHT[z][0]=0; for(int k=1;k<IBITS;k++){ if(AK[z][k-1]>=ICAP){ CHT[z][k]=0; continue; } acc+=-30*AK[z][k-1]+18; CHT[z][k]=acc; } } } static char s1[IBITS],s2[IBITS],s3[IBITS],s4[IBITS];
  int a0=atoi(av[1]); I B=parseI(av[2]); int a1=atoi(av[3]); I Y=parseI(av[4]); char outt[600]; snprintf(outt,600,"%s.partial",av[5]); FILE*out=0; FILE*sf=ac>6?fopen(av[6],"a"):0;
  for(int z=0;z<2;z++) for(int m=0;m<4;m++) slot[z][m].lv=malloc(sizeof(Lev)*MAXLV);
  for(int i=0;i<IBITS;i++) best[i].dpos=best[i].dneg=(I)1<<(IBITS-4);
  I B0=B; int a00=a0; time_t t0=time(0); int status=0;
  char ck[600]; snprintf(ck,600,"%s.ck",av[5]); time_t lastck=t0; double prior=0;
  { FILE*c=fopen(ck,"rb"); if(c){ size_t k=fread(&a0,sizeof a0,1,c);k+=fread(&B,sizeof B,1,c);k+=fread(&n,sizeof n,1,c);k+=fread(&ACC,sizeof ACC,1,c);k+=fread(&phases,8,1,c);k+=fread(&sweeps,8,1,c);k+=fread(&letters,8,1,c);k+=fread(&reused,8,1,c);k+=fread(&slowT,8,1,c);k+=fread(best,sizeof best,1,c);k+=fread(ph_sc,sizeof ph_sc,1,c);k+=fread(sw_sc,sizeof sw_sc,1,c);k+=fread(&prior,8,1,c);fclose(c); if(k!=13){ fprintf(stderr,"bad checkpoint\n"); return 3; } } }
  int lastsc=bl(B);
  while(B<Y){
    int sc=bl(B); if(sc!=lastsc){ flush_slots(); lastsc=sc; }
    if((phases&0xFFFFF)==0){ time_t now=time(0); if(STOP||difftime(now,lastck)>=CK_SECS){ lastck=now; flush_slots(); char t[620]; snprintf(t,620,"%s.tmp",ck); FILE*c=fopen(t,"wb"); if(c){ double el=prior+difftime(now,t0); fwrite(&a0,sizeof a0,1,c);fwrite(&B,sizeof B,1,c);fwrite(&n,sizeof n,1,c);fwrite(&ACC,sizeof ACC,1,c);fwrite(&phases,8,1,c);fwrite(&sweeps,8,1,c);fwrite(&letters,8,1,c);fwrite(&reused,8,1,c);fwrite(&slowT,8,1,c);fwrite(best,sizeof best,1,c);fwrite(ph_sc,sizeof ph_sc,1,c);fwrite(sw_sc,sizeof sw_sc,1,c);fwrite(&el,8,1,c);fflush(c);fsync(fileno(c));fclose(c);rename(t,ck); if(sf) { fflush(sf); fsync(fileno(sf)); } } if(STOP){ fprintf(stderr,"stopped by signal, checkpoint written\n"); return 143; } } }
    int az=a0; I bb=B; int m0=(int)B&3; I D=0,L=0; int hops=0; Slot*cy[8]; I Bs[8]; int ks[8]; int closed=0; int bad=0;
    while(hops<8){ int z=(az==22),m=(int)bb&3; Slot*s=&slot[z][m]; int seen=0; for(int i=0;i<hops;i++) if(cy[i]==s) seen=1; if(seen) break;
      if(hops>0&&bl(bb)!=sc) break;
      int r=prep(s,az,bb,n+L,sc);
      if(r<0){ if(hops==0){ status=r; bad=1; if(r==HALTED) v_add_W(&ACC,HALTCOST); } break; }
      cy[hops]=s;Bs[hops]=bb;ks[hops]=az;hops++; D+=s->delta; L+=s->len; bb+=s->delta; az=s->na0;
      if(az==a0&&((int)bb&3)==m0){ closed=1; break; } }
    if(bad) break;
    I take=1;
    if(closed){ I T=ICAP; for(int i=0;i<hops;i++){ I g=cy[i]->hi-Bs[i]; I q=g<D?0:g/D; if(q<T) T=q; }
      I lim=(I)((U)1<<sc); if(Y<lim) lim=Y; I space=lim-B;
      if(space<D) closed=0; else if(T==0) take=1; else { I room=space/D; take=T+1<room?T+1:room; } }
    if(!closed){ Slot*s=cy[0]; D=s->delta; L=s->len; hops=1; az=s->na0; s->lastB=B; s->lastn=n; cost1(s,ks[0]==22,B); n+=L; B+=D; a0=az; }
    else { I off=0; for(int i=0;i<hops;i++){ cy[i]->lastB=Bs[i]+(take-1)*D; cy[i]->lastn=n+(take-1)*L+off; off+=cy[i]->len; if(take==1) cost1(cy[i],ks[i]==22,Bs[i]); else { costT(cy[i],ks[i]==22,Bs[i],D,take); slowT++; } } n+=take*L; B+=take*D; }
    phases++; ph_sc[sc]++; sweeps+=hops; sw_sc[sc]+=hops;
    if(sf&&(phases&SAMPLE_MASK)==0){ fprintf(sf,"%s %d %s\n",ps(n,s1),a0,ps(B,s2)); fflush(sf); }
  }
  flush_slots(); out=fopen(outt,"w");
  int ok=(status==0&&B==Y&&a0==a1);
  fprintf(out,"seg start %d %s end %d %s want %d %s status %d ok %d apps %s phases %lld sweeps %lld letters %lld reused %lld slowT %lld secs %.0f\n",a00,ps(B0,s1),a0,ps(B,s2),a1,ps(Y,s3),status,ok,ps(n,s4),phases,sweeps,letters,reused,slowT,prior+difftime(time(0),t0));
  { char big[300]; v_dec(ACC,big); fprintf(out,"sum6R %s\n",big); }
  if(status==HALTED) fprintf(out,"halt a %s b %s offset_n %s\n",ps(HA,s1),ps(HB,s2),ps(HN,s3));
  if(status==NORESET) fprintf(out,"noreset a %s b %s\n",ps(HA,s1),ps(HB,s2));
  for(int i=0;i<IBITS;i++){ if(ph_sc[i]==0&&best[i].dpos==(I)1<<(IBITS-4)&&best[i].dneg==(I)1<<(IBITS-4)) continue;
    fprintf(out,"scale %d +d %s offn %s a %s b %s",i,ps(best[i].dpos,s1),ps(best[i].npos,s2),ps(best[i].apos,s3),ps(best[i].bpos,s4));
    fprintf(out," -d %s offn %s a %s b %s phases %lld sweeps %lld\n",ps(best[i].dneg,s1),ps(best[i].nneg,s2),ps(best[i].aneg,s3),ps(best[i].bneg,s4),ph_sc[i],sw_sc[i]); }
  fclose(out); rename(outt,av[5]); if(ok||status==HALTED) remove(ck); return ok?0:1; }
