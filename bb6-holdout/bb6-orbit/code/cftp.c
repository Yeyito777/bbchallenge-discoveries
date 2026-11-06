// History-free computation of the orbit. All reset states with B in [X,X+W) are advanced, lowest B first, and identical
// states are dropped. The sweep map is deterministic, so once one state remains, any orbit that lands in the window
// passes through it. Window width W must exceed the largest sweep increment that can jump over it.
// usage: cftp merge X W Ymax          run until merged; print merged state and cost
//        cftp event a0 B W            find a short lookback that merges; is (a0,B) on the merged path?
//        cftp scan kmin kmax W pairs  enumerate halting and sink-entry states at each level, test each
#include <stdio.h>
#include <stdlib.h>
#include "core.h"
typedef struct{int a0;I B;Cache*c;}C;
static long long phases=0,walks=0;
static int advance(C*x,I Y){
  int a0=x->a0;I B=x->B;I ha,hb; int k0=(int)B&3;
  I Bs[8]; Entry*es[8]; int hops=0; int az=a0;I bb=B; I D=0; int closed=0;
  while(hops<8){ int z=az==22,m=(int)bb&3; Entry*e=&x->c->e[z][m];
    int seen=0; for(int i=0;i<hops;i++) if(es[i]==e) seen=1; if(seen) break;
    if(!e->valid||bb>e->hi){ int r=walk(az,bb,e,&ha,&hb); walks++; if(r<0){ if(hops==0){ x->a0=az;x->B=bb; return r; } break; } }
    Bs[hops]=bb;es[hops]=e;hops++; D+=e->delta; bb+=e->delta; az=e->na0;
    if(az==a0&&((int)bb&3)==k0){ closed=1; break; }
  }
  phases++;
  if(closed){ I T=ICAP; for(int i=0;i<hops;i++){ I q=(es[i]->hi-Bs[i])/D; if(q<T)T=q; } if(T<0)T=0;
    I room=(Y-B)/D; // whole cycles that stay at or below Y
    if(room>=1){ I take=T+1<room?T+1:room; x->B=B+take*D; return 0; } }
  x->a0=es[0]->na0; x->B=B+es[0]->delta; return 0;
}
static C *pool=0; static int cap=0;
typedef struct { int n,aborted,hit,stopped,stopkind,stopa0,ma0; I mergeB,stopB; long long cost; } Res;
static int cmpC(const void*p,const void*q){ const C*a=p,*b=q; if(a->B<b->B) return -1; if(a->B>b->B) return 1; return a->a0-b->a0; }
static int STOP_ON_MERGE=0;
static Res run(I X,int W,I Y,int ea0,I eB,long long budget){
  Res R; memset(&R,0,sizeof R); R.mergeB=-1; long long p0=phases;
  int n=0; if(cap<2*W){ pool=realloc(pool,sizeof(C)*2*W); for(int i=cap;i<2*W;i++) pool[i].c=malloc(sizeof(Cache)); cap=2*W; }
  for(int i=0;i<W;i++) for(int z=0;z<2;z++){ pool[n].a0=z?22:6;pool[n].B=X+i;memset(pool[n].c,0,sizeof(Cache));n++; }
  C*c=pool;
  // one sweep for everyone, then sort-and-unique: almost all starts collapse onto the reachable residue classes
  { int o=0; for(int i=0;i<n;i++){ if(c[i].B<Y){ int r=advance(&c[i],Y); if(r<0){ R.stopped++; R.stopkind=r; R.stopa0=c[i].a0; R.stopB=c[i].B; continue; } }
      if(o!=i){ C t=c[o]; c[o]=c[i]; c[i]=t; } o++; }
    n=o; qsort(c,n,sizeof(C),cmpC); o=0; for(int i=0;i<n;i++){ if(o>0&&c[o-1].B==c[i].B&&c[o-1].a0==c[i].a0) continue; if(o!=i){ C t=c[o]; c[o]=c[i]; c[i]=t; } o++; } n=o; }
  if(n==1&&R.stopped==0){ R.mergeB=c[0].B; R.ma0=c[0].a0; }
  while(1){
    if(phases-p0>budget){ R.aborted=1; break; }
    int m=-1; for(int i=0;i<n;i++) if(c[i].B<Y&&(m<0||c[i].B<c[m].B)) m=i;
    if(m<0) break;
    int r=advance(&c[m],Y);
    if(r<0){ R.stopped++; R.stopkind=r; R.stopa0=c[m].a0; R.stopB=c[m].B; C t=c[m]; c[m]=c[n-1]; c[n-1]=t; n--; continue; }
    for(int i=0;i<n;i++) if(i!=m&&c[i].B==c[m].B&&c[i].a0==c[m].a0){ C t=c[m]; c[m]=c[n-1]; c[n-1]=t; n--; break; }
    if(n==1&&R.mergeB<0&&R.stopped==0){ R.mergeB=c[0].B; R.ma0=c[0].a0; if(STOP_ON_MERGE) break; }
  }
  R.n=n; for(int i=0;i<n;i++) if(c[i].a0==ea0&&c[i].B==eB) R.hit++;
  R.cost=phases-p0; return R;
}
// Does the merged path visit e? 1 yes, 0 no, -1 undecided. The lookback is searched: it must reach far enough back to merge,
// and no further than the budget, since the phase count from X to e is the cost.
static int test_event(int a0,I eB,int W,I *lb,long long*cost,int*left,long long budget){
  long long p0=phases; I lo=-1,hi=-1; I L=(I)1<<8; int iters=0;
  while(iters++<4000){
    if(L>=eB-W-8) { L=eB-W-8; }
    I X=eB-L-W; Res R=run(X,W,eB,a0,eB,budget);
    *left=R.n; *cost=phases-p0;
    if(!R.aborted&&R.n==1&&R.stopped==0&&R.mergeB>=0){ *lb=L; return R.hit?1:0; }
    if(R.aborted){ hi=L; } else { lo=L; if(L>=eB-W-8) return -1; }
    if(hi<0) L=L*2;
    else { if(lo<0) lo=0; if(hi-lo<=1) { *lb=L; return -1; } L=lo+(hi-lo)/2; }
  }
  return -1; }
// Upper boundaries of the word prefixes of the sweep from (a0,B): the B at which each guard along the word first fails.
static int boundaries(int a0,I B,I*out,int cap){ int z=a0==22,k=kfor(z,B); I a=AK[z][k],b=B-SK[z][k],ga=0,gb=1; int n=0;
  for(int steps=0;steps<400&&n<cap;steps++){ I d=b-a-3; if(d==0||b==1||b==3||b==a+1) break; I na,nb,nga,ngb;
    #define CONSIDER(g_,s_) do{ I s2=(s_); if(s2<0){ I q=(g_)/(-s2); if(n<cap) out[n++]=B+q; } }while(0)
    if(d>0){ CONSIDER(d-1,gb-ga); na=2*a+6;nb=d;nga=2*ga;ngb=gb-ga; }
    else if((int)b&1){ CONSIDER(b-5,gb); CONSIDER(a-1-b,ga-gb); nga=ga-gb;ngb=2*gb; if(((int)(a-b+5)&3)==2){na=a-b+11;nb=2*b-4;} else {na=a-b+19;nb=2*b-8;} }
    else { CONSIDER(b-2,gb); CONSIDER(a+2-b,ga-gb); break; }
    a=na;b=nb;ga=nga;gb=ngb; if(a==6||a==22) break; }
  return n; }
typedef struct { int a0,kind,k,depth; I B; } Ev;
static Ev *evs; static int nev=0,evcap=0;
static int kk,zz,A00;
static void addev(int kind,I B,int depth){ if(B<7) return; I ha,hb; Entry e; int r=walk(A00,B,&e,&ha,&hb);
  int ok=0; if(kind==0&&r==HALTED) ok=1; if(kind==1&&r==NORESET) ok=1; if(!ok) return;
  for(int i=0;i<nev;i++) if(evs[i].B==B&&evs[i].kind==kind) return;
  if(nev==evcap){ evcap=evcap?evcap*2:1024; evs=realloc(evs,sizeof(Ev)*evcap); }
  evs[nev].a0=A00;evs[nev].kind=kind;evs[nev].k=kk;evs[nev].depth=depth;evs[nev].B=B;nev++; }
// a = ga*B+ca, b = gb*B+cb at a state with b even (end of a pair). Halt form b=a+3 falls on odd b, sink form b=2a+18 on even b.
static void test_forms(I ga,I ca,I gb,I cb,int depth){
  I m=gb-ga,c=ca+3-cb; if(m!=0&&c%m==0) addev(0,c/m,depth);
  I m2=gb-2*ga,c2=2*ca+18-cb; if(m2!=0&&c2%m2==0) addev(1,c2/m2,depth); }
static void dfs(I ga,I ca,I gb,I cb,int depth,int maxd){ // state with b odd: next letter D, u or v, followed by a forced D
  test_forms(ga,ca,gb,cb,depth);
  if(depth>=maxd) return;
  for(int w=0;w<3;w++){ I ga1,ca1,gb1,cb1;
    if(w==0){ ga1=2*ga;ca1=2*ca+6;gb1=gb-ga;cb1=cb-ca-3; }
    else if(w==1){ ga1=ga-gb;ca1=ca-cb+11;gb1=2*gb;cb1=2*cb-4; }
    else { ga1=ga-gb;ca1=ca-cb+19;gb1=2*gb;cb1=2*cb-8; }
    test_forms(ga1,ca1,gb1,cb1,depth); // sink form on the even state
    I ga2=2*ga1,ca2=2*ca1+6,gb2=gb1-ga1,cb2=cb1-ca1-3;
    dfs(ga2,ca2,gb2,cb2,depth+1,maxd); } }
int main(int ac,char**av){ core_init(); static char s1[IBITS],s2[IBITS];
  if(ac>1&&!strcmp(av[1],"merge")){ I X=parseI(av[2]); int W=atoi(av[3]); I Y=parseI(av[4]); STOP_ON_MERGE=1;
    Res R=run(X,W,Y,0,0,1LL<<40); printf("n=%d a0=%d mergeB=%s phases=%lld walks=%lld\n",R.n,R.ma0,ps(R.mergeB,s1),phases,walks); return 0; }
  if(ac>1&&!strcmp(av[1],"near")){ // cftp near X W budget: merged state close after X, starting just below a word boundary above X
    I X=parseI(av[2]); int W=atoi(av[3]); long long budget=atoll(av[4]); STOP_ON_MERGE=1;
    static I cand[4096]; int nc=0;
    for(int z=0;z<2;z++){ int a0=z?22:6; I B=X; while(((int)B&3)!=(z?2:1)) B++; nc+=boundaries(a0,B,cand+nc,4000-nc); }
    for(int i=0;i<nc;i++) for(int j=i+1;j<nc;j++) if(cand[j]<cand[i]){ I t=cand[i];cand[i]=cand[j];cand[j]=t; }
    for(int i=0;i<nc;i++){ if(i&&cand[i]==cand[i-1]) continue; if(cand[i]<X) continue; for(int j=22;j<=40;j+=2){ I St=cand[i]-((I)1<<j); if(St<X) St=X; Res R=run(St,W,cand[i]+((I)1<<(j+2)),0,0,budget);
        if(R.mergeB>=0&&R.stopped==0&&!R.aborted){ printf("%d %s phases=%lld start=%s\n",R.ma0,ps(R.mergeB,s1),phases,ps(St,s2)); return 0; } if(R.aborted) break; } }
    printf("nomerge\n"); return 2; }
  if(ac>1&&!strcmp(av[1],"event")){ int a0=atoi(av[2]); I B=parseI(av[3]); int W=atoi(av[4]); int nl=0; long long cost=0; I lb=0;
    int r=test_event(a0,B,W,&lb,&cost,&nl,ac>5?atoll(av[5]):2000000); printf("result=%d lookback=%s phases=%lld left=%d\n",r,ps(lb,s1),cost,nl); return 0; }
  if(ac>1&&!strcmp(av[1],"scan")){ int kmin=atoi(av[2]),kmax=atoi(av[3]),W=atoi(av[4]),depth=atoi(av[5]); long long budget=ac>6?atoll(av[6]):2000000;
    for(kk=kmin;kk<=kmax;kk++) for(zz=0;zz<2;zz++){ A00=zz?22:6; nev=0;
      // level k end of chain: b = B - S_k. Sink form with b>=a+3 is at the chain itself; tail letter pairs follow an odd r.
      I ca=AK[zz][kk],cb=-SK[zz][kk];
      test_forms(0,ca,1,cb,0);
      dfs(0,ca,1,cb,0,depth);
      for(int i=0;i<nev;i++){ int nl=0; long long cost=0; I lb=0;
        int inclass=(evs[i].a0==6&&(int)(evs[i].B&3)==1)||(evs[i].a0==22&&(int)(evs[i].B&3)==2);
        if(!inclass){ printf("k=%d a0=%d %s pairs=%d B=%s offclass\n",kk,evs[i].a0,evs[i].kind?"SINK":"HALT",evs[i].depth,ps(evs[i].B,s1)); continue; }
        int r=test_event(evs[i].a0,evs[i].B,W,&lb,&cost,&nl,budget);
        printf("k=%d a0=%d %s pairs=%d B=%s result=%d lookback_bits=%d phases=%lld left=%d\n",kk,evs[i].a0,evs[i].kind?"SINK":"HALT",evs[i].depth,ps(evs[i].B,s1),r,bl(lb),cost,nl); fflush(stdout); } }
    return 0; }
  return 1; }
