// Gate 1: check the rule map against the raw Turing machine.
// For each (a,b): lay out 0^inf 1^a A> 1 1^b 0 1 0^inf on a real tape, run the raw TM, and require that
// the configuration predicted by the map appears (or a halt, for the halt branch). Prints raw step counts.
// usage: tm_check grid AMAX BMAX | rand N AMAX BMAX SEED | blank
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef long long ll;
// A:1RB0LF B:1RC1RA C:0RD0RB D:1LE--- E:0LA1LE F:1RD1LA
enum{A,B,C,D,E,F};
static const signed char W[6][2]={{1,0},{1,1},{0,0},{1,-1},{0,1},{1,1}};
static const signed char M[6][2]={{1,-1},{1,1},{1,1},{-1,0},{-1,-1},{1,-1}};
static const signed char N[6][2]={{B,F},{C,A},{D,B},{E,-1},{A,E},{D,A}};
static unsigned char *T; static ll TN;
static int branch(ll a,ll b,ll*pa,ll*pb){ // returns branch id; 0 = halt
  if(b==a+3) return 0;
  if(b>a+3){*pa=2*a+6;*pb=b-a-3;return 1;}
  if(b==1){ if(a%4==2){*pa=6;*pb=a+7;return 2;} *pa=22;*pb=a-2;return 3;}
  if(b==3){ if(a%4==2){*pa=6;*pb=a+13;return 4;} *pa=a+8;*pb=2;return 5;}
  if(b&1){ ll u=(a-b+5)/2; if(u==2){*pa=6;*pb=a+b+2;return 6;}
    if(u&1){*pa=a-b+11;*pb=2*b-4;return 7;} *pa=a-b+19;*pb=2*b-8;return 8;}
  ll h=(a-b)/2; if(h&1){*pa=6;*pb=a+b+7;return 9;} *pa=22;*pb=a+b-2;return 10;
}
// Run from A(a,b). Target: A(ta,tb) (or halt if ta<0). Returns raw steps or -1 on failure.
static ll run(ll a,ll b,ll ta,ll tb,ll lim,ll*firstother){
  ll need=2*(a+b+ta+tb)+4096;
  if(need>TN){ free(T); TN=need*2; T=calloc(TN,1); if(!T){puts("oom");exit(2);} }
  else memset(T,0,TN);
  ll pos=TN/2; ll p0=pos-a;
  for(ll i=0;i<a;i++) T[p0+i]=1;
  for(ll i=0;i<b+1;i++) T[pos+i]=1;
  T[pos+b+1]=0; T[pos+b+2]=1;
  ll ones=a+b+2; ll target=ta+tb+2; int s=A; ll n=0;
  while(n<lim){
    int c=T[pos];
    if(N[s][c]<0){ return ta<0? n : -1; }
    if(ta>=0 && s==A && c==1 && ones==target){
      // exact shape check: left of head exactly ta ones then all zero, right 1^(tb+1) 0 1 then zero
      ll i=pos-1,cnt=0; while(i>=0&&T[i]){cnt++;i--;}
      if(cnt==ta){ ll j=pos,c2=0; while(j<TN&&T[j]){c2++;j++;}
        if(c2==tb+1 && T[j+1]==1 && T[j+2]==0) return n; } // ones count guarantees no others
    }
    if(T[pos]!=W[s][c]){ ones+=W[s][c]-c; T[pos]=W[s][c]; }
    pos+=M[s][c]; s=N[s][c]; n++;
    if(pos<2||pos>=TN-2){ puts("tape edge"); return -2; }
  }
  return -3;
}
static ll fails=0,tests=0; static ll perbranch[11],costfail=0;
// Raw steps per rule, as polynomials. Doubled to stay integral.
static ll cost2(int k,ll a,ll b){ switch(k){ case 0:return 2*(a*a+7*a+41); case 1:return 2*(a*a+3*a+15); case 2:return 13*a+142; case 3:return 13*a+406; case 4:return 21*a+282; case 5:return 11*a+88;
  case 6:return 2*(a*a+5*a+41); case 7:return 2*b*b+11*a-5*b+85; case 8:return 2*b*b+19*a-13*b+231; case 9:return 2*b*b+13*a-3*b+150; default:return 2*b*b+13*a-3*b+414; } }
static void one(ll a,ll b,int verbose){
  ll pa=-1,pb=-1; int k=branch(a,b,&pa,&pb);
  ll lim=200*(a+b+50)*(a+b+50)+100000;
  ll r=run(a,b,k==0?-1:pa,pb,lim,0);
  tests++; perbranch[k]++;
  if(r<0){ fails++; printf("FAIL a=%lld b=%lld branch %d predicted (%lld,%lld) ret %lld\n",a,b,k,pa,pb,r); fflush(stdout);}
  else { if(2*r!=cost2(k,a,b)){ costfail++; printf("COST a=%lld b=%lld branch %d raw %lld poly %lld\n",a,b,k,r,cost2(k,a,b)/2); }
    if(verbose) printf("%d %lld %lld %lld %lld %lld\n",k,a,b,pa,pb,r); }
}
int main(int ac,char**av){
  TN=1<<22; T=calloc(TN,1);
  if(!strcmp(av[1],"blank")){
    // blank tape to A(6,1)
    ll pos=TN/2; int s=A; ll n=0;
    while(n<100000){ int c=T[pos];
      // shape check
      if(s==A&&c==1){ ll i=pos-1,cnt=0; while(T[i]){cnt++;i--;} ll j=pos,c2=0; while(T[j]){c2++;j++;}
        ll l=0; for(ll q=0;q<TN;q++) l+=T[q];
        if(l==cnt+c2+1 && T[j+1]==1){ printf("A(%lld,%lld) at raw step %lld\n",cnt,c2-1,n); if(cnt==6&&c2-1==1) return 0; } }
      if(N[s][c]<0){puts("halt");return 1;}
      T[pos]=W[s][c]; pos+=M[s][c]; s=N[s][c]; n++; }
    puts("not found"); return 1;
  }
  int verbose=getenv("VERBOSE")!=0;
  if(!strcmp(av[1],"grid")){ ll amax=atoll(av[2]),bmax=atoll(av[3]);
    for(ll a=6;a<=amax;a+=2) for(ll b=1;b<=bmax;b++) one(a,b,verbose);
  } else { ll cnt=atoll(av[2]),amax=atoll(av[3]),bmax=atoll(av[4]); srand48(atoll(av[5]));
    for(ll i=0;i<cnt;i++){ ll a=6+2*(lrand48()%(amax/2)); ll b;
      int mode=lrand48()%4;
      if(mode==0) b=1+lrand48()%bmax;
      else if(mode==1){ b=a+3+(lrand48()%41)-20; if(b<1)b=1; }
      else if(mode==2){ b=1+lrand48()%40; }
      else { b=a/3+(lrand48()%41)-20; if(b<1)b=1; }
      one(a,b,verbose);
    }
  }
  printf("tests %lld fails %lld costfails %lld; per branch:",tests,fails,costfail); for(int i=0;i<11;i++) printf(" %lld",perbranch[i]); puts("");
  return fails!=0;
}
