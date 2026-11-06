// Raw Turing machine from the blank tape, checked against the map and its step polynomials, no acceleration anywhere.
// At every rule application up to a raw-step limit the tape must be exactly A(a,b) at exactly the predicted step.
// usage: raw_prefix STEP_LIMIT
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <inttypes.h>
enum{A,B,C,D,E,F};
static const signed char W[6][2]={{1,0},{1,1},{0,0},{1,-1},{0,1},{1,1}},M[6][2]={{1,-1},{1,1},{1,1},{-1,0},{-1,-1},{1,-1}},N[6][2]={{B,F},{C,A},{D,B},{E,-1},{A,E},{D,A}};
typedef int64_t ll;
int main(int ac,char**av){ uint64_t lim=strtoull(av[1],0,10); ll TN=1LL<<30; unsigned char*T=calloc(TN,1); ll pos=TN/2,lo=pos,hi=pos; int s=A; uint64_t n=0,apps=0;
  for(;n<35;n++){ int c=T[pos]; T[pos]=W[s][c]; pos+=M[s][c]; s=N[s][c]; if(pos<lo)lo=pos; if(pos>hi)hi=pos; }
  ll a=6,b=1; uint64_t pred=35;
  while(pred<lim){
    while(n<pred){ int c=T[pos]; if(N[s][c]<0){ printf("unexpected halt at %" PRIu64 "\n",n); return 1; } T[pos]=W[s][c]; pos+=M[s][c]; s=N[s][c]; n++; if(pos<lo)lo=pos; if(pos>hi)hi=pos; if(pos<2||pos>=TN-2){puts("tape edge");return 2;} }
    ll i=pos-1,ca=0; while(T[i]){ca++;i--;} ll j=pos,cb=0; while(T[j]){cb++;j++;}
    int ok=(s==A&&T[pos]==1&&ca==a&&cb==b+1&&T[j+1]==1&&T[j+2]==0);
    if(ok){ for(ll q=lo-1;q<i&&ok;q++) if(T[q]) ok=0; for(ll q=j+2;q<=hi+1&&ok;q++) if(T[q]) ok=0; }
    if(!ok){ printf("MISMATCH app %" PRIu64 " step %" PRIu64 " want A(%" PRId64 ",%" PRId64 ") state %d left %" PRId64 " right %" PRId64 "\n",apps,n,a,b,s,ca,cb); return 1; }
    ll d=b-a-3; int64_t c2; ll na,nb;
    if(d==0){ printf("predicted halt\n"); return 1; }
    if(d>0){ c2=2*(a*a+3*a+15); na=2*a+6; nb=d; }
    else if(b==1){ if(a%4==2){c2=13*a+142;na=6;nb=a+7;} else {c2=13*a+406;na=22;nb=a-2;} }
    else if(b==3){ if(a%4==2){c2=21*a+282;na=6;nb=a+13;} else {c2=11*a+88;na=a+8;nb=2;} }
    else if(b&1){ if(b==a+1){c2=2*(a*a+5*a+41);na=6;nb=a+b+2;} else if(((a-b+5)/2)&1){c2=2*b*b+11*a-5*b+85;na=a-b+11;nb=2*b-4;} else {c2=2*b*b+19*a-13*b+231;na=a-b+19;nb=2*b-8;} }
    else { if(((a-b)/2)&1){c2=2*b*b+13*a-3*b+150;na=6;nb=a+b+7;} else {c2=2*b*b+13*a-3*b+414;na=22;nb=a+b-2;} }
    pred+=c2/2; a=na; b=nb; apps++;
  }
  printf("raw TM from blank: %" PRIu64 " applications, all exact, through raw step %" PRIu64 "; last A(%" PRId64 ",%" PRId64 ")\n",apps,n,a,b); return 0; }
