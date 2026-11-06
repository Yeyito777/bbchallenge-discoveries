// Plain rule-map iteration from A(6,1), one application at a time, 64-bit with overflow guard.
// Independent of the jumper. usage: brute MAXAPPS [checkfile]
// Prints near-diagonal records. With checkfile (lines "n a b", ascending n) verifies each one.
// Also prints per-bitlength(a+b) closest approach, for comparison against the jumper.
#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>
typedef int64_t ll; typedef uint64_t ull;
int main(int ac,char**av){
  ull maxn=strtoull(av[1],0,10); FILE*cf=ac>2?fopen(av[2],"r"):0;
  ull cn=0; ll ca=0,cb=0; int have=0; ull checked=0;
  if(cf&&fscanf(cf,"%" SCNu64 " %" SCNd64 " %" SCNd64,&cn,&ca,&cb)==3) have=1;
  ll a=6,b=1; ull n=0; ll best[80]; ull bn[80]; ll ba[80],bb[80];
  for(int i=0;i<80;i++) best[i]=INT64_MAX;
  ull sink=0;
  while(n<=maxn){
    if(have&&n==cn){ if(a!=ca||b!=cb){printf("MISMATCH n=%" PRIu64 " brute (%" PRId64 ",%" PRId64 ") file (%" PRId64 ",%" PRId64 ")\n",n,a,b,ca,cb);return 1;}
      checked++; if(fscanf(cf,"%" SCNu64 " %" SCNd64 " %" SCNd64,&cn,&ca,&cb)!=3) have=0; }
    ll d=b-a-3; ll ad=d<0?-d:d;
    int sc=64-__builtin_clzll((ull)(a+b));
    if(ad<best[sc]){best[sc]=ad;bn[sc]=n;ba[sc]=a;bb[sc]=b;}
    if(d==0){printf("HALT n=%" PRIu64 " a=%" PRId64 " b=%" PRId64 "\n",n,a,b);return 0;}
    if(a%4==2&&b==2*a+18&&a>6) {printf("SINK n=%" PRIu64 " a=%" PRId64 " b=%" PRId64 "\n",n,a,b);return 0;}
    if(d>0){a=2*a+6;b=d;}
    else if(b==1){ if(a%4==2){b=a+7;a=6;} else {b=a-2;a=22;} }
    else if(b==3){ if(a%4==2){b=a+13;a=6;} else {a=a+8;b=2;} }
    else if(b&1){ ll u=(a-b+5)/2; if(u==2){b=a+b+2;a=6;} else if(u&1){a=a-b+11;b=2*b-4;} else {a=a-b+19;b=2*b-8;} }
    else { if(((a-b)/2)&1){b=a+b+7;a=6;} else {b=a+b-2;a=22;} }
    n++;
    if(a>(1LL<<61)||b>(1LL<<61)){puts("overflow");return 2;}
  }
  printf("end n=%" PRIu64 " a=%" PRId64 " b=%" PRId64 " checked=%" PRIu64 " leftover=%d\n",n,a,b,checked,have);
  for(int i=0;i<80;i++) if(best[i]!=INT64_MAX) printf("scale %d mind %" PRId64 " n %" PRIu64 " a %" PRId64 " b %" PRId64 "\n",i,best[i],bn[i],ba[i],bb[i]);
  return 0;
}
