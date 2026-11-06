// Brute closest approach per scale, with scale = bit length of the B of the current sweep (the value at the last a in {6,22}).
#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>
typedef int64_t ll; typedef uint64_t ull;
int main(int ac,char**av){ ull maxn=strtoull(av[1],0,10); ll a=6,b=1; ull n=0; ll bp[80],bq[80]; ull np[80],nq[80]; ll ap[80],aq[80],bbp[80],bbq[80]; for(int i=0;i<80;i++) bp[i]=bq[i]=INT64_MAX; int sc=1;
  while(n<=maxn){ if(a==6||a==22) sc=64-__builtin_clzll((ull)b);
    ll d=b-a-3; if(d>=0){ if(d<bp[sc]){bp[sc]=d;np[sc]=n;ap[sc]=a;bbp[sc]=b;} } else { if(-d<bq[sc]){bq[sc]=-d;nq[sc]=n;aq[sc]=a;bbq[sc]=b;} }
    if(d==0){ puts("HALT"); return 0; }
    if(d>0){a=2*a+6;b=d;} else if(b==1){ if(a%4==2){b=a+7;a=6;} else {b=a-2;a=22;} } else if(b==3){ if(a%4==2){b=a+13;a=6;} else {a=a+8;b=2;} }
    else if(b&1){ ll u=(a-b+5)/2; if(u==2){b=a+b+2;a=6;} else if(u&1){a=a-b+11;b=2*b-4;} else {a=a-b+19;b=2*b-8;} }
    else { if(((a-b)/2)&1){b=a+b+7;a=6;} else {b=a+b-2;a=22;} } n++; }
  for(int i=0;i<80;i++) if(bp[i]!=INT64_MAX||bq[i]!=INT64_MAX) printf("%d %" PRId64 " %" PRIu64 " %" PRId64 " %" PRId64 " %" PRId64 " %" PRIu64 " %" PRId64 " %" PRId64 "\n",i,bp[i],np[i],ap[i],bbp[i],bq[i],nq[i],aq[i],bbq[i]);
  printf("end %" PRIu64 " %" PRId64 " %" PRId64 "\n",n,a,b); }
