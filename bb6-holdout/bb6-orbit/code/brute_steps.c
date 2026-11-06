// Sums raw-step costs application by application from A(6,1), straight from the per-rule polynomials. No telescoping.
// usage: brute_steps MAXAPPS  (checkfile lines: "n a b", prints total steps at each). Totals fit 128 bits up to B about 2^40.
#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>
typedef int64_t ll; typedef unsigned __int128 U; typedef __int128 I;
static void pu(U x){ char t[64]; int n=0; if(!x)t[n++]='0'; while(x){t[n++]='0'+(int)(x%10);x/=10;} while(n)putchar(t[--n]); }
int main(int ac,char**av){ uint64_t cn; ll ca,cb; FILE*f=fopen(av[1],"r"); U two=0; // two = 2*steps
  ll a=6,b=1; uint64_t n=0; int have=fscanf(f,"%" SCNu64 " %" SCNd64 " %" SCNd64,&cn,&ca,&cb)==3;
  while(have){
    if(n==cn){ if(a!=ca||b!=cb){ printf("MISMATCH at %" PRIu64 "\n",n); return 1; } printf("%" PRIu64 " %" PRId64 " %" PRId64 " ",n,a,b); pu(two/2); puts(""); have=fscanf(f,"%" SCNu64 " %" SCNd64 " %" SCNd64,&cn,&ca,&cb)==3; }
    ll d=b-a-3; I A=a,B=b;
    if(d==0){ two+=2*(A*A+7*A+41); printf("HALT %" PRIu64 "\n",n); return 0; }
    if(d>0){ two+=2*(A*A+3*A+15); a=2*a+6;b=d; }
    else if(b==1){ if(a%4==2){ two+=13*A+142; b=a+7;a=6;} else { two+=13*A+406; b=a-2;a=22;} }
    else if(b==3){ if(a%4==2){ two+=21*A+282; b=a+13;a=6;} else { two+=11*A+88; a=a+8;b=2;} }
    else if(b&1){ if(b==a+1){ two+=2*(A*A+5*A+41); b=a+b+2;a=6; }
      else if(((a-b+5)/2)&1){ two+=2*B*B+11*A-5*B+85; ll na=a-b+11; b=2*b-4;a=na; }
      else { two+=2*B*B+19*A-13*B+231; ll na=a-b+19; b=2*b-8;a=na; } }
    else { if(((a-b)/2)&1){ two+=2*B*B+13*A-3*B+150; b=a+b+7;a=6; } else { two+=2*B*B+13*A-3*B+414; b=a+b-2;a=22; } }
    n++;
  }
  return 0; }
