// Fast iteration of the 16-group list map. Stack a[0..m-1] above tail (8,6,3), stored reversed so index 0 is the rightmost.
// Prints each top event: step count, P, v2(P+2), list length, first runs. usage: lm start_list maxsteps
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef unsigned __int128 u128; typedef __int128 i128;
typedef i128 V;
#define MAXL 4096
static V a[MAXL]; static int m;
static void pv(V x){ char b[64];int n=0; if(x==0){putchar('0');return;} if(x<0){putchar('-');x=-x;} while(x>0){b[n++]='0'+(int)(x%10);x/=10;} while(n--)putchar(b[n]); }
int main(int c,char**v){
  long long maxsteps=atoll(v[2]); int verbose=c>3?atoi(v[3]):1;
  // start list: leftmost first
  { char*s=strdup(v[1]);char*t=strtok(s,",");V tmp[MAXL];int n=0;while(t){tmp[n++]=atoll(t);t=strtok(0,",");} for(int i=0;i<n;i++)a[i]=tmp[n-1-i]; m=n; }
  long long st=0; V mina=(V)1<<100; 
  while(st<maxsteps){
    st++;
    V r=a[0]+2; int i=0;
    while(1){
      if(r&1){
        if(i==m-1){ printf("ODD AT TOP step=%lld\n",st); return 1; }
        a[i+1]+=(r+3)/2; a[i]=(r+9)/2;
        break;
      }
      a[i]=r/2+2;
      if(i==m-1){ printf("EVEN AT TOP step=%lld\n",st); return 1; }
      if(i==m-2){
        V P=a[m-1]+r/2;
        // top event
        V Q=P+2; int vv=0; while((Q&1)==0){Q>>=1;vv++;}
        printf("top step=%lld m=%d P=",st,m); pv(P); printf(" v2(P+2)=%d odd=",vv); pv(Q); printf(" entriesnext=");
        // first-run stage
        m--; // remove a[m-1] slot; rebuild
        V p=P; int h=0;
        while((p&1)==0){
          if(p<=2){ printf("\nHALT-CONDITION reached: P chain hits %d at step %lld\n",(int)p,st); return 0; }
          a[m++]=p/2+1; p=p/2-1; h++;
          if(m>=MAXL-4){printf("overflow\n");return 1;}
        }
        a[m++]=(p+1)/2+3; a[m++]=(p+1)/2;
        printf("%d first=",h); pv(a[m-1]); printf("\n"); fflush(stdout);
        if(a[m-1]<=8) { printf("SMALL FIRST RUN step=%lld\n",st); }
        break;
      }
      r=a[i+1]+r/2-2; i++;
    }
  }
  printf("end step=%lld m=%d list(left first):",st,m); for(int i=m-1;i>=0&&i>=m-24;i--){putchar(' ');pv(a[i]);} printf("\n");
}
