// Raw TM (plain array) against the list map. Runs the machine from blank; each time the head reaches a new right extreme and the tape ends in runs 6,4,c,
// parses the whole tape as a list of 1-runs separated by single zeros and checks it equals the list map's prediction from the previous such tape.
// usage: rawlist TM mirror(0/1) c Tmax
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef long long i64;
#define TS (1<<27)
static unsigned char t[TS];
#define MAXL 256
static i64 a[MAXL],b[MAXL]; static int m=0,mb=0; // reversed: a[0] rightmost, above the tail
static long tops=0; static i64 lastP=0;
static int step(void){ // returns 0 ok, 1 predicted halt
  i64 r=a[0]+2; int i=0;
  while(1){
    if(r&1){ if(i==m-1)return 2; a[i+1]+=(r+3)/2; a[i]=(r+9)/2; return 0; }
    a[i]=r/2+2;
    if(i==m-1)return 2;
    if(i==m-2){
      i64 P=a[m-1]+r/2; lastP=P; tops++; m--;
      i64 p=P;
      while((p&1)==0){ if(p<=2)return 1; a[m++]=p/2+1; p=p/2-1; }
      a[m++]=(p+1)/2+3; a[m++]=(p+1)/2;
      return 0;
    }
    r=a[i+1]+r/2-2; i++;
  }
}
int main(int c,char**v){
  char*M=v[1]; int mir=atoi(v[2]); int cc=atoi(v[3]); i64 Tmax=atoll(v[4]);
  int nw[6][2],mv[6][2],ns[6][2];
  for(int s=0;s<6;s++)for(int b0=0;b0<2;b0++){char*x=M+s*7+b0*3;
    if(x[2]=='-'){ns[s][b0]=-1;nw[s][b0]=1;mv[s][b0]=1;} else{nw[s][b0]=x[0]-'0';mv[s][b0]=(x[1]=='R'?1:-1)*(mir?-1:1);ns[s][b0]=x[2]-'A';}}
  i64 p=TS/2,lo=p,hi=p,T=0; int s=0; long checks=0,bad=0,seen=0; int have=0,halted=0;
  while(T<Tmax){
    int b0=t[p]; if(ns[s][b0]<0){halted=1;break;}
    t[p]=nw[s][b0]; p+=mv[s][b0]; s=ns[s][b0]; T++;
    if(p<lo)lo=p;
    if(p>hi){ hi=p;
      if(t[p]==0){
        // tail check from the right: skip zero at p, run c, 0, run 4, 0, run 6, 0
        i64 q=p-1; int ok=1;
        int want[3]={cc,4,6};
        for(int k=0;k<3&&ok;k++){ int n=0; while(t[q]==1){n++;q--;} if(n!=want[k]||t[q]!=0)ok=0; if(k<2||1)q--; }
        if(ok){
          // parse list right to left from q (q points to last cell of the next run left, or a zero)
          int n=0; int good=1;
          while(q>=lo){
            i64 len=0; while(t[q]==1&&q>=lo){len++;q--;}
            if(len==0)break;
            b[n++]=len; if(n>=MAXL){good=0;break;}
            if(t[q]!=0){good=0;break;}
            q--;
          }
          // everything left of q must be blank
          for(i64 z=q;z>=lo&&good;z--) if(t[z]!=0)good=0;
          if(good&&n>=1){
            seen++;
            if(have){
              int r=step();
              if(r==1){ printf("map predicts halt P=%lld but raw continued T=%lld\n",lastP,T); have=0; }
              int same=(m==n); for(int i=0;i<n&&same;i++) if(a[i]!=b[i])same=0;
              checks++;
              if(!same){ bad++; if(bad<4){ printf("MISMATCH T=%lld pred:",T); for(int i=m-1;i>=0&&i>=m-8;i--)printf(" %lld",a[i]); printf(" raw:"); for(int i=n-1;i>=0&&i>=n-8;i--)printf(" %lld",b[i]); printf("\n"); } memcpy(a,b,sizeof(i64)*n); m=n; }
            } else if(n>=2){ memcpy(a,b,sizeof(i64)*n); m=n; have=1; }
          }
        }
      }
    }
  }
  printf("%s mirror=%d c=%d T=%lld width=%lld checks=%ld bad=%ld topevents=%ld lastP=%lld %s list:",M,mir,cc,T,hi-lo+1,checks,bad,tops,lastP,halted?"HALT":"running");
  for(int i=m-1;i>=0&&i>=m-6;i--)printf(" %lld",a[i]); printf("\n");
}
