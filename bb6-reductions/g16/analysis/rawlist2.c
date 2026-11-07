// Random start stacks: plain raw TM against the list map, including the halting criterion (P+2 a power of 2).
// Stack entries >= 3 except the first run, which may be small. usage: rawlist2 TM mirror c state count seed maxval
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef long long i64;
#define TS (1<<24)
static unsigned char t[TS];
#define MAXL 256
static i64 a[MAXL],b[MAXL]; static int m; static long tops; static i64 lastP;
static int step(void){
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
  char*M=v[1]; int mir=atoi(v[2]); int cc=atoi(v[3]); int st0=v[4][0]-'A'; long count=atol(v[5]); srand(atoi(v[6])); int maxv=atoi(v[7]);
  int nw[6][2],mv[6][2],ns[6][2];
  for(int s=0;s<6;s++)for(int b0=0;b0<2;b0++){char*x=M+s*7+b0*3;
    if(x[2]=='-'){ns[s][b0]=-1;nw[s][b0]=1;mv[s][b0]=1;} else{nw[s][b0]=x[0]-'0';mv[s][b0]=(x[1]=='R'?1:-1)*(mir?-1:1);ns[s][b0]=x[2]-'A';}}
  long tot=0,okcheck=0,bad=0,h_ok=0,h_miss=0,h_false=0,alltops=0,toohard=0;
  for(long it=0;it<count;it++){
    int L=2+rand()%6; i64 st[16];
    st[0]=1+rand()%maxv; for(int i=1;i<L;i++)st[i]=3+rand()%maxv;
    for(int i=0;i<L;i++)a[L-1-i]=st[i]; m=L; 
    i64 base=TS/2; i64 lo=base-1; 
    i64 q=base; memset(t,0,TS);
    i64 full[32]; int nf=0; for(int i=0;i<L;i++)full[nf++]=st[i]; full[nf++]=6;full[nf++]=4;full[nf++]=cc;
    for(int i=0;i<nf;i++){ for(i64 j=0;j<full[i];j++)t[q++]=1; if(i<nf-1)t[q++]=0; }
    i64 p=q,hi=q; int s=st0; i64 T=0; int steps=0; int predicted=0; int halted=0;
    tops=0;
    while(T<40000000&&steps<400){
      int b0=t[p]; if(ns[s][b0]<0){halted=1;break;}
      t[p]=nw[s][b0]; p+=mv[s][b0]; s=ns[s][b0]; T++;
      if(p<lo)lo=p;
      if(p>hi){ hi=p;
        if(t[p]==0){
          i64 z=p-1; int ok=1; int want[3]={cc,4,6};
          for(int k=0;k<3&&ok;k++){ int n=0; while(t[z]==1){n++;z--;} if(n!=want[k]||t[z]!=0)ok=0; z--; }
          if(ok){
            int n=0,good=1;
            while(z>=lo){ i64 len=0; while(t[z]==1&&z>=lo){len++;z--;} if(len==0)break; b[n++]=len; if(n>=MAXL){good=0;break;} if(t[z]!=0){good=0;break;} z--; }
            for(i64 y=z;y>=lo&&good;y--) if(t[y]!=0)good=0;
            if(good){
              // this tape is the first after the start (tail 6,4,1 at start is not re-announced at step 0)
              int r=step(); steps++;
              if(r==1){ predicted=1; printf("map says halt P=%lld but raw continued\n",lastP); h_false++; break; }
              if(r==2){ break; }
              int same=(m==n); for(int i=0;i<n&&same;i++) if(a[i]!=b[i])same=0;
              if(same)okcheck++; else { bad++; if(bad<6){ printf("MISMATCH start"); for(int i=0;i<L;i++)printf(" %lld",st[i]); printf(" T=%lld pred:",T); for(int i=m-1;i>=0&&i>=m-8;i--)printf(" %lld",a[i]); printf(" raw:"); for(int i=n-1;i>=0&&i>=n-8;i--)printf(" %lld",b[i]); printf("\n"); } break; }
            }
          }
        }
      }
    }
    alltops+=tops;
    if(halted){
      // next map steps must predict a halt with no other tape in between
      int r=step();
      int guard=0; while(r==0&&guard<1){ guard++; r=step(); }
      if(r==1){ i64 Q=lastP+2; if((Q&(Q-1))==0)h_ok++; else {h_miss++; printf("halt with P=%lld not of the form\n",lastP);} }
      else { h_miss++; printf("RAW HALT unpredicted start:"); for(int i=0;i<L;i++)printf(" %lld",st[i]); printf(" T=%lld lastP=%lld\n",T,lastP); }
    }
    tot++;
  }
  printf("%s stacks=%ld checks ok=%ld bad=%ld top events=%ld raw halts predicted=%ld unpredicted=%ld predicted-not-halted=%ld\n",M,tot,okcheck,bad,alltops,h_ok,h_miss,h_false);
}
