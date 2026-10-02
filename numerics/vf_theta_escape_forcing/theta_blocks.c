// Per-square-block theta mass Theta_R = sum_{R^2 < p < (R+1)^2} log p, and prime count P_R,
// for 1 <= R < N.  Output binary arrays of long double Theta and uint32 P.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <omp.h>
int main(int argc,char**argv){
  long N=atol(argv[1]);
  long top=(N+1)*(N+1); long sq=(long)sqrtl((long double)top)+2;
  // base primes up to sq
  char*bs=calloc(sq+1,1); long nb=0; long*bp=malloc(sizeof(long)*(sq+1));
  for(long i=2;i<=sq;i++){ if(!bs[i]){ bp[nb++]=i; for(long j=i*i;j<=sq;j+=i) bs[j]=1; } }
  long double*Th=calloc(N+1,sizeof(long double)); uint32_t*P=calloc(N+1,sizeof(uint32_t));
  long CH=64; // blocks per chunk at least; chunk spans [R0^2,(R1)^2)
  long nchunks=0; long *starts=malloc(sizeof(long)*(N+2));
  for(long R=1;R<N;){ starts[nchunks++]=R; long R1=(long)sqrtl((long double)(R*R+(1L<<22))); if(R1<=R) R1=R+1; if(R1>N) R1=N; R=R1; }
  starts[nchunks]=N;
  #pragma omp parallel
  {
    unsigned char*seg=NULL; long segcap=0;
    #pragma omp for schedule(dynamic,4)
    for(long c=0;c<nchunks;c++){
      long R0=starts[c],R1=starts[c+1]; long lo=R0*R0, hi=R1*R1; // [lo,hi)
      long len=hi-lo; if(len>segcap){ free(seg); seg=malloc(len); segcap=len; }
      memset(seg,1,len);
      for(long k=0;k<nb;k++){ long p=bp[k]; if(p*p>=hi) break;
        long s=((lo+p-1)/p)*p; if(s<p*p) s=p*p;
        for(long j=s;j<hi;j+=p) seg[j-lo]=0; }
      if(lo<=1){ for(long j=lo;j<2&&j<hi;j++) seg[j-lo]=0; }
      for(long R=R0;R<R1;R++){ long a=R*R, b=(R+1)*(R+1); long double t=0; uint32_t cnt=0; double tb=0;
        for(long n=a+1;n<b;n++) if(seg[n-lo]){ tb+=log((double)n); cnt++; }
        t=tb; Th[R]=t; P[R]=cnt; }
    }
    free(seg);
  }
  FILE*f=fopen("theta.bin","wb"); fwrite(Th,sizeof(long double),N+1,f); fclose(f);
  f=fopen("pcount.bin","wb"); fwrite(P,sizeof(uint32_t),N+1,f); fclose(f);
  return 0; }
