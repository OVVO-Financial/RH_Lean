/* envelope_census.c  --  EXT-20261115-ENV reproduction (exact integer arithmetic for M; doubles only for ratios)
 *
 * Computes the RH_Lean frozen-root objects exactly as defined on main in
 * RHLean/Proof/SquareRootAmplificationLogGrowth.lean:
 *     X_R      = R^2 - 1                                   (squareRootEndpoint)
 *     K_R      = max_{0<=y<R} (M(y)-1)^2/(y+1)             (squareRootHistoricalK)
 *     alpha_R  = (M(X_R)-1)^2 / (R^2 K_R)                  (squareRootEndpointAmplification)
 *     crit_R   = |M(X_R)-1| / (R K_R)                      (critical ratio of claim ENV-4)
 *     Q_R      = 2 M(R-1) - M(X_R)                         (frozen-root return)
 * by a segmented Moebius sieve up to Rmax^2.
 *
 * build:  gcc -O2 -o envelope_census envelope_census.c -lm
 * provenance: user-supplied external handoff, 2026-11-15; reviewed copy.
 * run:    ./envelope_census 100000 env_1e5.csv      (full original census; about 5 minutes)
 * smoke:  ./envelope_census --quick env_quick.csv  (Rmax=1000)
 * default Rmax remains 10000; no large census is forced on CI.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <errno.h>
#include <limits.h>
int main(int argc,char**argv){
  if(argc>3 || (argc>1 && strcmp(argv[1],"--help")==0)){
    fprintf(argc>3?stderr:stdout,"usage: %s [Rmax|--quick] [output.csv]\n",argv[0]);
    return argc>3?2:0;
  }
  long Rmax = 10000;
  if(argc>1){
    if(strcmp(argv[1],"--quick")==0) Rmax=1000;
    else {
      char* end=NULL; errno=0; Rmax=strtol(argv[1],&end,10);
      if(errno!=0 || end==argv[1] || *end!='\0'){
        fprintf(stderr,"Rmax must be an integer at least 2\n"); return 2;
      }
    }
  }
  if(Rmax<2 || Rmax>(LONG_MAX/4)/Rmax){
    fprintf(stderr,"Rmax must be at least 2 and its square must fit safely in long\n"); return 2;
  }
  const char* out = argc>2? argv[2] : "env.csv";
  long N = Rmax*Rmax;                       /* M is needed up to N-1 */
  long sq = Rmax+1;
  char* comp = calloc(sq+1,1); long* primes = malloc(sizeof(long)*(sq+1)); long np=0;
  if(!comp || !primes){fprintf(stderr,"prime-table allocation failed\n");return 1;}
  for(long i=2;i<=sq;i++){ if(!comp[i]){primes[np++]=i; for(long j=i*i;j<=sq;j+=i) comp[j]=1;} }
  /* history M(y), y<=Rmax */
  int8_t* mus = malloc(Rmax+2); long* Ms = malloc(sizeof(long)*(Rmax+2));
  if(!mus || !Ms){fprintf(stderr,"history allocation failed\n");return 1;}
  for(long i=0;i<=Rmax;i++) mus[i]=1;
  mus[0]=0;
  for(long k=0;k<np;k++){ long p=primes[k]; if(p>Rmax) break;
    for(long j=p;j<=Rmax;j+=p) mus[j]=-mus[j];
    long p2=p*p; for(long j=p2;j<=Rmax;j+=p2) mus[j]=0; }
  Ms[0]=0; for(long i=1;i<=Rmax;i++) Ms[i]=Ms[i-1]+mus[i];
  /* K_R = running max over 0<=y<R */
  double* K = malloc(sizeof(double)*(Rmax+2));
  if(!K){fprintf(stderr,"envelope allocation failed\n");return 1;}
  K[0]=0; double run=0;
  for(long R=1;R<=Rmax;R++){ long y=R-1; double v=(double)(Ms[y]-1)*(double)(Ms[y]-1)/(double)(y+1); if(v>run) run=v; K[R]=run; }
  /* segmented sieve, record M(R^2-1) */
  long SEG = 1L<<22;
  int8_t* mu = malloc(SEG); uint64_t* prod = malloc(sizeof(uint64_t)*SEG);
  long* MX = malloc(sizeof(long)*(Rmax+2));
  if(!mu || !prod || !MX){fprintf(stderr,"sieve allocation failed\n");return 1;}
  FILE* f=fopen(out,"w"); if(!f){perror(out);return 1;}
  long M=0; long nextR=2; long target = nextR*nextR-1;
  double maxabs=0; long argmax=0;
  for(long lo=1; lo<N; lo+=SEG){
    long hi = lo+SEG-1; if(hi>N-1) hi=N-1; long len=hi-lo+1;
    for(long i=0;i<len;i++){mu[i]=1; prod[i]=1;}
    for(long k=0;k<np;k++){ long p=primes[k]; if(p*p>hi) break;
      long st = ((lo+p-1)/p)*p; for(long j=st;j<=hi;j+=p){ mu[j-lo]=-mu[j-lo]; prod[j-lo]*=p; }
      long p2=p*p; long st2=((lo+p2-1)/p2)*p2; for(long j=st2;j<=hi;j+=p2) mu[j-lo]=0; }
    for(long i=0;i<len;i++){ long n=lo+i; int8_t m=mu[i]; if(m!=0 && prod[i]<(uint64_t)n) m=-m; M+=m;
      if(n>=1000){ double r=fabs((double)M)/sqrt((double)n); if(r>maxabs){maxabs=r;argmax=n;} }
      if(n==target){ MX[nextR]=M; nextR++; target=nextR*nextR-1; } }
  }
  fprintf(f,"R,X,M_X,M_Rm1,Q_R,K_R,alpha_R,crit_ratio\n");
  double Amax=0, cmax=0; long Aarg=0, carg=0;
  for(long R=2;R<=Rmax;R++){ long X=R*R-1; long mx=MX[R]; double num=(double)(mx-1)*(double)(mx-1);
    double a = num/((double)R*(double)R*K[R]); double c = fabs((double)(mx-1))/((double)R*K[R]);
    if(a>Amax){Amax=a;Aarg=R;} if(c>cmax){cmax=c;carg=R;}
    long Q = 2*Ms[R-1]-mx;
    fprintf(f,"%ld,%ld,%ld,%ld,%ld,%.10f,%.10f,%.10f\n",R,X,mx,Ms[R-1],Q,K[R],a,c); }
  if(fclose(f)!=0){perror(out);return 1;}
  printf("Rmax=%ld N=%ld  max alpha_R=%.6f at R=%ld ; max crit ratio=%.6f at R=%ld ; K_Rmax=%.6f ; max|M(n)|/sqrt(n) (n>=1000)=%.6f at n=%ld\n",
         Rmax,N,Amax,Aarg,cmax,carg,K[Rmax],maxabs,argmax);
  return 0; }
