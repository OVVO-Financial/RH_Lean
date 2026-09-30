/* Diagnostics for research/LI_DISCRETE_POISSON_OMEGA_NO_GO.md (finite data only;
   not evidence for any uniform bound -- the note proves the bounds are false).
   w_q = int_{q-1}^{q} dt/log t for q>=3, w_2 = 0 (repo primeSievePNTDensity).
   hard-core  nu : prod_{q>=3} (1 - w_q delta_q)      (IsAllScaleLiState diagonal L(X,X))
   Poisson    b  : b(n) log n = -sum_{q|n,q>=3} log(q) w_q b(n/q)   (exp_*(-sum w_q delta_q))
   unit       b0 : b0(n) log n = -sum_{q|n,q>=2} b0(n/q)             (eps = 0 kernel)
   mobius     mu : mu(n) log n = -sum_{q|n} Lambda(q) mu(n/q)
   Build: gcc -O2 -o li_diag li_discrete_omega_diagnostics.c -lm ; ./li_diag 1000000
   Columns: X, L(X,X)/sqrt X, critical hard-core, critical Poisson, B_Poisson/sqrt X,
            critical unit, B0/sqrt X, M(X)/sqrt X.  (1e8 needs ~7 GB RAM, ~4 min.) */
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
static const double gx[8]={-0.9602898564975363,-0.7966664774136267,-0.5255324099163290,-0.1834346424956498,0.1834346424956498,0.5255324099163290,0.7966664774136267,0.9602898564975363};
static const double gw[8]={0.1012285362903763,0.2223810344533745,0.3137066458778873,0.3626837833783620,0.3626837833783620,0.3137066458778873,0.2223810344533745,0.1012285362903763};
int main(int argc,char**argv){
  long N=atol(argv[1]);
  double *w=malloc((N+1)*sizeof(double));
  w[0]=w[1]=w[2]=0;
  for(long q=3;q<=N;q++){double a=q-1,b=q,s=0;for(int i=0;i<8;i++){double t=0.5*(a+b)+0.5*(b-a)*gx[i];s+=gw[i]/log(t);}w[q]=0.5*s;}
  double *nu=calloc(N+1,sizeof(double)); nu[1]=1;
  for(long q=3;q<=N;q++){double wq=w[q];for(long m=N/q;m>=1;m--){double v=nu[m];if(v!=0)nu[m*q]-=wq*v;}}
  double *b=calloc(N+1,sizeof(double)),*b0=calloc(N+1,sizeof(double)),*mu=calloc(N+1,sizeof(double));
  /* accumulate convolution sums forward */
  double *Sb=calloc(N+1,sizeof(double)),*S0=calloc(N+1,sizeof(double));
  char *comp=calloc(N+1,1); double *Lam=calloc(N+1,sizeof(double));
  for(long p=2;p<=N;p++) if(!comp[p]){ for(long m=2*p;m<=N;m+=p) comp[m]=1; double lp=log((double)p); for(long pk=p;pk<=N;pk*=p){Lam[pk]=lp; if(pk>N/p)break;} }
  double *Sm=calloc(N+1,sizeof(double));
  b[1]=b0[1]=mu[1]=1;
  for(long n=1;n<=N;n++){
    if(n>1){double ln=log((double)n); b[n]=-Sb[n]/ln; b0[n]=-S0[n]/ln; mu[n]=-Sm[n]/ln;}
    double bn=b[n],b0n=b0[n],mun=mu[n];
    for(long q=2;q<=N/n;q++){ long k=n*q; double lq=log((double)q);
      Sb[k]+=lq*w[q]*bn; S0[k]+=b0n; if(Lam[q]!=0) Sm[k]+=Lam[q]*mun; }
  }
  /* cumulatives */
  double Mnu=0,Anu=0,Ab=0,B=0,A0=0,B0=0,M=0; long next=10;
  printf("# X  M_Li/sqrtX  Acrit_hardcore  Acrit_poisson  B_poisson/sqrtX  A0_unit  B0_unit/sqrtX  M_mu/sqrtX\n");
  for(long n=1;n<=N;n++){
    double r=1.0/sqrt((double)n);
    Mnu+=nu[n]; Anu+=nu[n]*r; Ab+=b[n]*r; B+=b[n]; A0+=b0[n]*r; B0+=b0[n]; M+=mu[n];
    if(n==next||n==N||n==210||n==317){double s=sqrt((double)n);
      printf("%ld %.6f %.6f %.6f %.6f %.6f %.6f %.6f\n",n,Mnu/s,Anu,Ab,B/s,A0,B0/s,M/s);
      if(n==next) next = (long)(next*1.5849); }
  }
  /* sanity: mu should be integers */
  double err=0; for(long n=1;n<=1000;n++){double d=fabs(mu[n]-round(mu[n])); if(d>err)err=d;}
  fprintf(stderr,"max |mu - round(mu)| n<=1000: %g ; mu(30)=%g mu(4)=%g\n",err,mu[30],mu[4]);
  return 0;
}
