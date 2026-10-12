// All-root genuine-prime / Mobius audit of chronological signed cohort return.
// Cumulative-square-block identities, NOT a finite C/A or RH proof.
// Build:
// g++ -O3 -std=c++17 -Wall -Wextra -Werror \
//   experiments/PrimePopulationCutoff/square_clock_signed_return_audit.cpp \
//   -o /tmp/square_clock_signed_return_audit
// /tmp/square_clock_signed_return_audit 6000
#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <iomanip>
#include <iostream>
#include <vector>
using namespace std;

int main(int argc,char**argv){
  const int Rmax=argc>1?atoi(argv[1]):6000;
  if(Rmax<3||Rmax>20000) return 2;
  const int N=Rmax*Rmax-1;
  vector<int> lp(N+1), primes;
  vector<int8_t> mu(N+1);
  mu[1]=1;
  for(int n=2;n<=N;++n){
    if(!lp[n]){lp[n]=n;mu[n]=-1;primes.push_back(n);}
    for(int p:primes){
      int64_t t=int64_t(n)*p;
      if(t>N||p>lp[n])break;
      lp[t]=p;
      mu[t]=(n%p)?-mu[n]:0;
    }
  }

  vector<int> births(Rmax), deaths(Rmax);
  vector<int> birthCount(Rmax),deathCount(Rmax);
  int root=1;
  int64_t nextSq=4;
  for(int n=1;n<=N;++n){
    while(n>=nextSq){
      ++root;
      nextSq=int64_t(root+1)*(root+1);
    }
    if((n&1)&&mu[n]){
      births[root]+=mu[n];
      birthCount[root]++;
      if(int64_t(n)*2<=N){
        const int twice=2*n;
        int r=int(sqrt(double(twice)));
        while(int64_t(r+1)*(r+1)<=twice)++r;
        while(int64_t(r)*r>twice)--r;
        deaths[r]+=mu[n];
        deathCount[r]++;
      }
    }
  }
  const vector<int> samples={3,18,53,56,317,1000,2000,5561,6000};
  int64_t M=-1,L=1,Gamma=0;
  int64_t cross=0,birthPairs=0,deathPairs=0;
  int historicalM=mu[1];
  int posGammaRoots=0,firstFailRoot=0;
  cout<<"R,X,M,live_squarefree,Gamma,cumulative_cross,"
        "cumulative_birth_pairs,cumulative_death_pairs,Q\n";
  for(int R=2;R<=Rmax;++R){
    if(R>2){
      const int r=R-1;
      const int64_t a=births[r],d=deaths[r];
      const int64_t a2=birthCount[r],d2=deathCount[r];
      const int64_t u=M-d;
      const int64_t t1=a*a-a2,t2=d*d-d2;
      if((t1&1)||(t2&1))return 3;
      const int64_t inter=(a-d)*u,bi=t1/2,de=t2/2;
      cross+=inter;
      birthPairs+=bi;
      deathPairs+=de;
      Gamma+=inter+bi-de;
      M+=a-d;
      L+=a2-d2;
      historicalM+=mu[r];
      if(2*Gamma!=M*M-L && !firstFailRoot) firstFailRoot=R;
    }
    if(Gamma>0)++posGammaRoots;
    if(find(samples.begin(),samples.end(),R)!=samples.end()){
      const int64_t x=int64_t(R)*R-1;
      cout<<R<<","<<x<<","<<M<<","<<L<<","<<Gamma<<","
          <<cross<<","<<birthPairs<<","<<deathPairs<<","
          <<2*historicalM-M<<"\n";
    }
  }
  cerr<<"square_roots="<<(Rmax-1)<<" positive_cohort_covariance_roots="
      <<posGammaRoots<<" first_identity_failure="<<firstFailRoot<<"\n";
  return firstFailRoot?4:0;
}
