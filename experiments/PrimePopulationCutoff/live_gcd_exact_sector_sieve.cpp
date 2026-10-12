// Integer-exact signed interaction by exact gcd and historical root sector.
// Counts true odd squarefree Mobius packets born and dying across square blocks.
// Complexity O(x log x) via divisor-Mobius inversion, NOT O(x^2) pair enumeration.
// Does NOT establish a uniform finite A/C bound or RH.
//
// g++ -O3 -std=c++17 -Wall -Wextra -Werror \
//   experiments/PrimePopulationCutoff/live_gcd_exact_sector_sieve.cpp -o /tmp/gcd_ledger
// /tmp/gcd_ledger 5561
#include <algorithm>
#include <cmath>
#include <cstdint>
#include <iostream>
#include <vector>
using namespace std;

int main(int argc,char**argv){
  int R=argc>1?atoi(argv[1]):5561;
  if(R<2||R>10000)return 2;
  int x=R*R-1,maxg=x/5;
  vector<int>lp(x+1),primes;
  vector<int8_t>mu(x+1);
  mu[1]=1;
  for(int n=2;n<=x;++n){
    if(!lp[n]){lp[n]=n;mu[n]=-1;primes.push_back(n);}
    for(int p:primes){
      int64_t v=int64_t(n)*p;
      if(v>x||p>lp[n])break;
      lp[v]=p;
      mu[v]=(n%p)?-mu[n]:0;
    }
  }
  vector<int64_t>divisorPairs(maxg+1),exactGcd(maxg+1);
  int64_t M=0,L=0;
  for(int m=x/2+1;m<=x;++m){
    if((m&1)&&mu[m]){M+=mu[m];++L;}
  }
  for(int d=1;d<=maxg;d+=2){
    if(!mu[d])continue;
    int64_t V=0,C=0;
    int kFirst=x/(2*d)+1;
    if(!(kFirst&1))++kFirst;
    int kLast=x/d;
    for(int k=kFirst;k<=kLast;k+=2){
      int weight=mu[d*k];
      if(weight){V+=weight;++C;}
    }
    divisorPairs[d]=(V*V-C)/2;
  }
  for(int d=maxg;d>=1;--d){
    if(!(d&1)||!mu[d])continue;
    int64_t count=divisorPairs[d];
    // Exact gcd=d via inclusion-exclusion over larger common divisors.
    for(int k=3*d;k<=maxg;k+=2*d)count-=exactGcd[k];
    exactGcd[d]=count;
  }
  vector<int64_t>suffix(maxg+2);
  for(int d=maxg;d>=1;--d)suffix[d]=suffix[d+1]+exactGcd[d];

  const int64_t Gamma=(M*M-L)/2;
  cout<<"root="<<R<<" x="<<x<<" M="<<M<<" live="<<L
      <<" Gamma="<<Gamma<<" pair_gcd_sum="<<suffix[1]
      <<" coprime="<<exactGcd[1]<<" shared="<<Gamma-exactGcd[1]<<"\n";
  if(Gamma!=suffix[1]){
    cerr<<"FAIL: exact gcd ledger differs from signed live square\n";
    return 3;
  }
  for(int T:{6,15,50,100,200,300,500,1000,2000,R}){
    int lower=x/T;
    int64_t high=suffix[lower+1];
    cout<<"T="<<T<<" gcd_gt="<<lower
        <<" signed_high="<<high<<" signed_remaining="<<Gamma-high
        <<" normalized_high="<<double(high)/x<<"\n";
  }
  return 0;
}
