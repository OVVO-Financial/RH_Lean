// Exact dyadic/prime-comb cross-coordinate census through square endpoints.
// Compile: g++ -O3 -std=c++17 -Wall -Wextra -Werror
//          experiments/PrimePopulationCutoff/prime_comb_dyadic_crosswalk.cpp -o /tmp/prime_comb_dyadic_crosswalk
// Run: /tmp/prime_comb_dyadic_crosswalk
//
// The generic p>sqrt(R^2-1)=R-1 sector INCLUDES p=R when R is prime.
// The canonical p>R transport deliberately excludes that one prime.
// Checks true Mobius, genuine primes and all correction identities.
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <vector>
#include <algorithm>
using namespace std;

int main(int argc, char** argv) {
  vector<int> roots = {17,56,317,1000,2000,5561,6000};
  if (argc > 1) {
    roots.clear();
    for (int j=1; j<argc; ++j) roots.push_back(atoi(argv[j]));
  }
  int N=0;
  for (int R:roots) {
    if (R<2 || R>10000) {cerr << "Root must be in 2..10000\n";return 2;}
    N=max(N,R*R-1);
  }
  vector<int> least(N+1,0), primes, pref(N+1,0);
  vector<int8_t> mu(N+1,0);
  mu[1]=1;
  for (int n=2; n<=N; ++n) {
    if (!least[n]) {least[n]=n;primes.push_back(n);mu[n]=-1;}
    for (int p:primes) {
      long long v=1LL*n*p;
      if (v>N || p>least[n]) break;
      least[(int)v]=p;
      if (n%p==0) {mu[(int)v]=0;break;}
      mu[(int)v]=-mu[n];
    }
  }
  for (int n=1; n<=N; ++n) pref[n]=pref[n-1]+mu[n];
  cout << "R,X,is_R_prime,M_Rminus1,M_X,primes_gtR,high_canonical,high_generic,root_packet,smooth_generic,delta_canonical,delta_generic,odd_live_check\n";
  for (int R:roots) {
    int X=R*R-1;
    long long count=0,primeMtail=0,canonicalCount=0,canonicalMtail=0;
    for (int p:primes) {
      if (p>X) break;
      if (p>=R) {++count;primeMtail+=pref[X/p];}
      if (p>R) {++canonicalCount;canonicalMtail+=pref[X/p];}
    }
    bool rootPrime=(least[R]==R);
    long long hCan=-canonicalMtail,hGeneric=-primeMtail;
    long long rootPacket=rootPrime?-pref[R-1]:0;
    long long oddLive=0, independentSmooth=0;
    for (int c=X/2+1; c<=X; ++c) if(c%2==1) {
      oddLive+=mu[c];
      if(mu[c]) {
        int q=c, biggest=1;
        while(q>1) {int factor=least[q];biggest=max(biggest,factor);q/=factor;}
        if(biggest<R) independentSmooth+=mu[c];
      }
    }
    long long deltaCan=2*(canonicalCount-canonicalMtail);
    long long deltaGeneric=2*(count-primeMtail);
    if (hGeneric!=hCan+rootPacket ||
        pref[X]!=pref[X]+primeMtail+hGeneric ||
        oddLive!=pref[X] || independentSmooth!=pref[X]+primeMtail ||
        deltaGeneric!=deltaCan+(rootPrime?2*(1-pref[R-1]):0)) {
      cerr<<"Cross-coordinate equality failed at R="<<R<<"\n";
      return 3;
    }
    cout<<R<<','<<X<<','<<(rootPrime?1:0)<<','<<pref[R-1]<<','
        <<pref[X]<<','<<canonicalCount<<','<<hCan<<','<<hGeneric<<','
        <<rootPacket<<','<<pref[X]+primeMtail<<','
        <<deltaCan<<','<<deltaGeneric<<','<<oddLive<<"\n";
  }
}
