// Genuine integer-prime / Mobius square-block incidence, no surrogate signs.
// Inputs: maxR, minR. Prints block-by-block integer identities.
// For a block [R^2,(R+1)^2), q>R owns q*c (c<=R) uniquely, except
// the square R^2 whose mu is identically 0 (R>=2).
#include <bits/stdc++.h>
using namespace std;
int main(int argc, char **argv) {
  int maxR = argc>1 ? atoi(argv[1]) : 2048;
  int minR = argc>2 ? atoi(argv[2]) : 100;
  long long N = (long long)maxR*maxR;
  if(minR<2 || maxR<=minR || N>100000000LL) return 2;
  vector<uint8_t> isp(N,1); isp[0]=isp[1]=0;
  for(long long p=2;p*p<N;p++)
    if(isp[p]) for(long long k=p*p;k<N;k+=p) isp[k]=0;
  vector<int8_t> mu(N,1); mu[0]=0;
  vector<uint32_t> largestPrimeFactor(N,0);
  for(long long p=2;p<N;p++) if(isp[p]) {
    for(long long k=p;k<N;k+=p) {
      mu[k]=-mu[k];
      largestPrimeFactor[k]=(uint32_t)p;
    }
    if(p*p<N) for(long long k=p*p;k<N;k+=p*p) mu[k]=0;
  }
  vector<uint32_t> pi(N); uint32_t count=0;
  for(long long n=0;n<N;n++) pi[n]=(count+=isp[n]);
  cout << "R,prime_count,mobius_block,cofactor_prime_debt,smooth_population,mu2_block,left_half_primes\n";
  for(long long r=minR;r<maxR;r++) {
    long long lo=r*r, hi=(r+1)*(r+1)-1;
    int64_t signedMass=0, squarefreeSites=0, debt=0, smoothIndependent=0;
    for(long long n=lo;n<=hi;n++) {
      signedMass+=mu[n]; squarefreeSites+=(mu[n]!=0);
      if(largestPrimeFactor[n]<=r) smoothIndependent+=mu[n];
    }
    for(int c=1;c<=r;c++) if(mu[c]!=0)
      debt+=(int64_t)mu[c]*((int64_t)pi[hi/c]-(int64_t)pi[lo/c]);
    // Independently sieve largest-prime-factor smooth sites: verifies the
    // nontrivial original S_R - A_R = Delta_R carrier at every physical root.
    if(smoothIndependent!=signedMass+debt) {
      cerr<<"FAILED complete signed cofactor partition at R="<<r<<'\n';
      return 1;
    }
    cout<<r<<','<<(pi[hi]-pi[lo-1])<<','<<signedMass<<','<<debt
        <<','<<smoothIndependent<<','<<squarefreeSites
        <<','<<(pi[lo+r]-pi[lo-1])<<'\n';
  }
  return 0;
}
