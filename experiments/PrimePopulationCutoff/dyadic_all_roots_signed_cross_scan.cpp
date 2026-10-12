// Exhaustive original-prime and odd-Mobius smooth/high population scan.
// C++17: g++ -O3 -std=c++17 -Wall -Wextra -Werror <file> -o /tmp/dyadic_all_roots
// Usage: /tmp/dyadic_all_roots 6000
//
// Every odd squarefree m is LIVE at the square root R precisely when
//     floor(sqrt(m))+1 <= R <= floor(sqrt(2*m)).
// Every live odd m has at most one prime factor >= R since m<R^2.
// Its largest prime factor is the exact generic post-root owner at R,
// including p=R when R is prime (sqrt(R^2-1)=R-1).
// A pair of range-add ledgers gives S_R and H_R for ALL roots, with
// each occurrence visited once. Independently verify S_R+H_R=M(R^2-1).
// No randomized signs, heuristic prime wave or independence assumption.
#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <iomanip>
#include <iostream>
#include <vector>
using namespace std;
static int isqrt(uint64_t x) {
  int r=int(sqrt(double(x)));
  while(uint64_t(r+1)*(r+1)<=x) ++r;
  while(uint64_t(r)*r>x) --r;
  return r;
}
int main(int argc,char**argv) {
  int Rmax=(argc>1?atoi(argv[1]):6000);
  if(Rmax<2||Rmax>6000){cerr<<"Rmax must be in 2..6000\n";return 2;}
  int Xmax=Rmax*Rmax-1;
  vector<int> least(Xmax+1,0),primes;
  vector<int8_t> mu(Xmax+1,0);
  mu[1]=1;
  for(int n=2;n<=Xmax;++n) {
    if(!least[n]) {least[n]=n;primes.push_back(n);mu[n]=-1;}
    for(int p:primes) {
      long long product=1LL*n*p;
      if(product>Xmax||p>least[n])break;
      least[product]=p;
      if(n%p==0){mu[product]=0;break;}
      mu[product]=-mu[n];
    }
  }
  vector<long long> aliveChange(Rmax+3),highChange(Rmax+3);
  vector<int> directM(Rmax+1);
  int nextR=2,partialM=0;
  for(int m=1;m<=Xmax;++m) {
    partialM+=mu[m];
    if(nextR<=Rmax && m==nextR*nextR-1)
      directM[nextR++]=partialM;
    if(!(m&1)||mu[m]==0)continue;
    int born=max(2,isqrt(m)+1);
    int death=min(Rmax,isqrt(2LL*m));
    if(born>death)continue;
    int n=m,largestPrime=1;
    while(n>1) {
      int p=least[n];
      largestPrime=max(largestPrime,p);
      n/=p;
    }
    aliveChange[born]+=mu[m];
    aliveChange[death+1]-=mu[m];
    int highDeath=min(death,largestPrime);
    if(born<=highDeath) {
      highChange[born]+=mu[m];
      highChange[highDeath+1]-=mu[m];
    }
  }
  long long all=0,high=0;
  int positiveCross=0,exceptionsAbove22=0,zerosAbove22=0;
  double worstRelative=0;
  int worstRoot=0;
  cout<<"R,X,M,H_generic,S_generic,diagonal,twice_cross,cancellation_fraction\n";
  for(int R=2;R<=Rmax;++R) {
    all+=aliveChange[R];
    high+=highChange[R];
    if(all!=directM[R]) {
      cerr<<"Mertens endpoint mismatch at R="<<R<<"\n";
      return 3;
    }
    long long smooth=all-high;
    long long diagonal=high*high+smooth*smooth;
    long long cross=2*high*smooth;
    if(cross>0)++positiveCross;
    if(R>=22&&(high<=0||smooth>=0)) {
      ++exceptionsAbove22;
      if(cross==0) ++zerosAbove22;
      if(R!=26 || high!=0 || smooth!=-10) {
        cerr<<"Unexpected cross-sector sign exception at R="<<R<<"\n";
        return 4;
      }
    }
    if(R>=100&&diagonal!=0) {
      double relative=double(all*all)/double(diagonal);
      if(relative>worstRelative) {
        worstRelative=relative;
        worstRoot=R;
      }
    }
    if(R==2||R==3||R==17||R==26||R==53||R==56||R==317||
       R==1000||R==2000||R==5561||R==6000||cross>0)
      cout<<R<<','<<(R*R-1)<<','<<all<<','<<high<<','<<smooth<<','
          <<diagonal<<','<<cross<<','<<setprecision(10)
          <<(diagonal?1.-double(all*all)/double(diagonal):0.)<<"\n";
  }
  cerr<<"ALL ROOTS 2.."<<Rmax<<": positive cross="<<positiveCross
      <<"; sign exceptions R>=22="<<exceptionsAbove22
      <<"; zero cross R>=22="<<zerosAbove22
      <<"; worst relative M^2/diagonal R>=100="<<worstRelative
      <<" at R="<<worstRoot<<"\n";
  if(Rmax==6000 &&
     (positiveCross!=4||exceptionsAbove22!=1||
      zerosAbove22!=1||worstRoot!=102))return 5;
  return 0;
}
