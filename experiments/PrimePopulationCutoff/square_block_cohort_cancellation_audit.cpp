// Actual-prime / Moebius audit of cumulative square-block packet cancellation.
// g++ -O3 -std=c++17 -Wall -Wextra -Werror \
//   experiments/PrimePopulationCutoff/square_block_cohort_cancellation_audit.cpp -o /tmp/cohort_audit
// /tmp/cohort_audit 6000
#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <vector>
using namespace std;

int main(int argc,char**argv){
  const int maxR=(argc>1?atoi(argv[1]):2000);
  if(maxR<2||maxR>10000) return 2;
  const int xMax=maxR*maxR-1;
  vector<int> lp(xMax+1),primes;
  vector<int8_t> mu(xMax+1);
  mu[1]=1;
  for(int n=2;n<=xMax;++n){
    if(!lp[n]){lp[n]=n;primes.push_back(n);mu[n]=-1;}
    for(int p:primes){
      int64_t t=int64_t(n)*p;
      if(t>xMax||p>lp[n])break;
      lp[t]=p;
      mu[t]=(n%p? -mu[n]:0);
    }
  }

  vector<int> block(maxR);
  for(int r=1;r<maxR;++r)
    for(int n=r*r;n<(r+1)*(r+1);++n) block[r]+=mu[n];

  const vector<int> samples={2,3,18,53,56,317,1000,2000,5561,6000};
  long long accumulated=block[1],plus=0,minus=0,Q=3;
  int historicalM=1;
  int oldUpper=0,oldLower=0,positiveCovRoots=0;
  long long upperSF=0,lowerSF=0;
  cout<<"R,X,M,positive_blocks,negative_blocks_absolute,block_variation,"
        "Q,dyadic_odd_annulus,nonzero_odd_annulus,cube23_top,cube23_middle,twice_live_covariance\n";

  for(int R=2;R<=maxR;++R){
    if(R>2){
      int r=R-1;
      accumulated+=block[r];
      if(block[r]>0)plus+=block[r];else minus-=block[r];
      Q+=2*mu[r]-block[r];
      historicalM+=mu[r];
    }
    const int x=R*R-1;
    while(oldUpper<x){
      ++oldUpper;
      if(oldUpper%2&&mu[oldUpper])++upperSF;
    }
    while(oldLower<x/2){
      ++oldLower;
      if(oldLower%2&&mu[oldLower])++lowerSF;
    }
    const long long live=upperSF-lowerSF;
    const long long twiceCov=accumulated*accumulated-live;
    if(twiceCov>0){
      ++positiveCovRoots;
      cerr<<"positive signed live covariance at R="<<R
          <<" X="<<x<<" 2Gamma="<<twiceCov<<"\n";
    }
    if(find(samples.begin(),samples.end(),R)==samples.end())continue;
    long long odd=0,squarefreeOdd=0,cubeTop=0,cubeMiddle=0;
    for(int m=x/2+1;m<=x;++m){
      if(m%2){odd+=mu[m];if(mu[m])++squarefreeOdd;}
      if(m%2&&m%3)cubeTop+=mu[m];
    }
    for(int m=x/6+1;m<=x/3;++m)if(m%2&&m%3)cubeMiddle+=mu[m];
    if(odd!=accumulated || squarefreeOdd!=live || cubeTop-cubeMiddle!=accumulated ||
       Q!=2*historicalM-accumulated){
      cerr<<"Exact identity mismatch at root R="<<R<<"\n";
      return 3;
    }
    cout<<R<<","<<x<<","<<accumulated<<","<<plus<<","<<minus<<","
        <<plus+minus<<","<<Q<<","<<odd<<","<<squarefreeOdd<<","
        <<cubeTop<<","<<cubeMiddle<<","<<twiceCov<<"\n";
  }
  cerr<<"positive live covariance roots through "<<maxR
      <<": "<<positiveCovRoots<<"\n";
  return 0;
}
