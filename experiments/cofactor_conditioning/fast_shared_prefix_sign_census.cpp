// Shared-gcd signed Mobius prefix. Pure finite integer arithmetic.
// g++ -O3 -std=c++17 experiments/cofactor_conditioning/fast_shared_prefix_sign_census.cpp -o prefix
// ./prefix 100000000
// O(N log N), based on the exact gcd indicator:
// 1_{gcd(c,d)=1} = sum_{k|c,k|d} mu(k).
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <vector>
using i64=long long;
int main(int argc,char**argv){
 const int N=argc>1?std::atoi(argv[1]):1000000;
 if(N<100||N>100000000)return 2;
 std::vector<int> lp(N+1,0),primes;
 std::vector<int8_t> mu(N+1,0);mu[1]=1;
 for(int n=2;n<=N;n++){
   if(!lp[n]){lp[n]=n;mu[n]=-1;primes.push_back(n);}
   const int lpN=lp[n];
   for(int p:primes){
     const i64 v=(i64)n*p;
     if(v>N||p>lpN)break;
     lp[v]=p;
     if(p==lpN){mu[v]=0;break;}
     mu[v]=-mu[n];
   }
 }
 lp.clear();lp.shrink_to_fit();primes.clear();primes.shrink_to_fit();
 // cop[d] = sum_{c<d, gcd(c,d)=1} mu(c), INCLUDING c=1.
 std::vector<int> cop(N+1,0);
 for(int k=1;k<=N;k++)if(mu[k]){
   int running=0;
   for(int d=k;d<=N;d+=k){
     cop[d]+=mu[k]*running;
     running+=mu[d];
   }
 }
 i64 shared=0,coprime=0,maxPositive=0;
 int M=1,lastPositive=0,lastNonnegative=0,atMax=0;
 for(int d=2;d<=N;d++){
   const i64 copSmall=(i64)cop[d]-1; // exclude c=1
   const i64 sharedSmall=(i64)M-1-copSmall;
   shared+=2LL*mu[d]*sharedSmall;
   coprime+=2LL*mu[d]*copSmall;
   M+=mu[d];
   if(shared>0){lastPositive=d;if(shared>maxPositive){maxPositive=shared;atMax=d;}}
   if(shared>=0)lastNonnegative=d;
   if(d==229||d==230||d==191931||d==300893||d==300894||
      d==20000||d==100000||d==1000000||d==10000000||d==N){
     std::cout<<"t="<<d<<" shared_prefix="<<shared
              <<" coprime_prefix="<<coprime<<" M="<<M<<"\n";
   }
 }
 std::cout<<"N="<<N<<" last_positive="<<lastPositive
          <<" last_nonnegative="<<lastNonnegative
          <<" max_positive="<<maxPositive<<" at="<<atMax<<"\n";
 return 0;
}
