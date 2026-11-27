#include <algorithm>
#include <cmath>
#include <cstdint>
#include <iomanip>
#include <iostream>
#include <vector>
#include <cassert>
using namespace std; using i64=long long; using ld=long double;
// C=(N!)^m/A_m(N), A_m(N)=prod_{j<=mN} gcd(j,lcm(1..floor((j-1)/m))).
// Numerator of U_a=(N!)^m/((ma)! (N-a-1)!^m) divides C.
// Prime-blind shared grid a=0,m,...,(m-1)m, N=m^2-1.
void run(i64 m){
 const i64 N=m*m-1,L=m*N; vector<bool> prime(N+1,true);prime[0]=prime[1]=false;
 for(i64 p=2;p*p<=N;++p)if(prime[p])for(i64 n=p*p;n<=N;n+=p)prime[n]=false;
 ld C=0,grid=0,lowLoss=0,highLoss=0,selectedLoss=0,capBound=0; i64 highs=0,exact=0,positions=0,lowTests=0,highTests=0,maxGap=0;
 for(i64 p=2;p<=N;++p)if(prime[p]){
   vector<i64> powers; for(i64 d=p;d<=L;){powers.push_back(d);if(d>L/p)break;d*=p;}
   i64 cap=0;for(i64 d:powers)if(d<=N)cap+=m-m*(N%d)/d;
   i64 best=0;ld lp=logl(p);
   if(p<=m){
     for(i64 j=0;j<m;++j){i64 a=j*m; i64 v=0;
       for(i64 d:powers)v+=m*(N/d-(N-a-1)/d)-m*a/d;
       assert(v<=cap);best=max(best,v);++lowTests;}
     lowLoss+=(cap-best)*lp;
   } else {
     ++highs; i64 r=N%p; assert(p*p>N&&p*p>L/p);
     auto val=[&](i64 a){return m*(a%p>=r)-m*(a%p)/p-m*a/(p*p);};
     // Only the earliest grid point in the positive interval per p-cycle can maximize v_p.
     for(i64 k=0;k<N/p;++k){i64 a=m*((k*p+r+m-1)/m);++positions;
       if(a>=N||a>=p*(k+1))continue;
       i64 v=val(a);assert(v<=cap);best=max(best,v);++highTests;
       if(m<=64){i64 vv=0;for(i64 d:powers)vv+=m*(N/d-(N-a-1)/d)-m*a/d;assert(v==vv);}
     }
     if(m<=64){i64 brute=0;for(i64 j=0;j<m;++j)brute=max(brute,val(j*m));assert(best==brute);}
     i64 a=m*((r+m-1)/m);i64 chosen=(a<N&&a<p)?max(i64(0),val(a)):0;
     assert(chosen<=best&&best<=cap);
     assert(cap-chosen<=m*m/p+1);
     selectedLoss+=(cap-chosen)*lp; capBound+=(m*m/p+1)*lp;
     highLoss+=(cap-best)*lp;if(cap==best)++exact;maxGap=max(maxGap,cap-best);
   }
   C+=cap*lp;grid+=best*lp;
 }
 assert(fabsl(C-grid-lowLoss-highLoss)<1e-9L*max(1.L,C));
 cout<<setprecision(15)<<"{\"R\":"<<m<<",\"N\":"<<N<<",\"L\":"<<L<<",\"high_primes\":"<<highs<<",\"exact_high_primes\":"<<exact<<",\"grid_size\":"<<m<<",\"candidate_positions\":"<<positions<<",\"high_tests\":"<<highTests<<",\"low_tests\":"<<lowTests<<",\"C_normalized\":"<<C/(m*N)<<",\"grid_normalized\":"<<grid/(m*N)<<",\"loss_div_mR\":"<<(C-grid)/(m*m)<<",\"high_loss_div_mR\":"<<highLoss/(m*m)<<",\"low_loss_div_mR\":"<<lowLoss/(m*m)<<",\"simple_selected_loss_div_mR\":"<<selectedLoss/(m*m)<<",\"bound_div_mR\":"<<capBound/(m*m)<<",\"max_high_gap\":"<<maxGap<<"}"<<endl;
}
int main(int argc,char**argv){if(argc==1)for(i64 r:{16,32,64,128,317,1027,2048,4096})run(r);else for(int i=1;i<argc;++i)run(atoll(argv[i]));}
