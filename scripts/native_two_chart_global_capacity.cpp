// V7: exact two-chart middle-core and historical Abel capacity audit.
#include <algorithm>
#include <array>
#include <cassert>
#include <cmath>
#include <cstdint>
#include <iomanip>
#include <iostream>
#include <numeric>
#include <vector>
using namespace std;
using ll=long long;
int main(){
 const vector<int> roots={16,32,64,317,1027,2048,4096};
 const int N=roots.back()*roots.back()-1;
 vector<int> lo(N+1),hi(N+1),primes,M(N+1),pi(N+1);
 vector<int8_t> mu(N+1); mu[1]=1; hi[1]=1;
 for(int n=2;n<=N;n++){
  if(!lo[n]){lo[n]=n;primes.push_back(n);mu[n]=-1;}
  hi[n]=max(lo[n],hi[n/lo[n]]);
  for(int p:primes){if(p>lo[n]||1LL*p*n>N)break;lo[p*n]=p;mu[p*n]=p==lo[n]?0:-mu[n];}
 }
 for(int n=1;n<=N;n++){M[n]=M[n-1]+mu[n];pi[n]=pi[n-1]+(n>=2&&lo[n]==n);}
 cout<<"R,tail_count,noncentral_count,noncentral_signed,central_count,central_signed,high_count,high_signed,large_core_noncentral,root_star_signed_formula,Q,K,desc_cost_over_R,asc_cost_over_R,average_cost_over_R,largest_prime_star_cost_over_R\n";
 for(int R:roots){
  const int X=R*R-1;
  ll tail=0,nc=0,ncs=0,cent=0,cents=0,high=0,highs=0,bad=0;
  vector<ll> d(R),a(R),s(R),star(R);
  for(int n=R;n<=X;n++)if(mu[n]){
   int asc=1,b=n;while(asc<R){asc*=lo[b];b/=lo[b];}
   int desc=1,c=n;while(desc<R){desc*=hi[c];c/=hi[c];}
   assert(c<R&&b<R&&gcd(c,b)==1&&n%(c*b)==0);const int m=n/(c*b);
   assert(m>=2&&mu[n]==mu[c]*mu[b]*mu[m]);
   assert(b==1||c>1); assert((b==1)==(n/hi[n]<R));
   int z=-mu[n];tail++;d[c]+=z*mu[c];a[b]+=z*mu[b];
   if(b!=1){nc++;ncs+=z;if(m>=R)bad++;assert(m<R);assert(hi[c]<lo[m]&&hi[m]<lo[b]);assert(1LL*m*b>=R&&1LL*m*c>=R);assert(1LL*(m/lo[m])*b<R&&1LL*(m/hi[m])*c<R);}
   else{cent++;cents+=z;int t=n/hi[n];assert(t<R&&z==mu[t]);star[t]++;}
   if(hi[n]>=R){high++;highs+=z;assert(b==1&&c==n/hi[n]);}
  }
  ll cf=0,ct=0,hs=0,hc=0;
  for(int t=1;t<R;t++)if(mu[t]){
   int cutoff=max(hi[t],(R-1)/t); ll multiplicity=max(0,pi[X/t]-pi[cutoff]);
   assert(star[t]==multiplicity);ct+=multiplicity;cf+=mu[t]*multiplicity;
   ll ht=pi[X/t]-pi[R-1];hc+=ht;hs+=mu[t]*ht;
  }
  assert(cf==cents&&ct==cent&&hc==high&&hs==highs&&bad==0&&nc+cent==tail);
  const ll Q=2LL*M[R-1]-M[X];assert(Q==M[R-1]+cents+ncs);
  ll qd=0,qa=0;long double K=1;
  for(int t=1;t<R;t++){qd+=mu[t]*d[t];qa+=mu[t]*a[t];K=max(K,static_cast<long double>(M[t]-1)*(M[t]-1)/(t+1));s[t]=d[t]+a[t];}
  assert(qd==qa&&qd==Q-M[R-1]);
  // Centered historical Abel bound, skip squareful labels (interpolation across
  // gaps is free for the dot product); use M(y)-1 at previous supported site.
  // cost is |f(1)| + sqrt(K)*(sqrt(R)*|f(last)| + sum sqrt(t+1)|delta f|).
  // Division by R alone displays variation cost relative to the required root scale.
  auto cost=[&](const vector<ll>&f,long double scale){int prev=1;long double v=0;for(int t=2;t<R;t++)if(mu[t]){if(prev>1)v+=sqrtl(prev+1)*fabsl(f[t]-f[prev]);prev=t;}if(prev>1)v+=sqrtl(R)*fabsl(f[prev]);return scale*(fabsl(f[1])+sqrtl(K)*v)/(R*sqrtl(K));};
  cout<<R<<','<<tail<<','<<nc<<','<<ncs<<','<<cent<<','<<cents<<','<<high<<','<<highs<<','<<bad<<','<<cf<<','<<Q<<','<<setprecision(12)<<K<<','<<cost(d,1)<<','<<cost(a,1)<<','<<cost(s,0.5L)<<','<<cost(star,1)<<'\n';
 }
}
