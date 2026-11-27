// V7: unsigned divisor density rows, exact historical inversion, and signed cost.
#include <algorithm>
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
 vector<int8_t> mu(N+1),om(N+1); mu[1]=1; hi[1]=1;
 for(int n=2;n<=N;n++){
  if(!lo[n]){lo[n]=n;primes.push_back(n);mu[n]=-1;}
  hi[n]=max(lo[n],hi[n/lo[n]]);
  om[n]=om[n/lo[n]]+(n/lo[n]%lo[n]!=0);
  for(int p:primes){if(p>lo[n]||1LL*p*n>N)break;lo[p*n]=p;mu[p*n]=p==lo[n]?0:-mu[n];}
 }
 for(int n=1;n<=N;n++){M[n]=M[n-1]+mu[n];pi[n]=pi[n-1]+(n>=2&&lo[n]==n);}
 const long double density=6/(acosl(-1.L)*acosl(-1.L));
 cout<<"R,Q,K,rows,high_signed,weighted_density_errors,history_main,absolute_row_error_cost_over_budget,proved_triangle_ceiling_over_budget,finite_floor_error,finite_history_main,shared_floor_abel_over_budget\n";
 for(int R:roots){
  int X=R*R-1;ll smooth=0,high=0,high_rows=0;long double K=1;
  for(int n=1;n<=X;n++)if(hi[n]<R)smooth+=mu[n];
  for(int a=1;a<R;a++){high+=ll(mu[a])*(pi[X/a]-pi[R-1]);K=max(K,static_cast<long double>(M[a]-1)*(M[a]-1)/(a+1));}
  vector<long double> F(R);long double floor_main=0;
  int rows=0;long double errors=0,main=2.L*M[R-1]-smooth,abs_cost=0,ceil_cost=0;
  for(int d=1;d<R;d++)if(mu[d]){
   ++rows;ll Z=0,S=0;for(int n=d;n<=X;n+=d)if(mu[n]){Z++;S+=(hi[n]<R);}
   vector<int> ds{1};long double delta=density;int t=d;
   while(t>1){int p=lo[t];t/=p;delta/=p+1;int k=ds.size();for(int j=0;j<k;j++)ds.push_back(p*ds[j]);}
   assert(int(ds.size())==(1<<om[d]));ll Zhist=0;const ll c=ll(mu[d])*(1LL<<om[d]);
   for(int k=1;1LL*d*k*k<=X;k++)if(mu[k]&&gcd(d,k)==1){assert(k<R);ll inner=0;long double realpart=0;for(int e:ds){ll denom=1LL*d*k*k*e;inner+=ll(mu[e])*(X/denom);realpart+=mu[e]*static_cast<long double>(X)/denom;}Zhist+=ll(mu[k])*inner;F[k]+=c*(inner-realpart);floor_main+=c*mu[k]*realpart;}
   assert(Z==Zhist);
   ll H=0;for(int a=d;a<R;a+=d)if(mu[a])H+=pi[X/a]-pi[R-1];assert(H==Z-S);
   high_rows+=c*H;
   long double err=Z-delta*X;errors+=c*err;main+=c*(delta*X-S);abs_cost+=llabs(c)*fabsl(err);
   // The elementary conditional-squarefree density bound at X/d (real
   // argument, not floored) is (2^omega(d)+2)*sqrt(X/d).
   ceil_cost+=llabs(c)*((1LL<<om[d])+2)*sqrtl(static_cast<long double>(X)/d);
  }
  const ll Q=2LL*M[R-1]-M[X];assert(high==high_rows&&Q==2LL*M[R-1]-smooth+high);
  assert(fabsl(main+errors-Q)<1e-5L);long double budget=R*sqrtl(K);
  long double fe=0,v=0;int prev=1;for(int k=1;k<R;k++)if(mu[k]){fe+=mu[k]*F[k];if(k>1){if(prev>1)v+=sqrtl(prev+1)*fabsl(F[k]-F[prev]);prev=k;}}if(prev>1)v+=sqrtl(R)*fabsl(F[prev]);long double abel=fabsl(F[1])+sqrtl(K)*v;
  cout<<R<<','<<Q<<','<<setprecision(12)<<K<<','<<rows<<','<<high<<','<<errors<<','<<main<<','<<abs_cost/budget<<','<<ceil_cost/budget<<','<<fe<<','<<Q-fe<<','<<abel/budget<<'\n';
  assert(fabsl(floor_main+fe-(high_rows+([&]{ll weighted_s=0;for(int d=1;d<R;d++)if(mu[d]){ll sd=0;for(int n=d;n<=X;n+=d)sd+=(mu[n]!=0&&hi[n]<R);weighted_s+=ll(mu[d])*(1LL<<om[d])*sd;}return weighted_s;})()))<1e-5L);
 }
}
