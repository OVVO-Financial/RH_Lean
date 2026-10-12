// Reproducible: fixed-lag Pearson/Spearman can vanish while deterministic
// prime-factor parent/child sign reversal lives on MOVING square-block lags.
// g++ -O3 -std=c++17 -Wall -Wextra -Werror \
//   experiments/PrimePopulationCutoff/prime_dilation_moving_lag_audit.cpp \
//   -o /tmp/prime_dilation_moving_lag_audit
// /tmp/prime_dilation_moving_lag_audit
#include <algorithm>
#include <cmath>
#include <cstdint>
#include <iomanip>
#include <iostream>
#include <map>
#include <vector>

using namespace std;

static double pearson(const vector<double>& x, const vector<double>& y) {
  const size_t n=x.size();
  if(n!=y.size()||n<2)return NAN;
  double mx=0,my=0;
  for(size_t i=0;i<n;++i){mx+=x[i];my+=y[i];}
  mx/=n;my/=n;
  double c=0,vx=0,vy=0;
  for(size_t i=0;i<n;++i){
    const double a=x[i]-mx,b=y[i]-my;
    c+=a*b;vx+=a*a;vy+=b*b;
  }
  return c/sqrt(vx*vy);
}
static vector<double> ranks(const vector<double>& z) {
  vector<size_t>ind(z.size());
  for(size_t i=0;i<z.size();++i)ind[i]=i;
  sort(ind.begin(),ind.end(),[&](size_t a,size_t b){return z[a]<z[b];});
  vector<double>rk(z.size());
  for(size_t i=0;i<ind.size();) {
    size_t j=i+1;
    while(j<ind.size()&&z[ind[i]]==z[ind[j]])++j;
    const double avg=(i+j+1)/2.0;
    for(size_t k=i;k<j;++k)rk[ind[k]]=avg;
    i=j;
  }
  return rk;
}
static int sqroot(int64_t n) {
  int r=static_cast<int>(sqrt(static_cast<double>(n)));
  while(int64_t(r+1)*(r+1)<=n)++r;
  while(int64_t(r)*r>n)--r;
  return r;
}
int main(){
  const int Rmax=10000,pmax=3,ridgeRmax=6000;
  const int maxn=max(Rmax*Rmax-1,pmax*((ridgeRmax+1)*(ridgeRmax+1)-1));
  vector<int>least(maxn+1),primes;
  vector<int8_t>mu(maxn+1);
  mu[1]=1;
  for(int n=2;n<=maxn;++n){
    if(!least[n]){least[n]=n;primes.push_back(n);mu[n]=-1;}
    for(int p:primes){
      int64_t q=int64_t(n)*p;
      if(q>maxn||p>least[n])break;
      least[q]=p;
      if(n%p==0){mu[q]=0;break;}
      mu[q]=-mu[n];
    }
  }
  vector<int>br(Rmax),diagonal(Rmax);
  for(int r=1;r<Rmax;++r){
    for(int n=r*r;n<(r+1)*(r+1);++n){
      br[r]+=mu[n];diagonal[r]+=(mu[n]!=0);
    }
  }
  const int a=1000,b=9998;
  vector<double>z;
  int64_t signedSum=0,blockE=0;
  for(int r=a;r<=b;++r){
    z.push_back(double(br[r])/sqrt(double(diagonal[r])));
    signedSum+=br[r];blockE+=int64_t(br[r])*br[r];
  }
  const int64_t cross=(signedSum*signedSum-blockE)/2;
  cout<<setprecision(12) << "roots " << a << ".." << b
      << " count=" << z.size() << " sum=" << signedSum
      << " E=" << blockE << " cross=" << cross
      << " energy_ratio=" << double(signedSum*signedSum)/blockE << "\n";
  for(int lag:{1,2}){
    vector<double>x(z.begin(),z.end()-lag), y(z.begin()+lag,z.end());
    cout<<"block lag "<<lag<<" pearson="<<pearson(x,y)
        <<" spearman="<<pearson(ranks(x),ranks(y))<<"\n";
  }
  cout<<"prime-aligned packet pairs by moving sqrt(p) block dilation:\n";
  for(int r:{317,1000,6000})for(int p:{2,3}){
    int count=0,bad=0;
    map<int,int>lagbins;
    for(int m=r*r;m<(r+1)*(r+1);++m){
      if(mu[m]==0||m%p==0)continue;
      const int lag=sqroot(int64_t(p)*m)-r;
      ++lagbins[lag];++count;
      if(mu[m]*mu[p*m]!=-1)++bad;
    }
    cout<<"r="<<r<<" p="<<p<<" matched="<<count
        <<" sign_violations="<<bad<<" lag_distribution=";
    for(auto [lag,k]:lagbins)cout<<lag<<":"<<k<<" ";
    cout<<"\n";
    if(bad)return 2;
  }
  return 0;
}
