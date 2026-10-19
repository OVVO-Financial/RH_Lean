// Exact square-shell Euler prime/composite response.
// First-order x/log(x) is a comparison, never a substitute for true primes.
// g++ -O3 -std=c++17 -Wall -Wextra -Werror scripts/vf919_euler_prime_response_census.cpp -o /tmp/euler_census
// /tmp/euler_census 2048       (CI: includes 317/1027 and H=1024)
// /tmp/euler_census 10000      (independent extended census to 10^8)
#include <algorithm>
#include <cmath>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <vector>
using i64 = long long;
struct Shell {i64 b=0,q=0,k=0,upm=0,lpm=0,lowB=0,highB=0;};
int main(int argc,char **argv) {
  const int limit=argc>1?std::stoi(argv[1]):2048;
  if(limit<1028 || limit>10000) throw std::invalid_argument("1028 <= root limit <= 10000");
  const int64_t nmax=1LL*limit*limit-1;
  std::vector<int> lpf(nmax+1,0),largest(nmax+1,0),primes;
  std::vector<int8_t> mu(nmax+1,0);
  mu[1]=1;
  for(int n=2;n<=nmax;++n) {
    if(lpf[n]==0) {lpf[n]=n;largest[n]=n;mu[n]=-1;primes.push_back(n);}
    for(int p:primes) {
      int64_t v=1LL*n*p;
      if(v>nmax || p>lpf[n]) break;
      lpf[v]=p;largest[v]=std::max(largest[n],p);
      if(n%p==0) {mu[v]=0;break;}
      mu[v]=-mu[n];
    }
  }
  std::vector<Shell> shells(limit);
  std::vector<int> pi(limit+1,0);
  for(int p:primes) {if(p>limit)break;++pi[p];}
  for(int r=1;r<=limit;++r)pi[r]+=pi[r-1];
  i64 mertens=0,diagonal=0;
  for(int n=1,r=1;n<=nmax;++n) {
    while(1LL*(r+1)*(r+1)<=n) ++r;
    const int a=mu[n];
    auto &s=shells[r];
    mertens+=a;diagonal+=a*a;
    s.k+=a*a;
    if(a>0)++s.upm;
    if(a<0)++s.lpm;
    if(n>=2&&lpf[n]==n)++s.q;
    else s.b+=a;
    if(a && largest[n]<=r)s.lowB+=a;
    if(a && largest[n]>r && lpf[n]!=n)s.highB+=a;
  }
  auto base=[](int64_t x) {return x<=1?0.0:x/std::log(static_cast<double>(x));};
  for(int r=2;r<limit;++r) {
    auto s=shells[r];
    const i64 v=s.b-s.q;
    if(v!=s.upm-s.lpm || s.b!=s.lowB+s.highB || ((v*v-s.k)%2)!=0)
      throw std::runtime_error("Failed physical Euler shell identity at root "+std::to_string(r));
  }
  for(int r:{317,1027}) {
    const Shell s=shells[r];
    const i64 q=(r==317?54:144), b=(r==317?65:124), ss=(r==317?11:-20);
    const i64 k=(r==317?387:1252);
    if(s.q!=q||s.b!=b||s.b-s.q!=ss||s.k!=k)
      throw std::runtime_error("Incorrect exact historical root "+std::to_string(r));
    const double predicted=base(1LL*(r+1)*(r+1)-1)-base(1LL*r*r-1);
    std::cout<<"ROOT "<<r<<" pi(root)="<<pi[r]<<" prime arrivals="<<s.q
      <<" signed composites="<<s.b<<" lowB="<<s.lowB<<" highB="<<s.highB
      <<" shell="<<ss<<" K="<<s.k<<" x/logx shell baseline="<<predicted
      <<" residual="<<s.q-predicted<<"\n";
  }
  for(int h:{256,512,1024,2048,4096}) {
    if(2*h>limit)continue;
    i64 E=0,D=0,B2=0,Q2=0,BQ=0,Bsum=0,Qsum=0;
    for(int r=h;r<2*h;++r) {
      const auto &s=shells[r];const i64 v=s.b-s.q;
      E+=v*v;D+=s.k;B2+=s.b*s.b;Q2+=s.q*s.q;BQ+=s.b*s.q;
      Bsum+=s.b;Qsum+=s.q;
    }
    if(E!=B2+Q2-2*BQ || (E-D)%2!=0)
      throw std::runtime_error("Failed signed covariance decomposition at H "+std::to_string(h));
    if((h==256 && E!=110216)||(h==1024 && E!=1723387))
      throw std::runtime_error("Inconsistent historical dyadic energy at H "+std::to_string(h));
    std::cout<<"BAND "<<h<<" energy="<<E<<" diagonal="<<D
      <<" withinCov="<<(E-D)/2<<" B2="<<B2<<" Q2="<<Q2<<" mixed="<<-2*BQ
      <<" signed B-Q="<<Bsum-Qsum
      <<" E/H^2="<<static_cast<double>(E)/(1LL*h*h)
      <<" E/H^2.5="<<E/std::pow(static_cast<double>(h),2.5)<<"\n";
  }
  std::cout<<"PASS all true Mobius shells below "<<nmax+1
    <<" | M="<<mertens<<" squarefree diagonal="<<diagonal<<"\n";
}
