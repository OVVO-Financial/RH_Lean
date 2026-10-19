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
struct Shell {
  i64 b=0,q=0,k=0,upm=0,lpm=0,lowB=0,highB=0;
  i64 kLow=0,kHigh=0,primePair=0,nonprimePair=0,maxPrefixAbs=0,positivePrefixes=0,sites=0;
};
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
    const i64 oldS=s.lowB+s.highB-s.q, oldK=s.k;
    const bool prime=(n>=2 && lpf[n]==n);
    const bool smooth=(largest[n]<=r);
    if(n>=4 && prime==(lpf[n]<=r))
      throw std::runtime_error("Fixed wheel primality failed at n="+std::to_string(n));
    if(prime || !smooth) {
      const int p=largest[n],c=n/p;
      if(p<=r || c<1 || c>r || p<=c || p*c!=n || mu[n]!=-mu[c])
        throw std::runtime_error("Unique high-prime cofactor/parity failed at n="+std::to_string(n));
    }
    mertens+=a;diagonal+=a*a;
    s.k+=a*a;++s.sites;
    if(a>0)++s.upm;
    if(a<0)++s.lpm;
    if(prime)++s.q;else s.b+=a;
    if(!prime && smooth){s.lowB+=a;s.kLow+=a*a;}
    if(!prime && !smooth){s.highB+=a;s.kHigh+=a*a;}
    if(n==1){s.lowB+=a;s.kLow+=a*a;}
    const i64 A=s.lowB,H=s.highB,Q=s.q,S=A+H-Q;
    if(S!=oldS+a || s.k!=oldK+a*a || s.k!=s.kLow+s.kHigh+Q)
      throw std::runtime_error("Fixed-wheel signed source/diagonal mismatch at n="+std::to_string(n));
    const i64 aa=A*A-s.kLow,hh=H*H-s.kHigh,pp=Q*Q-Q;
    if((aa%2)!=0 || (hh%2)!=0 || (pp%2)!=0)
      throw std::runtime_error("Illegal signed pair parity");
    const i64 six=aa/2+hh/2+pp/2+A*H-A*Q-H*Q;
    const i64 previous=(oldS*oldS-oldK)/2, current=(S*S-s.k)/2;
    if(six!=current || current-previous!=a*oldS)
      throw std::runtime_error("Six-channel covariance / incremental source failed at n="+std::to_string(n));
    if(prime)s.primePair+=a*oldS;else s.nonprimePair+=a*oldS;
    if(s.primePair+s.nonprimePair!=current)
      throw std::runtime_error("Prime vs composite covariance accounting failed at n="+std::to_string(n));
    s.maxPrefixAbs=std::max(s.maxPrefixAbs,(i64)std::abs(S));
    if(current>0)++s.positivePrefixes;
  }
  auto base=[](int64_t x) {return x<=1?0.0:x/std::log(static_cast<double>(x));};
  for(int r=2;r<limit;++r) {
    auto s=shells[r];
    const i64 v=s.b-s.q;
    if(v!=s.upm-s.lpm || s.b!=s.lowB+s.highB || ((v*v-s.k)%2)!=0 ||
       s.k!=s.kLow+s.kHigh+s.q || s.sites!=2LL*r+1 ||
       s.primePair+s.nonprimePair!=(v*v-s.k)/2)
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
      <<" residual="<<s.q-predicted
      <<" fixed_smooth="<<s.lowB<<" high_composites="<<s.highB
      <<" K_smooth="<<s.kLow<<" K_high_composites="<<s.kHigh
      <<" C_smooth_smooth="<<(s.lowB*s.lowB-s.kLow)/2
      <<" C_highcomp_highcomp="<<(s.highB*s.highB-s.kHigh)/2
      <<" C_prime_prime="<<(s.q*s.q-s.q)/2
      <<" C_smooth_highcomp="<<s.lowB*s.highB
      <<" C_smooth_prime="<<-s.lowB*s.q
      <<" C_highcomp_prime="<<-s.highB*s.q
      <<" withinC="<<s.primePair+s.nonprimePair
      <<" max_partial_absS="<<s.maxPrefixAbs<<" positive_prefixes="<<s.positivePrefixes
      <<"\n";
  }
  for(int h:{256,512,1024,2048,4096}) {
    if(2*h>limit)continue;
    i64 E=0,D=0,B2=0,Q2=0,BQ=0,Bsum=0,Qsum=0;
    i64 A2=0,H2=0,AH=0,AQ=0,HQ=0,maxEnergy=0,pos=0;
    for(int r=h;r<2*h;++r) {
      const auto &s=shells[r];const i64 v=s.b-s.q;
      E+=v*v;D+=s.k;B2+=s.b*s.b;Q2+=s.q*s.q;BQ+=s.b*s.q;
      Bsum+=s.b;Qsum+=s.q;
      A2+=s.lowB*s.lowB;H2+=s.highB*s.highB;
      AH+=2*s.lowB*s.highB;
      AQ-=2*s.lowB*s.q;
      HQ-=2*s.highB*s.q;
      maxEnergy+=s.maxPrefixAbs*s.maxPrefixAbs;
      if((v*v-s.k)>0)++pos;
    }
    if(E!=B2+Q2-2*BQ || E!=A2+H2+Q2+AH+AQ+HQ || (E-D)%2!=0)
      throw std::runtime_error("Failed signed covariance decomposition at H "+std::to_string(h));
    if((h==256 && E!=110216)||(h==1024 && E!=1723387))
      throw std::runtime_error("Inconsistent historical dyadic energy at H "+std::to_string(h));
    std::cout<<"BAND "<<h<<" energy="<<E<<" diagonal="<<D
      <<" withinCov="<<(E-D)/2<<" B2="<<B2<<" Q2="<<Q2<<" mixed="<<-2*BQ
      <<" signed B-Q="<<Bsum-Qsum
      <<" smooth2="<<A2<<" high_composite2="<<H2
      <<" highprime2="<<Q2<<" smooth_highcomposite2="<<AH
      <<" smooth_prime2="<<AQ<<" highcomposite_prime2="<<HQ
      <<" positive_covariance_shells="<<pos<<" max_partial_energy="<<maxEnergy
      <<" E/H^2="<<static_cast<double>(E)/(1LL*h*h)
      <<" E/H^2.5="<<E/std::pow(static_cast<double>(h),2.5)<<"\n";
  }
  int handoffs=0,staticWheelSteps=0;
  std::vector<i64> parentM(limit+1,0),parentK(limit+1,0);
  for(int p=1;p<=limit;++p) {
    parentM[p]=parentM[p-1]+mu[p];
    parentK[p]=parentK[p-1]+mu[p]*mu[p];
  }
  for(int p=2;p<limit;++p) {
    if(lpf[p]!=p) {
      if(pi[p]!=pi[p-1])throw std::runtime_error("Composite root incorrectly changed wheel");
      ++staticWheelSteps;
      continue;
    }
    i64 moved=0,diagMoved=0;
    for(int c=1;c<p;++c) {
      int n=p*c;
      if(n>=p*p || largest[n]!=p || mu[n]!=-mu[c])
        throw std::runtime_error("Prime-square fixed-wheel owner mismatch");
      moved+=mu[n];diagMoved+=mu[n]*mu[n];
    }
    if(moved!=-parentM[p-1] || diagMoved!=parentK[p-1] ||
       pi[p]!=pi[p-1]+1 || mu[p*p]!=0)
      throw std::runtime_error("Prime-square chronological wheel handoff failed");
    ++handoffs;
  }
  std::cout<<"WHEEL_EVENTS prime_square_handoffs="<<handoffs
    <<" composite_root_no_change="<<staticWheelSteps<<"\n";
  std::cout<<"PASS all true Mobius shells below "<<nmax+1
    <<" | M="<<mertens<<" squarefree diagonal="<<diagonal<<"\n";
}
