// Exact genuine-Moebius second-centering census, with no analytic hypotheses.
// All shells 3..R, all dyadic gcd bands, all divisor channels d<=r.
// Test: g++ -O3 -std=c++17 -Wall -Wextra -Werror FILE -o /tmp/shell && /tmp/shell 4096
#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <iomanip>
#include <iostream>
#include <vector>
using i64 = long long;
int main(int argc, char** argv) {
  const int R = argc >= 2 ? std::atoi(argv[1]) : 4096;
  if (R < 32 || R > 8192) { std::cerr << "Require 32<=R<=8192\n"; return 2; }
  const int X = (R + 1) * (R + 1);
  std::vector<int> lp(X+1), big(X+1), primes;
  std::vector<int8_t> mu(X+1);
  mu[1] = 1;
  for (int n=2; n<=X; ++n) {
    if (!lp[n]) { lp[n]=big[n]=n; mu[n]=-1; primes.push_back(n); }
    for (int p: primes) {
      i64 m=1LL*n*p;
      if (m>X || p>lp[n]) break;
      lp[m]=p;
      big[m]=std::max(big[n],p);
      if (n%p==0) { mu[m]=0; break; }
      mu[m]=-mu[n];
    }
  }
  constexpr int NB=14;
  struct Row {
    i64 count=0, energy=0, lowD1=0, lowOthers=0;
    long double worst=0;
    int witness=0;
  };
  std::vector<Row> dyadic(NB);
  i64 checks=0;
  long double worstLow=0, worstEnergy=0;
  int worstLowR=0, worstEnergyR=0;
  for (int r=3;r<=R;++r) {
    const int L=r*r, U=L+2*r;
    std::vector<int> F(r+1), B(r+1), T(r+1), z(r+1);
    // Full and independently calculated smooth divisibility profiles.
    for (int d=1;d<=r;++d)
      for (int n=(L/d+1)*d;n<=U;n+=d) {
        F[d]+=mu[n];
        if (big[n]<=r) B[d]+=mu[n];
      }
    int primesInShell=0;
    for (int n=L+1;n<=U;++n) {
      if (lp[n]==n) ++primesInShell;
      if (mu[n] && big[n]>r) {
        const int c=n/big[n];
        if (c<1 || c>r) {std::cerr<<"bad high-prime cofactor\n";return 1;}
        // mu(qc)=-mu(c), and transport is sign-reversed.
        z[c]+=mu[c];
      }
    }
    if (z[1]!=primesInShell) {std::cerr<<"prime-only owner failure\n";return 1;}
    for (int d=1;d<=r;++d) {
      for (int c=d;c<=r;c+=d) T[d]+=z[c];
      if (F[d]!=B[d]-T[d]) {
        std::cerr<<"greatest-prime profile failure r="<<r<<" d="<<d<<"\n";
        return 1;
      }
    }
    // beta_D(d)=sum_(k|d, D<=k<2D) mu(d/k), for every dyadic D.
    std::vector<std::vector<int>> beta(NB,std::vector<int>(r+1));
    for (int k=1;k<=r;++k) {
      const int j=31-__builtin_clz((unsigned)k);
      if (j>=NB) {std::cerr<<"band overflow\n";return 1;}
      for (int a=1;a<=r/k;++a) beta[j][k*a]+=mu[a];
    }
    // Every coefficient, not just its weighted moment, telescopes to delta(d=1).
    for (int d=1;d<=r;++d) {
      int sum=0;
      for (int b=0;b<NB;++b) sum+=beta[b][d];
      if (sum!=int(d==1)) {
        std::cerr<<"Möbius band collapse failure r="<<r<<" d="<<d<<"\n";
        return 1;
      }
      if (!mu[d] && F[d]) {
        std::cerr<<"squareful divisor channel survives r="<<r<<" d="<<d<<"\n";
        return 1;
      }
    }
    i64 allLow=0, allFull=0, lowD1=0;
    for (int band=0;band<NB;++band) {
      i64 low=0,high=0;
      for (int d=1;d<=r;++d) {
        const i64 term=1LL*beta[band][d]*F[d]*F[d];
        if (1LL*d*d<r) low+=term;
        else high+=term;
      }
      allLow+=low;
      allFull+=low+high;
      if (band==0) lowD1=low;
    }
    const i64 energy=1LL*F[1]*F[1];
    if (allLow!=energy || allFull!=energy ||
        lowD1-energy != -(allLow-lowD1)) {
      std::cerr<<"zero mode hidden r="<<r<<"\n";
      return 1;
    }
    const int j=31-__builtin_clz((unsigned)r);
    auto& row=dyadic[j];
    row.count++;row.energy+=energy;
    row.lowD1+=lowD1;row.lowOthers+=allLow-lowD1;
    const long double lowRatio=std::abs((long double)lowD1) /
        std::pow((long double)r,1.5L);
    const long double energyRatio=(long double)energy /
        std::pow((long double)r,1.5L);
    if (lowRatio>row.worst) {row.worst=lowRatio;row.witness=r;}
    if (lowRatio>worstLow) {worstLow=lowRatio;worstLowR=r;}
    if (energyRatio>worstEnergy) {worstEnergy=energyRatio;worstEnergyR=r;}
    if (r==14 || r==31 || r==137 || r==317 || r==1000 ||
        r==2000 || r==3000 || r==4096 || r==R) {
      std::cout<<"SHELL r="<<r<<" primes="<<primesInShell
               <<" delta="<<F[1]<<" energy="<<energy
               <<" lowD1="<<lowD1<<" lowHigher="<<lowD1-energy
               <<" otherBands="<<allLow-lowD1<<"\n";
    }
    ++checks;
  }
  std::cout << "DYADIC H shells energy/H^2.5 lowD1/H^2.5 otherBands/H^2.5 worst|lowD1|/r^1.5\n";
  for (int b=0;b<NB;++b) if (dyadic[b].count>=16) {
    const auto& row=dyadic[b];
    const long double scale=std::pow((long double)(1<<b),2.5L);
    std::cout << (1<<b) << " " << row.count << " "
              << std::fixed << std::setprecision(8)
              << (double)(row.energy/scale) << " "
              << (double)(row.lowD1/scale) << " "
              << (double)(row.lowOthers/scale) << " "
              << (double)row.worst << " at r=" << row.witness << "\n";
  }
  std::cout<<"PEAK |lowD1|/r^1.5="<<(double)worstLow<<" r="<<worstLowR
           <<" peak energy/r^1.5="<<(double)worstEnergy
           <<" r="<<worstEnergyR<<"\n";
  std::cout<<"PASS: all "<<checks<<" shells and all dyadic gcd bands, "
           <<"exact coefficient delta, zero-mode and physical owner channels\n";
  std::cout<<"OPEN: uniform signed low-divisor moment at r^(3/2+eta)\n";
}