// Exact, integer-only three-stratum Euler prime population and dyadic sampler.
// Reuse the independently tested original Mobius/prime-count sieve implementation.
// No random signs, model distributions, fitted exponents or Li surrogates.
#define main baseline_admissible_euler_probe_main
#include "euler_admissible_population_probe.cpp"
#undef main

#include <array>

struct Three {
  int64_t low;
  int64_t middle; // signed composite response, can be positive or negative
  int64_t top;    // negative count of primes in (X/2,X]
  int64_t mertens;
};

struct SixMoment {
  int64_t ll=0, mm=0, tt=0, lm=0, lt=0, mt=0, total=0;
};

Three three_at(int root, const Sieve &s) {
  const int x = root * root - 1;
  const int lower = root - 1;
  const int64_t top = -static_cast<int64_t>(s.pi[x]-s.pi[x/2]);
  int64_t middle_debt = 0;
  for (int k=2; k<root; ++k) {
    int left = std::max(lower, x/(k+1));
    int right = x/k;
    assert(left<=right);
    const int64_t count = static_cast<int64_t>(s.pi[right]-s.pi[left]);
    middle_debt += s.mertens[k]*count;
  }
  const int64_t middle = -middle_debt;
  const int64_t mertens = s.mertens[x];
  const int64_t low = mertens-middle-top;
  assert(low+middle+top==mertens);
  return {low,middle,top,mertens};
}

void independent_at(int root, const Sieve &s, const Three &v) {
  const int x=root*root-1;
  int64_t direct_low=0, direct_middle_debt=0;
  for (int n=1;n<=x;++n)
    if (s.largest[n] < static_cast<uint32_t>(root)) direct_low+=s.mu[n];
  for (int p:s.primes) {
    if (p<x/2+1 && p>=root) direct_middle_debt += s.mertens[x/p];
    if (p>x/2) break;
  }
  const auto prime_begin=std::upper_bound(s.primes.begin(),s.primes.end(),x/2);
  const auto prime_end=std::upper_bound(s.primes.begin(),s.primes.end(),x);
  const auto direct_top=-(prime_end-prime_begin);
  assert(v.low==direct_low);
  assert(v.middle==-direct_middle_debt);
  assert(v.top==direct_top);
  std::cout<<"R="<<root<<" X="<<x<<" low="<<v.low
     <<" middle="<<v.middle<<" top="<<v.top
     <<" M(X)="<<v.mertens<<"\n";
}

SixMoment window(const std::vector<Three> &v,int H) {
  SixMoment s;
  for (int r=H; r<2*H; ++r) {
    const int64_t a=v[r+1].low-v[r].low;
    const int64_t b=v[r+1].middle-v[r].middle;
    const int64_t c=v[r+1].top-v[r].top;
    const int64_t d=v[r+1].mertens-v[r].mertens;
    assert(a+b+c==d);
    s.ll+=a*a;
    s.mm+=b*b;
    s.tt+=c*c;
    s.lm+=2*a*b;
    s.lt+=2*a*c;
    s.mt+=2*b*c;
    s.total+=d*d;
  }
  assert(s.ll+s.mm+s.tt+s.lm+s.lt+s.mt==s.total);
  return s;
}

int main() {
  constexpr int maxR=10000;
  Sieve s(maxR*maxR-1);
  std::vector<Three> values(maxR+1);
  int sign_positive=0,sign_zero=0,sign_negative=0;
  for (int root=2;root<=maxR;++root) {
    values[root]=three_at(root,s);
    if (values[root].middle>0) ++sign_positive;
    else if (values[root].middle<0) ++sign_negative;
    else ++sign_zero;
    if (root==317||root==1027||root==5561||root==10000)
      independent_at(root,s,values[root]);
  }
  std::cout<<"ALL ROOTS 2.."<<maxR
    <<" middle positive="<<sign_positive
    <<" middle negative="<<sign_negative
    <<" middle zero="<<sign_zero<<"\n";

  for (int H : std::array<int,5>{{16,64,256,1024,4096}}) {
    SixMoment m=window(values,H);
    const int64_t diagonals=m.ll+m.mm+m.tt;
    const int64_t crosses=m.lm+m.lt+m.mt;
    std::cout<<"H="<<H<<" shellEnergy="<<m.total
      <<" diagonalThree="<<diagonals
      <<" crossThree="<<crosses
      <<" LL="<<m.ll<<" MM="<<m.mm<<" TT="<<m.tt
      <<" 2LM="<<m.lm<<" 2LT="<<m.lt<<" 2MT="<<m.mt<<"\n";
  }
  std::cout<<"PASS independent three-stratum prime-product population,"
    <<" top prime singleton, six-moment square-block sampler\n";
}
