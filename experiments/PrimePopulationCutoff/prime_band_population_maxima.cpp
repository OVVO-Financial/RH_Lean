// Exact all-x sequential-prime band maxima and root-wheel survivor census.
// g++ -O3 -std=c++17 -Wall -Wextra -Werror prime_band_population_maxima.cpp -o band_audit
// ./band_audit 6000 200000
#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <iomanip>
#include <iostream>
#include <limits>
#include <vector>

using namespace std;

static int isqrt_int(int n) {
  int r = static_cast<int>(sqrt(static_cast<double>(n)));
  while (int64_t(r + 1) * (r + 1) <= n) ++r;
  while (int64_t(r) * r > n) --r;
  return r;
}

struct Sieve {
  vector<int> spf, M, picount, primes;
  vector<int8_t> mu;
  explicit Sieve(int n) : spf(n+1), M(n+1), picount(n+1),
                          mu(n+1) {
    mu[1] = 1;
    for (int i=2; i<=n; ++i) {
      if (!spf[i]) { spf[i]=i; primes.push_back(i); mu[i]=-1; }
      for (int p : primes) {
        int64_t q = int64_t(i)*p;
        if (q>n || p>spf[i]) break;
        spf[q]=p;
        mu[q]=(i%p==0 ? 0 : -mu[i]);
      }
    }
    for (int i=1; i<=n; ++i) {
      M[i]=M[i-1]+mu[i];
      picount[i]=picount[i-1]+(i>1 && spf[i]==i);
    }
  }
  int prime_band(int x,int k,int root) const {
    // Actual primes p>root with floor(x/p)=k.
    const int upper=x/k;
    const int lower=max(root,x/(k+1));
    return (upper>lower ? picount[upper]-picount[lower] : 0);
  }
  int top_half_survivors_by_root_wheel(int x) const {
    // For n>floor(x/2), no prime divisor <=sqrt(x) iff n is prime.
    int root=isqrt_int(x),lo=x/2+1;
    vector<uint8_t> alive(x-lo+1,1);
    for(int p:primes) {
      if(p>root) break;
      int first=((lo+p-1)/p)*p;
      for(int64_t n=first;n<=x;n+=p) alive[n-lo]=0;
    }
    int total=0;
    for(uint8_t bit:alive) total+=bit;
    return total;
  }
};

struct Result {
  int64_t max_earlier_minus_xthird=0;
  int64_t maximal_root_to_xthird_gain=0;
  int max_k=0;
};

Result test_endpoint(const Sieve& s,int x) {
  const int root=isqrt_int(x);
  int64_t prefix=0,largest=0,smallest=0;
  int peak_k=0;
  // A_y = A_(x/3) + sum_{j=3}^k M(j)*H_j(x)
  // at the earlier reciprocal-band boundaries.
  // Between boundaries the walk is monotone because each prime in
  // a band contributes exactly -M(k).
  for(int k=3;k<=root;++k) {
    prefix+=int64_t(s.M[k])*s.prime_band(x,k,root);
    if(prefix>largest){largest=prefix;peak_k=k;}
    smallest=min(smallest,prefix);
  }
  return {largest,-smallest,peak_k};
}

int main(int argc,char**argv) {
  int rootmax=(argc>1 ? atoi(argv[1]) : 6000);
  int allxmax=(argc>2 ? atoi(argv[2]) : 200000);
  if(rootmax<2 || allxmax<9) return 2;
  int64_t max_needed=max(int64_t(rootmax)*rootmax-1,
                         int64_t(allxmax));
  if(max_needed>numeric_limits<int>::max()) {
    cerr << "endpoint exceeds supported int range\n"; return 2;
  }
  Sieve s(static_cast<int>(max_needed));
  for(int k=3;k<=93;++k) {
    if(s.M[k]>0) {cerr<<"unexpected historical sign at "<<k<<"\n";return 3;}
  }
  if(s.M[94]!=1 || s.M[95]!=2) {
    cerr<<"historical threshold mismatch\n"; return 3;
  }

  cout<<"x,root,top_half_wheel_primes,stage_xthird,final_M,"
         "max_earlier_excess,prior_positive_gain\n";
  const vector<int> examples={20,317,1027,100488,999999,35999999};
  for(int x:examples) {
    if(x>max_needed) continue;
    int top=s.picount[x]-s.picount[x/2];
    int rootWheel=s.top_half_survivors_by_root_wheel(x);
    if(rootWheel!=top) {
      cerr<<"root-wheel / genuine-prime mismatch x="<<x<<"\n";
      return 4;
    }
    const auto audit=test_endpoint(s,x);
    cout<<x<<","<<isqrt_int(x)<<","<<rootWheel<<","
        <<s.M[x]+top<<","<<s.M[x]<<","
        <<audit.max_earlier_minus_xthird<<","
        <<audit.maximal_root_to_xthird_gain<<"\n";
  }

  int root_fails=0,earliest_root=0,arbitrary_fails=0,earliest_x=0;
  int max_root_excess=0,maximum_root_excess_at=0;
  for(int r=2;r<=rootmax;++r) {
    int x=r*r-1;
    const auto result=test_endpoint(s,x);
    if(result.max_earlier_minus_xthird>0) {
      if(!earliest_root) earliest_root=r;
      ++root_fails;
    }
    if(result.max_earlier_minus_xthird>max_root_excess) {
      max_root_excess=static_cast<int>(result.max_earlier_minus_xthird);
      maximum_root_excess_at=r;
    }
  }
  for(int x=9;x<=allxmax;++x) {
    const auto result=test_endpoint(s,x);
    if(result.max_earlier_minus_xthird>0) {
      if(!earliest_x) earliest_x=x;
      ++arbitrary_fails;
    }
  }
  cout<<"square_roots="<<rootmax-1
      <<" violating_xthird_global_postroot_max="<<root_fails
      <<" earliest_root="<<earliest_root
      <<" greatest_violation="<<max_root_excess
      <<" greatest_violation_root="<<maximum_root_excess_at<<"\n";
  cout<<"arbitrary_integer_endpoints="<<allxmax-8
      <<" violating_xthird_global_postroot_max="<<arbitrary_fails
      <<" earliest_x="<<earliest_x<<"\n";
  cout<<"historical M(93)="<<s.M[93]<<" M(94)="<<s.M[94]
      <<" M(95)="<<s.M[95]
      <<"; first possible negative native postroot update: "
      <<"x=9118,p=97,k=94,delta=-1\n";
  return root_fails || arbitrary_fails ? 1 : 0;
}
