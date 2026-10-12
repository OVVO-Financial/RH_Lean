// Exact prime insertion: future-suffix signs and signed-square energy.
// g++ -O3 -std=c++17 -Wall -Wextra -Werror prime_suffix_chronology_audit.cpp -o audit
// ./audit [max_root=2000] [max_random_x=1000000] [all_x_max=50000] [random_samples=4000]
#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <iomanip>
#include <iostream>
#include <limits>
#include <random>
#include <vector>

using namespace std;
struct Sieve {
  vector<int8_t> mu;
  vector<int32_t> M;
  vector<uint8_t> composite;
  vector<int> primes;
  explicit Sieve(int N):mu(N+1,1),M(N+1,0),composite(N+1,0){
    mu[0]=0;
    for(int n=2;n<=N;++n){
      if(!composite[n]){primes.push_back(n);mu[n]=-1;}
      for(int p:primes){
        int64_t v=int64_t(n)*p;
        if(v>N)break;
        composite[v]=1;
        if(n%p==0){mu[v]=0;break;}
        mu[v]=-mu[n];
      }
    }
    for(int n=1;n<=N;++n)M[n]=M[n-1]+mu[n];
  }
};

int isqrt_int(int x){
  int r=int(sqrt(double(x)));
  while(int64_t(r+1)*(r+1)<=x)++r;
  while(int64_t(r)*r>x)--r;
  return r;
}

struct Scan {
  int64_t min_suffix=0,total_delta=0,negative_mass=0,terminal_mass=0;
  int active=0,negative_steps=0,first_bad_prime=0;
};

Scan suffix_scan(const Sieve& s,int x,int first_prime){
  Scan out;
  auto first=lower_bound(s.primes.begin(),s.primes.end(),first_prime);
  auto last=upper_bound(s.primes.begin(),s.primes.end(),x/2);
  int64_t suffix=0;
  for(auto it=last;it!=first;){
    --it;
    int p=*it,k=x/p,delta=2*(1-s.M[k]);
    suffix+=delta;
    out.active++;
    if(delta<0){out.negative_mass-=delta;out.negative_steps++;}
    if(k==2)out.terminal_mass+=delta;
    if(suffix<out.min_suffix){out.min_suffix=suffix;out.first_bad_prime=p;}
  }
  out.total_delta=suffix;
  return out;
}

int main(int argc,char**argv){
  const int rmax=argc>1?atoi(argv[1]):2000;
  const int xcap=argc>2?atoi(argv[2]):1000000;
  const int all_x_cap=argc>3?atoi(argv[3]):50000;
  const int random_samples=argc>4?atoi(argv[4]):4000;
  if(rmax<2||xcap<3||all_x_cap<3||random_samples<0){
    cerr<<"invalid arguments\n";return 2;
  }
  const int64_t N64=max(int64_t(rmax)*rmax-1,int64_t(xcap));
  if(N64>numeric_limits<int>::max()){
    cerr<<"sieve too large\n";return 2;
  }
  const int N=int(N64);
  Sieve s(N);
  int root_failures=0,arbitrary_failures=0;
  int first_root_failure=0,first_arbitrary_failure=0;
  int64_t least_root_suffix=0,least_arbitrary_suffix=0;
  double worst_negative_to_terminal=0;
  int worst_negative_root=0;
  cout<<"R,X,Q,K,active,negative_steps,negative_mass,terminal_2p_mass,"
         "min_future_signed_response,outward_square_energy,outward_div_R2K\n";
  for(int R=2;R<=rmax;++R){
    const int X=R*R-1;
    const Scan sc=suffix_scan(s,X,R);
    if(sc.min_suffix<0){
      ++root_failures;
      if(!first_root_failure)first_root_failure=R;
    }
    least_root_suffix=min(least_root_suffix,sc.min_suffix);
    if(sc.terminal_mass &&
       double(sc.negative_mass)/sc.terminal_mass>worst_negative_to_terminal){
      worst_negative_to_terminal=double(sc.negative_mass)/sc.terminal_mass;
      worst_negative_root=R;
    }
    if(R==317||R==1000||R==rmax){
      double K=1;
      for(int t=0;t<R;++t){
        double z=double(s.M[t]-1);
        K=max(K,z*z/(t+1));
      }
      const int Q=2*s.M[R-1]-s.M[X];
      int64_t D=Q+sc.total_delta,outward=0;
      auto first=lower_bound(s.primes.begin(),s.primes.end(),R);
      auto last=upper_bound(s.primes.begin(),s.primes.end(),X/2);
      for(auto it=first;it!=last;++it){
        int delta=2*(1-s.M[X/(*it)]);
        int64_t updated=D-delta;
        outward+=max(int64_t(0),updated*updated-D*D);
        D=updated;
      }
      if(D!=Q){
        cerr<<"completion mismatch at R="<<R<<"\n";return 3;
      }
      cout<<R<<","<<X<<","<<Q<<","<<setprecision(9)<<K<<","
          <<sc.active<<","<<sc.negative_steps<<","<<sc.negative_mass<<","
          <<sc.terminal_mass<<","<<sc.min_suffix<<","<<outward<<","
          <<double(outward)/(double(R)*R*K)<<"\n";
    }
  }
  long double B=0,minB=numeric_limits<long double>::infinity();
  int minBindex=0;
  for(int t=2;t<rmax;++t){
    B+=(1.0L-s.M[t])/(static_cast<long double>(t)*(t+1));
    if(B<minB){minB=B;minBindex=t;}
  }
  auto check_x=[&](int x){
    const Scan sc=suffix_scan(s,x,isqrt_int(x)+1);
    if(sc.min_suffix<0){
      ++arbitrary_failures;
      if(!first_arbitrary_failure)first_arbitrary_failure=x;
    }
    least_arbitrary_suffix=min(least_arbitrary_suffix,sc.min_suffix);
  };
  for(int x=3;x<=min(all_x_cap,N);++x)check_x(x);
  mt19937 engine(20261011);
  uniform_int_distribution<int> sample_x(3,xcap);
  for(int i=0;i<random_samples;++i)check_x(sample_x(engine));
  cout<<setprecision(12)
      <<"summary roots="<<(rmax-1)
      <<" root_failures="<<root_failures
      <<" first_root_failure="<<first_root_failure
      <<" least_root_suffix="<<least_root_suffix
      <<" maximum_negative_vs_terminal="<<worst_negative_to_terminal
      <<" at_root="<<worst_negative_root<<"\n";
  cout<<"historical_B_min="<<static_cast<double>(minB)
      <<" at_t="<<minBindex<<"\n";
  cout<<"summary arbitrary_x="<<(min(all_x_cap,N)-2+random_samples)
      <<" arbitrary_failures="<<arbitrary_failures
      <<" first_arbitrary_failure="<<first_arbitrary_failure
      <<" least_arbitrary_suffix="<<least_arbitrary_suffix<<"\n";
  return root_failures+arbitrary_failures ? 1 : 0;
}
