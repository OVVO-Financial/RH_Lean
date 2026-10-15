// Exact finite-prefix Mertens extension experiment, 2026-10-15.
// Requires C++17 and Boost headers. All accepted power comparisons use
// arbitrary-precision integers. Floating-point estimates only seed corrected
// integer searches; they never decide an inequality.
// Usage: ./finite_certificate [output_directory]
// Finite computation, not a global envelope-preservation theorem.
#include <algorithm>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <filesystem>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>
#include <boost/multiprecision/cpp_int.hpp>
using boost::multiprecision::cpp_int;
cpp_int ipow(uint64_t x,int k){cpp_int a=x,b=1;while(k){if(k&1)b*=a;k>>=1;if(k)a*=a;}return b;}
uint64_t isqrt(uint64_t x){uint64_t r=std::sqrt((long double)x);while((r+1)*(r+1)<=x)++r;while(r*r>x)--r;return r;}
uint64_t floorpow(uint64_t n,int p,int q){uint64_t b=std::pow((long double)n,(long double)p/q);auto rhs=ipow(n,p);while(ipow(b+1,q)<=rhs)++b;while(ipow(b,q)>rhs)--b;return b;}
std::vector<int> sieve(unsigned N){std::vector<int>mu(N+1,1);std::vector<bool>comp(N+1);mu[0]=0;for(unsigned p=2;p<=N;++p)if(!comp[p]){for(unsigned k=p;k<=N;k+=p){mu[k]=-mu[k];if(k>p)comp[k]=true;}if(p<=N/p)for(unsigned k=p*p;k<=N;k+=p*p)mu[k]=0;}return mu;}
struct Predictor {
 std::vector<int> mu;std::vector<int64_t>M;
 explicit Predictor(unsigned N):mu(sieve(N)),M(N+1){for(unsigned n=1;n<=N;++n)M[n]=M[n-1]+mu[n];}
 int64_t at(uint64_t x)const {
  if(x<mu.size())return M[x];
  uint64_t r=isqrt(x);if(r>=mu.size())throw std::runtime_error("insufficient prefix");
  int64_t sum=0;
  for(uint64_t i=1;i<=r;++i)if(mu[i]){
   sum+=(int64_t)mu[i]*mu[i]*(x/(i*i));
   for(uint64_t j=i+1;j<=r;++j)if(mu[j])sum+=2LL*mu[i]*mu[j]*(int64_t)(x/(i*j));
  }
  return 2*M[r]-sum;
 }
};
int main(int argc,char**argv){
 try{
  if(argc>2)throw std::runtime_error("usage: finite_certificate [output_directory]");
  const std::filesystem::path output=argc==2?argv[1]:".";
  std::filesystem::create_directories(output);
  const unsigned N=1000;const uint64_t X=(N+1ULL)*(N+1ULL)-1;Predictor P(N);
  std::cout<<"{\"prefix\":"<<N<<",\"extended_through\":"<<X<<",\"certificates\":[";
  bool comma=false;
  for(auto pq:std::vector<std::pair<int,int>>{{9,20},{51,100}}){
   int p=pq.first,q=pq.second;
   for(unsigned n=1;n<=N;++n)if(ipow(std::abs(P.M[n]),q)>ipow(n,p))throw std::runtime_error("bad initial envelope");
   std::ofstream out(output/("certificate_"+std::to_string(p)+"_"+std::to_string(q)+".csv"));
   if(!out)throw std::runtime_error("cannot write certificate");
   out<<"left,right,M_left,integer_power_floor\n";
   uint64_t L=N+1,anchors=0,total=0;
   while(L<=X){int64_t m=P.at(L);uint64_t B=floorpow(L,p,q);if(B<(uint64_t)std::abs(m))throw std::runtime_error("envelope failure at "+std::to_string(L));
    uint64_t R=std::min<uint64_t>(X,L+B-std::abs(m));out<<L<<","<<R<<","<<m<<","<<B<<"\n";
    total+=R-L+1;++anchors;L=R+1;
   }
   if(comma)std::cout<<",";comma=true;
   std::cout<<"{\"p\":"<<p<<",\"q\":"<<q<<",\"anchors\":"<<anchors<<",\"covered_new_integers\":"<<total<<"}";
  }
  Predictor W(5547);
  std::cout<<"],\"first_failure_witness\":[";
  for(uint64_t n=30770120;n<=30770121;++n){if(n>30770120)std::cout<<",";int64_t m=W.at(n);cpp_int gap=ipow(std::abs(m),20)-ipow(n,9);std::cout<<"{\"n\":"<<n<<",\"M_from_prefix\":"<<m<<",\"power_gap\":\""<<gap<<"\"}";}
  std::cout<<"]}\n";
 }catch(const std::exception&e){std::cerr<<e.what()<<"\n";return 1;}
}
