// Exact physical Möbius signed-residue covariance over an arbitrary square run.
// Usage: g++ -O3 -std=c++17 -Wall -Wextra -Werror -o /tmp/residue scripts/physical_square_run_residue_covariance.cpp
//        /tmp/residue 5267 5417
// Tested separately at 5267..5417, 6000..6154, 88130..88140.
// This is a finite arithmetic certificate, NOT an all-scale mixing estimate.
#include <cassert>
#include <cmath>
#include <cstdint>
#include <iomanip>
#include <iostream>
#include <vector>

static std::vector<uint32_t> primes_upto(uint32_t N) {
  std::vector<uint8_t> composite(N + 1);
  for (uint64_t p = 2; p*p <= N; ++p)
    if (!composite[p])
      for (uint64_t n = p*p; n <= N; n += p) composite[n] = 1;
  std::vector<uint32_t> result;
  for (uint32_t p=2; p<=N; ++p)
    if (!composite[p]) result.push_back(p);
  return result;
}

int main(int argc, char** argv) {
  if (argc != 3) {
    std::cerr << "Usage: residue ROOT_A ROOT_B (max span 3000000 sites)\n";
    return 2;
  }
  const uint64_t a = std::stoull(argv[1]), b = std::stoull(argv[2]);
  assert(a >= 2 && a < b && b*b-a*a <= 3000000);
  const uint64_t first=a*a, last=b*b, length=last-first;
  std::vector<uint64_t> remaining(length);
  std::vector<int8_t> mu(length, 1);
  for (uint64_t i=0; i<length; ++i) remaining[i]=first+i;

  // Segmented actual Möbius sieve, including all primes and squareful zeros.
  for (uint32_t p:primes_upto(static_cast<uint32_t>(b))) {
    uint64_t start=((first+p-1)/p)*p;
    for (uint64_t n=start; n<last; n+=p) {
      size_t j=static_cast<size_t>(n-first);
      assert(remaining[j]%p==0);
      remaining[j]/=p;
      mu[j]=static_cast<int8_t>(-mu[j]);
      while(remaining[j]%p==0) { remaining[j]/=p; mu[j]=0; }
    }
  }
  int64_t physical_mass=0;
  for (size_t j=0; j<length; ++j) {
    if (remaining[j]>1) mu[j]=static_cast<int8_t>(-mu[j]);
    physical_mass+=mu[j];
  }

  std::cout << "a,b,length,p,Mobius_mass,complement_mass,centered_covariance,Cauchy_bound,ratio_to_bound,complement_variance\n";
  for (uint32_t p:{11u,13u,19u,29u}) {
    const uint64_t q=static_cast<uint64_t>(p)*p;
    const uint64_t fsum=static_cast<uint64_t>(p-1)*(p-1);
    std::vector<int64_t> class_mass(q,0);
    int64_t complement_mass=0;
    for (uint64_t j=0;j<length;++j) {
      uint64_t n=first+j;
      int f=(n%q==0)?0:((n%p==0)?-1:1);
      int64_t complement=static_cast<int64_t>(mu[j])*f;
      assert(f*complement==mu[j]);
      class_mass[n%q]+=complement;
      complement_mass+=complement;
    }
    int64_t class_sq=0;
    for (int64_t x:class_mass) class_sq+=x*x;
    const __int128 vf=static_cast<__int128>(q)*(q-1)
        -static_cast<__int128>(fsum)*fsum;
    const __int128 vn=static_cast<__int128>(q)*class_sq
        -static_cast<__int128>(complement_mass)*complement_mass;
    const __int128 numerator=static_cast<__int128>(q)*physical_mass
        -static_cast<__int128>(fsum)*complement_mass;
    assert(vf>=0 && vn>=0 && numerator*numerator<=vf*vn);
    long double actual=static_cast<long double>(numerator)/q;
    long double bound=std::sqrt(static_cast<long double>(vf)
                                *static_cast<long double>(vn))/q;
    std::cout << a << ',' << b << ',' << length << ',' << p << ','
        << physical_mass << ',' << complement_mass << ','
        << std::fixed << std::setprecision(8)
        << actual << ',' << bound << ','
        << std::abs(actual)/bound << ','
        << static_cast<long double>(vn)/q << '\n';
  }
  return 0;
}
