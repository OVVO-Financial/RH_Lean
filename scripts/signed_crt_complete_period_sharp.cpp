// Exact full-period sup norm of the SIGNED low-prime CRT phase and
// unsigned survivor-square correction. All bounds are for ALL integers x
// by periodicity, not just a finite observed root range.
// Usage: g++ -O3 -std=c++17 -Wall -Wextra -Werror -o /tmp/phase scripts/signed_crt_complete_period_sharp.cpp
//        /tmp/phase
#include <cassert>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <vector>

int main() {
  const std::vector<uint32_t> primes={2,3,5,7,11};
  uint64_t Q=1,phi=1;
  for(uint32_t p:primes) {
    Q*=p; phi*=p-1;
    const uint64_t period=Q*Q, numerator=phi*phi;
    int64_t signed_accumulated=0;
    uint64_t signed_maxnumer=0, signed_argmax=0, positive=0,negative=0,zero=0;
    for(uint64_t n=1;n<=period;++n) {
      int sign=1;
      for(uint32_t prime:primes) {
        if(prime>p)break;
        if(n%(prime*prime)==0) {sign=0;break;}
        if(n%prime==0) sign=-sign;
      }
      signed_accumulated+=sign;
      if(sign>0) ++positive;
      else if(sign<0) ++negative;
      else ++zero;
      const int64_t difference=signed_accumulated*static_cast<int64_t>(period)
                                    -static_cast<int64_t>(n*numerator);
      const uint64_t amount=static_cast<uint64_t>(std::llabs(difference));
      if(amount>signed_maxnumer){signed_maxnumer=amount;signed_argmax=n;}
    }
    // Complete period sum must equal phi(Q)^2 by the signed CRT product law.
    assert(signed_accumulated==static_cast<int64_t>(numerator));
    assert(positive+negative+zero==period);

    uint64_t survivors=0, unsigned_maxnumer=0, unsigned_argmax=0;
    for(uint64_t n=1;n<=Q;++n) {
      bool coprime=true;
      for(uint32_t prime:primes) {
        if(prime>p)break;
        if(n%prime==0){coprime=false;break;}
      }
      survivors+=coprime;
      const int64_t difference=static_cast<int64_t>(survivors*Q)
                                    -static_cast<int64_t>(n*phi);
      const uint64_t amount=static_cast<uint64_t>(std::llabs(difference));
      if(amount>unsigned_maxnumer){unsigned_maxnumer=amount;unsigned_argmax=n;}
    }
    assert(survivors==phi);
    const double uniform_open_cap=2.0*static_cast<double>(signed_maxnumer)/period
                                +2.0*static_cast<double>(unsigned_maxnumer)/Q;
    std::cout << "y="<<p<<" Q="<<Q<<" period="<<period
        <<" rho="<<numerator<<"/"<<period
        <<" max_signed_phase="<<signed_maxnumer<<"/"<<period
        <<" at="<<signed_argmax
        <<" max_unsigned_phase="<<unsigned_maxnumer<<"/"<<Q
        <<" at="<<unsigned_argmax
        <<" uniform_open_cap="<<uniform_open_cap<<'\n';
  }
}
