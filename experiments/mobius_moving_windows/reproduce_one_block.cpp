// Reproduce the exact integer shell/window measurements from the finite census.
// g++ -O3 -std=c++17 -Wall -Wextra -Werror reproduce_one_block.cpp -o mw_census
// ./mw_census 4096 512          # or ./mw_census 8192 861 (uses ~2.3 GiB RAM)
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <iomanip>
#include <iostream>
#include <vector>
using i64 = std::int64_t;
int main(int argc, char** argv) {
    if (argc != 3) { std::cerr << "usage: mw_census H T\n"; return 2; }
    const int H = std::atoi(argv[1]), T = std::atoi(argv[2]);
    if (H < 8 || H > 8192 || T < 0 || T >= H) {
        std::cerr << "require 8 <= H <= 8192 and 0 <= T < H\n"; return 2;
    }
    const i64 N = 4LL*H*H + T + 5;
    std::vector<std::uint32_t> lp(static_cast<std::size_t>(N)+1,0);
    std::vector<std::int8_t> mu(static_cast<std::size_t>(N)+1,0);
    std::vector<std::uint32_t> primes;
    mu[1]=1;
    for(std::uint32_t i=2;i<=N;i++) {
        if(!lp[i]) { lp[i]=i; primes.push_back(i); mu[i]=-1; }
        for(auto p:primes) {
            const std::uint64_t v=static_cast<std::uint64_t>(i)*p;
            if(v>static_cast<std::uint64_t>(N)||p>lp[i]) break;
            lp[static_cast<std::size_t>(v)]=p;
            if(p==lp[i]) {mu[static_cast<std::size_t>(v)]=0;break;}
            mu[static_cast<std::size_t>(v)]=static_cast<std::int8_t>(-mu[i]);
        }
    }
    std::vector<std::int32_t> M(static_cast<std::size_t>(N)+1,0);
    for(i64 i=1;i<=N;i++) M[static_cast<std::size_t>(i)] = M[static_cast<std::size_t>(i-1)]+mu[static_cast<std::size_t>(i)];
    const auto sum = [&](i64 a,i64 b)->i64 {return M[static_cast<std::size_t>(b)]-M[static_cast<std::size_t>(a-1)];};
    i64 E=0,W=0,D=0,signed_delta=0;
    long double mean_mode=0;
    for(int r=H;r<2*H;r++) {
        const i64 root=static_cast<i64>(r)*r;
        const i64 delta=sum(root+1,root+2*r);
        E+=delta*delta;
        signed_delta+=delta;
        i64 local_mean_sum=0;
        // Diagonal at first shift; update by one entering and one exiting site.
        const i64 left=root-T+1, right=root-T+2*r;
        i64 local_d=0;
        for(i64 k=left;k<=right;k++) local_d+=(mu[static_cast<std::size_t>(k)]!=0);
        for(int t=-T;t<=T;t++) {
            if(t>-T) {
                const i64 leaving=root+t;
                const i64 entering=root+t+2*r;
                local_d+=(mu[static_cast<std::size_t>(entering)]!=0)-(mu[static_cast<std::size_t>(leaving)]!=0);
            }
            const i64 s=sum(root+t+1,root+t+2*r);
            local_mean_sum+=s; W+=s*s; D+=local_d;
        }
        mean_mode+=static_cast<long double>(local_mean_sum)*local_mean_sum/(2*T+1);
    }
    if(T>=1 && 3LL*T*E > 3LL*W+4LL*H*T*(static_cast<i64>(T)*T-1)) {
        std::cerr<<"deterministic inequality failed\n";return 1;
    }
    std::cout<<std::setprecision(16)<<"H="<<H<<" T="<<T<<" E="<<E
      <<" signed_delta="<<signed_delta<<" W="<<W<<" D="<<D
      <<" offdiag_twice="<<(W-D)<<" mean_mode="<<static_cast<double>(mean_mode)
      <<" mean_fraction="<<static_cast<double>(mean_mode/W)<<"\n";
}
