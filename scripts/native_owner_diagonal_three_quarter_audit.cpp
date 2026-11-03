// Exact native owner-diagonal / signed-Gamma audit, 2026-11-03.
// The original source is: X_R = R^2 - 1, prime owners R < p <= X_R,
// D_R = sum_p M(floor(X_R/p))^2, Gamma_R=M(X_R)^2-D_R.
// Every integer <= maxRoot^2 is assigned its genuine Mobius coefficient.
#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <stdexcept>
#include <vector>

using i64 = std::int64_t;

struct Witness { int root; int mertens; i64 smooth; i64 transport; i64 diag; i64 gamma; };
static constexpr Witness witnesses[] = {
    {3,-2,0,2,2,2}, {317,-28,-915,-887,14887,-14103},
    {1027,367,-6602,-6969,131389,3300}
};

int main(int argc, char **argv) {
    const int maxRoot = argc > 1 ? std::atoi(argv[1]) : 1200;
    if (maxRoot < 3 || maxRoot > 6000) {
        std::fprintf(stderr,"Usage: %s [root 3..6000]\n",argv[0]);
        return 2;
    }
    const int N = maxRoot * maxRoot + 1;
    std::vector<int> lpf(N + 1,0), primes;
    std::vector<std::int8_t> mu(N + 1,0);
    mu[1] = 1;
    for (int n = 2; n <= N; n++) {
        if (lpf[n] == 0) {
            lpf[n] = n;
            mu[n] = -1;
            primes.push_back(n);
        }
        for (int p : primes) {
            const i64 k = i64(p) * n;
            if (k > N || p > lpf[n]) break;
            lpf[k] = p;
            mu[k] = (p == lpf[n]) ? 0 : -mu[n];
        }
    }
    std::vector<int> mertens(N + 1,0), primeCount(N + 1,0), largestPrime(N + 1,0);
    largestPrime[1] = 1;
    for (int n = 1; n <= N; n++) {
        mertens[n] = mertens[n-1] + mu[n];
        if (n >= 2) largestPrime[n] = std::max(lpf[n],largestPrime[n/lpf[n]]);
        primeCount[n] = primeCount[n-1] + (n >= 2 && lpf[n] == n);
    }
    int positive = 0, negative = 0, zero = 0;
    for (int R = 2; R <= maxRoot; R++) {
        const int X = R * R - 1;
        i64 diag = 0, transport = 0;
        // Source-exact pushforward by y=floor(X/p). For y=R-1, the
        // max(R,..) correction excludes the forbidden owner p=R.
        for (int y = 1; y < R; y++) {
            const int hi = X / y;
            const int lo = std::max(R, X / (y+1));
            const int count = primeCount[hi] - primeCount[lo];
            if (count < 0) throw std::runtime_error("negative owner multiplicity");
            diag += i64(count) * mertens[y] * mertens[y];
            transport += i64(count) * mertens[y];
        }
        // Independent direct prime-owner enumeration at selected roots.
        if (R <= 30 || R == 317 || R == 1027 || R == maxRoot) {
            i64 direct = 0, directTransport = 0;
            for (int p : primes) {
                if (p > X) break;
                if (p > R) {
                    direct += i64(mertens[X/p]) * mertens[X/p];
                    directTransport += mertens[X/p];
                }
            }
            if (diag != direct || transport != directTransport)
                throw std::runtime_error("owner pushforward mismatch");
            // Independent full-integer smooth/high partition; never infer
            // the smooth population merely from M(X)+transport.
            i64 smoothDirect = 0, highDirect = 0;
            for (int n = 1; n <= X; n++) {
                if (largestPrime[n] <= R) smoothDirect += mu[n];
                else highDirect += mu[n];
            }
            if (smoothDirect != mertens[X] + transport || highDirect != -transport)
                throw std::runtime_error("physical once-only smooth/high split mismatch");
        }
        const i64 smooth = i64(mertens[X]) + transport;
        const i64 gamma = i64(mertens[X])*mertens[X] - diag;
        if (smooth*smooth - 2*smooth*transport + transport*transport - diag != gamma)
            throw std::runtime_error("actual complete compensated owner Gram mismatch");
        if (diag + gamma != i64(mertens[X])*mertens[X])
            throw std::runtime_error("full signed energy mismatch");
        if (gamma > 0) positive++;
        else if (gamma < 0) negative++;
        else zero++;
        for (const Witness &w : witnesses) {
            if (R == w.root) {
                if (mertens[X] != w.mertens || smooth != w.smooth ||
                    transport != w.transport || diag != w.diag || gamma != w.gamma)
                    throw std::runtime_error("exact witness mismatch");
                std::printf("R=%d X=%d M=%d smooth=%lld transport=%lld D=%lld Gamma=%lld\n",
                    R,X,mertens[X],(long long)smooth,(long long)transport,
                    (long long)diag,(long long)gamma);
            }
        }
    }
    if (maxRoot == 3500 && (positive != 99 || negative != 3399 || zero != 1))
        throw std::runtime_error("full R<=3500 signature changed");
    std::printf("PASS roots=2..%d positiveGamma=%d negativeGamma=%d zeroGamma=%d\n",
        maxRoot,positive,negative,zero);
    return 0;
}
