// Exact integer Mobius census: square-shell coherent energy and long-lag Gram.
// Build: c++ -O3 -std=c++17 -o /tmp/square_lag scripts/square_shell_long_lag_census.cpp
// Run:   /tmp/square_lag 4096
// Root H must be a power of two, 128 <= H <= max_root (e.g. 8192).
// Does not assert an all-H exponent, RH, independence, or a signed inequality.
#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <iomanip>
#include <iostream>
#include <stdexcept>
#include <vector>

int main(int argc, char** argv) {
  const int Hmax = argc > 1 ? std::atoi(argv[1]) : 4096;
  if (Hmax < 128 || Hmax > 8192 || (Hmax & (Hmax - 1))) {
    std::cerr << "max_root must be a power of 2 in [128,8192]\n";
    return 2;
  }
  const int N = (2 * Hmax + 1) * (2 * Hmax + 1) + Hmax + 4;
  std::vector<std::int8_t> mu(N + 1, 1);
  std::vector<std::uint8_t> composite(N + 1, 0);
  mu[0] = 0;
  for (int p = 2; p <= N; ++p) {
    if (!composite[p]) {
      for (int j = p; j <= N; j += p) {
        composite[j] = 1;
        mu[j] = -mu[j];
      }
      if (std::int64_t(p) * p <= N)
        for (int j = p * p; j <= N; j += p * p) mu[j] = 0;
    }
  }
  composite.clear();
  composite.shrink_to_fit();

  // Independent trial-factorization check catches omitted primes > sqrt(N).
  for (int n = 1; n <= 1000; ++n) {
    int m = n, parity = 0;
    bool squareful = false;
    for (int p = 2; p <= m; ++p) {
      if (m % p) continue;
      int power = 0;
      while (m % p == 0) { ++power; m /= p; }
      if (power > 1) { squareful = true; break; }
      ++parity;
    }
    const int expected = squareful ? 0 : (parity % 2 ? -1 : 1);
    if (mu[n] != expected) {
      std::cerr << "Mobius check failed at " << n << "\n";
      return 3;
    }
  }
  std::vector<std::int32_t> M(N + 1, 0);
  for (int n = 1; n <= N; ++n) M[n] = M[n - 1] + mu[n];
  std::cout
    << "H,L,T,energy,block_sum,near,far,energy_over_H_7_3,"
       "abs_block_sum_over_H_5_3,near_over_H_10_3,far_over_H_10_3,"
       "smoothed_energy_over_H_7_3,smoothed_block_minus_sharp,"
       "large_gcd_unordered_witnesses,positive_far_prefixes,"
       "max_positive_far_prefix,max_positive_far_K\n";

  for (int H = 128; H <= Hmax; H *= 2) {
    std::vector<int> d(H);
    std::vector<int> a(H), b(H);
    std::int64_t E = 0, S = 0, near = 0;
    for (int k = 0; k < H; ++k) {
      const int r = H + k;
      a[k] = r * r;
      b[k] = (r + 1) * (r + 1);
      d[k] = M[b[k]] - M[a[k]];
      E += std::int64_t(d[k]) * d[k];
      S += d[k];
    }
    const int L = int(std::floor(std::cbrt(double(H))));
    for (int lag = 1; lag <= L; ++lag)
      for (int k = 0; k + lag < H; ++k)
        near += std::int64_t(d[k]) * d[k + lag];
    const std::int64_t far = (S * S - E) / 2 - near;
    if (S * S != E + 2 * near + 2 * far)
      throw std::runtime_error("Green-Kubo identity failed");

    // Test uniform prefixes; a negative far covariance is NOT automatic.
    std::vector<std::int64_t> prefix(H + 1, 0);
    for (int j = 0; j < H; ++j) prefix[j + 1] = prefix[j] + d[j];
    std::int64_t prefixDiagonal = 0, prefixNear = 0, maxPositiveFar = 0;
    int maxPositiveK = 0, positivePrefixCount = 0;
    for (int K = 1; K <= H; ++K) {
      const int j = K - 1;
      prefixDiagonal += std::int64_t(d[j]) * d[j];
      prefixNear += std::int64_t(d[j]) *
        (prefix[j] - prefix[std::max(0, j - L)]);
      const std::int64_t farK =
        (prefix[K] * prefix[K] - prefixDiagonal) / 2 - prefixNear;
      if (farK > 0) ++positivePrefixCount;
      if (farK > maxPositiveFar) {
        maxPositiveFar = farK;
        maxPositiveK = K;
      }
    }

    // An upper-bound witness count for ALL pairs with gcd > H, whether or
    // not the pair lies in separate shells. True pair count is no greater.
    std::int64_t largeGcdWitnesses = 0;
    const int lo = H * H, hi = 4 * H * H;
    for (int g = H + 1; g <= hi; ++g) {
      const std::int64_t multiples = hi / g - lo / g;
      largeGcdWitnesses += multiples * (multiples - 1) / 2;
    }
    if (largeGcdWitnesses > 8 * std::int64_t(H) * H * H)
      throw std::runtime_error("large-gcd counting budget failed");

    for (int setting = 0; setting < 2; ++setting) {
      const int T = setting == 0 ?
        int(std::floor(std::pow(double(H), 2.0/3.0))) :
        int(std::floor(0.8 * H));
      double smoothedEnergy = 0.0, smoothedBlock = 0.0;
      for (int k = 0; k < H; ++k) {
        std::int64_t signedSum = 0;
        for (int t = -T; t <= T; ++t)
          signedSum += M[b[k] + t] - M[a[k] + t];
        const double value = double(signedSum) / double(2 * T + 1);
        smoothedEnergy += value * value;
        smoothedBlock += value;
      }
      if (std::abs(smoothedBlock - double(S)) > T + 1e-7)
        throw std::runtime_error("endpoint telescope budget failed");
      std::cout << H << ',' << L << ',' << T << ',' << E << ','
        << S << ',' << near << ',' << far << ','
        << std::fixed << std::setprecision(8)
        << E / std::pow(H, 7.0/3.0) << ','
        << std::abs(double(S)) / std::pow(H, 5.0/3.0) << ','
        << near / std::pow(H, 10.0/3.0) << ','
        << far / std::pow(H, 10.0/3.0) << ','
        << smoothedEnergy / std::pow(H, 7.0/3.0) << ','
        << smoothedBlock - S << ','
        << largeGcdWitnesses << ',' << positivePrefixCount << ','
        << maxPositiveFar << ',' << maxPositiveK << "\n";
    }
  }
}
