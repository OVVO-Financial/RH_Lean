#include <algorithm>
#include <array>
#include <cassert>
#include <cmath>
#include <cstdint>
#include <iomanip>
#include <iostream>
#include <limits>
#include <numeric>
#include <string>
#include <vector>

namespace {

std::vector<int> mobiusSieve(int n) {
  std::vector<int> mu(n + 1, 0), leastPrime(n + 1, 0), primes;
  if (n >= 1) mu[1] = 1;
  for (int i = 2; i <= n; ++i) {
    if (leastPrime[i] == 0) {
      leastPrime[i] = i;
      primes.push_back(i);
      mu[i] = -1;
    }
    for (int p : primes) {
      const long long v = 1LL * i * p;
      if (v > n) break;
      leastPrime[v] = p;
      if (p == leastPrime[i]) {
        mu[v] = 0;
        break;
      }
      mu[v] = -mu[i];
    }
  }
  return mu;
}

std::vector<int> primeSieve(int n) {
  std::vector<bool> isPrime(n + 1, true);
  if (n >= 0) isPrime[0] = false;
  if (n >= 1) isPrime[1] = false;
  for (long long p = 2; p * p <= n; ++p) {
    if (!isPrime[p]) continue;
    for (long long m = p * p; m <= n; m += p) isPrime[m] = false;
  }
  std::vector<int> primes;
  for (int i = 2; i <= n; ++i) {
    if (isPrime[i]) primes.push_back(i);
  }
  return primes;
}

long double toLongDouble(__int128 x) {
  const bool neg = x < 0;
  if (neg) x = -x;
  const __int128 base = static_cast<__int128>(1) << 64;
  const auto lo = static_cast<unsigned long long>(x & (base - 1));
  const auto hi = static_cast<unsigned long long>(x >> 64);
  long double out = static_cast<long double>(hi) * 18446744073709551616.0L +
                    static_cast<long double>(lo);
  return neg ? -out : out;
}

struct Diagnostic {
  int R = 0;
  long long primeCount = 0;
  int nonemptyWindows = 0;
  __int128 diagonal36 = 0;
  __int128 offDiagonal36 = 0;
  __int128 withinWindowOffDiagonal36 = 0;
  __int128 crossWindowOffDiagonal36 = 0;
  __int128 total36 = 0;
};

Diagnostic computeDiagnostic(int R, const std::vector<int>& primes,
                             const std::vector<int>& mu) {
  const long long X = 1LL * R * R - 1;
  const long long carrierLength = (X - 3) / 4;

  // v_q is stored after multiplying every coefficient by 6. The first six
  // coordinates are 6 * centered B and the last six are 6 * C. The A
  // coordinate is identically zero for this exact transition ledger: a
  // nonzero local fibre mass forces one of the two adjacent states active.
  std::vector<std::array<__int128, 12>> windowSum(R);
  std::vector<__int128> windowDiagonal36(R, 0);
  std::array<__int128, 12> globalSum{};
  __int128 diagonal36 = 0;
  long long primeCount = 0;

  auto it = std::upper_bound(primes.begin(), primes.end(), R);
  for (; it != primes.end() && *it <= X; ++it) {
    const long long q = *it;
    const int d = static_cast<int>(X / q);
    assert(1 <= d && d < R);

    long long B[6] = {0, 0, 0, 0, 0, 0};
    long long C[6] = {0, 0, 0, 0, 0, 0};

    // q lies in Q_d, so the exact cofactor range is 1 <= c <= d.
    for (int c = 1; c <= d; ++c) {
      const int muc = mu[c];
      if (muc == 0) continue;

      const long long n = q * c;
      const int residue = static_cast<int>(n & 3LL);
      assert(residue != 0);
      const int slot = residue - 1;

      // Since c < R < q and q is prime, mu(c q) = -mu(c). Lean's Bool label
      // is true exactly when the visible source sign mu(c q) is +1.
      const bool visiblePositive = (muc == -1);
      const int label = 2 * slot + (visiblePositive ? 1 : 0);

      const long long cell = n / 4;
      assert(0 <= cell && cell <= carrierLength);

      // These are exactly the boundary-aware adjacent transitions used by
      // physicalDistinguishedPrimeB and physicalDistinguishedPrimeC.
      if (cell >= 1) B[label] += muc;
      if (cell < carrierLength) C[label] += muc;
    }

    const long long Btotal = std::accumulate(B, B + 6, 0LL);
    long long v[12];
    for (int i = 0; i < 6; ++i) {
      v[i] = 6 * B[i] - Btotal;
      v[6 + i] = 6 * C[i];
    }

    __int128 energy36 = 0;
    for (int i = 0; i < 12; ++i) {
      energy36 += static_cast<__int128>(v[i]) * v[i];
      windowSum[d][i] += v[i];
      globalSum[i] += v[i];
    }
    diagonal36 += energy36;
    windowDiagonal36[d] += energy36;
    ++primeCount;
  }

  __int128 sumWindowNorm36 = 0;
  int nonemptyWindows = 0;
  for (int d = 1; d < R; ++d) {
    __int128 norm36 = 0;
    for (int i = 0; i < 12; ++i) norm36 += windowSum[d][i] * windowSum[d][i];
    if (norm36 != 0 || windowDiagonal36[d] != 0) ++nonemptyWindows;
    sumWindowNorm36 += norm36;
  }

  __int128 total36 = 0;
  for (int i = 0; i < 12; ++i) total36 += globalSum[i] * globalSum[i];

  // No pairwise q,q' loop appears anywhere. These are exact polarization
  // identities applied only after the complete signed sums are formed.
  assert((total36 - diagonal36) % 2 == 0);
  assert((sumWindowNorm36 - diagonal36) % 2 == 0);
  assert((total36 - sumWindowNorm36) % 2 == 0);
  const __int128 offDiagonal36 = (total36 - diagonal36) / 2;
  const __int128 within36 = (sumWindowNorm36 - diagonal36) / 2;
  const __int128 cross36 = (total36 - sumWindowNorm36) / 2;
  assert(offDiagonal36 == within36 + cross36);

  return Diagnostic{R, primeCount, nonemptyWindows, diagonal36, offDiagonal36,
                    within36, cross36, total36};
}

}  // namespace

int main(int argc, char** argv) {
  std::vector<int> scales;
  for (int i = 1; i < argc; ++i) scales.push_back(std::stoi(argv[i]));
  if (scales.empty()) scales = {500, 1000, 2000, 4000, 5561};

  const int maxR = *std::max_element(scales.begin(), scales.end());
  const long long maxX64 = 1LL * maxR * maxR - 1;
  if (maxX64 > std::numeric_limits<int>::max()) {
    std::cerr << "max R is too large for this in-memory sieve\n";
    return 2;
  }

  const auto primes = primeSieve(static_cast<int>(maxX64));
  const auto mu = mobiusSieve(maxR);

  std::cout << "R,prime_count,D,O,O_over_D,within_window_O_over_D,"
               "cross_window_O_over_D,total_over_D,nonempty_windows\n";
  std::cout << std::fixed << std::setprecision(12);

  for (int R : scales) {
    const Diagnostic d = computeDiagnostic(R, primes, mu);
    const long double D36 = toLongDouble(d.diagonal36);
    const long double O36 = toLongDouble(d.offDiagonal36);
    const long double within36 = toLongDouble(d.withinWindowOffDiagonal36);
    const long double cross36 = toLongDouble(d.crossWindowOffDiagonal36);
    const long double total36 = toLongDouble(d.total36);

    std::cout << d.R << ',' << d.primeCount << ','
              << static_cast<double>(D36 / 36.0L) << ','
              << static_cast<double>(O36 / 36.0L) << ','
              << static_cast<double>(O36 / D36) << ','
              << static_cast<double>(within36 / D36) << ','
              << static_cast<double>(cross36 / D36) << ','
              << static_cast<double>(total36 / D36) << ','
              << d.nonemptyWindows << '\n';
  }
}
