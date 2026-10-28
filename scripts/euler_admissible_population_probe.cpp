// Exact admissible-Euler population and weighted Co-Div test.
// No random-sign or independent-prime approximation is used.
#include <algorithm>
#include <cassert>
#include <cmath>
#include <cstdint>
#include <iostream>
#include <vector>

struct Sieve {
  int limit;
  std::vector<uint32_t> least, largest, pi;
  std::vector<int32_t> mertens;
  std::vector<int8_t> mu;
  std::vector<int> primes;
  explicit Sieve(int n) : limit(n), least(n + 1, 0),
      largest(n + 1, 0), pi(n + 1, 0),
      mertens(n + 1, 0), mu(n + 1, 0) {
    mu[1] = 1;
    largest[1] = 1;
    for (int i = 2; i <= n; ++i) {
      if (least[i] == 0) {
        least[i] = static_cast<uint32_t>(i);
        primes.push_back(i);
        mu[i] = -1;
      }
      for (int p : primes) {
        if (p > static_cast<int>(least[i]) || 1LL * i * p > n) break;
        int v = i * p;
        least[v] = static_cast<uint32_t>(p);
        if (p == static_cast<int>(least[i])) {
          mu[v] = 0;
          break;
        }
        mu[v] = static_cast<int8_t>(-mu[i]);
      }
      largest[i] = std::max(least[i], largest[i / least[i]]);
    }
    for (int i = 1; i <= n; ++i) {
      mertens[i] = mertens[i-1] + mu[i];
      pi[i] = pi[i-1] + (i >= 2 && least[i] == static_cast<uint32_t>(i));
    }
  }
};

struct Counts {
  int64_t co = 0, div = 0, diagonal = 0;
};

Counts gram(int root, const Sieve &s) {
  const int n = root - 1;
  const int64_t x = 1LL * root * root - 1;
  Counts v;
  for (int b = 1; b <= n; ++b) {
    int64_t fb = x / (1LL * b * b);
    int64_t fbNext = x / (1LL * (b + 1) * (b + 1));
    v.diagonal += 1LL * s.mertens[b] * s.mertens[b] * (fb - fbNext);
    if (!s.mu[b]) continue;
    for (int a = 1; a < b; ++a) {
      if (!s.mu[a]) continue;
      int64_t w = x / (1LL * a * b) - fb;
      assert(w >= 0);
      if (s.mu[a] == s.mu[b]) v.co += w;
      else v.div += w;
    }
  }
  return v;
}

void selected(int root, const Sieve &s) {
  const int x = root * root - 1;
  int64_t actual_low = 0;
  for (int n = 1; n <= x; ++n)
    if (s.largest[n] < static_cast<uint32_t>(root)) actual_low += s.mu[n];

  int64_t direct_tail = 0, far_tail = 0;
  for (int p : s.primes) {
    if (p > x) break;
    if (p >= root) direct_tail += s.mertens[x / p];
    if (p > root) far_tail += s.mertens[x / p];
  }
  int64_t band_tail = 0;
  for (int k = 1; k < root; ++k) {
    int lower = std::max(root - 1, x / (k + 1));
    int upper = x / k;
    int64_t count = static_cast<int64_t>(s.pi[upper]) - s.pi[lower];
    assert(count >= 0);
    band_tail += s.mertens[k] * count;
  }
  const int64_t mertens = s.mertens[x];
  const int64_t innovation = -direct_tail;
  const int64_t prep = 2LL * s.mertens[root - 1] - actual_low;
  const int64_t q = 2LL * s.mertens[root - 1] - mertens;
  assert(actual_low - direct_tail == mertens);
  assert(direct_tail == band_tail);
  assert(direct_tail - far_tail ==
         ((s.least[root] == static_cast<uint32_t>(root)) ?
             s.mertens[root - 1] : 0));
  assert(prep - innovation == q);
  Counts v = gram(root, s);
  assert(v.diagonal + 2 * (v.co - v.div) == q);
  std::cout << "R=" << root << " X=" << x
            << " low=" << actual_low << " primeInnovation=" << innovation
            << " M(X)=" << mertens << " Q=" << q
            << " diagonal=" << v.diagonal << " co=" << v.co
            << " div=" << v.div << "\n";
}

int main() {
  constexpr int max_root = 10000;
  constexpr int x_max = max_root * max_root - 1;
  Sieve s(x_max);
  int positive = 0, negative = 0, zero = 0;
  int last_negative = 0;
  int64_t largest_abs_q = 0;
  for (int r = 2; r <= max_root; ++r) {
    int x = r * r - 1;
    int64_t tail = 0;
    for (int k = 1; k < r; ++k) {
      int lower = std::max(r-1, x/(k+1));
      int upper = x/k;
      assert(lower <= upper);
      tail += static_cast<int64_t>(s.mertens[k]) *
          (static_cast<int64_t>(s.pi[upper]) - s.pi[lower]);
    }
    const int64_t h = -tail;
    if (h > 0) ++positive;
    else if (h < 0) {++negative; last_negative = r;}
    else ++zero;
    int64_t q = 2LL * s.mertens[r-1] - s.mertens[x];
    largest_abs_q = std::max(largest_abs_q, std::abs(q));
    if (r == 317 || r == 1027 || r == 5561 || r == 10000)
      selected(r, s);
  }
  assert(positive + negative + zero == max_root - 1);
  std::cout << "ALL ROOTS [2,10000]: positive high innovations="
            << positive << " negative=" << negative << " zero=" << zero
            << " lastNegative=" << last_negative
            << " maxAbsQ=" << largest_abs_q << "\n";
  std::cout << "PASS genuine Euler product admissibility, prime-band counts,"
               " root-prime correction and signed Co-Div Gram\n";
  return 0;
}
