// Exact finite audit of the existing absolute-A target. Not an RH proof.
// Build with g++ -O3 -std=c++17 -Wall -Wextra -Werror.
// Source: scripts/absolute_a_signed_estimate_audit.cpp; output: /tmp/absolute_a_audit.
// Run: /tmp/absolute_a_audit 10000
// Uses a segmented prime-factor sieve; the lower envelope is computed by an
// independent linear sieve. Exact integer comparisons select every maximum.
#include <algorithm>
#include <cassert>
#include <cstdint>
#include <iomanip>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <string>
#include <vector>

using i64 = std::int64_t;
using i128 = __int128_t;

struct Fraction {
  i64 num;
  i64 den;
};

static bool less(Fraction a, Fraction b) {
  return i128(a.num) * b.den < i128(b.num) * a.den;
}

static Fraction reduced(i64 num, i64 den) {
  const i64 g = std::gcd(num, den);
  return {num / g, den / g};
}

static long double value(Fraction a) {
  return static_cast<long double>(a.num) / a.den;
}

static std::string integer(i128 x) {
  if (x == 0) return "0";
  const bool negative = x < 0;
  if (negative) x = -x;
  std::string s;
  while (x > 0) {
    s.push_back(static_cast<char>('0' + x % 10));
    x /= 10;
  }
  if (negative) s.push_back('-');
  std::reverse(s.begin(), s.end());
  return s;
}

struct Endpoint {
  int r = 0;
  i64 m = 0;
  i64 u = 0;
  i64 v = 0;
  Fraction k{1, 1};
  i128 numerator = 0;
  i128 denominator = 1;
};

static void print_endpoint(const char* label, const Endpoint& e) {
  std::cout << label << " R=" << e.r << " M=" << e.m
            << " U=" << e.u << " V=" << e.v
            << " K=" << e.k.num << '/' << e.k.den
            << " ratio=" << static_cast<long double>(e.numerator) /
                                  static_cast<long double>(e.denominator)
            << " exact=" << integer(e.numerator) << '/'
            << integer(e.denominator) << '\n';
}

int main(int argc, char** argv) {
  std::cout << std::fixed << std::setprecision(15);
  const int rmax = argc > 1 ? std::stoi(argv[1]) : 10000;
  if (rmax < 56 || rmax > 10000)
    throw std::invalid_argument("require 56 <= Rmax <= 10000");
  const i64 limit = i64(rmax) * rmax - 1;

  // Independent Euler linear sieve for all lower arguments y < Rmax.
  std::vector<int> low_mu(rmax + 1, 0), least(rmax + 1, 0), primes;
  low_mu[1] = 1;
  for (int n = 2; n <= rmax; ++n) {
    if (least[n] == 0) {
      least[n] = n;
      primes.push_back(n);
      low_mu[n] = -1;
    }
    for (int p : primes) {
      const i64 next = i64(n) * p;
      if (next > rmax) break;
      least[next] = p;
      if (p == least[n]) {
        low_mu[next] = 0;
        break;
      }
      low_mu[next] = -low_mu[n];
    }
  }
  std::vector<Fraction> k(rmax + 1, {1, 1});
  Fraction running_k{1, 1};
  i64 low_m = 0;
  for (int y = 0; y < rmax; ++y) {
    low_m += low_mu[y];
    Fraction energy = reduced((low_m - 1) * (low_m - 1), y + 1);
    if (less(running_k, energy)) running_k = energy;
    k[y + 1] = running_k;
  }

  // For n <= Rmax^2-1, removing primes <= Rmax leaves at most one prime.
  constexpr i64 segment_size = 1 << 20;
  std::vector<i64> residual(segment_size), largest(segment_size);
  std::vector<std::int8_t> mu(segment_size);
  i64 m = 0, u = 0, v = 0, positive = 0, negative = 0, zero = 0;
  Fraction largest_shifted_energy{1, 1};
  i64 energy_at = 0;
  int next_root = 2;
  Endpoint maximum;
  i64 base_failures = 0;
  for (i64 start = 1; start <= limit; start += segment_size) {
    const i64 end = std::min(limit, start + segment_size - 1);
    const i64 size = end - start + 1;
    for (i64 j = 0; j < size; ++j) {
      residual[j] = start + j;
      largest[j] = 1;
      mu[j] = 1;
    }
    for (int p : primes) {
      for (i64 n = ((start + p - 1) / p) * p; n <= end; n += p) {
        const i64 j = n - start;
        int exponent = 0;
        do {
          residual[j] /= p;
          ++exponent;
        } while (residual[j] % p == 0);
        largest[j] = p;
        mu[j] = exponent > 1 ? 0 : -mu[j];
      }
    }
    for (i64 j = 0; j < size; ++j) {
      const i64 n = start + j;
      if (residual[j] > 1) {
        mu[j] = -mu[j];
        largest[j] = residual[j];
      }
      if (n <= rmax) assert(mu[j] == low_mu[n]);
      m += mu[j];
      if (mu[j] > 0) ++positive;
      else if (mu[j] < 0) ++negative;
      else ++zero;
      if (n > 1 && mu[j] != 0) {
        const i64 q = largest[j];
        if (q > n / q) u += mu[j];
        else v += mu[j];
      }
      assert(u + v == m - 1);
      const i64 shifted_square = (m - 1) * (m - 1);
      Fraction energy{shifted_square, n + 1};
      if (less(largest_shifted_energy, energy)) {
        largest_shifted_energy = reduced(energy.num, energy.den);
        energy_at = n;
      }
      // Base for the paper's strong induction, checked on every integer.
      if (i128(shifted_square) * 1000000 > i128(1837) * 1837 * (n + 1))
        ++base_failures;

      if (n == i64(next_root) * next_root - 1) {
        Endpoint e{next_root, m, u, v, k[next_root],
                   i128(shifted_square) * k[next_root].den,
                   i128(next_root) * next_root * k[next_root].num};
        if (next_root >= 56 &&
            e.numerator * maximum.denominator >
                maximum.numerator * e.denominator)
          maximum = e;
        if (next_root == 5561) {
          assert(m == -2544 && u == 125204 && v == -127749);
          assert(k[next_root].num == 3 && k[next_root].den == 2);
          print_endpoint("witness", e);
        }
        ++next_root;
      }
    }
  }
  assert(next_root == rmax + 1);
  assert(positive - negative == m);
  assert(positive + negative + zero == limit);
  assert(base_failures == 0);
  if (rmax == 10000) assert(maximum.r == 5561);
  std::cout << std::fixed << std::setprecision(15);
  print_endpoint("maximum", maximum);
  std::cout << "integer_limit=" << limit << " base_failures=" << base_failures
            << " shifted_energy_max=" << largest_shifted_energy.num << '/'
            << largest_shifted_energy.den << " at=" << energy_at
            << " decimal=" << value(largest_shifted_energy)
            << " positive=" << positive << " negative=" << negative
            << " zero=" << zero << '\n';
}
