#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <iomanip>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
#include <tuple>
#include <utility>
#include <vector>

namespace {

struct SieveData {
  std::vector<int8_t> mu;
  std::vector<int> largest_prime;
  std::vector<int> primes;
};

SieveData linear_sieve(int n) {
  SieveData out;
  out.mu.assign(static_cast<std::size_t>(n) + 1, 0);
  out.largest_prime.assign(static_cast<std::size_t>(n) + 1, 1);
  std::vector<int> least_prime(static_cast<std::size_t>(n) + 1, 0);
  out.mu[1] = 1;
  out.largest_prime[1] = 1;

  for (int i = 2; i <= n; ++i) {
    if (least_prime[i] == 0) {
      least_prime[i] = i;
      out.primes.push_back(i);
      out.mu[i] = -1;
      out.largest_prime[i] = i;
    }
    for (int p : out.primes) {
      const std::int64_t x = static_cast<std::int64_t>(i) * p;
      if (x > n) break;
      least_prime[static_cast<std::size_t>(x)] = p;
      out.largest_prime[static_cast<std::size_t>(x)] =
          std::max(out.largest_prime[i], p);
      if (i % p == 0) {
        out.mu[static_cast<std::size_t>(x)] = 0;
        break;
      }
      out.mu[static_cast<std::size_t>(x)] =
          static_cast<int8_t>(-out.mu[i]);
    }
  }
  return out;
}

struct Metrics {
  int R = 0;
  int K = 0;
  int U = 0;
  int X = 0;
  std::uint64_t children = 0;
  std::uint64_t matched_pairs = 0;
  std::uint64_t frontier = 0;
  std::int64_t signed_mass = 0;
  std::int64_t frontier_signed_mass = 0;
  std::uint64_t frontier_born = 0;
  std::uint64_t frontier_far = 0;
  std::uint64_t frontier_one_fresh_factor = 0;
  std::uint64_t frontier_multiple_fresh_factors = 0;
};

Metrics scan_endpoint(int R, int K) {
  if (R < 3) throw std::invalid_argument("R must be at least 3");
  if (K < 1 || K >= R) throw std::invalid_argument("require 1 <= K < R");

  const int root_gap = static_cast<int>(std::sqrt(static_cast<double>(R)));
  const int U = R - root_gap;
  const std::int64_t x64 = static_cast<std::int64_t>(R) * R - 1;
  if (x64 > std::numeric_limits<int>::max()) {
    throw std::overflow_error("R^2-1 exceeds the scanner's 32-bit index range");
  }
  const int X = static_cast<int>(x64);
  SieveData sieve = linear_sieve(X);

  std::vector<uint8_t> in_response(static_cast<std::size_t>(X) + 1, 0);

  // Build the exact complete signed response-child carrier.  A child n=c*q
  // is admitted when K < P+(c) <= U, q is prime and q>P+(c), and either
  // q>R (post-root partner) or q<=c (born-smooth partner).
  for (int c = 2; c <= X; ++c) {
    if (sieve.mu[c] == 0) continue;
    const int p = sieve.largest_prime[c];
    if (!(K < p && p <= U)) continue;
    const int q_upper = X / c;
    if (q_upper <= p) continue;

    const int born_upper = std::min({q_upper, c, R});
    auto it = std::upper_bound(sieve.primes.begin(), sieve.primes.end(), p);
    for (; it != sieve.primes.end() && *it <= born_upper; ++it) {
      const int q = *it;
      const int n = c * q;
      in_response[n] = 1;
    }

    const int post_lower = std::max(R, p);
    it = std::upper_bound(sieve.primes.begin(), sieve.primes.end(), post_lower);
    for (; it != sieve.primes.end() && *it <= q_upper; ++it) {
      const int q = *it;
      const int n = c * q;
      in_response[n] = 1;
    }
  }

  std::vector<int> children;
  children.reserve(static_cast<std::size_t>(X / 4));
  std::int64_t signed_mass = 0;
  for (int n = 1; n <= X; ++n) {
    if (!in_response[n]) continue;
    children.push_back(n);
    signed_mass += sieve.mu[n];
  }

  // Sequential canonical matching.  At coordinate ell, pair every still
  // unpaired n not divisible by ell with ell*n whenever both arithmetic
  // children lie in the exact response carrier.  Multiplication by the fresh
  // prime reverses the Mobius sign, so every matched pair cancels exactly.
  std::vector<uint8_t> matched(static_cast<std::size_t>(X) + 1, 0);
  std::uint64_t matched_pairs = 0;
  auto ell_begin = std::upper_bound(sieve.primes.begin(), sieve.primes.end(), K);
  auto ell_end = std::upper_bound(sieve.primes.begin(), sieve.primes.end(), U);
  for (auto it = ell_begin; it != ell_end; ++it) {
    const int ell = *it;
    const int n_limit = X / ell;
    for (int n : children) {
      if (n > n_limit) break;
      if (matched[n] || n % ell == 0) continue;
      const int m = n * ell;
      if (!in_response[m] || matched[m]) continue;
      if (sieve.mu[m] != -sieve.mu[n]) {
        throw std::logic_error("fresh-prime pair did not reverse Mobius sign");
      }
      matched[n] = 1;
      matched[m] = 1;
      ++matched_pairs;
    }
  }

  Metrics result;
  result.R = R;
  result.K = K;
  result.U = U;
  result.X = X;
  result.children = children.size();
  result.matched_pairs = matched_pairs;
  result.signed_mass = signed_mass;

  for (int n : children) {
    if (matched[n]) continue;
    ++result.frontier;
    result.frontier_signed_mass += sieve.mu[n];

    const int q = sieve.largest_prime[n];
    const int c = n / q;
    if (q <= R) {
      ++result.frontier_born;
    } else {
      ++result.frontier_far;
    }

    int d = c;
    int fresh_factors = 0;
    while (d > 1) {
      const int p = sieve.largest_prime[d];
      if (p <= K) break;
      ++fresh_factors;
      d /= p;
    }
    if (fresh_factors <= 1) {
      ++result.frontier_one_fresh_factor;
    } else {
      ++result.frontier_multiple_fresh_factors;
    }
  }

  if (result.frontier_signed_mass != result.signed_mass) {
    throw std::logic_error("matched pairs did not preserve the signed mass");
  }
  if (2 * result.matched_pairs + result.frontier != result.children) {
    throw std::logic_error("matching population accounting failed");
  }
  return result;
}

void print_header() {
  std::cout
      << "R,K,U,X,children,matched_pairs,frontier,signed_mass,"
         "frontier_signed_mass,frontier_born,frontier_far,"
         "frontier_one_fresh_factor,frontier_multiple_fresh_factors,"
         "frontier_over_R,frontier_over_R_sqrtK,abs_mass_over_R,"
         "abs_mass_over_R_sqrtK\n";
}

void print_metrics(const Metrics& m) {
  const double r = static_cast<double>(m.R);
  const double scale = r * std::sqrt(static_cast<double>(m.K));
  std::cout << m.R << ',' << m.K << ',' << m.U << ',' << m.X << ','
            << m.children << ',' << m.matched_pairs << ',' << m.frontier << ','
            << m.signed_mass << ',' << m.frontier_signed_mass << ','
            << m.frontier_born << ',' << m.frontier_far << ','
            << m.frontier_one_fresh_factor << ','
            << m.frontier_multiple_fresh_factors << ',' << std::setprecision(12)
            << static_cast<double>(m.frontier) / r << ','
            << static_cast<double>(m.frontier) / scale << ','
            << std::abs(static_cast<double>(m.signed_mass)) / r << ','
            << std::abs(static_cast<double>(m.signed_mass)) / scale << '\n';
}

}  // namespace

int main(int argc, char** argv) {
  try {
    if (argc < 3 || (argc - 1) % 2 != 0) {
      std::cerr << "usage: " << argv[0] << " R K [R K ...]\n";
      return 2;
    }
    print_header();
    for (int i = 1; i < argc; i += 2) {
      const int R = std::stoi(argv[i]);
      const int K = std::stoi(argv[i + 1]);
      print_metrics(scan_endpoint(R, K));
    }
  } catch (const std::exception& e) {
    std::cerr << "error: " << e.what() << '\n';
    return 1;
  }
  return 0;
}
