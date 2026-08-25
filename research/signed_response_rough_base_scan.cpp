#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <iomanip>
#include <iostream>
#include <limits>
#include <map>
#include <stdexcept>
#include <string>
#include <unordered_map>
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

int strip_fresh_primes(int n, int K, int U, const SieveData& sieve) {
  int base = n;
  while (base > 1) {
    const int p = sieve.largest_prime[base];
    if (p <= K) break;
    if (p <= U) {
      base /= p;
    } else {
      // A response child has at most one partner prime above U, and that prime
      // belongs to the rough base rather than the processed Boolean cube.
      const int q = p;
      int rest = base / q;
      while (rest > 1) {
        const int r = sieve.largest_prime[rest];
        if (K < r && r <= U) rest /= r;
        else break;
      }
      base = q * rest;
      break;
    }
  }
  return base;
}

struct Metrics {
  int R = 0;
  int K = 0;
  int U = 0;
  int X = 0;
  std::uint64_t children = 0;
  std::uint64_t rough_bases = 0;
  std::uint64_t nonzero_bases = 0;
  std::uint64_t unit_residual_bases = 0;
  std::uint64_t larger_residual_bases = 0;
  std::uint64_t bases_at_or_below_root = 0;
  std::uint64_t nonzero_bases_at_or_below_root = 0;
  std::uint64_t total_abs_base_residual = 0;
  std::uint64_t max_abs_base_residual = 0;
  std::int64_t signed_mass = 0;
};

Metrics scan_endpoint(int R, int K) {
  if (R < 3) throw std::invalid_argument("R must be at least 3");
  if (K < 1 || K >= R) throw std::invalid_argument("require 1 <= K < R");
  const int U = R - static_cast<int>(std::sqrt(static_cast<double>(R)));
  const std::int64_t x64 = static_cast<std::int64_t>(R) * R - 1;
  if (x64 > std::numeric_limits<int>::max()) {
    throw std::overflow_error("R^2-1 exceeds 32-bit scanner range");
  }
  const int X = static_cast<int>(x64);
  const SieveData sieve = linear_sieve(X);
  std::vector<uint8_t> in_response(static_cast<std::size_t>(X) + 1, 0);

  for (int c = 2; c <= X; ++c) {
    if (sieve.mu[c] == 0) continue;
    const int p = sieve.largest_prime[c];
    if (!(K < p && p <= U)) continue;
    const int q_upper = X / c;
    if (q_upper <= p) continue;

    const int born_upper = std::min({q_upper, c, R});
    auto it = std::upper_bound(sieve.primes.begin(), sieve.primes.end(), p);
    for (; it != sieve.primes.end() && *it <= born_upper; ++it) {
      in_response[c * (*it)] = 1;
    }

    const int post_lower = std::max(R, p);
    it = std::upper_bound(sieve.primes.begin(), sieve.primes.end(), post_lower);
    for (; it != sieve.primes.end() && *it <= q_upper; ++it) {
      in_response[c * (*it)] = 1;
    }
  }

  struct FibreData {
    std::uint64_t card = 0;
    std::int64_t residual = 0;
  };
  std::unordered_map<int, FibreData> fibres;
  fibres.reserve(static_cast<std::size_t>(X / 16));

  Metrics result;
  result.R = R;
  result.K = K;
  result.U = U;
  result.X = X;
  for (int n = 1; n <= X; ++n) {
    if (!in_response[n]) continue;
    ++result.children;
    result.signed_mass += sieve.mu[n];
    const int base = strip_fresh_primes(n, K, U, sieve);
    FibreData& f = fibres[base];
    ++f.card;
    f.residual += sieve.mu[n];
  }

  result.rough_bases = fibres.size();
  std::int64_t residual_check = 0;
  for (const auto& [base, data] : fibres) {
    if (base <= R) ++result.bases_at_or_below_root;
    residual_check += data.residual;
    const std::uint64_t abs_residual =
        static_cast<std::uint64_t>(std::llabs(data.residual));
    if (abs_residual == 0) continue;
    ++result.nonzero_bases;
    if (base <= R) ++result.nonzero_bases_at_or_below_root;
    if (abs_residual == 1) ++result.unit_residual_bases;
    else ++result.larger_residual_bases;
    result.total_abs_base_residual += abs_residual;
    result.max_abs_base_residual =
        std::max(result.max_abs_base_residual, abs_residual);
  }
  if (residual_check != result.signed_mass) {
    throw std::logic_error("rough-base regrouping changed signed mass");
  }
  return result;
}

void print_header() {
  std::cout
      << "R,K,U,X,children,rough_bases,nonzero_bases,unit_residual_bases,"
         "larger_residual_bases,bases_at_or_below_root,"
         "nonzero_bases_at_or_below_root,total_abs_base_residual,"
         "max_abs_base_residual,signed_mass,nonzero_bases_over_R,"
         "nonzero_bases_over_R_sqrtK,total_abs_residual_over_R,"
         "total_abs_residual_over_R_sqrtK,abs_signed_mass_over_R,"
         "abs_signed_mass_over_R_sqrtK\n";
}

void print_metrics(const Metrics& m) {
  const double r = static_cast<double>(m.R);
  const double scale = r * std::sqrt(static_cast<double>(m.K));
  std::cout << m.R << ',' << m.K << ',' << m.U << ',' << m.X << ','
            << m.children << ',' << m.rough_bases << ',' << m.nonzero_bases
            << ',' << m.unit_residual_bases << ','
            << m.larger_residual_bases << ',' << m.bases_at_or_below_root
            << ',' << m.nonzero_bases_at_or_below_root << ','
            << m.total_abs_base_residual << ',' << m.max_abs_base_residual
            << ',' << m.signed_mass << ',' << std::setprecision(12)
            << static_cast<double>(m.nonzero_bases) / r << ','
            << static_cast<double>(m.nonzero_bases) / scale << ','
            << static_cast<double>(m.total_abs_base_residual) / r << ','
            << static_cast<double>(m.total_abs_base_residual) / scale << ','
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
      print_metrics(scan_endpoint(std::stoi(argv[i]), std::stoi(argv[i + 1])));
    }
  } catch (const std::exception& e) {
    std::cerr << "error: " << e.what() << '\n';
    return 1;
  }
  return 0;
}
