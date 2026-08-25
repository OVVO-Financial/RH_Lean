#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <iomanip>
#include <iostream>
#include <limits>
#include <numeric>
#include <stdexcept>
#include <string>
#include <vector>

namespace {

struct SieveData {
  std::vector<int8_t> mu;
  std::vector<int> largest_prime;
  std::vector<int> prime_prefix;
  std::vector<int> primes;
};

SieveData linear_sieve(int n) {
  SieveData out;
  out.mu.assign(static_cast<std::size_t>(n) + 1, 0);
  out.largest_prime.assign(static_cast<std::size_t>(n) + 1, 1);
  out.prime_prefix.assign(static_cast<std::size_t>(n) + 1, 0);
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
  std::vector<uint8_t> is_prime(static_cast<std::size_t>(n) + 1, 0);
  for (int p : out.primes) is_prime[p] = 1;
  for (int i = 1; i <= n; ++i) {
    out.prime_prefix[i] = out.prime_prefix[i - 1] + is_prime[i];
  }
  return out;
}

int prime_count_interval(const SieveData& sieve, int lo, int hi) {
  if (hi <= lo) return 0;
  hi = std::min<int>(hi, static_cast<int>(sieve.prime_prefix.size()) - 1);
  lo = std::max(lo, 0);
  return sieve.prime_prefix[hi] - sieve.prime_prefix[lo];
}

int post_root_prefix_count(const SieveData& sieve, int R, int X, int d) {
  if (d <= 0) return 0;
  const int upper = std::max(R, X / d);
  return prime_count_interval(sieve, R, upper);
}

int born_partner_count(const SieveData& sieve, int R, int X, int c) {
  if (c <= 0) return 0;
  const int p = sieve.largest_prime[c];
  const int upper = std::min({R, c, X / c});
  return prime_count_interval(sieve, p, upper);
}

struct Metrics {
  int R = 0;
  int K = 0;
  int j = 0;
  int layer_card = 0;
  int U = 0;
  int X = 0;
  std::uint64_t creation_seats = 0;
  std::uint64_t response_seats = 0;
  std::uint64_t total_seats_with_head = 0;
  std::uint64_t matched_pairs = 0;
  std::uint64_t frontier_seats_with_head = 0;
  std::uint64_t frontier_creation_seats = 0;
  std::uint64_t frontier_response_seats = 0;
  std::uint64_t frontier_born_channel = 0;
  std::uint64_t frontier_high_channel = 0;
  std::int64_t terminal_mass = 0;
  std::int64_t frontier_mass = 0;
};

Metrics scan_endpoint(int R, int K, int j_request) {
  if (R < 3) throw std::invalid_argument("R must be at least 3");
  if (K < 1 || K >= R) throw std::invalid_argument("require 1 <= K < R");
  const int U = R - static_cast<int>(std::sqrt(static_cast<double>(R)));
  const std::int64_t x64 = static_cast<std::int64_t>(R) * R - 1;
  if (x64 > std::numeric_limits<int>::max()) {
    throw std::overflow_error("R^2-1 exceeds 32-bit scanner range");
  }
  const int X = static_cast<int>(x64);
  const SieveData sieve = linear_sieve(X);

  const int prefix_k = post_root_prefix_count(sieve, R, X, K);
  const int prefix_k1 = post_root_prefix_count(sieve, R, X, K + 1);
  const int layer_card = prefix_k - prefix_k1;
  int j = j_request;
  if (j_request == -1) j = layer_card / 2;
  if (j_request == -2) j = layer_card;
  if (j < 0 || j > layer_card) {
    throw std::invalid_argument("j must lie in [0, reciprocal layer card]");
  }

  std::vector<int> born_count(static_cast<std::size_t>(X) + 1, 0);
  std::vector<int> high_count(static_cast<std::size_t>(X) + 1, 0);
  std::vector<int> combined_count(static_cast<std::size_t>(X) + 1, 0);

  for (int c = 1; c <= X; ++c) {
    if (sieve.mu[c] == 0 || sieve.largest_prime[c] > U) continue;
    born_count[c] = born_partner_count(sieve, R, X, c);
    if (c <= R - 1) {
      if (c <= K) {
        high_count[c] = (layer_card - j) + prefix_k1;
      } else {
        high_count[c] = post_root_prefix_count(sieve, R, X, c);
      }
    }
    combined_count[c] = born_count[c] + high_count[c];
  }

  // Flatten literal cofactor-seat states. Born seats come first, then high
  // seats, matching the channel-faithful Lean carrier.
  std::vector<std::uint64_t> offset(static_cast<std::size_t>(X) + 2, 0);
  for (int c = 1; c <= X; ++c) {
    offset[c + 1] = offset[c] + static_cast<std::uint64_t>(combined_count[c]);
  }
  const std::uint64_t total_seats = offset[X + 1];
  if (total_seats > 600000000ULL) {
    throw std::overflow_error("seat carrier too large for this diagnostic");
  }
  std::vector<uint8_t> matched(static_cast<std::size_t>(total_seats), 0);

  Metrics out;
  out.R = R;
  out.K = K;
  out.j = j;
  out.layer_card = layer_card;
  out.U = U;
  out.X = X;
  out.total_seats_with_head = total_seats + 1;

  std::int64_t total_mass = 1;
  for (int c = 1; c <= X; ++c) {
    if (combined_count[c] == 0) continue;
    const std::uint64_t seats = static_cast<std::uint64_t>(combined_count[c]);
    total_mass += static_cast<std::int64_t>(-sieve.mu[c]) *
                  static_cast<std::int64_t>(seats);
    if (sieve.largest_prime[c] <= K) out.creation_seats += seats;
    else out.response_seats += seats;
  }
  out.terminal_mass = total_mass;

  // Process the actual fresh-prime coordinates. A seat survives from c to
  // ell*c precisely when the same seat index is present in both response
  // fibres. The two Möbius weights are opposite.
  auto first_fresh = std::upper_bound(sieve.primes.begin(), sieve.primes.end(), K);
  auto last_fresh = std::upper_bound(sieve.primes.begin(), sieve.primes.end(), U);
  for (auto pit = first_fresh; pit != last_fresh; ++pit) {
    const int ell = *pit;
    const int c_limit = X / ell;
    for (int c = 1; c <= c_limit; ++c) {
      if (combined_count[c] == 0 || c % ell == 0) continue;
      const int child = c * ell;
      if (combined_count[child] == 0) continue;
      if (sieve.mu[child] != -sieve.mu[c]) {
        throw std::logic_error("fresh-prime cofactor seat did not flip sign");
      }
      const int overlap = std::min(combined_count[c], combined_count[child]);
      for (int s = 0; s < overlap; ++s) {
        const std::uint64_t lower_id = offset[c] + static_cast<std::uint64_t>(s);
        const std::uint64_t upper_id = offset[child] + static_cast<std::uint64_t>(s);
        if (matched[lower_id] || matched[upper_id]) continue;
        matched[lower_id] = 1;
        matched[upper_id] = 1;
        ++out.matched_pairs;
      }
    }
  }

  std::int64_t frontier_mass = 1;  // distinguished head always remains
  out.frontier_seats_with_head = 1;
  for (int c = 1; c <= X; ++c) {
    const int count = combined_count[c];
    if (count == 0) continue;
    for (int s = 0; s < count; ++s) {
      const std::uint64_t id = offset[c] + static_cast<std::uint64_t>(s);
      if (matched[id]) continue;
      ++out.frontier_seats_with_head;
      frontier_mass += -sieve.mu[c];
      if (sieve.largest_prime[c] <= K) ++out.frontier_creation_seats;
      else ++out.frontier_response_seats;
      if (s < born_count[c]) ++out.frontier_born_channel;
      else ++out.frontier_high_channel;
    }
  }
  out.frontier_mass = frontier_mass;

  if (frontier_mass != total_mass) {
    throw std::logic_error("C-to-R matching changed the terminal signed mass");
  }
  if (2 * out.matched_pairs + out.frontier_seats_with_head !=
      out.total_seats_with_head) {
    throw std::logic_error("C-to-R seat population accounting failed");
  }
  return out;
}

void print_header() {
  std::cout
      << "R,K,j,layer_card,U,X,creation_seats,response_seats,"
         "total_seats_with_head,matched_pairs,frontier_seats_with_head,"
         "frontier_creation_seats,frontier_response_seats,"
         "frontier_born_channel,frontier_high_channel,terminal_mass,"
         "frontier_mass,frontier_over_R,frontier_over_R_sqrtK,"
         "abs_terminal_over_R,abs_terminal_over_R_sqrtK\n";
}

void print_metrics(const Metrics& m) {
  const double r = static_cast<double>(m.R);
  const double scale = r * std::sqrt(static_cast<double>(m.K));
  std::cout << m.R << ',' << m.K << ',' << m.j << ',' << m.layer_card << ','
            << m.U << ',' << m.X << ',' << m.creation_seats << ','
            << m.response_seats << ',' << m.total_seats_with_head << ','
            << m.matched_pairs << ',' << m.frontier_seats_with_head << ','
            << m.frontier_creation_seats << ',' << m.frontier_response_seats
            << ',' << m.frontier_born_channel << ',' << m.frontier_high_channel
            << ',' << m.terminal_mass << ',' << m.frontier_mass << ','
            << std::setprecision(12)
            << static_cast<double>(m.frontier_seats_with_head) / r << ','
            << static_cast<double>(m.frontier_seats_with_head) / scale << ','
            << std::abs(static_cast<double>(m.terminal_mass)) / r << ','
            << std::abs(static_cast<double>(m.terminal_mass)) / scale << '\n';
}

}  // namespace

int main(int argc, char** argv) {
  try {
    if (argc < 4 || (argc - 1) % 3 != 0) {
      std::cerr << "usage: " << argv[0] << " R K j [R K j ...]\n"
                << "j=-1 selects half the layer; j=-2 selects the full layer\n";
      return 2;
    }
    print_header();
    for (int i = 1; i < argc; i += 3) {
      print_metrics(scan_endpoint(
          std::stoi(argv[i]), std::stoi(argv[i + 1]), std::stoi(argv[i + 2])));
    }
  } catch (const std::exception& e) {
    std::cerr << "error: " << e.what() << '\n';
    return 1;
  }
  return 0;
}
