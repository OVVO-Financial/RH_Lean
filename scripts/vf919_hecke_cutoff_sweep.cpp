// Exact integer reimplementation of PR #919's six-excluded rational coefficients.
// The quotient kernel is an explicit 36-periodic formula, not an OAI bound.
//
// Run:
//   g++ -O3 -std=c++17 scripts/vf919_hecke_cutoff_sweep.cpp -o /tmp/hecke_cutoffs
//   /tmp/hecke_cutoffs 10000000
//
// Optional argument: positive integer X >= 256 (default: ten million).
// Memory: O(X). For large X, choose the available machine accordingly.
// All summatory values and layer totals are signed 64-bit integers.
// Source and interpretations:
//   research/HECKE_SPLIT_PRIME_CUTOFF_TRADEOFF_20261016.md
#include <array>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <vector>

using namespace std;

static int floor_integer_root(int X, int d) {
  int y = 1;
  for (;;) {
    uint64_t v = 1;
    for (int i = 0; i < d; ++i) v *= uint64_t(y + 1);
    if (v > uint64_t(X)) break;
    ++y;
  }
  return y;
}

static int character_prefix(int t) { return (t % 3 == 1 ? 1 : 0); }

static int quotient_kernel_36(int t) {
  return character_prefix(t) - character_prefix(t / 3)
       - character_prefix(t / 4) + character_prefix(t / 12);
}

int main(int argc, char **argv) {
  int X = argc > 1 ? atoi(argv[1]) : 10000000;
  if (X < 256) {
    cerr << "X must be >= 256\n";
    return 2;
  }

  // Independent linear prime sieve and genuine Mobius coefficients.
  vector<int> spf(X + 1, 0), primes;
  vector<int8_t> mu(X + 1, 0);
  vector<int16_t> a6(X + 1, 0);
  mu[1] = 1;
  a6[1] = 1;
  for (int n = 2; n <= X; ++n) {
    if (!spf[n]) {
      spf[n] = n;
      primes.push_back(n);
      mu[n] = -1;
    }
    int p = spf[n], m = n / p;
    if (m != 1) mu[n] = (m % p ? -mu[m] : 0);
    for (int q : primes) {
      if (q > spf[n] || int64_t(q) * n > X) break;
      spf[q * n] = q;
    }

    // Local Euler polynomials: split (1-z)^2; inert 1-z^2.
    // 2 and 3 are excluded. Exponent >= 3 always has a6=0.
    if (p == 2 || p == 3) {
      a6[n] = 0;
    } else if (m % p == 0) {
      a6[n] = ((m / p) % p == 0) ? 0
            : (p % 3 == 1 ? a6[m / p] : -a6[m / p]);
    } else {
      a6[n] = (p % 3 == 1 ? -2 * a6[m] : 0);
    }
  }

  int64_t M = 0;
  for (int n = 1; n <= X; ++n) M += mu[n];
  cout << "X=" << X << " M=" << M << "\n";

  for (int d : {8, 4, 3, 2}) {
    const int y = floor_integer_root(X, d);
    int64_t CORE = 0, BAD = 0;
    array<int64_t, 16> layers{};
    // All signed quotient buckets are retained, including those with K(t)=0.
    vector<int64_t> buckets(X + 2, 0);
    for (int n = 1; n <= X; ++n) {
      if (a6[n] == 0) continue;
      int64_t weight = int64_t(a6[n]) * quotient_kernel_36(X / n);

      int remaining = n, depth = 0;
      bool has_large_square = false;
      while (remaining > 1) {
        int p = spf[remaining], exponent = 0;
        do { remaining /= p; ++exponent; } while (remaining % p == 0);
        if (p > y) {
          if (exponent >= 2) has_large_square = true;
          else ++depth; // Nonzero first-power large primes are split.
        }
      }
      if (has_large_square) {
        BAD += weight;
      } else {
        if (depth >= int(layers.size()) || depth >= d) {
          cerr << "Large-prime depth contradicts the cutoff: X="
               << X << " n=" << n << " y=" << y << " depth=" << depth << "\n";
          return 3;
        }
        layers[depth] += weight;
        CORE += weight;
        buckets[X / n] += a6[n];
      }
    }
    if (CORE + BAD != M) {
      cerr << "FAILED physical Mertens reconstruction at d=" << d << "\n";
      return 4;
    }
    if (d == 2 && BAD != 0) {
      cerr << "FAILED square-root no-large-square theorem\n";
      return 5;
    }

    int64_t variation = 0;
    for (int t = 1; t <= X; ++t)
      variation += llabs(buckets[t] - buckets[t + 1]);

    cout << "CUTOFF d=" << d << " y=" << y << " core=" << CORE
         << " bad=" << BAD << " reconstructed=" << CORE + BAD
         << " variation=" << variation << " layers=";
    for (int k = 0; k < d; ++k) {
      if (k) cout << ",";
      cout << k << ":" << layers[k];
    }
    cout << "\n";
  }
  cout << "PASS: exact genuine mu, prime-to-six Euler factors, "
       << "quotient kernel and all cutoff reconstructions\n";
  return 0;
}
