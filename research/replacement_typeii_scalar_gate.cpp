#include <algorithm>
#include <cmath>
#include <cstdint>
#include <iomanip>
#include <iostream>
#include <vector>
#include <tuple>

using namespace std;

struct Sieve {
  vector<int> mu, M, lp, largestPrimeFactor, primeCount, primes;

  explicit Sieve(int N)
      : mu(N + 1), M(N + 1), lp(N + 1),
        largestPrimeFactor(N + 1), primeCount(N + 1) {
    mu[1] = 1;
    for (int n = 2; n <= N; ++n) {
      if (lp[n] == 0) {
        lp[n] = n;
        primes.push_back(n);
        mu[n] = -1;
      }
      for (int p : primes) {
        long long m = 1LL * n * p;
        if (m > N) break;
        lp[m] = p;
        if (p == lp[n]) {
          mu[m] = 0;
          break;
        }
        mu[m] = -mu[n];
      }
    }

    largestPrimeFactor[1] = 1;
    for (int n = 2; n <= N; ++n)
      largestPrimeFactor[n] = max(lp[n], largestPrimeFactor[n / lp[n]]);

    vector<char> isPrime(N + 1, false);
    for (int p : primes) isPrime[p] = true;
    int pc = 0;
    for (int n = 1; n <= N; ++n) {
      M[n] = M[n - 1] + mu[n];
      if (isPrime[n]) ++pc;
      primeCount[n] = pc;
    }
  }
};

static int ceilDiv(int a, int b) { return (a + b - 1) / b; }

static double pntMain(double x) {
  return x >= 2.0 ? x / log(x) : 0.0;
}

static int exactCut(int R, int numerator, int denominator) {
  int c = 0;
  for (int k = 1;; ++k) {
    __int128 lhs = 1;
    __int128 rhs = 1;
    for (int i = 0; i < denominator; ++i) lhs *= k;
    for (int i = 0; i < numerator; ++i) rhs *= R;
    if (lhs > rhs) break;
    c = k;
  }
  return c;
}

static void runGate(int R) {
  const int X = R * R - 1;
  Sieve s(X);

  // Collapsed root dictionary:
  //   B_root = sum_{1 <= c < R} mu(c)
  //              #{q prime : c < q, R <= cq <= X}.
  vector<long long> rootByC(R, 0);
  long long Broot = 0;
  for (int c = 1; c < R; ++c) {
    if (s.mu[c] == 0) continue;
    const int upper = X / c;
    const int lowerPrimePrefix = max(c, ceilDiv(R, c) - 1);
    const long long count =
        s.primeCount[upper] - s.primeCount[lowerPrimePrefix];
    rootByC[c] = 1LL * s.mu[c] * count;
    Broot += rootByC[c];
  }

  // Collapsed smooth dictionary:
  //   B_smooth = sum_c mu(c)
  //                #{q prime : P+(c) < q < c, R <= cq <= X}.
  // The smooth orientation itself forces q < R, so loop over q first.
  vector<long long> smoothByC(X + 1, 0);
  long long Bsmooth = 0;
  for (int q : s.primes) {
    if (q >= R) break;
    const int cLower = max(q + 1, ceilDiv(R, q));
    const int cUpper = X / q;
    for (int c = cLower; c <= cUpper; ++c) {
      if (s.mu[c] == 0) continue;
      if (s.largestPrimeFactor[c] < q) {
        smoothByC[c] += s.mu[c];
        Bsmooth += s.mu[c];
      }
    }
  }

  // Independent orientation sums, used only as a cross-check and scale
  // diagnostic. They are not used to construct B_root or B_smooth.
  long long U = 0, V = 0;
  for (int n = 2; n <= X; ++n) {
    if (s.mu[n] == 0) continue;
    const int q = s.largestPrimeFactor[n];
    const int c = n / q;
    if (c < q)
      U += s.mu[n];
    else if (q < c)
      V += s.mu[n];
    else {
      cerr << "squarefree orientation equality at n=" << n << '\n';
      exit(2);
    }
  }

  const long long B = Broot + Bsmooth;
  const long long independentTail = s.M[R - 1] - s.M[X];
  const long long endpoint = s.M[X] - 1;

  cout << "R=" << R << " X=" << X
       << " Broot=" << Broot
       << " Bsmooth=" << Bsmooth
       << " B=" << B
       << " tailCheck=" << independentTail
       << " tailError=" << (B - independentTail)
       << " U=" << U
       << " V=" << V
       << " low=" << (s.M[R - 1] - 1)
       << " endpoint=" << endpoint << '\n';

  const vector<tuple<int, int, const char *>> cuts = {
      {1, 4, "1/4"}, {1, 3, "1/3"}, {2, 5, "2/5"}};
  for (auto [num, den, thetaName] : cuts) {
    const int C = exactCut(R, num, den);
    long long rootI = 0, rootII = 0, smoothI = 0, smoothII = 0;
    double mainI = 0.0;

    for (int c = 1; c < R; ++c) {
      if (c <= C) {
        rootI += rootByC[c];
        if (s.mu[c] != 0) {
          const double upper = static_cast<double>(X) / c;
          const double lower = static_cast<double>(max(c, ceilDiv(R, c) - 1));
          mainI += static_cast<double>(s.mu[c]) *
                   (pntMain(upper) - pntMain(lower));
        }
      } else {
        rootII += rootByC[c];
      }
    }
    for (int c = 1; c <= X; ++c) {
      if (c <= C)
        smoothI += smoothByC[c];
      else
        smoothII += smoothByC[c];
    }

    const long long BI = rootI + smoothI;
    const long long BII = rootII + smoothII;
    const double piErrorI = static_cast<double>(BI) - mainI;
    const double mainToError =
        fabs(piErrorI) > 0.0 ? fabs(mainI) / fabs(piErrorI) : 0.0;
    const double typeIIToEndpoint =
        endpoint != 0 ? static_cast<double>(llabs(BII)) / llabs(endpoint) : 0.0;
    const double typeIIToRoot =
        U != 0 ? static_cast<double>(llabs(BII)) / llabs(U) : 0.0;

    cout << fixed << setprecision(6)
         << "  theta=" << thetaName
         << " C=" << C
         << " rootI=" << rootI
         << " smoothI=" << smoothI
         << " rootII=" << rootII
         << " smoothII=" << smoothII
         << " BI=" << BI
         << " BII=" << BII
         << " pntMainI=" << mainI
         << " piErrorI=" << piErrorI
         << " absMainOverAbsError=" << mainToError
         << " absBIIOverAbsEndpoint=" << typeIIToEndpoint
         << " absBIIOverAbsU=" << typeIIToRoot
         << '\n';
  }
}

int main() {
  for (int R : {200, 500, 1000, 2000}) runGate(R);
}
