#include <algorithm>
#include <array>
#include <cmath>
#include <cstdint>
#include <iomanip>
#include <iostream>
#include <limits>
#include <unordered_map>
#include <vector>

using namespace std;
using int64 = long long;

// Exact finite diagnostic for the truncated upper-middle packet
//
//   X = R^2 - 1,
//   N_R(k) = #{q prime : R < q <= X, floor(X/q) = k},
//   U_R(K) = - sum_{1 <= k <= K} N_R(k) M(k).
//
// The program uses exact integer Mobius/Mertens values and exact Lehmer prime
// counting.  No PNT approximation is used in the reported finite table.

static const int MAXN = 5000000;
static const int PHIN = 100000;
static const int PHIM = 100;

static vector<int> primes;
static vector<int> piCount;
static vector<array<int, PHIM>> phiSmall;
static unordered_map<long long, long long> piMemo;

static long long isqrtll(long long x) {
  long long r = static_cast<long long>(sqrt(static_cast<long double>(x)));
  while ((r + 1) <= x / (r + 1)) ++r;
  while (r > x / r) --r;
  return r;
}

static long long icbrtll(long long x) {
  long long r = static_cast<long long>(cbrt(static_cast<long double>(x)));
  while ((__int128)(r + 1) * (r + 1) * (r + 1) <= x) ++r;
  while ((__int128)r * r * r > x) --r;
  return r;
}

static void initPrimeCounting() {
  vector<bool> isPrime(MAXN + 1, true);
  isPrime[0] = isPrime[1] = false;
  for (int i = 2; 1LL * i * i <= MAXN; ++i) {
    if (!isPrime[i]) continue;
    for (long long j = 1LL * i * i; j <= MAXN; j += i)
      isPrime[static_cast<int>(j)] = false;
  }
  piCount.assign(MAXN + 1, 0);
  for (int i = 2; i <= MAXN; ++i) {
    if (isPrime[i]) primes.push_back(i);
    piCount[i] = piCount[i - 1] + (isPrime[i] ? 1 : 0);
  }

  phiSmall.resize(PHIN);
  for (int x = 0; x < PHIN; ++x) phiSmall[x][0] = x;
  for (int s = 1; s < PHIM; ++s) {
    const int p = primes[s - 1];
    for (int x = 0; x < PHIN; ++x)
      phiSmall[x][s] = phiSmall[x][s - 1] - phiSmall[x / p][s - 1];
  }
}

static long long phi(long long x, int s) {
  if (s == 0) return x;
  if (s < PHIM && x < PHIN) return phiSmall[static_cast<int>(x)][s];
  return phi(x, s - 1) - phi(x / primes[s - 1], s - 1);
}

static long long lehmerPi(long long x) {
  if (x < MAXN) return piCount[static_cast<int>(x)];
  auto it = piMemo.find(x);
  if (it != piMemo.end()) return it->second;

  const long long a = lehmerPi(isqrtll(isqrtll(x)));
  const long long b = lehmerPi(isqrtll(x));
  const long long c = lehmerPi(icbrtll(x));
  long long sum = phi(x, static_cast<int>(a)) +
    ((b + a - 2) * (b - a + 1)) / 2;

  for (long long i = a; i < b; ++i) {
    const long long w = x / primes[static_cast<size_t>(i)];
    sum -= lehmerPi(w);
    if (i < c) {
      const long long lim = lehmerPi(isqrtll(w));
      for (long long j = i; j < lim; ++j)
        sum -= lehmerPi(w / primes[static_cast<size_t>(j)]) - j;
    }
  }
  piMemo[x] = sum;
  return sum;
}

static void buildMobiusMertens(int n, vector<int>& mu, vector<int>& M) {
  mu.assign(n + 1, 0);
  M.assign(n + 1, 0);
  vector<int> lp(n + 1, 0), ps;
  if (n >= 1) mu[1] = 1;
  for (int i = 2; i <= n; ++i) {
    if (lp[i] == 0) {
      lp[i] = i;
      ps.push_back(i);
      mu[i] = -1;
    }
    for (int p : ps) {
      if (p > lp[i] || 1LL * i * p > n) break;
      lp[i * p] = p;
      if (i % p == 0) {
        mu[i * p] = 0;
        break;
      }
      mu[i * p] = -mu[i];
    }
  }
  for (int i = 1; i <= n; ++i) M[i] = M[i - 1] + mu[i];
}

struct Row {
  int R = 0;
  int crossK = 0;
  int bestK = 0;
  long long bestU = 0;
};

static Row scanR(int R, int scanK, const vector<int>& M) {
  const long long X = 1LL * R * R - 1;
  long long U = 0;
  int crossK = 0;
  int bestK = 0;
  long long bestAbs = numeric_limits<long long>::max();
  long long bestU = 0;

  for (int k = 1; k <= min(scanK, R - 1); ++k) {
    const long long lo = max<long long>(R, X / (k + 1));
    const long long hi = X / k;
    const long long Nk = lehmerPi(hi) - lehmerPi(lo);
    U -= Nk * static_cast<long long>(M[k]);

    if (llabs(U) < bestAbs) {
      bestAbs = llabs(U);
      bestK = k;
      bestU = U;
    }
    if (crossK == 0 && U >= 0) crossK = k;
  }
  return {R, crossK, bestK, bestU};
}

int main() {
  initPrimeCounting();

  const vector<int> Rs =
    {200, 500, 1000, 2000, 5000, 10000, 20000, 50000, 100000,
      200000, 500000};
  const int scanK = 300;
  vector<int> mu, M;
  buildMobiusMertens(10000, mu, M);

  cout << fixed << setprecision(6);
  cout << "R  K_cross  K_best  U_best  |U_best|/R  K_best/log(R)\n";
  for (int R : Rs) {
    const Row row = scanR(R, scanK, M);
    cout << row.R << ' ' << row.crossK << ' ' << row.bestK << ' '
         << row.bestU << ' '
         << static_cast<double>(llabs(row.bestU)) / row.R << ' '
         << static_cast<double>(row.bestK) / log(static_cast<double>(row.R))
         << '\n';
  }

  cout << "\nFixed-K main coefficient S_K = sum M(k)/(k(k+1))\n";
  long double S = 0.0L;
  const vector<int> reportK = {50, 100, 200, 500, 1000, 2000, 5000, 10000};
  size_t next = 0;
  for (int k = 1; k <= 10000; ++k) {
    S += static_cast<long double>(M[k]) /
      (static_cast<long double>(k) * (k + 1));
    if (next < reportK.size() && k == reportK[next]) {
      cout << k << ' ' << static_cast<double>(S) << ' '
           << static_cast<double>(k * S) << '\n';
      ++next;
    }
  }
}