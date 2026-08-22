#include <algorithm>
#include <cmath>
#include <cstdint>
#include <iomanip>
#include <iostream>
#include <map>
#include <vector>
using namespace std;

// Exact finite gate for the additive fresh-prime (p,k) state.
//
// X = R^2-1, 2 <= k < R, and
//   J_R(k) = {q : R < q <= X/2, floor(X/q)=k}.
//
// Before prime p is processed:
//   C_<p(k) = frozen Boolean-cube mass F_<p(k),
//   Q_<p(k) = number of q in J_R(k) surviving all primes < p.
//
// Put
//   A_p(k) = F_<p(floor(k/p)),
//   H_p(k) = #{q in J_R(k) : minFac(q)=p}.
// Then the exact fresh-prime update is
//   C_<=p = C_<p - A_p,
//   Q_<=p = Q_<p - H_p,
// and its additive mixed cell is
//   D_p(k) = C_<=p Q_<=p - C_<p Q_<p
//          = -A_p Q_<=p - C_<p H_p.
//
// The program verifies terminally that after all p<=R:
//   C(k)=M(k), Q(k)=N_R(k),
// and
//   |J_R(k)| + sum_p D_p(k) = N_R(k) M(k)
// for every k.

static int bin2(long long x) {
  int b = -1;
  while (x) { x >>= 1; ++b; }
  return max(b, 0);
}

struct Sieve {
  vector<int> spf, primes;
  explicit Sieve(int N) : spf(N + 1, 0) {
    if (N >= 1) spf[1] = 1;
    for (int i = 2; i <= N; ++i) {
      if (spf[i] == 0) { spf[i] = i; primes.push_back(i); }
      for (int p : primes) {
        long long m = 1LL * p * i;
        if (m > N || p > spf[i]) break;
        spf[(int)m] = p;
      }
    }
  }
};

struct Cell {
  long long signedSum = 0;
  long long l1 = 0;
  long long qHit = 0;
  long long cofactor = 0;
  long long active = 0;
};

static void run(int R) {
  const int X = R * R - 1;
  const int U = X / 2;
  Sieve s(U);

  vector<int> lowPrimes;
  for (int p : s.primes) {
    if (p > R) break;
    lowPrimes.push_back(p);
  }
  const int P = (int)lowPrimes.size();
  vector<int> pIndex(R + 1, -1);
  for (int i = 0; i < P; ++i) pIndex[lowPrimes[i]] = i;

  // H[p,k] and terminal prime multiplicity N[k].
  vector<int> H((size_t)P * R, 0), Nk(R, 0), Jk(R, 0);
  auto at = [&](int pi, int k) -> int& { return H[(size_t)pi * R + k]; };

  for (int q = R + 1; q <= U; ++q) {
    const int k = X / q;
    if (k < 2 || k >= R) continue;
    ++Jk[k];
    if (s.spf[q] == q) {
      ++Nk[k];
    } else {
      const int p = s.spf[q];
      if (p <= R && pIndex[p] >= 0) {
        ++at(pIndex[p], k);
      } else {
        cerr << "unexpected composite q=" << q << " minFac=" << p
             << " R=" << R << '\n';
        exit(2);
      }
    }
  }

  // C[k] = F_<p(k), Q[k] = q survivors before p.
  vector<long long> C(R, 1), Q(R, 0), stepTotalK(R, 0);
  for (int k = 2; k < R; ++k) Q[k] = Jk[k];

  map<pair<int,int>, Cell> dy;
  long long exactL1 = 0, exactAbs = 0, qHitAbs = 0, cofactorAbs = 0;
  int exactActive = 0, exactSmall = 0;
  vector<double> ratios;

  for (int pi = 0; pi < P; ++pi) {
    const int p = lowPrimes[pi];
    const vector<long long> Cold = C;  // simultaneous fresh-p update

    for (int k = 2; k < R; ++k) {
      if (Jk[k] == 0) continue;

      const long long cOld = Cold[k];
      const long long A = (k / p == 0 ? 0 : Cold[k / p]);
      const int hit = at(pi, k);
      const long long qAfter = Q[k] - hit;

      const long long cofactor = -A * qAfter;
      const long long qHit = -cOld * (long long)hit;
      const long long step = cofactor + qHit;

      C[k] = cOld - A;
      Q[k] = qAfter;
      stepTotalK[k] += step;

      const long long den = llabs(cofactor) + llabs(qHit);
      if (den) {
        const double ratio = fabs((double)step) / den;
        ratios.push_back(ratio);
        ++exactActive;
        if (ratio <= 0.1) ++exactSmall;
        exactL1 += den;
        exactAbs += llabs(step);
        qHitAbs += llabs(qHit);
        cofactorAbs += llabs(cofactor);

        auto &cell = dy[{bin2(p), bin2(k)}];
        cell.signedSum += step;
        cell.l1 += den;
        cell.qHit += qHit;
        cell.cofactor += cofactor;
        ++cell.active;
      }
    }
  }

  // Independent Mertens prefix for the terminal C(k)=M(k) check.
  vector<int8_t> mu(R + 1);
  vector<int> lp(R + 1), ps, M(R + 1, 0);
  mu[1] = 1;
  for (int n = 2; n <= R; ++n) {
    if (lp[n] == 0) { lp[n] = n; ps.push_back(n); mu[n] = -1; }
    for (int p : ps) {
      long long m = 1LL * n * p;
      if (m > R) break;
      lp[m] = p;
      if (p == lp[n]) { mu[m] = 0; break; }
      mu[m] = -mu[n];
    }
  }
  for (int n = 1; n <= R; ++n) M[n] = M[n - 1] + mu[n];

  long long errQ = 0, errC = 0, telescopeErr = 0;
  long long initial = 0, finalValue = 0, allSteps = 0;
  for (int k = 2; k < R; ++k) {
    errQ += llabs(Q[k] - Nk[k]);
    errC += llabs(C[k] - M[k]);
    const long long init = Jk[k];
    const long long fin = 1LL * Nk[k] * M[k];
    telescopeErr += llabs(init + stepTotalK[k] - fin);
    initial += init;
    finalValue += fin;
    allSteps += stepTotalK[k];
  }

  vector<double> dyRatios;
  long long dyL1 = 0, dyAbs = 0;
  int dySmall = 0;
  struct Row {
    int pb, kb;
    long long signedSum, l1, qHit, cofactor;
    double ratio;
  };
  vector<Row> rows;

  for (auto &kv : dy) {
    if (!kv.second.l1) continue;
    const double ratio = fabs((double)kv.second.signedSum) / kv.second.l1;
    dyRatios.push_back(ratio);
    dyL1 += kv.second.l1;
    dyAbs += llabs(kv.second.signedSum);
    if (ratio <= 0.1) ++dySmall;
    rows.push_back({kv.first.first, kv.first.second, kv.second.signedSum,
      kv.second.l1, kv.second.qHit, kv.second.cofactor, ratio});
  }

  sort(ratios.begin(), ratios.end());
  sort(dyRatios.begin(), dyRatios.end());
  auto quant = [](const vector<double>& v, double a) {
    if (v.empty()) return 0.0;
    return v[(size_t)floor(a * (v.size() - 1))];
  };
  sort(rows.begin(), rows.end(), [](const Row& a, const Row& b) {
    return a.l1 > b.l1;
  });

  cout << "R=" << R << " X=" << X << " U=" << U
       << " primes<=R=" << P << '\n';
  cout << "  checks: Qerr=" << errQ << " Cerr=" << errC
       << " telescopeErr=" << telescopeErr
       << " global=" << initial << "+" << allSteps << "="
       << (initial + allSteps) << " final=" << finalValue << '\n';

  cout << fixed << setprecision(6);
  cout << "  exact fresh (p,k): active=" << exactActive
       << " median=" << quant(ratios, .5)
       << " p90=" << quant(ratios, .9)
       << " <=0.1=" << (exactActive ? (double)exactSmall / exactActive : 0.0)
       << " sum|step|/sum(parts)=" << (exactL1 ? (double)exactAbs / exactL1 : 0.0)
       << " qHitAbs=" << qHitAbs << " cofactorAbs=" << cofactorAbs << '\n';

  cout << "  dyadic (P,K): cells=" << dy.size()
       << " median=" << quant(dyRatios, .5)
       << " p90=" << quant(dyRatios, .9)
       << " <=0.1=" << (dy.size() ? (double)dySmall / dy.size() : 0.0)
       << " sum|cell|/sum(parts)=" << (dyL1 ? (double)dyAbs / dyL1 : 0.0)
       << '\n';

  cout << "  largest dyadic cells:\n";
  for (size_t i = 0; i < min<size_t>(10, rows.size()); ++i) {
    const auto &r = rows[i];
    cout << "    pb=" << r.pb << " kb=" << r.kb
         << " qHit=" << r.qHit << " cof=" << r.cofactor
         << " signed=" << r.signedSum << " L1=" << r.l1
         << " ratio=" << r.ratio << '\n';
  }
}

int main() {
  for (int R : {200, 500, 1000, 2000, 5000, 10000}) run(R);
}
