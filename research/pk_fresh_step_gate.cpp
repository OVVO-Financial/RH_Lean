#include <algorithm>
#include <cmath>
#include <cstdint>
#include <iomanip>
#include <iostream>
#include <string>
#include <utility>
#include <vector>
using namespace std;

// Exact finite gates for predecessor-prime / reciprocal-label cells.
// No asymptotic estimate is used.
//
// X = R^2-1, 2 <= k < R,
//   J_R(k) = {q : R < q <= X/2, floor(X/q)=k}.
//
// Before prime p is processed:
//   C_<p(k) = frozen Boolean-cube mass F_<p(k),
//   Q_<p(k) = number of q in J_R(k) surviving all primes < p.
//
// Put
//   A_p(k) = F_<p(floor(k/p)),
//   H_p(k) = #{q in J_R(k) : minFac(q)=p},
//   N_R(k) = #{q in J_R(k) : q prime}.
//
// Then
//   C_<=p = C_<p - A_p,
//   Q_<=p = Q_<p - H_p.
//
// Two distinct cross-root quantities must not be confused.
//
// (1) Literal cumulative cell, matching the state *through p*:
//     L_p(k) = C_<=p(k) Q_<=p(k),
//     DeltaCum = L_p + N_R A_p.
//     Exact identity:
//       DeltaCum
//         = C_<p Q_<p
//           + [-A_p(Q_<=p-N_R) - C_<p H_p].
//     Thus it retains the entire inherited parent product.
//
// (2) Additive fresh-prime change:
//     D_p(k) = L_p(k) - C_<p(k)Q_<p(k),
//     DeltaStep = D_p + N_R A_p
//               = -A_p(Q_<=p-N_R) - C_<p H_p.
//     The terminal-prime component cancels algebraically.  This derivative
//     residual is the current/future composite chronology.
//
// Statistics are restricted to cells with N_R(k) A_p(k) != 0, where the
// proposed low/post pairing actually has two sides.  The literal gate is
// reported once; moving p-cuts are then applied to the additive residual.

struct Sieve {
  vector<int> spf, primes;
  explicit Sieve(int N) : spf(N + 1, 0) {
    if (N >= 1) spf[1] = 1;
    for (int i = 2; i <= N; ++i) {
      if (spf[i] == 0) {
        spf[i] = i;
        primes.push_back(i);
      }
      for (int p : primes) {
        long long m = 1LL * p * i;
        if (m > N || p > spf[i]) break;
        spf[(int)m] = p;
      }
    }
  }
};

struct Acc {
  long long l1 = 0;
  long long absDelta = 0;
  long long lowAbs = 0;
  long long midAbs = 0;
  long long signedDelta = 0;
  long long n = 0;
  long long small10 = 0;
  long long small1 = 0;
  long double sx = 0, sy = 0, sxx = 0, syy = 0, sxy = 0;
};

static void add(Acc& a, long long low, long long mid, long long delta) {
  const long long den = llabs(low) + llabs(mid);
  if (den == 0) return;
  const double ratio = fabs((double)delta) / den;
  a.l1 += den;
  a.absDelta += llabs(delta);
  a.lowAbs += llabs(low);
  a.midAbs += llabs(mid);
  a.signedDelta += delta;
  ++a.n;
  if (ratio <= 0.1) ++a.small10;
  if (ratio <= 0.01) ++a.small1;
  const long double x = low, y = mid;
  a.sx += x; a.sy += y;
  a.sxx += x * x; a.syy += y * y; a.sxy += x * y;
}

static long double corr(const Acc& a) {
  if (a.n <= 1) return 0;
  const long double num = a.n * a.sxy - a.sx * a.sy;
  const long double dx = a.n * a.sxx - a.sx * a.sx;
  const long double dy = a.n * a.syy - a.sy * a.sy;
  return (dx > 0 && dy > 0) ? num / sqrt(dx * dy) : 0;
}

static int floorPower(int R, double theta) {
  return (int)floor(pow((double)R, theta) + 1e-12);
}

static void printAcc(const string& label, const Acc& a, int R) {
  cout << "  " << label
       << " n=" << setw(9) << a.n
       << " corr=" << setw(10) << (double)corr(a)
       << " <=.1=" << (a.n ? (double)a.small10 / a.n : 0.0)
       << " <=.01=" << (a.n ? (double)a.small1 / a.n : 0.0)
       << " weighted=" << (a.l1 ? (double)a.absDelta / a.l1 : 0.0)
       << " low/mid=" << (a.midAbs ? (double)a.lowAbs / a.midAbs : 0.0)
       << " absDelta/R=" << (double)a.absDelta / R
       << " absDelta/R2=" << (double)a.absDelta / ((double)R * R)
       << '\n';
}

static void run(int R) {
  const int X = R * R - 1;
  const int U = X / 2;
  Sieve s(U);

  vector<int> ps;
  for (int p : s.primes) {
    if (p > R) break;
    ps.push_back(p);
  }
  const int P = (int)ps.size();
  vector<int> pIndex(R + 1, -1);
  for (int i = 0; i < P; ++i) pIndex[ps[i]] = i;

  vector<int> H((size_t)P * R, 0), N(R, 0), J(R, 0);
  auto at = [&](int pi, int k) -> int& { return H[(size_t)pi * R + k]; };

  for (int q = R + 1; q <= U; ++q) {
    const int k = X / q;
    if (k < 2 || k >= R) continue;
    ++J[k];
    if (s.spf[q] == q) {
      ++N[k];
    } else {
      const int p = s.spf[q];
      if (p > R || pIndex[p] < 0) {
        cerr << "unexpected composite q=" << q << " minFac=" << p
             << " R=" << R << '\n';
        exit(2);
      }
      ++at(pIndex[p], k);
    }
  }

  vector<long long> C(R, 1), Q(R, 0);
  for (int k = 2; k < R; ++k) Q[k] = J[k];

  vector<pair<string, int>> cuts = {
      {"2", 2},
      {"R^1/4", floorPower(R, 0.25)},
      {"R^1/3", floorPower(R, 1.0 / 3.0)},
      {"R^2/5", floorPower(R, 0.4)},
      {"R^1/2", floorPower(R, 0.5)},
      {"R^3/5", floorPower(R, 0.6)},
  };
  vector<Acc> step(cuts.size());
  Acc literal;

  long long stepIdentityError = 0;
  long long cumulativeIdentityError = 0;

  for (int pi = 0; pi < P; ++pi) {
    const int p = ps[pi];
    const vector<long long> Cold = C;

    for (int k = 2; k < R; ++k) {
      if (J[k] == 0) continue;

      const long long cOld = Cold[k];
      const long long qOld = Q[k];
      const long long A = (k / p == 0 ? 0 : Cold[k / p]);
      const long long hit = at(pi, k);
      const long long cAfter = cOld - A;
      const long long qAfter = qOld - hit;

      const long long cumulativeLow = cAfter * qAfter;
      const long long D = cumulativeLow - cOld * qOld;
      const long long middle = 1LL * N[k] * A;
      const long long deltaStep = D + middle;
      const long long future = qAfter - N[k];
      const long long residual = -A * future - cOld * hit;
      const long long deltaCum = cumulativeLow + middle;

      stepIdentityError += llabs(deltaStep - residual);
      cumulativeIdentityError += llabs(deltaCum - (cOld * qOld + residual));

      C[k] = cAfter;
      Q[k] = qAfter;

      // No two-sided cross-root cell if the post-root predecessor term is zero.
      if (middle == 0) continue;

      add(literal, cumulativeLow, middle, deltaCum);
      for (size_t z = 0; z < cuts.size(); ++z) {
        if (p >= cuts[z].second) add(step[z], D, middle, deltaStep);
      }
    }
  }

  long long qError = 0;
  for (int k = 2; k < R; ++k) qError += llabs(Q[k] - N[k]);

  cout << "R=" << R << " X=" << X
       << " qError=" << qError
       << " stepIdentityError=" << stepIdentityError
       << " cumulativeIdentityError=" << cumulativeIdentityError << '\n';
  cout << fixed << setprecision(6);

  printAcc("literal cumulative", literal, R);
  for (size_t z = 0; z < step.size(); ++z) {
    printAcc("step cut=" + cuts[z].first + " C=" + to_string(cuts[z].second),
      step[z], R);
  }
}

int main() {
  for (int R : {500, 1000, 2000, 5000, 10000}) run(R);
}
