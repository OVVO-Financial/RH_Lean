#include <algorithm>
#include <cmath>
#include <cstdint>
#include <iomanip>
#include <iostream>
#include <string>
#include <utility>
#include <vector>
using namespace std;

// Exact finite gate for the cross-root predecessor-prime / reciprocal-label
// state.  Nothing in this program uses an asymptotic estimate.
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
// The additive fresh-prime step is
//   D_p(k) = (C_<p-A_p)(Q_<p-H_p) - C_<p Q_<p
//          = -A_p Q_<=p - C_<p H_p.
//
// The cross-root cell proposed after #453 is
//   Delta_p(k) = D_p(k) + N_R(k) A_p(k).
// It has the exact residual form
//   Delta_p(k)
//     = -A_p(k) (Q_<=p(k)-N_R(k)) - C_<p(k) H_p(k),
// so the terminal-prime component cancels algebraically before any statistic
// is taken.  The remaining first term is exactly the future composite-hit
// population.
//
// The table is restricted to cells with N_R(k) A_p(k) != 0; these are the
// cells where the cross-root pairing actually has both sides.  Moving p-cuts
// test where the anti-alignment lives.  absDelta/R^2 is printed because a small
// cancellation ratio is not itself an RH-scale estimate.

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

static int floorPower(int R, double theta) {
  return (int)floor(pow((double)R, theta) + 1e-12);
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

  // H[p,k], terminal primes N[k], and the unprocessed integer fibre J[k].
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

  // C[k]=F_<p(k), Q[k]=q survivors before p.
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
  vector<Acc> acc(cuts.size());

  long long identityError = 0;
  for (int pi = 0; pi < P; ++pi) {
    const int p = ps[pi];
    const vector<long long> Cold = C;  // simultaneous fresh-p update

    for (int k = 2; k < R; ++k) {
      if (J[k] == 0) continue;

      const long long cOld = Cold[k];
      const long long A = (k / p == 0 ? 0 : Cold[k / p]);
      const long long hit = at(pi, k);
      const long long qAfter = Q[k] - hit;

      const long long D = -A * qAfter - cOld * hit;
      const long long middle = 1LL * N[k] * A;
      const long long delta = D + middle;
      const long long future = qAfter - N[k];
      const long long residual = -A * future - cOld * hit;
      identityError += llabs(delta - residual);

      C[k] = cOld - A;
      Q[k] = qAfter;

      // The cross-root cell has two sides only when N*A is nonzero.
      if (middle == 0) continue;
      const long long den = llabs(D) + llabs(middle);
      if (den == 0) continue;
      const double ratio = fabs((double)delta) / den;

      for (size_t z = 0; z < cuts.size(); ++z) {
        if (p < cuts[z].second) continue;
        auto& a = acc[z];
        a.l1 += den;
        a.absDelta += llabs(delta);
        a.lowAbs += llabs(D);
        a.midAbs += llabs(middle);
        a.signedDelta += delta;
        ++a.n;
        if (ratio <= 0.1) ++a.small10;
        if (ratio <= 0.01) ++a.small1;
        const long double x = D, y = middle;
        a.sx += x; a.sy += y;
        a.sxx += x * x; a.syy += y * y; a.sxy += x * y;
      }
    }
  }

  long long qError = 0;
  for (int k = 2; k < R; ++k) qError += llabs(Q[k] - N[k]);

  cout << "R=" << R << " X=" << X
       << " qError=" << qError
       << " identityError=" << identityError << '\n';
  cout << fixed << setprecision(6);

  for (size_t z = 0; z < acc.size(); ++z) {
    const auto& a = acc[z];
    long double corr = 0;
    if (a.n > 1) {
      const long double num = a.n * a.sxy - a.sx * a.sy;
      const long double dx = a.n * a.sxx - a.sx * a.sx;
      const long double dy = a.n * a.syy - a.sy * a.sy;
      if (dx > 0 && dy > 0) corr = num / sqrt(dx * dy);
    }
    cout << "  cut=" << setw(6) << cuts[z].first
         << " C=" << setw(5) << cuts[z].second
         << " n=" << setw(9) << a.n
         << " corr=" << setw(10) << (double)corr
         << " <=.1=" << (a.n ? (double)a.small10 / a.n : 0.0)
         << " <=.01=" << (a.n ? (double)a.small1 / a.n : 0.0)
         << " weighted=" << (a.l1 ? (double)a.absDelta / a.l1 : 0.0)
         << " low/mid=" << (a.midAbs ? (double)a.lowAbs / a.midAbs : 0.0)
         << " absDelta/R=" << (double)a.absDelta / R
         << " absDelta/R2=" << (double)a.absDelta / ((double)R * R)
         << " signedDelta/R=" << (double)a.signedDelta / R
         << '\n';
  }
}

int main() {
  for (int R : {500, 1000, 2000, 5000, 10000}) run(R);
}
