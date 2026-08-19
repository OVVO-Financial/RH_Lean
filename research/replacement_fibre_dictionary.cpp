#include <algorithm>
#include <cmath>
#include <cstdint>
#include <iomanip>
#include <iostream>
#include <vector>

using namespace std;

struct Sieve {
  vector<int> mu, M, primes, lp;
  explicit Sieve(int N) : mu(N + 1), M(N + 1), lp(N + 1) {
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
    for (int n = 1; n <= N; ++n) M[n] = M[n - 1] + mu[n];
  }
};

static long long quotientKernel(int z, int y) {
  if (y <= 0 || y > z) return 0;
  return z / y - z / (y + 1);
}

static void run(int R) {
  const int X = R * R - 1;
  Sieve s(X);

  vector<int> C(X + 1, 0);
  for (int d = 1; d < R; ++d) {
    if (s.mu[d] == 0) continue;
    int start = ((R + d - 1) / d) * d;
    for (int n = start; n <= X; n += d) C[n] += s.mu[d];
  }

  vector<long long> b(R), t(R), a(R), p(R), q(R), joint(R);
  long long S = 0;
  for (int n = R; n <= X; ++n) {
    int y = X / n;
    b[y] += C[n];
    t[y] += s.mu[n];
    S += C[n];
  }
  for (int y = 1; y < R; ++y) a[y] = -b[y];
  a[R - 1] += 1;

  long long P = 0, Q = 0, J = 0, absJ = 0;
  for (int y = 1; y < R; ++y) {
    p[y] = a[y] * 1LL * (s.M[y] - 1);
    q[y] = 1LL * y * t[y];
    joint[y] = p[y] + q[y];
    P += p[y];
    Q += q[y];
    J += joint[y];
    absJ += llabs(joint[y]);
  }

  long long maxKernelError = 0;
  for (int y = 1; y < R; ++y) {
    long long rhs = 0;
    for (int z = y; z < R; ++z)
      rhs -= quotientKernel(z, y) * t[z];
    maxKernelError = max(maxKernelError, llabs(b[y] - rhs));
  }

  long long maxRenewalError = 0;
  for (int z = 1; z < R; ++z) {
    long long lhs = z;
    for (int y = 1; y <= z; ++y)
      lhs += quotientKernel(z, y) * 1LL * (s.M[y] - 1);
    maxRenewalError = max(maxRenewalError, llabs(lhs - 1));
  }

  vector<long long> mags;
  mags.reserve(R - 1);
  for (int y = 1; y < R; ++y) mags.push_back(llabs(joint[y]));
  sort(mags.rbegin(), mags.rend());
  long long top50 = 0;
  for (int i = 0; i < min(50, (int)mags.size()); ++i) top50 += mags[i];

  long long corrNum = 0, bSq = 0, qtSq = 0;
  for (int y = 1; y < R; ++y) {
    corrNum += b[y] * q[y];
    bSq += b[y] * b[y];
    qtSq += q[y] * q[y];
  }
  double corr = (bSq && qtSq)
      ? (double)corrNum / sqrt((double)bSq * (double)qtSq) : 0.0;

  long long abelMain = 1LL * s.M[R - 1] * (R + 1) - 1;
  long long abelResidual = 0;
  for (int n = 1; n <= R - 2; ++n)
    abelResidual += 1LL * s.M[n] * (X / n - X / (n + 1));

  cout << "R=" << R << " X=" << X << " M(X)=" << s.M[X]
       << " S=" << S << " P=" << P << " Q=" << Q << " J=" << J << "\n";
  cout << "  kernelError=" << maxKernelError
       << " renewalError=" << maxRenewalError
       << " endpointError=" << (J - (s.M[X] - 1)) << "\n";
  cout << fixed << setprecision(4)
       << "  top50JointAbs=" << (absJ ? 100.0 * top50 / absJ : 0.0) << "%"
       << " corr(b,y*t)=" << corr << "\n";
  cout << "  AbelMain=" << abelMain
       << " AbelResidual=" << abelResidual
       << " AbelTotal=" << abelMain + abelResidual << "\n";
}

int main() {
  for (int R : {100, 200, 500, 1000}) run(R);
}
