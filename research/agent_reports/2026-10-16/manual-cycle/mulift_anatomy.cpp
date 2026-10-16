// mulift_anatomy.cpp -- signed anatomy of the genuine floor kernel (MU-LIFT).
// For N <= X < (N+1)^2:  M(X) = 2M(N) - Q_N(X),  Q_N(X) = sum_{i,j<=N} mu(i)mu(j) floor(X/(ij)).
// With floor(t) = t - 1/2 - psi(t):
//   M(X) = 2M(N) + M(N)^2/2 - X m_N^2 + Psi_N(X)           (four-term form)
//        = 2M(N) + K1 - K2 + K3                              (hyperbola-truncated form)
// m_N = sum_{n<=N} mu(n)/n, Psi_N = sum_{i,j<=N} mu mu psi(X/ij),
// K1 = (1/2) sum_{ij<=X} mu mu, K2 = X sum_{ij<=X} mu mu/(ij), K3 = sum_{ij<=X} mu mu psi(X/ij).
// Q_N(X) is computed exactly in int64; the decomposition terms in long double.
// Build: g++ -O2 -std=c++20 mulift_anatomy.cpp -o mulift_anatomy
#include <bits/stdc++.h>
using namespace std;
typedef long double ld;
int main() {
    vector<long long> Ns = {1000, 3162, 10000};
    long long LIM = (Ns.back() + 1) * (Ns.back() + 1);
    vector<int8_t> mu(LIM + 1, 1);
    {   // linear sieve for mu
        vector<int> primes; vector<char> comp(LIM + 1, 0); mu[0] = 0; mu[1] = 1;
        for (long long i = 2; i <= LIM; ++i) {
            if (!comp[i]) { primes.push_back((int)i); mu[i] = -1; }
            for (int p : primes) {
                long long ip = i * p; if (ip > LIM) break;
                comp[ip] = 1;
                if (i % p == 0) { mu[ip] = 0; break; } else mu[ip] = -mu[i];
            }
        }
    }
    // queries
    struct Q { long long N, X; };
    vector<Q> qs;
    for (auto N : Ns) {
        vector<long long> Xs = {N, llround(powl((ld)N, 1.25L)), llround(powl((ld)N, 1.5L)), llround(powl((ld)N, 1.75L)), (N + 1) * (N + 1) - 1};
        for (auto X : Xs) qs.push_back({N, X});
    }
    // M at all query X and at N; E(N+1)
    set<long long> need; for (auto& q : qs) { need.insert(q.X); need.insert(q.N); }
    map<long long, long long> Mv; map<long long, ld> Emax;
    long long M = 0; ld E = 0;
    for (long long n = 1; n <= LIM; ++n) {
        M += mu[n];
        ld v = fabsl((ld)M) / sqrtl((ld)n); if (v > E) E = v;
        if (need.count(n)) Mv[n] = M;
        for (auto N : Ns) if (n == N) Emax[N] = E;  // E(N+1) = max_{n<=N}
    }
    printf("N,X,M(X),M(N),E(N+1),Q_exact,identity_exact,m_N,term_lin,term_MN2,term_XmN2,Psi,fourterm_residual,K1,K2,K3,trunc_residual,"
           "MN2_over_E2sqrtX,XmN2_over_E2sqrtX,Psi_over_sqrtX,K1_over_sqrtX,K2_over_sqrtX,K3_over_sqrtX,M_over_sqrtX\n");
    for (auto& q : qs) {
        long long N = q.N, X = q.X;
        vector<int> sf; for (int i = 1; i <= N; ++i) if (mu[i]) sf.push_back(i);
        ld mN = 0; for (int i : sf) mN += (ld)mu[i] / i;
        long long Qex = 0; ld Psi = 0, K1 = 0, K2 = 0, K3 = 0;
        for (int i : sf) for (int j : sf) {
            long long d = 1LL * i * j; int s = mu[i] * mu[j];
            long long fl = X / d, rem = X % d;
            Qex += s * fl;
            ld psi = (ld)rem / (ld)d - 0.5L;   // {X/d} - 1/2
            Psi += s * psi;
            if (d <= X) { K1 += 0.5L * s; K2 += (ld)s * (ld)X / (ld)d; K3 += s * psi; }
        }
        long long MX = Mv[X], MN = Mv[N];
        bool idex = (MX == 2 * MN - Qex);
        ld lin = 2.0L * MN, tMN2 = 0.5L * (ld)MN * MN, tX = (ld)X * mN * mN;
        ld four = lin + tMN2 - tX + Psi - (ld)MX;
        ld trunc = lin + K1 - K2 + K3 - (ld)MX;
        ld sx = sqrtl((ld)X), En = Emax[N];
        printf("%lld,%lld,%lld,%lld,%.6Lf,%lld,%d,%.12Le,%.6Lf,%.6Lf,%.6Lf,%.6Lf,%.3Le,%.6Lf,%.6Lf,%.6Lf,%.3Le,%.5Lf,%.5Lf,%.5Lf,%.5Lf,%.5Lf,%.5Lf,%.5Lf\n",
               N, X, MX, MN, En, Qex, (int)idex, mN, lin, tMN2, tX, Psi, four, K1, K2, K3, trunc,
               tMN2 / (En * En * sx), tX / (En * En * sx), Psi / sx, K1 / sx, K2 / sx, K3 / sx, (ld)MX / sx);
        fflush(stdout);
    }
    return 0;
}
