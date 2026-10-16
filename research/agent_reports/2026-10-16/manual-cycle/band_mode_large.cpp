// band_mode_large.cpp -- the proved sqrt(x)-band identity extrapolated to large R.
//
// By Owner-3 (paper proof, verified exactly for R<=5000 by ledger_lab), the band
//   T_R = sum_{R<=q<2R} Phi_R(q)  equals  M_R + F_R*(E(2R-1)-E(R-1)) + rho_R,
// with rho_R in an explicit bracket of size O(R/log^2 R).  The full ledger at x=R^2
// is out of reach for R ~ 1e9, but F_R and E(.) only need primes below 2R.  This
// program sieves primes to 2*Rmax, records E(y)=sum_{p<=y}1/p - loglog y - M at
// y=R-1, 2R-1 for a grid of R, computes F_R exactly, and also re-derives the
// Meissel-Mertens constant as an internal check.
// Build: g++ -O2 -std=c++20 band_mode_large.cpp -o band_mode_large
// Run:   ./band_mode_large Rmax out.csv
#include <bits/stdc++.h>
using namespace std;
typedef long double ld;
static const ld MEISSEL = 0.2614972128476427837554268386086958590516L;
static const ld EULERG  = 0.5772156649015328606065120900824024310422L;

int main(int argc, char** argv) {
    long long Rmax = argc > 1 ? atoll(argv[1]) : 1000000000LL;
    string outcsv = argc > 2 ? argv[2] : "band_large.csv";
    // grid of R
    vector<long long> Rs;
    int G = 3000;
    for (int i = 0; i <= G; ++i) { long long R = llround(powl(10.0L, 3.0L + (log10l((ld)Rmax) - 3.0L) * i / G)); Rs.push_back(R); }
    for (long long dec = 10000; dec <= Rmax; dec *= 10) for (int j = 0; j < 500; ++j) { long long R = dec + (dec / 1000) * j; if (R <= Rmax) Rs.push_back(R); }
    sort(Rs.begin(), Rs.end()); Rs.erase(unique(Rs.begin(), Rs.end()), Rs.end());
    vector<long long> ys; for (auto R : Rs) { ys.push_back(R - 1); ys.push_back(2 * R - 1); }
    sort(ys.begin(), ys.end()); ys.erase(unique(ys.begin(), ys.end()), ys.end());
    unordered_map<long long, ld> S;  // y -> sum_{p<=y} 1/p
    S.reserve(ys.size() * 2);
    long long N = 2 * Rmax;
    long long sq = (long long) sqrtl((ld)N) + 2;
    // base primes
    vector<char> isc(sq + 1, 0); vector<long long> base;
    for (long long i = 2; i <= sq; ++i) if (!isc[i]) { base.push_back(i); for (long long j = i * i; j <= sq; j += i) isc[j] = 1; }
    // Kahan sums: sum 1/p and sum log(1-1/p)+1/p
    ld s = 0, c = 0, t2 = 0, c2 = 0;
    auto kadd = [](ld& sum, ld& comp, ld v) { ld y = v - comp; ld t = sum + y; comp = (t - sum) - y; sum = t; };
    size_t qi = 0;
    auto record_upto = [&](long long y) { while (qi < ys.size() && ys[qi] < y) { S[ys[qi]] = s + 0; ++qi; } };
    // handle p=2 then odd segmented
    record_upto(2); kadd(s, c, 0.5L); kadd(t2, c2, logl(0.5L) + 0.5L);
    const long long SEG = 1 << 21;  // odd numbers per segment
    vector<char> seg(SEG);
    long long primecount = 1;
    for (long long lo = 3; lo <= N; lo += 2 * SEG) {
        long long hi = min(N, lo + 2 * SEG - 2);  // odd numbers lo..hi
        fill(seg.begin(), seg.end(), 0);
        for (size_t k = 1; k < base.size(); ++k) {
            long long p = base[k]; if (p * p > hi) break;
            long long st = max(p * p, ((lo + p - 1) / p) * p); if (!(st & 1)) st += p;
            for (long long m = st; m <= hi; m += 2 * p) seg[(m - lo) >> 1] = 1;
        }
        for (long long n = lo; n <= hi; n += 2) {
            if (!seg[(n - lo) >> 1]) {
                record_upto(n);
                ld inv = 1.0L / (ld)n; kadd(s, c, inv); kadd(t2, c2, log1pl(-inv) + inv); ++primecount;
            }
        }
    }
    record_upto(N + 1);
    ld tail = 1.0L / (2.0L * (ld)N * logl((ld)N));  // -sum_{p>N}(log(1-1/p)+1/p) ~ sum 1/(2p^2)
    ld Mcomp = EULERG + t2 - tail;
    fprintf(stderr, "primes<=%lld: %lld ; Meissel computed %.18Lf vs const %.18Lf (diff %.3Le)\n", N, primecount, Mcomp, MEISSEL, Mcomp - MEISSEL);
    // F_R exactly along sorted Rs
    ofstream out(outcsv); out << setprecision(17);
    out << "R,F,E_Rm1,E_2Rm1,Pred,RlogR,Pred_over_RlogR,Pred_over_R15_log2\n";
    ld F = 0; long long r = 2;
    for (auto R : Rs) {
        while (r < R) { F += (ld)(2 * r + 1) / logl((ld)r * r + r + 0.5L); ++r; }
        auto E = [&](long long y) { return S[y] - logl(logl((ld)y)) - MEISSEL; };
        ld E1 = E(R - 1), E2 = E(2 * R - 1), Pred = F * (E2 - E1);
        ld RlogR = (ld)R * logl((ld)R);
        out << R << ',' << (double)F << ',' << (double)E1 << ',' << (double)E2 << ',' << (double)Pred << ',' << (double)RlogR << ','
            << (double)(Pred / RlogR) << ',' << (double)(Pred / (powl((ld)R, 1.5L) / (logl((ld)R) * logl((ld)R)))) << '\n';
    }
    return 0;
}
