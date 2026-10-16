// ledger_lab.cpp -- raw odd-seat factor-depth ledger, all roots R in [3, Rmax].
//
// Carrier (CURRENT_PROOF_CONTRACT, main@69e44d7):
//   seats n odd, r^2 < n < (r+1)^2, 2 <= r < R;  w_r = (2r+1)/(r log(r^2+r+1/2));
//   c(n) = w_floor(sqrt n) - 1_Prime(n);  L_R = sum c(n).
// Every seat n has a unique greatest prime q = P+(n) >= 3; Phi_R(q) = sum of c(n)
// over the greatest-prime fibre of q.  T part = Omega(n) <= 2 (prime or distinct
// semiprime; prime squares are never seats), H part = Omega(n) >= 3.
//
// The program adds block r = R when moving R -> R+1 and keeps per-tag charges in
// Fenwick trees, so every sector sum is available for every R.  Sectors:
//   S1: 3 <= q < R           (lower, q-smooth cofactor fibres)
//   S2: R <= q < 2R          (the sqrt(x) band, complete fibres)
//   S3: 2R <= q <= x/3       (upper part of B, complete fibres)
//   S4: x/3 < q < x          (A_R)
// Output: one CSV row per R plus band bracket checks.  Long double throughout.
//
// Build: g++ -O2 -std=c++20 ledger_lab.cpp -o ledger_lab
// Run:   ./ledger_lab Rmax out.csv detailR1,detailR2,...
#include <bits/stdc++.h>
using namespace std;
typedef long double ld;

static const ld MEISSEL = 0.2614972128476427837554268386086958590516L;
static const ld EULERG  = 0.5772156649015328606065120900824024310422L;
static const ld LI2     = 1.045163780117492784844588889194613136523L;

ld li(ld t) {  // logarithmic integral (principal value), t > 1
    ld L = logl(t), term = 1, s = 0;
    for (int k = 1; k < 400; ++k) {
        term *= L / k;           // L^k / k!
        ld add = term / k;
        s += add;
        if (add < s * 1e-21L && k > L) break;
    }
    return EULERG + logl(L) + s;
}
ld Li(ld t) { return li(t) - LI2; }

struct Fen {
    int n; vector<ld> t;
    Fen(int n_) : n(n_), t(n_ + 1, 0) {}
    void add(int i, ld v) { for (++i; i <= n; i += i & -i) t[i] += v; }
    ld pre(int i) const { ld s = 0; for (; i > 0; i -= i & -i) s += t[i]; return s; } // sum [0,i)
    ld range(int a, int b) const { return (b > a) ? pre(b) - pre(a) : 0; }       // [a,b)
};

int main(int argc, char** argv) {
    int Rmax = argc > 1 ? atoi(argv[1]) : 5000;
    string outcsv = argc > 2 ? argv[2] : "ledger.csv";
    set<int> detail;
    if (argc > 3) { string s = argv[3]; stringstream ss(s); string tok; while (getline(ss, tok, ',')) detail.insert(stoi(tok)); }
    const long long X = 1LL * Rmax * Rmax + 2 * Rmax + 2;  // cover (Rmax)^2 and a little more
    // sieve gpf and Omega
    vector<uint32_t> gpf(X, 0);
    vector<uint8_t> om(X, 0);
    vector<int> primes;
    for (long long i = 2; i < X; ++i) {
        if (gpf[i] == 0) {  // prime
            primes.push_back((int)i);
            for (long long m = i; m < X; m += i) gpf[m] = (uint32_t)i;  // later primes overwrite
            for (long long pk = i; pk < X; pk *= i) {
                for (long long m = pk; m < X; m += pk) om[m]++;
                if (pk > X / i) break;
            }
        }
    }
    int P = primes.size();
    vector<int> pidx(X, -1);
    for (int k = 0; k < P; ++k) pidx[primes[k]] = k;
    // prime counting and reciprocal prefix sums
    vector<int> picnt(X, 0);
    {
        int c = 0; for (long long i = 0; i < X; ++i) { if (i >= 2 && pidx[i] >= 0) ++c; picnt[i] = c; }
    }
    vector<ld> recip(P + 1, 0);  // recip[k] = sum_{j<k} 1/p_j
    for (int k = 0; k < P; ++k) recip[k + 1] = recip[k] + 1.0L / primes[k];
    auto sumRecip = [&](long long y) -> ld { // sum_{p<=y} 1/p
        if (y < 2) return 0; int k = picnt[y]; return recip[k];
    };
    auto Efun = [&](long long y) -> ld { return sumRecip(y) - logl(logl((ld)y)) - MEISSEL; };
    // weights
    vector<ld> w(Rmax + 2, 0), cumWide(Rmax + 3, 0);  // cumWide[r] = sum_{s=2}^{r-1} (2s+1) w_s
    for (int r = 2; r <= Rmax + 1; ++r) w[r] = (ld)(2 * r + 1) / ((ld)r * logl((ld)r * r + r + 0.5L));
    for (int r = 2; r <= Rmax + 1; ++r) cumWide[r + 1] = cumWide[r] + (ld)(2 * r + 1) * w[r];
    auto wt = [&](long long u) -> ld { long long r = (long long) floorl(sqrtl((ld)u)); while (r * r > u) --r; while ((r + 1) * (r + 1) <= u) ++r; return w[r]; };
    auto intW = [&](long long t) -> ld {  // int_4^t wtilde(u) du for integer t >= 4
        long long r = (long long) floorl(sqrtl((ld)t)); while (r * r > t) --r; while ((r + 1) * (r + 1) <= t) ++r;
        return cumWide[r] + (ld)(t - r * r) * w[r];
    };

    Fen fall(P), fT(P), fH(P);
    vector<ld> charge(P, 0);
    ld F = 0, Wsum = 0;  // F_R = sum_{r<R} r w_r ; W_R = sum_{r<R} w_r
    long long seats = 0;
    ofstream out(outcsv);
    out << setprecision(15);
    out << "R,F,L,S1,S2,S3,S4,T1,T2,T3,T4,H1,H2,H3,H4,pi_x,pi_x3,pi_Rm1,pi_2Rm1,E_Rm1,E_2Rm1,Li_x,Li_x3,"
           "check_L,Delta,Pred,rho,brlo,brhi,eta_min_viol,eta_max_viol,Bmodel,Bdev,cutmode,Adev,eps_x,eps_x3\n";
    for (int R = 3; R <= Rmax; ++R) {
        // add block r = R-1  (blocks 2..R-1 present for root R)
        int r = R - 1;
        if (r >= 2) {
            long long lo = 1LL * r * r + 1, hi = 1LL * (r + 1) * (r + 1) - 1;
            for (long long n = lo; n <= hi; ++n) {
                if (!(n & 1)) continue;
                ++seats;
                int q = gpf[n]; int k = pidx[q];
                bool prime = (q == n);
                ld c = w[r] - (prime ? 1.0L : 0.0L);
                fall.add(k, c); charge[k] += c;
                if (om[n] <= 2) fT.add(k, c); else fH.add(k, c);
            }
            F += (ld)r * w[r]; Wsum += w[r];
        }
        long long x = 1LL * R * R;
        // sector boundaries as prime-index ranges
        auto idxLE = [&](long long y) -> int { return y < 2 ? 0 : picnt[min<long long>(y, X - 1)]; }; // # primes <= y = index past
        int i3 = idxLE(2);             // primes >= 3 start at index 1 (p=2 at index 0)
        int iR = idxLE(R - 1);          // q < R
        int i2R = idxLE(2LL * R - 1);   // q < 2R
        int ix3 = idxLE(x / 3);         // q <= x/3
        int ix = idxLE(x - 1);          // q < x
        ld S1 = fall.range(i3, iR), S2 = fall.range(iR, i2R), S3 = fall.range(i2R, ix3), S4 = fall.range(ix3, ix);
        ld T1 = fT.range(i3, iR), T2 = fT.range(iR, i2R), T3 = fT.range(i2R, ix3), T4 = fT.range(ix3, ix);
        ld H1 = fH.range(i3, iR), H2 = fH.range(iR, i2R), H3 = fH.range(i2R, ix3), H4 = fH.range(ix3, ix);
        ld L = S1 + S2 + S3 + S4;
        int pix = picnt[x - 1], pix3 = picnt[x / 3], piR = picnt[R - 1], pi2R = picnt[2 * R - 1];
        ld checkL = L - (F - pix + 2);
        // band law
        ld Mband = F * (logl(logl((ld)(2 * R - 1))) - logl(logl((ld)(R - 1)))) - (ld)(pi2R - piR);
        ld Delta = S2 - Mband;
        ld E1 = Efun(R - 1), E2 = Efun(2 * R - 1);
        ld Pred = F * (E2 - E1);
        ld rho = Delta - Pred;
        // per-tag bracket check:  eta(q) = Phi(q)+1-F/q in [W/(2q) - intW(q)/(2q), same + wt(q)]
        ld brlo = 0, brhi = 0; int vmin = 0, vmax = 0;
        if (R >= 5) {
            for (int k = iR; k < i2R; ++k) {
                long long q = primes[k];
                ld eta = charge[k] + 1.0L - F / (ld)q;
                ld lo_ = Wsum / (2.0L * q) - intW(q) / (2.0L * q);
                ld hi_ = lo_ + wt(q);
                brlo += lo_; brhi += hi_;
                if (eta < lo_ - 1e-12L) ++vmin;
                if (eta > hi_ + 1e-12L) ++vmax;
            }
        }
        // A/B cut-mode bookkeeping.  B model: F + 2 - Li(x/3) - int_{x/3}^{x} wtilde dLi.
        // int over blocks: sum_r w_r (Li(min((r+1)^2,x)) - Li(max(r^2,x/3)))
        ld x3 = (ld)x / 3.0L;
        ld intwdLi = 0, intEpsdW = 0;
        {
            long long r0 = (long long) floorl(sqrtl(x3)); while (r0 * r0 > (long long)x3) --r0;
            for (long long rr = r0; rr < R; ++rr) {
                ld a = max<ld>((ld)rr * rr, x3), b = (ld)(rr + 1) * (rr + 1);
                if (b > (ld)x) b = (ld)x;
                if (b > a) intwdLi += w[rr] * (Li(b) - Li(a));
            }
            // int_{(x/3,x)} eps dW: jumps of wtilde at squares s^2 in (x/3, x): (w_s - w_{s-1}) eps(s^2)
            for (long long s = r0 + 1; s < R; ++s) {
                long long sq = s * s; if ((ld)sq <= x3) continue;
                ld eps = (ld)picnt[sq] - Li((ld)sq);
                intEpsdW += (w[s] - w[s - 1]) * eps;
            }
        }
        ld Bmodel = F + 2 - Li(x3) - intwdLi;
        ld B = S1 + S2 + S3;
        ld Bdev = B - Bmodel;
        ld epsx = (ld)pix - Li((ld)x);           // pi(x-) = pi(x) since x is not prime
        ld epsx3 = (ld)pix3 - Li(x3);
        long long rx3 = (long long)floorl(sqrtl(x3)); while ((ld)(rx3+1)*(rx3+1) <= x3) ++rx3; while ((ld)rx3*rx3 > x3) --rx3;
        ld wx3 = w[rx3];                         // wtilde(x/3+) = w_floor(sqrt(x/3))
        ld wxm = w[R - 1];                       // wtilde(x-)
        ld cutmode = -(1 - wx3) * epsx3 - wxm * epsx + intEpsdW;
        ld Adev = S4 - (-(Li((ld)x) - Li(x3)) + intwdLi);
        out << R << ',' << (double)F << ',' << (double)L << ',' << (double)S1 << ',' << (double)S2 << ',' << (double)S3 << ',' << (double)S4 << ','
            << (double)T1 << ',' << (double)T2 << ',' << (double)T3 << ',' << (double)T4 << ','
            << (double)H1 << ',' << (double)H2 << ',' << (double)H3 << ',' << (double)H4 << ','
            << pix << ',' << pix3 << ',' << piR << ',' << pi2R << ',' << (double)E1 << ',' << (double)E2 << ','
            << (double)Li((ld)x) << ',' << (double)Li(x3) << ',' << (double)checkL << ','
            << (double)Delta << ',' << (double)Pred << ',' << (double)rho << ',' << (double)brlo << ',' << (double)brhi << ','
            << vmin << ',' << vmax << ',' << (double)Bmodel << ',' << (double)Bdev << ',' << (double)cutmode << ','
            << (double)Adev << ',' << (double)epsx << ',' << (double)epsx3 << '\n';
        if (detail.count(R)) {
            // detailed stratification of the sqrt band and of B by Omega and cofactor band
            string fn = "detail_R" + to_string(R) + ".txt";
            ofstream d(fn); d << setprecision(12);
            // recompute directly from seats (independent of Fenwick)
            map<string, ld> acc; map<string, long long> cnt;
            for (int rr = 2; rr < R; ++rr) {
                for (long long n = 1LL * rr * rr + 1; n < 1LL * (rr + 1) * (rr + 1); ++n) {
                    if (!(n & 1)) continue;
                    long long q = gpf[n]; long long a = n / q; int o = om[n];
                    ld c = w[rr] - (q == n ? 1.0L : 0.0L);
                    string sec = (q < R) ? "S1" : (q < 2LL * R) ? "S2" : (3 * q <= x) ? "S3" : "S4";
                    string oc = o == 1 ? "O1" : o == 2 ? "O2" : o == 3 ? "O3" : o == 4 ? "O4" : "O5+";
                    string ab;
                    if (a == 1) ab = "a=1"; else {
                        ld e = logl((ld)a) / logl((ld)x);   // cofactor exponent
                        int b8 = (int)floorl(8 * e); ab = "aexp8=" + to_string(b8);
                    }
                    acc[sec + "|" + oc] += c; cnt[sec + "|" + oc]++;
                    acc[sec + "|" + ab] += c; cnt[sec + "|" + ab]++;
                    acc[sec] += c; cnt[sec]++;
                }
            }
            d << "R=" << R << " x=" << x << "\n";
            for (auto& kv : acc) d << kv.first << "\tmass=" << (double)kv.second << "\tcount=" << cnt[kv.first] << "\n";
            d << "Fenwick S1..S4: " << (double)S1 << " " << (double)S2 << " " << (double)S3 << " " << (double)S4 << "\n";
        }
    }
    cerr << "done seats=" << seats << " primes=" << P << "\n";
    return 0;
}
