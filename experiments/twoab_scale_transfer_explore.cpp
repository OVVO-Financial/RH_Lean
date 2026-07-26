// Exact and approximate scale-transfer experiment for RH_Lean.
//
// Usage:
//   g++ -O3 -std=c++17 scale_transfer_explore.cpp -o scale_transfer_explore
//   ./scale_transfer_explore [Rmax] [sample_step] [random_seed] [series_csv]
//
// The program verifies the exact source-resolved identities
//   S_R = A_R - T_R
// and recovery of the transition scale from (m, q^2-c^2).  It then tests
// geometric low-to-high prime-interval scaling under q -> R^2/q, using
// Euclidean, PNT, logarithmic-integral, and a truncated Riemann-R baseline multiplier.
// Numerical output is evidence only; no asymptotic conclusion is inferred.

#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <limits>
#include <numeric>
#include <string>
#include <vector>

static inline int isqrt_floor(int64_t n) {
    int64_t r = (int64_t)std::sqrt((long double)n);
    while ((r + 1) * (r + 1) <= n) ++r;
    while (r * r > n) --r;
    return (int)r;
}

static inline uint64_t splitmix64(uint64_t x) {
    x += 0x9e3779b97f4a7c15ULL;
    x = (x ^ (x >> 30)) * 0xbf58476d1ce4e5b9ULL;
    x = (x ^ (x >> 27)) * 0x94d049bb133111ebULL;
    return x ^ (x >> 31);
}

struct RunningRegression {
    long double n = 0, sx = 0, sy = 0, sxx = 0, syy = 0, sxy = 0, sse = 0;
    void add(long double x, long double y) {
        n += 1; sx += x; sy += y; sxx += x*x; syy += y*y; sxy += x*y;
    }
    long double slope0() const { return sxx > 0 ? sxy / sxx : 0; }
    long double corr() const {
        long double vx = sxx - sx*sx/n;
        long double vy = syy - sy*sy/n;
        long double cov = sxy - sx*sy/n;
        return (vx > 0 && vy > 0) ? cov/std::sqrt(vx*vy) : 0;
    }
};

long double riemann_R(long double x, const std::vector<int8_t>& mu_small) {
    if (x < 2.0L) return 0.0L;
    int nmax = (int)std::floor(std::log(x)/std::log(2.0L));
    long double lx = std::log(x);
    long double out = 0.0L;
    nmax = std::min<int>(nmax, (int)mu_small.size()-1);
    for (int n=1; n<=nmax; ++n) {
        int mn = (int)mu_small[n];
        if (mn == 0) continue;
        out += ((long double)mn/n) * std::expint(lx/n);
    }
    return out;
}

int main(int argc, char** argv) {
    int Rmax = argc > 1 ? std::atoi(argv[1]) : 3000;
    int sample_step = argc > 2 ? std::atoi(argv[2]) : 10;
    uint64_t random_seed = argc > 3 ? std::strtoull(argv[3], nullptr, 10) : 0ULL;
    std::string series_csv = argc > 4 ? argv[4] : "scale_transfer_series.csv";
    if (Rmax < 10) { std::cerr << "Rmax must be >= 10\n"; return 2; }
    int64_t N64 = (int64_t)Rmax * Rmax - 1;
    if (N64 > std::numeric_limits<int>::max()) { std::cerr << "N too large\n"; return 2; }
    int N = (int)N64;

    std::cerr << "sieving through " << N << " (Rmax=" << Rmax << ")\n";
    std::vector<int> factor(N+1, 0); // SPF first, then overwritten by largest prime factor
    std::vector<int8_t> mu(N+1, 0);
    std::vector<int> primes;
    mu[1] = 1;
    for (int i=2; i<=N; ++i) {
        if (factor[i] == 0) {
            factor[i] = i;
            primes.push_back(i);
            mu[i] = -1;
        }
        for (int p : primes) {
            int64_t v = (int64_t)i * p;
            if (v > N) break;
            factor[(int)v] = p;
            if (p == factor[i]) {
                mu[(int)v] = 0;
                break;
            } else {
                mu[(int)v] = -mu[i];
            }
        }
    }
    std::vector<int> pi(N+1,0);
    std::vector<int64_t> mertens(N+1,0);
    factor[1] = 1;
    for (int i=2; i<=N; ++i) {
        bool isprime = (factor[i] == i);
        pi[i] = pi[i-1] + (isprime ? 1 : 0);
        int p = factor[i];
        factor[i] = std::max(p, factor[i/p]);
    }
    for (int i=1; i<=N; ++i) mertens[i] = mertens[i-1] + (int)mu[i];

    std::vector<int64_t> dS(Rmax+2,0), dA(Rmax+2,0), dT(Rmax+2,0);
    std::vector<int64_t> dSr(Rmax+2,0), dAr(Rmax+2,0), dTr(Rmax+2,0);
    std::vector<int64_t> dSo(Rmax+2,0), dAo(Rmax+2,0), dTo(Rmax+2,0);
    std::vector<int64_t> dA_recovered(Rmax+2,0);
    const int bins_list[] = {1,4,16,64};
    const int nb = 4;
    std::vector<std::vector<int64_t>> dA_coarse(nb, std::vector<int64_t>(Rmax+2,0));

    int64_t sqfree_count=0, transport_count=0, born_smooth_count=0, completed_transport_count=0;
    long double max_scale_err=0, sum_logshift=0, sum_logshift2=0;
    long double logmax = std::log((long double)Rmax);

    for (int m=1; m<=N; ++m) {
        int w = (int)mu[m];
        if (w == 0) continue;
        ++sqfree_count;
        int q = (m==1 ? 1 : factor[m]);
        int c = m / q;
        int r = isqrt_floor(m) + 1;
        int s = std::max(r,q);
        int wr = (splitmix64((uint64_t)m ^ random_seed) & 1ULL) ? 1 : -1;
        int wo = 1;
        dS[r] += w; dSr[r] += wr; dSo[r] += wo;
        if (s <= Rmax) { dA[s] += w; dAr[s] += wr; dAo[s] += wo; }
        if (q > r) {
            ++transport_count;
            dT[r] += -w; dTr[r] += -wr; dTo[r] += -wo;
            if (q <= Rmax) {
                dT[q] += w; dTr[q] += wr; dTo[q] += wo;
                ++completed_transport_count;
            }
        } else {
            ++born_smooth_count;
        }

        // Recover q/sqrt(m) from signed doubled height H=q^2-c^2.
        long double H = (long double)q*q - (long double)c*c;
        long double z = H / (2.0L*(long double)m);
        long double lambda_formula = std::exp(0.5L*std::asinh(z));
        long double lambda_direct = (long double)q/std::sqrt((long double)m);
        max_scale_err = std::max(max_scale_err, std::fabs(lambda_formula-lambda_direct));
        int qrec = (int)std::llround(std::sqrt((std::sqrt(H*H + 4.0L*(long double)m*m) + H)/2.0L));
        int srec = std::max(r,qrec);
        if (srec <= Rmax) dA_recovered[srec] += w;

        if (q > r && q <= Rmax) {
            long double ell = std::log((long double)q/(long double)r);
            sum_logshift += ell;
            sum_logshift2 += ell*ell;
            for (int bi=0; bi<nb; ++bi) {
                int B = bins_list[bi];
                int b = std::min(B-1, (int)std::floor((double)(ell/logmax*B)));
                long double mid = ((long double)b + 0.5L) / B * logmax;
                int shat = (int)std::llround((long double)r * std::exp(mid));
                shat = std::max(r+1, std::min(Rmax, shat));
                dA_coarse[bi][shat] += w;
            }
        } else if (s <= Rmax) {
            // Born-smooth sources are not dilated and are placed exactly.
            for (int bi=0; bi<nb; ++bi) dA_coarse[bi][s] += w;
        }
    }

    std::vector<int64_t> S(Rmax+1), A(Rmax+1), T(Rmax+1), Arec(Rmax+1);
    std::vector<int64_t> Sr(Rmax+1), Ar(Rmax+1), Tr(Rmax+1);
    std::vector<int64_t> So(Rmax+1), Ao(Rmax+1), To(Rmax+1);
    std::vector<std::vector<int64_t>> Acoarse(nb, std::vector<int64_t>(Rmax+1));
    int64_t ps=0, pa=0, pt=0, pr=0, psr=0, par=0, ptr=0, pso=0, pao=0, pto=0;
    int64_t max_identity_err=0, max_recovery_err=0;
    for (int R=1; R<=Rmax; ++R) {
        ps += dS[R]; pa += dA[R]; pt += dT[R]; pr += dA_recovered[R];
        psr += dSr[R]; par += dAr[R]; ptr += dTr[R];
        pso += dSo[R]; pao += dAo[R]; pto += dTo[R];
        S[R]=ps; A[R]=pa; T[R]=pt; Arec[R]=pr;
        Sr[R]=psr; Ar[R]=par; Tr[R]=ptr;
        So[R]=pso; Ao[R]=pao; To[R]=pto;
        max_identity_err = std::max<int64_t>(max_identity_err, std::llabs(S[R] - (A[R]-T[R])));
        max_recovery_err = std::max<int64_t>(max_recovery_err, std::llabs(A[R]-Arec[R]));
        for (int bi=0; bi<nb; ++bi) {
            Acoarse[bi][R] = Acoarse[bi][R-1] + dA_coarse[bi][R];
        }
    }

    int R0 = std::max(10, Rmax/10);
    long double eS=0,eA=0,eT=0,eAT=0, meanA=0,meanT=0;
    int nr=Rmax-R0+1;
    for (int R=R0; R<=Rmax; ++R) { meanA += A[R]; meanT += T[R]; }
    meanA/=nr; meanT/=nr;
    long double varA=0,varT=0,covAT=0;
    for (int R=R0; R<=Rmax; ++R) {
        eS += (long double)S[R]*S[R];
        eA += (long double)A[R]*A[R];
        eT += (long double)T[R]*T[R];
        eAT += (long double)A[R]*T[R];
        varA += ((long double)A[R]-meanA)*((long double)A[R]-meanA);
        varT += ((long double)T[R]-meanT)*((long double)T[R]-meanT);
        covAT += ((long double)A[R]-meanA)*((long double)T[R]-meanT);
    }
    long double corrAT = covAT/std::sqrt(varA*varT);

    std::ofstream csv(series_csv);
    csv << "R,S,A,T,A_positive_orientation,A_born_smooth_remainder,T_formula,T_low_mertens_formula,T_pred_length,T_pred_log,T_pred_pnt,T_pred_li,T_pred_riemann";
    for (int bi=0; bi<nb; ++bi) csv << ",A_coarse_B" << bins_list[bi];
    csv << "\n";

    long double agg_sse_len=0, agg_sse_log=0, agg_sse_pnt=0, agg_sse_li=0, agg_sse_riemann=0, agg_sst=0, meanTsamp=0;
    int nsamp=0;
    int64_t max_t_formula_error=0, max_t_low_mertens_formula_error=0;
    std::vector<long double> exactTs, predLens, predLogs, predPnts, predLis, predRiemanns;
    RunningRegression per_c_len, per_c_log, per_c_pnt, per_c_li, per_c_riemann;

    for (int R=std::max(10,sample_step); R<=Rmax; R+=sample_step) {
        int64_t tformula=0, tLowMertensFormula=0, Apositive=0;
        long double predLen=0, predLog=0, predPnt=0, predLi=0, predRiemann=0;
        int64_t R2m1=(int64_t)R*R-1;
        // Exact prime-dilation form: group primes q>R by d=floor((R^2-1)/q).
        // Every d is below R, so T_R is determined entirely by lower-scale
        // Mertens values M(d).
        for (int d=1; d<R; ++d) {
            int upperQ=(int)(R2m1/d);
            int lowerQ=std::max(R,(int)(R2m1/(d+1)));
            int primeCount=pi[upperQ]-pi[lowerQ];
            tLowMertensFormula += mertens[d]*primeCount;
        }

        for (int c=1; c<R; ++c) {
            int muc=(int)mu[c];
            if (muc==0) continue;
            int upper=(int)(R2m1/c);
            int Hcnt=pi[upper]-pi[R];
            tformula += (int64_t)muc*Hcnt;
            int Lcnt=pi[R]-pi[c];
            Apositive -= (int64_t)muc*Lcnt;
            long double scaleLen=(long double)R/c;
            long double lowMid=std::sqrt((long double)c*R);
            long double highUpper=(long double)R*R/c;
            long double highMid=std::sqrt((long double)R*highUpper);
            long double scaleLog=scaleLen;
            if (lowMid>1.0L && highMid>1.0L) scaleLog *= std::log(lowMid)/std::log(highMid);
            long double scalePnt=scaleLen;
            if (R>1 && highUpper>1.0L) scalePnt *= std::log((long double)R)/std::log(highUpper);
            predLen += (long double)muc*scaleLen*Lcnt;
            predLog += (long double)muc*scaleLog*Lcnt;
            predPnt += (long double)muc*scalePnt*Lcnt;
            long double cLi = std::max<long double>(2.0L, (long double)c);
            long double liU = std::expint(std::log(highUpper));
            long double liR = std::expint(std::log((long double)R));
            long double liC = std::expint(std::log(cLi));
            long double scaleLi = (liR != liC) ? (liU-liR)/(liR-liC) : scalePnt;
            predLi += (long double)muc*scaleLi*Lcnt;
            long double rrU=riemann_R(highUpper,mu), rrR=riemann_R((long double)R,mu), rrC=riemann_R((long double)c,mu);
            long double scaleRiemann = (rrR != rrC) ? (rrU-rrR)/(rrR-rrC) : scaleLi;
            predRiemann += (long double)muc*scaleRiemann*Lcnt;
            per_c_len.add(scaleLen*Lcnt,Hcnt);
            per_c_log.add(scaleLog*Lcnt,Hcnt);
            per_c_pnt.add(scalePnt*Lcnt,Hcnt);
            per_c_li.add(scaleLi*Lcnt,Hcnt);
            per_c_riemann.add(scaleRiemann*Lcnt,Hcnt);
        }
        max_t_formula_error = std::max<int64_t>(max_t_formula_error, std::llabs(T[R]-tformula));
        max_t_low_mertens_formula_error = std::max<int64_t>(max_t_low_mertens_formula_error, std::llabs(T[R]-tLowMertensFormula));
        exactTs.push_back((long double)T[R]); predLens.push_back(predLen); predLogs.push_back(predLog); predPnts.push_back(predPnt); predLis.push_back(predLi); predRiemanns.push_back(predRiemann);
        meanTsamp += T[R]; ++nsamp;
        csv << R << ',' << S[R] << ',' << A[R] << ',' << T[R] << ',' << Apositive << ',' << (A[R]-Apositive) << ',' << tformula << ',' << tLowMertensFormula << ','
            << std::setprecision(17) << (double)predLen << ',' << (double)predLog << ',' << (double)predPnt << ',' << (double)predLi << ',' << (double)predRiemann;
        for (int bi=0; bi<nb; ++bi) csv << ',' << Acoarse[bi][R];
        csv << '\n';
    }
    meanTsamp/=nsamp;
    for (int i=0;i<nsamp;++i) {
        agg_sse_len += (predLens[i]-exactTs[i])*(predLens[i]-exactTs[i]);
        agg_sse_log += (predLogs[i]-exactTs[i])*(predLogs[i]-exactTs[i]);
        agg_sse_pnt += (predPnts[i]-exactTs[i])*(predPnts[i]-exactTs[i]);
        agg_sse_li += (predLis[i]-exactTs[i])*(predLis[i]-exactTs[i]);
        agg_sse_riemann += (predRiemanns[i]-exactTs[i])*(predRiemanns[i]-exactTs[i]);
        agg_sst += (exactTs[i]-meanTsamp)*(exactTs[i]-meanTsamp);
    }

    auto energy_stats = [&](const std::vector<int64_t>& X, const std::vector<int64_t>& Y, const std::vector<int64_t>& Z) {
        long double ex=0,ey=0,ez=0,mx=0,my=0;
        for(int R=R0;R<=Rmax;++R){ ex+=(long double)X[R]*X[R]; ey+=(long double)Y[R]*Y[R]; ez+=(long double)Z[R]*Z[R]; mx+=Y[R]; my+=Z[R]; }
        mx/=nr; my/=nr; long double vx=0,vy=0,cv=0;
        for(int R=R0;R<=Rmax;++R){ long double a=Y[R]-mx,b=Z[R]-my; vx+=a*a;vy+=b*b;cv+=a*b; }
        long double corr=(vx>0&&vy>0)?cv/std::sqrt(vx*vy):0;
        return std::vector<long double>{ex/(ey+ez),corr,ex,ey,ez};
    };
    auto rs=energy_stats(Sr,Ar,Tr);
    auto os=energy_stats(So,Ao,To);

    std::cout << std::setprecision(12);
    std::cout << "Rmax=" << Rmax << " N=" << N << " primes=" << primes.size() << "\n";
    std::cout << "squarefree_sources=" << sqfree_count
              << " transport_sources=" << transport_count
              << " born_smooth_sources=" << born_smooth_count
              << " completed_transport_sources=" << completed_transport_count << "\n";
    std::cout << "max_A_minus_T_minus_S=" << max_identity_err << "\n";
    std::cout << "max_height_scale_formula_error=" << (double)max_scale_err << "\n";
    std::cout << "max_A_recovery_error_from_m_height=" << max_recovery_err << "\n";
    std::cout << "max_T_prime_interval_formula_error=" << max_t_formula_error << "\n";
    std::cout << "max_T_low_mertens_transform_error=" << max_t_low_mertens_formula_error << "\n";
    long double meanEll = completed_transport_count ? sum_logshift/completed_transport_count : 0;
    long double sdEll = completed_transport_count ? std::sqrt(sum_logshift2/completed_transport_count-meanEll*meanEll) : 0;
    std::cout << "completed_transport_log_shift_mean=" << (double)meanEll
              << " sd=" << (double)sdEll << "\n";
    std::cout << "energy_S=" << (double)eS << " energy_A=" << (double)eA
              << " energy_T=" << (double)eT << " interaction_minus2AT=" << (double)(-2*eAT) << "\n";
    std::cout << "energy_cancellation_ratio_S_over_AplusT=" << (double)(eS/(eA+eT)) << "\n";
    std::cout << "corr_A_T=" << (double)corrAT << "\n";
    std::cout << "random_sign_energy_ratio=" << (double)rs[0] << " random_sign_corr_A_T=" << (double)rs[1] << "\n";
    std::cout << "all_plus_energy_ratio=" << (double)os[0] << " all_plus_corr_A_T=" << (double)os[1] << "\n";
    std::cout << "per_c_count_corr_length_scaled=" << (double)per_c_len.corr()
              << " slope0=" << (double)per_c_len.slope0() << "\n";
    std::cout << "per_c_count_corr_log_scaled=" << (double)per_c_log.corr()
              << " slope0=" << (double)per_c_log.slope0() << "\n";
    std::cout << "per_c_count_corr_pnt_scaled=" << (double)per_c_pnt.corr()
              << " slope0=" << (double)per_c_pnt.slope0() << "\n";
    std::cout << "per_c_count_corr_li_scaled=" << (double)per_c_li.corr()
              << " slope0=" << (double)per_c_li.slope0() << "\n";
    std::cout << "per_c_count_corr_riemann_scaled=" << (double)per_c_riemann.corr()
              << " slope0=" << (double)per_c_riemann.slope0() << "\n";
    std::cout << "aggregate_T_R2_length=" << (double)(1-agg_sse_len/agg_sst)
              << " aggregate_T_R2_log=" << (double)(1-agg_sse_log/agg_sst)
              << " aggregate_T_R2_pnt=" << (double)(1-agg_sse_pnt/agg_sst)
              << " aggregate_T_R2_li=" << (double)(1-agg_sse_li/agg_sst)
              << " aggregate_T_R2_riemann=" << (double)(1-agg_sse_riemann/agg_sst) << "\n";
    for (int bi=0; bi<nb; ++bi) {
        long double sse=0,sst=0,mean=0;
        for(int R=R0;R<=Rmax;++R) mean+=A[R]; mean/=nr;
        for(int R=R0;R<=Rmax;++R){
            long double d=(long double)Acoarse[bi][R]-A[R]; sse+=d*d;
            long double z=(long double)A[R]-mean; sst+=z*z;
        }
        std::cout << "coarse_2ab_bins=" << bins_list[bi] << " A_prefix_R2=" << (double)(1-sse/sst) << "\n";
    }
    int64_t terminalApositive=0;
    for (int c=1; c<Rmax; ++c) {
        if (mu[c] == 0) continue;
        terminalApositive -= (int64_t)mu[c]*(pi[Rmax]-pi[c]);
    }
    std::cout << "terminal_A_positive_orientation=" << terminalApositive
              << " terminal_A_born_smooth_remainder=" << (A[Rmax]-terminalApositive)
              << " terminal_born_smooth_minus_T=" << (A[Rmax]-terminalApositive-T[Rmax]) << "\n";
    std::cout << "terminal_R S=" << S[Rmax] << " A=" << A[Rmax] << " T=" << T[Rmax] << "\n";
    std::cout << "series_csv=" << series_csv << "\n";
    return 0;
}
