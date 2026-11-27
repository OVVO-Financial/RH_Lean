# V6 — native multiplicity, integral index and economical factorial recovery

**Directive NATIVE_MULTIPLICITY_INDEX_V6 (2026-11-25), PR #1213.** A substantially native reconstruction of the quantitative mechanism, not a reconstruction of Alpöge's entire host. Keep #1201 as final integration and use the existing principal prime-power window consumer. V5's complete-cell reduction remains valid as a parallel physical diagnostic; do not ask for the old negative-balance energy estimate in new notation. V6 seeks an independently constructed arithmetic certificate of divisibility and size. Results below are paper proofs and reproducible diagnostics, not new Lean-certified declarations, a new zero-free exponent, or an unconditional RH proof.

## 1. Actual integral codimension

For integers N>=1, m>=1, L=mN, set LCM(k)=lcm(1,...,k), LCM(0)=1 and

    A_m(N) = product_{1<=j<=L} gcd(j,LCM(floor((j-1)/m))).
    S(N) = sum_{n<=N} Lambda(n)*(N/n-1).
    G(N) = S(N)-N log N+(1+gamma)N.

For each prime power d=p^e, the corresponding factor occurs iff d|j and j>md. Consequently

    v_p(A_m) = sum_{e>=1} max(floor(L/p^e)-m,0).

This is also exactly the valuation of the gcd of all (L-m)-minors of diag(1,...,L): the nonzero minors are products of L-m distinct diagonal entries, and deleting the m greatest p-adic valuations minimizes the sum simultaneously for every threshold e at that p. The minimizers need not be the same for different primes. Include the conventional empty minor when N=1. For ordinary integer-polynomial forward difference Delta from span{x,...,x^L} to degree <=L-1, use falling factorials (x)_j: Delta (x)_j=j(x)_(j-1). The two integral basis transformations are unimodular; thus the determinantal divisor of the same codimension is A_m. This is genuine arithmetic multiplicity, NOT an assertion that the raw square root coordinate is itself a dimension gain or that an arbitrary unimodular change of basis shrinks an index.

Related existing sources on #1201 (pinned 5eb0d87573d087aed794ef065ceea034021fa280): [NativePrimeExponentJet](https://github.com/OVVO-Financial/RH_Lean/blob/5eb0d87573d087aed794ef065ceea034021fa280/RHLean/Geometry/NativePrimeExponentJet.lean) (signed_inverse, det_one, column_mass, factorization_recovery), [NativeThetaIntegralJets](https://github.com/OVVO-Financial/RH_Lean/blob/5eb0d87573d087aed794ef065ceea034021fa280/RHLean/Geometry/NativeThetaIntegralJets.lean), [NativePrimeExponentAncestry](https://github.com/OVVO-Financial/RH_Lean/blob/5eb0d87573d087aed794ef065ceea034021fa280/RHLean/Analysis/AlpogeThin/NativePrimeExponentAncestry.lean). Reuse their integral basis/finite-difference ideas; these branch-pinned references are not imported by this PR, nor do their existing statements prove the new index bound.

## 2. Exact complementary index and original handoff

Let C_m(N)=(N!)^m/A_m(N). By Legendre and the preceding formula,

    cap(d)=m-floor(m*(N mod d)/d), 2<=d<=N,
    v_p(C_m)=sum_{p^e<=N} cap(p^e).

Each cap is nonnegative, so C_m is an integer. The exact identity is

    S(N)=log A_m/m + E_m(N),
    E_m(N)=(1/m)*sum_{n<=N} Lambda(n)*{mN/n},
    0<=E_m(N)<=psi(N)/m.

With Stirling,

    G(N)=gamma*N-log C_m/m + [log(N!)-N log N+N] + E_m(N)
        =gamma*N-log C_m/m+O(log N+N/m).

For N=R^2-1, m=R>=2 the rounding and Stirling costs are O(R). This is the *complete* von Mangoldt source, including every prime power: do not add the earlier pure-power correction a second time. The sign is important: an independently large divisor of C_m gives the required **upper** bound on G.

The sufficient terminal quantitative task is log C_R(R^2-1) >= gamma*R*(R^2-1)-O_eta(R^(2+eta)), for every eta>0. The existing #1205 handoff consumes the resulting G bound. Do not make the construction stronger than required: a suitable uniform complete-window version is also sufficient via the existing SmallEpsilonWindowBound quantifiers. To use square-clock windows rather than eventual all clocks, prove real interpolation and endpoint collars explicitly (G is continuous, and away from the integers its derivative is sum_{n<=x} Lambda(n)/n-log x+gamma=O(log x) by Chebyshev). No isolated favorable scales or unproved window existence suffice.

## 3. Actual independently chosen factorial lifts

Take any 0<=a_i<N (i=1,...,m). Let

    U_a = (N!)^m / ((sum_i a_i)! * product_i (N-a_i-1)!).

The reduced numerator of every U_a divides C_m. Indeed for d=p^e, let r=N mod d, s_i=a_i mod d. Legendre's formula gives the per-power contribution

    delta(d) = sum_i 1_{s_i>=r} - floor(sum_i s_i/d).

If k of the s_i are >=r, then delta(d)<=k-floor(k*r/d)<=m-floor(m*r/d); the last expression is monotone in k because r<d. For d>N, r=N and all s_i<N, hence delta(d)<=0. Summing contributions at p and taking the positive part proves the assertion. This is simultaneous prime divisibility on the *same actual rational number*, including the negative costs of carries and large prime powers. The formula is an exact paper proof, not an independence assumption.

For the diagonal choice all a_i=a, denote U(a)=(N!)^m/((ma)!*(N-a-1)!^m). With N=m^2-1 form the prime-blind grid a=0,m,...,(m-1)m and

    H_m(N)=lcm_{0<=j<m} numerator(U(jm)).

Then H_m divides C_m, with only m shared lift positions for all primes. No prime locations are used to choose the grid.

## 4. New unconditional economical shared-grid recovery

For p>m, p^2>N, so cap(p) is the whole available C_m valuation at p. Write r=N mod p and choose a=m*ceil(r/m). If a<p and a<N, then ma<p^2, so every contribution at p^e, e>=2, is zero. At p the valuation is m-floor(ma/p). Thus cap(p)-v_p(H_m)<=floor(ma/p)-floor(mr/p)<=m^2/p+1.

If a>=p (including the case a>=N since p<=N), then p-r<m, and cap(p)=ceil(m*(p-r)/p)<=m^2/p+1; use v_p(H_m)>=0. The selected point is on the grid whenever a<N, because N=m^2-1. This proves a pointwise valuation loss for all high primes, not an assertion that a single a works for every prime.

For low primes p<=m, use the whole cap bound:

    sum_{p<=m} v_p(C_m)*log p <= m*pi(m)*log N = O(m^2)

by Chebyshev. For high primes sum (m^2/p+1)*log p <= O(m^2 log N+N) by Chebyshev and partial summation. Therefore

    0 <= log C_m-log H_m = O(m^2 log m),
    0 <= (log C_m-log H_m)/m = O(R log R) at m=R.

This pays the local shared-grid recovery loss at RH scale. It does **not** prove an independent lower bound on log H_m or on log C_m. In particular an lcm of many rational numerators is not a product of their absolute sizes. A numerator may exceed or differ substantially from its rational value.

## 5. Why naive global constructions fail

### 5.1 A single ordinary monomial finite-difference minor

For the L-by-L ordinary monomial Delta matrix, det Delta=L! up to sign. Its inverse entries are coefficients of (B_i(x)-B_i(0))/i, 1<=i<=L, where B_i are Bernoulli polynomials. Jacobi's complementary minor identity expresses each nonzero (L-m)-minor as L! times an m-minor of this inverse, up to sign.

By von Staudt-Clausen, the denominator of B_k, k even positive, divides the product of p with p-1|k (B_0=1, B_1=-1/2, odd k>1 zero). Its logarithm is <= tau(k) log(k+1)=O_epsilon(L^epsilon) uniformly; the factor 1/i adds at most log L. The product of the denominators of the m^2 entries clears the entire complementary minor. Its nonzero absolute value is thus >=exp(-O_epsilon(m^2 L^epsilon)). At m=R, L=R(R^2-1), choose epsilon<1/3. Every nonzero large minor has log magnitude >=log(L!)-o(L). The required upper size for an A_m multiple would be L(log N-1-gamma)+O_eta(R^(2+eta)), smaller than log(L!) by order L log m. A single ordinary monomial-basis minor is therefore too expensive. This is a paper obstruction to that specific matrix and minor, not to arbitrary changed bases, integer combinations of minors, or all possible recovery constructions.

### 5.2 Products of one ordinary binomial split per lift

Restrict to P=product_{i=1}^m binom(N,a_i) that divides C_m, with m=R. Put t_i=min(a_i,N-a_i)/N in [0,1/2]. For N/2<p<=N, the binomial valuation is exactly 1 when t_i>(N-p)/N, and 0 otherwise. The cap at p gives

    fraction of t_i > s_p <= 2-N/p+1/m,
    s_p=(N-p)/N.

For fixed s in (0,1/2), by PNT there are primes with s_p<=s arbitrarily close to s as N grows. Consequently the limiting upper tail is bounded by (1-2s)/(1-s). The entropy bound log binom(N,a)<=N h(t), h(t)=-t log t-(1-t)log(1-t), and h(t)=integral_0^t log((1-s)/s) ds give, by dominated limsup using the integrable nonnegative derivative,

    limsup log P/(mN) <= integral_0^(1/2) log((1-s)/s)*(1-2s)/(1-s) ds
                       = 2 log 2 - pi^2/12
                       = 0.5638273277... < gamma.

For the integral, write the factor as 2-1/(1-s) and use u=s/(1-s) on the second term. The fixed asymptotic gap cannot be absorbed into the square-root error. This obstruction applies to the specified divisible product, not arbitrary signed factorial ratios or determinant combinations.

### 5.3 Cross-lift factorial determinant diagnostics

The additional script evaluates a beta-grid determinant via a Vandermonde formula (exact rational checks at small m) and a pooled Vandermonde/Selberg-style factorial ratio as a size-only diagnostic. At R=4096 normalized negative log determinant is 0.499939 and best scanned pooled value is 0.006888. Do NOT claim their denominators divide C_m without proving the necessary divisibility. These are not a global recovery supplier.

## 6. Attack signed factorial certificates, not raw covariance

Take integer exponents v_k supported on 2<=k<=N and a positive integer Q. Define

    P = product_k (k!)^v_k   (positive rational).
    F(d) = sum_k v_k floor(k/d).

If for EVERY integer 2<=d<=N,

    F(d) <= Q*cap(d),

then for every prime p, v_p(P)=sum_{p^e<=N} F(p^e)<=Q*v_p(C_m). Hence numerator(P) divides C_m^Q and

    log P / Q <= log C_m.

Equivalently use rational exponents v_k/Q in the logarithmic objective, but never claim the uncleared numerator divides C_m. Negative exponents are essential. An independent construction with log P/Q >= gamma*m*N-O_eta(R^(2+eta)) on the required scales would close the native route via section 2.

**Anti-circularity audit:** the floor matrix on d,k=2,...,N is triangular with unit diagonal. Back substitution v_d=cap(d)-sum_{k>d}v_k floor(k/d) (Q=1) saturates every cap. Its rational factorial product is then exactly C_m by unique factorization. This is not progress: it only repackages the original index. A uniform useful certificate must have an independently evaluated size lower bound, not a sum of the original prime valuations or a fitted gamma term. Seek structured signed coefficient families from the actual Euler/finite-difference and prime-exponent jet operations, whose floor inequalities and Stirling moments can be proved independently. Do not claim that a finite LP or low coefficient norm proves a uniform construction. All-integer constraints are a sufficient prime-blind design choice; failure of that restricted family alone is not failure of the prime-specific problem.

## 7. Reproducible diagnostics and audit

- [Sparse grid C++](../scripts/native_sparse_factorial_recovery.cpp), [eight-scale JSONL](native_sparse_factorial_recovery_results.jsonl). Compile with g++ -O3 -std=c++17 scripts/native_sparse_factorial_recovery.cpp -o /tmp/native_sparse_factorial_recovery; run with no arguments or supply R values. At R=4096, N=16777215, L=68719472640 (valuation formulas, not materializing all L rows), 1,077,307 high primes and 4,096 grid positions; 357,083 high-prime caps recovered exactly, 10,232,105 high candidate valuation tests and 2,310,144 low tests. Direct exhaustive high-grid cross-check only for R<=64. All assertions pass; logarithms are long double. Loss (log C-log H)/R^2=1.0220701858, log H/(mN)=0.5770921698, log C/(mN)=0.5773416987. The observed small loss is not a proof of O(R) normalized expense.
- [Exact arithmetic and certificate optimizer](../scripts/native_index_certificate_test.py), [extended LP output](native_index_certificate_lp_extended_results.jsonl). Requires Python, numpy and scipy. Run python scripts/native_index_certificate_test.py for exact index and source diagnostics, and append lp_extended for the recorded LP parameters. Append lp_witnesses to emit actual cleared integer coefficients. Float LP proposal; exact integer cap checks with explicit no-overflow guard; linear moment after rounding is recorded, not silently reset to zero. Optimization status and logs are not certified enclosures. Exact arithmetic check for R=2,3,4,5,6,8; gcd of minors directly enumerated at L<=24. The R16 witness is also [stored explicitly](native_index_certificate_R16_witness.json); it was rechecked at every integer d=2,...,255 with unbounded integer arithmetic.
- [Cross-lift factorial ratios and determinant diagnostics](../scripts/native_cross_lift_determinant.py), [recorded results](native_cross_lift_determinant_results.jsonl). Exact rational divisibility for every tuple at R=2,3,4 (9+512+50625=51,146 tuples); checks of beta determinant at small sizes. Run python scripts/native_cross_lift_determinant.py (full scan may take time).
- Local re-audit: reran C++ R=16,32,64,128,317 and reproduced the five recorded rows exactly; reran all exact index cases, all 51,146 tuple checks, beta determinant checks R=4,8, and the first LP case with identical summary. Larger rows are preserved from the preceding experiment. No local Lean executable or Lean build is claimed.

| R | shared-grid log H/(mN) | loss / R^2 |
|---:|---:|---:|
|16|0.547404|1.072513|
|32|0.559620|1.154119|
|64|0.566543|1.217 (rounded)|
|128|0.571984|1.189 (rounded)|
|317|0.575203|1.148 (rounded)|
|1027|0.576652|1.080 (rounded)|
|2048|0.576951|1.043 (rounded)|
|4096|0.577092|1.022070|

See JSONL for exact recorded precision. LP normalized log(P)/(Q*mN): R16 grid128 0.609578 (67 coefficients); R32 grid256 0.591195 (165); R64 grid256 0.576362 (336), grid512 0.581921 (390). These are finite, not asymptotic. No large-scale uniform coefficient construction exists in this update.

## 8. Seven-role directive — priority V6, V5 retained

- COORDINATOR: target independently generated signed factorial certificates or another explicitly justified native integral index construction. Track the exact C_m handoff and earned O(R) rounding/O(R log R) grid loss separately. Keep #1201 final integration; no new conditional RH endpoint.
- WHEEL: formalize gcd-index valuation and Legendre cap, floor/carry inequalities, prime-blind shared grid and p>R first-power recovery. Preserve all low-prime and higher-power allowances.
- OWNER: construct a structured signed factorial family using the native Euler insertion, complete-cell Perron differences and integral exponent jets, with actual simultaneous valuation constraints. Identify what supplies size independently of C_m; no diagonal index or arbitrary determinant as a surrogate.
- ANALYTIC: derive and bound explicit Stirling moments of the constructed coefficients and prove the original G upper bound with exact complete-window quantifiers and interpolation; do not demand full covariance control, do not double charge proper prime powers.
- CENSUS: regenerate and store coefficient witnesses, track certificate support, moment, exact cap slack, normalized log, and failure of sparse families. Test growth of explicit candidate families over scales; compare with binomial ceiling and factorial determinant diagnostics. No prime-location fitting or extrapolation of finite successes as proof.
- REFEREE: audit signs, Q-power normalization, floors for d>N, joint carries, p-adic versus archimedean inequalities, rational versus numerator size, overflow and quantifiers. Reject saturated floor-matrix inversion as a new proof, hypothetical independent rank, and any use of the terminal estimate to certify the size.
- LEAN: reuse the integral change-of-basis and exponent-jet lemmas where available; formalize the exact valuation, factorial lift divisibility and shared-grid recovery suppliers, then the actual certificate family and independently proved size. Use #1205 existing handoff only after the quantitative bound. No sorry, axioms, vacuous geometry, or new assumed critical estimate.

This is a repository-scoped directive only; no external runtime retasking, merge, or RH claim. V6 paper suppliers need Lean formalization and hosted review.


## V7 follow-on (2026-11-25)

Prioritize [native two-chart density recovery for finite C](RHLEAN_NATIVE_TWO_CHART_DENSITY_RECOVERY_20261125.md), using existing concurrent coordinates and signed shared density errors. V6 local factorial recovery is retained; neither V6 global size nor V7 global signed bound is proved.
