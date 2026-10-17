# Census pre-registration — unified manual cycle 2026-10-17 (written before any experiment of this cycle was run)
Timestamp (America/New_York): 2026-10-17T12:15:21-04:00

Run: RH-UNIFIED-MANUAL-20261017T1155-0400. Carrier: the merged #919 coefficient a6 = 1_(gcd(n,6)=1)[mu * (chi_-3 . mu)], C6(z) = sum_(m<=z) a6(m), period-36 kernel K, buckets B_X(t) = C6(floor(X/t)) - C6(floor(X/(t+1))), D_X(t) = B_X(t) - B_X(t+1). Zero-K buckets retained everywhere.

## Part A — exact regressions (integer equalities; any single failure is reported with its witness)

A1. Corrected crosswalk at X = R^2 - 1, Hecke root y = R - 1, for R in {7, 13, 103, 317, 1027} plus every R in [4, 400]:
    P0(X; R-1) = A_R + H_R - I_R + 1_(R prime)(1 + chi_-3(R)) M(R-1);  M(X) = P0 - 2 P1 = A_R - T_R.
A2. Same-cutoff dictionary for every X in [12, 20000] and X in {380, R^2-1, R^2, R^2+1 : R in the list}: with y = floor(sqrt X),
    P0 = A_y + T^chi_y,  P1 = H_y = (T_y + T^chi_y)/2,  where T^chi_y = H_y - I_y = sum_(y<q<=X) chi_-3(q) M(floor(X/q)).
A3. Census-2 general-X high formula: V_high = 2 sum_(n<=floor(X/(r+1))) |a6(n)| - |B_X(r+1)| <= 2 sqrt X, all X in [256, 20000] and the list (X = 380 must show the boundary term 2).
A4. Telescoped unweighted low return: sum_(t<=r) D_X(t) = C6(X) - C6(floor(X/2)) - B_X(r+1), same X set.
A5. Residue-class identities: U_1(X) := sum_(t == 1 mod 3) B_X(t) = sum_(a,b>=0) M(floor(X/(3^a 4^b)));  U_0+U_1+U_2 = C6(X);  M(X) = U_1(X) - U_1(floor(X/3)) - U_1(floor(X/4)) + U_1(floor(X/12)).
A6. Independent check of a6: multiplicative local-table sieve versus literal Dirichlet convolution, all n <= 10^5.

## Part B — discriminating spectral test (the mechanism test of this cycle)

Hypothesis H-L (L-sensitivity, Coordinator/Analytic): the bucket aggregates that are not paired with the exact K-weights encode the zeros of L(s, chi_-3) as well as those of zeta; the K-paired object (M) and the residue class t == 1 (mod 3) aggregate (U_1) encode zeta only.
Rival H-0: the Hecke coefficient buckets behave like mu buckets (zeta zeros only); no L(s, chi_-3) frequency is present.

Observables, on u = log X with X = floor(e^u), u in [log 10^3, log 10^8], uniform grid of 40,000 points:
  f_C6(u) = (C6(X) - C6(floor(X/2))) / sqrt(X)   [equals the unweighted signed low return + B_X(r+1), by A4]
  f_M(u)  = (M(X) - M(floor(X/2))) / sqrt(X)
  f_Uj(u) = (U_j(X) - U_j(floor(X/2))) / sqrt(X), j = 0, 1, 2.
Spectrum S_f(gamma) = | sum_u f(u) w(u) e^(-i gamma u) | with a Hann window w over the full u-range, gamma in [4, 30] step 0.01.
Reference frequencies: gamma_L1 = 8.0397 (first zero of L(s,chi_-3), computed with mpmath), gamma_Z1 = 14.1347 (first zeta zero).

Decision rule (fixed now):
  B1 (H-L supported for C6): S_C6 has a local maximum within 8.04 +- 0.5 whose height is >= 0.5 * max_(gamma in [5,30]) S_C6.
  B2 (zeta-only control for M): S_M(peak within 8.04 +- 0.5) <= 0.25 * S_M(peak within 14.13 +- 0.5).
  B3 (U_1 is L-blind): same ratio criterion as B2 for f_U1.
  B4 (U_0, U_2 are L-sensitive): S_Uj has a local maximum within 8.04 +- 0.5 of height >= 0.25 * its max on [5,30], j = 0 and 2.
  H-L is SUPPORTED if B1-B4 all hold on the full range AND B1, B2 hold separately on both halves u in [log 10^3, log 10^5.5] and [log 10^5.5, log 10^8] (held-out stability). H-0 is supported if B1 fails on the full range. Mixed outcomes are reported as such.

## Part C — matched-core mode (Owner hypothesis)

Hypothesis H-MC: S_q(R) := sum_(q<=R prime) M(q-1) (= -PositiveSmooth_R, exact on main) carries the zeta-zero mode of size ~ R^(3/2)/log R predicted by
  S_q(R) ~ [ -R + sum_rho R^(rho+1)/(rho(rho+1) zeta'(rho)) ] / log R   (first 50 zero pairs),
so that the matched premise ||Matched_R|| <= 3 R sqrt(K) of SquareRootLowPrimeSmoothTransportRecoupling cannot hold with bounded K for large R.
Observable: S_q(R) exactly for all R <= 10^8; correlation of S_q(R) log R / R^(3/2) with the zero prediction over R in [10^6, 10^8] (held out: the prediction uses only zeta zeros, no fitting). Decision: H-MC SUPPORTED if Pearson correlation >= 0.9 on [10^6, 10^8] and max |S_q(R)| / (R/log R) grows by a factor >= 3 between 10^6 and 10^8; REFUTED if the correlation < 0.5.
Also record, for R <= 10^4 (exactly computable), Matched_R = M(R^2-1) + S_q(R) and the least admissible integer K with ||Matched_R|| <= 3 R sqrt(K).

Numerical agreement is evidence about finite arithmetic only, never proof.
