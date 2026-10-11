# Cofactor-conditioned prime availability and shared ancestry: exact finite-C experiment

**Date:** 2026-10-11  
**Status:** Complete, integer-exact finite computation for roots `2 <= R <= 6000` (all 5,999 square endpoints, up to `X = 35,999,999`), plus six detailed smooth/high ancestry censuses. **No all-root finite-C, finite-A, or RH bound is established.**

## 1. What was tested

The hypothesis was that an apparent “confounder” missing from aggregated Euler, stochastic-dominance, and prime-wave comparisons is the **joint information** `(cofactor parity, factor depth, greatest prime owner, shared gcd ancestry, and actual prime-extension availability)`.

For each integer `R >= 2`, set

\[
X_R=R^2-1,\quad K_R=\max_{0\le y<R}\frac{(M(y)-1)^2}{y+1},\quad Q_R=2M(R-1)-M(X_R).
\]

The physical extension exposure of a historical cofactor `c < R` is

\[
\boxed{N_R(c)=\pi(\lfloor X_R/c\rfloor)-\pi(R-1).}
\]

Every high-prime squarefree product is uniquely `pc` with `p >= R`, `c < R`, and `mu(pc) = -mu(c)`. Consequently the high-prime signed population `H_R` and root-smooth signed population `S_R` obey

\[
\boxed{H_R=-\sum_{c<R}\mu(c)N_R(c),\qquad M(X_R)=S_R+H_R.} \tag{1}
\]

The program constructs the genuine Mobius function and prime-count prefix independently, calculates **every** `N_R(c)` for `2 <= R <= 6000`, reconstructs every `M(X_R)`, `Q_R`, `K_R`, and partitions the physical signed populations by parity, omega depth and owner. On six selected roots it independently enumerates every squarefree smooth integer to check the high-prime reconstruction.

## 2. Exact answer: availability substantially changes the apparent parity balance

The difference between unweighted signed parity and availability-weighted signed parity is real and sometimes reverses sign:

| R | high-prime μ(c)=+ exposure | high-prime μ(c)=− exposure | unweighted parity mean | exposure-weighted parity mean | high-prime mass H_R | smooth mass S_R | M(X_R) |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 56 | 714 | 761 | -0.05882 | -0.03186 | +47 | -41 | +6 |
| 317 | 22,615 | 23,505 | -0.01554 | -0.01930 | +890 | -918 | -28 |
| 1,000 | 224,083 | 230,650 | +0.00329 | -0.01444 | +6,567 | -6,355 | +212 |
| 2,000 | 892,969 | 914,576 | +0.00412 | -0.01195 | +21,607 | -21,415 | +192 |
| 5,561 | 6,872,704 | 6,997,077 | +0.00148 | -0.00897 | +124,373 | -126,917 | -2,544 |
| 6,000 | 7,996,421 | 8,141,975 | 0.00000 | -0.00902 | +145,554 | -143,298 | +2,256 |

For `R=1000`, simply averaging the cofactor parity would predict a *positive* signed μ-weighted exposure of about `+1496`, whereas the actual signed exposure is `-6567`. This sign reversal is attributable to the dependence of `N_R(c)` on `c`: the parent sign and its number of available high-prime children **are not independent**.

Among all 5,970 roots `31 <= R <= 6000`, the unweighted and extension-weighted parity means have strictly opposite signs at **2,274** roots (zeros not counted).

However, the conditional empirical CDFs of `N_R(c)` among `mu(c)=+1` and `mu(c)=-1` cross for **every root `31 <= R <= 6000`**. Thus neither parity stratum has first-order stochastic dominance in prime-extension availability. For `R=317`, the normalized CDF difference spans `[-0.063265,+0.073899]`. A one-sided CDF argument alone does not supply finite C.

Plot: `weighted_unweighted_parity.png`, `parity_conditional_cdf_crossing.png`.

## 3. Exact same-prime overlap Gram, conditioned on shared gcd

Let `A_c={p prime: R<=p, pc<=X_R}`. These sets are **nested**, not independent: `A_d` is a subset of `A_c` for `c<d`, and

\[
\boxed{\#(A_c\cap A_d)=N_R(\max(c,d)).}\tag{2}
\]

Therefore the genuinely coupled same-high-prime owner energy, with the `c=1` seed removed, is an exact positive-semidefinite Gram:

\[
\boxed{G_R=\sum_{c,d=2}^{R-1}\mu(c)\mu(d)N_R(\max(c,d))
=\sum_{\substack{R\le p\le X_R/2\\p\ \mathrm{prime}}}
       (M(\lfloor X_R/p\rfloor)-1)^2.}\tag{3}
\]

It decomposes into `D_R` (same-cofactor diagonal) and the two signed off-diagonal classes

\[
\begin{aligned}
D_R&=\sum_{2\le c<R}\mu(c)^2N_R(c),\\
\Gamma_R^{\rm coprime}&=2\sum_{2\le c<d<R,\ (c,d)=1}\mu(c)\mu(d)N_R(d),\\
\Gamma_R^{\rm shared}&=2\sum_{2\le c<d<R,\ (c,d)>1}\mu(c)\mu(d)N_R(d),\\
G_R&=D_R+\Gamma_R^{\rm coprime}+\Gamma_R^{\rm shared}\ge0.
\end{aligned}\tag{4}
\]

The full-root census uses an independent `O(R)` per-root gcd-stratified formula (after a one-time gcd-prefix setup), checked against **explicit pair enumeration** at the six detailed roots. For the selected roots:

| R | Shared-gcd signed cross | Coprime signed cross | Complete G_R | G_R / (R² K_R) |
|---:|---:|---:|---:|---:|
| 56 | -314 | +442 | 1,174 | 0.24958 |
| 317 | -8,362 | -1,950 | 26,242 | 0.17410 |
| 1,000 | -207,442 | +47,138 | 216,099 | 0.14407 |
| 2,000 | -1,156,766 | +414,916 | 782,852 | 0.13048 |
| 5,561 | -11,349,450 | +4,692,682 | 5,302,075 | 0.11430 |
| 6,000 | -13,352,348 | +5,545,316 | 6,127,885 | 0.11348 |

**Key empirical finding:** `Gamma_shared(R)<0` at **all 5,991 consecutive roots 10..6000**; it is never positive for any root 2..6000. Conversely `Gamma_coprime(R)>0` for every root 494..6000. These are **finite verified signs**, not universal theorems. Many individual `d`-indexed shared-gcd summands are positive (`d=21` is the earliest example), so the sign is not immediate termwise.

The conditional sign imbalance is numerically small but acts on enormous weighted pair populations. At `R=6000`, shared-gcd positive pair weight is `922,056,168`, negative pair weight `935,408,516`; the resulting **0.7188% excess of opposite-parity pairs** generates `-13,352,348` in the signed Gram. Coprime pair weight has a **0.0866% excess of same-parity pairs** and contributes `+5,545,316`. This is deterministic conditional parity superiority, on a fixed finite incidence population, not probabilistic independence.

The complete same-prime Gram **already has an independent scale bound** via historical `K_R`:

\[
G_R\le K_R\sum_{p\ \mathrm{active}}(\lfloor X_R/p\rfloor+1)
\le (\Lambda+\tfrac12)R^2K_R,
\quad \Lambda=\sup_{R\ge2}\sum_{R\le p<R^2}1/p<\infty.
\]

A sharper explicit prime-reciprocal bound is discussed in the companion Euler note. This Gram estimate is unconditional, but does not control the coherent **different-prime-owner** cross terms: at `R=6000`, `colsum²-G_R` is **5,517,949,907,204** versus same-prime `G_R=6,127,885`. Thus the proven same-prime bound alone does not close `Q_R`.

Plot: `conditional_gcd_overlap.png`.

## 4. The deeper test: smooth/high-prime cross-energy, conditioned on gcd ancestry

Let `T_R(c)=sum_{n<=X_R, P+(n)<R, gcd(n,c)=1} mu(n)` be the signed root-smooth mass coprime to cofactor `c` (`P+(1)=1`). Using Euler's exact coprime indicator,

\[
\boxed{T_R(c)=\sum_{d\mid c}\mu(d)
\sum_{\substack{n\le X_R,\ P^+(n)<R\\d\mid n}}\mu(n).}\tag{5}
\]

Since for a high-prime extension `pc` and root-smooth integer `n` we have `gcd(pc,n)=gcd(c,n)`, their **complete physical signed cross-energy** separates exactly into

\[
\boxed{S_RH_R=C_R^{\rm smooth/high,coprime}+C_R^{\rm smooth/high,shared},}\tag{6}
\]

where

\[
C_R^{\rm smooth/high,coprime}
=-\sum_{c<R}\mu(c)N_R(c)T_R(c),\qquad
C_R^{\rm smooth/high,shared}=S_RH_R-C_R^{\rm smooth/high,coprime}.
\]

**The sign of the dominant conditional interaction changes with scale**:

| R | Total S_R H_R | Coprime cross | Shared-gcd cross |
|---:|---:|---:|---:|
| 56 | -1,927 | -2,604 | +677 |
| 317 | -817,020 | -1,014,741 | +197,721 |
| 1,000 | -41,733,285 | +9,563,364 | -51,296,649 |
| 2,000 | -462,713,905 | +233,774,957 | -696,488,862 |
| 5,561 | -15,785,048,041 | +9,001,960,873 | -24,787,008,914 |
| 6,000 | -20,857,597,092 | +11,241,841,764 | -32,099,438,856 |

At `R=317`, coprime pairs supply the **restoring negative interaction** while shared-ancestry pairs partially undo it. At `R=6000`, the signs reverse: shared-ancestry pairs supply *154%* of the required negative interaction, while coprime pairs reinforce positively and offset the excess. The two classes are not separately stable signs.

This is a stronger, directly physical demonstration of the missing conditional dependence than the cofactor-only Gram. The identity (5) was cross-checked by **brute-force enumeration of every smooth/high squarefree pair at R=56**. The larger cases use exact divisor arithmetic, not pair sampling.

Plot: `smooth_high_conditional_reversal.png`.

## 5. Greatest-prime ownership and the residual across owners

For a fixed `R`, partition each smooth squarefree `n` by its greatest prime `P+(n)<R` (with `P+(1)=1`) and each high-prime occurrence `pc` by its cofactor's greatest prime `P+(c)<R`. Within each owner `q`, add smooth and high signed masses *before* taking absolute values. This retains actual occurrence multiplicities and uses no random model.

| R | Sum of separate owner absolute masses | Sum of owner-joined absolute masses | Actual |M(X_R)| | Fraction of remaining owner-joined absolute mass canceled across owners |
|---:|---:|---:|---:|---:|
| 56 | 954 | 866 | 6 | 99.31% |
| 317 | 21,312 | 19,498 | 28 | 99.86% |
| 1,000 | 173,998 | 160,136 | 212 | 99.87% |
| 2,000 | 627,846 | 581,276 | 192 | 99.97% |
| 5,561 | 4,231,152 | 3,942,694 | 2,544 | 99.94% |
| 6,000 | 4,879,242 | 4,547,574 | 2,256 | 99.95% |

Joining by largest cofactor prime removes only about **7%–9%** of unsigned owner mass directly. Almost all the final cancellation is **across different owner families**. This partition does not by itself yield a finite-C norm estimate.

## 6. Direct connection to finite C and the remaining theorem

At `R=317` we reconstruct exactly

\[
M(317^2-1)=S_R+H_R=-918+890=-28,
\qquad Q_R=2M(316)-M(100488)=22.
\]

At `R=6000`,

\[
M(35,999,999)=-143,298+145,554=2,256,
\qquad Q_{6000}=-2,256,
\qquad K_{6000}=1.5,
\qquad C_{6000}\approx0.307003.
\]

The objective is unchanged:

\[
\boxed{|2M(R-1)-S_R-H_R|\le C R\sqrt{K_R}\quad\text{for one finite }C,\ \forall R.}\tag{7}
\]

These experiments **support studying shared ancestry as a conditional variable**, but do not establish a domination principle at the necessary scale. Indeed the observed switching of signs in the smooth/high split directly rules out one-size-fits-all assertions such as “shared primes always restore” or “coprime pairs are independent.” The object needed is an independently proved quantitative **joint** smooth/high incidence (or cross-owner boundary) inequality, retaining both conditional sectors with their exact opposite signs. Rephrasing their sum as `(S_R+H_R)^2` would be circular.

### Candidate tractable subtheorem and explicit falsification gate

Study whether `Gamma_shared(R) <= 0` admits a genuinely arithmetic proof using the **actual** monotonically nested prime-arrival weights `N_R(d)` and the signed, shared-gcd cofactor census; this is empirically true through root 6000. It is **not** true for arbitrary decreasing nonnegative replacement weights: using `w_d=1_{d<=26}` gives the unweighted shared-gcd partial sum `2`, which is positive. Any proof must use additional restrictions specific to `N_R(d)`. Even this sign theorem would only control a **same-prime** Gram subterm and not finite C.

A finite-C proof must bound the **combined** smooth/high cross-owner contribution and cannot separately norm the huge constituent classes.

## 7. Reproducibility and checks

~~~bash
g++ -O3 -std=c++17 -Wall -Wextra cofactor_conditioning_census.cpp -o census
./census 6000
python3 plot_results.py
python3 analyze_results.py
~~~

- `root_features.csv`: **all 5,999 roots**, full cofactor-weighted parity, exact historical envelope, conditional CDF crossings, and all-root gcd-stratified same-prime Gram.
- `selected_owner_groups.csv`, `selected_depth.csv`, `selected_dyadic.csv`: complete physical occurrence-preserving decompositions for roots 56, 317, 1000, 2000, 5561, 6000.
- `selected_gcd_overlap.csv`: shared and coprime same-prime signed and unsigned pair masses, verified also by explicit pair enumeration.
- `selected_smooth_high_gcd.csv`: actual smooth–high cross-sector gcd classification, with independent brute-force check at R=56.
- `selected_prime_updates.csv`: independent exact prime-by-prime feedback reconstruction and diagonal check.
- `*.png`: four reproducible diagnostic figures.

The independently generated `M(X_R)`, `Q_R`, `K_R`, `C_R`, `A_R` match **all 5,999 roots** of the pre-existing `prime_phase_experiment/actual_root_scan.csv`: the integer fields agree exactly, and floating ratios to rounding precision. All exact internal partition identities assert equality and the program exits nonzero on any mismatch. Computations use exact integer arithmetic for every sign, count, and cross-product (floating arithmetic only for displayed normalized ratios).

**Overall conclusion:** conditioning matters and the shared-factor response is genuinely different from the coprime response. The evidence reveals an exact and potentially useful second-moment geometry, not an all-scale first-order dominance theorem or a proof of finite C/A.