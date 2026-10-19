# Moving Euler square-root covariance census: 317, 1027 and later prime-square handoffs

**Date:** 2026-10-19. **Status:** EXACT FINITE NUMERICAL EVIDENCE, not an unconditional asymptotic covariance estimate. Independent C++ linear Möbius sieve and Python prime/square sieve agree on the selected checkpoints and both complete target shells. The run covers EVERY integer from 1 through 13,890,530 = 3727²+1. This note changes no Lean proof assumptions.

## 1. Strict moving low/high partition

At each integer X>=1, call n<=X LOW if every prime factor p|n satisfies p²<X, and HIGH otherwise. The unit 1 is LOW. The strict boundary prime p remains HIGH at X=p² and becomes LOW at X=p²+1. Its Möbius sign is unchanged.

Write L(X),H(X) for the corresponding **signed** real Möbius sums, K_L,K_H for their actual squarefree diagonal contributions and C_LL,C_HH,C_LH for the real signed pair sums. All integer sites appear exactly once, including zero Möbius sites.

\[
M=L+H,\qquad K=K_L+K_H,
\quad C_{LL}=(L^2-K_L)/2,\quad
C_{HH}=(H^2-K_H)/2,\quad C_{LH}=LH,
\]
\[
\boxed{C_{LL}+C_{HH}+C_{LH}=(M^2-K)/2=C_{\mathrm{total}}.}
\]

Verified by exact 64-bit signed arithmetic **after each of the 13,890,530 integer admissions**.

## 2. Two distinct chronological mechanisms

**New integer enters at X:** put a=mu(X), with L,H the masses after any square-boundary handoff but before this new site. If LOW, delta C_LL=aL and delta C_LH=aH; if HIGH, delta C_HH=aH and delta C_LH=aL. Consequently delta total=aM(X-1). Every prime X=p enters HIGH with a=-1, hence

\[
\boxed{\Delta C_{\rm prime}(p)=-M(p-1).}
\]

**Prime-square handoff at X=p²+1:** all already-present sites pc with 1<=c<p move from HIGH to LOW, with exact transfer
\[
t=\sum_{c<p}\mu(pc)=-M(p-1),\qquad
d=\sum_{c<p}\mu(pc)^2=K(p-1).
\]
For pre-handoff signed masses L,H,
\[
\Delta C_{LL}=Lt+(t^2-d)/2,\quad
\Delta C_{HH}=-Ht+(t^2+d)/2,\quad
\Delta C_{LH}=t(H-L)-t^2.
\]
The sum of these three changes is **exactly zero**. The integer X=p²+1 is counted separately. Every one of the 520 prime-square handoffs in the scan was also checked by literally summing the p*c Möbius children.

## 3. Census snapshot

| X | M | K | L | H | C_LL | C_HH | C_LH | C_total |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 317 | -4 | 194 | -3 | -1 | -20 | -72 | +3 | -89 |
| 1027 | -3 | 625 | -12 | +9 | -6 | -194 | -108 | -308 |
| 100488=317²-1 | -28 | 61094 | -918 | +890 | +413875 | +372990 | -817020 | -30155 |
| 1054728=1027²-1 | +367 | 641207 | -6602 | +6969 | +21712299 | +24043780 | -46009338 | -253259 |
| 13890530=3727²+1 | -43 | 8444439 | -62449 | +62406 | +1948837790 | +1944133209 | -3897192294 | -4221295 |

Thus at X=13,890,530:

\[
1948837790+1944133209-3897192294=-4221295.
\]

This is a large, measured **cross-population compensation**, not a proof of its uniform continuation.

## 4. Prime-square handoff effects (computed before admitting the new integer)

| p | X=p²+1 | t | d | ΔC_LL | ΔC_HH | ΔC_LH | ΔC_total |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 317 | 100490 | +3 | 193 | -2846 | -2569 | +5415 | **0** |
| 439 | 192722 | +6 | 268 | -9386 | -9484 | +18870 | **0** |
| 3727 | 13890530 | +7 | 2265 | -438293 | -435734 | +874027 | **0** |

1027=13*79 is not a prime; therefore no PRIME handoff occurs at 1027²+1.

## 5. Distinguish the genuine prime arrivals from the x/log x model

Let b(X)=X/log X for X>=2 and b(0)=b(1)=0, with finite difference Δb(n)=b(n)-b(n-1). First-order PNT supplies π(X)~b(X), **not** a pointwise equality of individual prime indicators with Δb(n).

The exact signed prime-only covariance contribution is
\[
C_{\rm prime}(X)=-\sum_{2\le n\le X}\mathbf1_{\rm prime}(n)M(n-1).
\]
Decompose exactly as
\[
C_{\rm prime}=C_{\rm model}+C_{\rm residual},\quad
C_{\rm model}=-\sum_{2\le n\le X}\Delta b(n)M(n-1),
\]
\[
C_{\rm residual}=-\sum_{2\le n\le X}
(\mathbf1_{\rm prime}(n)-\Delta b(n))M(n-1).
\]
Then add the true nonprime signed covariance source; neither sector may be dropped.

At the terminal X=13,890,530: π(X)=903470, X/log X=844577.629956, so prime-count discrepancy is +58892.370044. Actual prime-arrival covariance is +46720805; x/log x weighted covariance is +44401852.875253; weighted **prime-model residual is +2318952.124747**. Nonprime signed covariance is -50942100; the complete total is -4221295. Therefore first-order PNT **does not itself provide** the missing uniform signed weighted-residual inequality.

## 6. Original square shells and dyadic bands

Exact shells: R=317 has UPM=199, LPM=188, S=+11, K=387, C=-133, S²=121; R=1027 has UPM=616, LPM=636, S=-20, K=1252, C=-426, S²=400.

Exact dyadic H=256: energy 110216, diagonal 119516, within-shell covariance -4650, signed block sum +10, cross-shell covariance -55058. H=1024: energy 1723387, diagonal 1912373, within-shell covariance -94493, block sum -29, cross-shell covariance -861273. These are different carriers from moving global low/high pair masses.

## 7. Finite envelope validation and remaining theorem

The maximum |M(X)|/X^(7/8) over **all X>=317 through 13,890,530** is 0.043515026165 at X=443; over X>=1027 it is 0.0324919784242 at X=1109; over X>=100489 it is 0.00476139204361 at X=119545. The stronger empirical |M(X)|/sqrt X envelope also holds in the same range, with its maximum over X>=100489 being 0.437776205949 at X=300551.

This is finite verification only: neither an all-X 7/8 proof nor RH. The novel arithmetic theorem still required is a quantitative **joint bound** for the newly arriving composite/prime weighted residual and the moving low/high interaction; the exact handoff is a conservation law, not a contraction. In the historical square-wheel source the prime-only c=1 channel is not omitted.

**Reproduction:** The companion C++/CSV/plots are produced as downloadable conversation artifacts (run command: g++ -O3 -std=c++17 -Wall -Wextra -Werror euler_moving_covariance.cpp -o euler_moving_covariance; ./euler_moving_covariance 13890530 ./euler_covariance). The script computes and checks exact conservation at each X, all p²+1 handoffs, real prime-versus-composite covariance contributions, and x/log x model residuals. Commit reproducible sources separately if they are to become CI authority.
