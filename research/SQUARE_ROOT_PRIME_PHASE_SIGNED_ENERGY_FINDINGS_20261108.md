# Actual primes' square-root phases versus original signed square-block energy

**2026-11-08 research + formalization audit.** Tested genuine primes and integer
Mobius values for all 9,900 square blocks 100<=R<10000, n<10^8. Mathematical
status: finite data, exact kernel-checkable identities, and separately OPEN
signed-correlation estimates. Nothing here proves RH, Mertens exponent 3/4,
uniform fan containment, or asymptotic prime phase decorrelation.

## 1. Already proved elsewhere: do NOT reprove

* research/VF_MID_HARMAN_HALF_PHASE_BRIDGE.lean:
  {sqrt p}<1/2 iff p<=R^2+R within the R-th square block, and
  G_(R+1)-G_R=U_R where U_R=L_R-P_R/2.
* research/VF_MID_GLOBAL_PHASE_UNIFORMITY_BRIDGE.lean:
  sum_{R=A}^{B-1} U_R = G_B-G_A (actual primes).
* research/VF_MID_HARMAN_FOUR_FIFTHS.lean:
  classical published 4/5+epsilon prime sqrt-phase discrepancy interface,
  plus kernel-checked *conditional* exponent transfer. The external analytic
  theorem is not reproved inside Lean and this is not local KS control.
* research/VF_MID_FLOOR_LI_DISCRETE_BACKLOG.lean:
  D_(R+1)-D_R=P_R-F_R for D_R=pi(R^2)-floor Li_2(R^2).
* research/VF_919_MARKED_FIRST_OWNER_SHELL_20261019.lean:
  original sharp shell exactly equals actual Mobius on [R^2,(R+1)^2).
* research/OAI_PAIRED_SHARP_EULER_SQUARE_LOCALIZATION_20261028.lean:
  actual sharp ideal-norm source equals actual three-moving-population Euler
  source, including all smooth/transport and quadratic mixed terms.
* research/EULER_SQUARE_BLOCK_DIVISOR_SURROGATE_20261028.lean:
  every fixed-divisor physical sampling error telescopes exactly, but joint
  signed second moments across growing divisors are NOT supplied.

## 2. New source-faithful Lean normal forms

File: research/SQUARE_ROOT_PRIME_PHASE_SIGNED_ENERGY_20261108.lean

Let P_R=pi((R+1)^2)-pi(R^2), F_R=floor Li_2((R+1)^2)-
floor Li_2(R^2), L_R=# primes in block with {sqrt p}<1/2 and
U_R=L_R-P_R/2.

The new exact two-channel identity is

  L_R - F_R/2 = U_R + (P_R-F_R)/2.                  (A)

The original fan drift P_R-F_R is independent as an algebraic coordinate
from the spatial imbalance U_R. The module formalizes a counterexample
on abstract real populations with exactly zero spatial imbalance but
arbitrarily large total-count excess. This example is explicitly NOT a
synthetic genuine-prime distribution.

For any integer weights f, let
  S_(R,k)=sum_{0<=i<k} f(R^2+i),
  D_(R,k)=sum_{0<=i<k} f(R^2+i)^2,
  C_(R,k)=sum_{0<=i<k} f(R^2+i)*sum_{0<=j<i} f(R^2+j).

It proves
  S_(R,k)^2 = D_(R,k) + 2 C_(R,k)                 (B)
with the genuine original signs, not absolute-value norms.

Specializing f(n)=mu(n), k=2R+1, and summing H<=R<2H yields

  E_sharp(H) = D_squarefree(H) + 2 C_signed(H), (C)
  0<=D_squarefree(H)<=3H^2.                    (D)

This equality is on exactly the EXISTING original OAI and three-population
Euler sharp shell, not a new surrogate.

Therefore the separate OPEN one-sided estimate

  exists C, for all H>=4: C_signed(H) <= C H^2  (E)

would give E_sharp(H)<= (3+2C)H^2 and hence M(x)=O(x^(3/4+eps))
by the already-identified dyadic square-shell/Cauchy route. The weaker
C_signed(H)<=C_eps H^(2+eps) is enough with the corresponding loss.

NO inequality (E) is supplied here. Source equality alone cannot prove it.

## 3. Reproducible actual-prime and actual-Mobius finite census

Full experiment run used:
  g++ -O3 -std=c++17 scripts/square_root_prime_phase_mobius_census.cpp -o /tmp/phase_mu
  /tmp/phase_mu 10000 100 > /tmp/phase_mu.csv

This integer-only sieve reproduces all prime and squarefree coefficients,
the exact high-prime cofactor-window debt

  A_R = sum_{1<=c<=R} mu(c)[pi(floor(((R+1)^2-1)/c))-
                            pi(floor(R^2/c))],

and the complementary smooth source S_R=Delta_R+A_R. R^2 has mu=0 for
R>=2, and every high-prime owner q>R has cofactor c<=R.

Finite pooled phase results: 5,760,226 primes; mean {sqrt(p)}=0.499984;
conditioned Li ten-bin chi-square=2.972; only 2/9,500 per-block iid-KS
nominal 5% flags. The iid p-values are DESCRIPTIVE and are strongly
miscalibrated for deterministic sieved prime locations.

Matched stochastic controls at 1,500 roots:
  actual mean KS D=0.033575,
  uniform points mean D=0.046711,
  random odd positions mean D=0.043127,
  random mod-30030 wheel positions mean D=0.038328.
These controls use one independent draw per root; they are not a proof.

New *deterministic* wheel-relative normalization at all 9,000 R>=1000:
  wheel Q = 30030 = 2*3*5*7*11*13, phi(Q)=5760;
  actual-prime conditional half-phase z standard deviation = 0.8131,
  after subtracting E[L_R | actual P_R, uniform subset of wheel survivors]
  and dividing by exact finite-population hypergeometric standard deviation.
  Count residual (P_R-Li expected)/sqrt(Li) SD=0.611,
  after normalizing Li by actual wheel-candidate density SD=0.611;
  lag-one count-residual correlation ~ -0.101.
  The simple 30030-wheel does NOT explain all count suppression; one
  cannot conclude the residuals are independent or uniformly bounded.

## 4. Exact signed energy: key empirical observation

H | E_sharp(H) | squarefree diagonal D | 2 C_signed | E/H^2 | E/D
---|-----------:|---------------------:|-----------:|------:|----:
128 | 37,622 | 29,882 | +7,740 | 2.2963 | 1.2590
256 | 110,216 | 119,516 | -9,300 | 1.6818 | 0.9222
512 | 486,935 | 478,101 | +8,834 | 1.8575 | 1.0185
1024 | 1,723,387 | 1,912,373 | -188,986 | 1.6435 | 0.9012
2048 | 7,380,415 | 7,649,467 | -269,052 | 1.7596 | 0.9648
4096 | 30,291,950 | 30,598,026 | -306,076 | 1.8055 | 0.9900

The squarefree diagonal asymptotic 18/pi^2~1.82378 times H^2 is
classically available; in this Lean file only the unconditional
diagonal<=3H^2 elementary estimate is claimed.

C_signed changes sign (H=128,512 positive; H=256,1024 negative).
DO NOT assume it is everywhere <=0, and DO NOT demand an unnecessarily
strong absolute-value bound. The numerical data suggest the ONE-SIDED
full signed upper bound (E) at the scale needed for Mertens 3/4.

Across R>=1000, the ordinary Pearson correlation of actual block
Delta_R with count excess P_R-Li_R is -0.5115, while its correlation
with spatial half-phase U_R is +0.00281 and with a Q=30030-corrected
half-phase residual is +0.00295. It is NOT evidence that phase
uniformity implies Mobius cancellation. The actual prime singleton
term in Delta_R causes a structural negative contribution; a
correlation or regression slope is not a causal prime-availability theorem.

A positive magnitude effect is visible: the highest quintile of
|count residual| has mean Delta_R^2 ~10,803 versus ~5,063 in the
lowest quintile. This strengthens the motivation to study
cofactor-conditioned COUNT fluctuations and their signed joint Gram.

## 5. Next theorem worth attacking

Prove, for the actual original coefficients and all H>=4,

  sum_{H<=R<2H} sum_{R^2<=j<i<(R+1)^2} mu(i)*mu(j)
      <= C_eps H^(2+eps),                         (T)

uniformly with C_eps fixed BEFORE H. Use the repo's existing exact
least-prime-owner compensator, cofactor-conditioned prime windows,
complete LOW/MIDDLE/TOP six-term signed Gram, and actual floor-Li
prime-event displacement. Keep smooth minus prime transport, the
singles, q^2 daughters, conductor corrections, and signed cross terms.

Independently, a Li fan restriction needs the complete cumulated
count excess (sum P_R-F_R), not the spatial U_R. A negative lag-one
Pearson correlation and uniform phase distribution do not bound the
WHOLE signed lag kernel. Prove a uniform all-lag prime-incidence
estimate or source-faithful non-escape capacity before invoking the
one-sided RH sufficiency theorem.

## 6. Verification, limits, and scientific integrity

CI compiles new Lean declarations warning-fatal, prints their exact
types and axiom dependencies, and runs an independent small-range
integer Möbius/prime census. This PR introduces no new axiom, sorry,
extra analytic hypothesis, Mathlib pin change, private wheel model
as actual primes, finite A, or claimed new exponent.

The full 100-million finite raw CSV and stochastic controls are
available as a downloadable research artifact from the originating
experiment, but not committed to this repository due to size. The
small C++ source in scripts/ reconstructs the exact integer results.
