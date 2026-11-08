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


## 7. Contradiction test against the proved 7/8 baseline (2026-11-08)

**Question:** Does M(x)=O_epsilon(x^(7/8+epsilon)) force primes to be
spatially uniform in every square block, or prevent Li-fan escapes?

**Answer:** No. It does impose a weaker, mathematically valid
non-persistence condition on the TOTAL signed prime-count backlog. This
distinction is now formalized in
research/SQUARE_ROOT_PRIME_PHASE_RUN_CONTRADICTION_20261108.lean.

Define actual signed prime-count error e_R=P_R-F_R and integer endpoint
backlog D_R=pi(R^2)-floor Li_2(R^2). The existing floor-Li recurrence and
the new Lean theorem give, on ALL finite runs A<=B,

    sum_{A<=R<B} e_R = D_B - D_A.                    (7.1)

For a uniform per-block deficit e_R<=-delta across B-A consecutive
actual square blocks, exact signed summation yields

    (B-A)*delta <= |D_A|+|D_B|.                     (7.2)

The analogous theorem holds for surplus e_R>=delta.
If the block deficit would demand more than the two actual endpoint
budgets, the Lean theorem
squarePhaseNoDeficitRun_exceeding_endpointBudget proves False.
The premises about a uniform per-block sign and about both endpoint
bounds are EXPLICIT, and neither follows from a local phase histogram.

Classical explicit-formula consequence, NOT yet a new Lean-certified
Mertens-to-PNT transfer: a zero-free half-plane Re(s)>theta, as supplied
by the actual Mertens 7/8 bound, gives for all epsilon>0
    pi(x)-Li_2(x)=O_epsilon(x^(theta+epsilon))
at the cost of standard analytic explicit-formula estimates.
At square endpoints, theta=7/8 corresponds to
    |D_R| <= C_epsilon R^(7/4+epsilon).

Take A=R large and B=R+h<=2R. If every block in this run exhibits a
relative fixed-sign excess or deficit at least c*R/log R, then (7.2)
requires, up to constants and an arbitrarily small exponent loss,

    h <= C_{c,epsilon} R^(3/4+epsilon) log R.        (7.3)

So a contradiction is available only for a run substantially
LONGER than R^(3/4) log R under these hypotheses. In contrast, starting
near the fan center, escaping a K R log R wall needs only roughly
    h ~ (K/c)*(log R)^2
blocks with the same relative count bias. The first is polynomial and
the second polylogarithmic. Thus the current 7/8 bound is **much too weak
to exclude the hypothetical first escape**.

Even RH's classical pi(x)=Li(x)+O(sqrt(x) log x) is not strong enough by
itself to force the correct prime count in *each individual* square
block: the error O(R log R) at the two endpoints exceeds the expected
block population ~ R/log R by two logarithms. The prime-between-squares
problem remains open. An even stronger spatial claim that primes split
50/50 inside every block is not the content of global equidistribution.

**Algebraic independence of the two diagnostics:** For an abstract
population with P=F>0 and L=P, the total prime-count excess P-F is
identically zero but the spatial half-phase bias L-P/2=P/2>0. Conversely,
L=P/2 is perfect spatial balance while P-F can be arbitrarily large.
Lean proves both finite real-population witnesses. They are mathematical
counterexamples to an *unsupported algebraic implication*, not alternative
actual primes, so they do not assert anything about multiplicative Euler
constraints. To prove stronger implications for genuine primes one needs
an additional genuinely arithmetic prime/composite or signed multi-window
restriction, not a re-labelling of the count/phase identities.

The repo's existing Harman/Vinogradov prime-sqrt equidistribution theorem
is still an EXTERNAL analytic statement, represented as the explicit
SquareRootPrimePhaseEquidistributionStatement hypothesis.
VF_MID_HARMAN_FOUR_FIFTHS.lean records a quantitative conditional
4/5 discrepancy consumer, but X^(4/5+epsilon) corresponds to
R^(8/5+2epsilon), also far larger than the fan width R log R at X=R^2.
The classical global phase theorem is about summing across many blocks,
not per-block sharp density and not the weighted Möbius covariance.

**Possible native stronger route:** Prove a new *actual-prime*
cofactor-conditioned signed inequality that turns persistent spatial
imbalance into a nonzero count backlog or controls the full joint
signed Möbius energy. That step is exactly the mathematical content
currently missing; (7.1) and (7.2) alone cannot provide it.
