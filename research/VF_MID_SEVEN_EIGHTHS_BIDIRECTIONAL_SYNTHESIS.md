# Bidirectional synthesis of the OpenAI 7/8 zero-free result and genuine RH_Lean prime owners

**Status:** Exact arithmetic/Mellin mathematics and warning-fatal Lean finite Abel lemmas; conditional analytic bounds, NOT RH.

## 1. Analytic information INTO genuine weighted owner cells

Freeze a subdoubling run at A=2634, B=5267. Genuine late-owner
semiprime cells have n=pq, A<p<q, pq<B^2. Their q cutoff is
U_p=floor((B^2-1)/p). Use the *original* root-of-product physical
weight w_p(q) = vfMidBandMass(floor(sqrt(pq)))/floor(sqrt(pq)).
This weight changes at completed square boundaries; it is not
a constant reference-density proxy.

Write E(q)=pi(q)-Li_2(q), where Li_2 is RH_Lean's
integral from 2. The weighted arithmetic-minus-Li contribution
of this true p-column is

\[
T_p=\sum_{q=p+1}^{U_p}w_p(q)
\big[(\pi(q)-\pi(q-1))-(Li_2(q)-Li_2(q-1))\big].
\]

**Exact signed discrete Abel reassembly:**

\[
\boxed{T_p=w_p(U_p)E(U_p)-w_p(p)E(p)
 +\sum_{q=p}^{U_p-1}(w_p(q)-w_p(q+1))E(q).}\tag{S1}
\]

The Mathlib-only Lean theorem
vfSevenEighthsWeightedOwnerPrimeLiDifference_eq_abel proves S1,
and vfSevenEighthsOwnerPacket_abel sums it over the true owner
columns while preserving all weights.

For a single p-column, assuming its weights are nonnegative and
nonincreasing and |E(q)|<=M throughout, Lean also proves

\[
\boxed{|T_p|\le2w_p(p)M.}\tag{S2}
\]

Declarations:
vfSevenEighthsWeightedIncrement_abs_le_twice_initial and
vfSevenEighthsWeightedOwnerPrimeLiDifference_abs_le.

This is a rigorous way to INSERT a 7/8 prime-counting error
bound *at the projected q scale* into the original-weight
semiprime incidence. The exact Lean bridge is agnostic as to
how M is proved; OpenAI's zeta nonvanishing would supply
it ONLY after the still-missing explicit-formula transfer
for arbitrary q, not just square endpoints.

**Actual-prime census** (independent fast test
scripts/vf_919_prime_owner_abel_spectral_probe.py):

| Genuine 2634..5267 source | Value |
|---|---:|
| Genuine prime p-owner columns | 316 |
| Genuine distinct semiprime p*q cells | 125,272 |
| Actual original VF-weighted positive mass | +14,955.134569 |
| Weighted discrete Li-increment model | +15,091.428262 |
| Signed actual-prime minus Li-model residual | **-136.293692** |
| Sum of absolute individual column residuals | 140.783735 |
| Inter-p signed cancellation factor | **1.033x** |
| Negative-sign column errors | **293** |
| Positive-sign column errors | **23** |
| Sum of the elementary one-column Abel envelopes | 1,588.123003 |

Li-increments in the numerical test use composite Simpson
quadrature on integer unit intervals. The algebraic Abel
identity is exact for this discrete cumulative model,
and the quadrature error is negligible at the observed scales.

**Warning:** the 316 spectral owner-column errors are mostly
ONE-SIGNED. The impressive completed-square *wheel-phase*
cancellation (~2000x) did not propagate automatically to
the selected *analytic semiprime* packet (only 1.03x).
Thus the 7/8 estimate cannot be assumed to produce the
missing Sector Six cross-owner cancellation.

## 2. Genuine wheel/owner arithmetic INTO zeta's analytic coordinates

Fix y>=3 and the primorial Q_y. Put
R_y(n)=1_{gcd(n,Q_y)=1}. For Re(s)>1 the *actual*
incomplete-wheel survivor Dirichlet series has the
well-known exact Euler identity

\[
\boxed{Z_y(s)=\sum_{n\ge1}R_y(n)n^{-s}
=\zeta(s)\prod_{p\le y}(1-p^{-s}).}\tag{S3}
\]

For Re(s)>0, these finite Euler factors are nonzero.
Consequently, in Re(s)>7/8 the **zeros of Z_y and zeta
are exactly the same** (the common pole at s=1 aside).
This is a genuine TWO-WAY analytic alignment, but it
does not itself improve OpenAI's 7/8 line.

Differentiate logarithmically to expose the prime powers:

\[
\boxed{-Z_y'(s)/Z_y(s)
=-\zeta'(s)/\zeta(s)
-\sum_{p\le y}\frac{\log p}{p^s-1}
=\sum_{p>y}\sum_{k\ge1}(\log p)p^{-ks}.}\tag{S4}
\]

The **exact coefficient identity** is

\[
\boxed{R_y(n)\log n
=\sum_{dm=n}R_y(m)\,R_y(d)\,\Lambda(d).}\tag{S5}
\]

Equivalently, for every finite X,

\[
\boxed{\sum_{\substack{n\le X\\(n,Q_y)=1}}\log n
=\sum_{\substack{p>y,\,k\ge1\\p^k\le X}}
(\log p)\,F_y(\lfloor X/p^k\rfloor).}\tag{S6}
\]

These are exact *arithmetic* identities between the
incomplete prime wheel and the high-prime logarithmic
forcing; they need no complete CRT period and can be
summed across the original completed square blocks.

**An already existing RH_Lean bridge:** the native theorem
arithmeticLogWeight_moebius_mul_zeta_eq_neg_vonMangoldt
in RHLean/Analysis/NativePNTSignedSecondSelbergFactorFourMoments.lean
proves (D mu)*zeta = -Lambda, with the coefficient version
sum_moebius_log_divisors_eq_neg_vonMangoldt. This
MOBIUS-TO-von-Mangoldt identity is directly pertinent to
OpenAI's reciprocal L-function detector.

Do NOT reinterpret the multi-divisor logarithmic
identity as multiple independent NNS negative owner
charges: S5 computes log(n) via all prime-power factors,
not the unique minFac(n) physical owner. To transport
S5 to the original Sector Six Gram requires an exact
once-charged occurrence classifier.

## 3. Backward analytic route: Möbius owner cancellation to stronger zero exclusion

For M(x)=sum_{n<=x}mu(n), classical Abel/Mellin summation gives

\[
\boxed{\frac{1}{\zeta(s)}
=s\int_1^\infty M(x)x^{-s-1}\,dx,\quad Re(s)>1.}\tag{S7}
\]

A genuinely NEW arithmetic estimate
M(x)=O(x^beta(log x)^k) for beta<7/8 would make
the right side holomorphic for Re(s)>beta.
Since it agrees with 1/zeta on Re(s)>1, analytic
continuation would exclude zeta zeros in Re(s)>beta.
This supplies a direct **owner/Mobius -> analytic**
direction and identifies a plausible common target
with OpenAI's reciprocal-L detector.

But RH_Lean's exact sieve/Fubini identities do not
give the needed new signed bound on M(x). This is
an analytic-strength theorem in its own right, not a
consequence of arithmetic factorization.

## 4. Precisely where synthesis stops

1. OpenAI's published Lean source formalizes zero-free
   Re(s)>7/8 on Lean 4.34.1. RH_Lean uses Lean 4.24.0.
   The classical zero-free -> explicit-prime-error
   estimate has not been integrated as a kernel theorem.
2. A moving cutoff y=A produces finite Euler products
   whose magnitude/inverse can depend substantially on A.
   Nonvanishing does not give uniform owner-correlation
   or moving-wheel spectral norm estimates. The additive
   log-derivative S4 is the better analytic source.
3. Even with uniform 7/8 errors at the partner scale
   q~A, summing per-column errors over O(A/log A)
   owners loses a power: the crude total is O(A^(15/8))
   up to log factors. It is well above the original
   RH wall O(A log A).
4. The exact native Sector Six energy retains the
   historical D_A anchor, all squareful and 3-channel
   charges, and all mixed Gram products. Proving a
   one-column Abel estimate gives NO permission to
   spend an earlier prime's negative charge once per
   descendant.

**Conclusion:** There IS genuine bidirectional synthesis.
The first version of PR #919 was too narrow.
The precise common objects are the *original-weighted
prime-Li Abel source*, *truncated rough Euler product*,
*Möbius inverse of zeta*, and *von Mangoldt logarithmic
derivative*. The analytic-strength global signed
inequality, however, remains genuinely open.
