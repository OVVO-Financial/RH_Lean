# Full-source Alpoge Gz as an exact NNS future tail

Date: 2026-11-21. This PR is independent of PR #1180.

## New unconditional Lean theorem

The root module RHLean/Analysis/AlpogeGzNNSFutureTail.lean
starts with the EXACT original Chebyshev-error atom

  E(n)=psi(n)-n;
  e(n)=E(n)/(n*(n+1)).

For positive integers N,M define

  T(N,M) =
   [UPM1(e,[1,M))-LPM1(e,[1,M))]
   -[UPM1(e,[1,N))-LPM1(e,[1,N))]
  = W(M-1)-W(N-1),

where W(k)=sum_(1<=n<=k) e(n).

Let d(n)=harmonic(n)-log(n)-EulerGamma.
The existing nativeHarmonicLogError_bounds gives
  0 <= d(n) <= 1/n  for n>=1.

The new Lean theorem proves, without any hypothesis on primes,

  Gz(N)/N = Gz(M)/M - T(N,M) + d(N)-d(M).              (1)

The following **unconditional quantitative NNS upper bound**
is therefore immediate and is included in the new Lean file:

  Gz(N) <= (N/M)*Gz(M) - N*T(N,M) + 1.                (2)

And there is a two-sided enclosure at normalized scale:

  Gz(M)/M - T(N,M)-1/M
    <= Gz(N)/N
    <= Gz(M)/M - T(N,M)+1/N.                         (3)

The exact one-sided finite target equivalence is

  Gz(N) <= B   IFF
  T(N,M) >= Gz(M)/M + d(N)-d(M)-B/N.                 (4)

All signs remain intact. There is no determinant, cohomology proxy,
randomness, smoothing or unquantified correction. (2) genuinely
pays the entire harmonic endpoint defect with one absolute unit.
Crucially, the future signed tail and terminal Gz(M) MUST be paid
in order to obtain an RH-critical rate.

Lean declarations:
  alpogeGzNativeNNSTail_eq_prefix_diff
  alpogeGzNativeHarmonicError_bounds
  alpogeGz_eq_NNS_futureTail_and_terminal
  alpogeGz_NNS_futureTail_oneSided_le
  alpogeGz_NNS_futureTail_twoSided
  alpogeGz_upperBound_iff_NNS_tailLower.

## Exact infinite-future theorem (mathematical derivation)

The classical strong PNT is already available from imported
PrimeNumberTheoremAnd.StrongPNT:

  psi(x)-x = O(x*exp(-c*sqrt(log x))) for some c>0.

Thus the series sum_(n>=1) |e(n)| converges absolutely.
The classical Laurent expansion at zeta(s)=1 establishes

  sum_(n<=N) Lambda(n)/n-log N --> -EulerGamma.

By the existing finite Abel identity, or the Mellin transform,
  W(infty) = -2*EulerGamma.

Taking M->infinity in (1), using
  Gz(M)/M -> 0,
  harmonic(M)-log M -> EulerGamma,
gives, exactly,

  Gz(N)/N = -T_N + d(N),                             (5)
  T_N = sum_(n>=N) (psi(n)-n)/(n(n+1)).

Therefore

  -N*T_N <= Gz(N) <= -N*T_N+1.                     (6)

The RH-critical one-sided bound
  Gz(N) <= C_eps*N^(1/2+eps)
is equivalent (with the one-unit collar) to the
  LOWER bound T_N >= -C'_eps*N^(-1/2+eps).
This is the single genuine NNS signed-tail supplier to find.

STATEMENT STATUS: (1)-(4) are Lean declarations in this PR;
(5)-(6) are proved mathematically in this document but the
infinite limiting theorem is not yet formalized in Lean.

## The precise continuous counterpart

Alpoge's original continuous real observable is

  Gz(x) = sum_(n<=x) Lambda(n)*(x/n-1)
            -x*log x +(1+EulerGamma)*x.

Finite Abel summation gives
  A(x)=sum_(n<=x) Lambda(n)/n
      =psi(x)/x +integral_1^x psi(t)/t^2 dt.

With E(t)=psi(t)-t and the zeta Laurent constant

  1+integral_1^infinity E(t)/t^2 dt = -EulerGamma.

Subtract the constant, and all endpoint corrections cancel:

  Gz(x) = -x*integral_x^infinity E(t)/t^2 dt.       (7)

This continuous integral is EXACTLY the same original prime-power
source as (5), not an arbitrary resolvent or Gram determinant.

StrongPNT now yields, unconditionally and for some c'>0,

  |Gz(x)| = O(x*exp(-c'*sqrt(log x))) = o(x).        (8)

Proof: bound the absolute tail in (7); use
u=sqrt(log t) to compute explicitly

  integral_x^infinity exp(-c sqrt(log t))/t dt
   = 2*exp(-c sqrt(log x))*
     (sqrt(log x)/c+1/c^2).

Absorb sqrt(log x) by reducing c. This is a genuine strict
sublinear bound, but it does NOT imply O(x^(1/2+eps)).
This analytic asymptotic consequence is documented here,
NOT claimed as a Lean-checked theorem.

## Search results: the best existing RHLean suppliers

- AlpogeGzErdosReciprocalHistory: literal original Gz signed source
  and reversible centered-historical inequality (EXACT).
- AlpogeSquareClockSignedHistorySampling: square-root-cost
  interpolation from square endpoints to all integers. Its
  square-endpoint critical bound is a HYPOTHESIS.
- AlpogeErdosHistoryIncrementNNS2: genuine unconditional
  dyadic O(H^3) UPM2 on POSITIVE SQUARE INCREMENTS, not their
  cumulative endpoint Gz values.
- NativePNTErrorMass: bounded whole signed historical prefix,
  insufficient for root-scale signed future-tail RATE.
- NativePNTMobiusMoments: exact harmonic collar 0<=d(N)<=1/N,
  now paid in full by (2).
- NativePNTReciprocalInterceptPowerBound: root-scale Chebyshev
  error depends on the unproved ReciprocalInterceptLaw K.
- NativePNTErdosContraction and StrongPNT: qualitative and
  stretched-log relative error decay, not a fixed exponent.
- NativePNTSignedSecondSelberg and the matched K2 layers:
  complete matched source cancellation but no uniform
  across-root signed covariance bound.
- OAI seven-eighths research import: not a half-exponent
  theorem and distinct from the desired full Gz tail source.

No unconditional root-scale tail-lower theorem was located
in the inspected root-module declarations. This does NOT
prove such a theorem cannot be derived from other repo work.

## Acceptance criterion

An unconditional Lean theorem giving, for all epsilon>0,
T_N >= -C_eps*N^(-1/2+eps), without using RH or the
equivalent Gz bound as a premise, would close the desired
one-sided Gz estimate via (5)-(6).

The new finite iff (4) prevents accidental weakening:
terminal Gz(M), local correction, and both NNS signs
must survive every change of arithmetic coordinates.
