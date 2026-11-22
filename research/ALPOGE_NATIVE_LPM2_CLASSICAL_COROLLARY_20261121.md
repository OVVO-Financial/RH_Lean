# Alpoge -> native signed Selberg -> negative Chebyshev semivariance
Date: 2026-11-21

## The unconditional MATHEMATICAL corollary (external theorem cited)

Let
\[
X_R=R^2-1,\qquad E(N)=\psi(N)-N
\]
and let \(C_R-B_R\) denote the *complete original* signed second-Selberg
source as defined in
`research/ALPOGE_LITERAL_GZ_SELBERG_TRANSLATION_20261120.lean`.
All prime powers, quotient returns, floor defects and first-Selberg terms
are retained. That source has the **proved algebraic identity**
\[
C_R-B_R=E(X_R)\log^2 X_R.
\]

**Theorem (unconditional as ordinary mathematics, using Alpoge's independently
verified RH theorem and the classical RH-to-Chebyshev explicit formula).**
For every \(\varepsilon>0\), there exists \(K_\varepsilon\ge0\) such that
for all integers \(H\ge2\),
\[
\sum_{H\le R<2H}\frac{(B_R-C_R)_+^2}{\log^4X_R}
\le K_\varepsilon H^{3+\varepsilon}.
\]
At \(H=1\) the unique term has \(X_1=0\); use the native LPM2
definition directly (the displayed logarithmic quotient is not defined).

**Proof.** By the exact signed source identity, and the positivity of
\(\log X_R\) for \(R\ge2\),
\[
\frac{(B_R-C_R)_+^2}{\log^4 X_R}
=\big(\max\{-E(X_R),0\}\big)^2.
\]
Alpoge's externally verified theorem proves RH. The classical explicit
formula under RH gives constants \(A,x_0\) for which
\[
|E(x)|\le A\sqrt{x}(\log x)^2\quad(x\ge x_0).
\]
Enlarge \(A\) to cover the finitely many smaller square endpoints.
For \(H\le R<2H\), \(X_R<R^2\le4H^2\), and hence
\[
\max(-E(X_R),0)^2\le A'^2R^2\log^4(4H^2)
\le4A'^2H^2\log^4(4H^2).
\]
There are exactly \(H\) integers in the dyadic interval. Therefore
\[
Q_-(H)\le4A'^2H^3\log^4(4H^2)
\le K_\varepsilon H^{3+\varepsilon},
\]
since every fixed power of \(\log H\) is \(O_\varepsilon(H^\varepsilon)\).
This proves the corollary as an unconditional statement of mathematics
with an **external proved RH input**; it is NOT a direct lattice-energy proof.

## What the newly added native Lean module actually proves

`RHLean/Analysis/AlpogeNegativeSelbergSemivariance.lean` includes:

1. `alpogeFullMatchedSecondSelberg_eq_nativeError`: exact complete original
   signed Selberg identity, with both lower logarithmic and floor-defect
   terms, and the genuine fully matched prime-power source.
2. `alpogeFullMatchedSquareNegativeLPM2_eq_native`: exact equality of the
   normalized squared negative matched source with the native zero-target
   LPM2 on all square endpoints \(H\le R<2H\), \(H\ge2\). No
   cancellation is assumed after splitting terms.
3. `alpogeNativeSquareNegativeLPM2_le_uniform`: the genuinely
   unconditional *finite* inequality
   \(Q_-(H)\le H\cdot\max_{H\le R<2H}|E(X_R)|^2\).
4. `alpogeNativeSquareNegativeLPM2_of_dyadicChebyshev`: a proved
   exponent-preserving implication from a **named** quantitative
   pointwise square-root supplier to the required \(H^{3+\varepsilon}\)
   negative semivariance bound.

**Lean verification status:** CI must finish before these new declarations
are treated as checked. The downstream critical bound still has
`NativeSquareDyadicChebyshevBound` as an explicit premise.

## The remaining cross-repository import and classical bridge

These are separate obligations, not silently axiomatized facts:

* Import the verified kernel certificate
  `UpperTheory.FinalTheorems.riemannHypothesis` from
  `CocoSgt/riemann-hypothesis-lean` into a compatible environment.
  RH_Lean is pinned at Lean 4.34.1 with a different dependency graph.
* Supply and check the quantitative *RH -> psi(x)-x* explicit-formula
  theorem against RH_Lean's actual `nativePsi` (sum of all prime-power
  von Mangoldt weights) and turn its logarithms into square-root-index
  exponent bounds.
* Compose these suppliers with
  `alpogeNativeSquareNegativeLPM2_of_dyadicChebyshev`.

Do NOT claim a self-contained Lean proof of the unconditional estimate
until those three steps are kernel checked.

## Why no isolated band or covariance can shortcut this

The already verified `alpogeNNSBand_principalMode_cancels` and
`alpogeNNSSecondSelbergSource_eq_first_times_log` show that
\(K_2-(\Lambda*\Lambda)=-\Lambda\log\) *for the same physical source*.
The apparent isolated near-root \(-S_R^2\) principal gain is canceled
by the ordered product convolution. A negative quadratic band gain cannot
be counted again as a free credit.

The prospective **direct** lattice-to-LPM2 theorem must therefore pay
\[
\sum_{H\le R<2H}
 \frac{[-(A_R+F_R)]_+^2}{\log^4X_R},
\qquad A_R+F_R=E(X_R)\log^2X_R,
\]
using the *full* joint covariance, and must account for the reciprocal
\(\Lambda\) channel when passing from Alpoge's one-sided \(G_z\) estimate
to the negative Chebyshev error. The exported geometric route need not
prove this particular moment bound directly, so it is a new proof goal.
