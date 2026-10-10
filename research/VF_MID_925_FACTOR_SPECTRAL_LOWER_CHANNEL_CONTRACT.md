# #925 — Genuine factor-range square theta forcing and its zeta-zero spectrum

**Date:** October 10, 2026. **Scope:** a second representation of the
EXISTING arithmetic forcing, not a substitute for the lower-channel proof.
**Status:** native finite factor/theta/owner algebra committed to Lean;
classical explicit formula and truncation estimates are external
analytic theorems and are NOT imported into Lean. The uniform signed
owner-return bound, and hence the lower-channel/RH proof, remains OPEN.

Companion source:
\`research/VF_MID_925_FACTOR_THETA_SPECTRAL_WELD.lean\`.
Main source contract:
\`research/VF_MID_LOWER_CHANNEL_ALONE_RH_AND_FIRST_BAD_GATE.md\`.

## 1. SAME arithmetic sources, no new definition of pi

For \(R\ge5\), let \(a=R^2,\ b=(R+1)^2\) and
\[
W_R=\{n:a<n<b,\ \gcd(n,30)=1\},\quad
C_R=\{n\in W_R:\exists\,7\le d\le R,\ d\mid n\}.
\]
The new source set is the **uncovered** factor-range carrier
\[
S_R=W_R\setminus C_R.
\]
The existing fundamental-factorization common-wheel theorem proves
\[
S_R=\{p:a<p<b,\ p\text{ prime}\},
\]
because every composite in the strict-open band has a prime factor
at most \(R\). In the Lean module:
\`vf925FactorRangeUncovered_eq_fullWheel\` and
\`vf925FactorRangeUncovered_eq_directPrimeBand\`.

The genuine log-weighted supply is
\[
\boxed{Q_R=\sum_{n\in S_R}\log n
=\theta(b)-\theta(a).}
\tag{S1}
\]
This is compiled-source finite arithmetic, not a numerically
approximated prime distribution. There is no independent definition
of the unknown prime count in the source carrier.

Set the theta **shortage** (the sign must be retained) to
\[
\boxed{U_R=(b-a)-Q_R=(2R+1)-Q_R.}
\tag{S2}
\]
Then the old direct theta band error is \(-U_R\), and
\[
U_R= [\theta(a)-a]-[\theta(b)-b].
\tag{S3}
\]
The new Lean exact source-to-native identities are
\`vf925FactorThetaForcing_eq_neg_thetaBandError\`,
\`vf925FactorThetaForcing_eq_thetaEndpointDrop\`, and
\[
\boxed{U_R=\log(m_R)\bigl(
\mathrm{NativeCharge}_R+\mathrm{DescentRemainder}_R+
\mathrm{LogPositionError}_R\bigr).}
\tag{S4}
\]
Equation (S4), formalized by
\`vf925FactorThetaForcing_eq_nativeOwnerPacket\`, uses the
ALREADY PRESENT original signed physical owner packet in
\`VF_MID_SQUARE_THETA_NATIVE_DESCENT.lean\`. It does not
create a new fitted packet, replace occurrence weights, or grant
the charge a favorable sign.

## 2. Retain the VF count weight and signed prime position

Write
\[
m_R=R^2+R+\tfrac12,\quad
V_R=\frac{2R+1}{\log m_R},\quad
P_R=|S_R|.
\]
Define the original within-band logarithmic placement term
\[
\mathrm{Pos}_R=P_R-\frac{Q_R}{\log m_R}.
\]
Then *algebraically*
\[
\boxed{
E_R=V_R-P_R=\frac{U_R}{\log m_R}-\mathrm{Pos}_R.
}
\tag{S5}
\]
This is the direct connection between the signed coverage excess in
\`VF_MID_THIRTY_FACTOR_RANGE_LOWER_GATE.lean\` and the log-weighted
theta source, with NO omitted placement term. The Lean bridge is
\`vf925FactorCoverageExcess_eq_thetaForcing_div_log_sub_position\`.

At a hypothetical FIRST lower breach \(R+1\) from a safe predecessor
\(R\), the exact old slack is \(S_R^{\rm slack}=D_R+KR\log R\) and
\(\Delta_K(R)=K[(R+1)\log(R+1)-R\log R]\).
The already-proved one-block overrun condition becomes
\[
\boxed{
\frac{U_R}{\log m_R}>
S_R^{\rm slack}+\Delta_K(R)+\mathrm{Pos}_R.
}
\tag{S6}
\]
This is \`vf925FirstLowerBreach_forces_thetaSourceThreshold\`.
It is a necessary condition at a *hypothetical* bad endpoint, NOT
an upper bound that excludes one. The original physical history
and source-to-owner cross-terms still require an independent estimate.

## 3. The CORRECT \(\psi_0\) and square-endpoint explicit formula

The classical second Chebyshev function is
\[
\psi(x)=\sum_{n\le x}\Lambda(n).
\]
At a real prime-power jump the explicit formula uses
\[
\psi_0(x)=\psi(x)-\tfrac12\Lambda(x)
\quad (x\text{ an integer}),
\]
with \(\Lambda(x)=0\) for integers not prime powers.
The exact von Mangoldt explicit formula for \(x>1\) is
\[
\boxed{
\psi_0(x)=x-\lim_{T\to\infty}
 \sum_{|\Im\rho|\le T}\frac{x^\rho}{\rho}
-\log(2\pi)-\tfrac12\log(1-x^{-2}).
}
\tag{S7}
\]
Nontrivial zeros are counted **with multiplicity** and the
conditionally convergent sum is taken by symmetric-height
truncation (through appropriate regular heights). The zero
ordinates and real parts are *exact* mathematical quantities.

Now isolate the genuine higher-prime-power mass **strictly inside**
one square band,
\[
H_R=\sum_{\substack{a<n<b\\n=p^k,\ k\ge2}}
 \log p.
\]
Both \(a,b\) are composite perfect squares, so any nonzero
\(\Lambda(a)\) or \(\Lambda(b)\) is genuinely a higher-power
endpoint contribution. Exactly,
\[
\begin{aligned}
\psi(b)-\psi(a)
 &=Q_R+H_R+\Lambda(b),\\
\psi_0(b)-\psi_0(a)
 &=Q_R+H_R+\tfrac12[\Lambda(a)+\Lambda(b)].
\end{aligned}
\tag{S8}
\]
**IMPORTANT:** The lower endpoint \(a\) is excluded by
\(\psi(b)-\psi(a)\) but reappears with a **positive** half-jump
in \(\psi_0(b)-\psi_0(a)\). The upper endpoint \(b\) contributes
its own positive half-jump. Do not use the incorrect one-sided
boundary rule \([\Lambda(b)-\Lambda(a)]/2\) as the final correction.

The new finite native Lean definitions are
\`vf925PsiMidAt\` and
\`vf925StrictInteriorHigherPowerMass\`; the theorem
\`vf925PsiMidSquareDiff_eq_factorTheta_plus_power_plus_halfJumps\`
proves (S8) by exact arithmetic, with no spectral input.

Subtracting (S7) at \(a,b\) and using (S8), the constant
\(-\log(2\pi)\) cancels. Thus
\[
\boxed{
\begin{aligned}
U_R={}&\lim_{T\to\infty}
 \sum_{|\Im\rho|\le T}\frac{b^\rho-a^\rho}{\rho}\\
 &+\frac12\log\frac{1-b^{-2}}{1-a^{-2}}
 +H_R+\frac{\Lambda(a)+\Lambda(b)}2.
\end{aligned}}
\tag{S9}
\]
This is an **unconditional paper-level exact identity** obtained
from the classical explicit formula. The corresponding Lean
\`vf925FactorThetaForcing_of_explicitPsiMidDifference\` is a
*CONDITIONAL CONSUMER* accepting the exact analytic square-endpoint
formula \`hformula\`; it does not assert or kernel-prove (S7).

At the transparent endpoint example \(R=7\):
\(a=49=7^2,\ b=64=2^6\). The two half-jumps are
\(\tfrac12(\log7+\log2)\), and \(H_7=0\).
The surviving actual prime sites are \(53,59,61\). Ignoring
either 49's or 64's half-jump breaks (S8).

## 4. The spectral square-root resolution — what is and isn't proved

Let \(\rho=\beta+i\gamma\). In one square band
\[
\Delta\log x=\log(b/a)
 =2\log(1+1/R)=2/R+O(R^{-2}),
\quad
\Delta\phi_\rho=\gamma\Delta\log x.
\]
The natural *block resolving frequency* is \(|\gamma|\asymp R\),
where the phase changes by order one across one square tile.

For a **fixed** zero \(\rho\) with \(R\to\infty\),
\[
\frac{b^\rho-a^\rho}{\rho}
 =2R^{2\rho-1}(1+O_\rho(R^{-1})),
\quad
\left|\frac{b^\rho-a^\rho}{\rho}\right|
 \sim2R^{2\beta-1}.
\tag{S10}
\]
Thus a fixed critical-line zero has an \(O(1)\)
single-tile contribution and a fixed off-line zero
\(\beta>1/2\) has an \(R^{2\beta-1}\)-scale single-tile
contribution. This is NOT uniform in \(|\gamma|\le cR\);
summing these terms without proving cancellation is invalid.

Classical *truncated* explicit formula estimates for
\(\psi_0(x)\) have errors of the form
\[
O\left(
\frac{x\log^2(xT)}{T}
+\log x\min\{1,\,x/(T\,d(x))\}
\right),
\tag{S11}
\]
for a suitable zero-avoiding height \(T\), where \(d(x)\)
is the distance to the nearest *other* prime-power
integer (with the midpoint convention at a jump).
The exact error conventions matter; do not drop
the near-prime-power contribution for arbitrary real \(x\).
For integer square endpoints, \(d(x)\ge1\);
taking \(T\asymp R\) at \(x=R^2\) gives a
**qualitative** \(O(R\log^2R)\) truncation remainder.
This is the RH-scale order for \(\psi\), but says
NOTHING about the size of the FINITE GROWING zero sum
\[
\sum_{|\Im\rho|\le R}\frac{R^{2\rho}}{\rho}.
\]

Cully-Hugill and Johnston (arXiv:2111.10001) give an
explicit \(O(x\log x/T)\) error, and their follow-up
(arXiv:2402.04272, latest revision February 23, 2026)
reports an explicit \(O(x/T)\) result. Before using
either to sharpen a particular square endpoint estimate,
check its exact hypotheses, height choice and jump convention.
**No such truncated formula is imported into Lean here.**

## 5. Zero ordinates are not numerical error sources

The real ordinates \(\gamma\) are exact even if numerical
software stores approximations. If a computed ordinate
has error \(\delta\gamma\), its phase error at \(x=R^2\)
is approximately \(2\delta\gamma\log R\).
Increasing numerical precision reduces this error
without any forced positive lower floor. Irrationality
of *all* ordinates is not known and cannot be used
as a distributional premise. Even irrational phases
by themselves do not prove signed arithmetic cancellation.
They do not explain the \(\sqrt2\) vertical phase.

The actual arithmetic-forcing discrepancy and exact
zeta spectrum encode **the same nontrivial fluctuation**;
finite precision and finite-zero truncation are
*additional approximation errors*, not a new source
of compensation for the original native Sector Six bill.

## 6. New exact lower first-bad spectral demand

Combining (S6) and the CONDITIONAL (S9) gives:
\[
\boxed{
\frac{
 \sum_\rho (b^\rho-a^\rho)/\rho+
 \frac12\log\frac{1-b^{-2}}{1-a^{-2}}+
 H_R+\frac{\Lambda(a)+\Lambda(b)}2
}{\log m_R}
>
S_R^{\rm slack}+\Delta_K(R)+\mathrm{Pos}_R.
}
\tag{S12}
\]
This uses the infinite symmetric-height interpretation of
the zero sum. In Lean the exact consumer is
\`vf925FirstLowerBreach_forces_spectralThreshold\`
with \`hformula\` supplied explicitly.

This is the **same necessary condition** as source (S6),
not an independent inequality and not a contradiction.
The remaining decisive theorem is still:

> For an actual least-prime-owner history with the original
> survivor masks, ages, clipped six-sector weights and historical
> slack, independently prove that a first lower-bad event cannot
> satisfy the physical signed owner-overrun / theta-forcing
> threshold.

The spectral representation may suggest useful
cofactor-rescaling or phase-correlation estimates, but
it does not supply that theorem automatically.
We should not attempt to derive RH by bounding each zero
or asserting an unproved spectral anti-phase property.

## 7. Precise numerical experiment to falsify or motivate a candidate return law

First run a **zero-free numerical arithmetic check**:
compute \(S_R,Q_R,H_R,\Lambda(a),\Lambda(b)\) by genuine
integer divisibility and verify (S1), (S5), (S8) for EVERY
root in a chosen finite horizon. The reproducible script
\`scripts/VFMid925Spectral/verify_factor_theta.py\`
does this, including both prime-power endpoints.
It does NOT numerically verify an infinite zero sum.

Then, *separately* and optionally, obtain validated
zero ordinates and compute symmetric-height
\[
Z_R(T)=\sum_{|\gamma|\le T}
 \frac{b^\rho-a^\rho}{\rho},\quad T\approx R
\]
with explicit numerical precision, zero multiplicities
and endpoint/truncation error bars. Compare
\[
U_R-
\left[ Z_R(T)+
 \tfrac12\log\frac{1-b^{-2}}{1-a^{-2}}
 +H_R+\tfrac12(\Lambda(a)+\Lambda(b))\right]
\]
against the **known** analytic truncation allowance.

Finally use the EXISTING original native owner ledgers to
condition the signed forcing on:
(1) predecessor historical wall slack \(S_R^{\rm slack}\);
(2) least-owner age and stripped-child scale;
(3) all first-left/next-right/returned-left square-sector
incidences and diagonal/squareful terms;
(4) the exact signed position term \(\mathrm{Pos}_R\).

Do not test a false unconditional one-tile sign, an absolute-value
replacement, or pairwise independent-prime phases.
The 25/629 early positive next-right clip already
falsifies such a shortcut. Do not silently equate a
match of numerical spectral and arithmetic representations
with a NEW signed inequality: (S9) guarantees their equality
in the infinite-zero limit.

## 8. Source and acceptance status

- **Arithmetic identity:** derived by exact FTA and theta/psi
  finite differences; new Lean theorems require current PR CI
  to certify kernel compilation.
- **Classical explicit formula (S7):** established in the literature
  but NOT kernel imported; Lean's spectral theorem is explicitly
  conditional on hformula.
- **Resolution asymptotic (S10):** fixed-zero paper deduction
  only, NOT a uniform zero-sum estimate.
- **Truncation (S11):** external estimate with caveats,
  NOT a proof of RH-scale sum cancellation.
- **Lower-channel first-bad exclusion:** STILL OPEN.

References:
- Wolfram MathWorld, Chebyshev explicit formula:
  https://mathworld.wolfram.com/MangoldtSummatoryFunction.html
- Detailed derivation, including prime-power jump and
  zero-avoiding truncation-height qualifications:
  https://ntriantafilidis.wordpress.com/2013/12/20/an-explicit-formula-1/
- Cully-Hugill & Johnston (2021/2024):
  https://arxiv.org/abs/2111.10001
- Johnston & Cully-Hugill (2024/2026):
  https://arxiv.org/abs/2402.04272
