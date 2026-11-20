# One-sided Chebyshev semivariance as the RH-strength supplier (2026-11-20)

**Status:** Rigorous classical-mathematics implication; the genuinely hard arithmetic semivariance estimate is OPEN, not Lean-certified. No RH claim. This is a new, **source-faithful target and transfer**, not a new cancellation theorem.

## 1. Why this target rather than full signed Selberg |E|^2?

Let E(x)=psi(x)-x, with psi(x)=sum_(n<=x) Lambda(n). For a real z let z_- = max(-z,0) and z_+ = max(z,0). Define the physical zero-target negative semivariance

  V_-(Y) = (1/Y) integral_[Y,2Y] ((psi(t)-t)_-)^2 dt.

The **one-sided critical second-moment condition** is:

  (SV) For every eta>0, V_-(Y) = O_eta(Y^(1+eta)) as Y goes to infinity.

**Classical theorem:** (SV) is equivalent to RH.

- RH -> (SV): the standard RH von Koch bound |psi(t)-t|=O(sqrt(t)*log(t)^2) implies V_-(Y)=O(Y log^4 Y), hence (SV).
- (SV) -> RH: use the *one-sided smoothing identity* and Alpoge's Landau criterion below.

This is not a probability model or randomized-prime hypothesis: the expectation is simply Lebesgue measure normalized on a deterministic physical interval.

## 2. Exact smoothing identity: semivariance controls the needed SIGN

Alpoge's (published) ordinary zeta error is

  G(x) = sum_(n<=x) Lambda(n) (x/n-1) - x log x + (1+gamma)x.

Finite Abel summation gives, for x>=1,

  G(x) = x * (1+gamma + integral_1^x E(t)/t^2 dt).

The classical reciprocal-von-Mangoldt asymptotic

  sum_(n<=x) Lambda(n)/n = log x - gamma + o(1)

together with the PNT implies

  integral_1^infinity E(t)/t^2 dt = -(1+gamma).

Therefore the exact *tail identity* is

  G(x) = -x integral_x^infinity E(t)/t^2 dt.

Consequently (this is the sign-correct use of negative semivariance):

  G(x) <= x integral_x^infinity E_-(t)/t^2 dt.

Let a=2^k x. Cauchy-Schwarz and (SV) give

  x integral_a^(2a) E_-(t)/t^2 dt
      <= x/a^2 sqrt(a) sqrt(integral_a^(2a) E_-(t)^2 dt)
      <= sqrt(C_eta) x * a^(-1/2+eta/2).

Summing k>=0, with 0<eta<1,

  G(x) <= sqrt(C_eta) x^(1/2+eta/2)
          /(1 - 2^(-1/2+eta/2)).

This is the **one-sided G(x)=O_eta(x^(1/2+eta))** condition consumed by Alpoge's
Formalism.zetaLandauEps and gives RH.

Published source declarations:

- Formalism.StatementU: ZetaLandauEps
- Formalism.ZetaNonvanishing.ZetaLandau: zetaLandauEps
- Formalism.ZetaNonvanishing.GzLipschitz: zetaPrimeSumErrorLipschitz

Importing them into RH_Lean's separate Lean environment remains a distinct uncompleted bridge; this note claims the classical mathematical implication, not a checked interrepository proof.

**Important nuance:** A local LPM2 bound yields this smoothed G bound *without* first obtaining a pointwise bound on E(t). Naive Lipschitz/excursion arguments for a pointwise E bound may lose an exponent (a spike of amplitude A occupies ~A width, and its square costs ~A^3).

## 3. Even better: precisely the square-block semivariance already available in RH_Lean

With X_R=R^2-1, set

  Q_-(H) = sum_(H<=R<2H) max(X_R-psi(X_R),0)^2.

The direct native RHLean.Analysis lowerPartialMomentNat degree=2 on the actual square-endpoint PNT error expresses **exactly this finite energy**.

**Source-target theorem:** for every eta>0,

  Q_-(H) = O_eta(H^(3+eta))

also implies RH; the converse follows from the standard RH psi-error bound.

To see why the square sampling loses nothing at this level, use ONLY that
psi(t) is monotone because Lambda(n)>=0. For t in [X_R,X_(R+1)),

  0 <= E_-(t) <= E_-(X_R) + (t-X_R)
               <= E_-(X_R) + (2R+1).

Squaring and integrating the block,

  integral_[X_R,X_(R+1)] E_-(t)^2 dt
     <= 2(2R+1) E_-(X_R)^2 + (2/3)(2R+1)^3.

Sum over H<=R<2H to get

  integral_[X_H,X_(2H)] E_-(t)^2 dt
     << H Q_-(H) + H^4
     <<_eta H^(4+eta).

Each sufficiently large dyadic [Y,2Y] lies within a square-root-index window
[X_H,X_(2H)] with H comparable to sqrt(Y), so this gives (SV) with eta/2.
**No log penalty, no independence assumption, no extra sign estimate.**

The matching expected scale is H samples of an O(H)-size signed error,
i.e. a sum O(H^3), *not* a universal O(H^2) pointwise maximal requirement.

The degree-ONE lower partial moment is in fact a weaker sufficient hypothesis:
sum_(H<=R<2H) E_-(X_R) = O_eta(H^(2+eta)) implies RH by
the same monotone interpolation and LPM1 tail argument.
Degree TWO is still the natural fit to RH_Lean's signed energy identities.

## 4. The signed Selberg source keeps the correct partial-moment TARGET

The existing main-branch theorem
RHLean.Analysis.nativePNTError_mul_log_sq_eq_signedSecondSelberg states exactly

  E(N) log^2(N) = S(N)log(N) - Lambda*S(N)
    + K2*E(N) - floorDefect(N),

with all sums interpreted using the repository's exact integer/floor definitions.

On the selected prime-cofactor block of PR #1157, the K2 contribution is
the fixed *negative* amount -B_R:

  B_R = 2 sum_i log(p_i) sum_(j<=i) log(q_j) > 0.

Let C_R be the **full** right-hand side with this selected negative
contribution removed, including EVERY signed Selberg remainder, all other
K2 coefficients, square-face terms, reciprocal quotients, and floor
defects. Then EXACTLY

  E(X_R) log^2(X_R) = C_R - B_R.

The correct zero-target lower semivariance is therefore

  Q_-(H) = sum_(H<=R<2H) ((B_R - C_R)_+)^2 / log^4(X_R).

**The missing hard arithmetic theorem is now**
  sum_(H<=R<2H) ((B_R - C_R)_+)^2 / log^4(X_R)
     <<_eta H^(3+eta)   for every eta>0,
with C_R containing the complete source and B_R being the *actual* selected
prime/cofactor terms (no double-counted products).

This **retains the source and a fixed target**. On blocks with C_R>=B_R,
the unfavorable semivariance contribution is ZERO: we are not required
to upper-bound C_R or take |C_R-B_R|.

**Sign correction:** the negative semiprime K2 block is not a favorable
credit for the present one-sided G-UPPER goal! It pushes E negative,
which is the DANGEROUS direction in the tail representation for G.
The complementary source must return enough mass that such a deficit is
rare or its excess below B_R small in degree-two severity.

The previous rank/coercivity matrix result alone cannot prove this. All
the arithmetic dependence and signed covariance live in C_R-B_R.

## 5. Actual finite square-endpoint PNT sample (diagnostic only)

Independent exact prime-power von Mangoldt sieve; no Gaussian or random model.
For H<=R<2H, the normalized negative/positive energy Q_-/H^3 is:

 H       negative/H^3   positive/H^3   negative share
 40        0.061398       0.036521        62.70%
 80        0.056044       0.054670        50.62%
 160       0.045184       0.051057        46.95%
 320       0.066643       0.062310        51.68%
 640       0.047067       0.053729        46.70%
 1000      0.055440       0.064185        46.35%

These data exhibit the predicted finite critical normalization but do NOT
bound supremum_H Q_-(H)/H^3, cannot establish a uniform constant, and are
not a proof of (SV). At these scales the negative squared mass is roughly
half, not orders of magnitude smaller: a semivariance split alone gives
NO free exponent gain.

## 6. Existing native formalization that can be reused

- RHLean/Proof/FinitePartialMoments.lean: negativePart and
  lowerPartialMomentNat 2.
- RHLean/Analysis/NativePNTErrorMass.lean: nativePNTError(N)=nativePsi(N)-N,
  and nativePsi_succ.
- RHLean/Analysis/NativePNTSignedSecondSelberg.lean: exact signed K2
  error recurrence, no absolute-value loss.
- RHLean/Analysis/NativePNTSignedSecondSelbergWheelFrontier.lean:
  semiprime positive mixed face and square-face negative diagonal.
- research/VF_MID_919_OAI_PARTIAL_MOMENT_TAILS.lean: native finite
  weighted LPM/UPM tail inequalities, which require **new arithmetic**
  moments for a quantitative improvement.
- research/VF_MID_LOWER_CHANNEL_ALONE_RH_AND_FIRST_BAD_GATE.md:
  existing alternative one-sided pi/li route, with the same caveat
  that the source estimate is unpaid.

**Verification boundary:** The new companion Lean file only defines the
native one-sided critical semivariance proposition and checks its exact
finite lower-part identity. The analytic tail identity, the square-to-
continuous interpolation integral, external Landau theorem and the
semivariance exponent are not falsely marked as Lean-certified.
