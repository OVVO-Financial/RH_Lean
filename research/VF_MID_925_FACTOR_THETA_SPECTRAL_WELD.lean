import Mathlib
import «research.VF_MID_THIRTY_FACTOR_RANGE_LOWER_GATE»
import «research.VF_MID_SQUARE_THETA_NATIVE_DESCENT»

/-!
# PR #925: actual factor-range theta forcing and the spectral input boundary

This file welds the NEW gcd-30/divisor-range physical source to the
ALREADY-PROVED native Chebyshev-theta and descending-owner source.
Every unconditional theorem refers only to genuine finite integers.

At the R-th OPEN square band, the exact survivors after the 2,3,5
wheel and divisors d in [7,R] ARE the actual prime-band sites by FTA.
Their logarithmically weighted supply is thus theta(b)-theta(a).
The centered forcing U_R = (b-a)-Q_R is the NEGATIVE local theta
error, with its original native signed owner/remainder/position packet.

The last theorem takes as an EXPLICIT premise the independent
analytical explicit formula at the TWO MIDPOINT-JUMP square endpoints.
It does NOT import zeta-zero sums, assume RH, or silently assert the
new cancellation estimate. Both endpoint von Mangoldt half jumps,
the proper prime powers, and the trivial-zero logarithmic correction
must be supplied before applying the theorem.
-/

noncomputable section

open scoped BigOperators ArithmeticFunction.vonMangoldt

namespace RHLean.Analysis

open RHLean.Arithmetic RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Genuine integer seats not covered by any factor up to R. This SOURCE
definition uses the existing 30-wheel and finite divisor predicate, and
does not involve pi, theta, zeros, or a prime indicator. -/
def vf925FactorRangeUncovered (R : ℕ) : Finset ℕ :=
  vfMidThirtyCandidates R \ vfMidThirtyFactorCovered R

/-- The 30-wheel surviving sites equal the full genuine R-factor wheel. -/
theorem vf925FactorRangeUncovered_eq_fullWheel
    (R : ℕ) (hR : 5 ≤ R) :
    vf925FactorRangeUncovered R =
      vfMidSquarePrefixWheelSurvivors R R := by
  classical
  ext n
  constructor
  · intro hn
    rcases Finset.mem_sdiff.mp hn with ⟨hc, hncovered⟩
    by_contra hnotFull
    have hcovered :=
      (vfMidThirtyFactorCovered_mem_iff_not_fullWheel hR hc).2 hnotFull
    exact hncovered hcovered
  · intro hfull
    have hc : n ∈ vfMidThirtyCandidates R :=
      vfMidFullWheel_subset_thirtyCandidates R hR hfull
    refine Finset.mem_sdiff.mpr ⟨hc, ?_⟩
    intro hcovered
    exact ((vfMidThirtyFactorCovered_mem_iff_not_fullWheel hR hc).1
      hcovered) hfull

/-- The FTA decoder is exact and occurrence-preserving at the original
strict-open square sites. The right endpoint is a composite square. -/
theorem vf925FactorRangeUncovered_eq_directPrimeBand
    (R : ℕ) (hR : 5 ≤ R) :
    vf925FactorRangeUncovered R = vfMidDirectPrimeBand R := by
  calc
    vf925FactorRangeUncovered R =
        vfMidSquarePrefixWheelSurvivors R R :=
      vf925FactorRangeUncovered_eq_fullWheel R hR
    _ = vfMidSquareWheelPrimes R := by
      rw [vfMidSquarePrefixWheelSurvivors_full,
        vfMidSquareWheelSurvivors_eq_primes R (by omega : 2 ≤ R)]
    _ = vfMidDirectPrimeBand R :=
      (vfMidDirectPrimeBand_eq_squareWheelPrimes R).symm

/-- Log weight is attached to EVERY true factor-range survivor. -/
def vf925FactorRangeThetaMass (R : ℕ) : ℝ :=
  ∑ n ∈ vf925FactorRangeUncovered R, Real.log (n : ℝ)

/-- The source-native log-weighted supply is the exact physical prime
log mass, not a smooth or fantasy theta surrogate. -/
theorem vf925FactorRangeThetaMass_eq_directThetaMass
    (R : ℕ) (hR : 5 ≤ R) :
    vf925FactorRangeThetaMass R = vfMidDirectThetaBandMass R := by
  unfold vf925FactorRangeThetaMass vfMidDirectThetaBandMass
  rw [vf925FactorRangeUncovered_eq_directPrimeBand R hR]

/-- FTA reveals the ORIGINAL finite Chebyshev-theta band increment. -/
theorem vf925FactorRangeThetaMass_eq_thetaDifference
    (R : ℕ) (hR : 5 ≤ R) :
    vf925FactorRangeThetaMass R =
      nativeTheta ((R + 1) ^ 2) - nativeTheta (R ^ 2) := by
  rw [vf925FactorRangeThetaMass_eq_directThetaMass R hR]
  exact vfMidDirectThetaBandMass_eq_theta_sub R

/-- The signed source-only square-band theta forcing: theta shortage,
measured in log-mass units rather than prime counts. -/
def vf925FactorThetaForcing (R : ℕ) : ℝ :=
  (2 * (R : ℝ) + 1) - vf925FactorRangeThetaMass R

/-- The sign is FIXED: theta shortage U_R = -(theta band error). -/
theorem vf925FactorThetaForcing_eq_neg_thetaBandError
    (R : ℕ) (hR : 5 ≤ R) :
    vf925FactorThetaForcing R = -vfMidDirectThetaBandError R := by
  unfold vf925FactorThetaForcing vfMidDirectThetaBandError
  rw [vf925FactorRangeThetaMass_eq_directThetaMass R hR]
  ring

/-- Exact endpoint first difference: accumulated source theta forcing
is the DECREASE in theta(x)-x. -/
theorem vf925FactorThetaForcing_eq_thetaEndpointDrop
    (R : ℕ) (hR : 5 ≤ R) :
    vf925FactorThetaForcing R =
      vfMidDirectThetaEndpointError R -
        vfMidDirectThetaEndpointError (R + 1) := by
  rw [vf925FactorThetaForcing_eq_neg_thetaBandError R hR,
    vfMidDirectThetaBandError_eq_endpoint_diff]
  ring

/-- The original signed theta source is EXACTLY the previously compiled
native least-owner descent + transfer remainder + within-band placement.
This is the physical owner weld, not a new sign/energy estimate. -/
theorem vf925FactorThetaForcing_eq_nativeOwnerPacket
    (R : ℕ) (hR : 7 ≤ R) :
    vf925FactorThetaForcing R =
      Real.log (vfMidBandMidpoint R) *
        (vfMidRecursiveAggregateNativeCharge R +
         vfMidNativeDescentRemainder R +
         vfMidDirectLogPositionError R) := by
  rw [vf925FactorThetaForcing_eq_neg_thetaBandError R
    (by omega : 5 ≤ R)]
  rw [vfMidDirectThetaBandError_eq_nativeVFDescent R hR]
  ring

/-- Critically, the exact LOWER-CHANNEL count excess is the new
theta forcing divided by the original midpoint log, MINUS the original
within-band prime-position correction. Nothing has been dropped. -/
theorem vf925FactorCoverageExcess_eq_thetaForcing_div_log_sub_position
    (R : ℕ) (hR : 5 ≤ R) :
    vfMidThirtyFactorCoverageExcess R =
      vf925FactorThetaForcing R / Real.log (vfMidBandMidpoint R) -
        vfMidDirectLogPositionError R := by
  calc
    vfMidThirtyFactorCoverageExcess R =
        vfMidOddCompositeTrackingDefect R :=
      vfMidThirtyFactorCoverageExcess_eq_oddOwnerDefect R hR
    _ = -vfMidSquareBandError R :=
      vfMidOddCompositeTrackingDefect_eq_neg_bandError R
        (by omega : 2 ≤ R)
    _ = -vfMidDirectBandError R := by
      rw [vfMidDirectBandError_eq_squareBandError]
    _ = -(vfMidDirectThetaBandError R /
          Real.log (vfMidBandMidpoint R) +
          vfMidDirectLogPositionError R) := by
      rw [vfMidDirectBandError_eq_theta_add_position R]
    _ = vf925FactorThetaForcing R /
          Real.log (vfMidBandMidpoint R) -
          vfMidDirectLogPositionError R := by
      rw [vf925FactorThetaForcing_eq_neg_thetaBandError R hR]
      ring

/-- psi_0 evaluated at one natural endpoint, using the usual average
of the left and right jumps. Only finite genuine Mangoldt arithmetic. -/
def vf925PsiMidAt (N : ℕ) : ℝ :=
  nativePsi N - (Λ N) / 2

/-- Strict-interior *higher-prime-power* mass. For a,b consecutive
perfect-square endpoints, the difference psi(b)-psi(a) contains all
prime and proper-power jumps in (a,b]; theta(b)-theta(a) contains
only prime jumps; subtract Lambda(b) to remove the UPPER endpoint.
The lower endpoint is excluded already. -/
def vf925StrictInteriorHigherPowerMass (R : ℕ) : ℝ :=
  (nativePsi ((R + 1) ^ 2) - nativePsi (R ^ 2)) -
    (nativeTheta ((R + 1) ^ 2) - nativeTheta (R ^ 2)) -
    Λ ((R + 1) ^ 2)

/-- Exact accounting of BOTH square endpoint half jumps:
psi_0(b)-psi_0(a) = Q_R + H_R + [Lambda(a)+Lambda(b)]/2.
No zero assumption or analytic truncation is needed. -/
theorem vf925PsiMidSquareDiff_eq_factorTheta_plus_power_plus_halfJumps
    (R : ℕ) (hR : 5 ≤ R) :
    vf925PsiMidAt ((R + 1) ^ 2) - vf925PsiMidAt (R ^ 2) =
      vf925FactorRangeThetaMass R +
        vf925StrictInteriorHigherPowerMass R +
        (Λ (R ^ 2) + Λ ((R + 1) ^ 2)) / 2 := by
  unfold vf925PsiMidAt vf925StrictInteriorHigherPowerMass
  rw [vf925FactorRangeThetaMass_eq_thetaDifference R hR]
  ring

/-- The exact FINITE ALGEBRA needed at the external zeta formula boundary.
Here spectralIncrement denotes the symmetric-height zero sum of
(b^rho-a^rho)/rho, and trivialIncrement denotes
(1/2)*log[(1-b^-2)/(1-a^-2)]. The hypothesis hformula is the
EXTERNAL classical explicit formula, not a theorem imported here.

Only hformula is analytical; the factor/theta/psi_0 identity is the
already-proved native arithmetic theorem above. -/
theorem vf925FactorThetaForcing_of_explicitPsiMidDifference
    (R : ℕ) (hR : 5 ≤ R)
    (spectralIncrement trivialIncrement : ℝ)
    (hformula :
      vf925PsiMidAt ((R + 1) ^ 2) - vf925PsiMidAt (R ^ 2) =
        (2 * (R : ℝ) + 1) -
          spectralIncrement - trivialIncrement) :
    vf925FactorThetaForcing R =
      spectralIncrement + trivialIncrement +
        vf925StrictInteriorHigherPowerMass R +
        (Λ (R ^ 2) + Λ ((R + 1) ^ 2)) / 2 := by
  have hfinite :=
    vf925PsiMidSquareDiff_eq_factorTheta_plus_power_plus_halfJumps
      R hR
  unfold vf925FactorThetaForcing
  linarith

end RHLean.Analysis
