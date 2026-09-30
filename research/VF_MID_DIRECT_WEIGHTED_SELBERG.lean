import Mathlib
import «research.VF_MID_DIRECT_SIGNED_DYNAMICS»
import RHLean.Analysis.NativePNTTransfer
import RHLean.Analysis.NativePNTNormalizedSignedRecurrence
import RHLean.Analysis.NativePNTSignedSecondSelberg

/-!
# Direct weighted Selberg attack on the VF-mid endpoint discrepancy

This file stays on the direct VF-mid proof graph.

The green direct dynamics file reduces the actual square-endpoint discrepancy
to the weighted signed theta prefix plus an explicit O(R) location term.
Here we transfer that *same weighted square-band object* from theta to psi,
where the repository's exact signed Selberg recurrences are available.

No PNT-rate hypothesis, zero-free hypothesis, RH-equivalent estimate, sieve
model, or Mertens estimate is introduced.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

/-- Square-endpoint psi error, in exactly the same coordinate as the direct
theta endpoint error. -/
def vfMidDirectPsiEndpointError (R : ℕ) : ℝ :=
  nativePsi (R ^ 2) - (R : ℝ) ^ 2

/-- Prime-power correction between psi and theta at the square endpoint. -/
def vfMidDirectPrimePowerEndpointCorrection (R : ℕ) : ℝ :=
  nativePsi (R ^ 2) - nativeTheta (R ^ 2)

/-- Exact endpoint decomposition psi-error = theta-error + prime-power error. -/
theorem vfMidDirectPsiEndpointError_eq_theta_add_primePower (R : ℕ) :
    vfMidDirectPsiEndpointError R =
      vfMidDirectThetaEndpointError R +
        vfMidDirectPrimePowerEndpointCorrection R := by
  unfold vfMidDirectPsiEndpointError vfMidDirectThetaEndpointError
    vfMidDirectPrimePowerEndpointCorrection
  ring

/-- The prime-power correction is nonnegative. -/
theorem vfMidDirectPrimePowerEndpointCorrection_nonneg (R : ℕ) :
    0 ≤ vfMidDirectPrimePowerEndpointCorrection R := by
  unfold vfMidDirectPrimePowerEndpointCorrection
  exact sub_nonneg.mpr (nativeTheta_le_psi (R ^ 2))

/-- The existing elementary prime-power estimate, specialized to a square
endpoint.  This is an unconditional square-root-scale endpoint estimate. -/
theorem vfMidDirectPrimePowerEndpointCorrection_le_sqrt_log
    (R : ℕ) (hR : 1 ≤ R) :
    vfMidDirectPrimePowerEndpointCorrection R ≤
      (Nat.sqrt (R ^ 2) : ℝ) * Real.log ((R ^ 2 : ℕ) : ℝ) := by
  have hsq : 1 ≤ R ^ 2 := by positivity
  have h := nativePsi_le_theta_add_sqrt_log (R ^ 2) hsq
  unfold vfMidDirectPrimePowerEndpointCorrection
  linarith

/-- Centered psi mass entering one square band. -/
def vfMidDirectPsiBandError (R : ℕ) : ℝ :=
  vfMidDirectPsiEndpointError (R + 1) - vfMidDirectPsiEndpointError R

/-- Prime-power increment entering one square band. -/
def vfMidDirectPrimePowerBandCorrection (R : ℕ) : ℝ :=
  vfMidDirectPrimePowerEndpointCorrection (R + 1) -
    vfMidDirectPrimePowerEndpointCorrection R

/-- Exact per-band transfer from theta to psi. -/
theorem vfMidDirectPsiBandError_eq_theta_add_primePower (R : ℕ) :
    vfMidDirectPsiBandError R =
      vfMidDirectThetaBandError R +
        vfMidDirectPrimePowerBandCorrection R := by
  unfold vfMidDirectPsiBandError vfMidDirectPrimePowerBandCorrection
  rw [vfMidDirectPsiEndpointError_eq_theta_add_primePower,
    vfMidDirectPsiEndpointError_eq_theta_add_primePower,
    vfMidDirectThetaBandError_eq_endpoint_diff]
  ring

/-- The direct square-weighted psi prefix. -/
def vfMidDirectPsiWeightedPrefix (R : ℕ) : ℝ :=
  ∑ r ∈ Finset.Ico 2 R,
    vfMidDirectPsiBandError r / Real.log (vfMidBandMidpoint r)

/-- The prime-power correction in the exact same square weights. -/
def vfMidDirectPrimePowerWeightedPrefix (R : ℕ) : ℝ :=
  ∑ r ∈ Finset.Ico 2 R,
    vfMidDirectPrimePowerBandCorrection r /
      Real.log (vfMidBandMidpoint r)

/-- Exact weighted transfer: psi prefix = theta prefix + prime-power prefix. -/
theorem vfMidDirectPsiWeightedPrefix_eq_theta_add_primePower (R : ℕ) :
    vfMidDirectPsiWeightedPrefix R =
      vfMidDirectThetaWeightedPrefix R +
        vfMidDirectPrimePowerWeightedPrefix R := by
  unfold vfMidDirectPsiWeightedPrefix vfMidDirectThetaWeightedPrefix
    vfMidDirectPrimePowerWeightedPrefix
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _hr
  rw [vfMidDirectPsiBandError_eq_theta_add_primePower]
  ring

/-- The square-endpoint psi error is literally the repository's native PNT
error at the square endpoint. -/
theorem vfMidDirectPsiEndpointError_eq_nativePNTError (R : ℕ) :
    vfMidDirectPsiEndpointError R = nativePNTError (R ^ 2) := by
  unfold vfMidDirectPsiEndpointError nativePNTError
  push_cast
  ring

/-- Existing signed first-Selberg recurrence, specialized exactly to square
endpoints.  No estimate is weakened or replaced. -/
theorem vfMidDirectPsiSquare_signedSelberg
    (R : ℕ) (hR : 2 ≤ R) :
    |vfMidDirectPsiEndpointError R * Real.log ((R ^ 2 : ℕ) : ℝ) +
        ∑ d ∈ Finset.Icc 1 (R ^ 2),
          Λ d * nativePNTError ((R ^ 2) / d)| ≤
      (3 * (Real.log 4 + 2) + 173) * ((R ^ 2 : ℕ) : ℝ) := by
  rw [vfMidDirectPsiEndpointError_eq_nativePNTError]
  exact nativePNTError_signed_log_sum_abs_le (R ^ 2) (by
    nlinarith)

/-- Normalized signed Selberg recurrence on the same square endpoints. -/
theorem vfMidDirectPsiSquare_normalizedSignedSelberg
    (R : ℕ) (hR : 2 ≤ R) :
    |nativePNTNormalizedError (R ^ 2) *
          Real.log ((R ^ 2 : ℕ) : ℝ) +
        nativePNTNormalizedFloorAverage (R ^ 2)| ≤
      nativePNTNormalizedSelbergConstant := by
  exact nativePNTNormalized_signed_first_recurrence_average_abs_le
    (R ^ 2) (by nlinarith)

/-- Signed second-Selberg identity specialized to square endpoints.  This is
recorded here so the direct weighted attack can test whether the second kernel
gives genuine strict contraction instead of merely another equivalent
coordinate. -/
theorem vfMidDirectPsiSquare_signedSecondSelberg (R : ℕ) :
    nativePNTError (R ^ 2) *
        (Real.log (((R ^ 2 : ℕ) : ℝ))) ^ 2 =
      nativePNTSignedSelbergRemainder (R ^ 2) *
          Real.log (((R ^ 2 : ℕ) : ℝ)) -
        nativePNTLambdaSignedSelbergRemainderMass (R ^ 2) +
        nativePNTSignedSecondSelbergKernelErrorMass (R ^ 2) -
        nativePNTLambdaFloorLogSignedDefectMass (R ^ 2) := by
  exact nativePNTError_mul_log_sq_eq_signedSecondSelberg (R ^ 2)

end RHLean.Analysis
