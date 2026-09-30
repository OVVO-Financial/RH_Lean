import Mathlib
import «research.VF_MID_DIRECT_SIGNED_DYNAMICS»
import RHLean.Analysis.NativePNTTransfer
import RHLean.Analysis.NativePNTNormalizedSignedRecurrence
import RHLean.Analysis.NativePNTSignedSecondSelberg
import RHLean.Analysis.NativePNTSignedSecondSelbergFactorFourBridge

/-!
# Direct weighted Selberg attack on the VF-mid endpoint discrepancy

This file stays on the direct VF-mid proof graph.

The green direct dynamics file reduces the actual square-endpoint discrepancy
to the weighted signed theta prefix plus an explicit O(R) location term.
Here we transfer that *same weighted square-band object* from theta to psi,
where the repository's exact signed Selberg recurrences are available.

No PNT-rate hypothesis, zero-free hypothesis, RH-equivalent estimate, sieve
model, or Mertens estimate is introduced. A contraction coefficient that fails
to stay uniformly below one is treated as a kill condition for this lane.
-/

noncomputable section

open scoped ArithmeticFunction.vonMangoldt BigOperators

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
  have hsq : 1 ≤ R ^ 2 := by nlinarith
  have h := nativePsi_le_theta_add_sqrt_log (R ^ 2) hsq
  unfold vfMidDirectPrimePowerEndpointCorrection
  linarith

/-- Prime-power correction at a general endpoint as an explicit
nonnegative prime sum. -/
private theorem vfMidDirect_nativePrimePowerCorrection_eq_sum (N : ℕ) :
    nativePsi N - nativeTheta N =
      ∑ p ∈ nativePrimeSet N,
        ((((p.log N : ℕ) : ℝ) - 1) * Real.log (p : ℝ)) := by
  rw [nativePsi_eq_sum_mul_log_prime]
  unfold nativeTheta
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _hp
  ring

/-- The prime-power correction psi - theta is monotone.  New primes themselves
enter with zero correction; only repeated prime powers add positive mass. -/
private theorem vfMidDirect_nativePrimePowerCorrection_monotone :
    Monotone (fun N : ℕ => nativePsi N - nativeTheta N) := by
  intro A B hAB
  rw [vfMidDirect_nativePrimePowerCorrection_eq_sum,
    vfMidDirect_nativePrimePowerCorrection_eq_sum]
  have hsubset : nativePrimeSet A ⊆ nativePrimeSet B := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpIcc, hpPrime⟩
    refine Finset.mem_filter.mpr ⟨?_, hpPrime⟩
    exact Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp hpIcc).1, (Finset.mem_Icc.mp hpIcc).2.trans hAB⟩
  calc
    (∑ p ∈ nativePrimeSet A,
        ((((p.log A : ℕ) : ℝ) - 1) * Real.log (p : ℝ))) ≤
      ∑ p ∈ nativePrimeSet A,
        ((((p.log B : ℕ) : ℝ) - 1) * Real.log (p : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpPrime : p.Prime := (Finset.mem_filter.mp hp).2
      have hlogp : 0 ≤ Real.log (p : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hpPrime.one_le)
      have hlogNat : p.log A ≤ p.log B := Nat.log_mono_right hAB
      have hlogReal :
          ((p.log A : ℕ) : ℝ) ≤ ((p.log B : ℕ) : ℝ) := by
        exact_mod_cast hlogNat
      exact mul_le_mul_of_nonneg_right
        (sub_le_sub_right hlogReal 1) hlogp
    _ ≤ ∑ p ∈ nativePrimeSet B,
        ((((p.log B : ℕ) : ℝ) - 1) * Real.log (p : ℝ)) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
      intro p hp _hpOld
      have hpPrime : p.Prime := (Finset.mem_filter.mp hp).2
      have hpB : p ≤ B :=
        (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).2
      have hlogPos : 0 < p.log B :=
        Nat.log_pos hpPrime.one_lt hpB
      have hcoefNat : 1 ≤ p.log B := by omega
      have hcoefReal : (1 : ℝ) ≤ ((p.log B : ℕ) : ℝ) := by
        exact_mod_cast hcoefNat
      have hlogp : 0 ≤ Real.log (p : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hpPrime.one_le)
      exact mul_nonneg (sub_nonneg.mpr hcoefReal) hlogp

/-- Square-endpoint prime-power correction is monotone in the square index. -/
theorem vfMidDirectPrimePowerEndpointCorrection_mono
    {R S : ℕ} (hRS : R ≤ S) :
    vfMidDirectPrimePowerEndpointCorrection R ≤
      vfMidDirectPrimePowerEndpointCorrection S := by
  unfold vfMidDirectPrimePowerEndpointCorrection
  exact vfMidDirect_nativePrimePowerCorrection_monotone
    (Nat.pow_le_pow_left hRS 2)

/-- Every square-band prime-power increment is nonnegative. -/
theorem vfMidDirectPrimePowerBandCorrection_nonneg (R : ℕ) :
    0 ≤ vfMidDirectPrimePowerBandCorrection R := by
  unfold vfMidDirectPrimePowerBandCorrection
  exact sub_nonneg.mpr
    (vfMidDirectPrimePowerEndpointCorrection_mono (Nat.le_succ R))

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

/-- Exact direct VF-mid endpoint decomposition in psi coordinates.

This is not a new route: it is the #824 endpoint identity with the exact
theta-to-psi transfer substituted in place. -/
theorem vfMidDirectSquareEndpointError_eq_base_add_psi_sub_primePower_add_position
    (R : ℕ) (hR : 2 ≤ R) :
    vfMidDirectSquareEndpointError R =
      vfMidDirectSquareEndpointError 2 +
        vfMidDirectPsiWeightedPrefix R -
        vfMidDirectPrimePowerWeightedPrefix R +
        vfMidDirectLogPositionPrefix R := by
  have hD :=
    vfMidDirectSquareEndpointError_eq_base_add_theta_add_position R hR
  have hpsi := vfMidDirectPsiWeightedPrefix_eq_theta_add_primePower R
  linarith

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

/-- The total normalized first-Selberg feedback mass is already almost the
full endpoint logarithm.  At N = R^2 it differs from
log N - 1 + 1/N by at most log N / N.

Consequently, dividing the recurrence by log N cannot produce a uniform
mass-based contraction coefficient c < 1: the available coefficient tends
to one with the scale. -/
theorem vfMidDirectPsiSquare_normalizedWeightMass_near_full
    (R : ℕ) (hR : 1 ≤ R) :
    |(∑ d ∈ Finset.Icc 1 (R ^ 2),
        nativePNTNormalizedFloorWeight (R ^ 2) d) -
        (Real.log (((R ^ 2 : ℕ) : ℝ)) - 1 +
          1 / (((R ^ 2 : ℕ) : ℝ)))| ≤
      Real.log (((R ^ 2 : ℕ) : ℝ)) / (((R ^ 2 : ℕ) : ℝ)) := by
  exact nativePNTNormalizedFloorWeight_sum_sub_main_abs_le
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

/-- The true signed K2 summatory mode tracks the same square-endpoint psi error
with a log weight, up to a merely linear-in-N remainder.  Thus the existing
second-Selberg kernel does not by itself supply an independent strict
contraction of the coherent endpoint error. -/
theorem vfMidDirectPsiSquare_signedK2_tracks_endpoint
    (R : ℕ) (hR : 2 ≤ R) :
    |nativePNTSignedK2Summatory (R ^ 2) +
        2 * vfMidDirectPsiEndpointError R *
          Real.log (((R ^ 2 : ℕ) : ℝ))| ≤
      (4 * (Real.log 4 + 2) + 172) * (((R ^ 2 : ℕ) : ℝ)) := by
  rw [vfMidDirectPsiEndpointError_eq_nativePNTError]
  exact nativePNTSignedK2Summatory_add_two_error_log_abs_le
    (R ^ 2) (by nlinarith)

end RHLean.Analysis
