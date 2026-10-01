import Mathlib
import «research.VF_MID_MIDPOINT_COMPLEMENT_DISPERSION»
import «research.VF_MID_SQUARE_BAND_COMPOSITE_BRIDGE»

/-!
# VF-mid square-block uniformity and coherent accumulation

This file stays on the direct

  D_R = pi(R^2) - VF_mid(R^2)

architecture.

The empirical square-block uniformity picture motivates a finite spatial-bias
coordinate at the geometric midpoint.  We do not assume or prove exact
uniformity here.  Instead we expose exactly what midpoint bias does to the
direct VF band error and exactly where coherent accumulation can occur.

For the R-th square block let

  e_R = P_R - V_R

be the direct VF-mid band error, and let U_R be the left-half prime excess over
one half of the realized block prime population.  The two half-block VF errors
satisfy the exact identities

  e_R^L + e_R^R = e_R,
  e_R^L - e_R^R = 2 U_R,

hence

  e_R^L = e_R / 2 + U_R,
  e_R^R = e_R / 2 - U_R.

Thus U_R = 0 removes the entire within-block spatial phase bias: both halves
carry exactly one half of the direct block error.

Across blocks, with D_(R+1) = D_R + e_R, the exact energy increment is

  D_(R+1)^2 - D_R^2 = 2 D_R e_R + e_R^2.

The cumulative term sum D_R e_R is therefore the precise coherent-accumulation
channel.  The finite telescope below makes "zero/nonpositive persistent
correlation" a kernel-checked condition, without claiming that empirical
uniformity already proves that cross-block decorrelation theorem.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

/-! ## 1. Midpoint spatial-bias coordinate -/

/-- Real prime population of the complete R-th square block. -/
def vfMidSquareBlockPrimeTotal (R : ℕ) : ℝ :=
  ((vfMidSquareWheelPrimes R).card : ℝ)

/-- Prime population in the left half of the square block, through R^2 + R. -/
def vfMidSquareBlockPrimeLeft (R : ℕ) : ℝ :=
  ((vfMidSquareWheelPrimePrefix R (R ^ 2 + R)).card : ℝ)

/-- Prime population in the right half, expressed as total minus left. -/
def vfMidSquareBlockPrimeRight (R : ℕ) : ℝ :=
  vfMidSquareBlockPrimeTotal R - vfMidSquareBlockPrimeLeft R

/-- Midpoint spatial bias: left-half prime excess over one half of the realized
block prime population.  Exact midpoint uniformity is U_R = 0. -/
def vfMidSquareBlockMidpointBias (R : ℕ) : ℝ :=
  vfMidSquareBlockPrimeLeft R - vfMidSquareBlockPrimeTotal R / 2

/-- Composite midpoint bias in the same normalization. -/
def vfMidSquareBlockCompositeMidpointBias (R : ℕ) : ℝ :=
  ((vfMidSquareWheelCompositePrefix R (R ^ 2 + R)).card : ℝ) -
    ((vfMidSquareWheelComposites R).card : ℝ) / 2

/-- Exact theoretical midpoint-unbiased condition.  This is an interface for
the empirical uniformity mechanism, not an unconditional theorem. -/
def VFMidSquareBlockMidpointUnbiased (R : ℕ) : Prop :=
  vfMidSquareBlockMidpointBias R = 0

/-- Prime and composite midpoint biases are exact negatives. -/
theorem vfMidSquareBlockMidpointBias_eq_neg_composite (R : ℕ) :
    vfMidSquareBlockMidpointBias R =
      -vfMidSquareBlockCompositeMidpointBias R := by
  exact vfMidSquareWheel_midpoint_prime_composite_discrepancy R

/-- Left-minus-right prime population is exactly twice the midpoint bias.
This is the finite algebraic version of the paper's above/below-midpoint ratio
having no directional skew. -/
theorem vfMidSquareBlockPrimeLeft_sub_right_eq_two_mul_bias (R : ℕ) :
    vfMidSquareBlockPrimeLeft R - vfMidSquareBlockPrimeRight R =
      2 * vfMidSquareBlockMidpointBias R := by
  unfold vfMidSquareBlockPrimeRight vfMidSquareBlockMidpointBias
  ring

/-! ## 2. Exact removal of within-block VF spatial bias -/

/-- VF error carried by the left half of the square block. -/
def vfMidSquareBlockLeftVFError (R : ℕ) : ℝ :=
  vfMidSquareBlockPrimeLeft R - vfMidBandMass R / 2

/-- VF error carried by the right half of the square block. -/
def vfMidSquareBlockRightVFError (R : ℕ) : ℝ :=
  vfMidSquareBlockPrimeRight R - vfMidBandMass R / 2

/-- The two half-block errors reassemble to the direct full-block VF error. -/
theorem vfMidSquareBlock_left_add_right_error_eq_bandError (R : ℕ) :
    vfMidSquareBlockLeftVFError R + vfMidSquareBlockRightVFError R =
      vfMidSquareBandError R := by
  unfold vfMidSquareBlockLeftVFError vfMidSquareBlockRightVFError
    vfMidSquareBlockPrimeRight vfMidSquareBlockPrimeTotal
    vfMidSquareBlockPrimeLeft vfMidSquareBandError
    vfMidSquareWheelPrimes vfMidSquareBandPrimes
    vfMidSquareWheelSites vfMidSquareBandSites
  ring

/-- The left-right VF-error difference is exactly twice the spatial bias. -/
theorem vfMidSquareBlock_left_sub_right_error_eq_two_mul_bias (R : ℕ) :
    vfMidSquareBlockLeftVFError R - vfMidSquareBlockRightVFError R =
      2 * vfMidSquareBlockMidpointBias R := by
  unfold vfMidSquareBlockLeftVFError vfMidSquareBlockRightVFError
    vfMidSquareBlockPrimeRight vfMidSquareBlockMidpointBias
  ring

/-- Exact bias decomposition of the left half:
e_R^L = e_R/2 + U_R. -/
theorem vfMidSquareBlock_leftVFError_eq_half_band_add_bias (R : ℕ) :
    vfMidSquareBlockLeftVFError R =
      vfMidSquareBandError R / 2 + vfMidSquareBlockMidpointBias R := by
  unfold vfMidSquareBlockLeftVFError vfMidSquareBlockMidpointBias
    vfMidSquareBlockPrimeTotal vfMidSquareBlockPrimeLeft
    vfMidSquareBandError vfMidSquareWheelPrimes vfMidSquareBandPrimes
    vfMidSquareWheelSites vfMidSquareBandSites
  ring

/-- Exact bias decomposition of the right half:
e_R^R = e_R/2 - U_R. -/
theorem vfMidSquareBlock_rightVFError_eq_half_band_sub_bias (R : ℕ) :
    vfMidSquareBlockRightVFError R =
      vfMidSquareBandError R / 2 - vfMidSquareBlockMidpointBias R := by
  unfold vfMidSquareBlockRightVFError vfMidSquareBlockPrimeRight
    vfMidSquareBlockMidpointBias vfMidSquareBlockPrimeTotal
    vfMidSquareBlockPrimeLeft vfMidSquareBandError
    vfMidSquareWheelPrimes vfMidSquareBandPrimes
    vfMidSquareWheelSites vfMidSquareBandSites
  ring

/-- Exact midpoint uniformity removes all left-half spatial bias. -/
theorem vfMidSquareBlock_leftVFError_eq_half_of_unbiased
    {R : ℕ} (hU : VFMidSquareBlockMidpointUnbiased R) :
    vfMidSquareBlockLeftVFError R = vfMidSquareBandError R / 2 := by
  rw [vfMidSquareBlock_leftVFError_eq_half_band_add_bias]
  have hb : vfMidSquareBlockMidpointBias R = 0 := by
    simpa [VFMidSquareBlockMidpointUnbiased] using hU
  rw [hb]
  ring

/-- Exact midpoint uniformity removes all right-half spatial bias. -/
theorem vfMidSquareBlock_rightVFError_eq_half_of_unbiased
    {R : ℕ} (hU : VFMidSquareBlockMidpointUnbiased R) :
    vfMidSquareBlockRightVFError R = vfMidSquareBandError R / 2 := by
  rw [vfMidSquareBlock_rightVFError_eq_half_band_sub_bias]
  have hb : vfMidSquareBlockMidpointBias R = 0 := by
    simpa [VFMidSquareBlockMidpointUnbiased] using hU
  rw [hb]
  ring

/-- Approximate uniformity controls the left-half departure from half of the
full band error with no loss. -/
theorem abs_vfMidSquareBlock_leftVFError_sub_half_eq_abs_bias (R : ℕ) :
    |vfMidSquareBlockLeftVFError R - vfMidSquareBandError R / 2| =
      |vfMidSquareBlockMidpointBias R| := by
  rw [vfMidSquareBlock_leftVFError_eq_half_band_add_bias]
  ring_nf

/-- Approximate uniformity controls the right-half departure with the same
magnitude. -/
theorem abs_vfMidSquareBlock_rightVFError_sub_half_eq_abs_bias (R : ℕ) :
    |vfMidSquareBlockRightVFError R - vfMidSquareBandError R / 2| =
      |vfMidSquareBlockMidpointBias R| := by
  have h :
      vfMidSquareBlockRightVFError R - vfMidSquareBandError R / 2 =
        -vfMidSquareBlockMidpointBias R := by
    rw [vfMidSquareBlock_rightVFError_eq_half_band_sub_bias]
    ring
  rw [h, abs_neg]

/-! ## 3. Finite lag correlation of the spatial phase -/

/-- Finite lag-h autocorrelation sum of the midpoint spatial-bias coordinate. -/
def vfMidSquareBlockBiasLagCorrelation (R h n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n,
    vfMidSquareBlockMidpointBias (R + k) *
      vfMidSquareBlockMidpointBias (R + k + h)

/-- Finite lag-h autocorrelation sum of the composite midpoint-bias coordinate. -/
def vfMidSquareBlockCompositeBiasLagCorrelation (R h n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n,
    vfMidSquareBlockCompositeMidpointBias (R + k) *
      vfMidSquareBlockCompositeMidpointBias (R + k + h)

/-- **Prime/composite correlation transfer.**  Because the midpoint biases are
exact negatives block by block, their finite lag correlations are exactly
equal.  Hence proving decorrelation on the dense composite population is
literally sufficient for the prime population. -/
theorem vfMidSquareBlockBiasLagCorrelation_eq_composite
    (R h n : ℕ) :
    vfMidSquareBlockBiasLagCorrelation R h n =
      vfMidSquareBlockCompositeBiasLagCorrelation R h n := by
  unfold vfMidSquareBlockBiasLagCorrelation
    vfMidSquareBlockCompositeBiasLagCorrelation
  apply Finset.sum_congr rfl
  intro k hk
  rw [vfMidSquareBlockMidpointBias_eq_neg_composite,
    vfMidSquareBlockMidpointBias_eq_neg_composite]
  ring

/-- Any exact zero-correlation theorem for composite midpoint bias transfers
unchanged to prime midpoint bias. -/
theorem vfMidSquareBlockBiasLagCorrelation_eq_zero_of_composite
    {R h n : ℕ}
    (hC : vfMidSquareBlockCompositeBiasLagCorrelation R h n = 0) :
    vfMidSquareBlockBiasLagCorrelation R h n = 0 := by
  rw [vfMidSquareBlockBiasLagCorrelation_eq_composite]
  exact hC

/-- Any absolute composite-correlation bound transfers with the same constant. -/
theorem abs_vfMidSquareBlockBiasLagCorrelation_le_of_composite
    {R h n : ℕ} {B : ℝ}
    (hC : |vfMidSquareBlockCompositeBiasLagCorrelation R h n| ≤ B) :
    |vfMidSquareBlockBiasLagCorrelation R h n| ≤ B := by
  rw [vfMidSquareBlockBiasLagCorrelation_eq_composite]
  exact hC

/-- If every source block in a finite window is exactly midpoint-unbiased, every
finite lag correlation sourced from that window is exactly zero. -/
theorem vfMidSquareBlockBiasLagCorrelation_eq_zero_of_unbiased
    {R h n : ℕ}
    (hU : ∀ k < n, VFMidSquareBlockMidpointUnbiased (R + k)) :
    vfMidSquareBlockBiasLagCorrelation R h n = 0 := by
  unfold vfMidSquareBlockBiasLagCorrelation
  apply Finset.sum_eq_zero
  intro k hk
  have hklt : k < n := Finset.mem_range.mp hk
  have hb : vfMidSquareBlockMidpointBias (R + k) = 0 := by
    simpa [VFMidSquareBlockMidpointUnbiased] using hU k hklt
  rw [hb]
  ring

/-! ## 4. Direct VF coherent-accumulation channel -/

/-- Pointwise correlation between accumulated endpoint discrepancy D_R and the
new direct band error e_R. -/
def vfMidSquareEndpointAccumulationCorrelation (R : ℕ) : ℝ :=
  vfMidSquareEndpointError R * vfMidSquareBandError R

/-- Cumulative coherent-correlation term over n consecutive square blocks. -/
def vfMidSquareEndpointAccumulationCorrelationSum (R n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n,
    vfMidSquareEndpointAccumulationCorrelation (R + k)

/-- Cumulative quadratic energy of the raw band errors over the same window. -/
def vfMidSquareBandErrorEnergySum (R n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, vfMidSquareBandError (R + k) ^ 2

/-- Exact one-block energy update in correlation coordinates. -/
theorem vfMidSquareEndpointError_sq_succ_eq_correlation
    (R : ℕ) (hR : 2 ≤ R) :
    vfMidSquareEndpointError (R + 1) ^ 2 -
        vfMidSquareEndpointError R ^ 2 =
      2 * vfMidSquareEndpointAccumulationCorrelation R +
        vfMidSquareBandError R ^ 2 := by
  rw [vfMidSquareEndpointError_sq_succ R hR]
  unfold vfMidSquareEndpointAccumulationCorrelation
  ring

/-- **Exact finite coherent-accumulation telescope.**

The endpoint-error energy after n blocks equals initial energy plus twice the
cumulative D_R*e_R correlation plus the unavoidable raw increment energy. -/
theorem vfMidSquareEndpointError_energy_telescope
    (R n : ℕ) (hR : 2 ≤ R) :
    vfMidSquareEndpointError (R + n) ^ 2 -
        vfMidSquareEndpointError R ^ 2 =
      2 * vfMidSquareEndpointAccumulationCorrelationSum R n +
        vfMidSquareBandErrorEnergySum R n := by
  induction n with
  | zero =>
      simp [vfMidSquareEndpointAccumulationCorrelationSum,
        vfMidSquareBandErrorEnergySum]
  | succ n ih =>
      have hRn : 2 ≤ R + n := by omega
      have hstep :=
        vfMidSquareEndpointError_sq_succ_eq_correlation (R + n) hRn
      rw [Nat.add_succ]
      calc
        vfMidSquareEndpointError (R + n + 1) ^ 2 -
              vfMidSquareEndpointError R ^ 2 =
            (vfMidSquareEndpointError (R + n + 1) ^ 2 -
                vfMidSquareEndpointError (R + n) ^ 2) +
              (vfMidSquareEndpointError (R + n) ^ 2 -
                vfMidSquareEndpointError R ^ 2) := by ring
        _ =
            (2 * vfMidSquareEndpointAccumulationCorrelation (R + n) +
                vfMidSquareBandError (R + n) ^ 2) +
              (2 * vfMidSquareEndpointAccumulationCorrelationSum R n +
                vfMidSquareBandErrorEnergySum R n) := by rw [hstep, ih]
        _ =
            2 * vfMidSquareEndpointAccumulationCorrelationSum R (n + 1) +
              vfMidSquareBandErrorEnergySum R (n + 1) := by
          unfold vfMidSquareEndpointAccumulationCorrelationSum
            vfMidSquareBandErrorEnergySum
          rw [Finset.sum_range_succ, Finset.sum_range_succ]
          ring

/-- With exactly zero cumulative D_R*e_R correlation, there is no coherent
cross-block contribution to endpoint-error energy. -/
theorem vfMidSquareEndpointError_energy_telescope_of_zero_correlation
    (R n : ℕ) (hR : 2 ≤ R)
    (hzero : vfMidSquareEndpointAccumulationCorrelationSum R n = 0) :
    vfMidSquareEndpointError (R + n) ^ 2 -
        vfMidSquareEndpointError R ^ 2 =
      vfMidSquareBandErrorEnergySum R n := by
  rw [vfMidSquareEndpointError_energy_telescope R n hR, hzero]
  ring

/-- If the cumulative D_R*e_R correlation is nonpositive, coherent alignment
cannot increase endpoint-error energy beyond the raw band-error energy. -/
theorem vfMidSquareEndpointError_sq_le_of_nonpos_correlation
    (R n : ℕ) (hR : 2 ≤ R)
    (hcorr : vfMidSquareEndpointAccumulationCorrelationSum R n ≤ 0) :
    vfMidSquareEndpointError (R + n) ^ 2 ≤
      vfMidSquareEndpointError R ^ 2 + vfMidSquareBandErrorEnergySum R n := by
  have htel := vfMidSquareEndpointError_energy_telescope R n hR
  linarith

end RHLean.Analysis
