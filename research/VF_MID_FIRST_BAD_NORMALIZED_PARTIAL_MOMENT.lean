import Mathlib
import «research.VF_MID_FIRST_BAD_PARTIAL_MOMENT_SYNTHESIS»
import «research.NNS_ZERO_TARGET_NORMALIZED_STOKES»

/-!
# NNS-normalized first-bad partial-moment budget

The NNS implementation normalizes each partial-moment covariance cell by the
total quadrant mass

  CUPM + CLPM + DUPM + DLPM.

At target zero this denominator is exactly |x| |y|.  This file applies the same
normalization to the anchored #896 first-bad carrier.

The result is an exact factorization

  anchored excess
    = normalized covariance * total co/divergent mass,

with

  total mass = (|D| + sum |a_i|)^2.

No mean target, Schur projection, triangle bound on the signed numerator, or
new prime-distribution estimate is introduced.

For the literal VF odd-seat carrier, every seat has magnitude at most one from
R >= 3 and there are exactly R seats.  Consequently, at a K=2 first-bad
successor, the compiled all-depth owner-tree constant 1/2 is already strong
enough from R >= 8 to imply the terminal radial budget.  Thus the remaining
normalized target is dimensionless:

  normalized anchored zero-target covariance <= 1/2.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic RHLean.Proof

attribute [local instance] Classical.propDecidable

def vfMidAnchoredZeroTargetTotalMass
    {α : Type*} [DecidableEq α]
    (s : Finset α) (a : α → ℝ) (D : ℝ) : ℝ :=
  vfMidAnchoredZeroTargetCoPartialGram s a D +
    vfMidAnchoredZeroTargetDivergentGram s a D

def vfMidAnchoredZeroTargetNNSNormalizedCovariance
    {α : Type*} [DecidableEq α]
    (s : Finset α) (a : α → ℝ) (D : ℝ) : ℝ :=
  nnsZeroTargetNormalizedCovariance
    (vfMidAnchoredZeroTargetCoPartialGram s a D)
    (vfMidAnchoredZeroTargetDivergentGram s a D)

private theorem zeroTargetCoPartialGram_nonneg_local
    {α : Type*} [DecidableEq α]
    (s : Finset α) (a : α → ℝ) :
    0 ≤ zeroTargetCoPartialGram s a := by
  unfold zeroTargetCoPartialGram
  apply Finset.sum_nonneg
  intro i _hi
  apply Finset.sum_nonneg
  intro j _hj
  exact zeroTargetCoPartialPair_nonneg _ _

private theorem zeroTargetDivergentGram_nonneg_local
    {α : Type*} [DecidableEq α]
    (s : Finset α) (a : α → ℝ) :
    0 ≤ zeroTargetDivergentGram s a := by
  unfold zeroTargetDivergentGram
  apply Finset.sum_nonneg
  intro i _hi
  apply Finset.sum_nonneg
  intro j _hj
  exact zeroTargetDivergentPair_nonneg _ _

theorem vfMidAnchoredZeroTargetCoPartialGram_nonneg
    {α : Type*} [DecidableEq α]
    (s : Finset α) (a : α → ℝ) (D : ℝ) :
    0 ≤ vfMidAnchoredZeroTargetCoPartialGram s a D := by
  unfold vfMidAnchoredZeroTargetCoPartialGram
  have hgram := zeroTargetCoPartialGram_nonneg_local s a
  have hcross :
      0 ≤ ∑ i ∈ s, zeroTargetCoPartialPair (-D) (a i) := by
    apply Finset.sum_nonneg
    intro i _hi
    exact zeroTargetCoPartialPair_nonneg _ _
  positivity

theorem vfMidAnchoredZeroTargetDivergentGram_nonneg
    {α : Type*} [DecidableEq α]
    (s : Finset α) (a : α → ℝ) (D : ℝ) :
    0 ≤ vfMidAnchoredZeroTargetDivergentGram s a D := by
  unfold vfMidAnchoredZeroTargetDivergentGram
  have hgram := zeroTargetDivergentGram_nonneg_local s a
  have hcross :
      0 ≤ ∑ i ∈ s, zeroTargetDivergentPair (-D) (a i) := by
    apply Finset.sum_nonneg
    intro i _hi
    exact zeroTargetDivergentPair_nonneg _ _
  positivity

theorem zeroTargetCoPartialGram_add_divergentGram_eq_absSum_sq
    {α : Type*} [DecidableEq α]
    (s : Finset α) (a : α → ℝ) :
    zeroTargetCoPartialGram s a + zeroTargetDivergentGram s a =
      (∑ i ∈ s, |a i|) ^ 2 := by
  unfold zeroTargetCoPartialGram zeroTargetDivergentGram
  rw [← Finset.sum_add_distrib]
  calc
    (∑ i ∈ s,
      ((∑ j ∈ s, zeroTargetCoPartialPair (a i) (a j)) +
        ∑ j ∈ s, zeroTargetDivergentPair (a i) (a j))) =
      ∑ i ∈ s, ∑ j ∈ s,
        (zeroTargetCoPartialPair (a i) (a j) +
          zeroTargetDivergentPair (a i) (a j)) := by
            apply Finset.sum_congr rfl
            intro i _hi
            rw [Finset.sum_add_distrib]
    _ = ∑ i ∈ s, ∑ j ∈ s, |a i| * |a j| := by
          apply Finset.sum_congr rfl
          intro i _hi
          apply Finset.sum_congr rfl
          intro j _hj
          exact zeroTargetCoPartial_add_divergent_eq_abs_mul_abs (a i) (a j)
    _ = (∑ i ∈ s, |a i|) ^ 2 := by
          calc
            (∑ i ∈ s, ∑ j ∈ s, |a i| * |a j|) =
              ∑ i ∈ s, |a i| * (∑ j ∈ s, |a j|) := by
                apply Finset.sum_congr rfl
                intro i _hi
                rw [Finset.mul_sum]
            _ = (∑ i ∈ s, |a i|) * (∑ j ∈ s, |a j|) := by
                rw [Finset.sum_mul]
            _ = (∑ i ∈ s, |a i|) ^ 2 := by ring

theorem vfMidAnchoredZeroTarget_crossTotal_eq
    {α : Type*} [DecidableEq α]
    (s : Finset α) (a : α → ℝ) (D : ℝ) :
    (∑ i ∈ s, zeroTargetCoPartialPair (-D) (a i)) +
        (∑ i ∈ s, zeroTargetDivergentPair (-D) (a i)) =
      |D| * (∑ i ∈ s, |a i|) := by
  rw [← Finset.sum_add_distrib]
  calc
    (∑ i ∈ s,
      (zeroTargetCoPartialPair (-D) (a i) +
        zeroTargetDivergentPair (-D) (a i))) =
      ∑ i ∈ s, |-D| * |a i| := by
        apply Finset.sum_congr rfl
        intro i _hi
        exact zeroTargetCoPartial_add_divergent_eq_abs_mul_abs (-D) (a i)
    _ = ∑ i ∈ s, |D| * |a i| := by
        simp only [abs_neg]
    _ = |D| * (∑ i ∈ s, |a i|) := by
        rw [Finset.mul_sum]

/-- Exact NNS denominator of the anchored all-pairs carrier. -/
theorem vfMidAnchoredZeroTargetTotalMass_eq_absSum_sq
    {α : Type*} [DecidableEq α]
    (s : Finset α) (a : α → ℝ) (D : ℝ) :
    vfMidAnchoredZeroTargetTotalMass s a D =
      (|D| + ∑ i ∈ s, |a i|) ^ 2 := by
  have hgram :=
    zeroTargetCoPartialGram_add_divergentGram_eq_absSum_sq s a
  have hcross := vfMidAnchoredZeroTarget_crossTotal_eq s a D
  unfold vfMidAnchoredZeroTargetTotalMass
    vfMidAnchoredZeroTargetCoPartialGram
    vfMidAnchoredZeroTargetDivergentGram
  rw [show D ^ 2 = |D| ^ 2 by simpa [sq_abs]]
  calc
    zeroTargetCoPartialGram s a +
          2 * (∑ i ∈ s, zeroTargetCoPartialPair (-D) (a i)) +
          |D| ^ 2 +
        (zeroTargetDivergentGram s a +
          2 * (∑ i ∈ s, zeroTargetDivergentPair (-D) (a i))) =
      (zeroTargetCoPartialGram s a + zeroTargetDivergentGram s a) +
        2 * ((∑ i ∈ s, zeroTargetCoPartialPair (-D) (a i)) +
          (∑ i ∈ s, zeroTargetDivergentPair (-D) (a i))) +
        |D| ^ 2 := by ring
    _ = (∑ i ∈ s, |a i|) ^ 2 +
        2 * (|D| * (∑ i ∈ s, |a i|)) + |D| ^ 2 := by
          rw [hgram, hcross]
    _ = (|D| + ∑ i ∈ s, |a i|) ^ 2 := by ring

theorem vfMidAnchoredZeroTargetNNSNormalizedCovariance_bounds
    {α : Type*} [DecidableEq α]
    (s : Finset α) (a : α → ℝ) (D : ℝ) :
    -1 ≤ vfMidAnchoredZeroTargetNNSNormalizedCovariance s a D ∧
      vfMidAnchoredZeroTargetNNSNormalizedCovariance s a D ≤ 1 := by
  unfold vfMidAnchoredZeroTargetNNSNormalizedCovariance
  exact nnsZeroTargetNormalizedCovariance_bounds
    (vfMidAnchoredZeroTargetCoPartialGram_nonneg s a D)
    (vfMidAnchoredZeroTargetDivergentGram_nonneg s a D)

theorem vfMidAnchoredZeroTargetNNSNormalizedCovariance_mul_total
    {α : Type*} [DecidableEq α]
    (s : Finset α) (a : α → ℝ) (D : ℝ) :
    vfMidAnchoredZeroTargetNNSNormalizedCovariance s a D *
        vfMidAnchoredZeroTargetTotalMass s a D =
      ((∑ i ∈ s, a i) - D) ^ 2 := by
  have hco := vfMidAnchoredZeroTargetCoPartialGram_nonneg s a D
  have hdiv := vfMidAnchoredZeroTargetDivergentGram_nonneg s a D
  calc
    vfMidAnchoredZeroTargetNNSNormalizedCovariance s a D *
        vfMidAnchoredZeroTargetTotalMass s a D =
      vfMidAnchoredZeroTargetCoPartialGram s a D -
        vfMidAnchoredZeroTargetDivergentGram s a D := by
          unfold vfMidAnchoredZeroTargetNNSNormalizedCovariance
            vfMidAnchoredZeroTargetTotalMass
          exact nnsZeroTargetNormalizedCovariance_mul_total hco hdiv
    _ = ((∑ i ∈ s, a i) - D) ^ 2 :=
      vfMidAnchoredZeroTarget_excess_eq_sub_sq s a D

theorem vfMidAnchoredZeroTargetNNSNormalizedCovariance_nonneg
    {α : Type*} [DecidableEq α]
    (s : Finset α) (a : α → ℝ) (D : ℝ) :
    0 ≤ vfMidAnchoredZeroTargetNNSNormalizedCovariance s a D := by
  unfold vfMidAnchoredZeroTargetNNSNormalizedCovariance
  by_cases hzero :
      vfMidAnchoredZeroTargetCoPartialGram s a D +
        vfMidAnchoredZeroTargetDivergentGram s a D = 0
  · simp [nnsZeroTargetNormalizedCovariance, hzero]
  · have hco := vfMidAnchoredZeroTargetCoPartialGram_nonneg s a D
    have hdiv := vfMidAnchoredZeroTargetDivergentGram_nonneg s a D
    have hden :
        0 < vfMidAnchoredZeroTargetCoPartialGram s a D +
          vfMidAnchoredZeroTargetDivergentGram s a D :=
      lt_of_le_of_ne (add_nonneg hco hdiv) (Ne.symm hzero)
    rw [nnsZeroTargetNormalizedCovariance, if_neg hzero]
    apply div_nonneg
    · rw [vfMidAnchoredZeroTarget_excess_eq_sub_sq s a D]
      exact sq_nonneg _
    · exact hden.le

def vfMidFirstBadNNSNormalizedCovariance (R : ℕ) : ℝ :=
  vfMidAnchoredZeroTargetNNSNormalizedCovariance
    (vfMidOddCandidateSeats R)
    (vfMidOddSignedSeatCharge R)
    (vfMidActualPrimeEndpointDefect R)

def vfMidFirstBadZeroTargetTotalMass (R : ℕ) : ℝ :=
  vfMidAnchoredZeroTargetTotalMass
    (vfMidOddCandidateSeats R)
    (vfMidOddSignedSeatCharge R)
    (vfMidActualPrimeEndpointDefect R)

theorem vfMidFirstBadZeroTargetTotalMass_eq
    (R : ℕ) :
    vfMidFirstBadZeroTargetTotalMass R =
      (|vfMidActualPrimeEndpointDefect R| +
        ∑ n ∈ vfMidOddCandidateSeats R, |vfMidOddSignedSeatCharge R n|) ^ 2 := by
  exact vfMidAnchoredZeroTargetTotalMass_eq_absSum_sq
    (vfMidOddCandidateSeats R)
    (vfMidOddSignedSeatCharge R)
    (vfMidActualPrimeEndpointDefect R)

theorem vfMidFirstBadNNSNormalizedCovariance_bounds
    (R : ℕ) :
    0 ≤ vfMidFirstBadNNSNormalizedCovariance R ∧
      vfMidFirstBadNNSNormalizedCovariance R ≤ 1 := by
  constructor
  · exact vfMidAnchoredZeroTargetNNSNormalizedCovariance_nonneg
      (vfMidOddCandidateSeats R)
      (vfMidOddSignedSeatCharge R)
      (vfMidActualPrimeEndpointDefect R)
  · exact
      (vfMidAnchoredZeroTargetNNSNormalizedCovariance_bounds
        (vfMidOddCandidateSeats R)
        (vfMidOddSignedSeatCharge R)
        (vfMidActualPrimeEndpointDefect R)).2

/-- Normalized NNS factorization of the complete #889/#896 first-bad bill. -/
theorem vfMidCorrelationEnergy_add_anchorSq_eq_nnsNormalized_mul_total
    {R : ℕ} (hR : 3 ≤ R) :
    2 * vfMidSquareEndpointAccumulationCorrelation R +
        vfMidSquareBandError R ^ 2 +
        vfMidActualPrimeEndpointDefect R ^ 2 =
      vfMidFirstBadNNSNormalizedCovariance R *
        vfMidFirstBadZeroTargetTotalMass R := by
  have hraw :=
    vfMidCorrelationEnergy_eq_anchoredPartialExcess_sub_anchorSq hR
  have hnorm :=
    vfMidAnchoredZeroTargetNNSNormalizedCovariance_mul_total
      (vfMidOddCandidateSeats R)
      (vfMidOddSignedSeatCharge R)
      (vfMidActualPrimeEndpointDefect R)
  unfold vfMidFirstBadNNSNormalizedCovariance
    vfMidFirstBadZeroTargetTotalMass
  have hexcess :=
    vfMidAnchoredZeroTarget_excess_eq_sub_sq
      (vfMidOddCandidateSeats R)
      (vfMidOddSignedSeatCharge R)
      (vfMidActualPrimeEndpointDefect R)
  linarith

/-- The terminal radial budget is exactly a normalized-covariance budget. -/
theorem vfMidCorrelationEnergy_le_radialBudget_iff_nnsNormalized
    {K : ℝ} {R : ℕ} (hR : 3 ≤ R) :
    (2 * vfMidSquareEndpointAccumulationCorrelation R +
        vfMidSquareBandError R ^ 2 ≤
      (K * vfMidSyntheticRadialScale (R + 1)) ^ 2 -
        vfMidActualPrimeEndpointDefect R ^ 2) ↔
    (vfMidFirstBadNNSNormalizedCovariance R *
        vfMidFirstBadZeroTargetTotalMass R ≤
      (K * vfMidSyntheticRadialScale (R + 1)) ^ 2) := by
  have h :=
    vfMidCorrelationEnergy_add_anchorSq_eq_nnsNormalized_mul_total hR
  constructor <;> intro hbudget <;> nlinarith

/-- Every literal VF odd-seat charge has magnitude at most one from R=3 on. -/
theorem abs_vfMidOddSignedSeatCharge_le_one
    {R n : ℕ} (hR : 3 ≤ R) :
    |vfMidOddSignedSeatCharge R n| ≤ 1 := by
  have hw0 :=
    vfMidOddFractionalPrimeSeatWeight_nonneg R (by omega : 2 ≤ R)
  have hw1 :=
    vfMidOddFractionalPrimeSeatWeight_le_one_of_three_le R hR
  by_cases hp : n.Prime
  · rw [vfMidOddSignedSeatCharge_of_prime R n hp, abs_neg]
    have hcomp : 0 ≤ 1 - vfMidOddFractionalPrimeSeatWeight R := by linarith
    rw [abs_of_nonneg hcomp]
    linarith
  · rw [vfMidOddSignedSeatCharge_of_not_prime R n hp]
    rw [abs_of_nonneg hw0]
    exact hw1

theorem vfMidOddSignedSeatCharge_absSum_le_root
    {R : ℕ} (hR : 3 ≤ R) :
    (∑ n ∈ vfMidOddCandidateSeats R, |vfMidOddSignedSeatCharge R n|) ≤
      (R : ℝ) := by
  calc
    (∑ n ∈ vfMidOddCandidateSeats R, |vfMidOddSignedSeatCharge R n|) ≤
      ∑ _n ∈ vfMidOddCandidateSeats R, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro n _hn
        exact abs_vfMidOddSignedSeatCharge_le_one hR
    _ = ((vfMidOddCandidateSeats R).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
    _ = (R : ℝ) := by
        rw [vfMidOddCandidateSeats_card]

private theorem vfMidSyntheticRadialScale_ge_two_mul_root
    {R : ℕ} (hR : 8 ≤ R) :
    2 * (R : ℝ) ≤ vfMidSyntheticRadialScale R := by
  have hlog2 : (9 / 10 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog8eq : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    calc
      Real.log (8 : ℝ) = Real.log ((2 : ℝ) ^ 3) := by norm_num
      _ = (3 : ℕ) * Real.log 2 := by rw [Real.log_pow]
      _ = 3 * Real.log 2 := by norm_num
  have hlog8 : (2 : ℝ) < Real.log 8 := by
    rw [hlog8eq]
    nlinarith
  have h8R : (8 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have hlog8R : Real.log (8 : ℝ) ≤ Real.log (R : ℝ) :=
    Real.log_le_log (by norm_num) h8R
  have hlogR : (2 : ℝ) < Real.log (R : ℝ) :=
    hlog8.trans_le hlog8R
  have hR0 : (0 : ℝ) < (R : ℝ) := by positivity
  unfold vfMidSyntheticRadialScale
  have hmul := mul_lt_mul_of_pos_left hlogR hR0
  nlinarith

/-- With K=2, one-half of the worst possible anchored total mass already fits
inside the next radial wall from R >= 8. -/
theorem vfMidActualPrimeFirstBadAt_two_succ_half_totalMass_le_radial
    {R : ℕ} (hR : 8 ≤ R)
    (hfirst : VFMidActualPrimeFirstBadAt (2 : ℝ) (R + 1)) :
    (1 / 2 : ℝ) * vfMidFirstBadZeroTargetTotalMass R ≤
      ((2 : ℝ) * vfMidSyntheticRadialScale (R + 1)) ^ 2 := by
  have hprior :=
    vfMidActualPrimeFirstBadAt_prior_inside
      hfirst (by omega : 2 ≤ R) (by omega : R < R + 1)
  have habsD :
      |vfMidActualPrimeEndpointDefect R| ≤
        2 * vfMidSyntheticRadialScale R := by
    simpa using hprior
  have hseat := vfMidOddSignedSeatCharge_absSum_le_root (R := R) (by omega)
  have hroot :
      2 * (R : ℝ) ≤ vfMidSyntheticRadialScale R :=
    vfMidSyntheticRadialScale_ge_two_mul_root hR
  have hrho0 : 0 ≤ vfMidSyntheticRadialScale R := by
    have hR0 : (0 : ℝ) ≤ (R : ℝ) := by positivity
    nlinarith
  have hsum :
      |vfMidActualPrimeEndpointDefect R| +
          (∑ n ∈ vfMidOddCandidateSeats R, |vfMidOddSignedSeatCharge R n|) ≤
        2 * vfMidSyntheticRadialScale R + (R : ℝ) := by
    linarith
  have htotal :
      vfMidFirstBadZeroTargetTotalMass R ≤
        (2 * vfMidSyntheticRadialScale R + (R : ℝ)) ^ 2 := by
    rw [vfMidFirstBadZeroTargetTotalMass_eq]
    have hleft0 :
        0 ≤ |vfMidActualPrimeEndpointDefect R| +
          ∑ n ∈ vfMidOddCandidateSeats R, |vfMidOddSignedSeatCharge R n| := by
      positivity
    have hright0 :
        0 ≤ 2 * vfMidSyntheticRadialScale R + (R : ℝ) := by
      positivity
    nlinarith
  have hhalf :
      (1 / 2 : ℝ) *
          (2 * vfMidSyntheticRadialScale R + (R : ℝ)) ^ 2 ≤
        4 * vfMidSyntheticRadialScale R ^ 2 := by
    have hR0 : 0 ≤ (R : ℝ) := by positivity
    nlinarith [sq_nonneg
      (vfMidSyntheticRadialScale R - 2 * (R : ℝ))]
  have hstep :=
    vfMidSyntheticRadialScale_sq_increment_gt_25_div_3_mul
      R (by omega : 7 ≤ R)
  have hrhosq :
      vfMidSyntheticRadialScale R ^ 2 ≤
        vfMidSyntheticRadialScale (R + 1) ^ 2 := by
    have hR0 : 0 < (25 / 3 : ℝ) * (R : ℝ) := by positivity
    linarith
  calc
    (1 / 2 : ℝ) * vfMidFirstBadZeroTargetTotalMass R ≤
      (1 / 2 : ℝ) *
        (2 * vfMidSyntheticRadialScale R + (R : ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_left htotal (by norm_num)
    _ ≤ 4 * vfMidSyntheticRadialScale R ^ 2 := hhalf
    _ ≤ 4 * vfMidSyntheticRadialScale (R + 1) ^ 2 := by
      nlinarith
    _ = ((2 : ℝ) * vfMidSyntheticRadialScale (R + 1)) ^ 2 := by ring

/-- **Normalized half-covariance closure.**

At K=2 and R>=8, a one-half ceiling on the anchored NNS zero-target normalized
covariance implies the exact terminal `hrank` inequality, hence contradicts
first badness.  The remaining owner-tree target is therefore dimensionless. -/
theorem vfMidActualPrimeFirstBadAt_two_succ_finalContraction_of_nnsNormalized_le_half
    {R : ℕ} (hR : 8 ≤ R)
    (hfirst : VFMidActualPrimeFirstBadAt (2 : ℝ) (R + 1))
    (hnorm : vfMidFirstBadNNSNormalizedCovariance R ≤ (1 / 2 : ℝ)) :
    False := by
  have htotal0 : 0 ≤ vfMidFirstBadZeroTargetTotalMass R := by
    rw [vfMidFirstBadZeroTargetTotalMass_eq]
    positivity
  have hprod :
      vfMidFirstBadNNSNormalizedCovariance R *
          vfMidFirstBadZeroTargetTotalMass R ≤
        (1 / 2 : ℝ) * vfMidFirstBadZeroTargetTotalMass R :=
    mul_le_mul_of_nonneg_right hnorm htotal0
  have hrad :=
    vfMidActualPrimeFirstBadAt_two_succ_half_totalMass_le_radial hR hfirst
  have hbudgetNorm :
      vfMidFirstBadNNSNormalizedCovariance R *
          vfMidFirstBadZeroTargetTotalMass R ≤
        ((2 : ℝ) * vfMidSyntheticRadialScale (R + 1)) ^ 2 :=
    hprod.trans hrad
  have hrank :
      2 * vfMidSquareEndpointAccumulationCorrelation R +
          vfMidSquareBandError R ^ 2 ≤
        ((2 : ℝ) * vfMidSyntheticRadialScale (R + 1)) ^ 2 -
          vfMidActualPrimeEndpointDefect R ^ 2 :=
    (vfMidCorrelationEnergy_le_radialBudget_iff_nnsNormalized
      (K := (2 : ℝ)) (R := R) (by omega : 3 ≤ R)).2 hbudgetNorm
  exact vfMidActualPrimeFirstBadAt_succ_finalContraction
    (by norm_num : (0 : ℝ) ≤ 2) (by omega : 3 ≤ R) hfirst hrank

end RHLean.Analysis
