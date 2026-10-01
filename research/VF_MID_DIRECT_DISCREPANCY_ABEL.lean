import Mathlib
import «research.VF_MID_DIRECT_SIGNED_DYNAMICS»

/-!
# Direct Abel attack on the VF-mid discrepancy

The remaining square-endpoint discrepancy is already reduced to

  D_R = D_2 + T_R + O(R),

where

  T_R = sum_{2 <= r < R} (E_{r+1} - E_r) / log(m_r)

and

  E_r = theta(r^2) - r^2.

This file Abel-transforms T_R itself.  The result is a positive-kernel
representation of the entire RH-scale term:

  T_R =
    E_R w_{R-1} - E_2 w_2
      + sum_{3 <= r < R} E_r (w_{r-1} - w_r),

where w_r = 1 / log(m_r).

The weights are positive and decreasing, and their total kernel mass
telescopes exactly to w_2.  Thus the theta contribution does not accumulate
as an arbitrary sum of R band errors: it is a positive weighted average of
square-endpoint theta errors, plus the fixed base term.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

/-- Reciprocal logarithmic midpoint weight used by the direct theta reduction. -/
def vfMidDirectThetaAbelWeight (r : ℕ) : ℝ :=
  (Real.log (vfMidBandMidpoint r))⁻¹

/-- Interior Abel kernel after summation by parts. -/
def vfMidDirectThetaAbelTail (R : ℕ) : ℝ :=
  ∑ r ∈ Finset.Ico 3 R,
    vfMidDirectThetaEndpointError r *
      (vfMidDirectThetaAbelWeight (r - 1) -
        vfMidDirectThetaAbelWeight r)

/-- The midpoint reciprocal-log weight is strictly positive from the live range. -/
theorem vfMidDirectThetaAbelWeight_pos
    {r : ℕ} (hr : 2 ≤ r) :
    0 < vfMidDirectThetaAbelWeight r := by
  unfold vfMidDirectThetaAbelWeight
  apply inv_pos.mpr
  apply Real.log_pos
  unfold vfMidBandMidpoint
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  nlinarith

/-- Midpoint reciprocal-log weights decrease with the square index. -/
theorem vfMidDirectThetaAbelWeight_succ_le
    {r : ℕ} (hr : 2 ≤ r) :
    vfMidDirectThetaAbelWeight (r + 1) ≤
      vfMidDirectThetaAbelWeight r := by
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hm0 : 0 < vfMidBandMidpoint r := by
    unfold vfMidBandMidpoint
    nlinarith
  have hm1 : 0 < vfMidBandMidpoint (r + 1) := by
    unfold vfMidBandMidpoint
    push_cast
    nlinarith
  have hmle :
      vfMidBandMidpoint r ≤ vfMidBandMidpoint (r + 1) := by
    unfold vfMidBandMidpoint
    push_cast
    nlinarith
  have hl0 : 0 < Real.log (vfMidBandMidpoint r) := by
    apply Real.log_pos
    unfold vfMidBandMidpoint
    nlinarith
  have hl1 : 0 < Real.log (vfMidBandMidpoint (r + 1)) := by
    apply Real.log_pos
    unfold vfMidBandMidpoint
    push_cast
    nlinarith
  have hlog :
      Real.log (vfMidBandMidpoint r) ≤
        Real.log (vfMidBandMidpoint (r + 1)) :=
    Real.log_le_log hm0 hmle
  unfold vfMidDirectThetaAbelWeight
  exact (inv_le_inv₀ hl1 hl0).2 hlog

/-- Every interior Abel coefficient is nonnegative. -/
theorem vfMidDirectThetaAbelWeight_drop_nonneg
    {r : ℕ} (hr : 3 ≤ r) :
    0 ≤ vfMidDirectThetaAbelWeight (r - 1) -
      vfMidDirectThetaAbelWeight r := by
  have hpred : 2 ≤ r - 1 := by omega
  have hstep :=
    vfMidDirectThetaAbelWeight_succ_le (r := r - 1) hpred
  have hrs : r - 1 + 1 = r := by omega
  rw [hrs] at hstep
  linarith

/-- The complete positive Abel kernel has exactly the fixed mass w_2. -/
theorem vfMidDirectThetaAbelKernel_mass
    (R : ℕ) (hR : 3 ≤ R) :
    vfMidDirectThetaAbelWeight (R - 1) +
        ∑ r ∈ Finset.Ico 3 R,
          (vfMidDirectThetaAbelWeight (r - 1) -
            vfMidDirectThetaAbelWeight r) =
      vfMidDirectThetaAbelWeight 2 := by
  induction R, hR using Nat.le_induction with
  | base =>
      simp
  | succ R hR ih =>
      rw [Finset.sum_Ico_succ_top hR]
      have hpred : R + 1 - 1 = R := by omega
      rw [hpred]
      linarith

/-- **Exact Abel form of the remaining direct theta discrepancy.**

The slowly weighted first differences collapse to a positive kernel on the
square-endpoint theta errors themselves. -/
theorem vfMidDirectThetaWeightedPrefix_abel
    (R : ℕ) (hR : 3 ≤ R) :
    vfMidDirectThetaWeightedPrefix R =
      vfMidDirectThetaEndpointError R *
          vfMidDirectThetaAbelWeight (R - 1) -
        vfMidDirectThetaEndpointError 2 *
          vfMidDirectThetaAbelWeight 2 +
        vfMidDirectThetaAbelTail R := by
  induction R, hR using Nat.le_induction with
  | base =>
      simp [vfMidDirectThetaWeightedPrefix,
        vfMidDirectThetaAbelWeight, vfMidDirectThetaAbelTail,
        vfMidDirectThetaBandError_eq_endpoint_diff, div_eq_mul_inv]
      ring
  | succ R hR ih =>
      have hprefix :
          vfMidDirectThetaWeightedPrefix (R + 1) =
            vfMidDirectThetaWeightedPrefix R +
              vfMidDirectThetaBandError R /
                Real.log (vfMidBandMidpoint R) := by
        unfold vfMidDirectThetaWeightedPrefix
        rw [Finset.sum_Ico_succ_top (by omega)]
      have htail :
          vfMidDirectThetaAbelTail (R + 1) =
            vfMidDirectThetaAbelTail R +
              vfMidDirectThetaEndpointError R *
                (vfMidDirectThetaAbelWeight (R - 1) -
                  vfMidDirectThetaAbelWeight R) := by
        unfold vfMidDirectThetaAbelTail
        rw [Finset.sum_Ico_succ_top hR]
      rw [hprefix, htail, ih, vfMidDirectThetaBandError_eq_endpoint_diff]
      have hpred : R + 1 - 1 = R := by omega
      rw [hpred]
      unfold vfMidDirectThetaAbelWeight
      simp only [div_eq_mul_inv]
      ring

/-- **Positive-kernel maximum principle.**

If all square-endpoint theta errors through R are bounded by M, then the
entire weighted theta contribution, after restoring its fixed base term, is
bounded by M times one fixed reciprocal-log weight.  In particular there is
no extra factor R coming from summing the square bands. -/
theorem abs_vfMidDirectThetaWeightedPrefix_add_base_le
    (R : ℕ) (hR : 3 ≤ R) (M : ℝ)
    (hE : ∀ r : ℕ, 3 ≤ r → r ≤ R →
      |vfMidDirectThetaEndpointError r| ≤ M) :
    |vfMidDirectThetaWeightedPrefix R +
        vfMidDirectThetaEndpointError 2 *
          vfMidDirectThetaAbelWeight 2| ≤
      M * vfMidDirectThetaAbelWeight 2 := by
  rw [vfMidDirectThetaWeightedPrefix_abel R hR]
  ring_nf
  have hwR : 0 ≤ vfMidDirectThetaAbelWeight (R - 1) :=
    (vfMidDirectThetaAbelWeight_pos (r := R - 1) (by omega)).le
  calc
    |vfMidDirectThetaEndpointError R *
          vfMidDirectThetaAbelWeight (R - 1) +
        vfMidDirectThetaAbelTail R|
        ≤ |vfMidDirectThetaEndpointError R *
              vfMidDirectThetaAbelWeight (R - 1)| +
            |vfMidDirectThetaAbelTail R| := abs_add_le _ _
    _ ≤ M * vfMidDirectThetaAbelWeight (R - 1) +
          ∑ r ∈ Finset.Ico 3 R,
            M * (vfMidDirectThetaAbelWeight (r - 1) -
              vfMidDirectThetaAbelWeight r) := by
      apply add_le_add
      · rw [abs_mul, abs_of_nonneg hwR]
        exact mul_le_mul_of_nonneg_right (hE R hR le_rfl) hwR
      · unfold vfMidDirectThetaAbelTail
        calc
          |∑ r ∈ Finset.Ico 3 R,
              vfMidDirectThetaEndpointError r *
                (vfMidDirectThetaAbelWeight (r - 1) -
                  vfMidDirectThetaAbelWeight r)|
              ≤ ∑ r ∈ Finset.Ico 3 R,
                  |vfMidDirectThetaEndpointError r *
                    (vfMidDirectThetaAbelWeight (r - 1) -
                      vfMidDirectThetaAbelWeight r)| :=
            Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ r ∈ Finset.Ico 3 R,
              M * (vfMidDirectThetaAbelWeight (r - 1) -
                vfMidDirectThetaAbelWeight r) := by
            apply Finset.sum_le_sum
            intro r hr
            have hrange := Finset.mem_Ico.mp hr
            have hdrop :=
              vfMidDirectThetaAbelWeight_drop_nonneg
                (r := r) hrange.1
            rw [abs_mul, abs_of_nonneg hdrop]
            exact mul_le_mul_of_nonneg_right
              (hE r hrange.1 hrange.2.le) hdrop
    _ = M * (vfMidDirectThetaAbelWeight (R - 1) +
          ∑ r ∈ Finset.Ico 3 R,
            (vfMidDirectThetaAbelWeight (r - 1) -
              vfMidDirectThetaAbelWeight r)) := by
      rw [mul_add, Finset.mul_sum]
    _ = vfMidDirectThetaAbelWeight 2 * M := by
      rw [vfMidDirectThetaAbelKernel_mass R hR]
      ring

/-! ## Quantitative decay of the Abel kernel -/

private theorem vfMidBandMidpoint_pred_formula
    (r : ℕ) (hr : 1 ≤ r) :
    vfMidBandMidpoint (r - 1) =
      (r : ℝ) ^ 2 - (r : ℝ) + (1 / 2 : ℝ) := by
  unfold vfMidBandMidpoint
  push_cast [Nat.cast_sub hr]
  ring

/-- The previous square midpoint stays above half the current square. -/
theorem vfMidBandMidpoint_pred_ge_half_sq
    {r : ℕ} (hr : 3 ≤ r) :
    (r : ℝ) ^ 2 / 2 ≤ vfMidBandMidpoint (r - 1) := by
  rw [vfMidBandMidpoint_pred_formula r (by omega)]
  nlinarith [sq_nonneg ((r : ℝ) - 1)]

/-- The previous square midpoint is already at least the current square index. -/
theorem vfMidBandMidpoint_pred_ge_index
    {r : ℕ} (hr : 3 ≤ r) :
    (r : ℝ) ≤ vfMidBandMidpoint (r - 1) := by
  have hrR : (3 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  rw [vfMidBandMidpoint_pred_formula r (by omega)]
  nlinarith [sq_nonneg ((r : ℝ) - 2)]

/-- Consecutive square midpoints differ by exactly 2r. -/
theorem vfMidBandMidpoint_sub_pred
    {r : ℕ} (hr : 1 ≤ r) :
    vfMidBandMidpoint r - vfMidBandMidpoint (r - 1) =
      2 * (r : ℝ) := by
  rw [vfMidBandMidpoint_pred_formula r hr]
  unfold vfMidBandMidpoint
  ring

/-- The logarithmic midpoint step is O(1/r), with an explicit constant. -/
theorem vfMidDirectThetaMidpoint_log_step_le_four_div
    {r : ℕ} (hr : 3 ≤ r) :
    Real.log (vfMidBandMidpoint r) -
        Real.log (vfMidBandMidpoint (r - 1)) ≤
      4 / (r : ℝ) := by
  have hrpos : (0 : ℝ) < (r : ℝ) := by
    exact_mod_cast (show 0 < r by omega)
  have hAhalf := vfMidBandMidpoint_pred_ge_half_sq (r := r) hr
  have hApos : 0 < vfMidBandMidpoint (r - 1) := by
    have hrsq : 0 < (r : ℝ) ^ 2 := sq_pos_of_pos hrpos
    nlinarith
  have hBpos : 0 < vfMidBandMidpoint r := by
    unfold vfMidBandMidpoint
    nlinarith [sq_pos_of_pos hrpos]
  have hlogRatio :=
    Real.log_le_sub_one_of_pos (div_pos hBpos hApos)
  rw [Real.log_div hBpos.ne' hApos.ne'] at hlogRatio
  have hratio :
      vfMidBandMidpoint r / vfMidBandMidpoint (r - 1) - 1 =
        (2 * (r : ℝ)) / vfMidBandMidpoint (r - 1) := by
    have hdiff := vfMidBandMidpoint_sub_pred (r := r) (by omega)
    field_simp [hApos.ne']
    nlinarith
  have hfrac :
      (2 * (r : ℝ)) / vfMidBandMidpoint (r - 1) ≤
        4 / (r : ℝ) := by
    rw [div_le_div_iff₀ hApos hrpos]
    nlinarith
  calc
    Real.log (vfMidBandMidpoint r) -
          Real.log (vfMidBandMidpoint (r - 1))
        ≤ vfMidBandMidpoint r / vfMidBandMidpoint (r - 1) - 1 :=
      hlogRatio
    _ = (2 * (r : ℝ)) / vfMidBandMidpoint (r - 1) := hratio
    _ ≤ 4 / (r : ℝ) := hfrac

/-- Both midpoint logs dominate log r on the square scale. -/
theorem vfMidDirectTheta_log_index_le_log_pred_midpoint
    {r : ℕ} (hr : 3 ≤ r) :
    Real.log (r : ℝ) ≤
      Real.log (vfMidBandMidpoint (r - 1)) := by
  have hrpos : (0 : ℝ) < (r : ℝ) := by
    exact_mod_cast (show 0 < r by omega)
  exact Real.log_le_log hrpos
    (vfMidBandMidpoint_pred_ge_index (r := r) hr)

/-- The current midpoint log also dominates log r. -/
theorem vfMidDirectTheta_log_index_le_log_midpoint
    {r : ℕ} (hr : 3 ≤ r) :
    Real.log (r : ℝ) ≤
      Real.log (vfMidBandMidpoint r) := by
  have hrpos : (0 : ℝ) < (r : ℝ) := by
    exact_mod_cast (show 0 < r by omega)
  have hle : (r : ℝ) ≤ vfMidBandMidpoint r := by
    have hrR : (3 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    unfold vfMidBandMidpoint
    nlinarith [sq_nonneg ((r : ℝ) - 1)]
  exact Real.log_le_log hrpos hle

/-- **Quantitative Abel-kernel decay.**

The positive reciprocal-log drop is at most
  (4/r) / log(r)^2.
This is the scale that prevents historical square-band errors from
accumulating another logarithmic or linear loss. -/
theorem vfMidDirectThetaAbelWeight_drop_le
    {r : ℕ} (hr : 3 ≤ r) :
    vfMidDirectThetaAbelWeight (r - 1) -
        vfMidDirectThetaAbelWeight r ≤
      (4 / (r : ℝ)) / (Real.log (r : ℝ)) ^ 2 := by
  have hrpos : (0 : ℝ) < (r : ℝ) := by
    exact_mod_cast (show 0 < r by omega)
  have hlogr : 0 < Real.log (r : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < r by omega)
  have hlogA : 0 < Real.log (vfMidBandMidpoint (r - 1)) := by
    exact lt_of_lt_of_le hlogr
      (vfMidDirectTheta_log_index_le_log_pred_midpoint (r := r) hr)
  have hlogB : 0 < Real.log (vfMidBandMidpoint r) := by
    exact lt_of_lt_of_le hlogr
      (vfMidDirectTheta_log_index_le_log_midpoint (r := r) hr)
  have hrewrite :
      vfMidDirectThetaAbelWeight (r - 1) -
          vfMidDirectThetaAbelWeight r =
        (Real.log (vfMidBandMidpoint r) -
            Real.log (vfMidBandMidpoint (r - 1))) /
          (Real.log (vfMidBandMidpoint (r - 1)) *
            Real.log (vfMidBandMidpoint r)) := by
    unfold vfMidDirectThetaAbelWeight
    field_simp [hlogA.ne', hlogB.ne']
  have hden :
      (Real.log (r : ℝ)) ^ 2 ≤
        Real.log (vfMidBandMidpoint (r - 1)) *
          Real.log (vfMidBandMidpoint r) := by
    rw [pow_two]
    exact mul_le_mul
      (vfMidDirectTheta_log_index_le_log_pred_midpoint (r := r) hr)
      (vfMidDirectTheta_log_index_le_log_midpoint (r := r) hr)
      hlogr.le hlogA.le
  have hnum0 : 0 ≤ 4 / (r : ℝ) := by positivity
  rw [hrewrite]
  calc
    (Real.log (vfMidBandMidpoint r) -
          Real.log (vfMidBandMidpoint (r - 1))) /
        (Real.log (vfMidBandMidpoint (r - 1)) *
          Real.log (vfMidBandMidpoint r))
        ≤ (4 / (r : ℝ)) /
            (Real.log (vfMidBandMidpoint (r - 1)) *
              Real.log (vfMidBandMidpoint r)) :=
      div_le_div_of_nonneg_right
        (vfMidDirectThetaMidpoint_log_step_le_four_div (r := r) hr)
        (mul_nonneg hlogA.le hlogB.le)
    _ ≤ (4 / (r : ℝ)) / (Real.log (r : ℝ)) ^ 2 :=
      div_le_div_of_nonneg_left hnum0 (sq_pos_of_pos hlogr) hden

/-- The terminal Abel weight loses at least one logarithm. -/
theorem vfMidDirectThetaAbelWeight_pred_le_recip_log
    {r : ℕ} (hr : 3 ≤ r) :
    vfMidDirectThetaAbelWeight (r - 1) ≤
      (Real.log (r : ℝ))⁻¹ := by
  have hlogr : 0 < Real.log (r : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < r by omega)
  have hlogA : 0 < Real.log (vfMidBandMidpoint (r - 1)) := by
    exact lt_of_lt_of_le hlogr
      (vfMidDirectTheta_log_index_le_log_pred_midpoint (r := r) hr)
  unfold vfMidDirectThetaAbelWeight
  exact (inv_le_inv₀ hlogA hlogr).2
    (vfMidDirectTheta_log_index_le_log_pred_midpoint (r := r) hr)


/-! ## Direct consumer at the RH square-theta scale -/

/-- Under the square-theta envelope C r log(r)^2, the entire historical Abel
tail is only linear in R. -/
theorem abs_vfMidDirectThetaAbelTail_le_four_mul
    (R : ℕ) (hR : 3 ≤ R) (C : ℝ) (hC : 0 ≤ C)
    (hE : ∀ r : ℕ, 3 ≤ r → r ≤ R →
      |vfMidDirectThetaEndpointError r| ≤
        C * (r : ℝ) * (Real.log (r : ℝ)) ^ 2) :
    |vfMidDirectThetaAbelTail R| ≤ 4 * C * (R : ℝ) := by
  unfold vfMidDirectThetaAbelTail
  calc
    |∑ r ∈ Finset.Ico 3 R,
        vfMidDirectThetaEndpointError r *
          (vfMidDirectThetaAbelWeight (r - 1) -
            vfMidDirectThetaAbelWeight r)|
        ≤ ∑ r ∈ Finset.Ico 3 R,
            |vfMidDirectThetaEndpointError r *
              (vfMidDirectThetaAbelWeight (r - 1) -
                vfMidDirectThetaAbelWeight r)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r ∈ Finset.Ico 3 R, 4 * C := by
      apply Finset.sum_le_sum
      intro r hr
      have hrange := Finset.mem_Ico.mp hr
      have hrpos : (0 : ℝ) < (r : ℝ) := by
        exact_mod_cast (show 0 < r by omega)
      have hlog : 0 < Real.log (r : ℝ) := by
        apply Real.log_pos
        exact_mod_cast (show 1 < r by omega)
      have hdrop0 :=
        vfMidDirectThetaAbelWeight_drop_nonneg (r := r) hrange.1
      have hdrop :=
        vfMidDirectThetaAbelWeight_drop_le (r := r) hrange.1
      have hupper0 :
          0 ≤ C * (r : ℝ) * (Real.log (r : ℝ)) ^ 2 := by
        positivity
      rw [abs_mul, abs_of_nonneg hdrop0]
      calc
        |vfMidDirectThetaEndpointError r| *
              (vfMidDirectThetaAbelWeight (r - 1) -
                vfMidDirectThetaAbelWeight r)
            ≤ (C * (r : ℝ) * (Real.log (r : ℝ)) ^ 2) *
                ((4 / (r : ℝ)) / (Real.log (r : ℝ)) ^ 2) :=
          mul_le_mul
            (hE r hrange.1 hrange.2.le) hdrop hdrop0 hupper0
        _ = 4 * C := by
          field_simp [hrpos.ne', hlog.ne']
    _ = ((Finset.Ico 3 R).card : ℝ) * (4 * C) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (R : ℝ) * (4 * C) := by
      have hcard : (Finset.Ico 3 R).card ≤ R := by
        rw [Nat.card_Ico]
        omega
      have hcardR : ((Finset.Ico 3 R).card : ℝ) ≤ (R : ℝ) := by
        exact_mod_cast hcard
      exact mul_le_mul_of_nonneg_right hcardR (by positivity)
    _ = 4 * C * (R : ℝ) := by ring

/-- The terminal Abel atom costs exactly one logarithm under the square-theta
RH-scale envelope. -/
theorem abs_vfMidDirectThetaEndpoint_mul_terminalWeight_le
    (R : ℕ) (hR : 3 ≤ R) (C : ℝ) (hC : 0 ≤ C)
    (hE :
      |vfMidDirectThetaEndpointError R| ≤
        C * (R : ℝ) * (Real.log (R : ℝ)) ^ 2) :
    |vfMidDirectThetaEndpointError R *
        vfMidDirectThetaAbelWeight (R - 1)| ≤
      C * (R : ℝ) * Real.log (R : ℝ) := by
  have hlog : 0 < Real.log (R : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < R by omega)
  have hw0 : 0 ≤ vfMidDirectThetaAbelWeight (R - 1) :=
    (vfMidDirectThetaAbelWeight_pos (r := R - 1) (by omega)).le
  have hw :=
    vfMidDirectThetaAbelWeight_pred_le_recip_log (r := R) hR
  have hupper0 :
      0 ≤ C * (R : ℝ) * (Real.log (R : ℝ)) ^ 2 := by
    positivity
  rw [abs_mul, abs_of_nonneg hw0]
  calc
    |vfMidDirectThetaEndpointError R| *
          vfMidDirectThetaAbelWeight (R - 1)
        ≤ (C * (R : ℝ) * (Real.log (R : ℝ)) ^ 2) *
            vfMidDirectThetaAbelWeight (R - 1) :=
      mul_le_mul_of_nonneg_right hE hw0
    _ ≤ (C * (R : ℝ) * (Real.log (R : ℝ)) ^ 2) *
          (Real.log (R : ℝ))⁻¹ :=
      mul_le_mul_of_nonneg_left hw hupper0
    _ = C * (R : ℝ) * Real.log (R : ℝ) := by
      field_simp [hlog.ne']

/-- **No-accumulation theorem at the exact RH theta scale.**

A square-endpoint theta envelope C r log(r)^2 gives the required
C R log R terminal scale plus only a linear historical tail. -/
theorem abs_vfMidDirectThetaWeightedPrefix_add_base_le_Rlog
    (R : ℕ) (hR : 3 ≤ R) (C : ℝ) (hC : 0 ≤ C)
    (hE : ∀ r : ℕ, 3 ≤ r → r ≤ R →
      |vfMidDirectThetaEndpointError r| ≤
        C * (r : ℝ) * (Real.log (r : ℝ)) ^ 2) :
    |vfMidDirectThetaWeightedPrefix R +
        vfMidDirectThetaEndpointError 2 *
          vfMidDirectThetaAbelWeight 2| ≤
      C * (R : ℝ) * Real.log (R : ℝ) +
        4 * C * (R : ℝ) := by
  have hrearr :
      vfMidDirectThetaWeightedPrefix R +
          vfMidDirectThetaEndpointError 2 *
            vfMidDirectThetaAbelWeight 2 =
        vfMidDirectThetaEndpointError R *
            vfMidDirectThetaAbelWeight (R - 1) +
          vfMidDirectThetaAbelTail R := by
    rw [vfMidDirectThetaWeightedPrefix_abel R hR]
    ring
  rw [hrearr]
  calc
    |vfMidDirectThetaEndpointError R *
          vfMidDirectThetaAbelWeight (R - 1) +
        vfMidDirectThetaAbelTail R|
        ≤ |vfMidDirectThetaEndpointError R *
              vfMidDirectThetaAbelWeight (R - 1)| +
            |vfMidDirectThetaAbelTail R| := abs_add_le _ _
    _ ≤ C * (R : ℝ) * Real.log (R : ℝ) +
          4 * C * (R : ℝ) :=
      add_le_add
        (abs_vfMidDirectThetaEndpoint_mul_terminalWeight_le
          R hR C hC (hE R hR le_rfl))
        (abs_vfMidDirectThetaAbelTail_le_four_mul R hR C hC hE)

/-- **Direct VF-mid endpoint consumer.**

Once the square theta endpoint error has the RH-scale envelope
  |theta(r^2)-r^2| <= C r log(r)^2,
the actual VF-mid square endpoint discrepancy is already at R log R scale,
up to an explicit fixed base atom and explicit linear terms. -/
theorem abs_vfMidDirectSquareEndpointError_le_of_thetaEnvelope
    (R : ℕ) (hR : 3 ≤ R) (C : ℝ) (hC : 0 ≤ C)
    (hE : ∀ r : ℕ, 3 ≤ r → r ≤ R →
      |vfMidDirectThetaEndpointError r| ≤
        C * (r : ℝ) * (Real.log (r : ℝ)) ^ 2) :
    |vfMidDirectSquareEndpointError R| ≤
      C * (R : ℝ) * Real.log (R : ℝ) +
        (4 * C + 9 / Real.log 4) * (R : ℝ) +
        |vfMidDirectSquareEndpointError 2 -
          vfMidDirectThetaEndpointError 2 *
            vfMidDirectThetaAbelWeight 2| := by
  have hrem :=
    abs_vfMidDirectSquareEndpointError_sub_thetaWeighted_le
      R (by omega)
  have htheta :=
    abs_vfMidDirectThetaWeightedPrefix_add_base_le_Rlog
      R hR C hC hE
  have hrearr :
      vfMidDirectSquareEndpointError R =
        (vfMidDirectSquareEndpointError R -
          vfMidDirectSquareEndpointError 2 -
          vfMidDirectThetaWeightedPrefix R) +
        (vfMidDirectThetaWeightedPrefix R +
          vfMidDirectThetaEndpointError 2 *
            vfMidDirectThetaAbelWeight 2) +
        (vfMidDirectSquareEndpointError 2 -
          vfMidDirectThetaEndpointError 2 *
            vfMidDirectThetaAbelWeight 2) := by
    ring
  rw [hrearr]
  calc
    |(vfMidDirectSquareEndpointError R -
          vfMidDirectSquareEndpointError 2 -
          vfMidDirectThetaWeightedPrefix R) +
        (vfMidDirectThetaWeightedPrefix R +
          vfMidDirectThetaEndpointError 2 *
            vfMidDirectThetaAbelWeight 2) +
        (vfMidDirectSquareEndpointError 2 -
          vfMidDirectThetaEndpointError 2 *
            vfMidDirectThetaAbelWeight 2)|
        ≤ (|(vfMidDirectSquareEndpointError R -
              vfMidDirectSquareEndpointError 2 -
              vfMidDirectThetaWeightedPrefix R)| +
            |vfMidDirectThetaWeightedPrefix R +
              vfMidDirectThetaEndpointError 2 *
                vfMidDirectThetaAbelWeight 2|) +
            |vfMidDirectSquareEndpointError 2 -
              vfMidDirectThetaEndpointError 2 *
                vfMidDirectThetaAbelWeight 2| := by
          exact (abs_add_le _ _).trans
            (add_le_add_right (abs_add_le _ _) _)
    _ ≤ (9 / Real.log 4) * (R : ℝ) +
          (C * (R : ℝ) * Real.log (R : ℝ) +
            4 * C * (R : ℝ)) +
          |vfMidDirectSquareEndpointError 2 -
            vfMidDirectThetaEndpointError 2 *
              vfMidDirectThetaAbelWeight 2| := by
          exact add_le_add
            (add_le_add hrem htheta) le_rfl
    _ = C * (R : ℝ) * Real.log (R : ℝ) +
          (4 * C + 9 / Real.log 4) * (R : ℝ) +
          |vfMidDirectSquareEndpointError 2 -
            vfMidDirectThetaEndpointError 2 *
              vfMidDirectThetaAbelWeight 2| := by
          ring


end RHLean.Analysis
