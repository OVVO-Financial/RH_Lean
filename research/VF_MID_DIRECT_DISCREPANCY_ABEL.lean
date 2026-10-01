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
  exact (inv_le_inv₀ hl0 hl1).2 hlog

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
    (R : ℕ) (hR : 3 ≤ R) (M : ℝ) (hM : 0 ≤ M)
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
            |vfMidDirectThetaAbelTail R| := abs_add _ _
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
      rw [Finset.mul_sum]
      ring
    _ = M * vfMidDirectThetaAbelWeight 2 := by
      rw [vfMidDirectThetaAbelKernel_mass R hR]

end RHLean.Analysis
