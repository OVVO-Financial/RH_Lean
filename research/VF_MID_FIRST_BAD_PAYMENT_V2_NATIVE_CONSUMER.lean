import Mathlib
import «research.VF_MID_FIRST_BAD_CORRELATION_DESCENT»

/-!
# Native first-bad v2 consumer: one exact missing arithmetic hypothesis

The statement below is the ENTIRE open first-bad signed payment. It is a Prop,
not an axiom or theorem. This file proves only that proving the stated payment
from genuine first-bad arithmetic contradicts existing compiled results.

This intentionally imports main's production definitions, not #915.
Expensive native import closure is tested ONLY by the optional deep CI job.
-/

noncomputable section

namespace RHLean.Analysis

/-- SINGLE OPEN ARITHMETIC GATE. This is a named statement, NOT a proof.
The RHS is exactly the original physical odd-seat anchored NNS mass. -/
def VFMidMinimalActualFirstBadPaymentV2Statement : Prop :=
  ∀ (R : ℕ), 8 ≤ R →
    VFMidActualPrimeFirstBadAt (2 : ℝ) (R + 1) →
      2 * vfMidActualPrimeEndpointDefect (R + 1) ^ 2 ≤
        vfMidFirstBadZeroTargetTotalMass R

/-- No unconditional balance statement is assumed.
If the actual-prime first-bad-specific budget can be proved, existing
green theorems force the strictly opposite normalized NNS inequality. -/
theorem vfMidMinimalActualFirstBad_closed_of_exactPaymentV2
    (hpayment : VFMidMinimalActualFirstBadPaymentV2Statement)
    {R : ℕ} (hR : 8 ≤ R)
    (hfirst : VFMidActualPrimeFirstBadAt (2 : ℝ) (R + 1)) :
    False := by
  have hprod :=
    vfMidFirstBadNormalizedProduct_eq_nextEndpointDefect_sq
      (R := R) (by omega : 3 ≤ R)
  have hgt :=
    vfMidActualPrimeFirstBadAt_two_succ_nnsNormalized_gt_half hR hfirst
  have hmass0 : 0 ≤ vfMidFirstBadZeroTargetTotalMass R := by
    rw [vfMidFirstBadZeroTargetTotalMass_eq]
    positivity
  have hbreach := hfirst.1
  unfold VFMidSyntheticBadAt at hbreach
  have hwall0 :
      0 ≤ (2 : ℝ) * vfMidSyntheticRadialScale (R + 1) :=
    mul_nonneg (by norm_num)
      (le_of_lt (vfMidSyntheticRadialScale_pos (by omega : 2 ≤ R + 1)))
  have habsPos : 0 < |vfMidActualPrimeEndpointDefect (R + 1)| :=
    lt_of_le_of_lt hwall0 hbreach
  have hdefSqPos :
      0 < vfMidActualPrimeEndpointDefect (R + 1) ^ 2 := by
    rw [← sq_abs]
    positivity
  have hmassPos : 0 < vfMidFirstBadZeroTargetTotalMass R := by
    by_contra hnot
    have hzero : vfMidFirstBadZeroTargetTotalMass R = 0 := by linarith
    rw [hzero] at hprod
    nlinarith
  have hpaid := hpayment R hR hfirst
  have hbound :
      vfMidFirstBadNNSNormalizedCovariance R *
          vfMidFirstBadZeroTargetTotalMass R ≤
        (1 / 2 : ℝ) * vfMidFirstBadZeroTargetTotalMass R := by
    rw [hprod]
    linarith
  have hstrict := mul_lt_mul_of_pos_right hgt hmassPos
  linarith

end RHLean.Analysis
