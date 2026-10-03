import Mathlib
import «research.VF_MID_VON_KOCH_BRIDGE»

/-!
# Uniform VF / Li midpoint quadrature

This file sharpens the existing root-scale VF/Li bridge.  The decisive
analytic input is that the derivative of the Li density has derivative

  (log x + 2) / (x^2 log(x)^3),

hence varies on the r-th square band at scale
O(r^-4 log(r)^-2).  Midpoint symmetry will turn that into a summable
O(1/(r log(r)^2)) local quadrature error.

No prime-distribution input occurs here.  All constants are deterministic.
-/

noncomputable section

open Set MeasureTheory intervalIntegral
open scoped BigOperators Interval Topology

namespace RHLean.Analysis

/-- First derivative of the inverse-log density, named as a function so that
its derivative can be bounded directly. -/
def vfInvLogDeriv (x : ℝ) : ℝ :=
  -x⁻¹ / Real.log x ^ 2

/-- The existing VF bridge derivative formula in named-function form. -/
theorem deriv_invLog_eq_vfInvLogDeriv
    {x : ℝ} (hx : 1 < x) :
    deriv (fun t : ℝ => (Real.log t)⁻¹) x =
      vfInvLogDeriv x := by
  simpa [vfInvLogDeriv] using deriv_inv_log_formula hx

/-- Exact derivative of the first derivative of the inverse-log density. -/
theorem hasDerivAt_vfInvLogDeriv
    {x : ℝ} (hx : 1 < x) :
    HasDerivAt vfInvLogDeriv
      ((Real.log x + 2) /
        (x ^ 2 * Real.log x ^ 3)) x := by
  have hx0 : x ≠ 0 := by linarith
  have hlog0 : Real.log x ≠ 0 :=
    ne_of_gt (Real.log_pos hx)
  have hnum :
      HasDerivAt (fun t : ℝ => -(t⁻¹)) ((x ^ 2)⁻¹) x := by
    convert (hasDerivAt_inv hx0).neg using 1 <;> ring_nf
  have hden :
      HasDerivAt (fun t : ℝ => Real.log t ^ 2)
        (2 * Real.log x * x⁻¹) x := by
    convert (Real.hasDerivAt_log hx0).pow 2 using 1 <;> ring_nf
  have hquot :=
    hnum.div hden (pow_ne_zero 2 hlog0)
  change HasDerivAt
    (fun t : ℝ => -(t⁻¹) / Real.log t ^ 2)
    ((Real.log x + 2) /
      (x ^ 2 * Real.log x ^ 3)) x
  convert hquot using 1
  field_simp [hx0, hlog0]
  ring

theorem deriv_vfInvLogDeriv
    {x : ℝ} (hx : 1 < x) :
    deriv vfInvLogDeriv x =
      (Real.log x + 2) /
        (x ^ 2 * Real.log x ^ 3) :=
  (hasDerivAt_vfInvLogDeriv hx).deriv

/-- A convenient elementary lower bound used to keep all later constants
explicit and rational. -/
theorem one_lt_log_four : (1 : ℝ) < Real.log 4 := by
  have h2 := Real.log_two_gt_d9
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [h4]
  nlinarith

/-- On square tile r, the second derivative of 1/log is
O(r^-4 log(r)^-2).  The constant 4 is intentionally generous. -/
theorem abs_deriv_vfInvLogDeriv_le_squareTile
    {r : ℕ} (hr : 2 ≤ r) {t : ℝ}
    (ht : t ∈ Icc ((r : ℝ) ^ 2)
      ((((r + 1 : ℕ) : ℝ) ^ 2))) :
    |deriv vfInvLogDeriv t| ≤
      4 / ((r : ℝ) ^ 4 * Real.log (r : ℝ) ^ 2) := by
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hr1 : (1 : ℝ) < (r : ℝ) := by linarith
  have hrpos : (0 : ℝ) < (r : ℝ) := by linarith
  have hlogr : 0 < Real.log (r : ℝ) := Real.log_pos hr1
  have hr4 : (4 : ℝ) ≤ (r : ℝ) ^ 2 := by nlinarith
  have ht4 : (4 : ℝ) ≤ t := hr4.trans ht.1
  have htpos : (0 : ℝ) < t := by linarith
  have ht1 : (1 : ℝ) < t := by linarith
  have hlogt : 0 < Real.log t := Real.log_pos ht1
  have hlogt1 : (1 : ℝ) < Real.log t := by
    exact one_lt_log_four.trans_le
      (Real.log_le_log (by norm_num) ht4)
  have hrr : (r : ℝ) ≤ (r : ℝ) ^ 2 := by
    nlinarith
  have hrt : (r : ℝ) ≤ t := hrr.trans ht.1
  have hlogle :
      Real.log (r : ℝ) ≤ Real.log t :=
    Real.log_le_log hrpos hrt
  have hlogsq :
      Real.log (r : ℝ) ^ 2 ≤ Real.log t ^ 2 := by
    nlinarith
  have hsumpos :
      0 ≤ t + (r : ℝ) ^ 2 := by positivity
  have hprod :
      0 ≤ (t - (r : ℝ) ^ 2) *
        (t + (r : ℝ) ^ 2) :=
    mul_nonneg (sub_nonneg.mpr ht.1) hsumpos
  have hrpow :
      (r : ℝ) ^ 4 ≤ t ^ 2 := by
    nlinarith
  have hden :
      (r : ℝ) ^ 4 * Real.log (r : ℝ) ^ 2 ≤
        t ^ 2 * Real.log t ^ 2 := by
    exact mul_le_mul hrpow hlogsq (sq_nonneg _) (by positivity)
  have hdensmall :
      0 < (r : ℝ) ^ 4 * Real.log (r : ℝ) ^ 2 := by
    positivity
  rw [deriv_vfInvLogDeriv ht1]
  have hform :
      0 ≤ (Real.log t + 2) /
        (t ^ 2 * Real.log t ^ 3) := by
    positivity
  rw [abs_of_nonneg hform]
  have hnum : Real.log t + 2 ≤ 3 * Real.log t := by
    nlinarith
  have hden3 : 0 < t ^ 2 * Real.log t ^ 3 := by
    positivity
  calc
    (Real.log t + 2) / (t ^ 2 * Real.log t ^ 3)
        ≤ (3 * Real.log t) /
            (t ^ 2 * Real.log t ^ 3) :=
      div_le_div_of_nonneg_right hnum hden3.le
    _ = 3 / (t ^ 2 * Real.log t ^ 2) := by
      field_simp [hlogt.ne']
    _ ≤ 3 / ((r : ℝ) ^ 4 *
          Real.log (r : ℝ) ^ 2) := by
      exact div_le_div_of_nonneg_left
        (by norm_num : (0 : ℝ) ≤ 3) hdensmall hden
    _ ≤ 4 / ((r : ℝ) ^ 4 *
          Real.log (r : ℝ) ^ 2) := by
      exact div_le_div_of_nonneg_right
        (by norm_num) hdensmall.le

end RHLean.Analysis
