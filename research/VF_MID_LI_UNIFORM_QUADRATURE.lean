import Mathlib
import Mathlib.MeasureTheory.Integral.IntervalIntegral.TrapezoidalRule
import Mathlib.Analysis.SpecialFunctions.Log.InvLog
import «research.VF_MID_VON_KOCH_BRIDGE»

/-!
# Uniform VF / Li midpoint quadrature

The existing VF-mid bridge deliberately used only a first-derivative estimate,
which gives an O(sqrt x) bound adequate for the von-Koch transfer.  Numerically,
however, the square-endpoint discrepancy

  Li_2(R^2) - vfMidFinishedMass R

stays near a constant (~2.1 over the current scans).

This file begins the sharper deterministic analysis.  The key structural fact
is that the midpoint-rule error on the r-th square band has summable size

  O(1 / (r log(r)^2)).

The proof uses Mathlib's second-derivative trapezoidal-rule estimate and the
identity expressing one midpoint approximation as 2*T_2 - T_1.

No prime-distribution input occurs anywhere in this file.
-/

noncomputable section

open Set MeasureTheory intervalIntegral
open scoped BigOperators Interval Topology

namespace RHLean.Analysis

/-- A one-panel midpoint approximation. -/
def vfMidpointIntegralApprox
    (f : ℝ → ℝ) (a b : ℝ) : ℝ :=
  (b - a) * f ((a + b) / 2)

/-- Its signed integration error. -/
def vfMidpointIntegralError
    (f : ℝ → ℝ) (a b : ℝ) : ℝ :=
  vfMidpointIntegralApprox f a b - ∫ x in a..b, f x

/-- A midpoint panel is the Richardson combination 2*T₂-T₁ of the one- and
two-panel trapezoidal approximations. -/
theorem vfMidpointIntegralApprox_eq_two_trapezoidal_sub_one
    (f : ℝ → ℝ) (a b : ℝ) :
    vfMidpointIntegralApprox f a b =
      2 * trapezoidal_integral f 2 a b -
        trapezoidal_integral f 1 a b := by
  unfold vfMidpointIntegralApprox trapezoidal_integral
  simp
  ring

/-- The same identity for signed errors. -/
theorem vfMidpointIntegralError_eq_two_trapezoidalError_sub_one
    (f : ℝ → ℝ) (a b : ℝ) :
    vfMidpointIntegralError f a b =
      2 * trapezoidal_error f 2 a b -
        trapezoidal_error f 1 a b := by
  unfold vfMidpointIntegralError trapezoidal_error
  rw [vfMidpointIntegralApprox_eq_two_trapezoidal_sub_one]
  ring

/-- Generic midpoint-rule error bound derived from Mathlib's trapezoidal-rule
bound.  The constant 1/8 is deliberately loose; summability, not sharpness, is
the objective. -/
theorem abs_vfMidpointIntegralError_le_of_c2
    {f : ℝ → ℝ} {a b ζ : ℝ}
    (hf : ContDiffOn ℝ 2 f [[a, b]])
    (hζ : ∀ x, |iteratedDerivWithin 2 f [[a, b]] x| ≤ ζ) :
    |vfMidpointIntegralError f a b| ≤
      |b - a| ^ 3 * ζ / 8 := by
  have h1 :=
    trapezoidal_error_le_of_c2
      (f := f) (a := a) (b := b) hf hζ
      (N := 1) (by norm_num : 0 < (1 : ℕ))
  have h2 :=
    trapezoidal_error_le_of_c2
      (f := f) (a := a) (b := b) hf hζ
      (N := 2) (by norm_num : 0 < (2 : ℕ))
  rw [vfMidpointIntegralError_eq_two_trapezoidalError_sub_one]
  calc
    |2 * trapezoidal_error f 2 a b -
        trapezoidal_error f 1 a b|
        ≤ 2 * |trapezoidal_error f 2 a b| +
            |trapezoidal_error f 1 a b| := by
          calc
            |2 * trapezoidal_error f 2 a b -
                trapezoidal_error f 1 a b|
                ≤ |2 * trapezoidal_error f 2 a b| +
                    |trapezoidal_error f 1 a b| := abs_sub _ _
            _ = 2 * |trapezoidal_error f 2 a b| +
                    |trapezoidal_error f 1 a b| := by
                  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ 2 * (|b - a| ^ 3 * ζ / (12 * (2 : ℝ) ^ 2)) +
          |b - a| ^ 3 * ζ / (12 * (1 : ℝ) ^ 2) := by
        gcongr
    _ = |b - a| ^ 3 * ζ / 8 := by ring

/-- Exact second derivative of the inverse-log density on the positive
non-singular range. -/
theorem iteratedDeriv_two_invLog_formula
    {x : ℝ} (hx : 1 < x) :
    iteratedDeriv 2 (fun t : ℝ => (Real.log t)⁻¹) x =
      (Real.log x + 2) /
        (x ^ 2 * Real.log x ^ 3) := by
  have hx0 : x ≠ 0 := by linarith
  have hlog0 : Real.log x ≠ 0 :=
    ne_of_gt (Real.log_pos hx)
  rw [show (2 : ℕ) = 1 + 1 by norm_num,
    iteratedDeriv_succ, iteratedDeriv_one,
    Real.deriv_inv_log_apply]
  have hnum :
      HasDerivAt (fun t : ℝ => -(t⁻¹)) ((x ^ 2)⁻¹) x := by
    convert (hasDerivAt_inv hx0).neg using 1 <;> ring
  have hden :
      HasDerivAt (fun t : ℝ => Real.log t ^ 2)
        (2 * Real.log x * x⁻¹) x := by
    convert (Real.hasDerivAt_log hx0).pow 2 using 1 <;> ring
  have hquot :=
    hnum.div hden (pow_ne_zero 2 hlog0)
  convert hquot.deriv using 1
  field_simp [hx0, hlog0]
  ring

/-- A convenient elementary lower bound used to make the inverse-log second
derivative estimate rational. -/
theorem one_lt_log_four : (1 : ℝ) < Real.log 4 := by
  have h2 := Real.log_two_gt_d9
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [h4]
  nlinarith

/-- On square tile r, the second derivative of 1/log is O(r^-4 log(r)^-2).
The constant 4 is intentionally generous. -/
theorem abs_iteratedDeriv_two_invLog_le_squareTile
    {r : ℕ} (hr : 2 ≤ r) {t : ℝ}
    (ht : t ∈ Icc ((r : ℝ) ^ 2)
      ((((r + 1 : ℕ) : ℝ) ^ 2))) :
    |iteratedDeriv 2 (fun u : ℝ => (Real.log u)⁻¹) t| ≤
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
  have hrt : (r : ℝ) ≤ t := by nlinarith
  have hlogle :
      Real.log (r : ℝ) ≤ Real.log t :=
    Real.log_le_log hrpos hrt
  have hlogsq :
      Real.log (r : ℝ) ^ 2 ≤ Real.log t ^ 2 := by
    nlinarith
  have hrpow :
      (r : ℝ) ^ 4 ≤ t ^ 2 := by
    nlinarith [sq_nonneg (t - (r : ℝ) ^ 2)]
  have hden :
      (r : ℝ) ^ 4 * Real.log (r : ℝ) ^ 2 ≤
        t ^ 2 * Real.log t ^ 2 := by
    exact mul_le_mul hrpow hlogsq (sq_nonneg _) (by positivity)
  have hdensmall :
      0 < (r : ℝ) ^ 4 * Real.log (r : ℝ) ^ 2 := by
    positivity
  have hdenbig :
      0 < t ^ 2 * Real.log t ^ 2 := by
    positivity
  rw [iteratedDeriv_two_invLog_formula ht1]
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
      ring
    _ ≤ 3 / ((r : ℝ) ^ 4 * Real.log (r : ℝ) ^ 2) := by
      exact div_le_div_of_nonneg_left
        (by norm_num : (0 : ℝ) ≤ 3) hdensmall hden
    _ ≤ 4 / ((r : ℝ) ^ 4 * Real.log (r : ℝ) ^ 2) := by
      exact div_le_div_of_nonneg_right (by norm_num) hdensmall.le

/-- The inverse-log density is C² on every complete VF square band. -/
theorem contDiffOn_two_invLog_squareTile
    {r : ℕ} (hr : 2 ≤ r) :
    ContDiffOn ℝ 2 (fun t : ℝ => (Real.log t)⁻¹)
      (Icc ((r : ℝ) ^ 2)
        ((((r + 1 : ℕ) : ℝ) ^ 2))) := by
  intro x hx
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hx4 : (4 : ℝ) ≤ x := by
    have hr4 : (4 : ℝ) ≤ (r : ℝ) ^ 2 := by nlinarith
    exact hr4.trans hx.1
  have hx0 : x ≠ 0 := by linarith
  have hx1 : x ≠ 1 := by linarith
  have hxm1 : x ≠ -1 := by linarith
  have hlog0 : Real.log x ≠ 0 :=
    Real.log_ne_zero_of_pos_of_ne_one (by linarith) hx1
  exact ((Real.contDiffAt_log.2 hx0).inv hlog0).contDiffWithinAt

/-- Second-derivative bound in the exact within-interval coordinates expected
by Mathlib's trapezoidal error theorem. -/
theorem abs_iteratedDerivWithin_two_invLog_le_squareTile
    {r : ℕ} (hr : 2 ≤ r) (x : ℝ) :
    |iteratedDerivWithin 2 (fun t : ℝ => (Real.log t)⁻¹)
        (Icc ((r : ℝ) ^ 2)
          ((((r + 1 : ℕ) : ℝ) ^ 2))) x| ≤
      4 / ((r : ℝ) ^ 4 * Real.log (r : ℝ) ^ 2) := by
  let a : ℝ := (r : ℝ) ^ 2
  let b : ℝ := (((r + 1 : ℕ) : ℝ) ^ 2)
  have hab : a < b := by
    dsimp [a, b]
    push_cast
    nlinarith
  have hζ :
      0 ≤ 4 / ((r : ℝ) ^ 4 * Real.log (r : ℝ) ^ 2) := by
    positivity
  by_cases hx : x ∈ Icc a b
  · have hx1 : (1 : ℝ) < x := by
      have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
      dsimp [a] at hx
      nlinarith
    have hx0 : x ≠ 0 := by linarith
    have hlog0 : Real.log x ≠ 0 :=
      ne_of_gt (Real.log_pos hx1)
    have hc :
        ContDiffAt ℝ 2 (fun t : ℝ => (Real.log t)⁻¹) x :=
      (Real.contDiffAt_log.2 hx0).inv hlog0
    rw [iteratedDerivWithin_eq_iteratedDeriv
      (uniqueDiffOn_Icc hab) hc hx]
    exact abs_iteratedDeriv_two_invLog_le_squareTile hr hx
  · rw [iteratedDerivWithin_succ,
      derivWithin_zero_of_notMem_closure (by
        simpa [closure_Icc] using hx)]
    simp
    exact hζ

/-- The complete r-th VF band is exactly the midpoint approximation of the
inverse-log integral over [r²,(r+1)²]. -/
theorem vfMidBandQuadratureError_eq_midpointError
    (r : ℕ) :
    vfMidBandQuadratureError r =
      vfMidpointIntegralError
        (fun t : ℝ => (Real.log t)⁻¹)
        ((r : ℝ) ^ 2)
        ((((r + 1 : ℕ) : ℝ) ^ 2)) := by
  unfold vfMidBandQuadratureError vfMidBandMass vfMidBandIntegral
    vfMidpointIntegralError vfMidpointIntegralApprox vfMidBandMidpoint
  congr 1
  push_cast
  ring

/-- Summable local VF/Li quadrature estimate.  The explicit constant 14 is
loose but the scale 1/(r log(r)^2) is the decisive point. -/
theorem abs_vfMidBandQuadratureError_le_logHarmonic
    {r : ℕ} (hr : 2 ≤ r) :
    |vfMidBandQuadratureError r| ≤
      14 / ((r : ℝ) * Real.log (r : ℝ) ^ 2) := by
  have hf := contDiffOn_two_invLog_squareTile hr
  have hζ := abs_iteratedDerivWithin_two_invLog_le_squareTile hr
  have hmid :=
    abs_vfMidpointIntegralError_le_of_c2
      (f := fun t : ℝ => (Real.log t)⁻¹)
      (a := (r : ℝ) ^ 2)
      (b := (((r + 1 : ℕ) : ℝ) ^ 2))
      (ζ := 4 / ((r : ℝ) ^ 4 * Real.log (r : ℝ) ^ 2))
      hf hζ
  rw [vfMidBandQuadratureError_eq_midpointError] 
  have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hrpos : (0 : ℝ) < (r : ℝ) := by linarith
  have hr1 : (1 : ℝ) < (r : ℝ) := by linarith
  have hlogr : 0 < Real.log (r : ℝ) := Real.log_pos hr1
  have hwidth :
      |(((r + 1 : ℕ) : ℝ) ^ 2) - (r : ℝ) ^ 2| ≤
        3 * (r : ℝ) := by
    push_cast
    have h : (0 : ℝ) ≤
        (((r : ℝ) + 1) ^ 2 - (r : ℝ) ^ 2) := by nlinarith
    rw [abs_of_nonneg h]
    nlinarith
  have hcube :
      |(((r + 1 : ℕ) : ℝ) ^ 2) - (r : ℝ) ^ 2| ^ 3 ≤
        (3 * (r : ℝ)) ^ 3 := by
    exact pow_le_pow_left₀ (abs_nonneg _)
      hwidth 3
  calc
    |vfMidpointIntegralError
        (fun t : ℝ => (Real.log t)⁻¹)
        ((r : ℝ) ^ 2)
        ((((r + 1 : ℕ) : ℝ) ^ 2))|
        ≤ |(((r + 1 : ℕ) : ℝ) ^ 2) - (r : ℝ) ^ 2| ^ 3 *
            (4 / ((r : ℝ) ^ 4 * Real.log (r : ℝ) ^ 2)) / 8 := hmid
    _ ≤ (3 * (r : ℝ)) ^ 3 *
            (4 / ((r : ℝ) ^ 4 * Real.log (r : ℝ) ^ 2)) / 8 := by
          gcongr
          positivity
    _ ≤ 14 / ((r : ℝ) * Real.log (r : ℝ) ^ 2) := by
          field_simp [hrpos.ne', hlogr.ne']
          nlinarith

end RHLean.Analysis
