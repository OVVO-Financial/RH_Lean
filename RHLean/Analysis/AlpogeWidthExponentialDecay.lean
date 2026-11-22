import Mathlib

/-!
# Every fixed power beats the explicit full-profile width curvature

This is an ordinary real-variable asymptotic theorem. It has no arithmetic
source or RH-strength hypothesis. The exponent epsilon is fixed and positive;
the threshold is allowed to depend on epsilon and the fixed polynomial data.

The Mathlib input is `tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero`, at the
repository's pinned Mathlib revision d13f23b723b8a846827a245b89c10fc7d3f11612.
Substituting y=x^(epsilon/3) reduces the exponential to exp(2y-2y^3), which
is at most exp(-y) for y>=2. This preserves the full exponent difference.
-/

noncomputable section
open Filter
open scoped Topology

namespace RHLean.Analysis

/-- Explicit stretched-exponential width costs are eventually below any
fixed inverse power, with all constants and exponents fixed before x. -/
theorem alpogeWidthExponentialCost_eventually_le_rpow
    (C A B epsilon : ℝ) (hC : 0 ≤ C) (hepsilon : 0 < epsilon) :
    ∀ᶠ x : ℝ in atTop,
      C * x ^ A * Real.exp (2 * x ^ (epsilon / 3) - 2 * x ^ epsilon) ≤
        x ^ (-B) := by
  let s : ℝ := 3 * (A + B) / epsilon
  have hy : Tendsto (fun x : ℝ => x ^ (epsilon / 3)) atTop atTop :=
    tendsto_rpow_atTop (by positivity)
  have hdecay : Tendsto
      (fun x : ℝ => C * (x ^ (epsilon / 3)) ^ s *
        Real.exp (-(x ^ (epsilon / 3)))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_mul, one_mul, mul_zero, mul_assoc] using
      (((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero s 1 (by norm_num)).comp hy)
        .const_mul C)
  filter_upwards [eventually_ge_atTop (1 : ℝ), hy.eventually_ge_atTop 2,
    hdecay.eventually_lt_const (by norm_num : (0 : ℝ) < 1)] with x hx hy2 hsmall
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hy0 : 0 ≤ x ^ (epsilon / 3) := Real.rpow_nonneg hx0.le _
  have hcube : (x ^ (epsilon / 3)) ^ (3 : ℕ) = x ^ epsilon := by
    calc
      _ = (x ^ (epsilon / 3)) ^ (3 : ℝ) := (Real.rpow_natCast _ 3).symm
      _ = x ^ ((epsilon / 3) * 3) := (Real.rpow_mul hx0.le _ _).symm
      _ = _ := by congr 1; ring
  have hs : (epsilon / 3) * s = A + B := by
    dsimp [s]
    field_simp [hepsilon.ne']
  have hpower : (x ^ (epsilon / 3)) ^ s = x ^ (A + B) := by
    rw [← Real.rpow_mul hx0.le, hs]
  have harg : 2 * x ^ (epsilon / 3) - 2 * x ^ epsilon ≤
      -(x ^ (epsilon / 3)) := by
    rw [← hcube]
    have hsq : 0 ≤ (x ^ (epsilon / 3)) ^ 2 - 4 := by
      nlinarith [sq_nonneg (x ^ (epsilon / 3) - 2)]
    nlinarith [mul_nonneg hy0 hsq]
  have hsmall' : C * x ^ (A + B) *
      Real.exp (-(x ^ (epsilon / 3))) < 1 := by
    simpa only [hpower] using hsmall
  have hpaid : C * x ^ (A + B) *
      Real.exp (2 * x ^ (epsilon / 3) - 2 * x ^ epsilon) ≤ 1 := by
    calc
      _ ≤ C * x ^ (A + B) * Real.exp (-(x ^ (epsilon / 3))) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg)
          (mul_nonneg hC (Real.rpow_nonneg hx0.le _))
      _ ≤ 1 := hsmall'.le
  apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hx0 B)).mp
  calc
    _ = C * x ^ (A + B) *
        Real.exp (2 * x ^ (epsilon / 3) - 2 * x ^ epsilon) := by
      rw [Real.rpow_add hx0]
      ring
    _ ≤ 1 := hpaid
    _ = x ^ (-B) * x ^ B := by
      rw [← Real.rpow_add hx0]
      simp

/-- The fully accounted RankVal/HostVal/HCVal numerical width ledger has
arbitrary inverse-power decay. The geometric/source instance still needs its
same-family hypotheses; this theorem closes the asymptotic scalar payment. -/
theorem alpogeNativeHC_width_ledger_eventually_le_rpow
    (ch B epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ x : ℝ in atTop,
      128 * x ^ (2 * ch + 6 + 17 * epsilon) *
        Real.exp (2 * x ^ (epsilon / 3) - 2 * x ^ epsilon) ≤ x ^ (-B) :=
  alpogeWidthExponentialCost_eventually_le_rpow
    128 (2 * ch + 6 + 17 * epsilon) B epsilon (by norm_num) hepsilon

end RHLean.Analysis
