import Mathlib
import RHLean.Analysis.OptimalLogBase
import «research.VF_MID_VON_KOCH_BRIDGE»

/-!
# Exact optimal-base coordinate for fantasy-channel transport

For a fixed cutoff x > 1, the scalar map

  B_x(y) = exp (y * log x / x)

is the exact optimal logarithmic base corresponding to count value y.  It
reconstructs y through x / log_b x and is strictly order preserving.

This file contains only the generic coordinate facts.  Existing VF fantasy
boundaries are transported through this map in
VF_MID_EXISTING_BOUNDARY_OPTIMAL_BASE, keeping the boundary geometry separate
from the change-of-coordinate algebra.
-/

noncomputable section

namespace RHLean.Analysis

/-- Exact optimal-base map applied to one scalar count value. -/
def optimalLogBaseValue (y x : ℝ) : ℝ :=
  Real.exp (y * Real.log x / x)

/-- The function-valued optimal base already in the repository is exactly the
scalar optimal-base map at its realized count value. -/
@[simp] theorem optimalLogBase_eq_value (P : ℝ → ℝ) (x : ℝ) :
    optimalLogBase P x = optimalLogBaseValue (P x) x := by
  rfl

/-- Exact reconstruction from a scalar optimal-base coordinate. -/
theorem optimalLogBaseValue_reconstructs
    {x y : ℝ} (hx : x ≠ 0) (hlogx : Real.log x ≠ 0) :
    x * Real.log (optimalLogBaseValue y x) / Real.log x = y := by
  unfold optimalLogBaseValue
  rw [Real.log_exp]
  field_simp [hx, hlogx]

/-- For fixed x > 1, the optimal-base coordinate preserves and reflects
count-space order exactly. -/
theorem optimalLogBaseValue_le_iff
    {x a b : ℝ} (hx : 1 < x) :
    optimalLogBaseValue a x ≤ optimalLogBaseValue b x ↔ a ≤ b := by
  have hxpos : 0 < x := lt_trans (by norm_num) hx
  have hlogpos : 0 < Real.log x := Real.log_pos hx
  unfold optimalLogBaseValue
  rw [Real.exp_le_exp]
  constructor
  · intro h
    have hmul :
        a * Real.log x ≤ b * Real.log x :=
      (div_le_div_iff_of_pos_right hxpos).1 h
    exact (mul_le_mul_right hlogpos).1 hmul
  · intro h
    apply (div_le_div_iff_of_pos_right hxpos).2
    exact (mul_le_mul_right hlogpos).2 h

/-- Every two-sided count-space bracket transports losslessly to optimal-base
coordinates. -/
theorem optimalLogBaseValue_between_iff
    {x L y U : ℝ} (hx : 1 < x) :
    (optimalLogBaseValue L x ≤ optimalLogBaseValue y x ∧
      optimalLogBaseValue y x ≤ optimalLogBaseValue U x) ↔
    (L ≤ y ∧ y ≤ U) := by
  constructor
  · rintro ⟨hL, hU⟩
    exact ⟨(optimalLogBaseValue_le_iff hx).1 hL,
      (optimalLogBaseValue_le_iff hx).1 hU⟩
  · rintro ⟨hL, hU⟩
    exact ⟨(optimalLogBaseValue_le_iff hx).2 hL,
      (optimalLogBaseValue_le_iff hx).2 hU⟩

/-! ## Coarse classical outer cage -/

/-- Exact rational form of the classical Rosser-Schoenfeld coefficient
1.25506. -/
def primeOptimalBaseOuterCoefficient : ℝ :=
  62753 / 50000

/-- The corresponding fixed upper optimal-base wall. -/
def primeOptimalBaseOuterUpper : ℝ :=
  Real.exp primeOptimalBaseOuterCoefficient

/-- Classical count-space corridor needed to instantiate the fixed outer
optimal-base cage.  This proposition is intentionally separated because the
current repository does not yet contain a kernel-checked proof of the explicit
Rosser-Schoenfeld inequalities themselves. -/
def ClassicalPrimeCountOuterCorridor : Prop :=
  ∀ x : ℝ, 17 ≤ x →
    x / Real.log x ≤ vfMidPrimeCount x ∧
      vfMidPrimeCount x ≤
        primeOptimalBaseOuterCoefficient * x / Real.log x

/-- The lower logarithmic model x/log(x) has optimal base exactly e. -/
theorem optimalLogBaseValue_x_div_log_eq_e
    {x : ℝ} (hx : 1 < x) :
    optimalLogBaseValue (x / Real.log x) x = Real.exp 1 := by
  have hxpos : 0 < x := lt_trans (by norm_num) hx
  have hlogne : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  unfold optimalLogBaseValue
  congr 1
  field_simp [hxpos.ne', hlogne]

/-- The upper logarithmic model c*x/log(x) has optimal base exactly exp(c). -/
theorem optimalLogBaseValue_coeff_mul_x_div_log
    (c : ℝ) {x : ℝ} (hx : 1 < x) :
    optimalLogBaseValue (c * x / Real.log x) x = Real.exp c := by
  have hxpos : 0 < x := lt_trans (by norm_num) hx
  have hlogne : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  unfold optimalLogBaseValue
  congr 1
  field_simp [hxpos.ne', hlogne]

/-- A classical x/log(x) to 1.25506*x/log(x) count corridor becomes the fixed
optimal-base cage [e, exp(1.25506)] exactly. -/
theorem actualPrimeOptimalBase_mem_fixed_outer_cage
    (hcorr : ClassicalPrimeCountOuterCorridor)
    {x : ℝ} (hx : 17 ≤ x) :
    Real.exp 1 ≤ optimalLogBase vfMidPrimeCount x ∧
      optimalLogBase vfMidPrimeCount x ≤ primeOptimalBaseOuterUpper := by
  have hx1 : 1 < x := by linarith
  have hcount := hcorr x hx
  rw [optimalLogBase_eq_value]
  have hbase :=
    (optimalLogBaseValue_between_iff
      (x := x)
      (L := x / Real.log x)
      (y := vfMidPrimeCount x)
      (U := primeOptimalBaseOuterCoefficient * x / Real.log x)
      hx1).2 hcount
  rw [optimalLogBaseValue_x_div_log_eq_e hx1,
    optimalLogBaseValue_coeff_mul_x_div_log
      primeOptimalBaseOuterCoefficient hx1] at hbase
  exact hbase

/-- The fixed upper wall is below exp(4/3). -/
theorem primeOptimalBaseOuterUpper_lt_exp_four_thirds :
    primeOptimalBaseOuterUpper < Real.exp (4 / 3 : ℝ) := by
  unfold primeOptimalBaseOuterUpper primeOptimalBaseOuterCoefficient
  rw [Real.exp_lt_exp]
  norm_num

end RHLean.Analysis
