import Mathlib

/-! Exact reconciliation cost for a common scalar on the original paired
depth layers. The scalar is constrained by the measured exterior norm.
This is an elementary quantitative test of the forward comparison,
not a new conditional RH supplier. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace RHLean.Analysis.NativeCommonScalarCost

/-- Necessary row content after multiplication by a scalar of valuation a
and a depth ratio of valuation s. -/
def rowBill (s a : ℝ) : ℝ := max 0 (-(a + s))

/-- Conjugate scalar phases cannot beat the balanced valuation. -/
theorem paired_row (s a b μ : ℝ) (h : a + b = -2 * μ) :
    2 * rowBill s (-μ) ≤ rowBill s a + rowBill s b := by
  unfold rowBill
  have ha : -(a+s) ≤ max 0 (-(a+s)) := le_max_right _ _
  have hb : -(b+s) ≤ max 0 (-(b+s)) := le_max_right _ _
  by_cases h0 : 0 ≤ -(-μ+s)
  · rw [max_eq_right h0]
    linarith only [ha,hb,h]
  · rw [max_eq_left (le_of_lt (lt_of_not_ge h0))]
    have h1 : 0 ≤ max 0 (-(a+s)) := le_max_left _ _
    have h2 : 0 ≤ max 0 (-(b+s)) := le_max_left _ _
    linarith only [h1,h2]

theorem balanced_row (s μ : ℝ) :
    2 * rowBill s (-μ) = |s-μ| - (s-μ) := by
  unfold rowBill
  by_cases h : 0 ≤ s-μ
  · rw [abs_of_nonneg h, max_eq_left (show -(-μ+s) ≤ 0 by linarith)]
    ring
  · rw [abs_of_neg (lt_of_not_ge h),
      max_eq_right (show 0 ≤ -(-μ+s) by linarith)]
    ring

/-- On the entire retained profile, the balanced paired bill is exactly
the absolute deviation from the central valuation. -/
theorem balanced_total {I : Type*} [Fintype I] (s : I → ℝ) (μ : ℝ)
    (hcenter : ∑ i, (s i-μ) = 0) :
    (∑ i, 2 * rowBill (s i) (-μ)) = ∑ i, |s i-μ| := by
  simp_rw [balanced_row]
  rw [Finset.sum_sub_distrib,hcenter,sub_zero]

/-- A phase-sensitive paired valuation comparison on all rows, including
multiple incidences of a prime. No primitivity or positive-definiteness
shortcut is used in this scalar arithmetic. -/
theorem paired_total {I : Type*} [Fintype I] (s : I → ℝ) (a b μ : ℝ)
    (h : a+b = -2*μ) (hcenter : ∑ i, (s i-μ) = 0) :
    (∑ i, |s i-μ|) ≤ ∑ i, (rowBill (s i) a + rowBill (s i) b) := by
  rw [← balanced_total s μ hcenter]
  exact Finset.sum_le_sum fun i _ => paired_row (s i) a b μ h

/-- Keep the two finite determinant-clearing allowances rather than
assigning zero cost to a place-dependent repair. -/
theorem paid_determinants {I : Type*} [Fintype I] (s : I → ℝ)
    (a b μ d d' e e' : ℝ)
    (h : a+b = -2*μ) (hcenter : ∑ i, (s i-μ) = 0)
    (ha : (∑ i, rowBill (s i) a) ≤ d+e)
    (hb : (∑ i, rowBill (s i) b) ≤ d'+e') :
    (∑ i, |s i-μ|) ≤ d+d'+e+e' := by
  have hh := paired_total s a b μ h hcenter
  rw [Finset.sum_add_distrib] at hh
  linarith only [hh,ha,hb]

end RHLean.Analysis.NativeCommonScalarCost
