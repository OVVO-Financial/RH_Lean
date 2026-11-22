import «research.ALPOGE_RECIPROCAL_SQUARE_CELL»

/-! The even-exponent prime powers in the principal reciprocal-cell quadrature.
This estimates only their Lambda part, not the drift or any character-twisted source. -/

noncomputable section
open scoped BigOperators ArithmeticFunction.vonMangoldt

namespace RHLean.Analysis

/-- The first site of each square cell has a positive kernel of order at most r^-3. -/
theorem alpogeSquareCell_first_site_bound (r : ℕ) (hr : 2 ≤ r) :
    0 < alpogeReciprocalCellKernel (r ^ 2 - 1) ((r + 1) ^ 2 - 1) (r ^ 2) ∧
    alpogeReciprocalCellKernel (r ^ 2 - 1) ((r + 1) ^ 2 - 1) (r ^ 2) ≤ 1 / (r : ℝ) ^ 3 := by
  have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := by linarith
  have ha : 0 < (r : ℝ) ^ 2 - 1 := by nlinarith [sq_nonneg ((r : ℝ) - 1)]
  have hb : 0 < (r : ℝ) ^ 2 + 2 * r := by positivity
  constructor
  · exact (alpogeSquareCell_kernel_sign r (r ^ 2) hr (pow_pos (by omega) 2)).1.2 (by omega)
  · have hc : (((r + 1) ^ 2 - 1 : ℕ) : ℝ) = (r : ℝ) ^ 2 + 2 * r := by
      rw [Nat.cast_sub (Nat.one_le_pow 2 (r + 1) (by omega))]
      push_cast
      ring
    unfold alpogeReciprocalCellKernel
    rw [hc, Nat.cast_sub (Nat.one_le_pow 2 r (by omega))]
    push_cast
    calc
      _ ≤ (1 / (r : ℝ) ^ 2 - 1 / ((r : ℝ) ^ 2 + 2 * r)) / 2 := by
        have he := one_div_le_one_div_of_le ha (show (r : ℝ) ^ 2 - 1 ≤ (r : ℝ) ^ 2 by linarith)
        linarith only [he]
      _ = 1 / ((r : ℝ) * ((r : ℝ) ^ 2 + 2 * r)) := by field_simp; ring
      _ ≤ 1 / (r : ℝ) ^ 3 := by
        apply one_div_le_one_div_of_le (by positivity)
        nlinarith [sq_nonneg (r : ℝ)]

/-- All even prime powers occur once among these first sites, with their original
von Mangoldt weight. The sole mass input is the elementary native Chebyshev bound. -/
theorem alpogeSquareCell_dyadic_even_power_cost (h : ℕ) (hh : 2 ≤ h) :
    0 ≤ (∑ r ∈ Finset.Ico h (2 * h), Λ (r ^ 2) *
      alpogeReciprocalCellKernel (r ^ 2 - 1) ((r + 1) ^ 2 - 1) (r ^ 2)) ∧
    (∑ r ∈ Finset.Ico h (2 * h), Λ (r ^ 2) *
      alpogeReciprocalCellKernel (r ^ 2 - 1) ((r + 1) ^ 2 - 1) (r ^ 2)) ≤
      2 * (Real.log 4 + 2) / (h : ℝ) ^ 2 := by
  have hh0 : (0 : ℝ) < h := by exact_mod_cast (show 0 < h by omega)
  simp only [ArithmeticFunction.vonMangoldt_apply_pow (by decide : (2 : ℕ) ≠ 0)]
  constructor
  · apply Finset.sum_nonneg
    intro r hr
    exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (alpogeSquareCell_first_site_bound r (hh.trans (Finset.mem_Ico.mp hr).1)).1.le
  · have hmass : (∑ r ∈ Finset.Ico h (2 * h), Λ r) ≤ nativePsi (2 * h) := by
      unfold nativePsi
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro r hr
        obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hr
        exact Finset.mem_Icc.mpr ⟨by omega, hhi.le⟩
      · intro r _ _
        exact ArithmeticFunction.vonMangoldt_nonneg
    calc
      _ ≤ ∑ r ∈ Finset.Ico h (2 * h), Λ r * (1 / (h : ℝ) ^ 3) := by
        apply Finset.sum_le_sum
        intro r hr
        have hle := (Finset.mem_Ico.mp hr).1
        have hleR : (h : ℝ) ≤ r := by exact_mod_cast hle
        apply mul_le_mul_of_nonneg_left _ ArithmeticFunction.vonMangoldt_nonneg
        exact (alpogeSquareCell_first_site_bound r (hh.trans hle)).2.trans
          (one_div_le_one_div_of_le (by positivity) (by gcongr))
      _ = (∑ r ∈ Finset.Ico h (2 * h), Λ r) * (1 / (h : ℝ) ^ 3) := (Finset.sum_mul ..).symm
      _ ≤ ((Real.log 4 + 2) * ((2 * h : ℕ) : ℝ)) * (1 / (h : ℝ) ^ 3) :=
        mul_le_mul_of_nonneg_right (hmass.trans (nativePsi_le_const_mul (2 * h))) (by positivity)
      _ = _ := by push_cast; field_simp; ring

end RHLean.Analysis

/-- info: 'RHLean.Analysis.alpogeSquareCell_first_site_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RHLean.Analysis.alpogeSquareCell_first_site_bound
/-- info: 'RHLean.Analysis.alpogeSquareCell_dyadic_even_power_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms RHLean.Analysis.alpogeSquareCell_dyadic_even_power_cost
