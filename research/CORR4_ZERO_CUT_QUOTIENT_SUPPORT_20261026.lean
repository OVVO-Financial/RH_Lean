import Mathlib
import «research.CORR4_PHYSICAL_TENT_CONSTANT_FOUR_20261026»

/-!
# CORR-4: exact zero-boundary low-quotient support

The 36-period quotient kernel is zero at multiples of 36. Choosing
L=36q+1 makes K(L-1)=0 and removes the low-quotient artificial
small-norm constant. In the literal physical tent every m satisfying
L*m + (H-1) <= X then contributes *exactly zero* to the low-u sum.

This is a source-support identity. It does not prove the remaining
ultra-high-norm signed power saving.
-/

noncomputable section
open scoped BigOperators
namespace RHLean.Analysis

theorem corr4_quotient_kernel_zero_at_36_multiple (q : ℕ) :
    vf919SharpQuotientKernel36 (36 * q) = 0 := by
  rw [vf919SharpQuotientKernel36_mod]
  have hmod : (36 * q) % 36 = 0 := by omega
  rw [hmod]
  norm_num [vf919SharpQuotientKernel36,
    vf919IntegerCharacterPrefix_eq_residue]

/-- Unrestricted finite difference telescope, including n=0. -/
theorem corr4_quotient_difference_prefix_telescope (N : ℕ) :
    (∑ u ∈ Finset.Icc 1 N, corr4SharpQuotientDifference u) =
      (vf919SharpQuotientKernel36 N : ℂ) := by
  induction N with
  | zero =>
      simp [corr4_sharp_quotient_kernel_zero]
  | succ N ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
      rw [ih]
      change (vf919SharpQuotientKernel36 N : ℂ) +
        ((vf919SharpQuotientKernel36 (N + 1) : ℂ) -
          (vf919SharpQuotientKernel36 ((N + 1) - 1) : ℂ)) =
        (vf919SharpQuotientKernel36 (N + 1) : ℂ)
      rw [show N + 1 - 1 = N by omega]
      ring

/-- Literal two-box tent is exactly one when every shifted physical
threshold admits n. No continuous replacement is used. -/
theorem corr4TentRamp_eq_one_of_below
    (X H n : ℕ) (hH : 0 < H) (hbelow : n + (H - 1) ≤ X) :
    corr4TentRamp X H n = 1 := by
  have hsum :
      (∑ i ∈ Finset.range H,
        ∑ j ∈ Finset.range H,
          if n + (H - 1) ≤ X + i + j then (1 : ℝ) else 0) =
        (H : ℝ) ^ 2 := by
    calc
      _ = ∑ i ∈ Finset.range H,
            ∑ _j ∈ Finset.range H, (1 : ℝ) := by
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            have ht : n + (H - 1) ≤ X + i + j := by omega
            simp [ht]
      _ = (H : ℝ) ^ 2 := by simp [pow_two]
  unfold corr4TentRamp
  rw [hsum]
  exact div_self (ne_of_gt (pow_pos (Nat.cast_pos.mpr hH) 2))

/-- Exact cancellation of a low-quotient physical occurrence lying below
the norm cutoff. This closes the boundary caveat in the low-u/ultra-high-m
coordinate identification when L is aligned with the period-36 zero. -/
theorem corr4_low_quotient_tent_zero_for_small_norm
    (X H L q m : ℕ) (hH : 0 < H) (hL : L = 36 * q + 1)
    (hdeep : L * m + (H - 1) ≤ X) :
    (∑ u ∈ Finset.Icc 1 (L - 1),
      corr4SharpQuotientDifference u *
        (corr4TentRamp X H (u * m) : ℂ)) = 0 := by
  have hw : ∀ u ∈ Finset.Icc 1 (L - 1),
      corr4TentRamp X H (u * m) = 1 := by
    intro u hu
    have huL : u ≤ L := by
      have hu' := (Finset.mem_Icc.mp hu).2
      omega
    have hum : u * m ≤ L * m := Nat.mul_le_mul_right m huL
    apply corr4TentRamp_eq_one_of_below X H (u * m) hH
    omega
  calc
    (∑ u ∈ Finset.Icc 1 (L - 1),
        corr4SharpQuotientDifference u *
          (corr4TentRamp X H (u * m) : ℂ)) =
      ∑ u ∈ Finset.Icc 1 (L - 1), corr4SharpQuotientDifference u := by
        apply Finset.sum_congr rfl
        intro u hu
        rw [hw u hu]
        norm_num
    _ = (vf919SharpQuotientKernel36 (L - 1) : ℂ) :=
      corr4_quotient_difference_prefix_telescope (L - 1)
    _ = 0 := by
      have hindex : L - 1 = 36 * q := by omega
      rw [hindex, corr4_quotient_kernel_zero_at_36_multiple]
      norm_num

#print axioms corr4_quotient_kernel_zero_at_36_multiple
#print axioms corr4_quotient_difference_prefix_telescope
#print axioms corr4TentRamp_eq_one_of_below
#print axioms corr4_low_quotient_tent_zero_for_small_norm

end RHLean.Analysis
