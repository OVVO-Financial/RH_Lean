import Mathlib
import «research.VF_MID_919_GENERAL_X_HIGH_QUOTIENT_ISOLATION»
import «research.CORR4_FIXED_HYPERBOLA_DOUBLE_ABEL_20261026»

/-!
# CORR-4: uniform constant-four high-quotient Abel payment

The core inequality is deterministic, with a nonnegative monotone ramp.
It uses the literal period-36 quotient kernel (sup norm <= 2) and the
already proved actual Eisenstein coefficient norm-mass <= N.

No mean-zero hypothesis, Mertens estimate, RH assumption, or signed
low-quotient saving enters the proof.
-/

noncomputable section
open scoped BigOperators
namespace RHLean.Analysis

/-- An Abel identity over an arbitrary nonempty integer interval. In the
upper-tail application the final boundary vanishes but the lower one
must be retained. -/
theorem corr4_abel_on_Icc_real (k w : ℕ → ℝ) (L U : ℕ)
    (hL : 1 ≤ L) (hLU : L ≤ U) :
    (∑ u ∈ Finset.Icc L U, (k u - k (u - 1)) * w u) =
      (∑ u ∈ Finset.Icc L U, k u * (w u - w (u + 1))) -
      k (L - 1) * w L + k U * w (U + 1) := by
  induction U, hLU using Nat.le_induction with
  | base =>
      simp only [Finset.sum_Icc_self]
      ring
  | succ U hLU ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      rw [Finset.sum_Icc_succ_top (by omega)]
      rw [ih, show U + 1 - 1 = U by omega]
      ring

/-- The required nonnegative variation telescopes before the absolute
values of the genuine Hecke coefficients are taken. -/
theorem corr4_Icc_successive_difference_telescope
    (w : ℕ → ℝ) (L U : ℕ) (hLU : L ≤ U) :
    (∑ u ∈ Finset.Icc L U, (w u - w (u + 1))) =
      w L - w (U + 1) := by
  induction U, hLU using Nat.le_induction with
  | base =>
      simp only [Finset.sum_Icc_self]
  | succ U hLU ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih]
      ring

/-- The constant four is 2 for the boundary plus 2 for the total
monotone variation, not two applications of an assumed cancellation. -/
theorem corr4_monotone_differenced_kernel_bound
    (k w : ℕ → ℝ) (L U : ℕ)
    (hL : 1 ≤ L) (hLU : L ≤ U)
    (hk : ∀ u, |k u| ≤ 2)
    (hweight : 0 ≤ w L)
    (hdesc : ∀ u ∈ Finset.Icc L U, w (u + 1) ≤ w u)
    (hfinal : w (U + 1) = 0) :
    |∑ u ∈ Finset.Icc L U, (k u - k (u - 1)) * w u| ≤
      4 * w L := by
  have htel := corr4_Icc_successive_difference_telescope w L U hLU
  have hAbel := corr4_abel_on_Icc_real k w L U hL hLU
  have hterms :
      (∑ u ∈ Finset.Icc L U, |k u * (w u - w (u + 1))|) ≤
        ∑ u ∈ Finset.Icc L U, 2 * (w u - w (u + 1)) := by
    apply Finset.sum_le_sum
    intro u hu
    have hpos : 0 ≤ w u - w (u + 1) := sub_nonneg.mpr (hdesc u hu)
    rw [abs_mul, abs_of_nonneg hpos]
    exact mul_le_mul_of_nonneg_right (hk u) hpos
  have hboundary : |k (L - 1) * w L| ≤ 2 * w L := by
    rw [abs_mul, abs_of_nonneg hweight]
    exact mul_le_mul_of_nonneg_right (hk (L - 1)) hweight
  calc
    |∑ u ∈ Finset.Icc L U, (k u - k (u - 1)) * w u| =
        |(∑ u ∈ Finset.Icc L U, k u * (w u - w (u + 1))) -
          k (L - 1) * w L| := by rw [hAbel, hfinal]; ring
    _ ≤ |∑ u ∈ Finset.Icc L U, k u * (w u - w (u + 1))| +
          |k (L - 1) * w L| := abs_sub_le _ _
    _ ≤ (∑ u ∈ Finset.Icc L U, |k u * (w u - w (u + 1))|) +
          |k (L - 1) * w L| := by
            exact add_le_add_right (Finset.abs_sum_le_sum_abs _ _) _
    _ ≤ (∑ u ∈ Finset.Icc L U, 2 * (w u - w (u + 1))) +
          2 * w L := add_le_add hterms hboundary
    _ = 4 * w L := by rw [← Finset.mul_sum, htel, hfinal]; ring

/-- The literal restored 36-quotient kernel has norm at most two.
No separate equidistribution argument is needed. -/
theorem corr4_sharp_quotient_kernel_real_abs_le_two (u : ℕ) :
    |(vf919SharpQuotientKernel36 u : ℝ)| ≤ 2 := by
  have hb := vf919SharpQuotientKernel36_bounds u
  have habs : |vf919SharpQuotientKernel36 u| ≤ (2 : ℤ) :=
    abs_le.mpr ⟨hb.1, by omega⟩
  exact_mod_cast habs

/-- Application of the monotone weight lemma to the actual integer
quotient kernel, with the complex cast used in #919. -/
theorem corr4_monotone_sharp_kernel_complex_norm
    (w : ℕ → ℝ) (L U : ℕ)
    (hL : 1 ≤ L) (hLU : L ≤ U)
    (hweight : 0 ≤ w L)
    (hdesc : ∀ u ∈ Finset.Icc L U, w (u + 1) ≤ w u)
    (hfinal : w (U + 1) = 0) :
    ‖∑ u ∈ Finset.Icc L U,
        ((vf919SharpQuotientKernel36 u : ℂ) -
         (vf919SharpQuotientKernel36 (u - 1) : ℂ)) *
           (w u : ℂ)‖ ≤ 4 * w L := by
  have hr := corr4_monotone_differenced_kernel_bound
    (fun u => (vf919SharpQuotientKernel36 u : ℝ))
    w L U hL hLU corr4_sharp_quotient_kernel_real_abs_le_two
    hweight hdesc hfinal
  have hc :
      (∑ u ∈ Finset.Icc L U,
        ((vf919SharpQuotientKernel36 u : ℂ) -
         (vf919SharpQuotientKernel36 (u - 1) : ℂ)) * (w u : ℂ)) =
      ((∑ u ∈ Finset.Icc L U,
        ((vf919SharpQuotientKernel36 u : ℝ) -
         (vf919SharpQuotientKernel36 (u - 1) : ℝ)) * w u) : ℂ) := by
    push_cast
    rfl
  rw [hc, Complex.norm_real, Real.norm_eq_abs]
  exact hr

end RHLean.Analysis
