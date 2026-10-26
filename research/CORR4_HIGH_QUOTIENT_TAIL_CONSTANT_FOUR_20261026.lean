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
    (_hL : 1 ≤ L) (hLU : L ≤ U) :
    (∑ u ∈ Finset.Icc L U, (k u - k (u - 1)) * w u) =
      (∑ u ∈ Finset.Icc L U, k u * (w u - w (u + 1))) -
      k (L - 1) * w L + k U * w (U + 1) := by
  induction U, hLU using Nat.le_induction with
  | base =>
      simp only [Finset.Icc_self, Finset.sum_singleton]
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
      simp only [Finset.Icc_self, Finset.sum_singleton]
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
          |k (L - 1) * w L| := by
            simpa only [sub_eq_add_neg, abs_neg] using
              (abs_add_le
                (∑ u ∈ Finset.Icc L U, k u * (w u - w (u + 1)))
                (-(k (L - 1) * w L)))
    _ ≤ (∑ u ∈ Finset.Icc L U, |k u * (w u - w (u + 1))|) +
          |k (L - 1) * w L| := by
            exact add_le_add (Finset.abs_sum_le_sum_abs _ _) le_rfl
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
  have hnormReal (r : ℝ) : ‖(r : ℂ)‖ = |r| := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  have hc :
      (∑ u ∈ Finset.Icc L U,
        ((vf919SharpQuotientKernel36 u : ℂ) -
         (vf919SharpQuotientKernel36 (u - 1) : ℂ)) * (w u : ℂ)) =
      ((∑ u ∈ Finset.Icc L U,
        ((vf919SharpQuotientKernel36 u : ℝ) -
         (vf919SharpQuotientKernel36 (u - 1) : ℝ)) * w u) : ℂ) := by
    push_cast
    rfl
  calc
    ‖∑ u ∈ Finset.Icc L U,
        ((vf919SharpQuotientKernel36 u : ℂ) -
         (vf919SharpQuotientKernel36 (u - 1) : ℂ)) * (w u : ℂ)‖ =
      ‖((∑ u ∈ Finset.Icc L U,
          ((vf919SharpQuotientKernel36 u : ℝ) -
           (vf919SharpQuotientKernel36 (u - 1) : ℝ)) * w u) : ℂ)‖ :=
        congrArg norm hc
    _ = |∑ u ∈ Finset.Icc L U,
          ((vf919SharpQuotientKernel36 u : ℝ) -
           (vf919SharpQuotientKernel36 (u - 1) : ℝ)) * w u| :=
          hnormReal _
    _ ≤ 4 * w L := hr


/-- The literal difference of adjacent period-36 coefficients in the
original #919 norm carrier. -/
def corr4SharpQuotientDifference (u : ℕ) : ℂ :=
  (vf919SharpQuotientKernel36 u : ℂ) -
    (vf919SharpQuotientKernel36 (u - 1) : ℂ)

/-- The exact mass lemma applied only after one signed Abel transform.
Every physical norm coefficient occurs once, with its original complex
value, not an ad hoc probability or absolute coefficient replacement.

The hypotheses on w are verified by nonnegative tent ramps (below).
The terminal assumption is precisely what closes the upper Abel boundary. -/
theorem corr4_actual_a6_monotone_weight_tail_le_four_mass
    (L U T N : ℕ) (w : ℕ → ℕ → ℝ)
    (hL : 1 ≤ L) (hLU : L ≤ U)
    (hwpos : ∀ m ∈ Finset.Ioc T N, 0 ≤ w m L)
    (hwdesc : ∀ m ∈ Finset.Ioc T N,
      ∀ u ∈ Finset.Icc L U, w m (u + 1) ≤ w m u)
    (hwzero : ∀ m ∈ Finset.Ioc T N, w m (U + 1) = 0)
    (hwunit : ∀ m ∈ Finset.Ioc T N, w m L ≤ 1) :
    ‖∑ u ∈ Finset.Icc L U,
        corr4SharpQuotientDifference u *
          (∑ m ∈ Finset.Ioc T N,
            vf919ExcludedNormCoefficients m * (w m u : ℂ))‖ ≤
       4 * (N : ℝ) := by
  have hswap :
      (∑ u ∈ Finset.Icc L U,
        corr4SharpQuotientDifference u *
          (∑ m ∈ Finset.Ioc T N,
            vf919ExcludedNormCoefficients m * (w m u : ℂ))) =
      (∑ m ∈ Finset.Ioc T N,
        vf919ExcludedNormCoefficients m *
          (∑ u ∈ Finset.Icc L U,
            corr4SharpQuotientDifference u * (w m u : ℂ))) := by
    calc
      _ = ∑ u ∈ Finset.Icc L U,
            ∑ m ∈ Finset.Ioc T N,
              corr4SharpQuotientDifference u *
                (vf919ExcludedNormCoefficients m * (w m u : ℂ)) := by
           apply Finset.sum_congr rfl
           intro u hu
           rw [Finset.mul_sum]
      _ = ∑ m ∈ Finset.Ioc T N,
            ∑ u ∈ Finset.Icc L U,
              corr4SharpQuotientDifference u *
                (vf919ExcludedNormCoefficients m * (w m u : ℂ)) := Finset.sum_comm
      _ = ∑ m ∈ Finset.Ioc T N,
            vf919ExcludedNormCoefficients m *
              (∑ u ∈ Finset.Icc L U,
                corr4SharpQuotientDifference u * (w m u : ℂ)) := by
           apply Finset.sum_congr rfl
           intro m hm
           rw [Finset.mul_sum]
           apply Finset.sum_congr rfl
           intro u hu
           ring
  have hpoint : ∀ m ∈ Finset.Ioc T N,
      ‖∑ u ∈ Finset.Icc L U,
           corr4SharpQuotientDifference u * (w m u : ℂ)‖ ≤ 4 := by
    intro m hm
    have ha := corr4_monotone_sharp_kernel_complex_norm
      (w m) L U hL hLU (hwpos m hm) (hwdesc m hm) (hwzero m hm)
    change ‖∑ u ∈ Finset.Icc L U,
        corr4SharpQuotientDifference u * (w m u : ℂ)‖ ≤
          4 * w m L at ha
    have hv := hwunit m hm
    linarith
  have hsubset : Finset.Ioc T N ⊆ Finset.Icc 1 N := by
    intro m hm
    have h := Finset.mem_Ioc.mp hm
    exact Finset.mem_Icc.mpr ⟨by omega, h.2⟩
  have hmass : (∑ m ∈ Finset.Ioc T N,
        ‖vf919ExcludedNormCoefficients m‖) ≤ (N : ℝ) := by
    calc
      _ ≤ ∑ m ∈ Finset.Icc 1 N,
          ‖vf919ExcludedNormCoefficients m‖ := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
          intro m hm _
          exact norm_nonneg _
      _ ≤ (N : ℝ) := vf919ExcludedNorm_mass_le N
  calc
    ‖∑ u ∈ Finset.Icc L U,
        corr4SharpQuotientDifference u *
          (∑ m ∈ Finset.Ioc T N,
            vf919ExcludedNormCoefficients m * (w m u : ℂ))‖ =
      ‖∑ m ∈ Finset.Ioc T N,
        vf919ExcludedNormCoefficients m *
          (∑ u ∈ Finset.Icc L U,
            corr4SharpQuotientDifference u * (w m u : ℂ))‖ := by rw [hswap]
    _ ≤ ∑ m ∈ Finset.Ioc T N,
        ‖vf919ExcludedNormCoefficients m *
          (∑ u ∈ Finset.Icc L U,
            corr4SharpQuotientDifference u * (w m u : ℂ))‖ :=
            norm_sum_le _ _
    _ = ∑ m ∈ Finset.Ioc T N,
        ‖vf919ExcludedNormCoefficients m‖ *
          ‖∑ u ∈ Finset.Icc L U,
            corr4SharpQuotientDifference u * (w m u : ℂ)‖ := by
            simp_rw [norm_mul]
    _ ≤ ∑ m ∈ Finset.Ioc T N,
        ‖vf919ExcludedNormCoefficients m‖ * 4 := by
          apply Finset.sum_le_sum
          intro m hm
          exact mul_le_mul_of_nonneg_left (hpoint m hm) (norm_nonneg _)
    _ = 4 * (∑ m ∈ Finset.Ioc T N,
        ‖vf919ExcludedNormCoefficients m‖) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro m hm
          ring
    _ ≤ 4 * (N : ℝ) := mul_le_mul_of_nonneg_left hmass (by norm_num)

#print axioms corr4_monotone_differenced_kernel_bound
#print axioms corr4_actual_a6_monotone_weight_tail_le_four_mass

end RHLean.Analysis
