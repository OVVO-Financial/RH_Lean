import Mathlib
import «research.CORR4_HIGH_QUOTIENT_TAIL_CONSTANT_FOUR_20261026»

/-!
# CORR-4 literal discrete tent: constant-four high quotient tail

The two-box convolution below counts each of the H^2 equally weighted
pairs (i,j). Its net shift is (i+j)-(H-1), giving the *exact* discrete
tent of weights H-|h| at integer h with |h|<H.

The proof uses only monotonicity, support and unit mass of the tent,
and the original genuine #919 coefficient mass <= N. No probabilistic,
Gaussian, Mertens or RH assumption is inserted.
-/

noncomputable section
open scoped BigOperators
namespace RHLean.Analysis

/-- Literal normalized discrete tent evaluated on the physical sharp
cutoff n<=X+h. We assume H>0 in its estimates. -/
def corr4TentRamp (X H n : ℕ) : ℝ :=
  (∑ i ∈ Finset.range H,
    ∑ j ∈ Finset.range H,
      if n + (H - 1) ≤ X + i + j then (1 : ℝ) else 0) /
    (H : ℝ) ^ 2

theorem corr4TentRamp_nonneg (X H n : ℕ) :
    0 ≤ corr4TentRamp X H n := by
  unfold corr4TentRamp
  apply div_nonneg ?_ (sq_nonneg _)
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  split_ifs <;> norm_num

theorem corr4TentRamp_antitone (X H : ℕ) {n n' : ℕ}
    (hn : n ≤ n') :
    corr4TentRamp X H n' ≤ corr4TentRamp X H n := by
  unfold corr4TentRamp
  apply div_le_div_of_nonneg_right ?_ (sq_nonneg _)
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  by_cases hnew : n' + (H - 1) ≤ X + i + j
  · have hold : n + (H - 1) ≤ X + i + j := by omega
    simp [hnew, hold]
  · by_cases hold : n + (H - 1) ≤ X + i + j
    · simp [hnew, hold]
    · simp [hnew, hold]

theorem corr4TentRamp_le_one (X H n : ℕ) (hH : 0 < H) :
    corr4TentRamp X H n ≤ 1 := by
  have hnum :
      (∑ i ∈ Finset.range H,
        ∑ j ∈ Finset.range H,
          if n + (H - 1) ≤ X + i + j then (1 : ℝ) else 0) ≤
        (H : ℝ) ^ 2 := by
    calc
      _ ≤ ∑ i ∈ Finset.range H,
            ∑ _j ∈ Finset.range H, (1 : ℝ) := by
              apply Finset.sum_le_sum
              intro i hi
              apply Finset.sum_le_sum
              intro j hj
              split_ifs <;> norm_num
      _ = (H : ℝ) ^ 2 := by simp [pow_two]
  unfold corr4TentRamp
  have hHreal : (0 : ℝ) < (H : ℝ) := Nat.cast_pos.mpr hH
  exact (div_le_iff₀ (pow_pos hHreal 2)).2 (by nlinarith [hnum])

theorem corr4TentRamp_zero_of_above (X H n : ℕ)
    (hH : 0 < H) (hn : X + H ≤ n) :
    corr4TentRamp X H n = 0 := by
  have hsum :
      (∑ i ∈ Finset.range H,
        ∑ j ∈ Finset.range H,
          if n + (H - 1) ≤ X + i + j then (1 : ℝ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro j hj
    have hi' : i < H := Finset.mem_range.mp hi
    have hj' : j < H := Finset.mem_range.mp hj
    have hno : ¬(n + (H - 1) ≤ X + i + j) := by omega
    simp [hno]
  unfold corr4TentRamp
  rw [hsum, zero_div]

/-- The real normalized physical tent is antitone on the quotient
index for each fixed m. This is the only smoothness fact the upper
quotient proof needs. -/
theorem corr4TentRamp_quotient_step (X H m u : ℕ) :
    corr4TentRamp X H ((u + 1) * m) ≤
      corr4TentRamp X H (u * m) := by
  apply corr4TentRamp_antitone X H
  exact Nat.mul_le_mul_right m (Nat.le_succ u)

/-- The exact genuine signed a6 source, truncated to m<=floor(Y/L),
is paid by the uniform constant-four bound. -/
theorem corr4_high_quotient_tail_exact_tent_restricted_le_four
    (X H T L U : ℕ)
    (hH : 0 < H) (hL : 1 ≤ L) (hLU : L ≤ U)
    (hEnd : X + H - 1 < (U + 1) * (T + 1)) :
    ‖∑ u ∈ Finset.Icc L U,
        corr4SharpQuotientDifference u *
          (∑ m ∈ Finset.Ioc T ((X + H - 1) / L),
            vf919ExcludedNormCoefficients m *
              (corr4TentRamp X H (u * m) : ℂ))‖ ≤
      4 * (((X + H - 1) / L : ℕ) : ℝ) := by
  let N := (X + H - 1) / L
  have hzero : ∀ m ∈ Finset.Ioc T N,
      corr4TentRamp X H ((U + 1) * m) = 0 := by
    intro m hm
    have hm' : T + 1 ≤ m := by
      have h := Finset.mem_Ioc.mp hm
      omega
    have hprod : (U + 1) * (T + 1) ≤ (U + 1) * m :=
      Nat.mul_le_mul_left (U + 1) hm'
    have hn : X + H ≤ (U + 1) * m := by omega
    exact corr4TentRamp_zero_of_above X H _ hH hn
  exact corr4_actual_a6_monotone_weight_tail_le_four_mass
    L U T N (fun m u => corr4TentRamp X H (u * m))
    hL hLU
    (by intro m hm; exact corr4TentRamp_nonneg _ _ _)
    (by intro m hm u hu; exact corr4TentRamp_quotient_step X H m u)
    hzero
    (by intro m hm; exact corr4TentRamp_le_one _ _ _ hH)

/-- There is no discarded m>T occurrence: if m>floor(Y/L) and u>=L,
the exact tent weight is zero. -/
theorem corr4_high_quotient_tail_exact_tent_le_four
    (X H T L U : ℕ)
    (hH : 0 < H) (hL : 1 ≤ L) (hLU : L ≤ U)
    (hEnd : X + H - 1 < (U + 1) * (T + 1)) :
    ‖∑ u ∈ Finset.Icc L U,
        corr4SharpQuotientDifference u *
          (∑ m ∈ Finset.Ioc T (X + H - 1),
            vf919ExcludedNormCoefficients m *
              (corr4TentRamp X H (u * m) : ℂ))‖ ≤
      4 * (((X + H - 1) / L : ℕ) : ℝ) := by
  let Y := X + H - 1
  let N := Y / L
  have hsub : Finset.Ioc T N ⊆ Finset.Ioc T Y := by
    intro m hm
    rcases Finset.mem_Ioc.mp hm with ⟨hmT,hmN⟩
    exact Finset.mem_Ioc.mpr
      ⟨hmT, hmN.trans (Nat.div_le_self Y L)⟩
  have hInner (u : ℕ) (hu : u ∈ Finset.Icc L U) :
      (∑ m ∈ Finset.Ioc T N,
          vf919ExcludedNormCoefficients m *
            (corr4TentRamp X H (u * m) : ℂ)) =
      (∑ m ∈ Finset.Ioc T Y,
          vf919ExcludedNormCoefficients m *
            (corr4TentRamp X H (u * m) : ℂ)) := by
    apply Finset.sum_subset hsub
    intro m hmBig hmNotSmall
    have hmT : T < m := (Finset.mem_Ioc.mp hmBig).1
    have hmN : N < m := by
      by_contra hbad
      have hmn : m ≤ N := Nat.le_of_not_gt hbad
      exact hmNotSmall (Finset.mem_Ioc.mpr ⟨hmT, hmn⟩)
    have hLm : Y < L * m := by
      have h := (Nat.div_lt_iff_lt_mul (by omega : 0 < L)).mp hmN
      nlinarith [h]
    have hUL : L ≤ u := (Finset.mem_Icc.mp hu).1
    have hUm : L * m ≤ u * m := Nat.mul_le_mul_right m hUL
    have hX : X + H ≤ u * m := by omega
    have hv := corr4TentRamp_zero_of_above X H (u * m) hH hX
    simp [hv]
  have hrew :
      (∑ u ∈ Finset.Icc L U,
        corr4SharpQuotientDifference u *
          (∑ m ∈ Finset.Ioc T Y,
            vf919ExcludedNormCoefficients m *
              (corr4TentRamp X H (u * m) : ℂ))) =
      (∑ u ∈ Finset.Icc L U,
        corr4SharpQuotientDifference u *
          (∑ m ∈ Finset.Ioc T N,
            vf919ExcludedNormCoefficients m *
              (corr4TentRamp X H (u * m) : ℂ))) := by
    apply Finset.sum_congr rfl
    intro u hu
    rw [hInner u hu]
  change ‖∑ u ∈ Finset.Icc L U,
        corr4SharpQuotientDifference u *
          (∑ m ∈ Finset.Ioc T Y,
            vf919ExcludedNormCoefficients m *
              (corr4TentRamp X H (u * m) : ℂ))‖ ≤ 4 * (N : ℝ)
  rw [hrew]
  exact corr4_high_quotient_tail_exact_tent_restricted_le_four
    X H T L U hH hL hLU hEnd

#print axioms corr4TentRamp_le_one
#print axioms corr4_high_quotient_tail_exact_tent_le_four

end RHLean.Analysis
