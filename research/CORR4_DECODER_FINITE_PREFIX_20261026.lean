import Mathlib
import «research.CORR4_SIX_POINT_ORTHOGONALITY_20261026»
import «research.CORR4_ZERO_CUT_QUOTIENT_SUPPORT_20261026»

/-!
# CORR-4: the Euler decoder really is the adjacent 36-kernel difference

It is not enough to prove a six-point Euler product for a new formal
Dirichlet decoder: that decoder must be the literal d(u)=K(u)-K(u-1)
used by the original #919 physical source. This file proves that
coefficient identification through finite quotient-prefix summation.
-/

noncomputable section
open scoped BigOperators
namespace RHLean.Analysis

/-- Finite reindexing of the multiples of k; no analytic convergence. -/
theorem corr4_scaled_prefix_reindex (f : ℕ → ℂ) (k Z : ℕ)
    (hk : 0 < k) :
    (∑ n ∈ Finset.Icc 1 Z,
      if k ∣ n then f (n / k) else 0) =
        ∑ j ∈ Finset.Icc 1 (Z / k), f j := by
  calc
    (∑ n ∈ Finset.Icc 1 Z, if k ∣ n then f (n / k) else 0) =
        ∑ n ∈ (Finset.Icc 1 Z).filter (fun n => k ∣ n), f (n / k) := by
          rw [Finset.sum_filter]
    _ = ∑ j ∈ Finset.Icc 1 (Z / k), f j := by
          apply Finset.sum_bij (fun n _ => n / k)
          · intro n hn
            obtain ⟨hnI, hnD⟩ := Finset.mem_filter.mp hn
            obtain ⟨hnpos, hnZ⟩ := Finset.mem_Icc.mp hnI
            have hklen : k ≤ n := Nat.le_of_dvd (by omega) hnD
            apply Finset.mem_Icc.mpr
            constructor
            · exact (Nat.le_div_iff_mul_le hk).mpr (by simpa using hklen)
            · exact Nat.div_le_div_right hnZ
          · intro a ha b hb hab
            have hda := (Finset.mem_filter.mp ha).2
            have hdb := (Finset.mem_filter.mp hb).2
            calc
              a = k * (a / k) := (Nat.mul_div_cancel' hda).symm
              _ = k * (b / k) := by rw [hab]
              _ = b := Nat.mul_div_cancel' hdb
          · intro j hj
            obtain ⟨hjpos, hjZ⟩ := Finset.mem_Icc.mp hj
            have hprod : k * j ≤ Z := by
              have ht := (Nat.le_div_iff_mul_le hk).mp hjZ
              simpa [Nat.mul_comm] using ht
            refine ⟨k * j, ?_, ?_⟩
            · exact Finset.mem_filter.mpr
                ⟨Finset.mem_Icc.mpr
                   ⟨Nat.mul_pos hk (by omega), hprod⟩,
                 ⟨j, rfl⟩⟩
            · exact Nat.mul_div_cancel_left j hk
          · intro n hn
            rfl

theorem corr4_quadratic_character_eq_integer_cast (n : ℕ) :
    vf919QuadraticCharacter n = (vf919IntegerCharacter n : ℂ) := by
  rw [vf919QuadraticCharacter_apply]
  unfold vf919ChiMinusThree vf919IntegerCharacter
  split_ifs <;> norm_num

theorem corr4_quadratic_character_prefix_cast (Z : ℕ) :
    (∑ n ∈ Finset.Icc 1 Z, vf919QuadraticCharacter n) =
      (vf919IntegerCharacterPrefix Z : ℂ) := by
  rw [vf919IntegerCharacterPrefix, Int.cast_sum]
  exact Finset.sum_congr rfl
    (fun n _ => corr4_quadratic_character_eq_integer_cast n)

theorem corr4_decoder_euler_eval (n : ℕ) :
    corr4DecoderEuler n =
      vf919QuadraticCharacter n -
        (if 3 ∣ n then vf919QuadraticCharacter (n / 3) else 0) -
        (if 4 ∣ n then vf919QuadraticCharacter (n / 4) else 0) +
        (if 12 ∣ n then vf919QuadraticCharacter (n / 12) else 0) := by
  have hdelta := vf919DirichletDelta_mul 3 4 (by decide) (by decide)
  have heq : corr4DecoderEuler =
      vf919QuadraticCharacter -
        vf919DirichletDelta 3 * vf919QuadraticCharacter -
        vf919DirichletDelta 4 * vf919QuadraticCharacter +
        vf919DirichletDelta 12 * vf919QuadraticCharacter := by
    unfold corr4DecoderEuler
    rw [← hdelta]
    ring
  rw [heq]
  simp only [vf919ArithmeticFunction_sub_apply, ArithmeticFunction.add_apply]
  rw [vf919DirichletDelta_mul_apply 3 (by decide),
    vf919DirichletDelta_mul_apply 4 (by decide),
    vf919DirichletDelta_mul_apply 12 (by decide)]

/-- Every prefix of the analytic Euler decoder is the *actual* #919
physical quotient kernel, including the 3,4,12 exclusions. -/
theorem corr4_decoder_euler_prefix_eq_sharp_kernel (Z : ℕ) :
    (∑ n ∈ Finset.Icc 1 Z, corr4DecoderEuler n) =
      (vf919SharpQuotientKernel36 Z : ℂ) := by
  have hpoint :
      (∑ n ∈ Finset.Icc 1 Z, corr4DecoderEuler n) =
      ∑ n ∈ Finset.Icc 1 Z,
        (vf919QuadraticCharacter n -
          (if 3 ∣ n then vf919QuadraticCharacter (n / 3) else 0) -
          (if 4 ∣ n then vf919QuadraticCharacter (n / 4) else 0) +
          (if 12 ∣ n then vf919QuadraticCharacter (n / 12) else 0)) := by
    apply Finset.sum_congr rfl
    intro n hn
    exact corr4_decoder_euler_eval n
  rw [hpoint, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib]
  rw [corr4_scaled_prefix_reindex _ 3 Z (by decide),
    corr4_scaled_prefix_reindex _ 4 Z (by decide),
    corr4_scaled_prefix_reindex _ 12 Z (by decide)]
  rw [corr4_quadratic_character_prefix_cast Z,
    corr4_quadratic_character_prefix_cast (Z / 3),
    corr4_quadratic_character_prefix_cast (Z / 4),
    corr4_quadratic_character_prefix_cast (Z / 12)]
  unfold vf919SharpQuotientKernel36
  push_cast
  rfl

/-- Genuine coefficient identification: no replacement decoder is used. -/
theorem corr4_decoder_euler_eq_actual_difference (u : ℕ) (hu : 0 < u) :
    corr4DecoderEuler u = corr4SharpQuotientDifference u := by
  obtain ⟨v, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : u ≠ 0)
  have hsum :
      corr4DecoderEuler (v + 1) =
        (∑ n ∈ Finset.Icc 1 (v + 1), corr4DecoderEuler n) -
        (∑ n ∈ Finset.Icc 1 v, corr4DecoderEuler n) := by
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ v + 1)]
    ring
  rw [hsum, corr4_decoder_euler_prefix_eq_sharp_kernel,
    corr4_decoder_euler_prefix_eq_sharp_kernel]
  unfold corr4SharpQuotientDifference
  rw [show v + 1 - 1 = v by omega]

#print axioms corr4_scaled_prefix_reindex
#print axioms corr4_decoder_euler_prefix_eq_sharp_kernel
#print axioms corr4_decoder_euler_eq_actual_difference

end RHLean.Analysis
