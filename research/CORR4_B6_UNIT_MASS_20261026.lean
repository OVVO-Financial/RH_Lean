import Mathlib
import «research.CORR4_SIX_POINT_ORTHOGONALITY_20261026»

/-!
# CORR-4: unconditional unit-mass control of the actual b6 coefficients

The B6 branch is a masked quadratic-character twist of the integer
Mobius coefficient. Each individual coefficient is 0, +1 or -1.
The mass bound here is direct and is independent of signed
Mertens-cancellation hypotheses.
-/

noncomputable section
open scoped BigOperators
namespace RHLean.Analysis

theorem corr4_b6_norm_le_one (n : ℕ) : ‖corr4B6 n‖ ≤ 1 := by
  have hmask : ‖vf919PrimeToSixMask n‖ ≤ 1 := by
    unfold vf919PrimeToSixMask
    split_ifs <;> norm_num
  have hchi : ‖vf919ChiMinusThree n‖ ≤ 1 := by
    unfold vf919ChiMinusThree
    split_ifs <;> norm_num
  have hmu : ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))
  have hchiMu :
      ‖vf919ChiMinusThree n‖ *
        ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ ≤ 1 := by
    calc
      _ ≤ 1 * ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ :=
        mul_le_mul_of_nonneg_right hchi (norm_nonneg _)
      _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hmu (by norm_num)
      _ = 1 := by ring
  change ‖vf919PrimeToSixMask n *
    (vf919ChiMinusThree n * ((ArithmeticFunction.moebius n : ℤ) : ℂ))‖ ≤ 1
  rw [norm_mul, norm_mul]
  calc
    ‖vf919PrimeToSixMask n‖ *
        (‖vf919ChiMinusThree n‖ *
          ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖) ≤
      1 * (‖vf919ChiMinusThree n‖ *
        ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖) :=
          mul_le_mul_of_nonneg_right hmask
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hchiMu (by norm_num)
    _ = 1 := by ring

theorem corr4_b6_mass_le (N : ℕ) :
    (∑ m ∈ Finset.Icc 1 N, ‖corr4B6 m‖) ≤ (N : ℝ) := by
  calc
    _ ≤ ∑ _m ∈ Finset.Icc 1 N, (1 : ℝ) :=
      Finset.sum_le_sum (fun m _ => corr4_b6_norm_le_one m)
    _ = (N : ℝ) := by simp

#print axioms corr4_b6_norm_le_one
#print axioms corr4_b6_mass_le

end RHLean.Analysis
