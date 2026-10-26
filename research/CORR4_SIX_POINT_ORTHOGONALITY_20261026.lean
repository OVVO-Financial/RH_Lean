import Mathlib
import «research.CORR4_PHYSICAL_TENT_CONSTANT_FOUR_20261026»

/-!
# CORR-4: actual excluded-six character factor and finite Euler polynomial

This proves the coefficient-level algebra that makes the B6 hyperbola branch
different from the unresolved M6 branch. The complete quotient decoder
times the *actual* masked quadratic Mobius coefficients is supported at
1, 2, 3 and 6.

The separate finite-prefix/physical-tent transport is not asserted by
the Euler polynomial identity alone.
-/

noncomputable section
open scoped BigOperators
namespace RHLean.Analysis

/-- Actual chi_{-3} times Mobius with the prime-to-six mask. -/
def corr4B6 : ArithmeticFunction ℂ :=
  vf919ArithmeticTwist vf919PrimeToSixMask vf919QuadraticInverse

/-- Full analytic quotient decoder, before the finite cutoff u < L. -/
def corr4DecoderEuler : ArithmeticFunction ℂ :=
  vf919QuadraticCharacter *
    ((1 - vf919DirichletDelta 3) * (1 - vf919DirichletDelta 4))

theorem corr4_masked_character_inverse :
    vf919ArithmeticTwist vf919PrimeToSixMask vf919QuadraticCharacter *
      corr4B6 = 1 := by
  unfold corr4B6
  rw [← vf919ArithmeticTwist_mul vf919PrimeToSixMask
    vf919PrimeToSixMask_mul, vf919QuadraticCharacter_mul_inverse]
  exact vf919ArithmeticTwist_one _ (by norm_num [vf919PrimeToSixMask])

/-- The inert local factor at 2 is *plus*: chi_{-3}(2) = -1.
This sign must survive until the product with (1-delta_4). -/
theorem corr4_masked_character_factor :
    vf919ArithmeticTwist vf919PrimeToSixMask vf919QuadraticCharacter =
      (1 + vf919DirichletDelta 2) * vf919QuadraticCharacter := by
  ext n
  rw [add_mul, one_mul, ArithmeticFunction.add_apply,
    vf919DirichletDelta_mul_apply 2 (by decide)]
  by_cases h2 : 2 ∣ n
  · have hchi : vf919ChiMinusThree n = -vf919ChiMinusThree (n / 2) := by
      calc
        vf919ChiMinusThree n =
            vf919ChiMinusThree 2 * vf919ChiMinusThree (n / 2) := by
              rw [← vf919ChiMinusThree_mul, Nat.mul_div_cancel' h2]
        _ = -vf919ChiMinusThree (n / 2) := by
          rw [show vf919ChiMinusThree 2 = -1 from by norm_num [vf919ChiMinusThree]]
          ring
    simp [vf919ArithmeticTwist, vf919PrimeToSixMask, h2, hchi]
  · by_cases h3 : 3 ∣ n
    · have hn3 : n % 3 = 0 := Nat.mod_eq_zero_of_dvd h3
      simp [vf919ArithmeticTwist, vf919PrimeToSixMask, h2,
        vf919ChiMinusThree, hn3]
    · simp [vf919ArithmeticTwist, vf919PrimeToSixMask, h2, h3]

theorem corr4_four_factor :
    1 - vf919DirichletDelta 4 =
      (1 - vf919DirichletDelta 2) * (1 + vf919DirichletDelta 2) := by
  have h := vf919DirichletDelta_mul 2 2 (by decide) (by decide)
  change vf919DirichletDelta 2 * vf919DirichletDelta 2 =
    vf919DirichletDelta 4 at h
  rw [← h]
  ring

/-- Full decoder * actual b6 = a finite four-point Euler polynomial.
No estimate on Mertens summatory values is used. -/
theorem corr4_decoder_mul_actual_b6_eq_six_polynomial :
    corr4DecoderEuler * corr4B6 =
      (1 - vf919DirichletDelta 2) * (1 - vf919DirichletDelta 3) := by
  unfold corr4DecoderEuler
  rw [corr4_four_factor]
  calc
    (vf919QuadraticCharacter *
        ((1 - vf919DirichletDelta 3) *
          ((1 - vf919DirichletDelta 2) * (1 + vf919DirichletDelta 2)))) *
       corr4B6 =
      ((1 - vf919DirichletDelta 2) * (1 - vf919DirichletDelta 3)) *
        ((vf919ArithmeticTwist vf919PrimeToSixMask vf919QuadraticCharacter) *
           corr4B6) := by
          rw [corr4_masked_character_factor]
          ring
    _ = (1 - vf919DirichletDelta 2) * (1 - vf919DirichletDelta 3) := by
          rw [corr4_masked_character_inverse]
          simp

/-- Its exact support is {1,2,3,6}, with signs + - - +. -/
theorem corr4_decoder_mul_actual_b6_eq_four_delta :
    corr4DecoderEuler * corr4B6 =
      1 - vf919DirichletDelta 2 - vf919DirichletDelta 3 +
        vf919DirichletDelta 6 := by
  rw [corr4_decoder_mul_actual_b6_eq_six_polynomial]
  have h := vf919DirichletDelta_mul 2 3 (by decide) (by decide)
  change vf919DirichletDelta 2 * vf919DirichletDelta 3 =
    vf919DirichletDelta 6 at h
  rw [← h]
  ring

#print axioms corr4_masked_character_inverse
#print axioms corr4_decoder_mul_actual_b6_eq_six_polynomial
#print axioms corr4_decoder_mul_actual_b6_eq_four_delta

end RHLean.Analysis
