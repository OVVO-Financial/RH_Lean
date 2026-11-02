import Mathlib
import «research.EULER_HYBRID_ABEL_GRAM_20261027»

/-!
# Binary parity reassembly for the finite-C kernel

This module formalizes the independently accepted finite parity obstruction
from claim `20261102-wheel-2`.  The literal square-endpoint bilinear form is
partitioned into all four parity sectors without changing its cutoff, floor,
Möbius coefficients, or the two mixed orientations.

At `R = 5`, the odd-odd sector is `10` while the complete form is zero:
the remaining three sectors cancel it exactly.  This rules out any homogeneous
bound of the odd-odd sector by the complete form alone.

The result is structural control and a scoped no-go theorem.  It proves no
finite-C estimate, endpoint gain, Mertens exponent, or RH statement.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

/-- One of the four exact parity sectors of the literal finite-C kernel.
The first flag selects the parity of `a`, the second the parity of `b`. -/
def eulerSelfDualParitySector (R : ℕ) (aOdd bOdd : Bool) : ℂ :=
  ∑ b ∈ Finset.Icc 1 (R - 1),
    if decide (Odd b) = bOdd then
      (((μ b : ℤ) : ℂ)) *
        ∑ a ∈ Finset.Icc 1 (R - 1),
          if decide (Odd a) = aOdd then
            (((μ a : ℤ) : ℂ)) * eulerSelfDualFloor R a b
          else 0
    else 0

/-- Exact four-sector reassembly. Both mixed orientations are retained. -/
theorem eulerSelfDualBilinear_eq_sum_paritySectors (R : ℕ) :
    eulerSelfDualBilinear R =
      eulerSelfDualParitySector R true true +
      eulerSelfDualParitySector R true false +
      eulerSelfDualParitySector R false true +
      eulerSelfDualParitySector R false false := by
  classical
  unfold eulerSelfDualBilinear eulerSelfDualParitySector
  simp_rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _hb
  by_cases hbo : Odd b
  · simp [hbo]
    rw [← mul_add]
    congr 1
    simp_rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _ha
    by_cases hao : Odd a <;> simp [hao]
  · simp [hbo]
    rw [← mul_add]
    congr 1
    simp_rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _ha
    by_cases hao : Odd a <;> simp [hao]

private theorem moebius_one : μ 1 = (1 : ℤ) :=
  ArithmeticFunction.moebius_apply_one

private theorem moebius_two : μ 2 = (-1 : ℤ) :=
  ArithmeticFunction.moebius_apply_prime Nat.prime_two

private theorem moebius_three : μ 3 = (-1 : ℤ) :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem moebius_four : μ 4 = (0 : ℤ) := by
  have h := ArithmeticFunction.moebius_apply_prime_pow
    (p := 2) (k := 2) (by norm_num) (by norm_num)
  norm_num at h
  exact h

/-- The genuine odd-odd sector in the accepted `R = 5` witness. -/
theorem eulerSelfDualParitySector_five_odd_odd :
    eulerSelfDualParitySector 5 true true = 10 := by
  rw [show Finset.Icc 1 4 = ({1, 2, 3, 4} : Finset ℕ) by decide]
  norm_num [eulerSelfDualParitySector, eulerSelfDualFloor, squareRootEndpoint,
    moebius_one, moebius_two, moebius_three, moebius_four]

/-- The odd-even orientation in the accepted `R = 5` witness. -/
theorem eulerSelfDualParitySector_five_odd_even :
    eulerSelfDualParitySector 5 true false = -8 := by
  rw [show Finset.Icc 1 4 = ({1, 2, 3, 4} : Finset ℕ) by decide]
  norm_num [eulerSelfDualParitySector, eulerSelfDualFloor, squareRootEndpoint,
    moebius_one, moebius_two, moebius_three, moebius_four]

/-- The even-odd orientation in the accepted `R = 5` witness. -/
theorem eulerSelfDualParitySector_five_even_odd :
    eulerSelfDualParitySector 5 false true = -8 := by
  rw [show Finset.Icc 1 4 = ({1, 2, 3, 4} : Finset ℕ) by decide]
  norm_num [eulerSelfDualParitySector, eulerSelfDualFloor, squareRootEndpoint,
    moebius_one, moebius_two, moebius_three, moebius_four]

/-- The even-even sector in the accepted `R = 5` witness. -/
theorem eulerSelfDualParitySector_five_even_even :
    eulerSelfDualParitySector 5 false false = 6 := by
  rw [show Finset.Icc 1 4 = ({1, 2, 3, 4} : Finset ℕ) by decide]
  norm_num [eulerSelfDualParitySector, eulerSelfDualFloor, squareRootEndpoint,
    moebius_one, moebius_two, moebius_three, moebius_four]

/-- All four genuine sectors cancel exactly at `R = 5`. -/
theorem eulerSelfDualBilinear_five : eulerSelfDualBilinear 5 = 0 := by
  rw [eulerSelfDualBilinear_eq_sum_paritySectors,
    eulerSelfDualParitySector_five_odd_odd,
    eulerSelfDualParitySector_five_odd_even,
    eulerSelfDualParitySector_five_even_odd,
    eulerSelfDualParitySector_five_even_even]
  norm_num

/-- No finite homogeneous comparison can bound the odd-odd sector by the
complete finite-C packet at every root. -/
theorem no_uniform_oddOdd_control_by_eulerSelfDualBilinear :
    ¬ ∃ C : ℝ, ∀ R : ℕ,
      ‖eulerSelfDualParitySector R true true‖ ≤
        C * ‖eulerSelfDualBilinear R‖ := by
  rintro ⟨C, hC⟩
  have h := hC 5
  rw [eulerSelfDualParitySector_five_odd_odd,
    eulerSelfDualBilinear_five] at h
  norm_num at h

#print axioms eulerSelfDualBilinear_eq_sum_paritySectors
#print axioms eulerSelfDualParitySector_five_odd_odd
#print axioms eulerSelfDualBilinear_five
#print axioms no_uniform_oddOdd_control_by_eulerSelfDualBilinear

end RHLean.Proof
