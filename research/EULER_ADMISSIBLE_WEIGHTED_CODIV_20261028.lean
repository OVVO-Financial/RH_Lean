import Mathlib
import «research.EULER_ADMISSIBLE_PRIME_POPULATION_CODIV_20261028»

/-!
# Actual weighted Euler Co-Div and admissible-prime population

The Abel historical cross is exactly the signed pair population under the
actual floor difference w(a,b) = floor(X/(ab)) - floor(X/b^2), a<b<R.
No replacement by independent signs, no absolute-value collapse, and no
extra Euler face multiplicities. The historical diagonal is kept separate.

The admissible-prime state is read from PR #1043, and the O(R) asymmetric
corner is imported from PR #1042.  No quantitative signed estimate is assumed.
-/

noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof
open RHLean.Analysis

/-- The true historical Abel floor-difference pair weight. -/
def eulerAdmissiblePairWeight (R a b : ℕ) : ℂ :=
  eulerSelfDualFloor R a b - eulerSelfDualFloor R b b

/-- Original weighted pairs of nonzero Mobius coefficients with the SAME sign. -/
def eulerAdmissibleWeightedCo (R : ℕ) : ℂ :=
  ∑ b ∈ Finset.Icc 1 (R - 1),
    ∑ a ∈ Finset.Icc 1 (b - 1),
      if (((μ a : ℤ) = 1 ∧ (μ b : ℤ) = 1) ∨
          ((μ a : ℤ) = -1 ∧ (μ b : ℤ) = -1)) then
        eulerAdmissiblePairWeight R a b
      else 0

/-- Original weighted pairs of nonzero Mobius coefficients with OPPOSITE signs. -/
def eulerAdmissibleWeightedDiv (R : ℕ) : ℂ :=
  ∑ b ∈ Finset.Icc 1 (R - 1),
    ∑ a ∈ Finset.Icc 1 (b - 1),
      if (((μ a : ℤ) = 1 ∧ (μ b : ℤ) = -1) ∨
          ((μ a : ℤ) = -1 ∧ (μ b : ℤ) = 1)) then
        eulerAdmissiblePairWeight R a b
      else 0

/-- Single-pair parity: the true weight is Co minus Div, not Div alone.
Zero Mobius coefficients contribute to neither population. -/
private theorem eulerAdmissiblePair_signed_eq_co_sub_div
    (R a b : ℕ) :
    (((μ a : ℤ) : ℂ)) * (((μ b : ℤ) : ℂ)) *
        eulerAdmissiblePairWeight R a b =
      (if (((μ a : ℤ) = 1 ∧ (μ b : ℤ) = 1) ∨
          ((μ a : ℤ) = -1 ∧ (μ b : ℤ) = -1)) then
        eulerAdmissiblePairWeight R a b else 0) -
      (if (((μ a : ℤ) = 1 ∧ (μ b : ℤ) = -1) ∨
          ((μ a : ℤ) = -1 ∧ (μ b : ℤ) = 1)) then
        eulerAdmissiblePairWeight R a b else 0) := by
  rcases ArithmeticFunction.moebius_eq_or a with ha | ha | ha <;>
    rcases ArithmeticFunction.moebius_eq_or b with hb | hb | hb <;>
    simp [ha, hb]

/-- Original Abel mixed cross = pairwise signed Mobius floor differences.
No probabilistic cancellation is used in the Abel transfer. -/
theorem eulerHybridStrictCross_eq_original_weighted_pairs (R : ℕ) :
    eulerHybridStrictCross R =
      ∑ b ∈ Finset.Icc 1 (R - 1),
        ∑ a ∈ Finset.Icc 1 (b - 1),
          (((μ a : ℤ) : ℂ)) * (((μ b : ℤ) : ℂ)) *
            eulerAdmissiblePairWeight R a b := by
  unfold eulerHybridStrictCross
  apply Finset.sum_congr rfl
  intro b hb
  have hpred : b - 1 + 1 = b := by
    have hbpos := (Finset.mem_Icc.mp hb).1
    omega
  have habel := RHLean.Analysis.sum_mertensSummatory_mul_forwardDifference
    (fun a => eulerSelfDualFloor R a b) (b - 1)
  rw [hpred] at habel
  rw [habel, mertensSummatory_eq_sum_Icc (b - 1)]
  rw [Finset.sum_mul, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  unfold eulerAdmissiblePairWeight
  ring

/-- The weighted Co-Div is EXACTLY the certified original historical cross.
Neither the diagonal nor the off-diagonal has been bounded. -/
theorem eulerHybridStrictCross_eq_admissible_weighted_Co_sub_Div
    (R : ℕ) :
    eulerHybridStrictCross R =
      eulerAdmissibleWeightedCo R - eulerAdmissibleWeightedDiv R := by
  rw [eulerHybridStrictCross_eq_original_weighted_pairs]
  unfold eulerAdmissibleWeightedCo eulerAdmissibleWeightedDiv
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  exact eulerAdmissiblePair_signed_eq_co_sub_div R a b

/-- Full self-dual Euler Gram, now in the ACTUAL Co-Div populations and the
genuine prime-admission debt on the same integer source. -/
theorem eulerAdmissible_weighted_CoDiv_eq_primePopulation
    (R : ℕ) (hR : 2 ≤ R) :
    eulerHybridDiagonal R +
        2 * (eulerAdmissibleWeightedCo R - eulerAdmissibleWeightedDiv R) =
      2 * mertensSummatory (R - 1) -
        eulerAdmissibleLowPopulation R +
        eulerAdmissiblePrimeDebt R := by
  calc
    _ = eulerSelfDualBilinear R := by
      rw [← eulerHybridStrictCross_eq_admissible_weighted_Co_sub_Div]
      exact (eulerSelfDualBilinear_eq_diagonal_add_signedStrictCross R hR).symm
    _ = _ := eulerSelfDualBilinear_eq_admissible_population R hR

/-- The asymmetric original Euler rectangle, full weighted Co-Div, original
historical end strip and its unconditionally O(R) signed corner. -/
theorem eulerAsymBilinear_eq_weighted_CoDiv_add_corner
    (R : ℕ) (hR : 2 ≤ R) :
    eulerAsymBilinear R =
      eulerHybridDiagonal R +
        2 * (eulerAdmissibleWeightedCo R - eulerAdmissibleWeightedDiv R) -
        (mertensSummatory (R - 1) -
          mertensSummatory (eulerAsymCutoff R)) +
        eulerAsymCorner R := by
  rw [eulerAsymBilinear_eq_signedGram_add_corner R hR,
    eulerHybridStrictCross_eq_admissible_weighted_Co_sub_Div]

#print axioms eulerHybridStrictCross_eq_original_weighted_pairs
#print axioms eulerHybridStrictCross_eq_admissible_weighted_Co_sub_Div
#print axioms eulerAdmissible_weighted_CoDiv_eq_primePopulation
#print axioms eulerAsymBilinear_eq_weighted_CoDiv_add_corner

end RHLean.Proof
