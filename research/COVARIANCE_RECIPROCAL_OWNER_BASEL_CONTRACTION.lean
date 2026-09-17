import Mathlib
import «research.STABLE_FAR_PERRON_BASEL_FRAME_SHARPENING»
import «research.COVARIANCE_RECIPROCAL_OWNER_CONGESTION»

/-!
# Basel-sharpened reciprocal covariance contraction

The covariance owner graph has at most two literal mixed children per prime.
The two-term Basel sharpening gives the odd-prime reciprocal-square budget
`211/900`; adding the possible prime `2` costs exactly `1/4`.  Hence

  sum_{p prime} 1/p^2 <= 109/225,

and the two-child owner congestion is at most

  2 * 109/225 = 218/225 < 1.

This improves the previous `79/81` coefficient without changing the physical
owner graph or introducing any analytic assumption.  The result is stated on
the full reciprocal outgoing graph; clipped critical exits inherit it later as
nonnegative sub-energies once the heavier clipped-energy stack is loaded.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- All-prime reciprocal-square budget obtained from the sharpened odd-prime
budget plus the exact contribution of prime `2`. -/
theorem primeOwnerReciprocalSquareBudget_le_109_over_225 (N : ℕ) :
    primeOwnerReciprocalSquareBudget N ≤ (109 / 225 : ℚ) := by
  have hodd := oddPrimeOwnerReciprocalSquareBudget_le_twoTermBasel N
  unfold primeOwnerReciprocalSquareBudget
  by_cases htwo : 2 ∈ primesUpTo N
  · have hsplit := Finset.sum_erase_add
      (s := primesUpTo N)
      (f := fun q => (1 : ℚ) / (q : ℚ) ^ 2) htwo
    have hsplit' :
        (∑ q ∈ (primesUpTo N).erase 2,
          (1 : ℚ) / (q : ℚ) ^ 2) + 1 / 4 =
        ∑ q ∈ primesUpTo N, (1 : ℚ) / (q : ℚ) ^ 2 := by
      norm_num at hsplit ⊢
      exact hsplit
    calc
      (∑ q ∈ primesUpTo N, (1 : ℚ) / (q : ℚ) ^ 2) =
          (∑ q ∈ (primesUpTo N).erase 2,
            (1 : ℚ) / (q : ℚ) ^ 2) + 1 / 4 := hsplit'.symm
      _ ≤ (211 / 900 : ℚ) + 1 / 4 := add_le_add_right hodd _
      _ = 109 / 225 := by norm_num
  · have heq : (primesUpTo N).erase 2 = primesUpTo N :=
      Finset.erase_eq_of_notMem htwo
    calc
      (∑ q ∈ primesUpTo N, (1 : ℚ) / (q : ℚ) ^ 2) =
          ∑ q ∈ (primesUpTo N).erase 2,
            (1 : ℚ) / (q : ℚ) ^ 2 := by rw [heq]
      _ ≤ 211 / 900 := hodd
      _ ≤ 109 / 225 := by norm_num

/-- The literal fixed-parent owner congestion inherits the two-child factor. -/
theorem postRootCovarianceReciprocalOwnerCongestion_le_218_over_225
    (W : ℕ) (parent : ℕ × ℕ) :
    postRootCovarianceReciprocalOwnerCongestion W parent ≤
      (218 / 225 : ℚ) := by
  have hcong :=
    postRootCovarianceReciprocalOwnerCongestion_le_two_mul_budget W parent
  have hbudget := primeOwnerReciprocalSquareBudget_le_109_over_225 W
  nlinarith

/-- The Basel-sharpened coefficient is strictly better than the previous
`79/81` contraction. -/
theorem twoHundredEighteen_over_225_lt_79_over_81 :
    (218 / 225 : ℚ) < 79 / 81 := by
  norm_num

/-- Physical reciprocal outgoing energy contracts with the sharpened coefficient. -/
theorem postRootCovarianceReciprocalOutgoingEnergy_le_218_over_225
    (W : ℕ) (parent : ℕ × ℕ) :
    postRootCovarianceReciprocalOutgoingEnergy W parent ≤
      (218 / 225 : ℝ) * postRootCovarianceReciprocalPairEnergy parent := by
  unfold postRootCovarianceReciprocalOutgoingEnergy
  rw [show
    (∑ p ∈ primesUpTo W,
      ∑ mn ∈ postRootCovarianceFixedOwnerChildFiber W parent p,
        postRootCovarianceReciprocalPairEnergy mn) =
      ∑ p ∈ primesUpTo W,
        (postRootCovarianceFixedOwnerChildMultiplicity W parent p : ℝ) /
          (p : ℝ) ^ 2 * postRootCovarianceReciprocalPairEnergy parent by
      apply Finset.sum_congr rfl
      intro p _hp
      exact sum_postRootCovarianceFixedOwnerChild_energy_eq W parent p]
  rw [← Finset.sum_mul]
  have hcongQ :=
    postRootCovarianceReciprocalOwnerCongestion_le_218_over_225 W parent
  have hcast :
      (((∑ p ∈ primesUpTo W,
          (postRootCovarianceFixedOwnerChildMultiplicity W parent p : ℚ) /
            (p : ℚ) ^ 2 : ℚ)) : ℝ) ≤
        (((218 / 225 : ℚ)) : ℝ) := by
    unfold postRootCovarianceReciprocalOwnerCongestion at hcongQ
    exact_mod_cast hcongQ
  push_cast at hcast
  norm_num at hcast ⊢
  have hcongR :
      (∑ p ∈ primesUpTo W,
        (postRootCovarianceFixedOwnerChildMultiplicity W parent p : ℝ) /
          (p : ℝ) ^ 2) ≤ 218 / 225 := by
    simpa [Nat.cast_pow] using hcast
  exact mul_le_mul_of_nonneg_right hcongR
    (postRootCovarianceReciprocalPairEnergy_nonneg parent)

end RHLean.Proof
