import Mathlib
import «research.GLOBAL_RETURNED_CORE_RETAINED_COEFFICIENT_OUTGOING_ENERGY»
import «research.COVARIANCE_RECIPROCAL_OWNER_BASEL_CONTRACTION»

/-!
# Basel sharpening on the actual greatest-owner reciprocal graph

The returned-core signed proof descends on the greatest-fresh-owner graph, not
the older covariance least-owner graph.  Fortunately the geometric reduction is
identical: for one stripped parent and one prime owner there are at most two
mixed children, and every child carries exactly `1/p^2` of the reciprocal pair
energy.

The sharpened all-prime budget already compiled on this branch is

  sum_{p prime} 1/p^2 <= 109/225.

Hence the actual greatest-owner graph contracts by

  2 * 109/225 = 218/225 < 79/81.

Because a coefficient retained after a legal incidence-energy gate factors out
as a scalar square, the same coefficient applies verbatim to every already-
gated retained-coefficient branch.  No signed polarization term is converted
to energy in this file.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Real form of the sharpened all-prime reciprocal-square budget at the
physical endpoint. -/
theorem primeOwnerReciprocalSquareBudgetReal_le_109_over_225 (N : ℕ) :
    (∑ p ∈ primesUpTo N, (1 : ℝ) / (p : ℝ) ^ 2) ≤
      (109 / 225 : ℝ) := by
  have hbudgetQ := primeOwnerReciprocalSquareBudget_le_109_over_225 N
  have hcast :
      (((∑ p ∈ primesUpTo N,
          (1 : ℚ) / (p : ℚ) ^ 2 : ℚ)) : ℝ) ≤
        (((109 / 225 : ℚ)) : ℝ) := by
    unfold primeOwnerReciprocalSquareBudget at hbudgetQ
    exact_mod_cast hbudgetQ
  push_cast at hcast
  norm_num at hcast ⊢
  simpa [Nat.cast_pow] using hcast

/-- **Basel-sharpened contraction on the reversed greatest-owner graph.** -/
theorem lowOwnerGreatestOwnerReciprocalOutgoingEnergy_le_218_over_225
    (R : ℕ) (parent : ℕ × ℕ) :
    lowOwnerGreatestOwnerReciprocalOutgoingEnergy R parent ≤
      (218 / 225 : ℝ) *
        postRootCovarianceReciprocalPairEnergy parent := by
  have hout :=
    lowOwnerGreatestOwnerReciprocalOutgoingEnergy_le_twoPrimeBudget R parent
  have hbudget :=
    primeOwnerReciprocalSquareBudgetReal_le_109_over_225
      (squareRootEndpoint R)
  have hE := postRootCovarianceReciprocalPairEnergy_nonneg parent
  nlinarith

/-- The sharpened greatest-owner coefficient is strictly smaller than the old
`79/81` coefficient. -/
theorem greatestOwner_twoHundredEighteen_over_225_lt_79_over_81 :
    (218 / 225 : ℝ) < 79 / 81 := by
  norm_num

/-- **History-safe Basel contraction.**  Any real coefficient already attached
at a legal gate is retained through all later greatest-owner children with the
same `218/225` geometric factor. -/
theorem lowOwnerRetainedCoefficientOutgoingEnergy_le_218_over_225
    (R : ℕ) (parent : ℕ × ℕ) (coefficient : ℝ) :
    lowOwnerRetainedCoefficientOutgoingEnergy R parent coefficient ≤
      (218 / 225 : ℝ) *
        lowOwnerRetainedCoefficientParentEnergy coefficient parent := by
  rw [lowOwnerRetainedCoefficientOutgoingEnergy_eq_coefficient_sq_mul,
    lowOwnerRetainedCoefficientParentEnergy_eq_coefficient_sq_mul]
  have hout :=
    lowOwnerGreatestOwnerReciprocalOutgoingEnergy_le_218_over_225 R parent
  have hc : 0 ≤ coefficient ^ 2 := sq_nonneg coefficient
  calc
    coefficient ^ 2 * lowOwnerGreatestOwnerReciprocalOutgoingEnergy R parent ≤
        coefficient ^ 2 *
          ((218 / 225 : ℝ) * postRootCovarianceReciprocalPairEnergy parent) :=
      mul_le_mul_of_nonneg_left hout hc
    _ = (218 / 225 : ℝ) *
        (coefficient ^ 2 * postRootCovarianceReciprocalPairEnergy parent) := by
      ring

end RHLean.Proof
