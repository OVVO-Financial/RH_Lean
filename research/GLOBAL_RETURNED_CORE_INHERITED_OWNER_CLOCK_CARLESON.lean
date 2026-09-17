import Mathlib
import «research.GLOBAL_RETURNED_CORE_INHERITED_MIXED_CLOCK_L2»

/-!
# Weighted greatest-owner clock packing

The fixed `(p,r)` mixed-incidence clock L2 estimate from #747 is already
root-scale.  The physical inherited ledger carries the reciprocal owner factor
`1/r^2`, so summing those one-coordinate clock energies over all admissible
greatest owners costs only the compiled odd-prime reciprocal-square budget.

This is deliberately one-coordinate: it does not tensorize the clock estimate
and therefore does not introduce an artificial `R^4` loss.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Admissible exterior greatest owners above a fixed first owner. -/
def lowOwnerExteriorGreatestOwnerSet (R p : ℕ) : Finset ℕ :=
  ((primesUpTo (squareRootEndpoint R)).erase 2).filter (fun r => p < r)

/-- The reciprocal-square budget survives restriction to exterior owners. -/
theorem sum_lowOwnerExteriorGreatestOwner_inv_sq_le_quarter
    (R p : ℕ) :
    (∑ r ∈ lowOwnerExteriorGreatestOwnerSet R p,
      ((1 : ℝ) / (r : ℝ)) ^ 2) ≤ 1 / 4 := by
  have hsub :
      lowOwnerExteriorGreatestOwnerSet R p ⊆
        (primesUpTo (squareRootEndpoint R)).erase 2 := by
    exact Finset.filter_subset _ _
  calc
    (∑ r ∈ lowOwnerExteriorGreatestOwnerSet R p,
        ((1 : ℝ) / (r : ℝ)) ^ 2) ≤
      ∑ r ∈ (primesUpTo (squareRootEndpoint R)).erase 2,
        ((1 : ℝ) / (r : ℝ)) ^ 2 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsub
          intro r _hr _hnot
          positivity
    _ ≤ 1 / 4 := by
      simpa [div_pow] using
        (oddPrimeOwnerReciprocalSquareBudgetReal_le_quarter
          (squareRootEndpoint R))

/-- Weighted one-coordinate owner/clock energy. -/
def lowOwnerThresholdExteriorOwnerClockEnergy (R p : ℕ) : ℝ :=
  ∑ r ∈ lowOwnerExteriorGreatestOwnerSet R p,
    ((1 : ℝ) / (r : ℝ)) ^ 2 *
      ∑ n ∈ Finset.Icc 1 (squareRootEndpoint R),
        lowOwnerThresholdSecondOwnerDifference R p r n ^ 2

/-- **Root-scale greatest-owner Carleson bound.**  For one fixed first owner,
all exterior greatest owners together cost at most `5/4 * R^2`. -/
theorem lowOwnerThresholdExteriorOwnerClockEnergy_le_five_fourths_root_sq
    {R p : ℕ} (hR : 1 ≤ R) (hp : p.Prime) :
    lowOwnerThresholdExteriorOwnerClockEnergy R p ≤
      (5 / 4 : ℝ) * (R : ℝ) ^ 2 := by
  unfold lowOwnerThresholdExteriorOwnerClockEnergy
  have hterm : ∀ r ∈ lowOwnerExteriorGreatestOwnerSet R p,
      (∑ n ∈ Finset.Icc 1 (squareRootEndpoint R),
        lowOwnerThresholdSecondOwnerDifference R p r n ^ 2) ≤
        5 * (R : ℝ) ^ 2 := by
    intro r hrMem
    rcases Finset.mem_filter.mp hrMem with ⟨hrBase, hpr⟩
    have hrUp : r ∈ primesUpTo (squareRootEndpoint R) :=
      (Finset.mem_erase.mp hrBase).2
    have hrPrime : r.Prime := (mem_primesUpTo.mp hrUp).1
    exact sum_lowOwnerThresholdSecondOwnerDifference_sq_le_five_root_sq
      hR hp hrPrime hpr
  calc
    (∑ r ∈ lowOwnerExteriorGreatestOwnerSet R p,
        ((1 : ℝ) / (r : ℝ)) ^ 2 *
          ∑ n ∈ Finset.Icc 1 (squareRootEndpoint R),
            lowOwnerThresholdSecondOwnerDifference R p r n ^ 2) ≤
      ∑ r ∈ lowOwnerExteriorGreatestOwnerSet R p,
        ((1 : ℝ) / (r : ℝ)) ^ 2 * (5 * (R : ℝ) ^ 2) := by
          apply Finset.sum_le_sum
          intro r hrMem
          exact mul_le_mul_of_nonneg_left (hterm r hrMem) (sq_nonneg _)
    _ = (∑ r ∈ lowOwnerExteriorGreatestOwnerSet R p,
          ((1 : ℝ) / (r : ℝ)) ^ 2) * (5 * (R : ℝ) ^ 2) := by
      rw [Finset.sum_mul]
    _ ≤ (1 / 4 : ℝ) * (5 * (R : ℝ) ^ 2) := by
      exact mul_le_mul_of_nonneg_right
        (sum_lowOwnerExteriorGreatestOwner_inv_sq_le_quarter R p)
        (by positivity)
    _ = (5 / 4 : ℝ) * (R : ℝ) ^ 2 := by ring

end RHLean.Proof
