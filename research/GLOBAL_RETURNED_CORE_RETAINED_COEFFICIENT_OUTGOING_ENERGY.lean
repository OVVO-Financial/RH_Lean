import Mathlib
import «research.GLOBAL_RETURNED_CORE_GENERIC_GREATEST_OWNER_CONTRACTION»
import «research.GLOBAL_RETURNED_CORE_GREATEST_OWNER_CONGESTION»

/-!
# History-safe all-owner contraction after the incidence-energy gate

This file lives entirely downstream of the signed polarization argument.

Once a completed incidence four-corner has crossed the legal energy gate, any
Euler coefficient accumulated at that gate is a fixed real scalar on the
resulting reciprocal-energy branch.  Later greatest-owner descent changes only
the reciprocal pair energy.  Therefore the existing all-owner `79/81`
contraction remains valid after multiplying the whole branch by an arbitrary
retained scalar square.

This does **not** convert a signed polarization ledger to energy, does not sum
distinct gate-owner coefficients into one square, and does not state a
recurrence for `Pi E`.  It is only a geometric side-ledger bound for energy
which has already passed through the completed-incidence gate.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Total greatest-owner reciprocal child energy after multiplying a whole
already-gated branch by one retained real coefficient. -/
def lowOwnerRetainedCoefficientOutgoingEnergy
    (R : ℕ) (parent : ℕ × ℕ) (coefficient : ℝ) : ℝ :=
  ∑ r ∈ primesUpTo (squareRootEndpoint R),
    ∑ child ∈ lowOwnerGreatestOwnerFixedParentChildFiber R parent r,
      lowOwnerRetainedCoefficientChildEnergy coefficient child

/-- The retained coefficient factors out of the entire downstream owner tree.
This is an exact identity, not an estimate. -/
theorem lowOwnerRetainedCoefficientOutgoingEnergy_eq_coefficient_sq_mul
    (R : ℕ) (parent : ℕ × ℕ) (coefficient : ℝ) :
    lowOwnerRetainedCoefficientOutgoingEnergy R parent coefficient =
      coefficient ^ 2 *
        lowOwnerGreatestOwnerReciprocalOutgoingEnergy R parent := by
  unfold lowOwnerRetainedCoefficientOutgoingEnergy
    lowOwnerGreatestOwnerReciprocalOutgoingEnergy
    lowOwnerRetainedCoefficientChildEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _hr
  rw [Finset.mul_sum]

/-- The matching retained-coefficient parent energy is exactly the same scalar
square times the raw reciprocal parent energy. -/
theorem lowOwnerRetainedCoefficientParentEnergy_eq_coefficient_sq_mul
    (coefficient : ℝ) (parent : ℕ × ℕ) :
    lowOwnerRetainedCoefficientParentEnergy coefficient parent =
      coefficient ^ 2 * postRootCovarianceReciprocalPairEnergy parent := by
  rfl

/-- **History-safe all-owner `79/81` contraction.**

After a legal completed-incidence gate has produced a reciprocal-energy branch,
any coefficient already accumulated at that gate may be retained through all
subsequent greatest-owner children without changing the global geometric
contraction factor. -/
theorem lowOwnerRetainedCoefficientOutgoingEnergy_le_79_over_81
    (R : ℕ) (parent : ℕ × ℕ) (coefficient : ℝ) :
    lowOwnerRetainedCoefficientOutgoingEnergy R parent coefficient ≤
      (79 / 81 : ℝ) *
        lowOwnerRetainedCoefficientParentEnergy coefficient parent := by
  rw [lowOwnerRetainedCoefficientOutgoingEnergy_eq_coefficient_sq_mul,
    lowOwnerRetainedCoefficientParentEnergy_eq_coefficient_sq_mul]
  have hout := lowOwnerGreatestOwnerReciprocalOutgoingEnergy_le_79_over_81
    R parent
  have hc : 0 ≤ coefficient ^ 2 := sq_nonneg coefficient
  calc
    coefficient ^ 2 * lowOwnerGreatestOwnerReciprocalOutgoingEnergy R parent ≤
        coefficient ^ 2 *
          ((79 / 81 : ℝ) * postRootCovarianceReciprocalPairEnergy parent) :=
      mul_le_mul_of_nonneg_left hout hc
    _ = (79 / 81 : ℝ) *
        (coefficient ^ 2 * postRootCovarianceReciprocalPairEnergy parent) := by
      ring

end RHLean.Proof
