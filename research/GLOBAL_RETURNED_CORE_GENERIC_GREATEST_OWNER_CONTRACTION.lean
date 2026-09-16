import Mathlib
import «research.GLOBAL_RETURNED_CORE_GREATEST_OWNER_CONGESTION»

/-!
# Coefficient-agnostic greatest-owner reciprocal contraction

The `2/9` contraction is geometric.  Its proof does not depend on the special
formula used for the threshold Euler coefficient: once a scalar coefficient is
attached to a stripped `(r,parent)` block and retained unchanged on that block's
literal children, only

  * at most two children, and
  * reciprocal child energy = parent energy / r^2

are used.

This file exposes that fact for an arbitrary real block coefficient.  It is the
form needed after one or more completed Dirichlet owner differences have already
been applied: previous owner history may change the retained coefficient, but it
does not change the local `2/9` factor.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Reciprocal parent energy with an arbitrary retained real coefficient. -/
def lowOwnerRetainedCoefficientParentEnergy
    (coefficient : ℝ) (parent : ℕ × ℕ) : ℝ :=
  coefficient ^ 2 * postRootCovarianceReciprocalPairEnergy parent

/-- One literal child inherits the same block coefficient. -/
def lowOwnerRetainedCoefficientChildEnergy
    (coefficient : ℝ) (child : ℕ × ℕ) : ℝ :=
  coefficient ^ 2 * postRootCovarianceReciprocalPairEnergy child

@[simp] theorem lowOwnerRetainedCoefficientParentEnergy_nonneg
    (coefficient : ℝ) (parent : ℕ × ℕ) :
    0 ≤ lowOwnerRetainedCoefficientParentEnergy coefficient parent := by
  unfold lowOwnerRetainedCoefficientParentEnergy
  exact mul_nonneg (sq_nonneg coefficient)
    (postRootCovarianceReciprocalPairEnergy_nonneg parent)

/-- Exact fixed-owner scaling for an arbitrary retained coefficient. -/
theorem sum_lowOwnerRetainedCoefficientChildEnergy_eq
    {R r : ℕ} (hr : r.Prime) (parent : ℕ × ℕ) (coefficient : ℝ) :
    (∑ child ∈ lowOwnerGreatestOwnerFixedParentChildFiber R parent r,
      lowOwnerRetainedCoefficientChildEnergy coefficient child) =
      (lowOwnerGreatestOwnerFixedParentChildMultiplicity R parent r : ℝ) /
          (r : ℝ) ^ 2 *
        lowOwnerRetainedCoefficientParentEnergy coefficient parent := by
  unfold lowOwnerRetainedCoefficientChildEnergy
    lowOwnerRetainedCoefficientParentEnergy
  rw [← Finset.mul_sum]
  rw [sum_lowOwnerGreatestOwnerFixedParentChild_energy_eq hr]
  ring

/-- **History-safe `2/9` contraction.**  Any coefficient already accumulated
from earlier completed owner differences can be retained on the current block
without changing the contraction constant. -/
theorem sum_lowOwnerRetainedCoefficientChildEnergy_le_two_ninths
    {R r : ℕ} {parent : ℕ × ℕ} (hr : r.Prime) (hr3 : 3 ≤ r)
    (coefficient : ℝ) :
    (∑ child ∈ lowOwnerGreatestOwnerFixedParentChildFiber R parent r,
      lowOwnerRetainedCoefficientChildEnergy coefficient child) ≤
      (2 / 9 : ℝ) *
        lowOwnerRetainedCoefficientParentEnergy coefficient parent := by
  rw [sum_lowOwnerRetainedCoefficientChildEnergy_eq hr]
  have hr3' : (3 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr3
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr.pos
  have hmultNat :=
    lowOwnerGreatestOwnerFixedParentChildMultiplicity_le_two R parent r
  have hmult :
      (lowOwnerGreatestOwnerFixedParentChildMultiplicity R parent r : ℝ) ≤ 2 := by
    exact_mod_cast hmultNat
  have hratio :
      (lowOwnerGreatestOwnerFixedParentChildMultiplicity R parent r : ℝ) /
          (r : ℝ) ^ 2 ≤ 2 / 9 := by
    have hsquare : (9 : ℝ) ≤ (r : ℝ) ^ 2 := by nlinarith
    have hdenpos : (0 : ℝ) < (r : ℝ) ^ 2 := sq_pos_of_pos hrpos
    calc
      (lowOwnerGreatestOwnerFixedParentChildMultiplicity R parent r : ℝ) /
          (r : ℝ) ^ 2 ≤ 2 / (r : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hmult (le_of_lt hdenpos)
      _ ≤ 2 / 9 := by
        exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hsquare
  exact mul_le_mul_of_nonneg_right hratio
    (lowOwnerRetainedCoefficientParentEnergy_nonneg coefficient parent)

/-- Chronological form used in the low-owner graph. -/
theorem sum_lowOwnerRetainedCoefficientChildEnergy_le_two_ninths_of_owner_gt
    {R p r : ℕ} {parent : ℕ × ℕ}
    (hp : p.Prime) (hr : r.Prime) (hpr : p < r)
    (coefficient : ℝ) :
    (∑ child ∈ lowOwnerGreatestOwnerFixedParentChildFiber R parent r,
      lowOwnerRetainedCoefficientChildEnergy coefficient child) ≤
      (2 / 9 : ℝ) *
        lowOwnerRetainedCoefficientParentEnergy coefficient parent := by
  have hr3 : 3 ≤ r := by
    have hp2 : 2 ≤ p := hp.two_le
    omega
  exact sum_lowOwnerRetainedCoefficientChildEnergy_le_two_ninths
    hr hr3 coefficient

end RHLean.Proof
