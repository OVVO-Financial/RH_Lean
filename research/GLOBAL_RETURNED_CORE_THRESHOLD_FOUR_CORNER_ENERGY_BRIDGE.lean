import Mathlib
import «research.GLOBAL_RETURNED_CORE_THRESHOLD_DIRECT_SUM_CONTRACTION»

/-!
# Actual threshold four-corner energy on the greatest-owner graph

The threshold/Euler intertwining identifies the complete next-owner four-corner
amplitude with reciprocal parent amplitude times the two Euler differences.
Its square is therefore exactly the owner-labelled reciprocal parent energy.

The descendant fibre used below is the unique-greatest-owner fibre required by
the global signed assembly.  No least-owner graph appears in this file.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- **Exact energy dictionary.** -/
theorem lowOwnerThresholdIncidence_fourCorner_sq_eq_eulerParentEnergy
    {R p r a b : ℕ}
    (hr : r.Prime) (hra : ¬ r ∣ a) (hrb : ¬ r ∣ b)
    (ha : 0 < a) (hb : 0 < b) :
    (weightedMoebiusFreshPrimeFourCornerMass
        (lowOwnerThresholdOwnerIncidenceWeight R p) r a b) ^ 2 =
      lowOwnerThresholdEulerParentEnergy R p r (a, b) := by
  rw [lowOwnerThresholdIncidence_fourCorner_eq_reciprocalEuler
    hr hra hrb ha hb]
  unfold lowOwnerThresholdEulerParentEnergy
    lowOwnerThresholdEulerPairCoefficient
    postRootCovarianceReciprocalPairEnergy
  ring

/-- Exact greatest-owner descendant energy in units of the actual threshold
four-corner square. -/
theorem sum_lowOwnerThresholdEulerInheritedGreatestChildEnergy_eq_fourCorner_sq
    {R p r a b : ℕ}
    (hr : r.Prime) (hra : ¬ r ∣ a) (hrb : ¬ r ∣ b)
    (ha : 0 < a) (hb : 0 < b) :
    (∑ child ∈ lowOwnerGreatestOwnerFixedParentChildFiber R (a, b) r,
      lowOwnerThresholdEulerInheritedGreatestChildEnergy
        R p r (a, b) child) =
      (lowOwnerGreatestOwnerFixedParentChildMultiplicity R (a, b) r : ℝ) /
          (r : ℝ) ^ 2 *
        (weightedMoebiusFreshPrimeFourCornerMass
          (lowOwnerThresholdOwnerIncidenceWeight R p) r a b) ^ 2 := by
  rw [sum_lowOwnerThresholdEulerInheritedGreatestChildEnergy_eq hr]
  rw [lowOwnerThresholdIncidence_fourCorner_sq_eq_eulerParentEnergy
    hr hra hrb ha hb]

/-- **Subcritical local kernel bridge on the correct graph.** -/
theorem sum_lowOwnerThresholdEulerInheritedGreatestChildEnergy_le_two_ninths_fourCorner
    {R p r a b : ℕ}
    (hp : p.Prime) (hr : r.Prime) (hpr : p < r)
    (hra : ¬ r ∣ a) (hrb : ¬ r ∣ b)
    (ha : 0 < a) (hb : 0 < b) :
    (∑ child ∈ lowOwnerGreatestOwnerFixedParentChildFiber R (a, b) r,
      lowOwnerThresholdEulerInheritedGreatestChildEnergy
        R p r (a, b) child) ≤
      (2 / 9 : ℝ) *
        (weightedMoebiusFreshPrimeFourCornerMass
          (lowOwnerThresholdOwnerIncidenceWeight R p) r a b) ^ 2 := by
  have hcon :=
    sum_lowOwnerThresholdEulerInheritedGreatestChildEnergy_le_two_ninths
      (R := R) (p := p) (r := r) (parent := (a, b)) hp hr hpr
  rw [← lowOwnerThresholdIncidence_fourCorner_sq_eq_eulerParentEnergy
    hr hra hrb ha hb] at hcon
  exact hcon

/-- **Clipped local kernel bridge.**  This applies only after an atom has left
the Dirichlet polarization and entered inherited reciprocal currency. -/
theorem sum_lowOwnerThresholdEulerInheritedGreatestChildEnergy_le_one_ninth_fourCorner_of_clipped
    {R p r a b : ℕ}
    (hp : p.Prime) (hr : r.Prime) (hpr : p < r)
    (hra : ¬ r ∣ a) (hrb : ¬ r ∣ b)
    (ha : 0 < a) (hb : 0 < b)
    (hclip : squareRootEndpoint R < r * b) :
    (∑ child ∈ lowOwnerGreatestOwnerFixedParentChildFiber R (a, b) r,
      lowOwnerThresholdEulerInheritedGreatestChildEnergy
        R p r (a, b) child) ≤
      (1 / 9 : ℝ) *
        (weightedMoebiusFreshPrimeFourCornerMass
          (lowOwnerThresholdOwnerIncidenceWeight R p) r a b) ^ 2 := by
  have hcon :=
    sum_lowOwnerThresholdEulerInheritedGreatestChildEnergy_le_one_ninth_of_clipped
      (R := R) (p := p) (r := r) (parent := (a, b))
      hp hr hpr hclip
  rw [← lowOwnerThresholdIncidence_fourCorner_sq_eq_eulerParentEnergy
    hr hra hrb ha hb] at hcon
  exact hcon

end RHLean.Proof
