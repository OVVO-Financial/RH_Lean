import Mathlib
import «research.GLOBAL_RETURNED_CORE_THRESHOLD_DIRECT_SUM_CONTRACTION»

/-!
# Actual threshold four-corner energy is the reciprocal child metric

The threshold/Euler intertwining already identifies the actual complete
next-owner four-corner amplitude with

  reciprocalPairAmplitude(parent) * EulerDiff(a) * EulerDiff(b).

Therefore its square is *exactly* the owner-labelled reciprocal parent energy.
No comparison constant and no site-product normalization remain.

Once this identity is made explicit, the literal fixed-owner child fibre gives
an exact `multiplicity/r^2` descendant energy.  Since every fresh next owner in
one compensated p-cell satisfies `p < r`, primality gives `r >= 3`, so the
complete descendant fibre costs at most `2/9` of the actual four-corner energy.
If the companion child is clipped, only one mixed child remains and the factor
improves to `1/9`.

This is the local theorem converting the nested-threshold kernel into the
already-compiled reciprocal child metric.  The remaining global step is only
the signed finite Fubini/owner telescope that assembles these local blocks.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- **Exact energy dictionary.**  The square of the actual complete threshold
four-corner is exactly the owner-labelled reciprocal parent energy. -/
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

/-- Exact fixed-owner descendant energy in units of the actual threshold
four-corner square. -/
theorem sum_lowOwnerThresholdEulerInheritedChildEnergy_eq_fourCorner_sq
    {R p W r a b : ℕ}
    (hr : r.Prime) (hra : ¬ r ∣ a) (hrb : ¬ r ∣ b)
    (ha : 0 < a) (hb : 0 < b) :
    (∑ child ∈ postRootCovarianceFixedOwnerChildFiber W (a, b) r,
      lowOwnerThresholdEulerInheritedChildEnergy R p r (a, b) child) =
      (postRootCovarianceFixedOwnerChildMultiplicity W (a, b) r : ℝ) /
          (r : ℝ) ^ 2 *
        (weightedMoebiusFreshPrimeFourCornerMass
          (lowOwnerThresholdOwnerIncidenceWeight R p) r a b) ^ 2 := by
  rw [sum_lowOwnerThresholdEulerInheritedChildEnergy_eq]
  rw [lowOwnerThresholdIncidence_fourCorner_sq_eq_eulerParentEnergy
    hr hra hrb ha hb]

/-- **Subcritical local kernel bridge.**  For a genuine next owner `r>p`, the
whole fixed-r descendant fibre has at most `2/9` of the actual complete
threshold four-corner energy. -/
theorem sum_lowOwnerThresholdEulerInheritedChildEnergy_le_two_ninths_fourCorner
    {R p W r a b : ℕ}
    (hp : p.Prime) (hr : r.Prime) (hpr : p < r)
    (hra : ¬ r ∣ a) (hrb : ¬ r ∣ b)
    (ha : 0 < a) (hb : 0 < b) :
    (∑ child ∈ postRootCovarianceFixedOwnerChildFiber W (a, b) r,
      lowOwnerThresholdEulerInheritedChildEnergy R p r (a, b) child) ≤
      (2 / 9 : ℝ) *
        (weightedMoebiusFreshPrimeFourCornerMass
          (lowOwnerThresholdOwnerIncidenceWeight R p) r a b) ^ 2 := by
  have hcon := sum_lowOwnerThresholdEulerInheritedChildEnergy_le_two_ninths
    (R := R) (p := p) (W := W) (r := r) (parent := (a, b)) hp hr hpr
  rw [← lowOwnerThresholdIncidence_fourCorner_sq_eq_eulerParentEnergy
    hr hra hrb ha hb] at hcon
  exact hcon

/-- **Clipped local kernel bridge.**  On a companion-clipped r-edge only one
mixed child survives, improving the local factor to `1/9`. -/
theorem sum_lowOwnerThresholdEulerInheritedChildEnergy_le_one_ninth_fourCorner_of_clipped
    {R p W r a b : ℕ}
    (hp : p.Prime) (hr : r.Prime) (hpr : p < r)
    (hra : ¬ r ∣ a) (hrb : ¬ r ∣ b)
    (ha : 0 < a) (hb : 0 < b)
    (hclip : W < r * b) :
    (∑ child ∈ postRootCovarianceFixedOwnerChildFiber W (a, b) r,
      lowOwnerThresholdEulerInheritedChildEnergy R p r (a, b) child) ≤
      (1 / 9 : ℝ) *
        (weightedMoebiusFreshPrimeFourCornerMass
          (lowOwnerThresholdOwnerIncidenceWeight R p) r a b) ^ 2 := by
  have hcon :=
    sum_lowOwnerThresholdEulerInheritedChildEnergy_le_one_ninth_of_clipped
      (R := R) (p := p) (W := W) (r := r) (parent := (a, b))
      hp hr hpr hclip
  rw [← lowOwnerThresholdIncidence_fourCorner_sq_eq_eulerParentEnergy
    hr hra hrb ha hb] at hcon
  exact hcon

end RHLean.Proof
