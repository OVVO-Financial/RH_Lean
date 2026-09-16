import Mathlib
import «research.GLOBAL_RETURNED_CORE_THRESHOLD_DIRECT_SUM_CONTRACTION»
import «research.GLOBAL_RETURNED_CORE_DIRICHLET_INCIDENCE_CLOSURE»

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

/-!
## Completed-block Dirichlet/threshold currency

The global rank induction is carried by the Dirichlet-extended AMP incidence,
whereas the `2/9` theorem above is written in threshold-potential currency.
On a completed owner block all four relevant `p`-edges are physical, so the
constant mode in `F = w - 1` cancels and the two currencies agree exactly.
Endpoint-crossing cases are intentionally excluded here; they remain in the
named clipped/terminal continuation classes.
-/

/-- On a fully physical `p`-edge, Dirichlet incidence and threshold incidence
are literally the same coefficient. -/
theorem lowOwnerPhysicalDirichletIncidenceWeight_eq_threshold_of_complete
    {R p n : ℕ}
    (hn : n ≤ squareRootEndpoint R)
    (hpn : p * n ≤ squareRootEndpoint R) :
    lowOwnerPhysicalDirichletIncidenceWeight R p n =
      lowOwnerThresholdOwnerIncidenceWeight R p n := by
  unfold lowOwnerPhysicalDirichletIncidenceWeight
    lowOwnerThresholdOwnerIncidenceWeight
  rw [lowOwnerPhysicalDirichletWeight_eq_weight_of_le hn,
    lowOwnerPhysicalDirichletWeight_eq_weight_of_le hpn]
  simp only [lowOwnerThresholdPotential_eq_weight_sub_one]
  ring

/-- Consequently a completed next-owner four-corner is independent of whether
it is formed in the Dirichlet incidence or threshold-incidence coordinate. -/
theorem lowOwnerPhysicalDirichletIncidence_fourCorner_eq_threshold_of_complete
    {R p r a b : ℕ}
    (hr : r.Prime) (hra : ¬ r ∣ a) (hrb : ¬ r ∣ b)
    (ha : a ≤ squareRootEndpoint R)
    (hpa : p * a ≤ squareRootEndpoint R)
    (hraX : r * a ≤ squareRootEndpoint R)
    (hpraX : p * (r * a) ≤ squareRootEndpoint R)
    (hb : b ≤ squareRootEndpoint R)
    (hpb : p * b ≤ squareRootEndpoint R)
    (hrbX : r * b ≤ squareRootEndpoint R)
    (hprbX : p * (r * b) ≤ squareRootEndpoint R) :
    weightedMoebiusFreshPrimeFourCornerMass
        (lowOwnerPhysicalDirichletIncidenceWeight R p) r a b =
      weightedMoebiusFreshPrimeFourCornerMass
        (lowOwnerThresholdOwnerIncidenceWeight R p) r a b := by
  rw [weightedMoebiusFreshPrimeFourCornerMass_eq_ownerDifferences
      (lowOwnerPhysicalDirichletIncidenceWeight R p) hr hra hrb,
    weightedMoebiusFreshPrimeFourCornerMass_eq_ownerDifferences
      (lowOwnerThresholdOwnerIncidenceWeight R p) hr hra hrb]
  rw [lowOwnerPhysicalDirichletIncidenceWeight_eq_threshold_of_complete ha hpa,
    lowOwnerPhysicalDirichletIncidenceWeight_eq_threshold_of_complete hb hpb,
    lowOwnerPhysicalDirichletIncidenceWeight_eq_threshold_of_complete hraX hpraX,
    lowOwnerPhysicalDirichletIncidenceWeight_eq_threshold_of_complete hrbX hprbX]

/-- **Completed-block currency identification.**  The square of the actual
Dirichlet-incidence four-corner is exactly the owner-labelled inherited-
reciprocal parent energy used by the contraction theorem. -/
theorem lowOwnerPhysicalDirichletIncidence_fourCorner_sq_eq_eulerParentEnergy_of_complete
    {R p r a b : ℕ}
    (hr : r.Prime) (hra : ¬ r ∣ a) (hrb : ¬ r ∣ b)
    (haPos : 0 < a) (hbPos : 0 < b)
    (ha : a ≤ squareRootEndpoint R)
    (hpa : p * a ≤ squareRootEndpoint R)
    (hraX : r * a ≤ squareRootEndpoint R)
    (hpraX : p * (r * a) ≤ squareRootEndpoint R)
    (hb : b ≤ squareRootEndpoint R)
    (hpb : p * b ≤ squareRootEndpoint R)
    (hrbX : r * b ≤ squareRootEndpoint R)
    (hprbX : p * (r * b) ≤ squareRootEndpoint R) :
    (weightedMoebiusFreshPrimeFourCornerMass
        (lowOwnerPhysicalDirichletIncidenceWeight R p) r a b) ^ 2 =
      lowOwnerThresholdEulerParentEnergy R p r (a, b) := by
  rw [lowOwnerPhysicalDirichletIncidence_fourCorner_eq_threshold_of_complete
    hr hra hrb ha hpa hraX hpraX hb hpb hrbX hprbX]
  exact lowOwnerThresholdIncidence_fourCorner_sq_eq_eulerParentEnergy
    hr hra hrb haPos hbPos

/-- The existing `2/9` fixed-owner contraction therefore applies directly to a
completed Dirichlet-incidence block, exactly once and with no normalization
loss. -/
theorem sum_lowOwnerThresholdEulerInheritedGreatestChildEnergy_le_two_ninths_dirichletFourCorner_of_complete
    {R p r a b : ℕ}
    (hp : p.Prime) (hr : r.Prime) (hpr : p < r)
    (hra : ¬ r ∣ a) (hrb : ¬ r ∣ b)
    (haPos : 0 < a) (hbPos : 0 < b)
    (ha : a ≤ squareRootEndpoint R)
    (hpa : p * a ≤ squareRootEndpoint R)
    (hraX : r * a ≤ squareRootEndpoint R)
    (hpraX : p * (r * a) ≤ squareRootEndpoint R)
    (hb : b ≤ squareRootEndpoint R)
    (hpb : p * b ≤ squareRootEndpoint R)
    (hrbX : r * b ≤ squareRootEndpoint R)
    (hprbX : p * (r * b) ≤ squareRootEndpoint R) :
    (∑ child ∈ lowOwnerGreatestOwnerFixedParentChildFiber R (a, b) r,
      lowOwnerThresholdEulerInheritedGreatestChildEnergy
        R p r (a, b) child) ≤
      (2 / 9 : ℝ) *
        (weightedMoebiusFreshPrimeFourCornerMass
          (lowOwnerPhysicalDirichletIncidenceWeight R p) r a b) ^ 2 := by
  calc
    (∑ child ∈ lowOwnerGreatestOwnerFixedParentChildFiber R (a, b) r,
      lowOwnerThresholdEulerInheritedGreatestChildEnergy
        R p r (a, b) child) ≤
        (2 / 9 : ℝ) *
          (weightedMoebiusFreshPrimeFourCornerMass
            (lowOwnerThresholdOwnerIncidenceWeight R p) r a b) ^ 2 :=
      sum_lowOwnerThresholdEulerInheritedGreatestChildEnergy_le_two_ninths_fourCorner
        hp hr hpr hra hrb haPos hbPos
    _ = (2 / 9 : ℝ) *
        (weightedMoebiusFreshPrimeFourCornerMass
          (lowOwnerPhysicalDirichletIncidenceWeight R p) r a b) ^ 2 := by
      rw [lowOwnerPhysicalDirichletIncidence_fourCorner_eq_threshold_of_complete
        hr hra hrb ha hpa hraX hpraX hb hpb hrbX hprbX]

end RHLean.Proof
