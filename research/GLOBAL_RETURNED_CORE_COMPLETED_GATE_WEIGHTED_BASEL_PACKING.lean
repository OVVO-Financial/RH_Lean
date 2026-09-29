import Mathlib
import «research.GLOBAL_RETURNED_CORE_EMITTED_RECIPROCAL_CHARGE»
import «research.GLOBAL_RETURNED_CORE_INHERITED_BASEL_ACTIVITY»

/-!
# Completed gate: weighted mixed-incidence / Basel activity normal form

The completed incidence gate should be estimated before the existing `2/9`
collapse to the unweighted owner-parent ledger.  On every completed raw parent,
the literal inherited child sum retains its physical
`multiplicity / r^2` factor.  Exact Möbius/denominator cancellation then
identifies the remaining parent currency with the product of two deterministic
mixed threshold-incidence squares.

This module records that exact normal form and immediately replaces each
second-incidence square by the compiled Basel-sharpened activity majorant.
The output is a completely positive, Möbius-free threshold-window packing
problem.  No owner count, Cauchy square of a fibre sum, Mertens estimate, or
asymptotic argument is introduced.
-/

noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Completed raw parents really lie on the nonzero Möbius base fibre in both
coordinates.  This is the exact support fact needed for the denominator
cancellation in the mixed-incidence dictionary. -/
private theorem completedPolarizationRawParent_base_data
    {R p r : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (hp : p.Prime)
    (hparent :
      parent ∈ lowOwnerFirstOwnerCompletedPolarizationRawParentSet R p sig r) :
    parent.1 ∈ lowOwnerFirstOwnerBaseFiber R p sig ∧
      parent.2 ∈ lowOwnerFirstOwnerBaseFiber R p sig := by
  rcases mem_lowOwnerFirstOwnerCompletedPolarizationRawParentSet.mp hparent with
    ⟨hraw, _hcomplete⟩
  rcases Finset.mem_image.mp hraw with ⟨rawChild, hrawChild, hrawEq⟩
  have hbase :=
    lowOwnerFirstOwnerPolarization_child_rawParent_mem_same_cell hp hrawChild
  rw [hrawEq] at hbase
  exact hbase

private theorem completedPolarizationRawParent_mobius_ne_zero
    {R p r : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (hp : p.Prime)
    (hparent :
      parent ∈ lowOwnerFirstOwnerCompletedPolarizationRawParentSet R p sig r) :
    realMoebiusStep parent.1 ≠ 0 ∧ realMoebiusStep parent.2 ≠ 0 := by
  rcases completedPolarizationRawParent_base_data hp hparent with ⟨ha, hb⟩
  have haCar := (Finset.mem_filter.mp ha).1
  have hbCar := (Finset.mem_filter.mp hb).1
  exact ⟨(Finset.mem_filter.mp haCar).2, (Finset.mem_filter.mp hbCar).2⟩

/-- The deterministic positive activity expression controlling one mixed
second incidence. -/
def lowOwnerThresholdBaselSecondDifferenceActivity
    (R p r n : ℕ) : ℝ :=
  (211 / 450 : ℝ) *
      (∑ q ∈ canonicalRoughLowQ2Owners R,
        (lowOwnerThresholdCrossingIndicator
            p n (rawQ2ChildCutoff R q) +
          lowOwnerThresholdCrossingIndicator
            p (r * n) (rawQ2ChildCutoff R q))) +
    2 *
      (lowOwnerThresholdCrossingIndicator p n (R - 1) +
        lowOwnerThresholdCrossingIndicator p (r * n) (R - 1))

theorem lowOwnerThresholdBaselSecondDifferenceActivity_nonneg
    (R p r n : ℕ) :
    0 ≤ lowOwnerThresholdBaselSecondDifferenceActivity R p r n := by
  unfold lowOwnerThresholdBaselSecondDifferenceActivity
  have hq :
      0 ≤
        (∑ q ∈ canonicalRoughLowQ2Owners R,
          (lowOwnerThresholdCrossingIndicator
              p n (rawQ2ChildCutoff R q) +
            lowOwnerThresholdCrossingIndicator
              p (r * n) (rawQ2ChildCutoff R q))) := by
    apply Finset.sum_nonneg
    intro q _hq
    unfold lowOwnerThresholdCrossingIndicator
    split <;> split <;> norm_num
  have hr0 :
      0 ≤ lowOwnerThresholdCrossingIndicator p n (R - 1) := by
    unfold lowOwnerThresholdCrossingIndicator
    split <;> norm_num
  have hr1 :
      0 ≤ lowOwnerThresholdCrossingIndicator p (r * n) (R - 1) := by
    unfold lowOwnerThresholdCrossingIndicator
    split <;> norm_num
  positivity

/-- Basel-sharpened pointwise control, repackaged as a named nonnegative
activity currency. -/
theorem lowOwnerThresholdSecondOwnerDifference_sq_le_baselActivity
    {R p r n : ℕ}
    (hR : 1 ≤ R) (hp : p.Prime) (hr : r.Prime)
    (hpr : p < r) (hn : 0 < n) :
    lowOwnerThresholdSecondOwnerDifference R p r n ^ 2 ≤
      lowOwnerThresholdBaselSecondDifferenceActivity R p r n := by
  exact
    lowOwnerThresholdSecondOwnerDifference_sq_le_twoTermBasel_activity
      hR hp hr hpr hn

/-- Exact weighted mixed-incidence form of one completed gate packet.  The
`multiplicity / r^2` factor is retained instead of being discarded into the
coarse `2/9` owner-parent bound. -/
theorem lowOwnerFirstOwnerCompletedInheritedReciprocalEnergy_eq_weightedMixedIncidence
    {R p r : ℕ} {sig : Finset ℕ}
    (hp : p.Prime) :
    lowOwnerFirstOwnerCompletedInheritedReciprocalEnergy R p sig r =
      ∑ parent ∈
        lowOwnerFirstOwnerCompletedPolarizationRawParentSet R p sig r,
        (lowOwnerGreatestOwnerFixedParentChildMultiplicity R parent r : ℝ) /
            (r : ℝ) ^ 2 *
          lowOwnerThresholdMixedIncidencePairEnergy R p r parent := by
  unfold lowOwnerFirstOwnerCompletedInheritedReciprocalEnergy
  apply Finset.sum_congr rfl
  intro parent hparent
  rcases lowOwnerFirstOwnerCompletedPolarizationRawParent_data hp hparent with
    ⟨hr, _hpr, _hra, _hrb, haPos, hbPos⟩
  rcases completedPolarizationRawParent_mobius_ne_zero hp hparent with
    ⟨haMu, hbMu⟩
  exact
    sum_lowOwnerThresholdEulerInheritedGreatestChildEnergy_eq_mixedIncidence
      (R := R) (p := p) (r := r) (parent := parent)
      hr haPos hbPos haMu hbMu

/-- Positive Basel activity majorant for one completed `(p,sig,r)` packet. -/
def lowOwnerFirstOwnerCompletedWeightedBaselActivity
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : ℝ :=
  ∑ parent ∈
      lowOwnerFirstOwnerCompletedPolarizationRawParentSet R p sig r,
    (lowOwnerGreatestOwnerFixedParentChildMultiplicity R parent r : ℝ) /
        (r : ℝ) ^ 2 *
      lowOwnerThresholdBaselSecondDifferenceActivity R p r parent.1 *
      lowOwnerThresholdBaselSecondDifferenceActivity R p r parent.2

/-- **Completed gate -> positive threshold-window census.**

Every emitted reciprocal atom is bounded while its native `1/r^2` owner
weight and duplicate-free child multiplicity are still attached. -/
theorem lowOwnerFirstOwnerCompletedInheritedReciprocalEnergy_le_weightedBaselActivity
    {R p r : ℕ} {sig : Finset ℕ}
    (hR : 1 ≤ R) (hp : p.Prime) :
    lowOwnerFirstOwnerCompletedInheritedReciprocalEnergy R p sig r ≤
      lowOwnerFirstOwnerCompletedWeightedBaselActivity R p sig r := by
  rw [lowOwnerFirstOwnerCompletedInheritedReciprocalEnergy_eq_weightedMixedIncidence hp]
  unfold lowOwnerFirstOwnerCompletedWeightedBaselActivity
  apply Finset.sum_le_sum
  intro parent hparent
  rcases lowOwnerFirstOwnerCompletedPolarizationRawParent_data hp hparent with
    ⟨hr, hpr, _hra, _hrb, haPos, hbPos⟩
  have ha :=
    lowOwnerThresholdSecondOwnerDifference_sq_le_baselActivity
      hR hp hr hpr haPos
  have hb :=
    lowOwnerThresholdSecondOwnerDifference_sq_le_baselActivity
      hR hp hr hpr hbPos
  have hAa :=
    lowOwnerThresholdBaselSecondDifferenceActivity_nonneg
      R p r parent.1
  have hAb :=
    lowOwnerThresholdBaselSecondDifferenceActivity_nonneg
      R p r parent.2
  have hda : 0 ≤ lowOwnerThresholdSecondOwnerDifference R p r parent.1 ^ 2 :=
    sq_nonneg _
  have hdb : 0 ≤ lowOwnerThresholdSecondOwnerDifference R p r parent.2 ^ 2 :=
    sq_nonneg _
  have hprod :
      lowOwnerThresholdMixedIncidencePairEnergy R p r parent ≤
        lowOwnerThresholdBaselSecondDifferenceActivity R p r parent.1 *
          lowOwnerThresholdBaselSecondDifferenceActivity R p r parent.2 := by
    unfold lowOwnerThresholdMixedIncidencePairEnergy
    exact
      (mul_le_mul ha hb hdb hAa)
  have hmult :
      0 ≤
        (lowOwnerGreatestOwnerFixedParentChildMultiplicity R parent r : ℝ) /
          (r : ℝ) ^ 2 := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hprod hmult
  simpa [mul_assoc] using hscaled

/-- Global positive packing ledger produced by the preceding local reduction. -/
def lowOwnerCompletedGateWeightedBaselActivity (R : ℕ) : ℝ :=
  ∑ p ∈ primesUpTo (squareRootEndpoint R),
    ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
      ∑ r ∈ primesUpTo (squareRootEndpoint R),
        lowOwnerFirstOwnerCompletedWeightedBaselActivity R p sig r

/-- **Global weighted-gate reduction.**

The entire completed gate is now bounded by a Möbius-free positive census of
literal threshold windows with the native reciprocal greatest-owner weights. -/
theorem lowOwnerCompletedGateEmittedEnergy_le_weightedBaselActivity
    {R : ℕ} (hR : 1 ≤ R) :
    lowOwnerCompletedGateEmittedEnergy R ≤
      lowOwnerCompletedGateWeightedBaselActivity R := by
  unfold lowOwnerCompletedGateEmittedEnergy
    lowOwnerFirstOwnerCompletedGateEmittedEnergy
    lowOwnerCompletedGateWeightedBaselActivity
  apply Finset.sum_le_sum
  intro p hpMem
  have hp : p.Prime := (mem_primesUpTo.mp hpMem).1
  apply Finset.sum_le_sum
  intro sig _hsig
  apply Finset.sum_le_sum
  intro r _hr
  exact
    lowOwnerFirstOwnerCompletedInheritedReciprocalEnergy_le_weightedBaselActivity
      hR hp

/-- The precise remaining positive packing statement after all arithmetic
currency changes have been discharged.  Any fixed `A,B` satisfying this
immediately gives the desired universal completed-gate injection bound. -/
def LowOwnerCompletedGateWeightedBaselPackingBound (A B : ℝ) : Prop :=
  ∀ R : ℕ, ∀ K : ℝ,
    56 ≤ R →
    LowerMertensCriticalEnvelope R K →
    lowOwnerCompletedGateWeightedBaselActivity R ≤
      A * canonicalRoughLowQ2DaughterEnergy R +
        B * (R : ℝ) ^ 2 * K

theorem lowOwnerCompletedGateEmittedEnergy_le_q2_add_rootEnvelope_of_weightedBaselPacking
    {A B : ℝ}
    (hpack : LowOwnerCompletedGateWeightedBaselPackingBound A B) :
    ∀ R : ℕ, ∀ K : ℝ,
      56 ≤ R →
      LowerMertensCriticalEnvelope R K →
      lowOwnerCompletedGateEmittedEnergy R ≤
        A * canonicalRoughLowQ2DaughterEnergy R +
          B * (R : ℝ) ^ 2 * K := by
  intro R K hR hK
  have hgate :=
    lowOwnerCompletedGateEmittedEnergy_le_weightedBaselActivity
      (R := R) (by omega)
  exact hgate.trans (hpack R K hR hK)

end RHLean.Proof
