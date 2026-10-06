import Mathlib
import «research.VF_MID_FRACTIONAL_INCIDENCE_CAPACITY»
import «research.VF_MID_FINAL_SIGNED_RANK_CONTRACTION»

/-!
# VF completed-gate degree-two partial-moment denominator

The active completed incidence gate is the legal point where the signed
Dirichlet/threshold four-corner crosses into reciprocal parent-energy currency.

This file defines the degree-two PM denominator on the *physical gate atom*
itself:

  sum_parent |IncidenceFourCorner(parent)|^2.

It then proves, parent by parent, that this literal PM denominator is exactly
the selected retained reciprocal parent energy used by the final clipped-tree
contraction.  Thus the #891 one-half bound is stated directly against the
correct PM denominator, not against the deflated child-fibre denominator.

No cardinality estimate, child-energy substitution, or normalization shortcut
is used.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Degree-two absolute partial-moment denominator on the literal active
completed incidence-gate atoms. -/
def vfMidCompletedGatePMDegreeTwoDenominator
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : ℝ :=
  ∑ parent ∈
      lowOwnerFirstOwnerActiveCompletedPolarizationRawParentSet R p sig r,
    |lowOwnerCompletedIncidenceFourCornerMass R p (r, parent)| ^ 2

@[simp] theorem vfMidCompletedGatePMDegreeTwoDenominator_nonneg
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) :
    0 ≤ vfMidCompletedGatePMDegreeTwoDenominator R p sig r := by
  unfold vfMidCompletedGatePMDegreeTwoDenominator
  apply Finset.sum_nonneg
  intro parent _hparent
  exact sq_nonneg _

/-- **Exact PM-to-parent-energy currency crossing.**

The degree-two PM denominator on the actual completed incidence atoms is
exactly the selected reciprocal parent-energy ledger.  The proof crosses the
currency locally on every active completed raw parent; it does not define the
PM object by the energy object. -/
theorem vfMidCompletedGatePMDegreeTwoDenominator_eq_selectedParentEnergy
    {R p r : ℕ} {sig : Finset ℕ}
    (hp : p.Prime) :
    vfMidCompletedGatePMDegreeTwoDenominator R p sig r =
      vfMidCompletedGateSelectedParentEnergy R p sig r := by
  rw [vfMidCompletedGateSelectedParentEnergy_eq_activeOwnerParentEnergy]
  unfold vfMidCompletedGatePMDegreeTwoDenominator
  apply Finset.sum_congr rfl
  intro parent hparent
  have hcompleted :
      parent ∈
        lowOwnerFirstOwnerCompletedPolarizationRawParentSet R p sig r :=
    (Finset.mem_filter.mp hparent).1
  rcases lowOwnerFirstOwnerCompletedPolarizationRawParent_data hp hcompleted with
    ⟨hr, _hpr, hra, hrb, haPos, hbPos⟩
  rw [sq_abs]
  simpa [lowOwnerCompletedIncidenceFourCornerMass] using
    (lowOwnerThresholdIncidence_fourCorner_sq_eq_eulerParentEnergy
      (R := R) (p := p) (r := r)
      (a := parent.1) (b := parent.2)
      hr hra hrb haPos hbPos)

/-- Expanded form of the same equality: the PM denominator is literally the
sum of retained parent coefficients squared times reciprocal parent energy. -/
theorem vfMidCompletedGatePMDegreeTwoDenominator_eq_retainedParentSum
    {R p r : ℕ} {sig : Finset ℕ}
    (hp : p.Prime) :
    vfMidCompletedGatePMDegreeTwoDenominator R p sig r =
      ∑ parent ∈
        lowOwnerFirstOwnerActiveCompletedPolarizationRawParentSet R p sig r,
        lowOwnerThresholdEulerPairCoefficient R p r parent ^ 2 *
          postRootCovarianceReciprocalPairEnergy parent := by
  rw [vfMidCompletedGatePMDegreeTwoDenominator_eq_selectedParentEnergy hp]
  rfl

/-- **#891 in literal PM denominator currency.**

All positive clipped exits below an active completed gate packet cost at most
one half of the packet's degree-two PM denominator.  This is the correctly
typed version of the desired contraction: the right side is parent-energy
currency, not the deflated child-fibre denominator. -/
theorem vfMidCompletedGateSelectedClippedExitTreeEnergy_le_half_pmDegreeTwo
    {R p r depth : ℕ} {sig : Finset ℕ}
    (hp : p.Prime) (hr : r.Prime) :
    vfMidCompletedGateSelectedClippedExitTreeEnergy R p sig r depth ≤
      (1 / 2 : ℝ) *
        vfMidCompletedGatePMDegreeTwoDenominator R p sig r := by
  rw [vfMidCompletedGatePMDegreeTwoDenominator_eq_selectedParentEnergy hp]
  exact
    vfMidCompletedGateSelectedClippedExitTreeEnergy_le_half_selected
      (R := R) (p := p) (r := r) (depth := depth) (sig := sig) hr

end RHLean.Analysis
