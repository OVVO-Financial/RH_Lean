import Mathlib
import «research.VF_MID_COMPLETED_GATE_PM_DENOMINATOR»

/-!
# Global completed-gate PM budget

Sum the literal completed-gate degree-two partial-moment denominators and the
corresponding all-depth positive clipped exits over the exact first-owner /
signature / later-greatest-owner chronology.

This file introduces no estimate beyond the already-compiled local #891/#898
half contraction.  It only performs the outer finite Fubini summation while
retaining every owner and signature label.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Global literal degree-two PM denominator on all active completed gates. -/
def vfMidGlobalCompletedGatePMDegreeTwoDenominator (R : ℕ) : ℝ :=
  ∑ p ∈ primesUpTo (squareRootEndpoint R),
    ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
      ∑ r ∈ lowOwnerRevealedPrimesAbove R p,
        vfMidCompletedGatePMDegreeTwoDenominator R p sig r

/-- Global selected reciprocal parent energy, with exactly the same chronology
as the literal PM denominator. -/
def vfMidGlobalCompletedGateSelectedParentEnergy (R : ℕ) : ℝ :=
  ∑ p ∈ primesUpTo (squareRootEndpoint R),
    ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
      ∑ r ∈ lowOwnerRevealedPrimesAbove R p,
        vfMidCompletedGateSelectedParentEnergy R p sig r

/-- Global positive clipped-exit tree energy on all active completed gates. -/
def vfMidGlobalCompletedGateSelectedClippedExitTreeEnergy
    (R depth : ℕ) : ℝ :=
  ∑ p ∈ primesUpTo (squareRootEndpoint R),
    ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
      ∑ r ∈ lowOwnerRevealedPrimesAbove R p,
        vfMidCompletedGateSelectedClippedExitTreeEnergy R p sig r depth

@[simp] theorem vfMidGlobalCompletedGatePMDegreeTwoDenominator_nonneg
    (R : ℕ) :
    0 ≤ vfMidGlobalCompletedGatePMDegreeTwoDenominator R := by
  unfold vfMidGlobalCompletedGatePMDegreeTwoDenominator
  apply Finset.sum_nonneg
  intro p _hp
  apply Finset.sum_nonneg
  intro sig _hsig
  apply Finset.sum_nonneg
  intro r _hr
  exact vfMidCompletedGatePMDegreeTwoDenominator_nonneg R p sig r

/-- The pointwise PM-to-parent-energy dictionary from #898 survives the full
outer owner/signature/greatest-owner Fubini with no loss. -/
theorem vfMidGlobalCompletedGatePMDegreeTwoDenominator_eq_selectedParentEnergy
    (R : ℕ) :
    vfMidGlobalCompletedGatePMDegreeTwoDenominator R =
      vfMidGlobalCompletedGateSelectedParentEnergy R := by
  unfold vfMidGlobalCompletedGatePMDegreeTwoDenominator
    vfMidGlobalCompletedGateSelectedParentEnergy
  apply Finset.sum_congr rfl
  intro p hpMem
  have hp : p.Prime := (mem_primesUpTo.mp hpMem).1
  apply Finset.sum_congr rfl
  intro sig _hsig
  apply Finset.sum_congr rfl
  intro r _hr
  exact vfMidCompletedGatePMDegreeTwoDenominator_eq_selectedParentEnergy
    (R := R) (p := p) (r := r) (sig := sig) hp

/-- **Global #891/#898 half contraction in literal PM currency.**

After summing over every first owner, signature, and legal later greatest
owner, the entire positive clipped descendant tree still costs at most one half
of the literal completed-gate degree-two PM denominator. -/
theorem vfMidGlobalCompletedGateSelectedClippedExitTreeEnergy_le_half_pmDegreeTwo
    (R depth : ℕ) :
    vfMidGlobalCompletedGateSelectedClippedExitTreeEnergy R depth ≤
      (1 / 2 : ℝ) *
        vfMidGlobalCompletedGatePMDegreeTwoDenominator R := by
  unfold vfMidGlobalCompletedGateSelectedClippedExitTreeEnergy
    vfMidGlobalCompletedGatePMDegreeTwoDenominator
  calc
    (∑ p ∈ primesUpTo (squareRootEndpoint R),
      ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
        ∑ r ∈ lowOwnerRevealedPrimesAbove R p,
          vfMidCompletedGateSelectedClippedExitTreeEnergy
            R p sig r depth) ≤
      ∑ p ∈ primesUpTo (squareRootEndpoint R),
        ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
          ∑ r ∈ lowOwnerRevealedPrimesAbove R p,
            (1 / 2 : ℝ) *
              vfMidCompletedGatePMDegreeTwoDenominator R p sig r := by
      apply Finset.sum_le_sum
      intro p hpMem
      have hp : p.Prime := (mem_primesUpTo.mp hpMem).1
      apply Finset.sum_le_sum
      intro sig _hsig
      apply Finset.sum_le_sum
      intro r hrMem
      have hr : r.Prime :=
        (mem_primesUpTo.mp (Finset.mem_filter.mp hrMem).1).1
      exact
        vfMidCompletedGateSelectedClippedExitTreeEnergy_le_half_pmDegreeTwo
          (R := R) (p := p) (r := r) (depth := depth) (sig := sig) hp hr
    _ = (1 / 2 : ℝ) *
        (∑ p ∈ primesUpTo (squareRootEndpoint R),
          ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
            ∑ r ∈ lowOwnerRevealedPrimesAbove R p,
              vfMidCompletedGatePMDegreeTwoDenominator R p sig r) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _hp
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro sig _hsig
      rw [Finset.mul_sum]

end RHLean.Analysis
