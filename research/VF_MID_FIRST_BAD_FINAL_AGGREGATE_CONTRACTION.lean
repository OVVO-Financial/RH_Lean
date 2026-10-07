import Mathlib
import «research.VF_MID_FIRST_BAD_ACTIVE_RAW_PARENT_SPLICE»
import «research.VF_MID_FIRST_BAD_SOURCE_TO_SECTOR_SIX_INLET»
import «research.GLOBAL_RETURNED_CORE_RAW_PARENT_ORIENTED_BOUNDARY_NORMAL_FORM»
import «research.GLOBAL_RETURNED_CORE_STOKES_SIMULTANEOUS_CORE_FUBINI»

/-!
# First-bad final aggregate contraction

This file starts the terminal production layer on top of green #913.

The crucial first observation is stronger than the provisional architecture:
the actual #913 returned active source has **zero** mass on a fully completed
raw parent.  If the occurring greatest-owner child is the left mixed corner,
completion would force its p-returned corner to remain inside the clock,
contradicting the defining first-owner clipping of the active source.  If it is
the right mixed corner, completion makes the first coordinate p-admitted and
the #913 source weight is already zero.

Thus the actual source is entirely on the already-compiled incomplete raw
boundary.  We then reuse the existing six-way chronological/orientation Fubini
without changing the retained VF weight.

No square, norm, triangle inequality, or packet-to-child selector is used here.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- **Completed raw parents carry no actual #913 active source.**

The source is the returned clipped pair carrier.  A completed p/r cube cannot
contain a source-supported mixed corner with its retained VF coefficient. -/
theorem vfMidActiveReturnedRawParentFiberMass_eq_zero_of_completed
    {R p r : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (hp : p.Prime)
    (hcompleted :
      parent ∈ lowOwnerFirstOwnerCompletedPolarizationRawParentSet
        (R + 1) p sig r) :
    vfMidActiveReturnedRawParentFiberMass R p sig r parent = 0 := by
  unfold vfMidActiveReturnedRawParentFiberMass
  apply Finset.sum_eq_zero
  intro child hchild
  rcases
      lowOwnerFirstOwnerPolarizationFixedRawParentFiber_child_mixed hchild with
    hleft | hright
  · rw [hleft]
    have hblock :
        LowOwnerCompletedPolarizationBlock (R + 1) p (r, parent) :=
      (Finset.mem_filter.mp hcompleted).2
    have hpra :
        p * (r * parent.1) ≤ squareRootEndpoint (R + 1) := by
      rcases hblock with
        ⟨_hr, _hra, _hrb, _ha, _hpa, _hraX, hpra,
          _hb, _hpb, _hrbX, _hprb⟩
      exact hpra
    have hnot :
        (r * parent.1, parent.2) ∉
          vfMidActiveReturnedPairCarrier R p sig := by
      intro hmem
      have hclip :
          r * parent.1 ∈
            lowOwnerFirstOwnerClippedBaseFiber (R + 1) p sig :=
        (Finset.mem_product.mp hmem).1
      have hgt :
          squareRootEndpoint (R + 1) < p * (r * parent.1) :=
        (Finset.mem_filter.mp hclip).2
      omega
    simp [vfMidActiveReturnedPairWeight, hnot]
  · rw [hright]
    exact
      vfMidActiveReturnedPairWeight_secondMixed_eq_zero_of_completed
        hcompleted

/-- The completed part of the #913 raw-parent splice vanishes identically, so
the actual active source is exactly the incomplete raw boundary. -/
theorem vfMidActiveScaledReturnedClippedCellMass_eq_incompleteRawParents
    {R p : ℕ} {sig : Finset ℕ} (hp : p.Prime) :
    vfMidActiveScaledReturnedClippedCellMass R p sig =
      ∑ r ∈ lowOwnerRevealedPrimesAbove (R + 1) p,
        ∑ parent ∈
          lowOwnerFirstOwnerIncompletePolarizationRawParentSet
            (R + 1) p sig r,
          vfMidActiveReturnedRawParentFiberMass R p sig r parent := by
  rw [vfMidActiveScaledReturnedClippedCellMass_eq_completed_add_incomplete hp]
  apply Finset.sum_congr rfl
  intro r _hr
  have hzero :
      (∑ parent ∈
        lowOwnerFirstOwnerCompletedPolarizationRawParentSet
          (R + 1) p sig r,
        vfMidActiveReturnedRawParentFiberMass R p sig r parent) = 0 := by
    apply Finset.sum_eq_zero
    intro parent hparent
    exact
      vfMidActiveReturnedRawParentFiberMass_eq_zero_of_completed
        hp hparent
  rw [hzero, zero_add]

/-- Exact six-sector split of the retained-weight active boundary on one
greatest-owner label. -/
theorem sum_vfMidActiveReturnedIncomplete_eq_sixOrientedSectors
    {R p r : ℕ} {sig : Finset ℕ} (hp : p.Prime) :
    (∑ parent ∈
      lowOwnerFirstOwnerIncompletePolarizationRawParentSet
        (R + 1) p sig r,
      vfMidActiveReturnedRawParentFiberMass R p sig r parent) =
      (∑ parent ∈
        lowOwnerFirstOwnerIncompleteFirstClipLeftSet
          (R + 1) p sig r,
        vfMidActiveReturnedRawParentFiberMass R p sig r parent) +
      (∑ parent ∈
        lowOwnerFirstOwnerIncompleteFirstClipRightSet
          (R + 1) p sig r,
        vfMidActiveReturnedRawParentFiberMass R p sig r parent) +
      (∑ parent ∈
        lowOwnerFirstOwnerIncompleteNextClipLeftSet
          (R + 1) p sig r,
        vfMidActiveReturnedRawParentFiberMass R p sig r parent) +
      (∑ parent ∈
        lowOwnerFirstOwnerIncompleteNextClipRightSet
          (R + 1) p sig r,
        vfMidActiveReturnedRawParentFiberMass R p sig r parent) +
      (∑ parent ∈
        lowOwnerFirstOwnerIncompleteReturnedClipLeftSet
          (R + 1) p sig r,
        vfMidActiveReturnedRawParentFiberMass R p sig r parent) +
      ∑ parent ∈
        lowOwnerFirstOwnerIncompleteReturnedClipRightSet
          (R + 1) p sig r,
        vfMidActiveReturnedRawParentFiberMass R p sig r parent := by
  exact
    sum_lowOwnerFirstOwnerIncompleteRawParents_eq_sixOrientedSectors
      (R := R + 1) (p := p) (r := r) (sig := sig) hp
      (vfMidActiveReturnedRawParentFiberMass R p sig r)

/-- Global cell-level source routing: the #913 source is now expressed solely
on the six existing oriented incomplete-boundary ledgers. -/
theorem vfMidActiveScaledReturnedClippedCellMass_eq_sixOrientedBoundary
    {R p : ℕ} {sig : Finset ℕ} (hp : p.Prime) :
    vfMidActiveScaledReturnedClippedCellMass R p sig =
      ∑ r ∈ lowOwnerRevealedPrimesAbove (R + 1) p,
        ((∑ parent ∈
            lowOwnerFirstOwnerIncompleteFirstClipLeftSet
              (R + 1) p sig r,
            vfMidActiveReturnedRawParentFiberMass R p sig r parent) +
          (∑ parent ∈
            lowOwnerFirstOwnerIncompleteFirstClipRightSet
              (R + 1) p sig r,
            vfMidActiveReturnedRawParentFiberMass R p sig r parent) +
          (∑ parent ∈
            lowOwnerFirstOwnerIncompleteNextClipLeftSet
              (R + 1) p sig r,
            vfMidActiveReturnedRawParentFiberMass R p sig r parent) +
          (∑ parent ∈
            lowOwnerFirstOwnerIncompleteNextClipRightSet
              (R + 1) p sig r,
            vfMidActiveReturnedRawParentFiberMass R p sig r parent) +
          (∑ parent ∈
            lowOwnerFirstOwnerIncompleteReturnedClipLeftSet
              (R + 1) p sig r,
            vfMidActiveReturnedRawParentFiberMass R p sig r parent) +
          ∑ parent ∈
            lowOwnerFirstOwnerIncompleteReturnedClipRightSet
              (R + 1) p sig r,
            vfMidActiveReturnedRawParentFiberMass R p sig r parent) := by
  rw [vfMidActiveScaledReturnedClippedCellMass_eq_incompleteRawParents hp]
  apply Finset.sum_congr rfl
  intro r _hr
  exact sum_vfMidActiveReturnedIncomplete_eq_sixOrientedSectors hp

end RHLean.Analysis
