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
        hparent
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


/-! ## Eliminate the three impossible oriented sectors -/

private theorem vfMidActiveReturnedPairWeight_eq_zero_of_not_mem
    {R p : ℕ} {sig : Finset ℕ} {ab : ℕ × ℕ}
    (hnot : ab ∉ vfMidActiveReturnedPairCarrier R p sig) :
    vfMidActiveReturnedPairWeight R p sig ab = 0 := by
  simp [vfMidActiveReturnedPairWeight, hnot]

/-- A first-owner right clip cannot carry the returned active source.
The right clip makes the returned second coordinate non-admitted, while the
complementary orientation keeps the first coordinate non-clipped. -/
theorem vfMidActiveReturnedRawParentFiberMass_eq_zero_of_firstClipRight
    {R p r : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (hparent :
      parent ∈ lowOwnerFirstOwnerIncompleteFirstClipRightSet
        (R + 1) p sig r) :
    vfMidActiveReturnedRawParentFiberMass R p sig r parent = 0 := by
  unfold vfMidActiveReturnedRawParentFiberMass
  apply Finset.sum_eq_zero
  intro child hchild
  have hnotLeft :
      ¬ squareRootEndpoint (R + 1) < p * parent.1 :=
    (Finset.mem_filter.mp hparent).2
  have hright :
      squareRootEndpoint (R + 1) < p * parent.2 :=
    lowOwnerFirstOwnerIncompleteFirstClipRight_mem_implies_rightClip hparent
  rcases
      lowOwnerFirstOwnerPolarizationFixedRawParentFiber_child_mixed hchild with
    hleft | hrightMixed
  · rw [hleft]
    apply vfMidActiveReturnedPairWeight_eq_zero_of_not_mem
    intro hmem
    have hadm :
        parent.2 ∈ lowOwnerFirstOwnerAdmittedBaseFiber (R + 1) p sig :=
      (Finset.mem_product.mp hmem).2
    have hle :
        p * parent.2 ≤ squareRootEndpoint (R + 1) :=
      (Finset.mem_filter.mp hadm).2
    omega
  · rw [hrightMixed]
    apply vfMidActiveReturnedPairWeight_eq_zero_of_not_mem
    intro hmem
    have hclip :
        parent.1 ∈ lowOwnerFirstOwnerClippedBaseFiber (R + 1) p sig :=
      (Finset.mem_product.mp hmem).1
    have hgt :
        squareRootEndpoint (R + 1) < p * parent.1 :=
      (Finset.mem_filter.mp hclip).2
    exact hnotLeft hgt

/-- A next-owner left clip cannot carry the returned active source.
The left mixed child is already outside the physical clock; the right mixed
child starts from a p-admitted first coordinate. -/
theorem vfMidActiveReturnedRawParentFiberMass_eq_zero_of_nextClipLeft
    {R p r : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (hparent :
      parent ∈ lowOwnerFirstOwnerIncompleteNextClipLeftSet
        (R + 1) p sig r) :
    vfMidActiveReturnedRawParentFiberMass R p sig r parent = 0 := by
  unfold vfMidActiveReturnedRawParentFiberMass
  apply Finset.sum_eq_zero
  intro child hchild
  have hnext :
      parent ∈ lowOwnerFirstOwnerIncompleteNextClipSet
        (R + 1) p sig r :=
    (Finset.mem_filter.mp hparent).1
  have hleft :
      squareRootEndpoint (R + 1) < r * parent.1 :=
    (Finset.mem_filter.mp hparent).2
  have hclass :
      LowOwnerRawParentNextOwnerClipped (R + 1) p r parent :=
    (Finset.mem_filter.mp hnext).2
  rcases
      lowOwnerFirstOwnerPolarizationFixedRawParentFiber_child_mixed hchild with
    hleftMixed | hrightMixed
  · have hgreatest :
        child ∈ lowOwnerFirstOwnerPolarizationGreatestOwnerPairFiber
          (R + 1) p sig r :=
      (Finset.mem_filter.mp hchild).1
    have hoff :
        child ∈ lowOwnerFirstOwnerBaseOffDiagonalPairCarrier
          (R + 1) p sig :=
      (Finset.mem_filter.mp hgreatest).1
    have hprod :
        child ∈
          (lowOwnerFirstOwnerBaseFiber (R + 1) p sig).product
            (lowOwnerFirstOwnerBaseFiber (R + 1) p sig) :=
      (Finset.mem_filter.mp hoff).1
    have hbase :
        child.1 ∈ lowOwnerFirstOwnerBaseFiber (R + 1) p sig :=
      (Finset.mem_product.mp hprod).1
    have hcar := (Finset.mem_filter.mp hbase).1
    have hicc := (Finset.mem_filter.mp hcar).1
    have hle : child.1 ≤ squareRootEndpoint (R + 1) :=
      (Finset.mem_Icc.mp hicc).2
    rw [hleftMixed] at hle
    omega
  · rw [hrightMixed]
    apply vfMidActiveReturnedPairWeight_eq_zero_of_not_mem
    intro hmem
    have hclip :
        parent.1 ∈ lowOwnerFirstOwnerClippedBaseFiber (R + 1) p sig :=
      (Finset.mem_product.mp hmem).1
    have hgt :
        squareRootEndpoint (R + 1) < p * parent.1 :=
      (Finset.mem_filter.mp hclip).2
    exact (Nat.not_lt_of_ge hclass.1) hgt

/-- A returned-next right clip cannot carry the returned active source.
Left priority says the left returned corner remains inside, and the right mixed
orientation starts from a p-admitted first coordinate. -/
theorem vfMidActiveReturnedRawParentFiberMass_eq_zero_of_returnedClipRight
    {R p r : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (hparent :
      parent ∈ lowOwnerFirstOwnerIncompleteReturnedClipRightSet
        (R + 1) p sig r) :
    vfMidActiveReturnedRawParentFiberMass R p sig r parent = 0 := by
  unfold vfMidActiveReturnedRawParentFiberMass
  apply Finset.sum_eq_zero
  intro child hchild
  have hret :
      parent ∈ lowOwnerFirstOwnerIncompleteReturnedClipSet
        (R + 1) p sig r :=
    (Finset.mem_filter.mp hparent).1
  have hnotLeft :
      ¬ squareRootEndpoint (R + 1) < p * (r * parent.1) :=
    (Finset.mem_filter.mp hparent).2
  have hclass :
      LowOwnerRawParentReturnedNextClipped (R + 1) p r parent :=
    (Finset.mem_filter.mp hret).2
  rcases
      lowOwnerFirstOwnerPolarizationFixedRawParentFiber_child_mixed hchild with
    hleftMixed | hrightMixed
  · rw [hleftMixed]
    apply vfMidActiveReturnedPairWeight_eq_zero_of_not_mem
    intro hmem
    have hclip :
        r * parent.1 ∈
          lowOwnerFirstOwnerClippedBaseFiber (R + 1) p sig :=
      (Finset.mem_product.mp hmem).1
    have hgt :
        squareRootEndpoint (R + 1) < p * (r * parent.1) :=
      (Finset.mem_filter.mp hclip).2
    exact hnotLeft hgt
  · rw [hrightMixed]
    apply vfMidActiveReturnedPairWeight_eq_zero_of_not_mem
    intro hmem
    have hclip :
        parent.1 ∈ lowOwnerFirstOwnerClippedBaseFiber (R + 1) p sig :=
      (Finset.mem_product.mp hmem).1
    have hgt :
        squareRootEndpoint (R + 1) < p * parent.1 :=
      (Finset.mem_filter.mp hclip).2
    exact (Nat.not_lt_of_ge hclass.1) hgt

/-- The actual #913 source therefore occupies only three of the six oriented
boundary sectors: first-left, next-right, and returned-left. -/
theorem vfMidActiveScaledReturnedClippedCellMass_eq_threeBoundarySectors
    {R p : ℕ} {sig : Finset ℕ} (hp : p.Prime) :
    vfMidActiveScaledReturnedClippedCellMass R p sig =
      ∑ r ∈ lowOwnerRevealedPrimesAbove (R + 1) p,
        ((∑ parent ∈
            lowOwnerFirstOwnerIncompleteFirstClipLeftSet
              (R + 1) p sig r,
            vfMidActiveReturnedRawParentFiberMass R p sig r parent) +
          (∑ parent ∈
            lowOwnerFirstOwnerIncompleteNextClipRightSet
              (R + 1) p sig r,
            vfMidActiveReturnedRawParentFiberMass R p sig r parent) +
          ∑ parent ∈
            lowOwnerFirstOwnerIncompleteReturnedClipLeftSet
              (R + 1) p sig r,
            vfMidActiveReturnedRawParentFiberMass R p sig r parent) := by
  rw [vfMidActiveScaledReturnedClippedCellMass_eq_sixOrientedBoundary hp]
  apply Finset.sum_congr rfl
  intro r _hr
  have hfr :
      (∑ parent ∈
        lowOwnerFirstOwnerIncompleteFirstClipRightSet
          (R + 1) p sig r,
        vfMidActiveReturnedRawParentFiberMass R p sig r parent) = 0 := by
    apply Finset.sum_eq_zero
    intro parent hparent
    exact
      vfMidActiveReturnedRawParentFiberMass_eq_zero_of_firstClipRight hparent
  have hnl :
      (∑ parent ∈
        lowOwnerFirstOwnerIncompleteNextClipLeftSet
          (R + 1) p sig r,
        vfMidActiveReturnedRawParentFiberMass R p sig r parent) = 0 := by
    apply Finset.sum_eq_zero
    intro parent hparent
    exact
      vfMidActiveReturnedRawParentFiberMass_eq_zero_of_nextClipLeft hparent
  have hrr :
      (∑ parent ∈
        lowOwnerFirstOwnerIncompleteReturnedClipRightSet
          (R + 1) p sig r,
        vfMidActiveReturnedRawParentFiberMass R p sig r parent) = 0 := by
    apply Finset.sum_eq_zero
    intro parent hparent
    exact
      vfMidActiveReturnedRawParentFiberMass_eq_zero_of_returnedClipRight hparent
  rw [hfr, hnl, hrr]
  ring


/-! ## Collapse the complete #911 excess to one three-boundary budget -/

/-- The globally assembled retained-weight mass on the only three oriented
raw-parent sectors which can carry the actual active source. -/
def vfMidActiveThreeBoundaryMass (R : ℕ) : ℝ :=
  ∑ p ∈ primesUpTo (squareRootEndpoint (R + 1)),
    ∑ sig ∈ lowOwnerFirstOwnerSignatureSet (R + 1) p,
      ∑ r ∈ lowOwnerRevealedPrimesAbove (R + 1) p,
        ((∑ parent ∈
            lowOwnerFirstOwnerIncompleteFirstClipLeftSet
              (R + 1) p sig r,
            vfMidActiveReturnedRawParentFiberMass R p sig r parent) +
          (∑ parent ∈
            lowOwnerFirstOwnerIncompleteNextClipRightSet
              (R + 1) p sig r,
            vfMidActiveReturnedRawParentFiberMass R p sig r parent) +
          ∑ parent ∈
            lowOwnerFirstOwnerIncompleteReturnedClipLeftSet
              (R + 1) p sig r,
            vfMidActiveReturnedRawParentFiberMass R p sig r parent)

/-- Global Fubini: the sum of actual active cell Grams is exactly the
three-boundary mass. -/
theorem sum_vfMidActiveCellGram_eq_threeBoundaryMass
    {R : ℕ} (hR : 3 ≤ R) :
    (∑ p ∈ primesUpTo (squareRootEndpoint (R + 1)),
      ∑ sig ∈ lowOwnerFirstOwnerSignatureSet (R + 1) p,
        lowOwnerFirstOwnerCellGramWith
          (R + 1) p sig (vfMidOneBlockActivePhysicalSite R)) =
      vfMidActiveThreeBoundaryMass R := by
  unfold vfMidActiveThreeBoundaryMass
  apply Finset.sum_congr rfl
  intro p hpMem
  have hp : p.Prime := (mem_primesUpTo.mp hpMem).1
  apply Finset.sum_congr rfl
  intro sig _hsig
  rw [vfMidActiveCellGram_eq_scaledReturnedClippedCellMass hR hp,
    vfMidActiveScaledReturnedClippedCellMass_eq_threeBoundarySectors hp]

/-- The complete active first-owner Co/Div cell excess is bounded by twice the
literal three-boundary mass.  This is just the already-green pointwise
`cellExcess ≤ 2 * cellGram` summed over the exact Fubini labels. -/
theorem sum_vfMidActiveWeightedCellExcess_le_two_threeBoundaryMass
    {R : ℕ} (hR : 3 ≤ R) :
    (∑ p ∈ primesUpTo (squareRootEndpoint (R + 1)),
      ∑ sig ∈ lowOwnerFirstOwnerSignatureSet (R + 1) p,
        vfMidActiveWeightedCellExcess R p sig) ≤
      2 * vfMidActiveThreeBoundaryMass R := by
  calc
    (∑ p ∈ primesUpTo (squareRootEndpoint (R + 1)),
      ∑ sig ∈ lowOwnerFirstOwnerSignatureSet (R + 1) p,
        vfMidActiveWeightedCellExcess R p sig) ≤
      ∑ p ∈ primesUpTo (squareRootEndpoint (R + 1)),
        ∑ sig ∈ lowOwnerFirstOwnerSignatureSet (R + 1) p,
          2 * lowOwnerFirstOwnerCellGramWith
            (R + 1) p sig (vfMidOneBlockActivePhysicalSite R) := by
      apply Finset.sum_le_sum
      intro p hpMem
      have hp : p.Prime := (mem_primesUpTo.mp hpMem).1
      apply Finset.sum_le_sum
      intro sig _hsig
      exact vfMidActiveWeightedCellExcess_le_two_cellGram hR hp
    _ = 2 *
        (∑ p ∈ primesUpTo (squareRootEndpoint (R + 1)),
          ∑ sig ∈ lowOwnerFirstOwnerSignatureSet (R + 1) p,
            lowOwnerFirstOwnerCellGramWith
              (R + 1) p sig (vfMidOneBlockActivePhysicalSite R)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _hp
      rw [Finset.mul_sum]
    _ = 2 * vfMidActiveThreeBoundaryMass R := by
      rw [sum_vfMidActiveCellGram_eq_threeBoundaryMass hR]

/-- **Final exact reduction before the arithmetic inequality.**

The full anchored Co/Div excess is at most the quarantined global residual plus
twice the three surviving retained-weight boundary sectors. -/
theorem vfMidFirstBadAnchoredCoDivExcess_le_activeResidual_add_threeBoundary
    {R : ℕ} (hR : 3 ≤ R) :
    vfMidFirstBadAnchoredCoDivExcess R ≤
      vfMidActiveGlobalResidualExcess R +
        2 * vfMidActiveThreeBoundaryMass R := by
  rw [vfMidFirstBadAnchoredCoDivExcess_eq_activeResidual_add_weightedCells hR]
  exact add_le_add_left
    (sum_vfMidActiveWeightedCellExcess_le_two_threeBoundaryMass hR)
    (vfMidActiveGlobalResidualExcess R)

/-- The single remaining arithmetic budget after all source/support/Fubini
routing has been compiled. -/
def VFMidFirstBadThreeBoundaryBudgetStatement : Prop :=
  ∀ {R : ℕ}, 8 ≤ R →
    VFMidActualPrimeFirstBadAt (2 : ℝ) (R + 1) →
      vfMidActiveGlobalResidualExcess R +
        2 * vfMidActiveThreeBoundaryMass R ≤ 0

/-- The three-boundary budget immediately gives the desired nonpositive full
anchored excess. -/
theorem vfMidActualPrimeFirstBadAt_two_succ_activeExcess_nonpos_of_threeBoundaryBudget
    (hbudget : VFMidFirstBadThreeBoundaryBudgetStatement)
    {R : ℕ} (hR : 8 ≤ R)
    (hfirst : VFMidActualPrimeFirstBadAt (2 : ℝ) (R + 1)) :
    vfMidFirstBadAnchoredCoDivExcess R ≤ 0 := by
  exact
    (vfMidFirstBadAnchoredCoDivExcess_le_activeResidual_add_threeBoundary
      (by omega : 3 ≤ R)).trans
      (hbudget hR hfirst)

/-- The budget is already in the exact historical-source inlet currency. -/
theorem vfMidFirstBadSourceToSectorSixInlet_of_threeBoundaryBudget
    (hbudget : VFMidFirstBadThreeBoundaryBudgetStatement) :
    VFMidFirstBadSourceToSectorSixInletStatement := by
  intro R hR hfirst
  have hcodiv :=
    vfMidActualPrimeFirstBadAt_two_succ_activeExcess_nonpos_of_threeBoundaryBudget
      hbudget hR hfirst
  rw [vfMidFirstBadAnchoredCoDivExcess_eq_decompressedHistoricalSource hR]
    at hcodiv
  linarith

/-- Once the three-boundary budget is discharged, the already-compiled
normalized half consumer contradicts the already-compiled first-bad strict
greater-than-half theorem. -/
theorem vfMidActualPrimeFirstBadAt_two_succ_closed_of_threeBoundaryBudget
    (hbudget : VFMidFirstBadThreeBoundaryBudgetStatement)
    {R : ℕ} (hR : 8 ≤ R)
    (hfirst : VFMidActualPrimeFirstBadAt (2 : ℝ) (R + 1)) :
    False := by
  have hle :=
    vfMidFirstBadNNSNormalizedCovariance_le_half_of_sourceToSectorSixInlet
      (vfMidFirstBadSourceToSectorSixInlet_of_threeBoundaryBudget hbudget)
      hR hfirst
  have hgt :=
    vfMidActualPrimeFirstBadAt_two_succ_nnsNormalized_gt_half hR hfirst
  linarith

end RHLean.Analysis
