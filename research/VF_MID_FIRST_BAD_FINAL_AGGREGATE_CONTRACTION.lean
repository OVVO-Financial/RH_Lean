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


/-! ## Start the actual budget calc block: exact algebraic normal form -/

/-- The active signed source square is exactly its physical diagonal plus twice
the three surviving boundary mass.  This is the #914 support/Fubini result
written in the scalar currency needed by the final budget algebra. -/
theorem vfMidActiveSourceSq_eq_diagonal_add_two_threeBoundary
    {R : ℕ} (hR : 3 ≤ R) :
    (vfMidOneBlockPrimeSeatCharge R +
        vfMidOneBlockProcessedSquarefreeCharge R) ^ 2 =
      vfMidActivePhysicalDiagonalMass R +
        2 * vfMidActiveThreeBoundaryMass R := by
  have hfubini :=
    vfMidWeightedSiteSquare_eq_diagonal_add_firstOwnerCells
      (R + 1) (vfMidOneBlockActivePhysicalSite R)
  rw [vfMidOneBlockActivePhysicalSite_sum_eq_activeSource] at hfubini
  have htwo :
      (∑ p ∈ primesUpTo (squareRootEndpoint (R + 1)),
        ∑ sig ∈ lowOwnerFirstOwnerSignatureSet (R + 1) p,
          2 * lowOwnerFirstOwnerCellGramWith
            (R + 1) p sig (vfMidOneBlockActivePhysicalSite R)) =
        2 * (∑ p ∈ primesUpTo (squareRootEndpoint (R + 1)),
          ∑ sig ∈ lowOwnerFirstOwnerSignatureSet (R + 1) p,
            lowOwnerFirstOwnerCellGramWith
              (R + 1) p sig (vfMidOneBlockActivePhysicalSite R)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _hp
    rw [Finset.mul_sum]
  rw [htwo, sum_vfMidActiveCellGram_eq_threeBoundaryMass hR] at hfubini
  unfold vfMidActivePhysicalDiagonalMass
  exact hfubini

/-- **Exact left-hand side of the real three-boundary budget.**

This is not conditional plumbing.  It expands the quantity that still must be
proved nonpositive and removes the cell/Fubini layer completely.  The only
remaining objects are the prior endpoint defect, the active signed/absolute
one-block masses, the squareful restoring charge, the omitted-seat mass, and
the next endpoint defect. -/
theorem vfMidFirstBadThreeBoundaryBudgetLHS_eq_physicalNormalForm
    {R : ℕ} (hR : 3 ≤ R) :
    vfMidActiveGlobalResidualExcess R +
        2 * vfMidActiveThreeBoundaryMass R =
      vfMidActualPrimeEndpointDefect R ^ 2 -
        4 * vfMidActualPrimeEndpointDefect R *
          (vfMidOneBlockPrimeSeatCharge R +
            vfMidOneBlockProcessedSquarefreeCharge R) +
        (vfMidOneBlockPrimeSeatCharge R +
          vfMidOneBlockProcessedSquarefreeCharge R) ^ 2 -
        2 * vfMidOneBlockProcessedSquarefulCharge R *
          (2 * vfMidActualPrimeEndpointDefect (R + 1) +
            vfMidOneBlockProcessedSquarefulCharge R) -
        2 * |vfMidActualPrimeEndpointDefect R| *
          vfMidOneBlockUpperActiveAbsMass R -
        vfMidWeightedOmittedSeatAbsMass R *
          (2 * (|vfMidActualPrimeEndpointDefect R| +
            vfMidOneBlockUpperActiveAbsMass R) +
            vfMidWeightedOmittedSeatAbsMass R) := by
  have hsquare :=
    vfMidActiveSourceSq_eq_diagonal_add_two_threeBoundary hR
  unfold vfMidActiveGlobalResidualExcess
    vfMidActiveDemandResidual vfMidActiveCapacityResidual
    vfMidActiveIdentityAnchorGate
  nlinarith only [hsquare]

/-- Same exact budget normal form with the omitted-seat mass replaced by the
literal squareful processed charge.  This is the form on which the endpoint
sign cooling lemmas and the first-bad prior-good descendant estimates must now
be applied term by term. -/
theorem vfMidFirstBadThreeBoundaryBudgetLHS_eq_squarefulNormalForm
    {R : ℕ} (hR : 3 ≤ R) :
    vfMidActiveGlobalResidualExcess R +
        2 * vfMidActiveThreeBoundaryMass R =
      vfMidActualPrimeEndpointDefect R ^ 2 -
        4 * vfMidActualPrimeEndpointDefect R *
          (vfMidOneBlockPrimeSeatCharge R +
            vfMidOneBlockProcessedSquarefreeCharge R) +
        (vfMidOneBlockPrimeSeatCharge R +
          vfMidOneBlockProcessedSquarefreeCharge R) ^ 2 -
        2 * vfMidOneBlockProcessedSquarefulCharge R *
          (2 * vfMidActualPrimeEndpointDefect (R + 1) +
            vfMidOneBlockProcessedSquarefulCharge R) -
        2 * |vfMidActualPrimeEndpointDefect R| *
          vfMidOneBlockUpperActiveAbsMass R -
        vfMidOneBlockProcessedSquarefulCharge R *
          (2 * (|vfMidActualPrimeEndpointDefect R| +
            vfMidOneBlockUpperActiveAbsMass R) +
            vfMidOneBlockProcessedSquarefulCharge R) := by
  rw [vfMidFirstBadThreeBoundaryBudgetLHS_eq_physicalNormalForm hR,
    vfMidWeightedOmittedSeatAbsMass_eq_squarefulCharge hR]


/-! ## Production correction: retain the literal Co/Div heat sink

The 317/1027 ledgers show that the sufficient bound
`cellExcess ≤ 2 * signedBoundaryMass` throws away exactly the negative
prime/composite cross terms which provide the needed cooling.  The production
route therefore carries the pointwise quantity

  4 z - 2 |z|

itself through the already-compiled returned/raw-parent Fubini.
-/

/-- One literal zero-target Co-minus-three-Div point excess. -/
def vfMidPointwiseCoDivExcess (z : ℝ) : ℝ :=
  4 * z - 2 * |z|

/-- Exact dissipation when an owner step reverses the signed pair weight. -/
theorem vfMidPointwiseCoDivExcess_add_neg (z : ℝ) :
    vfMidPointwiseCoDivExcess z +
      vfMidPointwiseCoDivExcess (-z) =
        -4 * |z| := by
  unfold vfMidPointwiseCoDivExcess
  rw [abs_neg]
  ring

theorem vfMidPointwiseCoDivExcess_add_neg_nonpos (z : ℝ) :
    vfMidPointwiseCoDivExcess z +
      vfMidPointwiseCoDivExcess (-z) ≤ 0 := by
  rw [vfMidPointwiseCoDivExcess_add_neg]
  have hz : 0 ≤ |z| := abs_nonneg z
  nlinarith

/-- Exact finite-orbit heat identity.  Once a signed packet has been paired
with its owner-reversed mate before any norm is taken, the complete orbit
contributes the literal negative heat `-4 * sum |z|`. -/
theorem sum_vfMidPointwiseCoDivExcess_add_neg
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (z : ι → ℝ) :
    (∑ i ∈ s,
      (vfMidPointwiseCoDivExcess (z i) +
        vfMidPointwiseCoDivExcess (-(z i)))) =
      -4 * ∑ i ∈ s, |z i| := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  exact vfMidPointwiseCoDivExcess_add_neg (z i)

/-- The already-compiled greatest-owner retained sign reversal is exactly a
Co/Div heat sink when the same retained scalar is kept on the stripped parent.
This is the local algebra required by the production owner-orbit pairing; no
absolute-value majorant or reciprocal estimate is used. -/
theorem descendingGreatestOwner_retained_pointwiseCoDivExcess_pair_eq_heat
    {R p m n : ℕ} (hp : p.Prime)
    (hcross : (m, n) ∈ lowOwnerRevealedCrossPairCarrier R
      (lowOwnerRevealedPrimesAbove R p) p)
    (coefficient : ℝ) :
    let um := squarefreePrimeFamilyParent p m
    let un := squarefreePrimeFamilyParent p n
    vfMidPointwiseCoDivExcess
        (coefficient ^ 2 * postRootZeroTargetPairExcess (m, n)) +
      vfMidPointwiseCoDivExcess
        (coefficient ^ 2 * postRootZeroTargetPairExcess (um, un)) =
      -4 *
        |coefficient ^ 2 * postRootZeroTargetPairExcess (m, n)| := by
  have hflip :=
    descendingGreatestOwner_retained_zeroTargetExcess_flip
      hp hcross coefficient
  dsimp only at hflip ⊢
  rw [hflip, abs_neg]
  simpa only [add_comm] using
    (vfMidPointwiseCoDivExcess_add_neg
      (coefficient ^ 2 *
        postRootZeroTargetPairExcess
          (squarefreePrimeFamilyParent p m,
            squarefreePrimeFamilyParent p n)))

/-- In particular, every legally retained owner-reversal pair is
nonpositive in the exact Co/Div currency. -/
theorem descendingGreatestOwner_retained_pointwiseCoDivExcess_pair_nonpos
    {R p m n : ℕ} (hp : p.Prime)
    (hcross : (m, n) ∈ lowOwnerRevealedCrossPairCarrier R
      (lowOwnerRevealedPrimesAbove R p) p)
    (coefficient : ℝ) :
    let um := squarefreePrimeFamilyParent p m
    let un := squarefreePrimeFamilyParent p n
    vfMidPointwiseCoDivExcess
        (coefficient ^ 2 * postRootZeroTargetPairExcess (m, n)) +
      vfMidPointwiseCoDivExcess
        (coefficient ^ 2 * postRootZeroTargetPairExcess (um, un)) ≤ 0 := by
  dsimp only
  rw [descendingGreatestOwner_retained_pointwiseCoDivExcess_pair_eq_heat
    hp hcross coefficient]
  have hnonneg :
      0 ≤
        |coefficient ^ 2 * postRootZeroTargetPairExcess (m, n)| :=
    abs_nonneg _
  nlinarith

/-- The literal returned-pair Co/Div excess.  Outside the #913 returned
carrier the signed weight is already zero, so this also zero-extends
automatically to the whole off-diagonal base square. -/
def vfMidActiveReturnedPairCoDivExcess
    (R p : ℕ) (sig : Finset ℕ) (ab : ℕ × ℕ) : ℝ :=
  vfMidPointwiseCoDivExcess
    (vfMidActiveReturnedPairWeight R p sig ab)

/-- On the physical returned carrier, #913's retained-weight atom is exactly
the original active physical pair product. -/
theorem vfMidActiveReturnedPairWeight_eq_physical
    {R p a c : ℕ} {sig : Finset ℕ}
    (hR : 3 ≤ R) (hp : p.Prime)
    (haClip : a ∈ lowOwnerFirstOwnerClippedBaseFiber (R + 1) p sig)
    (hcAdm : c ∈ lowOwnerFirstOwnerAdmittedBaseFiber (R + 1) p sig) :
    vfMidActiveReturnedPairWeight R p sig (a, c) =
      vfMidOneBlockActivePhysicalSite R a *
        vfMidOneBlockActivePhysicalSite R (p * c) := by
  have haBase :
      a ∈ lowOwnerFirstOwnerBaseFiber (R + 1) p sig :=
    (Finset.mem_filter.mp haClip).1
  have hbChild :
      p * c ∈ lowOwnerFirstOwnerChildFiber (R + 1) p sig :=
    lowOwnerFirstOwner_mul_mem_child_of_admitted hp hcAdm
  have hphys :=
    vfMidActivePhysicalPair_eq_scaledDirichletPolarizationAtom
      hR hp haBase hbChild
  have hdiv : (p * c) / p = c := by
    simpa [Nat.mul_comm] using Nat.mul_div_left c hp.pos
  rw [hdiv] at hphys
  have hmem :
      (a, c) ∈ vfMidActiveReturnedPairCarrier R p sig := by
    exact Finset.mem_product.mpr ⟨haClip, hcAdm⟩
  unfold vfMidActiveReturnedPairWeight
  rw [if_pos hmem]
  exact hphys.symm

/-- Exact child-to-returned-parent reindexing for the full pointwise Co/Div
excess, not merely for its signed part. -/
theorem vfMidActiveWeightedCellExcess_eq_returnedCoDivExcess
    {R p : ℕ} {sig : Finset ℕ}
    (hR : 3 ≤ R) (hp : p.Prime) :
    vfMidActiveWeightedCellExcess R p sig =
      ∑ ac ∈ vfMidActiveReturnedPairCarrier R p sig,
        vfMidActiveReturnedPairCoDivExcess R p sig ac := by
  rw [vfMidActiveWeightedCellExcess_eq_clippedPhysical hR hp]
  unfold vfMidActiveClippedPhysicalCellExcess
    vfMidActiveReturnedPairCarrier
  rw [Finset.product_eq_sprod, Finset.sum_product,
    Finset.product_eq_sprod, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro a haClip
  refine Finset.sum_bij
    (fun b _hb => b / p)
    (fun b hb => lowOwnerFirstOwner_div_mem_admitted_of_child hp hb)
    ?_ ?_ ?_
  · intro b hb d hd heq
    have hbDvd := (Finset.mem_filter.mp hb).2.2
    have hdDvd := (Finset.mem_filter.mp hd).2.2
    change b / p = d / p at heq
    calc
      b = p * (b / p) := (Nat.mul_div_cancel' hbDvd).symm
      _ = p * (d / p) := by rw [heq]
      _ = d := Nat.mul_div_cancel' hdDvd
  · intro d hd
    refine ⟨p * d, lowOwnerFirstOwner_mul_mem_child_of_admitted hp hd, ?_⟩
    change (p * d) / p = d
    simpa [Nat.mul_comm] using Nat.mul_div_left d hp.pos
  · intro b hb
    have hcAdm :=
      lowOwnerFirstOwner_div_mem_admitted_of_child hp hb
    have hcancel : p * (b / p) = b :=
      Nat.mul_div_cancel' (Finset.mem_filter.mp hb).2.2
    unfold vfMidActiveReturnedPairCoDivExcess
      vfMidPointwiseCoDivExcess
    rw [vfMidActiveReturnedPairWeight_eq_physical
      hR hp haClip hcAdm, hcancel]

/-- Zero extension of the literal Co/Div excess to the full off-diagonal base
carrier. -/
theorem vfMidActiveWeightedCellExcess_eq_offDiagonalReturnedCoDiv
    {R p : ℕ} {sig : Finset ℕ}
    (hR : 3 ≤ R) (hp : p.Prime) :
    vfMidActiveWeightedCellExcess R p sig =
      ∑ ab ∈ lowOwnerFirstOwnerBaseOffDiagonalPairCarrier (R + 1) p sig,
        vfMidActiveReturnedPairCoDivExcess R p sig ab := by
  rw [vfMidActiveWeightedCellExcess_eq_returnedCoDivExcess hR hp]
  have hsub :=
    vfMidActiveReturnedPairCarrier_subset_offDiagonal R p sig
  apply Finset.sum_subset hsub
  intro ab _hab hnot
  have hw :
      vfMidActiveReturnedPairWeight R p sig ab = 0 := by
    simp [vfMidActiveReturnedPairWeight, hnot]
  simp [vfMidActiveReturnedPairCoDivExcess,
    vfMidPointwiseCoDivExcess, hw]

/-- Exact greatest-owner Fubini of the literal active Co/Div excess. -/
theorem vfMidActiveWeightedCellExcess_eq_ownerFibers
    {R p : ℕ} {sig : Finset ℕ}
    (hR : 3 ≤ R) (hp : p.Prime) :
    vfMidActiveWeightedCellExcess R p sig =
      ∑ r ∈ lowOwnerRevealedPrimesAbove (R + 1) p,
        ∑ ab ∈
          lowOwnerFirstOwnerPolarizationGreatestOwnerPairFiber
            (R + 1) p sig r,
          vfMidActiveReturnedPairCoDivExcess R p sig ab := by
  rw [vfMidActiveWeightedCellExcess_eq_offDiagonalReturnedCoDiv hR hp]
  exact
    sum_lowOwnerFirstOwnerBaseOffDiagonal_eq_sum_polarizationOwnerFibers
      hp (vfMidActiveReturnedPairCoDivExcess R p sig)

/-- Literal Co/Div excess assigned to one orientation-preserving raw parent. -/
def vfMidActiveReturnedRawParentFiberExcess
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ)
    (parent : ℕ × ℕ) : ℝ :=
  ∑ ab ∈
      lowOwnerFirstOwnerPolarizationFixedRawParentFiber
        (R + 1) p sig r parent,
    vfMidActiveReturnedPairCoDivExcess R p sig ab

/-- Exact raw-parent reindex of the literal active Co/Div excess. -/
theorem vfMidActiveWeightedCellExcess_eq_rawParents
    {R p : ℕ} {sig : Finset ℕ}
    (hR : 3 ≤ R) (hp : p.Prime) :
    vfMidActiveWeightedCellExcess R p sig =
      ∑ r ∈ lowOwnerRevealedPrimesAbove (R + 1) p,
        ∑ parent ∈
          lowOwnerFirstOwnerPolarizationRawParentSet (R + 1) p sig r,
          vfMidActiveReturnedRawParentFiberExcess R p sig r parent := by
  rw [vfMidActiveWeightedCellExcess_eq_ownerFibers hR hp]
  apply Finset.sum_congr rfl
  intro r _hr
  rw [sum_lowOwnerFirstOwnerPolarizationGreatestOwnerPairFiber_eq_rawParents]
  rfl

private theorem vfMidActiveReturnedPairCoDivExcess_eq_zero_of_weight_zero
    {R p : ℕ} {sig : Finset ℕ} {ab : ℕ × ℕ}
    (hzero : vfMidActiveReturnedPairWeight R p sig ab = 0) :
    vfMidActiveReturnedPairCoDivExcess R p sig ab = 0 := by
  simp [vfMidActiveReturnedPairCoDivExcess,
    vfMidPointwiseCoDivExcess, hzero]

/-- Completed raw parents also carry zero literal Co/Div excess, not merely
zero signed mass. -/
theorem vfMidActiveReturnedRawParentFiberExcess_eq_zero_of_completed
    {R p r : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (hcompleted :
      parent ∈ lowOwnerFirstOwnerCompletedPolarizationRawParentSet
        (R + 1) p sig r) :
    vfMidActiveReturnedRawParentFiberExcess R p sig r parent = 0 := by
  unfold vfMidActiveReturnedRawParentFiberExcess
  apply Finset.sum_eq_zero
  intro child hchild
  rcases
      lowOwnerFirstOwnerPolarizationFixedRawParentFiber_child_mixed hchild with
    hleft | hright
  · rw [hleft]
    apply vfMidActiveReturnedPairCoDivExcess_eq_zero_of_weight_zero
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
    apply vfMidActiveReturnedPairCoDivExcess_eq_zero_of_weight_zero
    exact
      vfMidActiveReturnedPairWeight_secondMixed_eq_zero_of_completed
        hcompleted

/-- The full literal cell excess lives only on incomplete raw parents. -/
theorem vfMidActiveWeightedCellExcess_eq_incompleteRawParents
    {R p : ℕ} {sig : Finset ℕ}
    (hR : 3 ≤ R) (hp : p.Prime) :
    vfMidActiveWeightedCellExcess R p sig =
      ∑ r ∈ lowOwnerRevealedPrimesAbove (R + 1) p,
        ∑ parent ∈
          lowOwnerFirstOwnerIncompletePolarizationRawParentSet
            (R + 1) p sig r,
          vfMidActiveReturnedRawParentFiberExcess R p sig r parent := by
  rw [vfMidActiveWeightedCellExcess_eq_rawParents hR hp]
  apply Finset.sum_congr rfl
  intro r _hr
  have hsplit :=
    sum_vfMidRawParents_eq_completed_add_incomplete
      (R + 1) p sig r
      (vfMidActiveReturnedRawParentFiberExcess R p sig r)
  rw [hsplit]
  have hzero :
      (∑ parent ∈
        lowOwnerFirstOwnerCompletedPolarizationRawParentSet
          (R + 1) p sig r,
        vfMidActiveReturnedRawParentFiberExcess R p sig r parent) = 0 := by
    apply Finset.sum_eq_zero
    intro parent hparent
    exact
      vfMidActiveReturnedRawParentFiberExcess_eq_zero_of_completed hparent
  rw [hzero, zero_add]

/-- Six-sector split of the literal Co/Div excess. -/
theorem sum_vfMidActiveReturnedIncompleteExcess_eq_sixOrientedSectors
    {R p r : ℕ} {sig : Finset ℕ} (hp : p.Prime) :
    (∑ parent ∈
      lowOwnerFirstOwnerIncompletePolarizationRawParentSet
        (R + 1) p sig r,
      vfMidActiveReturnedRawParentFiberExcess R p sig r parent) =
      (∑ parent ∈
        lowOwnerFirstOwnerIncompleteFirstClipLeftSet
          (R + 1) p sig r,
        vfMidActiveReturnedRawParentFiberExcess R p sig r parent) +
      (∑ parent ∈
        lowOwnerFirstOwnerIncompleteFirstClipRightSet
          (R + 1) p sig r,
        vfMidActiveReturnedRawParentFiberExcess R p sig r parent) +
      (∑ parent ∈
        lowOwnerFirstOwnerIncompleteNextClipLeftSet
          (R + 1) p sig r,
        vfMidActiveReturnedRawParentFiberExcess R p sig r parent) +
      (∑ parent ∈
        lowOwnerFirstOwnerIncompleteNextClipRightSet
          (R + 1) p sig r,
        vfMidActiveReturnedRawParentFiberExcess R p sig r parent) +
      (∑ parent ∈
        lowOwnerFirstOwnerIncompleteReturnedClipLeftSet
          (R + 1) p sig r,
        vfMidActiveReturnedRawParentFiberExcess R p sig r parent) +
      ∑ parent ∈
        lowOwnerFirstOwnerIncompleteReturnedClipRightSet
          (R + 1) p sig r,
        vfMidActiveReturnedRawParentFiberExcess R p sig r parent := by
  exact
    sum_lowOwnerFirstOwnerIncompleteRawParents_eq_sixOrientedSectors
      (R := R + 1) (p := p) (r := r) (sig := sig) hp
      (vfMidActiveReturnedRawParentFiberExcess R p sig r)

/-- A first-right sector has zero literal Co/Div excess because every one of
its returned-pair weights is zero. -/
theorem vfMidActiveReturnedRawParentFiberExcess_eq_zero_of_firstClipRight
    {R p r : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (hparent :
      parent ∈ lowOwnerFirstOwnerIncompleteFirstClipRightSet
        (R + 1) p sig r) :
    vfMidActiveReturnedRawParentFiberExcess R p sig r parent = 0 := by
  unfold vfMidActiveReturnedRawParentFiberExcess
  apply Finset.sum_eq_zero
  intro child hchild
  apply vfMidActiveReturnedPairCoDivExcess_eq_zero_of_weight_zero
  rcases
      lowOwnerFirstOwnerPolarizationFixedRawParentFiber_child_mixed hchild with
    hleft | hrightMixed
  · rw [hleft]
    have hright :
        squareRootEndpoint (R + 1) < p * parent.2 :=
      lowOwnerFirstOwnerIncompleteFirstClipRight_mem_implies_rightClip hparent
    have hnot :
        (r * parent.1, parent.2) ∉
          vfMidActiveReturnedPairCarrier R p sig := by
      intro hmem
      have hadm :
          parent.2 ∈ lowOwnerFirstOwnerAdmittedBaseFiber (R + 1) p sig :=
        (Finset.mem_product.mp hmem).2
      have hle :
          p * parent.2 ≤ squareRootEndpoint (R + 1) :=
        (Finset.mem_filter.mp hadm).2
      omega
    simp [vfMidActiveReturnedPairWeight, hnot]
  · rw [hrightMixed]
    have hnotLeft :
        ¬ squareRootEndpoint (R + 1) < p * parent.1 :=
      (Finset.mem_filter.mp hparent).2
    have hnot :
        (parent.1, r * parent.2) ∉
          vfMidActiveReturnedPairCarrier R p sig := by
      intro hmem
      have hclip :
          parent.1 ∈ lowOwnerFirstOwnerClippedBaseFiber (R + 1) p sig :=
        (Finset.mem_product.mp hmem).1
      exact hnotLeft (Finset.mem_filter.mp hclip).2
    simp [vfMidActiveReturnedPairWeight, hnot]

/-- A next-left sector has zero literal Co/Div excess. -/
theorem vfMidActiveReturnedRawParentFiberExcess_eq_zero_of_nextClipLeft
    {R p r : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (hparent :
      parent ∈ lowOwnerFirstOwnerIncompleteNextClipLeftSet
        (R + 1) p sig r) :
    vfMidActiveReturnedRawParentFiberExcess R p sig r parent = 0 := by
  unfold vfMidActiveReturnedRawParentFiberExcess
  apply Finset.sum_eq_zero
  intro child hchild
  apply vfMidActiveReturnedPairCoDivExcess_eq_zero_of_weight_zero
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
  · rw [hleftMixed]
    have hgreatest :
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
    have hnot :
        (parent.1, r * parent.2) ∉
          vfMidActiveReturnedPairCarrier R p sig := by
      intro hmem
      have hclip :
          parent.1 ∈ lowOwnerFirstOwnerClippedBaseFiber (R + 1) p sig :=
        (Finset.mem_product.mp hmem).1
      have hgt :
          squareRootEndpoint (R + 1) < p * parent.1 :=
        (Finset.mem_filter.mp hclip).2
      exact (Nat.not_lt_of_ge hclass.1) hgt
    simp [vfMidActiveReturnedPairWeight, hnot]

/-- A returned-right sector has zero literal Co/Div excess. -/
theorem vfMidActiveReturnedRawParentFiberExcess_eq_zero_of_returnedClipRight
    {R p r : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (hparent :
      parent ∈ lowOwnerFirstOwnerIncompleteReturnedClipRightSet
        (R + 1) p sig r) :
    vfMidActiveReturnedRawParentFiberExcess R p sig r parent = 0 := by
  unfold vfMidActiveReturnedRawParentFiberExcess
  apply Finset.sum_eq_zero
  intro child hchild
  apply vfMidActiveReturnedPairCoDivExcess_eq_zero_of_weight_zero
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
    have hnot :
        (r * parent.1, parent.2) ∉
          vfMidActiveReturnedPairCarrier R p sig := by
      intro hmem
      have hclip :
          r * parent.1 ∈
            lowOwnerFirstOwnerClippedBaseFiber (R + 1) p sig :=
        (Finset.mem_product.mp hmem).1
      exact hnotLeft (Finset.mem_filter.mp hclip).2
    simp [vfMidActiveReturnedPairWeight, hnot]
  · rw [hrightMixed]
    have hnot :
        (parent.1, r * parent.2) ∉
          vfMidActiveReturnedPairCarrier R p sig := by
      intro hmem
      have hclip :
          parent.1 ∈ lowOwnerFirstOwnerClippedBaseFiber (R + 1) p sig :=
        (Finset.mem_product.mp hmem).1
      have hgt :
          squareRootEndpoint (R + 1) < p * parent.1 :=
        (Finset.mem_filter.mp hclip).2
      exact (Nat.not_lt_of_ge hclass.1) hgt
    simp [vfMidActiveReturnedPairWeight, hnot]

/-- The exact literal Co/Div excess occupies only first-left, next-right, and
returned-left, with all negative pair heat retained. -/
theorem vfMidActiveWeightedCellExcess_eq_threeBoundaryExcess
    {R p : ℕ} {sig : Finset ℕ}
    (hR : 3 ≤ R) (hp : p.Prime) :
    vfMidActiveWeightedCellExcess R p sig =
      ∑ r ∈ lowOwnerRevealedPrimesAbove (R + 1) p,
        ((∑ parent ∈
            lowOwnerFirstOwnerIncompleteFirstClipLeftSet
              (R + 1) p sig r,
            vfMidActiveReturnedRawParentFiberExcess R p sig r parent) +
          (∑ parent ∈
            lowOwnerFirstOwnerIncompleteNextClipRightSet
              (R + 1) p sig r,
            vfMidActiveReturnedRawParentFiberExcess R p sig r parent) +
          ∑ parent ∈
            lowOwnerFirstOwnerIncompleteReturnedClipLeftSet
              (R + 1) p sig r,
            vfMidActiveReturnedRawParentFiberExcess R p sig r parent) := by
  rw [vfMidActiveWeightedCellExcess_eq_incompleteRawParents hR hp]
  apply Finset.sum_congr rfl
  intro r _hr
  rw [sum_vfMidActiveReturnedIncompleteExcess_eq_sixOrientedSectors hp]
  have hfr :
      (∑ parent ∈
        lowOwnerFirstOwnerIncompleteFirstClipRightSet
          (R + 1) p sig r,
        vfMidActiveReturnedRawParentFiberExcess R p sig r parent) = 0 := by
    apply Finset.sum_eq_zero
    intro parent hparent
    exact
      vfMidActiveReturnedRawParentFiberExcess_eq_zero_of_firstClipRight hparent
  have hnl :
      (∑ parent ∈
        lowOwnerFirstOwnerIncompleteNextClipLeftSet
          (R + 1) p sig r,
        vfMidActiveReturnedRawParentFiberExcess R p sig r parent) = 0 := by
    apply Finset.sum_eq_zero
    intro parent hparent
    exact
      vfMidActiveReturnedRawParentFiberExcess_eq_zero_of_nextClipLeft hparent
  have hrr :
      (∑ parent ∈
        lowOwnerFirstOwnerIncompleteReturnedClipRightSet
          (R + 1) p sig r,
        vfMidActiveReturnedRawParentFiberExcess R p sig r parent) = 0 := by
    apply Finset.sum_eq_zero
    intro parent hparent
    exact
      vfMidActiveReturnedRawParentFiberExcess_eq_zero_of_returnedClipRight hparent
  rw [hfr, hnl, hrr]
  ring

/-- Global literal three-boundary Co/Div excess.  Unlike
`vfMidActiveThreeBoundaryMass`, this retains every negative physical pair
contribution. -/
def vfMidActiveThreeBoundaryExcess (R : ℕ) : ℝ :=
  ∑ p ∈ primesUpTo (squareRootEndpoint (R + 1)),
    ∑ sig ∈ lowOwnerFirstOwnerSignatureSet (R + 1) p,
      ∑ r ∈ lowOwnerRevealedPrimesAbove (R + 1) p,
        ((∑ parent ∈
            lowOwnerFirstOwnerIncompleteFirstClipLeftSet
              (R + 1) p sig r,
            vfMidActiveReturnedRawParentFiberExcess R p sig r parent) +
          (∑ parent ∈
            lowOwnerFirstOwnerIncompleteNextClipRightSet
              (R + 1) p sig r,
            vfMidActiveReturnedRawParentFiberExcess R p sig r parent) +
          ∑ parent ∈
            lowOwnerFirstOwnerIncompleteReturnedClipLeftSet
              (R + 1) p sig r,
            vfMidActiveReturnedRawParentFiberExcess R p sig r parent)

/-- Global exact Fubini for the active Co/Div cell excess. -/
theorem sum_vfMidActiveWeightedCellExcess_eq_threeBoundaryExcess
    {R : ℕ} (hR : 3 ≤ R) :
    (∑ p ∈ primesUpTo (squareRootEndpoint (R + 1)),
      ∑ sig ∈ lowOwnerFirstOwnerSignatureSet (R + 1) p,
        vfMidActiveWeightedCellExcess R p sig) =
      vfMidActiveThreeBoundaryExcess R := by
  unfold vfMidActiveThreeBoundaryExcess
  apply Finset.sum_congr rfl
  intro p hpMem
  have hp : p.Prime := (mem_primesUpTo.mp hpMem).1
  apply Finset.sum_congr rfl
  intro sig _hsig
  exact vfMidActiveWeightedCellExcess_eq_threeBoundaryExcess hR hp

/-- **Correct production budget identity.**

No local absolute capacity has been discarded: the full anchored excess is
exactly the quarantined global residual plus the literal three-boundary Co/Div
excess. -/
theorem vfMidFirstBadAnchoredCoDivExcess_eq_activeResidual_add_threeBoundaryExcess
    {R : ℕ} (hR : 3 ≤ R) :
    vfMidFirstBadAnchoredCoDivExcess R =
      vfMidActiveGlobalResidualExcess R +
        vfMidActiveThreeBoundaryExcess R := by
  rw [vfMidFirstBadAnchoredCoDivExcess_eq_activeResidual_add_weightedCells hR,
    sum_vfMidActiveWeightedCellExcess_eq_threeBoundaryExcess hR]

/-- Literal absolute pair mass on one returned raw-parent fibre. -/
def vfMidActiveReturnedRawParentFiberAbsMass
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) (parent : ℕ × ℕ) : ℝ :=
  ∑ child ∈
    lowOwnerFirstOwnerPolarizationFixedRawParentFiber
      (R + 1) p sig r parent,
    |vfMidActiveReturnedPairWeight R p sig child|

/-- Exact local Co/Div normal form: signed mass carries coefficient four and
the literal absolute heat is subtracted with coefficient two. -/
theorem vfMidActiveReturnedRawParentFiberExcess_eq_fourMass_sub_twoAbs
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) (parent : ℕ × ℕ) :
    vfMidActiveReturnedRawParentFiberExcess R p sig r parent =
      4 * vfMidActiveReturnedRawParentFiberMass R p sig r parent -
        2 * vfMidActiveReturnedRawParentFiberAbsMass R p sig r parent := by
  unfold vfMidActiveReturnedRawParentFiberExcess
    vfMidActiveReturnedRawParentFiberMass
    vfMidActiveReturnedRawParentFiberAbsMass
    vfMidActiveReturnedPairCoDivExcess
    vfMidPointwiseCoDivExcess
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]

/-- Absolute heat carried by exactly the three physical boundary sectors which
survive the #914 support classification. -/
def vfMidActiveThreeBoundaryAbsMass (R : ℕ) : ℝ :=
  ∑ p ∈ primesUpTo (squareRootEndpoint (R + 1)),
    ∑ sig ∈ lowOwnerFirstOwnerSignatureSet (R + 1) p,
      ∑ r ∈ lowOwnerRevealedPrimesAbove (R + 1) p,
        ((∑ parent ∈
            lowOwnerFirstOwnerIncompleteFirstClipLeftSet
              (R + 1) p sig r,
            vfMidActiveReturnedRawParentFiberAbsMass R p sig r parent) +
          (∑ parent ∈
            lowOwnerFirstOwnerIncompleteNextClipRightSet
              (R + 1) p sig r,
            vfMidActiveReturnedRawParentFiberAbsMass R p sig r parent) +
          ∑ parent ∈
            lowOwnerFirstOwnerIncompleteReturnedClipLeftSet
              (R + 1) p sig r,
            vfMidActiveReturnedRawParentFiberAbsMass R p sig r parent)

@[simp] theorem vfMidActiveThreeBoundaryAbsMass_nonneg (R : ℕ) :
    0 ≤ vfMidActiveThreeBoundaryAbsMass R := by
  unfold vfMidActiveThreeBoundaryAbsMass
    vfMidActiveReturnedRawParentFiberAbsMass
  positivity

/-- **Exact 317/1027 production normal form.**

The three-boundary Co/Div excess is not a positive boundary majorant.  It is
literally four times the signed physical boundary mass minus twice its retained
absolute heat.  This is the equality the finite 317/1027 ledgers were
diagnosing. -/
private theorem sum_eq_four_mul_sub_two_mul_of_pointwise
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (e m a : ι → ℝ)
    (h : ∀ i ∈ s, e i = 4 * m i - 2 * a i) :
    (∑ i ∈ s, e i) =
      4 * (∑ i ∈ s, m i) - 2 * (∑ i ∈ s, a i) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl h

theorem vfMidActiveThreeBoundaryExcess_eq_fourMass_sub_twoAbs
    (R : ℕ) :
    vfMidActiveThreeBoundaryExcess R =
      4 * vfMidActiveThreeBoundaryMass R -
        2 * vfMidActiveThreeBoundaryAbsMass R := by
  unfold vfMidActiveThreeBoundaryExcess
    vfMidActiveThreeBoundaryMass
    vfMidActiveThreeBoundaryAbsMass
  apply sum_eq_four_mul_sub_two_mul_of_pointwise
  intro p _hp
  apply sum_eq_four_mul_sub_two_mul_of_pointwise
  intro sig _hsig
  apply sum_eq_four_mul_sub_two_mul_of_pointwise
  intro r _hr
  have hfirst :
      (∑ parent ∈
          lowOwnerFirstOwnerIncompleteFirstClipLeftSet
            (R + 1) p sig r,
          vfMidActiveReturnedRawParentFiberExcess R p sig r parent) =
        4 * (∑ parent ∈
          lowOwnerFirstOwnerIncompleteFirstClipLeftSet
            (R + 1) p sig r,
          vfMidActiveReturnedRawParentFiberMass R p sig r parent) -
        2 * (∑ parent ∈
          lowOwnerFirstOwnerIncompleteFirstClipLeftSet
            (R + 1) p sig r,
          vfMidActiveReturnedRawParentFiberAbsMass R p sig r parent) := by
    apply sum_eq_four_mul_sub_two_mul_of_pointwise
    intro parent _hparent
    exact
      vfMidActiveReturnedRawParentFiberExcess_eq_fourMass_sub_twoAbs
        R p sig r parent
  have hnext :
      (∑ parent ∈
          lowOwnerFirstOwnerIncompleteNextClipRightSet
            (R + 1) p sig r,
          vfMidActiveReturnedRawParentFiberExcess R p sig r parent) =
        4 * (∑ parent ∈
          lowOwnerFirstOwnerIncompleteNextClipRightSet
            (R + 1) p sig r,
          vfMidActiveReturnedRawParentFiberMass R p sig r parent) -
        2 * (∑ parent ∈
          lowOwnerFirstOwnerIncompleteNextClipRightSet
            (R + 1) p sig r,
          vfMidActiveReturnedRawParentFiberAbsMass R p sig r parent) := by
    apply sum_eq_four_mul_sub_two_mul_of_pointwise
    intro parent _hparent
    exact
      vfMidActiveReturnedRawParentFiberExcess_eq_fourMass_sub_twoAbs
        R p sig r parent
  have hreturned :
      (∑ parent ∈
          lowOwnerFirstOwnerIncompleteReturnedClipLeftSet
            (R + 1) p sig r,
          vfMidActiveReturnedRawParentFiberExcess R p sig r parent) =
        4 * (∑ parent ∈
          lowOwnerFirstOwnerIncompleteReturnedClipLeftSet
            (R + 1) p sig r,
          vfMidActiveReturnedRawParentFiberMass R p sig r parent) -
        2 * (∑ parent ∈
          lowOwnerFirstOwnerIncompleteReturnedClipLeftSet
            (R + 1) p sig r,
          vfMidActiveReturnedRawParentFiberAbsMass R p sig r parent) := by
    apply sum_eq_four_mul_sub_two_mul_of_pointwise
    intro parent _hparent
    exact
      vfMidActiveReturnedRawParentFiberExcess_eq_fourMass_sub_twoAbs
        R p sig r parent
  rw [hfirst, hnext, hreturned]
  ring

/-- The complete anchored excess in the exact signed-boundary/heat currency.
No boundary absolute value has been introduced around the signed sum. -/
theorem vfMidFirstBadAnchoredCoDivExcess_eq_activeResidual_add_fourBoundary_sub_heat
    {R : ℕ} (hR : 3 ≤ R) :
    vfMidFirstBadAnchoredCoDivExcess R =
      vfMidActiveGlobalResidualExcess R +
        4 * vfMidActiveThreeBoundaryMass R -
        2 * vfMidActiveThreeBoundaryAbsMass R := by
  rw [vfMidFirstBadAnchoredCoDivExcess_eq_activeResidual_add_threeBoundaryExcess hR,
    vfMidActiveThreeBoundaryExcess_eq_fourMass_sub_twoAbs]
  ring

/-- The actual final budget statement.  This supersedes the stronger
`VFMidFirstBadThreeBoundaryBudgetStatement`, which was obtained only after
dropping the negative local Co/Div heat sink. -/
def VFMidFirstBadExactThreeBoundaryExcessBudgetStatement : Prop :=
  ∀ {R : ℕ}, 8 ≤ R →
    VFMidActualPrimeFirstBadAt (2 : ℝ) (R + 1) →
      vfMidActiveGlobalResidualExcess R +
        vfMidActiveThreeBoundaryExcess R ≤ 0

/-- The exact budget closes the anchored Co/Div excess without any intermediate
boundary majorant. -/
theorem vfMidActualPrimeFirstBadAt_two_succ_activeExcess_nonpos_of_exactBudget
    (hbudget : VFMidFirstBadExactThreeBoundaryExcessBudgetStatement)
    {R : ℕ} (hR : 8 ≤ R)
    (hfirst : VFMidActualPrimeFirstBadAt (2 : ℝ) (R + 1)) :
    vfMidFirstBadAnchoredCoDivExcess R ≤ 0 := by
  rw [vfMidFirstBadAnchoredCoDivExcess_eq_activeResidual_add_threeBoundaryExcess
    (by omega : 3 ≤ R)]
  exact hbudget hR hfirst

end RHLean.Analysis
