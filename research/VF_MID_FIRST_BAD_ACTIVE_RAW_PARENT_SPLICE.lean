import Mathlib
import «research.VF_MID_FIRST_BAD_SCALED_CLIPPED_GATE»
import «research.GLOBAL_RETURNED_CORE_POLARIZATION_RAW_PARENT_FUBINI»
import «research.GLOBAL_RETURNED_CORE_RAW_PARENT_COMPLETED_GATE_SPLIT»
import «research.GLOBAL_RETURNED_CORE_RAW_PARENT_BOUNDARY_ORIENTED_FUBINI»
import «research.VF_MID_FIRST_BAD_CORRELATION_DESCENT»

/-!
# First-bad active source: exact raw-parent completed/incomplete splice

This module keeps the #912 active VF coefficients attached before any new
square or norm is introduced.

The returned active source in one first-owner cell lives on
  clipped-base × admitted-returned-parent.
That carrier is a literal subset of the full p-free base off-diagonal square.
We therefore zero-extend the actual VF-weighted Dirichlet polarization atom to
that square, apply the already-compiled unique greatest-owner Fubini, and then
apply the already-compiled raw-parent Fubini.

Only after the exact raw-parent reindex do we split each raw-parent carrier by
the repository's native predicate
  LowOwnerCompletedPolarizationBlock.
The complement is exactly
  lowOwnerFirstOwnerIncompletePolarizationRawParentSet.

No square is distributed across this partition.  This is deliberately a signed
pre-energy splice: (A+B)^2 is not replaced by A^2+B^2.  The completed and
incomplete ledgers retain the literal site-dependent VF coefficient of every
physical child.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Literal returned active pair carrier in one first-owner cell. -/
def vfMidActiveReturnedPairCarrier
    (R p : ℕ) (sig : Finset ℕ) : Finset (ℕ × ℕ) :=
  (lowOwnerFirstOwnerClippedBaseFiber (R + 1) p sig).product
    (lowOwnerFirstOwnerAdmittedBaseFiber (R + 1) p sig)

/-- The exact VF-weighted Dirichlet atom on the returned active carrier,
zero-extended to the whole base square. -/
def vfMidActiveReturnedPairWeight
    (R p : ℕ) (sig : Finset ℕ) (ab : ℕ × ℕ) : ℝ :=
  if ab ∈ vfMidActiveReturnedPairCarrier R p sig then
    (vfMidActiveMobiusScale R ab.1 *
      vfMidActiveMobiusScale R (p * ab.2)) *
      lowOwnerFirstOwnerDirichletPolarizationAtom (R + 1) p ab
  else 0

/-- A clipped/admitted returned pair is necessarily off-diagonal and lies in
the full p-free base square. -/
theorem vfMidActiveReturnedPairCarrier_subset_offDiagonal
    (R p : ℕ) (sig : Finset ℕ) :
    vfMidActiveReturnedPairCarrier R p sig ⊆
      lowOwnerFirstOwnerBaseOffDiagonalPairCarrier (R + 1) p sig := by
  intro ab hab
  rcases Finset.mem_product.mp hab with ⟨haClip, hbAdm⟩
  have haBase :
      ab.1 ∈ lowOwnerFirstOwnerBaseFiber (R + 1) p sig :=
    (Finset.mem_filter.mp haClip).1
  have hbBase :
      ab.2 ∈ lowOwnerFirstOwnerBaseFiber (R + 1) p sig :=
    (Finset.mem_filter.mp hbAdm).1
  have haGt :
      squareRootEndpoint (R + 1) < p * ab.1 :=
    (Finset.mem_filter.mp haClip).2
  have hbLe :
      p * ab.2 ≤ squareRootEndpoint (R + 1) :=
    (Finset.mem_filter.mp hbAdm).2
  apply Finset.mem_filter.mpr
  constructor
  · exact Finset.mem_product.mpr ⟨haBase, hbBase⟩
  · intro habEq
    have : p * ab.1 = p * ab.2 := by rw [habEq]
    omega

/-- The returned clipped-cell mass is the same weighted sum on the full
off-diagonal base carrier after zero extension. -/
theorem vfMidActiveScaledReturnedClippedCellMass_eq_offDiagonal
    (R p : ℕ) (sig : Finset ℕ) :
    vfMidActiveScaledReturnedClippedCellMass R p sig =
      ∑ ab ∈ lowOwnerFirstOwnerBaseOffDiagonalPairCarrier (R + 1) p sig,
        vfMidActiveReturnedPairWeight R p sig ab := by
  have hsub :=
    vfMidActiveReturnedPairCarrier_subset_offDiagonal R p sig
  have hzero :
      ∀ ab ∈ lowOwnerFirstOwnerBaseOffDiagonalPairCarrier (R + 1) p sig,
        ab ∉ vfMidActiveReturnedPairCarrier R p sig →
          vfMidActiveReturnedPairWeight R p sig ab = 0 := by
    intro ab _hab hnot
    simp [vfMidActiveReturnedPairWeight, hnot]
  calc
    vfMidActiveScaledReturnedClippedCellMass R p sig =
        ∑ ab ∈ vfMidActiveReturnedPairCarrier R p sig,
          vfMidActiveReturnedPairWeight R p sig ab := by
      unfold vfMidActiveScaledReturnedClippedCellMass
        vfMidActiveReturnedPairCarrier
      apply Finset.sum_congr rfl
      intro ab hab
      have hmem :
          ab ∈ vfMidActiveReturnedPairCarrier R p sig := by
        simpa only [vfMidActiveReturnedPairCarrier] using hab
      unfold vfMidActiveReturnedPairWeight
      rw [if_pos hmem]
    _ = ∑ ab ∈ lowOwnerFirstOwnerBaseOffDiagonalPairCarrier (R + 1) p sig,
          vfMidActiveReturnedPairWeight R p sig ab :=
      Finset.sum_subset hsub hzero

/-- Exact greatest-owner Fubini of the returned active source, with the VF
weight still attached to each physical pair. -/
theorem vfMidActiveScaledReturnedClippedCellMass_eq_ownerFibers
    {R p : ℕ} {sig : Finset ℕ} (hp : p.Prime) :
    vfMidActiveScaledReturnedClippedCellMass R p sig =
      ∑ r ∈ lowOwnerRevealedPrimesAbove (R + 1) p,
        ∑ ab ∈
          lowOwnerFirstOwnerPolarizationGreatestOwnerPairFiber
            (R + 1) p sig r,
          vfMidActiveReturnedPairWeight R p sig ab := by
  rw [vfMidActiveScaledReturnedClippedCellMass_eq_offDiagonal]
  exact
    sum_lowOwnerFirstOwnerBaseOffDiagonal_eq_sum_polarizationOwnerFibers
      hp (vfMidActiveReturnedPairWeight R p sig)

/-- VF-weighted active mass assigned to one orientation-preserving raw parent. -/
def vfMidActiveReturnedRawParentFiberMass
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ)
    (parent : ℕ × ℕ) : ℝ :=
  ∑ ab ∈
      lowOwnerFirstOwnerPolarizationFixedRawParentFiber
        (R + 1) p sig r parent,
    vfMidActiveReturnedPairWeight R p sig ab

/-- Exact raw-parent reindex of the returned active source. -/
theorem vfMidActiveScaledReturnedClippedCellMass_eq_rawParents
    {R p : ℕ} {sig : Finset ℕ} (hp : p.Prime) :
    vfMidActiveScaledReturnedClippedCellMass R p sig =
      ∑ r ∈ lowOwnerRevealedPrimesAbove (R + 1) p,
        ∑ parent ∈
          lowOwnerFirstOwnerPolarizationRawParentSet (R + 1) p sig r,
          vfMidActiveReturnedRawParentFiberMass R p sig r parent := by
  rw [vfMidActiveScaledReturnedClippedCellMass_eq_ownerFibers hp]
  apply Finset.sum_congr rfl
  intro r _hr
  rw [sum_lowOwnerFirstOwnerPolarizationGreatestOwnerPairFiber_eq_rawParents]
  rfl

/-- Exact completed/incomplete split for an arbitrary raw-parent weight.
This is the native Boolean classifier used by the returned-core machinery. -/
theorem sum_vfMidRawParents_eq_completed_add_incomplete
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ)
    (f : (ℕ × ℕ) → ℝ) :
    (∑ parent ∈ lowOwnerFirstOwnerPolarizationRawParentSet R p sig r,
      f parent) =
      (∑ parent ∈ lowOwnerFirstOwnerCompletedPolarizationRawParentSet
          R p sig r,
        f parent) +
      ∑ parent ∈ lowOwnerFirstOwnerIncompletePolarizationRawParentSet
          R p sig r,
        f parent := by
  unfold lowOwnerFirstOwnerCompletedPolarizationRawParentSet
    lowOwnerFirstOwnerIncompletePolarizationRawParentSet
  simpa only using
    (Finset.sum_filter_add_sum_filter_not
      (s := lowOwnerFirstOwnerPolarizationRawParentSet R p sig r)
      (p := fun parent : ℕ × ℕ =>
        LowOwnerCompletedPolarizationBlock R p (r, parent))
      (f := f)).symm

/-- **Exact active source completed/incomplete splice.**

This is the requested source-to-boundary classifier: every retained-weight raw
parent is charged exactly once to the existing completed gate carrier or its
literal incomplete complement.  No energy estimate occurs here. -/
theorem vfMidActiveScaledReturnedClippedCellMass_eq_completed_add_incomplete
    {R p : ℕ} {sig : Finset ℕ} (hp : p.Prime) :
    vfMidActiveScaledReturnedClippedCellMass R p sig =
      ∑ r ∈ lowOwnerRevealedPrimesAbove (R + 1) p,
        ((∑ parent ∈
            lowOwnerFirstOwnerCompletedPolarizationRawParentSet
              (R + 1) p sig r,
            vfMidActiveReturnedRawParentFiberMass R p sig r parent) +
          ∑ parent ∈
            lowOwnerFirstOwnerIncompletePolarizationRawParentSet
              (R + 1) p sig r,
            vfMidActiveReturnedRawParentFiberMass R p sig r parent) := by
  rw [vfMidActiveScaledReturnedClippedCellMass_eq_rawParents hp]
  apply Finset.sum_congr rfl
  intro r _hr
  exact
    sum_vfMidRawParents_eq_completed_add_incomplete
      (R + 1) p sig r
      (vfMidActiveReturnedRawParentFiberMass R p sig r)

/-- On a completed raw parent the second mixed child orientation can never lie
on the active returned support: its first coordinate is the admitted raw
parent itself.  Hence that orientation has zero active weight. -/
theorem vfMidActiveReturnedPairWeight_secondMixed_eq_zero_of_completed
    {R p r : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (hcompleted :
      parent ∈ lowOwnerFirstOwnerCompletedPolarizationRawParentSet
        (R + 1) p sig r) :
    vfMidActiveReturnedPairWeight R p sig
      (parent.1, r * parent.2) = 0 := by
  have hblock :
      LowOwnerCompletedPolarizationBlock (R + 1) p (r, parent) :=
    (Finset.mem_filter.mp hcompleted).2
  have hpLeft :
      p * parent.1 ≤ squareRootEndpoint (R + 1) := by
    simpa [LowOwnerCompletedPolarizationBlock] using hblock.2.2.2.2.1
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
    omega
  simp [vfMidActiveReturnedPairWeight, hnot]


/-- On a completed raw parent the first mixed child orientation is also absent
from the active returned support: completion keeps the returned first
coordinate p-admitted, while the active source requires it to be p-clipped. -/
theorem vfMidActiveReturnedPairWeight_firstMixed_eq_zero_of_completed
    {R p r : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (hcompleted :
      parent ∈ lowOwnerFirstOwnerCompletedPolarizationRawParentSet
        (R + 1) p sig r) :
    vfMidActiveReturnedPairWeight R p sig
      (r * parent.1, parent.2) = 0 := by
  have hblock :
      LowOwnerCompletedPolarizationBlock (R + 1) p (r, parent) :=
    (Finset.mem_filter.mp hcompleted).2
  have hprLeft :
      p * (r * parent.1) ≤ squareRootEndpoint (R + 1) := by
    simpa [LowOwnerCompletedPolarizationBlock] using
      hblock.2.2.2.2.2.2.1
  have hnot :
      (r * parent.1, parent.2) ∉
        vfMidActiveReturnedPairCarrier R p sig := by
    intro hmem
    have hclip :
        r * parent.1 ∈ lowOwnerFirstOwnerClippedBaseFiber
          (R + 1) p sig :=
      (Finset.mem_product.mp hmem).1
    have hgt :
        squareRootEndpoint (R + 1) < p * (r * parent.1) :=
      (Finset.mem_filter.mp hclip).2
    omega
  simp [vfMidActiveReturnedPairWeight, hnot]

/-- **Completed raw parents carry no active returned source at all.**

A fixed raw-parent fibre contains only its two mixed r-corners.  Completion
keeps the first coordinate of both corners p-admitted, whereas the active
returned source is supported on p-clipped first coordinates. -/
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
    exact
      vfMidActiveReturnedPairWeight_firstMixed_eq_zero_of_completed hcompleted
  · rw [hright]
    exact
      vfMidActiveReturnedPairWeight_secondMixed_eq_zero_of_completed hcompleted

/-- Hence the whole completed side of one raw-parent split vanishes. -/
theorem sum_vfMidActiveCompletedRawParents_eq_zero
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) :
    (∑ parent ∈
      lowOwnerFirstOwnerCompletedPolarizationRawParentSet
        (R + 1) p sig r,
      vfMidActiveReturnedRawParentFiberMass R p sig r parent) = 0 := by
  apply Finset.sum_eq_zero
  intro parent hparent
  exact
    vfMidActiveReturnedRawParentFiberMass_eq_zero_of_completed hparent

/-- **All active returned mass is on incomplete raw parents.**

This removes the completed-gate branch entirely for the #911/#912 active
source; no completed-parent capacity is charged. -/
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
  rw [sum_vfMidActiveCompletedRawParents_eq_zero]
  ring

/-- **Exact six-sector active boundary normal form.**

After the completed side vanishes, every retained active coefficient lies in
exactly one of the six already-compiled oriented incomplete sectors. -/
theorem vfMidActiveScaledReturnedClippedCellMass_eq_sixOrientedSectors
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
  exact
    sum_lowOwnerFirstOwnerIncompleteRawParents_eq_sixOrientedSectors
      (R := R + 1) (p := p) (r := r) (sig := sig) hp
      (vfMidActiveReturnedRawParentFiberMass R p sig r)

/-- The literal active first-owner Gram is therefore exactly the six-sector
signed boundary mass, still before any new square or absolute value. -/
theorem vfMidActiveCellGram_eq_sixOrientedBoundary
    {R p : ℕ} {sig : Finset ℕ}
    (hR : 3 ≤ R) (hp : p.Prime) :
    lowOwnerFirstOwnerCellGramWith
        (R + 1) p sig (vfMidOneBlockActivePhysicalSite R) =
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
  rw [vfMidActiveCellGram_eq_scaledReturnedClippedCellMass hR hp,
    vfMidActiveScaledReturnedClippedCellMass_eq_sixOrientedSectors hp]

/-- Global active cell excess is bounded directly by twice the exact signed
six-sector boundary mass.  This is the legal pre-square splice: no completed
parent survives and no cross-term is dropped. -/
theorem sum_vfMidActiveWeightedCellExcess_le_two_sixOrientedBoundary
    {R : ℕ} (hR : 3 ≤ R) :
    (∑ p ∈ primesUpTo (squareRootEndpoint (R + 1)),
      ∑ sig ∈ lowOwnerFirstOwnerSignatureSet (R + 1) p,
        vfMidActiveWeightedCellExcess R p sig) ≤
      2 *
        (∑ p ∈ primesUpTo (squareRootEndpoint (R + 1)),
          ∑ sig ∈ lowOwnerFirstOwnerSignatureSet (R + 1) p,
            ∑ r ∈ lowOwnerRevealedPrimesAbove (R + 1) p,
              ((∑ parent ∈
                  lowOwnerFirstOwnerIncompleteFirstClipLeftSet
                    (R + 1) p sig r,
                  vfMidActiveReturnedRawParentFiberMass
                    R p sig r parent) +
                (∑ parent ∈
                  lowOwnerFirstOwnerIncompleteFirstClipRightSet
                    (R + 1) p sig r,
                  vfMidActiveReturnedRawParentFiberMass
                    R p sig r parent) +
                (∑ parent ∈
                  lowOwnerFirstOwnerIncompleteNextClipLeftSet
                    (R + 1) p sig r,
                  vfMidActiveReturnedRawParentFiberMass
                    R p sig r parent) +
                (∑ parent ∈
                  lowOwnerFirstOwnerIncompleteNextClipRightSet
                    (R + 1) p sig r,
                  vfMidActiveReturnedRawParentFiberMass
                    R p sig r parent) +
                (∑ parent ∈
                  lowOwnerFirstOwnerIncompleteReturnedClipLeftSet
                    (R + 1) p sig r,
                  vfMidActiveReturnedRawParentFiberMass
                    R p sig r parent) +
                ∑ parent ∈
                  lowOwnerFirstOwnerIncompleteReturnedClipRightSet
                    (R + 1) p sig r,
                  vfMidActiveReturnedRawParentFiberMass
                    R p sig r parent)) := by
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
            ∑ r ∈ lowOwnerRevealedPrimesAbove (R + 1) p,
              ((∑ parent ∈
                  lowOwnerFirstOwnerIncompleteFirstClipLeftSet
                    (R + 1) p sig r,
                  vfMidActiveReturnedRawParentFiberMass
                    R p sig r parent) +
                (∑ parent ∈
                  lowOwnerFirstOwnerIncompleteFirstClipRightSet
                    (R + 1) p sig r,
                  vfMidActiveReturnedRawParentFiberMass
                    R p sig r parent) +
                (∑ parent ∈
                  lowOwnerFirstOwnerIncompleteNextClipLeftSet
                    (R + 1) p sig r,
                  vfMidActiveReturnedRawParentFiberMass
                    R p sig r parent) +
                (∑ parent ∈
                  lowOwnerFirstOwnerIncompleteNextClipRightSet
                    (R + 1) p sig r,
                  vfMidActiveReturnedRawParentFiberMass
                    R p sig r parent) +
                (∑ parent ∈
                  lowOwnerFirstOwnerIncompleteReturnedClipLeftSet
                    (R + 1) p sig r,
                  vfMidActiveReturnedRawParentFiberMass
                    R p sig r parent) +
                ∑ parent ∈
                  lowOwnerFirstOwnerIncompleteReturnedClipRightSet
                    (R + 1) p sig r,
                  vfMidActiveReturnedRawParentFiberMass
                    R p sig r parent)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hpMem
      have hp : p.Prime := (mem_primesUpTo.mp hpMem).1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro sig _hsig
      rw [vfMidActiveCellGram_eq_sixOrientedBoundary hR hp]

/-- **Direct global accounting splice.**

The exact #911 global Co/Div ledger now sees only the root/exclusion residual
plus twice the six incomplete boundary sectors. -/
theorem vfMidFirstBadAnchoredCoDivExcess_le_activeResidual_add_two_sixBoundary
    {R : ℕ} (hR : 3 ≤ R) :
    vfMidFirstBadAnchoredCoDivExcess R ≤
      vfMidActiveGlobalResidualExcess R +
        2 *
          (∑ p ∈ primesUpTo (squareRootEndpoint (R + 1)),
            ∑ sig ∈ lowOwnerFirstOwnerSignatureSet (R + 1) p,
              ∑ r ∈ lowOwnerRevealedPrimesAbove (R + 1) p,
                ((∑ parent ∈
                    lowOwnerFirstOwnerIncompleteFirstClipLeftSet
                      (R + 1) p sig r,
                    vfMidActiveReturnedRawParentFiberMass
                      R p sig r parent) +
                  (∑ parent ∈
                    lowOwnerFirstOwnerIncompleteFirstClipRightSet
                      (R + 1) p sig r,
                    vfMidActiveReturnedRawParentFiberMass
                      R p sig r parent) +
                  (∑ parent ∈
                    lowOwnerFirstOwnerIncompleteNextClipLeftSet
                      (R + 1) p sig r,
                    vfMidActiveReturnedRawParentFiberMass
                      R p sig r parent) +
                  (∑ parent ∈
                    lowOwnerFirstOwnerIncompleteNextClipRightSet
                      (R + 1) p sig r,
                    vfMidActiveReturnedRawParentFiberMass
                      R p sig r parent) +
                  (∑ parent ∈
                    lowOwnerFirstOwnerIncompleteReturnedClipLeftSet
                      (R + 1) p sig r,
                    vfMidActiveReturnedRawParentFiberMass
                      R p sig r parent) +
                  ∑ parent ∈
                    lowOwnerFirstOwnerIncompleteReturnedClipRightSet
                      (R + 1) p sig r,
                    vfMidActiveReturnedRawParentFiberMass
                      R p sig r parent)) := by
  rw [vfMidFirstBadAnchoredCoDivExcess_eq_activeResidual_add_weightedCells hR]
  have hcells :=
    sum_vfMidActiveWeightedCellExcess_le_two_sixOrientedBoundary hR
  linarith

/-- A nonpositive bound on the now-explicit root-plus-six-boundary ledger gives
the terminal NNS half ceiling.  No owner-tree mathematics remains in this
consumer. -/
theorem vfMidFirstBadNNSNormalizedCovariance_le_half_of_activeSixBoundaryBudget
    {R : ℕ} (hR : 8 ≤ R)
    (hfirst : VFMidActualPrimeFirstBadAt (2 : ℝ) (R + 1))
    (hbudget :
      vfMidActiveGlobalResidualExcess R +
        2 *
          (∑ p ∈ primesUpTo (squareRootEndpoint (R + 1)),
            ∑ sig ∈ lowOwnerFirstOwnerSignatureSet (R + 1) p,
              ∑ r ∈ lowOwnerRevealedPrimesAbove (R + 1) p,
                ((∑ parent ∈
                    lowOwnerFirstOwnerIncompleteFirstClipLeftSet
                      (R + 1) p sig r,
                    vfMidActiveReturnedRawParentFiberMass
                      R p sig r parent) +
                  (∑ parent ∈
                    lowOwnerFirstOwnerIncompleteFirstClipRightSet
                      (R + 1) p sig r,
                    vfMidActiveReturnedRawParentFiberMass
                      R p sig r parent) +
                  (∑ parent ∈
                    lowOwnerFirstOwnerIncompleteNextClipLeftSet
                      (R + 1) p sig r,
                    vfMidActiveReturnedRawParentFiberMass
                      R p sig r parent) +
                  (∑ parent ∈
                    lowOwnerFirstOwnerIncompleteNextClipRightSet
                      (R + 1) p sig r,
                    vfMidActiveReturnedRawParentFiberMass
                      R p sig r parent) +
                  (∑ parent ∈
                    lowOwnerFirstOwnerIncompleteReturnedClipLeftSet
                      (R + 1) p sig r,
                    vfMidActiveReturnedRawParentFiberMass
                      R p sig r parent) +
                  ∑ parent ∈
                    lowOwnerFirstOwnerIncompleteReturnedClipRightSet
                      (R + 1) p sig r,
                    vfMidActiveReturnedRawParentFiberMass
                      R p sig r parent)) ≤ 0) :
    vfMidFirstBadNNSNormalizedCovariance R ≤ (1 / 2 : ℝ) := by
  have hcodiv :
      vfMidFirstBadAnchoredCoDivExcess R ≤ 0 :=
    (vfMidFirstBadAnchoredCoDivExcess_le_activeResidual_add_two_sixBoundary
      (by omega : 3 ≤ R)).trans hbudget
  have htotal0 : 0 ≤ vfMidFirstBadZeroTargetTotalMass R := by
    rw [vfMidFirstBadZeroTargetTotalMass_eq]
    positivity
  have hendpoint :=
    vfMidFirstBadNormalizedProduct_eq_nextEndpointDefect_sq
      (R := R) (by omega : 3 ≤ R)
  have htotalPos : 0 < vfMidFirstBadZeroTargetTotalMass R := by
    by_contra hnot
    have hzero : vfMidFirstBadZeroTargetTotalMass R = 0 :=
      le_antisymm (le_of_not_gt hnot) htotal0
    rw [hzero, mul_zero] at hendpoint
    have hDzero :
        vfMidActualPrimeEndpointDefect (R + 1) = 0 := by
      nlinarith [sq_nonneg (vfMidActualPrimeEndpointDefect (R + 1))]
    have hbreach := hfirst.1
    unfold VFMidSyntheticBadAt at hbreach
    rw [hDzero, abs_zero] at hbreach
    have hscalePos :
        0 < vfMidSyntheticRadialScale (R + 1) :=
      vfMidSyntheticRadialScale_pos (by omega : 2 ≤ R + 1)
    nlinarith
  by_contra hnot
  have hgt :
      (1 / 2 : ℝ) < vfMidFirstBadNNSNormalizedCovariance R :=
    lt_of_not_ge hnot
  have hmul :
      (1 / 2 : ℝ) * vfMidFirstBadZeroTargetTotalMass R <
        vfMidFirstBadNNSNormalizedCovariance R *
          vfMidFirstBadZeroTargetTotalMass R :=
    mul_lt_mul_of_pos_right hgt htotalPos
  have hpos :
      0 < vfMidFirstBadAnchoredCoDivExcess R := by
    rw [vfMidFirstBadAnchoredCoDivExcess_eq_two_product_sub_total]
    nlinarith
  exact (not_lt_of_ge hcodiv) hpos

/-- **Terminal collision.**  Once the exact root-plus-six-boundary budget is
nonpositive, first badness simultaneously forces N_R > 1/2 and N_R <= 1/2. -/
theorem vfMidActualPrimeFirstBadAt_two_succ_false_of_activeSixBoundaryBudget
    {R : ℕ} (hR : 8 ≤ R)
    (hfirst : VFMidActualPrimeFirstBadAt (2 : ℝ) (R + 1))
    (hbudget :
      vfMidActiveGlobalResidualExcess R +
        2 *
          (∑ p ∈ primesUpTo (squareRootEndpoint (R + 1)),
            ∑ sig ∈ lowOwnerFirstOwnerSignatureSet (R + 1) p,
              ∑ r ∈ lowOwnerRevealedPrimesAbove (R + 1) p,
                ((∑ parent ∈
                    lowOwnerFirstOwnerIncompleteFirstClipLeftSet
                      (R + 1) p sig r,
                    vfMidActiveReturnedRawParentFiberMass
                      R p sig r parent) +
                  (∑ parent ∈
                    lowOwnerFirstOwnerIncompleteFirstClipRightSet
                      (R + 1) p sig r,
                    vfMidActiveReturnedRawParentFiberMass
                      R p sig r parent) +
                  (∑ parent ∈
                    lowOwnerFirstOwnerIncompleteNextClipLeftSet
                      (R + 1) p sig r,
                    vfMidActiveReturnedRawParentFiberMass
                      R p sig r parent) +
                  (∑ parent ∈
                    lowOwnerFirstOwnerIncompleteNextClipRightSet
                      (R + 1) p sig r,
                    vfMidActiveReturnedRawParentFiberMass
                      R p sig r parent) +
                  (∑ parent ∈
                    lowOwnerFirstOwnerIncompleteReturnedClipLeftSet
                      (R + 1) p sig r,
                    vfMidActiveReturnedRawParentFiberMass
                      R p sig r parent) +
                  ∑ parent ∈
                    lowOwnerFirstOwnerIncompleteReturnedClipRightSet
                      (R + 1) p sig r,
                    vfMidActiveReturnedRawParentFiberMass
                      R p sig r parent)) ≤ 0) :
    False := by
  have hle :=
    vfMidFirstBadNNSNormalizedCovariance_le_half_of_activeSixBoundaryBudget
      hR hfirst hbudget
  have hgt :=
    vfMidActualPrimeFirstBadAt_two_succ_nnsNormalized_gt_half hR hfirst
  linarith


end RHLean.Analysis
