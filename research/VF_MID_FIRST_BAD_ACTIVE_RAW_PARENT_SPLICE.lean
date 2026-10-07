import Mathlib
import «research.VF_MID_FIRST_BAD_SCALED_CLIPPED_GATE»
import «research.GLOBAL_RETURNED_CORE_POLARIZATION_RAW_PARENT_FUBINI»
import «research.GLOBAL_RETURNED_CORE_RAW_PARENT_COMPLETED_GATE_SPLIT»
import «research.GLOBAL_RETURNED_CORE_RAW_PARENT_BOUNDARY_ORIENTED_FUBINI»

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
  have hs :=
    Finset.sum_subset hsub hzero
  unfold vfMidActiveScaledReturnedClippedCellMass
    vfMidActiveReturnedPairCarrier at hs ⊢
  have hleft :
      (∑ ab ∈
          (lowOwnerFirstOwnerClippedBaseFiber (R + 1) p sig).product
            (lowOwnerFirstOwnerAdmittedBaseFiber (R + 1) p sig),
        vfMidActiveReturnedPairWeight R p sig ab) =
      vfMidActiveScaledReturnedClippedCellMass R p sig := by
    unfold vfMidActiveScaledReturnedClippedCellMass
      vfMidActiveReturnedPairWeight vfMidActiveReturnedPairCarrier
    apply Finset.sum_congr rfl
    intro ab hab
    simp [hab]
  rw [hleft] at hs
  exact hs

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

end RHLean.Analysis
