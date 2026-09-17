import Mathlib
import «research.GLOBAL_RETURNED_CORE_RAW_PARENT_BOUNDARY_ORIENTED_FUBINI»

/-!
# Orientation-resolved descending boundary normal form

The incomplete raw-parent ledger is now split both chronologically and by a
canonical coordinate orientation.  Substituting that exact six-sector Fubini
into the completed-gate splice gives a one-layer descending inequality with no
anonymous boundary term and no duplicate left/right charge.

The only positive currency introduced upstream remains the completed incidence
gate.  All six boundary sectors and the lower-owner persistence remain signed.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- **Fully oriented one-layer signed normal form.** -/
theorem lowOwnerFirstOwnerRevealedPolarizationEnergy_descending_le_orientedBoundaryNormalForm
    {R p r : ℕ} {sig : Finset ℕ}
    (hp : p.Prime) (hr : r.Prime) (hpr : p < r) :
    lowOwnerFirstOwnerRevealedPolarizationEnergy R p sig
        (lowOwnerRevealedPrimesAbove R r) ≤
      lowOwnerFirstOwnerCompletedIncidenceGateMass R p sig r -
        lowOwnerFirstOwnerCompletedSameBranchMass R p sig r +
      (∑ parent ∈ lowOwnerFirstOwnerIncompleteFirstClipLeftSet R p sig r,
        lowOwnerFirstOwnerRawParentNextPolarizationTerm R p r parent) +
      (∑ parent ∈ lowOwnerFirstOwnerIncompleteFirstClipRightSet R p sig r,
        lowOwnerFirstOwnerRawParentNextPolarizationTerm R p r parent) +
      (∑ parent ∈ lowOwnerFirstOwnerIncompleteNextClipLeftSet R p sig r,
        lowOwnerFirstOwnerRawParentNextPolarizationTerm R p r parent) +
      (∑ parent ∈ lowOwnerFirstOwnerIncompleteNextClipRightSet R p sig r,
        lowOwnerFirstOwnerRawParentNextPolarizationTerm R p r parent) +
      (∑ parent ∈ lowOwnerFirstOwnerIncompleteReturnedClipLeftSet R p sig r,
        lowOwnerFirstOwnerRawParentNextPolarizationTerm R p r parent) +
      (∑ parent ∈ lowOwnerFirstOwnerIncompleteReturnedClipRightSet R p sig r,
        lowOwnerFirstOwnerRawParentNextPolarizationTerm R p r parent) +
      ∑ q ∈ lowOwnerFirstOwnerRawParentInertLowerOwnerSchedule R p r,
        ∑ mn ∈ lowOwnerFirstOwnerRawParentOrbitInertGreatestOwnerFiber
            R p sig r q,
          lowOwnerFirstOwnerDirichletPolarizationAtom R p mn := by
  have hdesc :=
    lowOwnerFirstOwnerRevealedPolarizationEnergy_descending_le_gate_sub_sameBranch_add_incomplete_add_lowerOwners
      (R := R) (p := p) (r := r) (sig := sig) hp hr hpr
  have horient :=
    sum_lowOwnerFirstOwnerIncompleteRawParents_eq_sixOrientedSectors
      (R := R) (p := p) (r := r) (sig := sig) hp
      (fun parent => lowOwnerFirstOwnerRawParentNextPolarizationTerm R p r parent)
  rw [horient] at hdesc
  linarith

end RHLean.Proof
