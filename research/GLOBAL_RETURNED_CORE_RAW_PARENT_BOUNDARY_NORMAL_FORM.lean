import Mathlib
import «research.GLOBAL_RETURNED_CORE_RAW_PARENT_INCOMPLETE_FUBINI»

/-!
# Complete signed boundary normal form for one descending owner layer

Substitute the exact three-sector incomplete-boundary Fubini into the completed
incidence-gate splice.  After the favorable inert diagonal is removed, every
surviving term now has a named role:

* completed incidence gate;
* completed same-branch signed continuation;
* first-owner clipping;
* next-owner physical exit;
* returned-after-r clipping;
* strictly-lower greatest-owner persistence.

There is no anonymous remainder.  No boundary sector is squared or estimated in
this file.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Signed next-polarization mass on the first-owner clipped incomplete sector. -/
def lowOwnerFirstOwnerIncompleteFirstClipMass
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : ℝ :=
  ∑ parent ∈ lowOwnerFirstOwnerIncompleteFirstClipSet R p sig r,
    lowOwnerFirstOwnerRawParentNextPolarizationTerm R p r parent

/-- Signed next-polarization mass on the next-owner physical-exit sector. -/
def lowOwnerFirstOwnerIncompleteNextClipMass
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : ℝ :=
  ∑ parent ∈ lowOwnerFirstOwnerIncompleteNextClipSet R p sig r,
    lowOwnerFirstOwnerRawParentNextPolarizationTerm R p r parent

/-- Signed next-polarization mass on the returned-after-r clipped sector. -/
def lowOwnerFirstOwnerIncompleteReturnedClipMass
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : ℝ :=
  ∑ parent ∈ lowOwnerFirstOwnerIncompleteReturnedClipSet R p sig r,
    lowOwnerFirstOwnerRawParentNextPolarizationTerm R p r parent

/-- **Complete one-layer signed normal form.** -/
theorem lowOwnerFirstOwnerRevealedPolarizationEnergy_descending_le_namedBoundaryNormalForm
    {R p r : ℕ} {sig : Finset ℕ}
    (hp : p.Prime) (hr : r.Prime) (hpr : p < r) :
    lowOwnerFirstOwnerRevealedPolarizationEnergy R p sig
        (lowOwnerRevealedPrimesAbove R r) ≤
      lowOwnerFirstOwnerCompletedIncidenceGateMass R p sig r -
        lowOwnerFirstOwnerCompletedSameBranchMass R p sig r +
      lowOwnerFirstOwnerIncompleteFirstClipMass R p sig r +
      lowOwnerFirstOwnerIncompleteNextClipMass R p sig r +
      lowOwnerFirstOwnerIncompleteReturnedClipMass R p sig r +
      ∑ q ∈ lowOwnerFirstOwnerRawParentInertLowerOwnerSchedule R p r,
        ∑ mn ∈ lowOwnerFirstOwnerRawParentOrbitInertGreatestOwnerFiber
            R p sig r q,
          lowOwnerFirstOwnerDirichletPolarizationAtom R p mn := by
  have hdesc :=
    lowOwnerFirstOwnerRevealedPolarizationEnergy_descending_le_gate_sub_sameBranch_add_incomplete_add_lowerOwners
      (R := R) (p := p) (r := r) (sig := sig) hp hr hpr
  have hboundary :=
    sum_lowOwnerFirstOwnerIncompleteRawParents_eq_threeClipSectors
      (R := R) (p := p) (r := r) (sig := sig) hp
      (fun parent => lowOwnerFirstOwnerRawParentNextPolarizationTerm R p r parent)
  unfold lowOwnerFirstOwnerIncompleteFirstClipMass
    lowOwnerFirstOwnerIncompleteNextClipMass
    lowOwnerFirstOwnerIncompleteReturnedClipMass
  rw [hboundary] at hdesc
  linarith

end RHLean.Proof
