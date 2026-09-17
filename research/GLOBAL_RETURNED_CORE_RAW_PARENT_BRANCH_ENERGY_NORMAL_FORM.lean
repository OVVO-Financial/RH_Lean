import Mathlib
import «research.GLOBAL_RETURNED_CORE_RAW_PARENT_BRANCH_SQUARES»
import «research.GLOBAL_RETURNED_CORE_RAW_PARENT_ENDPOINT_CORRECTION_SUPPORT»

/-!
# Descending raw-parent normal form with one legal positive branch energy

The signed raw-parent recursion has already been converted exactly to

  threshold incidence + endpoint correction - same branch + lower owners.

The prefix-star theorem then identifies the threshold incidence as

  BranchEnergy - TailEnergy,

and the fibrewise square realization proves `TailEnergy >= 0`.  This is the
first legal one-sided step on that term: discard only the explicitly
nonnegative tail *after* the exact signed factorization.

The endpoint correction remains signed and is restricted exactly to incomplete
raw parents.  The same-branch continuation and strictly-lower-owner persistence
also remain signed.  No triangle inequality is used.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- **One-layer branch-energy normal form.**  The only positive quantity paid
at the current owner is the revealed-branch sum-of-squares energy. -/
theorem lowOwnerFirstOwnerRevealedPolarizationEnergy_descending_le_branchEnergy_add_incompleteEndpointCorrection_sub_sameBranch_add_lowerOwners
    {R p r : ℕ} {sig : Finset ℕ}
    (hR : 2 ≤ R) (hp : p.Prime) (hr : r.Prime) (hpr : p < r) :
    lowOwnerFirstOwnerRevealedPolarizationEnergy R p sig
        (lowOwnerRevealedPrimesAbove R r) ≤
      lowOwnerFirstOwnerRawParentBranchThresholdEnergy R p sig r +
        lowOwnerFirstOwnerIncompleteEndpointIncidenceCorrectionMass
          R p sig r -
        lowOwnerFirstOwnerRawParentSameBranchMass R p sig r +
      ∑ q ∈ lowOwnerFirstOwnerRawParentInertLowerOwnerSchedule R p r,
        ∑ mn ∈ lowOwnerFirstOwnerRawParentOrbitInertGreatestOwnerFiber
            R p sig r q,
          lowOwnerFirstOwnerDirichletPolarizationAtom R p mn := by
  have hdesc :=
    lowOwnerFirstOwnerRevealedPolarizationEnergy_descending_le_threshold_add_endpointCorrection_sub_sameBranch_add_lowerOwners
      (R := R) (p := p) (r := r) (sig := sig) hR hp hr hpr
  rw [lowOwnerFirstOwnerRawParentEndpointIncidenceCorrectionMass_eq_incomplete]
    at hdesc
  have hthreshold :=
    lowOwnerFirstOwnerRawParentThresholdIncidenceMass_le_branchThresholdEnergy
      (R := R) (p := p) (r := r) (sig := sig) hp hr hpr
  linarith

end RHLean.Proof
