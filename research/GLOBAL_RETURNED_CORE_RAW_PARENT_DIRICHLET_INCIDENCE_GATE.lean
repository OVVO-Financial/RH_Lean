import Mathlib
import «research.GLOBAL_RETURNED_CORE_RAW_PARENT_BOUNDARY_NORMAL_FORM»
import «research.GLOBAL_RETURNED_CORE_THRESHOLD_FOUR_CORNER_ENERGY_BRIDGE»

/-!
# Universal Dirichlet-incidence gate on the raw-parent recursion

Completion is not needed for the signed polarization algebra itself.  For every
occurring raw parent `(a,b)` with fresh owner `r`, the next-polarization term is
exactly

  DirichletIncidenceFourCorner(r,a,b)
    - BaseFourCorner(r,a,b)
    - ReturnedFourCorner(r,a,b).

The completion hypothesis is needed only one step later, when the Dirichlet
incidence four-corner is identified with the threshold-incidence currency that
has the compiled reciprocal energy gate.

This lets us keep one signed same-branch ledger across completed and incomplete
parents.  The only boundary object that remains to classify is the *incidence*
four-corner on incomplete parents; the full polarization is never packetwise
normed.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Dirichlet-incidence four-corner on one raw parent, with no completion
assumption. -/
def lowOwnerRawParentDirichletIncidenceFourCornerMass
    (R p r : ℕ) (parent : ℕ × ℕ) : ℝ :=
  weightedMoebiusFreshPrimeFourCornerMass
    (lowOwnerPhysicalDirichletIncidenceWeight R p)
    r parent.1 parent.2

/-- The two signed same-branch four-corners on one raw parent. -/
def lowOwnerRawParentSameBranchFourCornerMass
    (R p r : ℕ) (parent : ℕ × ℕ) : ℝ :=
  weightedMoebiusFreshPrimeFourCornerMass
      (lowOwnerDirichletBaseCoefficient R)
      r parent.1 parent.2 +
    weightedMoebiusFreshPrimeFourCornerMass
      (lowOwnerDirichletReturnedCoefficient R p)
      r parent.1 parent.2

/-- **Universal raw-parent signed currency.**  No endpoint-completion hypothesis
is required because all three coordinates use the same Dirichlet zero
extension. -/
theorem lowOwnerFirstOwnerRawParentNextPolarizationTerm_eq_dirichletIncidence_sub_sameBranch
    {R p r : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (hp : p.Prime)
    (hparent : parent ∈ lowOwnerFirstOwnerPolarizationRawParentSet R p sig r) :
    lowOwnerFirstOwnerRawParentNextPolarizationTerm R p r parent =
      lowOwnerRawParentDirichletIncidenceFourCornerMass R p r parent -
        lowOwnerRawParentSameBranchFourCornerMass R p r parent := by
  rcases lowOwnerFirstOwnerPolarizationRawParent_data hp hparent with
    ⟨hr, _hpr, _haBase, _hbBase, hra, hrb⟩
  unfold lowOwnerFirstOwnerRawParentNextPolarizationTerm
    lowOwnerRawParentDirichletIncidenceFourCornerMass
    lowOwnerRawParentSameBranchFourCornerMass
  rw [weightedMoebiusFreshPrimeFourCornerMass_eq_ownerDifferences
      (lowOwnerPhysicalDirichletIncidenceWeight R p) hr hra hrb,
    weightedMoebiusFreshPrimeFourCornerMass_eq_ownerDifferences
      (lowOwnerDirichletBaseCoefficient R) hr hra hrb,
    weightedMoebiusFreshPrimeFourCornerMass_eq_ownerDifferences
      (lowOwnerDirichletReturnedCoefficient R p) hr hra hrb]
  unfold lowOwnerDirichletNextPolarizationScalar
    lowOwnerDirichletOwnerDifference
    lowOwnerDirichletIncidenceCoefficient
    lowOwnerDirichletBaseCoefficient
    lowOwnerDirichletReturnedCoefficient
    lowOwnerPhysicalDirichletIncidenceWeight
  ring

/-- Aggregate Dirichlet-incidence mass over all occurring raw parents. -/
def lowOwnerFirstOwnerRawParentDirichletIncidenceMass
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : ℝ :=
  ∑ parent ∈ lowOwnerFirstOwnerPolarizationRawParentSet R p sig r,
    lowOwnerRawParentDirichletIncidenceFourCornerMass R p r parent

/-- Aggregate same-branch mass over all occurring raw parents. -/
def lowOwnerFirstOwnerRawParentSameBranchMass
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : ℝ :=
  ∑ parent ∈ lowOwnerFirstOwnerPolarizationRawParentSet R p sig r,
    lowOwnerRawParentSameBranchFourCornerMass R p r parent

/-- The entire next-polarization layer is incidence minus same-branch before any
completed/incomplete split. -/
theorem sum_lowOwnerFirstOwnerRawParentNextPolarization_eq_dirichletIncidence_sub_sameBranch
    {R p r : ℕ} {sig : Finset ℕ} (hp : p.Prime) :
    (∑ parent ∈ lowOwnerFirstOwnerPolarizationRawParentSet R p sig r,
      lowOwnerFirstOwnerRawParentNextPolarizationTerm R p r parent) =
      lowOwnerFirstOwnerRawParentDirichletIncidenceMass R p sig r -
        lowOwnerFirstOwnerRawParentSameBranchMass R p sig r := by
  unfold lowOwnerFirstOwnerRawParentDirichletIncidenceMass
    lowOwnerFirstOwnerRawParentSameBranchMass
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro parent hparent
  exact
    lowOwnerFirstOwnerRawParentNextPolarizationTerm_eq_dirichletIncidence_sub_sameBranch
      hp hparent

/-- Dirichlet-incidence boundary retained only on incomplete raw parents. -/
def lowOwnerFirstOwnerIncompleteDirichletIncidenceMass
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : ℝ :=
  ∑ parent ∈ lowOwnerFirstOwnerIncompletePolarizationRawParentSet R p sig r,
    lowOwnerRawParentDirichletIncidenceFourCornerMass R p r parent

/-- Exact completed/incomplete partition of the universal incidence mass. -/
theorem lowOwnerFirstOwnerRawParentDirichletIncidenceMass_eq_completed_add_incomplete
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) :
    lowOwnerFirstOwnerRawParentDirichletIncidenceMass R p sig r =
      (∑ parent ∈ lowOwnerFirstOwnerCompletedPolarizationRawParentSet R p sig r,
        lowOwnerRawParentDirichletIncidenceFourCornerMass R p r parent) +
      lowOwnerFirstOwnerIncompleteDirichletIncidenceMass R p sig r := by
  unfold lowOwnerFirstOwnerRawParentDirichletIncidenceMass
    lowOwnerFirstOwnerCompletedPolarizationRawParentSet
    lowOwnerFirstOwnerIncompletePolarizationRawParentSet
    lowOwnerFirstOwnerIncompleteDirichletIncidenceMass
  simpa only using
    (Finset.sum_filter_add_sum_filter_not
      (s := lowOwnerFirstOwnerPolarizationRawParentSet R p sig r)
      (p := fun parent : ℕ × ℕ =>
        LowOwnerCompletedPolarizationBlock R p (r, parent))
      (f := fun parent =>
        lowOwnerRawParentDirichletIncidenceFourCornerMass R p r parent)).symm

/-- On a completed raw parent, the universal Dirichlet incidence is exactly the
threshold-incidence gate currency. -/
theorem lowOwnerRawParentDirichletIncidenceFourCornerMass_eq_completedIncidence
    {R p r : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (hparent : parent ∈
      lowOwnerFirstOwnerCompletedPolarizationRawParentSet R p sig r) :
    lowOwnerRawParentDirichletIncidenceFourCornerMass R p r parent =
      lowOwnerCompletedIncidenceFourCornerMass R p (r, parent) := by
  have hcomplete := (Finset.mem_filter.mp hparent).2
  rcases hcomplete with
    ⟨hr, hra, hrb, ha, hpa, hraX, hpraX, hb, hpb, hrbX, hprbX⟩
  unfold lowOwnerRawParentDirichletIncidenceFourCornerMass
    lowOwnerCompletedIncidenceFourCornerMass
  exact lowOwnerPhysicalDirichletIncidence_fourCorner_eq_threshold_of_complete
    hr hra hrb ha hpa hraX hpraX hb hpb hrbX hprbX

/-- Aggregate completed universal incidence is the already-compiled incidence
gate mass. -/
theorem sum_lowOwnerCompletedRawParentDirichletIncidence_eq_gateMass
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) :
    (∑ parent ∈ lowOwnerFirstOwnerCompletedPolarizationRawParentSet R p sig r,
      lowOwnerRawParentDirichletIncidenceFourCornerMass R p r parent) =
      lowOwnerFirstOwnerCompletedIncidenceGateMass R p sig r := by
  unfold lowOwnerFirstOwnerCompletedIncidenceGateMass
  apply Finset.sum_congr rfl
  intro parent hparent
  exact lowOwnerRawParentDirichletIncidenceFourCornerMass_eq_completedIncidence
    hparent

/-- **Gate moved inside the polarization.**  All completed parents enter the
threshold incidence gate; all incomplete parents leave only their Dirichlet
incidence boundary, while the same-branch ledger remains signed across both. -/
theorem sum_lowOwnerFirstOwnerRawParentNextPolarization_eq_gate_add_incompleteIncidence_sub_allSameBranch
    {R p r : ℕ} {sig : Finset ℕ} (hp : p.Prime) :
    (∑ parent ∈ lowOwnerFirstOwnerPolarizationRawParentSet R p sig r,
      lowOwnerFirstOwnerRawParentNextPolarizationTerm R p r parent) =
      lowOwnerFirstOwnerCompletedIncidenceGateMass R p sig r +
        lowOwnerFirstOwnerIncompleteDirichletIncidenceMass R p sig r -
        lowOwnerFirstOwnerRawParentSameBranchMass R p sig r := by
  rw [sum_lowOwnerFirstOwnerRawParentNextPolarization_eq_dirichletIncidence_sub_sameBranch
    hp]
  rw [lowOwnerFirstOwnerRawParentDirichletIncidenceMass_eq_completed_add_incomplete]
  rw [sum_lowOwnerCompletedRawParentDirichletIncidence_eq_gateMass]

/-- **Cleaner descending one-layer estimate.**  After exact signed reassembly,
only completed incidence and incomplete incidence are exposed at the gate.  The
same-branch continuation and lower-owner persistence remain signed. -/
theorem lowOwnerFirstOwnerRevealedPolarizationEnergy_descending_le_gate_add_incompleteIncidence_sub_sameBranch_add_lowerOwners
    {R p r : ℕ} {sig : Finset ℕ}
    (hp : p.Prime) (hr : r.Prime) (hpr : p < r) :
    lowOwnerFirstOwnerRevealedPolarizationEnergy R p sig
        (lowOwnerRevealedPrimesAbove R r) ≤
      lowOwnerFirstOwnerCompletedIncidenceGateMass R p sig r +
        lowOwnerFirstOwnerIncompleteDirichletIncidenceMass R p sig r -
        lowOwnerFirstOwnerRawParentSameBranchMass R p sig r +
      ∑ q ∈ lowOwnerFirstOwnerRawParentInertLowerOwnerSchedule R p r,
        ∑ mn ∈ lowOwnerFirstOwnerRawParentOrbitInertGreatestOwnerFiber
            R p sig r q,
          lowOwnerFirstOwnerDirichletPolarizationAtom R p mn := by
  have hdesc :=
    lowOwnerFirstOwnerRevealedPolarizationEnergy_descending_le_next_add_lowerOwners
      (R := R) (p := p) (r := r) (sig := sig) hp hr hpr
  have hsplit :=
    sum_lowOwnerFirstOwnerRawParentNextPolarization_eq_gate_add_incompleteIncidence_sub_allSameBranch
      (R := R) (p := p) (r := r) (sig := sig) hp
  unfold lowOwnerFirstOwnerRawParentNextPolarizationTerm at hsplit
  rw [hsplit] at hdesc
  exact hdesc

end RHLean.Proof
