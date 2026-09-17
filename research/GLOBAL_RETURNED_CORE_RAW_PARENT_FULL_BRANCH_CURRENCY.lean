import Mathlib
import «research.GLOBAL_RETURNED_CORE_RAW_PARENT_INERT_EQ_TAIL»
import «research.GLOBAL_RETURNED_CORE_DIRICHLET_THRESHOLD_ENDPOINT_CORRECTION»

/-!
# Full-branch threshold currency after inert = tail

Once the inert survivor is identified with the prefix-star tail, one descending
owner layer is exactly a sum of virtual next-polarization four-corners over the
entire revealed r-free branch.  The Dirichlet/threshold endpoint correction is
pointwise and therefore applies on this larger branch as well; it does not need
raw-parent occurrence.

For every branch parent,

  NextPolarization
    = ThresholdFourCorner
      + EndpointCorrection
      - BaseFourCorner
      - ReturnedFourCorner.

After summation, the threshold four-corner is exactly the branch quadratic
energy already realized as a sum of squares.  The endpoint correction and both
same-branch four-corners remain signed.

Thus the old inert/lower-owner remainder disappears completely from the
one-step currency identity.  No inequality is used in this file.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Branch-wide same-branch four-corner continuation. -/
def lowOwnerFirstOwnerBranchSameBranchMass
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : ℝ :=
  ∑ parent ∈ lowOwnerFirstOwnerRawParentBranchCarrier R p sig r,
    lowOwnerRawParentSameBranchFourCornerMass R p r parent

/-- Branch-wide endpoint correction. -/
def lowOwnerFirstOwnerBranchEndpointIncidenceCorrectionMass
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : ℝ :=
  ∑ parent ∈ lowOwnerFirstOwnerRawParentBranchCarrier R p sig r,
    lowOwnerRawParentEndpointIncidenceCorrectionMass R p r parent

/-- On any r-free base-cell branch parent, the next polarization is Dirichlet
incidence minus the two same-branch four-corners. -/
theorem lowOwnerFirstOwnerBranchNextPolarizationTerm_eq_dirichletIncidence_sub_sameBranch
    {R p r : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (hr : r.Prime)
    (hparent : parent ∈ lowOwnerFirstOwnerRawParentBranchCarrier R p sig r) :
    lowOwnerFirstOwnerRawParentNextPolarizationTerm R p r parent =
      lowOwnerRawParentDirichletIncidenceFourCornerMass R p r parent -
        lowOwnerRawParentSameBranchFourCornerMass R p r parent := by
  rcases Finset.mem_filter.mp hparent with
    ⟨_hprod, _hsigAbove, hra, hrb⟩
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

/-- Branch-wide version of the universal Dirichlet/threshold endpoint
correction. -/
theorem lowOwnerFirstOwnerBranchDirichletIncidenceFourCorner_eq_threshold_add_endpointCorrection
    {R p r : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (hR : 2 ≤ R) (hp : p.Prime) (hr : r.Prime)
    (hparent : parent ∈ lowOwnerFirstOwnerRawParentBranchCarrier R p sig r) :
    lowOwnerRawParentDirichletIncidenceFourCornerMass R p r parent =
      weightedMoebiusFreshPrimeFourCornerMass
          (lowOwnerThresholdOwnerIncidenceWeight R p)
          r parent.1 parent.2 +
        lowOwnerRawParentEndpointIncidenceCorrectionMass R p r parent := by
  rcases Finset.mem_filter.mp hparent with
    ⟨_hprod, _hsigAbove, hra, hrb⟩
  unfold lowOwnerRawParentDirichletIncidenceFourCornerMass
  rw [weightedMoebiusFreshPrimeFourCornerMass_eq_ownerDifferences
      (lowOwnerPhysicalDirichletIncidenceWeight R p) hr hra hrb,
    weightedMoebiusFreshPrimeFourCornerMass_eq_ownerDifferences
      (lowOwnerThresholdOwnerIncidenceWeight R p) hr hra hrb,
    lowOwnerDirichletIncidence_ownerDifference_eq_threshold_add_endpointClippedDifference
      hR hp.one_le hr.one_le,
    lowOwnerDirichletIncidence_ownerDifference_eq_threshold_add_endpointClippedDifference
      hR hp.one_le hr.one_le]
  rw [postRootZeroTargetPairExcess_eq_weight]
  unfold lowOwnerRawParentEndpointIncidenceCorrectionMass
  ring

/-- Threshold four-corner on a full branch parent is exactly the product of its
signed one-dimensional second-incidence sites. -/
theorem lowOwnerFirstOwnerBranchThresholdFourCorner_eq_siteProduct
    {R p r : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (hr : r.Prime)
    (hparent : parent ∈ lowOwnerFirstOwnerRawParentBranchCarrier R p sig r) :
    weightedMoebiusFreshPrimeFourCornerMass
        (lowOwnerThresholdOwnerIncidenceWeight R p)
        r parent.1 parent.2 =
      lowOwnerRawParentThresholdSignedSite R p r parent.1 *
        lowOwnerRawParentThresholdSignedSite R p r parent.2 := by
  rcases Finset.mem_filter.mp hparent with
    ⟨_hprod, _hsigAbove, hra, hrb⟩
  rw [weightedMoebiusFreshPrimeFourCornerMass_eq_ownerDifferences
    (lowOwnerThresholdOwnerIncidenceWeight R p) hr hra hrb]
  rw [postRootZeroTargetPairExcess_eq_weight]
  unfold lowOwnerRawParentThresholdSignedSite
  ring

/-- The aggregate threshold four-corner over the full branch is exactly the
branch quadratic energy. -/
theorem sum_lowOwnerFirstOwnerBranchThresholdFourCorner_eq_branchThresholdEnergy
    {R p r : ℕ} {sig : Finset ℕ} (hr : r.Prime) :
    (∑ parent ∈ lowOwnerFirstOwnerRawParentBranchCarrier R p sig r,
      weightedMoebiusFreshPrimeFourCornerMass
        (lowOwnerThresholdOwnerIncidenceWeight R p)
        r parent.1 parent.2) =
      lowOwnerFirstOwnerRawParentBranchThresholdEnergy R p sig r := by
  unfold lowOwnerFirstOwnerRawParentBranchThresholdEnergy
  apply Finset.sum_congr rfl
  intro parent hparent
  exact lowOwnerFirstOwnerBranchThresholdFourCorner_eq_siteProduct hr hparent

/-- **Exact full-branch currency identity.** -/
theorem sum_lowOwnerFirstOwnerBranchNextPolarization_eq_branchEnergy_add_endpointCorrection_sub_sameBranch
    {R p r : ℕ} {sig : Finset ℕ}
    (hR : 2 ≤ R) (hp : p.Prime) (hr : r.Prime) :
    (∑ parent ∈ lowOwnerFirstOwnerRawParentBranchCarrier R p sig r,
      lowOwnerFirstOwnerRawParentNextPolarizationTerm R p r parent) =
      lowOwnerFirstOwnerRawParentBranchThresholdEnergy R p sig r +
        lowOwnerFirstOwnerBranchEndpointIncidenceCorrectionMass R p sig r -
        lowOwnerFirstOwnerBranchSameBranchMass R p sig r := by
  unfold lowOwnerFirstOwnerBranchEndpointIncidenceCorrectionMass
    lowOwnerFirstOwnerBranchSameBranchMass
  calc
    (∑ parent ∈ lowOwnerFirstOwnerRawParentBranchCarrier R p sig r,
      lowOwnerFirstOwnerRawParentNextPolarizationTerm R p r parent) =
      ∑ parent ∈ lowOwnerFirstOwnerRawParentBranchCarrier R p sig r,
        (lowOwnerRawParentDirichletIncidenceFourCornerMass R p r parent -
          lowOwnerRawParentSameBranchFourCornerMass R p r parent) := by
      apply Finset.sum_congr rfl
      intro parent hparent
      exact
        lowOwnerFirstOwnerBranchNextPolarizationTerm_eq_dirichletIncidence_sub_sameBranch
          hr hparent
    _ =
      (∑ parent ∈ lowOwnerFirstOwnerRawParentBranchCarrier R p sig r,
        lowOwnerRawParentDirichletIncidenceFourCornerMass R p r parent) -
      ∑ parent ∈ lowOwnerFirstOwnerRawParentBranchCarrier R p sig r,
        lowOwnerRawParentSameBranchFourCornerMass R p r parent := by
      rw [Finset.sum_sub_distrib]
    _ =
      ((∑ parent ∈ lowOwnerFirstOwnerRawParentBranchCarrier R p sig r,
        weightedMoebiusFreshPrimeFourCornerMass
          (lowOwnerThresholdOwnerIncidenceWeight R p)
          r parent.1 parent.2) +
        ∑ parent ∈ lowOwnerFirstOwnerRawParentBranchCarrier R p sig r,
          lowOwnerRawParentEndpointIncidenceCorrectionMass R p r parent) -
      ∑ parent ∈ lowOwnerFirstOwnerRawParentBranchCarrier R p sig r,
        lowOwnerRawParentSameBranchFourCornerMass R p r parent := by
      congr 1
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro parent hparent
      exact
        lowOwnerFirstOwnerBranchDirichletIncidenceFourCorner_eq_threshold_add_endpointCorrection
          hR hp hr hparent
    _ = _ := by
      rw [sum_lowOwnerFirstOwnerBranchThresholdFourCorner_eq_branchThresholdEnergy hr]

/-- **Exact one-step descending currency with no inert/lower-owner remainder.** -/
theorem lowOwnerFirstOwnerRevealedPolarizationEnergy_descending_eq_branchEnergy_add_endpointCorrection_sub_sameBranch
    {R p r : ℕ} {sig : Finset ℕ}
    (hR : 2 ≤ R) (hp : p.Prime) (hr : r.Prime) (hpr : p < r) :
    lowOwnerFirstOwnerRevealedPolarizationEnergy R p sig
        (lowOwnerRevealedPrimesAbove R r) =
      lowOwnerFirstOwnerRawParentBranchThresholdEnergy R p sig r +
        lowOwnerFirstOwnerBranchEndpointIncidenceCorrectionMass R p sig r -
        lowOwnerFirstOwnerBranchSameBranchMass R p sig r := by
  rw [lowOwnerFirstOwnerRevealedPolarizationEnergy_descending_eq_branchNextPolarization
    hp hr hpr]
  exact
    sum_lowOwnerFirstOwnerBranchNextPolarization_eq_branchEnergy_add_endpointCorrection_sub_sameBranch
      hR hp hr

end RHLean.Proof
