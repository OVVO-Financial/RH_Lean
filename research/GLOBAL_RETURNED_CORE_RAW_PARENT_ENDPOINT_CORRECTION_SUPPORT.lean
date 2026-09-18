import Mathlib
import «research.GLOBAL_RETURNED_CORE_DIRICHLET_THRESHOLD_ENDPOINT_CORRECTION»
import «research.GLOBAL_RETURNED_CORE_THRESHOLD_DOUBLE_CORNER_RECIPROCAL»

/-!
# Support and two-boundary normal form of the endpoint correction

The universal Dirichlet/threshold bridge leaves one exact endpoint correction
per raw parent.  That correction has two further elementary properties.

First, it vanishes identically on every completed raw-parent cube.  Therefore
its aggregate support is literally the already-defined incomplete raw-parent
set; no completed gate atom pays an endpoint error.

Second, the commuting-incidence identity gives, coordinate by coordinate,

  endpointCorrection(n)
    = chi_p(n, X_R) - DoubleCorner_{p,r}(n, X_R).

Hence the only primitive endpoint modes are the current first-owner clip and
the returned-after-r double corner.  A next-owner physical exit is encoded in
the ordinary threshold second difference and is not a third endpoint-correction
mode.

No magnitude estimate is used.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- On a completed coordinate the endpoint clipped-difference is exactly zero. -/
private theorem lowOwnerThresholdClippedDifference_eq_zero_of_completedCoordinate
    {R p r n : ℕ}
    (hn : n ≤ squareRootEndpoint R)
    (hpn : p * n ≤ squareRootEndpoint R)
    (hrn : r * n ≤ squareRootEndpoint R)
    (hprn : p * (r * n) ≤ squareRootEndpoint R) :
    lowOwnerThresholdClippedDifference
        p r n (squareRootEndpoint R) = 0 := by
  have hrpn : r * (p * n) ≤ squareRootEndpoint R := by
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hprn
  unfold lowOwnerThresholdClippedDifference
    lowOwnerThresholdCrossingIndicator
  simp [hn, hpn, Nat.not_lt_of_ge hrn, Nat.not_lt_of_ge hrpn]

/-- **Completed cubes carry no endpoint correction.** -/
theorem lowOwnerRawParentEndpointIncidenceCorrectionMass_eq_zero_of_completed
    {R p r : ℕ} {parent : ℕ × ℕ}
    (hcomplete : LowOwnerCompletedPolarizationBlock R p (r, parent)) :
    lowOwnerRawParentEndpointIncidenceCorrectionMass R p r parent = 0 := by
  rcases hcomplete with
    ⟨_hr, _hraFresh, _hrbFresh,
      ha, hpa, hra, hpra,
      hb, hpb, hrb, hprb⟩
  have hca :=
    lowOwnerThresholdClippedDifference_eq_zero_of_completedCoordinate
      ha hpa hra hpra
  have hcb :=
    lowOwnerThresholdClippedDifference_eq_zero_of_completedCoordinate
      hb hpb hrb hprb
  unfold lowOwnerRawParentEndpointIncidenceCorrectionMass
  rw [hca, hcb]
  ring

/-- Endpoint correction restricted to the incomplete raw-parent carrier. -/
def lowOwnerFirstOwnerIncompleteEndpointIncidenceCorrectionMass
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : ℝ :=
  ∑ parent ∈ lowOwnerFirstOwnerIncompletePolarizationRawParentSet R p sig r,
    lowOwnerRawParentEndpointIncidenceCorrectionMass R p r parent

/-- **Exact support restriction.**  Summing the endpoint correction over all
raw parents is exactly the same as summing it over incomplete parents. -/
theorem lowOwnerFirstOwnerRawParentEndpointIncidenceCorrectionMass_eq_incomplete
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) :
    lowOwnerFirstOwnerRawParentEndpointIncidenceCorrectionMass R p sig r =
      lowOwnerFirstOwnerIncompleteEndpointIncidenceCorrectionMass R p sig r := by
  unfold lowOwnerFirstOwnerRawParentEndpointIncidenceCorrectionMass
    lowOwnerFirstOwnerIncompleteEndpointIncidenceCorrectionMass
    lowOwnerFirstOwnerIncompletePolarizationRawParentSet
  refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
  intro parent hparent hnot
  have hcompleted : LowOwnerCompletedPolarizationBlock R p (r, parent) := by
    by_contra hincomplete
    exact hnot (Finset.mem_filter.mpr ⟨hparent, hincomplete⟩)
  exact lowOwnerRawParentEndpointIncidenceCorrectionMass_eq_zero_of_completed
    hcompleted

/-- First-owner endpoint clip atom. -/
def lowOwnerRawParentFirstEndpointClip
    (R p : ℕ) (n : ℕ) : ℝ :=
  lowOwnerThresholdCrossingIndicator p n (squareRootEndpoint R)

/-- Returned-after-r double-corner endpoint atom. -/
def lowOwnerRawParentReturnedDoubleCorner
    (R p r : ℕ) (n : ℕ) : ℝ :=
  lowOwnerThresholdDoubleCornerBoundary
    p r n (squareRootEndpoint R)

/-- **Coordinate endpoint correction has exactly two modes.** -/
theorem lowOwnerThresholdClippedDifference_endpoint_eq_firstClip_sub_returnedDoubleCorner
    {R p r n : ℕ}
    (hp : p.Prime) (hr : r.Prime) (hpr : p < r) (hn : 0 < n) :
    lowOwnerThresholdClippedDifference
        p r n (squareRootEndpoint R) =
      lowOwnerRawParentFirstEndpointClip R p n -
        lowOwnerRawParentReturnedDoubleCorner R p r n := by
  unfold lowOwnerRawParentFirstEndpointClip
    lowOwnerRawParentReturnedDoubleCorner
  exact lowOwnerThresholdClippedDifference_eq_current_sub_doubleCorner
    hp hr hpr hn

/-- **Two-boundary normal form of one raw-parent endpoint correction.** -/
theorem lowOwnerRawParentEndpointIncidenceCorrectionMass_eq_twoBoundaryModes
    {R p r : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (hp : p.Prime)
    (hparent : parent ∈
      lowOwnerFirstOwnerPolarizationRawParentSet R p sig r) :
    lowOwnerRawParentEndpointIncidenceCorrectionMass R p r parent =
      postRootZeroTargetPairExcess parent *
        ((lowOwnerRawParentFirstEndpointClip R p parent.1 -
            lowOwnerRawParentReturnedDoubleCorner R p r parent.1) *
          lowOwnerThresholdSecondOwnerDifference R p r parent.2 +
         lowOwnerThresholdSecondOwnerDifference R p r parent.1 *
          (lowOwnerRawParentFirstEndpointClip R p parent.2 -
            lowOwnerRawParentReturnedDoubleCorner R p r parent.2) +
         (lowOwnerRawParentFirstEndpointClip R p parent.1 -
            lowOwnerRawParentReturnedDoubleCorner R p r parent.1) *
          (lowOwnerRawParentFirstEndpointClip R p parent.2 -
            lowOwnerRawParentReturnedDoubleCorner R p r parent.2)) := by
  rcases lowOwnerFirstOwnerPolarizationRawParent_data hp hparent with
    ⟨hr, hpr, haBase, hbBase, _hra, _hrb⟩
  have haCar := (Finset.mem_filter.mp haBase).1
  have hbCar := (Finset.mem_filter.mp hbBase).1
  have haPos := (lowOwnerNonzeroMobiusCarrier_squarefree_pos haCar).2
  have hbPos := (lowOwnerNonzeroMobiusCarrier_squarefree_pos hbCar).2
  unfold lowOwnerRawParentEndpointIncidenceCorrectionMass
  rw [lowOwnerThresholdClippedDifference_endpoint_eq_firstClip_sub_returnedDoubleCorner
      hp hr hpr haPos,
    lowOwnerThresholdClippedDifference_endpoint_eq_firstClip_sub_returnedDoubleCorner
      hp hr hpr hbPos]

/-- The universal signed threshold splice may therefore restrict its correction
term to the incomplete carrier exactly. -/
theorem sum_lowOwnerFirstOwnerRawParentNextPolarization_eq_threshold_add_incompleteEndpointCorrection_sub_sameBranch
    {R p r : ℕ} {sig : Finset ℕ}
    (hR : 2 ≤ R) (hp : p.Prime) :
    (∑ parent ∈ lowOwnerFirstOwnerPolarizationRawParentSet R p sig r,
      lowOwnerFirstOwnerRawParentNextPolarizationTerm R p r parent) =
      lowOwnerFirstOwnerRawParentThresholdIncidenceMass R p sig r +
        lowOwnerFirstOwnerIncompleteEndpointIncidenceCorrectionMass
          R p sig r -
        lowOwnerFirstOwnerRawParentSameBranchMass R p sig r := by
  rw [sum_lowOwnerFirstOwnerRawParentNextPolarization_eq_threshold_add_endpointCorrection_sub_sameBranch
    hR hp]
  rw [lowOwnerFirstOwnerRawParentEndpointIncidenceCorrectionMass_eq_incomplete]

end RHLean.Proof
