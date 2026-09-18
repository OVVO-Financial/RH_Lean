import Mathlib
import «research.GLOBAL_RETURNED_CORE_RAW_PARENT_BOUNDARY_NORMAL_FORM»
import «research.GLOBAL_RETURNED_CORE_THRESHOLD_DOUBLE_CORNER_RECIPROCAL»

/-!
# Reciprocal coordinates for the three raw-parent boundary sectors

The signed incomplete-boundary Fubini has already separated one descending
owner layer into three chronological physical exit classes.  This file maps
those classes to the existing reciprocal/Dirichlet coordinates *before* any
norm or triangle inequality.

* first-owner clipping makes the returned p-coordinate literally zero under
  the physical Dirichlet extension, so p-incidence equals the base coordinate;
* next-owner clipping makes the moved r-coordinate a one-ended Euler edge;
* returned-after-r clipping is exactly the p/r double-corner event, and the
  already-compiled critical covariance four-corner is therefore exactly
  `-1/r` times the parent target-zero excess.

Thus the three named boundary sectors do not introduce new analytic objects.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- A left first-owner clip kills the returned p-coordinate exactly. -/
theorem lowOwnerRawParentFirstOwnerClipped_left_returnedCoefficient_eq_zero
    {R p r : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (_hp : p.Prime)
    (_hraw : parent ∈ lowOwnerFirstOwnerPolarizationRawParentSet R p sig r)
    (hleft : squareRootEndpoint R < p * parent.1) :
    lowOwnerDirichletReturnedCoefficient R p parent.1 = 0 := by
  unfold lowOwnerDirichletReturnedCoefficient
  exact lowOwnerPhysicalDirichletWeight_eq_zero_of_lt hleft

/-- Hence on a left first-owner clip the p-incidence is just the base
coordinate. -/
theorem lowOwnerRawParentFirstOwnerClipped_left_incidence_eq_base
    {R p r : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (hp : p.Prime)
    (hraw : parent ∈ lowOwnerFirstOwnerPolarizationRawParentSet R p sig r)
    (hleft : squareRootEndpoint R < p * parent.1) :
    lowOwnerDirichletIncidenceCoefficient R p parent.1 =
      lowOwnerDirichletBaseCoefficient R parent.1 := by
  unfold lowOwnerDirichletIncidenceCoefficient
  rw [lowOwnerRawParentFirstOwnerClipped_left_returnedCoefficient_eq_zero
    hp hraw hleft]
  ring

/-- Symmetric first-owner clip on the second coordinate. -/
theorem lowOwnerRawParentFirstOwnerClipped_right_incidence_eq_base
    {R p r : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (_hp : p.Prime)
    (_hraw : parent ∈ lowOwnerFirstOwnerPolarizationRawParentSet R p sig r)
    (hright : squareRootEndpoint R < p * parent.2) :
    lowOwnerDirichletIncidenceCoefficient R p parent.2 =
      lowOwnerDirichletBaseCoefficient R parent.2 := by
  unfold lowOwnerDirichletIncidenceCoefficient
    lowOwnerDirichletReturnedCoefficient
  rw [lowOwnerPhysicalDirichletWeight_eq_zero_of_lt hright]
  ring

/-- A left next-owner physical exit is exactly the one-ended critical Euler
edge: the r-child contributes zero. -/
theorem lowOwnerRawParentNextOwnerClipped_left_criticalEuler_eq_parent
    {R p r : ℕ} {parent : ℕ × ℕ}
    (hR : 2 ≤ R) (hp : p.Prime)
    (hleft : squareRootEndpoint R < r * parent.1) :
    lowOwnerThresholdCriticalEulerDifference R p r parent.1 =
      lowOwnerThresholdOwnerEulerWeight R p parent.1 := by
  exact lowOwnerThresholdCriticalEulerDifference_eq_parent_of_next_clipped
    hR hp.one_le hleft

/-- Symmetric one-ended Euler edge on the second coordinate. -/
theorem lowOwnerRawParentNextOwnerClipped_right_criticalEuler_eq_parent
    {R p r : ℕ} {parent : ℕ × ℕ}
    (hR : 2 ≤ R) (hp : p.Prime)
    (hright : squareRootEndpoint R < r * parent.2) :
    lowOwnerThresholdCriticalEulerDifference R p r parent.2 =
      lowOwnerThresholdOwnerEulerWeight R p parent.2 := by
  exact lowOwnerThresholdCriticalEulerDifference_eq_parent_of_next_clipped
    hR hp.one_le hright

/-- A returned-after-r clip on the left is literally the p/r double-corner
indicator at the physical endpoint. -/
theorem lowOwnerRawParentReturnedNextClipped_left_doubleCorner_eq_one
    {R p r : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (hp : p.Prime)
    (hraw : parent ∈ lowOwnerFirstOwnerPolarizationRawParentSet R p sig r)
    (hclip : LowOwnerRawParentReturnedNextClipped R p r parent)
    (hleft : squareRootEndpoint R < p * (r * parent.1)) :
    lowOwnerThresholdDoubleCornerBoundary
        p r parent.1 (squareRootEndpoint R) = 1 := by
  rcases lowOwnerFirstOwnerPolarizationRawParent_data hp hraw with
    ⟨_hr, _hpr, _haBase, _hbBase, _hra, _hrb⟩
  have hdouble :
      squareRootEndpoint R < r * (p * parent.1) := by
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hleft
  unfold lowOwnerThresholdDoubleCornerBoundary
  simp [hclip.1, hclip.2.2.1, hdouble]

/-- Symmetric returned-after-r double-corner indicator on the right. -/
theorem lowOwnerRawParentReturnedNextClipped_right_doubleCorner_eq_one
    {R p r : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (hp : p.Prime)
    (hraw : parent ∈ lowOwnerFirstOwnerPolarizationRawParentSet R p sig r)
    (hclip : LowOwnerRawParentReturnedNextClipped R p r parent)
    (hright : squareRootEndpoint R < p * (r * parent.2)) :
    lowOwnerThresholdDoubleCornerBoundary
        p r parent.2 (squareRootEndpoint R) = 1 := by
  rcases lowOwnerFirstOwnerPolarizationRawParent_data hp hraw with
    ⟨_hr, _hpr, _haBase, _hbBase, _hra, _hrb⟩
  have hdouble :
      squareRootEndpoint R < r * (p * parent.2) := by
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hright
  unfold lowOwnerThresholdDoubleCornerBoundary
  simp [hclip.2.1, hclip.2.2.2.1, hdouble]

/-- **Exact reciprocal left double-corner.**  A returned-after-r clipped raw
parent emits the already-compiled critical covariance atom with coefficient
`-1/r`, not a new boundary coefficient. -/
theorem lowOwnerRawParentReturnedNextClipped_left_criticalFourCorner_eq_neg_reciprocal
    {R p r : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (hp : p.Prime)
    (hraw : parent ∈ lowOwnerFirstOwnerPolarizationRawParentSet R p sig r)
    (hclip : LowOwnerRawParentReturnedNextClipped R p r parent)
    (hleft : squareRootEndpoint R < p * (r * parent.1)) :
    zeroTargetMellinPhysicalSuperLcmFourCorner (squareRootEndpoint R) r
        (zeroTargetCriticalOwnerRatio r) parent.1 (p * parent.1) =
      -(1 / (r : ℝ)) *
        postRootZeroTargetPairExcess (parent.1, p * parent.1) := by
  rcases lowOwnerFirstOwnerPolarizationRawParent_data hp hraw with
    ⟨hr, hpr, haBase, _hbBase, hra, _hrb⟩
  have haCar := (Finset.mem_filter.mp haBase).1
  have haPos := (lowOwnerNonzeroMobiusCarrier_squarefree_pos haCar).2
  have hdouble :=
    lowOwnerRawParentReturnedNextClipped_left_doubleCorner_eq_one
      hp hraw hclip hleft
  exact zeroTargetCriticalFourCorner_of_doubleCornerIndicator
    hp hr hpr haPos hra hdouble

/-- Symmetric exact reciprocal double-corner on the second coordinate. -/
theorem lowOwnerRawParentReturnedNextClipped_right_criticalFourCorner_eq_neg_reciprocal
    {R p r : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (hp : p.Prime)
    (hraw : parent ∈ lowOwnerFirstOwnerPolarizationRawParentSet R p sig r)
    (hclip : LowOwnerRawParentReturnedNextClipped R p r parent)
    (hright : squareRootEndpoint R < p * (r * parent.2)) :
    zeroTargetMellinPhysicalSuperLcmFourCorner (squareRootEndpoint R) r
        (zeroTargetCriticalOwnerRatio r) parent.2 (p * parent.2) =
      -(1 / (r : ℝ)) *
        postRootZeroTargetPairExcess (parent.2, p * parent.2) := by
  rcases lowOwnerFirstOwnerPolarizationRawParent_data hp hraw with
    ⟨hr, hpr, _haBase, hbBase, _hra, hrb⟩
  have hbCar := (Finset.mem_filter.mp hbBase).1
  have hbPos := (lowOwnerNonzeroMobiusCarrier_squarefree_pos hbCar).2
  have hdouble :=
    lowOwnerRawParentReturnedNextClipped_right_doubleCorner_eq_one
      hp hraw hclip hright
  exact zeroTargetCriticalFourCorner_of_doubleCornerIndicator
    hp hr hpr hbPos hrb hdouble

end RHLean.Proof
