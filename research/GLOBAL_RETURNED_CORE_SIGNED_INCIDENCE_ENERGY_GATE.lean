import Mathlib
import «research.GLOBAL_RETURNED_CORE_RAW_PARENT_ORBIT_PARTITION»
import «research.GLOBAL_RETURNED_CORE_COMPLETED_POLARIZATION_AGGREGATE»
import «research.GLOBAL_RETURNED_CORE_THRESHOLD_FOUR_CORNER_ENERGY_BRIDGE»

/-!
# Signed polarization stays upstream of the incidence-energy gate

The induction state in the returned-core argument is the signed Dirichlet
polarization ledger.  Reciprocal energy is not that state.  It is a downstream
currency available only for the completed incidence summand after an exact
four-corner identification.

This file records that separation literally.

For one first-owner cell `(p,sig)` and one next owner `r`, restrict the existing
raw-parent set to those parents whose full p/r cube is completed.  On that set:

* the signed cube is exactly incidence minus the two signed same-branch cubes;
* only the incidence four-corner is squared and identified with owner-labelled
  reciprocal parent energy;
* the existing `2/9` theorem is then applied once per completed raw parent.

The same-branch polarization ledger is not converted to energy here, and no
rank recurrence is stated.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Raw parents under the current full-polarization owner fibre whose complete
four-corner is fully physical in the sense required by the #738 currency
identity. -/
def lowOwnerFirstOwnerCompletedPolarizationRawParentSet
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : Finset (ℕ × ℕ) :=
  (lowOwnerFirstOwnerPolarizationRawParentSet R p sig r).filter fun parent =>
    LowOwnerCompletedPolarizationBlock R p (r, parent)

/-- Membership exposes both the raw-parent origin and the completed-cube
hypotheses. -/
theorem mem_lowOwnerFirstOwnerCompletedPolarizationRawParentSet
    {R p r : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ} :
    parent ∈ lowOwnerFirstOwnerCompletedPolarizationRawParentSet R p sig r ↔
      parent ∈ lowOwnerFirstOwnerPolarizationRawParentSet R p sig r ∧
        LowOwnerCompletedPolarizationBlock R p (r, parent) := by
  simp [lowOwnerFirstOwnerCompletedPolarizationRawParentSet]

/-- An occurring completed raw parent has exactly the arithmetic data needed by
both the signed currency identity and the reciprocal-energy gate. -/
theorem lowOwnerFirstOwnerCompletedPolarizationRawParent_data
    {R p r : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (hp : p.Prime)
    (hparent : parent ∈
      lowOwnerFirstOwnerCompletedPolarizationRawParentSet R p sig r) :
    r.Prime ∧ p < r ∧
      ¬ r ∣ parent.1 ∧ ¬ r ∣ parent.2 ∧
      0 < parent.1 ∧ 0 < parent.2 := by
  rcases (mem_lowOwnerFirstOwnerCompletedPolarizationRawParentSet.mp hparent) with
    ⟨hraw, hcomplete⟩
  rcases Finset.mem_image.mp hraw with ⟨child, hchild, hrawEq⟩
  have hcell :=
    lowOwnerFirstOwnerPolarization_child_rawParent_mem_same_cell hp hchild
  have hfree := lowOwnerFirstOwnerPolarization_child_rawParent_not_dvd hchild
  have hcell' :
      parent.1 ∈ lowOwnerFirstOwnerBaseFiber R p sig ∧
        parent.2 ∈ lowOwnerFirstOwnerBaseFiber R p sig := by
    simpa [hrawEq] using hcell
  have hfree' : ¬ r ∣ parent.1 ∧ ¬ r ∣ parent.2 := by
    simpa [hrawEq] using hfree
  have hpaCar := (Finset.mem_filter.mp hcell'.1).1
  have hpbCar := (Finset.mem_filter.mp hcell'.2).1
  have haPos := (lowOwnerNonzeroMobiusCarrier_squarefree_pos hpaCar).2
  have hbPos := (lowOwnerNonzeroMobiusCarrier_squarefree_pos hpbCar).2
  rcases child with ⟨m, n⟩
  rcases Finset.mem_filter.mp hchild with ⟨hoff, howner⟩
  rcases Finset.mem_filter.mp hoff with ⟨hprod, _hne⟩
  rcases Finset.mem_product.mp hprod with ⟨hmBase, hnBase⟩
  have hpr :=
    lowOwnerFirstOwnerBasePair_freshPrime_gt_owner hp hmBase hnBase howner.1
  have hr : r.Prime := by
    have hmCar := (Finset.mem_filter.mp hmBase).1
    have hnCar := (Finset.mem_filter.mp hnBase).1
    exact (freshPrime_of_nonzeroPhysicalPair hmCar hnCar howner.1).1
  exact ⟨hr, hpr, hfree'.1, hfree'.2, haPos, hbPos⟩

/-- Signed completed-cube mass on the orbit-covered completed raw parents. -/
def lowOwnerFirstOwnerCompletedSignedCubeMass
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : ℝ :=
  ∑ parent ∈ lowOwnerFirstOwnerCompletedPolarizationRawParentSet R p sig r,
    lowOwnerCompletedPolarizationCubeMass R p (r, parent)

/-- The incidence summand of the same completed signed cubes.  It is still a
signed bilinear quantity at this point. -/
def lowOwnerFirstOwnerCompletedIncidenceGateMass
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : ℝ :=
  ∑ parent ∈ lowOwnerFirstOwnerCompletedPolarizationRawParentSet R p sig r,
    lowOwnerCompletedIncidenceFourCornerMass R p (r, parent)

/-- The base+returned same-branch summand.  This remains in signed amplitude
space and is not sent through the reciprocal-energy gate. -/
def lowOwnerFirstOwnerCompletedSameBranchMass
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : ℝ :=
  ∑ parent ∈ lowOwnerFirstOwnerCompletedPolarizationRawParentSet R p sig r,
    lowOwnerCompletedSameBranchFourCornerMass R p (r, parent)

/-- **Exact signed gate split.**  No estimate and no squaring: the completed
polarization is incidence minus same-branch. -/
theorem lowOwnerFirstOwnerCompletedSignedCubeMass_eq_incidence_sub_sameBranch
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) :
    lowOwnerFirstOwnerCompletedSignedCubeMass R p sig r =
      lowOwnerFirstOwnerCompletedIncidenceGateMass R p sig r -
        lowOwnerFirstOwnerCompletedSameBranchMass R p sig r := by
  unfold lowOwnerFirstOwnerCompletedSignedCubeMass
    lowOwnerFirstOwnerCompletedIncidenceGateMass
    lowOwnerFirstOwnerCompletedSameBranchMass
  calc
    (∑ parent ∈ lowOwnerFirstOwnerCompletedPolarizationRawParentSet R p sig r,
      lowOwnerCompletedPolarizationCubeMass R p (r, parent)) =
        ∑ parent ∈ lowOwnerFirstOwnerCompletedPolarizationRawParentSet R p sig r,
          (lowOwnerCompletedIncidenceFourCornerMass R p (r, parent) -
            lowOwnerCompletedSameBranchFourCornerMass R p (r, parent)) := by
      apply Finset.sum_congr rfl
      intro parent hparent
      exact lowOwnerCompletedPolarizationCubeMass_eq_incidence_sub_sameBranch
        (mem_lowOwnerFirstOwnerCompletedPolarizationRawParentSet.mp hparent).2
    _ = _ := by rw [Finset.sum_sub_distrib]

/-- Nonnegative currency after the gate: square only the completed incidence
four-corner, parent by parent. -/
def lowOwnerFirstOwnerCompletedIncidenceGateSquareMass
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : ℝ :=
  ∑ parent ∈ lowOwnerFirstOwnerCompletedPolarizationRawParentSet R p sig r,
    (lowOwnerCompletedIncidenceFourCornerMass R p (r, parent)) ^ 2

/-- Matching owner-labelled reciprocal parent energy. -/
def lowOwnerFirstOwnerCompletedOwnerParentEnergy
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : ℝ :=
  ∑ parent ∈ lowOwnerFirstOwnerCompletedPolarizationRawParentSet R p sig r,
    lowOwnerThresholdEulerParentEnergy R p r parent

/-- **The gate dictionary.**  Only the completed incidence square crosses from
signed polarization into reciprocal energy. -/
theorem lowOwnerFirstOwnerCompletedIncidenceGateSquareMass_eq_ownerParentEnergy
    {R p r : ℕ} {sig : Finset ℕ}
    (hp : p.Prime) :
    lowOwnerFirstOwnerCompletedIncidenceGateSquareMass R p sig r =
      lowOwnerFirstOwnerCompletedOwnerParentEnergy R p sig r := by
  unfold lowOwnerFirstOwnerCompletedIncidenceGateSquareMass
    lowOwnerFirstOwnerCompletedOwnerParentEnergy
  apply Finset.sum_congr rfl
  intro parent hparent
  rcases lowOwnerFirstOwnerCompletedPolarizationRawParent_data hp hparent with
    ⟨hr, _hpr, hra, hrb, haPos, hbPos⟩
  simpa [lowOwnerCompletedIncidenceFourCornerMass] using
    (lowOwnerThresholdIncidence_fourCorner_sq_eq_eulerParentEnergy
      (R := R) (p := p) (r := r)
      (a := parent.1) (b := parent.2)
      hr hra hrb haPos hbPos)

/-- Inherited reciprocal energy generated from the completed raw-parent blocks.
This object is downstream of the gate; it is not the signed induction state. -/
def lowOwnerFirstOwnerCompletedInheritedReciprocalEnergy
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : ℝ :=
  ∑ parent ∈ lowOwnerFirstOwnerCompletedPolarizationRawParentSet R p sig r,
    ∑ child ∈ lowOwnerGreatestOwnerFixedParentChildFiber R parent r,
      lowOwnerThresholdEulerInheritedGreatestChildEnergy R p r parent child

/-- **Apply `2/9` exactly once per completed raw parent.**  The right side is
only the square-mass of the completed incidence summand.  No signed survivor or
full polarization term appears here. -/
theorem lowOwnerFirstOwnerCompletedInheritedReciprocalEnergy_le_two_ninths_gateSquare
    {R p r : ℕ} {sig : Finset ℕ}
    (hp : p.Prime) :
    lowOwnerFirstOwnerCompletedInheritedReciprocalEnergy R p sig r ≤
      (2 / 9 : ℝ) *
        lowOwnerFirstOwnerCompletedIncidenceGateSquareMass R p sig r := by
  unfold lowOwnerFirstOwnerCompletedInheritedReciprocalEnergy
    lowOwnerFirstOwnerCompletedIncidenceGateSquareMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro parent hparent
  rcases lowOwnerFirstOwnerCompletedPolarizationRawParent_data hp hparent with
    ⟨hr, hpr, hra, hrb, haPos, hbPos⟩
  simpa [lowOwnerCompletedIncidenceFourCornerMass] using
    (sum_lowOwnerThresholdEulerInheritedGreatestChildEnergy_le_two_ninths_fourCorner
      (R := R) (p := p) (r := r)
      (a := parent.1) (b := parent.2)
      hp hr hpr hra hrb haPos hbPos)

end RHLean.Proof
