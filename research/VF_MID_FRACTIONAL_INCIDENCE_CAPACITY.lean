import Mathlib
import «research.VF_MID_FIRST_BAD_AFFINE_OWNER_SPLICE»
import «research.GLOBAL_RETURNED_CORE_EMITTED_RECIPROCAL_CHARGE»

/-!
# VF fractional reciprocal incidence capacity

This file records the legal fractional-capacity replacement for an invalid
cardinality inheritance step.

A localized packet does not inherit a fraction of a macroscopic signed square
from its cardinality.  Once the signed returned-core descent reaches a completed
incidence gate, however, the packet has crossed into a nonnegative reciprocal
parent ledger.  On that ledger restriction is monotone, so the active completed
parents carry an exact fraction of the full completed incidence square.

The fraction below is therefore defined from the actual reciprocal energy, not
from the number of seats.  It remains attached to the literal active completed
parent set and the literal Euler coefficient.  The #888 selection-stable quarter
contraction can then be applied without enlarging the selected carrier.

No prior-good endpoint bound, packet-to-full-scale inheritance, triangle
inequality on a signed packet, or new analytic hypothesis is used here.
-/

noncomputable section
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

open RHLean.Arithmetic RHLean.Proof

attribute [local instance] Classical.propDecidable

/-- Reciprocal parent energy on exactly the active completed raw parents of one
`(p,sig,r)` gate packet, with the actual threshold-Euler coefficient retained. -/
def vfMidCompletedGateSelectedParentEnergy
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : ℝ :=
  vfMidSelectedReciprocalParentEnergy
    (lowOwnerFirstOwnerActiveCompletedPolarizationRawParentSet R p sig r)
    (lowOwnerThresholdEulerPairCoefficient R p r)

/-- The selected parent energy is literally the owner-labelled Euler parent
energy on the active completed parent set. -/
theorem vfMidCompletedGateSelectedParentEnergy_eq_activeOwnerParentEnergy
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) :
    vfMidCompletedGateSelectedParentEnergy R p sig r =
      ∑ parent ∈
        lowOwnerFirstOwnerActiveCompletedPolarizationRawParentSet R p sig r,
        lowOwnerThresholdEulerParentEnergy R p r parent := by
  rfl

@[simp] theorem vfMidCompletedGateSelectedParentEnergy_nonneg
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) :
    0 ≤ vfMidCompletedGateSelectedParentEnergy R p sig r := by
  unfold vfMidCompletedGateSelectedParentEnergy
    vfMidSelectedReciprocalParentEnergy
  apply Finset.sum_nonneg
  intro parent _hparent
  exact mul_nonneg
    (sq_nonneg (lowOwnerThresholdEulerPairCoefficient R p r parent))
    (postRootCovarianceReciprocalPairEnergy_nonneg parent)

/-- **Legal subset-capacity comparison.**

The active completed packet is a literal subset of the completed gate parent
set.  Since reciprocal parent energy is nonnegative, its selected energy is at
most the full completed incidence square.  This is the valid positive-currency
replacement for a cardinality-fraction inheritance claim. -/
theorem vfMidCompletedGateSelectedParentEnergy_le_incidenceGateSquare
    {R p r : ℕ} {sig : Finset ℕ}
    (hp : p.Prime) :
    vfMidCompletedGateSelectedParentEnergy R p sig r ≤
      lowOwnerFirstOwnerCompletedIncidenceGateSquareMass R p sig r := by
  rw [lowOwnerFirstOwnerCompletedIncidenceGateSquareMass_eq_ownerParentEnergy hp]
  unfold vfMidCompletedGateSelectedParentEnergy
    vfMidSelectedReciprocalParentEnergy
    lowOwnerFirstOwnerCompletedOwnerParentEnergy
    lowOwnerThresholdEulerParentEnergy
  have hsub :
      lowOwnerFirstOwnerActiveCompletedPolarizationRawParentSet R p sig r ⊆
        lowOwnerFirstOwnerCompletedPolarizationRawParentSet R p sig r := by
    intro parent hparent
    exact (Finset.mem_filter.mp hparent).1
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub
    (by
      intro parent _hparent _hnot
      exact mul_nonneg
        (sq_nonneg (lowOwnerThresholdEulerPairCoefficient R p r parent))
        (postRootCovarianceReciprocalPairEnergy_nonneg parent))

@[simp] theorem lowOwnerFirstOwnerCompletedIncidenceGateSquareMass_nonneg_local
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) :
    0 ≤ lowOwnerFirstOwnerCompletedIncidenceGateSquareMass R p sig r := by
  unfold lowOwnerFirstOwnerCompletedIncidenceGateSquareMass
  apply Finset.sum_nonneg
  intro parent _hparent
  exact sq_nonneg _

/-- Exact reciprocal-energy share of the full completed incidence gate carried
by the active selected parent packet.  The zero-gate case is assigned fraction
zero. -/
def vfMidCompletedGateActiveCapacityFraction
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : ℝ :=
  if lowOwnerFirstOwnerCompletedIncidenceGateSquareMass R p sig r = 0 then
    0
  else
    vfMidCompletedGateSelectedParentEnergy R p sig r /
      lowOwnerFirstOwnerCompletedIncidenceGateSquareMass R p sig r

@[simp] theorem vfMidCompletedGateActiveCapacityFraction_nonneg
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) :
    0 ≤ vfMidCompletedGateActiveCapacityFraction R p sig r := by
  unfold vfMidCompletedGateActiveCapacityFraction
  split_ifs with hzero
  · norm_num
  · exact div_nonneg
      (vfMidCompletedGateSelectedParentEnergy_nonneg R p sig r)
      (lowOwnerFirstOwnerCompletedIncidenceGateSquareMass_nonneg_local
        R p sig r)

theorem vfMidCompletedGateActiveCapacityFraction_le_one
    {R p r : ℕ} {sig : Finset ℕ}
    (hp : p.Prime) :
    vfMidCompletedGateActiveCapacityFraction R p sig r ≤ 1 := by
  have hgate0 :
      0 ≤ lowOwnerFirstOwnerCompletedIncidenceGateSquareMass R p sig r :=
    lowOwnerFirstOwnerCompletedIncidenceGateSquareMass_nonneg_local R p sig r
  unfold vfMidCompletedGateActiveCapacityFraction
  split_ifs with hzero
  · norm_num
  · have hgatePos :
        0 < lowOwnerFirstOwnerCompletedIncidenceGateSquareMass R p sig r :=
      lt_of_le_of_ne hgate0 (Ne.symm hzero)
    apply (div_le_iff₀ hgatePos).2
    simpa using
      vfMidCompletedGateSelectedParentEnergy_le_incidenceGateSquare
        (R := R) (p := p) (r := r) (sig := sig) hp

/-- **Exact fractional reconstruction.**

The reciprocal capacity fraction times the full gate square is exactly the
selected active-parent energy.  In the zero-gate case monotonicity forces the
selected energy itself to vanish. -/
theorem vfMidCompletedGateActiveCapacityFraction_mul_gate_eq_selected
    {R p r : ℕ} {sig : Finset ℕ}
    (hp : p.Prime) :
    vfMidCompletedGateActiveCapacityFraction R p sig r *
        lowOwnerFirstOwnerCompletedIncidenceGateSquareMass R p sig r =
      vfMidCompletedGateSelectedParentEnergy R p sig r := by
  have hsel0 :
      0 ≤ vfMidCompletedGateSelectedParentEnergy R p sig r :=
    vfMidCompletedGateSelectedParentEnergy_nonneg R p sig r
  have hselLe :=
    vfMidCompletedGateSelectedParentEnergy_le_incidenceGateSquare
      (R := R) (p := p) (r := r) (sig := sig) hp
  unfold vfMidCompletedGateActiveCapacityFraction
  split_ifs with hzero
  · have hselEq :
        vfMidCompletedGateSelectedParentEnergy R p sig r = 0 := by
      rw [hzero] at hselLe
      linarith
    rw [hzero, hselEq]
    norm_num
  · exact div_mul_cancel₀ _ hzero

/-- The #888 selected clipped-exit ledger specialized to the active completed
gate parents and the literal threshold-Euler coefficient. -/
def vfMidCompletedGateSelectedClippedOutgoingEnergy
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : ℝ :=
  vfMidSelectedClippedOutgoingEnergy R r
    (lowOwnerFirstOwnerActiveCompletedPolarizationRawParentSet R p sig r)
    (lowOwnerThresholdEulerPairCoefficient R p r)

/-- **Fractional incidence-capacity contraction.**

The genuine clipped outgoing energy of one active completed packet costs at
most one quarter of its exact reciprocal capacity fraction of the full completed
incidence square.  No seat cardinality appears. -/
theorem vfMidCompletedGateSelectedClippedOutgoingEnergy_le_fractionalGate
    {R p r : ℕ} {sig : Finset ℕ}
    (hp : p.Prime) (hr : r.Prime) :
    vfMidCompletedGateSelectedClippedOutgoingEnergy R p sig r ≤
      (1 / 4 : ℝ) *
        (vfMidCompletedGateActiveCapacityFraction R p sig r *
          lowOwnerFirstOwnerCompletedIncidenceGateSquareMass R p sig r) := by
  have hquarter :=
    vfMidSelectedClippedOutgoingEnergy_le_quarter
      (R := R) (first := r) hr
      (lowOwnerFirstOwnerActiveCompletedPolarizationRawParentSet R p sig r)
      (lowOwnerThresholdEulerPairCoefficient R p r)
  have hreconstruct :=
    vfMidCompletedGateActiveCapacityFraction_mul_gate_eq_selected
      (R := R) (p := p) (r := r) (sig := sig) hp
  unfold vfMidCompletedGateSelectedClippedOutgoingEnergy at *
  rw [hreconstruct]
  exact hquarter

/-- External-budget form of the same legal fractional inheritance.  Any future
bound on the *full completed incidence square* may be inherited by the selected
packet only after multiplication by its exact reciprocal capacity fraction. -/
theorem vfMidCompletedGateSelectedClippedOutgoingEnergy_le_fractionalBudget
    {R p r : ℕ} {sig : Finset ℕ} {B : ℝ}
    (hp : p.Prime) (hr : r.Prime)
    (hgate :
      lowOwnerFirstOwnerCompletedIncidenceGateSquareMass R p sig r ≤ B) :
    vfMidCompletedGateSelectedClippedOutgoingEnergy R p sig r ≤
      (1 / 4 : ℝ) *
        (vfMidCompletedGateActiveCapacityFraction R p sig r * B) := by
  have hfrac :=
    vfMidCompletedGateSelectedClippedOutgoingEnergy_le_fractionalGate
      (R := R) (p := p) (r := r) (sig := sig) hp hr
  have hfrac0 :
      0 ≤ vfMidCompletedGateActiveCapacityFraction R p sig r :=
    vfMidCompletedGateActiveCapacityFraction_nonneg R p sig r
  have hscaled :
      vfMidCompletedGateActiveCapacityFraction R p sig r *
          lowOwnerFirstOwnerCompletedIncidenceGateSquareMass R p sig r ≤
        vfMidCompletedGateActiveCapacityFraction R p sig r * B :=
    mul_le_mul_of_nonneg_left hgate hfrac0
  exact hfrac.trans
    (mul_le_mul_of_nonneg_left hscaled (by norm_num : (0 : ℝ) ≤ 1 / 4))

end RHLean.Analysis
