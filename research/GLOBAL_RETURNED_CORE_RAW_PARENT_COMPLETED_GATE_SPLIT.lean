import Mathlib
import «research.GLOBAL_RETURNED_CORE_RAW_PARENT_INERT_DIAGONAL_BOUND»
import «research.GLOBAL_RETURNED_CORE_SIGNED_INCIDENCE_ENERGY_GATE»

/-!
# Exact completed/incomplete split of the descending raw-parent recursion

After the raw-parent orbit and inert-owner Fubini identities, the only active
current-owner term is the next-polarization scalar on occurring raw parents.
This file partitions those parents at the already-defined completed incidence
energy gate.

On a completed raw parent, the next-polarization term is literally the full
Dirichlet four-corner cube, hence exactly

  incidence four-corner - same-branch four-corners.

The complement is retained as one signed `incomplete` raw-parent ledger.  It is
not normed or bounded here.  Thus the first legal one-sided descending estimate
has the shape

  current <= completed incidence
             - completed same-branch
             + incomplete signed boundary
             + strictly-lower owner fibres.

Only the completed incidence summand is now eligible for the existing `2/9`
energy gate.  No square, triangle inequality, or RH-strength assumption is
introduced in this file.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Signed next-polarization atom carried by one stripped raw parent. -/
def lowOwnerFirstOwnerRawParentNextPolarizationTerm
    (R p r : ℕ) (parent : ℕ × ℕ) : ℝ :=
  realMoebiusStep parent.1 * realMoebiusStep parent.2 *
    lowOwnerDirichletNextPolarizationScalar R p r parent.1 parent.2

/-- Occurring raw parents which do not form a fully physical completed p/r
block.  No classification of the failure is made yet. -/
def lowOwnerFirstOwnerIncompletePolarizationRawParentSet
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : Finset (ℕ × ℕ) :=
  (lowOwnerFirstOwnerPolarizationRawParentSet R p sig r).filter fun parent =>
    ¬ LowOwnerCompletedPolarizationBlock R p (r, parent)

/-- Exact partition of the raw-parent next-polarization sum into completed and
incomplete signed ledgers. -/
theorem sum_lowOwnerFirstOwnerRawParentNextPolarization_eq_completed_add_incomplete
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) :
    (∑ parent ∈ lowOwnerFirstOwnerPolarizationRawParentSet R p sig r,
      lowOwnerFirstOwnerRawParentNextPolarizationTerm R p r parent) =
      (∑ parent ∈ lowOwnerFirstOwnerCompletedPolarizationRawParentSet R p sig r,
        lowOwnerFirstOwnerRawParentNextPolarizationTerm R p r parent) +
      ∑ parent ∈ lowOwnerFirstOwnerIncompletePolarizationRawParentSet R p sig r,
        lowOwnerFirstOwnerRawParentNextPolarizationTerm R p r parent := by
  unfold lowOwnerFirstOwnerCompletedPolarizationRawParentSet
    lowOwnerFirstOwnerIncompletePolarizationRawParentSet
  simpa only using
    (Finset.sum_filter_add_sum_filter_not
      (s := lowOwnerFirstOwnerPolarizationRawParentSet R p sig r)
      (p := fun parent : ℕ × ℕ =>
        LowOwnerCompletedPolarizationBlock R p (r, parent))
      (f := fun parent =>
        lowOwnerFirstOwnerRawParentNextPolarizationTerm R p r parent)).symm

/-- On a completed occurring raw parent, the signed next-polarization atom is
exactly the completed four-corner polarization cube. -/
theorem lowOwnerFirstOwnerRawParentNextPolarizationTerm_eq_completedCubeMass
    {R p r : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (hp : p.Prime)
    (hparent : parent ∈
      lowOwnerFirstOwnerCompletedPolarizationRawParentSet R p sig r) :
    lowOwnerFirstOwnerRawParentNextPolarizationTerm R p r parent =
      lowOwnerCompletedPolarizationCubeMass R p (r, parent) := by
  rcases lowOwnerFirstOwnerCompletedPolarizationRawParent_data hp hparent with
    ⟨hr, _hpr, hra, hrb, _haPos, _hbPos⟩
  unfold lowOwnerFirstOwnerRawParentNextPolarizationTerm
    lowOwnerCompletedPolarizationCubeMass
  dsimp
  symm
  exact lowOwnerDirichletPolarization_fourCorner_eq_nextPolarization
    (R := R) (p := p) hr hra hrb

/-- Aggregate completed next-polarization mass is exactly the signed completed
cube mass already used by the incidence-energy gate. -/
theorem sum_lowOwnerFirstOwnerCompletedRawParentNextPolarization_eq_signedCubeMass
    {R p r : ℕ} {sig : Finset ℕ} (hp : p.Prime) :
    (∑ parent ∈ lowOwnerFirstOwnerCompletedPolarizationRawParentSet R p sig r,
      lowOwnerFirstOwnerRawParentNextPolarizationTerm R p r parent) =
      lowOwnerFirstOwnerCompletedSignedCubeMass R p sig r := by
  unfold lowOwnerFirstOwnerCompletedSignedCubeMass
  apply Finset.sum_congr rfl
  intro parent hparent
  exact lowOwnerFirstOwnerRawParentNextPolarizationTerm_eq_completedCubeMass
    hp hparent

/-- **Exact completed-gate splice.**  The whole raw-parent next-polarization
sum is completed incidence minus completed same-branch, plus the untouched
incomplete signed boundary ledger. -/
theorem sum_lowOwnerFirstOwnerRawParentNextPolarization_eq_gate_sub_sameBranch_add_incomplete
    {R p r : ℕ} {sig : Finset ℕ} (hp : p.Prime) :
    (∑ parent ∈ lowOwnerFirstOwnerPolarizationRawParentSet R p sig r,
      lowOwnerFirstOwnerRawParentNextPolarizationTerm R p r parent) =
      lowOwnerFirstOwnerCompletedIncidenceGateMass R p sig r -
        lowOwnerFirstOwnerCompletedSameBranchMass R p sig r +
      ∑ parent ∈ lowOwnerFirstOwnerIncompletePolarizationRawParentSet R p sig r,
        lowOwnerFirstOwnerRawParentNextPolarizationTerm R p r parent := by
  rw [sum_lowOwnerFirstOwnerRawParentNextPolarization_eq_completed_add_incomplete]
  rw [sum_lowOwnerFirstOwnerCompletedRawParentNextPolarization_eq_signedCubeMass hp]
  rw [lowOwnerFirstOwnerCompletedSignedCubeMass_eq_incidence_sub_sameBranch]

/-- **Descending signed recursion at the energy gate.**  The favorable inert
diagonal has already been removed.  The completed incidence is now isolated,
while same-branch, incomplete-boundary, and strictly-lower-owner terms remain
signed and upstream of any energy estimate. -/
theorem lowOwnerFirstOwnerRevealedPolarizationEnergy_descending_le_gate_sub_sameBranch_add_incomplete_add_lowerOwners
    {R p r : ℕ} {sig : Finset ℕ}
    (hp : p.Prime) (hr : r.Prime) (hpr : p < r) :
    lowOwnerFirstOwnerRevealedPolarizationEnergy R p sig
        (lowOwnerRevealedPrimesAbove R r) ≤
      lowOwnerFirstOwnerCompletedIncidenceGateMass R p sig r -
        lowOwnerFirstOwnerCompletedSameBranchMass R p sig r +
      (∑ parent ∈ lowOwnerFirstOwnerIncompletePolarizationRawParentSet R p sig r,
        lowOwnerFirstOwnerRawParentNextPolarizationTerm R p r parent) +
      ∑ q ∈ lowOwnerFirstOwnerRawParentInertLowerOwnerSchedule R p r,
        ∑ mn ∈ lowOwnerFirstOwnerRawParentOrbitInertGreatestOwnerFiber
            R p sig r q,
          lowOwnerFirstOwnerDirichletPolarizationAtom R p mn := by
  have hdesc :=
    lowOwnerFirstOwnerRevealedPolarizationEnergy_descending_le_next_add_lowerOwners
      (R := R) (p := p) (r := r) (sig := sig) hp hr hpr
  have hsplice :=
    sum_lowOwnerFirstOwnerRawParentNextPolarization_eq_gate_sub_sameBranch_add_incomplete
      (R := R) (p := p) (r := r) (sig := sig) hp
  unfold lowOwnerFirstOwnerRawParentNextPolarizationTerm at hsplice
  rw [hsplice] at hdesc
  exact hdesc

end RHLean.Proof
