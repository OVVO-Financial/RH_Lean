import Mathlib
import «research.GLOBAL_RETURNED_CORE_SIGNED_INCIDENCE_ENERGY_GATE»
import «research.GLOBAL_RETURNED_CORE_UNIQUE_GREATEST_OWNER_ASSEMBLY»
import «research.GLOBAL_RETURNED_CORE_VIRTUAL_OWNER_CORNER_CLASSIFICATION»

/-!
# Charge completed incidence output to the existing reciprocal side ledger

The signed polarization survivor remains upstream.  This file touches only the
nonnegative reciprocal currency which has already crossed the completed
incidence gate.

A raw completed parent can occur in both orientations in the signed carrier,
whereas the reciprocal greatest-owner graph stores the stripped parent in its
canonical ordered orientation.  The only raw parents which can emit a literal
reciprocal child are therefore those whose greatest-owner child fibre is
nonempty.  We call these `active` completed raw parents.

For an active completed parent, full physical completion implies that both
parent coordinates and both virtual r-children are admitted in the same
first-owner `(p,sig)` cell.  Any literal greatest-owner child over that parent
therefore witnesses the same duplicate-free `(r,stripped-parent)` block already
used by `lowOwnerFirstOwnerRecursiveInheritedEnergy`.

Consequently the completed gate output is a nonnegative subledger of the
existing admitted reciprocal ledger.  No signed survivor, same-branch term,
rank recurrence, or parent-square inventory is used here.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Completed raw parents which actually emit at least one literal reciprocal
child on the greatest-owner graph. -/
def lowOwnerFirstOwnerActiveCompletedPolarizationRawParentSet
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : Finset (ℕ × ℕ) :=
  (lowOwnerFirstOwnerCompletedPolarizationRawParentSet R p sig r).filter
    (fun parent =>
      (lowOwnerGreatestOwnerFixedParentChildFiber R parent r).Nonempty)

/-- Canonical orientation preserves membership in a Cartesian square. -/
private theorem covarianceOrderedPair_mem_product
    {S : Finset ℕ} {a b : ℕ} (ha : a ∈ S) (hb : b ∈ S) :
    covarianceOrderedPair a b ∈ S.product S := by
  unfold covarianceOrderedPair
  by_cases hab : a < b
  · simp [hab, ha, hb]
  · simp [hab, ha, hb]

/-- **Active completed parents already belong to the admitted owner-parent
ledger.**  Completion supplies the missing physical p*r corners; no estimate is
used. -/
theorem lowOwnerFirstOwnerActiveCompletedRawParent_subset_admittedBlocks
    {R p r : ℕ} {sig : Finset ℕ} (hp : p.Prime) :
    lowOwnerFirstOwnerActiveCompletedPolarizationRawParentSet R p sig r ⊆
      lowOwnerFirstOwnerAdmittedGreatestOwnerParentBlocks R p sig r := by
  intro parent hparent
  rcases Finset.mem_filter.mp hparent with ⟨hcompleted, hactive⟩
  rcases mem_lowOwnerFirstOwnerCompletedPolarizationRawParentSet.mp hcompleted with
    ⟨hraw, hcomplete⟩
  rcases lowOwnerFirstOwnerCompletedPolarizationRawParent_data hp hcompleted with
    ⟨hr, hpr, hraFresh, hrbFresh, _haPos, _hbPos⟩
  rcases hcomplete with
    ⟨_hr', _hraFresh', _hrbFresh',
      _haX, hpaX, _hraX, hpraX,
      _hbX, hpbX, _hrbX, hprbX⟩

  rcases Finset.mem_image.mp hraw with ⟨rawChild, hrawChild, hrawEq⟩
  have hbase :=
    lowOwnerFirstOwnerPolarization_child_rawParent_mem_same_cell hp hrawChild
  rw [hrawEq] at hbase
  have haAd : parent.1 ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig :=
    Finset.mem_filter.mpr ⟨hbase.1, hpaX⟩
  have hbAd : parent.2 ∈ lowOwnerFirstOwnerAdmittedBaseFiber R p sig :=
    Finset.mem_filter.mpr ⟨hbase.2, hpbX⟩
  have hraAd : r * parent.1 ∈
      lowOwnerFirstOwnerAdmittedBaseFiber R p sig :=
    lowOwnerFirstOwner_mul_larger_prime_mem_admittedBase
      hp hr hpr hraFresh haAd hpraX
  have hrbAd : r * parent.2 ∈
      lowOwnerFirstOwnerAdmittedBaseFiber R p sig :=
    lowOwnerFirstOwner_mul_larger_prime_mem_admittedBase
      hp hr hpr hrbFresh hbAd hprbX

  rcases hactive with ⟨child, hchild⟩
  have hcand :=
    lowOwnerGreatestOwnerFixedParentChildFiber_subset_candidates
      R parent r hchild
  have hpair : child ∈ lowOwnerFirstOwnerAdmittedPairCarrier R p sig := by
    unfold covarianceOwnerChildCandidates at hcand
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcand
    rcases hcand with hcand | hcand
    · rw [hcand]
      exact covarianceOrderedPair_mem_product hraAd hbAd
    · rw [hcand]
      exact covarianceOrderedPair_mem_product haAd hrbAd

  rcases Finset.mem_filter.mp hchild with ⟨hlt, hparentEq⟩
  rcases Finset.mem_filter.mp hlt with ⟨hcross, _hchildLt⟩
  have howner : IsSquarefreePairGreatestFreshPrimeOwner r child.1 child.2 :=
    descendingCrossPair_greatestFreshOwner hr hcross
  have howned : child ∈
      lowOwnerFirstOwnerAdmittedGreatestOwnerPairFiber R p sig r :=
    mem_lowOwnerFirstOwnerAdmittedGreatestOwnerPairFiber.mpr ⟨hpair, howner⟩
  unfold lowOwnerFirstOwnerAdmittedGreatestOwnerParentBlocks
  exact Finset.mem_image.mpr ⟨child, howned, hparentEq⟩

/-- Restricting to active completed parents does not change the emitted energy:
an inactive parent has an empty literal child fibre. -/
theorem lowOwnerFirstOwnerCompletedInheritedReciprocalEnergy_eq_active
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) :
    lowOwnerFirstOwnerCompletedInheritedReciprocalEnergy R p sig r =
      ∑ parent ∈
        lowOwnerFirstOwnerActiveCompletedPolarizationRawParentSet R p sig r,
        ∑ child ∈ lowOwnerGreatestOwnerFixedParentChildFiber R parent r,
          lowOwnerThresholdEulerInheritedGreatestChildEnergy
            R p r parent child := by
  unfold lowOwnerFirstOwnerCompletedInheritedReciprocalEnergy
    lowOwnerFirstOwnerActiveCompletedPolarizationRawParentSet
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro parent _hparent
  by_cases hactive :
      (lowOwnerGreatestOwnerFixedParentChildFiber R parent r).Nonempty
  · simp [hactive]
  · have hempty :
        lowOwnerGreatestOwnerFixedParentChildFiber R parent r = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hactive
    simp [hactive, hempty]

/-- One completed `(p,sig,r)` gate packet is charged to the already-defined
admitted reciprocal owner-parent ledger at the same labels. -/
theorem lowOwnerFirstOwnerCompletedInheritedReciprocalEnergy_le_admittedLedger
    {R p r : ℕ} {sig : Finset ℕ} (hp : p.Prime) :
    lowOwnerFirstOwnerCompletedInheritedReciprocalEnergy R p sig r ≤
      ∑ parent ∈
        lowOwnerFirstOwnerAdmittedGreatestOwnerParentBlocks R p sig r,
        ∑ child ∈ lowOwnerGreatestOwnerFixedParentChildFiber R parent r,
          lowOwnerThresholdEulerInheritedGreatestChildEnergy
            R p r parent child := by
  rw [lowOwnerFirstOwnerCompletedInheritedReciprocalEnergy_eq_active]
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (lowOwnerFirstOwnerActiveCompletedRawParent_subset_admittedBlocks hp) ?_
  intro parent _hparent _hnot
  apply Finset.sum_nonneg
  intro child _hchild
  unfold lowOwnerThresholdEulerInheritedGreatestChildEnergy
  exact mul_nonneg
    (sq_nonneg (lowOwnerThresholdEulerPairCoefficient R p r parent))
    (postRootCovarianceReciprocalPairEnergy_nonneg child)

/-- Completed gate output over all next owners of one `(p,sig)` cell. -/
def lowOwnerFirstOwnerCompletedGateEmittedEnergy
    (R p : ℕ) (sig : Finset ℕ) : ℝ :=
  ∑ r ∈ primesUpTo (squareRootEndpoint R),
    lowOwnerFirstOwnerCompletedInheritedReciprocalEnergy R p sig r

/-- **Cell-level charge theorem.**  Every completed gate atom lands in the
existing unique-owner reciprocal side ledger. -/
theorem lowOwnerFirstOwnerCompletedGateEmittedEnergy_le_recursiveInheritedEnergy
    {R p : ℕ} {sig : Finset ℕ} (hp : p.Prime) :
    lowOwnerFirstOwnerCompletedGateEmittedEnergy R p sig ≤
      lowOwnerFirstOwnerRecursiveInheritedEnergy R p sig := by
  unfold lowOwnerFirstOwnerCompletedGateEmittedEnergy
    lowOwnerFirstOwnerRecursiveInheritedEnergy
  apply Finset.sum_le_sum
  intro r _hr
  exact lowOwnerFirstOwnerCompletedInheritedReciprocalEnergy_le_admittedLedger hp

/-- Global completed gate output with the first-owner and signature labels kept
explicit until after the charge has been proved. -/
def lowOwnerCompletedGateEmittedEnergy (R : ℕ) : ℝ :=
  ∑ p ∈ primesUpTo (squareRootEndpoint R),
    ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
      lowOwnerFirstOwnerCompletedGateEmittedEnergy R p sig

/-- Existing global admitted reciprocal side ledger. -/
def lowOwnerGlobalRecursiveInheritedEnergy (R : ℕ) : ℝ :=
  ∑ p ∈ primesUpTo (squareRootEndpoint R),
    ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
      lowOwnerFirstOwnerRecursiveInheritedEnergy R p sig

/-- **Global exact-label charge.**  The right rail is now attached to an
existing reciprocal ledger; no part of the signed polarization survivor pays
for it. -/
theorem lowOwnerCompletedGateEmittedEnergy_le_globalRecursiveInheritedEnergy
    (R : ℕ) :
    lowOwnerCompletedGateEmittedEnergy R ≤
      lowOwnerGlobalRecursiveInheritedEnergy R := by
  unfold lowOwnerCompletedGateEmittedEnergy
    lowOwnerGlobalRecursiveInheritedEnergy
  apply Finset.sum_le_sum
  intro p hpMem
  have hp : p.Prime := (mem_primesUpTo.mp hpMem).1
  apply Finset.sum_le_sum
  intro sig _hsig
  exact lowOwnerFirstOwnerCompletedGateEmittedEnergy_le_recursiveInheritedEnergy hp

/-- Matching global owner-labelled parent-energy ledger. -/
def lowOwnerGlobalRecursiveOwnerParentEnergy (R : ℕ) : ℝ :=
  ∑ p ∈ primesUpTo (squareRootEndpoint R),
    ∑ sig ∈ lowOwnerFirstOwnerSignatureSet R p,
      lowOwnerFirstOwnerRecursiveOwnerParentEnergy R p sig

/-- The completed gate charge inherits the already-compiled `2/9` bound after
it has landed on the reciprocal side ledger. -/
theorem lowOwnerCompletedGateEmittedEnergy_le_two_ninths_globalOwnerParentEnergy
    (R : ℕ) :
    lowOwnerCompletedGateEmittedEnergy R ≤
      (2 / 9 : ℝ) * lowOwnerGlobalRecursiveOwnerParentEnergy R := by
  have hcharge :=
    lowOwnerCompletedGateEmittedEnergy_le_globalRecursiveInheritedEnergy R
  have hcontract :
      lowOwnerGlobalRecursiveInheritedEnergy R ≤
        (2 / 9 : ℝ) * lowOwnerGlobalRecursiveOwnerParentEnergy R := by
    unfold lowOwnerGlobalRecursiveInheritedEnergy
      lowOwnerGlobalRecursiveOwnerParentEnergy
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hpMem
    have hp : p.Prime := (mem_primesUpTo.mp hpMem).1
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro sig _hsig
    exact
      lowOwnerFirstOwnerRecursiveInheritedEnergy_le_two_ninths_ownerParentEnergy hp
  exact hcharge.trans hcontract

end RHLean.Proof
