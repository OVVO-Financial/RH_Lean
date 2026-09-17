import Mathlib
import «research.GLOBAL_RETURNED_CORE_EMITTED_RECIPROCAL_CHARGE»
import «research.GLOBAL_RETURNED_CORE_OWNER_PARENT_CONTINUATION»

/-!
# Exact cell-specific carrier for the completed incidence gate

The completed-gate charge was previously embedded into the larger global
fixed-parent greatest-owner graph.  For an active completed raw parent this
majorization is unnecessary: full p/r completion puts both possible r-children
back in the same admitted `(p,sig)` cell.

Consequently the global fixed-parent fibre is exactly the cell-specific
fixed-parent fibre.  The completed gate therefore lands in the already-disjoint
unique-owner parent Fubini, with no extra child or parent congestion introduced
by the reciprocal majorant.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

private theorem covarianceOrderedPair_mem_product_exactGate
    {S : Finset ℕ} {a b : ℕ} (ha : a ∈ S) (hb : b ∈ S) :
    covarianceOrderedPair a b ∈ S.product S := by
  unfold covarianceOrderedPair
  by_cases hab : a < b
  · simp [hab, ha, hb]
  · simp [hab, ha, hb]

/-- **No extra children at a completed gate block.**  Once a completed raw
parent is active, the literal global greatest-owner fibre over that parent is
exactly the fixed-parent fibre inside the original `(p,sig)` cell. -/
theorem lowOwnerGreatestOwnerFixedParentChildFiber_eq_cellFiber_of_activeCompleted
    {R p r : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (hp : p.Prime)
    (hparent : parent ∈
      lowOwnerFirstOwnerActiveCompletedPolarizationRawParentSet R p sig r) :
    lowOwnerGreatestOwnerFixedParentChildFiber R parent r =
      lowOwnerFirstOwnerGreatestOwnerFixedParentCellFiber
        R p sig r parent := by
  apply Finset.Subset.antisymm
  · intro child hchild
    rcases Finset.mem_filter.mp hparent with ⟨hcompleted, _hactive⟩
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

    have hcand :=
      lowOwnerGreatestOwnerFixedParentChildFiber_subset_candidates
        R parent r hchild
    have hpair : child ∈ lowOwnerFirstOwnerAdmittedPairCarrier R p sig := by
      unfold covarianceOwnerChildCandidates at hcand
      simp only [Finset.mem_insert, Finset.mem_singleton] at hcand
      rcases hcand with hcand | hcand
      · rw [hcand]
        exact covarianceOrderedPair_mem_product_exactGate hraAd hbAd
      · rw [hcand]
        exact covarianceOrderedPair_mem_product_exactGate haAd hrbAd

    rcases Finset.mem_filter.mp hchild with ⟨hltFilter, hparentEq⟩
    rcases Finset.mem_filter.mp hltFilter with ⟨hcross, hchildLt⟩
    have howner : IsSquarefreePairGreatestFreshPrimeOwner
        r child.1 child.2 :=
      descendingCrossPair_greatestFreshOwner hr hcross
    have hoff : child ∈
        lowOwnerFirstOwnerAdmittedOffDiagonalPairCarrier R p sig :=
      Finset.mem_filter.mpr ⟨hpair, ne_of_lt hchildLt⟩
    have hownerFiber : child ∈
        lowOwnerFirstOwnerGreatestOwnerPairFiber R p sig r :=
      Finset.mem_filter.mpr ⟨hoff, howner⟩
    have hpositive : child ∈
        lowOwnerFirstOwnerGreatestOwnerPositivePairFiber R p sig r :=
      Finset.mem_filter.mpr ⟨hownerFiber, hchildLt⟩
    exact Finset.mem_filter.mpr ⟨hpositive, hparentEq⟩
  · intro child hchild
    exact lowOwnerFirstOwnerGreatestOwnerFixedParentCellFiber_subset_graph
      hp hchild

/-- The completed gate energy can therefore be written using the exact
cell-specific fixed-parent fibres, not the larger graph fibres. -/
theorem lowOwnerFirstOwnerCompletedInheritedReciprocalEnergy_eq_activeCellFibers
    {R p r : ℕ} {sig : Finset ℕ} (hp : p.Prime) :
    lowOwnerFirstOwnerCompletedInheritedReciprocalEnergy R p sig r =
      ∑ parent ∈
        lowOwnerFirstOwnerActiveCompletedPolarizationRawParentSet R p sig r,
        lowOwnerFirstOwnerGreatestOwnerFixedParentInheritedEnergy
          R p sig r parent := by
  rw [lowOwnerFirstOwnerCompletedInheritedReciprocalEnergy_eq_active]
  apply Finset.sum_congr rfl
  intro parent hparent
  unfold lowOwnerFirstOwnerGreatestOwnerFixedParentInheritedEnergy
  rw [lowOwnerGreatestOwnerFixedParentChildFiber_eq_cellFiber_of_activeCompleted
    hp hparent]

/-- Every active completed parent is one of the actual unique-owner parent
labels appearing in the cell-specific parent Fubini. -/
theorem lowOwnerFirstOwnerActiveCompletedRawParent_subset_parentSet
    {R p r : ℕ} {sig : Finset ℕ} (hp : p.Prime) :
    lowOwnerFirstOwnerActiveCompletedPolarizationRawParentSet R p sig r ⊆
      lowOwnerFirstOwnerGreatestOwnerParentSet R p sig r := by
  intro parent hparent
  have hblock : parent ∈
      lowOwnerFirstOwnerAdmittedGreatestOwnerParentBlocks R p sig r :=
    lowOwnerFirstOwnerActiveCompletedRawParent_subset_admittedBlocks hp hparent
  rcases lowOwnerFirstOwnerAdmittedGreatestOwnerParentBlock_has_positiveWitness
      hblock with ⟨m, n, hmn, hparentEq⟩
  unfold lowOwnerFirstOwnerGreatestOwnerParentSet
  exact Finset.mem_image.mpr ⟨(m, n), hmn, hparentEq⟩

@[simp] theorem lowOwnerFirstOwnerGreatestOwnerFixedParentInheritedEnergy_nonneg
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) (parent : ℕ × ℕ) :
    0 ≤ lowOwnerFirstOwnerGreatestOwnerFixedParentInheritedEnergy
      R p sig r parent := by
  unfold lowOwnerFirstOwnerGreatestOwnerFixedParentInheritedEnergy
  apply Finset.sum_nonneg
  intro child _hchild
  unfold lowOwnerThresholdEulerInheritedGreatestChildEnergy
  exact mul_nonneg
    (sq_nonneg (lowOwnerThresholdEulerPairCoefficient R p r parent))
    (postRootCovarianceReciprocalPairEnergy_nonneg child)

/-- The active completed gate is a nonnegative subledger of the *exact*
cell-specific unique-owner parent partition. -/
theorem lowOwnerFirstOwnerCompletedInheritedReciprocalEnergy_le_exactParentPartition
    {R p r : ℕ} {sig : Finset ℕ} (hp : p.Prime) :
    lowOwnerFirstOwnerCompletedInheritedReciprocalEnergy R p sig r ≤
      ∑ parent ∈ lowOwnerFirstOwnerGreatestOwnerParentSet R p sig r,
        lowOwnerFirstOwnerGreatestOwnerFixedParentInheritedEnergy
          R p sig r parent := by
  rw [lowOwnerFirstOwnerCompletedInheritedReciprocalEnergy_eq_activeCellFibers hp]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (lowOwnerFirstOwnerActiveCompletedRawParent_subset_parentSet hp)
    (by
      intro parent _hparent _hnot
      exact lowOwnerFirstOwnerGreatestOwnerFixedParentInheritedEnergy_nonneg
        R p sig r parent)

/-- Owner-dependent child energy after eliminating the redundant parent label. -/
def lowOwnerFirstOwnerGreatestOwnerCellInheritedChildEnergy
    (R p r : ℕ) (child : ℕ × ℕ) : ℝ :=
  lowOwnerThresholdEulerInheritedGreatestChildEnergy
    R p r (squarefreePairPrimeOrderedParent r child.1 child.2) child

/-- **Exact parent-label elimination.**  The full cell-specific parent ledger
is literally one sum over the positive unique-owner child fibre. -/
theorem sum_lowOwnerFirstOwnerGreatestOwnerParentSet_inheritedEnergy_eq_childFiber
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) :
    (∑ parent ∈ lowOwnerFirstOwnerGreatestOwnerParentSet R p sig r,
      lowOwnerFirstOwnerGreatestOwnerFixedParentInheritedEnergy
        R p sig r parent) =
      ∑ child ∈ lowOwnerFirstOwnerGreatestOwnerPositivePairFiber R p sig r,
        lowOwnerFirstOwnerGreatestOwnerCellInheritedChildEnergy R p r child := by
  rw [sum_lowOwnerFirstOwnerGreatestOwnerPositivePairFiber_eq_sum_parentFibers]
  apply Finset.sum_congr rfl
  intro parent _hparent
  unfold lowOwnerFirstOwnerGreatestOwnerFixedParentInheritedEnergy
  apply Finset.sum_congr rfl
  intro child hchild
  unfold lowOwnerFirstOwnerGreatestOwnerCellInheritedChildEnergy
  have hparentEq := (Finset.mem_filter.mp hchild).2
  rw [hparentEq]

/-- The completed gate at one `(p,sig,r)` label is therefore bounded by an
exact, duplicate-free child-fibre sum. -/
theorem lowOwnerFirstOwnerCompletedInheritedReciprocalEnergy_le_exactChildFiber
    {R p r : ℕ} {sig : Finset ℕ} (hp : p.Prime) :
    lowOwnerFirstOwnerCompletedInheritedReciprocalEnergy R p sig r ≤
      ∑ child ∈ lowOwnerFirstOwnerGreatestOwnerPositivePairFiber R p sig r,
        lowOwnerFirstOwnerGreatestOwnerCellInheritedChildEnergy R p r child := by
  calc
    lowOwnerFirstOwnerCompletedInheritedReciprocalEnergy R p sig r ≤
        ∑ parent ∈ lowOwnerFirstOwnerGreatestOwnerParentSet R p sig r,
          lowOwnerFirstOwnerGreatestOwnerFixedParentInheritedEnergy
            R p sig r parent :=
      lowOwnerFirstOwnerCompletedInheritedReciprocalEnergy_le_exactParentPartition hp
    _ = _ :=
      sum_lowOwnerFirstOwnerGreatestOwnerParentSet_inheritedEnergy_eq_childFiber
        R p sig r

end RHLean.Proof
