import Mathlib
import «research.GLOBAL_RETURNED_CORE_EMITTED_RECIPROCAL_CHARGE»

/-!
# The sufficient reciprocal envelope lives on inherited gate energy

The completed incidence gate has already crossed from signed polarization into
nonnegative reciprocal currency.  PR #740 proves the exact-label charge

  completed gate emitted energy <= global recursive inherited energy

and separately the coarse owner-parent majorant

  global recursive inherited energy <= (2/9) * global owner-parent energy.

The second inequality is useful but is not logically required for closure.
The physical right-rail object retains the literal child factor `1/r^2`, so a
root-scale estimate may be proved directly on the inherited ledger without
first proving the visibly stronger unweighted parent-energy estimate.

On the nonzero Mobius carrier there is a further exact simplification.  The
Euler lift contributes one factor of each parent coordinate, while reciprocal
pair energy contributes the inverse square of their product.  Since nonzero
Mobius weights have square one, these factors cancel exactly.  The retained
parent energy is therefore the square of the two commuting second incidence
differences of the deterministic threshold potential.  This is an identity,
not an estimate and not a Mertens input.

This file records that hierarchy as named interfaces.  No signed survivor,
AMP Gram, rank recurrence, or unweighted parent inventory is introduced into
the inherited target.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- A nonzero real Mobius step has unit square.  Kept local to this seam so the
cancellation theorem does not depend on an unrelated diagonal-energy module. -/
private theorem realMoebiusStep_sq_eq_one_of_ne_zero_inherited
    {n : ℕ} (hn : realMoebiusStep n ≠ 0) :
    realMoebiusStep n ^ 2 = 1 := by
  rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;>
    simp [realMoebiusStep, h] at hn ⊢

/-- On a nonzero reciprocal pair the reciprocal energy is exactly the inverse
square of the coordinate product. -/
private theorem postRootCovarianceReciprocalPairEnergy_eq_inv_product_sq_inherited
    {a b : ℕ}
    (hma : realMoebiusStep a ≠ 0)
    (hmb : realMoebiusStep b ≠ 0) :
    postRootCovarianceReciprocalPairEnergy (a, b) =
      1 / (((a : ℝ) ^ 2) * ((b : ℝ) ^ 2)) := by
  have hmaSq : realMoebiusStep a ^ 2 = 1 :=
    realMoebiusStep_sq_eq_one_of_ne_zero_inherited hma
  have hmbSq : realMoebiusStep b ^ 2 = 1 :=
    realMoebiusStep_sq_eq_one_of_ne_zero_inherited hmb
  unfold postRootCovarianceReciprocalPairEnergy
    postRootCovarianceReciprocalPairAmplitude
  rw [div_pow]
  rw [mul_pow, hmaSq, hmbSq]
  ring

/-- **Exact Mobius/reciprocal cancellation.**  On a positive nonzero parent,
Euler normalization cancels the reciprocal pair denominators and the squared
Mobius weights.  What remains is purely the product of the two second mixed
incidence squares of the deterministic threshold potential. -/
theorem lowOwnerThresholdEulerParentEnergy_eq_secondOwnerDifference_sq
    {R p r a b : ℕ}
    (hr : 0 < r) (ha : 0 < a) (hb : 0 < b)
    (hma : realMoebiusStep a ≠ 0)
    (hmb : realMoebiusStep b ≠ 0) :
    lowOwnerThresholdEulerParentEnergy R p r (a, b) =
      lowOwnerThresholdSecondOwnerDifference R p r a ^ 2 *
        lowOwnerThresholdSecondOwnerDifference R p r b ^ 2 := by
  have ha0 : (a : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt ha)
  have hb0 : (b : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hb)
  unfold lowOwnerThresholdEulerParentEnergy
  rw [postRootCovarianceReciprocalPairEnergy_eq_inv_product_sq_inherited hma hmb]
  unfold lowOwnerThresholdEulerPairCoefficient
  rw [lowOwnerThresholdCriticalEulerDifference_eq_nat_mul_secondDifference hr,
    lowOwnerThresholdCriticalEulerDifference_eq_nat_mul_secondDifference hr]
  field_simp [ha0, hb0]

/-- Root-scale envelope statement for the actual reciprocal energy emitted by
all greatest-owner children after the completed incidence gate.  This is the
minimal positive right-rail estimate needed to bound the gate output. -/
def LowOwnerGlobalRecursiveInheritedEnergyBound (C : ℝ) : Prop :=
  ∀ R : ℕ, ∀ K : ℝ,
    56 ≤ R →
    LowerMertensCriticalEnvelope R K →
    lowOwnerGlobalRecursiveInheritedEnergy R ≤
      C * (R : ℝ) ^ 2 * K

/-- Stronger optional envelope on the unweighted owner-labelled parent ledger.
It implies the inherited estimate, but closure does not require proving it. -/
def LowOwnerGlobalRecursiveOwnerParentEnergyBound (C : ℝ) : Prop :=
  ∀ R : ℕ, ∀ K : ℝ,
    56 ≤ R →
    LowerMertensCriticalEnvelope R K →
    lowOwnerGlobalRecursiveOwnerParentEnergy R ≤
      C * (R : ℝ) ^ 2 * K

/-- The global inherited ledger itself has the already-compiled `2/9`
owner-parent majorant.  This theorem merely exposes the local contraction from
#740 as a reusable global statement. -/
theorem lowOwnerGlobalRecursiveInheritedEnergy_le_two_ninths_globalOwnerParentEnergy
    (R : ℕ) :
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

/-- Any root-scale parent-ledger bound therefore supplies a root-scale inherited
bound with the expected `2/9` coefficient. -/
theorem lowOwnerGlobalRecursiveInheritedEnergyBound_of_ownerParentEnergyBound
    {C : ℝ}
    (hparent : LowOwnerGlobalRecursiveOwnerParentEnergyBound C) :
    LowOwnerGlobalRecursiveInheritedEnergyBound ((2 / 9 : ℝ) * C) := by
  intro R K hR hK
  have hinherited :=
    lowOwnerGlobalRecursiveInheritedEnergy_le_two_ninths_globalOwnerParentEnergy R
  have hparentR := hparent R K hR hK
  have hscale : (0 : ℝ) ≤ 2 / 9 := by norm_num
  calc
    lowOwnerGlobalRecursiveInheritedEnergy R ≤
        (2 / 9 : ℝ) * lowOwnerGlobalRecursiveOwnerParentEnergy R := hinherited
    _ ≤ (2 / 9 : ℝ) * (C * (R : ℝ) ^ 2 * K) :=
      mul_le_mul_of_nonneg_left hparentR hscale
    _ = ((2 / 9 : ℝ) * C) * (R : ℝ) ^ 2 * K := by ring

/-- **The inherited envelope is already sufficient for the completed gate.**
No parent-square estimate is needed: #740's exact-label charge lands directly
on this ledger. -/
theorem lowOwnerCompletedGateEmittedEnergy_le_root_sq_K_of_inheritedEnergyBound
    {C : ℝ}
    (hinherited : LowOwnerGlobalRecursiveInheritedEnergyBound C) :
    ∀ R : ℕ, ∀ K : ℝ,
      56 ≤ R →
      LowerMertensCriticalEnvelope R K →
      lowOwnerCompletedGateEmittedEnergy R ≤
        C * (R : ℝ) ^ 2 * K := by
  intro R K hR hK
  exact
    (lowOwnerCompletedGateEmittedEnergy_le_globalRecursiveInheritedEnergy R).trans
      (hinherited R K hR hK)

/-- Parent-envelope form, retained only as a convenient stronger sufficient
interface. -/
theorem lowOwnerCompletedGateEmittedEnergy_le_root_sq_K_of_ownerParentEnergyBound
    {C : ℝ}
    (hparent : LowOwnerGlobalRecursiveOwnerParentEnergyBound C) :
    ∀ R : ℕ, ∀ K : ℝ,
      56 ≤ R →
      LowerMertensCriticalEnvelope R K →
      lowOwnerCompletedGateEmittedEnergy R ≤
        ((2 / 9 : ℝ) * C) * (R : ℝ) ^ 2 * K := by
  exact
    lowOwnerCompletedGateEmittedEnergy_le_root_sq_K_of_inheritedEnergyBound
      (lowOwnerGlobalRecursiveInheritedEnergyBound_of_ownerParentEnergyBound hparent)

/-!
## Tightening the completed gate back to the exact cell fibre

For a completed active raw parent, full p/r completion puts both possible
r-children in the same admitted `(p,sig)` cell.  Therefore the global
fixed-parent fibre used in the coarse reciprocal majorant has no extra children
at all: it equals the cell-specific fixed-parent fibre from the unique-owner
Fubini.  This removes artificial parent/child congestion before the remaining
quantitative estimate is attempted.
-/

private theorem covarianceOrderedPair_mem_product_exactGate
    {S : Finset ℕ} {a b : ℕ} (ha : a ∈ S) (hb : b ∈ S) :
    covarianceOrderedPair a b ∈ S.product S := by
  unfold covarianceOrderedPair
  by_cases hab : a < b
  · simp [hab, ha, hb]
  · simp [hab, ha, hb]

/-- **No extra children at a completed gate block.** -/
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

/-- The completed gate energy can therefore be written using exact cell fibres. -/
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

/-- Active completed parents are actual labels in the exact parent partition. -/
theorem lowOwnerFirstOwnerActiveCompletedRawParent_subset_parentSet
    {R p r : ℕ} {sig : Finset ℕ} (hp : p.Prime) :
    lowOwnerFirstOwnerActiveCompletedPolarizationRawParentSet R p sig r ⊆
      lowOwnerFirstOwnerGreatestOwnerParentSet R p sig r := by
  intro parent hparent
  rcases (Finset.mem_filter.mp hparent).2 with ⟨child, hchild⟩
  have hcell : child ∈
      lowOwnerFirstOwnerGreatestOwnerFixedParentCellFiber
        R p sig r parent := by
    rw [← lowOwnerGreatestOwnerFixedParentChildFiber_eq_cellFiber_of_activeCompleted
      hp hparent]
    exact hchild
  have hpositive := (Finset.mem_filter.mp hcell).1
  have hparentEq := (Finset.mem_filter.mp hcell).2
  unfold lowOwnerFirstOwnerGreatestOwnerParentSet
  exact Finset.mem_image.mpr ⟨child, hpositive, hparentEq⟩

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

/-- The active completed gate is a subledger of the exact parent partition. -/
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

/-- **Exact parent-label elimination.** -/
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

/-- One completed gate packet is bounded by a duplicate-free child-fibre sum. -/
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
