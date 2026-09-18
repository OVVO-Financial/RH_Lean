import Mathlib
import «research.GLOBAL_RETURNED_CORE_RAW_PARENT_BOUNDARY_RECIPROCAL_BRIDGE»

/-!
# Orientation-disjoint Fubini for raw-parent boundary exits

Each chronological boundary class can clip in one or both coordinates.  Before
any positive estimate is applied we assign a unique orientation by left
priority: the left sector consists of parents whose first coordinate clips,
and the right sector is the complementary filter inside the same chronological
class.  The right-sector hypotheses therefore force clipping of the second
coordinate.

This produces six pairwise chronological/orientation ledgers with no duplicate
charge:

* first-owner left/right;
* next-owner left/right;
* returned-after-r left/right.

All identities are signed finite Fubini statements.  In particular, no factor
of two is paid merely because both coordinates can hit a boundary.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Left-priority first-owner clipping. -/
def lowOwnerFirstOwnerIncompleteFirstClipLeftSet
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : Finset (ℕ × ℕ) :=
  (lowOwnerFirstOwnerIncompleteFirstClipSet R p sig r).filter fun parent =>
    squareRootEndpoint R < p * parent.1

/-- Complementary right first-owner clipping. -/
def lowOwnerFirstOwnerIncompleteFirstClipRightSet
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : Finset (ℕ × ℕ) :=
  (lowOwnerFirstOwnerIncompleteFirstClipSet R p sig r).filter fun parent =>
    ¬ squareRootEndpoint R < p * parent.1

/-- Left-priority next-owner physical exit. -/
def lowOwnerFirstOwnerIncompleteNextClipLeftSet
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : Finset (ℕ × ℕ) :=
  (lowOwnerFirstOwnerIncompleteNextClipSet R p sig r).filter fun parent =>
    squareRootEndpoint R < r * parent.1

/-- Complementary right next-owner physical exit. -/
def lowOwnerFirstOwnerIncompleteNextClipRightSet
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : Finset (ℕ × ℕ) :=
  (lowOwnerFirstOwnerIncompleteNextClipSet R p sig r).filter fun parent =>
    ¬ squareRootEndpoint R < r * parent.1

/-- Left-priority returned-after-r clipping. -/
def lowOwnerFirstOwnerIncompleteReturnedClipLeftSet
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : Finset (ℕ × ℕ) :=
  (lowOwnerFirstOwnerIncompleteReturnedClipSet R p sig r).filter fun parent =>
    squareRootEndpoint R < p * (r * parent.1)

/-- Complementary right returned-after-r clipping. -/
def lowOwnerFirstOwnerIncompleteReturnedClipRightSet
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : Finset (ℕ × ℕ) :=
  (lowOwnerFirstOwnerIncompleteReturnedClipSet R p sig r).filter fun parent =>
    ¬ squareRootEndpoint R < p * (r * parent.1)

/-- A right first-owner sector member necessarily clips in coordinate two. -/
theorem lowOwnerFirstOwnerIncompleteFirstClipRight_mem_implies_rightClip
    {R p r : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (hparent : parent ∈
      lowOwnerFirstOwnerIncompleteFirstClipRightSet R p sig r) :
    squareRootEndpoint R < p * parent.2 := by
  rcases Finset.mem_filter.mp hparent with ⟨hfirst, hnotLeft⟩
  have hclip := (Finset.mem_filter.mp hfirst).2
  rcases hclip with hleft | hright
  · exact False.elim (hnotLeft hleft)
  · exact hright

/-- A right next-owner sector member necessarily exits in coordinate two. -/
theorem lowOwnerFirstOwnerIncompleteNextClipRight_mem_implies_rightClip
    {R p r : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (hparent : parent ∈
      lowOwnerFirstOwnerIncompleteNextClipRightSet R p sig r) :
    squareRootEndpoint R < r * parent.2 := by
  rcases Finset.mem_filter.mp hparent with ⟨hnext, hnotLeft⟩
  have hclip := (Finset.mem_filter.mp hnext).2
  rcases hclip.2.2 with hleft | hright
  · exact False.elim (hnotLeft hleft)
  · exact hright

/-- A right returned sector member necessarily clips the returned second
coordinate. -/
theorem lowOwnerFirstOwnerIncompleteReturnedClipRight_mem_implies_rightClip
    {R p r : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (hparent : parent ∈
      lowOwnerFirstOwnerIncompleteReturnedClipRightSet R p sig r) :
    squareRootEndpoint R < p * (r * parent.2) := by
  rcases Finset.mem_filter.mp hparent with ⟨hret, hnotLeft⟩
  have hclip := (Finset.mem_filter.mp hret).2
  rcases hclip.2.2.2.2 with hleft | hright
  · exact False.elim (hnotLeft hleft)
  · exact hright

/-- Exact left/right split of the first-owner boundary mass. -/
theorem sum_lowOwnerFirstOwnerIncompleteFirstClip_eq_left_add_right
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) (f : ℕ × ℕ → ℝ) :
    (∑ parent ∈ lowOwnerFirstOwnerIncompleteFirstClipSet R p sig r,
      f parent) =
      (∑ parent ∈ lowOwnerFirstOwnerIncompleteFirstClipLeftSet R p sig r,
        f parent) +
      ∑ parent ∈ lowOwnerFirstOwnerIncompleteFirstClipRightSet R p sig r,
        f parent := by
  unfold lowOwnerFirstOwnerIncompleteFirstClipLeftSet
    lowOwnerFirstOwnerIncompleteFirstClipRightSet
  simpa only using
    (Finset.sum_filter_add_sum_filter_not
      (s := lowOwnerFirstOwnerIncompleteFirstClipSet R p sig r)
      (p := fun parent : ℕ × ℕ => squareRootEndpoint R < p * parent.1)
      (f := f)).symm

/-- Exact left/right split of the next-owner physical-exit mass. -/
theorem sum_lowOwnerFirstOwnerIncompleteNextClip_eq_left_add_right
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) (f : ℕ × ℕ → ℝ) :
    (∑ parent ∈ lowOwnerFirstOwnerIncompleteNextClipSet R p sig r,
      f parent) =
      (∑ parent ∈ lowOwnerFirstOwnerIncompleteNextClipLeftSet R p sig r,
        f parent) +
      ∑ parent ∈ lowOwnerFirstOwnerIncompleteNextClipRightSet R p sig r,
        f parent := by
  unfold lowOwnerFirstOwnerIncompleteNextClipLeftSet
    lowOwnerFirstOwnerIncompleteNextClipRightSet
  simpa only using
    (Finset.sum_filter_add_sum_filter_not
      (s := lowOwnerFirstOwnerIncompleteNextClipSet R p sig r)
      (p := fun parent : ℕ × ℕ => squareRootEndpoint R < r * parent.1)
      (f := f)).symm

/-- Exact left/right split of the returned-after-r boundary mass. -/
theorem sum_lowOwnerFirstOwnerIncompleteReturnedClip_eq_left_add_right
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) (f : ℕ × ℕ → ℝ) :
    (∑ parent ∈ lowOwnerFirstOwnerIncompleteReturnedClipSet R p sig r,
      f parent) =
      (∑ parent ∈ lowOwnerFirstOwnerIncompleteReturnedClipLeftSet R p sig r,
        f parent) +
      ∑ parent ∈ lowOwnerFirstOwnerIncompleteReturnedClipRightSet R p sig r,
        f parent := by
  unfold lowOwnerFirstOwnerIncompleteReturnedClipLeftSet
    lowOwnerFirstOwnerIncompleteReturnedClipRightSet
  simpa only using
    (Finset.sum_filter_add_sum_filter_not
      (s := lowOwnerFirstOwnerIncompleteReturnedClipSet R p sig r)
      (p := fun parent : ℕ × ℕ =>
        squareRootEndpoint R < p * (r * parent.1))
      (f := f)).symm

/-- **Six-sector signed Fubini.**  Every incomplete raw parent is charged once,
first by chronological failure class and then by canonical orientation. -/
theorem sum_lowOwnerFirstOwnerIncompleteRawParents_eq_sixOrientedSectors
    {R p r : ℕ} {sig : Finset ℕ} (hp : p.Prime)
    (f : ℕ × ℕ → ℝ) :
    (∑ parent ∈ lowOwnerFirstOwnerIncompletePolarizationRawParentSet R p sig r,
      f parent) =
      (∑ parent ∈ lowOwnerFirstOwnerIncompleteFirstClipLeftSet R p sig r,
        f parent) +
      (∑ parent ∈ lowOwnerFirstOwnerIncompleteFirstClipRightSet R p sig r,
        f parent) +
      (∑ parent ∈ lowOwnerFirstOwnerIncompleteNextClipLeftSet R p sig r,
        f parent) +
      (∑ parent ∈ lowOwnerFirstOwnerIncompleteNextClipRightSet R p sig r,
        f parent) +
      (∑ parent ∈ lowOwnerFirstOwnerIncompleteReturnedClipLeftSet R p sig r,
        f parent) +
      ∑ parent ∈ lowOwnerFirstOwnerIncompleteReturnedClipRightSet R p sig r,
        f parent := by
  rw [sum_lowOwnerFirstOwnerIncompleteRawParents_eq_threeClipSectors hp]
  rw [sum_lowOwnerFirstOwnerIncompleteFirstClip_eq_left_add_right]
  rw [sum_lowOwnerFirstOwnerIncompleteNextClip_eq_left_add_right]
  rw [sum_lowOwnerFirstOwnerIncompleteReturnedClip_eq_left_add_right]
  ring

/-- On an oriented returned-left sector the exact reciprocal double-corner
identity is available without an existential orientation choice. -/
theorem lowOwnerFirstOwnerIncompleteReturnedClipLeft_criticalFourCorner_eq_neg_reciprocal
    {R p r : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (hp : p.Prime)
    (hparent : parent ∈
      lowOwnerFirstOwnerIncompleteReturnedClipLeftSet R p sig r) :
    zeroTargetMellinPhysicalSuperLcmFourCorner (squareRootEndpoint R) r
        (zeroTargetCriticalOwnerRatio r) parent.1 (p * parent.1) =
      -(1 / (r : ℝ)) *
        postRootZeroTargetPairExcess (parent.1, p * parent.1) := by
  rcases Finset.mem_filter.mp hparent with ⟨hret, hleft⟩
  rcases Finset.mem_filter.mp hret with ⟨hinc, hclip⟩
  have hraw := (Finset.mem_filter.mp hinc).1
  exact
    lowOwnerRawParentReturnedNextClipped_left_criticalFourCorner_eq_neg_reciprocal
      hp hraw hclip hleft

/-- Symmetric oriented returned-right reciprocal identity. -/
theorem lowOwnerFirstOwnerIncompleteReturnedClipRight_criticalFourCorner_eq_neg_reciprocal
    {R p r : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (hp : p.Prime)
    (hparent : parent ∈
      lowOwnerFirstOwnerIncompleteReturnedClipRightSet R p sig r) :
    zeroTargetMellinPhysicalSuperLcmFourCorner (squareRootEndpoint R) r
        (zeroTargetCriticalOwnerRatio r) parent.2 (p * parent.2) =
      -(1 / (r : ℝ)) *
        postRootZeroTargetPairExcess (parent.2, p * parent.2) := by
  rcases Finset.mem_filter.mp hparent with ⟨hret, _hnotLeft⟩
  rcases Finset.mem_filter.mp hret with ⟨hinc, hclip⟩
  have hraw := (Finset.mem_filter.mp hinc).1
  have hright :=
    lowOwnerFirstOwnerIncompleteReturnedClipRight_mem_implies_rightClip hparent
  exact
    lowOwnerRawParentReturnedNextClipped_right_criticalFourCorner_eq_neg_reciprocal
      hp hraw hclip hright

/-- Oriented next-left sector is a literal one-ended Euler edge. -/
theorem lowOwnerFirstOwnerIncompleteNextClipLeft_criticalEuler_eq_parent
    {R p r : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (hR : 2 ≤ R) (hp : p.Prime)
    (hparent : parent ∈
      lowOwnerFirstOwnerIncompleteNextClipLeftSet R p sig r) :
    lowOwnerThresholdCriticalEulerDifference R p r parent.1 =
      lowOwnerThresholdOwnerEulerWeight R p parent.1 := by
  have hleft := (Finset.mem_filter.mp hparent).2
  exact lowOwnerRawParentNextOwnerClipped_left_criticalEuler_eq_parent
    hR hp hleft

/-- Oriented next-right sector is the symmetric one-ended Euler edge. -/
theorem lowOwnerFirstOwnerIncompleteNextClipRight_criticalEuler_eq_parent
    {R p r : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (hR : 2 ≤ R) (hp : p.Prime)
    (hparent : parent ∈
      lowOwnerFirstOwnerIncompleteNextClipRightSet R p sig r) :
    lowOwnerThresholdCriticalEulerDifference R p r parent.2 =
      lowOwnerThresholdOwnerEulerWeight R p parent.2 := by
  have hright :=
    lowOwnerFirstOwnerIncompleteNextClipRight_mem_implies_rightClip hparent
  exact lowOwnerRawParentNextOwnerClipped_right_criticalEuler_eq_parent
    hR hp hright

end RHLean.Proof
