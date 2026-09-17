import Mathlib
import «research.GLOBAL_RETURNED_CORE_RAW_PARENT_INCOMPLETE_CLASSIFICATION»

/-!
# Exact three-sector Fubini of the incomplete raw-parent boundary

The pointwise incomplete-block classification is mutually exclusive in its
chronological form.  This file packages it as a finite signed Fubini:

  incomplete = first-owner clip
             ⊔ next-owner physical exit
             ⊔ returned-after-r clip.

The three carriers are disjoint.  Therefore an arbitrary signed weight splits
exactly across them with no absolute value or multiplicity loss.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Incomplete raw parents already clipped by the original first owner p. -/
def lowOwnerFirstOwnerIncompleteFirstClipSet
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : Finset (ℕ × ℕ) :=
  (lowOwnerFirstOwnerIncompletePolarizationRawParentSet R p sig r).filter fun parent =>
    LowOwnerRawParentFirstOwnerClipped R p parent

/-- Incomplete raw parents whose first new failure is the moved r-child. -/
def lowOwnerFirstOwnerIncompleteNextClipSet
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : Finset (ℕ × ℕ) :=
  (lowOwnerFirstOwnerIncompletePolarizationRawParentSet R p sig r).filter fun parent =>
    LowOwnerRawParentNextOwnerClipped R p r parent

/-- Incomplete raw parents whose r-children remain physical but whose returned
p-after-r child clips. -/
def lowOwnerFirstOwnerIncompleteReturnedClipSet
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : Finset (ℕ × ℕ) :=
  (lowOwnerFirstOwnerIncompletePolarizationRawParentSet R p sig r).filter fun parent =>
    LowOwnerRawParentReturnedNextClipped R p r parent

private theorem firstClip_disjoint_nextClip
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) :
    Disjoint
      (lowOwnerFirstOwnerIncompleteFirstClipSet R p sig r)
      (lowOwnerFirstOwnerIncompleteNextClipSet R p sig r) := by
  rw [Finset.disjoint_left]
  intro parent hfirst hnext
  have hf := (Finset.mem_filter.mp hfirst).2
  have hn := (Finset.mem_filter.mp hnext).2
  rcases hf with hf | hf
  · omega
  · omega

private theorem firstClip_disjoint_returnedClip
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) :
    Disjoint
      (lowOwnerFirstOwnerIncompleteFirstClipSet R p sig r)
      (lowOwnerFirstOwnerIncompleteReturnedClipSet R p sig r) := by
  rw [Finset.disjoint_left]
  intro parent hfirst hret
  have hf := (Finset.mem_filter.mp hfirst).2
  have hr := (Finset.mem_filter.mp hret).2
  rcases hf with hf | hf
  · omega
  · omega

private theorem nextClip_disjoint_returnedClip
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) :
    Disjoint
      (lowOwnerFirstOwnerIncompleteNextClipSet R p sig r)
      (lowOwnerFirstOwnerIncompleteReturnedClipSet R p sig r) := by
  rw [Finset.disjoint_left]
  intro parent hnext hret
  have hn := (Finset.mem_filter.mp hnext).2
  have hr := (Finset.mem_filter.mp hret).2
  rcases hn.2.2 with h | h
  · omega
  · omega

/-- The three chronological cutoff classes cover the incomplete raw-parent set. -/
theorem lowOwnerFirstOwnerIncompletePolarizationRawParentSet_eq_threeClipUnion
    {R p r : ℕ} {sig : Finset ℕ} (hp : p.Prime) :
    lowOwnerFirstOwnerIncompletePolarizationRawParentSet R p sig r =
      lowOwnerFirstOwnerIncompleteFirstClipSet R p sig r ∪
        (lowOwnerFirstOwnerIncompleteNextClipSet R p sig r ∪
          lowOwnerFirstOwnerIncompleteReturnedClipSet R p sig r) := by
  ext parent
  constructor
  · intro hparent
    rcases lowOwnerFirstOwnerIncompletePolarizationRawParent_classification
      hp hparent with hfirst | hnext | hret
    · exact Finset.mem_union.mpr
        (Or.inl (Finset.mem_filter.mpr ⟨hparent, hfirst⟩))
    · exact Finset.mem_union.mpr
        (Or.inr (Finset.mem_union.mpr
          (Or.inl (Finset.mem_filter.mpr ⟨hparent, hnext⟩))))
    · exact Finset.mem_union.mpr
        (Or.inr (Finset.mem_union.mpr
          (Or.inr (Finset.mem_filter.mpr ⟨hparent, hret⟩))))
  · intro h
    rcases Finset.mem_union.mp h with hfirst | hrest
    · exact (Finset.mem_filter.mp hfirst).1
    · rcases Finset.mem_union.mp hrest with hnext | hret
      · exact (Finset.mem_filter.mp hnext).1
      · exact (Finset.mem_filter.mp hret).1

/-- **Exact signed incomplete-boundary Fubini.** -/
theorem sum_lowOwnerFirstOwnerIncompleteRawParents_eq_threeClipSectors
    {R p r : ℕ} {sig : Finset ℕ} (hp : p.Prime)
    (f : ℕ × ℕ → ℝ) :
    (∑ parent ∈ lowOwnerFirstOwnerIncompletePolarizationRawParentSet R p sig r,
      f parent) =
      (∑ parent ∈ lowOwnerFirstOwnerIncompleteFirstClipSet R p sig r,
        f parent) +
      (∑ parent ∈ lowOwnerFirstOwnerIncompleteNextClipSet R p sig r,
        f parent) +
      ∑ parent ∈ lowOwnerFirstOwnerIncompleteReturnedClipSet R p sig r,
        f parent := by
  rw [lowOwnerFirstOwnerIncompletePolarizationRawParentSet_eq_threeClipUnion hp]
  rw [Finset.sum_union (firstClip_disjoint_nextClip R p sig r |>.mono_right
    (Finset.subset_union_left))]
  rw [Finset.sum_union (nextClip_disjoint_returnedClip R p sig r)]
  ring

end RHLean.Proof
