import Mathlib
import «research.GLOBAL_RETURNED_CORE_UNIQUE_OWNER_CONTINUATION_LEDGER»
import «research.GLOBAL_RETURNED_CORE_THRESHOLD_DIRECT_SUM_CONTRACTION»

/-!
# Unique greatest-owner / stripped-parent Fubini

A unique owner is not by itself enough to prevent double charging: applying a
fixed-parent fibre estimate once for each child would count the same two-child
fibre twice.  This file performs the second exact Fubini required by the global
assembly.

Inside one positive `(p,sig,r)` owner fibre, group children by their stripped
ordered parent.  These parent fibres are pairwise disjoint and their biUnion is
exactly the owner fibre.  The cell-specific parent fibre is a subset of the
literal greatest-owner fixed-parent fibre, so every child inherits exactly
`1/r^2` reciprocal energy from that parent and its cardinality is at most two.

The recursive subfibre is obtained only after the named continuation
classification and excludes clipped, terminal, and complete-family exits.
No clipped energy estimate appears here.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Stripped ordered parents actually occurring in one positive unique-owner
fibre. -/
def lowOwnerFirstOwnerGreatestOwnerParentSet
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : Finset (ℕ × ℕ) :=
  (lowOwnerFirstOwnerGreatestOwnerPositivePairFiber R p sig r).image
    (fun mn => squarefreePairPrimeOrderedParent r mn.1 mn.2)

/-- Cell-specific children with both greatest owner and stripped parent fixed. -/
def lowOwnerFirstOwnerGreatestOwnerFixedParentCellFiber
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ)
    (parent : ℕ × ℕ) : Finset (ℕ × ℕ) :=
  (lowOwnerFirstOwnerGreatestOwnerPositivePairFiber R p sig r).filter
    (fun mn => squarefreePairPrimeOrderedParent r mn.1 mn.2 = parent)

/-- Fixed-parent cell fibres are pairwise disjoint. -/
theorem lowOwnerFirstOwnerGreatestOwnerFixedParentCellFiber_pairwiseDisjoint
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) :
    Set.PairwiseDisjoint
      (↑(lowOwnerFirstOwnerGreatestOwnerParentSet R p sig r))
      (lowOwnerFirstOwnerGreatestOwnerFixedParentCellFiber R p sig r) := by
  intro parent _hp childParent _hc hne
  change Disjoint
    (lowOwnerFirstOwnerGreatestOwnerFixedParentCellFiber R p sig r parent)
    (lowOwnerFirstOwnerGreatestOwnerFixedParentCellFiber R p sig r childParent)
  rw [Finset.disjoint_left]
  intro mn hmp hmc
  have hpEq := (Finset.mem_filter.mp hmp).2
  have hcEq := (Finset.mem_filter.mp hmc).2
  exact hne (hpEq.symm.trans hcEq)

/-- Exact parent partition inside one owner fibre. -/
theorem lowOwnerFirstOwnerGreatestOwnerFixedParentCellFiber_biUnion
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) :
    (lowOwnerFirstOwnerGreatestOwnerParentSet R p sig r).biUnion
        (lowOwnerFirstOwnerGreatestOwnerFixedParentCellFiber R p sig r) =
      lowOwnerFirstOwnerGreatestOwnerPositivePairFiber R p sig r := by
  ext mn
  constructor
  · intro h
    rcases Finset.mem_biUnion.mp h with ⟨parent, _hparent, hmn⟩
    exact (Finset.mem_filter.mp hmn).1
  · intro hmn
    let parent := squarefreePairPrimeOrderedParent r mn.1 mn.2
    apply Finset.mem_biUnion.mpr
    refine ⟨parent, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨mn, hmn, rfl⟩
    · exact Finset.mem_filter.mpr ⟨hmn, rfl⟩

/-- Signed Fubini by stripped parent inside one unique-owner fibre. -/
theorem sum_lowOwnerFirstOwnerGreatestOwnerPositivePairFiber_eq_sum_parentFibers
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ)
    (f : ℕ × ℕ → ℝ) :
    (∑ mn ∈ lowOwnerFirstOwnerGreatestOwnerPositivePairFiber R p sig r,
        f mn) =
      ∑ parent ∈ lowOwnerFirstOwnerGreatestOwnerParentSet R p sig r,
        ∑ mn ∈ lowOwnerFirstOwnerGreatestOwnerFixedParentCellFiber
            R p sig r parent,
          f mn := by
  rw [← lowOwnerFirstOwnerGreatestOwnerFixedParentCellFiber_biUnion]
  exact Finset.sum_biUnion
    (lowOwnerFirstOwnerGreatestOwnerFixedParentCellFiber_pairwiseDisjoint
      R p sig r)

/-- A cell-specific fixed-parent child is a literal child in the full greatest-
owner graph for the same parent and owner. -/
theorem lowOwnerFirstOwnerGreatestOwnerFixedParentCellFiber_subset_graph
    {R p r : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (hp : p.Prime) :
    lowOwnerFirstOwnerGreatestOwnerFixedParentCellFiber R p sig r parent ⊆
      lowOwnerGreatestOwnerFixedParentChildFiber R parent r := by
  intro mn hmn
  rcases Finset.mem_filter.mp hmn with ⟨hpos, hparent⟩
  have hgraph :=
    lowOwnerFirstOwnerGreatestOwnerPositivePair_mem_fixedParentChildFiber
      hp hpos
  simpa [hparent] using hgraph

/-- Cell-specific fixed-parent multiplicity is at most two. -/
theorem lowOwnerFirstOwnerGreatestOwnerFixedParentCellFiber_card_le_two
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) (parent : ℕ × ℕ)
    (hp : p.Prime) :
    (lowOwnerFirstOwnerGreatestOwnerFixedParentCellFiber
      R p sig r parent).card ≤ 2 := by
  exact (Finset.card_le_card
    (lowOwnerFirstOwnerGreatestOwnerFixedParentCellFiber_subset_graph
      (R := R) (p := p) (r := r) (sig := sig) (parent := parent) hp)).trans
    (lowOwnerGreatestOwnerFixedParentChildFiber_card_le_two R parent r)

/-- Exact reciprocal-energy inheritance on the cell-specific parent fibre. -/
theorem sum_lowOwnerFirstOwnerGreatestOwnerFixedParentCellFiber_energy_eq
    {R p r : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (hp : p.Prime) (hr : r.Prime) :
    (∑ child ∈ lowOwnerFirstOwnerGreatestOwnerFixedParentCellFiber
        R p sig r parent,
      postRootCovarianceReciprocalPairEnergy child) =
      ((lowOwnerFirstOwnerGreatestOwnerFixedParentCellFiber
          R p sig r parent).card : ℝ) /
        (r : ℝ) ^ 2 * postRootCovarianceReciprocalPairEnergy parent := by
  calc
    (∑ child ∈ lowOwnerFirstOwnerGreatestOwnerFixedParentCellFiber
        R p sig r parent,
      postRootCovarianceReciprocalPairEnergy child) =
      ∑ _child ∈ lowOwnerFirstOwnerGreatestOwnerFixedParentCellFiber
          R p sig r parent,
        (1 / (r : ℝ) ^ 2) *
          postRootCovarianceReciprocalPairEnergy parent := by
      apply Finset.sum_congr rfl
      intro child hchild
      exact lowOwnerGreatestOwnerFixedParentChild_energy_eq hr
        (lowOwnerFirstOwnerGreatestOwnerFixedParentCellFiber_subset_graph hp hchild)
    _ = ((lowOwnerFirstOwnerGreatestOwnerFixedParentCellFiber
          R p sig r parent).card : ℝ) /
        (r : ℝ) ^ 2 * postRootCovarianceReciprocalPairEnergy parent := by
      simp [div_eq_mul_inv]
      ring

/-- Owner-labelled inherited energy on one cell-specific fixed-parent fibre. -/
def lowOwnerFirstOwnerGreatestOwnerFixedParentInheritedEnergy
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ)
    (parent : ℕ × ℕ) : ℝ :=
  ∑ child ∈ lowOwnerFirstOwnerGreatestOwnerFixedParentCellFiber
      R p sig r parent,
    lowOwnerThresholdEulerInheritedGreatestChildEnergy
      R p r parent child

/-- Exact multiplicity/r^2 formula with the owner-labelled Euler coefficient
retained. -/
theorem lowOwnerFirstOwnerGreatestOwnerFixedParentInheritedEnergy_eq
    {R p r : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (hp : p.Prime) (hr : r.Prime) :
    lowOwnerFirstOwnerGreatestOwnerFixedParentInheritedEnergy
        R p sig r parent =
      ((lowOwnerFirstOwnerGreatestOwnerFixedParentCellFiber
          R p sig r parent).card : ℝ) /
        (r : ℝ) ^ 2 *
          lowOwnerThresholdEulerParentEnergy R p r parent := by
  unfold lowOwnerFirstOwnerGreatestOwnerFixedParentInheritedEnergy
    lowOwnerThresholdEulerInheritedGreatestChildEnergy
    lowOwnerThresholdEulerParentEnergy
  rw [← Finset.mul_sum]
  rw [sum_lowOwnerFirstOwnerGreatestOwnerFixedParentCellFiber_energy_eq hp hr]
  ring

/-- **No-congestion local charge.**  One `(r,parent)` block is paid exactly
once and costs at most `2/9` of its own owner-labelled parent energy. -/
theorem lowOwnerFirstOwnerGreatestOwnerFixedParentInheritedEnergy_le_two_ninths
    {R p r : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (hp : p.Prime) (hr : r.Prime) (hpr : p < r) :
    lowOwnerFirstOwnerGreatestOwnerFixedParentInheritedEnergy
        R p sig r parent ≤
      (2 / 9 : ℝ) * lowOwnerThresholdEulerParentEnergy R p r parent := by
  rw [lowOwnerFirstOwnerGreatestOwnerFixedParentInheritedEnergy_eq hp hr]
  have hp2 : 2 ≤ p := hp.two_le
  have hr3nat : 3 ≤ r := by omega
  have hr3 : (3 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr3nat
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr.pos
  have hcardNat :=
    lowOwnerFirstOwnerGreatestOwnerFixedParentCellFiber_card_le_two
      R p sig r parent hp
  have hcard :
      ((lowOwnerFirstOwnerGreatestOwnerFixedParentCellFiber
          R p sig r parent).card : ℝ) ≤ 2 := by
    exact_mod_cast hcardNat
  have hratio :
      ((lowOwnerFirstOwnerGreatestOwnerFixedParentCellFiber
          R p sig r parent).card : ℝ) / (r : ℝ) ^ 2 ≤ 2 / 9 := by
    have hsquare : (9 : ℝ) ≤ (r : ℝ) ^ 2 := by nlinarith
    have hdenpos : (0 : ℝ) < (r : ℝ) ^ 2 := sq_pos_of_pos hrpos
    calc
      ((lowOwnerFirstOwnerGreatestOwnerFixedParentCellFiber
          R p sig r parent).card : ℝ) / (r : ℝ) ^ 2 ≤
          2 / (r : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hcard (le_of_lt hdenpos)
      _ ≤ 2 / 9 := by
        exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hsquare
  exact mul_le_mul_of_nonneg_right hratio
    (lowOwnerThresholdEulerParentEnergy_nonneg R p r parent)

/-- Recursive members of one owner fibre.  The filter is applied only after
unique-owner selection and the named continuation classification. -/
def lowOwnerFirstOwnerGreatestOwnerRecursivePairFiber
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : Finset (ℕ × ℕ) :=
  (lowOwnerFirstOwnerGreatestOwnerPositivePairFiber R p sig r).filter fun mn =>
    let parent := squarefreePairPrimeOrderedParent r mn.1 mn.2
    parent ∈ postRootCovarianceRemainderRecursivePairCarrier
      (squareRootEndpoint R / r)

/-- The recursive filter introduces no new carrier class: every recursive pair
is still in its unique greatest-owner positive fibre. -/
theorem lowOwnerFirstOwnerGreatestOwnerRecursivePairFiber_subset
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) :
    lowOwnerFirstOwnerGreatestOwnerRecursivePairFiber R p sig r ⊆
      lowOwnerFirstOwnerGreatestOwnerPositivePairFiber R p sig r := by
  intro mn hmn
  exact (Finset.mem_filter.mp hmn).1

end RHLean.Proof
