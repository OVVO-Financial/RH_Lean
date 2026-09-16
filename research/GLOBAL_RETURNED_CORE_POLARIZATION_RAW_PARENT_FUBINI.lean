import Mathlib
import «research.GLOBAL_RETURNED_CORE_POLARIZATION_UNIQUE_OWNER_FUBINI»
import «research.GLOBAL_RETURNED_CORE_GREATEST_OWNER_CONGESTION»
import «research.GLOBAL_RETURNED_CORE_UNIQUE_OWNER_RANK_DROP»
import «research.GLOBAL_RETURNED_CORE_DIRICHLET_POLARIZATION_OWNER_CUBE»

/-!
# Raw-parent Fubini on the full Dirichlet polarization carrier

For the signed cancellation, sorting the stripped parent is unnecessary and
obscures the literal four-corner cube.  This file therefore groups the full
polarization greatest-owner fibre by the orientation-preserving raw parent

  (parent_r(m), parent_r(n)).

Every child in one such fibre is one of the two literal mixed corners

  (r*a,b), (a,r*b),

its raw parent stays in the same p/signature base cell, both parent coordinates
are r-free, and the fresh-prime rank drops exactly one.  The raw-parent fibres
are disjoint and give an exact signed Fubini.

No magnitude estimate is used.  This is the carrier layer needed to complete
each owner fibre to a Dirichlet four-corner before applying the already compiled
currency theorem.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Orientation-preserving parent obtained by stripping r from both endpoints. -/
def lowOwnerFirstOwnerPolarizationRawParent
    (r : ℕ) (mn : ℕ × ℕ) : ℕ × ℕ :=
  (squarefreePrimeFamilyParent r mn.1,
    squarefreePrimeFamilyParent r mn.2)

/-- Raw parents actually occurring in one full-polarization owner fibre. -/
def lowOwnerFirstOwnerPolarizationRawParentSet
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : Finset (ℕ × ℕ) :=
  (lowOwnerFirstOwnerPolarizationGreatestOwnerPairFiber R p sig r).image
    (lowOwnerFirstOwnerPolarizationRawParent r)

/-- Children in one full-polarization owner fibre with raw parent fixed. -/
def lowOwnerFirstOwnerPolarizationFixedRawParentFiber
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ)
    (parent : ℕ × ℕ) : Finset (ℕ × ℕ) :=
  (lowOwnerFirstOwnerPolarizationGreatestOwnerPairFiber R p sig r).filter
    (fun mn => lowOwnerFirstOwnerPolarizationRawParent r mn = parent)

/-- Fixed raw-parent fibres are pairwise disjoint. -/
theorem lowOwnerFirstOwnerPolarizationFixedRawParentFiber_pairwiseDisjoint
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) :
    Set.PairwiseDisjoint
      (↑(lowOwnerFirstOwnerPolarizationRawParentSet R p sig r))
      (lowOwnerFirstOwnerPolarizationFixedRawParentFiber R p sig r) := by
  intro parent _hp other _ho hne
  change Disjoint
    (lowOwnerFirstOwnerPolarizationFixedRawParentFiber R p sig r parent)
    (lowOwnerFirstOwnerPolarizationFixedRawParentFiber R p sig r other)
  rw [Finset.disjoint_left]
  intro mn hmp hmo
  have hpEq := (Finset.mem_filter.mp hmp).2
  have hoEq := (Finset.mem_filter.mp hmo).2
  exact hne (hpEq.symm.trans hoEq)

/-- Exact partition of a full-polarization owner fibre by raw stripped parent. -/
theorem lowOwnerFirstOwnerPolarizationFixedRawParentFiber_biUnion
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) :
    (lowOwnerFirstOwnerPolarizationRawParentSet R p sig r).biUnion
        (lowOwnerFirstOwnerPolarizationFixedRawParentFiber R p sig r) =
      lowOwnerFirstOwnerPolarizationGreatestOwnerPairFiber R p sig r := by
  ext mn
  constructor
  · intro h
    rcases Finset.mem_biUnion.mp h with ⟨parent, _hparent, hmn⟩
    exact (Finset.mem_filter.mp hmn).1
  · intro hmn
    let parent := lowOwnerFirstOwnerPolarizationRawParent r mn
    exact Finset.mem_biUnion.mpr
      ⟨parent, Finset.mem_image.mpr ⟨mn, hmn, rfl⟩,
        Finset.mem_filter.mpr ⟨hmn, rfl⟩⟩

/-- Exact signed Fubini by orientation-preserving raw parent. -/
theorem sum_lowOwnerFirstOwnerPolarizationGreatestOwnerPairFiber_eq_rawParents
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ)
    (f : ℕ × ℕ → ℝ) :
    (∑ mn ∈ lowOwnerFirstOwnerPolarizationGreatestOwnerPairFiber R p sig r,
        f mn) =
      ∑ parent ∈ lowOwnerFirstOwnerPolarizationRawParentSet R p sig r,
        ∑ mn ∈ lowOwnerFirstOwnerPolarizationFixedRawParentFiber
            R p sig r parent,
          f mn := by
  rw [← lowOwnerFirstOwnerPolarizationFixedRawParentFiber_biUnion]
  exact Finset.sum_biUnion
    (lowOwnerFirstOwnerPolarizationFixedRawParentFiber_pairwiseDisjoint
      R p sig r)

/-- The raw parent of a greatest-owner child remains in the same full base cell. -/
theorem lowOwnerFirstOwnerPolarization_child_rawParent_mem_same_cell
    {R p r : ℕ} {sig : Finset ℕ} {mn : ℕ × ℕ}
    (hp : p.Prime)
    (hmn : mn ∈
      lowOwnerFirstOwnerPolarizationGreatestOwnerPairFiber R p sig r) :
    (lowOwnerFirstOwnerPolarizationRawParent r mn).1 ∈
        lowOwnerFirstOwnerBaseFiber R p sig ∧
      (lowOwnerFirstOwnerPolarizationRawParent r mn).2 ∈
        lowOwnerFirstOwnerBaseFiber R p sig := by
  rcases mn with ⟨m, n⟩
  rcases Finset.mem_filter.mp hmn with ⟨hoff, howner⟩
  rcases Finset.mem_filter.mp hoff with ⟨hprod, _hne⟩
  rcases Finset.mem_product.mp hprod with ⟨hmBase, hnBase⟩
  have hparents :=
    lowOwnerFirstOwnerBasePair_freshPrime_parents_mem_same_cell
      hp hmBase hnBase howner.1
  simpa [lowOwnerFirstOwnerPolarizationRawParent] using hparents

/-- Both coordinates of an occurring raw parent are r-free. -/
theorem lowOwnerFirstOwnerPolarization_child_rawParent_not_dvd
    {R p r : ℕ} {sig : Finset ℕ} {mn : ℕ × ℕ}
    (hmn : mn ∈
      lowOwnerFirstOwnerPolarizationGreatestOwnerPairFiber R p sig r) :
    ¬ r ∣ (lowOwnerFirstOwnerPolarizationRawParent r mn).1 ∧
      ¬ r ∣ (lowOwnerFirstOwnerPolarizationRawParent r mn).2 := by
  rcases mn with ⟨m, n⟩
  rcases Finset.mem_filter.mp hmn with ⟨hoff, howner⟩
  rcases Finset.mem_filter.mp hoff with ⟨hprod, _hne⟩
  rcases Finset.mem_product.mp hprod with ⟨hmBase, hnBase⟩
  have hmCar := (Finset.mem_filter.mp hmBase).1
  have hnCar := (Finset.mem_filter.mp hnBase).1
  rcases lowOwnerNonzeroMobiusCarrier_squarefree_pos hmCar with ⟨hmSq, _hmPos⟩
  rcases lowOwnerNonzeroMobiusCarrier_squarefree_pos hnCar with ⟨hnSq, _hnPos⟩
  have hr := (freshPrime_of_nonzeroPhysicalPair hmCar hnCar howner.1).1
  exact ⟨by
      simpa [lowOwnerFirstOwnerPolarizationRawParent] using
        (squarefreePrimeFamilyParent_not_dvd hr hmSq),
    by
      simpa [lowOwnerFirstOwnerPolarizationRawParent] using
        (squarefreePrimeFamilyParent_not_dvd hr hnSq)⟩

/-- Every child with fixed raw parent is one of the two literal mixed r-corners. -/
theorem lowOwnerFirstOwnerPolarizationFixedRawParentFiber_child_mixed
    {R p r : ℕ} {sig : Finset ℕ} {parent child : ℕ × ℕ}
    (hchild : child ∈
      lowOwnerFirstOwnerPolarizationFixedRawParentFiber
        R p sig r parent) :
    child = (r * parent.1, parent.2) ∨
      child = (parent.1, r * parent.2) := by
  rcases child with ⟨m, n⟩
  rcases Finset.mem_filter.mp hchild with ⟨hmn, hparent⟩
  rcases Finset.mem_filter.mp hmn with ⟨hoff, howner⟩
  rcases Finset.mem_filter.mp hoff with ⟨hprod, _hne⟩
  rcases Finset.mem_product.mp hprod with ⟨hmBase, hnBase⟩
  have hmCar := (Finset.mem_filter.mp hmBase).1
  have hnCar := (Finset.mem_filter.mp hnBase).1
  have hr := (freshPrime_of_nonzeroPhysicalPair hmCar hnCar howner.1).1
  have hcross := greatestFreshOwner_descendingCrossPair
    hr hmCar hnCar howner
  have hmix := revealedCrossPair_parentCube hcross
  dsimp only at hmix
  have hparent' :
      (squarefreePrimeFamilyParent r m,
        squarefreePrimeFamilyParent r n) = parent := by
    simpa [lowOwnerFirstOwnerPolarizationRawParent] using hparent
  rcases parent with ⟨a, b⟩
  simp only [Prod.mk.injEq] at hparent'
  rcases hparent' with ⟨ha, hb⟩
  rcases hmix with hmix | hmix
  · left
    rcases hmix with ⟨hm, hn⟩
    simp only [Prod.mk.injEq]
    exact ⟨hm.trans (congrArg (fun z => r * z) ha), hn.trans hb⟩
  · right
    rcases hmix with ⟨hm, hn⟩
    simp only [Prod.mk.injEq]
    exact ⟨hm.trans ha, hn.trans (congrArg (fun z => r * z) hb)⟩

/-- Fixed raw-parent multiplicity is at most two. -/
theorem lowOwnerFirstOwnerPolarizationFixedRawParentFiber_card_le_two
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) (parent : ℕ × ℕ) :
    (lowOwnerFirstOwnerPolarizationFixedRawParentFiber
      R p sig r parent).card ≤ 2 := by
  let candidates : Finset (ℕ × ℕ) :=
    {(r * parent.1, parent.2), (parent.1, r * parent.2)}
  have hsub :
      lowOwnerFirstOwnerPolarizationFixedRawParentFiber R p sig r parent ⊆
        candidates := by
    intro child hchild
    rcases lowOwnerFirstOwnerPolarizationFixedRawParentFiber_child_mixed
      hchild with h | h
    · simp [candidates, h]
    · simp [candidates, h]
  have hcard := Finset.card_le_card hsub
  have hcand : candidates.card ≤ 2 := by
    simp [candidates]
  exact hcard.trans hcand

/-- Raw-parent rank is exactly one below every child in its owner fibre. -/
theorem lowOwnerFirstOwnerPolarizationFixedRawParentFiber_parent_rank_add_one
    {R p r : ℕ} {sig : Finset ℕ} {parent child : ℕ × ℕ}
    (hchild : child ∈
      lowOwnerFirstOwnerPolarizationFixedRawParentFiber
        R p sig r parent) :
    lowOwnerFreshPairRank parent + 1 = lowOwnerFreshPairRank child := by
  rcases child with ⟨m, n⟩
  rcases Finset.mem_filter.mp hchild with ⟨hmn, hparent⟩
  rcases Finset.mem_filter.mp hmn with ⟨hoff, howner⟩
  rcases Finset.mem_filter.mp hoff with ⟨hprod, _hne⟩
  rcases Finset.mem_product.mp hprod with ⟨hmBase, hnBase⟩
  have hmCar := (Finset.mem_filter.mp hmBase).1
  have hnCar := (Finset.mem_filter.mp hnBase).1
  rcases lowOwnerNonzeroMobiusCarrier_squarefree_pos hmCar with ⟨hmSq, hmPos⟩
  rcases lowOwnerNonzeroMobiusCarrier_squarefree_pos hnCar with ⟨hnSq, hnPos⟩
  have hr := (freshPrime_of_nonzeroPhysicalPair hmCar hnCar howner.1).1
  have hrank := freshPrimeSet_stripped_card_add_one
    hr hmSq hnSq hmPos hnPos howner.1
  unfold lowOwnerFreshPairRank
  have hparent' :
      (squarefreePrimeFamilyParent r m,
        squarefreePrimeFamilyParent r n) = parent := by
    simpa [lowOwnerFirstOwnerPolarizationRawParent] using hparent
  rw [← hparent']
  exact hrank

end RHLean.Proof
