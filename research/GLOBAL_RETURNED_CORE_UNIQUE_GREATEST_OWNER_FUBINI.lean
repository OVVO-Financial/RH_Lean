import Mathlib
import «research.GLOBAL_RETURNED_CORE_COMPENSATED_CELL_DESCENT_CARRIER»
import «research.GLOBAL_RETURNED_CORE_DESCENDING_PAIR_OWNER»

/-!
# Unique greatest-owner Fubini inside one compensated first-owner cell

This is the combinatorial assembly layer required before any owner-labelled
energy estimate may be summed.

For one admitted `(p,sig)` cell, remove the diagonal and assign every remaining
pair to its greatest fresh-prime coordinate.  The assignment is unique.  Since
all fresh coordinates inside the cell are strictly larger than `p`, every owner
lies in the existing revealed-above-p prime set.

The resulting owner fibres are pairwise disjoint and their biUnion is exactly
the admitted off-diagonal pair carrier.  Consequently arbitrary signed weights
admit an exact finite Fubini over the unique greatest-owner coordinate.

No owner energy is collapsed here, and no `2/9` or `1/9` estimate is used.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Admitted ordered pairs in one compensated cell with the diagonal removed. -/
def lowOwnerFirstOwnerAdmittedOffDiagonalPairCarrier
    (R p : ℕ) (sig : Finset ℕ) : Finset (ℕ × ℕ) :=
  (lowOwnerFirstOwnerAdmittedPairCarrier R p sig).filter fun mn =>
    mn.1 ≠ mn.2

/-- The fibre of admitted off-diagonal pairs whose unique greatest fresh owner
is `r`. -/
def lowOwnerFirstOwnerGreatestOwnerPairFiber
    (R p : ℕ) (sig : Finset ℕ) (r : ℕ) : Finset (ℕ × ℕ) :=
  (lowOwnerFirstOwnerAdmittedOffDiagonalPairCarrier R p sig).filter fun mn =>
    IsSquarefreePairGreatestFreshPrimeOwner r mn.1 mn.2

/-- Two greatest fresh-prime owners of the same pair are equal.  This is the
uniqueness invariant needed to prevent paying an owner-labelled contraction
more than once. -/
theorem squarefreePairGreatestFreshPrimeOwner_unique
    {r s m n : ℕ}
    (hr : IsSquarefreePairGreatestFreshPrimeOwner r m n)
    (hs : IsSquarefreePairGreatestFreshPrimeOwner s m n) :
    r = s := by
  have hrs : s ≤ r := hr.2 s hs.1
  have hsr : r ≤ s := hs.2 r hr.1
  omega

/-- Every admitted off-diagonal pair in one first-owner cell has a greatest
fresh owner, and that owner is a physical prime strictly larger than `p`. -/
theorem lowOwnerFirstOwnerAdmittedOffDiagonalPair_has_greatestOwner
    {R p : ℕ} {sig : Finset ℕ} {m n : ℕ}
    (hp : p.Prime)
    (hmn : (m, n) ∈
      lowOwnerFirstOwnerAdmittedOffDiagonalPairCarrier R p sig) :
    ∃ r ∈ lowOwnerRevealedPrimesAbove R p,
      IsSquarefreePairGreatestFreshPrimeOwner r m n := by
  rcases Finset.mem_filter.mp hmn with ⟨hpair, hne⟩
  rcases Finset.mem_product.mp hpair with ⟨hm, hn⟩
  have hmBase := (Finset.mem_filter.mp hm).1
  have hnBase := (Finset.mem_filter.mp hn).1
  have hmCar := (Finset.mem_filter.mp hmBase).1
  have hnCar := (Finset.mem_filter.mp hnBase).1
  rcases lowOwnerNonzeroMobiusCarrier_squarefree_pos hmCar with
    ⟨hmSq, hmPos⟩
  rcases lowOwnerNonzeroMobiusCarrier_squarefree_pos hnCar with
    ⟨hnSq, hnPos⟩
  have hleast := squarefreePairFreshPrimeOwner_isOwner hmSq hnSq hne
  let S := squarefreePairFreshPrimeSet m n
  have hSnonempty : S.Nonempty := ⟨squarefreePairFreshPrimeOwner m n, hleast.1⟩
  let r := S.max' hSnonempty
  have hrFresh : r ∈ S := Finset.max'_mem S hSnonempty
  have hrGreatest : ∀ q ∈ S, q ≤ r := by
    intro q hq
    exact Finset.le_max' S q hq
  have howner : IsSquarefreePairGreatestFreshPrimeOwner r m n := by
    exact ⟨hrFresh, hrGreatest⟩
  have hrData := freshPrime_of_nonzeroPhysicalPair hmCar hnCar hrFresh
  have hpr := lowOwnerFirstOwnerAdmittedPair_freshPrime_gt_owner
    hp hm hn hrFresh
  refine ⟨r, ?_, howner⟩
  exact Finset.mem_filter.mpr
    ⟨mem_primesUpTo.mpr hrData, hpr⟩

/-- The greatest-owner fibres of one admitted cell are pairwise disjoint. -/
theorem lowOwnerFirstOwnerGreatestOwnerPairFiber_pairwiseDisjoint
    (R p : ℕ) (sig : Finset ℕ) :
    Set.PairwiseDisjoint (↑(lowOwnerRevealedPrimesAbove R p))
      (lowOwnerFirstOwnerGreatestOwnerPairFiber R p sig) := by
  intro r _hr s _hs hrs
  rw [Finset.disjoint_left]
  intro mn hmr hms
  have hro := (Finset.mem_filter.mp hmr).2
  have hso := (Finset.mem_filter.mp hms).2
  exact hrs (squarefreePairGreatestFreshPrimeOwner_unique hro hso)

/-- Exact carrier partition by the unique greatest remaining owner. -/
theorem lowOwnerFirstOwnerGreatestOwnerPairFiber_biUnion
    {R p : ℕ} {sig : Finset ℕ} (hp : p.Prime) :
    (lowOwnerRevealedPrimesAbove R p).biUnion
        (lowOwnerFirstOwnerGreatestOwnerPairFiber R p sig) =
      lowOwnerFirstOwnerAdmittedOffDiagonalPairCarrier R p sig := by
  ext mn
  constructor
  · intro h
    rcases Finset.mem_biUnion.mp h with ⟨r, _hr, hmn⟩
    exact (Finset.mem_filter.mp hmn).1
  · intro hmn
    rcases mn with ⟨m, n⟩
    rcases lowOwnerFirstOwnerAdmittedOffDiagonalPair_has_greatestOwner
      hp hmn with ⟨r, hr, howner⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨r, hr, ?_⟩
    exact Finset.mem_filter.mpr ⟨hmn, howner⟩

/-- **Unique-owner finite signed Fubini.**  Every admitted off-diagonal pair is
charged exactly once, to its greatest fresh owner.  This identity is valid for
an arbitrary signed weight and therefore precedes all energy inequalities. -/
theorem sum_lowOwnerFirstOwnerAdmittedOffDiagonal_eq_sum_greatestOwnerFibers
    {R p : ℕ} {sig : Finset ℕ} (hp : p.Prime)
    (f : ℕ × ℕ → ℝ) :
    (∑ mn ∈ lowOwnerFirstOwnerAdmittedOffDiagonalPairCarrier R p sig,
        f mn) =
      ∑ r ∈ lowOwnerRevealedPrimesAbove R p,
        ∑ mn ∈ lowOwnerFirstOwnerGreatestOwnerPairFiber R p sig r,
          f mn := by
  rw [← lowOwnerFirstOwnerGreatestOwnerPairFiber_biUnion hp]
  exact Finset.sum_biUnion
    (lowOwnerFirstOwnerGreatestOwnerPairFiber_pairwiseDisjoint R p sig)

end RHLean.Proof
