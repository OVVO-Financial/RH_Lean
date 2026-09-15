import Mathlib
import «research.GLOBAL_RETURNED_CORE_UNIQUE_OWNER_CONTINUATION_LEDGER»

/-!
# Exact rank drop on the unique greatest-owner assembly

The induction measure is purely combinatorial and precedes the continuation
case split.  If a positive admitted pair is assigned to its unique greatest
fresh owner `r`, stripping `r` removes exactly that one coordinate from the
fresh-prime symmetric difference.  Reorientation does not change the set size.
Every remaining fresh coordinate is strictly smaller than `r`.
-/

noncomputable section

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Fresh-prime separation rank of an ordered pair. -/
def lowOwnerFreshPairRank (mn : ℕ × ℕ) : ℕ :=
  (squarefreePairFreshPrimeSet mn.1 mn.2).card

/-- **Rank drops by exactly one under the uniquely selected greatest owner.** -/
theorem lowOwnerFirstOwnerGreatestOwnerPositivePair_parent_rank_add_one
    {R p r m n : ℕ} {sig : Finset ℕ}
    (hp : p.Prime)
    (hmn : (m, n) ∈
      lowOwnerFirstOwnerGreatestOwnerPositivePairFiber R p sig r) :
    lowOwnerFreshPairRank (squarefreePairPrimeOrderedParent r m n) + 1 =
      lowOwnerFreshPairRank (m, n) := by
  have howner := lowOwnerFirstOwnerGreatestOwnerPositivePair_owner hmn
  have hownerData :=
    lowOwnerFirstOwnerGreatestOwnerPositivePair_owner_data hp hmn
  have hoff := (Finset.mem_filter.mp (Finset.mem_filter.mp hmn).1).1
  have hpair := (Finset.mem_filter.mp hoff).1
  rcases Finset.mem_product.mp hpair with ⟨hmAd, hnAd⟩
  have hmCar := (Finset.mem_filter.mp (Finset.mem_filter.mp hmAd).1).1
  have hnCar := (Finset.mem_filter.mp (Finset.mem_filter.mp hnAd).1).1
  rcases lowOwnerNonzeroMobiusCarrier_squarefree_pos hmCar with ⟨hmSq, hmPos⟩
  rcases lowOwnerNonzeroMobiusCarrier_squarefree_pos hnCar with ⟨hnSq, hnPos⟩
  have hrankRaw := freshPrimeSet_stripped_card_add_one
    hownerData.1 hmSq hnSq hmPos hnPos howner.1
  unfold lowOwnerFreshPairRank
  rw [squarefreePairFreshPrimeSet_primeOrderedParent_card]
  exact hrankRaw

/-- Every fresh coordinate remaining after the greatest-owner strip is smaller
than the owner just removed. -/
theorem lowOwnerFirstOwnerGreatestOwnerPositivePair_parent_fresh_lt_owner
    {R p r m n q : ℕ} {sig : Finset ℕ}
    (hp : p.Prime)
    (hmn : (m, n) ∈
      lowOwnerFirstOwnerGreatestOwnerPositivePairFiber R p sig r)
    (hq : q ∈ squarefreePairFreshPrimeSet
      (squarefreePairPrimeOrderedParent r m n).1
      (squarefreePairPrimeOrderedParent r m n).2) :
    q < r := by
  have hrData := lowOwnerFirstOwnerGreatestOwnerPositivePair_owner_data hp hmn
  have hcross :=
    lowOwnerFirstOwnerGreatestOwnerPositivePair_mem_descendingCross hp hmn
  exact descendingGreatestOwner_orderedParent_fresh_lt hrData.1 hcross hq

/-- Strict rank decrease, ready for Nat strong induction. -/
theorem lowOwnerFirstOwnerGreatestOwnerPositivePair_parent_rank_lt
    {R p r m n : ℕ} {sig : Finset ℕ}
    (hp : p.Prime)
    (hmn : (m, n) ∈
      lowOwnerFirstOwnerGreatestOwnerPositivePairFiber R p sig r) :
    lowOwnerFreshPairRank (squarefreePairPrimeOrderedParent r m n) <
      lowOwnerFreshPairRank (m, n) := by
  have h := lowOwnerFirstOwnerGreatestOwnerPositivePair_parent_rank_add_one hp hmn
  omega

end RHLean.Proof
