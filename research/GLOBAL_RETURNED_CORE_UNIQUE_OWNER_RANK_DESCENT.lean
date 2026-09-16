import Mathlib
import «research.GLOBAL_RETURNED_CORE_UNIQUE_GREATEST_OWNER_ASSEMBLY»

/-!
# Unique-owner rank descent inside one compensated cell

The final signed Fubini is an induction on the number of remaining fresh-prime
coordinates.  This file proves the exact induction step on the actual admitted
`(p,sig)` pair carrier.

For a pair owned by its unique greatest remaining fresh prime `r`:

* `r` is prime and `p < r`;
* stripping `r` from both endpoints stays inside the same admitted cell;
* the fresh-prime rank drops by exactly one.

The stripped pair is not assigned an additional sibling owner at the current
rank.  Its next owner, if any, is chosen only after the rank has decreased.
-/

noncomputable section

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Data carried by one unique-greatest-owner rank step. -/
theorem lowOwnerFirstOwnerAdmittedGreatestOwner_rank_descent
    {R p r m n : ℕ} {sig : Finset ℕ}
    (hp : p.Prime)
    (hmn : (m, n) ∈
      lowOwnerFirstOwnerAdmittedGreatestOwnerPairFiber R p sig r) :
    let um := squarefreePrimeFamilyParent r m
    let un := squarefreePrimeFamilyParent r n
    r.Prime ∧ p < r ∧
      (um, un) ∈ lowOwnerFirstOwnerAdmittedPairCarrier R p sig ∧
      (squarefreePairFreshPrimeSet um un).card + 1 =
        (squarefreePairFreshPrimeSet m n).card := by
  rcases mem_lowOwnerFirstOwnerAdmittedGreatestOwnerPairFiber.mp hmn with
    ⟨hpair, howner⟩
  rcases Finset.mem_product.mp hpair with ⟨hmAd, hnAd⟩
  have hmCar := (Finset.mem_filter.mp (Finset.mem_filter.mp hmAd).1).1
  have hnCar := (Finset.mem_filter.mp (Finset.mem_filter.mp hnAd).1).1
  rcases lowOwnerNonzeroMobiusCarrier_squarefree_pos hmCar with ⟨hmSq, hmPos⟩
  rcases lowOwnerNonzeroMobiusCarrier_squarefree_pos hnCar with ⟨hnSq, hnPos⟩
  have hrData := freshPrime_of_nonzeroPhysicalPair hmCar hnCar howner.1
  have hrPrime : r.Prime := hrData.1
  have hpr : p < r :=
    lowOwnerFirstOwnerAdmittedPair_freshPrime_gt_owner
      hp hmAd hnAd howner.1
  have hparents :=
    lowOwnerFirstOwnerAdmittedPair_freshPrime_parentPair_mem
      hp hpair howner.1
  have hrank := freshPrimeSet_stripped_card_add_one
    hrPrime hmSq hnSq hmPos hnPos howner.1
  dsimp only
  exact ⟨hrPrime, hpr, hparents, hrank⟩

/-- If the stripped parent is still off-diagonal, its next greatest owner exists
uniquely only at the lower rank.  This is the recursion discipline that keeps
owner labels from being summed against a single current-rank parent block. -/
theorem lowOwnerFirstOwnerAdmittedGreatestOwner_nextOwner_after_rank_drop
    {R p r m n : ℕ} {sig : Finset ℕ}
    (hp : p.Prime)
    (hmn : (m, n) ∈
      lowOwnerFirstOwnerAdmittedGreatestOwnerPairFiber R p sig r)
    (hne : squarefreePrimeFamilyParent r m ≠
      squarefreePrimeFamilyParent r n) :
    ∃! s : ℕ,
      s ∈ primesUpTo (squareRootEndpoint R) ∧ p < s ∧
        (squarefreePrimeFamilyParent r m,
          squarefreePrimeFamilyParent r n) ∈
          lowOwnerFirstOwnerAdmittedGreatestOwnerPairFiber R p sig s := by
  have hstep := lowOwnerFirstOwnerAdmittedGreatestOwner_rank_descent hp hmn
  dsimp only at hstep
  exact lowOwnerFirstOwnerAdmittedPair_existsUnique_greatestOwner
    hp hstep.2.2.1 hne

/-- The lower-rank owner is strictly smaller than the current greatest owner.
This makes the reversed recursion triangular rather than merely terminating by
cardinality. -/
theorem lowOwnerFirstOwnerAdmittedGreatestOwner_nextOwner_lt_current
    {R p r s m n : ℕ} {sig : Finset ℕ}
    (hp : p.Prime)
    (hmn : (m, n) ∈
      lowOwnerFirstOwnerAdmittedGreatestOwnerPairFiber R p sig r)
    (hs : IsSquarefreePairGreatestFreshPrimeOwner s
      (squarefreePrimeFamilyParent r m)
      (squarefreePrimeFamilyParent r n)) :
    s < r := by
  rcases mem_lowOwnerFirstOwnerAdmittedGreatestOwnerPairFiber.mp hmn with
    ⟨hpair, hrOwner⟩
  rcases Finset.mem_product.mp hpair with ⟨hmAd, hnAd⟩
  have hmCar := (Finset.mem_filter.mp (Finset.mem_filter.mp hmAd).1).1
  have hnCar := (Finset.mem_filter.mp (Finset.mem_filter.mp hnAd).1).1
  rcases lowOwnerNonzeroMobiusCarrier_squarefree_pos hmCar with ⟨hmSq, hmPos⟩
  rcases lowOwnerNonzeroMobiusCarrier_squarefree_pos hnCar with ⟨hnSq, hnPos⟩
  have hrPrime := (freshPrime_of_nonzeroPhysicalPair hmCar hnCar hrOwner.1).1
  have hset := freshPrimeSet_stripped_eq_erase
    hrPrime hmSq hnSq hmPos hnPos hrOwner.1
  have hsFresh : s ∈ squarefreePairFreshPrimeSet m n := by
    rw [hset] at hs
    exact (Finset.mem_erase.mp hs.1).2
  have hsle : s ≤ r := hrOwner.2 s hsFresh
  have hsne : s ≠ r := by
    intro heq
    subst s
    rw [hset] at hs
    exact (Finset.mem_erase.mp hs.1).1 rfl
  omega

end RHLean.Proof
