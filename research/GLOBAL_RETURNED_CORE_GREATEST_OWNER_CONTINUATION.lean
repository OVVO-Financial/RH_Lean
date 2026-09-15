import Mathlib
import «research.GLOBAL_RETURNED_CORE_ARBITRARY_FRESH_PRIME_DESCENT»
import «research.GLOBAL_RETURNED_CORE_CONTINUATION_CARRIER»

/-!
# No residual class for the reversed / greatest-owner continuation

The order-independent filtration assigns each off-diagonal pair equally well to
its greatest fresh-prime coordinate.  This file proves that the corresponding
owner descent has the same finite stopping/continuation structure as the old
least-owner recursion.

Let `p` be the greatest fresh prime of a nonzero squarefree remainder pair and
strip `p` from both endpoints.  There are only five possibilities:

1. the two stripped parents coincide; then the current pair is an immediate
   nonpositive terminal `-mu(u)^2`;
2. the larger stripped parent has clipped p-child at the current endpoint;
3. the ordered parent lies in a complete post-root family at endpoint `W/p`;
4. it is an existing nonpositive terminal pair there;
5. it remains recursively in the remainder at `W/p`.

In the recursive case the fresh-prime rank has dropped by exactly one and every
remaining fresh coordinate is strictly smaller than `p`.  Hence reversed owner
recursion is triangular in the opposite prime order.

No norm, magnitude estimate, or RH input is used.
-/

noncomputable section
open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- The two parents obtained by stripping a specified prime are equal. -/
def SquarefreePairPrimeParentsEqual (p : ℕ) (mn : ℕ × ℕ) : Prop :=
  squarefreePrimeFamilyParent p mn.1 =
    squarefreePrimeFamilyParent p mn.2

/-- Reordering the specified-prime parents preserves the fresh-set cardinality. -/
theorem squarefreePairFreshPrimeSet_primeOrderedParent_card
    (p m n : ℕ) :
    (squarefreePairFreshPrimeSet
        (squarefreePairPrimeOrderedParent p m n).1
        (squarefreePairPrimeOrderedParent p m n).2).card =
      (squarefreePairFreshPrimeSet
        (squarefreePrimeFamilyParent p m)
        (squarefreePrimeFamilyParent p n)).card := by
  unfold squarefreePairPrimeOrderedParent
  dsimp only
  split_ifs
  · rfl
  · rw [squarefreePairFreshPrimeSet_comm]

/-- Reordering the specified-prime parents does not change reciprocal pair
energy. -/
theorem postRootCovarianceReciprocalPairEnergy_primeOrderedParent
    (p m n : ℕ) :
    postRootCovarianceReciprocalPairEnergy
        (squarefreePairPrimeOrderedParent p m n) =
      postRootCovarianceReciprocalPairEnergy
        (squarefreePrimeFamilyParent p m,
          squarefreePrimeFamilyParent p n) := by
  unfold squarefreePairPrimeOrderedParent
  dsimp only
  split_ifs
  · rfl
  · unfold postRootCovarianceReciprocalPairEnergy
      postRootCovarianceReciprocalPairAmplitude
    ring

/-- An equal specified-prime parent is immediately favorable: the current
Mobius pair weight is the negative of a square. -/
theorem arbitraryFreshPrime_equalParent_weight_nonpos
    {p m n : ℕ}
    (hp : p.Prime) (hmSq : Squarefree m) (hnSq : Squarefree n)
    (hm : 0 < m) (hn : 0 < n)
    (hxor : (p ∣ m ∧ ¬ p ∣ n) ∨ (p ∣ n ∧ ¬ p ∣ m))
    (heq : squarefreePrimeFamilyParent p m =
      squarefreePrimeFamilyParent p n) :
    realMoebiusStep m * realMoebiusStep n ≤ 0 := by
  rw [arbitraryFreshPrime_pairWeight_eq_neg_parentPairWeight
    hp hmSq hnSq hm hn hxor, heq]
  exact neg_nonpos.mpr (mul_self_nonneg _)

/-- **Greatest-owner immediate terminal is nonpositive.** -/
theorem descendingGreatestOwner_equalParent_weight_nonpos
    {R p m n : ℕ} (hp : p.Prime)
    (hcross : (m, n) ∈ lowOwnerRevealedCrossPairCarrier R
      (lowOwnerRevealedPrimesAbove R p) p)
    (heq : SquarefreePairPrimeParentsEqual p (m, n)) :
    realMoebiusStep m * realMoebiusStep n ≤ 0 := by
  have hprod := (Finset.mem_filter.mp hcross).1
  rcases Finset.mem_product.mp hprod with ⟨hmCar, hnCar⟩
  rcases lowOwnerNonzeroMobiusCarrier_squarefree_pos hmCar with ⟨hmSq, hmPos⟩
  rcases lowOwnerNonzeroMobiusCarrier_squarefree_pos hnCar with ⟨hnSq, hnPos⟩
  have howner := descendingCrossPair_greatestFreshOwner hp hcross
  have hxor :=
    (mem_squarefreePairFreshPrimeSet_iff_prime_dvd_xor hp hmPos hnPos).1
      howner.1
  exact arbitraryFreshPrime_equalParent_weight_nonpos
    hp hmSq hnSq hmPos hnPos hxor heq

/-- After stripping the greatest fresh owner, every remaining fresh coordinate
is strictly smaller than that owner. -/
theorem arbitraryGreatestFreshOwner_stripped_fresh_lt
    {p m n q : ℕ}
    (hp : p.Prime) (hmSq : Squarefree m) (hnSq : Squarefree n)
    (hm : 0 < m) (hn : 0 < n)
    (hgreatest : IsSquarefreePairGreatestFreshPrimeOwner p m n)
    (hq : q ∈ squarefreePairFreshPrimeSet
      (squarefreePrimeFamilyParent p m)
      (squarefreePrimeFamilyParent p n)) :
    q < p := by
  have hset := freshPrimeSet_stripped_eq_erase
    hp hmSq hnSq hm hn hgreatest.1
  rw [hset] at hq
  rcases Finset.mem_erase.mp hq with ⟨hqp, hqOld⟩
  have hqle := hgreatest.2 q hqOld
  omega

/-- The same strict-decrease statement after positive-lag reorientation. -/
theorem descendingGreatestOwner_orderedParent_fresh_lt
    {R p m n q : ℕ} (hp : p.Prime)
    (hcross : (m, n) ∈ lowOwnerRevealedCrossPairCarrier R
      (lowOwnerRevealedPrimesAbove R p) p)
    (hq : q ∈ squarefreePairFreshPrimeSet
      (squarefreePairPrimeOrderedParent p m n).1
      (squarefreePairPrimeOrderedParent p m n).2) :
    q < p := by
  have hprod := (Finset.mem_filter.mp hcross).1
  rcases Finset.mem_product.mp hprod with ⟨hmCar, hnCar⟩
  rcases lowOwnerNonzeroMobiusCarrier_squarefree_pos hmCar with ⟨hmSq, hmPos⟩
  rcases lowOwnerNonzeroMobiusCarrier_squarefree_pos hnCar with ⟨hnSq, hnPos⟩
  have hgreatest := descendingCrossPair_greatestFreshOwner hp hcross
  unfold squarefreePairPrimeOrderedParent at hq
  dsimp only at hq
  split at hq
  · exact arbitraryGreatestFreshOwner_stripped_fresh_lt
      hp hmSq hnSq hmPos hnPos hgreatest hq
  · rw [squarefreePairFreshPrimeSet_comm] at hq
    exact arbitraryGreatestFreshOwner_stripped_fresh_lt
      hp hmSq hnSq hmPos hnPos hgreatest hq

/-- If the specified-prime parents are distinct, their ordered pair is positive
and lies on the current post-root remainder carrier. -/
theorem descendingGreatestOwner_orderedParent_mem_remainder
    {W R p m n : ℕ}
    (hrem : (m, n) ∈ postRootCovarianceRemainderPhysicalPairCarrier W)
    (hp : p.Prime)
    (hcross : (m, n) ∈ lowOwnerRevealedCrossPairCarrier R
      (lowOwnerRevealedPrimesAbove R p) p)
    (hne : ¬ SquarefreePairPrimeParentsEqual p (m, n)) :
    squarefreePairPrimeOrderedParent p m n ∈
      postRootCovarianceRemainderPhysicalPairCarrier W := by
  have hprod := (Finset.mem_filter.mp hcross).1
  rcases Finset.mem_product.mp hprod with ⟨hmCar, hnCar⟩
  have hmPos := (lowOwnerNonzeroMobiusCarrier_squarefree_pos hmCar).2
  have hnPos := (lowOwnerNonzeroMobiusCarrier_squarefree_pos hnCar).2
  exact arbitraryFreshPrime_orderedParent_mem_postRootRemainder
    hrem hp hmPos hnPos hne

/-- **No residual class for one greatest-owner continuation.**

The first alternative is the immediate equal-parent terminal.  If parents are
distinct, the remaining four alternatives are clipped / complete family /
existing terminal / recursive lower-rank.  In the recursive case every
remaining fresh coordinate is strictly smaller than p. -/
theorem descendingGreatestOwner_continuation_has_no_residual_class
    {W R p m n : ℕ}
    (hp : p.Prime)
    (hcross : (m, n) ∈ lowOwnerRevealedCrossPairCarrier R
      (lowOwnerRevealedPrimesAbove R p) p)
    (hrem : (m, n) ∈ postRootCovarianceRemainderPhysicalPairCarrier W) :
    let parent := squarefreePairPrimeOrderedParent p m n
    SquarefreePairPrimeParentsEqual p (m, n) ∨
      W < p * parent.2 ∨
      parent ∈ postRootPrimePhysicalPairUnion (W / p) ∨
      parent ∈ postRootCovarianceRemainderTerminalPairCarrier (W / p) ∨
      (parent ∈ postRootCovarianceRemainderRecursivePairCarrier (W / p) ∧
        (squarefreePairFreshPrimeSet parent.1 parent.2).card + 1 =
          (squarefreePairFreshPrimeSet m n).card ∧
        ∀ q ∈ squarefreePairFreshPrimeSet parent.1 parent.2, q < p) := by
  dsimp only
  by_cases heq : SquarefreePairPrimeParentsEqual p (m, n)
  · exact Or.inl heq
  · right
    let parent := squarefreePairPrimeOrderedParent p m n
    have hparentMem : parent ∈
        postRootCovarianceRemainderPhysicalPairCarrier W := by
      dsimp [parent]
      exact descendingGreatestOwner_orderedParent_mem_remainder
        hrem hp hcross heq
    have hparentPhysical :=
      (mem_postRootCovarianceRemainderPhysicalPairCarrier.mp hparentMem).1
    rcases mem_mertensPositivePhysicalPairCarrier.mp hparentPhysical with
      ⟨ha1, _haW, hb1, _hbW, hab⟩
    by_cases hclip : W < p * parent.2
    · exact Or.inl hclip
    · have hcomplete : p * parent.2 ≤ W := Nat.le_of_not_gt hclip
      have hlower := zeroTargetCriticalCompleteParent_le_lowerEndpoint
        hp.pos (Nat.le_of_lt hab) hcomplete
      have hpartition := lowerEndpointPhysicalPair_remainder_or_postRootFamily
        ha1 hlower.1 hb1 hlower.2 hab
      rcases hpartition with hparentRem | hfamily
      · by_cases hterminal : SquarefreePairFreshPrimeParentsEqual parent
        · exact Or.inr (Or.inr (Or.inl
            (Finset.mem_filter.mpr ⟨hparentRem, hterminal⟩)))
        · have hrecursive :
              parent ∈ postRootCovarianceRemainderRecursivePairCarrier
                (W / p) :=
            Finset.mem_filter.mpr ⟨hparentRem, hterminal⟩
          have hprod := (Finset.mem_filter.mp hcross).1
          rcases Finset.mem_product.mp hprod with ⟨hmCar, hnCar⟩
          rcases lowOwnerNonzeroMobiusCarrier_squarefree_pos hmCar with
            ⟨hmSq, hmPos⟩
          rcases lowOwnerNonzeroMobiusCarrier_squarefree_pos hnCar with
            ⟨hnSq, hnPos⟩
          have hgreatest := descendingCrossPair_greatestFreshOwner hp hcross
          have hrankRaw := freshPrimeSet_stripped_card_add_one
            hp hmSq hnSq hmPos hnPos hgreatest.1
          have hrank :
              (squarefreePairFreshPrimeSet parent.1 parent.2).card + 1 =
                (squarefreePairFreshPrimeSet m n).card := by
            dsimp [parent]
            rw [squarefreePairFreshPrimeSet_primeOrderedParent_card]
            exact hrankRaw
          have hlt :
              ∀ q ∈ squarefreePairFreshPrimeSet parent.1 parent.2, q < p := by
            intro q hq
            dsimp [parent] at hq
            exact descendingGreatestOwner_orderedParent_fresh_lt hp hcross hq
          exact Or.inr (Or.inr (Or.inr ⟨hrecursive, hrank, hlt⟩))
      · exact Or.inr (Or.inl hfamily)

end RHLean.Proof
