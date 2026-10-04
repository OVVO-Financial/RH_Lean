import Mathlib
import «research.RECIPROCAL_COVARIANCE_PAIR_AMPLITUDE_CONTRACTION»

/-!
# Covariance remainder owner Fubini

The zero-target covariance descent uses the total number of nonzero recursive
children stripping to one ordered parent.  The reciprocal contraction uses the
same children split by their unique chronological owner prime.

This file proves those are literally the same finite population:

  totalParentMultiplicity(W,parent)
    = sum_{p prime <= W} fixedOwnerMultiplicity(W,parent,p).

No estimate is used.  This is the carrier-level splice needed before applying
the reciprocal-square owner weights and the existing 79/81 contraction.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Nonzero recursive children with one stripped ordered parent fixed, before
splitting by their unique owner prime. -/
def postRootCovarianceFixedParentChildFiber
    (W : ℕ) (parent : ℕ × ℕ) : Finset (ℕ × ℕ) :=
  ((postRootCovarianceRemainderRecursivePairCarrier W).filter
      (fun mn => realMoebiusStep mn.1 * realMoebiusStep mn.2 ≠ 0)).filter
    (fun mn => squarefreePairFreshPrimeOrderedParent mn.1 mn.2 = parent)

/-- The aggregate multiplicity from EndpointCubeAnalyticClosure is exactly the
cardinality of the fixed-parent child fibre. -/
theorem postRootCovarianceRemainderOwnerChildMultiplicity_eq_fixedParent_card
    (W : ℕ) (parent : ℕ × ℕ) :
    postRootCovarianceRemainderOwnerChildMultiplicity W parent =
      (postRootCovarianceFixedParentChildFiber W parent).card := by
  rfl

/-- Every child in a fixed-parent fibre has its unique chronological owner in
the physical prime universe through W. -/
theorem postRootCovarianceFixedParentChild_owner_mem_primesUpTo
    {W : ℕ} {parent mn : ℕ × ℕ}
    (hmn : mn ∈ postRootCovarianceFixedParentChildFiber W parent) :
    squarefreePairFreshPrimeOwner mn.1 mn.2 ∈ primesUpTo W := by
  rcases mn with ⟨m, n⟩
  rcases Finset.mem_filter.mp hmn with ⟨hweightFilter, _hparent⟩
  rcases Finset.mem_filter.mp hweightFilter with ⟨hrec, hweight⟩
  rcases Finset.mem_filter.mp hrec with ⟨hremainder, _hparentNe⟩
  have hphysical :=
    (mem_postRootCovarianceRemainderPhysicalPairCarrier.mp hremainder).1
  rcases mem_mertensPositivePhysicalPairCarrier.mp hphysical with
    ⟨hm1, hmW, hn1, hnW, hmnlt⟩
  have hmstep : realMoebiusStep m ≠ 0 := by
    intro hmzero
    exact hweight (by rw [hmzero, zero_mul])
  have hnstep : realMoebiusStep n ≠ 0 := by
    intro hnzero
    exact hweight (by rw [hnzero, mul_zero])
  have hmsq : Squarefree m := squarefree_of_realMoebiusStep_ne_zero hmstep
  have hnsq : Squarefree n := squarefree_of_realMoebiusStep_ne_zero hnstep
  have hmnne : m ≠ n := ne_of_lt hmnlt
  have hp :=
    squarefreePairFreshPrimeOwner_prime hmsq hnsq hmnne
  have hxor :=
    squarefreePairFreshPrimeOwner_dvd_xor
      hmsq hnsq hmnne (by omega) (by omega)
  have hpW : squarefreePairFreshPrimeOwner m n ≤ W := by
    rcases hxor with hxor | hxor
    · exact (Nat.le_of_dvd (by omega : 0 < m) hxor.1).trans hmW
    · exact (Nat.le_of_dvd (by omega : 0 < n) hxor.1).trans hnW
  exact mem_primesUpTo.mpr ⟨hp, hpW⟩

/-- Splitting the fixed-parent fibre at owner p gives exactly the existing
fixed-owner/fixed-parent child fibre. -/
theorem postRootCovarianceFixedParentChildFiber_filter_owner_eq
    (W : ℕ) (parent : ℕ × ℕ) (p : ℕ) :
    (postRootCovarianceFixedParentChildFiber W parent).filter
        (fun mn => squarefreePairFreshPrimeOwner mn.1 mn.2 = p) =
      postRootCovarianceFixedOwnerChildFiber W parent p := by
  ext mn
  simp only [postRootCovarianceFixedParentChildFiber,
    postRootCovarianceFixedOwnerChildFiber, Finset.mem_filter]
  aesop

/-- **Exact owner Fubini for child multiplicity.**

The raw aggregate multiplicity is the sum of the literal fixed-owner
multiplicities.  The strict reciprocal-square contraction can therefore be
applied to this exact child population after the q^-2 weights are retained. -/
theorem postRootCovarianceRemainderOwnerChildMultiplicity_eq_sum_fixedOwner
    (W : ℕ) (parent : ℕ × ℕ) :
    postRootCovarianceRemainderOwnerChildMultiplicity W parent =
      ∑ p ∈ primesUpTo W,
        postRootCovarianceFixedOwnerChildMultiplicity W parent p := by
  let S := postRootCovarianceFixedParentChildFiber W parent
  let O := primesUpTo W
  let owner : ℕ × ℕ → ℕ :=
    fun mn => squarefreePairFreshPrimeOwner mn.1 mn.2
  have hmaps : ∀ mn ∈ S, owner mn ∈ O := by
    intro mn hmn
    exact postRootCovarianceFixedParentChild_owner_mem_primesUpTo hmn
  have hfiber :=
    Finset.sum_fiberwise_of_maps_to
      (s := S) (t := O) (g := owner) hmaps (fun _ => (1 : ℕ))
  have hraw :
      (∑ mn ∈ S, (1 : ℕ)) =
        ∑ p ∈ O, ∑ mn ∈ S with owner mn = p, (1 : ℕ) :=
    hfiber.symm
  rw [postRootCovarianceRemainderOwnerChildMultiplicity_eq_fixedParent_card]
  calc
    (postRootCovarianceFixedParentChildFiber W parent).card =
        ∑ mn ∈ S, (1 : ℕ) := by
          dsimp [S]
          rw [Finset.card_eq_sum_ones]
    _ = ∑ p ∈ O, ∑ mn ∈ S with owner mn = p, (1 : ℕ) := hraw
    _ = ∑ p ∈ primesUpTo W,
          postRootCovarianceFixedOwnerChildMultiplicity W parent p := by
      dsimp [O, S, owner]
      apply Finset.sum_congr rfl
      intro p hp
      rw [← Finset.card_eq_sum_ones]
      rw [postRootCovarianceFixedParentChildFiber_filter_owner_eq]
      rfl

end RHLean.Proof
