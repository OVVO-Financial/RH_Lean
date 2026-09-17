import Mathlib
import «research.GLOBAL_RETURNED_CORE_INHERITED_DETERMINISTIC_CANCELLATION»
import «research.GLOBAL_RETURNED_CORE_OWNER_PARENT_CONTINUATION»
import «research.GLOBAL_RETURNED_CORE_UNIQUE_OWNER_RANK_DROP»

/-!
# Exterior-owner bracketing on inherited parent blocks

Every fresh prime remaining on a duplicate-free greatest-owner parent block lies
strictly between the first owner `p` and the stripped greatest owner `r`.

This is the exact label geometry needed before summing deterministic mixed
incidences globally: the `(p,r)` labels form exterior prime faces around every
remaining fresh coordinate of the stripped parent.
-/

noncomputable section

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

private theorem prime_of_mem_squarefreePairFreshPrimeSet_exterior
    {q a b : ℕ}
    (hq : q ∈ squarefreePairFreshPrimeSet a b) :
    q.Prime := by
  simp only [squarefreePairFreshPrimeSet, Finset.mem_union,
    Finset.mem_sdiff] at hq
  rcases hq with hq | hq
  · have hpf : q ∈ a.primeFactors := by
      simpa [squarefreePrimeFace] using hq.1
    exact Nat.prime_of_mem_primeFactors hpf
  · have hpf : q ∈ b.primeFactors := by
      simpa [squarefreePrimeFace] using hq.1
    exact Nat.prime_of_mem_primeFactors hpf

/-- Membership in the fresh set of the ordered stripped parent is equivalent,
up to the harmless coordinate swap used by `squarefreePairPrimeOrderedParent`,
to membership in the raw stripped pair. -/
theorem mem_rawStrippedFresh_of_mem_primeOrderedParentFresh
    {r m n q : ℕ}
    (hq : q ∈ squarefreePairFreshPrimeSet
      (squarefreePairPrimeOrderedParent r m n).1
      (squarefreePairPrimeOrderedParent r m n).2) :
    q ∈ squarefreePairFreshPrimeSet
      (squarefreePrimeFamilyParent r m)
      (squarefreePrimeFamilyParent r n) := by
  unfold squarefreePairPrimeOrderedParent at hq
  dsimp only at hq
  by_cases hlt : squarefreePrimeFamilyParent r m <
      squarefreePrimeFamilyParent r n
  · simpa [hlt] using hq
  · have hswap : q ∈ squarefreePairFreshPrimeSet
        (squarefreePrimeFamilyParent r n)
        (squarefreePrimeFamilyParent r m) := by
      simpa [hlt] using hq
    rw [squarefreePairFreshPrimeSet_comm]
    exact hswap

/-- **Exterior-owner bracket.**  Every fresh coordinate of a duplicate-free
owner-parent block lies strictly between the first owner and greatest owner. -/
theorem lowOwnerFirstOwnerAdmittedGreatestOwnerParentBlock_fresh_between_owners
    {R p r q : ℕ} {sig : Finset ℕ} {parent : ℕ × ℕ}
    (hp : p.Prime)
    (hparent : parent ∈
      lowOwnerFirstOwnerAdmittedGreatestOwnerParentBlocks R p sig r)
    (hq : q ∈ squarefreePairFreshPrimeSet parent.1 parent.2) :
    p < q ∧ q < r := by
  rcases lowOwnerFirstOwnerAdmittedGreatestOwnerParentBlock_has_positiveWitness
      hparent with ⟨m, n, hmn, hparentEq⟩
  have hqOrdered : q ∈ squarefreePairFreshPrimeSet
      (squarefreePairPrimeOrderedParent r m n).1
      (squarefreePairPrimeOrderedParent r m n).2 := by
    simpa [hparentEq] using hq
  have hqr : q < r :=
    lowOwnerFirstOwnerGreatestOwnerPositivePair_parent_fresh_lt_owner
      hp hmn hqOrdered
  have hrData := lowOwnerFirstOwnerGreatestOwnerPositivePair_owner_data hp hmn
  have hrPrime : r.Prime := hrData.1
  have hqRaw := mem_rawStrippedFresh_of_mem_primeOrderedParentFresh hqOrdered
  have hqPrime : q.Prime :=
    prime_of_mem_squarefreePairFreshPrimeSet_exterior hqRaw
  have hqrNe : q ≠ r := Nat.ne_of_lt hqr
  have hoff := (Finset.mem_filter.mp (Finset.mem_filter.mp hmn).1).1
  have hpair := (Finset.mem_filter.mp hoff).1
  rcases Finset.mem_product.mp hpair with ⟨hmAd, hnAd⟩
  have hmCar := (Finset.mem_filter.mp (Finset.mem_filter.mp hmAd).1).1
  have hnCar := (Finset.mem_filter.mp (Finset.mem_filter.mp hnAd).1).1
  have hmPos := (lowOwnerNonzeroMobiusCarrier_squarefree_pos hmCar).2
  have hnPos := (lowOwnerNonzeroMobiusCarrier_squarefree_pos hnCar).2
  have hqChild : q ∈ squarefreePairFreshPrimeSet m n :=
    (mem_freshPrimeSet_stripped_iff_of_ne
      hrPrime hqPrime hqrNe hmPos hnPos).1 hqRaw
  have hpq : p < q :=
    lowOwnerFirstOwnerAdmittedPair_freshPrime_gt_owner hp hmAd hnAd hqChild
  exact ⟨hpq, hqr⟩

end RHLean.Proof
