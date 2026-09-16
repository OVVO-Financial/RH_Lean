import Mathlib
import «research.GLOBAL_RETURNED_CORE_ARBITRARY_PRIME_FILTRATION»

/-!
# Descending pair owner: the greatest fresh prime

Apply the arbitrary revealed-coordinate filtration with all prime coordinates
strictly larger than the current prime `p` already revealed.  A p-crossing pair
then agrees at every larger prime and disagrees at p.  Equivalently, p is the
greatest prime coordinate on which the two squarefree sites differ.

This is the exact pair-space owner for a descending prime chronology.  It is the
order-reversed counterpart of the repository's least-fresh-prime owner used by
the ascending first-separation Gram.
-/

noncomputable section

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Prime coordinates above p that can occur on the physical common clock. -/
def lowOwnerRevealedPrimesAbove (R p : ℕ) : Finset ℕ :=
  (primesUpTo (squareRootEndpoint R)).filter fun q => p < q

/-- p is the greatest prime coordinate on which the two squarefree faces
disagree. -/
def IsSquarefreePairGreatestFreshPrimeOwner
    (p m n : ℕ) : Prop :=
  p ∈ squarefreePairFreshPrimeSet m n ∧
    ∀ q ∈ squarefreePairFreshPrimeSet m n, q ≤ p

/-- General fresh-set membership is exactly prime divisibility xor on positive
support. -/
theorem mem_squarefreePairFreshPrimeSet_iff_prime_dvd_xor
    {p m n : ℕ} (hp : p.Prime) (hm : 0 < m) (hn : 0 < n) :
    p ∈ squarefreePairFreshPrimeSet m n ↔
      ((p ∣ m ∧ ¬ p ∣ n) ∨ (p ∣ n ∧ ¬ p ∣ m)) := by
  have hpm := prime_mem_squarefreePrimeFace_iff_dvd_public hp hm
  have hpn := prime_mem_squarefreePrimeFace_iff_dvd_public hp hn
  simp [squarefreePairFreshPrimeSet, hpm, hpn]

/-- Every fresh coordinate of a nonzero physical pair is itself a prime no
larger than the physical endpoint. -/
theorem freshPrime_of_nonzeroPhysicalPair
    {R m n q : ℕ}
    (hm : m ∈ lowOwnerNonzeroMobiusCarrier R)
    (hn : n ∈ lowOwnerNonzeroMobiusCarrier R)
    (hq : q ∈ squarefreePairFreshPrimeSet m n) :
    q.Prime ∧ q ≤ squareRootEndpoint R := by
  rcases Finset.mem_filter.mp hm with ⟨hmIcc, _hmMu⟩
  rcases Finset.mem_filter.mp hn with ⟨hnIcc, _hnMu⟩
  have hmOne : 1 ≤ m := (Finset.mem_Icc.mp hmIcc).1
  have hnOne : 1 ≤ n := (Finset.mem_Icc.mp hnIcc).1
  have hmPos : 0 < m := lt_of_lt_of_le Nat.zero_lt_one hmOne
  have hnPos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hnOne
  have hmX := (Finset.mem_Icc.mp hmIcc).2
  have hnX := (Finset.mem_Icc.mp hnIcc).2
  simp only [squarefreePairFreshPrimeSet, Finset.mem_union,
    Finset.mem_sdiff] at hq
  rcases hq with hq | hq
  · have hqpf : q ∈ m.primeFactors := by
      simpa [squarefreePrimeFace] using hq.1
    have hqPrime := Nat.prime_of_mem_primeFactors hqpf
    have hqDvd := Nat.dvd_of_mem_primeFactors hqpf
    have hqle : q ≤ m := Nat.le_of_dvd hmPos hqDvd
    exact ⟨hqPrime, hqle.trans hmX⟩
  · have hqpf : q ∈ n.primeFactors := by
      simpa [squarefreePrimeFace] using hq.1
    have hqPrime := Nat.prime_of_mem_primeFactors hqpf
    have hqDvd := Nat.dvd_of_mem_primeFactors hqpf
    have hqle : q ≤ n := Nat.le_of_dvd hnPos hqDvd
    exact ⟨hqPrime, hqle.trans hnX⟩

/-- Agreement of the revealed-above-p signatures means agreement of the raw
squarefree faces at every physically possible prime above p. -/
theorem revealedAbove_signature_eq_implies_face_eq
    {R p m n q : ℕ}
    (hsig : lowOwnerRevealedPrimeSignature
        (lowOwnerRevealedPrimesAbove R p) m =
      lowOwnerRevealedPrimeSignature
        (lowOwnerRevealedPrimesAbove R p) n)
    (hqPrime : q.Prime) (hpq : p < q)
    (hqX : q ≤ squareRootEndpoint R) :
    (q ∈ squarefreePrimeFace m ↔ q ∈ squarefreePrimeFace n) := by
  have hmem := congrArg (fun T : Finset ℕ => q ∈ T) hsig
  simpa [lowOwnerRevealedPrimeSignature, lowOwnerRevealedPrimesAbove,
    hqPrime, hpq, hqX] using hmem

/-- **Descending crossing implies greatest fresh-prime owner.** -/
theorem descendingCrossPair_greatestFreshOwner
    {R p m n : ℕ} (hp : p.Prime)
    (hcross : (m, n) ∈ lowOwnerRevealedCrossPairCarrier R
      (lowOwnerRevealedPrimesAbove R p) p) :
    IsSquarefreePairGreatestFreshPrimeOwner p m n := by
  rcases Finset.mem_filter.mp hcross with ⟨hprod, hdata⟩
  rcases Finset.mem_product.mp hprod with ⟨hmCar, hnCar⟩
  have hmPos := (lowOwnerNonzeroMobiusCarrier_squarefree_pos hmCar).2
  have hnPos := (lowOwnerNonzeroMobiusCarrier_squarefree_pos hnCar).2
  have hpFresh : p ∈ squarefreePairFreshPrimeSet m n :=
    (mem_squarefreePairFreshPrimeSet_iff_prime_dvd_xor hp hmPos hnPos).2 hdata.2
  refine ⟨hpFresh, ?_⟩
  intro q hqFresh
  by_contra hnot
  have hpq : p < q := by omega
  rcases freshPrime_of_nonzeroPhysicalPair hmCar hnCar hqFresh with
    ⟨hqPrime, hqX⟩
  have hsame := revealedAbove_signature_eq_implies_face_eq
    hdata.1 hqPrime hpq hqX
  simp only [squarefreePairFreshPrimeSet, Finset.mem_union,
    Finset.mem_sdiff] at hqFresh
  rcases hqFresh with hq | hq
  · exact hq.2 (hsame.mp hq.1)
  · exact hq.2 (hsame.mpr hq.1)

/-- **Greatest fresh-prime owner implies descending crossing.** -/
theorem greatestFreshOwner_descendingCrossPair
    {R p m n : ℕ} (hp : p.Prime)
    (hmCar : m ∈ lowOwnerNonzeroMobiusCarrier R)
    (hnCar : n ∈ lowOwnerNonzeroMobiusCarrier R)
    (howner : IsSquarefreePairGreatestFreshPrimeOwner p m n) :
    (m, n) ∈ lowOwnerRevealedCrossPairCarrier R
      (lowOwnerRevealedPrimesAbove R p) p := by
  have hmPos := (lowOwnerNonzeroMobiusCarrier_squarefree_pos hmCar).2
  have hnPos := (lowOwnerNonzeroMobiusCarrier_squarefree_pos hnCar).2
  have hxor :=
    (mem_squarefreePairFreshPrimeSet_iff_prime_dvd_xor hp hmPos hnPos).1
      howner.1
  have hsig : lowOwnerRevealedPrimeSignature
      (lowOwnerRevealedPrimesAbove R p) m =
    lowOwnerRevealedPrimeSignature
      (lowOwnerRevealedPrimesAbove R p) n := by
    ext q
    simp only [lowOwnerRevealedPrimeSignature, Finset.mem_inter]
    constructor
    · rintro ⟨hqm, hqAbove⟩
      rcases Finset.mem_filter.mp hqAbove with ⟨hqUpTo, hpq⟩
      have _hqPrime := (mem_primesUpTo.mp hqUpTo).1
      refine ⟨?_, Finset.mem_filter.mpr ⟨hqUpTo, hpq⟩⟩
      by_contra hqn
      have hqFresh : q ∈ squarefreePairFreshPrimeSet m n := by
        unfold squarefreePairFreshPrimeSet
        exact Finset.mem_union.mpr
          (Or.inl (Finset.mem_sdiff.mpr ⟨hqm, hqn⟩))
      have hqle := howner.2 q hqFresh
      omega
    · rintro ⟨hqn, hqAbove⟩
      rcases Finset.mem_filter.mp hqAbove with ⟨hqUpTo, hpq⟩
      have _hqPrime := (mem_primesUpTo.mp hqUpTo).1
      refine ⟨?_, Finset.mem_filter.mpr ⟨hqUpTo, hpq⟩⟩
      by_contra hqm
      have hqFresh : q ∈ squarefreePairFreshPrimeSet m n := by
        unfold squarefreePairFreshPrimeSet
        exact Finset.mem_union.mpr
          (Or.inr (Finset.mem_sdiff.mpr ⟨hqn, hqm⟩))
      have hqle := howner.2 q hqFresh
      omega
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨hmCar, hnCar⟩, ⟨hsig, hxor⟩⟩

/-- **Exact descending owner carrier.**  The arbitrary-order crossing packet
with all larger primes revealed is precisely the greatest-fresh-prime packet. -/
theorem mem_descendingCrossPair_iff_greatestFreshOwner
    {R p m n : ℕ} (hp : p.Prime) :
    (m, n) ∈ lowOwnerRevealedCrossPairCarrier R
        (lowOwnerRevealedPrimesAbove R p) p ↔
      m ∈ lowOwnerNonzeroMobiusCarrier R ∧
      n ∈ lowOwnerNonzeroMobiusCarrier R ∧
      IsSquarefreePairGreatestFreshPrimeOwner p m n := by
  constructor
  · intro h
    have hprod := (Finset.mem_filter.mp h).1
    rcases Finset.mem_product.mp hprod with ⟨hm, hn⟩
    exact ⟨hm, hn, descendingCrossPair_greatestFreshOwner hp h⟩
  · rintro ⟨hm, hn, howner⟩
    exact greatestFreshOwner_descendingCrossPair hp hm hn howner

end RHLean.Proof
