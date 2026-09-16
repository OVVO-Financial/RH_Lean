import Mathlib
import «research.GLOBAL_RETURNED_CORE_DESCENDING_PAIR_OWNER»
import «research.RECIPROCAL_COVARIANCE_PAIR_AMPLITUDE_CONTRACTION»
import RHLean.Proof.LowWheelCofactorQuotientToggle

/-!
# Reciprocal covariance descent at an arbitrary fresh prime

The existing covariance recursion chooses the least fresh prime only to obtain a
canonical ordering of recursive steps.  The local algebra does not need that
choice.  If `p` is *any* prime dividing exactly one endpoint of a nonzero
squarefree pair, stripping p from the two endpoints:

* preserves every prime-face coordinate `q != p`;
* deletes p from the fresh-prime symmetric difference and no other coordinate;
* reverses the Mobius pair sign exactly;
* multiplies reciprocal pair amplitude by `-1/p` and energy by `1/p^2`;
* and, for a distinct stripped pair, stays inside the post-root remainder by
  the already-compiled downward-closure theorem.

This makes the reciprocal descent currency available to the greatest-fresh-
prime packets produced by the reversed filtration, without identifying them
with the old least-owner fibres.
-/

noncomputable section

namespace RHLean.Proof

open RHLean.Analysis RHLean.Arithmetic

attribute [local instance] Classical.propDecidable

/-- Strip a chosen prime and orient the two parents as a positive-lag pair. -/
def squarefreePairPrimeOrderedParent (p m n : ℕ) : ℕ × ℕ :=
  let um := squarefreePrimeFamilyParent p m
  let un := squarefreePrimeFamilyParent p n
  if um < un then (um, un) else (un, um)

/-- The chosen-prime parent is always a divisor of the original endpoint. -/
theorem squarefreePrimeFamilyParent_dvd_public (p n : ℕ) :
    squarefreePrimeFamilyParent p n ∣ n := by
  unfold squarefreePrimeFamilyParent
  by_cases hpn : p ∣ n
  · rw [if_pos hpn]
    exact ⟨p, (Nat.div_mul_cancel hpn).symm⟩
  · simp [hpn]

/-- The chosen-prime parent of a positive endpoint is positive. -/
theorem squarefreePrimeFamilyParent_pos_public
    {p n : ℕ} (hp : p.Prime) (hn : 0 < n) :
    0 < squarefreePrimeFamilyParent p n := by
  unfold squarefreePrimeFamilyParent
  by_cases hpn : p ∣ n
  · rw [if_pos hpn]
    exact Nat.div_pos (Nat.le_of_dvd hn hpn) hp.pos
  · simpa [hpn] using hn

/-- Stripping p preserves divisibility by every distinct prime q. -/
theorem prime_dvd_squarefreePrimeFamilyParent_iff_of_ne_public
    {p q n : ℕ} (hp : p.Prime) (hq : q.Prime) (hqp : q ≠ p) :
    q ∣ squarefreePrimeFamilyParent p n ↔ q ∣ n := by
  unfold squarefreePrimeFamilyParent
  by_cases hpn : p ∣ n
  · rw [if_pos hpn]
    constructor
    · intro hqdiv
      have hmul : p * (n / p) = n := Nat.mul_div_cancel' hpn
      exact hmul ▸ dvd_mul_of_dvd_right hqdiv p
    · intro hqn
      have hmul : p * (n / p) = n := Nat.mul_div_cancel' hpn
      have hprod : q ∣ p * (n / p) := by simpa [hmul] using hqn
      rcases hq.dvd_mul.mp hprod with hqP | hqParent
      · have heq : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp hqP
        exact False.elim (hqp heq)
      · exact hqParent
  · simp [hpn]

/-- Hence every distinct prime-face coordinate survives stripping p. -/
theorem mem_squarefreePrimeFace_parent_iff_of_ne_public
    {p q n : ℕ} (hp : p.Prime) (hq : q.Prime) (hqp : q ≠ p)
    (hn : 0 < n) :
    q ∈ squarefreePrimeFace (squarefreePrimeFamilyParent p n) ↔
      q ∈ squarefreePrimeFace n := by
  have hparentPos := squarefreePrimeFamilyParent_pos_public hp hn
  have hleft := prime_mem_squarefreePrimeFace_iff_dvd_public hq hparentPos
  have hright := prime_mem_squarefreePrimeFace_iff_dvd_public hq hn
  rw [hleft, hright]
  exact prime_dvd_squarefreePrimeFamilyParent_iff_of_ne_public hp hq hqp

/-- For a squarefree endpoint, p itself is absent after stripping p. -/
theorem owner_not_mem_squarefreePrimeFace_parent
    {p n : ℕ} (hp : p.Prime) (hnSq : Squarefree n) (hn : 0 < n) :
    p ∉ squarefreePrimeFace (squarefreePrimeFamilyParent p n) := by
  have hparentPos := squarefreePrimeFamilyParent_pos_public hp hn
  rw [prime_mem_squarefreePrimeFace_iff_dvd_public hp hparentPos]
  unfold squarefreePrimeFamilyParent
  by_cases hpn : p ∣ n
  · rw [if_pos hpn]
    exact prime_not_dvd_div_of_squarefree hp hnSq hpn
  · simp [hpn]

/-- Every q != p fresh coordinate is preserved by stripping p from both
endpoints. -/
theorem mem_freshPrimeSet_stripped_iff_of_ne
    {p q m n : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hqp : q ≠ p)
    (hm : 0 < m) (hn : 0 < n) :
    q ∈ squarefreePairFreshPrimeSet
        (squarefreePrimeFamilyParent p m)
        (squarefreePrimeFamilyParent p n) ↔
      q ∈ squarefreePairFreshPrimeSet m n := by
  have hmm := mem_squarefreePrimeFace_parent_iff_of_ne_public hp hq hqp hm
  have hnn := mem_squarefreePrimeFace_parent_iff_of_ne_public hp hq hqp hn
  simp only [squarefreePairFreshPrimeSet, Finset.mem_union, Finset.mem_sdiff]
  tauto

/-- **Fresh-set erasure at an arbitrary fresh prime.** -/
theorem freshPrimeSet_stripped_eq_erase
    {p m n : ℕ}
    (hp : p.Prime) (hmSq : Squarefree m) (hnSq : Squarefree n)
    (hm : 0 < m) (hn : 0 < n)
    (_hpFresh : p ∈ squarefreePairFreshPrimeSet m n) :
    squarefreePairFreshPrimeSet
        (squarefreePrimeFamilyParent p m)
        (squarefreePrimeFamilyParent p n) =
      (squarefreePairFreshPrimeSet m n).erase p := by
  ext q
  by_cases hqp : q = p
  · subst q
    have hpm := owner_not_mem_squarefreePrimeFace_parent hp hmSq hm
    have hpn := owner_not_mem_squarefreePrimeFace_parent hp hnSq hn
    simp [squarefreePairFreshPrimeSet, hpm, hpn]
  · constructor
    · intro hqStrip
      have hqPrime : q.Prime := by
        simp only [squarefreePairFreshPrimeSet, Finset.mem_union,
          Finset.mem_sdiff] at hqStrip
        rcases hqStrip with hqStrip | hqStrip
        · have hpf : q ∈ (squarefreePrimeFamilyParent p m).primeFactors := by
            simpa [squarefreePrimeFace] using hqStrip.1
          exact Nat.prime_of_mem_primeFactors hpf
        · have hpf : q ∈ (squarefreePrimeFamilyParent p n).primeFactors := by
            simpa [squarefreePrimeFace] using hqStrip.1
          exact Nat.prime_of_mem_primeFactors hpf
      have hqOrig :=
        (mem_freshPrimeSet_stripped_iff_of_ne hp hqPrime hqp hm hn).1 hqStrip
      exact Finset.mem_erase.mpr ⟨hqp, hqOrig⟩
    · intro hqErase
      rcases Finset.mem_erase.mp hqErase with ⟨hqp', hqOrig⟩
      have hqPrime : q.Prime := by
        simp only [squarefreePairFreshPrimeSet, Finset.mem_union,
          Finset.mem_sdiff] at hqOrig
        rcases hqOrig with hqOrig | hqOrig
        · have hpf : q ∈ m.primeFactors := by
            simpa [squarefreePrimeFace] using hqOrig.1
          exact Nat.prime_of_mem_primeFactors hpf
        · have hpf : q ∈ n.primeFactors := by
            simpa [squarefreePrimeFace] using hqOrig.1
          exact Nat.prime_of_mem_primeFactors hpf
      exact (mem_freshPrimeSet_stripped_iff_of_ne hp hqPrime hqp' hm hn).2 hqOrig

/-- Separation rank drops by exactly one after stripping any fresh prime. -/
theorem freshPrimeSet_stripped_card_add_one
    {p m n : ℕ}
    (hp : p.Prime) (hmSq : Squarefree m) (hnSq : Squarefree n)
    (hm : 0 < m) (hn : 0 < n)
    (hpFresh : p ∈ squarefreePairFreshPrimeSet m n) :
    (squarefreePairFreshPrimeSet
        (squarefreePrimeFamilyParent p m)
        (squarefreePrimeFamilyParent p n)).card + 1 =
      (squarefreePairFreshPrimeSet m n).card := by
  rw [freshPrimeSet_stripped_eq_erase hp hmSq hnSq hm hn hpFresh]
  exact Finset.card_erase_add_one hpFresh

/-- **Mobius pair sign reversal at any fresh prime.** -/
theorem arbitraryFreshPrime_pairWeight_eq_neg_parentPairWeight
    {p m n : ℕ}
    (hp : p.Prime) (hmSq : Squarefree m) (hnSq : Squarefree n)
    (_hm : 0 < m) (_hn : 0 < n)
    (hxor : (p ∣ m ∧ ¬ p ∣ n) ∨ (p ∣ n ∧ ¬ p ∣ m)) :
    realMoebiusStep m * realMoebiusStep n =
      -(realMoebiusStep (squarefreePrimeFamilyParent p m) *
        realMoebiusStep (squarefreePrimeFamilyParent p n)) := by
  rcases hxor with h | h
  · have hnot := prime_not_dvd_div_of_squarefree hp hmSq h.1
    have hmEq : p * (m / p) = m := Nat.mul_div_cancel' h.1
    unfold squarefreePrimeFamilyParent
    rw [if_pos h.1, if_neg h.2]
    calc
      realMoebiusStep m * realMoebiusStep n =
          realMoebiusStep (p * (m / p)) * realMoebiusStep n := by rw [hmEq]
      _ = -(realMoebiusStep (m / p)) * realMoebiusStep n := by
        rw [realMoebiusStep_mul_prime_eq_neg hp hnot]
      _ = -(realMoebiusStep (m / p) * realMoebiusStep n) := by ring
  · have hnot := prime_not_dvd_div_of_squarefree hp hnSq h.1
    have hnEq : p * (n / p) = n := Nat.mul_div_cancel' h.1
    unfold squarefreePrimeFamilyParent
    rw [if_neg h.2, if_pos h.1]
    calc
      realMoebiusStep m * realMoebiusStep n =
          realMoebiusStep m * realMoebiusStep (p * (n / p)) := by rw [hnEq]
      _ = realMoebiusStep m * (-(realMoebiusStep (n / p))) := by
        rw [realMoebiusStep_mul_prime_eq_neg hp hnot]
      _ = -(realMoebiusStep m * realMoebiusStep (n / p)) := by ring

/-- **Reciprocal amplitude descent at any fresh prime.** -/
theorem arbitraryFreshPrime_reciprocalPairAmplitude_descent
    {p m n : ℕ}
    (hp : p.Prime) (hmSq : Squarefree m) (hnSq : Squarefree n)
    (hm : 0 < m) (hn : 0 < n)
    (hxor : (p ∣ m ∧ ¬ p ∣ n) ∨ (p ∣ n ∧ ¬ p ∣ m)) :
    postRootCovarianceReciprocalPairAmplitude (m, n) =
      -(1 / (p : ℝ)) *
        postRootCovarianceReciprocalPairAmplitude
          (squarefreePrimeFamilyParent p m,
            squarefreePrimeFamilyParent p n) := by
  have hsign := arbitraryFreshPrime_pairWeight_eq_neg_parentPairWeight
    hp hmSq hnSq hm hn hxor
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have humPos := squarefreePrimeFamilyParent_pos_public hp hm
  have hunPos := squarefreePrimeFamilyParent_pos_public hp hn
  have hum0 : ((squarefreePrimeFamilyParent p m : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt humPos)
  have hun0 : ((squarefreePrimeFamilyParent p n : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hunPos)
  have hprod : (m : ℝ) * (n : ℝ) =
      (p : ℝ) *
        ((squarefreePrimeFamilyParent p m : ℕ) : ℝ) *
        ((squarefreePrimeFamilyParent p n : ℕ) : ℝ) := by
    rcases hxor with h | h
    · have hmEq : p * (m / p) = m := Nat.mul_div_cancel' h.1
      have hmCast : (m : ℝ) = (p : ℝ) * (((m / p : ℕ) : ℝ)) := by
        exact_mod_cast hmEq.symm
      unfold squarefreePrimeFamilyParent
      rw [if_pos h.1, if_neg h.2]
      rw [hmCast]
    · have hnEq : p * (n / p) = n := Nat.mul_div_cancel' h.1
      have hnCast : (n : ℝ) = (p : ℝ) * (((n / p : ℕ) : ℝ)) := by
        exact_mod_cast hnEq.symm
      unfold squarefreePrimeFamilyParent
      rw [if_neg h.2, if_pos h.1]
      rw [hnCast]
  unfold postRootCovarianceReciprocalPairAmplitude
  rw [hsign, hprod]
  field_simp [hp0, hum0, hun0]

/-- Squaring gives the genuine reciprocal-square contraction currency. -/
theorem arbitraryFreshPrime_reciprocalPairEnergy_descent
    {p m n : ℕ}
    (hp : p.Prime) (hmSq : Squarefree m) (hnSq : Squarefree n)
    (hm : 0 < m) (hn : 0 < n)
    (hxor : (p ∣ m ∧ ¬ p ∣ n) ∨ (p ∣ n ∧ ¬ p ∣ m)) :
    postRootCovarianceReciprocalPairEnergy (m, n) =
      (1 / (p : ℝ) ^ 2) *
        postRootCovarianceReciprocalPairEnergy
          (squarefreePrimeFamilyParent p m,
            squarefreePrimeFamilyParent p n) := by
  unfold postRootCovarianceReciprocalPairEnergy
  rw [arbitraryFreshPrime_reciprocalPairAmplitude_descent
    hp hmSq hnSq hm hn hxor]
  ring

/-- Distinct stripped parents remain in the literal post-root remainder after
positive-lag reorientation. -/
theorem arbitraryFreshPrime_orderedParent_mem_postRootRemainder
    {W p m n : ℕ}
    (hpair : (m, n) ∈ postRootCovarianceRemainderPhysicalPairCarrier W)
    (hp : p.Prime) (hm : 0 < m) (hn : 0 < n)
    (hne : squarefreePrimeFamilyParent p m ≠
      squarefreePrimeFamilyParent p n) :
    squarefreePairPrimeOrderedParent p m n ∈
      postRootCovarianceRemainderPhysicalPairCarrier W := by
  let um := squarefreePrimeFamilyParent p m
  let un := squarefreePrimeFamilyParent p n
  have humPos : 0 < um := squarefreePrimeFamilyParent_pos_public hp hm
  have hunPos : 0 < un := squarefreePrimeFamilyParent_pos_public hp hn
  have humDvd : um ∣ m := squarefreePrimeFamilyParent_dvd_public p m
  have hunDvd : un ∣ n := squarefreePrimeFamilyParent_dvd_public p n
  change (if um < un then (um, un) else (un, um)) ∈
    postRootCovarianceRemainderPhysicalPairCarrier W
  by_cases hlt : um < un
  · rw [if_pos hlt]
    exact postRootCovarianceRemainderPhysicalPairCarrier_of_dvd hpair
      (Or.inl ⟨humDvd, hunDvd⟩) humPos hunPos hlt
  · rw [if_neg hlt]
    have hrev : un < um := by
      dsimp [um, un] at hne
      omega
    exact postRootCovarianceRemainderPhysicalPairCarrier_of_dvd hpair
      (Or.inr ⟨hunDvd, humDvd⟩) hunPos humPos hrev

/-- **Greatest-owner specialization.**  Every nonzero descending-crossing pair
gets the same exact sign/rank/reciprocal descent as the old least-owner pair. -/
theorem descendingGreatestOwner_reciprocal_descent
    {R p m n : ℕ} (hp : p.Prime)
    (hcross : (m, n) ∈ lowOwnerRevealedCrossPairCarrier R
      (lowOwnerRevealedPrimesAbove R p) p) :
    let um := squarefreePrimeFamilyParent p m
    let un := squarefreePrimeFamilyParent p n
    (squarefreePairFreshPrimeSet um un).card + 1 =
        (squarefreePairFreshPrimeSet m n).card ∧
      realMoebiusStep m * realMoebiusStep n =
        -(realMoebiusStep um * realMoebiusStep un) ∧
      postRootCovarianceReciprocalPairEnergy (m, n) =
        (1 / (p : ℝ) ^ 2) *
          postRootCovarianceReciprocalPairEnergy (um, un) := by
  have hprod := (Finset.mem_filter.mp hcross).1
  rcases Finset.mem_product.mp hprod with ⟨hmCar, hnCar⟩
  rcases lowOwnerNonzeroMobiusCarrier_squarefree_pos hmCar with ⟨hmSq, hmPos⟩
  rcases lowOwnerNonzeroMobiusCarrier_squarefree_pos hnCar with ⟨hnSq, hnPos⟩
  have howner := descendingCrossPair_greatestFreshOwner hp hcross
  have hxor :=
    (mem_squarefreePairFreshPrimeSet_iff_prime_dvd_xor hp hmPos hnPos).1
      howner.1
  dsimp only
  exact ⟨freshPrimeSet_stripped_card_add_one hp hmSq hnSq hmPos hnPos howner.1,
    arbitraryFreshPrime_pairWeight_eq_neg_parentPairWeight
      hp hmSq hnSq hmPos hnPos hxor,
    arbitraryFreshPrime_reciprocalPairEnergy_descent
      hp hmSq hnSq hmPos hnPos hxor⟩

end RHLean.Proof