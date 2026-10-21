import Mathlib

/-!
# Exact historical-prime multiplicity in genuine owner ancestry

For a prime historical cofactor `q`, a current composite `p*q` has
an eligible small prime owner at scale `R_p = Nat.sqrt (p*q)` when
`1024*p <= R_p`. This file counts genuine prime owners with their
physical occurrences. No historical prime is cloned to pay more than one
source charge; multiplicity is an obstruction, not a cancellation estimate.

Accepted agent findings: 20261014-analytic-1 and 20261014-analytic-2 (PAPER_PROOF, now formalized here).
The original masks, clips, anchor and restored NNS cross terms are NOT bounded.
-/

namespace RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- The ancestry threshold squared, `1024^2`. -/
def vfMidHistoricalOwnerThreshold : ℕ := 1048576

/-- Exact conversion of the current square-root threshold to a prime-cofactor
bound. Both factors are natural; no continuous square-root estimate is used. -/
theorem vfMidHistoricalOwner_sqrt_iff
    {p q : ℕ} (hp : 0 < p) :
    1024 * p ≤ Nat.sqrt (p * q) ↔
      vfMidHistoricalOwnerThreshold * p ≤ q := by
  constructor
  · intro hroot
    have hsq : (1024 * p) * (1024 * p) ≤ p * q :=
      (Nat.le_sqrt).1 hroot
    have hscaled : p * (vfMidHistoricalOwnerThreshold * p) ≤ p * q := by
      dsimp [vfMidHistoricalOwnerThreshold]
      nlinarith [hsq]
    exact Nat.le_of_mul_le_mul_left hscaled hp
  · intro hbound
    apply (Nat.le_sqrt).2
    have hscaled :
        p * (vfMidHistoricalOwnerThreshold * p) ≤ p * q :=
      Nat.mul_le_mul_left p hbound
    dsimp [vfMidHistoricalOwnerThreshold] at hscaled
    nlinarith [hscaled]

/-- Literal eligible odd-prime owners whose current semiprime `p*q`
lies in the block with root `Nat.sqrt (p*q)`. The upper interval endpoint
is only a finiteness guard; the threshold imposes a much stronger bound. -/
def vfMidHistoricalPrimeOwnerFibre (q : ℕ) : Finset ℕ :=
  (Finset.Icc 3 q).filter
    (fun p => p.Prime ∧ 1024 * p ≤ Nat.sqrt (p * q))

/-- The eligible `p` are exactly the odd primes below `q/2^20`.
This counts OWNER DEMANDS, not available historical charges. -/
theorem mem_vfMidHistoricalPrimeOwnerFibre_iff
    {p q : ℕ} :
    p ∈ vfMidHistoricalPrimeOwnerFibre q ↔
      p.Prime ∧ 3 ≤ p ∧ p ≤ q / vfMidHistoricalOwnerThreshold := by
  simp only [vfMidHistoricalPrimeOwnerFibre, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hp3, _hpq⟩, hpPrime, hroot⟩
    have hbound :
        vfMidHistoricalOwnerThreshold * p ≤ q :=
      (vfMidHistoricalOwner_sqrt_iff (by omega : 0 < p)).mp hroot
    have hpDiv : p ≤ q / vfMidHistoricalOwnerThreshold := by
      apply (Nat.le_div_iff_mul_le
        (by norm_num [vfMidHistoricalOwnerThreshold])).2
      simpa [Nat.mul_comm] using! hbound
    exact ⟨hpPrime, hp3, hpDiv⟩
  · rintro ⟨hpPrime, hp3, hpDiv⟩
    have hpq : p ≤ q :=
      hpDiv.trans (Nat.div_le_self q vfMidHistoricalOwnerThreshold)
    have hbound :
        vfMidHistoricalOwnerThreshold * p ≤ q := by
      have h := (Nat.le_div_iff_mul_le
        (by norm_num [vfMidHistoricalOwnerThreshold])).1 hpDiv
      simpa [Nat.mul_comm] using! h
    exact ⟨⟨hp3, hpq⟩, hpPrime,
      (vfMidHistoricalOwner_sqrt_iff (by omega : 0 < p)).mpr hbound⟩

/-- Global ancestry-owner fibre is exactly the prime population in
`[3, floor(q / 2^20)]`, with no independence assumption. -/
theorem vfMidHistoricalPrimeOwnerFibre_eq_primeInterval (q : ℕ) :
    vfMidHistoricalPrimeOwnerFibre q =
      (Finset.Icc 3 (q / vfMidHistoricalOwnerThreshold)).filter Nat.Prime := by
  ext p
  rw [mem_vfMidHistoricalPrimeOwnerFibre_iff]
  simp only [Finset.mem_filter, Finset.mem_Icc]
  tauto

/-- For every `N`, counting primes in the literal interval `[2,N]`
agrees with the actual prime-counting function. -/
private theorem vfMidHistoricalPrimeInterval_card_eq_pi (N : ℕ) :
    ((Finset.Icc 2 N).filter Nat.Prime).card = Nat.primeCounting N := by
  have hset :
      (Finset.Icc 2 N).filter Nat.Prime =
        (Finset.range (N + 1)).filter Nat.Prime := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range,
      Nat.lt_succ_iff]
    constructor
    · rintro ⟨⟨_hp2, hpN⟩, hpPrime⟩
      exact ⟨hpN, hpPrime⟩
    · rintro ⟨hpN, hpPrime⟩
      exact ⟨⟨hpPrime.two_le, hpN⟩, hpPrime⟩
  unfold Nat.primeCounting Nat.primeCounting'
  rw [Nat.count_eq_card_filter_range]
  exact congrArg Finset.card hset

/-- Exact global multiplicity of owner demands for an odd historical
prime `q>=2*2^20`: `pi(floor(q/2^20))-1` (subtract the even prime 2). -/
theorem vfMidHistoricalPrimeOwnerFibre_card_eq_pi_sub_one
    {q : ℕ} (hq : 2 * vfMidHistoricalOwnerThreshold ≤ q) :
    (vfMidHistoricalPrimeOwnerFibre q).card =
      Nat.primeCounting (q / vfMidHistoricalOwnerThreshold) - 1 := by
  let N := q / vfMidHistoricalOwnerThreshold
  have hN : 2 ≤ N := by
    dsimp [N]
    apply (Nat.le_div_iff_mul_le
      (by norm_num [vfMidHistoricalOwnerThreshold])).2
    simpa [Nat.mul_comm] using! hq
  have h2not : 2 ∉ ((Finset.Icc 3 N).filter Nat.Prime) := by simp
  have hsplit :
      ((Finset.Icc 2 N).filter Nat.Prime) =
        insert 2 ((Finset.Icc 3 N).filter Nat.Prime) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert]
    constructor
    · rintro ⟨⟨hp2, hpN⟩, hpPrime⟩
      by_cases hpEq : p = 2
      · exact Or.inl hpEq
      · exact Or.inr ⟨⟨by omega, hpN⟩, hpPrime⟩
    · rintro (hpEq | ⟨⟨hp3, hpN⟩, hpPrime⟩)
      · subst p
        exact ⟨⟨by norm_num, hN⟩, by norm_num⟩
      · exact ⟨⟨by omega, hpN⟩, hpPrime⟩
  have hpi := vfMidHistoricalPrimeInterval_card_eq_pi N
  rw [hsplit, Finset.card_insert_of_notMem h2not] at hpi
  rw [vfMidHistoricalPrimeOwnerFibre_eq_primeInterval]
  change ((Finset.Icc 3 N).filter Nat.Prime).card =
    Nat.primeCounting N - 1
  omega

/-- On each arbitrary prescribed finite range of potential small owners,
there exists a GENUINE prime `q` for which all of those odd-prime owners
occur. Thus choosing one copy of each prime historical charge cannot
globally supply every demanded owner occurrence. -/
theorem vfMidHistoricalPrimeOwnerFibre_covers_bounded_primes (T : ℕ) :
    ∃ q : ℕ, q.Prime ∧
      ∀ p : ℕ, p.Prime → 3 ≤ p → p ≤ T →
        p ∈ vfMidHistoricalPrimeOwnerFibre q := by
  obtain ⟨q, hqBig, hqPrime⟩ :=
    Nat.exists_infinite_primes (vfMidHistoricalOwnerThreshold * T + 1)
  refine ⟨q, hqPrime, ?_⟩
  intro p hpPrime hp3 hpT
  apply mem_vfMidHistoricalPrimeOwnerFibre_iff.mpr
  have hscaled :
      vfMidHistoricalOwnerThreshold * p ≤ q := by
    calc
      vfMidHistoricalOwnerThreshold * p ≤
          vfMidHistoricalOwnerThreshold * T :=
        Nat.mul_le_mul_left _ hpT
      _ ≤ q := by omega
  have hpDiv : p ≤ q / vfMidHistoricalOwnerThreshold := by
    apply (Nat.le_div_iff_mul_le
      (by norm_num [vfMidHistoricalOwnerThreshold])).2
    simpa [Nat.mul_comm] using! hscaled
  exact ⟨hpPrime, hp3, hpDiv⟩

/-- Strict square-block membership at the canonical integer root of an
ordinary semiprime product. The lower endpoint is strict when the primes
are distinct, so the product is not a perfect square. -/
theorem vfMidHistoricalProduct_lt_root_succ_square
    (p q : ℕ) :
    p * q < (Nat.sqrt (p * q) + 1) ^ 2 := by
  exact (Nat.sqrt_lt').1 (Nat.lt_succ_self _)

/-- For a FIXED block `R`, there is at most one owner of a shared
historical `q` in the small-owner sector. No uniqueness is claimed
between different square blocks. -/
theorem vfMidHistoricalSmallOwner_sameBlock_unique
    {R p₁ p₂ q : ℕ}
    (hR : 1024 * p₁ ≤ R)
    (hp₁ : 3 ≤ p₁)
    (hpLt : p₁ < p₂)
    (hbelow : R ^ 2 < p₁ * q)
    (habove : p₂ * q < (R + 1) ^ 2) : False := by
  have hqLarge : 1024 * R < q := by
    by_contra hnot
    have hqLe : q ≤ 1024 * R := Nat.le_of_not_gt hnot
    have hmul : p₁ * q ≤ p₁ * (1024 * R) :=
      Nat.mul_le_mul_left p₁ hqLe
    have hroot : (1024 * p₁) * R ≤ R * R :=
      Nat.mul_le_mul_right R hR
    nlinarith [hmul, hroot]
  have hqSmall : q < 2 * R + 1 := by
    have hstep : (p₁ + 1) * q ≤ p₂ * q :=
      Nat.mul_le_mul_right q (by omega : p₁ + 1 ≤ p₂)
    nlinarith [hbelow, habove, hstep]
  omega

#print axioms vfMidHistoricalOwner_sqrt_iff
#print axioms mem_vfMidHistoricalPrimeOwnerFibre_iff
#print axioms vfMidHistoricalPrimeOwnerFibre_card_eq_pi_sub_one
#print axioms vfMidHistoricalPrimeOwnerFibre_covers_bounded_primes
#print axioms vfMidHistoricalSmallOwner_sameBlock_unique

end RHLean.Analysis
