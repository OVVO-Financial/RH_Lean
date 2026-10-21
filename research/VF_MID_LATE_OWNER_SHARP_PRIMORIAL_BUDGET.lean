import Mathlib
import «research.VF_MID_LATE_OWNER_WHEEL_THIRTY_BUDGET»

/-!
# Genuine late-owner four-slot sieve at exact modulus 2310 and 30030

Independent referee accepted claims 20261014-wheel-5 and 20261014-wheel-6. These are
unconditional **unsigned** upper bounds for actual prime child fibres.
All objects retain the strict open square-band endpoints. This module
does not estimate VF-signed ancestral charges or historical availability.
-/

noncomputable section
namespace RHLean.Analysis

open RHLean.Arithmetic RHLean.Proof
attribute [local instance] Classical.propDecidable

/-- The exact quotient window (unlike an enlarged four-slot proxy) avoids
straddling either physical square wall. -/
def vfMidExactPrimorialChildCapacity (R p M : ℕ) : ℕ :=
  ((Finset.Ioc (R ^ 2 / p) (((R + 1) ^ 2 - 1) / p)).filter
    (fun q => Nat.Coprime q M)).card

private theorem prime_gt_eleven_coprime_2310
    {q : ℕ} (hq : q.Prime) (hlarge : 11 < q) :
    Nat.Coprime q 2310 := by
  apply hq.coprime_iff_not_dvd.mpr
  intro hd
  change q ∣ (((2 * 3) * 5) * 7) * 11 at hd
  rcases hq.dvd_mul.mp hd with h210 | h11
  · rcases hq.dvd_mul.mp h210 with h30 | h7
    · rcases hq.dvd_mul.mp h30 with h6 | h5
      · rcases hq.dvd_mul.mp h6 with h2 | h3
        · have hle := Nat.le_of_dvd (by norm_num : 0 < 2) h2
          omega
        · have hle := Nat.le_of_dvd (by norm_num : 0 < 3) h3
          omega
      · have hle := Nat.le_of_dvd (by norm_num : 0 < 5) h5
        omega
    · have hle := Nat.le_of_dvd (by norm_num : 0 < 7) h7
      omega
  · have hle := Nat.le_of_dvd (by norm_num : 0 < 11) h11
    omega

private theorem prime_gt_thirteen_coprime_30030
    {q : ℕ} (hq : q.Prime) (hlarge : 13 < q) :
    Nat.Coprime q 30030 := by
  apply hq.coprime_iff_not_dvd.mpr
  intro hd
  change q ∣ 2310 * 13 at hd
  rcases hq.dvd_mul.mp hd with h2310 | h13
  · have hc := prime_gt_eleven_coprime_2310 hq (by omega)
    exact ((hq.coprime_iff_not_dvd.mp hc) h2310).elim
  · have hle := Nat.le_of_dvd (by norm_num : 0 < 13) h13
    omega

/-- A genuine late owner `p>A>=7` is at least 11. -/
private theorem prime_owner_gt_ten
    {A p : ℕ} (hA : 7 ≤ A) (hp : p.Prime) (hAp : A < p) :
    10 < p := by
  by_contra h
  have hrange : p = 8 ∨ p = 9 ∨ p = 10 := by omega
  rcases hrange with h8 | h9 | h10
  · subst p; norm_num at hp
  · subst p; norm_num at hp
  · subst p; norm_num at hp

private theorem prime_owner_gt_twelve
    {A p : ℕ} (hA : 11 ≤ A) (hp : p.Prime) (hAp : A < p) :
    12 < p := by
  by_contra h
  have hp12 : p = 12 := by omega
  subst p
  norm_num at hp

/-- Any actual rough prime child lies in the exact quotient interval
and *strictly beyond* its prime owner. This strictness comes from
`R^2 < p*q`, not from an assumed probabilistic prime gap. -/
private theorem vfMidLateRoughChild_exact_window_and_gt_owner
    {A R p q : ℕ}
    (_hA : 3 ≤ A) (_hAR : A ≤ R) (_hRlt : R < 2 * A)
    (hp : p ∈ vfMidSquareBandLateOwnerPrimes A R)
    (hq : q ∈ vfMidSquareBandOwnerRoughChildren R p) :
    q ∈ Finset.Ioc (R ^ 2 / p) (((R + 1) ^ 2 - 1) / p) ∧
      p < q := by
  have hpData := mem_vfMidSquareBandLateOwnerPrimes.mp hp
  have hpRoot : p ≤ R :=
    (mem_vfMidSquareBandOwnerPrimes.mp hpData.1).2
  have hpPrime : p.Prime :=
    (mem_vfMidSquareBandOwnerPrimes.mp hpData.1).1
  have hpos : 0 < p := hpPrime.pos
  have hdata := (Finset.mem_filter.mp hq).2
  have hlo : R ^ 2 < p * q := hdata.1
  have hhi : p * q < (R + 1) ^ 2 := hdata.2.1
  have hlow : R ^ 2 / p < q := by
    apply (Nat.div_lt_iff_lt_mul hpos).2
    simpa [Nat.mul_comm] using! hlo
  have hhigh : q ≤ ((R + 1) ^ 2 - 1) / p := by
    apply (Nat.le_div_iff_mul_le hpos).2
    have hhiComm : q * p < (R + 1) ^ 2 := by
      simpa [Nat.mul_comm] using! hhi
    have hn : q * p ≤ (R + 1) ^ 2 - 1 := by omega
    exact hn
  have hgt : p < q := by
    by_contra hh
    have hqp : q ≤ p := by omega
    have hmul : p * q ≤ p * p := Nat.mul_le_mul_left p hqp
    have hsqr : p ^ 2 ≤ R ^ 2 := Nat.pow_le_pow_left hpRoot 2
    nlinarith [hmul, hsqr]
  exact ⟨Finset.mem_Ioc.mpr ⟨hlow, hhigh⟩, hgt⟩

/-- Referee-accepted sharp threshold A>=7 for the 2310 wheel. -/
theorem vfMidLateOwner_roughChildren_subset_exact2310
    {A R p : ℕ} (hA : 7 ≤ A) (hAR : A ≤ R)
    (hRlt : R < 2 * A)
    (hp : p ∈ vfMidSquareBandLateOwnerPrimes A R) :
    vfMidSquareBandOwnerRoughChildren R p ⊆
      (Finset.Ioc (R ^ 2 / p) (((R + 1) ^ 2 - 1) / p)).filter
        (fun q => Nat.Coprime q 2310) := by
  have hpData := mem_vfMidSquareBandLateOwnerPrimes.mp hp
  have hpPrime : p.Prime :=
    (mem_vfMidSquareBandOwnerPrimes.mp hpData.1).1
  have hpBig : 10 < p :=
    prime_owner_gt_ten hA hpPrime hpData.2
  intro q hq
  obtain ⟨hwindow, hpq⟩ :=
    vfMidLateRoughChild_exact_window_and_gt_owner
      (by omega : 3 ≤ A) hAR hRlt hp hq
  have hqPrime : q.Prime :=
    vfMidSquareBandLateOwnerRoughChild_prime_of_subdoubling
      (by omega : 3 ≤ A) hRlt hp hq
  exact Finset.mem_filter.mpr
    ⟨hwindow, prime_gt_eleven_coprime_2310 hqPrime (by omega)⟩

/-- Referee-accepted sharp threshold A>=11 for the 30030 wheel. -/
theorem vfMidLateOwner_roughChildren_subset_exact30030
    {A R p : ℕ} (hA : 11 ≤ A) (hAR : A ≤ R)
    (hRlt : R < 2 * A)
    (hp : p ∈ vfMidSquareBandLateOwnerPrimes A R) :
    vfMidSquareBandOwnerRoughChildren R p ⊆
      (Finset.Ioc (R ^ 2 / p) (((R + 1) ^ 2 - 1) / p)).filter
        (fun q => Nat.Coprime q 30030) := by
  have hpData := mem_vfMidSquareBandLateOwnerPrimes.mp hp
  have hpPrime : p.Prime :=
    (mem_vfMidSquareBandOwnerPrimes.mp hpData.1).1
  have hpBig : 12 < p :=
    prime_owner_gt_twelve hA hpPrime hpData.2
  intro q hq
  obtain ⟨hwindow, hpq⟩ :=
    vfMidLateRoughChild_exact_window_and_gt_owner
      (by omega : 3 ≤ A) hAR hRlt hp hq
  have hqPrime : q.Prime :=
    vfMidSquareBandLateOwnerRoughChild_prime_of_subdoubling
      (by omega : 3 ≤ A) hRlt hp hq
  exact Finset.mem_filter.mpr
    ⟨hwindow, prime_gt_thirteen_coprime_30030 hqPrime (by omega)⟩

theorem vfMidExactPrimorialChildCapacity_30030_le_2310
    (R p : ℕ) :
    vfMidExactPrimorialChildCapacity R p 30030 ≤
      vfMidExactPrimorialChildCapacity R p 2310 := by
  unfold vfMidExactPrimorialChildCapacity
  apply Finset.card_le_card
  intro q hq
  have hqWindow := (Finset.mem_filter.mp hq).1
  have hqCoprime := (Finset.mem_filter.mp hq).2
  have hdiv : 2310 ∣ 30030 := by norm_num
  exact Finset.mem_filter.mpr
    ⟨hqWindow, hqCoprime.coprime_dvd_right hdiv⟩

theorem vfMidLateOwner_card_le_exact2310
    {A R p : ℕ} (hA : 7 ≤ A) (hAR : A ≤ R)
    (hRlt : R < 2 * A)
    (hp : p ∈ vfMidSquareBandLateOwnerPrimes A R) :
    (vfMidSquareBandCompositeOwner R p).card ≤
      vfMidExactPrimorialChildCapacity R p 2310 := by
  have hpOwner : p ∈ vfMidSquareBandOwnerPrimes R :=
    (mem_vfMidSquareBandLateOwnerPrimes.mp hp).1
  have hrough :
      vfMidSquareBandCompositeOwnerChildren R p =
        vfMidSquareBandOwnerRoughChildren R p :=
    vfMidSquareBandCompositeOwnerChildren_eq_rough
      (by omega : 3 ≤ R) hpOwner
  calc
    (vfMidSquareBandCompositeOwner R p).card =
        (vfMidSquareBandCompositeOwnerChildren R p).card := by
          symm
          exact vfMidSquareBandCompositeOwnerChildren_card R p
    _ = (vfMidSquareBandOwnerRoughChildren R p).card := by
          rw [hrough]
    _ ≤ vfMidExactPrimorialChildCapacity R p 2310 := by
          unfold vfMidExactPrimorialChildCapacity
          exact Finset.card_le_card
            (vfMidLateOwner_roughChildren_subset_exact2310
              hA hAR hRlt hp)

theorem vfMidLateOwner_card_le_exact30030
    {A R p : ℕ} (hA : 11 ≤ A) (hAR : A ≤ R)
    (hRlt : R < 2 * A)
    (hp : p ∈ vfMidSquareBandLateOwnerPrimes A R) :
    (vfMidSquareBandCompositeOwner R p).card ≤
      vfMidExactPrimorialChildCapacity R p 30030 := by
  have hpOwner : p ∈ vfMidSquareBandOwnerPrimes R :=
    (mem_vfMidSquareBandLateOwnerPrimes.mp hp).1
  have hrough :
      vfMidSquareBandCompositeOwnerChildren R p =
        vfMidSquareBandOwnerRoughChildren R p :=
    vfMidSquareBandCompositeOwnerChildren_eq_rough
      (by omega : 3 ≤ R) hpOwner
  calc
    (vfMidSquareBandCompositeOwner R p).card =
        (vfMidSquareBandCompositeOwnerChildren R p).card := by
          symm
          exact vfMidSquareBandCompositeOwnerChildren_card R p
    _ = (vfMidSquareBandOwnerRoughChildren R p).card := by
          rw [hrough]
    _ ≤ vfMidExactPrimorialChildCapacity R p 30030 := by
          unfold vfMidExactPrimorialChildCapacity
          exact Finset.card_le_card
            (vfMidLateOwner_roughChildren_subset_exact30030
              hA hAR hRlt hp)

/-- One owner/root remains one physical occurrence. This is an unsigned
budget, and never provides a new historical negative VF charge. -/
def vfMidDyadicExactPrimorialLateBudget (M A B : ℕ) : ℝ :=
  ∑ R ∈ Finset.Ico A B,
    ∑ p ∈ vfMidSquareBandLateOwnerPrimes A R,
      (vfMidExactPrimorialChildCapacity R p M : ℝ)

theorem vfMidDyadicLateRemoval_le_exact30030
    {A B : ℕ} (hA : 11 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A) :
    vfMidDyadicLateRemoval A A B ≤
      vfMidDyadicExactPrimorialLateBudget 30030 A B := by
  rw [vfMidDyadicLateRemoval_eq_ownerCensus A A B
    (by omega) le_rfl hAB]
  unfold vfMidDyadicOwnerLateRemoval
    vfMidDyadicExactPrimorialLateBudget
  apply Finset.sum_le_sum
  intro R hR
  apply Finset.sum_le_sum
  intro p hp
  have hAR : A ≤ R := (Finset.mem_Ico.mp hR).1
  have hRlt : R < 2 * A :=
    (Finset.mem_Ico.mp hR).2.trans_le hBA
  exact_mod_cast
    (vfMidLateOwner_card_le_exact30030 hA hAR hRlt hp)

theorem vfMidDyadicExactPrimorialBudget_30030_le_2310
    (A B : ℕ) :
    vfMidDyadicExactPrimorialLateBudget 30030 A B ≤
      vfMidDyadicExactPrimorialLateBudget 2310 A B := by
  unfold vfMidDyadicExactPrimorialLateBudget
  apply Finset.sum_le_sum
  intro R hR
  apply Finset.sum_le_sum
  intro p hp
  exact_mod_cast
    vfMidExactPrimorialChildCapacity_30030_le_2310 R p

theorem vfMidDyadicPrimeSupply_ge_exact30030
    {A B : ℕ} (hA : 11 ≤ A) (hAB : A ≤ B) (hBA : B ≤ 2 * A) :
    vfMidDyadicPrefixSupply A A B -
      vfMidDyadicExactPrimorialLateBudget 30030 A B ≤
        vfMidDyadicPrimeSupply A B := by
  have hlate := vfMidDyadicLateRemoval_le_exact30030 hA hAB hBA
  unfold vfMidDyadicLateRemoval at hlate
  linarith

/-- Actual primes and strict physical square-block placement demonstrate the
failure of the 2310 statement if its threshold is weakened to A>=6. -/
example : Nat.Prime 7 ∧ Nat.Prime 11 ∧
    6 ≤ 8 ∧ 8 < 2 * 6 ∧ 8 ^ 2 < 7 * 11 ∧
      7 * 11 < (8 + 1) ^ 2 ∧ ¬Nat.Coprime 11 2310 := by
  norm_num

/-- Likewise, A>=10 does NOT suffice for the 30030 wheel. -/
example : Nat.Prime 11 ∧ Nat.Prime 13 ∧
    10 ≤ 11 ∧ 11 < 2 * 10 ∧ 11 ^ 2 < 11 * 13 ∧
      11 * 13 < (11 + 1) ^ 2 ∧ ¬Nat.Coprime 13 30030 := by
  norm_num

#print axioms vfMidLateOwner_roughChildren_subset_exact2310
#print axioms vfMidLateOwner_roughChildren_subset_exact30030
#print axioms vfMidExactPrimorialChildCapacity_30030_le_2310
#print axioms vfMidDyadicLateRemoval_le_exact30030
#print axioms vfMidDyadicPrimeSupply_ge_exact30030

end RHLean.Analysis
