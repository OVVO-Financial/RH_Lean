import Mathlib
import RHLean.Proof.GlobalFirstJumpCriticalCorrelationBridge

/-!
# Literal pair carriers for the post-root covariance subtraction

The scalar `postRootCovarianceRemainder W` subtracts the complete covariance
copies carried by primes `p > sqrt W`.  This file starts the carrier-level
realization of that subtraction.

A physical positive-lag pair is an ordered pair `1 <= m < n <= W`.  The
`p`-family pair carrier consists of those physical pairs for which `p` divides
both endpoints.  Distinct post-root prime family carriers are disjoint: if two
distinct primes `p,q > sqrt W` divided the same positive endpoint, then
`p*q <= W`, while ordering the two primes gives `W < p*q`.

No estimate, norm, PNT input, or distributional assumption is used.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- Literal positive unordered-pair carrier for the Mertens prefix through
`W`, represented in the canonical orientation `m < n`. -/
def mertensPositivePhysicalPairCarrier (W : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 W).product (Finset.Icc 1 W)).filter fun mn => mn.1 < mn.2

/-- Physical positive-lag pairs lying in one common post-root prime family. -/
def postRootPrimePhysicalPairCarrier (W p : ℕ) : Finset (ℕ × ℕ) :=
  (mertensPositivePhysicalPairCarrier W).filter fun mn =>
    p ∣ mn.1 ∧ p ∣ mn.2

@[simp] theorem mem_mertensPositivePhysicalPairCarrier
    {W m n : ℕ} :
    (m, n) ∈ mertensPositivePhysicalPairCarrier W ↔
      1 ≤ m ∧ m ≤ W ∧ 1 ≤ n ∧ n ≤ W ∧ m < n := by
  simp [mertensPositivePhysicalPairCarrier, and_assoc]

@[simp] theorem mem_postRootPrimePhysicalPairCarrier
    {W p m n : ℕ} :
    (m, n) ∈ postRootPrimePhysicalPairCarrier W p ↔
      1 ≤ m ∧ m ≤ W ∧ 1 ≤ n ∧ n ≤ W ∧ m < n ∧
        p ∣ m ∧ p ∣ n := by
  simp [postRootPrimePhysicalPairCarrier, and_assoc]

/-- Two distinct post-root primes cannot divide the same positive physical site
below the endpoint.  This is the product-packing fact behind pair-family
disjointness. -/
theorem no_common_distinct_postRootPrime_divisors
    {W p q n : ℕ}
    (hp : p ∈ postRootPrimeFamilySet W)
    (hq : q ∈ postRootPrimeFamilySet W)
    (hpq : p ≠ q)
    (hnpos : 0 < n) (hnW : n ≤ W)
    (hpn : p ∣ n) (hqn : q ∣ n) : False := by
  rcases mem_postRootPrimeFamilySet.mp hp with ⟨hpRoot, _hpW, hpPrime⟩
  rcases mem_postRootPrimeFamilySet.mp hq with ⟨hqRoot, _hqW, hqPrime⟩
  have hcop : Nat.Coprime p q := by
    rw [hpPrime.coprime_iff_not_dvd]
    intro hpdq
    have heq : p = q :=
      (Nat.prime_dvd_prime_iff_eq hpPrime hqPrime).mp hpdq
    exact hpq heq
  have hpqdvd : p * q ∣ n :=
    hcop.mul_dvd_of_dvd_of_dvd hpn hqn
  have hpqle : p * q ≤ n := Nat.le_of_dvd hnpos hpqdvd
  have hWlt : W < p * q := by
    by_cases hp_le_q : p ≤ q
    · have hWpp : W < p * p := (Nat.sqrt_lt).1 hpRoot
      exact hWpp.trans_le (Nat.mul_le_mul_left p hp_le_q)
    · have hq_le_p : q ≤ p := Nat.le_of_not_ge hp_le_q
      have hWqq : W < q * q := (Nat.sqrt_lt).1 hqRoot
      have hqqp : q * q ≤ q * p := Nat.mul_le_mul_left q hq_le_p
      simpa [Nat.mul_comm] using hWqq.trans_le hqqp
  omega

/-- **Post-root family pair carriers are genuinely disjoint.**  Thus subtracting
all complete post-root family covariances does not double-count any positive
physical pair. -/
theorem postRootPrimePhysicalPairCarrier_disjoint
    {W p q : ℕ}
    (hp : p ∈ postRootPrimeFamilySet W)
    (hq : q ∈ postRootPrimeFamilySet W)
    (hpq : p ≠ q) :
    Disjoint (postRootPrimePhysicalPairCarrier W p)
      (postRootPrimePhysicalPairCarrier W q) := by
  rw [Finset.disjoint_left]
  intro mn hmp hmq
  have hpData := mem_postRootPrimePhysicalPairCarrier.mp hmp
  have hqData := mem_postRootPrimePhysicalPairCarrier.mp hmq
  exact no_common_distinct_postRootPrime_divisors hp hq hpq
    (by omega) hpData.2.1 hpData.2.2.2.2.2.2.1 hqData.2.2.2.2.2.2.1

end RHLean.Proof