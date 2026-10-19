import Mathlib
import RHLean.Analysis.CanonicalLowOccupancy

/-!
# Odd residual cofactor support

This module formalizes the elementary arithmetic core of claims
`20261016-wheel-1` and `20261016-wheel-2`.

For the canonical factorization `m = c * q`, residual exclusions rule out
`c = 1` and prime `c`: otherwise `m` is respectively prime, a product of
two distinct primes, or a prime square.  If the cofactor is odd, it is therefore
at least nine.  Consequently an occurrence below `R^2` has
`9 * P+(m) < R^2`.

This is a support theorem only.  It does not define or estimate the raw
factor-depth ledger, transfer to the returned-cell carrier, or bound any signed
sum or covariance.
-/

noncomputable section

namespace RHLean.Proof

/-- The exact residual exclusions used by the odd-seat factor-depth partition:
the source is neither prime, a product of two distinct primes, nor a prime
square. -/
def IsOddFactorDepthResidual (m : ℕ) : Prop :=
  ¬ m.Prime ∧
    (∀ p q : ℕ, p.Prime → q.Prime → p < q → m ≠ p * q) ∧
    (∀ q : ℕ, q.Prime → m ≠ q ^ 2)

/-- The residual exclusions force the canonical cofactor to be nontrivial and
nonprime.  The strict-square exclusion is used exactly in the equal-factor
case. -/
theorem canonicalCofactor_one_lt_and_not_prime_of_factorDepthResidual
    {m : ℕ} (hm : 1 < m) (hres : IsOddFactorDepthResidual m) :
    1 < canonicalCofactor m ∧ ¬ (canonicalCofactor m).Prime := by
  classical
  let c := canonicalCofactor m
  let q := canonicalLargestPrimeFactor m
  have hqPrime : q.Prime := canonicalLargestPrimeFactor_prime hm
  have hprod : c * q = m := canonicalCofactor_mul_largestPrimeFactor hm
  have hc0 : c ≠ 0 := by
    intro hc
    rw [hc, zero_mul] at hprod
    omega
  have hc1 : c ≠ 1 := by
    intro hc
    apply hres.1
    have hmq : m = q := by
      calc
        m = c * q := hprod.symm
        _ = q := by simp [hc]
    simpa [hmq] using! hqPrime
  have hcgt : 1 < c := by omega
  refine ⟨hcgt, ?_⟩
  intro hcPrime
  have hm0 : m ≠ 0 := by omega
  have hcdvd : c ∣ m := ⟨q, hprod.symm⟩
  have hcmem : c ∈ m.primeFactors := by
    rw [Nat.mem_primeFactors]
    exact ⟨hcPrime, hcdvd, hm0⟩
  have hcq : c ≤ q := by
    unfold q canonicalLargestPrimeFactor
    rw [dite_eq_left hm]
    exact Finset.le_max' m.primeFactors c hcmem
  rcases eq_or_lt_of_le hcq with hcqEq | hcqLt
  · apply hres.2.2 q hqPrime
    calc
      m = c * q := hprod.symm
      _ = q ^ 2 := by rw [hcqEq, pow_two]
  · exact hres.2.1 c q hcPrime hqPrime hcqLt hprod.symm

/-- Nine is the least odd nonprime natural number strictly above one. -/
theorem nine_le_of_odd_one_lt_not_prime
    {c : ℕ} (hcOdd : Odd c) (hcgt : 1 < c) (hcPrime : ¬ c.Prime) :
    9 ≤ c := by
  by_contra h
  have hc8 : c ≤ 8 := by omega
  have hcCases : c = 3 ∨ c = 5 ∨ c = 7 := by
    rcases hcOdd with ⟨k, hk⟩
    omega
  rcases hcCases with rfl | rfl | rfl <;> norm_num at hcPrime

/-- Every odd residual source has canonical cofactor at least nine. -/
theorem nine_le_canonicalCofactor_of_odd_factorDepthResidual
    {m : ℕ} (hm : 1 < m) (hcOdd : Odd (canonicalCofactor m))
    (hres : IsOddFactorDepthResidual m) :
    9 ≤ canonicalCofactor m := by
  obtain ⟨hcgt, hcPrime⟩ :=
    canonicalCofactor_one_lt_and_not_prime_of_factorDepthResidual hm hres
  exact nine_le_of_odd_one_lt_not_prime hcOdd hcgt hcPrime

/-- Sharp one-ninth support: below a strict square endpoint, an odd residual
source has largest-prime tag strictly below that endpoint divided by nine, in
the division-free form `9 * P+(m) < R^2`. -/
theorem nine_mul_canonicalLargestPrimeFactor_lt_sq
    {R m : ℕ} (hm : 1 < m) (hcOdd : Odd (canonicalCofactor m))
    (hres : IsOddFactorDepthResidual m) (hmR : m < R ^ 2) :
    9 * canonicalLargestPrimeFactor m < R ^ 2 := by
  have hc9 := nine_le_canonicalCofactor_of_odd_factorDepthResidual hm hcOdd hres
  have hprod := canonicalCofactor_mul_largestPrimeFactor hm
  calc
    9 * canonicalLargestPrimeFactor m ≤
        canonicalCofactor m * canonicalLargestPrimeFactor m :=
      Nat.mul_le_mul_right (canonicalLargestPrimeFactor m) hc9
    _ = m := hprod
    _ < R ^ 2 := hmR

#print axioms RHLean.Proof.canonicalCofactor_one_lt_and_not_prime_of_factorDepthResidual
#print axioms RHLean.Proof.nine_mul_canonicalLargestPrimeFactor_lt_sq

end RHLean.Proof
