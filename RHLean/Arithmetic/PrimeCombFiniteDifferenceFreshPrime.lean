import Mathlib
import Mathlib.Data.Finset.NatDivisors
import RHLean.Arithmetic.PrimeCombFiniteDifference

open scoped ArithmeticFunction.Moebius BigOperators Pointwise

noncomputable section

namespace RHLean.Arithmetic

/-- A prime outside a finite prime set is coprime to the product of that set. -/
theorem prime_coprime_primorial
    (S : Finset ℕ) (p : ℕ)
    (hp : Nat.Prime p) (hpS : p ∉ S)
    (hprime : ∀ q ∈ S, Nat.Prime q) :
    Nat.Coprime p (primorial S) := by
  rw [hp.coprime_iff_not_dvd]
  intro hpdiv
  have hpdiv' : p ∣ S.prod id := by
    simpa [primorial] using hpdiv
  rcases (Prime.dvd_finset_prod_iff hp.prime id).mp hpdiv' with
    ⟨q, hqS, hpq⟩
  rcases (hprime q hqS).eq_one_or_self_of_dvd p hpq with hpOne | hpqEq
  · exact hp.ne_one hpOne
  · exact hpS (hpqEq ▸ hqS)

/-- Exact fresh-prime recurrence for the canonical finite Möbius divisor-sum
operator.  No ordering of `S` and no complete CRT period enters the statement. -/
theorem finiteDifferenceOperator_insert
    {R : Type*} [CommRing R]
    (S : Finset ℕ) (p : ℕ)
    (hp : Nat.Prime p) (hpS : p ∉ S)
    (hprime : ∀ q ∈ S, Nat.Prime q)
    (f : ℕ → R) :
    finiteDifferenceOperator (insert p S) f =
      finiteDifferenceOperator S f -
        finiteDifferenceOperator S (shift p f) := by
  classical
  funext x
  have hcop : Nat.Coprime p (primorial S) :=
    prime_coprime_primorial S p hp hpS hprime
  unfold finiteDifferenceOperator
  rw [primorial_insert S p hpS]
  rw [hcop.divisors_mul]
  simp only [Finset.sum_map]
  rw [Finset.sum_attach]
  rw [Finset.sum_product]
  rw [hp.divisors]
  rw [Finset.sum_pair hp.ne_one.symm]
  have hsecond :
      (∑ b ∈ (primorial S).divisors,
          (((μ (p * b) : ℤ) : R)) * f (x / (p * b))) =
        -(∑ b ∈ (primorial S).divisors,
          (((μ b : ℤ) : R)) * shift b (shift p f) x) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro b hb
    have hbP : b ∣ primorial S := Nat.dvd_of_mem_divisors hb
    have hcopb : Nat.Coprime p b := hcop.of_dvd_right hbP
    have hmu : μ (p * b) = -μ b := by
      rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcopb]
      rw [ArithmeticFunction.moebius_apply_prime hp]
      ring
    rw [hmu]
    simp [shift, Nat.div_div_eq_div_mul, Nat.mul_comm]
  rw [hsecond]
  simp [shift]
  ring

/-- Singleton specialization: the canonical divisor operator is exactly one
multiplicative finite difference. -/
theorem finiteDifferenceOperator_singleton
    {R : Type*} [CommRing R]
    (p : ℕ) (hp : Nat.Prime p) (f : ℕ → R) :
    finiteDifferenceOperator {p} f =
      f - shift p f := by
  have h := finiteDifferenceOperator_insert
    (R := R) ∅ p hp (by simp) (by simp) f
  simpa using h

end RHLean.Arithmetic
