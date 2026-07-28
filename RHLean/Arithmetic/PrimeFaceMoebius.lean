import Mathlib
import RHLean.Arithmetic.PrimeProductCubeFrontier

open scoped ArithmeticFunction.Moebius

noncomputable section

namespace RHLean.Arithmetic

/-- The product of a finite set of distinct primes has Möbius value equal to
its Boolean-cube parity sign. -/
theorem moebius_primeFaceProduct_eq_booleanCubeSign
    (t : Finset ℕ)
    (hprime : ∀ p ∈ t, Nat.Prime p) :
    μ (primeFaceProduct t) = booleanCubeSign t := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      simp [primeFaceProduct, booleanCubeSign]
  | @insert p t hp ih =>
      have hpPrime : Nat.Prime p := hprime p (Finset.mem_insert_self p t)
      have htPrime : ∀ q ∈ t, Nat.Prime q := by
        intro q hq
        exact hprime q (Finset.mem_insert_of_mem hq)
      have hcop : Nat.Coprime p (primeFaceProduct t) := by
        rw [hpPrime.coprime_iff_not_dvd]
        intro hpdiv
        rcases (hpPrime.prime.dvd_finsetProd_iff id).mp hpdiv with
          ⟨q, hqt, hpq⟩
        have hpAssoc : Associated p q :=
          hpPrime.prime.associated_of_dvd (htPrime q hqt).prime hpq
        have hpqEq : p = q := by simpa using hpAssoc
        exact hp (hpqEq ▸ hqt)
      rw [primeFaceProduct]
      simp only [Finset.prod_insert hp]
      rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop]
      rw [ArithmeticFunction.moebius_apply_prime hpPrime]
      rw [ih htPrime]
      simp [booleanCubeSign, Finset.card_insert_of_notMem, hp, pow_succ]

/-- Every term in the concrete prime-product frontier can therefore be read
as an actual Möbius value rather than an abstract parity sign. -/
theorem truncatedPrimeProductCube_eq_moebius_frontier
    {S : Finset ℕ} {X ell : ℕ}
    (hell : ell ∈ S)
    (hprime : ∀ p ∈ S, Nat.Prime p) :
    truncatedCubeAlternatingSum S (primeProductAdmissible S X) =
      ∑ t ∈ primeProductFirstFailureBoundary S X ell,
        μ (primeFaceProduct t) := by
  rw [truncatedPrimeProductCube_eq_frontier hell hprime]
  apply Finset.sum_congr rfl
  intro t ht
  symm
  apply moebius_primeFaceProduct_eq_booleanCubeSign
  intro p hp
  exact hprime p ((mem_primeProductFirstFailureBoundary.mp ht).1 hp)

end RHLean.Arithmetic
