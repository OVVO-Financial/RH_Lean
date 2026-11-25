import RHLean.Analysis.AlpogeNativeLocalGainSource
import RHLean.Analysis.AlpogeNativeSquareCandidateCapacity
import Mathlib.Data.Nat.Factorization.PrimePow

set_option autoImplicit false
noncomputable section

open scoped ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.Analysis

/-- A mixed low/high site has exactly zero principal weight, including all
proper powers, whenever both coprime factors exceed one. -/
theorem nativePrincipal_mixed_site_zero {l d : ℕ} (hl : 1 < l) (hd : 1 < d)
    (hc : l.Coprime d) : Λ (l * d) = 0 := by
  apply ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr
  intro hpow
  rcases (hc.isPrimePow_dvd_mul hpow).mp (dvd_refl _) with h | h
  · have hle := Nat.le_of_dvd (by omega : 0 < l) h
    nlinarith [Nat.mul_le_mul_left l (show 2 ≤ d from hd)]
  · have hle := Nat.le_of_dvd (by omega : 0 < d) h
    nlinarith [Nat.mul_le_mul_right d (show 2 ≤ l from hl)]

/-- On any nontrivial low-prime fibre, the exact signed ancestor pullback of
the original principal kernel has a single supported term. Choosing the
binomial Möbius coefficient gives b(1)=(-1)^Ω(h). -/
theorem nativePrincipal_low_fibre_pullback (N l : ℕ) (hl : 1 < l)
    (F : Finset ℕ) (hone : 1 ∈ F) (hd : ∀ d ∈ F, 0 < d)
    (hc : ∀ d ∈ F, l.Coprime d) (b : ℕ → ℝ) :
    (∑ d ∈ F, b d * (Λ (l * d) * nativeSquareCandidateKernel N (l * d))) =
      b 1 * (Λ l * nativeSquareCandidateKernel N l) := by
  rw [Finset.sum_eq_single 1]
  · simp
  · intro d hF hne
    have hd' := hd d hF
    rw [nativePrincipal_mixed_site_zero hl (by omega) (hc d hF), zero_mul, mul_zero]
  · exact fun h => (h hone).elim

namespace AlpogeThin
open Formalism.FrobeniusOrbits Formalism.HC

/-- On the actual unramified Frobenius colour measure, the signed
binomial sum is a single sign times its positive-binomial counterpart.
The site function may depend on the power and retain every colour width.
The full ASK has F(k,g)=log(p) times its actual positive-part site cut. -/
theorem nativeDyadic_signedAncestor_on_unramified_prime
    (e q d p v A : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hH : HostHyp q d) (hp : p.Prime) (hpN : ¬ p ∣ alpogeNativeHostN e q d)
    (hv : v ≤ A) (F : ℕ → AlpogeNativeE0 × AlpogeNativeDyadicH e → ℂ) :
    (∑ k ∈ Finset.Icc 1 v, ((-1 : ℂ) ^ (A - k) * (v.choose k : ℂ)) *
      nativeDyadicHostPrimePowerWeight e q d p k (F k)) =
      -((-1 : ℂ) ^ A) * ∑ k ∈ Finset.Icc 1 v,
        (v.choose k : ℂ) * nativeDyadicHostPrimePowerWeight e q d p k (F k) := by
  classical
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkA : k ≤ A := (Finset.mem_Icc.mp hk).2.trans hv
  rw [nativeDyadicHostPrimePowerWeight_unramified e q d p k hH hp hpN (F k)]
  by_cases h : Odd k ∧ jacobiSym (-(d : ℤ)) p = -1
  · rw [ite_eq_left h]
    have he := pow_add (-1 : ℂ) (A - k) k
    rw [Nat.sub_add_cancel hkA, h.1.neg_one_pow] at he
    have hs : (-1 : ℂ) ^ (A - k) = -((-1 : ℂ) ^ A) := by rw [he]; ring
    rw [hs]
    ring
  · rw [ite_eq_right h]
    ring

/-- On the complete native colour measure, only even powers of the genuine
ramified d-prime reverse the common binomial sign. This retains both
dyadic-and-q inertia and the moving d-inertia coset at every exponent. -/
theorem nativeDyadic_signedAncestor_all_primes
    (e q d p v A : ℕ) [Fact q.Prime] [Fact d.Prime]
    (hH : HostHyp q d) (hp : p.Prime) (hv : v ≤ A)
    (F : ℕ → AlpogeNativeE0 × AlpogeNativeDyadicH e → ℂ) :
    (∑ k ∈ Finset.Icc 1 v, ((-1 : ℂ) ^ (A - k) * (v.choose k : ℂ)) *
      nativeDyadicHostPrimePowerWeight e q d p k (F k)) =
      -((-1 : ℂ) ^ A) * ∑ k ∈ Finset.Icc 1 v,
        (if p = d ∧ Even k then (-1 : ℂ) else 1) *
          ((v.choose k : ℂ) * nativeDyadicHostPrimePowerWeight e q d p k (F k)) := by
  classical
  by_cases hpd : p = d
  · subst p
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkA := (Finset.mem_Icc.mp hk).2.trans hv
    have he := pow_add (-1 : ℂ) (A - k) k
    rw [Nat.sub_add_cancel hkA] at he
    by_cases heven : Even k
    · rw [heven.neg_one_pow, mul_one] at he
      rw [ite_eq_left ⟨rfl, heven⟩, he]
      ring
    · have hodd := Nat.not_even_iff_odd.mp heven
      rw [hodd.neg_one_pow] at he
      rw [ite_eq_right (fun h => heven h.2), he]
      ring
  · simp only [hpd, false_and, ite_false, one_mul]
    by_cases hpN : p ∣ alpogeNativeHostN e q d
    · have hpA : p ∣ 2 ^ (e + 2) * q := by
        rcases hp.dvd_mul.mp hpN with hpA | hpd'
        · exact hpA
        · exact (hpd ((Nat.prime_dvd_prime_iff_eq hp Fact.out).mp hpd')).elim
      simp only [nativeDyadicHostPrimePowerWeight_typeI e q d p _ hH hp hpA,
        mul_zero, Finset.sum_const_zero]
    · exact nativeDyadic_signedAncestor_on_unramified_prime e q d p v A hH hp hpN hv F

end AlpogeThin
end RHLean.Analysis
end
