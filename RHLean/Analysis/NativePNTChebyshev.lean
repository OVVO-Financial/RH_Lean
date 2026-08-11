import Mathlib
import RHLean.Analysis.LogWeightedPrimeExtensionEndpoint

/-!
# Architecture-native Chebyshev layer

This module develops only the elementary prime and prime-power bounds needed by
the Selberg--Erdos PNT route.  The starting point is the primorial inequality
already available at the pinned Mathlib revision; no prime number theorem or
prime-density asymptotic is imported.
-/

noncomputable section

open Finset Nat
open scoped ArithmeticFunction.vonMangoldt BigOperators

namespace RHLean.Analysis

/-- The finite prime-coordinate set through `N`. -/
def nativePrimeSet (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter Nat.Prime

/-- The first Chebyshev function on an integer endpoint. -/
def nativeTheta (N : ℕ) : ℝ :=
  ∑ p ∈ nativePrimeSet N, Real.log p

/-- The prime layer is nonnegative. -/
theorem nativeTheta_nonneg (N : ℕ) : 0 ≤ nativeTheta N := by
  unfold nativeTheta
  apply Finset.sum_nonneg
  intro p hp
  have hpPrime : p.Prime := (Finset.mem_filter.mp hp).2
  exact Real.log_nonneg (by exact_mod_cast hpPrime.one_le)

/-- The finite prime layer is exactly the logarithm of the primorial. -/
theorem nativeTheta_eq_log_primorial (N : ℕ) :
    nativeTheta N = Real.log (primorial N) := by
  unfold nativeTheta nativePrimeSet primorial
  have hset :
      (Finset.Icc 1 N).filter Nat.Prime =
        (Finset.range (N + 1)).filter Nat.Prime := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range,
      Nat.lt_succ_iff]
    constructor
    · rintro ⟨⟨_hp1, hpN⟩, hpPrime⟩
      exact ⟨hpN, hpPrime⟩
    · rintro ⟨hpN, hpPrime⟩
      exact ⟨⟨hpPrime.one_le, hpN⟩, hpPrime⟩
  rw [hset, Nat.cast_prod, Real.log_prod]
  intro p hp
  have hpPrime : p.Prime := (Finset.mem_filter.mp hp).2
  exact_mod_cast hpPrime.ne_zero

/-- Chebyshev's elementary upper bound on the prime layer, inherited only from
the finite central-binomial proof of `primorial_le_4_pow`. -/
theorem nativeTheta_le_log4_mul (N : ℕ) :
    nativeTheta N ≤ Real.log 4 * (N : ℝ) := by
  rw [nativeTheta_eq_log_primorial]
  calc
    Real.log (primorial N) ≤ Real.log (4 ^ N) := by
      apply Real.log_le_log
      · exact_mod_cast primorial_pos N
      · exact_mod_cast primorial_le_4_pow N
    _ = Real.log 4 * (N : ℝ) := by
      rw [Real.log_pow]
      ring

/-- Exact prime-coordinate decomposition of the second Chebyshev mass:

`psi(N) = sum_{p <= N} floor(log_p N) log p`.

This is the prime-power analogue of the cofactor-first/prime-first reindexings
used throughout the repository. -/
theorem nativePsi_eq_sum_mul_log_prime (N : ℕ) :
    nativePsi N = ∑ p ∈ nativePrimeSet N, p.log N * Real.log p := by
  unfold nativePsi nativePrimeSet
  calc
    (∑ m ∈ Finset.Icc 1 N, Λ m) =
        ∑ m ∈ ((Finset.Icc 1 N).filter Nat.Prime).biUnion
          (fun p => Finset.image (p ^ ·) (Finset.Icc 1 (p.log N))), Λ m := by
      refine (Finset.sum_subset (fun q hq => ?_) (fun x hx => ?_)).symm
      · simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_Icc,
          Finset.mem_image] at hq ⊢
        obtain ⟨p, _, k, ⟨_, hk⟩, rfl⟩ := hq
        exact ⟨by grind, Nat.pow_le_of_le_log (by grind) hk⟩
      · simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_Icc,
          Finset.mem_image, not_exists, not_and, and_imp,
          ArithmeticFunction.vonMangoldt_eq_zero_iff, isPrimePow_nat_iff]
        contrapose!
        rintro ⟨p, k, hp, hk, rfl⟩
        simp only [Finset.mem_Icc] at hx
        have hpn : p ≤ N :=
          (Nat.le_of_dvd (by grind) (Nat.dvd_pow_self p hk.ne')).trans hx.2
        exact ⟨p, ⟨hp.one_le, hpn, hp,
          ⟨k, ⟨by grind, Nat.le_log_of_pow_le hp.one_lt hx.2, rfl⟩⟩⟩⟩
    _ = ∑ p ∈ nativePrimeSet N,
        ∑ q ∈ Finset.image (fun k => p ^ k) (Finset.Icc 1 (p.log N)), Λ q := by
      rw [Finset.sum_biUnion <| by
        rw [Finset.pairwiseDisjoint_iff]
        grind [Nat.Prime.pow_inj']]
    _ = ∑ p ∈ nativePrimeSet N,
        ∑ k ∈ Finset.Icc 1 (p.log N), Λ (p ^ k) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.sum_image]
      intro a _ha b _hb hab
      have hpPrime : p.Prime := (Finset.mem_filter.mp hp).2
      exact Nat.pow_right_injective hpPrime.two_le hab
    _ = ∑ p ∈ nativePrimeSet N,
        ∑ _k ∈ Finset.Icc 1 (p.log N), Real.log p := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro k hk
      have hpPrime : p.Prime := (Finset.mem_filter.mp hp).2
      rw [ArithmeticFunction.vonMangoldt_apply_pow (by grind),
        ArithmeticFunction.vonMangoldt_apply_prime hpPrime]
    _ = ∑ p ∈ nativePrimeSet N, p.log N * Real.log p := by
      apply Finset.sum_congr rfl
      intro p _hp
      simp

end RHLean.Analysis
