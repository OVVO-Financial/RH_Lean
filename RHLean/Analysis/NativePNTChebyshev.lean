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
        obtain ⟨p, ⟨⟨hp1, hpN⟩, hpPrime⟩, k, ⟨hk1, hklog⟩, rfl⟩ := hq
        exact ⟨by
          exact ⟨Nat.one_le_pow_of_one_le hp1, Nat.pow_le_of_le_log hpPrime.one_lt hklog⟩,
          rfl⟩
      · simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_Icc,
          Finset.mem_image, not_exists, not_and, and_imp,
          ArithmeticFunction.vonMangoldt_eq_zero_iff, Nat.isPrimePow_iff] at hx ⊢
        contrapose! hx
        rintro ⟨p, k, hpPrime, hk, rfl⟩
        have hkpos : 0 < k := by omega
        have hpN : p ≤ N := by
          have hpdvd : p ∣ p ^ k := Nat.dvd_pow_self p hkpos.ne'
          exact (Nat.le_of_dvd (Nat.pow_pos hpPrime.pos k) hpdvd).trans hx.2
        refine ⟨p, ⟨⟨hpPrime.one_le, hpN⟩, hpPrime⟩, k, ?_, rfl⟩
        exact ⟨hkpos, Nat.le_log_of_pow_le hpPrime.one_lt hx.2⟩
    _ = ∑ p ∈ nativePrimeSet N,
        ∑ q ∈ Finset.image (fun k => p ^ k) (Finset.Icc 1 (p.log N)), Λ q := by
      rw [Finset.sum_biUnion]
      intro p hp q hq hpq
      rw [Finset.disjoint_left]
      intro z hzq hzp
      simp only [Finset.mem_image, Finset.mem_Icc] at hzq hzp
      obtain ⟨kq, hkq, hkqeq⟩ := hzq
      obtain ⟨kp, hkp, hkpeq⟩ := hzp
      have hpPrime : p.Prime := (Finset.mem_filter.mp hp).2
      have hqPrime : q.Prime := (Finset.mem_filter.mp hq).2
      have heq : q ^ kq = p ^ kp := by simpa [hkqeq, hkpeq]
      have hpqEq : p = q := (hpPrime.pow_inj' hqPrime hkq.1 hkp.1 heq.symm).1
      exact hpq hpqEq.symm
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
      rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega),
        ArithmeticFunction.vonMangoldt_apply_prime hpPrime]
    _ = ∑ p ∈ nativePrimeSet N, p.log N * Real.log p := by
      apply Finset.sum_congr rfl
      intro p _hp
      simp

end RHLean.Analysis
