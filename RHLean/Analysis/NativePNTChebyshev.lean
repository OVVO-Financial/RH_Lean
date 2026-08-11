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

/-- The first Chebyshev function on an integer endpoint. -/
def nativeTheta (N : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log p

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
  unfold nativeTheta primorial
  rw [Nat.cast_prod, Real.log_prod]
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

end RHLean.Analysis
