import Mathlib
import RHLean.Analysis.NativePNTMertens

/-!
# Odd Möbius floor telescope

This module begins the kernel proof of the independently accepted finite
odd-divisor telescope. It first exposes the exact finite Fubini identity on
the repository's native Möbius carrier, then certifies that the inner
odd-divisor sum is one on every power of two.

No asymptotic estimate, local moment, complete-source bound, endpoint gain,
or RH statement is assumed or proved here.
-/

noncomputable section

open Finset
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Analysis

/-- The exact finite odd-cofactor floor sum. -/
def oddMoebiusFloorSum (A : ℕ) : ℤ :=
  ∑ m ∈ Finset.Icc 1 A,
    if Odd m then
      (ArithmeticFunction.moebius m : ℤ) * ((A / m : ℕ) : ℤ)
    else 0

/-- The Möbius sum over odd divisors of a positive integer. -/
def oddDivisorMoebiusSum (n : ℕ) : ℤ :=
  ∑ d ∈ n.divisors,
    if Odd d then ArithmeticFunction.moebius d else 0

/-- Exact finite Fubini expansion of the odd Möbius floor sum. -/
theorem oddMoebiusFloorSum_eq_sum_oddDivisorMoebiusSum (A : ℕ) :
    oddMoebiusFloorSum A =
      ∑ n ∈ Finset.Icc 1 A, oddDivisorMoebiusSum n := by
  have key : ∀ m : ℕ,
      (if Odd m then
          (ArithmeticFunction.moebius m : ℤ) * ((A / m : ℕ) : ℤ)
        else 0) =
        ∑ n ∈ Finset.Icc 1 A,
          if Odd m ∧ m ∣ n then ArithmeticFunction.moebius m else 0 := by
    intro m
    by_cases hmOdd : Odd m
    · simp only [hmOdd, ite_true, true_and]
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
        nsmul_eq_mul, RHLean.Analysis.nativeCardMultiplesIcc]
      ring
    · simp [hmOdd]
  calc
    oddMoebiusFloorSum A =
        ∑ m ∈ Finset.Icc 1 A,
          ∑ n ∈ Finset.Icc 1 A,
            if Odd m ∧ m ∣ n then ArithmeticFunction.moebius m else 0 := by
      unfold oddMoebiusFloorSum
      exact Finset.sum_congr rfl (fun m _ => key m)
    _ = ∑ n ∈ Finset.Icc 1 A,
          ∑ m ∈ Finset.Icc 1 A,
            if Odd m ∧ m ∣ n then ArithmeticFunction.moebius m else 0 :=
      Finset.sum_comm
    _ = ∑ n ∈ Finset.Icc 1 A, oddDivisorMoebiusSum n := by
      refine Finset.sum_congr rfl (fun n hn => ?_)
      unfold oddDivisorMoebiusSum
      simp only [Finset.mem_Icc] at hn
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, ← Finset.sum_filter]
      apply Finset.sum_congr
      · ext m
        constructor
        · intro hm
          rw [Finset.mem_filter] at hm
          rcases hm with ⟨hmIcc, hmOdd, hmn⟩
          rw [Finset.mem_Icc] at hmIcc
          rw [Finset.mem_filter, Nat.mem_divisors]
          exact ⟨⟨hmn, by omega⟩, hmOdd⟩
        · intro hm
          rw [Finset.mem_filter] at hm
          rcases hm with ⟨hmDiv, hmOdd⟩
          rw [Nat.mem_divisors] at hmDiv
          rcases hmDiv with ⟨hmn, hnNe⟩
          have hnPos : 0 < n := by omega
          have hmPos : 0 < m := Nat.pos_of_dvd_of_pos hmn hnPos
          have hmLe : m ≤ n := Nat.le_of_dvd hnPos hmn
          rw [Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨hmPos, by omega⟩, hmOdd, hmn⟩
      · intro m hm
        rfl

/-- On a power of two the only odd divisor is one, so the odd-divisor
Möbius sum is exactly one. -/
theorem oddDivisorMoebiusSum_two_pow (j : ℕ) :
    oddDivisorMoebiusSum (2 ^ j) = 1 := by
  have hset : (2 ^ j).divisors.filter Odd = {1} := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hdvd, _⟩, hdOdd⟩
      have hcop : Nat.Coprime d (2 ^ j) :=
        hdOdd.coprime_two_right.pow_right j
      exact Nat.eq_one_of_dvd_coprimes hcop (dvd_refl d) hdvd
    · rintro rfl
      simp
  unfold oddDivisorMoebiusSum
  rw [← Finset.sum_filter, hset]
  simp

#print axioms oddMoebiusFloorSum_eq_sum_oddDivisorMoebiusSum
#print axioms oddDivisorMoebiusSum_two_pow

end RHLean.Analysis
