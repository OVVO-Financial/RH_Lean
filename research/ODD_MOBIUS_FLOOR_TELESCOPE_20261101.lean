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
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta BigOperators

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


/-- Möbius restricted to odd inputs, as an arithmetic function. -/
def oddMoebius : ArithmeticFunction ℤ where
  toFun n := if Odd n then ArithmeticFunction.moebius n else 0
  map_zero' := by simp

@[simp] theorem oddMoebius_apply (n : ℕ) :
    oddMoebius n = if Odd n then ArithmeticFunction.moebius n else 0 := rfl

/-- The odd restriction of Möbius remains multiplicative. -/
theorem isMultiplicative_oddMoebius :
    ArithmeticFunction.IsMultiplicative oddMoebius := by
  refine ⟨by simp [oddMoebius], ?_⟩
  intro m n hmn
  simp only [oddMoebius_apply]
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hmn]
  by_cases hm : Odd m <;> by_cases hn : Odd n <;> simp [hm, hn]

/-- The divisor sum of odd Möbius coefficients. -/
def oddMoebiusZeta : ArithmeticFunction ℤ :=
  oddMoebius * (ArithmeticFunction.zeta : ArithmeticFunction ℤ)

theorem isMultiplicative_oddMoebiusZeta :
    ArithmeticFunction.IsMultiplicative oddMoebiusZeta :=
  isMultiplicative_oddMoebius.mul ArithmeticFunction.isMultiplicative_zeta.natCast

/-- The arithmetic-function convolution is the literal odd-divisor sum. -/
theorem oddMoebiusZeta_apply (n : ℕ) :
    oddMoebiusZeta n = oddDivisorMoebiusSum n := by
  unfold oddMoebiusZeta oddDivisorMoebiusSum
  rw [ArithmeticFunction.coe_mul_zeta_apply]
  apply Finset.sum_congr rfl
  intro d hd
  rfl

/-- Local Euler factor: the odd Möbius divisor sum is one on powers of two
and zero on powers of every odd prime. -/
theorem oddMoebiusZeta_prime_pow
    (p k : ℕ) (hp : Nat.Prime p) (hk : 0 < k) :
    oddMoebiusZeta (p ^ k) = if p = 2 then 1 else 0 := by
  unfold oddMoebiusZeta
  rw [ArithmeticFunction.coe_mul_zeta_apply, Nat.sum_divisors_prime_pow hp,
    Finset.sum_range_succ']
  by_cases hpTwo : p = 2
  · subst p
    simp [oddMoebius, ArithmeticFunction.moebius_apply_prime_pow,
      Nat.prime_two, Nat.not_odd_iff_even, hk]
  · have hpOdd : Odd p := hp.odd_of_ne_two hpTwo
    simp [oddMoebius, hpOdd.pow, ArithmeticFunction.moebius_apply_prime_pow,
      hp, hpTwo, hk]

/-- Integer-valued indicator of the powers of two. -/
noncomputable def powerOfTwoIndicator (n : ℕ) : ℤ := by
  classical
  exact if ∃ j : ℕ, n = 2 ^ j then 1 else 0

/-- The odd Möbius divisor sum is exactly the power-of-two indicator. -/
theorem oddMoebiusZeta_eq_powerOfTwoIndicator (n : ℕ) :
    oddMoebiusZeta n = powerOfTwoIndicator n := by
  classical
  unfold powerOfTwoIndicator
  induction n using Nat.recOnPrimePow with
  | zero =>
      simp [oddMoebiusZeta]
  | one =>
      simp [oddMoebiusZeta, oddMoebius]
  | prime_pow_mul a p k hp hpa hk ih =>
      have hcop : Nat.Coprime (p ^ k) a :=
        (hp.coprime_iff_not_dvd.mpr hpa).pow_left k
      rw [isMultiplicative_oddMoebiusZeta.map_mul_of_coprime hcop,
        oddMoebiusZeta_prime_pow p k hp hk, ih]
      by_cases hpTwo : p = 2
      · subst p
        simp only [ite_true, one_mul]
        have hiff :
            (∃ j : ℕ, 2 ^ k * a = 2 ^ j) ↔
              ∃ j : ℕ, a = 2 ^ j := by
          constructor
          · rintro ⟨j, hj⟩
            have haDvd : a ∣ 2 ^ j := by
              rw [← hj]
              exact ⟨2 ^ k, by ac_rfl⟩
            have haOdd : Odd a := by
              rw [← Nat.not_even_iff_odd, Nat.even_iff_two_dvd]
              exact hpa
            have haCoprime : Nat.Coprime a (2 ^ j) :=
              haOdd.coprime_two_right.pow_right j
            have haOne : a = 1 :=
              Nat.eq_one_of_dvd_coprimes haCoprime (dvd_refl a) haDvd
            exact ⟨0, by simp [haOne]⟩
          · rintro ⟨j, hj⟩
            have haOdd : Odd a := by
              rw [← Nat.not_even_iff_odd, Nat.even_iff_two_dvd]
              exact hpa
            have hjZero : j = 0 := by
              by_contra hj0
              have htwo : 2 ∣ a := by
                rw [hj]
                exact dvd_pow_self 2 hj0
              exact hpa htwo
            subst j
            simp only [pow_zero] at hj
            subst a
            exact ⟨k, by simp⟩
        rw [hiff]
      · have hnot : ¬ ∃ j : ℕ, p ^ k * a = 2 ^ j := by
          rintro ⟨j, hj⟩
          have hpDvdPow : p ∣ p ^ k := dvd_pow_self p hk.ne'
          have hpDvdTwoPow : p ∣ 2 ^ j := by
            rw [← hj]
            exact dvd_mul_of_dvd_left hpDvdPow a
          have hpDvdTwo : p ∣ 2 := hp.dvd_of_dvd_pow hpDvdTwoPow
          have hpEq : p = 2 :=
            (Nat.dvd_prime Nat.prime_two).mp hpDvdTwo |>.resolve_left hp.ne_one
          exact hpTwo hpEq
        simp [hpTwo, hnot]

/-- Finite number of powers of two in the positive prefix, represented as
an integer-valued indicator sum. -/
def finitePowerOfTwoCount (A : ℕ) : ℤ :=
  ∑ n ∈ Finset.Icc 1 A, powerOfTwoIndicator n

/-- Independently accepted finite odd-divisor telescope:
the odd Möbius floor sum counts exactly the powers of two up to `A`. -/
theorem oddMoebiusFloorSum_eq_finitePowerOfTwoCount (A : ℕ) :
    oddMoebiusFloorSum A = finitePowerOfTwoCount A := by
  rw [oddMoebiusFloorSum_eq_sum_oddDivisorMoebiusSum]
  unfold finitePowerOfTwoCount
  apply Finset.sum_congr rfl
  intro n hn
  rw [← oddMoebiusZeta_apply, oddMoebiusZeta_eq_powerOfTwoIndicator]

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
#print axioms oddMoebiusZeta_eq_powerOfTwoIndicator
#print axioms oddMoebiusFloorSum_eq_finitePowerOfTwoCount

end RHLean.Analysis
