import Mathlib

open scoped BigOperators ArithmeticFunction.Moebius

namespace RHLean.Arithmetic

/-- The finite dyadic block `(N,2N]`. -/
def dyadicBlock (N : ℕ) : Finset ℕ := Finset.Icc (N + 1) (2 * N)

/-- The number of multiples of `d` in `(N,2N]`. -/
def dyadicDivisorWeight (N d : ℕ) : ℕ :=
  ((dyadicBlock N).filter fun n => d ∣ n).card

/-- Every proper divisor of an integer in `(N,2N]` lies in the frozen prefix. -/
theorem properDivisor_le_base {N n d : ℕ}
    (hnN : N < n) (hn2 : n ≤ 2 * N) (hd : d ∣ n) (hdn : d < n) : d ≤ N := by
  obtain ⟨k, rfl⟩ := hd
  have hk : 2 ≤ k := by
    by_contra h
    interval_cases k <;> simp_all
  nlinarith

/-- The proper divisors of `n` that lie in the frozen prefix. -/
def frozenProperDivisors (N n : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter fun d => d ∣ n ∧ d < n

/-- Möbius is reconstructed from its proper-divisor values. -/
theorem moebius_eq_neg_sum_properDivisors {n : ℕ} (hn : 1 < n) :
    μ n = -∑ d ∈ n.divisors.erase n, μ d := by
  have hconv :
      ((ArithmeticFunction.moebius * (ArithmeticFunction.zeta : ArithmeticFunction ℤ)) n) =
        (1 : ArithmeticFunction ℤ) n :=
    congrArg (fun f : ArithmeticFunction ℤ => f n)
      ArithmeticFunction.moebius_mul_coe_zeta
  have hsum : ∑ d ∈ n.divisors, μ d = 0 := by
    simpa only [ArithmeticFunction.mul_apply, ArithmeticFunction.zeta_apply,
      ArithmeticFunction.one_apply, hn.ne', if_false, mul_one,
      Nat.sum_divisorsAntidiagonal'] using hconv
  have hnmem : n ∈ n.divisors := Nat.mem_divisors.mpr ⟨dvd_rfl, hn.ne'⟩
  rw [← Finset.sum_erase_add _ hnmem] at hsum
  linarith

/-- On `(N,2N]`, the frozen proper-divisor set is the full proper-divisor set. -/
theorem frozenProperDivisors_eq {N n : ℕ}
    (hnN : N < n) (hn2 : n ≤ 2 * N) :
    frozenProperDivisors N n = n.divisors.erase n := by
  have hn : 1 < n := by omega
  ext d
  simp only [frozenProperDivisors, Finset.mem_filter, Finset.mem_range,
    Finset.mem_erase, Nat.mem_divisors]
  constructor
  · rintro ⟨hdN, hdvd, hdn⟩
    exact ⟨Nat.ne_of_lt hdn, hdvd, hn.ne'⟩
  · rintro ⟨hdn, hdvd, _⟩
    exact ⟨Nat.lt_succ_iff.mpr (properDivisor_le_base hnN hn2 hdvd (Nat.lt_of_le_of_ne
      (Nat.le_of_dvd (by omega) hdvd) hdn)), hdvd, lt_of_le_of_ne
      (Nat.le_of_dvd (by omega) hdvd) hdn⟩

/-- Pointwise frozen-prefix reconstruction on the next dyadic block. -/
theorem moebius_eq_neg_frozenPrefixSum {N n : ℕ}
    (hnN : N < n) (hn2 : n ≤ 2 * N) :
    μ n = -∑ d ∈ frozenProperDivisors N n, μ d := by
  have hn : 1 < n := by omega
  rw [frozenProperDivisors_eq hnN hn2]
  exact moebius_eq_neg_sum_properDivisors hn

/-- Exact finite divisor-incidence form of the dyadic increment. -/
theorem dyadic_moebius_increment_eq_frozen_weighted_sum (N : ℕ) :
    (∑ n ∈ dyadicBlock N, μ n) =
      -∑ d ∈ Finset.range (N + 1), (dyadicDivisorWeight N d : ℤ) * μ d := by
  classical
  calc
    (∑ n ∈ dyadicBlock N, μ n) =
        ∑ n ∈ dyadicBlock N, -∑ d ∈ frozenProperDivisors N n, μ d := by
          apply Finset.sum_congr rfl
          intro n hn
          simp only [dyadicBlock, Finset.mem_Icc] at hn
          exact moebius_eq_neg_frozenPrefixSum hn.1 hn.2
    _ = -∑ d ∈ Finset.range (N + 1),
          ∑ n ∈ dyadicBlock N, if d ∣ n then μ d else 0 := by
          simp [frozenProperDivisors, Finset.sum_comm]
    _ = -∑ d ∈ Finset.range (N + 1), (dyadicDivisorWeight N d : ℤ) * μ d := by
          apply congrArg Neg.neg
          apply Finset.sum_congr rfl
          intro d hd
          simp [dyadicDivisorWeight, mul_comm]

/-- The finite prime contribution in the new dyadic block. -/
def dyadicPrimeBirths (N : ℕ) : ℕ :=
  ((dyadicBlock N).filter Nat.Prime).card

/-- The inherited composite Möbius mass in the new dyadic block. -/
def dyadicInheritedCompositeMass (N : ℕ) : ℤ :=
  ∑ n ∈ (dyadicBlock N).filter (fun n => ¬ Nat.Prime n), μ n

/-- Exact prime-birth versus inherited-composite decomposition. -/
theorem dyadic_increment_eq_inherited_sub_primeBirths (N : ℕ) :
    (∑ n ∈ dyadicBlock N, μ n) =
      dyadicInheritedCompositeMass N - dyadicPrimeBirths N := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not (s := dyadicBlock N) (p := Nat.Prime)]
  have hprime :
      (∑ n ∈ (dyadicBlock N).filter Nat.Prime, μ n) =
        -(dyadicPrimeBirths N : ℤ) := by
    calc
      (∑ n ∈ (dyadicBlock N).filter Nat.Prime, μ n) =
          ∑ _n ∈ (dyadicBlock N).filter Nat.Prime, (-1 : ℤ) := by
            apply Finset.sum_congr rfl
            intro n hn
            exact ArithmeticFunction.moebius_apply_prime (Finset.mem_filter.mp hn).2
      _ = -(dyadicPrimeBirths N : ℤ) := by
            simp [dyadicPrimeBirths]
  rw [hprime]
  simp [dyadicInheritedCompositeMass]

/-- A typed finite cancellation premise for the dyadic frozen-prefix operator. -/
def DyadicFrozenPrefixCancellation : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    |((∑ n ∈ dyadicBlock N, μ n : ℤ) : ℝ)| ≤ ε * N

end RHLean.Arithmetic
