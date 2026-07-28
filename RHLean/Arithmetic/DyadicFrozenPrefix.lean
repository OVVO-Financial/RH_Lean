import Mathlib

open scoped BigOperators ArithmeticFunction.Moebius

namespace RHLean.Arithmetic

/-- The finite dyadic block `(N,2N]`. -/
def dyadicBlock (N : ℕ) : Finset ℕ := Finset.Icc (N + 1) (2 * N)

/-- The number of multiples of `d` in `(N,2N]`. -/
def dyadicDivisorWeight (N d : ℕ) : ℕ :=
  (dyadicBlock N).filter (fun n => d ∣ n) |>.card

/-- Every proper divisor of a positive integer in `(N,2N]` lies in the frozen prefix. -/
theorem properDivisor_le_base {N n d : ℕ}
    (hnN : N < n) (hn2 : n ≤ 2 * N) (hd : d ∣ n) (hdn : d < n) : d ≤ N := by
  obtain ⟨k, rfl⟩ := hd
  have hk : 2 ≤ k := by
    by_contra h
    interval_cases k <;> simp_all
  nlinarith

/-- Möbius is reconstructed from its proper-divisor values. -/
theorem moebius_eq_neg_sum_properDivisors {n : ℕ} (hn : 1 < n) :
    μ n = -∑ d ∈ n.divisors.erase n, μ d := by
  have hconv := congrArg (fun f : ArithmeticFunction ℤ => f n)
    ArithmeticFunction.moebius_mul_coe_zeta
  simp [ArithmeticFunction.mul_apply, hn.ne, Nat.divisorsAntidiagonal, Finset.sum_erase_add _ _] at hconv ⊢
  linarith

/-- Pointwise frozen-prefix reconstruction on the next dyadic block. -/
theorem moebius_eq_neg_frozenPrefixSum {N n : ℕ}
    (hnN : N < n) (hn2 : n ≤ 2 * N) :
    μ n = -∑ d ∈ Finset.range (N + 1), if d ∣ n ∧ d < n then μ d else 0 := by
  have hn : 1 < n := by omega
  rw [moebius_eq_neg_sum_properDivisors hn]
  congr 1
  apply Finset.sum_subset
  · intro d hd
    simp only [Finset.mem_erase, Nat.mem_divisors] at hd
    simp [properDivisor_le_base hnN hn2 hd.2.2 hd.1]
  · intro d hdRange hdNot
    simp only [Finset.mem_range] at hdRange
    by_cases hdn : d ∣ n ∧ d < n
    · exfalso
      apply hdNot
      simp [hdn, hn.ne']
    · simp [hdn]

/-- Exact finite divisor-incidence form of the dyadic increment. -/
theorem dyadic_moebius_increment_eq_frozen_weighted_sum (N : ℕ) :
    (∑ n ∈ dyadicBlock N, μ n) =
      -∑ d ∈ Finset.range (N + 1), (dyadicDivisorWeight N d : ℤ) * μ d := by
  classical
  rw [Finset.sum_congr rfl]
  · simp_rw [show ∀ n ∈ dyadicBlock N,
        μ n = -∑ d ∈ Finset.range (N + 1), if d ∣ n ∧ d < n then μ d else 0 by
      intro n hn
      simp only [dyadicBlock, Finset.mem_Icc] at hn
      exact moebius_eq_neg_frozenPrefixSum hn.1 hn.2]
    rw [Finset.sum_neg_distrib, Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro d hd
    rw [← Finset.card_filter]
    simp [dyadicDivisorWeight, dyadicBlock]
  · intro n hn
    rfl

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
  simp [dyadicInheritedCompositeMass, dyadicPrimeBirths,
    ArithmeticFunction.moebius_apply_prime]

/-- A typed finite cancellation premise for the dyadic frozen-prefix operator. -/
def DyadicFrozenPrefixCancellation : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    |((∑ n ∈ dyadicBlock N, μ n : ℤ) : ℝ)| ≤ ε * N

end RHLean.Arithmetic
