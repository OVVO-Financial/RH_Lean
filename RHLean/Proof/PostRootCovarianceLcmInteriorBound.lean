import Mathlib
import RHLean.Proof.PostRootCovarianceLcmBoundary

open scoped ArithmeticFunction.Moebius BigOperators

/-!
# Linear bound for the complete-lcm interior

The lcm-fibre identity from `PostRootCovarianceLcmBoundary` says that the full
ordered Möbius mass on one complete divisor-pair fibre is `μ(L)`.  This file
extracts the positive orientation of those fibres.

Because the ordered carrier splits into diagonal plus two symmetric positive
orientations, the complete-lcm positive mass is

`(sum μ(L) - sum μ(L)^2) / 2`.

Hence it is always nonpositive, and its negative size is at most the physical
endpoint.  This is a deterministic finite identity; no PNT, independence, or
prime-gap input is used.
-/

noncomputable section

namespace RHLean.Proof

open RHLean.Analysis
open Finset Nat

attribute [local instance] Classical.propDecidable

/-- Canonically oriented positive pairs in the complete-lcm interior. -/
def moebiusLcmInteriorPositiveCarrier (W : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 W).product (Finset.Icc 1 W)).filter fun mn =>
    mn.1 < mn.2 ∧ Nat.lcm mn.1 mn.2 ≤ W

@[simp] theorem mem_moebiusLcmInteriorPositiveCarrier
    {W : ℕ} {mn : ℕ × ℕ} :
    mn ∈ moebiusLcmInteriorPositiveCarrier W ↔
      mn.1 ∈ Finset.Icc 1 W ∧ mn.2 ∈ Finset.Icc 1 W ∧
        mn.1 < mn.2 ∧ Nat.lcm mn.1 mn.2 ≤ W := by
  simp [moebiusLcmInteriorPositiveCarrier, and_assoc]

/-- The direct positive-lcm carrier is exactly the lcm-filter of the physical
positive-pair carrier used by the post-root covariance descent. -/
theorem moebiusLcmInteriorPositiveCarrier_eq_filter (W : ℕ) :
    moebiusLcmInteriorPositiveCarrier W =
      (mertensPositivePhysicalPairCarrier W).filter fun mn =>
        Nat.lcm mn.1 mn.2 ≤ W := by
  ext mn
  simp [moebiusLcmInteriorPositiveCarrier,
    mertensPositivePhysicalPairCarrier, and_assoc]

/-- The ordered complete-lcm carrier splits exactly into its diagonal and two
symmetric positive orientations. -/
theorem sum_moebiusLcmInteriorOrderedCarrier_eq_diagonal_add_two_mul_positive
    (W : ℕ) :
    (∑ mn ∈ moebiusLcmInteriorOrderedCarrier W, μ mn.1 * μ mn.2) =
      (∑ n ∈ Finset.Icc 1 W, μ n * μ n) +
        2 * ∑ mn ∈ moebiusLcmInteriorPositiveCarrier W,
          μ mn.1 * μ mn.2 := by
  have hsplit (m n : ℕ) :
      (if Nat.lcm m n ≤ W then μ m * μ n else 0) =
        (if m = n ∧ Nat.lcm m n ≤ W then μ m * μ n else 0) +
        (if m < n ∧ Nat.lcm m n ≤ W then μ m * μ n else 0) +
        (if n < m ∧ Nat.lcm m n ≤ W then μ m * μ n else 0) := by
    by_cases hcut : Nat.lcm m n ≤ W
    · rcases lt_trichotomy m n with hlt | heq | hgt
      · have hne : m ≠ n := ne_of_lt hlt
        have hrev : ¬ n < m := by omega
        simp [hcut, hlt, hne, hrev]
      · subst n
        simp [hcut]
      · have hne : m ≠ n := by omega
        have hfwd : ¬ m < n := by omega
        simp [hcut, hgt, hne, hfwd]
    · simp [hcut]
  have hdiag :
      (∑ m ∈ Finset.Icc 1 W,
        ∑ n ∈ Finset.Icc 1 W,
          if m = n ∧ Nat.lcm m n ≤ W then μ m * μ n else 0) =
        ∑ n ∈ Finset.Icc 1 W, μ n * μ n := by
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.sum_eq_single m]
    · have hmW : m ≤ W := (Finset.mem_Icc.mp hm).2
      simp [hmW]
    · intro b _hb hbm
      simp [Ne.symm hbm]
    · intro hnot
      exact (hnot hm).elim
  have hswap :
      (∑ m ∈ Finset.Icc 1 W,
        ∑ n ∈ Finset.Icc 1 W,
          if n < m ∧ Nat.lcm m n ≤ W then μ m * μ n else 0) =
        ∑ m ∈ Finset.Icc 1 W,
          ∑ n ∈ Finset.Icc 1 W,
            if m < n ∧ Nat.lcm m n ≤ W then μ m * μ n else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m _hm
    apply Finset.sum_congr rfl
    intro n _hn
    simp [Nat.lcm_comm, mul_comm]
  unfold moebiusLcmInteriorOrderedCarrier
    moebiusLcmInteriorPositiveCarrier
  simp_rw [Finset.sum_filter, Finset.sum_product]
  calc
    (∑ m ∈ Finset.Icc 1 W,
      ∑ n ∈ Finset.Icc 1 W,
        if Nat.lcm m n ≤ W then μ m * μ n else 0) =
      (∑ m ∈ Finset.Icc 1 W,
        ∑ n ∈ Finset.Icc 1 W,
          if m = n ∧ Nat.lcm m n ≤ W then μ m * μ n else 0) +
      (∑ m ∈ Finset.Icc 1 W,
        ∑ n ∈ Finset.Icc 1 W,
          if m < n ∧ Nat.lcm m n ≤ W then μ m * μ n else 0) +
      (∑ m ∈ Finset.Icc 1 W,
        ∑ n ∈ Finset.Icc 1 W,
          if n < m ∧ Nat.lcm m n ≤ W then μ m * μ n else 0) := by
        simp_rw [hsplit, Finset.sum_add_distrib]
        ring
    _ = (∑ n ∈ Finset.Icc 1 W, μ n * μ n) +
        2 * ∑ m ∈ Finset.Icc 1 W,
          ∑ n ∈ Finset.Icc 1 W,
            if m < n ∧ Nat.lcm m n ≤ W then μ m * μ n else 0 := by
      rw [hdiag, hswap]
      ring

private theorem moebius_le_square_int (n : ℕ) :
    μ n ≤ μ n * μ n := by
  rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;> simp [h]

private theorem neg_moebius_square_le_int (n : ℕ) :
    -(μ n * μ n) ≤ μ n := by
  rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;> simp [h]

private theorem moebius_square_le_one_int (n : ℕ) :
    μ n * μ n ≤ (1 : ℤ) := by
  rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;> simp [h]

/-- The complete-lcm positive mass never contributes positively. -/
theorem sum_moebiusLcmInteriorPositiveCarrier_nonpos (W : ℕ) :
    (∑ mn ∈ moebiusLcmInteriorPositiveCarrier W,
      μ mn.1 * μ mn.2) ≤ 0 := by
  have hdecomp :=
    sum_moebiusLcmInteriorOrderedCarrier_eq_diagonal_add_two_mul_positive W
  rw [sum_moebiusLcmInteriorOrderedCarrier_eq_moebiusPrefix] at hdecomp
  have hprefix_le_diag :
      (∑ n ∈ Finset.Icc 1 W, μ n) ≤
        ∑ n ∈ Finset.Icc 1 W, μ n * μ n := by
    exact Finset.sum_le_sum fun n _hn => moebius_le_square_int n
  omega

/-- The negative size of the complete-lcm positive mass is at most the endpoint. -/
theorem neg_endpoint_le_sum_moebiusLcmInteriorPositiveCarrier (W : ℕ) :
    -(W : ℤ) ≤
      ∑ mn ∈ moebiusLcmInteriorPositiveCarrier W,
        μ mn.1 * μ mn.2 := by
  have hdecomp :=
    sum_moebiusLcmInteriorOrderedCarrier_eq_diagonal_add_two_mul_positive W
  rw [sum_moebiusLcmInteriorOrderedCarrier_eq_moebiusPrefix] at hdecomp
  have hneg_prefix :
      -(∑ n ∈ Finset.Icc 1 W, μ n * μ n) ≤
        ∑ n ∈ Finset.Icc 1 W, μ n := by
    calc
      -(∑ n ∈ Finset.Icc 1 W, μ n * μ n) =
          ∑ n ∈ Finset.Icc 1 W, -(μ n * μ n) := by simp
      _ ≤ ∑ n ∈ Finset.Icc 1 W, μ n := by
        exact Finset.sum_le_sum fun n _hn => neg_moebius_square_le_int n
  have hdiag_endpoint :
      (∑ n ∈ Finset.Icc 1 W, μ n * μ n) ≤ (W : ℤ) := by
    calc
      (∑ n ∈ Finset.Icc 1 W, μ n * μ n) ≤
          ∑ _n ∈ Finset.Icc 1 W, (1 : ℤ) := by
        exact Finset.sum_le_sum fun n _hn => moebius_square_le_one_int n
      _ = (W : ℤ) := by
        rw [Finset.sum_const, Nat.card_Icc]
        simp
  omega

/-- Real-valued form used by the covariance carrier. -/
theorem sum_realMoebiusStep_lcmInteriorPositive_nonpos (W : ℕ) :
    (∑ mn ∈ moebiusLcmInteriorPositiveCarrier W,
      realMoebiusStep mn.1 * realMoebiusStep mn.2) ≤ 0 := by
  simp only [realMoebiusStep]
  exact_mod_cast sum_moebiusLcmInteriorPositiveCarrier_nonpos W

/-- Real-valued lower bound used when subtracting post-root family interiors. -/
theorem neg_endpoint_le_sum_realMoebiusStep_lcmInteriorPositive (W : ℕ) :
    -(W : ℝ) ≤
      ∑ mn ∈ moebiusLcmInteriorPositiveCarrier W,
        realMoebiusStep mn.1 * realMoebiusStep mn.2 := by
  simp only [realMoebiusStep]
  exact_mod_cast neg_endpoint_le_sum_moebiusLcmInteriorPositiveCarrier W

end RHLean.Proof
