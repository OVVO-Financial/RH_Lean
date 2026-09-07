import Mathlib
import RHLean.Proof.PostRootCovarianceLcmInteriorPacking

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Analysis
open RHLean.Arithmetic
open Finset Nat

attribute [local instance] Classical.propDecidable

/-- The real Mertens prefix on `1,...,W` is the length-`W+1` physical prefix;
the site zero has zero Möbius weight. -/
theorem sum_Icc_realMoebiusStep_eq_realMertensLength (W : ℕ) :
    (∑ n ∈ Finset.Icc 1 W, realMoebiusStep n) =
      realMertensLength (W + 1) := by
  have hrange : Finset.range (W + 1) = {0} ∪ Finset.Icc 1 W := by
    ext n
    simp
    omega
  unfold realMertensLength
  rw [hrange, Finset.sum_union]
  · simp [realMoebiusStep]
  · rw [Finset.disjoint_left]
    intro n hn0 hnIcc
    simp at hn0
    subst n
    simp at hnIcc

/-- The real squarefree diagonal on `1,...,W` is the length-`W+1` Green--Kubo
diagonal. -/
theorem sum_Icc_realMoebiusStep_sq_eq_realMertensDiagonal (W : ℕ) :
    (∑ n ∈ Finset.Icc 1 W, realMoebiusStep n ^ 2) =
      realMertensDiagonal (W + 1) := by
  have hrange : Finset.range (W + 1) = {0} ∪ Finset.Icc 1 W := by
    ext n
    simp
    omega
  unfold realMertensDiagonal
  rw [hrange, Finset.sum_union]
  · simp [realMoebiusStep]
  · rw [Finset.disjoint_left]
    intro n hn0 hnIcc
    simp at hn0
    subst n
    simp at hnIcc

/-- Real form of the ordered complete-lcm decomposition. -/
theorem two_mul_sum_realMoebiusStep_lcmInteriorPositive_eq_length_sub_diagonal
    (W : ℕ) :
    2 * (∑ mn ∈ moebiusLcmInteriorPositiveCarrier W,
      realMoebiusStep mn.1 * realMoebiusStep mn.2) =
      realMertensLength (W + 1) - realMertensDiagonal (W + 1) := by
  have hordered :=
    sum_moebiusLcmInteriorOrderedCarrier_eq_diagonal_add_two_mul_positive W
  rw [sum_moebiusLcmInteriorOrderedCarrier_eq_moebiusPrefix] at hordered
  have hreal :
      (∑ n ∈ Finset.Icc 1 W, realMoebiusStep n) =
        (∑ n ∈ Finset.Icc 1 W, realMoebiusStep n ^ 2) +
          2 * (∑ mn ∈ moebiusLcmInteriorPositiveCarrier W,
            realMoebiusStep mn.1 * realMoebiusStep mn.2) := by
    simp only [realMoebiusStep]
    exact_mod_cast hordered
  rw [sum_Icc_realMoebiusStep_eq_realMertensLength,
    sum_Icc_realMoebiusStep_sq_eq_realMertensDiagonal] at hreal
  linarith

/-- **The complete super-endpoint lcm boundary is the Mertens falling
factorial.**  All squarefree diagonal terms cancel between Green--Kubo and the
complete-lcm interior:

`2 B(W) = M(W)^2 - M(W)`.
-/
theorem two_mul_fullLcmBoundaryKernel_eq_length_sq_sub_length (W : ℕ) :
    2 * fullLcmBoundaryKernel W =
      realMertensLength (W + 1) ^ 2 - realMertensLength (W + 1) := by
  have hgreen :=
    realMertensLength_sq_eq_diagonal_add_two_mul_positiveLagPairSum (W + 1)
  have hinterior :=
    two_mul_sum_realMoebiusStep_lcmInteriorPositive_eq_length_sub_diagonal W
  unfold fullLcmBoundaryKernel
  nlinarith

/-- **Exact scalar form of the post-root super-endpoint boundary.**  The entire
literal LCM-boundary pair sum is the prime Euler finite difference of the
integer-valued falling-factorial field `M(M-1)`. -/
theorem two_mul_sum_postRootCovarianceRemainderBoundaryLcmCarrier_eq_lengthFiniteDifference
    (W : ℕ) :
    2 * (∑ mn ∈ postRootCovarianceRemainderBoundaryLcmCarrier W,
      realMoebiusStep mn.1 * realMoebiusStep mn.2) =
      (realMertensLength (W + 1) ^ 2 - realMertensLength (W + 1)) -
        ∑ p ∈ postRootPrimeFamilySet W,
          (realMertensLength (W / p + 1) ^ 2 -
            realMertensLength (W / p + 1)) := by
  rw [sum_postRootCovarianceRemainderBoundaryLcmCarrier_eq_finiteDifference]
  rw [mul_sub]
  rw [two_mul_fullLcmBoundaryKernel_eq_length_sq_sub_length]
  rw [Finset.mul_sum]
  apply congrArg (fun x : ℝ =>
    (realMertensLength (W + 1) ^ 2 - realMertensLength (W + 1)) - x)
  apply Finset.sum_congr rfl
  intro p _hp
  exact two_mul_fullLcmBoundaryKernel_eq_length_sq_sub_length (W / p)

end RHLean.Proof
