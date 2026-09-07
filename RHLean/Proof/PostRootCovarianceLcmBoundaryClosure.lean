import Mathlib
import RHLean.Proof.PostRootCovarianceLcmInteriorPacking

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Analysis
open RHLean.Arithmetic
open Finset Nat

attribute [local instance] Classical.propDecidable

/-- The complete-lcm interior identity in the same real Green--Kubo coordinates
as the covariance.  Complete lcm cubes turn the Mertens prefix itself, rather
than its square, into diagonal plus twice the positive orientation. -/
theorem realMertensLength_eq_diagonal_add_two_mul_lcmInteriorPositive
    (W : ℕ) :
    realMertensLength (W + 1) =
      realMertensDiagonal (W + 1) +
        2 * ∑ mn ∈ moebiusLcmInteriorPositiveCarrier W,
          realMoebiusStep mn.1 * realMoebiusStep mn.2 := by
  have hprefix :
      realMertensLength (W + 1) =
        ∑ n ∈ Finset.Icc 1 W, realMoebiusStep n := by
    unfold realMertensLength
    rw [show Finset.range (W + 1) = {0} ∪ Finset.Icc 1 W by
      ext n
      simp
      omega]
    rw [Finset.sum_union]
    · simp [realMoebiusStep]
    · rw [Finset.disjoint_left]
      intro n hn0 hnIcc
      simp at hn0
      subst n
      simp at hnIcc
  have hdiag :
      realMertensDiagonal (W + 1) =
        ∑ n ∈ Finset.Icc 1 W, realMoebiusStep n ^ 2 := by
    unfold realMertensDiagonal
    rw [show Finset.range (W + 1) = {0} ∪ Finset.Icc 1 W by
      ext n
      simp
      omega]
    rw [Finset.sum_union]
    · simp [realMoebiusStep]
    · rw [Finset.disjoint_left]
      intro n hn0 hnIcc
      simp at hn0
      subst n
      simp at hnIcc
  have hdecomp :=
    sum_moebiusLcmInteriorOrderedCarrier_eq_diagonal_add_two_mul_positive W
  rw [sum_moebiusLcmInteriorOrderedCarrier_eq_moebiusPrefix] at hdecomp
  have hreal :
      (∑ n ∈ Finset.Icc 1 W, realMoebiusStep n) =
        (∑ n ∈ Finset.Icc 1 W, realMoebiusStep n ^ 2) +
          2 * ∑ mn ∈ moebiusLcmInteriorPositiveCarrier W,
            realMoebiusStep mn.1 * realMoebiusStep mn.2 := by
    simpa [realMoebiusStep, pow_two] using
      congrArg (fun z : ℤ => (z : ℝ)) hdecomp
  calc
    realMertensLength (W + 1) =
        ∑ n ∈ Finset.Icc 1 W, realMoebiusStep n := hprefix
    _ = (∑ n ∈ Finset.Icc 1 W, realMoebiusStep n ^ 2) +
          2 * ∑ mn ∈ moebiusLcmInteriorPositiveCarrier W,
            realMoebiusStep mn.1 * realMoebiusStep mn.2 := hreal
    _ = realMertensDiagonal (W + 1) +
          2 * ∑ mn ∈ moebiusLcmInteriorPositiveCarrier W,
            realMoebiusStep mn.1 * realMoebiusStep mn.2 := by
      rw [← hdiag]

/-- **Falling-energy form of the complete super-endpoint boundary.**  The
square Green--Kubo identity and the complete-lcm identity have the same
diagonal, so subtracting them removes the diagonal exactly. -/
theorem two_mul_completeLcmBoundaryPositiveMass_eq_fallingMertensEnergy
    (W : ℕ) :
    2 * completeLcmBoundaryPositiveMass W =
      realMertensLength (W + 1) ^ 2 - realMertensLength (W + 1) := by
  have hgreen :=
    realMertensLength_sq_eq_diagonal_add_two_mul_positiveLagPairSum (W + 1)
  have hinterior :=
    realMertensLength_eq_diagonal_add_two_mul_lcmInteriorPositive W
  unfold completeLcmBoundaryPositiveMass
  nlinarith

/-- **Exact falling-energy defect on the #595 super-endpoint carrier.**  Twice
the signed remainder boundary is the global falling Mertens energy minus the
same energy on every complete post-root quotient. -/
theorem two_mul_sum_postRootCovarianceRemainderBoundaryLcmCarrier_eq_fallingEnergyDefect
    (W : ℕ) :
    2 * (∑ mn ∈ postRootCovarianceRemainderBoundaryLcmCarrier W,
      realMoebiusStep mn.1 * realMoebiusStep mn.2) =
      (realMertensLength (W + 1) ^ 2 - realMertensLength (W + 1)) -
        ∑ p ∈ postRootPrimeFamilySet W,
          (realMertensLength (W / p + 1) ^ 2 -
            realMertensLength (W / p + 1)) := by
  have hrec :=
    sum_postRootCovarianceRemainderBoundaryLcmCarrier_eq_complete_sub_families W
  have htop :=
    two_mul_completeLcmBoundaryPositiveMass_eq_fallingMertensEnergy W
  have hfamily :
      2 * (∑ p ∈ postRootPrimeFamilySet W,
        completeLcmBoundaryPositiveMass (W / p)) =
        ∑ p ∈ postRootPrimeFamilySet W,
          (realMertensLength (W / p + 1) ^ 2 -
            realMertensLength (W / p + 1)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _hp
    exact two_mul_completeLcmBoundaryPositiveMass_eq_fallingMertensEnergy (W / p)
  linear_combination 2 * hrec + htop - hfamily

/-- The #595 complete-lcm remainder interior is also bounded from below by one
endpoint.  Removed post-root interiors are nonpositive, while the full complete
interior is at least `-W`. -/
theorem neg_endpoint_le_sum_postRootCovarianceRemainderInteriorLcmCarrier
    (W : ℕ) :
    -(W : ℝ) ≤
      ∑ mn ∈ postRootCovarianceRemainderInteriorLcmCarrier W,
        realMoebiusStep mn.1 * realMoebiusStep mn.2 := by
  have hfull := neg_endpoint_le_sum_realMoebiusStep_lcmInteriorPositive W
  have hpart :=
    sum_moebiusLcmInteriorPositiveCarrier_eq_remainder_add_removed W
  have hremoved :
      (∑ mn ∈ postRootPrimePhysicalInteriorLcmUnion W,
        realMoebiusStep mn.1 * realMoebiusStep mn.2) ≤ 0 := by
    rw [sum_postRootPrimePhysicalInteriorLcmUnion_eq_familySum]
    apply Finset.sum_nonpos
    intro p hp
    exact sum_postRootPrimePhysicalInteriorLcmCarrier_nonpos hp
  linarith

/-- One-sided linear target isolated on the literal super-endpoint lcm carrier. -/
def PostRootCovarianceBoundaryLcmLinearStatement : Prop :=
  ∃ D : ℝ, 0 ≤ D ∧
    ∀ W : ℕ, 2 ≤ W →
      (∑ mn ∈ postRootCovarianceRemainderBoundaryLcmCarrier W,
        realMoebiusStep mn.1 * realMoebiusStep mn.2) ≤ D * (W : ℝ)

/-- **The super-endpoint lcm boundary is exactly the remaining linear seam.**
The complete-lcm interior is already trapped between `-W` and `W`, so a linear
upper bound on the boundary is equivalent, up to adding one to the constant,
to the old post-root covariance remainder statement. -/
theorem postRootCovarianceBoundaryLcmLinear_iff_remainderLinear :
    PostRootCovarianceBoundaryLcmLinearStatement ↔
      PostRootCovarianceLinearRemainderStatement := by
  constructor
  · rintro ⟨D, hD, hboundary⟩
    refine ⟨D + 1, by positivity, ?_⟩
    intro W hW
    have hsplit :=
      postRootCovarianceRemainder_eq_interiorLcm_add_boundaryLcm W
    have hinterior :=
      sum_postRootCovarianceRemainderInteriorLcmCarrier_le_endpoint W
    have hbound := hboundary W hW
    nlinarith [show (0 : ℝ) ≤ (W : ℝ) by positivity]
  · rintro ⟨D, hD, hremainder⟩
    refine ⟨D + 1, by positivity, ?_⟩
    intro W hW
    have hsplit :=
      postRootCovarianceRemainder_eq_interiorLcm_add_boundaryLcm W
    have hinterior :=
      neg_endpoint_le_sum_postRootCovarianceRemainderInteriorLcmCarrier W
    have hrem := hremainder W hW
    nlinarith [show (0 : ℝ) ≤ (W : ℝ) by positivity]

end RHLean.Proof
