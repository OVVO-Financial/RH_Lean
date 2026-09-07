import Mathlib
import RHLean.Proof.PostRootCovarianceLcmInteriorPacking

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Analysis
open RHLean.Arithmetic
open Finset Nat

attribute [local instance] Classical.propDecidable

/-- The complete positive-pair mass left above the lcm wall at endpoint `W`.
Equivalently this is the full positive-lag covariance minus the complete-lcm
interior. -/
def fullLcmBoundaryKernel (W : ℕ) : ℝ :=
  realMertensPositiveLagPairSum (W + 1) -
    ∑ mn ∈ moebiusLcmInteriorPositiveCarrier W,
      realMoebiusStep mn.1 * realMoebiusStep mn.2

/-- The #595 complete-lcm remainder interior is bounded on both sides by one
endpoint unit.  The upper bound was the product-packing theorem; the lower
bound follows because every removed post-root interior is nonpositive. -/
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
    exact Finset.sum_nonpos fun p hp =>
      sum_postRootPrimePhysicalInteriorLcmCarrier_nonpos hp
  linarith

/-- Exact Euler finite-difference identity for the super-endpoint lcm boundary.
After all complete post-root prime families are removed, the remaining boundary
is the full boundary kernel at `W` minus the same kernel on every quotient seat
`floor(W/p)`.  No absolute values, prime-gap input, or probabilistic model enters. -/
theorem sum_postRootCovarianceRemainderBoundaryLcmCarrier_eq_finiteDifference
    (W : ℕ) :
    (∑ mn ∈ postRootCovarianceRemainderBoundaryLcmCarrier W,
      realMoebiusStep mn.1 * realMoebiusStep mn.2) =
      fullLcmBoundaryKernel W -
        ∑ p ∈ postRootPrimeFamilySet W, fullLcmBoundaryKernel (W / p) := by
  have hrem := postRootCovarianceRemainder_eq_interiorLcm_add_boundaryLcm W
  have hinterior :=
    sum_moebiusLcmInteriorPositiveCarrier_eq_remainder_add_removed W
  have hremoved :=
    sum_postRootPrimePhysicalInteriorLcmUnion_eq_familySum W
  have hscale :
      (∑ p ∈ postRootPrimeFamilySet W,
        ∑ mn ∈ postRootPrimePhysicalInteriorLcmCarrier W p,
          realMoebiusStep mn.1 * realMoebiusStep mn.2) =
      ∑ p ∈ postRootPrimeFamilySet W,
        ∑ mn ∈ moebiusLcmInteriorPositiveCarrier (W / p),
          realMoebiusStep mn.1 * realMoebiusStep mn.2 := by
    apply Finset.sum_congr rfl
    intro p hp
    exact sum_postRootPrimePhysicalInteriorLcmCarrier_eq_lower hp
  rw [hremoved, hscale] at hinterior
  unfold postRootCovarianceRemainder postRootPrimeFamilyCovarianceTotal at hrem
  unfold fullLcmBoundaryKernel
  rw [Finset.sum_sub_distrib]
  linarith

/-- A linear bound on the literal super-endpoint lcm boundary. -/
def PostRootCovarianceBoundaryLcmLinearStatement : Prop :=
  ∃ D : ℝ, 0 ≤ D ∧
    ∀ W : ℕ, 2 ≤ W →
      (∑ mn ∈ postRootCovarianceRemainderBoundaryLcmCarrier W,
        realMoebiusStep mn.1 * realMoebiusStep mn.2) ≤ D * (W : ℝ)

/-- Once the complete-lcm interior is packed, the old post-root linear remainder
target and the literal lcm-boundary target are equivalent up to one endpoint
unit in the constant.  Thus no analytic difficulty remains anywhere except the
Euler finite difference in
`sum_postRootCovarianceRemainderBoundaryLcmCarrier_eq_finiteDifference`. -/
theorem postRootCovarianceBoundaryLcmLinear_iff_remainderLinear :
    PostRootCovarianceBoundaryLcmLinearStatement ↔
      PostRootCovarianceLinearRemainderStatement := by
  constructor
  · rintro ⟨D, hD, hboundary⟩
    refine ⟨D + 1, by positivity, ?_⟩
    intro W hW
    have hb := hboundary W hW
    have hi := sum_postRootCovarianceRemainderInteriorLcmCarrier_le_endpoint W
    have hsplit := postRootCovarianceRemainder_eq_interiorLcm_add_boundaryLcm W
    nlinarith
  · rintro ⟨D, hD, hremainder⟩
    refine ⟨D + 1, by positivity, ?_⟩
    intro W hW
    have hr := hremainder W hW
    have hi :=
      neg_endpoint_le_sum_postRootCovarianceRemainderInteriorLcmCarrier W
    have hsplit := postRootCovarianceRemainder_eq_interiorLcm_add_boundaryLcm W
    nlinarith

end RHLean.Proof
