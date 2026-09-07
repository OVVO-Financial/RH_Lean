import Mathlib
import RHLean.Proof.PostRootCovarianceLcmInteriorPacking

open scoped ArithmeticFunction.Moebius BigOperators

noncomputable section

namespace RHLean.Proof

open RHLean.Analysis
open RHLean.Arithmetic
open Finset Nat

attribute [local instance] Classical.propDecidable

/-- The complete positive-pair mass left after removing every lcm fibre that
already closes below the physical endpoint.  This is the unmasked
super-endpoint lcm boundary at one scale. -/
def completeLcmBoundaryPositiveMass (W : ℕ) : ℝ :=
  realMertensPositiveLagPairSum (W + 1) -
    ∑ mn ∈ moebiusLcmInteriorPositiveCarrier W,
      realMoebiusStep mn.1 * realMoebiusStep mn.2

/-- **Exact recursive factorization of the post-root super-endpoint boundary.**
The remainder boundary is the complete super-endpoint lcm boundary at scale
`W`, minus one exact lower-scale copy at `floor(W/p)` for every post-root prime
family.  Every complete-lcm interior contribution cancels algebraically before
any estimate or norm is taken. -/
theorem sum_postRootCovarianceRemainderBoundaryLcmCarrier_eq_complete_sub_families
    (W : ℕ) :
    (∑ mn ∈ postRootCovarianceRemainderBoundaryLcmCarrier W,
      realMoebiusStep mn.1 * realMoebiusStep mn.2) =
      completeLcmBoundaryPositiveMass W -
        ∑ p ∈ postRootPrimeFamilySet W,
          completeLcmBoundaryPositiveMass (W / p) := by
  have hsplit :=
    postRootCovarianceRemainder_eq_interiorLcm_add_boundaryLcm W
  have hinterior :=
    sum_moebiusLcmInteriorPositiveCarrier_eq_remainder_add_removed W
  have hremovedScale :
      (∑ mn ∈ postRootPrimePhysicalInteriorLcmUnion W,
        realMoebiusStep mn.1 * realMoebiusStep mn.2) =
        ∑ p ∈ postRootPrimeFamilySet W,
          ∑ ab ∈ moebiusLcmInteriorPositiveCarrier (W / p),
            realMoebiusStep ab.1 * realMoebiusStep ab.2 := by
    rw [sum_postRootPrimePhysicalInteriorLcmUnion_eq_familySum]
    apply Finset.sum_congr rfl
    intro p hp
    exact sum_postRootPrimePhysicalInteriorLcmCarrier_eq_lower hp
  rw [hremovedScale] at hinterior
  unfold completeLcmBoundaryPositiveMass
  rw [Finset.sum_sub_distrib]
  unfold postRootCovarianceRemainder postRootPrimeFamilyCovarianceTotal at hsplit
  linear_combination hsplit - hinterior

end RHLean.Proof
