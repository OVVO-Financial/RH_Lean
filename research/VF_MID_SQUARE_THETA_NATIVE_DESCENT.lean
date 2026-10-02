import Mathlib
import «research.VF_MID_RECURSIVE_REMAINDER_BOUND»
import «research.VF_MID_DIRECT_DISCREPANCY_ABEL»

/-!
# Native VF descent written in Chebyshev theta coordinates

The direct signed-dynamics layer already proves, for one square block,

  P_R - V_R
    = (Theta_R - (2R+1)) / log(m_R) + position_R.

PR #855 proves the same VF block defect in the opposite sign as

  V_R - P_R = native_R + remainder_R,

where native_R is carried entirely by strict lower child square scales and
the full transfer remainder is O(R).

This file identifies those two exact descriptions before taking any norm.
Consequently the centered square-block theta increment is exactly the
log-weighted native VF descent packet plus the already-explicit transfer and
within-band position terms.

No new cancellation principle, PNT rate, Li allocation, or RH hypothesis is
introduced here. This is the bridge needed to attack the existing
square-endpoint Chebyshev envelope directly with the #855 native descent.
-/

noncomputable section

open scoped BigOperators

namespace RHLean.Analysis

attribute [local instance] Classical.propDecidable

/-- The direct right-closed prime-band error and the open-interior square-band
error are literally the same scalar. The upper square never contributes a
prime. -/
theorem vfMidDirectBandError_eq_squareBandError
    (R : ℕ) :
    vfMidDirectBandError R = vfMidSquareBandError R := by
  unfold vfMidDirectBandError vfMidDirectPrimeBandCount vfMidSquareBandError
  rw [vfMidDirectPrimeBand_eq_squareWheelPrimes]
  simp only [vfMidSquareWheelPrimes, vfMidSquareWheelSites,
    vfMidSquareBandPrimes, vfMidSquareBandSites]

/-- #855 written with the sign convention of the direct prime-band error. -/
theorem vfMidDirectBandError_eq_neg_native_add_remainder
    (R : ℕ) (hR : 7 ≤ R) :
    vfMidDirectBandError R =
      -(vfMidRecursiveAggregateNativeCharge R +
        vfMidNativeDescentRemainder R) := by
  have hdesc :=
    vfMidOddCompositeTrackingDefect_eq_nativeCharge_add_descentRemainder
      R hR
  have hneg :=
    vfMidOddCompositeTrackingDefect_eq_neg_bandError
      R (by omega : 2 ≤ R)
  rw [hneg] at hdesc
  rw [vfMidDirectBandError_eq_squareBandError]
  linarith

/-- The logarithm at the midpoint of every live square band in the #855 range
is strictly positive. -/
theorem vfMidBandMidpoint_log_pos_of_seven_le
    {R : ℕ} (hR : 7 ≤ R) :
    0 < Real.log (vfMidBandMidpoint R) := by
  apply Real.log_pos
  unfold vfMidBandMidpoint
  have hRreal : (7 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  nlinarith

/-- Exact square-block Chebyshev/native-VF identity.

The centered theta increment is not a new cancellation problem. It is exactly
the #855 native lower-scale packet, its explicit transfer remainder, and the
already-bounded within-band logarithmic position correction, all expressed in
the natural logarithmic currency of the block:

  Theta_R - (2R+1)
    = -log(m_R) * (native_R + remainder_R + position_R).
-/
theorem vfMidDirectThetaBandError_eq_nativeVFDescent
    (R : ℕ) (hR : 7 ≤ R) :
    vfMidDirectThetaBandError R =
      -Real.log (vfMidBandMidpoint R) *
        (vfMidRecursiveAggregateNativeCharge R +
          vfMidNativeDescentRemainder R +
          vfMidDirectLogPositionError R) := by
  have hsplit := vfMidDirectBandError_eq_theta_add_position R
  have hdesc :=
    vfMidDirectBandError_eq_neg_native_add_remainder R hR
  have hlog :=
    vfMidBandMidpoint_log_pos_of_seven_le hR
  have heq :
      vfMidDirectThetaBandError R /
            Real.log (vfMidBandMidpoint R) +
          vfMidDirectLogPositionError R =
        -(vfMidRecursiveAggregateNativeCharge R +
          vfMidNativeDescentRemainder R) := by
    rw [← hsplit]
    exact hdesc
  have hlogne : Real.log (vfMidBandMidpoint R) ≠ 0 := hlog.ne'
  field_simp [hlogne] at heq
  nlinarith

/-- Native lower-scale part of one centered theta increment. -/
def vfMidThetaNativeDescentMain (R : ℕ) : ℝ :=
  -Real.log (vfMidBandMidpoint R) *
    vfMidRecursiveAggregateNativeCharge R

/-- Everything outside the native lower-scale packet after changing from VF
seat currency to theta/logarithmic currency. The two prime-population terms
inside the #855 remainder remain signed against one another. -/
def vfMidThetaNativeDescentRemainder (R : ℕ) : ℝ :=
  -Real.log (vfMidBandMidpoint R) *
    (vfMidNativeDescentRemainder R +
      vfMidDirectLogPositionError R)

/-- The block theta increment splits exactly into the native descended packet
and the signed non-native transfer packet. -/
theorem vfMidDirectThetaBandError_eq_thetaNativeMain_add_remainder
    (R : ℕ) (hR : 7 ≤ R) :
    vfMidDirectThetaBandError R =
      vfMidThetaNativeDescentMain R +
        vfMidThetaNativeDescentRemainder R := by
  rw [vfMidDirectThetaBandError_eq_nativeVFDescent R hR]
  unfold vfMidThetaNativeDescentMain vfMidThetaNativeDescentRemainder
  ring

/-- Exact theta endpoint ledger over an arbitrary square window.

For 7 <= A <= B, the change of the Chebyshev square-endpoint error is the
signed sum of native lower-scale VF packets plus their explicit transfer
remainders. No absolute values have been inserted. -/
theorem vfMidDirectThetaEndpointError_sub_eq_nativeVFDescent_sum
    (A B : ℕ) (hA : 7 ≤ A) (hAB : A ≤ B) :
    vfMidDirectThetaEndpointError B -
        vfMidDirectThetaEndpointError A =
      ∑ R ∈ Finset.Ico A B,
        (vfMidThetaNativeDescentMain R +
          vfMidThetaNativeDescentRemainder R) := by
  calc
    vfMidDirectThetaEndpointError B -
          vfMidDirectThetaEndpointError A =
        ∑ R ∈ Finset.Ico A B,
          (vfMidDirectThetaEndpointError (R + 1) -
            vfMidDirectThetaEndpointError R) := by
              symm
              exact Finset.sum_Ico_sub vfMidDirectThetaEndpointError hAB
    _ = ∑ R ∈ Finset.Ico A B, vfMidDirectThetaBandError R := by
          apply Finset.sum_congr rfl
          intro R _hR
          rw [vfMidDirectThetaBandError_eq_endpoint_diff]
    _ = ∑ R ∈ Finset.Ico A B,
          (vfMidThetaNativeDescentMain R +
            vfMidThetaNativeDescentRemainder R) := by
          apply Finset.sum_congr rfl
          intro R hRmem
          have hR7 : 7 ≤ R :=
            hA.trans (Finset.mem_Ico.mp hRmem).1
          rw [vfMidDirectThetaBandError_eq_thetaNativeMain_add_remainder R hR7]

/-- The exact square-endpoint Chebyshev target sufficient for the already
compiled Abel consumer. -/
def VFMidSquareThetaEnvelopeStatement : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ R : ℕ, 3 ≤ R →
      |vfMidDirectThetaEndpointError R| ≤
        C * (R : ℝ) * (Real.log (R : ℝ)) ^ 2

/-- A square-theta envelope supplies the direct VF endpoint estimate at every
R >= 3 with the constants already proved by the Abel layer. -/
theorem abs_vfMidDirectSquareEndpointError_le_of_squareThetaEnvelope
    (h : VFMidSquareThetaEnvelopeStatement)
    (R : ℕ) (hR : 3 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧
      |vfMidDirectSquareEndpointError R| ≤
        C * (R : ℝ) * Real.log (R : ℝ) +
          (4 * C + 9 / Real.log 4) * (R : ℝ) +
          |vfMidDirectSquareEndpointError 2 -
            vfMidDirectThetaEndpointError 2 *
              vfMidDirectThetaAbelWeight 2| := by
  rcases h with ⟨C, hC0, hC⟩
  refine ⟨C, hC0, ?_⟩
  exact abs_vfMidDirectSquareEndpointError_le_of_thetaEnvelope
    R hR C hC0 (fun r hr _hrR => hC r hr)

/-- The remaining Chebyshev problem after #855, stated directly on the exact
native theta ledger rather than as a new cancellation hypothesis. -/
def VFMidThetaNativeDescentBoundedStatement : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ R : ℕ, 7 ≤ R →
      |vfMidDirectThetaEndpointError R| ≤
        C * (R : ℝ) * (Real.log (R : ℝ)) ^ 2

end RHLean.Analysis
