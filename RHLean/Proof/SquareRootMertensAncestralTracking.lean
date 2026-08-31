import Mathlib
import RHLean.Proof.SquareRootMertensMiddleTracking
import RHLean.Proof.SquareRootMertensPositiveTracking

/-!
# The terminal obstruction in ancestral coordinates

`squareRootPositiveSmoothMass_eq_neg_primeMertensTransform` is exact:

`A_pos R = - positiveSmoothPrimeMertensTransform R`,

so the terminal obstruction reads, in the most revealing coordinates,

`|M(R^2-1) + sum_{q <= R prime} M(q-1)| <= C * R`.

This file states that form and connects it to the two already-named
propositions.

* Against `SquareRootMertensPositiveTrackingReal` the identification is
  **exact** — same proposition, different coordinates.
* Against `SquareRootMertensMiddleTracking` it costs `7` in the constant in
  each direction, because the middle term carries the seven-coordinate strip:
  `Middle = A_pos - near` and `core = matched + near`, with `‖near‖ ≤ 7R`.

The name differs from the one proposed in discussion
(`SquareRootMertensPositiveTracking`) because that name is already taken, in
`SquareRootMertensPositiveTracking.lean`, by the norm form stated against
`squareRootPositiveSmoothMass`.  The two are the same mathematical statement;
this one is written with the literal integer Mertens value and the prime
transform.
-/

noncomputable section

open scoped ArithmeticFunction.Moebius BigOperators

namespace RHLean.Proof

open RHLean.Analysis

/-- **The terminal obstruction, in ancestral coordinates.**

`|M(R^2-1) + sum_{q <= R prime} M(q-1)| <= C * R`. -/
def SquareRootMertensAncestralTracking (C : ℝ) (R : ℕ) : Prop :=
  |(squareRootMertensInt (squareRootEndpoint R) : ℝ) +
      (squareRootPositiveSmoothPrimeMertensTransform R).re| ≤ C * (R : ℝ)

/-- Ancestral coordinates are exactly the positive-orientation real form. -/
theorem squareRootMertensAncestralTracking_iff_positiveTrackingReal
    {C : ℝ} {R : ℕ} (hR : 1 ≤ R) :
    SquareRootMertensAncestralTracking C R ↔
      SquareRootMertensPositiveTrackingReal C R := by
  unfold SquareRootMertensAncestralTracking
    SquareRootMertensPositiveTrackingReal
  have hre :
      (RHLean.Analysis.mertensSummatory (squareRootEndpoint R) -
          squareRootPositiveSmoothMass R).re =
        (squareRootMertensInt (squareRootEndpoint R) : ℝ) +
          (squareRootPositiveSmoothPrimeMertensTransform R).re := by
    rw [Complex.sub_re, mertensSummatory_squareRootEndpoint_re,
      squareRootPositiveSmoothMass_eq_neg_primeMertensTransform R hR]
    simp
  rw [hre]

/-- The seven-coordinate strip, in real coordinates. -/
private theorem abs_nearPrimeTransport_re_le
    {R : ℕ} (hR : 56 ≤ R) :
    |(squareRootNearPrimeTransport R).re| ≤ 7 * (R : ℝ) :=
  (Complex.abs_re_le_norm _).trans (norm_squareRootNearPrimeTransport_le R hR)

/-- `core.re = matched.re + near.re`. -/
private theorem matchedCore_re_eq
    {R : ℕ} (hR : 56 ≤ R) :
    (squareRootLowPrimeMatchedCore R).re =
      (squareRootMatchedBornSmoothTransport R).re +
        (squareRootNearPrimeTransport R).re := by
  have hre :
      (squareRootMatchedBornSmoothTransport R).re =
        (squareRootLowPrimeMatchedCore R).re -
          (squareRootNearPrimeTransport R).re := by
    rw [squareRootMatchedBornSmoothTransport_eq_core_sub_near R hR]
    simp
  linarith

/-- **Ancestral tracking gives middle tracking, at a cost of `7`.** -/
theorem squareRootMertensMiddleTracking_of_ancestralTracking
    {C : ℝ} {R : ℕ} (hR : 56 ≤ R)
    (h : SquareRootMertensAncestralTracking C R) :
    SquareRootMertensMiddleTracking (C + 7) R := by
  have hmatched : |(squareRootMatchedBornSmoothTransport R).re| ≤ C * (R : ℝ) :=
    (squareRootMertensPositiveTrackingReal_iff_matched_re (by omega)).mp
      ((squareRootMertensAncestralTracking_iff_positiveTrackingReal
        (by omega)).mp h)
  have hnear := abs_nearPrimeTransport_re_le hR
  have hcoreBound : SquareRootLowPrimeMatchedCoreRealBound (C + 7) R := by
    unfold SquareRootLowPrimeMatchedCoreRealBound
    rw [matchedCore_re_eq hR, abs_le]
    have h1 := abs_le.mp hmatched
    have h2 := abs_le.mp hnear
    constructor <;> linarith
  exact squareRootMertensMiddleTracking_iff_mertensMiddleRealBound.mpr
    ((squareRootLowPrimeMatchedCoreRealBound_iff_mertensMiddleRealBound hR).mp
      hcoreBound)

/-- **Middle tracking gives ancestral tracking, at a cost of `7`.** -/
theorem squareRootMertensAncestralTracking_of_middleTracking
    {C : ℝ} {R : ℕ} (hR : 56 ≤ R)
    (h : SquareRootMertensMiddleTracking C R) :
    SquareRootMertensAncestralTracking (C + 7) R := by
  have hcoreBound : SquareRootLowPrimeMatchedCoreRealBound C R :=
    (squareRootLowPrimeMatchedCoreRealBound_iff_mertensMiddleRealBound hR).mpr
      (squareRootMertensMiddleTracking_iff_mertensMiddleRealBound.mp h)
  have hcore : |(squareRootLowPrimeMatchedCore R).re| ≤ C * (R : ℝ) := hcoreBound
  have hnear := abs_nearPrimeTransport_re_le hR
  have hmatched :
      |(squareRootMatchedBornSmoothTransport R).re| ≤ (C + 7) * (R : ℝ) := by
    have hre :
        (squareRootMatchedBornSmoothTransport R).re =
          (squareRootLowPrimeMatchedCore R).re -
            (squareRootNearPrimeTransport R).re := by
      rw [squareRootMatchedBornSmoothTransport_eq_core_sub_near R hR]
      simp
    rw [hre, abs_le]
    have h1 := abs_le.mp hcore
    have h2 := abs_le.mp hnear
    constructor <;> linarith
  exact (squareRootMertensAncestralTracking_iff_positiveTrackingReal
      (by omega)).mpr
    ((squareRootMertensPositiveTrackingReal_iff_matched_re (by omega)).mpr
      hmatched)

/-- **The branch, from ancestral tracking.** -/
theorem abs_squareRootLowPrimeRunningImbalanceReal_le_of_ancestralTracking
    {C : ℝ} {R K j : ℕ} (hR : 56 ≤ R) (hK : 1 ≤ K) (hKR : K < R)
    (hj : j ≤ squareRootReciprocalPrimeLayerCard R K)
    (hV0 : 0 ≤ squareRootCrossingLayerPartialPacketInt R K j)
    (hVK : squareRootCrossingLayerPartialPacketInt R K j < (K : ℤ))
    (h : SquareRootMertensAncestralTracking C R) :
    |squareRootLowPrimeRunningImbalanceReal R K j
        (squareRootBornPostTailLowPrimeCutoff R)| ≤
      C * (R : ℝ) + (R : ℝ) + (K : ℝ) :=
  abs_squareRootLowPrimeRunningImbalanceReal_le_of_mertensPositiveTracking
    hR hK hKR hj hV0 hVK
    ((squareRootMertensAncestralTracking_iff_positiveTrackingReal
      (by omega)).mp h)

end RHLean.Proof
