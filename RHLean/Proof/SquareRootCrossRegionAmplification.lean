import Mathlib
import RHLean.Proof.SquareRootAmplificationClosure
import RHLean.Analysis.SquareRootPositiveSmoothCollapse
import RHLean.Proof.MatchedFarSurvivorBridge

/-!
# Cross-region sufficient targets for square-root amplification

The legal root/successor cancellation is overwhelmingly cross-region rather than
fixed-prime fibrewise.  The exact square-root decomposition already packages the
relevant signed interactions into two channels:

* `squareRootPositiveSmoothMass R`, the complete positive-orientation smooth
  channel; and
* `squareRootMatchedBornSmoothTransport R`, the born-smooth/high-transport
  matched channel.

The endpoint identity is

`M(R^2-1) = positiveSmooth(R) + matched(R)`.

Because the ancestry universe omits the exceptional source `m=1`, the shifted
endpoint numerator is

`M(R^2-1)-1 = positiveSmooth(R) + (matched(R)-1)`.

This module proves that fixed critical-envelope amplification bounds for those
two already-signed channels imply the full endpoint amplification theorem.  It
does not bound raw root or successor diagonals and does not split the matched
channel by distinguished prime.
-/

noncomputable section

namespace RHLean.Proof

/-- Fixed amplification for the positive-orientation signed channel. -/
def SquareRootPositiveSmoothAmplificationStatement : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧
    ∀ R : ℕ, ∀ K : ℝ,
      2 ≤ R →
      LowerMertensCriticalEnvelope R K →
      ‖squareRootPositiveSmoothMass R‖ ^ 2 ≤
        A * (R : ℝ) ^ 2 * K

/-- Fixed amplification for the complete matched born-smooth/high-transport
channel after the same exceptional-source shift as the ancestry renewal. -/
def SquareRootMatchedShiftedAmplificationStatement : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧
    ∀ R : ℕ, ∀ K : ℝ,
      2 ≤ R →
      LowerMertensCriticalEnvelope R K →
      ‖squareRootMatchedBornSmoothTransport R - 1‖ ^ 2 ≤
        A * (R : ℝ) ^ 2 * K

/-- Pair of signed cross-region amplification targets. -/
def SquareRootCrossRegionAmplificationStatement : Prop :=
  SquareRootPositiveSmoothAmplificationStatement ∧
    SquareRootMatchedShiftedAmplificationStatement

private theorem cross_region_norm_sq_add_le_two (u v : ℂ) :
    ‖u + v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
  have hnorm := norm_add_le u v
  have hu : 0 ≤ ‖u‖ := norm_nonneg _
  have hv : 0 ≤ ‖v‖ := norm_nonneg _
  have huv : 0 ≤ ‖u + v‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖u‖ - ‖v‖)]

/-- Exact shifted endpoint decomposition into the two cross-region channels. -/
theorem shiftedMertensEndpoint_eq_positive_add_matchedShift
    (R : ℕ) (hR : 2 ≤ R) :
    RHLean.Analysis.mertensSummatory (squareRootEndpoint R) - 1 =
      squareRootPositiveSmoothMass R +
        (squareRootMatchedBornSmoothTransport R - 1) := by
  have hR1 : 1 ≤ R := by omega
  have hend :
      RHLean.Analysis.squarePrefixEndpoint (R - 1) = squareRootEndpoint R :=
    squarePrefixEndpoint_pred_eq_squareRootEndpoint R hR1
  have hsplit := squarePrefixMertens_eq_positiveSmooth_add_matched R hR1
  unfold RHLean.Analysis.squarePrefixMertens at hsplit
  rw [hend] at hsplit
  rw [hsplit]
  ring

/-- Fixed amplification of the two signed cross-region channels is sufficient
for the complete endpoint amplification theorem. -/
theorem squareRootEndpointAmplification_of_crossRegion
    (hcross : SquareRootCrossRegionAmplificationStatement) :
    SquareRootMertensEndpointAmplificationStatement := by
  rcases hcross.1 with ⟨AP, hAP, hpos⟩
  rcases hcross.2 with ⟨AJ, hAJ, hmatched⟩
  refine ⟨2 * (AP + AJ), by positivity, ?_⟩
  intro R K hR hK
  have hp := hpos R K hR hK
  have hj := hmatched R K hR hK
  have hsum := cross_region_norm_sq_add_le_two
    (squareRootPositiveSmoothMass R)
    (squareRootMatchedBornSmoothTransport R - 1)
  rw [← shiftedMertensEndpoint_eq_positive_add_matchedShift R hR] at hsum
  have hendEnergy :
      ‖RHLean.Analysis.mertensSummatory (squareRootEndpoint R) - 1‖ ^ 2 =
        (((mertensSummatoryInt (squareRootEndpoint R) - 1 : ℤ) : ℝ) ^ 2) := by
    simpa [shiftedMertensEnergy] using
      shiftedMertensEnergy_eq_intSquare (squareRootEndpoint R)
  rw [hendEnergy] at hsum
  calc
    (((mertensSummatoryInt (squareRootEndpoint R) - 1 : ℤ) : ℝ) ^ 2) ≤
        2 * ‖squareRootPositiveSmoothMass R‖ ^ 2 +
          2 * ‖squareRootMatchedBornSmoothTransport R - 1‖ ^ 2 := hsum
    _ ≤ 2 * (AP * (R : ℝ) ^ 2 * K) +
          2 * (AJ * (R : ℝ) ^ 2 * K) := by
      linarith
    _ = (2 * (AP + AJ)) * (R : ℝ) ^ 2 * K := by ring

/-- Consequently the two cross-region targets already imply the full repository
Mertens energy criterion through the fixed-amplification closure theorem. -/
theorem mertensEnergyBounded_of_crossRegionAmplification
    (hcross : SquareRootCrossRegionAmplificationStatement) :
    RHLean.Analysis.MertensEnergyBoundedStatement :=
  mertensEnergyBounded_of_squareRootEndpointAmplification
    (squareRootEndpointAmplification_of_crossRegion hcross)

end RHLean.Proof
