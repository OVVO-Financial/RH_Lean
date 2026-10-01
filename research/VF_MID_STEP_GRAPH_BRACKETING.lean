import Mathlib
import «research.VF_MID_LITERAL_BLOCK_CROSSING»

/-!
# VF-mid step-graph bracketing

The literal VF plot is a step graph, not merely a family of horizontal
plateaux.  Consequently the prime-count staircase can intersect VF in two
ways on the R-th square block:

1. horizontally: pi crosses the plateau K_R inside [R^2,(R+1)^2];
2. vertically: at the right square boundary, the VF jump from K_R to K_{R+1}
   crosses the prime-count level pi((R+1)^2).

This file packages that union as the actual graph-bracketing condition.
-/

noncomputable section

namespace RHLean.Analysis

/-- The vertical VF jump at the right edge of square block R contains the
prime-count value at that boundary. -/
def VFMidIntegerVerticalStepCrossed (R : ℕ) : Prop :=
  vfMidIntegerBlockLevel R ≤ Nat.primeCounting ((R + 1) ^ 2) ∧
    Nat.primeCounting ((R + 1) ^ 2) ≤ vfMidIntegerBlockLevel (R + 1)

/-- The step graphs intersect on square block R either along the horizontal
VF plateau or along the vertical VF jump at the right boundary. -/
def VFMidIntegerStepGraphBracketed (R : ℕ) : Prop :=
  VFMidIntegerBlockCaptured R ∨ VFMidIntegerVerticalStepCrossed R

/-- If the vertical crossing is the genuinely new case, namely pi is already
above K_R at the left endpoint, then the positive square-endpoint discrepancy
is bounded by one VF band mass. -/
theorem vfMidIntegerVerticalStepCrossed_abs_squareEndpointError_le_bandMass
    (R : ℕ) (hR : 2 ≤ R)
    (hvert : VFMidIntegerVerticalStepCrossed R)
    (habove : vfMidIntegerBlockLevel R < Nat.primeCounting (R ^ 2)) :
    |vfMidDirectSquareEndpointError R| ≤ vfMidBandMass R := by
  rcases hvert with ⟨_hvertLow, hvertHigh⟩
  have hgap :
      vfMidIntegerBlockLevel R + 1 ≤ Nat.primeCounting (R ^ 2) := by
    omega
  have hgapR :
      (vfMidIntegerBlockLevel R : ℝ) + 1 ≤
        (Nat.primeCounting (R ^ 2) : ℝ) := by
    exact_mod_cast hgap
  have hFlt :=
    vfMidFinishedMass_lt_integerBlockLevel_add_one R
  have hnonneg :
      0 ≤ vfMidDirectSquareEndpointError R := by
    unfold vfMidDirectSquareEndpointError
    linarith
  have hsq : R ^ 2 ≤ (R + 1) ^ 2 := by
    exact Nat.pow_le_pow_left (by omega) 2
  have hmono := Nat.monotone_primeCounting hsq
  have hmonoR :
      (Nat.primeCounting (R ^ 2) : ℝ) ≤
        (Nat.primeCounting ((R + 1) ^ 2) : ℝ) := by
    exact_mod_cast hmono
  have hvertHighR :
      (Nat.primeCounting ((R + 1) ^ 2) : ℝ) ≤
        (vfMidIntegerBlockLevel (R + 1) : ℝ) := by
    exact_mod_cast hvertHigh
  have hKnext :=
    vfMidIntegerBlockLevel_cast_le (R + 1)
  have hsucc := vfMidFinishedMass_succ hR
  have hupper :
      vfMidDirectSquareEndpointError R ≤ vfMidBandMass R := by
    unfold vfMidDirectSquareEndpointError
    linarith
  rw [abs_of_nonneg hnonneg]
  exact hupper

/-- Graph bracketing gives an explicit local endpoint bound.  Horizontal
crossing uses the existing one-block width bound.  A genuinely vertical
crossing bounds the positive discrepancy by one VF band mass. -/
theorem vfMidIntegerStepGraphBracketed_abs_squareEndpointError_lt
    (R : ℕ) (hR : 2 ≤ R)
    (hgraph : VFMidIntegerStepGraphBracketed R) :
    |vfMidDirectSquareEndpointError R| <
      2 * (R : ℝ) + 2 + vfMidBandMass R := by
  have hmass : 0 ≤ vfMidBandMass R :=
    vfMidBandMass_nonneg_of_two_le R hR
  rcases hgraph with hhorizontal | hvert
  · have h :=
      vfMidIntegerBlockCaptured_abs_squareEndpointError_lt R hhorizontal
    linarith
  · rcases hvert with ⟨hvertLow, hvertHigh⟩
    by_cases hleft :
        Nat.primeCounting (R ^ 2) ≤ vfMidIntegerBlockLevel R
    · have hhorizontal : VFMidIntegerBlockCaptured R :=
        ⟨hleft, hvertLow⟩
      have h :=
        vfMidIntegerBlockCaptured_abs_squareEndpointError_lt R hhorizontal
      linarith
    · have habove :
          vfMidIntegerBlockLevel R < Nat.primeCounting (R ^ 2) := by
        omega
      have h :=
        vfMidIntegerVerticalStepCrossed_abs_squareEndpointError_le_bandMass
          R hR ⟨hvertLow, hvertHigh⟩ habove
      have hwidth : 0 < 2 * (R : ℝ) + 2 := by positivity
      linarith

/-- Universal horizontal-or-vertical graph bracketing. -/
def VFMidIntegerStepGraphBracketingStatement : Prop :=
  ∀ R : ℕ, 2 ≤ R → VFMidIntegerStepGraphBracketed R

end RHLean.Analysis
