import Mathlib
import «research.VF_MID_LITERAL_BLOCK_CROSSING»

/-!
# Aligned VF-mid step-graph crossing

The square endpoints and square-block widths are deterministic.  This file
separates that geometry from a one-time vertical phase alignment of the
cumulative VF-mid level.

A constant additive alignment is deliberately preferred to a multiplicative
rescaling: it leaves every square-band increment exactly unchanged and hence
does not alter the asymptotic VF/Li bridge.

The natural first anchor is R = 3, x = 9, where pi(9) = 4.  Thus

  c0 = 4 - vfMidFinishedMass 3

and the aligned cumulative level is exactly 4 at the first anchored endpoint.
-/

noncomputable section

namespace RHLean.Analysis

/-- Additive phase alignment of the cumulative VF-mid level. -/
def vfMidAlignedMass (c : ℝ) (R : ℕ) : ℝ :=
  vfMidFinishedMass R + c

/-- Integer step level of an additively aligned VF-mid path. -/
def vfMidAlignedIntegerBlockLevel (c : ℝ) (R : ℕ) : ℕ :=
  ⌊vfMidAlignedMass c R⌋₊

/-- The canonical finite anchor at x = 9, where pi(9) = 4. -/
def vfMidInitialAnchor : ℝ :=
  4 - vfMidFinishedMass 3

/-- The anchor aligns the real VF level exactly at the first nontrivial square
endpoint. -/
@[simp] theorem vfMidAlignedMass_initialAnchor_three :
    vfMidAlignedMass vfMidInitialAnchor 3 = 4 := by
  unfold vfMidAlignedMass vfMidInitialAnchor
  ring

/-- Consequently the aligned integer step level at R = 3 is exactly 4. -/
@[simp] theorem vfMidAlignedIntegerBlockLevel_initialAnchor_three :
    vfMidAlignedIntegerBlockLevel vfMidInitialAnchor 3 = 4 := by
  unfold vfMidAlignedIntegerBlockLevel
  rw [vfMidAlignedMass_initialAnchor_three]
  norm_num

/-- Zero phase alignment recovers the existing integer VF level. -/
@[simp] theorem vfMidAlignedIntegerBlockLevel_zero (R : ℕ) :
    vfMidAlignedIntegerBlockLevel 0 R = vfMidIntegerBlockLevel R := by
  simp [vfMidAlignedIntegerBlockLevel, vfMidAlignedMass,
    vfMidIntegerBlockLevel]

/-- **Alignment does not change the dynamics.**  Every square-band increment
of the aligned mass is exactly the original midpoint band mass. -/
theorem vfMidAlignedMass_succ
    (c : ℝ) {R : ℕ} (hR : 2 ≤ R) :
    vfMidAlignedMass c (R + 1) =
      vfMidAlignedMass c R + vfMidBandMass R := by
  unfold vfMidAlignedMass
  rw [vfMidFinishedMass_succ hR]
  ring

/-- Horizontal intersection of the prime staircase with the aligned VF step
inside the R-th square block. -/
def VFMidAlignedHorizontalCrossed (c : ℝ) (R : ℕ) : Prop :=
  Nat.primeCounting (R ^ 2) ≤ vfMidAlignedIntegerBlockLevel c R ∧
    vfMidAlignedIntegerBlockLevel c R ≤
      Nat.primeCounting ((R + 1) ^ 2)

/-- Vertical intersection at the left square boundary x = R^2.  This is the
piece absent from the horizontal-only criterion of #840. -/
def VFMidAlignedLeftVerticalCrossed (c : ℝ) (R : ℕ) : Prop :=
  vfMidAlignedIntegerBlockLevel c (R - 1) ≤
      Nat.primeCounting (R ^ 2) ∧
    Nat.primeCounting (R ^ 2) ≤ vfMidAlignedIntegerBlockLevel c R

/-- Vertical intersection at the right square boundary x = (R+1)^2. -/
def VFMidAlignedRightVerticalCrossed (c : ℝ) (R : ℕ) : Prop :=
  vfMidAlignedIntegerBlockLevel c R ≤
      Nat.primeCounting ((R + 1) ^ 2) ∧
    Nat.primeCounting ((R + 1) ^ 2) ≤
      vfMidAlignedIntegerBlockLevel c (R + 1)

/-- Full step-graph intersection: horizontal or either vertical face. -/
def VFMidAlignedStepGraphCrossed (c : ℝ) (R : ℕ) : Prop :=
  VFMidAlignedHorizontalCrossed c R ∨
    VFMidAlignedLeftVerticalCrossed c R ∨
      VFMidAlignedRightVerticalCrossed c R

/-- The #840 horizontal capture criterion is exactly the zero-alignment
horizontal face of the more general step graph. -/
theorem vfMidAlignedHorizontalCrossed_zero_iff_captured (R : ℕ) :
    VFMidAlignedHorizontalCrossed 0 R ↔ VFMidIntegerBlockCaptured R := by
  simp [VFMidAlignedHorizontalCrossed, VFMidIntegerBlockCaptured]

/-- Therefore every #840 horizontal crossing is automatically a crossing of the
full zero-aligned step graph. -/
theorem vfMidAlignedStepGraphCrossed_zero_of_captured
    (R : ℕ) (hcap : VFMidIntegerBlockCaptured R) :
    VFMidAlignedStepGraphCrossed 0 R := by
  left
  exact (vfMidAlignedHorizontalCrossed_zero_iff_captured R).2 hcap

/-- Aligned endpoint error differs from the existing direct endpoint error by
the constant phase only.  Thus any fixed alignment is analytically harmless at
the von-Koch scale. -/
def vfMidAlignedSquareEndpointError (c : ℝ) (R : ℕ) : ℝ :=
  (Nat.primeCounting (R ^ 2) : ℝ) - vfMidAlignedMass c R

theorem vfMidAlignedSquareEndpointError_eq_direct_sub
    (c : ℝ) (R : ℕ) :
    vfMidAlignedSquareEndpointError c R =
      vfMidDirectSquareEndpointError R - c := by
  unfold vfMidAlignedSquareEndpointError vfMidAlignedMass
    vfMidDirectSquareEndpointError
  ring

end RHLean.Analysis
